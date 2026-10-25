//! Lowering bodies: expressions, statements, patterns, with local name resolution and the
//! desugarings rustc does (`for`, `while`, `?`, ranges, destructuring assignment).

use super::{LowerCtx, err, strip_block};
use crate::hir::*;
use hyprc_resolve::{Lookup, Ns};
use hyprc_span::{FxHashMap, Ident, Span, Symbol, SyntaxContext};
use hyprc_syntax::ast;

/// Local variables in scope at one level, or (with `macro_def`) the point after a
/// `macro_rules!` defined in the body.
#[derive(Default)]
pub(crate) struct Rib {
    bindings: Vec<(Symbol, SyntaxContext, LocalId)>,
    macro_def: Option<u32>,
}

/// A body under construction.
#[derive(Default)]
pub(crate) struct BodyBuilder {
    exprs: Vec<Expr>,
    pats: Vec<Pat>,
    locals: Vec<Local>,
    loops: Vec<LoopData>,
    closures: Vec<ClosureData>,
    /// Local scopes, innermost last: (name, hygiene context, local).
    ribs: Vec<Rib>,
    /// Enclosing loops and labeled blocks, innermost last.
    labels: Vec<(Option<(Symbol, SyntaxContext)>, LoopId, bool)>,
    /// Block item scopes, innermost last.
    scopes: Vec<DefId>,
    /// `try` blocks: `?` breaks to the innermost one.
    try_blocks: Vec<LoopId>,
    /// Bindings of the pattern being lowered: or-pattern alternatives share them.
    pat_bindings: Option<FxHashMap<(Symbol, SyntaxContext), LocalId>>,
}

impl LowerCtx<'_, '_> {
    fn b(&mut self) -> &mut BodyBuilder {
        self.body_stack.last_mut().expect("lowering outside a body")
    }

    fn alloc_expr(&mut self, kind: ExprKind, span: Span) -> ExprId {
        let b = self.b();
        b.exprs.push(Expr { kind, span });
        ExprId(b.exprs.len() as u32 - 1)
    }

    fn alloc_pat(&mut self, kind: PatKind, span: Span) -> PatId {
        let b = self.b();
        b.pats.push(Pat { kind, span });
        PatId(b.pats.len() as u32 - 1)
    }

    fn new_loop(&mut self, label: Option<Ident>, is_block: bool) -> LoopId {
        let b = self.b();
        b.loops.push(LoopData { label, is_block });
        LoopId(b.loops.len() as u32 - 1)
    }

    /// A compiler-made local (`for` loops, `?`): its name can't clash with user code.
    fn fresh_local(&mut self, name: &str, mutable: bool, span: Span) -> (LocalId, PatId) {
        let ident = Ident::new(Symbol::intern(name), span);
        let local = LocalId(self.b().locals.len() as u32);
        let pat = self.alloc_pat(
            PatKind::Binding {
                mode: BindingMode::Value { mutable },
                local,
                sub: None,
            },
            span,
        );
        self.b().locals.push(Local {
            name: ident,
            mutable,
            span,
            pat,
        });
        (local, pat)
    }

    /// Starts a body; `finish_body` ends it.
    fn start_body(&mut self) {
        // A body inside a body (an array length, a const block) sees the items of the
        // blocks around it.
        let scopes = self.body_scope().into_iter().collect();
        self.body_stack.push(BodyBuilder {
            ribs: vec![Rib::default()],
            scopes,
            ..BodyBuilder::default()
        });
    }

    fn finish_body(
        &mut self,
        kind: BodyKind,
        params: Vec<PatId>,
        value: ExprId,
        span: Span,
    ) -> BodyId {
        let b = self.body_stack.pop().expect("body started");
        let id = self.new_body_id();
        let scope = self.current_scope();
        self.bodies.push((
            id,
            Body {
                owner: self.owner,
                kind,
                params,
                value,
                exprs: b.exprs,
                pats: b.pats,
                locals: b.locals,
                loops: b.loops,
                closures: b.closures,
                scope,
                span,
            },
        ));
        id
    }

    pub(crate) fn lower_body_expr(&mut self, e: &ast::Expr, kind: BodyKind) -> BodyId {
        self.start_body();
        let value = self.lower_expr(e);
        self.finish_body(kind, Vec::new(), value, e.span)
    }

    pub(crate) fn lower_fn_body(&mut self, decl: &ast::FnDecl, block: &ast::Block) -> BodyId {
        self.start_body();
        let mut params = Vec::new();
        for p in &decl.inputs {
            if matches!(p.ty.kind, ast::TyKind::CVarArgs) {
                continue;
            }
            let pat = self.lower_pat_top(&p.pat);
            self.commit_bindings();
            params.push(pat);
        }
        let value = self.lower_block_expr(block, None);
        self.finish_body(BodyKind::Fn, params, value, block.span)
    }

    // ---------------------------------------------------------------------------------------
    // Names

    fn lookup_local(&self, ident: Ident) -> Option<LocalId> {
        let b = self.body_stack.last()?;
        let mut ctxt = ident.span.ctxt.normalize_to_macro_rules();
        for rib in b.ribs.iter().rev() {
            // Leaving the part of the body after a local `macro_rules!`: a name that macro
            // wrote means the name as written in its definition.
            if let Some(m) = rib.macro_def {
                if ctxt != SyntaxContext::ROOT && ctxt.outer_expn().data().macro_def == m {
                    ctxt = ctxt.parent();
                }
                continue;
            }
            for &(name, c, local) in rib.bindings.iter().rev() {
                if name == ident.name && c == ctxt {
                    return Some(local);
                }
            }
        }
        None
    }

    fn push_rib(&mut self) {
        self.b().ribs.push(Rib::default());
    }

    fn pop_rib(&mut self) {
        self.b().ribs.pop();
    }

    /// Makes the bindings of the pattern just lowered visible.
    fn commit_bindings(&mut self) {
        let b = self.b();
        if let Some(bindings) = b.pat_bindings.take() {
            let mut list: Vec<_> = bindings.into_iter().collect();
            list.sort_by_key(|(_, l)| l.0);
            let rib = b.ribs.last_mut().unwrap();
            for ((name, ctxt), local) in list {
                rib.bindings.push((name, ctxt, local));
            }
        }
    }

    // ---------------------------------------------------------------------------------------
    // Patterns

    /// A whole pattern: its bindings are collected, then made visible by `commit_bindings`.
    fn lower_pat_top(&mut self, p: &ast::Pat) -> PatId {
        let outer = self.b().pat_bindings.replace(FxHashMap::default());
        // Bindings of an enclosing pattern under construction stay pending; nested top-level
        // patterns don't happen in Rust syntax.
        let _ = outer;
        self.lower_pat(p)
    }

    fn lower_pat(&mut self, p: &ast::Pat) -> PatId {
        use ast::PatKind as K;
        let kind = match &p.kind {
            K::Wild => PatKind::Wild,
            K::Ident(mode, ident, sub) => {
                // A name that resolves to a unit struct, unit variant or constant is a path,
                // unless it binds by `ref`/`mut` or has a subpattern.
                if mode.by_ref == ast::ByRef::No
                    && mode.mutbl == Mutability::Not
                    && sub.is_none()
                    && let Some(res) = self.pat_ident_path_res(*ident)
                {
                    let path = Path {
                        res,
                        segments: vec![PathSegment {
                            ident: *ident,
                            res,
                            args: None,
                        }],
                        span: ident.span,
                    };
                    PatKind::Path(QPath::Resolved(None, path))
                } else {
                    let local = self.bind(
                        *ident,
                        mode.mutbl == Mutability::Mut && mode.by_ref == ast::ByRef::No,
                        p.span,
                    );
                    let sub = sub.as_ref().map(|s| self.lower_pat(s));
                    let mode = match mode.by_ref {
                        ast::ByRef::Yes(m) => BindingMode::Ref {
                            mutable: m == Mutability::Mut,
                        },
                        ast::ByRef::No => BindingMode::Value {
                            mutable: mode.mutbl == Mutability::Mut,
                        },
                    };
                    let id = self.alloc_pat(PatKind::Binding { mode, local, sub }, p.span);
                    self.b().locals[local.index()].pat = id;
                    return id;
                }
            }
            K::Struct(q, path, fields, rest) => {
                let path = self.lower_qpath_body(q.as_deref(), path, Ns::Type);
                let fields = fields
                    .iter()
                    .map(|f| FieldPat {
                        name: f.ident,
                        pat: self.lower_pat(&f.pat),
                    })
                    .collect();
                PatKind::Struct {
                    path,
                    fields,
                    rest: *rest == ast::PatFieldsRest::Rest,
                }
            }
            K::TupleStruct(q, path, pats) => {
                let path = self.lower_qpath_body(q.as_deref(), path, Ns::Value);
                let (pats, rest) = self.lower_pat_seq(pats);
                PatKind::TupleStruct { path, pats, rest }
            }
            K::Or(alts) => PatKind::Or(alts.iter().map(|a| self.lower_pat(a)).collect()),
            K::Path(q, path) => PatKind::Path(self.lower_qpath_body(q.as_deref(), path, Ns::Value)),
            K::Tuple(pats) => {
                let (pats, rest) = self.lower_pat_seq(pats);
                PatKind::Tuple { pats, rest }
            }
            K::Box(p) => PatKind::Box(self.lower_pat(p)),
            K::Deref(p) => PatKind::Deref(self.lower_pat(p)),
            K::Ref(p, m) => PatKind::Ref(self.lower_pat(p), *m),
            K::Expr(e) => PatKind::Lit(self.lower_expr(e)),
            K::Range(lo, hi, end) => PatKind::Range {
                lo: lo.as_ref().map(|e| self.lower_expr(e)),
                hi: hi.as_ref().map(|e| self.lower_expr(e)),
                end: *end,
            },
            K::Slice(pats) => {
                let mut before = Vec::new();
                let mut after = Vec::new();
                let mut rest = None;
                let mut has_rest = false;
                for sp in pats {
                    let is_rest = match &sp.kind {
                        K::Rest => true,
                        K::Ident(_, _, Some(sub)) => matches!(sub.kind, K::Rest),
                        _ => false,
                    };
                    if is_rest && !has_rest {
                        has_rest = true;
                        if let K::Ident(mode, ident, Some(_)) = &sp.kind {
                            let local = self.bind(*ident, mode.mutbl == Mutability::Mut, sp.span);
                            let mode = match mode.by_ref {
                                ast::ByRef::Yes(m) => BindingMode::Ref {
                                    mutable: m == Mutability::Mut,
                                },
                                ast::ByRef::No => BindingMode::Value {
                                    mutable: mode.mutbl == Mutability::Mut,
                                },
                            };
                            let id = self.alloc_pat(
                                PatKind::Binding {
                                    mode,
                                    local,
                                    sub: None,
                                },
                                sp.span,
                            );
                            self.b().locals[local.index()].pat = id;
                            rest = Some(id);
                        }
                        continue;
                    }
                    let id = self.lower_pat(sp);
                    if has_rest {
                        after.push(id)
                    } else {
                        before.push(id)
                    }
                }
                PatKind::Slice {
                    before,
                    rest,
                    after,
                    has_rest,
                }
            }
            K::Rest => {
                self.emit(err(p.span, "`..` patterns are not allowed here"));
                PatKind::Err
            }
            K::Never => PatKind::Never,
            K::Guard(p, _) => return self.lower_pat(p),
            K::Paren(p) => return self.lower_pat(p),
            K::MacCall(_) | K::Err => PatKind::Err,
        };
        self.alloc_pat(kind, p.span)
    }

    fn lower_pat_seq(&mut self, pats: &[P<ast::Pat>]) -> (Vec<PatId>, Option<usize>) {
        let mut out = Vec::new();
        let mut rest = None;
        for (i, p) in pats.iter().enumerate() {
            if matches!(p.kind, ast::PatKind::Rest) {
                rest = Some(i);
                continue;
            }
            out.push(self.lower_pat(p));
        }
        (out, rest)
    }

    /// Is this pattern identifier a path (unit struct/variant, constant)?
    fn pat_ident_path_res(&self, ident: Ident) -> Option<Res> {
        let scope = self.current_scope();
        match self.r.resolve_ident_lexical(ident, Ns::Value, scope) {
            Lookup::Found(b) => match b.res {
                Res::Def(
                    DefKind::Ctor(_, CtorKind::Const)
                    | DefKind::Const
                    | DefKind::AssocConst
                    | DefKind::Static { .. },
                    _,
                ) => Some(b.res),
                _ => None,
            },
            _ => None,
        }
    }

    /// Declares a binding of the pattern being lowered. Or-alternatives share bindings.
    fn bind(&mut self, ident: Ident, mutable: bool, span: Span) -> LocalId {
        let key = (ident.name, ident.span.ctxt.normalize_to_macro_rules());
        if let Some(map) = &self.b().pat_bindings
            && let Some(&l) = map.get(&key)
        {
            return l;
        }
        let local = LocalId(self.b().locals.len() as u32);
        self.b().locals.push(Local {
            name: ident,
            mutable,
            span,
            pat: PatId(u32::MAX),
        });
        if let Some(map) = &mut self.b().pat_bindings {
            map.insert(key, local);
        } else {
            let rib = self.b().ribs.last_mut().unwrap();
            rib.bindings.push((key.0, key.1, local));
        }
        local
    }

    // ---------------------------------------------------------------------------------------
    // Paths in bodies

    pub(crate) fn lower_qpath_body(
        &mut self,
        q: Option<&ast::QSelf>,
        path: &ast::Path,
        ns: Ns,
    ) -> QPath {
        let scope = self.current_scope();
        self.lower_qpath_in(q, path, ns, false, scope, &|_| None)
    }

    fn lower_path_expr(&mut self, q: Option<&ast::QSelf>, path: &ast::Path, span: Span) -> ExprId {
        if q.is_none() && path.segments.len() == 1 && path.segments[0].args.is_none() {
            let ident = path.segments[0].ident;
            if let Some(local) = self.lookup_local(ident) {
                let res = Res::Local(local.0);
                let qpath = QPath::Resolved(
                    None,
                    Path {
                        res,
                        segments: vec![PathSegment {
                            ident,
                            res,
                            args: None,
                        }],
                        span,
                    },
                );
                return self.alloc_expr(ExprKind::Path(qpath), span);
            }
        }
        let qpath = self.lower_qpath_body(q, path, Ns::Value);
        self.alloc_expr(ExprKind::Path(qpath), span)
    }

    fn lang_path(&mut self, name: &str, span: Span) -> ExprId {
        self.alloc_expr(
            ExprKind::Path(QPath::LangItem(Symbol::intern(name), span)),
            span,
        )
    }

    fn local_expr(&mut self, local: LocalId, span: Span) -> ExprId {
        let res = Res::Local(local.0);
        let name = self.b().locals[local.index()].name;
        let qpath = QPath::Resolved(
            None,
            Path {
                res,
                segments: vec![PathSegment {
                    ident: name,
                    res,
                    args: None,
                }],
                span,
            },
        );
        self.alloc_expr(ExprKind::Path(qpath), span)
    }

    // ---------------------------------------------------------------------------------------
    // Blocks and statements

    fn lower_block_expr(&mut self, block: &ast::Block, label: Option<LoopId>) -> ExprId {
        let b = self.lower_block(block);
        self.alloc_expr(ExprKind::Block(b, label), block.span)
    }

    fn lower_block(&mut self, block: &ast::Block) -> Block {
        let scope = (block.id != ast::NodeId::DUMMY).then_some(DefId(block.id.0));
        if let Some(s) = scope {
            self.b().scopes.push(s);
        }
        self.push_rib();
        let mut stmts = Vec::new();
        let mut macro_ribs = 0;
        let mut tail = None;
        let n = block.stmts.len();
        for (i, s) in block.stmts.iter().enumerate() {
            match &s.kind {
                ast::StmtKind::Let(l) => {
                    let ty = l.ty.as_ref().map(|t| self.lower_ty(t));
                    let (init, els) = match &l.kind {
                        ast::LocalKind::Decl => (None, None),
                        ast::LocalKind::Init(e) => (Some(self.lower_expr(e)), None),
                        ast::LocalKind::InitElse(e, b) => {
                            let init = self.lower_expr(e);
                            let els = self.lower_block(b);
                            (Some(init), Some(els))
                        }
                    };
                    // The binding is visible after its initializer: a new rib.
                    let pat = self.lower_pat_top(&l.pat);
                    self.push_rib();
                    self.commit_bindings();
                    stmts.push(Stmt {
                        kind: StmtKind::Let { pat, ty, init, els },
                        span: s.span,
                    });
                }
                ast::StmtKind::Expr(e) if i + 1 == n => tail = Some(self.lower_expr(e)),
                ast::StmtKind::Expr(e) | ast::StmtKind::Semi(e) => {
                    let id = self.lower_expr(e);
                    stmts.push(Stmt {
                        kind: StmtKind::Expr(id),
                        span: s.span,
                    });
                }
                // The marker a body's `macro_rules!` left (see `lookup_local`).
                ast::StmtKind::Item(it)
                    if matches!(it.kind, ast::ItemKind::MacroDef(_))
                        && it.id != ast::NodeId::DUMMY =>
                {
                    self.b().ribs.push(Rib {
                        bindings: Vec::new(),
                        macro_def: Some(it.id.0),
                    });
                    macro_ribs += 1;
                }
                ast::StmtKind::Item(_) | ast::StmtKind::Empty => {}
                ast::StmtKind::MacCall(m) => {
                    // Expansion replaced every macro statement; one left means an error was
                    // reported for it.
                    let _ = m;
                }
            }
        }
        // Pop the block's rib and the ribs `let`s pushed.
        let b = self.b();
        let lets = stmts
            .iter()
            .filter(|s| matches!(s.kind, StmtKind::Let { .. }))
            .count();
        for _ in 0..=lets + macro_ribs {
            b.ribs.pop();
        }
        if scope.is_some() {
            self.b().scopes.pop();
        }
        Block {
            stmts,
            tail,
            unsafe_: block.rules == ast::BlockCheckMode::Unsafe,
            scope,
            span: block.span,
        }
    }

    // ---------------------------------------------------------------------------------------
    // Expressions

    fn lower_exprs(&mut self, es: &[P<ast::Expr>]) -> Vec<ExprId> {
        es.iter().map(|e| self.lower_expr(e)).collect()
    }

    pub(crate) fn lower_expr(&mut self, e: &ast::Expr) -> ExprId {
        use ast::ExprKind as K;
        let span = e.span;
        let kind = match &e.kind {
            K::Lit(l) => ExprKind::Lit(Lit {
                kind: l.kind,
                symbol: l.symbol,
                suffix: l.suffix,
                span: l.span,
            }),
            K::Path(q, p) => return self.lower_path_expr(q.as_deref(), p, span),
            K::Paren(inner) => return self.lower_expr(inner),
            K::Array(es) => ExprKind::Array(self.lower_exprs(es)),
            K::Tup(es) => ExprKind::Tuple(self.lower_exprs(es)),
            K::Repeat(e, count) => {
                let e = self.lower_expr(e);
                ExprKind::Repeat(e, self.lower_const_arg(&count.value))
            }
            K::ConstBlock(c) => ExprKind::ConstBlock(self.lower_expr(&c.value)),
            K::Call(f, args) => {
                let f = self.lower_expr(f);
                ExprKind::Call(f, self.lower_exprs(args))
            }
            K::MethodCall(m) => {
                let receiver = self.lower_expr(&m.receiver);
                let args = self.lower_exprs(&m.args);
                let segment = PathSegment {
                    ident: m.seg.ident,
                    res: Res::Err,
                    args: m
                        .seg
                        .args
                        .as_ref()
                        .map(|a| Box::new(self.lower_generic_args_pub(a))),
                };
                ExprKind::MethodCall {
                    receiver,
                    segment,
                    args,
                }
            }
            K::Binary(op, a, b) => {
                let a = self.lower_expr(a);
                let b = self.lower_expr(b);
                ExprKind::Binary(op.kind, a, b)
            }
            K::Unary(op, a) => ExprKind::Unary(*op, self.lower_expr(a)),
            K::Cast(e, t) => {
                let e = self.lower_expr(e);
                ExprKind::Cast(e, self.lower_ty(t))
            }
            K::Type(e, t) => {
                let e = self.lower_expr(e);
                ExprKind::Type(e, self.lower_ty(t))
            }
            K::Let(p, init, _) => {
                let init = self.lower_expr(init);
                let pat = self.lower_pat_top(p);
                self.commit_bindings();
                ExprKind::Let { pat, init }
            }
            K::If(cond, then, els) => {
                // `let` bindings in the condition are visible in the `then` block only.
                self.push_rib();
                let cond = self.lower_expr(cond);
                let then = self.lower_block_expr(then, None);
                self.pop_rib();
                let els = els.as_ref().map(|e| self.lower_expr(e));
                ExprKind::If { cond, then, els }
            }
            K::While(cond, body, label) => {
                let id = self.new_loop(label.as_ref().map(|l| l.ident), false);
                self.b()
                    .labels
                    .push((label.as_ref().map(|l| label_key(l.ident)), id, false));
                self.push_rib();
                let cond = self.lower_expr(cond);
                let then = self.lower_block_expr(body, None);
                self.pop_rib();
                let brk = self.alloc_expr(
                    ExprKind::Break {
                        target: Some(id),
                        value: None,
                    },
                    span,
                );
                let iff = self.alloc_expr(
                    ExprKind::If {
                        cond,
                        then,
                        els: Some(brk),
                    },
                    span,
                );
                self.b().labels.pop();
                let body = Block {
                    stmts: Vec::new(),
                    tail: Some(iff),
                    unsafe_: false,
                    scope: None,
                    span,
                };
                ExprKind::Loop {
                    body,
                    id,
                    source: LoopSource::While,
                }
            }
            K::Loop(body, label) => {
                let id = self.new_loop(label.as_ref().map(|l| l.ident), false);
                self.b()
                    .labels
                    .push((label.as_ref().map(|l| label_key(l.ident)), id, false));
                let body = self.lower_block(body);
                self.b().labels.pop();
                ExprKind::Loop {
                    body,
                    id,
                    source: LoopSource::Loop,
                }
            }
            K::ForLoop {
                pat,
                iter,
                body,
                label,
                ..
            } => return self.lower_for(pat, iter, body, label.as_ref(), span),
            K::Match(scrutinee, arms, _) => {
                let scrutinee = self.lower_expr(scrutinee);
                let arms = arms.iter().map(|a| self.lower_arm(a)).collect();
                ExprKind::Match {
                    scrutinee,
                    arms,
                    source: MatchSource::Normal,
                }
            }
            K::Block(b, label) => {
                let id = label.as_ref().map(|l| {
                    let id = self.new_loop(Some(l.ident), true);
                    self.b().labels.push((Some(label_key(l.ident)), id, true));
                    id
                });
                let blk = self.lower_block(b);
                if id.is_some() {
                    self.b().labels.pop();
                }
                ExprKind::Block(blk, id)
            }
            K::TryBlock(b) => {
                // `try { … }`: the value goes through `Try::from_output`; `?` breaks here.
                let id = self.new_loop(None, true);
                self.b().try_blocks.push(id);
                let blk = self.lower_block(b);
                self.b().try_blocks.pop();
                let tail_span = b.span;
                let tail = blk
                    .tail
                    .unwrap_or_else(|| self.alloc_expr(ExprKind::Tuple(Vec::new()), tail_span));
                let from_output = self.lang_path("from_output", tail_span);
                let wrapped = self.alloc_expr(ExprKind::Call(from_output, vec![tail]), tail_span);
                let blk = Block {
                    tail: Some(wrapped),
                    ..blk
                };
                ExprKind::Block(blk, Some(id))
            }
            K::Gen(capture, b, kind) => {
                let kind = match kind {
                    ast::GenBlockKind::Async => ClosureKind::Async,
                    _ => ClosureKind::Gen,
                };
                let saved = std::mem::take(&mut self.b().labels);
                let body = self.lower_block_expr(b, None);
                self.b().labels = saved;
                let id = ClosureId(self.b().closures.len() as u32);
                self.b().closures.push(ClosureData {
                    params: Vec::new(),
                    ret: None,
                    body,
                    by_move: matches!(capture, ast::CaptureBy::Value { .. }),
                    kind,
                    span,
                });
                ExprKind::Closure(id)
            }
            K::Closure(c) => {
                self.push_rib();
                let saved_labels = std::mem::take(&mut self.b().labels);
                let mut params = Vec::new();
                for p in &c.fn_decl.inputs {
                    let pat = self.lower_pat_top(&p.pat);
                    self.commit_bindings();
                    let ty = if matches!(p.ty.kind, ast::TyKind::Infer) {
                        None
                    } else {
                        Some(self.lower_ty(&p.ty))
                    };
                    params.push((pat, ty));
                }
                let ret = match &c.fn_decl.output {
                    ast::FnRetTy::Default(_) => None,
                    ast::FnRetTy::Ty(t) => Some(self.lower_ty(t)),
                };
                let body = self.lower_expr(&c.body);
                self.b().labels = saved_labels;
                self.pop_rib();
                let kind = match c.coroutine_kind {
                    Some(ast::CoroutineKind::Async { .. }) => ClosureKind::Async,
                    Some(_) => ClosureKind::Gen,
                    None => ClosureKind::Closure,
                };
                let id = ClosureId(self.b().closures.len() as u32);
                self.b().closures.push(ClosureData {
                    params,
                    ret,
                    body,
                    by_move: matches!(c.capture_clause, ast::CaptureBy::Value { .. }),
                    kind,
                    span,
                });
                ExprKind::Closure(id)
            }
            K::Await(e, _) => ExprKind::Await(self.lower_expr(e)),
            K::Use(e, _) => return self.lower_expr(e),
            K::Assign(lhs, rhs, _) => return self.lower_assign(lhs, rhs, span),
            K::AssignOp(op, a, b) => {
                let a = self.lower_expr(a);
                let b = self.lower_expr(b);
                ExprKind::AssignOp(op.kind, a, b)
            }
            K::Field(e, name) => ExprKind::Field(self.lower_expr(e), *name),
            K::Index(a, b, _) => {
                let a = self.lower_expr(a);
                ExprKind::Index(a, self.lower_expr(b))
            }
            K::Range(lo, hi, limits) => {
                return self.lower_range(lo.as_deref(), hi.as_deref(), *limits, span);
            }
            K::Underscore => {
                self.emit(err(
                    span,
                    "in expressions, `_` can only be used on the left-hand side of an assignment",
                ));
                ExprKind::Err
            }
            K::AddrOf(kind, m, e) => ExprKind::AddrOf(*kind, *m, self.lower_expr(e)),
            K::Break(label, value) => {
                let target = self.loop_target(label.as_ref(), span, false);
                let value = value.as_ref().map(|v| self.lower_expr(v));
                ExprKind::Break { target, value }
            }
            K::Continue(label) => ExprKind::Continue {
                target: self.loop_target(label.as_ref(), span, true),
            },
            K::Ret(e) => ExprKind::Return(e.as_ref().map(|e| self.lower_expr(e))),
            K::Yeet(e) => {
                // `do yeet e` = `return FromResidual::from_residual(Yeet(e))`.
                let v = match e {
                    Some(e) => self.lower_expr(e),
                    None => self.alloc_expr(ExprKind::Tuple(Vec::new()), span),
                };
                let yeet = self.lang_path("Yeet", span);
                let wrapped = self.alloc_expr(ExprKind::Call(yeet, vec![v]), span);
                let from_residual = self.lang_path("from_residual", span);
                let call = self.alloc_expr(ExprKind::Call(from_residual, vec![wrapped]), span);
                ExprKind::Return(Some(call))
            }
            K::Become(e) => ExprKind::Become(self.lower_expr(e)),
            K::Yield(e) => ExprKind::Yield(e.as_ref().map(|e| self.lower_expr(e))),
            K::Try(e) => return self.lower_try(e, span),
            K::OffsetOf(t, fields) => ExprKind::OffsetOf(self.lower_ty(t), fields.clone()),
            K::Struct(s) => {
                let path = self.lower_qpath_body(s.qself.as_deref(), &s.path, Ns::Type);
                let fields = s
                    .fields
                    .iter()
                    .map(|f| ExprField {
                        name: f.ident,
                        expr: self.lower_expr(&f.expr),
                        span: f.span,
                    })
                    .collect();
                let tail = match &s.rest {
                    ast::StructRest::Base(b) => StructTail::Base(self.lower_expr(b)),
                    ast::StructRest::Rest(_) => StructTail::Defaults,
                    ast::StructRest::None => StructTail::None,
                };
                ExprKind::Struct { path, fields, tail }
            }
            K::FormatArgs(f) => return self.lower_format_args(f, span),
            K::InlineAsm(a) => ExprKind::InlineAsm(a.clone()),
            K::MacCall(m) => {
                // Left over only after an expansion error.
                let _ = m;
                ExprKind::Err
            }
            K::Err => ExprKind::Err,
        };
        self.alloc_expr(kind, span)
    }

    fn lower_arm(&mut self, a: &ast::Arm) -> Arm {
        self.push_rib();
        let pat = self.lower_pat_top(&a.pat);
        self.commit_bindings();
        let guard = a.guard.as_ref().map(|g| self.lower_expr(g));
        let body = match &a.body {
            Some(b) => self.lower_expr(b),
            None => self.alloc_expr(ExprKind::Err, a.span),
        };
        self.pop_rib();
        Arm {
            pat,
            guard,
            body,
            span: a.span,
        }
    }

    /// The loop or labeled block a `break`/`continue` refers to.
    fn loop_target(
        &mut self,
        label: Option<&ast::Label>,
        span: Span,
        is_continue: bool,
    ) -> Option<LoopId> {
        let labels = &self.body_stack.last().unwrap().labels;
        match label {
            Some(l) => {
                let key = label_key(l.ident);
                for &(name, id, is_block) in labels.iter().rev() {
                    if name == Some(key) {
                        if is_continue && is_block {
                            self.emit(
                                err(span, "`continue` pointing to a labeled block").code("E0696"),
                            );
                            return None;
                        }
                        return Some(id);
                    }
                }
                self.emit(
                    err(
                        l.ident.span,
                        format!("use of undeclared label `{}`", l.ident),
                    )
                    .code("E0426"),
                );
                None
            }
            None => {
                for &(_, id, is_block) in labels.iter().rev() {
                    if !is_block {
                        return Some(id);
                    }
                }
                let what = if is_continue { "continue" } else { "break" };
                self.emit(err(span, format!("`{what}` outside of a loop")).code("E0268"));
                None
            }
        }
    }

    /// `for pat in iter body` →
    /// `match IntoIterator::into_iter(iter) { mut it => loop { match Iterator::next(&mut it)
    /// { None => break, Some(pat) => body } } }`
    fn lower_for(
        &mut self,
        pat: &ast::Pat,
        iter: &ast::Expr,
        body: &ast::Block,
        label: Option<&ast::Label>,
        span: Span,
    ) -> ExprId {
        let head = self.lower_expr(iter);
        let into_iter = self.lang_path("into_iter", iter.span);
        let head = self.alloc_expr(ExprKind::Call(into_iter, vec![head]), iter.span);
        let (it_local, it_pat) = self.fresh_local("iter", true, iter.span);
        let id = self.new_loop(label.map(|l| l.ident), false);
        self.b()
            .labels
            .push((label.map(|l| label_key(l.ident)), id, false));

        let it_ref_inner = self.local_expr(it_local, iter.span);
        let it_ref = self.alloc_expr(
            ExprKind::AddrOf(BorrowKind::Ref, Mutability::Mut, it_ref_inner),
            iter.span,
        );
        let next = self.lang_path("next", iter.span);
        let next_call = self.alloc_expr(ExprKind::Call(next, vec![it_ref]), iter.span);

        let none_pat = self.alloc_pat(
            PatKind::Path(QPath::LangItem(Symbol::intern("None"), span)),
            span,
        );
        let brk = self.alloc_expr(
            ExprKind::Break {
                target: Some(id),
                value: None,
            },
            span,
        );
        let none_arm = Arm {
            pat: none_pat,
            guard: None,
            body: brk,
            span,
        };

        self.push_rib();
        let user_pat = self.lower_pat_top(pat);
        self.commit_bindings();
        let some_pat = self.alloc_pat(
            PatKind::TupleStruct {
                path: QPath::LangItem(Symbol::intern("Some"), span),
                pats: vec![user_pat],
                rest: None,
            },
            pat.span,
        );
        let body_expr = self.lower_block_expr(body, None);
        self.pop_rib();
        let some_arm = Arm {
            pat: some_pat,
            guard: None,
            body: body_expr,
            span,
        };
        self.b().labels.pop();

        let inner = self.alloc_expr(
            ExprKind::Match {
                scrutinee: next_call,
                arms: vec![none_arm, some_arm],
                source: MatchSource::ForLoop,
            },
            span,
        );
        let loop_body = Block {
            stmts: vec![Stmt {
                kind: StmtKind::Expr(inner),
                span,
            }],
            tail: None,
            unsafe_: false,
            scope: None,
            span,
        };
        let lp = self.alloc_expr(
            ExprKind::Loop {
                body: loop_body,
                id,
                source: LoopSource::ForLoop,
            },
            span,
        );
        let arm = Arm {
            pat: it_pat,
            guard: None,
            body: lp,
            span,
        };
        self.alloc_expr(
            ExprKind::Match {
                scrutinee: head,
                arms: vec![arm],
                source: MatchSource::ForLoop,
            },
            span,
        )
    }

    /// `e?` → `match Try::branch(e) { Continue(v) => v, Break(r) => return
    /// FromResidual::from_residual(r) }` (in a `try` block: break to it instead).
    fn lower_try(&mut self, e: &ast::Expr, span: Span) -> ExprId {
        let inner = self.lower_expr(e);
        let branch = self.lang_path("branch", span);
        let call = self.alloc_expr(ExprKind::Call(branch, vec![inner]), span);
        let (v, v_pat) = self.fresh_local("val", false, span);
        let cont = self.alloc_pat(
            PatKind::TupleStruct {
                path: QPath::LangItem(Symbol::intern("Continue"), span),
                pats: vec![v_pat],
                rest: None,
            },
            span,
        );
        let v_expr = self.local_expr(v, span);
        let (r, r_pat) = self.fresh_local("residual", false, span);
        let brk = self.alloc_pat(
            PatKind::TupleStruct {
                path: QPath::LangItem(Symbol::intern("Break"), span),
                pats: vec![r_pat],
                rest: None,
            },
            span,
        );
        let r_expr = self.local_expr(r, span);
        let from_residual = self.lang_path("from_residual", span);
        let converted = self.alloc_expr(ExprKind::Call(from_residual, vec![r_expr]), span);
        let exit = match self.b().try_blocks.last().copied() {
            Some(target) => self.alloc_expr(
                ExprKind::Break {
                    target: Some(target),
                    value: Some(converted),
                },
                span,
            ),
            None => self.alloc_expr(ExprKind::Return(Some(converted)), span),
        };
        let arms = vec![
            Arm {
                pat: cont,
                guard: None,
                body: v_expr,
                span,
            },
            Arm {
                pat: brk,
                guard: None,
                body: exit,
                span,
            },
        ];
        self.alloc_expr(
            ExprKind::Match {
                scrutinee: call,
                arms,
                source: MatchSource::Try,
            },
            span,
        )
    }

    /// Ranges are the `core::ops` range types.
    fn lower_range(
        &mut self,
        lo: Option<&ast::Expr>,
        hi: Option<&ast::Expr>,
        limits: ast::RangeLimits,
        span: Span,
    ) -> ExprId {
        let lo = lo.map(|e| self.lower_expr(e));
        let hi = hi.map(|e| self.lower_expr(e));
        let field = |name: &str, expr: ExprId| ExprField {
            name: Ident::new(Symbol::intern(name), span),
            expr,
            span,
        };
        let (lang, fields) = match (lo, hi, limits) {
            (Some(lo), Some(hi), ast::RangeLimits::Closed) => {
                let new = self.lang_path("range_inclusive_new", span);
                return self.alloc_expr(ExprKind::Call(new, vec![lo, hi]), span);
            }
            (Some(lo), Some(hi), ast::RangeLimits::HalfOpen) => {
                ("Range", vec![field("start", lo), field("end", hi)])
            }
            (Some(lo), None, _) => ("RangeFrom", vec![field("start", lo)]),
            (None, Some(hi), ast::RangeLimits::HalfOpen) => ("RangeTo", vec![field("end", hi)]),
            (None, Some(hi), ast::RangeLimits::Closed) => {
                ("RangeToInclusive", vec![field("end", hi)])
            }
            (None, None, _) => ("RangeFull", Vec::new()),
        };
        let path = QPath::LangItem(Symbol::intern(lang), span);
        if fields.is_empty() {
            return self.alloc_expr(ExprKind::Path(path), span);
        }
        self.alloc_expr(
            ExprKind::Struct {
                path,
                fields,
                tail: StructTail::None,
            },
            span,
        )
    }

    /// `a = b`, and destructuring assignments: `(a, b) = (b, a)` becomes
    /// `{ let (x, y) = (b, a); a = x; b = y; }`.
    fn lower_assign(&mut self, lhs: &ast::Expr, rhs: &ast::Expr, span: Span) -> ExprId {
        let destructuring = matches!(
            strip_parens(lhs).kind,
            ast::ExprKind::Tup(_)
                | ast::ExprKind::Array(_)
                | ast::ExprKind::Underscore
                | ast::ExprKind::Struct(_)
        ) || matches!(&strip_parens(lhs).kind, ast::ExprKind::Call(f, _) if matches!(f.kind, ast::ExprKind::Path(..)));
        if !destructuring {
            let l = self.lower_expr(lhs);
            let r = self.lower_expr(rhs);
            return self.alloc_expr(ExprKind::Assign(l, r), span);
        }
        let r = self.lower_expr(rhs);
        let mut assigns: Vec<(ExprId, LocalId, Span)> = Vec::new();
        self.b().pat_bindings = Some(FxHashMap::default());
        let pat = self.destructure_pat(lhs, &mut assigns);
        self.b().pat_bindings = None;
        let mut stmts = vec![Stmt {
            kind: StmtKind::Let {
                pat,
                ty: None,
                init: Some(r),
                els: None,
            },
            span,
        }];
        for (target, local, sp) in assigns {
            let value = self.local_expr(local, sp);
            let a = self.alloc_expr(ExprKind::Assign(target, value), sp);
            stmts.push(Stmt {
                kind: StmtKind::Expr(a),
                span: sp,
            });
        }
        let block = Block {
            stmts,
            tail: None,
            unsafe_: false,
            scope: None,
            span,
        };
        self.alloc_expr(ExprKind::Block(block, None), span)
    }

    fn destructure_pat(
        &mut self,
        e: &ast::Expr,
        assigns: &mut Vec<(ExprId, LocalId, Span)>,
    ) -> PatId {
        let e = strip_parens(e);
        let kind = match &e.kind {
            ast::ExprKind::Underscore => PatKind::Wild,
            ast::ExprKind::Tup(es) => {
                let mut pats = Vec::new();
                let mut rest = None;
                for (i, sub) in es.iter().enumerate() {
                    if matches!(sub.kind, ast::ExprKind::Range(None, None, _)) {
                        rest = Some(i);
                        continue;
                    }
                    pats.push(self.destructure_pat(sub, assigns));
                }
                PatKind::Tuple { pats, rest }
            }
            ast::ExprKind::Array(es) => {
                let mut before = Vec::new();
                let mut after = Vec::new();
                let mut has_rest = false;
                for sub in es {
                    if matches!(sub.kind, ast::ExprKind::Range(None, None, _)) {
                        has_rest = true;
                        continue;
                    }
                    let p = self.destructure_pat(sub, assigns);
                    if has_rest {
                        after.push(p)
                    } else {
                        before.push(p)
                    }
                }
                PatKind::Slice {
                    before,
                    rest: None,
                    after,
                    has_rest,
                }
            }
            ast::ExprKind::Call(f, args) => {
                let ast::ExprKind::Path(q, p) = &f.kind else {
                    unreachable!()
                };
                let path = self.lower_qpath_body(q.as_deref(), p, Ns::Value);
                let mut pats = Vec::new();
                let mut rest = None;
                for (i, sub) in args.iter().enumerate() {
                    if matches!(sub.kind, ast::ExprKind::Range(None, None, _)) {
                        rest = Some(i);
                        continue;
                    }
                    pats.push(self.destructure_pat(sub, assigns));
                }
                PatKind::TupleStruct { path, pats, rest }
            }
            ast::ExprKind::Struct(s) => {
                let path = self.lower_qpath_body(s.qself.as_deref(), &s.path, Ns::Type);
                let fields = s
                    .fields
                    .iter()
                    .map(|f| FieldPat {
                        name: f.ident,
                        pat: self.destructure_pat(&f.expr, assigns),
                    })
                    .collect();
                PatKind::Struct {
                    path,
                    fields,
                    rest: matches!(s.rest, ast::StructRest::Rest(_)),
                }
            }
            _ => {
                // A place: bind a temporary and assign it after.
                let target = self.lower_expr(e);
                let n = assigns.len();
                let (local, pat) = self.fresh_local(&format!("lhs{n}"), false, e.span);
                assigns.push((target, local, e.span));
                return pat;
            }
        };
        self.alloc_pat(kind, e.span)
    }

    // ---------------------------------------------------------------------------------------
    // Helpers used by item lowering

    pub(crate) fn lower_generic_args_pub(&mut self, args: &ast::GenericArgs) -> GenericArgs {
        self.lower_generic_args(args)
    }

    pub(crate) fn body_scope(&self) -> Option<DefId> {
        self.body_stack
            .last()
            .and_then(|b| b.scopes.last().copied())
    }

    fn lower_format_args(&mut self, f: &ast::FormatArgs, span: Span) -> ExprId {
        let template = strip_block(&f.template);
        let (text, raw) = match &template.kind {
            ast::ExprKind::Lit(l) if matches!(l.kind, hyprc_syntax::token::LitKind::Str) => {
                (l.symbol.as_str().to_string(), false)
            }
            ast::ExprKind::Lit(l) if matches!(l.kind, hyprc_syntax::token::LitKind::StrRaw(_)) => {
                (l.symbol.as_str().to_string(), true)
            }
            _ => {
                self.emit(err(
                    template.span,
                    "format argument must be a string literal",
                ));
                return self.alloc_expr(ExprKind::Err, span);
            }
        };
        let text = if raw {
            text
        } else {
            hyprc_resolve::macros::builtin::unescape_str(&text, false).unwrap_or(text)
        };
        let mut args: Vec<ExprId> = f.args.iter().map(|a| self.lower_expr(&a.expr)).collect();
        let names: Vec<Option<Symbol>> = f.args.iter().map(|a| a.name.map(|n| n.name)).collect();
        let mut extra_names: Vec<Symbol> = Vec::new();
        let parsed = super::format::parse(&text, f.newline);
        let mut pieces = Vec::new();
        let mut next_positional = 0usize;
        let mut resolve_arg =
            |this: &mut Self, arg: &super::format::ArgRef, args: &mut Vec<ExprId>| -> usize {
                match arg {
                    super::format::ArgRef::Next => {
                        let i = next_positional;
                        next_positional += 1;
                        i
                    }
                    super::format::ArgRef::Index(i) => *i,
                    super::format::ArgRef::Name(name) => {
                        if let Some(i) = names.iter().position(|n| *n == Some(*name)) {
                            return i;
                        }
                        if let Some(i) = extra_names.iter().position(|n| n == name) {
                            return f.args.len() + i;
                        }
                        // `{x}`: a captured variable, named where the string was written.
                        let path = ast::Path::from_ident(Ident::new(*name, template.span));
                        let e = this.lower_path_expr(None, &path, template.span);
                        args.push(e);
                        extra_names.push(*name);
                        args.len() - 1
                    }
                }
            };
        for piece in parsed {
            match piece {
                super::format::Piece::Lit(s) => {
                    pieces.push(FormatPiece::Literal(Symbol::intern(&s)))
                }
                super::format::Piece::Arg {
                    arg,
                    trait_,
                    spec,
                    width,
                    precision,
                } => {
                    let arg = resolve_arg(self, &arg, &mut args);
                    let mut spec = spec;
                    spec.width = width.map(|w| match w {
                        super::format::Count::Lit(n) => FormatCount::Literal(n),
                        super::format::Count::Arg(a) => {
                            FormatCount::Arg(resolve_arg(self, &a, &mut args))
                        }
                    });
                    spec.precision = precision.map(|p| match p {
                        super::format::Count::Lit(n) => FormatCount::Literal(n),
                        super::format::Count::Arg(a) => {
                            FormatCount::Arg(resolve_arg(self, &a, &mut args))
                        }
                    });
                    pieces.push(FormatPiece::Placeholder { arg, trait_, spec });
                }
                super::format::Piece::Error(msg) => {
                    self.emit(err(template.span, format!("invalid format string: {msg}")));
                }
            }
        }
        self.alloc_expr(
            ExprKind::FormatArgs(Box::new(FormatArgs {
                template: pieces,
                args,
                span,
            })),
            span,
        )
    }
}

fn strip_parens(e: &ast::Expr) -> &ast::Expr {
    match &e.kind {
        ast::ExprKind::Paren(inner) => strip_parens(inner),
        _ => e,
    }
}

fn label_key(ident: Ident) -> (Symbol, SyntaxContext) {
    (ident.name, ident.span.ctxt.normalize_to_macro_rules())
}

type P<T> = Box<T>;
