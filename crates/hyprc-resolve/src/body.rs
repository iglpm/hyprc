//! Phase 2: macros inside bodies, signatures and types; items inside blocks.
//!
//! Every definition's syntax is walked once, mutably: `#[cfg]` removes statements, fields,
//! arms and parameters; macro calls are expanded in place (recursively, in source order,
//! with the `macro_rules!` scope threaded through); blocks that contain items get a scope
//! of their own (a `Block` definition), and their items are collected like module items.

use crate::cfg;
use crate::expand::MacroLookup;
use crate::{DefId, DefKind, FragmentKind, ItemNode, Resolver, ScopeId, TextualScope, Vis};
use hyprc_span::hygiene::ExpnId;
use hyprc_span::{Diag, Edition, Span};
use hyprc_syntax::Parser;
use hyprc_syntax::ast::*;
use hyprc_syntax::token::{Token, TokenKind};

/// What a macro call in a body expands into.
enum Frag {
    Expr,
    Stmts,
    Pat,
    Ty,
}

struct BodyExpander<'r, 's> {
    r: &'r mut Resolver<'s>,
    /// The scope paths resolve in: the innermost block with items, or the module.
    module: DefId,
    /// The textual `macro_rules!` scope.
    scope: ScopeId,
    /// The definition whose syntax this is (blocks with items become its children).
    owner: DefId,
    edition: Edition,
    depth: u32,
}

impl Resolver<'_> {
    pub(crate) fn expand_bodies(&mut self) {
        let mut i = 0;
        // Definitions created while expanding (items in blocks) are walked too.
        while i < self.defs.len() {
            let def = DefId(i as u32);
            i += 1;
            let node = std::mem::replace(&mut self.nodes[def.0 as usize], ItemNode::None);
            let node = match node {
                ItemNode::None => continue,
                node => node,
            };
            let module = self.scope_of(def);
            let scope = self
                .item_scopes
                .get(&def)
                .copied()
                .unwrap_or(ScopeId::EMPTY);
            let edition = self.edition_of(def);
            let mut ex = BodyExpander {
                module,
                scope,
                owner: def,
                edition,
                depth: 0,
                r: self,
            };
            let node = match node {
                ItemNode::Item(mut item) => {
                    ex.item(&mut item);
                    ItemNode::Item(item)
                }
                ItemNode::Assoc(mut item) => {
                    ex.assoc_item(&mut item);
                    ItemNode::Assoc(item)
                }
                ItemNode::Foreign(mut item) => {
                    ex.foreign_item(&mut item);
                    ItemNode::Foreign(item)
                }
                ItemNode::None => unreachable!(),
            };
            self.nodes[def.0 as usize] = node;
        }
        // Imports in blocks may have been left for the end.
        while self.resolve_imports_round() {}
    }
}

impl BodyExpander<'_, '_> {
    fn process_attrs(&self, attrs: &mut Vec<Attribute>) -> bool {
        let ctx = self.r.active_cfg_context();
        cfg::process_attrs_ctx(&ctx, &self.r.sess.dcx, self.edition, attrs)
    }

    fn keep(&mut self, attrs: &mut Vec<Attribute>) -> bool {
        self.process_attrs(attrs)
    }

    // ---------------------------------------------------------------------------------------
    // Macro calls

    /// Expands a call in a body: its tokens, ready to parse. `None` after reporting an error.
    fn expand_call(&mut self, mac: &MacCall) -> Option<(Vec<Token>, Edition, ExpnId)> {
        let def = match self
            .r
            .resolve_macro_path(&mac.path, self.module, self.scope, true)
        {
            MacroLookup::Found(d) => d,
            _ => {
                let name = mac
                    .path
                    .segments
                    .iter()
                    .map(|s| s.ident.as_str())
                    .collect::<Vec<_>>()
                    .join("::");
                self.r.sess.dcx.emit(
                    Diag::error(format!("cannot find macro `{name}` in this scope"))
                        .span(mac.path.span, ""),
                );
                return None;
            }
        };
        if !matches!(self.r.def_kind(def), DefKind::Macro(_)) {
            self.r.sess.dcx.emit(
                Diag::error(format!(
                    "expected macro, found {}",
                    self.r.def_kind(def).descr()
                ))
                .span(mac.path.span, ""),
            );
            return None;
        }
        self.depth += 1;
        if self.depth > 256 {
            self.r.sess.dcx.emit(
                Diag::error("recursion limit reached while expanding macros")
                    .span(mac.path.span, "")
                    .help("consider increasing the recursion limit by adding a `#![recursion_limit = \"512\"]` attribute"),
            );
            self.depth -= 1;
            return None;
        }
        let parent = mac.path.span.ctxt.outer_expn();
        let call_site = mac.path.span.to(mac.args.close);
        let expn = self.r.new_expansion(def, parent, call_site);
        let (_, _, edition, _) = self.r.macro_impl(def);
        let expansion =
            self.r
                .expand_bang(def, mac, expn, self.module, self.scope, FragmentKind::Items);
        match expansion {
            Ok(tokens) => {
                if std::env::var_os("HYPRC_DEBUG_MACROS").is_some() {
                    eprintln!(
                        "hyprc: {}! => {}",
                        mac.path
                            .segments
                            .iter()
                            .map(|segment| segment.ident.as_str())
                            .collect::<Vec<_>>()
                            .join("::"),
                        crate::macros::builtin::tokens_to_string(&tokens)
                    );
                }
                Some((tokens, edition, expn))
            }
            Err(d) => {
                self.r.sess.dcx.emit(d);
                self.depth -= 1;
                None
            }
        }
    }

    /// Parses an expansion as an expression, statements, pattern or type.
    fn parse_frag(
        &mut self,
        mut tokens: Vec<Token>,
        edition: Edition,
        span: Span,
        frag: Frag,
    ) -> Option<FragOut> {
        tokens.push(Token::new(TokenKind::Eof, span.shrink_to_hi()));
        let dcx = &self.r.sess.dcx;
        let mut p = Parser::new(&tokens, edition, dcx);
        let out = match frag {
            Frag::Stmts => Some(FragOut::Stmts(p.parse_stmts_fragment())),
            Frag::Expr => match p.parse_expr() {
                Ok(e) => Some(FragOut::Expr(e)),
                Err(e) => {
                    p.emit(e);
                    None
                }
            },
            Frag::Pat => match p.parse_pat_allow_top_alt() {
                Ok(e) => Some(FragOut::Pat(e)),
                Err(e) => {
                    p.emit(e);
                    None
                }
            },
            Frag::Ty => match p.parse_ty() {
                Ok(e) => Some(FragOut::Ty(e)),
                Err(e) => {
                    p.emit(e);
                    None
                }
            },
        };
        if !matches!(out, Some(FragOut::Stmts(_)) | None) && !p.check(TokenKind::Eof) {
            let what = Parser::describe_token(&p.token);
            dcx.emit(
                Diag::error(format!(
                    "macro expansion ignores {what} and any tokens following"
                ))
                .span(p.token.span, "")
                .label(span, "caused by the macro expansion here"),
            );
        }
        out
    }

    // ---------------------------------------------------------------------------------------
    // Items

    fn item(&mut self, item: &mut Item) {
        match &mut item.kind {
            ItemKind::Fn(f) => self.fn_(f),
            ItemKind::Const(c) => {
                self.generics(&mut c.generics);
                self.ty(&mut c.ty);
                if let Some(e) = &mut c.expr {
                    self.expr(e);
                }
            }
            ItemKind::Static(s) => {
                self.ty(&mut s.ty);
                if let Some(e) = &mut s.expr {
                    self.expr(e);
                }
            }
            ItemKind::Struct(data, g) | ItemKind::Union(data, g) => {
                self.generics(g);
                self.variant_data(data);
            }
            ItemKind::Enum(def, g) => {
                self.generics(g);
                for v in &mut def.variants {
                    self.variant_data(&mut v.data);
                    if let Some(d) = &mut v.disr_expr {
                        self.expr(&mut d.value);
                    }
                }
            }
            ItemKind::TyAlias(t) => self.ty_alias(t),
            ItemKind::Trait(t) => {
                self.generics(&mut t.generics);
                self.bounds(&mut t.bounds);
            }
            ItemKind::TraitAlias(g, b) => {
                self.generics(g);
                self.bounds(b);
            }
            ItemKind::Impl(imp) => {
                self.generics(&mut imp.generics);
                if let Some(t) = &mut imp.of_trait {
                    self.path(&mut t.path);
                }
                self.ty(&mut imp.self_ty);
            }
            ItemKind::ExternCrate(_)
            | ItemKind::Use(_)
            | ItemKind::Mod(..)
            | ItemKind::ForeignMod(_)
            | ItemKind::MacCall(_)
            | ItemKind::MacroDef(_)
            | ItemKind::GlobalAsm(_) => {}
        }
    }

    fn assoc_item(&mut self, item: &mut AssocItem) {
        match &mut item.kind {
            AssocItemKind::Fn(f) => self.fn_(f),
            AssocItemKind::Const(c) => {
                self.generics(&mut c.generics);
                self.ty(&mut c.ty);
                if let Some(e) = &mut c.expr {
                    self.expr(e);
                }
            }
            AssocItemKind::Type(t) => self.ty_alias(t),
            AssocItemKind::MacCall(_) => {}
        }
    }

    fn foreign_item(&mut self, item: &mut ForeignItem) {
        match &mut item.kind {
            ForeignItemKind::Fn(f) => self.fn_(f),
            ForeignItemKind::Static(s) => self.ty(&mut s.ty),
            ForeignItemKind::TyAlias(t) => self.ty_alias(t),
            ForeignItemKind::MacCall(_) => {}
        }
    }

    fn fn_(&mut self, f: &mut Fn) {
        self.generics(&mut f.generics);
        self.fn_decl(&mut f.sig.decl);
        if let Some(body) = &mut f.body {
            self.block(body);
        }
    }

    fn fn_decl(&mut self, decl: &mut FnDecl) {
        decl.inputs.retain_mut(|p| self.process_attrs(&mut p.attrs));
        for p in &mut decl.inputs {
            self.pat(&mut p.pat);
            self.ty(&mut p.ty);
        }
        if let FnRetTy::Ty(t) = &mut decl.output {
            self.ty(t);
        }
    }

    fn ty_alias(&mut self, t: &mut TyAlias) {
        self.generics(&mut t.generics);
        self.bounds(&mut t.bounds);
        if let Some(ty) = &mut t.ty {
            self.ty(ty);
        }
        self.where_clause(&mut t.after_where);
    }

    fn variant_data(&mut self, data: &mut VariantData) {
        match data {
            VariantData::Struct { fields } | VariantData::Tuple(fields, _) => {
                for f in fields {
                    self.ty(&mut f.ty);
                    if let Some(d) = &mut f.default {
                        self.expr(&mut d.value);
                    }
                }
            }
            VariantData::Unit(_) => {}
        }
    }

    fn generics(&mut self, g: &mut Generics) {
        g.params.retain_mut(|p| self.process_attrs(&mut p.attrs));
        for p in &mut g.params {
            self.bounds(&mut p.bounds);
            match &mut p.kind {
                GenericParamKind::Lifetime => {}
                GenericParamKind::Type { default } => {
                    if let Some(t) = default {
                        self.ty(t);
                    }
                }
                GenericParamKind::Const { ty, default } => {
                    self.ty(ty);
                    if let Some(d) = default {
                        self.expr(&mut d.value);
                    }
                }
            }
        }
        self.where_clause(&mut g.where_clause);
    }

    fn where_clause(&mut self, w: &mut WhereClause) {
        w.predicates
            .retain_mut(|p| self.process_attrs(&mut p.attrs));
        for p in &mut w.predicates {
            match &mut p.kind {
                WherePredicateKind::Bound {
                    bound_generic_params,
                    bounded_ty,
                    bounds,
                } => {
                    for gp in bound_generic_params {
                        self.bounds(&mut gp.bounds);
                    }
                    self.ty(bounded_ty);
                    self.bounds(bounds);
                }
                WherePredicateKind::Region { .. } => {}
                WherePredicateKind::Eq { lhs_ty, rhs_ty } => {
                    self.ty(lhs_ty);
                    self.ty(rhs_ty);
                }
            }
        }
    }

    fn bounds(&mut self, bounds: &mut GenericBounds) {
        for b in bounds {
            if let GenericBound::Trait(p) = b {
                for gp in &mut p.bound_generic_params {
                    self.bounds(&mut gp.bounds);
                }
                self.path(&mut p.trait_ref.path);
            }
        }
    }

    fn path(&mut self, path: &mut Path) {
        for seg in &mut path.segments {
            if let Some(args) = &mut seg.args {
                self.generic_args(args);
            }
        }
    }

    fn generic_args(&mut self, args: &mut GenericArgs) {
        match args {
            GenericArgs::AngleBracketed { args, .. } => {
                for a in args {
                    match a {
                        AngleBracketedArg::Arg(GenericArg::Type(t)) => self.ty(t),
                        AngleBracketedArg::Arg(GenericArg::Const(c)) => self.expr(&mut c.value),
                        AngleBracketedArg::Arg(GenericArg::Lifetime(_)) => {}
                        AngleBracketedArg::Constraint(c) => {
                            if let Some(g) = &mut c.gen_args {
                                self.generic_args(g);
                            }
                            match &mut c.kind {
                                AssocItemConstraintKind::Equality(Term::Ty(t)) => self.ty(t),
                                AssocItemConstraintKind::Equality(Term::Const(c)) => {
                                    self.expr(&mut c.value)
                                }
                                AssocItemConstraintKind::Bound(b) => self.bounds(b),
                            }
                        }
                    }
                }
            }
            GenericArgs::Parenthesized { inputs, output, .. } => {
                for t in inputs {
                    self.ty(t);
                }
                if let FnRetTy::Ty(t) = output {
                    self.ty(t);
                }
            }
            GenericArgs::ParenthesizedElided(_) => {}
        }
    }

    fn qself(&mut self, q: &mut Option<P<QSelf>>) {
        if let Some(q) = q {
            self.ty(&mut q.ty);
        }
    }

    // ---------------------------------------------------------------------------------------
    // Types and patterns

    fn ty(&mut self, ty: &mut P<Ty>) {
        if let TyKind::MacCall(mac) = &ty.kind {
            let mac = mac.clone();
            if let Some((tokens, edition, expn)) = self.expand_call(&mac) {
                let span = ty.span;
                if let Some(FragOut::Ty(new)) = self.parse_frag(tokens, edition, span, Frag::Ty) {
                    *ty = new;
                    let _ = expn;
                    self.ty(ty);
                }
                self.depth -= 1;
            } else {
                ty.kind = TyKind::Err;
            }
            return;
        }
        match &mut ty.kind {
            TyKind::Slice(t) | TyKind::Paren(t) => self.ty(t),
            TyKind::Array(t, len) => {
                self.ty(t);
                self.expr(&mut len.value);
            }
            TyKind::Ptr(m) | TyKind::Ref(_, m) | TyKind::PinnedRef(_, m) => self.ty(&mut m.ty),
            TyKind::BareFn(f) => self.fn_decl(&mut f.decl),
            TyKind::UnsafeBinder(b) => self.ty(&mut b.inner_ty),
            TyKind::Tup(ts) => {
                for t in ts {
                    self.ty(t);
                }
            }
            TyKind::Path(q, p) => {
                self.qself(q);
                self.path(p);
            }
            TyKind::TraitObject(b, _) | TyKind::ImplTrait(_, b) => self.bounds(b),
            TyKind::Typeof(c) => self.expr(&mut c.value),
            TyKind::Pat(t, p) => {
                self.ty(t);
                self.ty_pat(p);
            }
            _ => {}
        }
    }

    fn ty_pat(&mut self, p: &mut hyprc_syntax::ast::TyPat) {
        match &mut p.kind {
            hyprc_syntax::ast::TyPatKind::Range(start, end, _) => {
                for c in [start, end].into_iter().flatten() {
                    self.expr(&mut c.value);
                }
            }
            hyprc_syntax::ast::TyPatKind::Or(alts) => {
                for a in alts {
                    self.ty_pat(a);
                }
            }
            hyprc_syntax::ast::TyPatKind::NotNull | hyprc_syntax::ast::TyPatKind::Err => {}
        }
    }

    fn pat(&mut self, pat: &mut P<Pat>) {
        if let PatKind::MacCall(mac) = &pat.kind {
            let mac = mac.clone();
            if let Some((tokens, edition, _)) = self.expand_call(&mac) {
                let span = pat.span;
                if let Some(FragOut::Pat(new)) = self.parse_frag(tokens, edition, span, Frag::Pat) {
                    *pat = new;
                    self.pat(pat);
                }
                self.depth -= 1;
            } else {
                pat.kind = PatKind::Err;
            }
            return;
        }
        match &mut pat.kind {
            PatKind::Ident(_, _, Some(p))
            | PatKind::Box(p)
            | PatKind::Deref(p)
            | PatKind::Ref(p, _)
            | PatKind::Paren(p) => self.pat(p),
            PatKind::Struct(q, path, fields, _) => {
                self.qself(q);
                self.path(path);
                fields.retain_mut(|f| self.process_attrs(&mut f.attrs));
                for f in fields {
                    self.pat(&mut f.pat);
                }
            }
            PatKind::TupleStruct(q, path, ps) => {
                self.qself(q);
                self.path(path);
                for p in ps {
                    self.pat(p);
                }
            }
            PatKind::Or(ps) | PatKind::Tuple(ps) | PatKind::Slice(ps) => {
                for p in ps {
                    self.pat(p);
                }
            }
            PatKind::Path(q, path) => {
                self.qself(q);
                self.path(path);
            }
            PatKind::Expr(e) => self.expr(e),
            PatKind::Range(a, b, _) => {
                if let Some(a) = a {
                    self.expr(a);
                }
                if let Some(b) = b {
                    self.expr(b);
                }
            }
            PatKind::Guard(p, e) => {
                self.pat(p);
                self.expr(e);
            }
            _ => {}
        }
    }

    // ---------------------------------------------------------------------------------------
    // Expressions and blocks

    fn exprs(&mut self, es: &mut Vec<P<Expr>>) {
        for e in es {
            self.expr(e);
        }
    }

    fn expr(&mut self, expr: &mut P<Expr>) {
        if let ExprKind::MacCall(mac) = &expr.kind {
            let mac = mac.clone();
            let attrs = std::mem::take(&mut expr.attrs);
            if let Some((tokens, edition, _)) = self.expand_call(&mac) {
                let span = expr.span;
                if let Some(FragOut::Expr(mut new)) =
                    self.parse_frag(tokens, edition, span, Frag::Expr)
                {
                    let mut all = attrs;
                    all.append(&mut new.attrs);
                    new.attrs = all;
                    *expr = new;
                    self.expr(expr);
                }
                self.depth -= 1;
            } else {
                expr.kind = ExprKind::Err;
            }
            return;
        }
        match &mut expr.kind {
            ExprKind::Array(es) | ExprKind::Tup(es) => self.exprs(es),
            ExprKind::ConstBlock(c) => self.expr(&mut c.value),
            ExprKind::Call(f, args) => {
                self.expr(f);
                self.exprs(args);
            }
            ExprKind::MethodCall(m) => {
                self.expr(&mut m.receiver);
                if let Some(a) = &mut m.seg.args {
                    self.generic_args(a);
                }
                self.exprs(&mut m.args);
            }
            ExprKind::Binary(_, a, b)
            | ExprKind::Assign(a, b, _)
            | ExprKind::AssignOp(_, a, b)
            | ExprKind::Index(a, b, _) => {
                self.expr(a);
                self.expr(b);
            }
            ExprKind::Unary(_, e)
            | ExprKind::Await(e, _)
            | ExprKind::Use(e, _)
            | ExprKind::Field(e, _)
            | ExprKind::AddrOf(_, _, e)
            | ExprKind::Paren(e)
            | ExprKind::Try(e)
            | ExprKind::Become(e) => self.expr(e),
            ExprKind::Cast(e, t) | ExprKind::Type(e, t) => {
                self.expr(e);
                self.ty(t);
            }
            ExprKind::Let(p, e, _) => {
                self.pat(p);
                self.expr(e);
            }
            ExprKind::If(c, then, els) => {
                self.expr(c);
                self.block(then);
                if let Some(e) = els {
                    self.expr(e);
                }
            }
            ExprKind::While(c, b, _) => {
                self.expr(c);
                self.block(b);
            }
            ExprKind::ForLoop {
                pat, iter, body, ..
            } => {
                self.pat(pat);
                self.expr(iter);
                self.block(body);
            }
            ExprKind::Loop(b, _)
            | ExprKind::Block(b, _)
            | ExprKind::Gen(_, b, _)
            | ExprKind::TryBlock(b) => self.block(b),
            ExprKind::Match(e, arms, _) => {
                self.expr(e);
                arms.retain_mut(|a| self.process_attrs(&mut a.attrs));
                for a in arms {
                    self.pat(&mut a.pat);
                    if let Some(g) = &mut a.guard {
                        self.expr(g);
                    }
                    if let Some(b) = &mut a.body {
                        self.expr(b);
                    }
                }
            }
            ExprKind::Closure(c) => {
                self.fn_decl(&mut c.fn_decl);
                self.expr(&mut c.body);
            }
            ExprKind::Range(a, b, _) => {
                if let Some(a) = a {
                    self.expr(a);
                }
                if let Some(b) = b {
                    self.expr(b);
                }
            }
            ExprKind::Path(q, p) => {
                self.qself(q);
                self.path(p);
            }
            ExprKind::Break(_, e) | ExprKind::Ret(e) | ExprKind::Yield(e) | ExprKind::Yeet(e) => {
                if let Some(e) = e {
                    self.expr(e);
                }
            }
            ExprKind::OffsetOf(t, _) => self.ty(t),
            ExprKind::Struct(s) => {
                self.qself(&mut s.qself);
                self.path(&mut s.path);
                s.fields.retain_mut(|f| self.process_attrs(&mut f.attrs));
                for f in &mut s.fields {
                    self.expr(&mut f.expr);
                }
                if let StructRest::Base(b) = &mut s.rest {
                    self.expr(b);
                }
            }
            ExprKind::Repeat(e, c) => {
                self.expr(e);
                self.expr(&mut c.value);
            }
            ExprKind::FormatArgs(f) => {
                self.expr(&mut f.template);
                for a in &mut f.args {
                    self.expr(&mut a.expr);
                }
            }
            ExprKind::Lit(_)
            | ExprKind::Underscore
            | ExprKind::Continue(_)
            | ExprKind::InlineAsm(_)
            | ExprKind::Err
            | ExprKind::MacCall(_) => {}
        }
    }

    fn block(&mut self, block: &mut P<Block>) {
        let saved_scope = self.scope;
        let saved_module = self.module;
        // Items get a scope of their own, created at the first one.
        let mut block_scope: Option<DefId> = None;
        let mut i = 0;
        while i < block.stmts.len() {
            let keep = match &mut block.stmts[i].kind {
                StmtKind::Let(l) => self.process_attrs(&mut l.attrs),
                StmtKind::Item(item) => self.keep(&mut item.attrs),
                StmtKind::Expr(e) | StmtKind::Semi(e) => self.process_attrs(&mut e.attrs),
                StmtKind::MacCall(m) => self.process_attrs(&mut m.attrs),
                StmtKind::Empty => true,
            };
            if !keep {
                block.stmts.remove(i);
                continue;
            }
            // A macro call statement: replaced by its expansion's statements, which are
            // then processed in turn.
            if let StmtKind::MacCall(m) = &block.stmts[i].kind {
                let style = m.style;
                let mac = m.mac.clone();
                let span = block.stmts[i].span;
                let Some((tokens, edition, _)) = self.expand_call(&mac) else {
                    block.stmts.remove(i);
                    continue;
                };
                let stmts = match self.parse_frag(tokens, edition, span, Frag::Stmts) {
                    Some(FragOut::Stmts(s)) => s,
                    _ => Vec::new(),
                };
                self.depth -= 1;
                let mut stmts = stmts;
                // `m!(…);`: the expansion's last expression is a statement too.
                if style == MacStmtStyle::Semicolon
                    && let Some(last) = stmts.last_mut()
                    && let StmtKind::Expr(_) = last.kind
                {
                    let StmtKind::Expr(e) = std::mem::replace(&mut last.kind, StmtKind::Empty)
                    else {
                        unreachable!()
                    };
                    last.kind = StmtKind::Semi(e);
                }
                block.stmts.splice(i..=i, stmts);
                continue;
            }
            // A marker left for a `macro_rules!` (below) stays.
            if let StmtKind::Item(it) = &block.stmts[i].kind
                && it.id != NodeId::DUMMY
            {
                i += 1;
                continue;
            }
            if let StmtKind::Item(_) = &block.stmts[i].kind {
                let StmtKind::Item(item) = block.stmts.remove(i).kind else {
                    unreachable!()
                };
                let scope_def = *block_scope.get_or_insert_with(|| {
                    let parent_scope = self.module;
                    let def = self.r.new_def(
                        DefKind::Block,
                        Some(self.owner),
                        hyprc_span::kw::Empty,
                        block.span,
                        Vis::Restricted(self.r.parent_module(parent_scope)),
                    );
                    let normal = self.r.parent_module(parent_scope);
                    let dir = self.r.modules[&parent_scope].dir.clone();
                    let mut data = crate::collect::new_module(
                        def,
                        Some(parent_scope),
                        normal,
                        crate::loader::ModDir {
                            in_block: true,
                            ..dir
                        },
                    );
                    data.no_implicit_prelude = self.r.modules[&parent_scope].no_implicit_prelude;
                    self.r.modules.insert(def, data);
                    def
                });
                block.id = NodeId(scope_def.0);
                self.module = scope_def;
                let expn = item.span.ctxt.outer_expn();
                let before = self.r.invocations.len();
                let is_macro_rules = matches!(&item.kind, ItemKind::MacroDef(md) if md.macro_rules);
                let (item_span, item_ident) = (item.span, item.ident);
                self.scope = self
                    .r
                    .collect_items(scope_def, vec![item], self.scope, expn);
                // A `macro_rules!` in a body leaves a marker where it was: the macro can name
                // the body's locals declared before it (rustc's macro definition rib).
                if is_macro_rules
                    && let TextualScope::Def { mac, .. } = self.r.scopes[self.scope.0 as usize]
                {
                    let marker = Item {
                        attrs: Vec::new(),
                        id: NodeId(mac.0),
                        span: item_span,
                        vis: Visibility::inherited(item_span),
                        ident: item_ident,
                        kind: ItemKind::MacroDef(MacroDef {
                            body: DelimArgs {
                                open: item_span,
                                close: item_span,
                                delim: hyprc_syntax::token::Delim::Brace,
                                tokens: TokenStream::new(Vec::new()),
                            },
                            macro_rules: true,
                        }),
                    };
                    block.stmts.insert(
                        i,
                        Stmt {
                            id: NodeId::DUMMY,
                            kind: StmtKind::Item(Box::new(marker)),
                            span: item_span,
                        },
                    );
                    i += 1;
                }
                // Item-level macros in a block expand right away, as do the block's imports.
                self.expand_block_invocations(before);
                while self.r.resolve_imports_round() {}
                continue;
            }
            match &mut block.stmts[i].kind {
                StmtKind::Let(l) => {
                    self.pat(&mut l.pat);
                    if let Some(t) = &mut l.ty {
                        self.ty(t);
                    }
                    match &mut l.kind {
                        LocalKind::Decl => {}
                        LocalKind::Init(e) => self.expr(e),
                        LocalKind::InitElse(e, b) => {
                            self.expr(e);
                            self.block(b);
                        }
                    }
                }
                StmtKind::Expr(e) | StmtKind::Semi(e) => self.expr(e),
                _ => {}
            }
            i += 1;
        }
        self.scope = saved_scope;
        self.module = saved_module;
    }

    /// Expands item-level macro calls collected into a block scope (`thread_local! {}` in
    /// a function body), and those their expansions produce.
    fn expand_block_invocations(&mut self, from: usize) {
        let mut i = from;
        while i < self.r.invocations.len() {
            let inv = &self.r.invocations[i];
            if inv.done || inv.failed {
                i += 1;
                continue;
            }
            let (path, bang) = match &inv.kind {
                crate::InvocKind::Bang(m) => (m.path.clone(), true),
                crate::InvocKind::Derive { path, .. } => (path.clone(), false),
            };
            match self
                .r
                .resolve_macro_path(&path, inv.module, inv.scope, bang)
            {
                MacroLookup::Found(def) => self.r.expand_invocation(i, def),
                _ => {
                    let name = path
                        .segments
                        .iter()
                        .map(|s| s.ident.as_str())
                        .collect::<Vec<_>>()
                        .join("::");
                    self.r.sess.dcx.emit(
                        Diag::error(format!("cannot find macro `{name}` in this scope"))
                            .span(path.span, ""),
                    );
                    self.r.invocations[i].failed = true;
                    // Later items in the block see the scope as if the call weren't there.
                }
            }
            i += 1;
        }
        // The textual scope continues after the last invocation's output.
        if let TextualScope::Invocation { invoc, parent } = self.r.scopes[self.scope.0 as usize] {
            self.scope = self.r.invocations[invoc].output_scope.unwrap_or(parent);
        }
    }
}

enum FragOut {
    Expr(P<Expr>),
    Stmts(Vec<Stmt>),
    Pat(P<Pat>),
    Ty(P<Ty>),
}
