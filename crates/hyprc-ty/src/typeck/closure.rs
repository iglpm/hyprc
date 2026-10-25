//! Closures: signatures (from annotations and from what's expected), captures, kinds; and
//! calls through the `Fn*` traits.

use super::{Adjust, Adjustment, Callee, CaptureKind, ClosureResult, Expectation, FnCtxt, Upvar};
use crate::collect::ClosureKind;
use crate::traits::{Eval, closure_kind_ty};
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{ClosureId, ExprId, ExprKind, LocalId, Mutability, Res};
use hyprc_span::{FxHashMap, FxHashSet, Span};

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn closure_ref(&self, id: ClosureId) -> ClosureRef {
        ClosureRef {
            owner: self.owner,
            body: self.body_id.0,
            index: id.0,
        }
    }

    pub(crate) fn closure_sig_now(&self, c: ClosureRef, args: Args) -> Option<FnSig> {
        if c.owner == self.owner && c.body == self.body_id.0 {
            return self
                .closure_info
                .borrow()
                .get(c.index as usize)
                .and_then(|x| x.map(|(s, _, _)| s));
        }
        crate::traits::closure_sig_from_args(args)
    }

    pub(crate) fn check_closure(&self, e: ExprId, id: ClosureId, expected: Expectation) -> Ty {
        let data = &self.body.closures[id.index()];
        let span = self.span(e);
        let (exp_inputs, exp_output) = self.deduce_closure_sig(expected, data.params.len());
        let inputs: Vec<Ty> = data
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, ty))| match ty {
                Some(t) => self.lower_ty(t),
                None => exp_inputs
                    .as_ref()
                    .and_then(|v| v.get(i).copied())
                    .unwrap_or_else(|| self.next_ty_var(span)),
            })
            .collect();
        let output = match &data.ret {
            Some(t) => self.lower_ty(t),
            None => exp_output.unwrap_or_else(|| self.next_ty_var(span)),
        };
        let body_ty = output;
        // `async` blocks and closures produce a future; their body's value is its output.
        let is_coroutine = data.kind != hir::ClosureKind::Closure;
        let sig = FnSig::new(&inputs, output, false, false, Abi::Rust);
        let kind_var = self.next_ty_var(span);
        let upvars_var = self.next_ty_var(span);
        let mut args = self.tcx.identity_args(self.owner).as_slice().to_vec();
        args.push(GenericArg::Ty(kind_var));
        args.push(GenericArg::Ty(Ty::fn_ptr(sig)));
        args.push(GenericArg::Ty(upvars_var));
        let cref = self.closure_ref(id);
        let ty = if is_coroutine {
            Ty::new(TyKind::Coroutine(cref, Args::new(&args)))
        } else {
            Ty::new(TyKind::Closure(cref, Args::new(&args)))
        };
        self.closure_info.borrow_mut()[id.index()] = Some((sig, None, ty));
        for (i, (pat, _)) in data.params.iter().enumerate() {
            self.check_pat_top(*pat, inputs[i], true);
        }
        self.ret_tys.borrow_mut().push(body_ty);
        let saved = self.diverges.replace(false);
        self.check_expr_coercible_to(data.body, body_ty);
        self.diverges.set(saved);
        self.ret_tys.borrow_mut().pop();
        self.analyze_closure(id.index());
        ty
    }

    /// What the context says about a closure's signature: an expected `fn` pointer type, or
    /// `Fn*` bounds pending on the expected type variable.
    fn deduce_closure_sig(&self, expected: Expectation, n: usize) -> (Option<Vec<Ty>>, Option<Ty>) {
        let Some(t) = expected.only_has_type() else {
            return (None, None);
        };
        let mut t = self.shallow(t);
        while let TyKind::Ref(inner, _) | TyKind::RawPtr(inner, _) = *t.kind() {
            t = self.shallow(inner);
        }
        if let TyKind::FnPtr(sig) = *t.kind() {
            return (Some(sig.inputs().to_vec()), Some(sig.output()));
        }
        if let TyKind::Dynamic(preds) = *t.kind() {
            let mut inputs = None;
            let mut output = None;
            let fn_once_output = self.tcx.lang_item("fn_once_output");
            for p in preds.as_slice() {
                match *p {
                    ExistentialPredicate::Trait { def, args }
                        if self.tcx.fn_trait_kind(def).is_some() =>
                    {
                        if let Some(GenericArg::Ty(arg_t)) = args.get(0) {
                            let arg_t = self.shallow(arg_t);
                            let fields = arg_t.tuple_fields();
                            if fields.len() == n || (n == 0 && arg_t.is_unit()) {
                                inputs = Some(fields.to_vec());
                            }
                        }
                    }
                    ExistentialPredicate::Projection { def, term, .. }
                        if Some(def) == fn_once_output =>
                    {
                        output = Some(self.shallow(term));
                    }
                    _ => {}
                }
            }
            if inputs.is_some() || output.is_some() {
                let inputs = inputs.map(|v| v.into_iter().map(|t| self.normalize(t)).collect());
                return (inputs, output.map(|t| self.normalize(t)));
            }
        }
        if !t.is_ty_var() {
            return (None, None);
        }
        let mut inputs = None;
        let mut output = None;
        let fn_once_output = self.tcx.lang_item("fn_once_output");
        for (p, _) in self.obligations.borrow().iter() {
            match p {
                Predicate::Trait(tr) if self.tcx.fn_trait_kind(tr.def).is_some() => {
                    let self_ty = self.shallow(tr.self_ty());
                    let matches_t = self_ty == t
                        || match *self_ty.kind() {
                            TyKind::Ref(inner, _) => self.shallow(inner) == t,
                            _ => false,
                        };
                    if matches_t && let Some(GenericArg::Ty(args)) = tr.args.get(1) {
                        let args = self.shallow(args);
                        let fields = args.tuple_fields();
                        if fields.len() == n || (n == 0 && args.is_unit()) {
                            inputs = Some(fields.to_vec());
                        }
                    }
                }
                Predicate::Projection(alias, ty) if Some(alias.def) == fn_once_output => {
                    let self_ty = alias
                        .args
                        .get(0)
                        .and_then(|a| a.as_ty())
                        .map(|s| self.shallow(s));
                    let matches_t = self_ty == Some(t)
                        || match self_ty.and_then(|st| match *st.kind() {
                            TyKind::Ref(inner, _) => Some(self.shallow(inner)),
                            _ => None,
                        }) {
                            Some(inner) => inner == t,
                            None => false,
                        };
                    if matches_t {
                        output = Some(self.shallow(*ty));
                    }
                }
                _ => {}
            }
        }
        // `FnMut(B, I::Item)`: with `I: Iterator<Item = u32>` in scope, the closure takes a `u32`.
        let inputs = inputs.map(|v| v.into_iter().map(|t| self.normalize(t)).collect());
        (inputs, output.map(|t| self.normalize(t)))
    }

    /// `f(args)` where `f` isn't a function: a closure behind references, or a type
    /// implementing `Fn*` (`Box<dyn Fn(u8)>`, a generic `F: FnMut()`).
    pub(crate) fn check_overloaded_call(
        &self,
        e: ExprId,
        f: ExprId,
        callee_ty: Ty,
        args: &[ExprId],
    ) -> Option<Ty> {
        let span = self.span(e);
        let steps = self.autoderef_steps(callee_ty, span);
        for (i, (step, _)) in steps.iter().enumerate() {
            let st = self.structurally_resolve(*step);
            let direct = match *st.kind() {
                TyKind::Closure(c, a) => self.closure_sig_now(c, a),
                TyKind::FnDef(d, a) => Some(self.normalize_sig(self.tcx.fn_sig(d).subst(a))),
                TyKind::FnPtr(sig) => Some(sig),
                _ => None,
            };
            if let Some(sig) = direct {
                self.record_autoderef(f, &steps[..=i]);
                self.check_args(span, sig.inputs(), args, sig.c_variadic);
                return Some(sig.output());
            }
            for (lang, method) in [
                ("fn", "call"),
                ("fn_mut", "call_mut"),
                ("fn_once", "call_once"),
            ] {
                let Some(trait_) = self.tcx.lang_item(lang) else {
                    continue;
                };
                let tuple = self.next_ty_var(span);
                let tr = TraitRef::new(trait_, Args::from_tys(&[st, tuple]));
                if self.evaluate(Predicate::Trait(tr)) == Eval::Fails {
                    continue;
                }
                // Commit: select to learn the argument tuple.
                let solver = self.solver();
                let _ = self.infcx.commit_if_ok(|| match solver.select(tr) {
                    crate::traits::SelectResult::Ok(sel) => {
                        for n in sel.nested {
                            self.register(n, span);
                            if let Predicate::Trait(nested_tr) = n {
                                let _ = solver.select(nested_tr);
                            }
                        }
                        Ok(())
                    }
                    _ => Err(()),
                });
                self.register(Predicate::Trait(tr), span);
                let mut adj = self.autoderef_adjustments(&steps[..=i]);
                if lang != "fn_once" {
                    let m = if lang == "fn_mut" {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    };
                    adj.push(Adjustment {
                        kind: Adjust::Borrow(m),
                        target: Ty::reference(st, m),
                    });
                }
                self.add_adjustments(f, adj);
                if let Some(m) =
                    self.tcx
                        .assoc_item(trait_, hyprc_span::Symbol::intern(method), true)
                {
                    self.r.borrow_mut().overloaded.insert(
                        e,
                        Callee {
                            def: m,
                            args: tr.args,
                        },
                    );
                }
                let inputs: Vec<Ty> = self.shallow(tuple).tuple_fields().to_vec();
                if self.shallow(tuple).is_ty_var() {
                    let tys: Vec<Ty> = args.iter().map(|&a| self.check_expr(a)).collect();
                    let _ = self.infcx.unify(tuple, Ty::tuple(&tys));
                } else {
                    self.check_args(span, &inputs, args, false);
                }
                let output = self.tcx.lang_item("fn_once_output")?;
                let out = Ty::new(TyKind::Alias(
                    AliasKind::Projection,
                    AliasTy {
                        def: output,
                        args: Args::from_tys(&[st, tuple]),
                        index: 0,
                    },
                ));
                return Some(self.normalize(out));
            }
        }
        None
    }

    /// After the body is checked: what each closure captures and how, its kind, and its
    /// type's final arguments.
    pub(crate) fn analyze_closures(&self) {
        for i in 0..self.body.closures.len() {
            self.analyze_closure(i);
        }
    }

    pub(crate) fn analyze_closure(&self, i: usize) {
        if self
            .r
            .borrow()
            .closures
            .get(i)
            .and_then(|x| x.as_ref())
            .is_some()
        {
            return;
        }
        let Some((sig, _, ty)) = self.closure_info.borrow().get(i).copied().flatten() else {
            return;
        };
        let c = &self.body.closures[i];
        // Locals declared inside the closure (parameters and its body's bindings).
        let mut inside: FxHashSet<LocalId> = FxHashSet::default();
        for (p, _) in &c.params {
            self.collect_bindings(*p, &mut inside);
        }
        let mut uses: FxHashMap<LocalId, Use> = FxHashMap::default();
        self.walk_uses(c.body, &mut inside, &mut uses, Use::Value);
        let mut upvars = Vec::new();
        let mut kind = ClosureKind::Fn;
        let mut locals: Vec<(LocalId, Use)> = uses
            .into_iter()
            .filter(|(l, _)| !inside.contains(l))
            .collect();
        locals.sort_by_key(|(l, _)| l.0);
        for (l, u) in locals {
            let lty = self.resolve(self.r.borrow().local_tys[l.index()]);
            let is_copy = self.is_copy(lty);
            let is_ref = matches!(self.shallow(lty).kind(), TyKind::Ref(..));
            let is_mut_ref = matches!(self.shallow(lty).kind(), TyKind::Ref(_, Mutability::Mut));
            let moved = u == Use::Value && !is_copy && !is_ref;
            let capture = if c.by_move || moved {
                CaptureKind::ByValue
            } else if u == Use::Mut || is_mut_ref {
                CaptureKind::ByRef(Mutability::Mut)
            } else {
                CaptureKind::ByRef(Mutability::Not)
            };
            if moved {
                kind = ClosureKind::FnOnce;
            } else if (u == Use::Mut || is_mut_ref) && kind == ClosureKind::Fn {
                kind = ClosureKind::FnMut;
            }
            upvars.push(Upvar {
                local: l,
                kind: capture,
                ty: lty,
            });
        }
        let upvar_tys: Vec<Ty> = upvars
            .iter()
            .map(|u| match u.kind {
                CaptureKind::ByValue => u.ty,
                CaptureKind::ByRef(m) => Ty::reference(u.ty, m),
            })
            .collect();
        if let TyKind::Closure(_, args) | TyKind::Coroutine(_, args) = *ty.kind() {
            let s = args.as_slice();
            let n = s.len();
            let _ = self
                .infcx
                .unify(s[n - 3].expect_ty(), closure_kind_ty(kind));
            let _ = self
                .infcx
                .unify(s[n - 1].expect_ty(), Ty::tuple(&upvar_tys));
        }
        self.closure_info.borrow_mut()[i] = Some((sig, Some(kind), ty));
        self.r.borrow_mut().closures[i] = Some(ClosureResult {
            kind,
            sig,
            upvars,
            ty,
        });
    }

    fn is_copy(&self, t: Ty) -> bool {
        let Some(copy) = self.tcx.lang_item("copy") else {
            return t.is_scalar() || matches!(t.kind(), TyKind::Ref(_, Mutability::Not));
        };
        self.evaluate(Predicate::Trait(TraitRef::new(copy, Args::from_tys(&[t])))) == Eval::Holds
    }

    fn collect_bindings(&self, p: hir::PatId, out: &mut FxHashSet<LocalId>) {
        match &self.body.pat(p).kind {
            hir::PatKind::Binding { local, sub, .. } => {
                out.insert(*local);
                if let Some(s) = sub {
                    self.collect_bindings(*s, out);
                }
            }
            hir::PatKind::Struct { fields, .. } => fields
                .iter()
                .for_each(|f| self.collect_bindings(f.pat, out)),
            hir::PatKind::TupleStruct { pats, .. }
            | hir::PatKind::Tuple { pats, .. }
            | hir::PatKind::Or(pats) => pats.iter().for_each(|&s| self.collect_bindings(s, out)),
            hir::PatKind::Box(s) | hir::PatKind::Deref(s) | hir::PatKind::Ref(s, _) => {
                self.collect_bindings(*s, out)
            }
            hir::PatKind::Slice {
                before,
                rest,
                after,
                ..
            } => {
                before
                    .iter()
                    .chain(after)
                    .for_each(|&s| self.collect_bindings(s, out));
                if let Some(r) = rest {
                    self.collect_bindings(*r, out);
                }
            }
            _ => {}
        }
    }

    /// Records how locals are used in an expression: moved, mutated or read.
    fn walk_uses(
        &self,
        e: ExprId,
        inside: &mut FxHashSet<LocalId>,
        uses: &mut FxHashMap<LocalId, Use>,
        ctx: Use,
    ) {
        let note = |l: LocalId, u: Use, uses: &mut FxHashMap<LocalId, Use>| {
            let entry = uses.entry(l).or_insert(u);
            *entry = (*entry).max(u);
        };
        // A method receiver or operand with a `&`/`&mut` adjustment is used by reference.
        let ctx = match self
            .r
            .borrow()
            .adjustments
            .get(&e)
            .and_then(|a| a.iter().find(|a| matches!(a.kind, Adjust::Borrow(_))))
        {
            Some(Adjustment {
                kind: Adjust::Borrow(Mutability::Mut),
                ..
            }) => Use::Mut,
            Some(_) => Use::Ref,
            None => ctx,
        };
        let expr = self.body.expr(e);
        let walk =
            |x: ExprId,
             c: Use,
             inside: &mut FxHashSet<LocalId>,
             uses: &mut FxHashMap<LocalId, Use>| self.walk_uses(x, inside, uses, c);
        match &expr.kind {
            ExprKind::Path(hir::QPath::Resolved(None, p)) => {
                if let Res::Local(l) = p.res {
                    note(LocalId(l), ctx, uses);
                }
            }
            ExprKind::AddrOf(_, m, x) => walk(
                *x,
                if *m == Mutability::Mut {
                    Use::Mut
                } else {
                    Use::Ref
                },
                inside,
                uses,
            ),
            ExprKind::Assign(l, r) => {
                walk(*l, Use::Mut, inside, uses);
                walk(*r, Use::Value, inside, uses);
            }
            ExprKind::AssignOp(_, l, r) => {
                walk(*l, Use::Mut, inside, uses);
                walk(*r, Use::Value, inside, uses);
            }
            ExprKind::Field(x, _) => {
                let xt = self
                    .r
                    .borrow()
                    .expr_tys
                    .get(x.index())
                    .copied()
                    .unwrap_or(Ty::ERROR);
                let is_ref = matches!(self.shallow(xt).kind(), TyKind::Ref(..));
                let fty = self
                    .r
                    .borrow()
                    .expr_tys
                    .get(e.index())
                    .copied()
                    .unwrap_or(Ty::ERROR);
                let u = if is_ref || self.is_copy(fty) {
                    if ctx == Use::Mut { Use::Mut } else { Use::Ref }
                } else {
                    ctx
                };
                walk(*x, u, inside, uses);
            }
            ExprKind::Binary(op, l, r) => {
                let u = if op.is_comparison() { Use::Ref } else { ctx };
                walk(*l, u, inside, uses);
                walk(*r, u, inside, uses);
            }
            ExprKind::Index(x, i) => {
                walk(
                    *x,
                    if ctx == Use::Mut { Use::Mut } else { Use::Ref },
                    inside,
                    uses,
                );
                walk(*i, Use::Value, inside, uses);
            }
            ExprKind::Unary(hyprc_hir::UnOp::Deref, x) => walk(
                *x,
                if ctx == Use::Mut { Use::Mut } else { Use::Ref },
                inside,
                uses,
            ),
            ExprKind::MethodCall { receiver, args, .. } => {
                let callee = self
                    .r
                    .borrow()
                    .type_dependent
                    .get(&e)
                    .copied()
                    .or_else(|| self.r.borrow().overloaded.get(&e).copied());
                let rcvr_use = if let Some(callee) = callee {
                    let sig = self.tcx.fn_sig(callee.def);
                    if let Some(&first) = sig.inputs().first() {
                        match *first.kind() {
                            TyKind::Ref(_, Mutability::Mut) => Use::Mut,
                            TyKind::Ref(_, Mutability::Not) => Use::Ref,
                            _ => Use::Value,
                        }
                    } else {
                        Use::Value
                    }
                } else {
                    Use::Value
                };
                walk(*receiver, rcvr_use, inside, uses);
                for &a in args {
                    walk(a, Use::Value, inside, uses);
                }
            }
            ExprKind::Let { pat, init } => {
                self.collect_bindings(*pat, inside);
                walk(*init, Use::Ref, inside, uses);
            }
            ExprKind::Match {
                scrutinee, arms, ..
            } => {
                walk(*scrutinee, Use::Ref, inside, uses);
                for a in arms {
                    self.collect_bindings(a.pat, inside);
                    if let Some(g) = a.guard {
                        walk(g, Use::Value, inside, uses);
                    }
                    walk(a.body, Use::Value, inside, uses);
                }
            }
            ExprKind::Block(b, _) | ExprKind::Loop { body: b, .. } => {
                self.walk_block_uses(b, inside, uses)
            }
            ExprKind::Closure(id) => {
                let c = &self.body.closures[id.index()];
                for (p, _) in &c.params {
                    self.collect_bindings(*p, inside);
                }
                walk(
                    c.body,
                    if c.by_move { Use::Value } else { Use::Ref },
                    inside,
                    uses,
                );
            }
            _ => {
                for child in expr_children(&expr.kind) {
                    walk(child, Use::Value, inside, uses);
                }
            }
        }
        let _ = Span::DUMMY;
    }

    fn walk_block_uses(
        &self,
        b: &hir::Block,
        inside: &mut FxHashSet<LocalId>,
        uses: &mut FxHashMap<LocalId, Use>,
    ) {
        for s in &b.stmts {
            match &s.kind {
                hir::StmtKind::Let { pat, init, els, .. } => {
                    self.collect_bindings(*pat, inside);
                    if let Some(i) = init {
                        self.walk_uses(*i, inside, uses, Use::Value);
                    }
                    if let Some(e) = els {
                        self.walk_block_uses(e, inside, uses);
                    }
                }
                hir::StmtKind::Expr(e) => self.walk_uses(*e, inside, uses, Use::Value),
            }
        }
        if let Some(t) = b.tail {
            self.walk_uses(t, inside, uses, Use::Value);
        }
    }
}

/// How a closure uses a captured local, weakest first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Use {
    Ref,
    Mut,
    Value,
}

/// The sub-expressions of an expression (for walks that don't care about the kind).
pub(crate) fn expr_children(kind: &ExprKind) -> Vec<ExprId> {
    match kind {
        ExprKind::Lit(_)
        | ExprKind::Path(_)
        | ExprKind::Continue { .. }
        | ExprKind::Closure(_)
        | ExprKind::InlineAsm(_)
        | ExprKind::OffsetOf(..)
        | ExprKind::Err => Vec::new(),
        ExprKind::Call(f, args) => std::iter::once(*f).chain(args.iter().copied()).collect(),
        ExprKind::MethodCall { receiver, args, .. } => std::iter::once(*receiver)
            .chain(args.iter().copied())
            .collect(),
        ExprKind::Binary(_, a, b)
        | ExprKind::Assign(a, b)
        | ExprKind::AssignOp(_, a, b)
        | ExprKind::Index(a, b) => vec![*a, *b],
        ExprKind::Unary(_, a)
        | ExprKind::Cast(a, _)
        | ExprKind::Type(a, _)
        | ExprKind::AddrOf(_, _, a)
        | ExprKind::Field(a, _)
        | ExprKind::ConstBlock(a)
        | ExprKind::Await(a)
        | ExprKind::Become(a) => vec![*a],
        ExprKind::Repeat(a, _) => vec![*a],
        ExprKind::Tuple(es) | ExprKind::Array(es) => es.clone(),
        ExprKind::Struct { fields, tail, .. } => {
            let mut v: Vec<ExprId> = fields.iter().map(|f| f.expr).collect();
            if let hir::StructTail::Base(b) = tail {
                v.push(*b);
            }
            v
        }
        ExprKind::If { cond, then, els } => {
            let mut v = vec![*cond, *then];
            v.extend(els);
            v
        }
        ExprKind::Let { init, .. } => vec![*init],
        ExprKind::Loop { body, .. } | ExprKind::Block(body, _) => block_children(body),
        ExprKind::Match {
            scrutinee, arms, ..
        } => {
            let mut v = vec![*scrutinee];
            for a in arms {
                v.extend(a.guard);
                v.push(a.body);
            }
            v
        }
        ExprKind::Break { value, .. } | ExprKind::Return(value) | ExprKind::Yield(value) => {
            value.iter().copied().collect()
        }
        ExprKind::FormatArgs(f) => f.args.clone(),
    }
}

pub(crate) fn block_children(b: &hir::Block) -> Vec<ExprId> {
    let mut v = Vec::new();
    for s in &b.stmts {
        match &s.kind {
            hir::StmtKind::Let { init, .. } => v.extend(init),
            hir::StmtKind::Expr(e) => v.push(*e),
        }
    }
    v.extend(b.tail);
    v
}
