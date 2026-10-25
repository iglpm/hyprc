//! Coercions: the implicit conversions at coercion sites (arguments, `let` with a type,
//! returns, struct fields, array elements, branches).

use super::{Adjust, Adjustment, Expectation, FnCtxt};
use crate::infer::TypeError;
use crate::traits::Eval;
use crate::ty::*;
use hyprc_hir::{ExprId, Mutability};
use hyprc_span::{Diag, Span};

impl<'a, 'h> FnCtxt<'a, 'h> {
    /// Coerces `e` (of type `from`) to `to`; reports a mismatch if it can't.
    pub(crate) fn demand_coerce(&self, e: ExprId, from: Ty, to: Ty) -> bool {
        match self.try_coerce(e, from, to) {
            Ok(()) => true,
            Err(err) => {
                self.report_mismatch(self.span(e), to, from, err);
                false
            }
        }
    }

    pub(crate) fn try_coerce(&self, e: ExprId, from: Ty, to: Ty) -> Result<(), TypeError> {
        // An unknown source type: let the pending obligations say what it is first
        // (`e.into()` with `E: Into<!>` in scope is `!`, which then coerces), as rustc does.
        if self.shallow(from).is_ty_var() && !self.shallow(to).is_ty_var() {
            self.select_where_possible();
        }
        let from = self.shallow(self.normalize(self.shallow(from)));
        let to = self.shallow(self.normalize(self.shallow(to)));
        if from == to {
            return Ok(());
        }
        if from.is_never() {
            if to.is_ty_var() {
                self.diverging_vars.borrow_mut().push(to);
            }
            self.add_adjustments(
                e,
                vec![Adjustment {
                    kind: Adjust::NeverToAny,
                    target: to,
                }],
            );
            return Ok(());
        }
        if from.is_ty_var() || to.is_ty_var() {
            return self.infcx.unify(from, to);
        }
        match (*from.kind(), *to.kind()) {
            (TyKind::Ref(a, m1), TyKind::Ref(b, m2)) => self.coerce_ref(e, from, a, m1, to, b, m2),
            (TyKind::Ref(a, m1), TyKind::RawPtr(b, m2)) => {
                if !self.infcx.mutability_ok(m1, m2) {
                    return Err(TypeError::MutabilityMismatch);
                }
                let r = self.infcx.commit_if_ok(|| self.infcx.unify(a, b));
                if r.is_ok() {
                    self.add_adjustments(
                        e,
                        vec![
                            Adjustment {
                                kind: Adjust::Deref(None),
                                target: a,
                            },
                            Adjustment {
                                kind: Adjust::RawBorrow(m2),
                                target: to,
                            },
                        ],
                    );
                    return Ok(());
                }
                if self.try_unsize(a, b) {
                    let p = Ty::ptr(a, m2);
                    self.add_adjustments(
                        e,
                        vec![
                            Adjustment {
                                kind: Adjust::Deref(None),
                                target: a,
                            },
                            Adjustment {
                                kind: Adjust::RawBorrow(m2),
                                target: p,
                            },
                            Adjustment {
                                kind: Adjust::Unsize,
                                target: to,
                            },
                        ],
                    );
                    return Ok(());
                }
                Err(TypeError::Mismatch(from, to))
            }
            (TyKind::RawPtr(a, m1), TyKind::RawPtr(b, m2)) => {
                if !self.infcx.mutability_ok(m1, m2) {
                    return Err(TypeError::MutabilityMismatch);
                }
                if self.infcx.commit_if_ok(|| self.infcx.unify(a, b)).is_ok() {
                    if m1 != m2 {
                        self.add_adjustments(
                            e,
                            vec![Adjustment {
                                kind: Adjust::MutToConstPointer,
                                target: to,
                            }],
                        );
                    }
                    return Ok(());
                }
                if self.try_unsize(a, b) {
                    self.add_adjustments(
                        e,
                        vec![Adjustment {
                            kind: Adjust::Unsize,
                            target: to,
                        }],
                    );
                    return Ok(());
                }
                Err(TypeError::Mismatch(from, to))
            }
            (TyKind::FnDef(d, args), TyKind::FnPtr(target_sig)) => {
                let sig = self.normalize_sig(self.tcx.fn_sig(d).subst(args));
                // A safe fn coerces to an `unsafe fn` pointer too.
                let sig_ty = Ty::fn_ptr(FnSig {
                    unsafe_: sig.unsafe_ || target_sig.unsafe_,
                    ..sig
                });
                self.infcx.unify(sig_ty, to)?;
                self.add_adjustments(
                    e,
                    vec![Adjustment {
                        kind: Adjust::ReifyFnPointer,
                        target: to,
                    }],
                );
                Ok(())
            }
            (TyKind::Closure(c, cargs), TyKind::FnPtr(target_sig)) => {
                let Some(sig) = self.closure_sig_now(c, cargs) else {
                    return Err(TypeError::Mismatch(from, to));
                };
                // A non-capturing closure is a safe fn: an `unsafe fn` pointer takes it too.
                self.infcx.unify(
                    Ty::fn_ptr(FnSig {
                        abi: Abi::Rust,
                        unsafe_: target_sig.unsafe_,
                        ..sig
                    }),
                    to,
                )?;
                self.add_adjustments(
                    e,
                    vec![Adjustment {
                        kind: Adjust::ClosureFnPointer,
                        target: to,
                    }],
                );
                Ok(())
            }
            (TyKind::Adt(d1, _), TyKind::Adt(d2, _)) if d1 == d2 => {
                if self
                    .infcx
                    .commit_if_ok(|| self.infcx.unify(from, to))
                    .is_ok()
                {
                    return Ok(());
                }
                if self.try_coerce_unsized(from, to, self.span(e)) {
                    self.add_adjustments(
                        e,
                        vec![Adjustment {
                            kind: Adjust::Unsize,
                            target: to,
                        }],
                    );
                    return Ok(());
                }
                self.infcx.unify(from, to)
            }
            _ => self.infcx.unify(from, to),
        }
    }

    fn coerce_ref(
        &self,
        e: ExprId,
        from: Ty,
        a: Ty,
        m1: Mutability,
        to: Ty,
        b: Ty,
        m2: Mutability,
    ) -> Result<(), TypeError> {
        if !self.infcx.mutability_ok(m1, m2) {
            return Err(TypeError::MutabilityMismatch);
        }
        // `&T` → `&T` (or `&mut T` → `&T`): a reborrow.
        if self.infcx.commit_if_ok(|| self.infcx.unify(a, b)).is_ok() {
            if m1 != m2 {
                self.add_adjustments(
                    e,
                    vec![
                        Adjustment {
                            kind: Adjust::Deref(None),
                            target: a,
                        },
                        Adjustment {
                            kind: Adjust::Borrow(m2),
                            target: to,
                        },
                    ],
                );
            }
            return Ok(());
        }
        // Unsizing: `&[T; N]` → `&[T]`, `&T` → `&dyn Trait`.
        if self.try_unsize(a, b) {
            let reborrowed = Ty::reference(a, m2);
            self.add_adjustments(
                e,
                vec![
                    Adjustment {
                        kind: Adjust::Deref(None),
                        target: a,
                    },
                    Adjustment {
                        kind: Adjust::Borrow(m2),
                        target: reborrowed,
                    },
                    Adjustment {
                        kind: Adjust::Unsize,
                        target: to,
                    },
                ],
            );
            return Ok(());
        }
        // Deref coercion: `&String` → `&str`, `&Box<T>` → `&T`, `&&T` → `&T`.
        let steps = self.autoderef_steps(a, self.span(e));
        for (i, (step, _)) in steps.iter().enumerate().skip(1) {
            let step = self.shallow(*step);
            if self
                .infcx
                .commit_if_ok(|| self.infcx.unify(step, b))
                .is_ok()
            {
                let mut adj = vec![Adjustment {
                    kind: Adjust::Deref(None),
                    target: a,
                }];
                adj.extend(self.autoderef_adjustments_from(&steps[..=i], m2));
                adj.push(Adjustment {
                    kind: Adjust::Borrow(m2),
                    target: to,
                });
                self.add_adjustments(e, adj);
                return Ok(());
            }
            // A deref step that then unsizes (`&Vec<[T; 2]>`… rare); stop at slices.
            if self.try_unsize(step, b) {
                let mut adj = vec![Adjustment {
                    kind: Adjust::Deref(None),
                    target: a,
                }];
                adj.extend(self.autoderef_adjustments_from(&steps[..=i], m2));
                adj.push(Adjustment {
                    kind: Adjust::Borrow(m2),
                    target: Ty::reference(step, m2),
                });
                adj.push(Adjustment {
                    kind: Adjust::Unsize,
                    target: to,
                });
                self.add_adjustments(e, adj);
                return Ok(());
            }
        }
        Err(TypeError::Mismatch(from, to))
    }

    /// Can `a` unsize to `b` (`[T; N]` to `[T]`, `T` to `dyn Trait`)? Registers the
    /// obligations if so.
    pub(crate) fn try_unsize(&self, a: Ty, b: Ty) -> bool {
        let a = self.shallow(a);
        let b = self.shallow(b);
        if let Some(u) = self.tcx.lang_item("unsize") {
            let pred = Predicate::Trait(TraitRef::new(u, Args::from_tys(&[a, b])));
            if self.evaluate(pred) == Eval::Holds {
                self.register(pred, hyprc_span::Span::DUMMY);
                return true;
            }
        }
        match (*a.kind(), *b.kind()) {
            (TyKind::Array(t, _), TyKind::Slice(u)) => {
                self.infcx.commit_if_ok(|| self.infcx.unify(t, u)).is_ok()
            }
            // `dyn Tr + Send` → `dyn Tr` (dropping auto traits), `dyn Sub` → `dyn Super`.
            (TyKind::Dynamic(pa), TyKind::Dynamic(pb)) => {
                let autos = |p: PredList| -> Vec<hyprc_hir::DefId> {
                    p.as_slice()
                        .iter()
                        .filter_map(|x| match *x {
                            ExistentialPredicate::AutoTrait(d) => Some(d),
                            _ => None,
                        })
                        .collect()
                };
                let (from_autos, to_autos) = (autos(pa), autos(pb));
                if !to_autos.iter().all(|d| from_autos.contains(d)) {
                    return false;
                }
                match (pa.principal(), pb.principal()) {
                    (_, None) => true,
                    (None, Some(_)) => false,
                    (Some(_), Some((db, xb))) => {
                        // The target's principal among the source's traits (itself or a
                        // supertrait), with the same arguments.
                        let solver = self.solver();
                        solver.object_traits(a, pa).into_iter().any(|t| {
                            t.def == db
                                && self
                                    .infcx
                                    .commit_if_ok(|| {
                                        self.infcx
                                            .unify_args(Args::new(&t.args.as_slice()[1..]), xb)
                                    })
                                    .is_ok()
                        })
                    }
                }
            }
            (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
                let adt = self.tcx.adt_def(d1);
                if !adt.is_struct() {
                    return false;
                }
                let v = adt.non_enum_variant();
                let Some(last) = v.fields.last() else {
                    return false;
                };
                let last_from = last.ty.subst(a1);
                let last_to = last.ty.subst(a2);
                for f in &v.fields[..v.fields.len() - 1] {
                    let f1 = f.ty.subst(a1);
                    let f2 = f.ty.subst(a2);
                    if self
                        .infcx
                        .commit_if_ok(|| self.infcx.unify(f1, f2))
                        .is_err()
                    {
                        return false;
                    }
                }
                self.try_unsize(last_from, last_to)
            }
            (_, TyKind::Dynamic(preds)) => {
                if a.is_ty_var() {
                    return false;
                }
                let solver = self.solver();
                let traits: Vec<TraitRef> = preds
                    .as_slice()
                    .iter()
                    .filter_map(|p| match *p {
                        ExistentialPredicate::Trait { def, args } => {
                            let mut full = vec![GenericArg::Ty(a)];
                            full.extend_from_slice(args.as_slice());
                            Some(TraitRef::new(def, Args::new(&full)))
                        }
                        ExistentialPredicate::AutoTrait(def) => {
                            Some(TraitRef::new(def, Args::from_tys(&[a])))
                        }
                        _ => None,
                    })
                    .collect();
                let ok = traits
                    .iter()
                    .all(|t| solver.evaluate(Predicate::Trait(*t)) != Eval::Fails);
                if ok {
                    for t in traits {
                        self.register(Predicate::Trait(t), hyprc_span::Span::DUMMY);
                    }
                    self.require_sized(a, hyprc_span::Span::DUMMY);
                }
                ok
            }
            _ => false,
        }
    }

    /// `Box<T>` → `Box<dyn Trait>` and other smart pointers, through `CoerceUnsized`.
    fn try_coerce_unsized(&self, from: Ty, to: Ty, span: Span) -> bool {
        let Some(cu) = self.tcx.lang_item("coerce_unsized") else {
            return false;
        };
        let pred = Predicate::Trait(TraitRef::new(cu, Args::from_tys(&[from, to])));
        // The impls (`impl<T: Unsize<U>, U> CoerceUnsized<Box<U>> for Box<T>`) need the
        // pointee unsizing, which the solver checks through `Unsize`.
        if self.evaluate(pred) == Eval::Holds
            || (self.evaluate(pred) == Eval::Ambiguous && to.has_infer() == false)
        {
            self.register(pred, span);
            return true;
        }
        false
    }

    pub(crate) fn can_coerce(&self, from: Ty, to: Ty) -> bool {
        let saved_adj = self.r.borrow().adjustments.clone();
        let r = self.infcx.probe(|| self.try_coerce(ExprId(0), from, to));
        self.r.borrow_mut().adjustments = saved_adj;
        r.is_ok()
    }

    /// The common type of branches (`if`/`else`, `match` arms).
    pub(crate) fn coerce_branches(
        &self,
        branches: &[(ExprId, Ty)],
        expected: Expectation,
        span: Span,
    ) -> Ty {
        if let Some(t) = expected.only_has_type()
            && !self.shallow(t).is_ty_var()
        {
            for &(e, ty) in branches {
                self.demand_coerce(e, ty, t);
            }
            return t;
        }
        let target = branches
            .iter()
            .map(|&(_, t)| t)
            .find(|&t| !self.shallow(t).is_never());
        let Some(mut target) = target else {
            return Ty::NEVER;
        };
        for &(_, ty) in branches {
            if self.shallow(ty).is_never() {
                continue;
            }
            if !self.can_coerce(ty, target) {
                if self.can_coerce(target, ty) {
                    target = ty;
                } else if let (TyKind::FnDef(d1, a1), TyKind::FnDef(d2, a2)) =
                    (target.kind(), ty.kind())
                {
                    let s1 = self.normalize_sig(self.tcx.fn_sig(*d1).subst(*a1));
                    let s2 = self.normalize_sig(self.tcx.fn_sig(*d2).subst(*a2));
                    let p1 = Ty::fn_ptr(s1);
                    let p2 = Ty::fn_ptr(s2);
                    if self.infcx.probe(|| self.infcx.unify(p1, p2)).is_ok() {
                        target = p1;
                    }
                }
            }
        }
        for &(e, ty) in branches {
            if self.shallow(ty).is_never() {
                self.add_adjustments(
                    e,
                    vec![Adjustment {
                        kind: Adjust::NeverToAny,
                        target,
                    }],
                );
                continue;
            }
            if self.try_coerce(e, ty, target).is_err() {
                let (t1, t2) = (self.resolve(target), self.resolve(ty));
                if !t1.has_errors() && !t2.has_errors() {
                    self.emit(
                        Diag::error("`if` and `else` (or `match` arms) have incompatible types")
                            .code("E0308")
                            .span(self.span(e), format!("expected `{t1}`, found `{t2}`"))
                            .label(span, ""),
                    );
                }
            }
        }
        target
    }
}
