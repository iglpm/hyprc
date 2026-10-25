//! Autoderef and method calls.

use super::{Adjust, Adjustment, Callee, Expectation, FnCtxt, OverloadedDeref};
use crate::collect::simplify;
use crate::lower_ty::TyLowerer;
use crate::traits::Eval;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{DefId, DefKind, ExprId, Mutability};
use hyprc_span::{Diag, Span, Symbol, sym};

/// One autoderef step: the type, and how it was reached (`None` for the start).
pub(crate) type Step = (Ty, Option<Option<OverloadedDeref>>);

/// A chosen method: which, from where, and how the receiver gets there.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Pick {
    pub method: DefId,
    pub container: DefId,
    pub step: usize,
    pub autoref: Option<Mutability>,
    /// The receiver is an array used as a slice.
    pub unsize: bool,
}

impl<'a, 'h> FnCtxt<'a, 'h> {
    /// The types reachable from `ty` by dereferencing: references and `Box` (built-in),
    /// then `Deref` impls. Raw pointers are not dereferenced implicitly.
    pub(crate) fn autoderef_steps(&self, ty: Ty, span: Span) -> Vec<Step> {
        let mut steps: Vec<Step> = vec![(ty, None)];
        let mut cur = ty;
        for _ in 0..16 {
            let c = self.structurally_resolve(cur);
            if c.is_ty_var() || c.is_error() {
                break;
            }
            match *c.kind() {
                TyKind::Ref(t, _) => {
                    steps.push((t, Some(None)));
                    cur = t;
                    continue;
                }
                TyKind::Adt(d, args) if self.tcx.adt_def(d).is_box => {
                    let t = args.ty(0);
                    steps.push((t, Some(None)));
                    cur = t;
                    continue;
                }
                _ => {}
            }
            let Some(deref) = self.tcx.lang_item("deref") else {
                break;
            };
            let tr = TraitRef::new(deref, Args::from_tys(&[c]));
            if self.evaluate(Predicate::Trait(tr)) == Eval::Fails {
                break;
            }
            let Some(target) = self
                .tcx
                .lang_item("deref_target")
                .or_else(|| self.tcx.assoc_item(deref, sym::Target, false))
            else {
                break;
            };
            let Some(method) = self.tcx.assoc_item(deref, sym::deref, true) else {
                break;
            };
            let mut t = self.normalize(Ty::new(TyKind::Alias(
                AliasKind::Projection,
                AliasTy {
                    def: target,
                    args: tr.args,
                    index: 0,
                },
            )));
            if let TyKind::Alias(AliasKind::Projection, _) = *t.kind() {
                if let TyKind::Adt(d, args) = *c.kind() {
                    let name = self.tcx.hir.name(d).as_str();
                    if name == "Vec" && !args.is_empty() {
                        t = Ty::slice(args.ty(0));
                    } else if name == "String" {
                        t = Ty::STR;
                    } else if (name == "Arc" || name == "Rc") && !args.is_empty() {
                        t = args.ty(0);
                    }
                }
            }
            steps.push((
                t,
                Some(Some(OverloadedDeref {
                    method,
                    args: tr.args,
                    mutbl: Mutability::Not,
                })),
            ));
            cur = t;
            let _ = span;
        }
        steps
    }

    pub(crate) fn autoderef_adjustments(&self, steps: &[Step]) -> Vec<Adjustment> {
        steps
            .iter()
            .skip(1)
            .map(|(t, how)| Adjustment {
                kind: Adjust::Deref(how.unwrap_or(None)),
                target: *t,
            })
            .collect()
    }

    /// Deref adjustments for `steps[1..]` starting after a first built-in deref (coercions
    /// begin from `&T`, already dereferenced once).
    pub(crate) fn autoderef_adjustments_from(
        &self,
        steps: &[Step],
        m: Mutability,
    ) -> Vec<Adjustment> {
        steps
            .iter()
            .skip(1)
            .map(|(t, how)| {
                let kind = match how.unwrap_or(None) {
                    Some(o) => Adjust::Deref(Some(OverloadedDeref { mutbl: m, ..o })),
                    None => Adjust::Deref(None),
                };
                Adjustment { kind, target: *t }
            })
            .collect()
    }

    pub(crate) fn record_autoderef(&self, e: ExprId, steps: &[Step]) {
        let adj = self.autoderef_adjustments(steps);
        self.add_adjustments(e, adj);
    }

    // ---------------------------------------------------------------------------------------
    // Method calls

    pub(crate) fn check_method_call(
        &self,
        e: ExprId,
        receiver: ExprId,
        segment: &hir::PathSegment,
        args: &[ExprId],
        expected: Expectation,
    ) -> Ty {
        let rcvr_ty = self.check_expr(receiver);
        let span = self.span(e);
        let name = segment.ident.name;
        let mut steps = self.autoderef_steps(rcvr_ty, span);
        let mut pick = self.probe_method(&steps, name, span);
        if pick.is_none() {
            self.select_where_possible();
            let rcvr_ty = self.resolve(rcvr_ty);
            steps = self.autoderef_steps(rcvr_ty, span);
            pick = self.probe_method(&steps, name, span);
        }
        let Some(pick) = pick else {
            for &a in args {
                self.check_expr(a);
            }
            let rt = self.resolve(rcvr_ty);
            if !rt.has_errors() {
                if rt.is_ty_var() {
                    self.emit(
                        Diag::error("type annotations needed")
                            .code("E0282")
                            .span(self.span(receiver), "type must be known at this point"),
                    );
                } else {
                    self.emit(
                        Diag::error(format!(
                            "no method named `{}` found for {} `{rt}` in the current scope",
                            segment.ident,
                            ty_descr(rt)
                        ))
                        .code("E0599")
                        .span(segment.ident.span, "method not found"),
                    );
                }
            }
            return Ty::ERROR;
        };
        // Receiver adjustments.
        let mut adj = self.autoderef_adjustments(&steps[..=pick.step]);
        let mut self_ty = steps[pick.step].0;
        if pick.unsize {
            let elem = match *self.shallow(self_ty).kind() {
                TyKind::Array(t, _) => t,
                _ => self_ty,
            };
            let m = pick.autoref.unwrap_or(Mutability::Not);
            adj.push(Adjustment {
                kind: Adjust::Borrow(m),
                target: Ty::reference(self_ty, m),
            });
            self_ty = Ty::slice(elem);
            adj.push(Adjustment {
                kind: Adjust::Unsize,
                target: Ty::reference(self_ty, m),
            });
            if pick.autoref.is_none() {
                adj.push(Adjustment {
                    kind: Adjust::Deref(None),
                    target: self_ty,
                });
            }
        } else if let Some(m) = pick.autoref {
            adj.push(Adjustment {
                kind: Adjust::Borrow(m),
                target: Ty::reference(self_ty, m),
            });
        }
        let adjusted = adj.last().map_or(self_ty, |a| a.target);
        // Overloaded derefs of a `&mut self` receiver must be `DerefMut`.
        if matches!(pick.autoref, Some(Mutability::Mut)) {
            for a in adj.iter_mut() {
                if let Adjust::Deref(Some(o)) = &mut a.kind {
                    o.mutbl = Mutability::Mut;
                }
            }
        }
        self.add_adjustments(receiver, adj);
        let (method_args, sig) = self.instantiate_method(pick, self_ty, segment, span);
        if let Some(&first) = sig.inputs().first() {
            if self.infcx.unify(first, adjusted).is_err() {
                self.report_mismatch(
                    self.span(receiver),
                    first,
                    adjusted,
                    crate::infer::TypeError::Mismatch(first, adjusted),
                );
            }
        }
        if sig.unsafe_ {
            self.require_unsafe(span, "call to unsafe function");
        }
        self.r.borrow_mut().type_dependent.insert(
            e,
            Callee {
                def: pick.method,
                args: method_args,
            },
        );
        // The method's where-clauses (and its container's).
        for p in self.tcx.predicates_of(pick.method).iter() {
            self.register(p.subst(method_args), span);
        }
        if self.tcx.is_trait(pick.container) {
            let g = self.tcx.generics_of(pick.container);
            let trait_args = method_args.truncate(g.count() as usize);
            self.register(
                Predicate::Trait(TraitRef::new(pick.container, trait_args)),
                span,
            );
            for p in self.tcx.predicates_of(pick.container).iter() {
                self.register(p.subst(trait_args), span);
            }
        } else {
            let g = self.tcx.generics_of(pick.container);
            let impl_args = method_args.truncate(g.count() as usize);
            for p in self.tcx.predicates_of(pick.container).iter() {
                self.register(p.subst(impl_args), span);
            }
        }
        let rest = &sig.inputs()[1.min(sig.inputs().len())..];
        let expected_inputs = self.expected_inputs_for(rest, sig.output(), expected);
        self.check_args_with(span, rest, &expected_inputs, args, sig.c_variadic);
        let out = sig.output();
        if let Some(h) = expected.only_has_type() {
            let _ = self.infcx.probe(|| self.infcx.unify(h, out).is_ok());
        }
        out
    }

    /// Generic arguments and signature of a picked method: the container's arguments
    /// (fresh, the impl's tied to the receiver type), then the method's own (explicit or
    /// fresh).
    fn instantiate_method(
        &self,
        pick: Pick,
        self_ty: Ty,
        segment: &hir::PathSegment,
        span: Span,
    ) -> (Args, FnSig) {
        let solver = self.solver();
        let container_args = solver.fresh_args(pick.container);
        // `Self` follows from the receiver (unified by the caller).
        let _ = self_ty;
        let infer = |s: Span| self.next_ty_var(s);
        let infer_const = |ty: Ty| self.infcx.new_const_var(ty);
        let lowerer = TyLowerer::with_infer(self.tcx, self.owner, &infer, &infer_const);
        let args = lowerer.lower_args(
            pick.method,
            segment.args.as_deref(),
            container_args.as_slice(),
            None,
            span,
        );
        let sig = self.normalize_sig(self.tcx.fn_sig(pick.method).subst(args));
        (args, sig)
    }

    /// Finds the method `name` for a receiver: at each autoderef step, by value, then `&`,
    /// then `&mut`; inherent methods before trait methods. Arrays also try as slices.
    pub(crate) fn probe_method(&self, steps: &[Step], name: Symbol, span: Span) -> Option<Pick> {
        let mut all_steps: Vec<(Ty, bool)> = steps.iter().map(|(t, _)| (*t, false)).collect();
        if let Some(&(last, _)) = steps.last()
            && let TyKind::Array(elem, _) = *self.shallow(last).kind()
        {
            all_steps.push((Ty::slice(elem), true));
        }
        let last_real = steps.len() - 1;
        // Pass 1: Inherent methods
        for (i, &(step_ty, unsize)) in all_steps.iter().enumerate() {
            let step_ty = self.structurally_resolve(step_ty);
            if step_ty.is_ty_var() {
                return None;
            }
            for autoref in [None, Some(Mutability::Not), Some(Mutability::Mut)] {
                let adjusted = match autoref {
                    None => step_ty,
                    Some(m) => Ty::reference(step_ty, m),
                };
                if let Some((method, container)) = self.probe_inherent(step_ty, adjusted, name) {
                    return Some(Pick {
                        method,
                        container,
                        step: if unsize { last_real } else { i },
                        autoref,
                        unsize,
                    });
                }
            }
        }
        // Pass 2: Trait methods
        for (i, &(step_ty, unsize)) in all_steps.iter().enumerate() {
            let step_ty = self.structurally_resolve(step_ty);
            if step_ty.is_ty_var() {
                return None;
            }
            for autoref in [None, Some(Mutability::Not), Some(Mutability::Mut)] {
                let adjusted = match autoref {
                    None => step_ty,
                    Some(m) => Ty::reference(step_ty, m),
                };
                if let Some((method, container)) = self.probe_traits(step_ty, adjusted, name, span)
                {
                    return Some(Pick {
                        method,
                        container,
                        step: if unsize { last_real } else { i },
                        autoref,
                        unsize,
                    });
                }
            }
        }
        None
    }

    /// The method's receiver parameter type, instantiated with fresh variables, unified with
    /// the adjusted receiver: does the candidate apply?
    fn method_applies(&self, method: DefId, container: DefId, step_ty: Ty, adjusted: Ty) -> bool {
        let Some(item) = self.tcx.hir.get_item(method) else {
            return false;
        };
        let hir::ItemKind::Fn(f) = &item.kind else {
            return false;
        };
        if !f.sig.has_self {
            return false;
        }
        self.infcx.probe(|| {
            let solver = self.solver();
            let container_args = solver.fresh_args(container);
            // The method's `Self` (a trait's, or an impl's arguments) is whatever makes its
            // receiver type the adjusted receiver: `&self` at a `&T` step means `Self = T`,
            // `self: Pin<&mut Self>` at `Pin<&mut Pin<P>>` means `Self = Pin<P>` (rustc).
            let _ = step_ty;
            let all = solver.fresh_args(method);
            let args = Args::new(
                &[
                    container_args.as_slice(),
                    &all.as_slice()[container_args.len()..],
                ]
                .concat(),
            );
            let sig = self.tcx.fn_sig(method).subst(args);
            let Some(&first) = sig.inputs().first() else {
                return false;
            };
            // Normalized here, not through the body's obligations: this is only a probe.
            let mut pending = Vec::new();
            let first = solver.normalize(self.resolve(first), &mut pending);
            if self.infcx.unify(first, adjusted).is_err() {
                return false;
            }
            if pending.iter().any(|p| self.evaluate(*p) == Eval::Fails) {
                return false;
            }
            if self.tcx.is_trait(container) {
                let g = self.tcx.generics_of(container);
                let trait_args = args.truncate(g.count() as usize);
                let tr = TraitRef::new(container, trait_args);
                let r = self.evaluate(Predicate::Trait(tr));
                // `HYPRC_DEBUG_METHOD=<name>`: why a trait's method does or doesn't apply.
                if std::env::var("HYPRC_DEBUG_METHOD")
                    .is_ok_and(|n| n == self.tcx.hir.name(method).as_str())
                {
                    eprintln!(
                        "method `{}` of `{}` at step `{}` (receiver `{}`): `{}: {}` {:?}",
                        self.tcx.hir.name(method),
                        self.tcx.def_path(container),
                        self.resolve(step_ty),
                        self.resolve(adjusted),
                        self.resolve(tr.self_ty()),
                        self.tcx.def_path(container),
                        r
                    );
                }
                return r != Eval::Fails;
            }
            // Inherent impl: its where-clauses must be satisfiable.
            self.tcx
                .predicates_of(container)
                .iter()
                .all(|p| self.evaluate(p.subst(container_args)) != Eval::Fails)
        })
    }

    fn probe_inherent(&self, step_ty: Ty, adjusted: Ty, name: Symbol) -> Option<(DefId, DefId)> {
        let mut simps = Vec::new();
        if let Some(st) = simplify(step_ty) {
            simps.push(st);
        }
        if let Some(pin) = self.tcx.lang_item("pin")
            && let TyKind::Adt(d, args) = *step_ty.kind()
            && d == pin
            && let Some(p) = args.get(0).and_then(|a| a.as_ty())
        {
            let target = match *p.kind() {
                TyKind::Ref(t, _) | TyKind::RawPtr(t, _) => t,
                _ => p,
            };
            if let Some(st) = simplify(target) {
                simps.push(st);
            }
        }
        if let Some(boxed) = self.tcx.lang_item("owned_box")
            && let TyKind::Adt(d, args) = *step_ty.kind()
            && d == boxed
            && let Some(p) = args.get(0).and_then(|a| a.as_ty())
        {
            if let Some(st) = simplify(p) {
                simps.push(st);
            }
        }
        let mut found = None;
        for st in simps {
            for &imp in self.tcx.inherent_impls(st) {
                if let Some(m) = self.tcx.assoc_item(imp, name, true)
                    && self.tcx.hir.def_kind(m) == DefKind::AssocFn
                    && self.method_applies(m, imp, step_ty, adjusted)
                {
                    if found.is_some() {
                        // Several inherent impls with the method (e.g. for `Foo<u8>` and
                        // `Foo<u16>`): the first that applies.
                        break;
                    }
                    found = Some((m, imp));
                }
            }
        }
        found
    }

    fn probe_traits(
        &self,
        step_ty: Ty,
        adjusted: Ty,
        name: Symbol,
        span: Span,
    ) -> Option<(DefId, DefId)> {
        let mut traits: Vec<DefId> = self.traits_here();
        // `dyn Trait`: its traits' methods are callable without importing them.
        if let TyKind::Dynamic(preds) = *step_ty.kind() {
            for t in self.solver().object_traits(step_ty, preds) {
                if !traits.contains(&t.def) {
                    traits.push(t.def);
                }
            }
        }
        // Bounds on a type parameter or projection.
        for p in &self.env.preds {
            if let Predicate::Trait(t) = p
                && !traits.contains(&t.def)
            {
                traits.push(t.def);
            }
        }
        let mut found: Vec<(DefId, DefId)> = Vec::new();
        for t in traits {
            let Some(m) = self.find_trait_method(t, name) else {
                continue;
            };
            let container = self.tcx.assoc_container(m).unwrap_or(t);
            if self.method_applies(m, container, step_ty, adjusted)
                && !found.iter().any(|(fm, _)| *fm == m)
            {
                found.push((m, container));
            }
        }
        match found.len() {
            0 => None,
            1 => Some(found[0]),
            _ => {
                // Prefer a trait whose bound is in the where-clauses; otherwise report.
                for (m, c) in &found {
                    if self
                        .env
                        .preds
                        .iter()
                        .any(|p| matches!(p, Predicate::Trait(t) if t.def == *c))
                    {
                        return Some((*m, *c));
                    }
                }
                let names: Vec<String> = found
                    .iter()
                    .map(|(_, c)| format!("`{}`", self.tcx.def_path(*c)))
                    .collect();
                self.emit(
                    Diag::error(format!(
                        "multiple applicable items in scope: `{name}` from {}",
                        names.join(" and ")
                    ))
                    .code("E0034")
                    .span(span, "multiple `{name}` found"),
                );
                Some(found[0])
            }
        }
    }

    /// A method of a trait or one of its supertraits.
    fn find_trait_method(&self, t: DefId, name: Symbol) -> Option<DefId> {
        if let Some(m) = self.tcx.assoc_item(t, name, true)
            && self.tcx.hir.def_kind(m) == DefKind::AssocFn
        {
            return Some(m);
        }
        None
    }
}

fn ty_descr(t: Ty) -> &'static str {
    match t.kind() {
        TyKind::Adt(..) => "type",
        TyKind::Ref(..) => "reference",
        TyKind::Param(..) => "type parameter",
        _ => "type",
    }
}
