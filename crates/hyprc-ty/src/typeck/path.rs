//! Paths in expressions: locals, functions, constants, constructors, associated items.

use super::{Callee, Expectation, FnCtxt};
use crate::collect::simplify;
use crate::lower_ty::TyLowerer;
use crate::traits::Eval;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{CtorKind, DefId, DefKind, ExprId, Res};
use hyprc_span::{Diag, Span};

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn lowerer_args(
        &self,
        def: DefId,
        args: Option<&hir::GenericArgs>,
        parent: &[GenericArg],
        self_ty: Option<Ty>,
        span: Span,
    ) -> Args {
        let infer = |s: Span| self.next_ty_var(s);
        let infer_const = |ty: Ty| self.infcx.new_const_var(ty);
        let mut lowerer = TyLowerer::with_infer(self.tcx, self.owner, &infer, &infer_const);
        lowerer.value_path = true;
        lowerer.lower_args(def, args, parent, self_ty, span)
    }

    pub(crate) fn check_path_expr(&self, e: ExprId, q: &hir::QPath, expected: Expectation) -> Ty {
        let span = self.span(e);
        let _ = expected;
        match q {
            hir::QPath::Resolved(Some(qself), path) => {
                // `<T as Trait>::item`
                let self_ty = self.lower_ty(qself);
                let Res::Def(kind, item) = path.res else {
                    return Ty::ERROR;
                };
                let Some(trait_) = self.tcx.assoc_container(item) else {
                    return Ty::ERROR;
                };
                let trait_seg = path
                    .segments
                    .len()
                    .checked_sub(2)
                    .map(|i| &path.segments[i]);
                let trait_args = self.lowerer_args(
                    trait_,
                    trait_seg.and_then(|s| s.args.as_deref()),
                    &[],
                    Some(self_ty),
                    span,
                );
                self.register_trait(trait_, trait_args, span);
                let own = path.segments.last().and_then(|s| s.args.as_deref());
                let args = self.lowerer_args(item, own, trait_args.as_slice(), None, span);
                self.r
                    .borrow_mut()
                    .type_dependent
                    .insert(e, Callee { def: item, args });
                self.item_value_ty(e, kind, item, args, span)
            }
            hir::QPath::Resolved(None, path) => self.check_resolved_path(e, path, span),
            hir::QPath::TypeRelative(base, seg) => {
                let base_ty = self.lower_value_path_ty(base);
                match self.resolve_type_relative(base_ty, seg, span) {
                    Some((kind, def, args)) => {
                        self.r
                            .borrow_mut()
                            .type_dependent
                            .insert(e, Callee { def, args });
                        self.item_value_ty(e, kind, def, args, span)
                    }
                    None => Ty::ERROR,
                }
            }
            hir::QPath::LangItem(name, _) => {
                let Some(&def) = self.tcx.lang_items().get(name) else {
                    self.err(span, format!("requires `{name}` lang_item"));
                    return Ty::ERROR;
                };
                let kind = self.tcx.hir.def_kind(def);
                let kind = match kind {
                    // Lang items on variants name the constructor.
                    DefKind::Variant => {
                        let adt = self.tcx.adt_def(self.tcx.hir.parent(def).unwrap());
                        let v = adt.variants.iter().find(|v| v.def == def);
                        match v.map(|v| v.shape) {
                            Some(hir::CtorShape::Tuple) => {
                                DefKind::Ctor(hir::CtorOf::Variant, CtorKind::Fn)
                            }
                            _ => DefKind::Ctor(hir::CtorOf::Variant, CtorKind::Const),
                        }
                    }
                    DefKind::Struct => DefKind::Ctor(hir::CtorOf::Struct, CtorKind::Const),
                    k => k,
                };
                let args = match kind {
                    DefKind::AssocFn | DefKind::AssocConst => {
                        let container = self.tcx.assoc_container(def).unwrap();
                        let container_args = self.solver().fresh_args(container);
                        if self.tcx.is_trait(container) {
                            self.register_trait(container, container_args, span);
                        }
                        self.lowerer_args(def, None, container_args.as_slice(), None, span)
                    }
                    DefKind::Ctor(..) => {
                        let adt = self.adt_of_ctor(def);
                        self.lowerer_args(adt, None, &[], None, span)
                    }
                    _ => self.lowerer_args(def, None, &[], None, span),
                };
                self.item_value_ty(e, kind, def, args, span)
            }
        }
    }

    fn adt_of_ctor(&self, def: DefId) -> DefId {
        match self.tcx.hir.def_kind(def) {
            DefKind::Variant => self.tcx.hir.parent(def).unwrap(),
            _ => def,
        }
    }

    fn check_resolved_path(&self, e: ExprId, path: &hir::Path, span: Span) -> Ty {
        match path.res {
            Res::Local(l) => self.r.borrow().local_tys[l as usize],
            Res::Def(kind @ (DefKind::Fn | DefKind::Const | DefKind::Static { .. }), d) => {
                let own = path.segments.last().and_then(|s| s.args.as_deref());
                let args = self.lowerer_args(d, own, &[], None, span);
                self.item_value_ty(e, kind, d, args, span)
            }
            Res::Def(kind @ (DefKind::AssocFn | DefKind::AssocConst), d) => {
                // `Trait::item` (inherent items are reached type-relatively).
                let container = self.tcx.assoc_container(d).unwrap();
                let container_seg = path
                    .segments
                    .len()
                    .checked_sub(2)
                    .map(|i| &path.segments[i]);
                let container_args = if self.tcx.is_trait(container) {
                    let self_ty = self.next_ty_var(span);
                    let a = self.lowerer_args(
                        container,
                        container_seg.and_then(|s| s.args.as_deref()),
                        &[],
                        Some(self_ty),
                        span,
                    );
                    self.register_trait(container, a, span);
                    a
                } else {
                    self.solver().fresh_args(container)
                };
                let own = path.segments.last().and_then(|s| s.args.as_deref());
                let args = self.lowerer_args(d, own, container_args.as_slice(), None, span);
                self.r
                    .borrow_mut()
                    .type_dependent
                    .insert(e, Callee { def: d, args });
                self.item_value_ty(e, kind, d, args, span)
            }
            Res::Def(kind @ DefKind::Ctor(..), d) => {
                let adt = self.adt_of_ctor(d);
                // Arguments may be on the enum's segment or the variant's.
                let seg_args = path.segments.iter().rev().find_map(|s| s.args.as_deref());
                let args = self.lowerer_args(adt, seg_args, &[], None, span);
                self.item_value_ty(e, kind, d, args, span)
            }
            Res::SelfCtor(def) => {
                let self_ty = match self.tcx.hir.def_kind(def) {
                    DefKind::Impl { .. } => self.tcx.type_of(def),
                    _ => self.tcx.type_of(def),
                };
                let TyKind::Adt(adt, args) = *self.normalize(self_ty).kind() else {
                    self.err(
                        span,
                        "the `Self` constructor can only be used with tuple or unit structs",
                    );
                    return Ty::ERROR;
                };
                let shape = self.tcx.adt_def(adt).variants.first().map(|v| v.shape);
                let kind = match shape {
                    Some(hir::CtorShape::Tuple) => DefKind::Ctor(hir::CtorOf::Struct, CtorKind::Fn),
                    _ => DefKind::Ctor(hir::CtorOf::Struct, CtorKind::Const),
                };
                self.item_value_ty(e, kind, adt, args, span)
            }
            Res::ConstParam { owner, index } => self.tcx.const_param_ty(owner, index),
            Res::Def(DefKind::Struct | DefKind::Union | DefKind::Enum, d) => {
                self.emit(
                    Diag::error(format!(
                        "expected value, found struct `{}`",
                        self.tcx.def_path(d)
                    ))
                    .code("E0423")
                    .span(span, "use struct literal syntax instead"),
                );
                Ty::ERROR
            }
            Res::Err => Ty::ERROR,
            res => {
                self.emit(
                    Diag::error(format!("expected value, found {}", res.descr()))
                        .code("E0423")
                        .span(span, ""),
                );
                Ty::ERROR
            }
        }
    }

    /// The type of a path to an item, with its arguments; records them.
    pub(crate) fn item_value_ty(
        &self,
        e: ExprId,
        kind: DefKind,
        def: DefId,
        args: Args,
        span: Span,
    ) -> Ty {
        self.r.borrow_mut().node_args.insert(e, args);
        let preds_of = |d: DefId| {
            for p in self.tcx.predicates_of(d).iter() {
                self.register(p.subst(args), span);
            }
        };
        match kind {
            DefKind::Fn | DefKind::AssocFn => {
                preds_of(def);
                Ty::fn_def(def, args)
            }
            DefKind::Ctor(_, CtorKind::Fn) => Ty::fn_def(def, args),
            DefKind::Ctor(_, CtorKind::Const) => {
                let adt = self.adt_of_ctor(def);
                Ty::adt(adt, args)
            }
            DefKind::Const | DefKind::AssocConst => {
                preds_of(def);
                self.normalize(self.tcx.type_of(def).subst(args))
            }
            DefKind::Static { mutable } => {
                let foreign = matches!(
                    self.tcx.hir.get_item(def).map(|i| &i.kind),
                    Some(hir::ItemKind::Static { foreign: true, .. })
                );
                if mutable || foreign {
                    self.require_unsafe(
                        span,
                        if mutable {
                            "use of mutable static"
                        } else {
                            "use of extern static"
                        },
                    );
                }
                self.normalize(self.tcx.type_of(def))
            }
            _ => Ty::ERROR,
        }
    }

    /// `Type::item`: an enum variant, an inherent associated item, or a trait's.
    pub(crate) fn resolve_type_relative(
        &self,
        base: Ty,
        seg: &hir::PathSegment,
        span: Span,
    ) -> Option<(DefKind, DefId, Args)> {
        let base = self.structurally_resolve(base);
        if base.is_error() {
            return None;
        }
        let name = seg.ident.name;
        // An enum variant through a type alias: `Alias::Variant`.
        if let TyKind::Adt(d, adt_args) = *base.kind() {
            let adt = self.tcx.adt_def(d);
            if adt.is_enum()
                && let Some(v) = adt.variants.iter().find(|v| v.name == name)
            {
                let kind = match v.shape {
                    hir::CtorShape::Tuple => DefKind::Ctor(hir::CtorOf::Variant, CtorKind::Fn),
                    hir::CtorShape::Unit => DefKind::Ctor(hir::CtorOf::Variant, CtorKind::Const),
                    hir::CtorShape::Struct => {
                        self.err(span, "struct variants can't be used as values");
                        return None;
                    }
                };
                return Some((kind, v.def, adt_args));
            }
        }
        // Inherent items.
        if let Some(st) = simplify(base) {
            for &imp in self.tcx.inherent_impls(st) {
                let Some(item) = self.tcx.assoc_item(imp, name, true) else {
                    continue;
                };
                let applies = self.infcx.probe(|| {
                    let a = self.solver().fresh_args(imp);
                    self.infcx
                        .unify(self.tcx.type_of(imp).subst(a), base)
                        .is_ok()
                });
                if !applies {
                    continue;
                }
                let impl_args = self.solver().fresh_args(imp);
                let _ = self
                    .infcx
                    .unify(self.tcx.type_of(imp).subst(impl_args), base);
                let args =
                    self.lowerer_args(item, seg.args.as_deref(), impl_args.as_slice(), None, span);
                return Some((self.tcx.hir.def_kind(item), item, args));
            }
        }
        // Trait items: traits in scope and bounds.
        let mut traits = self.traits_here();
        if let TyKind::Dynamic(preds) = *base.kind() {
            for t in self.solver().object_traits(base, preds) {
                if !traits.contains(&t.def) {
                    traits.push(t.def);
                }
            }
        }
        let mut found = None;
        for t in traits {
            let Some(item) = self.tcx.assoc_item(t, name, true) else {
                continue;
            };
            let trait_args = self.solver().fresh_args(t);
            let g = self.tcx.generics_of(t);
            let ok = self.infcx.probe(|| {
                if let Some(GenericArg::Ty(s)) = trait_args.get(g.parent_count as usize) {
                    let _ = self.infcx.unify(s, base);
                }
                self.evaluate(Predicate::Trait(TraitRef::new(t, trait_args))) != Eval::Fails
            });
            if ok {
                if let Some(GenericArg::Ty(s)) = trait_args.get(g.parent_count as usize) {
                    let _ = self.infcx.unify(s, base);
                }
                self.register_trait(t, trait_args, span);
                let args =
                    self.lowerer_args(item, seg.args.as_deref(), trait_args.as_slice(), None, span);
                found = Some((self.tcx.hir.def_kind(item), item, args));
                break;
            }
        }
        if found.is_none() {
            let b = self.resolve(base);
            if !b.has_errors() {
                self.emit(
                    Diag::error(format!("no function or associated item named `{name}` found for `{b}` in the current scope"))
                        .code("E0599")
                        .span(seg.ident.span, "associated item not found"),
                );
            }
        }
        found
    }

    /// The ADT type and variant a struct expression or pattern path names.
    pub(crate) fn resolve_struct_path(
        &self,
        path: &hir::QPath,
        span: Span,
    ) -> Option<(Ty, DefId, usize)> {
        let (adt, variant_def, args) = match path {
            hir::QPath::Resolved(None, p) => match p.res {
                Res::Def(DefKind::Struct | DefKind::Union, d) => {
                    let a = self.lowerer_args(
                        d,
                        p.segments.last().and_then(|s| s.args.as_deref()),
                        &[],
                        None,
                        span,
                    );
                    (d, d, a)
                }
                Res::Def(DefKind::Variant, v)
                | Res::Def(DefKind::Ctor(hir::CtorOf::Variant, _), v) => {
                    let d = self.tcx.hir.parent(v).unwrap();
                    let seg_args = p.segments.iter().rev().find_map(|s| s.args.as_deref());
                    let a = self.lowerer_args(d, seg_args, &[], None, span);
                    (d, v, a)
                }
                Res::Def(DefKind::Ctor(hir::CtorOf::Struct, _), d) => {
                    let a = self.lowerer_args(
                        d,
                        p.segments.last().and_then(|s| s.args.as_deref()),
                        &[],
                        None,
                        span,
                    );
                    (d, d, a)
                }
                Res::Def(DefKind::TyAlias, _) | Res::SelfTyAlias { .. } => {
                    let t = self.lower_ty(&hir::Ty {
                        kind: hir::TyKind::Path(path.clone()),
                        span,
                    });
                    match *self.normalize(t).kind() {
                        TyKind::Adt(d, a) => (d, d, a),
                        _ => {
                            self.err(
                                span,
                                "expected struct, found type alias to a non-struct type",
                            );
                            return None;
                        }
                    }
                }
                Res::Err => return None,
                res => {
                    self.emit(
                        Diag::error(format!(
                            "expected struct, variant or union type, found {}",
                            res.descr()
                        ))
                        .code("E0574")
                        .span(span, ""),
                    );
                    return None;
                }
            },
            hir::QPath::TypeRelative(base, seg) => {
                let base_ty = self.lower_value_path_ty(base);
                let base_ty = self.structurally_resolve(base_ty);
                if let TyKind::Adt(d, a) = *base_ty.kind() {
                    let adt = self.tcx.adt_def(d);
                    if adt.is_enum() {
                        if let Some(v) = adt.variants.iter().find(|v| v.name == seg.ident.name) {
                            (d, v.def, a)
                        } else {
                            self.err(span, format!("no variant named `{}`", seg.ident));
                            return None;
                        }
                    } else {
                        let hir_ty = hir::Ty {
                            kind: hir::TyKind::Path(hir::QPath::TypeRelative(
                                base.clone(),
                                seg.clone(),
                            )),
                            span,
                        };
                        let t = self.lower_ty(&hir_ty);
                        let t = self.normalize(t);
                        let t = self.structurally_resolve(t);
                        if let TyKind::Adt(d, a) = *t.kind() {
                            (d, d, a)
                        } else {
                            self.err(span, "expected a struct or enum variant");
                            return None;
                        }
                    }
                } else {
                    let hir_ty = hir::Ty {
                        kind: hir::TyKind::Path(hir::QPath::TypeRelative(
                            base.clone(),
                            seg.clone(),
                        )),
                        span,
                    };
                    let t = self.lower_ty(&hir_ty);
                    let t = self.normalize(t);
                    let t = self.structurally_resolve(t);
                    if let TyKind::Adt(d, a) = *t.kind() {
                        (d, d, a)
                    } else {
                        self.err(span, "expected a struct or enum variant");
                        return None;
                    }
                }
            }
            hir::QPath::LangItem(name, _) => {
                let &d = self.tcx.lang_items().get(name)?;
                match self.tcx.hir.def_kind(d) {
                    DefKind::Variant => {
                        let adt = self.tcx.hir.parent(d).unwrap();
                        let a = self.solver().fresh_args(adt);
                        (adt, d, a)
                    }
                    _ => {
                        let a = self.solver().fresh_args(d);
                        (d, d, a)
                    }
                }
            }
            hir::QPath::Resolved(Some(_), _) => return None,
        };
        let adt_def = self.tcx.adt_def(adt);
        let idx = adt_def.variant_index(variant_def).unwrap_or(0);
        Some((Ty::adt(adt, args), variant_def, idx))
    }
}
