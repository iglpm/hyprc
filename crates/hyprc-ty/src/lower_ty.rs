//! HIR types to semantic types ("astconv").

use crate::TyCtxt;
use crate::collect::GenericParamDefKind;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{DefId, DefKind, PrimTy, Res};
use hyprc_span::{Diag, Span, Symbol, kw};
use std::cell::RefCell;

/// Lowers types written in an item (or a body: then `_` and missing arguments become
/// inference variables through `infer`).
pub struct TyLowerer<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    /// The item whose generic parameters are in scope.
    pub owner: DefId,
    pub infer: Option<&'a dyn Fn(Span) -> Ty>,
    pub infer_const: Option<&'a dyn Fn(Ty) -> Const>,
    /// Errors already reported for this lowering (so a bad type reports once).
    reported: RefCell<u32>,
    /// Lowering a path in an expression: parameters without written arguments are
    /// inferred, not defaulted (`HashMap::new()`, `Add::add(a, b)`), as in rustc.
    pub value_path: bool,
}

fn err(span: Span, msg: impl Into<String>) -> Diag {
    Diag::error(msg).span(span, "")
}

impl<'a, 'h> TyLowerer<'a, 'h> {
    pub fn new(tcx: &'a TyCtxt<'h>, owner: DefId) -> Self {
        TyLowerer {
            tcx,
            owner,
            infer: None,
            infer_const: None,
            reported: RefCell::new(0),
            value_path: false,
        }
    }

    pub fn with_infer(
        tcx: &'a TyCtxt<'h>,
        owner: DefId,
        infer: &'a dyn Fn(Span) -> Ty,
        infer_const: &'a dyn Fn(Ty) -> Const,
    ) -> Self {
        TyLowerer {
            tcx,
            owner,
            infer: Some(infer),
            infer_const: Some(infer_const),
            reported: RefCell::new(0),
            value_path: false,
        }
    }

    fn report(&self, d: Diag) {
        *self.reported.borrow_mut() += 1;
        self.tcx.emit(d);
    }

    pub fn lower(&self, t: &hir::Ty) -> Ty {
        match &t.kind {
            hir::TyKind::Path(q) => self.lower_qpath(q, t.span),
            hir::TyKind::Ref(m, inner) => Ty::reference(self.lower(inner), *m),
            hir::TyKind::Ptr(m, inner) => Ty::ptr(self.lower(inner), *m),
            hir::TyKind::Slice(e) => Ty::slice(self.lower(e)),
            hir::TyKind::Array(e, len) => {
                let elem = self.lower(e);
                Ty::array(elem, self.lower_const_arg(len, Ty::USIZE))
            }
            hir::TyKind::Tup(ts) => {
                let tys: Vec<Ty> = ts.iter().map(|t| self.lower(t)).collect();
                Ty::tuple(&tys)
            }
            hir::TyKind::FnPtr(f) => {
                let inputs: Vec<Ty> = f.inputs.iter().map(|t| self.lower(t)).collect();
                let output = f.output.as_ref().map_or(Ty::UNIT, |t| self.lower(t));
                let abi = match f.abi {
                    hir::Abi::Rust => Abi::Rust,
                    hir::Abi::C => Abi::C,
                    hir::Abi::Other(s) if s.as_str() == "rust-call" => Abi::RustCall,
                    hir::Abi::Other(s) if s.as_str() == "system" => Abi::System,
                    hir::Abi::Other(s) => Abi::Other(s),
                };
                Ty::fn_ptr(FnSig::new(
                    &inputs,
                    output,
                    f.c_variadic,
                    f.safety_unsafe,
                    abi,
                ))
            }
            hir::TyKind::Never => Ty::NEVER,
            hir::TyKind::Infer => {
                match self.infer {
                    Some(f) => f(t.span),
                    None => {
                        self.report(err(t.span, "the placeholder `_` is not allowed within types on item signatures").code("E0121"));
                        Ty::ERROR
                    }
                }
            }
            hir::TyKind::TraitObject(bounds) => self.lower_dyn(bounds, t.span),
            hir::TyKind::Opaque { owner, index, .. } => {
                let args = self.tcx.identity_args(*owner);
                Ty::new(TyKind::Alias(
                    AliasKind::Opaque,
                    AliasTy {
                        def: *owner,
                        args,
                        index: *index,
                    },
                ))
            }
            hir::TyKind::Pat(base, pat) => {
                let base_ty = self.lower(base);
                match self.pat_range(base_ty, pat) {
                    Some(r) => Ty::new(TyKind::Pat(base_ty, r)),
                    None => {
                        self.report(err(
                            t.span,
                            "hyprc can't use this pattern type's pattern yet",
                        ));
                        Ty::ERROR
                    }
                }
            }
            hir::TyKind::ImplicitSelf | hir::TyKind::Err => Ty::ERROR,
        }
    }

    /// The valid range of a pattern type's pattern, as bits of `base`.
    fn pat_range(&self, base: Ty, pat: &hir::TyPat) -> Option<PatRange> {
        let pw = self.tcx.pointer_width;
        let bits = match base.kind() {
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Char => crate::consteval::int_bits(base, pw),
            _ => pw,
        };
        let mask = if bits >= 128 {
            u128::MAX
        } else {
            (1u128 << bits) - 1
        };
        match pat {
            hir::TyPat::NotNull => Some(PatRange {
                start: 1,
                end: mask,
            }),
            hir::TyPat::Range {
                start,
                end,
                inclusive,
            } => {
                let signed = base.is_signed();
                let min = if signed { 1u128 << (bits - 1) } else { 0 };
                let max = match base.kind() {
                    TyKind::Char => 0x10FFFF,
                    _ if signed => (1u128 << (bits - 1)) - 1,
                    _ => mask,
                };
                let eval = |b: hir::BodyId| {
                    self.tcx
                        .eval_const_body(b, base, Args::EMPTY)
                        .try_to_bits()
                        .map(|v| v & mask)
                };
                let s = match start {
                    Some(b) => eval(*b)?,
                    None => min,
                };
                let mut e = match end {
                    Some(b) => eval(*b)?,
                    None => max,
                };
                if end.is_some() && !inclusive {
                    e = e.wrapping_sub(1) & mask;
                }
                Some(PatRange { start: s, end: e })
            }
            hir::TyPat::Or(alts) => {
                // Ranges that touch (wrapping around) make one range: `..0 | 1..` is `1..=-1`.
                let mut ranges = alts.iter().map(|a| self.pat_range(base, a));
                let mut acc = ranges.next()??;
                for r in ranges {
                    let r = r?;
                    if acc.end.wrapping_add(1) & mask == r.start {
                        acc.end = r.end;
                    } else if r.end.wrapping_add(1) & mask == acc.start {
                        acc.start = r.start;
                    } else {
                        return None;
                    }
                }
                Some(acc)
            }
            hir::TyPat::Err => None,
        }
    }

    pub fn lower_const_arg(&self, c: &hir::ConstArg, ty: Ty) -> Const {
        match c {
            hir::ConstArg::Body(b) => {
                self.tcx
                    .eval_const_body(*b, ty, self.tcx.identity_args(self.owner))
            }
            hir::ConstArg::Param { index, owner } => {
                let name = self
                    .tcx
                    .all_params(*owner)
                    .iter()
                    .find(|p| p.index == *index)
                    .map_or(kw::Empty, |p| p.name);
                let pty = self.tcx.const_param_ty(*owner, *index);
                Const::new(pty, ConstKind::Param(*index, name))
            }
            hir::ConstArg::Infer => match self.infer_const {
                Some(f) => f(ty),
                None => Const::error(ty),
            },
        }
    }

    fn lower_qpath(&self, q: &hir::QPath, span: Span) -> Ty {
        match q {
            hir::QPath::Resolved(qself, path) => {
                if let Some(qself) = qself {
                    // `<T as Trait>::Assoc`
                    let self_ty = self.lower(qself);
                    return self.lower_assoc_through_trait(self_ty, path, span);
                }
                self.lower_resolved(path, span)
            }
            hir::QPath::TypeRelative(base, seg) => {
                let base_ty = self.lower(base);
                self.lower_type_relative(base_ty, base, seg, span)
            }
            hir::QPath::LangItem(name, _) => match self.tcx.hir.lang_items.get(name) {
                Some(&d) => self.tcx.type_of(d),
                None => {
                    self.report(err(span, format!("requires `{name}` lang_item")));
                    Ty::ERROR
                }
            },
        }
    }

    fn last_args<'p>(&self, path: &'p hir::Path) -> Option<&'p hir::GenericArgs> {
        path.segments.last().and_then(|s| s.args.as_deref())
    }

    fn lower_resolved(&self, path: &hir::Path, span: Span) -> Ty {
        match path.res {
            Res::PrimTy(p) => {
                if let Some(a) = self.last_args(path)
                    && !a.args.is_empty()
                {
                    self.report(
                        err(
                            span,
                            format!(
                                "type arguments are not allowed on builtin type `{}`",
                                p.name()
                            ),
                        )
                        .code("E0109"),
                    );
                }
                prim_ty(p)
            }
            Res::Def(DefKind::Struct | DefKind::Enum | DefKind::Union, d) => {
                let args = self.lower_args(d, self.last_args(path), &[], None, span);
                Ty::adt(d, args)
            }
            Res::Def(DefKind::TyAlias, d) => {
                let args = self.lower_args(d, self.last_args(path), &[], None, span);
                self.tcx.type_of(d).subst(args)
            }
            Res::Def(DefKind::ForeignTy, d) => Ty::new(TyKind::Foreign(d)),
            Res::Def(DefKind::AssocTy, d) => {
                // `Trait::Assoc` without a self type, inside the trait: `<Self as Trait>::Assoc`.
                let trait_ = self.tcx.assoc_container(d);
                match trait_ {
                    Some(t) if self.tcx.is_trait(t) => {
                        let args = self.tcx.identity_args(t);
                        Ty::new(TyKind::Alias(
                            AliasKind::Projection,
                            AliasTy {
                                def: d,
                                args,
                                index: 0,
                            },
                        ))
                    }
                    _ => {
                        self.report(err(span, "ambiguous associated type").code("E0223"));
                        Ty::ERROR
                    }
                }
            }
            Res::TyParam { index, .. } => {
                let name = path.segments.last().map_or(kw::Empty, |s| s.ident.name);
                Ty::param(index, name)
            }
            Res::SelfTyParam { trait_ } => {
                let g = self.tcx.generics_of(trait_);
                Ty::param(g.parent_count, kw::SelfUpper)
            }
            Res::SelfTyAlias { alias_to } => match self.tcx.hir.def_kind(alias_to) {
                DefKind::Impl { .. } => self.tcx.type_of(alias_to),
                _ => Ty::adt(alias_to, self.tcx.identity_args(alias_to)),
            },
            Res::Def(DefKind::Trait | DefKind::TraitAlias, _) => {
                self.report(
                    err(span, "expected a type, found a trait")
                        .code("E0782")
                        .help("add `dyn` to make a trait object"),
                );
                Ty::ERROR
            }
            Res::Err => Ty::ERROR,
            res => {
                self.report(
                    err(span, format!("expected type, found {}", res.descr())).code("E0573"),
                );
                Ty::ERROR
            }
        }
    }

    /// `<SelfTy as Trait>::Assoc`: the path's last segment is the associated item.
    fn lower_assoc_through_trait(&self, self_ty: Ty, path: &hir::Path, span: Span) -> Ty {
        let Res::Def(DefKind::AssocTy, assoc) = path.res else {
            if path.res != Res::Err {
                self.report(err(span, "expected an associated type"));
            }
            return Ty::ERROR;
        };
        let Some(trait_) = self.tcx.assoc_container(assoc) else {
            return Ty::ERROR;
        };
        // The trait's segment carries the trait's arguments.
        let trait_seg = path
            .segments
            .len()
            .checked_sub(2)
            .map(|i| &path.segments[i]);
        let trait_args = self.lower_args(
            trait_,
            trait_seg.and_then(|s| s.args.as_deref()),
            &[],
            Some(self_ty),
            span,
        );
        let own = path.segments.last().and_then(|s| s.args.as_deref());
        let args = self.lower_args(assoc, own, trait_args.as_slice(), None, span);
        Ty::new(TyKind::Alias(
            AliasKind::Projection,
            AliasTy {
                def: assoc,
                args,
                index: 0,
            },
        ))
    }

    /// `T::Assoc`, `Self::Assoc`: find the trait that defines `Assoc` among the bounds.
    fn lower_type_relative(
        &self,
        base: Ty,
        base_hir: &hir::Ty,
        seg: &hir::PathSegment,
        span: Span,
    ) -> Ty {
        if base.is_error() {
            return Ty::ERROR;
        }
        let name = seg.ident.name;
        let candidates = self.trait_refs_for(base, base_hir);
        for tr in candidates {
            if let Some((assoc, trait_args)) = self.find_assoc_ty(tr, name) {
                let args = self.lower_args(
                    assoc,
                    seg.args.as_deref(),
                    trait_args.as_slice(),
                    None,
                    span,
                );
                return Ty::new(TyKind::Alias(
                    AliasKind::Projection,
                    AliasTy {
                        def: assoc,
                        args,
                        index: 0,
                    },
                ));
            }
        }
        // An inherent associated type, or an enum variant used as a type (an error).
        self.report(
            err(
                span,
                format!("ambiguous associated type `{name}` on `{base}`"),
            )
            .code("E0223")
            .help(format!(
                "use fully-qualified syntax: `<{base} as Trait>::{name}`"
            )),
        );
        Ty::ERROR
    }

    /// A trait (or its supertraits) with an associated type `name`.
    fn find_assoc_ty(&self, tr: TraitRef, name: Symbol) -> Option<(DefId, Args)> {
        if let Some(d) = self.tcx.assoc_item(tr.def, name, false) {
            return Some((d, tr.args));
        }
        for p in self.tcx.predicates_of(tr.def).iter() {
            if let Predicate::Trait(sup) = p
                && sup.def != tr.def
                && sup.self_ty()
                    == Ty::param(self.tcx.generics_of(tr.def).parent_count, kw::SelfUpper)
            {
                let sup = sup.subst(tr.args);
                if let Some(found) = self.find_assoc_ty(sup, name) {
                    return Some(found);
                }
            }
        }
        None
    }

    /// The traits a type is known to implement where it's written: bounds on a type
    /// parameter, the trait itself for `Self` in a trait, the implemented trait for `Self`
    /// in an impl. Found by scanning bounds syntactically, so it can't cycle with
    /// `predicates_of`.
    fn trait_refs_for(&self, base: Ty, base_hir: &hir::Ty) -> Vec<TraitRef> {
        let mut out = Vec::new();
        if let hir::TyKind::Path(hir::QPath::Resolved(None, p)) = &base_hir.kind
            && let Res::SelfTyAlias { alias_to } = p.res
            && matches!(
                self.tcx.hir.def_kind(alias_to),
                DefKind::Impl { of_trait: true }
            )
            && let Some(tr) = self.tcx.impl_trait_ref(alias_to)
        {
            out.push(tr);
            return out;
        }
        let TyKind::Param(index, _) = *base.kind() else {
            return out;
        };
        // Walk the owner and its parents' generics for bounds on this parameter.
        let mut cur = Some(self.owner);
        while let Some(d) = cur {
            if let Some(item) = self.tcx.hir.get_item(d) {
                if let hir::ItemKind::Trait(_) = &item.kind
                    && self.tcx.generics_of(d).parent_count == index
                {
                    out.push(TraitRef::new(d, self.tcx.identity_args(d)));
                }
                let hg = match &item.kind {
                    hir::ItemKind::Fn(f) => Some(&f.generics),
                    hir::ItemKind::Const { generics, .. }
                    | hir::ItemKind::TyAlias { generics, .. } => Some(generics),
                    hir::ItemKind::Struct { generics, .. }
                    | hir::ItemKind::Enum { generics, .. }
                    | hir::ItemKind::Union { generics, .. } => Some(generics),
                    hir::ItemKind::Trait(t) => Some(&t.generics),
                    hir::ItemKind::Impl(i) => Some(&i.generics),
                    _ => None,
                };
                if let Some(hg) = hg {
                    for pred in &hg.predicates {
                        let hir::WherePredicate::Bound { ty, bounds } = pred else {
                            continue;
                        };
                        let is_this = match &ty.kind {
                            hir::TyKind::Path(hir::QPath::Resolved(None, p)) => match p.res {
                                Res::TyParam { index: i, .. } => i == index,
                                Res::SelfTyParam { trait_ } => {
                                    self.tcx.generics_of(trait_).parent_count == index
                                }
                                _ => false,
                            },
                            _ => false,
                        };
                        if !is_this {
                            continue;
                        }
                        for b in bounds {
                            if let hir::GenericBound::Trait {
                                trait_ref,
                                negative: false,
                                maybe: false,
                                ..
                            } = b
                                && let Res::Def(DefKind::Trait, t) = trait_ref.path.res
                            {
                                let seg_args = trait_ref
                                    .path
                                    .segments
                                    .last()
                                    .and_then(|s| s.args.as_deref());
                                let args = self.lower_args_no_bounds(t, seg_args, base);
                                out.push(TraitRef::new(t, args));
                            }
                        }
                    }
                }
                cur = hg.and_then(|g| g.parent);
            } else {
                cur = None;
            }
        }
        out
    }

    /// Trait arguments without associated-type constraints (no projections needed).
    fn lower_args_no_bounds(
        &self,
        trait_: DefId,
        args: Option<&hir::GenericArgs>,
        self_ty: Ty,
    ) -> Args {
        self.lower_args(trait_, args, &[], Some(self_ty), Span::DUMMY)
    }

    /// Generic arguments for `def` from a path segment's arguments: parents' arguments,
    /// `Self` for traits, then this item's own, with defaults and inference filling in.
    pub fn lower_args(
        &self,
        def: DefId,
        args: Option<&hir::GenericArgs>,
        parent_args: &[GenericArg],
        self_ty: Option<Ty>,
        span: Span,
    ) -> Args {
        let g = self.tcx.generics_of(def);
        let mut out: Vec<GenericArg> = parent_args.to_vec();
        out.truncate(g.parent_count as usize);
        // Parents' arguments not given: fill with inference variables or identity.
        while out.len() < g.parent_count as usize {
            let i = out.len() as u32;
            let p = self.tcx.all_params(def).into_iter().find(|p| p.index == i);
            out.push(self.fill_param(def, p.as_ref(), &out, span, self.value_path));
        }
        let infer_own = self.value_path && args.is_none();
        let written: Vec<&hir::GenericArg> = args.map_or(Vec::new(), |a| {
            a.args
                .iter()
                .filter(|a| !matches!(a, hir::GenericArg::Lifetime))
                .collect()
        });
        let mut written = written.into_iter();
        for p in &g.params {
            if g.has_self && p.index == g.parent_count {
                out.push(GenericArg::Ty(self_ty.unwrap_or(Ty::ERROR)));
                continue;
            }
            match written.next() {
                Some(a) => out.push(self.lower_generic_arg(a, &p.kind, def, p.index, &out)),
                None => out.push(self.fill_param(def, Some(p), &out, span, infer_own)),
            }
        }
        if written.next().is_some() && *self.reported.borrow() == 0 {
            self.report(
                err(
                    span,
                    format!(
                        "too many generic arguments for `{}`",
                        self.tcx.def_path(def)
                    ),
                )
                .code("E0107"),
            );
        }
        Args::new(&out)
    }

    fn lower_generic_arg(
        &self,
        a: &hir::GenericArg,
        kind: &GenericParamDefKind,
        def: DefId,
        index: u32,
        so_far: &[GenericArg],
    ) -> GenericArg {
        match (a, kind) {
            (hir::GenericArg::Type(t), GenericParamDefKind::Type { .. }) => {
                GenericArg::Ty(self.lower(t))
            }
            (hir::GenericArg::Const(c), GenericParamDefKind::Const { .. }) => {
                let ty = self.tcx.const_param_ty(def, index).subst(Args::new(so_far));
                GenericArg::Const(self.lower_const_arg(c, ty))
            }
            (hir::GenericArg::Infer, GenericParamDefKind::Type { .. }) => match self.infer {
                Some(f) => GenericArg::Ty(f(Span::DUMMY)),
                None => GenericArg::Ty(Ty::ERROR),
            },
            (hir::GenericArg::Infer, GenericParamDefKind::Const { .. }) => {
                let ty = self.tcx.const_param_ty(def, index);
                GenericArg::Const(match self.infer_const {
                    Some(f) => f(ty),
                    None => Const::error(ty),
                })
            }
            // A path that named a type where a const is expected (or the reverse).
            (hir::GenericArg::Type(t), GenericParamDefKind::Const { .. }) => {
                self.report(
                    err(t.span, "expected a constant argument, found a type").code("E0747"),
                );
                GenericArg::Const(Const::error(Ty::ERROR))
            }
            (hir::GenericArg::Const(_), GenericParamDefKind::Type { .. }) => {
                self.report(
                    err(Span::DUMMY, "expected a type argument, found a constant").code("E0747"),
                );
                GenericArg::Ty(Ty::ERROR)
            }
            (hir::GenericArg::Lifetime, _) => unreachable!(),
        }
    }

    /// An argument not written: its default (unless `prefer_infer`), an inference variable,
    /// or an error.
    fn fill_param(
        &self,
        def: DefId,
        p: Option<&crate::collect::GenericParamDef>,
        so_far: &[GenericArg],
        span: Span,
        prefer_infer: bool,
    ) -> GenericArg {
        let Some(p) = p else {
            return GenericArg::Ty(Ty::ERROR);
        };
        let owner = self.owner_of_param(def, p.index);
        if !(prefer_infer && self.infer.is_some())
            && let Some(d) = self.tcx.param_default(owner, p.index)
        {
            return match d {
                GenericArg::Ty(t) => GenericArg::Ty(t.subst(Args::new(so_far))),
                GenericArg::Const(c) => GenericArg::Const(c.subst(Args::new(so_far))),
            };
        }
        match p.kind {
            GenericParamDefKind::Type { .. } => match self.infer {
                Some(f) => GenericArg::Ty(f(span)),
                None => {
                    if *self.reported.borrow() == 0 {
                        self.report(
                            err(
                                span,
                                format!("missing generics for `{}`", self.tcx.def_path(def)),
                            )
                            .code("E0107"),
                        );
                    }
                    GenericArg::Ty(Ty::ERROR)
                }
            },
            GenericParamDefKind::Const { .. } => {
                let ty = self.tcx.const_param_ty(owner, p.index);
                GenericArg::Const(match self.infer_const {
                    Some(f) => f(ty),
                    None => Const::error(ty),
                })
            }
        }
    }

    fn owner_of_param(&self, def: DefId, index: u32) -> DefId {
        let mut cur = def;
        loop {
            let g = self.tcx.generics_of(cur);
            if index >= g.parent_count || g.parent.is_none() {
                return cur;
            }
            cur = g.parent.unwrap();
        }
    }

    /// A trait path with a self type: the trait reference, and `Assoc = T` constraints as
    /// projection predicates.
    pub fn lower_trait_ref(
        &self,
        path: &hir::Path,
        self_ty: Ty,
        projections: &mut Vec<(AliasTy, Ty)>,
    ) -> Option<TraitRef> {
        let trait_ = match path.res {
            Res::Def(DefKind::Trait, d) => d,
            Res::Def(DefKind::TraitAlias, d) => d,
            Res::Err => return None,
            res => {
                self.report(
                    err(path.span, format!("expected trait, found {}", res.descr())).code("E0404"),
                );
                return None;
            }
        };
        let seg_args = path.segments.last().and_then(|s| s.args.as_deref());
        let args = self.lower_args(trait_, seg_args, &[], Some(self_ty), path.span);
        let tr = TraitRef::new(trait_, args);
        if let Some(ga) = seg_args {
            for c in &ga.constraints {
                let Some((assoc, trait_args)) = self.find_assoc_ty(tr, c.name.name) else {
                    self.report(
                        err(
                            c.name.span,
                            format!(
                                "associated type `{}` not found for `{}`",
                                c.name,
                                self.tcx.def_path(trait_)
                            ),
                        )
                        .code("E0220"),
                    );
                    continue;
                };
                let alias_args = self.lower_args(
                    assoc,
                    c.args.as_deref(),
                    trait_args.as_slice(),
                    None,
                    c.name.span,
                );
                let alias = AliasTy {
                    def: assoc,
                    args: alias_args,
                    index: 0,
                };
                match &c.kind {
                    hir::AssocConstraintKind::Equality(t) => {
                        projections.push((alias, self.lower(t)))
                    }
                    hir::AssocConstraintKind::EqualityConst(_) => {}
                    hir::AssocConstraintKind::Bound(_) => {}
                }
            }
        }
        Some(tr)
    }

    /// Bounds on `self_ty` as predicates.
    pub fn lower_bounds(
        &self,
        self_ty: Ty,
        bounds: &[hir::GenericBound],
        out: &mut Vec<Predicate>,
    ) {
        for b in bounds {
            let hir::GenericBound::Trait {
                trait_ref,
                maybe,
                negative,
                ..
            } = b
            else {
                continue;
            };
            if *maybe {
                out.push(Predicate::MaybeSized(self_ty));
                continue;
            }
            let mut projections = Vec::new();
            let Some(tr) = self.lower_trait_ref(&trait_ref.path, self_ty, &mut projections) else {
                continue;
            };
            out.push(if *negative {
                Predicate::NegTrait(tr)
            } else {
                Predicate::Trait(tr)
            });
            for (alias, ty) in projections {
                out.push(Predicate::Projection(alias, ty));
            }
            // `T: Trait<Assoc: Bound>`: bounds on the projection.
            let seg_args = trait_ref
                .path
                .segments
                .last()
                .and_then(|s| s.args.as_deref());
            if let Some(ga) = seg_args {
                for c in &ga.constraints {
                    if let hir::AssocConstraintKind::Bound(inner) = &c.kind
                        && let Some((assoc, trait_args)) = self.find_assoc_ty(tr, c.name.name)
                    {
                        let alias = AliasTy {
                            def: assoc,
                            args: trait_args,
                            index: 0,
                        };
                        let proj = Ty::new(TyKind::Alias(AliasKind::Projection, alias));
                        self.lower_bounds(proj, inner, out);
                    }
                }
            }
        }
    }

    /// `dyn Trait<A, Assoc = B> + Send`
    fn lower_dyn(&self, bounds: &[hir::GenericBound], span: Span) -> Ty {
        let mut preds = Vec::new();
        let dummy_self = Ty::ERROR;
        for b in bounds {
            let hir::GenericBound::Trait {
                trait_ref,
                maybe: false,
                ..
            } = b
            else {
                continue;
            };
            let mut projections = Vec::new();
            let Some(tr) = self.lower_trait_ref(&trait_ref.path, dummy_self, &mut projections)
            else {
                continue;
            };
            if self.tcx.is_auto_trait(tr.def) {
                preds.push(ExistentialPredicate::AutoTrait(tr.def));
                continue;
            }
            let args = Args::new(&tr.args.as_slice()[1..]);
            preds.push(ExistentialPredicate::Trait { def: tr.def, args });
            for (alias, ty) in projections {
                preds.push(ExistentialPredicate::Projection {
                    def: alias.def,
                    args: Args::new(&alias.args.as_slice()[1..]),
                    term: ty,
                });
            }
        }
        if preds
            .iter()
            .filter(|p| matches!(p, ExistentialPredicate::Trait { .. }))
            .count()
            > 1
        {
            self.report(
                err(
                    span,
                    "only auto traits can be used as additional traits in a trait object",
                )
                .code("E0225"),
            );
        }
        // Principal first, then projections, then auto traits sorted (a canonical order).
        preds.sort_by_key(|p| match p {
            ExistentialPredicate::Trait { .. } => (0, 0),
            ExistentialPredicate::Projection { def, .. } => (1, def.0),
            ExistentialPredicate::AutoTrait(d) => (2, d.0),
        });
        preds.dedup();
        Ty::new(TyKind::Dynamic(PredList::new(&preds)))
    }
}

pub fn prim_ty(p: PrimTy) -> Ty {
    match p {
        PrimTy::Bool => Ty::BOOL,
        PrimTy::Char => Ty::CHAR,
        PrimTy::Str => Ty::STR,
        PrimTy::Int(i) => Ty::int(i),
        PrimTy::Uint(u) => Ty::uint(u),
        PrimTy::Float(f) => Ty::float(f),
    }
}
