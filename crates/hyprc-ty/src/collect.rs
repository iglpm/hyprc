//! Item-level queries: generics, where-clauses, types, signatures, ADT definitions, impls.

use crate::TyCtxt;
use crate::lower_ty::TyLowerer;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{BodyId, CtorShape, DefId, DefKind, Mutability, Res};
use hyprc_span::{FxHashMap, Span, Symbol, kw};
use std::sync::{Arc, OnceLock};

#[derive(Clone, Debug)]
pub struct Generics {
    pub def: DefId,
    pub parent: Option<DefId>,
    pub parent_count: u32,
    /// This item's own parameters (for traits, `Self` first).
    pub params: Vec<GenericParamDef>,
    pub has_self: bool,
}

#[derive(Clone, Debug)]
pub struct GenericParamDef {
    pub name: Symbol,
    pub index: u32,
    pub kind: GenericParamDefKind,
}

#[derive(Clone, Debug)]
pub enum GenericParamDefKind {
    Type { has_default: bool, synthetic: bool },
    Const { has_default: bool },
}

impl Generics {
    pub fn count(&self) -> u32 {
        self.parent_count + self.params.len() as u32
    }

    pub fn own_count(&self) -> usize {
        self.params.len()
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AdtKind {
    Struct,
    Enum,
    Union,
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub name: Symbol,
    pub ty: Ty,
    pub vis: hir::Vis,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct VariantDef {
    /// The variant's `DefId`, or the struct's for structs and unions.
    pub def: DefId,
    pub name: Symbol,
    pub fields: Vec<FieldDef>,
    pub shape: CtorShape,
    /// An explicit discriminant (`A = 5`).
    pub discr_body: Option<BodyId>,
}

#[derive(Clone, Debug)]
pub struct AdtDef {
    pub def: DefId,
    pub kind: AdtKind,
    pub variants: Vec<VariantDef>,
    pub repr: hir::Repr,
    /// `Box<T>`: the `owned_box` lang item.
    pub is_box: bool,
    pub is_phantom_data: bool,
    pub is_manually_drop: bool,
    pub non_exhaustive: bool,
}

impl AdtDef {
    pub fn is_enum(&self) -> bool {
        self.kind == AdtKind::Enum
    }

    pub fn is_struct(&self) -> bool {
        self.kind == AdtKind::Struct
    }

    pub fn is_union(&self) -> bool {
        self.kind == AdtKind::Union
    }

    pub fn non_enum_variant(&self) -> &VariantDef {
        &self.variants[0]
    }

    pub fn variant_index(&self, def: DefId) -> Option<usize> {
        self.variants.iter().position(|v| v.def == def)
    }
}

/// A type reduced to what impls can be indexed by.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SimplifiedType {
    Bool,
    Char,
    Int(hir::IntTy),
    Uint(hir::UintTy),
    Float(hir::FloatTy),
    Str,
    Never,
    Adt(DefId),
    Foreign(DefId),
    Array,
    Slice,
    Ptr(Mutability),
    Ref(Mutability),
    FnPtr(usize),
    Tuple(usize),
    Dyn(Option<DefId>),
    Closure,
    Pat,
}

pub fn simplify(t: Ty) -> Option<SimplifiedType> {
    Some(match *t.kind() {
        TyKind::Bool => SimplifiedType::Bool,
        TyKind::Char => SimplifiedType::Char,
        TyKind::Int(i) => SimplifiedType::Int(i),
        TyKind::Uint(u) => SimplifiedType::Uint(u),
        TyKind::Float(f) => SimplifiedType::Float(f),
        TyKind::Str => SimplifiedType::Str,
        TyKind::Never => SimplifiedType::Never,
        TyKind::Adt(d, _) => SimplifiedType::Adt(d),
        TyKind::Foreign(d) => SimplifiedType::Foreign(d),
        TyKind::Array(..) => SimplifiedType::Array,
        TyKind::Slice(_) => SimplifiedType::Slice,
        TyKind::RawPtr(_, m) => SimplifiedType::Ptr(m),
        TyKind::Ref(_, m) => SimplifiedType::Ref(m),
        TyKind::FnPtr(sig) => SimplifiedType::FnPtr(sig.inputs().len()),
        TyKind::FnDef(..) => SimplifiedType::FnPtr(usize::MAX),
        TyKind::Tuple(ts) => SimplifiedType::Tuple(ts.as_slice().len()),
        TyKind::Dynamic(p) => SimplifiedType::Dyn(p.principal().map(|(d, _)| d)),
        TyKind::Closure(..) | TyKind::Coroutine(..) => SimplifiedType::Closure,
        TyKind::Pat(..) => SimplifiedType::Pat,
        _ => return None,
    })
}

#[derive(Default, Debug)]
pub struct TraitImpls {
    pub all: Vec<DefId>,
    pub blanket: Vec<DefId>,
    pub non_blanket: FxHashMap<SimplifiedType, Vec<DefId>>,
}

pub struct Queries {
    generics: Vec<OnceLock<Arc<Generics>>>,
    predicates: Vec<OnceLock<Arc<Vec<Predicate>>>>,
    type_of: Vec<OnceLock<Ty>>,
    fn_sig: Vec<OnceLock<FnSig>>,
    adt: Vec<OnceLock<Arc<AdtDef>>>,
    impl_trait_ref: Vec<OnceLock<Option<TraitRef>>>,
    assoc_by_name: Vec<OnceLock<Arc<FxHashMap<(Symbol, bool), DefId>>>>,
    item_bounds: Vec<OnceLock<Arc<Vec<Predicate>>>>,
    pub(crate) param_env: Vec<OnceLock<Arc<crate::traits::ParamEnv>>>,
    /// `impl_specializes(a, b)` answers.
    specializes: std::sync::Mutex<FxHashMap<(DefId, DefId), bool>>,
    trait_impls: OnceLock<FxHashMap<DefId, TraitImpls>>,
    inherent_impls: OnceLock<FxHashMap<SimplifiedType, Vec<DefId>>>,
    /// Impls whose self type is a parameter or otherwise can't be indexed (blanket impls).
    blanket_impls: OnceLock<FxHashMap<DefId, Vec<DefId>>>,
}

impl Queries {
    pub fn new(n: usize) -> Queries {
        fn v<T>(n: usize) -> Vec<OnceLock<T>> {
            (0..n).map(|_| OnceLock::new()).collect()
        }
        Queries {
            generics: v(n),
            predicates: v(n),
            type_of: v(n),
            fn_sig: v(n),
            adt: v(n),
            impl_trait_ref: v(n),
            assoc_by_name: v(n),
            item_bounds: v(n),
            param_env: v(n),
            specializes: Default::default(),
            trait_impls: OnceLock::new(),
            inherent_impls: OnceLock::new(),
            blanket_impls: OnceLock::new(),
        }
    }
}

const Q_TYPE_OF: u8 = 1;
const Q_PREDICATES: u8 = 2;
const Q_SIG: u8 = 3;
const Q_ADT: u8 = 4;
const Q_ITEM_BOUNDS: u8 = 5;

impl<'h> TyCtxt<'h> {
    fn hir_generics(&self, def: DefId) -> Option<&'h hir::Generics> {
        let item = self.hir.get_item(def)?;
        Some(match &item.kind {
            hir::ItemKind::Fn(f) => &f.generics,
            hir::ItemKind::Const { generics, .. } => generics,
            hir::ItemKind::Struct { generics, .. }
            | hir::ItemKind::Union { generics, .. }
            | hir::ItemKind::Enum { generics, .. } => generics,
            hir::ItemKind::TyAlias { generics, .. } => generics,
            hir::ItemKind::Trait(t) => &t.generics,
            hir::ItemKind::TraitAlias { generics, .. } => generics,
            hir::ItemKind::Impl(i) => &i.generics,
            _ => return None,
        })
    }

    /// The generic parameters of an item, parents included by reference.
    pub fn generics_of(&self, def: DefId) -> Arc<Generics> {
        self.q.generics[def.0 as usize]
            .get_or_init(|| {
                let kind = self.hir.def_kind(def);
                // Variants and constructors share their enum's (or struct's) generics.
                if kind == DefKind::Variant
                    && let Some(p) = self.hir.parent(def)
                {
                    let g = self.generics_of(p);
                    return Arc::new(Generics {
                        def,
                        ..(*g).clone()
                    });
                }
                let Some(hg) = self.hir_generics(def) else {
                    return Arc::new(Generics {
                        def,
                        parent: None,
                        parent_count: 0,
                        params: Vec::new(),
                        has_self: false,
                    });
                };
                let parent_count = hg.parent.map_or(0, |p| self.generics_of(p).count());
                let mut params = Vec::new();
                if hg.has_self {
                    params.push(GenericParamDef {
                        name: kw::SelfUpper,
                        index: parent_count,
                        kind: GenericParamDefKind::Type {
                            has_default: false,
                            synthetic: false,
                        },
                    });
                }
                for p in &hg.params {
                    params.push(GenericParamDef {
                        name: p.name,
                        index: p.index,
                        kind: match &p.kind {
                            hir::GenericParamKind::Type { default } => GenericParamDefKind::Type {
                                has_default: default.is_some(),
                                synthetic: p.synthetic,
                            },
                            hir::GenericParamKind::Const { default, .. } => {
                                GenericParamDefKind::Const {
                                    has_default: default.is_some(),
                                }
                            }
                        },
                    });
                }
                Arc::new(Generics {
                    def,
                    parent: hg.parent,
                    parent_count,
                    params,
                    has_self: hg.has_self,
                })
            })
            .clone()
    }

    /// All parameters of an item in order, parents first.
    pub fn all_params(&self, def: DefId) -> Vec<GenericParamDef> {
        let g = self.generics_of(def);
        let mut out = match g.parent {
            Some(p) => self.all_params(p),
            None => Vec::new(),
        };
        out.extend(g.params.iter().cloned());
        out
    }

    /// The arguments that name an item's own parameters: `Param(0), Param(1), …`.
    pub fn identity_args(&self, def: DefId) -> Args {
        let params = self.all_params(def);
        let v: Vec<GenericArg> = params
            .iter()
            .map(|p| match p.kind {
                GenericParamDefKind::Type { .. } => GenericArg::Ty(Ty::param(p.index, p.name)),
                GenericParamDefKind::Const { .. } => {
                    let ty = self.const_param_ty(def, p.index);
                    GenericArg::Const(Const::new(ty, ConstKind::Param(p.index, p.name)))
                }
            })
            .collect();
        Args::new(&v)
    }

    /// The type of a const parameter.
    pub fn const_param_ty(&self, def: DefId, index: u32) -> Ty {
        let mut cur = Some(def);
        while let Some(d) = cur {
            if let Some(hg) = self.hir_generics(d) {
                for p in &hg.params {
                    if p.index == index
                        && let hir::GenericParamKind::Const { ty, .. } = &p.kind
                    {
                        return TyLowerer::new(self, d).lower(ty);
                    }
                }
                cur = hg.parent;
            } else {
                cur = self.hir.parent(d);
            }
        }
        Ty::ERROR
    }

    /// The default of a generic parameter, in terms of the earlier parameters.
    pub fn param_default(&self, def: DefId, index: u32) -> Option<GenericArg> {
        let hg = self.hir_generics(def)?;
        let p = hg.params.iter().find(|p| p.index == index)?;
        match &p.kind {
            hir::GenericParamKind::Type { default: Some(t) } => {
                Some(GenericArg::Ty(TyLowerer::new(self, def).lower(t)))
            }
            hir::GenericParamKind::Const {
                default: Some(b),
                ty,
            } => {
                let ty = TyLowerer::new(self, def).lower(ty);
                Some(GenericArg::Const(self.eval_const_body(
                    *b,
                    ty,
                    self.identity_args(def),
                )))
            }
            _ => None,
        }
    }

    /// The where-clauses of an item, its parents' included, with implied `Sized` bounds.
    pub fn predicates_of(&self, def: DefId) -> Arc<Vec<Predicate>> {
        if let Some(p) = self.q.predicates[def.0 as usize].get() {
            return p.clone();
        }
        let preds = self.guarded(
            Q_PREDICATES,
            def,
            || Arc::new(Vec::new()),
            || Arc::new(self.compute_predicates(def)),
        );
        let _ = self.q.predicates[def.0 as usize].set(preds.clone());
        self.q.predicates[def.0 as usize].get().unwrap().clone()
    }

    fn compute_predicates(&self, def: DefId) -> Vec<Predicate> {
        let mut out = Vec::new();
        let kind = self.hir.def_kind(def);
        if kind == DefKind::Variant {
            if let Some(p) = self.hir.parent(def) {
                return (*self.predicates_of(p)).clone();
            }
        }
        let Some(hg) = self.hir_generics(def) else {
            return out;
        };
        if let Some(p) = hg.parent {
            out.extend(self.predicates_of(p).iter().copied());
        }
        let lowerer = TyLowerer::new(self, def);
        let mut maybe_sized: Vec<Ty> = Vec::new();
        for pred in &hg.predicates {
            match pred {
                hir::WherePredicate::Bound { ty, bounds } => {
                    let ty = lowerer.lower(ty);
                    if self.relaxes_sized(bounds) {
                        maybe_sized.push(ty);
                    }
                    lowerer.lower_bounds(ty, bounds, &mut out);
                }
                hir::WherePredicate::Eq { .. } => {}
            }
        }
        // Every type parameter is `Sized` unless it says `?Sized`.
        if let Some(sized) = self.lang_item("sized") {
            for p in &hg.params {
                if let hir::GenericParamKind::Type { .. } = p.kind {
                    let t = Ty::param(p.index, p.name);
                    if !maybe_sized.contains(&t) {
                        out.push(Predicate::Trait(TraitRef::new(sized, Args::from_tys(&[t]))));
                    }
                }
            }
        }
        // In a trait: `Self: Trait`, and the supertraits.
        if let Some(item) = self.hir.get_item(def)
            && let hir::ItemKind::Trait(t) = &item.kind
        {
            let self_ty = Ty::param(hg.parent_count, kw::SelfUpper);
            out.push(Predicate::Trait(TraitRef::new(
                def,
                self.identity_args(def),
            )));
            lowerer.lower_bounds(self_ty, &t.supertraits, &mut out);
        }
        // A trait alias: its bounds, about `Self` (`trait Thin = Pointee<Metadata = ()>`).
        if let Some(item) = self.hir.get_item(def)
            && let hir::ItemKind::TraitAlias { bounds, .. } = &item.kind
        {
            let self_ty = Ty::param(hg.parent_count, kw::SelfUpper);
            lowerer.lower_bounds(self_ty, bounds, &mut out);
        }
        out
    }

    /// Do these bounds opt out of the implicit `Sized`: `?Sized`, or a bound from the sized
    /// hierarchy (`PointeeSized`, `MetaSized`)?
    pub fn relaxes_sized(&self, bounds: &[hir::GenericBound]) -> bool {
        bounds.iter().any(|b| match b {
            hir::GenericBound::Trait {
                maybe: true,
                trait_ref,
                ..
            } => self.is_lang(trait_ref.path.res, "sized"),
            hir::GenericBound::Trait {
                maybe: false,
                negative: false,
                trait_ref,
                ..
            } => {
                self.is_lang(trait_ref.path.res, "pointee_sized")
                    || self.is_lang(trait_ref.path.res, "meta_sized")
            }
            _ => false,
        })
    }

    /// The bounds of the `index`-th `impl Trait` in `owner`'s signature, about that opaque
    /// type (`impl FnMut(u8) -> bool`: `Opaque: FnMut<(u8,)>`, `<Opaque as FnOnce>::Output == bool`).
    pub fn opaque_bounds(&self, owner: DefId, index: u32) -> Vec<Predicate> {
        fn in_args<'t>(a: &'t hir::GenericArgs, index: u32) -> Option<&'t [hir::GenericBound]> {
            a.args
                .iter()
                .find_map(|g| match g {
                    hir::GenericArg::Type(t) => find(t, index),
                    _ => None,
                })
                .or_else(|| {
                    a.constraints.iter().find_map(|c| match &c.kind {
                        hir::AssocConstraintKind::Equality(t) => find(t, index),
                        hir::AssocConstraintKind::Bound(bs) => in_bounds(bs, index),
                        hir::AssocConstraintKind::EqualityConst(_) => None,
                    })
                })
        }
        fn in_bounds<'t>(
            bs: &'t [hir::GenericBound],
            index: u32,
        ) -> Option<&'t [hir::GenericBound]> {
            bs.iter().find_map(|b| match b {
                hir::GenericBound::Trait { trait_ref, .. } => trait_ref
                    .path
                    .segments
                    .iter()
                    .find_map(|s| s.args.as_deref().and_then(|a| in_args(a, index))),
                hir::GenericBound::Outlives => None,
            })
        }
        fn find(t: &hir::Ty, index: u32) -> Option<&[hir::GenericBound]> {
            match &t.kind {
                hir::TyKind::Opaque {
                    index: i, bounds, ..
                } => {
                    if *i == index {
                        Some(bounds)
                    } else {
                        in_bounds(bounds, index)
                    }
                }
                hir::TyKind::Ref(_, t)
                | hir::TyKind::Ptr(_, t)
                | hir::TyKind::Slice(t)
                | hir::TyKind::Array(t, _)
                | hir::TyKind::Pat(t, _) => find(t, index),
                hir::TyKind::Tup(ts) => ts.iter().find_map(|t| find(t, index)),
                hir::TyKind::Path(q) => {
                    let mut q = q;
                    loop {
                        match q {
                            hir::QPath::Resolved(qself, path) => {
                                return qself.as_deref().and_then(|t| find(t, index)).or_else(
                                    || {
                                        path.segments.iter().find_map(|s| {
                                            s.args.as_deref().and_then(|a| in_args(a, index))
                                        })
                                    },
                                );
                            }
                            hir::QPath::TypeRelative(base, seg) => {
                                if let Some(b) = seg.args.as_deref().and_then(|a| in_args(a, index))
                                {
                                    return Some(b);
                                }
                                match &base.kind {
                                    hir::TyKind::Path(inner) => q = inner,
                                    _ => return find(base, index),
                                }
                            }
                            hir::QPath::LangItem(..) => return None,
                        }
                    }
                }
                hir::TyKind::FnPtr(f) => f
                    .inputs
                    .iter()
                    .chain(f.output.as_ref())
                    .find_map(|t| find(t, index)),
                hir::TyKind::TraitObject(bs) => in_bounds(bs, index),
                _ => None,
            }
        }
        let Some(item) = self.hir.get_item(owner) else {
            return Vec::new();
        };
        let hir::ItemKind::Fn(f) = &item.kind else {
            return Vec::new();
        };
        let Some(bounds) = f.sig.output.as_ref().and_then(|t| find(t, index)) else {
            return Vec::new();
        };
        let alias = AliasTy {
            def: owner,
            args: self.identity_args(owner),
            index,
        };
        let self_ty = Ty::new(TyKind::Alias(AliasKind::Opaque, alias));
        let mut out = Vec::new();
        TyLowerer::new(self, owner).lower_bounds(self_ty, bounds, &mut out);
        out
    }

    /// What an `impl Trait` return type of `owner` is: the type its body returns (in
    /// `owner`'s generic parameters). For code generation; type checking keeps it opaque.
    pub fn opaque_hidden_type(&self, owner: DefId, index: u32) -> Ty {
        let body = match self.hir.get_item(owner).map(|i| &i.kind) {
            Some(hir::ItemKind::Fn(f)) => f.body,
            _ => None,
        };
        let Some(body) = body else { return Ty::ERROR };
        self.typeck(body)
            .opaque_hidden
            .iter()
            .find(|(i, _)| *i == index)
            .map_or(Ty::ERROR, |&(_, t)| t)
    }

    /// Is an associated type `Sized` by its declaration (no `?Sized` or weaker bound)?
    pub fn assoc_ty_is_sized(&self, def: DefId) -> bool {
        match self.hir.get_item(def).map(|i| &i.kind) {
            Some(hir::ItemKind::TyAlias { bounds, .. }) => !self.relaxes_sized(bounds),
            _ => true,
        }
    }

    pub fn is_lang(&self, res: Res, name: &str) -> bool {
        match (res, self.lang_item(name)) {
            (Res::Def(_, d), Some(l)) => d == l,
            _ => false,
        }
    }

    /// The bounds of an associated type, about `<Self as Trait>::Assoc` (`type Item: Clone`).
    pub fn item_bounds(&self, def: DefId) -> Arc<Vec<Predicate>> {
        if let Some(p) = self.q.item_bounds[def.0 as usize].get() {
            return p.clone();
        }
        let preds = self.guarded(
            Q_ITEM_BOUNDS,
            def,
            || Arc::new(Vec::new()),
            || {
                let mut out = Vec::new();
                if let Some(item) = self.hir.get_item(def)
                    && let hir::ItemKind::TyAlias { bounds, .. } = &item.kind
                {
                    let alias = AliasTy {
                        def,
                        args: self.identity_args(def),
                        index: 0,
                    };
                    let self_ty = Ty::new(TyKind::Alias(AliasKind::Projection, alias));
                    TyLowerer::new(self, def).lower_bounds(self_ty, bounds, &mut out);
                }
                Arc::new(out)
            },
        );
        let _ = self.q.item_bounds[def.0 as usize].set(preds.clone());
        self.q.item_bounds[def.0 as usize].get().unwrap().clone()
    }

    /// The type of an item: what a path to it has (before substitution).
    pub fn type_of(&self, def: DefId) -> Ty {
        if let Some(&t) = self.q.type_of[def.0 as usize].get() {
            return t;
        }
        let t = self.guarded(
            Q_TYPE_OF,
            def,
            || {
                self.emit(Diag_cycle(
                    self.hir.span(def),
                    format!(
                        "cycle detected when computing the type of `{}`",
                        self.def_path(def)
                    ),
                ));
                Ty::ERROR
            },
            || self.compute_type_of(def),
        );
        let _ = self.q.type_of[def.0 as usize].set(t);
        *self.q.type_of[def.0 as usize].get().unwrap()
    }

    fn compute_type_of(&self, def: DefId) -> Ty {
        let kind = self.hir.def_kind(def);
        match kind {
            DefKind::Struct | DefKind::Enum | DefKind::Union => {
                return Ty::adt(def, self.identity_args(def));
            }
            DefKind::Variant => {
                let parent = self.hir.parent(def).unwrap();
                return Ty::adt(parent, self.identity_args(parent));
            }
            DefKind::Fn | DefKind::AssocFn => return Ty::fn_def(def, self.identity_args(def)),
            DefKind::ForeignTy => return Ty::new(TyKind::Foreign(def)),
            _ => {}
        }
        let Some(item) = self.hir.get_item(def) else {
            return Ty::ERROR;
        };
        let lowerer = TyLowerer::new(self, def);
        match &item.kind {
            hir::ItemKind::Const { ty, .. } | hir::ItemKind::Static { ty, .. } => lowerer.lower(ty),
            hir::ItemKind::TyAlias { ty: Some(ty), .. } => lowerer.lower(ty),
            hir::ItemKind::TyAlias { ty: None, .. } => {
                // An associated type without a value (in a trait): the projection itself.
                let alias = AliasTy {
                    def,
                    args: self.identity_args(def),
                    index: 0,
                };
                Ty::new(TyKind::Alias(AliasKind::Projection, alias))
            }
            hir::ItemKind::Impl(imp) => lowerer.lower(&imp.self_ty),
            _ => Ty::ERROR,
        }
    }

    /// The signature of a function, or of a tuple struct's or variant's constructor.
    pub fn fn_sig(&self, def: DefId) -> FnSig {
        if let Some(&s) = self.q.fn_sig[def.0 as usize].get() {
            return s;
        }
        let sig = self.guarded(
            Q_SIG,
            def,
            || FnSig::new(&[], Ty::ERROR, false, false, Abi::Rust),
            || self.compute_fn_sig(def),
        );
        let _ = self.q.fn_sig[def.0 as usize].set(sig);
        *self.q.fn_sig[def.0 as usize].get().unwrap()
    }

    fn compute_fn_sig(&self, def: DefId) -> FnSig {
        match self.hir.def_kind(def) {
            DefKind::Struct | DefKind::Variant => {
                let adt_def = if self.hir.def_kind(def) == DefKind::Variant {
                    self.hir.parent(def).unwrap()
                } else {
                    def
                };
                let adt = self.adt_def(adt_def);
                let v = adt
                    .variants
                    .iter()
                    .find(|v| v.def == def)
                    .unwrap_or(&adt.variants[0]);
                let inputs: Vec<Ty> = v.fields.iter().map(|f| f.ty).collect();
                return FnSig::new(
                    &inputs,
                    Ty::adt(adt_def, self.identity_args(adt_def)),
                    false,
                    false,
                    Abi::Rust,
                );
            }
            _ => {}
        }
        let Some(item) = self.hir.get_item(def) else {
            return FnSig::new(&[], Ty::ERROR, false, false, Abi::Rust);
        };
        let hir::ItemKind::Fn(f) = &item.kind else {
            return FnSig::new(&[], Ty::ERROR, false, false, Abi::Rust);
        };
        let lowerer = TyLowerer::new(self, def);
        let inputs: Vec<Ty> = f.sig.inputs.iter().map(|t| lowerer.lower(t)).collect();
        let output = f.sig.output.as_ref().map_or(Ty::UNIT, |t| lowerer.lower(t));
        let abi = match f.sig.abi {
            hir::Abi::Rust => Abi::Rust,
            hir::Abi::C => Abi::C,
            hir::Abi::Other(s) => match s.as_str() {
                "rust-call" => Abi::RustCall,
                "rust-intrinsic" => Abi::RustIntrinsic,
                "system" | "system-unwind" => Abi::System,
                "unadjusted" => Abi::Unadjusted,
                _ => Abi::Other(s),
            },
        };
        let abi = if item.attrs.rustc_intrinsic {
            Abi::RustIntrinsic
        } else {
            abi
        };
        FnSig::new(&inputs, output, f.sig.c_variadic, f.sig.safety_unsafe, abi)
    }

    /// A struct's, enum's or union's definition.
    pub fn adt_def(&self, def: DefId) -> Arc<AdtDef> {
        if let Some(a) = self.q.adt[def.0 as usize].get() {
            return a.clone();
        }
        let adt = self.guarded(
            Q_ADT,
            def,
            || Arc::new(empty_adt(def)),
            || Arc::new(self.compute_adt_def(def)),
        );
        let _ = self.q.adt[def.0 as usize].set(adt);
        self.q.adt[def.0 as usize].get().unwrap().clone()
    }

    fn compute_adt_def(&self, def: DefId) -> AdtDef {
        let Some(item) = self.hir.get_item(def) else {
            return empty_adt(def);
        };
        let lowerer = TyLowerer::new(self, def);
        let lower_fields = |data: &hir::VariantData| -> Vec<FieldDef> {
            data.fields
                .iter()
                .map(|f| FieldDef {
                    name: f.name,
                    ty: lowerer.lower(&f.ty),
                    vis: f.vis,
                    span: f.span,
                })
                .collect()
        };
        let (kind, variants) = match &item.kind {
            hir::ItemKind::Struct { data, .. } => (
                AdtKind::Struct,
                vec![VariantDef {
                    def,
                    name: item.name,
                    fields: lower_fields(data),
                    shape: data.kind,
                    discr_body: None,
                }],
            ),
            hir::ItemKind::Union { data, .. } => (
                AdtKind::Union,
                vec![VariantDef {
                    def,
                    name: item.name,
                    fields: lower_fields(data),
                    shape: data.kind,
                    discr_body: None,
                }],
            ),
            hir::ItemKind::Enum { variants, .. } => (
                AdtKind::Enum,
                variants
                    .iter()
                    .map(|v| VariantDef {
                        def: v.def,
                        name: v.name,
                        fields: lower_fields(&v.data),
                        shape: v.data.kind,
                        discr_body: v.discr,
                    })
                    .collect(),
            ),
            _ => return empty_adt(def),
        };
        AdtDef {
            def,
            kind,
            variants,
            repr: item.attrs.repr.clone(),
            is_box: self.lang_item("owned_box") == Some(def),
            is_phantom_data: self.lang_item("phantom_data") == Some(def),
            is_manually_drop: self.lang_item("manually_drop") == Some(def),
            non_exhaustive: item.attrs.non_exhaustive,
        }
    }

    /// The trait an impl implements, with the impl's self type as `Self`.
    pub fn impl_trait_ref(&self, def: DefId) -> Option<TraitRef> {
        *self.q.impl_trait_ref[def.0 as usize].get_or_init(|| {
            let item = self.hir.get_item(def)?;
            let hir::ItemKind::Impl(imp) = &item.kind else {
                return None;
            };
            let t = imp.of_trait.as_ref()?;
            let self_ty = self.type_of(def);
            let lowerer = TyLowerer::new(self, def);
            let mut projections = Vec::new();
            lowerer.lower_trait_ref(&t.path, self_ty, &mut projections)
        })
    }

    /// An associated item of a trait or impl, by name; `value`: functions and consts (or
    /// types).
    pub fn assoc_item(&self, container: DefId, name: Symbol, value: bool) -> Option<DefId> {
        let map = self.q.assoc_by_name[container.0 as usize].get_or_init(|| {
            let mut m = FxHashMap::default();
            if let Some(item) = self.hir.get_item(container) {
                let items = match &item.kind {
                    hir::ItemKind::Trait(t) => &t.items,
                    hir::ItemKind::Impl(i) => &i.items,
                    _ => return Arc::new(m),
                };
                for &d in items {
                    let is_value =
                        matches!(self.hir.def_kind(d), DefKind::AssocFn | DefKind::AssocConst);
                    m.insert((self.hir.name(d), is_value), d);
                }
            }
            Arc::new(m)
        });
        map.get(&(name, value)).copied()
    }

    /// The items of a trait or impl.
    pub fn assoc_items(&self, container: DefId) -> &'h [DefId] {
        match self.hir.get_item(container).map(|i| &i.kind) {
            Some(hir::ItemKind::Trait(t)) => &t.items,
            Some(hir::ItemKind::Impl(i)) => &i.items,
            _ => &[],
        }
    }

    /// The trait or impl an associated item belongs to.
    pub fn assoc_container(&self, def: DefId) -> Option<DefId> {
        let p = self.hir.parent(def)?;
        matches!(self.hir.def_kind(p), DefKind::Trait | DefKind::Impl { .. }).then_some(p)
    }

    /// Impls of a trait, indexed by their self type's simplified shape.
    pub fn trait_impl_table(&self, trait_: DefId) -> Option<&TraitImpls> {
        let map = self.q.trait_impls.get_or_init(|| {
            let mut m: FxHashMap<DefId, TraitImpls> = FxHashMap::default();
            for &imp in &self.hir.impls {
                if let Some(t) = self.impl_trait_ref(imp) {
                    let entry = m.entry(t.def).or_default();
                    entry.all.push(imp);
                    let self_ty = self.type_of(imp);
                    if let Some(st) = simplify(self_ty) {
                        entry.non_blanket.entry(st).or_default().push(imp);
                    } else {
                        entry.blanket.push(imp);
                    }
                }
            }
            m
        });
        map.get(&trait_)
    }

    /// All impls of a trait.
    pub fn trait_impls(&self, trait_: DefId) -> &[DefId] {
        self.trait_impl_table(trait_).map_or(&[], |t| &t.all)
    }

    /// Iterates only over impls of `trait_` that can match `self_ty`.
    pub fn for_each_relevant_impl(&self, trait_: DefId, self_ty: Ty, mut f: impl FnMut(DefId)) {
        if let Some(table) = self.trait_impl_table(trait_) {
            if let Some(st) = simplify(self_ty) {
                if let Some(impls) = table.non_blanket.get(&st) {
                    for &imp in impls {
                        f(imp);
                    }
                }
                for &imp in &table.blanket {
                    f(imp);
                }
            } else {
                for &imp in &table.all {
                    f(imp);
                }
            }
        }
    }

    /// Does impl `a` specialize impl `b`: same trait, `a`'s header an instance of `b`'s, and
    /// `a`'s where-clauses implying `b`'s (`impl<I: FusedIterator> X for Fuse<I>` over
    /// `impl<I: Iterator> X for Fuse<I>`)?
    pub fn impl_specializes(&self, a: DefId, b: DefId) -> bool {
        if a == b {
            return false;
        }
        if let Some(&r) = self.q.specializes.lock().unwrap().get(&(a, b)) {
            return r;
        }
        // Provisionally no (a cycle through the solver ends there).
        self.q.specializes.lock().unwrap().insert((a, b), false);
        let r = (|| {
            let (ta, tb) = (self.impl_trait_ref(a)?, self.impl_trait_ref(b)?);
            if ta.def != tb.def {
                return Some(false);
            }
            let env = crate::traits::ParamEnv::for_item(self, a);
            let infcx = crate::infer::InferCtxt::new();
            let solver = crate::traits::Solver::new(self, &infcx, &env, &crate::traits::NoClosures);
            let b_args = solver.fresh_args(b);
            if infcx.unify_args(ta.args, tb.subst(b_args).args).is_err() {
                return Some(false);
            }
            Some(
                self.predicates_of(b)
                    .iter()
                    .all(|p| solver.evaluate(p.subst(b_args)) == crate::traits::Eval::Holds),
            )
        })()
        .unwrap_or(false);
        self.q.specializes.lock().unwrap().insert((a, b), r);
        r
    }

    /// Inherent impls whose self type simplifies to `st`.
    pub fn inherent_impls(&self, st: SimplifiedType) -> &[DefId] {
        let map = self.q.inherent_impls.get_or_init(|| {
            let mut m: FxHashMap<SimplifiedType, Vec<DefId>> = FxHashMap::default();
            for &imp in &self.hir.impls {
                if matches!(self.hir.def_kind(imp), DefKind::Impl { of_trait: false })
                    && let Some(st) = simplify(self.type_of(imp))
                {
                    m.entry(st).or_default().push(imp);
                }
            }
            m
        });
        map.get(&st).map_or(&[], |v| v)
    }

    pub fn is_trait(&self, def: DefId) -> bool {
        self.hir.def_kind(def) == DefKind::Trait
    }

    pub fn is_auto_trait(&self, def: DefId) -> bool {
        matches!(self.hir.get_item(def).map(|i| &i.kind), Some(hir::ItemKind::Trait(t)) if t.is_auto)
    }

    /// Is `def` (a `Fn`/`FnMut`/`FnOnce` lang item) one of the closure traits?
    pub fn fn_trait_kind(&self, def: DefId) -> Option<ClosureKind> {
        if Some(def) == self.lang_item("fn") {
            Some(ClosureKind::Fn)
        } else if Some(def) == self.lang_item("fn_mut") {
            Some(ClosureKind::FnMut)
        } else if Some(def) == self.lang_item("fn_once") {
            Some(ClosureKind::FnOnce)
        } else {
            None
        }
    }

    #[allow(dead_code)]
    fn blanket(&self) -> &FxHashMap<DefId, Vec<DefId>> {
        self.q.blanket_impls.get_or_init(FxHashMap::default)
    }
}

/// How a closure may be called.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

fn empty_adt(def: DefId) -> AdtDef {
    AdtDef {
        def,
        kind: AdtKind::Struct,
        variants: Vec::new(),
        repr: hir::Repr::default(),
        is_box: false,
        is_phantom_data: false,
        is_manually_drop: false,
        non_exhaustive: false,
    }
}

#[allow(non_snake_case)]
fn Diag_cycle(span: Span, msg: String) -> hyprc_span::Diag {
    hyprc_span::Diag::error(msg).code("E0391").span(span, "")
}
