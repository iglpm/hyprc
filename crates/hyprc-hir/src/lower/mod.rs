//! AST → HIR: items and their signatures, generics, types and paths.

mod body;
mod format;

use crate::hir::*;
use hyprc_resolve::cfg::{attr_item, attr_str_value};
use hyprc_resolve::{ItemNode, Ns, PathResult, Resolver};
use hyprc_span::{Diag, FxHashMap, Ident, Span, Symbol, kw};
use hyprc_syntax::ast;
use std::sync::atomic::{AtomicU32, Ordering};

/// Lowers every item of a resolved crate.
pub fn lower_crate(r: &Resolver<'_>) -> Crate {
    let n = r.defs.len();
    let next_body = AtomicU32::new(0);
    let lowered: Vec<(Option<Item>, Vec<(BodyId, Body)>)> = {
        use rayon::prelude::*;
        (0..n)
            .into_par_iter()
            .map(|i| {
                let def = DefId(i as u32);
                let mut cx = LowerCtx::new(r, def, &next_body);
                let item = cx.lower_def(def);
                (item, cx.bodies)
            })
            .collect()
    };
    let mut items = Vec::with_capacity(n);
    let mut bodies: Vec<Option<Body>> = (0..next_body.load(Ordering::Relaxed))
        .map(|_| None)
        .collect();
    for (item, bs) in lowered {
        items.push(item);
        for (id, b) in bs {
            bodies[id.index()] = Some(b);
        }
    }
    let traits_in_scope = traits_in_scope(r);
    let entry = r.modules[&r.root]
        .resolutions
        .get(&(hyprc_span::sym::main, Ns::Value))
        .and_then(|b| match b.res {
            Res::Def(DefKind::Fn, d) => Some(d),
            _ => None,
        });
    Crate {
        items,
        bodies: bodies
            .into_iter()
            .map(|b| b.expect("every body id is used"))
            .collect(),
        root: r.root,
        crate_name: r.crate_name,
        lang_items: r.lang_items.clone(),
        impls: r.impls.clone(),
        def_kinds: r.defs.iter().map(|d| d.kind).collect(),
        def_parents: r.defs.iter().map(|d| d.parent).collect(),
        def_names: r.defs.iter().map(|d| d.name).collect(),
        def_spans: r.defs.iter().map(|d| d.span).collect(),
        def_krates: r.defs.iter().map(|d| d.krate.0).collect(),
        traits_in_scope,
        no_core: r.no_core,
        no_std: r.no_std,
        no_main: r.no_main,
        entry,
        features: r.features.clone(),
    }
}

/// For each module and block: the traits whose methods can be called there.
fn traits_in_scope(r: &Resolver<'_>) -> FxHashMap<DefId, Vec<DefId>> {
    let prelude_traits: Vec<DefId> = r
        .prelude
        .and_then(|p| r.modules.get(&p))
        .map(|m| {
            m.resolutions
                .values()
                .filter_map(|b| match b.res {
                    Res::Def(DefKind::Trait, t) => Some(t),
                    _ => None,
                })
                .collect()
        })
        .unwrap_or_default();
    let mut out = FxHashMap::default();
    for (&id, m) in &r.modules {
        if !matches!(r.def_kind(id), DefKind::Mod | DefKind::Block) {
            continue;
        }
        let mut traits: Vec<DefId> = m
            .resolutions
            .iter()
            .filter(|((_, ns), _)| *ns == Ns::Type)
            .filter_map(|(_, b)| match b.res {
                Res::Def(DefKind::Trait, t) => Some(t),
                _ => None,
            })
            .collect();
        traits.extend(m.anon_traits.iter().copied());
        if !m.no_implicit_prelude {
            traits.extend(prelude_traits.iter().copied());
        }
        traits.sort();
        traits.dedup();
        out.insert(id, traits);
    }
    // A block sees the traits of the blocks and the module around it too.
    let blocks: Vec<DefId> = out
        .keys()
        .copied()
        .filter(|&id| r.def_kind(id) == DefKind::Block)
        .collect();
    for b in blocks {
        let mut extra = Vec::new();
        let mut cur = r.modules[&b].parent;
        while let Some(p) = cur {
            if let Some(t) = out.get(&p) {
                extra.extend(t.iter().copied());
            }
            if r.def_kind(p) != DefKind::Block {
                break;
            }
            cur = r.modules[&p].parent;
        }
        if !extra.is_empty() {
            let list = out.get_mut(&b).unwrap();
            list.extend(extra);
            list.sort();
            list.dedup();
        }
    }
    out
}

/// Generic parameters in scope, innermost last.
#[derive(Clone)]
pub(crate) struct GenericScope {
    pub owner: DefId,
    /// Type and const parameters by name: (name, absolute index, is_const).
    pub params: Vec<(Symbol, u32, bool)>,
    /// What `Self` means here, if anything.
    pub self_res: Option<Res>,
    /// `Self` as a constructor (in impls of tuple and unit structs).
    pub self_ctor: Option<DefId>,
}

pub(crate) struct LowerCtx<'a, 's> {
    pub r: &'a Resolver<'s>,
    pub owner: DefId,
    pub generics: Vec<GenericScope>,
    pub bodies: Vec<(BodyId, Body)>,
    next_body: &'a AtomicU32,
    /// `impl Trait` in return position: how many so far in this signature.
    opaque_count: u32,
    /// Collected synthetic parameters for `impl Trait` in argument position.
    synthetic: Option<Vec<(GenericParam, Vec<GenericBound>)>>,
    synthetic_base: u32,
    /// Bodies being lowered (an array length inside a function body nests).
    pub(crate) body_stack: Vec<body::BodyBuilder>,
}

pub(crate) fn err(span: Span, msg: impl Into<String>) -> Diag {
    Diag::error(msg).span(span, "")
}

impl<'a, 's> LowerCtx<'a, 's> {
    fn new(r: &'a Resolver<'s>, owner: DefId, next_body: &'a AtomicU32) -> Self {
        LowerCtx {
            r,
            owner,
            generics: Vec::new(),
            bodies: Vec::new(),
            next_body,
            opaque_count: 0,
            synthetic: None,
            synthetic_base: 0,
            body_stack: Vec::new(),
        }
    }

    pub(crate) fn emit(&self, d: Diag) {
        self.r.sess.dcx.emit(d);
    }

    pub(crate) fn new_body_id(&self) -> BodyId {
        BodyId(self.next_body.fetch_add(1, Ordering::Relaxed))
    }

    /// The module or block scope paths in this item resolve in.
    pub(crate) fn scope(&self) -> DefId {
        self.r.scope_of(self.owner)
    }

    // ---------------------------------------------------------------------------------------
    // Items

    fn lower_def(&mut self, def: DefId) -> Option<Item> {
        let data = self.r.def(def);
        let (attrs_src, kind) = match &self.r.nodes[def.0 as usize] {
            ItemNode::Item(item) => {
                self.push_parent_generics(def);
                let kind = self.lower_item_kind(def, item);
                (&item.attrs, kind)
            }
            ItemNode::Assoc(item) => {
                self.push_parent_generics(def);
                let kind = self.lower_assoc_item(def, item);
                (&item.attrs, kind)
            }
            ItemNode::Foreign(item) => {
                let kind = self.lower_foreign_item(def, item);
                (&item.attrs, kind)
            }
            ItemNode::None => return None,
        };
        let attrs = self.lower_attrs(attrs_src);
        Some(Item {
            def,
            name: data.name,
            span: data.span,
            vis: data.vis,
            attrs,
            kind,
        })
    }

    /// The generic scopes of an associated item's container (trait or impl).
    fn push_parent_generics(&mut self, def: DefId) {
        let Some(parent) = self.r.def(def).parent else {
            return;
        };
        match self.r.def_kind(parent) {
            DefKind::Trait | DefKind::Impl { .. } => {
                if let ItemNode::Item(item) = &self.r.nodes[parent.0 as usize] {
                    let scope = self.generic_scope_of(parent, item);
                    self.generics.push(scope);
                }
            }
            _ => {}
        }
    }

    /// The parameters an item declares, as a scope.
    fn generic_scope_of(&self, def: DefId, item: &ast::Item) -> GenericScope {
        let (generics, has_self, self_res, self_ctor) = match &item.kind {
            ast::ItemKind::Trait(t) => (
                Some(&t.generics),
                true,
                Some(Res::SelfTyParam { trait_: def }),
                None,
            ),
            ast::ItemKind::TraitAlias(g, _) => {
                (Some(g), true, Some(Res::SelfTyParam { trait_: def }), None)
            }
            ast::ItemKind::Impl(imp) => {
                // `Self(…)` names the impl (its self type has the impl's arguments), as in rustc.
                let ctor = self.impl_self_ctor(imp).map(|_| def);
                (
                    Some(&imp.generics),
                    false,
                    Some(Res::SelfTyAlias { alias_to: def }),
                    ctor,
                )
            }
            ast::ItemKind::Struct(_, g)
            | ast::ItemKind::Union(_, g)
            | ast::ItemKind::Enum(_, g) => (
                Some(g),
                false,
                Some(Res::SelfTyAlias { alias_to: def }),
                None,
            ),
            ast::ItemKind::Fn(f) => (Some(&f.generics), false, None, None),
            ast::ItemKind::TyAlias(t) => (Some(&t.generics), false, None, None),
            ast::ItemKind::Const(c) => (Some(&c.generics), false, None, None),
            _ => (None, false, None, None),
        };
        let mut params = Vec::new();
        let mut index = has_self as u32;
        if let Some(g) = generics {
            for p in &g.params {
                match &p.kind {
                    ast::GenericParamKind::Lifetime => {}
                    ast::GenericParamKind::Type { .. } => {
                        params.push((p.ident.name, index, false));
                        index += 1;
                    }
                    ast::GenericParamKind::Const { .. } => {
                        params.push((p.ident.name, index, true));
                        index += 1;
                    }
                }
            }
        }
        GenericScope {
            owner: def,
            params,
            self_res,
            self_ctor,
        }
    }

    /// In `impl S { … }` for a tuple or unit struct `S`, `Self(…)`/`Self` construct it.
    fn impl_self_ctor(&self, imp: &ast::Impl) -> Option<DefId> {
        let ast::TyKind::Path(None, path) = &imp.self_ty.kind else {
            return None;
        };
        let segs: Vec<Ident> = path.segments.iter().map(|s| s.ident).collect();
        match self
            .r
            .resolve_path(&segs, Ns::Type, self.r.scope_of(self.owner), false)
        {
            PathResult::NonModule {
                res: Res::Def(DefKind::Struct, d),
                unresolved: 0,
            } => {
                if let ItemNode::Item(item) = &self.r.nodes[d.0 as usize]
                    && let ast::ItemKind::Struct(data, _) = &item.kind
                    && !matches!(data, ast::VariantData::Struct { .. })
                {
                    return Some(d);
                }
                None
            }
            _ => None,
        }
    }

    fn parent_count(&self) -> u32 {
        self.generics.last().map_or(0, |g| {
            let has_self = matches!(g.self_res, Some(Res::SelfTyParam { .. }));
            g.params.len() as u32 + has_self as u32
        })
    }

    /// Lowers an item's own generics (its scope must already be pushed).
    fn lower_generics(
        &mut self,
        g: &ast::Generics,
        has_self: bool,
        parent: Option<DefId>,
        parent_count: u32,
    ) -> Generics {
        let mut out = Generics {
            parent,
            parent_count,
            has_self,
            span: g.span,
            ..Generics::default()
        };
        let mut index = parent_count + has_self as u32;
        for p in &g.params {
            let kind = match &p.kind {
                ast::GenericParamKind::Lifetime => continue,
                ast::GenericParamKind::Type { default } => GenericParamKind::Type {
                    default: default.as_ref().map(|t| self.lower_ty(t)),
                },
                ast::GenericParamKind::Const { ty, default } => GenericParamKind::Const {
                    ty: self.lower_ty(ty),
                    default: default.as_ref().map(|d| self.lower_anon_const(&d.value)),
                },
            };
            let bounds = self.lower_bounds(&p.bounds);
            if !bounds.is_empty() {
                let ty = Ty {
                    kind: TyKind::Path(self.param_path(p.ident, index)),
                    span: p.ident.span,
                };
                out.predicates.push(WherePredicate::Bound { ty, bounds });
            }
            out.params.push(GenericParam {
                name: p.ident.name,
                span: p.span,
                index,
                kind,
                synthetic: false,
            });
            index += 1;
        }
        for pred in &g.where_clause.predicates {
            match &pred.kind {
                ast::WherePredicateKind::Bound {
                    bounded_ty, bounds, ..
                } => {
                    let ty = self.lower_ty(bounded_ty);
                    let bounds = self.lower_bounds(bounds);
                    out.predicates.push(WherePredicate::Bound { ty, bounds });
                }
                ast::WherePredicateKind::Region { .. } => {}
                ast::WherePredicateKind::Eq { lhs_ty, rhs_ty } => {
                    let lhs = self.lower_ty(lhs_ty);
                    let rhs = self.lower_ty(rhs_ty);
                    out.predicates.push(WherePredicate::Eq { lhs, rhs });
                }
            }
        }
        out
    }

    fn param_path(&self, ident: Ident, index: u32) -> QPath {
        let res = Res::TyParam {
            owner: self.generics.last().map_or(self.owner, |g| g.owner),
            index,
        };
        QPath::Resolved(
            None,
            Path {
                res,
                segments: vec![PathSegment {
                    ident,
                    res,
                    args: None,
                }],
                span: ident.span,
            },
        )
    }

    fn lower_item_kind(&mut self, def: DefId, item: &ast::Item) -> ItemKind {
        use ast::ItemKind as K;
        match &item.kind {
            K::Fn(f) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                ItemKind::Fn(self.lower_fn(def, f, None, false))
            }
            K::Const(c) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(&c.generics, false, None, 0);
                let ty = self.lower_ty(&c.ty);
                let body = c
                    .expr
                    .as_ref()
                    .map(|e| self.lower_body_expr(e, BodyKind::Const));
                ItemKind::Const { ty, generics, body }
            }
            K::Static(s) => {
                let ty = self.lower_ty(&s.ty);
                let body = s
                    .expr
                    .as_ref()
                    .map(|e| self.lower_body_expr(e, BodyKind::Static));
                ItemKind::Static {
                    ty,
                    mutable: s.mutability == Mutability::Mut,
                    body,
                    foreign: false,
                }
            }
            K::Struct(data, g) | K::Union(data, g) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(g, false, None, 0);
                let data = self.lower_variant_data(data);
                if matches!(item.kind, K::Struct(..)) {
                    ItemKind::Struct { data, generics }
                } else {
                    ItemKind::Union { data, generics }
                }
            }
            K::Enum(e, g) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(g, false, None, 0);
                let variant_defs: Vec<DefId> = self
                    .r
                    .children(def)
                    .iter()
                    .copied()
                    .filter(|&c| self.r.def_kind(c) == DefKind::Variant)
                    .collect();
                let variants = e
                    .variants
                    .iter()
                    .zip(variant_defs)
                    .map(|(v, vdef)| Variant {
                        def: vdef,
                        name: v.ident.name,
                        span: v.span,
                        data: self.lower_variant_data(&v.data),
                        discr: v
                            .disr_expr
                            .as_ref()
                            .map(|d| self.lower_anon_const(&d.value)),
                    })
                    .collect();
                ItemKind::Enum { variants, generics }
            }
            K::TyAlias(t) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(&t.generics, false, None, 0);
                let ty = t.ty.as_ref().map(|ty| self.lower_ty(ty));
                let bounds = self.lower_bounds(&t.bounds);
                ItemKind::TyAlias {
                    ty,
                    generics,
                    bounds,
                }
            }
            K::Trait(t) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(&t.generics, true, None, 0);
                let supertraits = self.lower_bounds(&t.bounds);
                let items = self.r.children(def).to_vec();
                ItemKind::Trait(TraitItem {
                    generics,
                    supertraits,
                    items,
                    is_auto: t.is_auto,
                    is_unsafe: matches!(t.safety, ast::Safety::Unsafe(_)),
                    is_const: matches!(t.constness, ast::Constness::Yes(_)),
                })
            }
            K::TraitAlias(g, bounds) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(g, true, None, 0);
                let bounds = self.lower_bounds(bounds);
                ItemKind::TraitAlias { generics, bounds }
            }
            K::Impl(imp) => {
                let scope = self.generic_scope_of(def, item);
                self.generics.push(scope);
                let generics = self.lower_generics(&imp.generics, false, None, 0);
                let of_trait = imp.of_trait.as_ref().map(|t| TraitRef {
                    path: self.lower_trait_path(&t.path),
                    span: t.path.span,
                });
                let self_ty = self.lower_ty(&imp.self_ty);
                let items = self.r.children(def).to_vec();
                ItemKind::Impl(ImplItem {
                    generics,
                    of_trait,
                    self_ty,
                    items,
                    negative: matches!(imp.polarity, ast::ImplPolarity::Negative(_)),
                    is_unsafe: matches!(imp.safety, ast::Safety::Unsafe(_)),
                    is_const: matches!(imp.constness, ast::Constness::Yes(_)),
                    default: matches!(imp.defaultness, ast::Defaultness::Default(_)),
                })
            }
            K::Mod(..)
            | K::Use(_)
            | K::ExternCrate(_)
            | K::ForeignMod(_)
            | K::MacCall(_)
            | K::MacroDef(_)
            | K::GlobalAsm(_) => ItemKind::Other,
        }
    }

    fn lower_assoc_item(&mut self, def: DefId, item: &ast::AssocItem) -> ItemKind {
        let parent = self.r.def(def).parent;
        let parent_count = self.parent_count();
        match &item.kind {
            ast::AssocItemKind::Fn(f) => {
                let scope = self.fn_scope(def, &f.generics, parent_count);
                self.generics.push(scope);
                ItemKind::Fn(self.lower_fn(def, f, parent, false))
            }
            ast::AssocItemKind::Const(c) => {
                let scope = self.fn_scope(def, &c.generics, parent_count);
                self.generics.push(scope);
                let generics = self.lower_generics(&c.generics, false, parent, parent_count);
                let ty = self.lower_ty(&c.ty);
                let body = c
                    .expr
                    .as_ref()
                    .map(|e| self.lower_body_expr(e, BodyKind::Const));
                ItemKind::Const { ty, generics, body }
            }
            ast::AssocItemKind::Type(t) => {
                let scope = self.fn_scope(def, &t.generics, parent_count);
                self.generics.push(scope);
                let generics = self.lower_generics(&t.generics, false, parent, parent_count);
                let ty = t.ty.as_ref().map(|ty| self.lower_ty(ty));
                let bounds = self.lower_bounds(&t.bounds);
                ItemKind::TyAlias {
                    ty,
                    generics,
                    bounds,
                }
            }
            ast::AssocItemKind::MacCall(_) => ItemKind::Other,
        }
    }

    /// A scope for an item's own parameters, numbered after `parent_count`.
    fn fn_scope(&self, def: DefId, g: &ast::Generics, parent_count: u32) -> GenericScope {
        let mut params = Vec::new();
        let mut index = parent_count;
        for p in &g.params {
            match &p.kind {
                ast::GenericParamKind::Lifetime => {}
                ast::GenericParamKind::Type { .. } => {
                    params.push((p.ident.name, index, false));
                    index += 1;
                }
                ast::GenericParamKind::Const { .. } => {
                    params.push((p.ident.name, index, true));
                    index += 1;
                }
            }
        }
        // `Self` and the `Self` constructor carry over from the container.
        let (self_res, self_ctor) = self
            .generics
            .last()
            .map_or((None, None), |g| (g.self_res, g.self_ctor));
        GenericScope {
            owner: def,
            params,
            self_res,
            self_ctor,
        }
    }

    fn lower_foreign_item(&mut self, def: DefId, item: &ast::ForeignItem) -> ItemKind {
        match &item.kind {
            ast::ForeignItemKind::Fn(f) => {
                let scope = self.fn_scope(def, &f.generics, 0);
                self.generics.push(scope);
                let mut f = self.lower_fn(def, f, None, true);
                f.foreign = true;
                // Foreign fns take the block's ABI.
                if let Some(parent) = self.r.def(def).parent
                    && let ItemNode::Item(fm) = &self.r.nodes[parent.0 as usize]
                    && let ast::ItemKind::ForeignMod(m) = &fm.kind
                {
                    f.sig.abi = lower_abi(m.abi.map(|a| a.symbol));
                    // Items of `extern` blocks are unsafe to call unless marked `safe`.
                    f.sig.safety_unsafe = true;
                }
                if let ast::ForeignItemKind::Fn(af) = &item.kind
                    && matches!(af.sig.header.safety, ast::Safety::Safe(_))
                {
                    f.sig.safety_unsafe = false;
                }
                ItemKind::Fn(f)
            }
            ast::ForeignItemKind::Static(s) => {
                let ty = self.lower_ty(&s.ty);
                ItemKind::Static {
                    ty,
                    mutable: s.mutability == Mutability::Mut,
                    body: None,
                    foreign: true,
                }
            }
            ast::ForeignItemKind::TyAlias(_) => ItemKind::ForeignTy,
            ast::ForeignItemKind::MacCall(_) => ItemKind::Other,
        }
    }

    fn lower_fn(
        &mut self,
        def: DefId,
        f: &ast::Fn,
        container: Option<DefId>,
        foreign: bool,
    ) -> FnItem {
        let parent_count = if container.is_some() {
            self.generics.iter().rev().nth(1).map_or(0, |g| {
                let has_self = matches!(g.self_res, Some(Res::SelfTyParam { .. }));
                g.params.len() as u32 + has_self as u32
            })
        } else {
            0
        };
        let mut generics = self.lower_generics(&f.generics, false, container, parent_count);
        // `impl Trait` arguments become extra parameters after the declared ones.
        self.synthetic = Some(Vec::new());
        self.synthetic_base = generics.count();
        self.opaque_count = 0;
        let mut inputs = Vec::new();
        let mut names = Vec::new();
        for p in &f.sig.decl.inputs {
            if matches!(p.ty.kind, ast::TyKind::CVarArgs) {
                continue;
            }
            inputs.push(self.lower_ty(&p.ty));
            names.push(match &p.pat.kind {
                ast::PatKind::Ident(_, ident, _) => *ident,
                _ => Ident::new(kw::Underscore, p.pat.span),
            });
        }
        let synthetic = self.synthetic.take().unwrap_or_default();
        for (param, bounds) in synthetic {
            let ty = Ty {
                kind: TyKind::Path(
                    self.param_path(Ident::new(param.name, param.span), param.index),
                ),
                span: param.span,
            };
            generics
                .predicates
                .push(WherePredicate::Bound { ty, bounds });
            generics.params.push(param);
        }
        let output = match &f.sig.decl.output {
            ast::FnRetTy::Default(_) => None,
            ast::FnRetTy::Ty(t) => Some(self.lower_ret_ty(def, t)),
        };
        let header = &f.sig.header;
        let sig = FnSig {
            inputs,
            output,
            c_variadic: f.sig.decl.c_variadic(),
            safety_unsafe: matches!(header.safety, ast::Safety::Unsafe(_)),
            is_const: matches!(header.constness, ast::Constness::Yes(_)),
            is_async: matches!(
                header.coroutine_kind,
                Some(ast::CoroutineKind::Async { .. })
            ),
            abi: match header.ext {
                ast::Extern::None => Abi::Rust,
                ast::Extern::Implicit(_) => Abi::C,
                ast::Extern::Explicit(abi, _) => lower_abi(Some(abi.symbol)),
            },
            has_self: f.sig.decl.has_self(),
            param_names: names,
        };
        let body = if foreign {
            None
        } else {
            f.body.as_ref().map(|b| self.lower_fn_body(&f.sig.decl, b))
        };
        FnItem {
            sig,
            generics,
            body,
            container,
            foreign,
            defaultness_default: matches!(f.defaultness, ast::Defaultness::Default(_)),
        }
    }

    /// Return types: `impl Trait` there is an opaque type of this function.
    fn lower_ret_ty(&mut self, def: DefId, t: &ast::Ty) -> Ty {
        if let ast::TyKind::ImplTrait(_, bounds) = &t.kind {
            let index = self.opaque_count;
            self.opaque_count += 1;
            let bounds = self.lower_bounds(bounds);
            return Ty {
                kind: TyKind::Opaque {
                    owner: def,
                    index,
                    bounds,
                },
                span: t.span,
            };
        }
        self.lower_ty(t)
    }

    fn lower_variant_data(&mut self, data: &ast::VariantData) -> VariantData {
        let (kind, fields) = match data {
            ast::VariantData::Struct { fields } => (CtorShape::Struct, &fields[..]),
            ast::VariantData::Tuple(fields, _) => (CtorShape::Tuple, &fields[..]),
            ast::VariantData::Unit(_) => (CtorShape::Unit, &[][..]),
        };
        let module = self.r.parent_module(self.scope());
        let fields = fields
            .iter()
            .enumerate()
            .map(|(i, f)| FieldDef {
                name: f
                    .ident
                    .map_or_else(|| Symbol::intern(&i.to_string()), |i| i.name),
                span: f.span,
                vis: lower_vis(self.r, &f.vis, module),
                ty: self.lower_ty(&f.ty),
            })
            .collect();
        VariantData { kind, fields }
    }

    fn lower_attrs(&self, attrs: &[ast::Attribute]) -> ItemAttrs {
        let mut out = ItemAttrs::default();
        for a in attrs {
            let Some(item) = attr_item(a) else { continue };
            let name = match item.path.segments.as_slice() {
                [seg] => seg.ident.as_str(),
                _ => continue,
            };
            let list: Vec<String> = match &item.args {
                ast::AttrArgs::Delimited(args) => {
                    hyprc_resolve::cfg::split_commas(args.tokens.tokens())
                        .iter()
                        .map(|part| {
                            part.iter()
                                .map(hyprc_syntax::token::token_text)
                                .collect::<Vec<_>>()
                                .join("")
                        })
                        .collect()
                }
                _ => Vec::new(),
            };
            match name {
                "no_mangle" => out.no_mangle = true,
                "panic_handler" => {
                    out.no_mangle = true;
                    out.export_name = Some(Symbol::intern("panic_impl"));
                }
                "export_name" => out.export_name = attr_str_value(a),
                "link_name" => out.link_name = attr_str_value(a),
                "link_section" => out.link_section = attr_str_value(a),
                "lang" => out.lang = attr_str_value(a),
                "inline" => {
                    out.inline = Some(match list.first().map(String::as_str) {
                        Some("always") => InlineAttr::Always,
                        Some("never") => InlineAttr::Never,
                        _ => InlineAttr::Hint,
                    })
                }
                "cold" => out.cold = true,
                "track_caller" => out.track_caller = true,
                "used" => out.used = true,
                "naked" => out.naked = true,
                "thread_local" => out.thread_local = true,
                "rustc_intrinsic" => out.rustc_intrinsic = true,
                "rustc_legacy_const_generics" => {
                    let indices: Vec<usize> =
                        list.iter().filter_map(|s| s.trim().parse().ok()).collect();
                    if !indices.is_empty() {
                        out.legacy_const_generics = Some(indices);
                    }
                }
                "must_use" => out.must_use = true,
                "non_exhaustive" => out.non_exhaustive = true,
                "target_feature" => {
                    for l in &list {
                        if let Some(v) = l.strip_prefix("enable=") {
                            out.target_features
                                .extend(v.trim_matches('"').split(',').map(Symbol::intern));
                        }
                    }
                }
                "repr" => {
                    for l in &list {
                        let l = l.as_str();
                        match l {
                            "C" => out.repr.c = true,
                            "transparent" => out.repr.transparent = true,
                            "simd" => out.repr.simd = true,
                            "packed" => out.repr.packed = Some(1),
                            _ if l.starts_with("align(") => {
                                out.repr.align = l[6..l.len() - 1].parse().ok();
                            }
                            _ if l.starts_with("packed(") => {
                                out.repr.packed = l[7..l.len() - 1].parse().ok();
                            }
                            other => {
                                if let Some(p) = PrimTy::from_name(Symbol::intern(other)) {
                                    out.repr.int = Some(p);
                                }
                            }
                        }
                    }
                }
                "doc" => {
                    if list.iter().any(|l| l == "hidden") {
                        out.doc_hidden = true;
                    }
                }
                n if n.starts_with("rustc_") => out.rustc.push(Symbol::intern(n)),
                _ => {}
            }
        }
        out
    }

    // ---------------------------------------------------------------------------------------
    // Bounds

    fn lower_bounds(&mut self, bounds: &[ast::GenericBound]) -> Vec<GenericBound> {
        bounds
            .iter()
            .filter_map(|b| match b {
                ast::GenericBound::Trait(p) => Some(GenericBound::Trait {
                    trait_ref: TraitRef {
                        path: self.lower_trait_path(&p.trait_ref.path),
                        span: p.span,
                    },
                    maybe: matches!(p.modifiers.polarity, ast::BoundPolarity::Maybe(_)),
                    negative: matches!(p.modifiers.polarity, ast::BoundPolarity::Negative(_)),
                    is_const: !matches!(p.modifiers.constness, ast::BoundConstness::Never),
                }),
                ast::GenericBound::Outlives(_) => Some(GenericBound::Outlives),
                ast::GenericBound::Use(..) => None,
            })
            .collect()
    }

    /// A path naming a trait (in bounds, `impl Trait for`, `dyn Trait`).
    fn lower_trait_path(&mut self, path: &ast::Path) -> Path {
        match self.lower_qpath(None, path, Ns::Type, true) {
            QPath::Resolved(_, p) => p,
            QPath::TypeRelative(_, seg) => {
                self.emit(err(path.span, "expected trait, found associated type"));
                Path {
                    res: Res::Err,
                    segments: vec![seg],
                    span: path.span,
                }
            }
            QPath::LangItem(..) => unreachable!(),
        }
    }

    // ---------------------------------------------------------------------------------------
    // Types

    fn lower_ty_pat(&mut self, p: &ast::TyPat) -> TyPat {
        match &p.kind {
            ast::TyPatKind::Range(start, end, e) => TyPat::Range {
                start: start.as_ref().map(|c| self.lower_anon_const(&c.value)),
                end: end.as_ref().map(|c| self.lower_anon_const(&c.value)),
                inclusive: matches!(e, ast::RangeEnd::Included(_)),
            },
            ast::TyPatKind::NotNull => TyPat::NotNull,
            ast::TyPatKind::Or(alts) => {
                TyPat::Or(alts.iter().map(|a| self.lower_ty_pat(a)).collect())
            }
            ast::TyPatKind::Err => TyPat::Err,
        }
    }

    pub(crate) fn lower_ty(&mut self, t: &ast::Ty) -> Ty {
        use ast::TyKind as K;
        let kind = match &t.kind {
            K::Slice(e) => TyKind::Slice(Box::new(self.lower_ty(e))),
            K::Array(e, len) => {
                TyKind::Array(Box::new(self.lower_ty(e)), self.lower_const_arg(&len.value))
            }
            K::Ptr(m) => TyKind::Ptr(m.mutbl, Box::new(self.lower_ty(&m.ty))),
            K::Ref(_, m) | K::PinnedRef(_, m) => {
                TyKind::Ref(m.mutbl, Box::new(self.lower_ty(&m.ty)))
            }
            K::BareFn(f) => {
                let inputs = f
                    .decl
                    .inputs
                    .iter()
                    .filter(|p| !matches!(p.ty.kind, K::CVarArgs))
                    .map(|p| self.lower_ty(&p.ty))
                    .collect();
                let output = match &f.decl.output {
                    ast::FnRetTy::Default(_) => None,
                    ast::FnRetTy::Ty(t) => Some(self.lower_ty(t)),
                };
                TyKind::FnPtr(Box::new(FnPtrTy {
                    inputs,
                    output,
                    c_variadic: f.decl.c_variadic(),
                    safety_unsafe: matches!(f.safety, ast::Safety::Unsafe(_)),
                    abi: match f.ext {
                        ast::Extern::None => Abi::Rust,
                        ast::Extern::Implicit(_) => Abi::C,
                        ast::Extern::Explicit(a, _) => lower_abi(Some(a.symbol)),
                    },
                }))
            }
            K::UnsafeBinder(b) => return self.lower_ty(&b.inner_ty),
            K::Never => TyKind::Never,
            K::Tup(ts) => TyKind::Tup(ts.iter().map(|t| self.lower_ty(t)).collect()),
            K::Path(q, p) => {
                // A bare trait in type position (2015): a trait object.
                let qpath = self.lower_qpath(q.as_deref(), p, Ns::Type, false);
                if let QPath::Resolved(None, path) = &qpath
                    && matches!(path.res, Res::Def(DefKind::Trait | DefKind::TraitAlias, _))
                {
                    return Ty {
                        kind: TyKind::TraitObject(vec![GenericBound::Trait {
                            trait_ref: TraitRef {
                                path: path.clone(),
                                span: t.span,
                            },
                            maybe: false,
                            negative: false,
                            is_const: false,
                        }]),
                        span: t.span,
                    };
                }
                TyKind::Path(qpath)
            }
            K::TraitObject(bounds, _) => TyKind::TraitObject(self.lower_bounds(bounds)),
            K::ImplTrait(_, bounds) => {
                // Argument position: a synthetic type parameter.
                if self.synthetic.is_some() {
                    let bounds = self.lower_bounds(bounds);
                    let syn = self.synthetic.as_mut().unwrap();
                    let index = self.synthetic_base + syn.len() as u32;
                    let name = Symbol::intern(&format!("impl#{index}"));
                    syn.push((
                        GenericParam {
                            name,
                            span: t.span,
                            index,
                            kind: GenericParamKind::Type { default: None },
                            synthetic: true,
                        },
                        bounds,
                    ));
                    let owner = self.generics.last().map_or(self.owner, |g| g.owner);
                    let res = Res::TyParam { owner, index };
                    return Ty {
                        kind: TyKind::Path(QPath::Resolved(
                            None,
                            Path {
                                res,
                                segments: vec![PathSegment {
                                    ident: Ident::new(name, t.span),
                                    res,
                                    args: None,
                                }],
                                span: t.span,
                            },
                        )),
                        span: t.span,
                    };
                }
                let bounds = self.lower_bounds(bounds);
                let index = self.opaque_count;
                self.opaque_count += 1;
                TyKind::Opaque {
                    owner: self.owner,
                    index,
                    bounds,
                }
            }
            K::Paren(t) => return self.lower_ty(t),
            K::Infer => TyKind::Infer,
            K::ImplicitSelf => match self.self_res() {
                Some(res) => TyKind::Path(QPath::Resolved(
                    None,
                    Path {
                        res,
                        segments: vec![PathSegment {
                            ident: Ident::new(kw::SelfUpper, t.span),
                            res,
                            args: None,
                        }],
                        span: t.span,
                    },
                )),
                None => {
                    self.emit(err(
                        t.span,
                        "`self` parameter is only allowed in associated functions",
                    ));
                    TyKind::Err
                }
            },
            K::Typeof(_) => {
                self.emit(
                    err(t.span, "`typeof` is a reserved keyword but unimplemented").code("E0516"),
                );
                TyKind::Err
            }
            K::Pat(inner, pat) => {
                TyKind::Pat(Box::new(self.lower_ty(inner)), self.lower_ty_pat(pat))
            }
            K::MacCall(_) | K::Err | K::CVarArgs | K::AnonStruct(..) | K::AnonUnion(..) => {
                TyKind::Err
            }
        };
        Ty { kind, span: t.span }
    }

    pub(crate) fn self_res(&self) -> Option<Res> {
        self.generics.iter().rev().find_map(|g| g.self_res)
    }

    /// A const generic argument or array length: a const parameter, or a body.
    pub(crate) fn lower_const_arg(&mut self, e: &ast::Expr) -> ConstArg {
        let e = strip_block(e);
        if let ast::ExprKind::Path(None, p) = &e.kind
            && p.segments.len() == 1
            && p.segments[0].args.is_none()
            && let Some((owner, index)) = self.find_const_param(p.segments[0].ident.name)
        {
            return ConstArg::Param { owner, index };
        }
        if matches!(e.kind, ast::ExprKind::Underscore) {
            return ConstArg::Infer;
        }
        ConstArg::Body(self.lower_anon_const(e))
    }

    pub(crate) fn find_const_param(&self, name: Symbol) -> Option<(DefId, u32)> {
        for g in self.generics.iter().rev() {
            if let Some(&(_, index, true)) = g.params.iter().find(|(n, _, _)| *n == name) {
                return Some((g.owner, index));
            }
        }
        None
    }

    pub(crate) fn find_ty_param(&self, name: Symbol) -> Option<(DefId, u32, bool)> {
        for g in self.generics.iter().rev() {
            if let Some(&(_, index, is_const)) = g.params.iter().find(|(n, _, _)| *n == name) {
                return Some((g.owner, index, is_const));
            }
        }
        None
    }

    // ---------------------------------------------------------------------------------------
    // Paths

    pub(crate) fn lower_generic_args(&mut self, args: &ast::GenericArgs) -> GenericArgs {
        match args {
            ast::GenericArgs::AngleBracketed { args, span } => {
                let mut out = GenericArgs {
                    span: *span,
                    ..GenericArgs::default()
                };
                for a in args {
                    match a {
                        ast::AngleBracketedArg::Arg(ast::GenericArg::Lifetime(_)) => {}
                        ast::AngleBracketedArg::Arg(ast::GenericArg::Type(t)) => {
                            // `Foo<N>` where `N` is a const parameter: a const argument.
                            if let ast::TyKind::Path(None, p) = &t.kind
                                && p.segments.len() == 1
                                && p.segments[0].args.is_none()
                                && let Some((owner, index, true)) =
                                    self.find_ty_param(p.segments[0].ident.name)
                            {
                                out.args
                                    .push(GenericArg::Const(ConstArg::Param { owner, index }));
                                continue;
                            }
                            if let ast::TyKind::Path(None, p) = &t.kind
                                && self.path_is_value_const(p)
                            {
                                let e = ast::Expr {
                                    id: ast::NodeId::DUMMY,
                                    kind: ast::ExprKind::Path(None, p.clone()),
                                    span: t.span,
                                    attrs: Vec::new(),
                                };
                                out.args.push(GenericArg::Const(ConstArg::Body(
                                    self.lower_anon_const(&e),
                                )));
                                continue;
                            }
                            if matches!(t.kind, ast::TyKind::Infer) {
                                out.args.push(GenericArg::Infer);
                                continue;
                            }
                            out.args.push(GenericArg::Type(self.lower_ty(t)));
                        }
                        ast::AngleBracketedArg::Arg(ast::GenericArg::Const(c)) => {
                            out.args
                                .push(GenericArg::Const(self.lower_const_arg(&c.value)));
                        }
                        ast::AngleBracketedArg::Constraint(c) => {
                            let kind = match &c.kind {
                                ast::AssocItemConstraintKind::Equality(ast::Term::Ty(t)) => {
                                    AssocConstraintKind::Equality(self.lower_ty(t))
                                }
                                ast::AssocItemConstraintKind::Equality(ast::Term::Const(k)) => {
                                    AssocConstraintKind::EqualityConst(
                                        self.lower_const_arg(&k.value),
                                    )
                                }
                                ast::AssocItemConstraintKind::Bound(b) => {
                                    AssocConstraintKind::Bound(self.lower_bounds(b))
                                }
                            };
                            let args = c
                                .gen_args
                                .as_ref()
                                .map(|g| Box::new(self.lower_generic_args(g)));
                            out.constraints.push(AssocConstraint {
                                name: c.ident,
                                args,
                                kind,
                            });
                        }
                    }
                }
                out
            }
            ast::GenericArgs::Parenthesized {
                inputs,
                output,
                span,
            } => {
                let tys = inputs.iter().map(|t| self.lower_ty(t)).collect();
                let output = match output {
                    ast::FnRetTy::Default(s) => Ty {
                        kind: TyKind::Tup(Vec::new()),
                        span: *s,
                    },
                    ast::FnRetTy::Ty(t) => self.lower_ty(t),
                };
                GenericArgs {
                    args: vec![GenericArg::Type(Ty {
                        kind: TyKind::Tup(tys),
                        span: *span,
                    })],
                    constraints: vec![AssocConstraint {
                        name: Ident::new(hyprc_span::sym::Output, *span),
                        args: None,
                        kind: AssocConstraintKind::Equality(output),
                    }],
                    parenthesized: true,
                    span: *span,
                }
            }
            ast::GenericArgs::ParenthesizedElided(span) => GenericArgs {
                span: *span,
                ..GenericArgs::default()
            },
        }
    }

    /// Does a single-segment path name a constant (so `Foo<N>` passes a value)?
    fn path_is_value_const(&self, p: &ast::Path) -> bool {
        if p.segments.len() != 1 || p.segments[0].args.is_some() {
            return false;
        }
        let ident = p.segments[0].ident;
        if self.find_ty_param(ident.name).is_some() {
            return false;
        }
        let scope = self.current_scope();
        let ty = self.r.resolve_ident_lexical(ident, Ns::Type, scope);
        if matches!(ty, hyprc_resolve::Lookup::Found(_)) {
            return false;
        }
        matches!(
            self.r.resolve_ident_lexical(ident, Ns::Value, scope),
            hyprc_resolve::Lookup::Found(b) if matches!(b.res, Res::Def(DefKind::Const | DefKind::AssocConst, _))
        )
    }

    /// The scope names resolve in right now (blocks in bodies override the item's scope).
    pub(crate) fn current_scope(&self) -> DefId {
        self.body_scope().unwrap_or_else(|| self.scope())
    }

    fn lower_segment(&mut self, seg: &ast::PathSegment, res: Res) -> PathSegment {
        PathSegment {
            ident: seg.ident,
            res,
            args: seg
                .args
                .as_ref()
                .map(|a| Box::new(self.lower_generic_args(a))),
        }
    }

    /// Resolves and lowers a path in a namespace. `trait_only`: report non-traits.
    pub(crate) fn lower_qpath(
        &mut self,
        qself: Option<&ast::QSelf>,
        path: &ast::Path,
        ns: Ns,
        trait_only: bool,
    ) -> QPath {
        self.lower_qpath_in(qself, path, ns, trait_only, self.current_scope(), &|_| None)
    }

    /// Like `lower_qpath`, with a scope and a local-variable lookup for bodies.
    pub(crate) fn lower_qpath_in(
        &mut self,
        qself: Option<&ast::QSelf>,
        path: &ast::Path,
        ns: Ns,
        _trait_only: bool,
        scope: DefId,
        local: &dyn Fn(Ident) -> Option<Res>,
    ) -> QPath {
        let segs = &path.segments;
        if let Some(q) = qself {
            let qty = self.lower_ty(&q.ty);
            if q.position == 0 {
                // `<T>::a::b`
                let mut base = Ty {
                    kind: qty.kind,
                    span: qty.span,
                };
                for (i, seg) in segs.iter().enumerate() {
                    let seg = self.lower_segment(seg, Res::Err);
                    if i + 1 == segs.len() {
                        return QPath::TypeRelative(Box::new(base), seg);
                    }
                    base = Ty {
                        kind: TyKind::Path(QPath::TypeRelative(Box::new(base), seg)),
                        span: path.span,
                    };
                }
                return QPath::TypeRelative(
                    Box::new(base),
                    PathSegment {
                        ident: Ident::new(kw::Empty, path.span),
                        res: Res::Err,
                        args: None,
                    },
                );
            }
            // `<T as Trait>::Item…`: the trait's path, then the item in the trait.
            let trait_segs: Vec<Ident> = segs[..q.position].iter().map(|s| s.ident).collect();
            let trait_res = match self.r.resolve_path(&trait_segs, Ns::Type, scope, false) {
                PathResult::NonModule { res, unresolved: 0 } => res,
                _ => {
                    self.emit(
                        err(
                            path.span,
                            "failed to resolve the trait in this qualified path",
                        )
                        .code("E0433"),
                    );
                    Res::Err
                }
            };
            let mut lowered: Vec<PathSegment> = Vec::new();
            for s in &segs[..q.position] {
                let s = self.lower_segment(s, Res::Err);
                lowered.push(s);
            }
            if let Some(last) = lowered.last_mut() {
                last.res = trait_res;
            }
            let item_seg = &segs[q.position];
            let item_res = match trait_res {
                Res::Def(DefKind::Trait, t) => {
                    let item_ns = if q.position + 1 == segs.len() {
                        ns
                    } else {
                        Ns::Type
                    };
                    match self.r.ident_ns_lookup(t, item_seg.ident, item_ns) {
                        Some(b) => b.res,
                        None => {
                            self.emit(
                                err(
                                    item_seg.ident.span,
                                    format!(
                                        "cannot find associated item `{}` in trait",
                                        item_seg.ident
                                    ),
                                )
                                .code("E0576"),
                            );
                            Res::Err
                        }
                    }
                }
                _ => Res::Err,
            };
            lowered.push(self.lower_segment(item_seg, item_res));
            let resolved = QPath::Resolved(
                Some(Box::new(qty)),
                Path {
                    res: item_res,
                    segments: lowered,
                    span: path.span,
                },
            );
            let mut base = resolved;
            for s in &segs[q.position + 1..] {
                let seg = self.lower_segment(s, Res::Err);
                base = QPath::TypeRelative(
                    Box::new(Ty {
                        kind: TyKind::Path(base),
                        span: path.span,
                    }),
                    seg,
                );
            }
            return base;
        }

        // Generic parameters, `Self`, locals: single names and path prefixes.
        let first = segs.first().map(|s| s.ident);
        let mut base_res: Option<(Res, usize)> = None;
        if let Some(first) = first {
            if segs.len() == 1
                && ns == Ns::Value
                && let Some(res) = local(first)
            {
                base_res = Some((res, 1));
            } else if first.name == kw::SelfUpper
                && !matches!(segs.first().map(|s| s.ident.span.ctxt), None)
            {
                let res = if ns == Ns::Value && segs.len() == 1 {
                    self.generics
                        .iter()
                        .rev()
                        .find_map(|g| g.self_ctor)
                        .map(Res::SelfCtor)
                        .or_else(|| self.self_res())
                } else {
                    self.self_res()
                };
                match res {
                    Some(res) => base_res = Some((res, 1)),
                    None => {
                        self.emit(
                            err(first.span, "cannot find type `Self` in this scope").code("E0411"),
                        );
                        base_res = Some((Res::Err, 1));
                    }
                }
            } else if let Some((owner, index, is_const)) = self.find_ty_param(first.name) {
                if is_const {
                    if ns == Ns::Value {
                        base_res = Some((Res::ConstParam { owner, index }, 1));
                    }
                } else if ns == Ns::Type || segs.len() > 1 {
                    base_res = Some((Res::TyParam { owner, index }, 1));
                }
            }
        }
        let (res, resolved_len) = match base_res {
            Some(x) => x,
            None => {
                let idents: Vec<Ident> = segs.iter().map(|s| s.ident).collect();
                match self.r.resolve_path(&idents, ns, scope, false) {
                    PathResult::NonModule { res, unresolved } => (res, segs.len() - unresolved),
                    // `u8::MAX` with a module `u8` in scope, or `char::from_u32`: the
                    // primitive type, the rest associated items (rustc's fallback).
                    PathResult::Module(_) | PathResult::Failed { .. }
                        if (ns == Ns::Type || segs.len() > 1)
                            && let Some(p) =
                                hyprc_resolve::PrimTy::from_name(segs[0].ident.name) =>
                    {
                        (Res::PrimTy(p), 1)
                    }
                    PathResult::Module(m) => {
                        if ns != Ns::Type {
                            self.emit(
                                err(
                                    path.span,
                                    format!(
                                        "expected {}, found module `{}`",
                                        ns_descr(ns),
                                        path_str(path)
                                    ),
                                )
                                .code("E0423"),
                            );
                            (Res::Err, segs.len())
                        } else {
                            (Res::Def(DefKind::Mod, m), segs.len())
                        }
                    }
                    PathResult::Indeterminate | PathResult::Failed { .. } => {
                        let (code, what) = match ns {
                            Ns::Type => ("E0412", "type"),
                            Ns::Value => ("E0425", "value"),
                            Ns::Macro => ("E0433", "macro"),
                        };
                        let msg = if segs.len() == 1 {
                            format!("cannot find {what} `{}` in this scope", path_str(path))
                        } else {
                            format!("failed to resolve: cannot find `{}`", path_str(path))
                        };
                        self.emit(err(path.span, msg).code(if segs.len() == 1 {
                            code
                        } else {
                            "E0433"
                        }));
                        (Res::Err, segs.len())
                    }
                }
            }
        };
        let mut lowered: Vec<PathSegment> = Vec::with_capacity(resolved_len);
        for (i, s) in segs[..resolved_len].iter().enumerate() {
            let r = if i + 1 == resolved_len { res } else { Res::Err };
            lowered.push(self.lower_segment(s, r));
        }
        let mut q = QPath::Resolved(
            None,
            Path {
                res,
                segments: lowered,
                span: path.span,
            },
        );
        for s in &segs[resolved_len..] {
            let seg = self.lower_segment(s, Res::Err);
            q = QPath::TypeRelative(
                Box::new(Ty {
                    kind: TyKind::Path(q),
                    span: path.span,
                }),
                seg,
            );
        }
        q
    }

    // ---------------------------------------------------------------------------------------
    // Bodies

    pub(crate) fn lower_anon_const(&mut self, e: &ast::Expr) -> BodyId {
        self.lower_body_expr(e, BodyKind::AnonConst)
    }
}

pub(crate) fn strip_block(e: &ast::Expr) -> &ast::Expr {
    // `{ N }` as a const argument is `N`.
    if let ast::ExprKind::Block(b, None) = &e.kind
        && b.stmts.len() == 1
        && let ast::StmtKind::Expr(inner) = &b.stmts[0].kind
    {
        return strip_block(inner);
    }
    if let ast::ExprKind::Paren(inner) = &e.kind {
        return strip_block(inner);
    }
    e
}

fn ns_descr(ns: Ns) -> &'static str {
    match ns {
        Ns::Type => "type",
        Ns::Value => "value",
        Ns::Macro => "macro",
    }
}

pub(crate) fn path_str(p: &ast::Path) -> String {
    p.segments
        .iter()
        .map(|s| s.ident.as_str())
        .collect::<Vec<_>>()
        .join("::")
        .replace("{{root}}", "")
}

fn lower_abi(abi: Option<Symbol>) -> Abi {
    match abi.map(|a| a.as_str()) {
        None | Some("C") | Some("C-unwind") | Some("cdecl") | Some("sysv64") => Abi::C,
        Some("Rust") => Abi::Rust,
        Some(other) => Abi::Other(Symbol::intern(other)),
    }
}

pub(crate) fn lower_vis(r: &Resolver<'_>, vis: &ast::Visibility, module: DefId) -> Vis {
    match &vis.kind {
        ast::VisibilityKind::Public => Vis::Public,
        ast::VisibilityKind::Inherited => Vis::Restricted(module),
        ast::VisibilityKind::Restricted { path, .. } => {
            match path.segments.first().map(|s| s.ident.name) {
                Some(kw::Crate) => Vis::Restricted(r.crate_root_of(module)),
                Some(kw::Super) => Vis::Restricted(
                    r.module(module)
                        .parent
                        .map_or(module, |p| r.parent_module(p)),
                ),
                _ => Vis::Restricted(module),
            }
        }
    }
}
