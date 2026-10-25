//! Phase 1, collection: items into definitions and module scopes.

use crate::cfg;
use crate::imports::{Import, ImportKind};
use crate::loader::{Loader, ModDir};
use crate::{
    Binding, BindingKind, CtorKind, CtorOf, DefId, DefKind, FragmentKind, InvocKind, Invocation,
    ItemNode, MacroKind, ModuleData, Ns, Res, Resolver, ScopeId, TextualScope, Vis,
};
use hyprc_span::hygiene::ExpnId;
use hyprc_span::session::Session;
use hyprc_span::{Diag, FxHashSet, Ident, Span, Symbol, kw, sym};
use hyprc_syntax::ast::{
    self, AssocItemKind, ForeignItemKind, ItemKind, ModKind, P, UseTreeKind, VariantData,
};
use std::path::{Path, PathBuf};

pub(crate) fn new_resolver<'s>(
    sess: &'s Session,
    crate_name: Symbol,
    root_file: &Path,
) -> Resolver<'s> {
    let edition = sess.edition();
    let mut r = Resolver {
        sess,
        edition,
        crate_name,
        root: DefId(0),
        defs: Vec::new(),
        nodes: Vec::new(),
        modules: Default::default(),
        children: Default::default(),
        impls: Vec::new(),
        crate_attrs: Vec::new(),
        features: Default::default(),
        lang_items: Default::default(),
        extern_prelude: Default::default(),
        macro_use_prelude: Default::default(),
        prelude: None,
        has_prelude_import: false,
        no_std: false,
        no_core: false,
        no_main: false,
        imports: Vec::new(),
        invocations: Vec::new(),
        scopes: vec![TextualScope::Empty],
        macros: Default::default(),
        item_scopes: Default::default(),
        item_expns: Default::default(),
        loader: Loader::default(),
        expn_crates: Default::default(),
        crate_roots: Vec::new(),
        current_krate: crate::CrateNum::LOCAL,
        crate_cfgs: Default::default(),
        crate_has_explicit_features: Default::default(),
        crate_editions: Default::default(),
        crate_preludes: Default::default(),
        crate_has_prelude_import: Default::default(),
        current_import: std::sync::atomic::AtomicUsize::new(usize::MAX),
    };
    r.crate_editions.insert(crate::CrateNum::LOCAL, edition);
    let root = r.new_def(DefKind::Mod, None, crate_name, Span::DUMMY, Vis::Public);
    r.root = root;
    r.crate_roots.push(root);

    for builtin in [
        "format",
        "print",
        "println",
        "eprint",
        "eprintln",
        "write",
        "writeln",
        "vec",
        "matches",
        "todo",
        "unimplemented",
        "panic",
        "panic_2015",
        "panic_2021",
        "assert",
        "debug_assert",
        "debug_assert_eq",
        "debug_assert_ne",
        "cfg",
        "env",
        "option_env",
        "concat",
        "stringify",
        "include",
        "include_str",
        "include_bytes",
        "format_args",
        "format_args_nl",
        "const_format_args",
    ] {
        let sym = Symbol::intern(builtin);
        let def = r.new_def(
            DefKind::Macro(MacroKind::Bang),
            None,
            sym,
            Span::DUMMY,
            Vis::Public,
        );
        r.macro_use_prelude.insert(sym, def);
        r.macros.insert(
            def,
            crate::MacroData {
                def,
                kind: crate::macros::MacroImpl::Builtin(
                    crate::macros::builtin::BuiltinMacro::from_name(builtin),
                ),
                krate: crate::CrateNum::LOCAL,
                edition,
                macro_2_0: false,
            },
        );
    }
    let dir = ModDir::owned_by_file(root_file);
    let Some(parsed) = r.loader.take(root_file, edition) else {
        sess.dcx.emit(Diag::error(format!(
            "couldn't read `{}`",
            root_file.display()
        )));
        r.modules.insert(root, new_module(root, None, root, dir));
        return r;
    };
    for d in parsed.diags {
        sess.dcx.emit(d);
    }
    let ast::Crate {
        mut attrs,
        items,
        span,
    } = parsed.krate;
    r.defs[root.0 as usize].span = span;
    cfg::expand_cfg_attrs(sess, edition, &mut attrs);
    r.read_crate_attrs(&attrs);
    let no_implicit_prelude = cfg::has_attr(&attrs, "no_implicit_prelude");
    r.crate_attrs = attrs;
    let mut module = new_module(root, None, root, dir.clone());
    module.no_implicit_prelude = no_implicit_prelude;
    r.modules.insert(root, module);

    r.load_extern_crates();

    if !no_implicit_prelude {
        let prelude_crate = if !r.no_std
            && r.crate_name != Symbol::intern("std")
            && r.extern_prelude.contains_key(&Symbol::intern("std"))
        {
            Some(Symbol::intern("std"))
        } else if !r.no_core
            && r.crate_name != sym::core
            && r.extern_prelude.contains_key(&sym::core)
        {
            Some(sym::core)
        } else {
            None
        };
        if let Some(krate_sym) = prelude_crate {
            let edition_sym = match edition {
                hyprc_span::Edition::E2024 => Symbol::intern("rust_2024"),
                hyprc_span::Edition::E2021 => Symbol::intern("rust_2021"),
                hyprc_span::Edition::E2018 => Symbol::intern("rust_2018"),
                hyprc_span::Edition::E2015 => Symbol::intern("rust_2015"),
            };
            r.imports.push(Import {
                module: root,
                scope: ScopeId::EMPTY,
                vis: Vis::Restricted(root),
                span: Span::DUMMY,
                path: vec![
                    Ident::new(krate_sym, Span::DUMMY),
                    Ident::new(Symbol::intern("prelude"), Span::DUMMY),
                    Ident::new(edition_sym, Span::DUMMY),
                ],
                kind: ImportKind::Glob {
                    is_prelude: true,
                    target: None,
                },
                expn: ExpnId::ROOT,
                resolved: false,
                failed: false,
            });
        }
    }

    let cfg_ctx = r.active_cfg_context();
    r.loader.prefetch(&cfg_ctx, edition, &items, &dir);
    r.collect_items(root, items, ScopeId::EMPTY, ExpnId::ROOT);
    r
}

pub(crate) fn new_module(
    def: DefId,
    parent: Option<DefId>,
    normal_module: DefId,
    dir: ModDir,
) -> ModuleData {
    ModuleData {
        def,
        parent,
        normal_module,
        resolutions: Default::default(),
        globs: Vec::new(),
        glob_importers: Vec::new(),
        anon_traits: Vec::new(),
        no_implicit_prelude: false,
        pending_macros: 0,
        single_imports: Default::default(),
        dir,
    }
}

/// The value of `#[lang = "…"]`.
fn lang_attr(attrs: &[ast::Attribute]) -> Option<Symbol> {
    attrs
        .iter()
        .find(|a| a.has_name(sym::lang))
        .and_then(cfg::attr_str_value)
}

impl<'s> Resolver<'s> {
    fn read_crate_attrs(&mut self, attrs: &[ast::Attribute]) {
        for attr in attrs {
            let Some(name) = attr.name() else { continue };
            match name.as_str() {
                "no_std" => self.no_std = true,
                "no_core" => self.no_core = true,
                "no_main" => self.no_main = true,
                "feature" => {
                    if let Some(item) = cfg::attr_item(attr)
                        && let ast::AttrArgs::Delimited(args) = &item.args
                    {
                        for part in cfg::split_commas(args.tokens.tokens()) {
                            if let Some(t) = part.first() {
                                self.features.insert(t.sym);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub(crate) fn new_scope(&mut self, s: TextualScope) -> ScopeId {
        self.scopes.push(s);
        ScopeId(self.scopes.len() as u32 - 1)
    }

    /// The visibility an item written with `vis` in `module` has.
    pub(crate) fn resolve_vis(&mut self, vis: &ast::Visibility, module: DefId) -> Vis {
        let normal = self.parent_module(module);
        match &vis.kind {
            ast::VisibilityKind::Public => Vis::Public,
            ast::VisibilityKind::Inherited => Vis::Restricted(normal),
            ast::VisibilityKind::Restricted {
                path, shorthand, ..
            } => {
                let first = path.segments.first().map(|s| s.ident.name);
                if *shorthand || path.segments.len() == 1 {
                    match first {
                        Some(kw::Crate) => return Vis::Restricted(self.crate_root_of(module)),
                        Some(kw::SelfLower) => return Vis::Restricted(normal),
                        Some(kw::Super) => {
                            let parent = self.modules[&normal]
                                .parent
                                .map(|p| self.parent_module(p))
                                .unwrap_or(normal);
                            return Vis::Restricted(parent);
                        }
                        _ => {}
                    }
                }
                // `pub(in path)`: the path must name an ancestor module; resolved from the
                // crate root (2018) or relative to it (2015) like any absolute path.
                let segs: Vec<Ident> = path.segments.iter().map(|s| s.ident).collect();
                match self.resolve_module_path_now(&segs, normal) {
                    Some(m) => Vis::Restricted(m),
                    None => {
                        self.sess.dcx.emit(
                            Diag::error("visibilities can only be restricted to ancestor modules")
                                .code("E0742")
                                .span(vis.span, ""),
                        );
                        Vis::Restricted(normal)
                    }
                }
            }
        }
    }

    /// Binds a name in a scope, applying shadowing rules: definitions and single imports
    /// beat glob imports; two different globs make the name ambiguous.
    pub(crate) fn define(&mut self, module: DefId, ident: Ident, ns: Ns, binding: Binding) {
        if ident.name == kw::Underscore || ident.name == kw::Empty {
            return;
        }
        let key = (ident.name, ns);
        let m = self
            .modules
            .get_mut(&module)
            .expect("binding in a scope that isn't one");
        let changed = match m.resolutions.get(&key).copied() {
            None => {
                m.resolutions.insert(key, binding);
                true
            }
            Some(old) => {
                let old_glob = matches!(old.kind, BindingKind::Glob(_) | BindingKind::Ambiguous(_));
                let new_glob = matches!(binding.kind, BindingKind::Glob(_));
                if old.res == binding.res {
                    // Re-imported, or the same thing twice: keep the stronger binding.
                    if old_glob && !new_glob {
                        m.resolutions.insert(key, binding);
                        true
                    } else if old.kind != binding.kind
                        && matches!(old.kind, BindingKind::Ambiguous(_))
                    {
                        false
                    } else {
                        false
                    }
                } else if old_glob && !new_glob {
                    m.resolutions.insert(key, binding);
                    true
                } else if !old_glob && new_glob {
                    false
                } else if old_glob && new_glob {
                    if let BindingKind::Ambiguous(_) = old.kind {
                        false
                    } else {
                        m.resolutions.insert(
                            key,
                            Binding {
                                kind: BindingKind::Ambiguous(binding.res),
                                ..old
                            },
                        );
                        true
                    }
                } else {
                    // Two definitions (or imports) with one name in one namespace.
                    let what = binding.res.descr();
                    self.sess.dcx.emit(
                        Diag::error(format!(
                            "the name `{}` is defined multiple times",
                            ident.name
                        ))
                        .code("E0428")
                        .span(binding.span, format!("`{}` redefined here", ident.name))
                        .label(
                            old.span,
                            format!("previous definition of the {what} `{}` here", ident.name),
                        ),
                    );
                    false
                }
            }
        };
        if changed {
            self.propagate_to_glob_importers(module, ident, ns);
        }
    }

    pub(crate) fn define_def(&mut self, module: DefId, ident: Ident, ns: Ns, res: Res, vis: Vis) {
        self.define(
            module,
            ident,
            ns,
            Binding {
                res,
                vis,
                span: ident.span,
                kind: BindingKind::Def,
            },
        );
    }

    /// Takes an item's `cfg`s into account and reports whether it stays.
    fn keep(&mut self, attrs: &mut Vec<ast::Attribute>) -> bool {
        let cfg_ctx = self.active_cfg_context();
        if !cfg::process_attrs_ctx(&cfg_ctx, &self.sess.dcx, self.edition, attrs) {
            return false;
        }
        self.expand_attr_values(attrs);
        // `#[test]` and `#[bench]` items exist only in test builds.
        if !self.sess.opts.test
            && attrs
                .iter()
                .any(|a| a.has_name(sym::test) || a.has_name(sym::bench))
        {
            return false;
        }
        true
    }

    /// `#[lang = stringify!(x)]`, `#[doc = include_str!("x")]`: macro calls in attribute
    /// values expand to literals before anything reads them.
    pub(crate) fn expand_attr_values(&mut self, attrs: &mut [ast::Attribute]) {
        for a in attrs.iter_mut() {
            let is_doc = a.has_name(sym::doc);
            let ast::AttrKind::Normal(item) = &mut a.kind else {
                continue;
            };
            let ast::AttrArgs::Eq(_, expr) = &mut item.args else {
                continue;
            };
            let ast::ExprKind::MacCall(mac) = &expr.kind else {
                continue;
            };
            // Documentation doesn't change what's compiled: `#[doc = concat!(…)]` isn't
            // expanded (std has hundreds, many through further macros).
            if is_doc {
                expr.kind = ast::ExprKind::Lit(ast::Lit {
                    kind: hyprc_syntax::token::LitKind::Str,
                    symbol: kw::Empty,
                    suffix: kw::Empty,
                    span: expr.span,
                });
                continue;
            }
            match self.eager_attr_literal(mac.clone()) {
                Ok(lit) => expr.kind = ast::ExprKind::Lit(lit),
                Err(d) => self.sess.dcx.emit(d),
            }
        }
    }

    pub(crate) fn push_invocation(
        &mut self,
        kind: InvocKind,
        module: DefId,
        scope: ScopeId,
        fragment: FragmentKind,
        span: Span,
        expn: ExpnId,
        attrs: Vec<ast::Attribute>,
    ) -> ScopeId {
        let idx = self.invocations.len();
        self.invocations.push(Invocation {
            kind,
            module,
            scope,
            fragment,
            span,
            parent_expn: expn,
            attrs,
            output_scope: None,
            done: false,
            failed: false,
        });
        if let Some(m) = self.modules.get_mut(&module) {
            m.pending_macros += 1;
        }
        self.new_scope(TextualScope::Invocation {
            invoc: idx,
            parent: scope,
        })
    }

    /// Collects items into `module` in order; returns the textual macro scope after them.
    pub(crate) fn collect_items(
        &mut self,
        module: DefId,
        items: Vec<P<ast::Item>>,
        mut scope: ScopeId,
        expn: ExpnId,
    ) -> ScopeId {
        for mut item in items {
            if !self.keep(&mut item.attrs) {
                continue;
            }
            scope = self.collect_item(module, item, scope, expn);
        }
        scope
    }

    fn collect_item(
        &mut self,
        module: DefId,
        mut item: P<ast::Item>,
        scope: ScopeId,
        expn: ExpnId,
    ) -> ScopeId {
        let vis = self.resolve_vis(&item.vis, module);
        let ident = item.ident;
        let span = item.span;
        match &mut item.kind {
            ItemKind::MacCall(_) => {
                let ItemKind::MacCall(mac) =
                    std::mem::replace(&mut item.kind, ItemKind::Use(empty_use_tree(span)))
                else {
                    unreachable!()
                };
                let attrs = std::mem::take(&mut item.attrs);
                return self.push_invocation(
                    InvocKind::Bang(mac),
                    module,
                    scope,
                    FragmentKind::Items,
                    span,
                    expn,
                    attrs,
                );
            }
            ItemKind::MacroDef(def) => {
                let macro_rules = def.macro_rules;
                let id = self.new_def(
                    DefKind::Macro(MacroKind::Bang),
                    Some(module),
                    ident.name,
                    span,
                    vis,
                );
                self.item_scopes.insert(id, scope);
                self.item_expns.insert(id, expn);
                let exported = cfg::has_attr(&item.attrs, "macro_export");
                self.nodes[id.0 as usize] = ItemNode::Item(item);
                if macro_rules {
                    if self.edition_of(module).at_least_2018() {
                        self.define_def(
                            module,
                            ident,
                            Ns::Macro,
                            Res::Def(DefKind::Macro(MacroKind::Bang), id),
                            vis,
                        );
                    }
                    if exported {
                        let root = self.crate_root_of(module);
                        self.define_def(
                            root,
                            ident,
                            Ns::Macro,
                            Res::Def(DefKind::Macro(MacroKind::Bang), id),
                            Vis::Public,
                        );
                    }
                    return self.new_scope(TextualScope::Def {
                        name: ident.name,
                        mac: id,
                        parent: scope,
                    });
                }
                self.define_def(
                    module,
                    ident,
                    Ns::Macro,
                    Res::Def(DefKind::Macro(MacroKind::Bang), id),
                    vis,
                );
                return scope;
            }
            ItemKind::Use(_) => {
                let ItemKind::Use(tree) = &item.kind else {
                    unreachable!()
                };
                let is_prelude = cfg::has_attr(&item.attrs, "prelude_import");
                if is_prelude {
                    self.has_prelude_import = true;
                    self.crate_has_prelude_import.insert(self.current_krate);
                }
                self.collect_use_tree(module, tree, &[], vis, is_prelude, expn, scope);
                return scope;
            }
            ItemKind::ExternCrate(orig) => {
                let orig_name = orig.unwrap_or(ident.name);
                let target = if orig_name == kw::SelfLower {
                    Some(self.crate_root_of(module))
                } else if let Some(&root) = self.extern_prelude.get(&orig_name) {
                    Some(root)
                } else {
                    self.try_load_named_crate(orig_name)
                };
                match target {
                    Some(root) => {
                        self.define_def(module, ident, Ns::Type, Res::Def(DefKind::Mod, root), vis);
                        if module == self.crate_root_of(module) {
                            self.extern_prelude.insert(ident.name, root);
                        }
                        if cfg::has_attr(&item.attrs, "macro_use") {
                            self.add_macro_use(root);
                        }
                    }
                    None => self.sess.dcx.emit(
                        Diag::error(format!("can't find crate for `{orig_name}`"))
                            .code("E0463")
                            .span(span, "can't find crate"),
                    ),
                }
                return scope;
            }
            ItemKind::Mod(..) => return self.collect_mod(module, item, vis, scope, expn),
            _ => {}
        }
        let id = self.define_item(module, &mut item, vis, scope, expn);
        // Derives queue their expansions after the item they apply to.
        let mut scope = scope;
        let derives = derive_paths(&item.attrs);
        self.nodes[id.0 as usize] = ItemNode::Item(item);
        for (path, is_const) in derives {
            let span = path.span;
            scope = self.push_invocation(
                InvocKind::Derive {
                    path,
                    item: id,
                    is_const,
                },
                module,
                scope,
                FragmentKind::Items,
                span,
                expn,
                Vec::new(),
            );
        }
        scope
    }

    fn add_macro_use(&mut self, krate_root: DefId) {
        let names: Vec<(Symbol, Res)> = self
            .modules
            .get(&krate_root)
            .map(|m| {
                m.resolutions
                    .iter()
                    .filter(|((_, ns), _)| *ns == Ns::Macro)
                    .map(|((n, _), b)| (*n, b.res))
                    .collect()
            })
            .unwrap_or_default();
        for (name, res) in names {
            if let Some(d) = res.def_id() {
                self.macro_use_prelude.insert(name, d);
            }
        }
    }

    fn collect_mod(
        &mut self,
        module: DefId,
        mut item: P<ast::Item>,
        vis: Vis,
        scope: ScopeId,
        expn: ExpnId,
    ) -> ScopeId {
        let ident = item.ident;
        let parent_dir = self.modules[&module].dir.clone();
        let ItemKind::Mod(_, kind) = &mut item.kind else {
            unreachable!()
        };
        let (items, dir) = match std::mem::replace(kind, ModKind::Unloaded) {
            ModKind::Loaded {
                items,
                inline,
                span,
            } => {
                let dir = parent_dir.inline_child(ident.name, &item.attrs);
                *kind = ModKind::Loaded {
                    items: Vec::new(),
                    inline,
                    span,
                };
                (items, dir)
            }
            ModKind::Unloaded => {
                let candidates = match parent_dir.file_candidates(ident.name, &item.attrs) {
                    Ok(c) => c,
                    Err(msg) => {
                        self.sess.dcx.emit(Diag::error(msg).span(item.span, ""));
                        return scope;
                    }
                };
                let found = candidates.iter().find(|(p, _)| p.is_file()).cloned();
                let Some((path, dir)) = found else {
                    let names: Vec<String> = candidates
                        .iter()
                        .map(|(p, _)| p.display().to_string())
                        .collect();
                    self.sess.dcx.emit(
                        Diag::error(format!("file not found for module `{}`", ident.name))
                            .code("E0583")
                            .span(item.span, "")
                            .help(format!(
                                "to create the module `{}`, create file \"{}\"",
                                ident.name,
                                names.join("\" or \"")
                            )),
                    );
                    return scope;
                };
                let Some(parsed) = self.loader.take(&path, self.edition) else {
                    self.sess.dcx.emit(
                        Diag::error(format!("couldn't read `{}`", path.display()))
                            .span(item.span, ""),
                    );
                    return scope;
                };
                for d in parsed.diags {
                    self.sess.dcx.emit(d);
                }
                let mut inner = parsed.krate.attrs;
                // A module file's inner attributes are the module's: `#![cfg(…)]` at the top
                // of a file removes the module.
                let cfg_ctx = self.active_cfg_context();
                if !cfg::process_attrs_ctx(&cfg_ctx, &self.sess.dcx, self.edition, &mut inner) {
                    return scope;
                }
                item.attrs.extend(inner);
                if let ItemKind::Mod(_, kind) = &mut item.kind {
                    *kind = ModKind::Loaded {
                        items: Vec::new(),
                        inline: false,
                        span: parsed.krate.span,
                    };
                }
                (parsed.krate.items, dir)
            }
        };
        let id = self.new_def(DefKind::Mod, Some(module), ident.name, item.span, vis);
        let mut data = new_module(id, Some(module), id, dir);
        data.no_implicit_prelude = cfg::has_attr(&item.attrs, "no_implicit_prelude")
            || self.modules[&module].no_implicit_prelude;
        self.modules.insert(id, data);
        self.define_def(module, ident, Ns::Type, Res::Def(DefKind::Mod, id), vis);
        if let Some(lang) = lang_attr(&item.attrs) {
            self.lang_items.insert(lang, id);
        }
        let macro_use = cfg::has_attr(&item.attrs, "macro_use");
        self.item_scopes.insert(id, scope);
        self.item_expns.insert(id, expn);
        self.nodes[id.0 as usize] = ItemNode::Item(item);
        let end = self.collect_items(id, items, scope, expn);
        if macro_use { end } else { scope }
    }

    /// Defines a non-module item and binds its names; returns its `DefId`.
    fn define_item(
        &mut self,
        module: DefId,
        item: &mut P<ast::Item>,
        vis: Vis,
        scope: ScopeId,
        expn: ExpnId,
    ) -> DefId {
        let ident = item.ident;
        let span = item.span;
        let lang = lang_attr(&item.attrs);
        let (kind, ns) = match &item.kind {
            ItemKind::Struct(..) => (DefKind::Struct, Some(Ns::Type)),
            ItemKind::Union(..) => (DefKind::Union, Some(Ns::Type)),
            ItemKind::Enum(..) => (DefKind::Enum, Some(Ns::Type)),
            ItemKind::Trait(..) => (DefKind::Trait, Some(Ns::Type)),
            ItemKind::TraitAlias(..) => (DefKind::TraitAlias, Some(Ns::Type)),
            ItemKind::TyAlias(..) => (DefKind::TyAlias, Some(Ns::Type)),
            ItemKind::Fn(..) => (DefKind::Fn, Some(Ns::Value)),
            ItemKind::Const(..) => (DefKind::Const, Some(Ns::Value)),
            ItemKind::Static(s) => (
                DefKind::Static {
                    mutable: s.mutability == ast::Mutability::Mut,
                },
                Some(Ns::Value),
            ),
            ItemKind::Impl(imp) => (
                DefKind::Impl {
                    of_trait: imp.of_trait.is_some(),
                },
                None,
            ),
            ItemKind::ForeignMod(_) => (DefKind::ForeignMod, None),
            ItemKind::GlobalAsm(_) => (DefKind::GlobalAsm, None),
            ItemKind::Mod(..)
            | ItemKind::MacCall(_)
            | ItemKind::MacroDef(_)
            | ItemKind::Use(_)
            | ItemKind::ExternCrate(_) => {
                unreachable!("handled by collect_item")
            }
        };
        let id = self.new_def(kind, Some(module), ident.name, span, vis);
        self.item_scopes.insert(id, scope);
        self.item_expns.insert(id, expn);
        if let Some(lang) = lang {
            self.lang_items.insert(lang, id);
        }
        if let Some(ns) = ns {
            self.define_def(module, ident, ns, Res::Def(kind, id), vis);
        }
        match &mut item.kind {
            ItemKind::Struct(data, _) | ItemKind::Union(data, _) => {
                self.strip_fields(data);
                if let Some(ctor_kind) = ctor_kind(data) {
                    // The constructor is no more visible than the least visible field.
                    let mut ctor_vis = vis;
                    for f in data.fields() {
                        let fv = self.resolve_vis(&f.vis, module);
                        ctor_vis = self.min_vis(ctor_vis, fv);
                    }
                    if matches!(item.kind, ItemKind::Struct(..)) {
                        self.define_def(
                            module,
                            ident,
                            Ns::Value,
                            Res::Def(DefKind::Ctor(CtorOf::Struct, ctor_kind), id),
                            ctor_vis,
                        );
                    }
                }
            }
            ItemKind::Enum(def, _) => {
                let mut data = new_module(
                    id,
                    Some(module),
                    self.parent_module(module),
                    self.modules[&module].dir.clone(),
                );
                data.no_implicit_prelude = true;
                self.modules.insert(id, data);
                let cfg_ctx = self.active_cfg_context();
                def.variants.retain_mut(|v| {
                    cfg::process_attrs_ctx(&cfg_ctx, &self.sess.dcx, self.edition, &mut v.attrs)
                });
                for v in &mut def.variants {
                    self.strip_fields(&mut v.data);
                }
                for v in &def.variants {
                    let vid = self.new_def(DefKind::Variant, Some(id), v.ident.name, v.span, vis);
                    if let Some(lang) = lang_attr(&v.attrs) {
                        self.lang_items.insert(lang, vid);
                    }
                    self.define_def(id, v.ident, Ns::Type, Res::Def(DefKind::Variant, vid), vis);
                    if let Some(ck) = ctor_kind(&v.data) {
                        self.define_def(
                            id,
                            v.ident,
                            Ns::Value,
                            Res::Def(DefKind::Ctor(CtorOf::Variant, ck), vid),
                            vis,
                        );
                    }
                }
            }
            ItemKind::Trait(t) => {
                let mut data = new_module(
                    id,
                    Some(module),
                    self.parent_module(module),
                    self.modules[&module].dir.clone(),
                );
                data.no_implicit_prelude = true;
                self.modules.insert(id, data);
                let items = std::mem::take(&mut t.items);
                self.collect_assoc_items(id, module, items, scope, expn);
            }
            ItemKind::Impl(imp) => {
                self.impls.push(id);
                let items = std::mem::take(&mut imp.items);
                self.collect_assoc_items(id, module, items, scope, expn);
            }
            ItemKind::ForeignMod(fm) => {
                let items = std::mem::take(&mut fm.items);
                self.collect_foreign_items(id, module, items, scope, expn);
            }
            _ => {}
        }
        id
    }

    /// Removes fields whose `cfg` doesn't hold.
    fn strip_fields(&self, data: &mut VariantData) {
        match data {
            VariantData::Struct { fields } | VariantData::Tuple(fields, _) => {
                let cfg_ctx = self.active_cfg_context();
                fields.retain_mut(|f| {
                    cfg::process_attrs_ctx(&cfg_ctx, &self.sess.dcx, self.edition, &mut f.attrs)
                });
            }
            VariantData::Unit(_) => {}
        }
    }

    /// Associated items of a trait or impl `owner` declared in `module`.
    pub(crate) fn collect_assoc_items(
        &mut self,
        owner: DefId,
        module: DefId,
        items: Vec<P<ast::AssocItem>>,
        mut scope: ScopeId,
        expn: ExpnId,
    ) {
        let is_trait = self.def_kind(owner) == DefKind::Trait;
        let owner_vis = self.def(owner).vis;
        for mut item in items {
            if !self.keep(&mut item.attrs) {
                continue;
            }
            let span = item.span;
            let (kind, ns) = match &item.kind {
                AssocItemKind::MacCall(_) => {
                    let AssocItemKind::MacCall(mac) = std::mem::replace(
                        &mut item.kind,
                        AssocItemKind::Type(Box::new(empty_ty_alias())),
                    ) else {
                        unreachable!()
                    };
                    let attrs = std::mem::take(&mut item.attrs);
                    scope = self.push_invocation(
                        InvocKind::Bang(mac),
                        module,
                        scope,
                        FragmentKind::AssocItems(owner),
                        span,
                        expn,
                        attrs,
                    );
                    continue;
                }
                AssocItemKind::Fn(_) => (DefKind::AssocFn, Ns::Value),
                AssocItemKind::Const(_) => (DefKind::AssocConst, Ns::Value),
                AssocItemKind::Type(_) => (DefKind::AssocTy, Ns::Type),
            };
            let vis = if is_trait {
                owner_vis
            } else {
                self.resolve_vis(&item.vis, module)
            };
            let id = self.new_def(kind, Some(owner), item.ident.name, span, vis);
            self.item_scopes.insert(id, scope);
            self.item_expns.insert(id, expn);
            if let Some(lang) = lang_attr(&item.attrs) {
                self.lang_items.insert(lang, id);
            }
            if is_trait {
                self.define_def(owner, item.ident, ns, Res::Def(kind, id), Vis::Public);
            }
            self.nodes[id.0 as usize] = ItemNode::Assoc(item);
        }
    }

    pub(crate) fn collect_foreign_items(
        &mut self,
        owner: DefId,
        module: DefId,
        items: Vec<P<ast::ForeignItem>>,
        mut scope: ScopeId,
        expn: ExpnId,
    ) {
        for mut item in items {
            if !self.keep(&mut item.attrs) {
                continue;
            }
            let span = item.span;
            let (kind, ns) = match &item.kind {
                ForeignItemKind::MacCall(_) => {
                    let ForeignItemKind::MacCall(mac) = std::mem::replace(
                        &mut item.kind,
                        ForeignItemKind::TyAlias(Box::new(empty_ty_alias())),
                    ) else {
                        unreachable!()
                    };
                    let attrs = std::mem::take(&mut item.attrs);
                    scope = self.push_invocation(
                        InvocKind::Bang(mac),
                        module,
                        scope,
                        FragmentKind::ForeignItems(owner),
                        span,
                        expn,
                        attrs,
                    );
                    continue;
                }
                ForeignItemKind::Fn(_) => (DefKind::Fn, Ns::Value),
                ForeignItemKind::Static(s) => (
                    DefKind::Static {
                        mutable: s.mutability == ast::Mutability::Mut,
                    },
                    Ns::Value,
                ),
                ForeignItemKind::TyAlias(_) => (DefKind::ForeignTy, Ns::Type),
            };
            let vis = self.resolve_vis(&item.vis, module);
            let id = self.new_def(kind, Some(owner), item.ident.name, span, vis);
            self.item_scopes.insert(id, scope);
            self.item_expns.insert(id, expn);
            if let Some(lang) = lang_attr(&item.attrs) {
                self.lang_items.insert(lang, id);
            }
            self.define_def(module, item.ident, ns, Res::Def(kind, id), vis);
            self.nodes[id.0 as usize] = ItemNode::Foreign(item);
        }
    }

    /// Flattens a `use` tree into imports.
    #[allow(clippy::too_many_arguments)]
    fn collect_use_tree(
        &mut self,
        module: DefId,
        tree: &ast::UseTree,
        prefix: &[Ident],
        vis: Vis,
        is_prelude: bool,
        expn: ExpnId,
        scope: ScopeId,
    ) {
        let mut path: Vec<Ident> = prefix.to_vec();
        path.extend(tree.prefix.segments.iter().map(|s| s.ident));
        match &tree.kind {
            UseTreeKind::Simple(rename) => {
                let Some(&last) = path.last() else { return };
                // `use a::{self}` / `use a::{self as b}`: the module `a` itself.
                let (source_path, source, type_only) =
                    if last.name == kw::SelfLower && path.len() > 1 {
                        let p = path[..path.len() - 1].to_vec();
                        let s = *p.last().unwrap();
                        (p[..p.len() - 1].to_vec(), s, true)
                    } else {
                        (path[..path.len() - 1].to_vec(), last, false)
                    };
                let target = rename.unwrap_or(source);
                if target.name != kw::Underscore {
                    let idx = self.imports.len();
                    self.modules
                        .get_mut(&module)
                        .unwrap()
                        .single_imports
                        .entry(target.name)
                        .or_default()
                        .push(idx);
                }
                self.imports.push(Import {
                    module,
                    path: source_path,
                    kind: ImportKind::Single {
                        source,
                        target,
                        type_only,
                        results: [None; 3],
                    },
                    vis,
                    span: tree.span,
                    resolved: false,
                    failed: false,
                    expn,
                    scope,
                });
            }
            UseTreeKind::Glob => {
                self.imports.push(Import {
                    module,
                    path,
                    kind: ImportKind::Glob {
                        is_prelude,
                        target: None,
                    },
                    vis,
                    span: tree.span,
                    resolved: false,
                    failed: false,
                    expn,
                    scope,
                });
            }
            UseTreeKind::Nested { items, .. } => {
                for (sub, _) in items {
                    self.collect_use_tree(module, sub, &path, vis, is_prelude, expn, scope);
                }
            }
        }
    }
}

fn ctor_kind(data: &VariantData) -> Option<CtorKind> {
    match data {
        VariantData::Tuple(..) => Some(CtorKind::Fn),
        VariantData::Unit(_) => Some(CtorKind::Const),
        VariantData::Struct { .. } => None,
    }
}

/// The paths in `#[derive(A, B)]` and `#[derive_const(A, B)]` attributes, in order, with
/// whether they're `derive_const`.
pub(crate) fn derive_paths(attrs: &[ast::Attribute]) -> Vec<(ast::Path, bool)> {
    let mut out = Vec::new();
    for a in attrs {
        let is_const = a.name().is_some_and(|n| n.as_str() == "derive_const");
        if !a.has_name(sym::derive) && !is_const {
            continue;
        }
        let Some(item) = cfg::attr_item(a) else {
            continue;
        };
        let ast::AttrArgs::Delimited(args) = &item.args else {
            continue;
        };
        for part in cfg::split_commas(args.tokens.tokens()) {
            if part.is_empty() {
                continue;
            }
            let mut toks = part.to_vec();
            toks.push(hyprc_syntax::token::Token::new(
                hyprc_syntax::token::TokenKind::Eof,
                a.span,
            ));
            let dcx = hyprc_span::DiagCtxt::buffered();
            let mut p = hyprc_syntax::Parser::new(&toks, hyprc_span::Edition::E2021, &dcx);
            if let Ok(path) = p.parse_path(hyprc_syntax::PathStyle::Mod) {
                out.push((path, is_const));
            }
        }
    }
    out
}

fn empty_use_tree(span: Span) -> ast::UseTree {
    ast::UseTree {
        prefix: ast::Path {
            span,
            segments: Vec::new(),
        },
        kind: UseTreeKind::Glob,
        span,
    }
}

fn empty_ty_alias() -> ast::TyAlias {
    ast::TyAlias {
        defaultness: ast::Defaultness::Final,
        generics: ast::Generics::default(),
        bounds: Vec::new(),
        ty: None,
        after_where: ast::WhereClause::default(),
    }
}

fn extract_features_from_json(content: &str) -> Option<Vec<String>> {
    let key = "\"features\":";
    let idx = content.find(key)?;
    let rest = &content[idx + key.len()..];
    let start_bracket = rest.find('[')?;
    let end_bracket = rest[start_bracket..].find(']')?;
    let array_str = &rest[start_bracket + 1..start_bracket + end_bracket];
    let mut feats = Vec::new();
    let mut chars = array_str.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '"' {
            let mut s = String::new();
            for c2 in chars.by_ref() {
                if c2 == '\\' {
                    continue;
                }
                if c2 == '"' {
                    break;
                }
                s.push(c2);
            }
            if !s.is_empty() {
                feats.push(s);
            }
        }
    }
    Some(feats)
}

fn load_crate_cfgs(
    sess: &Session,
    name: Symbol,
    extern_artifact: Option<&Path>,
) -> (FxHashSet<(Symbol, Option<Symbol>)>, bool) {
    let mut cfgs = FxHashSet::default();
    for (k, v) in &sess.cfg {
        if k.as_str() != "feature" {
            cfgs.insert((*k, *v));
        }
    }

    let mut has_explicit_features = false;

    // 1. Try reading from HYPRC_META in the rmeta or rlib artifact
    let mut rmeta_candidates = Vec::new();
    if let Some(p) = extern_artifact {
        rmeta_candidates.push(p.to_path_buf());
        let companion = p.with_extension("rmeta");
        if companion != *p {
            rmeta_candidates.push(companion);
        }
    }

    let name_str = name.as_str();
    let name_dashed = name_str.replace('_', "-");
    let name_snake = name_str.replace('-', "_");

    // 1. Try reading from HYPRC_META in the rmeta or rlib artifact
    let mut rmeta_candidates = Vec::new();
    if let Some(p) = extern_artifact {
        if p.is_file() {
            rmeta_candidates.push(p.to_path_buf());
            let companion = p.with_extension("rmeta");
            if companion != *p {
                rmeta_candidates.push(companion);
            }
        } else if let Some(file_name) = p.file_name() {
            for (_, sp) in &sess.opts.search_paths {
                let cand = sp.join(file_name);
                if cand.is_file() {
                    rmeta_candidates.push(cand.clone());
                    let companion = cand.with_extension("rmeta");
                    if companion != cand {
                        rmeta_candidates.push(companion);
                    }
                }
            }
        }
    }

    let mut deps_dirs = Vec::new();
    for (_, sp) in &sess.opts.search_paths {
        deps_dirs.push(sp.clone());
    }
    deps_dirs.push(PathBuf::from("target/debug/deps"));
    deps_dirs.push(PathBuf::from("target/release/deps"));

    for deps_dir in deps_dirs {
        if let Ok(entries) = std::fs::read_dir(&deps_dir) {
            for entry in entries.flatten() {
                let fname = entry.file_name();
                let s = fname.to_string_lossy();
                if (s.starts_with(&format!("lib{name_snake}"))
                    || s.starts_with(&format!("lib{name_dashed}")))
                    && s.ends_with(".rmeta")
                {
                    rmeta_candidates.push(entry.path());
                }
            }
        }
    }

    for cand in rmeta_candidates {
        if cand.is_file() {
            if let Ok(content) = std::fs::read_to_string(&cand) {
                if content.starts_with("HYPRC_META") {
                    for line in content.lines() {
                        if let Some(cfg_str) = line.strip_prefix("cfg=") {
                            if let Some((k, v_str)) = cfg_str.split_once('=') {
                                let v = v_str.trim_matches('"');
                                let k_sym = Symbol::intern(k);
                                let v_sym = Symbol::intern(v);
                                if k == "feature" {
                                    has_explicit_features = true;
                                }
                                cfgs.insert((k_sym, Some(v_sym)));
                            } else {
                                cfgs.insert((Symbol::intern(cfg_str), None));
                            }
                        }
                    }
                    if has_explicit_features {
                        return (cfgs, true);
                    }
                }
            }
        }
    }

    // 2. Try reading features from .fingerprint
    let mut fp_dirs = Vec::new();
    if let Some(p) = extern_artifact {
        if let Some(deps_dir) = p.parent() {
            if let Some(target_dir) = deps_dir.parent() {
                fp_dirs.push(target_dir.join(".fingerprint"));
            }
        }
    }
    for (_, sp) in &sess.opts.search_paths {
        if let Some(target_dir) = sp.parent() {
            fp_dirs.push(target_dir.join(".fingerprint"));
        }
    }
    fp_dirs.push(PathBuf::from("target/debug/.fingerprint"));
    fp_dirs.push(PathBuf::from("target/release/.fingerprint"));

    let prefix_dashed = format!("{name_dashed}-");
    let prefix_snake = format!("{name_snake}-");

    // Gather candidate fingerprint folders, sorted by modification time (newest first)
    let mut cand_dirs = Vec::new();
    for fp_dir in fp_dirs {
        if let Ok(entries) = std::fs::read_dir(fp_dir) {
            for entry in entries.flatten() {
                let fname = entry.file_name();
                let s = fname.to_string_lossy();
                if s.starts_with(&prefix_dashed) || s.starts_with(&prefix_snake) {
                    let mtime = entry
                        .metadata()
                        .and_then(|m| m.modified())
                        .unwrap_or(std::time::SystemTime::UNIX_EPOCH);
                    cand_dirs.push((mtime, entry.path()));
                }
            }
        }
    }
    cand_dirs.sort_by(|a, b| b.0.cmp(&a.0));

    for (_, d) in cand_dirs {
        for json_name in [
            format!("lib-{name_snake}.json"),
            format!("lib-{name_dashed}.json"),
        ] {
            let json_path = d.join(json_name);
            if json_path.is_file() {
                if let Ok(content) = std::fs::read_to_string(&json_path) {
                    if let Some(feats) = extract_features_from_json(&content) {
                        for feat in feats {
                            cfgs.insert((Symbol::intern("feature"), Some(Symbol::intern(&feat))));
                        }
                        return (cfgs, true);
                    }
                }
            }
        }
    }

    (cfgs, has_explicit_features)
}

fn read_crate_edition(
    sess: &Session,
    name: Symbol,
    extern_artifact: Option<&Path>,
) -> Option<hyprc_span::Edition> {
    let mut rmeta_candidates = Vec::new();
    if let Some(p) = extern_artifact {
        if p.is_file() {
            rmeta_candidates.push(p.to_path_buf());
            let companion = p.with_extension("rmeta");
            if companion != *p {
                rmeta_candidates.push(companion);
            }
        }
    }
    let name_str = name.as_str();
    let name_dashed = name_str.replace('_', "-");
    let name_snake = name_str.replace('-', "_");

    for (_, sp) in &sess.opts.search_paths {
        if let Ok(entries) = std::fs::read_dir(sp) {
            for entry in entries.flatten() {
                let fname = entry.file_name();
                let s = fname.to_string_lossy();
                if (s.starts_with(&format!("lib{name_snake}"))
                    || s.starts_with(&format!("lib{name_dashed}")))
                    && s.ends_with(".rmeta")
                {
                    rmeta_candidates.push(entry.path());
                }
            }
        }
    }

    for cand in rmeta_candidates {
        if cand.is_file() {
            if let Ok(content) = std::fs::read_to_string(&cand) {
                if content.starts_with("HYPRC_META") {
                    for line in content.lines() {
                        if let Some(ed_str) = line.strip_prefix("edition=") {
                            if let Some(ed) = hyprc_span::Edition::parse(ed_str) {
                                return Some(ed);
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

impl<'s> Resolver<'s> {
    pub(crate) fn load_extern_crate(&mut self, name: Symbol, path: &Path) -> Option<DefId> {
        let krate = crate::CrateNum(self.crate_roots.len() as u32);
        let root = DefId(self.defs.len() as u32);
        self.defs.push(crate::DefData {
            kind: DefKind::Mod,
            krate,
            parent: None,
            name,
            span: Span::DUMMY,
            vis: Vis::Public,
        });
        self.nodes.push(ItemNode::None);
        self.crate_roots.push(root);
        self.extern_prelude.insert(name, root);

        let extern_artifact = self
            .sess
            .opts
            .externs
            .iter()
            .find(|e| e.name == name.as_str())
            .and_then(|e| e.path.as_deref());
        let (cfgs, has_feats) = load_crate_cfgs(self.sess, name, extern_artifact);
        self.crate_cfgs.insert(krate, cfgs);
        if has_feats {
            self.crate_has_explicit_features.insert(krate);
        }

        let crate_edition = if name == sym::core
            || name == Symbol::intern("alloc")
            || name == Symbol::intern("std")
            || name == Symbol::intern("proc_macro")
        {
            hyprc_span::Edition::E2021
        } else {
            read_crate_edition(self.sess, name, extern_artifact)
                .unwrap_or(hyprc_span::Edition::E2021)
        };
        self.crate_editions.insert(krate, crate_edition);

        let prev_krate = self.current_krate;
        let prev_edition = self.edition;
        self.current_krate = krate;
        self.edition = crate_edition;

        let dir = ModDir::owned_by_file(path);
        let parsed = self.loader.take(path, self.edition)?;
        for d in parsed.diags {
            self.sess.dcx.emit(d);
        }
        let ast::Crate {
            mut attrs,
            items,
            span,
        } = parsed.krate;
        self.defs[root.0 as usize].span = span;
        cfg::expand_cfg_attrs_ctx(
            &self.active_cfg_context(),
            &self.sess.dcx,
            self.edition,
            &mut attrs,
        );
        let mut module = new_module(root, None, root, dir.clone());
        let no_implicit_prelude = cfg::has_attr(&attrs, "no_implicit_prelude");
        module.no_implicit_prelude = no_implicit_prelude;
        self.modules.insert(root, module);

        if !no_implicit_prelude && name != sym::core {
            let is_no_std = cfg::has_attr(&attrs, "no_std");
            let prelude_crate = if !is_no_std {
                if !self.extern_prelude.contains_key(&Symbol::intern("std")) {
                    if let Some(std_path) = find_sysroot_crate(self.sess, "std") {
                        self.load_extern_crate(Symbol::intern("std"), &std_path);
                    }
                }
                if self.extern_prelude.contains_key(&Symbol::intern("std")) {
                    Symbol::intern("std")
                } else {
                    sym::core
                }
            } else {
                sym::core
            };
            let edition_sym = match crate_edition {
                hyprc_span::Edition::E2024 => Symbol::intern("rust_2024"),
                hyprc_span::Edition::E2021 => Symbol::intern("rust_2021"),
                hyprc_span::Edition::E2018 => Symbol::intern("rust_2018"),
                hyprc_span::Edition::E2015 => Symbol::intern("rust_2015"),
            };
            self.imports.push(Import {
                module: root,
                scope: ScopeId::EMPTY,
                vis: Vis::Restricted(root),
                span: Span::DUMMY,
                path: vec![
                    Ident::new(prelude_crate, Span::DUMMY),
                    Ident::new(Symbol::intern("prelude"), Span::DUMMY),
                    Ident::new(edition_sym, Span::DUMMY),
                ],
                kind: ImportKind::Glob {
                    is_prelude: true,
                    target: None,
                },
                expn: ExpnId::ROOT,
                resolved: false,
                failed: false,
            });
        }

        let cfg_ctx = self.active_cfg_context();
        self.loader.prefetch(&cfg_ctx, self.edition, &items, &dir);
        self.collect_items(root, items, ScopeId::EMPTY, ExpnId::ROOT);

        self.add_macro_use(root);

        self.current_krate = prev_krate;
        self.edition = prev_edition;
        Some(root)
    }

    pub(crate) fn try_load_named_crate(&mut self, name: Symbol) -> Option<DefId> {
        if let Some(&root) = self.extern_prelude.get(&name) {
            return Some(root);
        }
        let name_str = name.as_str();
        if let Some(path) = find_sysroot_crate(self.sess, name_str) {
            return self.load_extern_crate(name, &path);
        }
        for e in &self.sess.opts.externs {
            if e.name == name_str {
                if let Some(p) = &e.path {
                    if let Some(f) = resolve_extern_source(&e.name, p, self.sess) {
                        return self.load_extern_crate(name, &f);
                    }
                }
            }
        }
        if let Some(src) = resolve_extern_source(name_str, Path::new(""), self.sess) {
            return self.load_extern_crate(name, &src);
        }
        None
    }

    pub(crate) fn load_extern_crates(&mut self) {
        let mut loaded_core = false;
        let mut loaded_alloc = false;
        let mut loaded_std = false;

        for e in &self.sess.opts.externs {
            let name_sym = Symbol::intern(&e.name);
            if let Some(p) = &e.path {
                if let Some(f) = resolve_extern_source(&e.name, p, self.sess) {
                    self.load_extern_crate(name_sym, &f);
                    if name_sym == sym::core {
                        loaded_core = true;
                    } else if name_sym == Symbol::intern("alloc") {
                        loaded_alloc = true;
                    } else if name_sym == Symbol::intern("std") {
                        loaded_std = true;
                    }
                }
            }
        }

        if !self.no_core && self.crate_name != sym::core && !loaded_core {
            if let Some(core_path) = find_sysroot_crate(self.sess, "core") {
                self.load_extern_crate(sym::core, &core_path);
            }
        }
        if !self.no_core
            && !self.no_std
            && self.crate_name != Symbol::intern("alloc")
            && !loaded_alloc
        {
            if let Some(alloc_path) = find_sysroot_crate(self.sess, "alloc") {
                self.load_extern_crate(Symbol::intern("alloc"), &alloc_path);
            }
        }
        if !self.no_core
            && !self.no_std
            && self.crate_name != Symbol::intern("std")
            && self.crate_name != Symbol::intern("libc")
            && !loaded_std
        {
            if let Some(std_path) = find_sysroot_crate(self.sess, "std") {
                self.load_extern_crate(Symbol::intern("std"), &std_path);
            }
        }
    }
}

fn resolve_extern_source(name: &str, p: &Path, sess: &Session) -> Option<PathBuf> {
    let resolved_p = if p.is_file() || p.as_os_str().is_empty() {
        p.to_path_buf()
    } else {
        sess.opts
            .search_paths
            .iter()
            .find_map(|(_, sp)| {
                let cand = sp.join(p.file_name()?);
                cand.is_file().then_some(cand)
            })
            .unwrap_or_else(|| p.to_path_buf())
    };
    let p = &resolved_p;

    if p.is_file() && p.extension().is_some_and(|ext| ext == "rs") {
        return Some(p.to_path_buf());
    }
    if p.join("src/lib.rs").is_file() {
        return Some(p.join("src/lib.rs"));
    }
    if p.join("lib.rs").is_file() {
        return Some(p.join("lib.rs"));
    }

    if p.is_file() {
        // 1. Check if it's a hyprc metadata file containing "HYPRC_META\nsource=<path>"
        if let Ok(content) = std::fs::read_to_string(p) {
            if content.starts_with("HYPRC_META") {
                for line in content.lines() {
                    if let Some(src) = line.strip_prefix("source=") {
                        let path = PathBuf::from(src);
                        if path.is_file() {
                            return Some(path);
                        }
                    }
                }
            }
        }

        // 2. Check companion .rmeta if p was .rlib
        let rmeta_path = p.with_extension("rmeta");
        if rmeta_path != *p && rmeta_path.is_file() {
            if let Ok(content) = std::fs::read_to_string(&rmeta_path) {
                if content.starts_with("HYPRC_META") {
                    for line in content.lines() {
                        if let Some(src) = line.strip_prefix("source=") {
                            let path = PathBuf::from(src);
                            if path.is_file() {
                                return Some(path);
                            }
                        }
                    }
                }
            }
        }

        // 3. Check companion .d dep-info file in the same directory (e.g. target/debug/deps/foo.d)
        if let Some(parent) = p.parent() {
            if let Some(file_name) = p.file_name().and_then(|f| f.to_str()) {
                let stem = p.file_stem().and_then(|s| s.to_str()).unwrap_or("");
                let stem_no_lib = stem.strip_prefix("lib").unwrap_or(stem);
                for d_name in [
                    format!("{stem}.d"),
                    format!("{stem_no_lib}.d"),
                    format!("{file_name}.d"),
                ] {
                    let d_path = parent.join(d_name);
                    if d_path.is_file() {
                        if let Ok(d_content) = std::fs::read_to_string(&d_path) {
                            for line in d_content.lines() {
                                if let Some((_, deps)) = line.split_once(':') {
                                    for part in deps.split_whitespace() {
                                        if part.ends_with(".rs") {
                                            let cand = PathBuf::from(part);
                                            if cand.is_file() {
                                                return Some(cand);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // 4. Sysroot fallback
    if let Some(sys_crate) = find_sysroot_crate(sess, name) {
        return Some(sys_crate);
    }

    // 5. Registry fallback: .igel/registry or .cargo/registry
    if let Some(home) = std::env::var_os("HOME").map(PathBuf::from) {
        for reg_base in [
            home.join(".igel/registry/src"),
            home.join(".cargo/registry/src"),
        ] {
            if let Ok(index_dirs) = std::fs::read_dir(reg_base) {
                for index_dir in index_dirs.flatten() {
                    if let Ok(crate_dirs) = std::fs::read_dir(index_dir.path()) {
                        for crate_dir in crate_dirs.flatten() {
                            let name_with_dash = format!("{name}-");
                            let dir_name = crate_dir.file_name();
                            let dir_str = dir_name.to_string_lossy();
                            if dir_str.starts_with(&name_with_dash) {
                                let cand = crate_dir.path().join("src/lib.rs");
                                if cand.is_file() {
                                    return Some(cand);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // 6. Workspace crates fallback
    let ws_cand = PathBuf::from(format!("crates/{name}/src/lib.rs"));
    if ws_cand.is_file() {
        return Some(ws_cand);
    }

    None
}

fn find_sysroot_crate(sess: &Session, crate_name: &str) -> Option<PathBuf> {
    for e in &sess.opts.externs {
        if e.name == crate_name {
            if let Some(p) = &e.path {
                if p.is_file() && p.extension().is_some_and(|ext| ext == "rs") {
                    return Some(p.clone());
                }
                let cand = p.join("src/lib.rs");
                if cand.is_file() {
                    return Some(cand);
                }
                let cand = p.join("lib.rs");
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    // 1. Check hyprc's own bundled libraries (e.g. hyprc/library/std/src/lib.rs)
    for base in [
        PathBuf::from("hyprc/library"),
        PathBuf::from("library"),
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../library"),
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../library"),
    ] {
        let cand = base.join(crate_name).join("src/lib.rs");
        if cand.is_file() {
            return Some(cand);
        }
    }

    if let Some(sysroot) = &sess.opts.sysroot {
        let cand = sysroot.join(format!(
            "lib/rustlib/src/rust/library/{crate_name}/src/lib.rs"
        ));
        if cand.is_file() {
            return Some(cand);
        }
    }
    if let Some(home) = std::env::var_os("HOME").map(PathBuf::from) {
        let rustup = home.join(".rustup/toolchains");
        for tc in [
            "1.98.1-x86_64-unknown-linux-gnu",
            "1.99.0-x86_64-unknown-linux-gnu",
            "stable-x86_64-unknown-linux-gnu",
        ] {
            let cand = rustup.join(tc).join(format!(
                "lib/rustlib/src/rust/library/{crate_name}/src/lib.rs"
            ));
            if cand.is_file() {
                return Some(cand);
            }
        }
        if let Ok(entries) = std::fs::read_dir(&rustup) {
            for entry in entries.flatten() {
                let cand = entry.path().join(format!(
                    "lib/rustlib/src/rust/library/{crate_name}/src/lib.rs"
                ));
                if cand.is_file() {
                    return Some(cand);
                }
            }
        }
    }
    None
}
