//! `use` declarations, resolved to a fixed point together with macro expansion.

use crate::paths::{Lookup, PathResult};
use crate::{ALL_NS, Binding, BindingKind, DefId, Ns, Res, Resolver, Vis};
use hyprc_span::hygiene::ExpnId;
use hyprc_span::{Diag, Ident, Span, kw};

pub(crate) struct Import {
    /// The scope the `use` is in.
    pub module: DefId,
    /// For a single import, the path up to (not including) the imported name; for a glob,
    /// the whole path.
    pub path: Vec<Ident>,
    pub kind: ImportKind,
    pub vis: Vis,
    pub span: Span,
    pub resolved: bool,
    /// Given up on (reported, or its path failed).
    pub failed: bool,
    #[allow(dead_code)]
    pub expn: ExpnId,
    /// The `macro_rules!` scope at the import: `use m;` can name a `macro_rules! m` above it.
    pub scope: crate::ScopeId,
}

pub(crate) enum ImportKind {
    Single {
        source: Ident,
        target: Ident,
        /// `use a::{self}`: only the module (type namespace).
        type_only: bool,
        /// What was found so far in each namespace (`Type`, `Value`, `Macro`).
        results: [Option<Res>; 3],
    },
    Glob {
        /// `#[prelude_import]`: the standard prelude, not an ordinary glob.
        is_prelude: bool,
        target: Option<DefId>,
    },
}

pub(crate) fn ns_index(ns: Ns) -> usize {
    match ns {
        Ns::Type => 0,
        Ns::Value => 1,
        Ns::Macro => 2,
    }
}

impl Resolver<'_> {
    /// One pass over the unresolved imports. Returns whether anything changed.
    pub(crate) fn resolve_imports_round(&mut self) -> bool {
        let mut progress = false;
        for idx in 0..self.imports.len() {
            if self.imports[idx].resolved {
                continue;
            }
            progress |= match self.imports[idx].kind {
                ImportKind::Single { .. } => self.resolve_single_import(idx),
                ImportKind::Glob { .. } => self.resolve_glob_import(idx),
            };
        }
        progress
    }

    /// Where a single import's name is looked up: the module its path names, or for a
    /// one-segment `use name;`, the current scope and the extern prelude.
    fn import_source_scope(&self, idx: usize) -> Result<Option<DefId>, bool> {
        let imp = &self.imports[idx];
        if imp.path.is_empty() {
            return Ok(None);
        }
        match self.resolve_path(&imp.path, Ns::Type, imp.module, true) {
            PathResult::Module(m) => Ok(Some(m)),
            // `use Enum::Variant;`, `use Trait::item;`
            PathResult::NonModule {
                res: Res::Def(crate::DefKind::Enum | crate::DefKind::Trait, d),
                unresolved: 0,
            } if self.modules.contains_key(&d) => Ok(Some(d)),
            PathResult::Indeterminate => Err(false),
            PathResult::NonModule { .. } | PathResult::Failed { .. } => Err(true),
        }
    }

    fn resolve_single_import(&mut self, idx: usize) -> bool {
        let (source, target, type_only) = match &self.imports[idx].kind {
            ImportKind::Single {
                source,
                target,
                type_only,
                ..
            } => (*source, *target, *type_only),
            _ => unreachable!(),
        };
        let module = self.imports[idx].module;
        let vis = self.imports[idx].vis;
        let span = self.imports[idx].span;
        let textual = self.imports[idx].scope;
        self.set_current_import(Some(idx));
        let scope = self.import_source_scope(idx);
        self.set_current_import(None);
        let scope = match scope {
            Ok(s) => s,
            // Failed paths are reported at the end, when nothing more can change.
            Err(_) => return false,
        };
        // `use crate;`, `use self as x;`, `use super;`: the module itself.
        if scope.is_none()
            && matches!(
                source.name,
                kw::Crate | kw::SelfLower | kw::Super | kw::DollarCrate
            )
        {
            if let PathResult::Module(m) = self.resolve_path(&[source], Ns::Type, module, true) {
                self.define(
                    module,
                    target,
                    Ns::Type,
                    Binding {
                        res: Res::Def(crate::DefKind::Mod, m),
                        vis,
                        span,
                        kind: BindingKind::Import(idx),
                    },
                );
                self.imports[idx].resolved = true;
                return true;
            }
            return false;
        }
        let mut progress = false;
        let mut indeterminate = false;
        for ns in ALL_NS {
            if type_only && ns != Ns::Type {
                continue;
            }
            if let ImportKind::Single { results, .. } = &self.imports[idx].kind
                && results[ns_index(ns)].is_some()
            {
                continue;
            }
            self.set_current_import(Some(idx));
            let lookup = match scope {
                Some(m) => self.lookup_in_module(m, source.name, ns),
                None if !self.edition_of(module).at_least_2018() => {
                    self.lookup_in_module(self.crate_root_of(module), source.name, ns)
                }
                None => {
                    // `use name;` in 2018: a `macro_rules!` above it, a name in scope here,
                    // or a crate.
                    let mut weak = false;
                    let textual = if ns == Ns::Macro {
                        match self.lookup_textual(source.name, textual) {
                            crate::expand::MacroLookup::Found(d) => Some(d),
                            crate::expand::MacroLookup::Indeterminate => {
                                weak = true;
                                None
                            }
                            crate::expand::MacroLookup::NotFound => None,
                        }
                    } else {
                        None
                    };
                    match textual {
                        Some(d) => Lookup::Found(Binding {
                            res: Res::Def(crate::DefKind::Macro(crate::MacroKind::Bang), d),
                            vis: Vis::Public,
                            span,
                            kind: BindingKind::Def,
                        }),
                        None => match self.resolve_ident_lexical_ext(source, ns, module, weak) {
                            Lookup::Found(b) if matches!(b.kind, BindingKind::Import(i) if i == idx) => {
                                Lookup::NotFound
                            }
                            other => other,
                        },
                    }
                }
            };
            self.set_current_import(None);
            match lookup {
                Lookup::Found(b) => {
                    // An import can't make a name more visible than it is.
                    let import_vis = self.min_vis(vis, b.vis);
                    if let ImportKind::Single { results, .. } = &mut self.imports[idx].kind {
                        results[ns_index(ns)] = Some(b.res);
                    }
                    if target.name == kw::Underscore {
                        // `use Trait as _;`: the trait is in scope for method calls.
                        if let Res::Def(crate::DefKind::Trait, t) = b.res {
                            self.modules.get_mut(&module).unwrap().anon_traits.push(t);
                        }
                    } else {
                        self.define(
                            module,
                            target,
                            ns,
                            Binding {
                                res: b.res,
                                vis: import_vis,
                                span,
                                kind: BindingKind::Import(idx),
                            },
                        );
                    }
                    progress = true;
                }
                Lookup::Indeterminate => indeterminate = true,
                Lookup::NotFound => {}
            }
        }
        let found_any = match &self.imports[idx].kind {
            ImportKind::Single { results, .. } => results.iter().any(Option::is_some),
            _ => false,
        };
        if !indeterminate && found_any {
            self.imports[idx].resolved = true;
            progress = true;
        }
        progress
    }

    fn resolve_glob_import(&mut self, idx: usize) -> bool {
        let module = self.imports[idx].module;
        let path = self.imports[idx].path.clone();
        self.set_current_import(Some(idx));
        let target = self.resolve_path(&path, Ns::Type, module, true);
        self.set_current_import(None);
        let target = match target {
            PathResult::Module(m) => m,
            PathResult::NonModule {
                res: Res::Def(crate::DefKind::Enum | crate::DefKind::Trait, d),
                unresolved: 0,
            } => d,
            _ => return false,
        };
        self.imports[idx].resolved = true;
        let is_prelude = matches!(
            self.imports[idx].kind,
            ImportKind::Glob {
                is_prelude: true,
                ..
            }
        );
        if let ImportKind::Glob { target: t, .. } = &mut self.imports[idx].kind {
            *t = Some(target);
        }
        if is_prelude {
            let krate = self.defs[self.imports[idx].module.0 as usize].krate;
            self.crate_preludes.insert(krate, target);
            self.crate_has_prelude_import.insert(krate);
            self.prelude = Some(target);
            self.has_prelude_import = true;
            return true;
        }
        self.modules.get_mut(&module).unwrap().globs.push(idx);
        self.modules
            .get_mut(&target)
            .unwrap()
            .glob_importers
            .push(idx);
        let names: Vec<((hyprc_span::Symbol, Ns), Binding)> = self.modules[&target]
            .resolutions
            .iter()
            .map(|(k, b)| (*k, *b))
            .collect();
        for ((name, ns), b) in names {
            self.import_by_glob(idx, Ident::new(name, b.span), ns, b);
        }
        true
    }

    fn import_by_glob(&mut self, idx: usize, ident: Ident, ns: Ns, b: Binding) {
        let importer = self.imports[idx].module;
        if !self.is_accessible_from(b.vis, importer) {
            return;
        }
        let vis = self.min_vis(self.imports[idx].vis, b.vis);
        let res = match b.kind {
            BindingKind::Ambiguous(_) => b.res,
            _ => b.res,
        };
        self.define(
            importer,
            ident,
            ns,
            Binding {
                res,
                vis,
                span: self.imports[idx].span,
                kind: BindingKind::Glob(idx),
            },
        );
    }

    /// A name appeared or changed in `module`: pass it on to globs importing from it.
    pub(crate) fn propagate_to_glob_importers(&mut self, module: DefId, ident: Ident, ns: Ns) {
        let importers = match self.modules.get(&module) {
            Some(m) if !m.glob_importers.is_empty() => m.glob_importers.clone(),
            _ => return,
        };
        let Some(b) = self.modules[&module]
            .resolutions
            .get(&(ident.name, ns))
            .copied()
        else {
            return;
        };
        for idx in importers {
            self.import_by_glob(idx, ident, ns, b);
        }
    }

    pub(crate) fn report_unresolved_imports(&mut self) {
        for idx in 0..self.imports.len() {
            if self.imports[idx].resolved {
                continue;
            }
            self.imports[idx].failed = true;
            let imp = &self.imports[idx];
            let mut full: Vec<String> = imp
                .path
                .iter()
                .map(|i| i.name.as_str().to_string())
                .collect();
            if let ImportKind::Single {
                source, results, ..
            } = &imp.kind
            {
                if results.iter().any(Option::is_some) {
                    continue;
                }
                full.push(source.name.as_str().to_string());
            }
            let full = full.join("::").replace("{{root}}::", "::");
            self.sess.dcx.emit(
                Diag::error(format!("unresolved import `{full}`"))
                    .code("E0432")
                    .span(imp.span, "no such module or item"),
            );
        }
    }
}
