//! Resolving names and paths in module scopes.

use crate::{Binding, BindingKind, DefId, DefKind, Ns, PrimTy, Res, Resolver};
use hyprc_span::{Ident, Span, Symbol, SyntaxContext, kw};

#[derive(Clone, Copy, Debug)]
pub enum PathResult {
    /// The path names a module, enum, trait or block scope.
    Module(DefId),
    /// The path resolves to `res` after its first segments; the last `unresolved` segments
    /// are associated items (`Vec::new`: `Vec` resolved, `new` left for type checking).
    NonModule {
        res: Res,
        unresolved: usize,
    },
    /// Can't tell yet: a scope on the way still has unexpanded macros or unresolved globs.
    Indeterminate,
    Failed {
        span: Span,
        segment: usize,
    },
}

/// One step of a path, for diagnostics.
#[derive(Clone, Copy, Debug)]
pub struct PathSegmentRes {
    pub ident: Ident,
    pub res: Option<Res>,
}

#[derive(Clone, Copy, Debug)]
pub enum Lookup {
    Found(Binding),
    NotFound,
    Indeterminate,
}

/// Why a name can't be looked up yet (as rustc tells them apart in early resolution).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Undetermined {
    /// An unresolved single import may define the name here: nothing outside this scope may
    /// be used instead.
    Strong,
    /// Only a macro expansion or a glob may still add it. Those can't shadow names from
    /// outer scopes (that's an ambiguity error), so outer scopes may be searched meanwhile.
    Weak,
}

impl Resolver<'_> {
    /// A name in one scope (not its parents or preludes).
    pub fn lookup_in_module(&self, module: DefId, name: Symbol, ns: Ns) -> Lookup {
        match self.lookup_in_module_ext(module, name, ns) {
            Ok(Some(b)) => Lookup::Found(b),
            Ok(None) => Lookup::NotFound,
            Err(_) => Lookup::Indeterminate,
        }
    }

    fn lookup_in_module_ext(
        &self,
        module: DefId,
        name: Symbol,
        ns: Ns,
    ) -> Result<Option<Binding>, Undetermined> {
        let Some(m) = self.modules.get(&module) else {
            return Ok(None);
        };
        let found = m.resolutions.get(&(name, ns)).copied();
        if let Some(b) = found
            && !matches!(b.kind, BindingKind::Glob(_))
        {
            return Ok(Some(b));
        }
        // A glob binding (or none): a single import may still define the name.
        if self.single_import_pending(m, name, ns) {
            return Err(Undetermined::Strong);
        }
        if found.is_some() {
            return Ok(found);
        }
        let pending_glob = m.globs.iter().any(|&g| !self.imports[g].resolved);
        if m.pending_macros > 0 || pending_glob {
            Err(Undetermined::Weak)
        } else {
            Ok(None)
        }
    }

    fn single_import_pending(&self, m: &crate::ModuleData, name: Symbol, ns: Ns) -> bool {
        let Some(list) = m.single_imports.get(&name) else {
            return false;
        };
        let current = self.current_import();
        list.iter().any(|&i| {
            let imp = &self.imports[i];
            if imp.resolved || imp.failed || Some(i) == current {
                return false;
            }
            match &imp.kind {
                crate::imports::ImportKind::Single {
                    results, type_only, ..
                } => {
                    results[crate::imports::ns_index(ns)].is_none()
                        && (!*type_only || ns == Ns::Type)
                }
                _ => false,
            }
        })
    }

    fn found(res: Res) -> Lookup {
        Lookup::Found(Binding {
            res,
            vis: crate::Vis::Public,
            span: Span::DUMMY,
            kind: BindingKind::Def,
        })
    }

    /// A single name as code in `scope` sees it: the scope and the blocks around it up to the
    /// nearest module, then the extern prelude, `#[macro_use]` macros, the standard prelude,
    /// and built-in types.
    ///
    /// Like rustc during expansion, scopes that may still get the name from a macro or a
    /// glob don't stop the search: the first name found further out is used.
    pub fn resolve_ident_lexical(&self, ident: Ident, ns: Ns, scope: DefId) -> Lookup {
        self.resolve_ident_lexical_ext(ident, ns, scope, false)
    }

    /// `weak_before`: a scope searched before this one (the `macro_rules!` scope) may still
    /// get the name.
    pub(crate) fn resolve_ident_lexical_ext(
        &self,
        ident: Ident,
        ns: Ns,
        scope: DefId,
        weak_before: bool,
    ) -> Lookup {
        let mut cur = scope;
        let mut no_prelude = false;
        let mut weak = weak_before;
        // Opaque marks: the name was written in a `macro` (2.0) and means what it means where
        // that macro is defined.
        let mut ctxt = ident.span.ctxt.normalize_to_macros_2_0();
        loop {
            match self.lookup_in_module_ext(cur, ident.name, ns) {
                Ok(Some(b)) => return Lookup::Found(b),
                Ok(None) => {}
                Err(Undetermined::Weak) => weak = true,
                Err(Undetermined::Strong) => return Lookup::Indeterminate,
            }
            let m = &self.modules[&cur];
            no_prelude |= m.no_implicit_prelude;
            if self.def_kind(cur) == DefKind::Block
                && let Some(p) = m.parent
            {
                cur = p;
                continue;
            }
            // Not here: from the definition site of the macro that wrote the name.
            if ctxt != SyntaxContext::ROOT {
                let def = ctxt.outer_expn().data().macro_def;
                ctxt = ctxt.parent();
                if def != u32::MAX && (def as usize) < self.defs.len() {
                    let def_module = self.parent_module(DefId(def));
                    if def_module != cur {
                        cur = def_module;
                    }
                    continue;
                }
                continue;
            }
            break;
        }
        match self.resolve_in_preludes(ident.name, ns, no_prelude, cur) {
            Lookup::NotFound if weak => Lookup::Indeterminate,
            other => other,
        }
    }

    pub fn resolve_in_preludes(
        &self,
        name: Symbol,
        ns: Ns,
        no_implicit_prelude: bool,
        scope: DefId,
    ) -> Lookup {
        let allow_prelude = !no_implicit_prelude || self.has_prelude_import_for(scope);
        match ns {
            Ns::Type => {
                if let Some(&root) = self.extern_prelude.get(&name) {
                    return Self::found(Res::Def(DefKind::Mod, root));
                }
            }
            Ns::Macro => {
                if allow_prelude && let Some(&m) = self.macro_use_prelude.get(&name) {
                    return Self::found(Res::Def(self.def_kind(m), m));
                }
            }
            Ns::Value => {}
        }
        if allow_prelude && let Some(prelude) = self.prelude_of(scope) {
            match self.lookup_in_module(prelude, name, ns) {
                Lookup::Found(b) => return Lookup::Found(b),
                Lookup::Indeterminate => return Lookup::Indeterminate,
                Lookup::NotFound => {}
            }
        }
        if ns == Ns::Type
            && let Some(p) = PrimTy::from_name(name)
        {
            return Self::found(Res::PrimTy(p));
        }
        Lookup::NotFound
    }

    /// The crate root `$crate` means for a token: the crate of the macro that wrote it.
    pub fn dollar_crate_root(&self, ident: Ident) -> DefId {
        let expn = ident.span.ctxt.dollar_crate_expn();
        let krate = self
            .expn_crates
            .get(&expn)
            .copied()
            .unwrap_or(crate::CrateNum::LOCAL);
        self.crate_roots
            .get(krate.0 as usize)
            .copied()
            .unwrap_or(self.root)
    }

    /// Resolves a path in `scope`; `ns` is the namespace of the last segment.
    ///
    /// `import`: resolving a `use` path. In 2015 such paths start at the crate root; in 2018
    /// and later they start in the current scope or at a crate name.
    pub fn resolve_path(&self, path: &[Ident], ns: Ns, scope: DefId, import: bool) -> PathResult {
        let mut module: Option<DefId> = None;
        let mut i = 0;
        while i < path.len() {
            let seg = path[i];
            let is_last = i + 1 == path.len();
            let seg_ns = if is_last { ns } else { Ns::Type };
            let name = seg.name;
            // Path-root keywords.
            if i == 0 || (name == kw::Super && module.is_some()) {
                let handled = match name {
                    kw::PathRoot => {
                        if self.edition_of(scope).at_least_2018() {
                            // `::crate_name::…`
                            let Some(next) = path.get(1) else {
                                return PathResult::Failed {
                                    span: seg.span,
                                    segment: 0,
                                };
                            };
                            match self.extern_prelude.get(&next.name) {
                                Some(&root) => {
                                    module = Some(root);
                                    i += 2;
                                    if i == path.len() {
                                        return PathResult::Module(root);
                                    }
                                    continue;
                                }
                                None => {
                                    return PathResult::Failed {
                                        span: next.span,
                                        segment: 1,
                                    };
                                }
                            }
                        }
                        module = Some(self.crate_root_of(scope));
                        true
                    }
                    kw::Crate => {
                        module = Some(self.crate_root_of(scope));
                        true
                    }
                    kw::DollarCrate => {
                        module = Some(self.dollar_crate_root(seg));
                        true
                    }
                    kw::SelfLower if i == 0 => {
                        module = Some(self.parent_module(scope));
                        true
                    }
                    kw::Super => {
                        let base = module.unwrap_or_else(|| self.parent_module(scope));
                        let normal = self.parent_module(base);
                        match self.modules[&normal].parent {
                            Some(p) => module = Some(self.parent_module(p)),
                            None => {
                                return PathResult::Failed {
                                    span: seg.span,
                                    segment: i,
                                };
                            }
                        }
                        true
                    }
                    _ => false,
                };
                if handled {
                    i += 1;
                    if i == path.len() {
                        return PathResult::Module(module.unwrap());
                    }
                    continue;
                }
            }
            let lookup = match module {
                Some(m) => self.lookup_in_module(m, name, seg_ns),
                None => {
                    if import && !self.edition_of(scope).at_least_2018() {
                        let l = self.lookup_in_module(self.crate_root_of(scope), name, seg_ns);
                        if let Lookup::NotFound = l {
                            if let Some(&root) = self.extern_prelude.get(&name) {
                                Lookup::Found(crate::Binding {
                                    res: Res::Def(crate::DefKind::Mod, root),
                                    vis: crate::Vis::Public,
                                    span: seg.span,
                                    kind: crate::BindingKind::Def,
                                })
                            } else {
                                l
                            }
                        } else {
                            l
                        }
                    } else {
                        self.resolve_ident_lexical(seg, seg_ns, scope)
                    }
                }
            };
            let res = match lookup {
                Lookup::Found(b) => b.res,
                Lookup::Indeterminate => return PathResult::Indeterminate,
                // `Enum::method`, `Trait::CONST`: not a variant or a trait item by name, so
                // an associated item of the type, found with types (as in rustc).
                Lookup::NotFound
                    if let Some(m) = module
                        && matches!(self.def_kind(m), DefKind::Enum | DefKind::Trait) =>
                {
                    return PathResult::NonModule {
                        res: Res::Def(self.def_kind(m), m),
                        unresolved: path.len() - i,
                    };
                }
                Lookup::NotFound => {
                    return PathResult::Failed {
                        span: seg.span,
                        segment: i,
                    };
                }
            };
            if is_last {
                return match res {
                    Res::Def(DefKind::Mod | DefKind::Block, d) if ns == Ns::Type => {
                        PathResult::Module(d)
                    }
                    _ => PathResult::NonModule { res, unresolved: 0 },
                };
            }
            match res {
                Res::Def(DefKind::Mod | DefKind::Enum | DefKind::Trait | DefKind::Block, d)
                    if self.modules.contains_key(&d) =>
                {
                    module = Some(d);
                }
                Res::Err => return PathResult::NonModule { res, unresolved: 0 },
                // A type: the rest are associated items, resolved with types.
                _ => {
                    return PathResult::NonModule {
                        res,
                        unresolved: path.len() - i - 1,
                    };
                }
            }
            i += 1;
        }
        match module {
            Some(m) => PathResult::Module(m),
            None => PathResult::Failed {
                span: Span::DUMMY,
                segment: 0,
            },
        }
    }

    /// Resolves a module path right away (for `pub(in path)`): `None` if it doesn't name a
    /// module yet.
    pub(crate) fn resolve_module_path_now(&self, path: &[Ident], scope: DefId) -> Option<DefId> {
        match self.resolve_path(path, Ns::Type, scope, true) {
            PathResult::Module(m) => Some(m),
            _ => None,
        }
    }
}
