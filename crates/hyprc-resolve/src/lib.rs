//! Expansion and name resolution: from a parsed root file to a fully expanded crate whose
//! module-level names are resolved.
//!
//! The work happens in two phases, like rust-analyzer's def map and rustc's resolver:
//!
//! 1. **Items.** Modules are loaded and items collected into a table of definitions; `cfg`
//!    removes what doesn't apply; imports are resolved and item-level macros expanded,
//!    together, until nothing changes (a macro can define what an import needs and an import
//!    can bring a macro into scope).
//! 2. **Bodies.** Macros inside function bodies, constants and types are expanded in place,
//!    and the items inside bodies collected, with all module-level names already known.
//!
//! What comes out: the definitions (`defs`), their syntax trees (`nodes`), and the module
//! scopes later stages resolve paths in (`modules`, through [`Resolver::resolve_path`]).

mod body;
pub mod cfg;
mod collect;
pub mod defs;
mod derive;
mod expand;
mod imports;
mod loader;
pub mod macros;
mod paths;

pub use defs::*;
pub use paths::{Lookup, PathResult, PathSegmentRes};

use hyprc_span::hygiene::ExpnId;
use hyprc_span::session::Session;
use hyprc_span::{Edition, FxHashMap, FxHashSet, Ident, Span, Symbol};
use hyprc_syntax::ast::{self, P};

/// The syntax of a definition, moved out of the tree into this table so it can be found by
/// `DefId`. Variants, blocks and other definitions without their own node have `None`.
pub enum ItemNode {
    None,
    Item(P<ast::Item>),
    Assoc(P<ast::AssocItem>),
    Foreign(P<ast::ForeignItem>),
}

/// A name in a module's scope.
#[derive(Clone, Copy, Debug)]
pub struct Binding {
    pub res: Res,
    pub vis: Vis,
    pub span: Span,
    pub kind: BindingKind,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingKind {
    /// Defined here.
    Def,
    /// Brought in by a single `use` (index into the imports).
    Import(usize),
    /// Brought in by a glob import.
    Glob(usize),
    /// Two glob imports bring different things under this name; using it is an error.
    Ambiguous(Res),
}

/// A scope names can be looked up in: a module, block, enum or trait.
pub struct ModuleData {
    pub def: DefId,
    /// The scope this one is nested in: the parent module, or the enclosing block or module
    /// for a block. `None` for a crate root.
    pub parent: Option<DefId>,
    /// The nearest real module (`self` in paths): itself for modules.
    pub normal_module: DefId,
    pub resolutions: FxHashMap<(Symbol, Ns), Binding>,
    /// Glob imports into this scope (import indices).
    pub globs: Vec<usize>,
    /// Glob imports that import from this scope; new names propagate to them.
    pub glob_importers: Vec<usize>,
    /// Traits imported with `use Trait as _`: in scope for method calls without a name.
    pub anon_traits: Vec<DefId>,
    pub no_implicit_prelude: bool,
    /// Item-level macro calls in this scope not yet expanded: names may still appear.
    pub pending_macros: u32,
    /// Single imports into this scope by the name they define (import indices): while one
    /// is unresolved, its name can't be looked up past this scope.
    pub single_imports: FxHashMap<Symbol, Vec<usize>>,
    /// Where `mod x;` inside this module looks for files.
    pub dir: loader::ModDir,
}

/// Textual scope of `macro_rules!` macros: a chain from the innermost definition outwards.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ScopeId(pub u32);

impl ScopeId {
    pub const EMPTY: ScopeId = ScopeId(0);
}

#[derive(Clone, Copy, Debug)]
pub enum TextualScope {
    Empty,
    Def {
        name: Symbol,
        mac: DefId,
        parent: ScopeId,
    },
    /// The point after a macro call: whatever `macro_rules!` its expansion defines is in scope
    /// from here on, once it is expanded.
    Invocation {
        invoc: usize,
        parent: ScopeId,
    },
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FragmentKind {
    Items,
    /// In a trait or impl (its `DefId`).
    AssocItems(DefId),
    /// In an `extern` block (the block's `DefId`).
    ForeignItems(DefId),
}

pub enum InvocKind {
    Bang(P<ast::MacCall>),
    /// `#[derive(Path)]` on the item with this `DefId` (`#[derive_const(Path)]`: `is_const`).
    Derive {
        path: ast::Path,
        item: DefId,
        is_const: bool,
    },
}

pub struct Invocation {
    pub kind: InvocKind,
    /// The scope paths resolve in.
    pub module: DefId,
    /// The textual macro scope at the call.
    pub scope: ScopeId,
    pub fragment: FragmentKind,
    pub span: Span,
    /// The expansion this call was produced by (`ROOT` for source code).
    pub parent_expn: ExpnId,
    /// Attributes of the call (`#[cfg]` already applied); `#[macro_use]`-style ones matter.
    pub attrs: Vec<ast::Attribute>,
    /// Set once expanded: the textual scope after the expansion's items.
    pub output_scope: Option<ScopeId>,
    pub done: bool,
    pub failed: bool,
}

/// Compiled `macro_rules!` and `macro` definitions.
pub struct MacroData {
    pub def: DefId,
    pub kind: macros::MacroImpl,
    /// The crate whose items `$crate` names.
    pub krate: CrateNum,
    pub edition: Edition,
    /// `macro` 2.0 (opaque hygiene) rather than `macro_rules!` (semi-transparent).
    pub macro_2_0: bool,
}

pub struct Resolver<'s> {
    pub sess: &'s Session,
    pub edition: Edition,
    pub crate_name: Symbol,
    pub root: DefId,
    pub defs: Vec<DefData>,
    pub nodes: Vec<ItemNode>,
    pub modules: FxHashMap<DefId, ModuleData>,
    /// Children of definitions: items of modules, associated items of traits and impls,
    /// variants of enums, foreign items of extern blocks.
    pub children: FxHashMap<DefId, Vec<DefId>>,
    pub impls: Vec<DefId>,
    pub crate_attrs: Vec<ast::Attribute>,
    pub features: FxHashSet<Symbol>,
    pub lang_items: FxHashMap<Symbol, DefId>,
    /// Crates nameable without `extern crate` (`--extern`, `core`, `std`).
    pub extern_prelude: FxHashMap<Symbol, DefId>,
    /// `#[macro_use] extern crate`: macros nameable everywhere.
    pub macro_use_prelude: FxHashMap<Symbol, DefId>,
    /// The module whose names are the standard prelude (`std::prelude::rust_20xx`).
    pub prelude: Option<DefId>,
    pub has_prelude_import: bool,
    pub no_std: bool,
    pub no_core: bool,
    pub no_main: bool,

    pub(crate) imports: Vec<imports::Import>,
    pub invocations: Vec<Invocation>,
    pub scopes: Vec<TextualScope>,
    pub macros: FxHashMap<DefId, MacroData>,
    /// The textual macro scope at each item (bodies expand macros with it).
    pub item_scopes: FxHashMap<DefId, ScopeId>,
    /// The expansion each item came from.
    pub item_expns: FxHashMap<DefId, ExpnId>,
    pub(crate) loader: loader::Loader,
    /// Each expansion's crate (for `$crate`).
    pub expn_crates: FxHashMap<ExpnId, CrateNum>,
    /// Roots of crates: crate 0 is the local crate.
    pub crate_roots: Vec<DefId>,
    /// The crate currently being loaded (for assigning `DefData::krate`).
    pub current_krate: CrateNum,
    /// Explicit cfgs for extern crates loaded from metadata or fingerprint.
    pub crate_cfgs: FxHashMap<CrateNum, FxHashSet<(Symbol, Option<Symbol>)>>,
    /// Tracks which crates have an explicit list of known enabled features.
    pub crate_has_explicit_features: FxHashSet<CrateNum>,
    /// Per-crate editions.
    pub crate_editions: FxHashMap<CrateNum, Edition>,
    /// Per-crate preludes.
    pub crate_preludes: FxHashMap<CrateNum, DefId>,
    /// Tracks which crates have a prelude_import.
    pub crate_has_prelude_import: FxHashSet<CrateNum>,
    /// The import being resolved, which mustn't wait for itself (`usize::MAX`: none).
    pub(crate) current_import: std::sync::atomic::AtomicUsize,
}

#[derive(Clone, Copy)]
pub struct ActiveCfgContext<'a> {
    pub sess: &'a Session,
    pub cfgs: Option<&'a FxHashSet<(Symbol, Option<Symbol>)>>,
    pub has_explicit_features: bool,
    pub is_root: bool,
}

impl cfg::CfgContext for ActiveCfgContext<'_> {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        if self.is_root {
            return self.sess.cfg.contains(&(name, value));
        }
        if let Some(cfgs) = self.cfgs {
            if cfgs.contains(&(name, value)) {
                return true;
            }
            if name.as_str() != "feature" && self.sess.cfg.contains(&(name, value)) {
                return true;
            }
            false
        } else {
            if name.as_str() == "feature" {
                false
            } else {
                self.sess.cfg.contains(&(name, value))
            }
        }
    }
}

impl<'s> cfg::CfgContext for Resolver<'s> {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        self.active_cfg_context().cfg_set(name, value)
    }
}

impl Resolver<'_> {
    pub fn edition_of(&self, scope: DefId) -> Edition {
        let krate = self
            .defs
            .get(scope.0 as usize)
            .map(|d| d.krate)
            .unwrap_or(CrateNum::LOCAL);
        self.crate_editions
            .get(&krate)
            .copied()
            .unwrap_or(self.edition)
    }

    pub fn prelude_of(&self, scope: DefId) -> Option<DefId> {
        let krate = self
            .defs
            .get(scope.0 as usize)
            .map(|d| d.krate)
            .unwrap_or(CrateNum::LOCAL);
        self.crate_preludes.get(&krate).copied().or(self.prelude)
    }

    pub fn has_prelude_import_for(&self, scope: DefId) -> bool {
        let krate = self
            .defs
            .get(scope.0 as usize)
            .map(|d| d.krate)
            .unwrap_or(CrateNum::LOCAL);
        self.crate_has_prelude_import.contains(&krate) || self.has_prelude_import
    }

    pub fn active_cfg_context(&self) -> ActiveCfgContext<'_> {
        let is_root = self.current_krate == CrateNum::LOCAL;
        let cfgs = self.crate_cfgs.get(&self.current_krate);
        let has_explicit_features = self
            .crate_has_explicit_features
            .contains(&self.current_krate);
        ActiveCfgContext {
            sess: self.sess,
            cfgs,
            has_explicit_features,
            is_root,
        }
    }

    pub(crate) fn set_current_import(&self, idx: Option<usize>) {
        self.current_import.store(
            idx.unwrap_or(usize::MAX),
            std::sync::atomic::Ordering::Relaxed,
        );
    }

    pub(crate) fn current_import(&self) -> Option<usize> {
        let v = self
            .current_import
            .load(std::sync::atomic::Ordering::Relaxed);
        (v != usize::MAX).then_some(v)
    }
}

impl<'s> Resolver<'s> {
    pub fn def(&self, id: DefId) -> &DefData {
        &self.defs[id.0 as usize]
    }

    pub fn def_kind(&self, id: DefId) -> DefKind {
        self.defs[id.0 as usize].kind
    }

    pub fn item(&self, id: DefId) -> Option<&ast::Item> {
        match &self.nodes[id.0 as usize] {
            ItemNode::Item(i) => Some(i),
            _ => None,
        }
    }

    pub fn module(&self, id: DefId) -> &ModuleData {
        &self.modules[&id]
    }

    pub fn children(&self, id: DefId) -> &[DefId] {
        self.children.get(&id).map_or(&[], |v| v)
    }

    /// The nearest enclosing module (`self` for paths) of a definition.
    pub fn parent_module(&self, mut id: DefId) -> DefId {
        loop {
            if let Some(m) = self.modules.get(&id)
                && matches!(self.def_kind(id), DefKind::Mod | DefKind::Block)
            {
                return m.normal_module;
            }
            match self.def(id).parent {
                Some(p) => id = p,
                None => return id,
            }
        }
    }

    /// The root module of the crate `def` belongs to.
    pub fn crate_root_of(&self, def: DefId) -> DefId {
        let krate = self.def(def).krate;
        self.crate_roots
            .get(krate.0 as usize)
            .copied()
            .unwrap_or(self.root)
    }

    /// The scope (module or block) an item's names resolve in.
    pub fn scope_of(&self, mut id: DefId) -> DefId {
        loop {
            match self.def(id).parent {
                Some(p) => {
                    if matches!(self.def_kind(p), DefKind::Mod | DefKind::Block) {
                        return p;
                    }
                    id = p;
                }
                None => return id,
            }
        }
    }

    pub fn def_path_str(&self, id: DefId) -> String {
        let mut parts = Vec::new();
        let mut cur = Some(id);
        while let Some(d) = cur {
            let data = self.def(d);
            if data.parent.is_some() && data.name != hyprc_span::kw::Empty {
                parts.push(data.name.as_str().to_string());
            } else if data.parent.is_none() {
                parts.push(self.crate_name.as_str().to_string());
            }
            cur = data.parent;
        }
        parts.reverse();
        parts.join("::")
    }

    /// Is `module` (a module or block) the same as or inside `ancestor`?
    pub fn is_descendant_of(&self, mut module: DefId, ancestor: DefId) -> bool {
        loop {
            if module == ancestor {
                return true;
            }
            match self.def(module).parent {
                Some(p) => module = p,
                None => return false,
            }
        }
    }

    pub fn is_accessible_from(&self, vis: Vis, module: DefId) -> bool {
        match vis {
            Vis::Public => true,
            Vis::Restricted(m) => self.is_descendant_of(module, m),
        }
    }

    /// The more restrictive of two visibilities.
    pub fn min_vis(&self, a: Vis, b: Vis) -> Vis {
        match (a, b) {
            (Vis::Public, v) | (v, Vis::Public) => v,
            (Vis::Restricted(x), Vis::Restricted(y)) => {
                if self.is_descendant_of(x, y) {
                    Vis::Restricted(x)
                } else {
                    Vis::Restricted(y)
                }
            }
        }
    }

    pub fn new_def(
        &mut self,
        kind: DefKind,
        parent: Option<DefId>,
        name: Symbol,
        span: Span,
        vis: Vis,
    ) -> DefId {
        let krate = parent.map_or(self.current_krate, |p| self.def(p).krate);
        let id = DefId(self.defs.len() as u32);
        self.defs.push(DefData {
            kind,
            krate,
            parent,
            name,
            span,
            vis,
        });
        self.nodes.push(ItemNode::None);
        if let Some(p) = parent {
            self.children.entry(p).or_default().push(id);
        }
        id
    }

    pub fn has_feature(&self, name: &str) -> bool {
        self.features.contains(&Symbol::intern(name))
    }

    /// Resolves a lang item by name (`sized`, `add`, …).
    pub fn lang_item(&self, name: &str) -> Option<DefId> {
        self.lang_items.get(&Symbol::intern(name)).copied()
    }

    pub fn ident_ns_lookup(&self, module: DefId, ident: Ident, ns: Ns) -> Option<Binding> {
        self.modules
            .get(&module)?
            .resolutions
            .get(&(ident.name, ns))
            .copied()
    }
}

/// Runs phase 1 and phase 2 on a crate: everything expanded, every module-level name
/// resolved. Errors go to the session's diagnostics.
pub fn resolve_crate<'s>(
    sess: &'s Session,
    crate_name: &str,
    root_file: &std::path::Path,
) -> Resolver<'s> {
    let mut r = collect::new_resolver(sess, Symbol::intern(crate_name), root_file);
    r.resolve_items();
    r.expand_bodies();
    r
}
