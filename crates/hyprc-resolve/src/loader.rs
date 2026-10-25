//! Finding and parsing the files of out-of-line modules (`mod foo;`).
//!
//! The file rules are rustc's: `foo.rs` or `foo/mod.rs` next to a `mod.rs`-like file (the
//! crate root, a `mod.rs`, a `#[path]` file), `parent/foo.rs` or `parent/foo/mod.rs` next to
//! any other file, inline modules adding their name to the directory, and `#[path]` relative
//! to the current module's directory.
//!
//! Files are parsed in parallel ahead of collection: as soon as a file is parsed, the files
//! of its `mod` declarations are queued, so the whole module tree loads on all cores.
//! Collection then takes parsed files from the cache.

use crate::cfg;
use hyprc_span::{Diag, DiagCtxt, Edition, FxHashMap, SourceFile, Symbol, source_map};
use hyprc_syntax::ast::{self, ItemKind, ModKind, P};
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

/// Where a module's `mod x;` declarations look for files.
#[derive(Clone, Debug)]
pub struct ModDir {
    pub path: PathBuf,
    /// For a module in a non-`mod.rs` file `foo.rs`: `foo`, so its children are `foo/x.rs`.
    pub relative: Option<Symbol>,
    /// Inside a block (`fn f() { mod m; }`): only `#[path]` modules can be loaded.
    pub in_block: bool,
}

impl ModDir {
    /// The directory of a file treated as `mod.rs` (crate roots, `mod.rs`, `#[path]` files).
    pub fn owned_by_file(file: &Path) -> ModDir {
        ModDir {
            path: file.parent().map(Path::to_path_buf).unwrap_or_default(),
            relative: None,
            in_block: false,
        }
    }

    /// The directory of an inline module `mod name { … }` declared in this one.
    pub fn inline_child(&self, name: Symbol, attrs: &[ast::Attribute]) -> ModDir {
        if let Some(p) = path_attr(attrs) {
            // For inline modules, `#[path]` names the directory itself.
            return ModDir {
                path: self.path.join(p.as_str()),
                relative: None,
                in_block: self.in_block,
            };
        }
        let mut path = self.path.clone();
        if let Some(rel) = self.relative {
            path.push(rel.as_str());
        }
        path.push(name.as_str());
        ModDir {
            path,
            relative: None,
            in_block: self.in_block,
        }
    }

    /// Candidate files for `mod name;`, and the directory its children use.
    pub fn file_candidates(
        &self,
        name: Symbol,
        attrs: &[ast::Attribute],
    ) -> Result<Vec<(PathBuf, ModDir)>, String> {
        if let Some(p) = path_attr(attrs) {
            let file = self.path.join(p.as_str());
            let dir = ModDir::owned_by_file(&file);
            return Ok(vec![(file, dir)]);
        }
        if self.in_block {
            return Err(
                "cannot declare a file module inside a block unless it has a path attribute"
                    .to_string(),
            );
        }
        let mut base = self.path.clone();
        if let Some(rel) = self.relative {
            base.push(rel.as_str());
        }
        let primary = base.join(format!("{name}.rs"));
        let secondary = base.join(name.as_str()).join("mod.rs");
        let primary_dir = ModDir {
            path: base.clone(),
            relative: Some(name),
            in_block: false,
        };
        let secondary_dir = ModDir::owned_by_file(&secondary);
        Ok(vec![(primary, primary_dir), (secondary, secondary_dir)])
    }
}

fn path_attr(attrs: &[ast::Attribute]) -> Option<Symbol> {
    attrs
        .iter()
        .find(|a| a.has_name(hyprc_span::sym::path))
        .and_then(cfg::attr_str_value)
}

pub struct ParsedFile {
    #[allow(dead_code)]
    pub file: Arc<SourceFile>,
    pub krate: ast::Crate,
    /// Diagnostics from lexing and parsing, reported when the file is used.
    pub diags: Vec<Diag>,
}

#[derive(Default)]
pub struct Loader {
    cache: Mutex<FxHashMap<PathBuf, Option<ParsedFile>>>,
}

pub fn parse_path(path: &Path, edition: Edition) -> Option<ParsedFile> {
    let file = source_map().load_file(path).ok()?;
    let dcx = DiagCtxt::buffered();
    let tokens = hyprc_syntax::tokenize(file.src, file.start, &dcx);
    let krate = hyprc_syntax::parse_file(&tokens, edition, &dcx);
    Some(ParsedFile {
        file,
        krate,
        diags: dcx.take(),
    })
}

impl Loader {
    /// Takes a parsed file from the cache, parsing it now if prefetching didn't.
    pub fn take(&self, path: &Path, edition: Edition) -> Option<ParsedFile> {
        let cached = self.cache.lock().unwrap().remove(path);
        match cached {
            Some(parsed) => parsed,
            None => parse_path(path, edition),
        }
    }

    /// Parses, in parallel, the files of every `mod x;` reachable from `items` (outside
    /// macros), following the module tree down.
    pub fn prefetch<'a, C: cfg::CfgContext + Sync>(
        &'a self,
        ctx: &'a C,
        edition: Edition,
        items: &[P<ast::Item>],
        dir: &ModDir,
    ) {
        let todo = mods_to_load(ctx, edition, items, dir);
        let run = move |s: &rayon::Scope<'a>| {
            for (path, child_dir) in todo {
                self.spawn_load(s, ctx, edition, path, child_dir);
            }
        };
        match rayon::ThreadPoolBuilder::new()
            .stack_size(hyprc_syntax::PARSER_STACK_SIZE)
            .build()
        {
            Ok(pool) => pool.scope(run),
            Err(_) => rayon::scope(run),
        }
    }

    fn spawn_load<'a, C: cfg::CfgContext + Sync>(
        &'a self,
        s: &rayon::Scope<'a>,
        ctx: &'a C,
        edition: Edition,
        path: PathBuf,
        dir: ModDir,
    ) {
        {
            let mut cache = self.cache.lock().unwrap();
            if cache.contains_key(&path) {
                return;
            }
            cache.insert(path.clone(), None);
        }
        s.spawn(move |s| {
            let parsed = parse_path(&path, edition);
            let next = parsed.as_ref().map_or_else(Vec::new, |p| {
                mods_to_load(ctx, edition, &p.krate.items, &dir)
            });
            self.cache.lock().unwrap().insert(path, parsed);
            for (path, dir) in next {
                self.spawn_load(s, ctx, edition, path, dir);
            }
        });
    }
}

/// The files of `mod x;` declarations in these items and in inline modules among them,
/// with `cfg` evaluated leniently (an unparsable `cfg` loads the file; collection reports
/// the error).
fn mods_to_load<C: cfg::CfgContext>(
    ctx: &C,
    edition: Edition,
    items: &[P<ast::Item>],
    dir: &ModDir,
) -> Vec<(PathBuf, ModDir)> {
    let mut out = Vec::new();
    let quiet = DiagCtxt::buffered();
    for item in items {
        let ItemKind::Mod(_, kind) = &item.kind else {
            continue;
        };
        let mut attrs = item.attrs.clone();
        cfg::expand_cfg_attrs_ctx(ctx, &quiet, edition, &mut attrs);
        if !cfg::cfg_holds_ctx(ctx, &quiet, &attrs) {
            continue;
        }
        match kind {
            ModKind::Loaded {
                items,
                inline: true,
                ..
            } => {
                let child = dir.inline_child(item.ident.name, &attrs);
                out.extend(mods_to_load(ctx, edition, items, &child));
            }
            ModKind::Unloaded => {
                let Ok(candidates) = dir.file_candidates(item.ident.name, &attrs) else {
                    continue;
                };
                if let Some(found) = candidates.into_iter().find(|(p, _)| p.is_file()) {
                    out.push(found);
                }
            }
            _ => {}
        }
    }
    out
}
