//! Symbol names, in rustc's legacy mangling (`_ZN…17h<hash>E`) so tools that demangle Rust
//! symbols (debuggers, profilers, hyprlnk's diagnostics) show readable paths.

use hyprc_hir::DefId;
use hyprc_mir::mono::{Instance, InstanceKind};
use hyprc_ty::TyCtxt;
use std::hash::{BuildHasher, Hash, Hasher};

fn escape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
            '<' => out.push_str("$LT$"),
            '>' => out.push_str("$GT$"),
            ' ' => out.push_str("$u20$"),
            '&' => out.push_str("$RF$"),
            '*' => out.push_str("$BP$"),
            '@' => out.push_str("$SP$"),
            ',' => out.push_str("$C$"),
            ':' => out.push_str(".."),
            c => out.push_str(&format!("$u{:x}$", c as u32)),
        }
    }
    if out.starts_with(|c: char| c.is_ascii_digit()) {
        out.insert(0, '_');
    }
    out
}

fn mangle_path(parts: &[String], hash: u64) -> String {
    let mut s = String::from("_ZN");
    for p in parts {
        let e = escape(p);
        s.push_str(&e.len().to_string());
        s.push_str(&e);
    }
    let h = format!("h{hash:016x}");
    s.push_str(&h.len().to_string());
    s.push_str(&h);
    s.push('E');
    s
}

fn path_parts(tcx: &TyCtxt<'_>, def: DefId) -> Vec<String> {
    tcx.def_path(def)
        .split("::")
        .map(|s| s.to_string())
        .collect()
}

fn hash_of(x: impl Hash) -> u64 {
    let mut h = rustc_hash::FxBuildHasher.build_hasher();
    x.hash(&mut h);
    h.finish()
}

pub fn symbol_name(tcx: &TyCtxt<'_>, inst: Instance) -> String {
    match inst.kind {
        InstanceKind::Foreign(d) => {
            let item = tcx.hir.get_item(d);
            item.and_then(|i| i.attrs.link_name).map_or_else(
                || tcx.hir.name(d).as_str().to_string(),
                |s| s.as_str().to_string(),
            )
        }
        InstanceKind::Item(d) => {
            if let Some(item) = tcx.hir.get_item(d) {
                if let Some(e) = item.attrs.export_name {
                    return e.as_str().to_string();
                }
                if item.attrs.no_mangle {
                    return item.name.as_str().to_string();
                }
            }
            let parts = path_parts(tcx, d);
            let key = format!("{}{:?}", tcx.def_path(d), inst.args.as_slice());
            mangle_path(&parts, hash_of(key))
        }
        InstanceKind::Closure(c) => {
            let mut parts = path_parts(tcx, c.owner);
            parts.push(format!("{{closure#{}}}", c.index));
            let key = format!(
                "{}{}{}{:?}",
                tcx.def_path(c.owner),
                c.body,
                c.index,
                inst.args.as_slice()
            );
            mangle_path(&parts, hash_of(key))
        }
        other => {
            let key = format!("{other:?}{:?}", inst.args.as_slice());
            mangle_path(&["hyprc_shim".to_string()], hash_of(key))
        }
    }
}

pub fn static_symbol(tcx: &TyCtxt<'_>, def: DefId) -> String {
    if let Some(item) = tcx.hir.get_item(def) {
        if let Some(e) = item.attrs.export_name {
            return e.as_str().to_string();
        }
        if item.attrs.no_mangle {
            return item.name.as_str().to_string();
        }
        if let hyprc_hir::ItemKind::Static { foreign: true, .. } = item.kind {
            return item.attrs.link_name.map_or_else(
                || item.name.as_str().to_string(),
                |s| s.as_str().to_string(),
            );
        }
    }
    let parts = path_parts(tcx, def);
    mangle_path(&parts, hash_of(tcx.def_path(def)))
}
