//! Code generation: compiles every instance a program needs to x86-64, writes an ELF
//! object, and links it.

pub mod elf;
pub mod link;
mod mangle;
pub mod x86_64;

use elf::{Object, Section, SymKind, Symbol};
use hyprc_hir as hir;
use hyprc_hir::DefId;
use hyprc_mir::layout::LayoutCx;
use hyprc_mir::mono::{Instance, InstanceKind, MonoCtxt};
use hyprc_ty::{Abi, Args, Const, ConstKind, Ty, TyCtxt, TyKind};
use rustc_hash::FxHashMap;
use std::sync::Mutex;
use x86_64::asm::{Reloc, RelocKind};

pub struct CodegenCx<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    pub mcx: &'a MonoCtxt<'a, 'h>,
    pub lcx: LayoutCx<'a, 'h>,
    rodata: Mutex<(Vec<u8>, FxHashMap<Vec<u8>, String>, Vec<(String, u64, u64)>)>,
    symbols: Mutex<FxHashMap<Instance, String>>,
    /// Instances code generation found it needs that collection didn't (panic functions).
    requested: Mutex<Vec<Instance>>,
}

impl<'a, 'h> CodegenCx<'a, 'h> {
    pub fn new(tcx: &'a TyCtxt<'h>, mcx: &'a MonoCtxt<'a, 'h>) -> Self {
        CodegenCx {
            tcx,
            mcx,
            lcx: LayoutCx::new(tcx),
            rodata: Mutex::new((Vec::new(), FxHashMap::default(), Vec::new())),
            symbols: Mutex::new(FxHashMap::default()),
            requested: Mutex::new(Vec::new()),
        }
    }

    pub fn request(&self, inst: Instance) {
        self.requested.lock().unwrap().push(inst);
    }

    pub fn resolve(&self, def: DefId, args: Args) -> Option<Instance> {
        self.mcx.resolve(def, args)
    }

    /// The linker-visible name of an instance.
    pub fn symbol_for(&self, inst: Instance) -> String {
        if let Some(s) = self.symbols.lock().unwrap().get(&inst) {
            return s.clone();
        }
        let s = mangle::symbol_name(self.tcx, inst);
        self.symbols.lock().unwrap().insert(inst, s.clone());
        s
    }

    /// Does the instance's symbol need to be visible outside this object?
    pub fn is_exported(&self, inst: Instance) -> bool {
        match inst.kind {
            InstanceKind::Item(d) => self
                .tcx
                .hir
                .get_item(d)
                .is_some_and(|i| i.attrs.no_mangle || i.attrs.export_name.is_some()),
            _ => false,
        }
    }

    pub fn instance_abi(&self, inst: Instance) -> Abi {
        match inst.kind {
            InstanceKind::Item(d) | InstanceKind::Foreign(d) => self.tcx.fn_sig(d).abi,
            _ => Abi::Rust,
        }
    }

    /// A symbol for bytes in read-only data (deduplicated).
    pub fn rodata_symbol(&self, bytes: &[u8]) -> String {
        let mut g = self.rodata.lock().unwrap();
        if let Some(s) = g.1.get(bytes) {
            return s.clone();
        }
        let name = format!(".Lhyprc.rodata.{}", g.1.len());
        while g.0.len() % 8 != 0 {
            g.0.push(0);
        }
        let off = g.0.len() as u64;
        g.0.extend_from_slice(bytes);
        g.1.insert(bytes.to_vec(), name.clone());
        g.2.push((name.clone(), off, bytes.len() as u64));
        name
    }

    pub fn static_symbol(&self, def: DefId) -> String {
        mangle::static_symbol(self.tcx, def)
    }

    pub fn eval_const(&self, c: Const) -> Result<u128, String> {
        match c.kind() {
            ConstKind::Value(v) => Ok(v),
            ConstKind::Unevaluated { body, args, .. } => {
                let r = self.tcx.eval_const_body(hir::BodyId(body), c.ty(), args);
                r.try_to_bits()
                    .ok_or_else(|| "a constant hyprc can't evaluate yet".to_string())
            }
            _ => Err("a generic constant without arguments".into()),
        }
    }

    pub fn eval_const_item(&self, def: DefId, args: Args, ty: Ty) -> Result<u128, String> {
        let item = self
            .tcx
            .hir
            .get_item(def)
            .ok_or("constant without a definition")?;
        let hir::ItemKind::Const { body: Some(b), .. } = &item.kind else {
            return Err(format!(
                "the constant `{}` has no value",
                self.tcx.def_path(def)
            ));
        };
        let c = self.tcx.eval_const_body(*b, ty, args);
        c.try_to_bits().ok_or_else(|| {
            format!(
                "hyprc can't evaluate the constant `{}` yet",
                self.tcx.def_path(def)
            )
        })
    }

    /// Does dropping a value of this type run code?
    pub fn needs_drop(&self, t: Ty) -> bool {
        match *t.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::Never
            | TyKind::RawPtr(..)
            | TyKind::Ref(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(_)
            | TyKind::Str => false,
            TyKind::Tuple(ts) => ts.as_slice().iter().any(|&t| self.needs_drop(t)),
            TyKind::Array(e, _) | TyKind::Slice(e) => self.needs_drop(e),
            TyKind::Pat(..) => false,
            TyKind::Adt(d, args) => {
                if let Some(drop) = self.tcx.lang_item("drop")
                    && !self.tcx.trait_impls(drop).iter().all(|&i| {
                        hyprc_ty::collect::simplify(self.tcx.type_of(i))
                            != Some(hyprc_ty::collect::SimplifiedType::Adt(d))
                    })
                {
                    return true;
                }
                let adt = self.tcx.adt_def(d);
                if adt.is_manually_drop || adt.is_union() {
                    return false;
                }
                adt.variants.iter().any(|v| {
                    v.fields.iter().any(|f| {
                        self.needs_drop(hyprc_mir::normalize_erasing(self.tcx, f.ty.subst(args)))
                    })
                })
            }
            TyKind::Closure(_, args) => hyprc_ty::traits::closure_upvars_from_args(args)
                .unwrap_or_default()
                .iter()
                .any(|&t| self.needs_drop(t)),
            _ => true,
        }
    }
}

/// The result of code generation: an object file's bytes.
pub struct CodegenOutput {
    pub object: Vec<u8>,
    pub errors: Vec<String>,
}

/// Compiles every instance (on all cores) and writes one object.
pub fn codegen(
    cx: &CodegenCx<'_, '_>,
    instances: &[Instance],
    statics: &[DefId],
    c_main: Option<Instance>,
) -> CodegenOutput {
    use rayon::prelude::*;
    let compile_all =
        |list: &[Instance]| -> Vec<Result<x86_64::func::CompiledFn, (Instance, String)>> {
            list.par_iter()
                .filter(|i| cx.mcx.has_body(**i))
                .map(|&inst| {
                    let body = cx
                        .mcx
                        .instance_mir(inst)
                        .ok_or((inst, "no body".to_string()))?;
                    x86_64::func::FnGen::new(cx, inst, body)
                        .compile()
                        .map_err(|e| (inst, e))
                })
                .collect()
        };
    let mut compiled = compile_all(instances);
    // Functions code generation asked for (and what they need), until nothing is new.
    let mut done: rustc_hash::FxHashSet<Instance> = instances.iter().copied().collect();
    loop {
        let requested: Vec<Instance> = std::mem::take(&mut *cx.requested.lock().unwrap())
            .into_iter()
            .filter(|i| done.insert(*i))
            .collect();
        if requested.is_empty() {
            break;
        }
        let (more, _) = cx.mcx.collect(requested);
        let more: Vec<Instance> = more
            .into_iter()
            .filter(|i| done.insert(*i) || true)
            .collect();
        compiled.extend(compile_all(&more));
    }
    let mut obj = Object {
        text_align: 16,
        data_align: 16,
        rodata_align: 16,
        ..Object::default()
    };
    let mut errors = Vec::new();
    let mut defined: FxHashMap<String, ()> = FxHashMap::default();
    let mut text_relocs: Vec<Reloc> = Vec::new();
    let mut add_fn =
        |obj: &mut Object, f: x86_64::func::CompiledFn, text_relocs: &mut Vec<Reloc>| {
            while obj.text.len() % 16 != 0 {
                obj.text.push(0xCC);
            }
            let off = obj.text.len() as u64;
            obj.text.extend_from_slice(&f.code);
            for mut r in f.relocs {
                r.offset += off;
                text_relocs.push(r);
            }
            defined.insert(f.symbol.clone(), ());
            obj.symbols.push(Symbol {
                name: f.symbol,
                section: Section::Text,
                offset: off,
                size: f.code.len() as u64,
                global: f.global,
                kind: SymKind::Func,
            });
        };
    for c in compiled {
        match c {
            Ok(f) => add_fn(&mut obj, f, &mut text_relocs),
            Err((inst, e)) => {
                let what = match inst.kind {
                    InstanceKind::Item(d) => cx.tcx.def_path(d),
                    InstanceKind::Closure(c) => {
                        format!("a closure in {}", cx.tcx.def_path(c.owner))
                    }
                    _ => format!("{inst:?}"),
                };
                errors.push(format!("{what}: {e}"));
            }
        }
    }
    // `main` for C runtimes, calling the Rust `main`.
    if let Some(main) = c_main {
        let target = cx.symbol_for(main);
        let mut a = x86_64::asm::Asm::new();
        use x86_64::asm::{Reg, Size};
        a.push(Reg::Rbp);
        a.mov_rr(Size::B64, Reg::Rbp, Reg::Rsp);
        a.call_sym(&target);
        a.mov_ri(Reg::Rax, 0);
        a.pop(Reg::Rbp);
        a.ret();
        a.finish();
        add_fn(
            &mut obj,
            x86_64::func::CompiledFn {
                symbol: "main".into(),
                code: a.code,
                relocs: a.relocs,
                global: true,
            },
            &mut text_relocs,
        );
    }
    // Statics: zero-initialized unless their value is a known scalar.
    for &s in statics {
        let name = cx.static_symbol(s);
        if defined.contains_key(&name) {
            continue;
        }
        let item = cx.tcx.hir.get_item(s);
        let foreign = matches!(
            item.map(|i| &i.kind),
            Some(hir::ItemKind::Static { foreign: true, .. })
        );
        if foreign {
            continue;
        }
        let ty = cx.tcx.type_of(s);
        let Ok(l) = cx.lcx.layout_of(ty) else {
            continue;
        };
        let value = match item.map(|i| &i.kind) {
            Some(hir::ItemKind::Static { body: Some(b), .. }) => {
                cx.tcx.eval_const_body(*b, ty, Args::EMPTY).try_to_bits()
            }
            _ => None,
        };
        while obj.data.len() as u64 % l.align.max(1) != 0 {
            obj.data.push(0);
        }
        let off = obj.data.len() as u64;
        let mut bytes = vec![0u8; l.size as usize];
        if let Some(v) = value {
            let b = v.to_le_bytes();
            let n = bytes.len().min(16);
            bytes[..n].copy_from_slice(&b[..n]);
        } else if l.size > 0 {
            errors.push(format!(
                "the initial value of the static `{}` can't be evaluated by hyprc yet",
                cx.tcx.def_path(s)
            ));
        }
        obj.data.extend_from_slice(&bytes);
        defined.insert(name.clone(), ());
        obj.symbols.push(Symbol {
            name,
            section: Section::Data,
            offset: off,
            size: l.size,
            global: false,
            kind: SymKind::Object,
        });
    }
    let rodata = cx.rodata.lock().unwrap();
    obj.rodata = rodata.0.clone();
    for (name, off, size) in &rodata.2 {
        defined.insert(name.clone(), ());
        obj.symbols.push(Symbol {
            name: name.clone(),
            section: Section::Rodata,
            offset: *off,
            size: *size,
            global: false,
            kind: SymKind::Object,
        });
    }
    // Everything referenced but not defined here: undefined (the linker finds it).
    let mut undefined: Vec<String> = text_relocs
        .iter()
        .map(|r| r.symbol.clone())
        .filter(|s| !defined.contains_key(s))
        .collect();
    undefined.sort();
    undefined.dedup();
    for s in undefined {
        obj.symbols.push(Symbol {
            name: s,
            section: Section::Undef,
            offset: 0,
            size: 0,
            global: true,
            kind: SymKind::NoType,
        });
    }
    obj.relocs = text_relocs
        .into_iter()
        .map(|r| (Section::Text, r))
        .collect();
    let _ = RelocKind::Abs64;
    CodegenOutput {
        object: obj.write(),
        errors,
    }
}
