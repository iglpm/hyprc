//! Printing types the way rustc's diagnostics do.

use crate::ty::*;
use hyprc_hir::{DefId, FloatTy, IntTy, Mutability, UintTy};
use std::sync::{Arc, RwLock};

type Namer = Arc<dyn Fn(DefId) -> String + Send + Sync>;

static NAMER: RwLock<Option<Namer>> = RwLock::new(None);

/// Sets how definitions are named when types are printed (the current crate's paths).
pub fn set_namer(f: Namer) {
    *NAMER.write().unwrap() = Some(f);
}

pub fn def_name(def: DefId) -> String {
    match &*NAMER.read().unwrap() {
        Some(f) => f(def),
        None => format!("{def:?}"),
    }
}

fn args_to_string(args: &[GenericArg]) -> String {
    if args.is_empty() {
        return String::new();
    }
    let parts: Vec<String> = args
        .iter()
        .map(|a| match *a {
            GenericArg::Ty(t) => ty_to_string(t),
            GenericArg::Const(c) => const_to_string(c),
        })
        .collect();
    format!("<{}>", parts.join(", "))
}

pub fn int_name(t: IntTy) -> &'static str {
    match t {
        IntTy::Isize => "isize",
        IntTy::I8 => "i8",
        IntTy::I16 => "i16",
        IntTy::I32 => "i32",
        IntTy::I64 => "i64",
        IntTy::I128 => "i128",
    }
}

pub fn uint_name(t: UintTy) -> &'static str {
    match t {
        UintTy::Usize => "usize",
        UintTy::U8 => "u8",
        UintTy::U16 => "u16",
        UintTy::U32 => "u32",
        UintTy::U64 => "u64",
        UintTy::U128 => "u128",
    }
}

pub fn float_name(t: FloatTy) -> &'static str {
    match t {
        FloatTy::F16 => "f16",
        FloatTy::F32 => "f32",
        FloatTy::F64 => "f64",
        FloatTy::F128 => "f128",
    }
}

pub fn ty_to_string(t: Ty) -> String {
    match *t.kind() {
        TyKind::Pat(base, r) => format!("({base} is {}..={})", r.start, r.end),
        TyKind::Bool => "bool".into(),
        TyKind::Char => "char".into(),
        TyKind::Int(i) => int_name(i).into(),
        TyKind::Uint(u) => uint_name(u).into(),
        TyKind::Float(f) => float_name(f).into(),
        TyKind::Str => "str".into(),
        TyKind::Never => "!".into(),
        TyKind::Adt(d, args) => format!("{}{}", def_name(d), args_to_string(args.as_slice())),
        TyKind::Foreign(d) => def_name(d),
        TyKind::Array(t, c) => format!("[{}; {}]", ty_to_string(t), const_to_string(c)),
        TyKind::Slice(t) => format!("[{}]", ty_to_string(t)),
        TyKind::RawPtr(t, m) => format!(
            "*{} {}",
            if m == Mutability::Mut { "mut" } else { "const" },
            ty_to_string(t)
        ),
        TyKind::Ref(t, m) => format!(
            "&{}{}",
            if m == Mutability::Mut { "mut " } else { "" },
            ty_to_string(t)
        ),
        TyKind::FnDef(d, args) => format!(
            "fn item {{{}{}}}",
            def_name(d),
            args_to_string(args.as_slice())
        ),
        TyKind::FnPtr(sig) => {
            let mut s = String::new();
            if sig.unsafe_ {
                s.push_str("unsafe ");
            }
            if sig.abi == Abi::C {
                s.push_str("extern \"C\" ");
            }
            let inputs: Vec<String> = sig.inputs().iter().map(|t| ty_to_string(*t)).collect();
            s.push_str(&format!("fn({}", inputs.join(", ")));
            if sig.c_variadic {
                s.push_str(", ...");
            }
            s.push(')');
            if !sig.output().is_unit() {
                s.push_str(&format!(" -> {}", ty_to_string(sig.output())));
            }
            s
        }
        TyKind::Dynamic(preds) => {
            let parts: Vec<String> = preds
                .as_slice()
                .iter()
                .filter_map(|p| match *p {
                    ExistentialPredicate::Trait { def, args } => Some(format!(
                        "{}{}",
                        def_name(def),
                        args_to_string(args.as_slice())
                    )),
                    ExistentialPredicate::AutoTrait(def) => Some(def_name(def)),
                    ExistentialPredicate::Projection { .. } => None,
                })
                .collect();
            format!("dyn {}", parts.join(" + "))
        }
        TyKind::Closure(c, _) => format!("{{closure#{}@{}}}", c.index, def_name(c.owner)),
        TyKind::Coroutine(c, _) => format!("{{coroutine#{}@{}}}", c.index, def_name(c.owner)),
        TyKind::Tuple(ts) => {
            let parts: Vec<String> = ts.as_slice().iter().map(|t| ty_to_string(*t)).collect();
            if parts.len() == 1 {
                format!("({},)", parts[0])
            } else {
                format!("({})", parts.join(", "))
            }
        }
        TyKind::Alias(AliasKind::Opaque, a) => format!("impl ?{}#{}", def_name(a.def), a.index),
        TyKind::Alias(_, a) => {
            let s = a.args.as_slice();
            match s.first() {
                Some(GenericArg::Ty(self_ty)) => format!(
                    "<{} as ?>::{}",
                    ty_to_string(*self_ty),
                    def_name(a.def).rsplit("::").next().unwrap_or("")
                ),
                _ => def_name(a.def),
            }
        }
        TyKind::Param(_, name) => name.as_str().into(),
        TyKind::Infer(InferTy::IntVar(_)) => "{integer}".into(),
        TyKind::Infer(InferTy::FloatVar(_)) => "{float}".into(),
        TyKind::Infer(InferTy::TyVar(_)) => "_".into(),
        TyKind::Error => "{type error}".into(),
    }
}

pub fn const_to_string(c: Const) -> String {
    match c.kind() {
        ConstKind::Value(v) => {
            if c.ty() == Ty::BOOL {
                (v != 0).to_string()
            } else if c.ty().is_signed() {
                (v as i128).to_string()
            } else {
                v.to_string()
            }
        }
        ConstKind::Param(_, n) => n.as_str().into(),
        ConstKind::Infer(_) => "_".into(),
        ConstKind::Unevaluated { .. } => "{const}".into(),
        ConstKind::Error => "{const error}".into(),
    }
}
