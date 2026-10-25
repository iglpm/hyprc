//! Definitions and what names resolve to.

use hyprc_span::{Span, Symbol};
use std::fmt;

/// A definition: an item, an associated item, a variant, a macro, a block scope. One table
/// per session; crates loaded from metadata append to it.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct DefId(pub u32);

impl fmt::Debug for DefId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "d{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct CrateNum(pub u32);

impl CrateNum {
    pub const LOCAL: CrateNum = CrateNum(0);
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CtorOf {
    Struct,
    Variant,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CtorKind {
    /// `S(..)`: a function.
    Fn,
    /// `S`: a constant.
    Const,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MacroKind {
    Bang,
    Attr,
    Derive,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum DefKind {
    /// A crate root or `mod`.
    Mod,
    Struct,
    Union,
    Enum,
    Variant,
    Trait,
    TraitAlias,
    TyAlias,
    ForeignTy,
    Fn,
    Const,
    Static {
        mutable: bool,
    },
    /// The constructor of a tuple or unit struct or variant (same `DefId` as the struct or
    /// variant).
    Ctor(CtorOf, CtorKind),
    AssocFn,
    AssocConst,
    AssocTy,
    Macro(MacroKind),
    ExternCrate,
    Use,
    ForeignMod,
    Impl {
        of_trait: bool,
    },
    GlobalAsm,
    /// An anonymous scope for the items inside a block.
    Block,
}

impl DefKind {
    pub fn descr(self) -> &'static str {
        match self {
            DefKind::Mod => "module",
            DefKind::Struct => "struct",
            DefKind::Union => "union",
            DefKind::Enum => "enum",
            DefKind::Variant => "variant",
            DefKind::Trait => "trait",
            DefKind::TraitAlias => "trait alias",
            DefKind::TyAlias => "type alias",
            DefKind::ForeignTy => "foreign type",
            DefKind::Fn => "function",
            DefKind::Const => "constant",
            DefKind::Static { .. } => "static",
            DefKind::Ctor(CtorOf::Struct, _) => "struct constructor",
            DefKind::Ctor(CtorOf::Variant, _) => "variant constructor",
            DefKind::AssocFn => "associated function",
            DefKind::AssocConst => "associated constant",
            DefKind::AssocTy => "associated type",
            DefKind::Macro(_) => "macro",
            DefKind::ExternCrate => "extern crate",
            DefKind::Use => "import",
            DefKind::ForeignMod => "foreign module",
            DefKind::Impl { .. } => "implementation",
            DefKind::GlobalAsm => "global assembly",
            DefKind::Block => "block",
        }
    }

    /// Kinds that act as modules in paths: `m::x`, `Enum::Variant`, `Trait::item`.
    pub fn is_module_like(self) -> bool {
        matches!(
            self,
            DefKind::Mod | DefKind::Enum | DefKind::Trait | DefKind::Block
        )
    }
}

/// The three namespaces: types (and modules), values, macros.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum Ns {
    Type,
    Value,
    Macro,
}

pub const ALL_NS: [Ns; 3] = [Ns::Type, Ns::Value, Ns::Macro];

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PrimTy {
    Bool,
    Char,
    Str,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum IntTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum UintTy {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub enum FloatTy {
    F16,
    F32,
    F64,
    F128,
}

impl PrimTy {
    pub fn from_name(name: Symbol) -> Option<PrimTy> {
        use hyprc_span::sym;
        Some(match name {
            n if n == sym::bool => PrimTy::Bool,
            n if n == sym::char => PrimTy::Char,
            n if n == sym::str => PrimTy::Str,
            n if n == sym::isize => PrimTy::Int(IntTy::Isize),
            n if n == sym::i8 => PrimTy::Int(IntTy::I8),
            n if n == sym::i16 => PrimTy::Int(IntTy::I16),
            n if n == sym::i32 => PrimTy::Int(IntTy::I32),
            n if n == sym::i64 => PrimTy::Int(IntTy::I64),
            n if n == sym::i128 => PrimTy::Int(IntTy::I128),
            n if n == sym::usize => PrimTy::Uint(UintTy::Usize),
            n if n == sym::u8 => PrimTy::Uint(UintTy::U8),
            n if n == sym::u16 => PrimTy::Uint(UintTy::U16),
            n if n == sym::u32 => PrimTy::Uint(UintTy::U32),
            n if n == sym::u64 => PrimTy::Uint(UintTy::U64),
            n if n == sym::u128 => PrimTy::Uint(UintTy::U128),
            n if n == sym::f16 => PrimTy::Float(FloatTy::F16),
            n if n == sym::f32 => PrimTy::Float(FloatTy::F32),
            n if n == sym::f64 => PrimTy::Float(FloatTy::F64),
            n if n == sym::f128 => PrimTy::Float(FloatTy::F128),
            _ => return None,
        })
    }

    pub fn name(self) -> &'static str {
        match self {
            PrimTy::Bool => "bool",
            PrimTy::Char => "char",
            PrimTy::Str => "str",
            PrimTy::Int(IntTy::Isize) => "isize",
            PrimTy::Int(IntTy::I8) => "i8",
            PrimTy::Int(IntTy::I16) => "i16",
            PrimTy::Int(IntTy::I32) => "i32",
            PrimTy::Int(IntTy::I64) => "i64",
            PrimTy::Int(IntTy::I128) => "i128",
            PrimTy::Uint(UintTy::Usize) => "usize",
            PrimTy::Uint(UintTy::U8) => "u8",
            PrimTy::Uint(UintTy::U16) => "u16",
            PrimTy::Uint(UintTy::U32) => "u32",
            PrimTy::Uint(UintTy::U64) => "u64",
            PrimTy::Uint(UintTy::U128) => "u128",
            PrimTy::Float(FloatTy::F16) => "f16",
            PrimTy::Float(FloatTy::F32) => "f32",
            PrimTy::Float(FloatTy::F64) => "f64",
            PrimTy::Float(FloatTy::F128) => "f128",
        }
    }
}

/// What a name resolves to.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Res {
    Def(DefKind, DefId),
    PrimTy(PrimTy),
    /// `Self` in a trait: the trait's implicit type parameter.
    SelfTyParam {
        trait_: DefId,
    },
    /// `Self` in an impl or a type definition: the type itself.
    SelfTyAlias {
        alias_to: DefId,
    },
    /// `Self(..)` / `Self` as a constructor in an impl of a tuple or unit struct: the impl.
    SelfCtor(DefId),
    /// A generic type or const parameter: its owner and its index in the owner's generics
    /// (counting the parents' parameters first).
    TyParam {
        owner: DefId,
        index: u32,
    },
    ConstParam {
        owner: DefId,
        index: u32,
    },
    /// A local variable, by binding id within its body.
    Local(u32),
    /// `rustfmt`, `clippy`, …: tool attribute namespaces.
    ToolMod,
    /// An attribute the compiler handles itself (`inline`, `repr`, …).
    NonMacroAttr,
    Err,
}

impl Res {
    pub fn def_id(self) -> Option<DefId> {
        match self {
            Res::Def(_, d) => Some(d),
            _ => None,
        }
    }

    pub fn ns(self) -> Option<Ns> {
        Some(match self {
            Res::Def(kind, _) => match kind {
                DefKind::Mod
                | DefKind::Struct
                | DefKind::Union
                | DefKind::Enum
                | DefKind::Variant
                | DefKind::Trait
                | DefKind::TraitAlias
                | DefKind::TyAlias
                | DefKind::ForeignTy
                | DefKind::AssocTy
                | DefKind::ExternCrate
                | DefKind::Block => Ns::Type,
                DefKind::Fn
                | DefKind::Const
                | DefKind::Static { .. }
                | DefKind::Ctor(..)
                | DefKind::AssocFn
                | DefKind::AssocConst => Ns::Value,
                DefKind::Macro(_) => Ns::Macro,
                _ => return None,
            },
            Res::PrimTy(_)
            | Res::SelfTyParam { .. }
            | Res::SelfTyAlias { .. }
            | Res::TyParam { .. }
            | Res::ToolMod => Ns::Type,
            Res::SelfCtor(_) | Res::Local(_) | Res::ConstParam { .. } => Ns::Value,
            Res::NonMacroAttr => Ns::Macro,
            Res::Err => return None,
        })
    }

    pub fn descr(self) -> &'static str {
        match self {
            Res::Def(kind, _) => kind.descr(),
            Res::PrimTy(_) => "builtin type",
            Res::SelfTyParam { .. } | Res::SelfTyAlias { .. } => "self type",
            Res::SelfCtor(_) => "self constructor",
            Res::TyParam { .. } => "type parameter",
            Res::ConstParam { .. } => "const parameter",
            Res::Local(_) => "local variable",
            Res::ToolMod => "tool module",
            Res::NonMacroAttr => "built-in attribute",
            Res::Err => "unresolved item",
        }
    }
}

/// A resolved visibility.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Vis {
    Public,
    /// Visible in this module and its descendants.
    Restricted(DefId),
}

pub struct DefData {
    pub kind: DefKind,
    pub krate: CrateNum,
    /// The enclosing definition: the module for items, the impl/trait for associated items,
    /// the enum for variants, the enclosing item (or block) for items in bodies.
    pub parent: Option<DefId>,
    pub name: Symbol,
    pub span: Span,
    pub vis: Vis,
}
