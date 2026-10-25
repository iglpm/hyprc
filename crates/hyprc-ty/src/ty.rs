//! Semantic types.
//!
//! A [`Ty`] is a `u32` into a process-wide interner: equal types are equal ids, so comparing
//! and hashing types costs nothing, and types are `Copy` and usable from any thread. Lists
//! (tuple fields, generic arguments) are interned the same way. Lifetimes are erased: hyprc
//! doesn't borrow-check, and generated code doesn't depend on them.

use crate::intern::Interner;
use hyprc_hir::{DefId, FloatTy, IntTy, Mutability, UintTy};
use hyprc_span::Symbol;
use std::fmt;
use std::sync::OnceLock;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct TyList(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Args(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Const(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct PredList(u32);

/// A closure, `async` block or coroutine: the body it's in and its index there.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct ClosureRef {
    pub owner: DefId,
    pub body: u32,
    pub index: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum InferTy {
    TyVar(u32),
    IntVar(u32),
    FloatVar(u32),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AliasKind {
    /// `<T as Trait>::Assoc`
    Projection,
    /// `impl Trait` in return position.
    Opaque,
    /// `Type::Assoc` from an inherent impl.
    Inherent,
}

/// An alias: `def` is the associated type (or the function owning an opaque type), `args`
/// its generic arguments (for projections, the trait's arguments with `Self` first, then
/// the associated type's own).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct AliasTy {
    pub def: DefId,
    pub args: Args,
    /// For opaque types: which `impl Trait` of the function.
    pub index: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Abi {
    Rust,
    C,
    RustCall,
    RustIntrinsic,
    System,
    Unadjusted,
    Other(Symbol),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct FnSig {
    /// Parameters followed by the return type.
    pub inputs_and_output: TyList,
    pub c_variadic: bool,
    pub unsafe_: bool,
    pub abi: Abi,
}

impl FnSig {
    pub fn inputs(&self) -> &'static [Ty] {
        let all = self.inputs_and_output.as_slice();
        &all[..all.len() - 1]
    }

    pub fn output(&self) -> Ty {
        *self.inputs_and_output.as_slice().last().unwrap()
    }

    pub fn new(inputs: &[Ty], output: Ty, c_variadic: bool, unsafe_: bool, abi: Abi) -> FnSig {
        let mut v = inputs.to_vec();
        v.push(output);
        FnSig {
            inputs_and_output: TyList::new(&v),
            c_variadic,
            unsafe_,
            abi,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ExistentialPredicate {
    /// `dyn Trait<Args>`: the trait's arguments without `Self`.
    Trait { def: DefId, args: Args },
    /// `dyn Trait<Assoc = T>`
    Projection { def: DefId, args: Args, term: Ty },
    /// `+ Send`
    AutoTrait(DefId),
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TyKind {
    Bool,
    Char,
    Int(IntTy),
    Uint(UintTy),
    Float(FloatTy),
    Str,
    Never,
    Adt(DefId, Args),
    Foreign(DefId),
    Array(Ty, Const),
    Slice(Ty),
    RawPtr(Ty, Mutability),
    Ref(Ty, Mutability),
    FnDef(DefId, Args),
    FnPtr(FnSig),
    Dynamic(PredList),
    Closure(ClosureRef, Args),
    Coroutine(ClosureRef, Args),
    Tuple(TyList),
    Alias(AliasKind, AliasTy),
    Param(u32, Symbol),
    Infer(InferTy),
    Error,
    /// A pattern type (`u32 is 1..`, `*const T is !null`): the base type with only the
    /// values in a (wrapping) range valid; the rest are niches.
    Pat(Ty, PatRange),
}

/// The valid values of a pattern type: `start..=end` as bits of the base type, wrapping
/// around when `start > end` (as layouts describe scalars).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct PatRange {
    pub start: u128,
    pub end: u128,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum GenericArg {
    Ty(Ty),
    Const(Const),
}

impl GenericArg {
    pub fn expect_ty(self) -> Ty {
        match self {
            GenericArg::Ty(t) => t,
            GenericArg::Const(_) => panic!("expected a type argument"),
        }
    }

    pub fn as_ty(self) -> Option<Ty> {
        match self {
            GenericArg::Ty(t) => Some(t),
            GenericArg::Const(_) => None,
        }
    }

    pub fn as_const(self) -> Option<Const> {
        match self {
            GenericArg::Const(c) => Some(c),
            GenericArg::Ty(_) => None,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum ConstKind {
    /// A value: integers, `bool`, `char` as bits (sign-extended for signed types).
    Value(u128),
    Param(u32, Symbol),
    Infer(u32),
    /// A constant expression not evaluated yet: an anonymous const body (by index) or a
    /// named const item, with generic arguments.
    Unevaluated {
        def: DefId,
        body: u32,
        args: Args,
    },
    Error,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ConstData {
    pub ty: Ty,
    pub kind: ConstKind,
}

/// Flags summarizing what a type contains, computed when it is interned.
pub mod flags {
    pub const HAS_PARAMS: u8 = 1;
    pub const HAS_INFER: u8 = 2;
    pub const HAS_ALIAS: u8 = 4;
    pub const HAS_ERROR: u8 = 8;
    pub const HAS_TY_VAR: u8 = 16;
}

/// An interned type: its kind and flags (equality and hashing look at the kind only).
#[derive(Clone, Copy, Debug)]
pub struct TyData {
    pub kind: TyKind,
    pub flags: u8,
}

impl PartialEq for TyData {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for TyData {}

impl std::hash::Hash for TyData {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.kind.hash(state)
    }
}

fn compute_flags(kind: &TyKind) -> u8 {
    use flags::*;
    let mut f = 0u8;
    let args_flags = |args: Args| -> u8 {
        let mut f = 0;
        for a in args.as_slice() {
            f |= match *a {
                GenericArg::Ty(t) => t.flags(),
                GenericArg::Const(c) => c.flags(),
            };
        }
        f
    };
    match *kind {
        TyKind::Param(..) => f |= HAS_PARAMS,
        TyKind::Infer(InferTy::TyVar(_)) => f |= HAS_INFER | HAS_TY_VAR,
        TyKind::Infer(_) => f |= HAS_INFER,
        TyKind::Error => f |= HAS_ERROR,
        TyKind::Alias(_, a) => f |= HAS_ALIAS | args_flags(a.args),
        TyKind::Adt(_, args)
        | TyKind::FnDef(_, args)
        | TyKind::Closure(_, args)
        | TyKind::Coroutine(_, args) => f |= args_flags(args),
        TyKind::Array(t, c) => f |= t.flags() | c.flags(),
        TyKind::Slice(t) | TyKind::RawPtr(t, _) | TyKind::Ref(t, _) | TyKind::Pat(t, _) => {
            f |= t.flags()
        }
        TyKind::FnPtr(sig) => {
            for &t in sig.inputs_and_output.as_slice() {
                f |= t.flags();
            }
        }
        TyKind::Tuple(ts) => {
            for &t in ts.as_slice() {
                f |= t.flags();
            }
        }
        TyKind::Dynamic(preds) => {
            for p in preds.as_slice() {
                match *p {
                    ExistentialPredicate::Trait { args, .. } => f |= args_flags(args),
                    ExistentialPredicate::Projection { args, term, .. } => {
                        f |= args_flags(args) | term.flags()
                    }
                    ExistentialPredicate::AutoTrait(_) => {}
                }
            }
        }
        _ => {}
    }
    f
}

struct Interners {
    tys: Interner<TyData>,
    ty_lists: Interner<Box<[Ty]>>,
    args: Interner<Box<[GenericArg]>>,
    consts: Interner<ConstData>,
    preds: Interner<Box<[ExistentialPredicate]>>,
}

fn interners() -> &'static Interners {
    static I: OnceLock<Interners> = OnceLock::new();
    I.get_or_init(|| {
        let i = Interners {
            tys: Interner::new(),
            ty_lists: Interner::new(),
            args: Interner::new(),
            consts: Interner::new(),
            preds: Interner::new(),
        };
        // Common types get fixed ids (see the constants on `Ty`), in this order.
        for k in COMMON {
            i.tys.intern(TyData {
                kind: k,
                flags: if k == TyKind::Error {
                    flags::HAS_ERROR
                } else {
                    0
                },
            });
        }
        i.ty_lists.intern(Box::new([]));
        i.args.intern(Box::new([]));
        i
    })
}

const COMMON: [TyKind; 22] = [
    TyKind::Bool,
    TyKind::Char,
    TyKind::Str,
    TyKind::Never,
    TyKind::Error,
    TyKind::Tuple(TyList(0)),
    TyKind::Int(IntTy::Isize),
    TyKind::Int(IntTy::I8),
    TyKind::Int(IntTy::I16),
    TyKind::Int(IntTy::I32),
    TyKind::Int(IntTy::I64),
    TyKind::Int(IntTy::I128),
    TyKind::Uint(UintTy::Usize),
    TyKind::Uint(UintTy::U8),
    TyKind::Uint(UintTy::U16),
    TyKind::Uint(UintTy::U32),
    TyKind::Uint(UintTy::U64),
    TyKind::Uint(UintTy::U128),
    TyKind::Float(FloatTy::F16),
    TyKind::Float(FloatTy::F32),
    TyKind::Float(FloatTy::F64),
    TyKind::Float(FloatTy::F128),
];

impl Ty {
    pub const BOOL: Ty = Ty(0);
    pub const CHAR: Ty = Ty(1);
    pub const STR: Ty = Ty(2);
    pub const NEVER: Ty = Ty(3);
    pub const ERROR: Ty = Ty(4);
    pub const UNIT: Ty = Ty(5);
    pub const ISIZE: Ty = Ty(6);
    pub const I8: Ty = Ty(7);
    pub const I16: Ty = Ty(8);
    pub const I32: Ty = Ty(9);
    pub const I64: Ty = Ty(10);
    pub const I128: Ty = Ty(11);
    pub const USIZE: Ty = Ty(12);
    pub const U8: Ty = Ty(13);
    pub const U16: Ty = Ty(14);
    pub const U32: Ty = Ty(15);
    pub const U64: Ty = Ty(16);
    pub const U128: Ty = Ty(17);
    pub const F16: Ty = Ty(18);
    pub const F32: Ty = Ty(19);
    pub const F64: Ty = Ty(20);
    pub const F128: Ty = Ty(21);

    pub fn new(kind: TyKind) -> Ty {
        let flags = compute_flags(&kind);
        Ty(interners().tys.intern(TyData { kind, flags }))
    }

    #[inline]
    pub fn kind(self) -> &'static TyKind {
        &interners().tys.get(self.0).kind
    }

    #[inline]
    pub fn flags(self) -> u8 {
        interners().tys.get(self.0).flags
    }

    pub fn as_u32(self) -> u32 {
        self.0
    }

    pub fn int(t: IntTy) -> Ty {
        match t {
            IntTy::Isize => Ty::ISIZE,
            IntTy::I8 => Ty::I8,
            IntTy::I16 => Ty::I16,
            IntTy::I32 => Ty::I32,
            IntTy::I64 => Ty::I64,
            IntTy::I128 => Ty::I128,
        }
    }

    pub fn uint(t: UintTy) -> Ty {
        match t {
            UintTy::Usize => Ty::USIZE,
            UintTy::U8 => Ty::U8,
            UintTy::U16 => Ty::U16,
            UintTy::U32 => Ty::U32,
            UintTy::U64 => Ty::U64,
            UintTy::U128 => Ty::U128,
        }
    }

    pub fn float(t: FloatTy) -> Ty {
        match t {
            FloatTy::F16 => Ty::F16,
            FloatTy::F32 => Ty::F32,
            FloatTy::F64 => Ty::F64,
            FloatTy::F128 => Ty::F128,
        }
    }

    pub fn tuple(tys: &[Ty]) -> Ty {
        if tys.is_empty() {
            return Ty::UNIT;
        }
        Ty::new(TyKind::Tuple(TyList::new(tys)))
    }

    pub fn reference(inner: Ty, m: Mutability) -> Ty {
        Ty::new(TyKind::Ref(inner, m))
    }

    pub fn ptr(inner: Ty, m: Mutability) -> Ty {
        Ty::new(TyKind::RawPtr(inner, m))
    }

    pub fn slice(elem: Ty) -> Ty {
        Ty::new(TyKind::Slice(elem))
    }

    pub fn array(elem: Ty, len: Const) -> Ty {
        Ty::new(TyKind::Array(elem, len))
    }

    pub fn adt(def: DefId, args: Args) -> Ty {
        Ty::new(TyKind::Adt(def, args))
    }

    pub fn param(index: u32, name: Symbol) -> Ty {
        Ty::new(TyKind::Param(index, name))
    }

    pub fn var(v: u32) -> Ty {
        Ty::new(TyKind::Infer(InferTy::TyVar(v)))
    }

    pub fn fn_def(def: DefId, args: Args) -> Ty {
        Ty::new(TyKind::FnDef(def, args))
    }

    pub fn fn_ptr(sig: FnSig) -> Ty {
        Ty::new(TyKind::FnPtr(sig))
    }

    pub fn is_unit(self) -> bool {
        self == Ty::UNIT
    }

    pub fn is_never(self) -> bool {
        self == Ty::NEVER
    }

    pub fn is_error(self) -> bool {
        self == Ty::ERROR
    }

    pub fn is_integral(self) -> bool {
        matches!(
            self.kind(),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Infer(InferTy::IntVar(_))
        )
    }

    pub fn is_float(self) -> bool {
        matches!(
            self.kind(),
            TyKind::Float(_) | TyKind::Infer(InferTy::FloatVar(_))
        )
    }

    pub fn is_numeric(self) -> bool {
        self.is_integral() || self.is_float()
    }

    pub fn is_signed(self) -> bool {
        matches!(self.kind(), TyKind::Int(_))
    }

    pub fn is_scalar(self) -> bool {
        matches!(
            self.kind(),
            TyKind::Bool
                | TyKind::Char
                | TyKind::Int(_)
                | TyKind::Uint(_)
                | TyKind::Float(_)
                | TyKind::RawPtr(..)
                | TyKind::FnPtr(_)
                | TyKind::FnDef(..)
        )
    }

    pub fn is_ty_var(self) -> bool {
        matches!(self.kind(), TyKind::Infer(InferTy::TyVar(_)))
    }

    pub fn is_infer(self) -> bool {
        matches!(self.kind(), TyKind::Infer(_))
    }

    /// Does this type mention inference variables?
    #[inline]
    pub fn has_infer(self) -> bool {
        self.flags() & flags::HAS_INFER != 0
    }

    #[inline]
    pub fn has_params(self) -> bool {
        self.flags() & flags::HAS_PARAMS != 0
    }

    #[inline]
    pub fn has_errors(self) -> bool {
        self.flags() & flags::HAS_ERROR != 0
    }

    #[inline]
    pub fn has_aliases(self) -> bool {
        self.flags() & flags::HAS_ALIAS != 0
    }

    /// Visits this type and every type in it.
    pub fn walk(self, f: &mut dyn FnMut(Ty)) {
        f(self);
        match *self.kind() {
            TyKind::Adt(_, args)
            | TyKind::FnDef(_, args)
            | TyKind::Closure(_, args)
            | TyKind::Coroutine(_, args) => args.walk_tys(f),
            TyKind::Alias(_, a) => a.args.walk_tys(f),
            TyKind::Array(t, c) => {
                t.walk(f);
                c.walk_tys(f);
            }
            TyKind::Slice(t) | TyKind::RawPtr(t, _) | TyKind::Ref(t, _) => t.walk(f),
            TyKind::FnPtr(sig) => {
                for &t in sig.inputs_and_output.as_slice() {
                    t.walk(f);
                }
            }
            TyKind::Tuple(ts) => {
                for &t in ts.as_slice() {
                    t.walk(f);
                }
            }
            TyKind::Dynamic(preds) => {
                for p in preds.as_slice() {
                    match *p {
                        ExistentialPredicate::Trait { args, .. } => args.walk_tys(f),
                        ExistentialPredicate::Projection { args, term, .. } => {
                            args.walk_tys(f);
                            term.walk(f);
                        }
                        ExistentialPredicate::AutoTrait(_) => {}
                    }
                }
            }
            _ => {}
        }
    }

    pub fn tuple_fields(self) -> &'static [Ty] {
        match self.kind() {
            TyKind::Tuple(ts) => ts.as_slice(),
            _ => &[],
        }
    }

    /// `&T`, `&mut T`, `*const T`, `*mut T`: the pointee.
    pub fn builtin_deref(self, include_raw: bool) -> Option<(Ty, Mutability)> {
        match *self.kind() {
            TyKind::Ref(t, m) => Some((t, m)),
            TyKind::RawPtr(t, m) if include_raw => Some((t, m)),
            _ => None,
        }
    }

    /// `[T; N]` and `[T]`: the element type.
    pub fn builtin_index(self) -> Option<Ty> {
        match *self.kind() {
            TyKind::Array(t, _) | TyKind::Slice(t) => Some(t),
            TyKind::Str => Some(Ty::U8),
            _ => None,
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::print::ty_to_string(*self))
    }
}

impl fmt::Display for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::print::ty_to_string(*self))
    }
}

impl TyList {
    pub const EMPTY: TyList = TyList(0);

    pub fn new(tys: &[Ty]) -> TyList {
        if tys.is_empty() {
            return TyList::EMPTY;
        }
        TyList(interners().ty_lists.intern(tys.into()))
    }

    #[inline]
    pub fn as_slice(self) -> &'static [Ty] {
        interners().ty_lists.get(self.0)
    }
}

impl Args {
    pub const EMPTY: Args = Args(0);

    pub fn new(args: &[GenericArg]) -> Args {
        if args.is_empty() {
            return Args::EMPTY;
        }
        Args(interners().args.intern(args.into()))
    }

    pub fn from_tys(tys: &[Ty]) -> Args {
        let v: Vec<GenericArg> = tys.iter().map(|&t| GenericArg::Ty(t)).collect();
        Args::new(&v)
    }

    #[inline]
    pub fn as_slice(self) -> &'static [GenericArg] {
        interners().args.get(self.0)
    }

    pub fn len(self) -> usize {
        self.as_slice().len()
    }

    pub fn is_empty(self) -> bool {
        self.as_slice().is_empty()
    }

    pub fn ty(self, i: usize) -> Ty {
        self.as_slice()[i].expect_ty()
    }

    pub fn get(self, i: usize) -> Option<GenericArg> {
        self.as_slice().get(i).copied()
    }

    pub fn walk_tys(self, f: &mut dyn FnMut(Ty)) {
        for a in self.as_slice() {
            match *a {
                GenericArg::Ty(t) => t.walk(f),
                GenericArg::Const(c) => c.walk_tys(f),
            }
        }
    }

    /// The first `n` arguments.
    pub fn truncate(self, n: usize) -> Args {
        let s = self.as_slice();
        Args::new(&s[..n.min(s.len())])
    }

    /// These arguments followed by more.
    pub fn extend(self, more: &[GenericArg]) -> Args {
        let mut v = self.as_slice().to_vec();
        v.extend_from_slice(more);
        Args::new(&v)
    }

    pub fn flags(self) -> u8 {
        let mut f = 0;
        for a in self.as_slice() {
            f |= match *a {
                GenericArg::Ty(t) => t.flags(),
                GenericArg::Const(c) => c.flags(),
            };
        }
        f
    }

    pub fn has_infer(self) -> bool {
        self.flags() & flags::HAS_INFER != 0
    }

    pub fn has_params(self) -> bool {
        self.flags() & flags::HAS_PARAMS != 0
    }
}

impl Const {
    pub fn new(ty: Ty, kind: ConstKind) -> Const {
        Const(interners().consts.intern(ConstData { ty, kind }))
    }

    pub fn from_usize(v: u64) -> Const {
        Const::new(Ty::USIZE, ConstKind::Value(v as u128))
    }

    pub fn from_bool(v: bool) -> Const {
        Const::new(Ty::BOOL, ConstKind::Value(v as u128))
    }

    pub fn error(ty: Ty) -> Const {
        Const::new(ty, ConstKind::Error)
    }

    #[inline]
    pub fn data(self) -> &'static ConstData {
        interners().consts.get(self.0)
    }

    pub fn kind(self) -> ConstKind {
        self.data().kind
    }

    pub fn ty(self) -> Ty {
        self.data().ty
    }

    pub fn try_to_bits(self) -> Option<u128> {
        match self.kind() {
            ConstKind::Value(v) => Some(v),
            _ => None,
        }
    }

    pub fn try_to_usize(self) -> Option<u64> {
        self.try_to_bits().map(|v| v as u64)
    }

    pub fn walk_tys(self, f: &mut dyn FnMut(Ty)) {
        f(self.ty());
        if let ConstKind::Unevaluated { args, .. } = self.kind() {
            args.walk_tys(f);
        }
    }

    pub fn flags(self) -> u8 {
        let f = match self.kind() {
            ConstKind::Param(..) => flags::HAS_PARAMS,
            ConstKind::Infer(_) => flags::HAS_INFER,
            ConstKind::Error => flags::HAS_ERROR,
            ConstKind::Unevaluated { args, .. } => args.flags(),
            ConstKind::Value(_) => 0,
        };
        f | self.ty().flags()
    }
}

impl fmt::Debug for Const {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", crate::print::const_to_string(*self))
    }
}

impl PredList {
    pub fn new(preds: &[ExistentialPredicate]) -> PredList {
        PredList(interners().preds.intern(preds.into()))
    }

    pub fn as_slice(self) -> &'static [ExistentialPredicate] {
        interners().preds.get(self.0)
    }

    /// The principal trait of a `dyn` type.
    pub fn principal(self) -> Option<(DefId, Args)> {
        self.as_slice().iter().find_map(|p| match *p {
            ExistentialPredicate::Trait { def, args } => Some((def, args)),
            _ => None,
        })
    }
}

/// `Trait<Args>` for a type: `args[0]` is the self type.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct TraitRef {
    pub def: DefId,
    pub args: Args,
}

impl TraitRef {
    pub fn new(def: DefId, args: Args) -> TraitRef {
        TraitRef { def, args }
    }

    pub fn self_ty(self) -> Ty {
        self.args.ty(0)
    }

    pub fn has_aliases(self) -> bool {
        self.args
            .as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| t.has_aliases()))
    }
}

/// What a where-clause or an obligation says.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Predicate {
    /// `T: Trait`
    Trait(TraitRef),
    /// `T: !Trait`
    NegTrait(TraitRef),
    /// `<T as Trait>::Assoc == U`
    Projection(AliasTy, Ty),
    /// `T: ?Sized` (recorded to know `Sized` isn't implied).
    MaybeSized(Ty),
}
