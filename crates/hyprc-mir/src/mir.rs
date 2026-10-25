//! The MIR: a function as basic blocks of simple statements over places.
//!
//! Close to rustc's MIR. Bodies are generic: types mention the item's parameters, and code
//! generation substitutes the arguments of each instance as it goes.

use hyprc_hir::{BinOpKind, DefId, Mutability};
use hyprc_span::{Span, Symbol};
use hyprc_ty::{Args, ClosureRef, Const, Ty};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Local(pub u32);

impl Local {
    /// Where the return value goes.
    pub const RETURN: Local = Local(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for Local {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "_{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct BasicBlock(pub u32);

impl BasicBlock {
    pub const START: BasicBlock = BasicBlock(0);

    pub fn index(self) -> usize {
        self.0 as usize
    }
}

impl fmt::Debug for BasicBlock {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.0)
    }
}

#[derive(Clone, Debug)]
pub struct LocalDecl {
    pub ty: Ty,
    pub mutable: bool,
    pub name: Option<Symbol>,
    pub span: Span,
}

/// What a MIR body is the code of.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum MirSource {
    /// A function, method, constant or static (by its HIR body).
    Item(DefId),
    /// A closure body (by the closure's identity).
    Closure(ClosureRef),
    /// An anonymous constant body.
    AnonConst(DefId, u32),
    /// A function the compiler provides (`Fn*` calls, built-in `Clone`), by the trait
    /// method it implements.
    Shim(DefId),
}

#[derive(Clone, Debug)]
pub struct Body {
    pub source: MirSource,
    pub locals: Vec<LocalDecl>,
    pub arg_count: usize,
    pub blocks: Vec<BasicBlockData>,
    pub span: Span,
    /// The C-variadic `...` parameter of an extern fn definition.
    pub c_variadic: bool,
}

impl Body {
    pub fn local_ty(&self, l: Local) -> Ty {
        self.locals[l.index()].ty
    }

    pub fn args(&self) -> impl Iterator<Item = Local> {
        (1..=self.arg_count as u32).map(Local)
    }
}

#[derive(Clone, Debug)]
pub struct BasicBlockData {
    pub stmts: Vec<Statement>,
    pub terminator: Option<Terminator>,
}

#[derive(Clone, Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StatementKind {
    Assign(Place, Rvalue),
    StorageLive(Local),
    StorageDead(Local),
    /// Writes an enum's discriminant (after its fields are written).
    SetDiscriminant(Place, u32),
    /// A drop flag or other bookkeeping: `local = value`.
    Nop,
}

#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Place {
    pub local: Local,
    pub projection: Vec<PlaceElem>,
}

impl Place {
    pub fn local(l: Local) -> Place {
        Place {
            local: l,
            projection: Vec::new(),
        }
    }

    pub fn ret() -> Place {
        Place::local(Local::RETURN)
    }

    pub fn project(&self, e: PlaceElem) -> Place {
        let mut p = self.clone();
        p.projection.push(e);
        p
    }

    pub fn field(&self, i: u32, ty: Ty) -> Place {
        self.project(PlaceElem::Field(i, ty))
    }

    pub fn deref(&self) -> Place {
        self.project(PlaceElem::Deref)
    }

    pub fn is_local(&self) -> bool {
        self.projection.is_empty()
    }
}

impl fmt::Debug for Place {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = format!("{:?}", self.local);
        for p in &self.projection {
            s = match p {
                PlaceElem::Deref => format!("(*{s})"),
                PlaceElem::Field(i, _) => format!("{s}.{i}"),
                PlaceElem::Index(l) => format!("{s}[{l:?}]"),
                PlaceElem::ConstantIndex {
                    offset, from_end, ..
                } => {
                    if *from_end {
                        format!("{s}[-{offset}]")
                    } else {
                        format!("{s}[{offset}]")
                    }
                }
                PlaceElem::Subslice { from, to, .. } => format!("{s}[{from}..-{to}]"),
                PlaceElem::Downcast(v) => format!("({s} as v{v})"),
            };
        }
        f.write_str(&s)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum PlaceElem {
    Deref,
    /// A field, with its type.
    Field(u32, Ty),
    /// `[i]` with a local holding a `usize`.
    Index(Local),
    /// `[n]` or `[len - n]` (slice patterns).
    ConstantIndex {
        offset: u64,
        min_length: u64,
        from_end: bool,
    },
    /// `[from..len - to]` (slice patterns); for arrays `to` counts from the start.
    Subslice {
        from: u64,
        to: u64,
        from_end: bool,
    },
    /// Viewing an enum as one of its variants (to reach its fields).
    Downcast(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitXor,
    BitAnd,
    BitOr,
    Shl,
    Shr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    /// Pointer plus count (in units of the pointee): `ptr.add(n)`.
    Offset,
    /// `Ord::cmp` on primitives: -1, 0, 1 as `i8`.
    Cmp,
}

impl BinOp {
    pub fn from_hir(op: BinOpKind) -> BinOp {
        match op {
            BinOpKind::Add => BinOp::Add,
            BinOpKind::Sub => BinOp::Sub,
            BinOpKind::Mul => BinOp::Mul,
            BinOpKind::Div => BinOp::Div,
            BinOpKind::Rem => BinOp::Rem,
            BinOpKind::BitXor => BinOp::BitXor,
            BinOpKind::BitAnd => BinOp::BitAnd,
            BinOpKind::BitOr => BinOp::BitOr,
            BinOpKind::Shl => BinOp::Shl,
            BinOpKind::Shr => BinOp::Shr,
            BinOpKind::Eq => BinOp::Eq,
            BinOpKind::Lt => BinOp::Lt,
            BinOpKind::Le => BinOp::Le,
            BinOpKind::Ne => BinOp::Ne,
            BinOpKind::Ge => BinOp::Ge,
            BinOpKind::Gt => BinOp::Gt,
            BinOpKind::And | BinOpKind::Or => unreachable!("lazy operators are control flow"),
        }
    }

    pub fn is_comparison(self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::Lt | BinOp::Le | BinOp::Ne | BinOp::Ge | BinOp::Gt
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
    /// The metadata of a wide pointer (`len` of a slice pointer).
    PtrMetadata,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CastKind {
    /// Between integers, floats, and integers and pointers; `as` on primitives.
    IntToInt,
    FloatToInt,
    IntToFloat,
    FloatToFloat,
    PtrToPtr,
    /// `*const T` → `usize`
    PtrToAddr,
    /// `usize` → `*const T`
    AddrToPtr,
    /// A function item to a function pointer.
    ReifyFnPointer,
    /// A non-capturing closure to a function pointer.
    ClosureFnPointer,
    /// `&[T; N]` → `&[T]`, `&T` → `&dyn Trait`, `Box<T>` → `Box<dyn Trait>`.
    Unsize,
    /// Reinterpret bits (same size): `transmute`.
    Transmute,
}

#[derive(Clone, Debug, PartialEq)]
pub enum AggregateKind {
    Array(Ty),
    Tuple,
    /// An ADT: the ADT, the variant index, the arguments, and for unions the field.
    Adt(DefId, u32, Args, Option<u32>),
    Closure(ClosureRef, Args),
    /// A wide pointer from a data pointer and metadata.
    RawPtr(Ty, Mutability),
}

#[derive(Clone, Debug)]
pub enum Rvalue {
    Use(Operand),
    Repeat(Operand, Const),
    Ref(Mutability, Place),
    RawPtr(Mutability, Place),
    /// The length of an array or slice place.
    Len(Place),
    Cast(CastKind, Operand, Ty),
    BinaryOp(BinOp, Operand, Operand),
    /// `(result, overflowed)`
    CheckedBinaryOp(BinOp, Operand, Operand),
    UnaryOp(UnOp, Operand),
    Discriminant(Place),
    Aggregate(AggregateKind, Vec<Operand>),
    SizeOf(Ty),
    AlignOf(Ty),
    /// `offset_of!`: a container type and the path's (variant, field, field type) steps.
    OffsetOf(Ty, Vec<(u32, u32, Ty)>),
    /// The address of a thread-local static.
    ThreadLocalRef(DefId),
    CopyForDeref(Place),
}

#[derive(Clone, Debug)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    Constant(Box<Constant>),
}

impl Operand {
    pub fn place(&self) -> Option<&Place> {
        match self {
            Operand::Copy(p) | Operand::Move(p) => Some(p),
            Operand::Constant(_) => None,
        }
    }

    pub fn constant(ty: Ty, kind: ConstValue) -> Operand {
        Operand::Constant(Box::new(Constant { ty, kind }))
    }

    pub fn unit() -> Operand {
        Operand::constant(Ty::UNIT, ConstValue::ZeroSized)
    }
}

#[derive(Clone, Debug)]
pub struct Constant {
    pub ty: Ty,
    pub kind: ConstValue,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ConstValue {
    /// An integer, `bool`, `char`, float (bits), or thin pointer value.
    Scalar(u128),
    /// A value of a zero-sized type (`()`, a function item, a unit struct).
    ZeroSized,
    /// A `&str` or `&[u8]` literal: the bytes, in read-only data.
    Bytes(std::sync::Arc<[u8]>),
    /// A reference to a static: `&STATIC` (its address).
    StaticRef(DefId),
    /// A constant item or anonymous constant evaluated at code generation.
    Unevaluated(Const),
    /// A constant item, by its definition.
    Item(DefId, Args),
}

#[derive(Clone, Debug)]
pub enum UnwindAction {
    Continue,
    Unreachable,
}

#[derive(Clone, Debug)]
pub enum AssertKind {
    BoundsCheck { len: Operand, index: Operand },
    Overflow(BinOp),
    OverflowNeg,
    DivisionByZero,
    RemainderByZero,
    MisalignedPointerDereference,
}

#[derive(Clone, Debug)]
pub struct Terminator {
    pub kind: TerminatorKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TerminatorKind {
    Goto(BasicBlock),
    SwitchInt {
        discr: Operand,
        targets: Vec<(u128, BasicBlock)>,
        otherwise: BasicBlock,
    },
    Return,
    Unreachable,
    Call {
        func: Operand,
        args: Vec<Operand>,
        destination: Place,
        target: Option<BasicBlock>,
    },
    Drop {
        place: Place,
        target: BasicBlock,
    },
    Assert {
        cond: Operand,
        expected: bool,
        msg: AssertKind,
        target: BasicBlock,
    },
    /// `asm!` with these operands; the template is kept with the body.
    InlineAsm {
        template: Symbol,
        operands: Vec<Operand>,
        destination: Option<BasicBlock>,
    },
}

impl TerminatorKind {
    pub fn successors(&self) -> Vec<BasicBlock> {
        match self {
            TerminatorKind::Goto(b) => vec![*b],
            TerminatorKind::SwitchInt {
                targets, otherwise, ..
            } => {
                let mut v: Vec<BasicBlock> = targets.iter().map(|(_, b)| *b).collect();
                v.push(*otherwise);
                v
            }
            TerminatorKind::Return | TerminatorKind::Unreachable => Vec::new(),
            TerminatorKind::Call { target, .. } => target.iter().copied().collect(),
            TerminatorKind::Drop { target, .. } | TerminatorKind::Assert { target, .. } => {
                vec![*target]
            }
            TerminatorKind::InlineAsm { destination, .. } => destination.iter().copied().collect(),
        }
    }
}
