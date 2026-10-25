//! The syntax tree, as parsed and before macro expansion.
//!
//! Close to rustc's AST on purpose: Rust's grammar is defined by what rustc accepts, and
//! keeping the same shapes makes it easy to follow rustc's parser where the reference is
//! silent. Nodes are boxed (`P<T>`); macro expansion replaces nodes in place, and the tree is
//! lowered to an arena-based form for type checking, which is where speed matters more.

use crate::token::{AttrStyle, CommentKind, Delim, LitKind, Token};
use hyprc_span::{Ident, Span, Symbol};
use std::fmt;
use std::sync::Arc;

pub type P<T> = Box<T>;

/// Identifies a node after expansion (assigned by the expander; `DUMMY` until then).
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct NodeId(pub u32);

impl NodeId {
    pub const DUMMY: NodeId = NodeId(u32::MAX);
}

impl Default for NodeId {
    fn default() -> NodeId {
        NodeId::DUMMY
    }
}

impl fmt::Debug for NodeId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if *self == NodeId::DUMMY {
            f.write_str("_")
        } else {
            write!(f, "n{}", self.0)
        }
    }
}

/// A run of tokens with balanced delimiters (macro arguments and bodies). Flat: nested groups
/// are their `Open`/`Close` tokens inline. Shared, because macro expansion copies it around.
#[derive(Clone, Default)]
pub struct TokenStream(pub Arc<[Token]>);

impl TokenStream {
    pub fn new(tokens: Vec<Token>) -> TokenStream {
        TokenStream(tokens.into())
    }

    pub fn tokens(&self) -> &[Token] {
        &self.0
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl fmt::Debug for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TokenStream(")?;
        for (i, t) in self.0.iter().enumerate() {
            if i > 0 && !self.0[i - 1].joint {
                f.write_str(" ")?;
            }
            write!(f, "{}", crate::token::token_text(t))?;
        }
        write!(f, ")")
    }
}

#[derive(Clone, Debug)]
pub struct Crate {
    pub attrs: Vec<Attribute>,
    pub items: Vec<P<Item>>,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------------
// Attributes

#[derive(Clone, Debug)]
pub struct Attribute {
    pub kind: AttrKind,
    pub style: AttrStyle,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum AttrKind {
    Normal(P<AttrItem>),
    /// `/// text`: the same as `#[doc = "text"]`.
    DocComment(CommentKind, Symbol),
}

#[derive(Clone, Debug)]
pub struct AttrItem {
    /// `#[unsafe(no_mangle)]`.
    pub unsafety: Safety,
    pub path: Path,
    pub args: AttrArgs,
}

#[derive(Clone, Debug)]
pub enum AttrArgs {
    /// `#[test]`
    Empty,
    /// `#[derive(Copy)]`, `#[cfg(unix)]`
    Delimited(DelimArgs),
    /// `#[doc = "…"]`, `#[path = "x.rs"]`, `#[doc = include_str!("README.md")]`
    Eq(Span, P<Expr>),
}

#[derive(Clone, Debug)]
pub struct DelimArgs {
    /// The span of the opening and of the closing delimiter.
    pub open: Span,
    pub close: Span,
    pub delim: Delim,
    pub tokens: TokenStream,
}

impl Attribute {
    /// The attribute's name when its path is a single segment (`cfg`, `derive`, `doc`).
    pub fn name(&self) -> Option<Symbol> {
        match &self.kind {
            AttrKind::Normal(item) if item.path.segments.len() == 1 => {
                Some(item.path.segments[0].ident.name)
            }
            AttrKind::DocComment(..) => Some(hyprc_span::sym::doc),
            _ => None,
        }
    }

    pub fn has_name(&self, name: Symbol) -> bool {
        self.name() == Some(name)
    }

    pub fn is_doc_comment(&self) -> bool {
        matches!(self.kind, AttrKind::DocComment(..))
    }
}

// ---------------------------------------------------------------------------------------------
// Paths

#[derive(Clone, Debug)]
pub struct Path {
    pub span: Span,
    /// A path starting with `::` begins with a `kw::PathRoot` segment.
    pub segments: Vec<PathSegment>,
}

impl Path {
    pub fn from_ident(ident: Ident) -> Path {
        Path {
            span: ident.span,
            segments: vec![PathSegment::from_ident(ident)],
        }
    }

    pub fn is_ident(&self, name: Symbol) -> bool {
        self.segments.len() == 1
            && self.segments[0].ident.name == name
            && self.segments[0].args.is_none()
    }
}

#[derive(Clone, Debug)]
pub struct PathSegment {
    pub ident: Ident,
    pub id: NodeId,
    pub args: Option<P<GenericArgs>>,
}

impl PathSegment {
    pub fn from_ident(ident: Ident) -> PathSegment {
        PathSegment {
            ident,
            id: NodeId::DUMMY,
            args: None,
        }
    }
}

/// `<Ty as Trait>::Assoc`: the path holds the trait's segments followed by the item's;
/// `position` is the number of segments that belong to the trait (0 for `<Ty>::Assoc`).
#[derive(Clone, Debug)]
pub struct QSelf {
    pub ty: P<Ty>,
    pub path_span: Span,
    pub position: usize,
}

#[derive(Clone, Debug)]
pub enum GenericArgs {
    /// `<A, B, C = D, E: Bound>`
    AngleBracketed {
        args: Vec<AngleBracketedArg>,
        span: Span,
    },
    /// `(A, B) -> C`
    Parenthesized {
        inputs: Vec<P<Ty>>,
        output: FnRetTy,
        span: Span,
    },
    /// `(..)`: return type notation.
    ParenthesizedElided(Span),
}

#[derive(Clone, Debug)]
pub enum AngleBracketedArg {
    Arg(GenericArg),
    Constraint(AssocItemConstraint),
}

#[derive(Clone, Debug)]
pub enum GenericArg {
    Lifetime(Lifetime),
    Type(P<Ty>),
    Const(AnonConst),
}

/// `Item = Ty`, `Item: Bound`, `Assoc<'a> = Ty`.
#[derive(Clone, Debug)]
pub struct AssocItemConstraint {
    pub id: NodeId,
    pub ident: Ident,
    pub gen_args: Option<GenericArgs>,
    pub kind: AssocItemConstraintKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum AssocItemConstraintKind {
    Equality(Term),
    Bound(GenericBounds),
}

#[derive(Clone, Debug)]
pub enum Term {
    Ty(P<Ty>),
    Const(AnonConst),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lifetime {
    pub id: NodeId,
    /// Includes the quote: `'a`, `'static`, `'_`.
    pub ident: Ident,
}

// ---------------------------------------------------------------------------------------------
// Generics

#[derive(Clone, Debug, Default)]
pub struct Generics {
    pub params: Vec<GenericParam>,
    pub where_clause: WhereClause,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct GenericParam {
    pub id: NodeId,
    pub ident: Ident,
    pub attrs: Vec<Attribute>,
    pub bounds: GenericBounds,
    pub kind: GenericParamKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum GenericParamKind {
    Lifetime,
    Type {
        default: Option<P<Ty>>,
    },
    Const {
        ty: P<Ty>,
        default: Option<AnonConst>,
    },
}

pub type GenericBounds = Vec<GenericBound>;

#[derive(Clone, Debug)]
pub enum GenericBound {
    Trait(PolyTraitRef),
    Outlives(Lifetime),
    /// `use<'a, T>`: precise capturing.
    Use(Vec<PreciseCapturingArg>, Span),
}

#[derive(Clone, Debug)]
pub enum PreciseCapturingArg {
    Lifetime(Lifetime),
    Arg(Path, NodeId),
}

/// `for<'a> const ?Trait<Args>`
#[derive(Clone, Debug)]
pub struct PolyTraitRef {
    pub bound_generic_params: Vec<GenericParam>,
    pub modifiers: TraitBoundModifiers,
    pub trait_ref: TraitRef,
    pub span: Span,
    /// Written in parentheses: `(Trait)`.
    pub parens: bool,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TraitBoundModifiers {
    pub constness: BoundConstness,
    pub asyncness: bool,
    pub polarity: BoundPolarity,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BoundConstness {
    #[default]
    Never,
    /// `const Trait`
    Always(Span),
    /// `~const Trait` or `[const] Trait`
    Maybe(Span),
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum BoundPolarity {
    #[default]
    Positive,
    /// `!Trait`
    Negative(Span),
    /// `?Trait`
    Maybe(Span),
}

#[derive(Clone, Debug)]
pub struct TraitRef {
    pub path: Path,
    pub ref_id: NodeId,
}

#[derive(Clone, Debug, Default)]
pub struct WhereClause {
    pub has_where_token: bool,
    pub predicates: Vec<WherePredicate>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct WherePredicate {
    pub attrs: Vec<Attribute>,
    pub kind: WherePredicateKind,
    pub id: NodeId,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum WherePredicateKind {
    /// `for<'a> T: Bound + 'a`
    Bound {
        bound_generic_params: Vec<GenericParam>,
        bounded_ty: P<Ty>,
        bounds: GenericBounds,
    },
    /// `'a: 'b + 'c`
    Region {
        lifetime: Lifetime,
        bounds: GenericBounds,
    },
    /// `T = U` (not accepted by rustc either; parsed to report it)
    Eq { lhs_ty: P<Ty>, rhs_ty: P<Ty> },
}

// ---------------------------------------------------------------------------------------------
// Types

#[derive(Clone, Debug)]
pub struct Ty {
    pub id: NodeId,
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Slice(P<Ty>),
    Array(P<Ty>, AnonConst),
    Ptr(MutTy),
    Ref(Option<Lifetime>, MutTy),
    /// `&pin mut T`, `&pin const T`
    PinnedRef(Option<Lifetime>, MutTy),
    BareFn(P<BareFnTy>),
    /// `unsafe<'a> &'a T`
    UnsafeBinder(P<UnsafeBinderTy>),
    Never,
    Tup(Vec<P<Ty>>),
    Path(Option<P<QSelf>>, Path),
    TraitObject(GenericBounds, TraitObjectSyntax),
    ImplTrait(NodeId, GenericBounds),
    Paren(P<Ty>),
    Typeof(AnonConst),
    /// `_`
    Infer,
    /// The `Self` of `self`, `&self`, `&mut self`.
    ImplicitSelf,
    MacCall(P<MacCall>),
    /// `...` at the end of a C-variadic function's parameters.
    CVarArgs,
    /// `u32 is 1..` (pattern types)
    Pat(P<Ty>, P<TyPat>),
    /// A type made of the tokens a macro substituted for `$t:ty`, not yet reparsed.
    Err,
    /// `_` as the field type of an unnamed struct or union field: `_: struct { … }`.
    AnonStruct(NodeId, Vec<FieldDef>),
    AnonUnion(NodeId, Vec<FieldDef>),
}

#[derive(Clone, Debug)]
pub struct TyPat {
    pub id: NodeId,
    pub kind: TyPatKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TyPatKind {
    Range(Option<P<AnonConst>>, Option<P<AnonConst>>, RangeEnd),
    /// `!null` (pointers)
    NotNull,
    Or(Vec<P<TyPat>>),
    Err,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TraitObjectSyntax {
    Dyn,
    /// `dyn* Trait`
    DynStar,
    /// A bare trait in type position (2015 edition).
    None,
}

#[derive(Clone, Debug)]
pub struct MutTy {
    pub ty: P<Ty>,
    pub mutbl: Mutability,
}

#[derive(Clone, Debug)]
pub struct BareFnTy {
    pub safety: Safety,
    pub ext: Extern,
    pub generic_params: Vec<GenericParam>,
    pub decl: P<FnDecl>,
    pub decl_span: Span,
}

#[derive(Clone, Debug)]
pub struct UnsafeBinderTy {
    pub generic_params: Vec<GenericParam>,
    pub inner_ty: P<Ty>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Mutability {
    Not,
    Mut,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Safety {
    Default,
    Unsafe(Span),
    /// `safe fn` in an `unsafe extern` block.
    Safe(Span),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Constness {
    Yes(Span),
    No,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Defaultness {
    Default(Span),
    /// No `default`.
    Final,
    /// `final fn` in a trait: implementations may not override it.
    FinalKw(Span),
}

/// `extern`, `extern "C"`, or nothing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Extern {
    None,
    /// `extern fn`: the C ABI.
    Implicit(Span),
    Explicit(StrLit, Span),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StrLit {
    /// The string's text, escapes unprocessed.
    pub symbol: Symbol,
    pub suffix: Symbol,
    pub style: LitKind,
    pub span: Span,
}

// ---------------------------------------------------------------------------------------------
// Patterns

#[derive(Clone, Debug)]
pub struct Pat {
    pub id: NodeId,
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BindingMode {
    pub by_ref: ByRef,
    pub mutbl: Mutability,
}

impl BindingMode {
    pub const NONE: BindingMode = BindingMode {
        by_ref: ByRef::No,
        mutbl: Mutability::Not,
    };
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ByRef {
    Yes(Mutability),
    No,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    /// `_`
    Wild,
    /// `ref mut x @ sub`
    Ident(BindingMode, Ident, Option<P<Pat>>),
    /// `S { a, b: p, .. }`
    Struct(Option<P<QSelf>>, Path, Vec<PatField>, PatFieldsRest),
    /// `S(a, b)`
    TupleStruct(Option<P<QSelf>>, Path, Vec<P<Pat>>),
    /// `a | b`
    Or(Vec<P<Pat>>),
    /// `S::C`, `<T>::C`
    Path(Option<P<QSelf>>, Path),
    Tuple(Vec<P<Pat>>),
    Box(P<Pat>),
    /// `deref!(p)`
    Deref(P<Pat>),
    /// `&p`, `&mut p`
    Ref(P<Pat>, Mutability),
    /// A literal, `-1`, or `const { … }`.
    Expr(P<Expr>),
    /// `a..=b`, `a..`, `..=b`
    Range(Option<P<Expr>>, Option<P<Expr>>, RangeEnd),
    Slice(Vec<P<Pat>>),
    /// `..` in a tuple or slice pattern.
    Rest,
    /// `!`
    Never,
    /// `p if cond` (guard patterns)
    Guard(P<Pat>, P<Expr>),
    Paren(P<Pat>),
    MacCall(P<MacCall>),
    Err,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeEnd {
    /// `..=` or the obsolete `...`
    Included(RangeSyntax),
    Excluded,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeSyntax {
    DotDotDot,
    DotDotEq,
}

#[derive(Clone, Debug)]
pub struct PatField {
    pub ident: Ident,
    pub pat: P<Pat>,
    /// `S { x }` rather than `S { x: x }`.
    pub is_shorthand: bool,
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PatFieldsRest {
    Rest,
    None,
}

// ---------------------------------------------------------------------------------------------
// Expressions

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: NodeId,
    pub kind: ExprKind,
    pub span: Span,
    pub attrs: Vec<Attribute>,
}

#[derive(Clone, Debug)]
pub struct AnonConst {
    pub id: NodeId,
    pub value: P<Expr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lit {
    pub kind: LitKind,
    /// The literal's text, without quotes or prefix, escapes unprocessed.
    pub symbol: Symbol,
    pub suffix: Symbol,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BinOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    And,
    Or,
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
}

impl BinOpKind {
    pub fn as_str(self) -> &'static str {
        use BinOpKind::*;
        match self {
            Add => "+",
            Sub => "-",
            Mul => "*",
            Div => "/",
            Rem => "%",
            And => "&&",
            Or => "||",
            BitXor => "^",
            BitAnd => "&",
            BitOr => "|",
            Shl => "<<",
            Shr => ">>",
            Eq => "==",
            Lt => "<",
            Le => "<=",
            Ne => "!=",
            Ge => ">=",
            Gt => ">",
        }
    }

    pub fn is_comparison(self) -> bool {
        use BinOpKind::*;
        matches!(self, Eq | Lt | Le | Ne | Ge | Gt)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BinOp {
    pub kind: BinOpKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum UnOp {
    Deref,
    Not,
    Neg,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BorrowKind {
    /// `&x`
    Ref,
    /// `&raw const x`
    Raw,
    /// `&pin mut x`
    Pin,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RangeLimits {
    HalfOpen,
    Closed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureBy {
    Ref,
    Value {
        move_kw: Span,
    },
    /// `use ||`
    Use {
        use_kw: Span,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoroutineKind {
    Async { span: Span },
    Gen { span: Span },
    AsyncGen { span: Span },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GenBlockKind {
    Async,
    Gen,
    AsyncGen,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatchKind {
    Prefix,
    /// `x.match { … }`
    Postfix,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForLoopKind {
    For,
    ForAwait,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Movability {
    Static,
    Movable,
}

#[derive(Clone, Debug)]
pub struct Label {
    /// Includes the quote: `'outer`.
    pub ident: Ident,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Array(Vec<P<Expr>>),
    ConstBlock(AnonConst),
    Call(P<Expr>, Vec<P<Expr>>),
    MethodCall(P<MethodCall>),
    Tup(Vec<P<Expr>>),
    Binary(BinOp, P<Expr>, P<Expr>),
    Unary(UnOp, P<Expr>),
    Lit(Lit),
    Cast(P<Expr>, P<Ty>),
    /// `builtin # type_ascribe(e, T)`
    Type(P<Expr>, P<Ty>),
    /// `let pat = e` in a condition.
    Let(P<Pat>, P<Expr>, Span),
    If(P<Expr>, P<Block>, Option<P<Expr>>),
    While(P<Expr>, P<Block>, Option<Label>),
    ForLoop {
        pat: P<Pat>,
        iter: P<Expr>,
        body: P<Block>,
        label: Option<Label>,
        kind: ForLoopKind,
    },
    Loop(P<Block>, Option<Label>),
    Match(P<Expr>, Vec<Arm>, MatchKind),
    Closure(P<Closure>),
    Block(P<Block>, Option<Label>),
    /// `async {}`, `gen {}`, `async gen {}`
    Gen(CaptureBy, P<Block>, GenBlockKind),
    Await(P<Expr>, Span),
    /// `e.use`
    Use(P<Expr>, Span),
    TryBlock(P<Block>),
    Assign(P<Expr>, P<Expr>, Span),
    AssignOp(BinOp, P<Expr>, P<Expr>),
    Field(P<Expr>, Ident),
    Index(P<Expr>, P<Expr>, Span),
    Range(Option<P<Expr>>, Option<P<Expr>>, RangeLimits),
    /// `_` on the left of a destructuring assignment.
    Underscore,
    Path(Option<P<QSelf>>, Path),
    AddrOf(BorrowKind, Mutability, P<Expr>),
    Break(Option<Label>, Option<P<Expr>>),
    Continue(Option<Label>),
    Ret(Option<P<Expr>>),
    /// `builtin # offset_of(Ty, field.path)`
    OffsetOf(P<Ty>, Vec<Ident>),
    MacCall(P<MacCall>),
    Struct(P<StructExpr>),
    /// `[e; N]`
    Repeat(P<Expr>, AnonConst),
    Paren(P<Expr>),
    Try(P<Expr>),
    Yield(Option<P<Expr>>),
    /// `do yeet e`
    Yeet(Option<P<Expr>>),
    /// `become f(x)`
    Become(P<Expr>),
    /// `format_args!(…)`: `builtin # format_args(…)` after expansion.
    FormatArgs(P<FormatArgs>),
    /// `asm!(…)`, `naked_asm!(…)`: the operands, parsed when lowering.
    InlineAsm(P<InlineAsm>),
    Err,
}

#[derive(Clone, Debug)]
pub struct FormatArgs {
    /// The format string: a literal, or a macro call expanding to one (`concat!(…)`).
    pub template: P<Expr>,
    pub args: Vec<FormatArgument>,
    pub span: Span,
    /// `format_args_nl!`: a newline is appended.
    pub newline: bool,
    /// `const_format_args!`
    pub is_const: bool,
}

#[derive(Clone, Debug)]
pub struct FormatArgument {
    /// `name = expr`
    pub name: Option<Ident>,
    pub expr: P<Expr>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AsmMacro {
    Asm,
    NakedAsm,
    GlobalAsm,
}

#[derive(Clone, Debug)]
pub struct InlineAsm {
    pub kind: AsmMacro,
    pub tokens: TokenStream,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct MethodCall {
    pub seg: PathSegment,
    pub receiver: P<Expr>,
    pub args: Vec<P<Expr>>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct StructExpr {
    pub qself: Option<P<QSelf>>,
    pub path: Path,
    pub fields: Vec<ExprField>,
    pub rest: StructRest,
}

#[derive(Clone, Debug)]
pub enum StructRest {
    /// `..base`
    Base(P<Expr>),
    /// `..` (default field values, or a destructuring assignment)
    Rest(Span),
    None,
}

#[derive(Clone, Debug)]
pub struct ExprField {
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub span: Span,
    pub ident: Ident,
    pub expr: P<Expr>,
    pub is_shorthand: bool,
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub attrs: Vec<Attribute>,
    pub pat: P<Pat>,
    pub guard: Option<P<Expr>>,
    /// `None` for an arm with a never pattern: `Err(!)`.
    pub body: Option<P<Expr>>,
    pub span: Span,
    pub id: NodeId,
}

#[derive(Clone, Debug)]
pub struct Closure {
    /// `for<'a>`
    pub binder: Vec<GenericParam>,
    pub capture_clause: CaptureBy,
    pub constness: Constness,
    pub coroutine_kind: Option<CoroutineKind>,
    pub movability: Movability,
    pub fn_decl: P<FnDecl>,
    pub body: P<Expr>,
    pub fn_decl_span: Span,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub id: NodeId,
    pub rules: BlockCheckMode,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockCheckMode {
    Default,
    Unsafe,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub id: NodeId,
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Let(P<Local>),
    Item(P<Item>),
    /// An expression without a semicolon: the block's value, or a block-like expression.
    Expr(P<Expr>),
    Semi(P<Expr>),
    /// A lone `;`.
    Empty,
    MacCall(P<MacCallStmt>),
}

#[derive(Clone, Debug)]
pub struct Local {
    pub id: NodeId,
    /// `super let`: the binding lives as long as the enclosing block's value.
    pub super_: Option<Span>,
    pub pat: P<Pat>,
    pub ty: Option<P<Ty>>,
    pub kind: LocalKind,
    pub span: Span,
    pub attrs: Vec<Attribute>,
}

#[derive(Clone, Debug)]
pub enum LocalKind {
    Decl,
    Init(P<Expr>),
    InitElse(P<Expr>, P<Block>),
}

#[derive(Clone, Debug)]
pub struct MacCallStmt {
    pub mac: P<MacCall>,
    pub style: MacStmtStyle,
    pub attrs: Vec<Attribute>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MacStmtStyle {
    /// `foo!(…);`, `foo![…];`
    Semicolon,
    /// `foo! { … }`
    Braces,
    /// `foo!(…)`, the block's value.
    NoBraces,
}

#[derive(Clone, Debug)]
pub struct MacCall {
    pub path: Path,
    pub args: DelimArgs,
}

// ---------------------------------------------------------------------------------------------
// Items

#[derive(Clone, Debug)]
pub struct Visibility {
    pub kind: VisibilityKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum VisibilityKind {
    Public,
    /// `pub(crate)`, `pub(super)`, `pub(self)` (shorthand) or `pub(in path)`.
    Restricted {
        path: P<Path>,
        id: NodeId,
        shorthand: bool,
    },
    Inherited,
}

impl Visibility {
    pub fn inherited(span: Span) -> Visibility {
        Visibility {
            kind: VisibilityKind::Inherited,
            span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Item<K = ItemKind> {
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub span: Span,
    pub vis: Visibility,
    /// `kw::Empty` for items without a name (impls, `use`, foreign modules, macro calls).
    pub ident: Ident,
    pub kind: K,
}

pub type AssocItem = Item<AssocItemKind>;
pub type ForeignItem = Item<ForeignItemKind>;

#[derive(Clone, Debug)]
pub enum ItemKind {
    /// `extern crate orig as ident;` (`orig` is `None` without `as`).
    ExternCrate(Option<Symbol>),
    Use(UseTree),
    Static(P<StaticItem>),
    Const(P<ConstItem>),
    Fn(P<Fn>),
    Mod(Safety, ModKind),
    ForeignMod(ForeignMod),
    TyAlias(P<TyAlias>),
    Enum(EnumDef, Generics),
    Struct(VariantData, Generics),
    Union(VariantData, Generics),
    Trait(P<Trait>),
    TraitAlias(Generics, GenericBounds),
    Impl(P<Impl>),
    MacCall(P<MacCall>),
    /// `macro_rules! name { … }` or `macro name(…) { … }`.
    MacroDef(MacroDef),
    /// `global_asm!(…)`
    GlobalAsm(P<InlineAsm>),
}

#[derive(Clone, Debug)]
pub enum AssocItemKind {
    Const(P<ConstItem>),
    Fn(P<Fn>),
    Type(P<TyAlias>),
    MacCall(P<MacCall>),
}

#[derive(Clone, Debug)]
pub enum ForeignItemKind {
    Static(P<StaticItem>),
    Fn(P<Fn>),
    TyAlias(P<TyAlias>),
    MacCall(P<MacCall>),
}

#[derive(Clone, Debug)]
pub struct UseTree {
    pub prefix: Path,
    pub kind: UseTreeKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum UseTreeKind {
    /// `use prefix` or `use prefix as rename`
    Simple(Option<Ident>),
    /// `use prefix::{…}`
    Nested {
        items: Vec<(UseTree, NodeId)>,
        span: Span,
    },
    /// `use prefix::*`
    Glob,
}

#[derive(Clone, Debug)]
pub struct StaticItem {
    pub ty: P<Ty>,
    pub safety: Safety,
    pub mutability: Mutability,
    pub expr: Option<P<Expr>>,
}

#[derive(Clone, Debug)]
pub struct ConstItem {
    pub defaultness: Defaultness,
    pub generics: Generics,
    pub ty: P<Ty>,
    pub expr: Option<P<Expr>>,
}

#[derive(Clone, Debug)]
pub struct Fn {
    pub defaultness: Defaultness,
    pub generics: Generics,
    pub sig: FnSig,
    pub body: Option<P<Block>>,
}

#[derive(Clone, Debug)]
pub struct FnSig {
    pub header: FnHeader,
    pub decl: P<FnDecl>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug)]
pub struct FnHeader {
    pub safety: Safety,
    pub coroutine_kind: Option<CoroutineKind>,
    pub constness: Constness,
    pub ext: Extern,
}

impl Default for FnHeader {
    fn default() -> FnHeader {
        FnHeader {
            safety: Safety::Default,
            coroutine_kind: None,
            constness: Constness::No,
            ext: Extern::None,
        }
    }
}

#[derive(Clone, Debug)]
pub struct FnDecl {
    pub inputs: Vec<Param>,
    pub output: FnRetTy,
}

impl FnDecl {
    pub fn has_self(&self) -> bool {
        self.inputs.first().is_some_and(|p| p.is_self())
    }

    pub fn c_variadic(&self) -> bool {
        self.inputs
            .last()
            .is_some_and(|p| matches!(p.ty.kind, TyKind::CVarArgs))
    }
}

#[derive(Clone, Debug)]
pub enum FnRetTy {
    /// No `-> T`: the span is where it would be.
    Default(Span),
    Ty(P<Ty>),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub attrs: Vec<Attribute>,
    pub ty: P<Ty>,
    pub pat: P<Pat>,
    pub id: NodeId,
    pub span: Span,
}

impl Param {
    pub fn is_self(&self) -> bool {
        matches!(&self.pat.kind, PatKind::Ident(_, ident, _) if ident.name == hyprc_span::kw::SelfLower)
    }
}

#[derive(Clone, Debug)]
pub enum ModKind {
    /// Inline (`mod m { … }`) or loaded from its file. `inline` tells which; `span` covers the
    /// items (the braces, or the whole file).
    Loaded {
        items: Vec<P<Item>>,
        inline: bool,
        span: Span,
    },
    /// `mod m;`, not loaded yet.
    Unloaded,
}

#[derive(Clone, Debug)]
pub struct ForeignMod {
    pub extern_span: Span,
    pub safety: Safety,
    pub abi: Option<StrLit>,
    pub items: Vec<P<ForeignItem>>,
}

#[derive(Clone, Debug)]
pub struct TyAlias {
    pub defaultness: Defaultness,
    pub generics: Generics,
    /// `type Assoc: Bound;` in traits.
    pub bounds: GenericBounds,
    pub ty: Option<P<Ty>>,
    /// A `where` clause after the type: `type A = B where …;`.
    pub after_where: WhereClause,
}

#[derive(Clone, Debug)]
pub struct EnumDef {
    pub variants: Vec<Variant>,
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub span: Span,
    pub vis: Visibility,
    pub ident: Ident,
    pub data: VariantData,
    pub disr_expr: Option<AnonConst>,
}

#[derive(Clone, Debug)]
pub enum VariantData {
    Struct { fields: Vec<FieldDef> },
    Tuple(Vec<FieldDef>, NodeId),
    Unit(NodeId),
}

impl VariantData {
    pub fn fields(&self) -> &[FieldDef] {
        match self {
            VariantData::Struct { fields } | VariantData::Tuple(fields, _) => fields,
            VariantData::Unit(_) => &[],
        }
    }
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub attrs: Vec<Attribute>,
    pub id: NodeId,
    pub span: Span,
    pub vis: Visibility,
    pub safety: Safety,
    /// `None` for tuple fields.
    pub ident: Option<Ident>,
    pub ty: P<Ty>,
    /// `field: T = default` (default field values).
    pub default: Option<AnonConst>,
}

#[derive(Clone, Debug)]
pub struct Trait {
    /// `impl(crate) trait`: where the trait may be implemented.
    pub impl_restriction: Option<P<Path>>,
    pub constness: Constness,
    pub safety: Safety,
    pub is_auto: bool,
    pub generics: Generics,
    pub bounds: GenericBounds,
    pub items: Vec<P<AssocItem>>,
}

#[derive(Clone, Debug)]
pub struct Impl {
    pub defaultness: Defaultness,
    pub safety: Safety,
    pub generics: Generics,
    pub constness: Constness,
    pub polarity: ImplPolarity,
    pub of_trait: Option<TraitRef>,
    pub self_ty: P<Ty>,
    pub items: Vec<P<AssocItem>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ImplPolarity {
    Positive,
    /// `impl !Trait for T`
    Negative(Span),
}

#[derive(Clone, Debug)]
pub struct MacroDef {
    /// For `macro_rules!`: the body. For `macro name(args) { body }`: both, as
    /// `(args) => { body }` so either kind is one list of rules.
    pub body: DelimArgs,
    pub macro_rules: bool,
}
