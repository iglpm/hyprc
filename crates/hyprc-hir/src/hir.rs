//! The HIR: items and bodies with every name resolved and the surface sugar removed.
//!
//! Bodies are arenas: expressions and patterns are `ExprId`/`PatId` indices into vectors
//! owned by their `Body`, so later stages keep their per-node results in plain vectors
//! indexed the same way.

pub use hyprc_resolve::{
    CtorKind, CtorOf, DefId, DefKind, FloatTy, IntTy, PrimTy, Res, UintTy, Vis,
};
use hyprc_span::{FxHashMap, Ident, Span, Symbol};
pub use hyprc_syntax::ast::{BinOpKind, BorrowKind, Mutability, RangeEnd, UnOp};
use hyprc_syntax::token::LitKind;
use std::fmt;

macro_rules! id {
    ($name:ident, $p:literal) => {
        #[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        pub struct $name(pub u32);
        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, concat!($p, "{}"), self.0)
            }
        }
        impl $name {
            pub fn index(self) -> usize {
                self.0 as usize
            }
        }
    };
}

id!(BodyId, "body");
id!(ExprId, "e");
id!(PatId, "p");
id!(LocalId, "l");
id!(LoopId, "loop");
id!(ClosureId, "closure");

// -------------------------------------------------------------------------------------------
// Crate and items

pub struct Crate {
    /// Indexed by `DefId`; `None` for definitions without an item (blocks, variants, …).
    pub items: Vec<Option<Item>>,
    pub bodies: Vec<Body>,
    pub root: DefId,
    pub crate_name: Symbol,
    pub lang_items: FxHashMap<Symbol, DefId>,
    /// All impls, trait and inherent.
    pub impls: Vec<DefId>,
    /// Definition kinds and parents, for everything (also definitions without an item).
    pub def_kinds: Vec<DefKind>,
    pub def_parents: Vec<Option<DefId>>,
    pub def_names: Vec<Symbol>,
    pub def_spans: Vec<Span>,
    pub def_krates: Vec<u32>,
    /// Traits in scope in each module and block scope (for method calls): imported traits,
    /// traits defined there, `use Trait as _`, and the prelude's.
    pub traits_in_scope: FxHashMap<DefId, Vec<DefId>>,
    pub no_core: bool,
    pub no_std: bool,
    pub no_main: bool,
    /// The `main` function of a binary crate, if any.
    pub entry: Option<DefId>,
    pub features: hyprc_span::FxHashSet<Symbol>,
}

impl Crate {
    pub fn is_local(&self, def: DefId) -> bool {
        self.def_krates.get(def.0 as usize).copied().unwrap_or(0) == 0
    }

    pub fn has_feature(&self, name: &str) -> bool {
        self.features.contains(&Symbol::intern(name))
    }

    pub fn item(&self, def: DefId) -> &Item {
        self.items[def.0 as usize]
            .as_ref()
            .unwrap_or_else(|| panic!("{def:?} has no item"))
    }

    pub fn get_item(&self, def: DefId) -> Option<&Item> {
        self.items.get(def.0 as usize).and_then(Option::as_ref)
    }

    pub fn body(&self, id: BodyId) -> &Body {
        &self.bodies[id.index()]
    }

    pub fn def_kind(&self, def: DefId) -> DefKind {
        self.def_kinds[def.0 as usize]
    }

    pub fn parent(&self, def: DefId) -> Option<DefId> {
        self.def_parents[def.0 as usize]
    }

    pub fn name(&self, def: DefId) -> Symbol {
        self.def_names[def.0 as usize]
    }

    pub fn span(&self, def: DefId) -> Span {
        self.def_spans[def.0 as usize]
    }

    pub fn lang_item(&self, name: &str) -> Option<DefId> {
        self.lang_items.get(&Symbol::intern(name)).copied()
    }

    pub fn def_path(&self, def: DefId) -> String {
        let mut parts = Vec::new();
        let mut cur = Some(def);
        while let Some(d) = cur {
            let name = self.name(d);
            let p = self.parent(d);
            if p.is_none() {
                parts.push(self.crate_name.as_str().to_string());
            } else if !name.as_str().is_empty() {
                parts.push(name.as_str().to_string());
            } else if matches!(self.def_kind(d), DefKind::Impl { .. }) {
                parts.push(format!("{{impl#{}}}", d.0));
            }
            cur = p;
        }
        parts.reverse();
        parts.join("::")
    }
}

/// Attributes later stages care about, decoded once.
#[derive(Clone, Debug, Default)]
pub struct ItemAttrs {
    pub no_mangle: bool,
    pub export_name: Option<Symbol>,
    pub link_name: Option<Symbol>,
    pub link_section: Option<Symbol>,
    pub lang: Option<Symbol>,
    pub inline: Option<InlineAttr>,
    pub cold: bool,
    pub track_caller: bool,
    pub repr: Repr,
    pub used: bool,
    pub naked: bool,
    pub thread_local: bool,
    pub rustc_intrinsic: bool,
    pub must_use: bool,
    pub non_exhaustive: bool,
    /// `#[rustc_*]` attributes that change semantics (`rustc_box`, `rustc_nounwind`, …).
    pub rustc: Vec<Symbol>,
    pub target_features: Vec<Symbol>,
    pub doc_hidden: bool,
    pub legacy_const_generics: Option<Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InlineAttr {
    Hint,
    Always,
    Never,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Repr {
    pub c: bool,
    pub transparent: bool,
    pub simd: bool,
    /// `repr(u8)` and friends.
    pub int: Option<PrimTy>,
    pub align: Option<u64>,
    pub packed: Option<u64>,
}

#[derive(Clone, Debug)]
pub struct Item {
    pub def: DefId,
    pub name: Symbol,
    pub span: Span,
    pub vis: Vis,
    pub attrs: ItemAttrs,
    pub kind: ItemKind,
}

#[derive(Clone, Debug)]
pub enum ItemKind {
    Fn(FnItem),
    Const {
        ty: Ty,
        generics: Generics,
        body: Option<BodyId>,
    },
    Static {
        ty: Ty,
        mutable: bool,
        body: Option<BodyId>,
        foreign: bool,
    },
    Struct {
        data: VariantData,
        generics: Generics,
    },
    Union {
        data: VariantData,
        generics: Generics,
    },
    Enum {
        variants: Vec<Variant>,
        generics: Generics,
    },
    TyAlias {
        ty: Option<Ty>,
        generics: Generics,
        bounds: Vec<GenericBound>,
    },
    ForeignTy,
    Trait(TraitItem),
    TraitAlias {
        generics: Generics,
        bounds: Vec<GenericBound>,
    },
    Impl(ImplItem),
    /// Modules, `use`, macros, extern blocks: nothing for later stages but their children.
    Other,
}

#[derive(Clone, Debug)]
pub struct FnItem {
    pub sig: FnSig,
    pub generics: Generics,
    pub body: Option<BodyId>,
    /// An associated fn's container (trait or impl), or `None` for free and foreign fns.
    pub container: Option<DefId>,
    /// In an `extern` block.
    pub foreign: bool,
    pub defaultness_default: bool,
}

#[derive(Clone, Debug)]
pub struct FnSig {
    pub inputs: Vec<Ty>,
    pub output: Option<Ty>,
    pub c_variadic: bool,
    pub safety_unsafe: bool,
    pub is_const: bool,
    pub is_async: bool,
    pub abi: Abi,
    /// `&self`/`self`/`self: T`: the first input is the receiver.
    pub has_self: bool,
    pub param_names: Vec<Ident>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Abi {
    Rust,
    C,
    /// `extern "rust-intrinsic"`, `extern "rust-call"`, `extern "system"`, … kept by name.
    Other(Symbol),
}

#[derive(Clone, Debug)]
pub struct TraitItem {
    pub generics: Generics,
    pub supertraits: Vec<GenericBound>,
    pub items: Vec<DefId>,
    pub is_auto: bool,
    pub is_unsafe: bool,
    pub is_const: bool,
}

#[derive(Clone, Debug)]
pub struct ImplItem {
    pub generics: Generics,
    pub of_trait: Option<TraitRef>,
    pub self_ty: Ty,
    pub items: Vec<DefId>,
    pub negative: bool,
    pub is_unsafe: bool,
    pub is_const: bool,
    pub default: bool,
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub def: DefId,
    pub name: Symbol,
    pub span: Span,
    pub data: VariantData,
    pub discr: Option<BodyId>,
}

#[derive(Clone, Debug)]
pub struct VariantData {
    pub kind: CtorShape,
    pub fields: Vec<FieldDef>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CtorShape {
    /// `S { a: T }`
    Struct,
    /// `S(T)`
    Tuple,
    /// `S`
    Unit,
}

#[derive(Clone, Debug)]
pub struct FieldDef {
    pub name: Symbol,
    pub span: Span,
    pub vis: Vis,
    pub ty: Ty,
}

// -------------------------------------------------------------------------------------------
// Generics

#[derive(Clone, Debug, Default)]
pub struct Generics {
    /// The parameters this item declares (not its parent's), lifetimes excluded: hyprc
    /// erases lifetimes.
    pub params: Vec<GenericParam>,
    pub predicates: Vec<WherePredicate>,
    /// The generic item this one is nested in (an associated item's trait or impl).
    pub parent: Option<DefId>,
    /// How many parameters the parents have: this item's first parameter has that index.
    pub parent_count: u32,
    /// Traits declare `Self` as parameter 0.
    pub has_self: bool,
    pub span: Span,
}

impl Generics {
    pub fn count(&self) -> u32 {
        self.parent_count + self.params.len() as u32 + self.has_self as u32
    }
}

#[derive(Clone, Debug)]
pub struct GenericParam {
    pub name: Symbol,
    pub span: Span,
    /// The absolute index in the item's generic arguments.
    pub index: u32,
    pub kind: GenericParamKind,
    /// `impl Trait` in argument position, turned into a parameter.
    pub synthetic: bool,
}

#[derive(Clone, Debug)]
pub enum GenericParamKind {
    Type { default: Option<Ty> },
    Const { ty: Ty, default: Option<BodyId> },
}

#[derive(Clone, Debug)]
pub enum WherePredicate {
    /// `T: Bound + Bound` (also bounds written on parameters, and `Self: Trait`).
    Bound { ty: Ty, bounds: Vec<GenericBound> },
    /// `T = U`
    Eq { lhs: Ty, rhs: Ty },
}

#[derive(Clone, Debug)]
pub enum GenericBound {
    Trait {
        trait_ref: TraitRef,
        maybe: bool,
        negative: bool,
        is_const: bool,
    },
    /// Lifetimes are erased; kept only as a marker.
    Outlives,
}

#[derive(Clone, Debug)]
pub struct TraitRef {
    pub path: Path,
    pub span: Span,
}

// -------------------------------------------------------------------------------------------
// Types and paths

#[derive(Clone, Debug)]
pub struct Ty {
    pub kind: TyKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum TyKind {
    Path(QPath),
    Ref(Mutability, Box<Ty>),
    Ptr(Mutability, Box<Ty>),
    Slice(Box<Ty>),
    Array(Box<Ty>, ConstArg),
    Tup(Vec<Ty>),
    FnPtr(Box<FnPtrTy>),
    Never,
    /// `_`
    Infer,
    /// `dyn Trait + Send` (or a bare trait in 2015 code).
    TraitObject(Vec<GenericBound>),
    /// `impl Trait` in return position: an opaque type defined by `owner`'s body; `index`
    /// tells several apart.
    Opaque {
        owner: DefId,
        index: u32,
        bounds: Vec<GenericBound>,
    },
    /// `impl Trait` in argument position: the synthetic type parameter it became.
    /// (Lowered to `Path(Res::TyParam)` directly; this variant isn't produced.)
    ImplicitSelf,
    /// `u32 is 1..`: a pattern type.
    Pat(Box<Ty>, TyPat),
    /// `typeof(e)` and other unsupported forms; an error was reported.
    Err,
}

/// The pattern of a pattern type.
#[derive(Clone, Debug)]
pub enum TyPat {
    /// `a..b`, `a..=b`, `..b`, `a..`: bounds are constant bodies.
    Range {
        start: Option<BodyId>,
        end: Option<BodyId>,
        inclusive: bool,
    },
    /// `!null`
    NotNull,
    Or(Vec<TyPat>),
    Err,
}

#[derive(Clone, Debug)]
pub struct FnPtrTy {
    pub inputs: Vec<Ty>,
    pub output: Option<Ty>,
    pub c_variadic: bool,
    pub safety_unsafe: bool,
    pub abi: Abi,
}

/// A const generic argument or array length.
#[derive(Clone, Debug)]
pub enum ConstArg {
    /// An expression with its own body.
    Body(BodyId),
    /// A path to a const parameter.
    Param {
        owner: DefId,
        index: u32,
    },
    Infer,
}

#[derive(Clone, Debug)]
pub enum QPath {
    /// A path resolved completely, with an optional `<qself as …>`.
    Resolved(Option<Box<Ty>>, Path),
    /// `<T>::name`, `T::name`, `Vec::<u8>::new`: an associated item of a type, found when
    /// type checking.
    TypeRelative(Box<Ty>, PathSegment),
    /// A lang item path the lowering made up (`IntoIterator::into_iter` in `for` loops).
    LangItem(Symbol, Span),
}

#[derive(Clone, Debug)]
pub struct Path {
    pub res: Res,
    pub segments: Vec<PathSegment>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct PathSegment {
    pub ident: Ident,
    /// What this segment alone resolved to (modules, types, the final item).
    pub res: Res,
    pub args: Option<Box<GenericArgs>>,
}

#[derive(Clone, Debug, Default)]
pub struct GenericArgs {
    pub args: Vec<GenericArg>,
    pub constraints: Vec<AssocConstraint>,
    /// `Fn(A, B) -> C` sugar: `args` holds the tuple `(A, B)`, the constraint `Output = C`.
    pub parenthesized: bool,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum GenericArg {
    Type(Ty),
    Const(ConstArg),
    /// Lifetimes are erased but their position matters for counting with `_` inference.
    Lifetime,
    Infer,
}

#[derive(Clone, Debug)]
pub struct AssocConstraint {
    pub name: Ident,
    pub args: Option<Box<GenericArgs>>,
    pub kind: AssocConstraintKind,
}

#[derive(Clone, Debug)]
pub enum AssocConstraintKind {
    Equality(Ty),
    EqualityConst(ConstArg),
    Bound(Vec<GenericBound>),
}

// -------------------------------------------------------------------------------------------
// Bodies

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BodyKind {
    Fn,
    Const,
    Static,
    /// An array length, const generic argument, enum discriminant, or default.
    AnonConst,
}

pub struct Body {
    pub owner: DefId,
    pub kind: BodyKind,
    pub params: Vec<PatId>,
    pub value: ExprId,
    pub exprs: Vec<Expr>,
    pub pats: Vec<Pat>,
    pub locals: Vec<Local>,
    pub loops: Vec<LoopData>,
    pub closures: Vec<ClosureData>,
    /// The scope (module or block) names in this body resolve in, for method-call traits.
    pub scope: DefId,
    /// Each block's own item scope, if it has items.
    pub span: Span,
}

impl Body {
    pub fn expr(&self, id: ExprId) -> &Expr {
        &self.exprs[id.index()]
    }

    pub fn pat(&self, id: PatId) -> &Pat {
        &self.pats[id.index()]
    }

    pub fn local(&self, id: LocalId) -> &Local {
        &self.locals[id.index()]
    }
}

#[derive(Clone, Debug)]
pub struct Local {
    pub name: Ident,
    pub mutable: bool,
    pub span: Span,
    /// The pattern that binds it.
    pub pat: PatId,
}

#[derive(Clone, Debug)]
pub struct LoopData {
    pub label: Option<Ident>,
    /// A labeled block (`'a: { … }`) rather than a loop: `continue` can't target it.
    pub is_block: bool,
}

#[derive(Clone, Debug)]
pub struct ClosureData {
    pub params: Vec<(PatId, Option<Ty>)>,
    pub ret: Option<Ty>,
    pub body: ExprId,
    pub by_move: bool,
    pub kind: ClosureKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClosureKind {
    Closure,
    /// `async` blocks and `async` closures' bodies.
    Async,
    /// `gen` blocks.
    Gen,
    /// `#[coroutine] || { yield … }`
    Coroutine,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Lit {
    pub kind: LitKind,
    pub symbol: Symbol,
    pub suffix: Symbol,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub tail: Option<ExprId>,
    pub unsafe_: bool,
    /// The block's item scope, if it declares items.
    pub scope: Option<DefId>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    Let {
        pat: PatId,
        ty: Option<Ty>,
        init: Option<ExprId>,
        els: Option<Block>,
    },
    /// An expression statement (`;` or block-like).
    Expr(ExprId),
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: PatId,
    pub guard: Option<ExprId>,
    pub body: ExprId,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatchSource {
    Normal,
    /// The `match` a `for` loop became.
    ForLoop,
    /// The `match` `?` became.
    Try,
    /// `if let` / `while let` without chains became a match? (no: those stay `Let`).
    Await,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LoopSource {
    Loop,
    While,
    ForLoop,
}

#[derive(Clone, Debug)]
pub struct ExprField {
    pub name: Ident,
    pub expr: ExprId,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StructTail {
    None,
    Base(ExprId),
    /// `..` with default field values.
    Defaults,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Lit(Lit),
    Path(QPath),
    Call(ExprId, Vec<ExprId>),
    MethodCall {
        receiver: ExprId,
        segment: PathSegment,
        args: Vec<ExprId>,
    },
    Binary(BinOpKind, ExprId, ExprId),
    Unary(UnOp, ExprId),
    Cast(ExprId, Ty),
    /// Type ascription.
    Type(ExprId, Ty),
    AddrOf(BorrowKind, Mutability, ExprId),
    Field(ExprId, Ident),
    Index(ExprId, ExprId),
    Tuple(Vec<ExprId>),
    Array(Vec<ExprId>),
    Repeat(ExprId, ConstArg),
    Struct {
        path: QPath,
        fields: Vec<ExprField>,
        tail: StructTail,
    },
    If {
        cond: ExprId,
        then: ExprId,
        els: Option<ExprId>,
    },
    /// `let pat = init` in a condition.
    Let {
        pat: PatId,
        init: ExprId,
    },
    Loop {
        body: Block,
        id: LoopId,
        source: LoopSource,
    },
    Match {
        scrutinee: ExprId,
        arms: Vec<Arm>,
        source: MatchSource,
    },
    Block(Block, Option<LoopId>),
    Assign(ExprId, ExprId),
    AssignOp(BinOpKind, ExprId, ExprId),
    Break {
        target: Option<LoopId>,
        value: Option<ExprId>,
    },
    Continue {
        target: Option<LoopId>,
    },
    Return(Option<ExprId>),
    Closure(ClosureId),
    /// `const { … }`
    ConstBlock(ExprId),
    Yield(Option<ExprId>),
    /// `e.await`: kept for the coroutine lowering.
    Await(ExprId),
    FormatArgs(Box<FormatArgs>),
    InlineAsm(Box<hyprc_syntax::ast::InlineAsm>),
    OffsetOf(Ty, Vec<Ident>),
    /// `become f(x)`
    Become(ExprId),
    Err,
}

#[derive(Clone, Debug)]
pub struct FormatArgs {
    pub template: Vec<FormatPiece>,
    pub args: Vec<ExprId>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum FormatPiece {
    Literal(Symbol),
    /// `{}`, `{:?}`, `{x:>5}`…: which argument, how, with what options.
    Placeholder {
        arg: usize,
        trait_: FormatTrait,
        spec: FormatSpec,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FormatTrait {
    Display,
    Debug,
    LowerHex,
    UpperHex,
    Octal,
    Binary,
    LowerExp,
    UpperExp,
    Pointer,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct FormatSpec {
    pub fill: Option<char>,
    pub align: u8,
    pub sign_plus: bool,
    pub sign_minus: bool,
    pub alternate: bool,
    pub zero_pad: bool,
    pub width: Option<FormatCount>,
    pub precision: Option<FormatCount>,
    pub debug_hex: u8,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormatCount {
    Literal(usize),
    /// An argument (index) holding the count.
    Arg(usize),
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub kind: PatKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BindingMode {
    Value { mutable: bool },
    Ref { mutable: bool },
}

#[derive(Clone, Debug)]
pub struct FieldPat {
    pub name: Ident,
    pub pat: PatId,
}

#[derive(Clone, Debug)]
pub enum PatKind {
    Wild,
    Binding {
        mode: BindingMode,
        local: LocalId,
        sub: Option<PatId>,
    },
    Struct {
        path: QPath,
        fields: Vec<FieldPat>,
        rest: bool,
    },
    /// `S(a, .., b)`: `rest` is the position of the `..`.
    TupleStruct {
        path: QPath,
        pats: Vec<PatId>,
        rest: Option<usize>,
    },
    /// A unit struct or variant, or a constant.
    Path(QPath),
    Tuple {
        pats: Vec<PatId>,
        rest: Option<usize>,
    },
    Box(PatId),
    Deref(PatId),
    Ref(PatId, Mutability),
    /// A literal, `-literal`, or `const { … }`.
    Lit(ExprId),
    Range {
        lo: Option<ExprId>,
        hi: Option<ExprId>,
        end: RangeEnd,
    },
    /// `[a, b, rest @ .., z]`
    Slice {
        before: Vec<PatId>,
        rest: Option<PatId>,
        after: Vec<PatId>,
        has_rest: bool,
    },
    Or(Vec<PatId>),
    Never,
    Err,
}
