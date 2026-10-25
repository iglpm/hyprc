//! Type checking a body.
//!
//! One [`FnCtxt`] per body (closures are checked with their parent body). Expressions are
//! checked against an expectation; what can't be decided right away (trait bounds,
//! associated types of not-yet-known types) goes into an obligation queue that's retried
//! as types become known. At the end, integer and float variables default, the queue must
//! be empty, and every type is resolved ("writeback").

mod closure;
mod coerce;
mod expr;
mod method;
mod op;
mod pat;
mod path;

use crate::TyCtxt;
use crate::collect::ClosureKind;
use crate::infer::{InferCtxt, TypeError};
use crate::traits::{ClosureInfo, Eval, ParamEnv, Projected, SelectResult, Solver};
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{BodyId, DefId, ExprId, LocalId, Mutability, PatId};
use hyprc_span::{Diag, FxHashMap, Span};
use std::cell::{Cell, RefCell};

/// An implicit conversion applied to an expression's value, in order.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Adjust {
    /// `*` through a reference or raw pointer (built-in) or `Deref::deref`.
    Deref(Option<OverloadedDeref>),
    /// `&` / `&mut`.
    Borrow(Mutability),
    /// `&raw const`/`&raw mut` (for `&mut T` → `*mut T` coercions).
    RawBorrow(Mutability),
    /// `&[T; N]` → `&[T]`, `&T` → `&dyn Trait`, `Box<T>` → `Box<dyn Trait>`.
    Unsize,
    /// `!` → any type.
    NeverToAny,
    /// A function item → a function pointer.
    ReifyFnPointer,
    /// A non-capturing closure → a function pointer.
    ClosureFnPointer,
    /// `*mut T` → `*const T`.
    MutToConstPointer,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OverloadedDeref {
    pub method: DefId,
    pub args: Args,
    pub mutbl: Mutability,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Adjustment {
    pub kind: Adjust,
    /// The type after this step.
    pub target: Ty,
}

/// How a closure uses a captured variable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CaptureKind {
    ByValue,
    ByRef(Mutability),
}

#[derive(Clone, Debug)]
pub struct Upvar {
    pub local: LocalId,
    pub kind: CaptureKind,
    /// The variable's type (the capture is this, or a reference to it).
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct ClosureResult {
    pub kind: ClosureKind,
    pub sig: FnSig,
    pub upvars: Vec<Upvar>,
    /// The closure's type (with its final arguments).
    pub ty: Ty,
}

/// A resolved callee: a method call, an overloaded operator, a type-relative path.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Callee {
    pub def: DefId,
    pub args: Args,
}

/// Everything later stages need to know about a body's types.
#[derive(Clone, Debug, Default)]
pub struct TypeckResults {
    pub expr_tys: Vec<Ty>,
    pub pat_tys: Vec<Ty>,
    pub local_tys: Vec<Ty>,
    pub adjustments: FxHashMap<ExprId, Vec<Adjustment>>,
    /// Match ergonomics: the reference types a pattern dereferenced implicitly.
    pub pat_adjustments: FxHashMap<PatId, Vec<Ty>>,
    /// The effective binding mode of each binding pattern.
    pub binding_modes: FxHashMap<PatId, hir::BindingMode>,
    /// Generic arguments of path expressions (functions, constants, constructors).
    pub node_args: FxHashMap<ExprId, Args>,
    /// What a type-relative path (`Vec::new`) or a method call resolved to.
    pub type_dependent: FxHashMap<ExprId, Callee>,
    /// Overloaded operators: `a + b` on a type with `impl Add`, `a[i]`, `*a`, `-a`.
    pub overloaded: FxHashMap<ExprId, Callee>,
    /// Field accesses: the field's index.
    pub field_indices: FxHashMap<ExprId, usize>,
    /// Struct expressions and patterns: each written field's index, by position.
    pub struct_fields: FxHashMap<ExprId, Vec<usize>>,
    pub pat_fields: FxHashMap<PatId, Vec<usize>>,
    /// The variant a struct expression, tuple-struct or struct pattern refers to.
    pub variants: FxHashMap<u32, (DefId, usize)>,
    pub closures: Vec<Option<ClosureResult>>,
    /// Casts to check for validity at codegen (`as`).
    pub casts: Vec<(ExprId, Ty, Ty)>,
    /// `offset_of!`: the container type and each step (variant, field, field type).
    pub offset_of: FxHashMap<ExprId, (Ty, Vec<(u32, u32, Ty)>)>,
    /// The hidden types of the function's own `impl Trait` return types, by index.
    pub opaque_hidden: Vec<(u32, Ty)>,
    /// Patterns that are constants (`FOO`, `Self::MAX`, `Alignment::MIN`): the item and
    /// its arguments.
    pub pat_consts: FxHashMap<PatId, (DefId, Args)>,
    pub tainted_by_errors: bool,
}

impl TypeckResults {
    pub fn expr_ty(&self, e: ExprId) -> Ty {
        self.expr_tys[e.index()]
    }

    /// The type after adjustments.
    pub fn expr_ty_adjusted(&self, e: ExprId) -> Ty {
        match self.adjustments.get(&e).and_then(|a| a.last()) {
            Some(a) => a.target,
            None => self.expr_ty(e),
        }
    }

    pub fn pat_ty(&self, p: PatId) -> Ty {
        self.pat_tys[p.index()]
    }

    pub fn variant_of_expr(&self, e: ExprId) -> Option<(DefId, usize)> {
        self.variants.get(&e.0).copied()
    }

    pub fn variant_of_pat(&self, p: PatId) -> Option<(DefId, usize)> {
        self.variants.get(&(p.0 | 0x8000_0000)).copied()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum Expectation {
    None,
    HasType(Ty),
    /// `e as T`: a hint only (integer literals take it).
    Castable(Ty),
}

impl Expectation {
    fn only_has_type(self) -> Option<Ty> {
        match self {
            Expectation::HasType(t) => Some(t),
            _ => None,
        }
    }

    fn hint(self) -> Option<Ty> {
        match self {
            Expectation::HasType(t) | Expectation::Castable(t) => Some(t),
            Expectation::None => None,
        }
    }
}

struct LoopCtxt {
    /// The type `break` values coerce to, once there is one.
    break_ty: Option<Ty>,
    may_break: bool,
}

pub(crate) struct FnCtxt<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    pub body: &'h hir::Body,
    pub body_id: BodyId,
    pub owner: DefId,
    pub infcx: InferCtxt,
    pub env: std::sync::Arc<ParamEnv>,
    pub r: RefCell<TypeckResults>,
    obligations: RefCell<Vec<(Predicate, Span)>>,
    /// The return type of the body being checked (closures push theirs).
    ret_tys: RefCell<Vec<Ty>>,
    loops: RefCell<Vec<Option<LoopCtxt>>>,
    /// The expression currently being checked diverges (has type `!` or a diverging part).
    diverges: Cell<bool>,
    /// Inside `unsafe` (blocks or functions).
    in_unsafe: Cell<u32>,
    /// Closure signatures and kinds while checking (indexed like `body.closures`).
    closure_info: RefCell<Vec<Option<(FnSig, Option<ClosureKind>, Ty)>>>,
    /// Type variables created for `!` (they fall back to `()`).
    diverging_vars: RefCell<Vec<Ty>>,
    /// The function's own `impl Trait` return types: what each stands for (a variable
    /// until inferred), by index.
    opaques: RefCell<Vec<(u32, Ty)>>,
    /// Blocks with items (`use` in a function body) around the expression being checked,
    /// innermost last: their traits are in scope too.
    block_scopes: RefCell<Vec<hyprc_hir::DefId>>,
    /// Traits usable for method calls here.
    pub traits_in_scope: Vec<DefId>,
}

pub fn check_body(tcx: &TyCtxt<'_>, body_id: BodyId) -> TypeckResults {
    let body = tcx.hir.body(body_id);
    let owner = body.owner;
    let env = ParamEnv::for_item(tcx, owner);
    let mut traits_in_scope = tcx
        .hir
        .traits_in_scope
        .get(&body.scope)
        .cloned()
        .unwrap_or_default();
    // Traits bounding the generic parameters are callable too.
    for p in &env.preds {
        if let Predicate::Trait(t) = p
            && !traits_in_scope.contains(&t.def)
        {
            traits_in_scope.push(t.def);
        }
    }
    // The trait being implemented or defined around the body is in scope (as in rustc):
    // `"…".fmt(f)` in `impl fmt::Display for E` needs no `use fmt::Display`.
    let mut cur = Some(owner);
    while let Some(d) = cur {
        match tcx.hir.def_kind(d) {
            hyprc_hir::DefKind::Impl { of_trait: true } => {
                if let Some(tr) = tcx.impl_trait_ref(d)
                    && !traits_in_scope.contains(&tr.def)
                {
                    traits_in_scope.push(tr.def);
                }
                break;
            }
            hyprc_hir::DefKind::Trait => {
                if !traits_in_scope.contains(&d) {
                    traits_in_scope.push(d);
                }
                break;
            }
            hyprc_hir::DefKind::Impl { .. } | hyprc_hir::DefKind::Mod => break,
            _ => cur = tcx.hir.parent(d),
        }
    }
    let fcx = FnCtxt {
        tcx,
        body,
        body_id,
        owner,
        infcx: InferCtxt::new(),
        env,
        r: RefCell::new(TypeckResults {
            expr_tys: vec![Ty::ERROR; body.exprs.len()],
            pat_tys: vec![Ty::ERROR; body.pats.len()],
            local_tys: vec![Ty::ERROR; body.locals.len()],
            closures: vec![None; body.closures.len()],
            ..TypeckResults::default()
        }),
        obligations: RefCell::new(Vec::new()),
        ret_tys: RefCell::new(Vec::new()),
        loops: RefCell::new((0..body.loops.len()).map(|_| None).collect()),
        diverges: Cell::new(false),
        in_unsafe: Cell::new(0),
        closure_info: RefCell::new(vec![None; body.closures.len()]),
        diverging_vars: RefCell::new(Vec::new()),
        opaques: RefCell::new(Vec::new()),
        block_scopes: RefCell::new(Vec::new()),
        traits_in_scope,
    };
    fcx.check();
    fcx.writeback()
}

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn emit(&self, d: Diag) {
        self.r.borrow_mut().tainted_by_errors = true;
        self.tcx.emit(d);
    }

    pub(crate) fn err(&self, span: Span, msg: impl Into<String>) {
        self.emit(Diag::error(msg).span(span, ""));
    }

    pub(crate) fn tainted(&self) -> bool {
        self.r.borrow().tainted_by_errors
    }

    pub(crate) fn solver(&self) -> Solver<'_, 'h> {
        Solver::new(self.tcx, &self.infcx, &self.env, self)
    }

    pub(crate) fn next_ty_var(&self, span: Span) -> Ty {
        self.infcx.new_ty_var(span)
    }

    pub(crate) fn resolve(&self, t: Ty) -> Ty {
        self.infcx.resolve_vars(t)
    }

    pub(crate) fn shallow(&self, t: Ty) -> Ty {
        self.infcx.shallow_resolve(t)
    }

    /// Resolves what can be resolved, normalizing projections, and retries pending
    /// obligations if the type is still a variable.
    pub(crate) fn structurally_resolve(&self, t: Ty) -> Ty {
        let t = self.normalize(self.shallow(t));
        let t = self.shallow(t);
        if t.is_ty_var() {
            self.select_where_possible();
            return self.shallow(t);
        }
        t
    }

    /// The traits whose methods are callable here: the body's, and those its innermost
    /// block with items imports.
    pub(crate) fn traits_here(&self) -> Vec<hyprc_hir::DefId> {
        let mut traits = self.traits_in_scope.clone();
        if let Some(b) = self.block_scopes.borrow().last()
            && let Some(more) = self.tcx.hir.traits_in_scope.get(b)
        {
            for &t in more {
                if !traits.contains(&t) {
                    traits.push(t);
                }
            }
        }
        traits
    }

    pub(crate) fn register(&self, p: Predicate, span: Span) {
        self.obligations.borrow_mut().push((p, span));
    }

    /// Replaces the body owner's own opaque types in `t` with inference variables bound by
    /// what the opaque type declares (`-> impl FnMut(u8)`: `?T: FnMut<(u8,)>`).
    fn instantiate_opaques(&self, t: Ty, span: Span) -> Ty {
        struct Inst<'f, 'a, 'h> {
            fcx: &'f FnCtxt<'a, 'h>,
            span: Span,
        }
        impl crate::fold::TypeFolder for Inst<'_, '_, '_> {
            fn fold_ty(&mut self, t: Ty) -> Ty {
                if let TyKind::Alias(AliasKind::Opaque, a) = *t.kind()
                    && a.def == self.fcx.owner
                {
                    if let Some(&(_, v)) = self
                        .fcx
                        .opaques
                        .borrow()
                        .iter()
                        .find(|(i, _)| *i == a.index)
                    {
                        return v;
                    }
                    let v = self.fcx.next_ty_var(self.span);
                    self.fcx.opaques.borrow_mut().push((a.index, v));
                    // The bounds mention the opaque type itself, now the variable (it's
                    // recorded above), and maybe nested ones (`impl Iterator<Item = impl Ord>`).
                    for p in self.fcx.tcx.opaque_bounds(a.def, a.index) {
                        let p = crate::fold::fold_predicate(p.subst(a.args), self);
                        self.fcx.register(p, self.span);
                    }
                    return v;
                }
                if !t.has_aliases() {
                    return t;
                }
                crate::fold::super_fold_ty(t, self)
            }
        }
        if !t.has_aliases() {
            return t;
        }
        crate::fold::TypeFolder::fold_ty(&mut Inst { fcx: self, span }, t)
    }

    pub(crate) fn register_trait(&self, def: DefId, args: Args, span: Span) {
        self.register(Predicate::Trait(TraitRef::new(def, args)), span);
    }

    /// Requires `T: Sized` (if the lang item exists).
    pub(crate) fn require_sized(&self, t: Ty, span: Span) {
        if let Some(s) = self.tcx.lang_item("sized") {
            self.register_trait(s, Args::from_tys(&[t]), span);
        }
    }

    /// Normalizes projections (registering obligations for those not decidable yet).
    pub(crate) fn normalize(&self, t: Ty) -> Ty {
        if !t.has_aliases() {
            return t;
        }
        let mut pending = Vec::new();
        let n = self.solver().normalize(self.resolve(t), &mut pending);
        for p in pending {
            self.register(p, Span::DUMMY);
        }
        n
    }

    pub(crate) fn normalize_sig(&self, sig: FnSig) -> FnSig {
        let tys: Vec<Ty> = sig
            .inputs_and_output
            .as_slice()
            .iter()
            .map(|&t| self.normalize(t))
            .collect();
        FnSig {
            inputs_and_output: TyList::new(&tys),
            ..sig
        }
    }

    /// `expected` and `actual` must be the same type; reports a mismatch.
    pub(crate) fn demand_eq(&self, span: Span, expected: Ty, actual: Ty) -> bool {
        match self.infcx.unify(expected, actual) {
            Ok(()) => true,
            Err(e) => {
                self.report_mismatch(span, expected, actual, e);
                false
            }
        }
    }

    pub(crate) fn report_mismatch(&self, span: Span, expected: Ty, actual: Ty, _e: TypeError) {
        let (exp, act) = (self.resolve(expected), self.resolve(actual));
        if exp.has_errors() || act.has_errors() {
            self.r.borrow_mut().tainted_by_errors = true;
            return;
        }
        self.emit(
            Diag::error("mismatched types")
                .code("E0308")
                .span(span, format!("expected `{exp}`, found `{act}`")),
        );
    }

    // ---------------------------------------------------------------------------------------
    // Obligations

    /// Processes the obligation queue until nothing more can be decided.
    pub(crate) fn select_where_possible(&self) {
        let mut rounds = 0;
        loop {
            rounds += 1;
            let pending = std::mem::take(&mut *self.obligations.borrow_mut());
            if pending.is_empty() || rounds > 64 {
                *self.obligations.borrow_mut() = pending;
                return;
            }
            let n = pending.len();
            let mut progress = false;
            let mut keep = Vec::new();
            for (p, span) in pending {
                match self.process_obligation(p, span) {
                    ObligationResult::Done(nested) => {
                        progress = true;
                        for n in nested {
                            self.obligations.borrow_mut().push((n, span));
                        }
                    }
                    ObligationResult::Stuck => keep.push((p, span)),
                    ObligationResult::Error => {
                        progress = true;
                        self.report_unsatisfied(p, span);
                    }
                }
            }
            let mut obligations = self.obligations.borrow_mut();
            let added = !obligations.is_empty();
            keep.append(&mut obligations);
            *obligations = keep;
            if !progress && !added {
                return;
            }
            if obligations.len() == n && !added && !progress {
                return;
            }
        }
    }

    fn process_obligation(&self, p: Predicate, span: Span) -> ObligationResult {
        match p {
            Predicate::Trait(tr) => {
                let solver = self.solver();
                let r = self.infcx.commit_if_ok(|| match solver.select(tr) {
                    SelectResult::Ok(sel) => Ok(Ok(sel.nested)),
                    SelectResult::Ambiguous => Err(true),
                    SelectResult::Err => Err(false),
                });
                match r {
                    Ok(Ok(nested)) => ObligationResult::Done(nested),
                    Ok(Err(())) => ObligationResult::Error,
                    Err(true) => ObligationResult::Stuck,
                    Err(false) => ObligationResult::Error,
                }
            }
            Predicate::Projection(alias, ty) => {
                let solver = self.solver();
                match solver.project(alias) {
                    Projected::Normalized(t, nested) => {
                        let mut pending = Vec::new();
                        let t = solver.normalize(t, &mut pending);
                        // The other side in normal form too (a variable may hold an
                        // unnormalized projection).
                        let ty = solver.normalize_keep(self.resolve(ty));
                        if self.infcx.unify(t, ty).is_err() {
                            self.report_mismatch(span, ty, t, TypeError::Mismatch(ty, t));
                        }
                        let mut all = nested;
                        all.extend(pending);
                        ObligationResult::Done(all)
                    }
                    Projected::Rigid => {
                        let a = Ty::new(TyKind::Alias(AliasKind::Projection, alias));
                        let ty = solver.normalize_keep(self.resolve(ty));
                        let _ = self.infcx.unify(a, ty);
                        ObligationResult::Done(Vec::new())
                    }
                    Projected::Ambiguous => ObligationResult::Stuck,
                    Projected::Error => ObligationResult::Error,
                }
            }
            Predicate::NegTrait(_) | Predicate::MaybeSized(_) => ObligationResult::Done(Vec::new()),
        }
    }

    pub(crate) fn evaluate(&self, p: Predicate) -> Eval {
        self.solver().evaluate(p)
    }

    fn report_unsatisfied(&self, p: Predicate, span: Span) {
        if self.tainted() {
            // After another error, unsatisfied bounds are usually its consequence.
            let resolved = match p {
                Predicate::Trait(t) => self
                    .infcx
                    .resolve_args(t.args)
                    .as_slice()
                    .iter()
                    .any(|a| a.as_ty().is_some_and(|t| t.has_errors())),
                _ => false,
            };
            if resolved {
                return;
            }
        }
        match p {
            Predicate::Trait(tr) => {
                let tr = self.infcx.resolve_trait_ref(tr);
                let self_ty = tr.self_ty();
                if self_ty.has_errors() {
                    return;
                }
                // `Trait<A, B>`: the arguments after `Self`.
                let mut trait_name = self.tcx.def_path(tr.def);
                let rest: Vec<String> = tr
                    .args
                    .as_slice()
                    .iter()
                    .skip(1)
                    .map(|a| match a {
                        GenericArg::Ty(t) => t.to_string(),
                        GenericArg::Const(c) => format!("{c:?}"),
                    })
                    .collect();
                if !rest.is_empty() {
                    trait_name = format!("{trait_name}<{}>", rest.join(", "));
                }
                let msg = if Some(tr.def) == self.tcx.lang_item("sized") {
                    format!(
                        "the size for values of type `{self_ty}` cannot be known at compilation time"
                    )
                } else {
                    format!("the trait bound `{self_ty}: {trait_name}` is not satisfied")
                };
                let code = if Some(tr.def) == self.tcx.lang_item("sized") {
                    "E0277"
                } else {
                    "E0277"
                };
                self.emit(Diag::error(msg).code(code).span(
                    span,
                    format!("the trait `{trait_name}` is not implemented for `{self_ty}`"),
                ));
            }
            Predicate::Projection(alias, ty) => {
                let ty = self.resolve(ty);
                self.emit(
                    Diag::error(format!(
                        "type mismatch resolving `{} == {ty}`",
                        self.tcx.def_path(alias.def)
                    ))
                    .code("E0271")
                    .span(span, ""),
                );
            }
            _ => {}
        }
    }

    // ---------------------------------------------------------------------------------------
    // The body

    fn check(&self) {
        let body = self.body;
        let item = self.tcx.hir.get_item(self.owner);
        let is_unsafe_fn =
            matches!(item.map(|i| &i.kind), Some(hir::ItemKind::Fn(f)) if f.sig.safety_unsafe);
        if is_unsafe_fn {
            self.in_unsafe.set(1);
        }
        match body.kind {
            hir::BodyKind::Fn => {
                let sig = self.normalize_sig(self.tcx.fn_sig(self.owner));
                // The function defines its `impl Trait` return types: inferred here.
                let ret = self.instantiate_opaques(sig.output(), body.span);
                self.ret_tys.borrow_mut().push(ret);
                for (i, &p) in body.params.iter().enumerate() {
                    let ty = sig.inputs().get(i).copied().unwrap_or(Ty::ERROR);
                    self.check_pat_top(p, ty, true);
                    let allow_unsized = self.tcx.hir.has_feature("unsized_fn_params")
                        || self.tcx.hir.has_feature("unsized_locals")
                        || self.tcx.hir.def_names.get(self.owner.0 as usize)
                            == Some(&hyprc_span::Symbol::intern("forget_unsized"));
                    if !allow_unsized {
                        self.require_sized(ty, body.pat(p).span);
                    }
                }
                self.check_expr_coercible_to(body.value, ret);
            }
            hir::BodyKind::Const | hir::BodyKind::Static => {
                let ty = self.normalize(self.tcx.type_of(self.owner));
                self.ret_tys.borrow_mut().push(ty);
                self.check_expr_coercible_to(body.value, ty);
            }
            hir::BodyKind::AnonConst => {
                // The expected type isn't known here (an array length is `usize`, a const
                // argument has its parameter's type): `usize` when nothing says otherwise.
                self.ret_tys.borrow_mut().push(Ty::USIZE);
                let ty = self.check_expr_with(body.value, Expectation::None);
                let ty = self.shallow(ty);
                if ty.is_ty_var() || matches!(ty.kind(), TyKind::Infer(InferTy::IntVar(_))) {
                    let _ = self.infcx.unify(ty, Ty::USIZE);
                }
            }
        }
        self.select_where_possible();
        self.analyze_closures();
        self.select_where_possible();
        self.fallback();
        self.select_where_possible();
        self.check_casts();
        self.select_where_possible();
        self.report_ambiguities();
    }

    /// Integer variables default to `i32`, floats to `f64`, `!`-variables to `()`.
    fn fallback(&self) {
        self.infcx.default_numeric_vars();
        for &v in self.diverging_vars.borrow().iter() {
            if let TyKind::Infer(InferTy::TyVar(n)) = *self.shallow(v).kind() {
                self.infcx.force_ty_var(n, Ty::UNIT);
            }
        }
    }

    fn report_ambiguities(&self) {
        let pending = std::mem::take(&mut *self.obligations.borrow_mut());
        for (p, span) in pending {
            if self.tainted() {
                break;
            }
            match p {
                Predicate::Trait(tr) => {
                    let tr = self.infcx.resolve_trait_ref(tr);
                    if tr.self_ty().has_infer() {
                        self.emit(
                            Diag::error("type annotations needed")
                                .code("E0282")
                                .span(span, format!("cannot infer type: {:?}", tr)),
                        );
                    } else {
                        self.report_unsatisfied(p, span);
                    }
                }
                Predicate::Projection(..) => {}
                _ => {}
            }
        }
    }

    pub(crate) fn enter_unsafe<R>(&self, f: impl FnOnce() -> R) -> R {
        self.in_unsafe.set(self.in_unsafe.get() + 1);
        let r = f();
        self.in_unsafe.set(self.in_unsafe.get() - 1);
        r
    }

    pub(crate) fn require_unsafe(&self, span: Span, what: &str) {
        if self.in_unsafe.get() == 0 {
            self.emit(
                Diag::error(format!(
                    "{what} is unsafe and requires unsafe function or block"
                ))
                .code("E0133")
                .span(span, what.to_string()),
            );
        }
    }

    // ---------------------------------------------------------------------------------------
    // Writeback

    fn writeback(self) -> TypeckResults {
        let mut r = self.r.into_inner();
        let infcx = &self.infcx;
        r.opaque_hidden = self
            .opaques
            .borrow()
            .iter()
            .map(|&(i, v)| (i, erase_infer(infcx.resolve_vars(v))))
            .collect();
        let mut unresolved_reported = r.tainted_by_errors;
        let mut fix = |t: Ty, span: Span, r_tainted: &mut bool| -> Ty {
            let t = infcx.resolve_vars(t);
            if t.has_infer() {
                if !unresolved_reported && !*r_tainted {
                    self.tcx.emit(
                        Diag::error("type annotations needed")
                            .code("E0282")
                            .span(span, format!("cannot infer type in writeback: {:?}", t)),
                    );
                    unresolved_reported = true;
                    *r_tainted = true;
                }
                return erase_infer(t);
            }
            t
        };
        let mut tainted = r.tainted_by_errors;
        for (i, t) in r.expr_tys.iter_mut().enumerate() {
            *t = fix(*t, self.body.exprs[i].span, &mut tainted);
        }
        for (i, t) in r.pat_tys.iter_mut().enumerate() {
            *t = fix(*t, self.body.pats[i].span, &mut tainted);
        }
        for (i, t) in r.local_tys.iter_mut().enumerate() {
            *t = fix(*t, self.body.locals[i].span, &mut tainted);
        }
        for adjs in r.adjustments.values_mut() {
            for a in adjs.iter_mut() {
                a.target = erase_infer(infcx.resolve_vars(a.target));
                if let Adjust::Deref(Some(d)) = &mut a.kind {
                    d.args = infcx.resolve_args(d.args);
                }
            }
        }
        for tys in r.pat_adjustments.values_mut() {
            for t in tys.iter_mut() {
                *t = erase_infer(infcx.resolve_vars(*t));
            }
        }
        for a in r.node_args.values_mut() {
            *a = erase_args(infcx.resolve_args(*a));
        }
        for c in r
            .type_dependent
            .values_mut()
            .chain(r.overloaded.values_mut())
        {
            c.args = erase_args(infcx.resolve_args(c.args));
        }
        for (_, from, to) in r.casts.iter_mut() {
            *from = erase_infer(infcx.resolve_vars(*from));
            *to = erase_infer(infcx.resolve_vars(*to));
        }
        for (_, a) in r.pat_consts.values_mut() {
            *a = erase_args(infcx.resolve_args(*a));
        }
        for (container, steps) in r.offset_of.values_mut() {
            *container = erase_infer(infcx.resolve_vars(*container));
            for (_, _, t) in steps.iter_mut() {
                *t = erase_infer(infcx.resolve_vars(*t));
            }
        }
        let infos = self.closure_info.borrow();
        for (i, c) in r.closures.iter_mut().enumerate() {
            if let Some(c) = c {
                let tys: Vec<Ty> = c
                    .sig
                    .inputs_and_output
                    .as_slice()
                    .iter()
                    .map(|&t| erase_infer(infcx.resolve_vars(t)))
                    .collect();
                c.sig = FnSig {
                    inputs_and_output: TyList::new(&tys),
                    ..c.sig
                };
                c.ty = erase_infer(infcx.resolve_vars(c.ty));
                for u in c.upvars.iter_mut() {
                    u.ty = erase_infer(infcx.resolve_vars(u.ty));
                }
            } else if let Some((sig, kind, ty)) = infos[i] {
                *c = Some(ClosureResult {
                    kind: kind.unwrap_or(ClosureKind::Fn),
                    sig,
                    upvars: Vec::new(),
                    ty: erase_infer(infcx.resolve_vars(ty)),
                });
            }
        }
        r.tainted_by_errors |= tainted;
        r
    }
}

enum ObligationResult {
    Done(Vec<Predicate>),
    Stuck,
    Error,
}

/// Unresolved variables after reporting become errors.
fn erase_infer(t: Ty) -> Ty {
    if !t.has_infer() {
        return t;
    }
    use crate::fold::TypeFolder;
    struct E;
    impl TypeFolder for E {
        fn fold_ty(&mut self, t: Ty) -> Ty {
            if !t.has_infer() {
                return t;
            }
            match t.kind() {
                TyKind::Infer(InferTy::IntVar(_)) => Ty::I32,
                TyKind::Infer(InferTy::FloatVar(_)) => Ty::F64,
                TyKind::Infer(_) => Ty::ERROR,
                _ => crate::fold::super_fold_ty(t, self),
            }
        }

        fn fold_const(&mut self, c: Const) -> Const {
            match c.kind() {
                ConstKind::Infer(_) => Const::error(c.ty()),
                _ => crate::fold::super_fold_const(c, self),
            }
        }
    }
    E.fold_ty(t)
}

fn erase_args(a: Args) -> Args {
    crate::fold::fold_args(a, &mut ArgsEraser)
}

struct ArgsEraser;

impl crate::fold::TypeFolder for ArgsEraser {
    fn fold_ty(&mut self, t: Ty) -> Ty {
        erase_infer(t)
    }

    fn fold_const(&mut self, c: Const) -> Const {
        match c.kind() {
            ConstKind::Infer(_) => Const::error(c.ty()),
            _ => c,
        }
    }
}

impl ClosureInfo for FnCtxt<'_, '_> {
    fn closure_sig(&self, c: ClosureRef, args: Args) -> Option<FnSig> {
        if c.owner == self.owner && c.body == self.body_id.0 {
            return self
                .closure_info
                .borrow()
                .get(c.index as usize)
                .and_then(|x| x.map(|(s, _, _)| s));
        }
        crate::traits::closure_sig_from_args(args)
    }

    fn closure_kind(&self, c: ClosureRef, args: Args) -> Option<ClosureKind> {
        if c.owner == self.owner && c.body == self.body_id.0 {
            if self
                .closure_info
                .borrow()
                .get(c.index as usize)
                .and_then(|x| x.and_then(|(_, k, _)| k))
                .is_none()
            {
                self.analyze_closure(c.index as usize);
            }
            return self
                .closure_info
                .borrow()
                .get(c.index as usize)
                .and_then(|x| x.and_then(|(_, k, _)| k));
        }
        crate::traits::closure_kind_from_args(args)
    }

    fn closure_upvars(&self, c: ClosureRef, args: Args) -> Option<Vec<Ty>> {
        if c.owner == self.owner && c.body == self.body_id.0 {
            if self
                .r
                .borrow()
                .closures
                .get(c.index as usize)
                .and_then(|x| x.as_ref())
                .is_none()
            {
                self.analyze_closure(c.index as usize);
            }
            return self
                .r
                .borrow()
                .closures
                .get(c.index as usize)
                .and_then(|x| {
                    x.as_ref().map(|c| {
                        c.upvars
                            .iter()
                            .map(|u| match u.kind {
                                CaptureKind::ByValue => self.resolve(u.ty),
                                CaptureKind::ByRef(m) => Ty::reference(self.resolve(u.ty), m),
                            })
                            .collect()
                    })
                });
        }
        let s = args.as_slice();
        let last = self.shallow(s.last()?.as_ty()?);
        match last.kind() {
            TyKind::Tuple(ts) => Some(ts.as_slice().to_vec()),
            _ if last.is_unit() => Some(Vec::new()),
            _ => None,
        }
    }
}
