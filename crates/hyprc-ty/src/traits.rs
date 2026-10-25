//! Trait solving: which impl (or where-clause, or built-in rule) proves `T: Trait`, and
//! what associated types normalize to.
//!
//! Selection assembles candidates (where-clauses in scope, impls, built-in impls, the
//! traits of a `dyn` type), drops the ones that don't unify, and confirms the one left,
//! producing nested obligations (the impl's where-clauses). Several candidates left is
//! ambiguity: the caller retries once more types are known.

use crate::TyCtxt;
use crate::collect::ClosureKind;
use crate::fold::TypeFolder;
use crate::infer::InferCtxt;
use crate::ty::*;
use hyprc_hir::DefId;
use hyprc_span::{Span, Symbol, kw};

/// Where-clauses in scope, elaborated with supertraits.
#[derive(Clone, Debug, Default)]
pub struct ParamEnv {
    pub def: Option<DefId>,
    pub preds: Vec<Predicate>,
}

impl ParamEnv {
    pub fn empty() -> ParamEnv {
        ParamEnv {
            def: None,
            preds: Vec::new(),
        }
    }

    /// The where-clauses of an item, with what supertraits imply, normalized
    /// (`F: FnMut(<Self as Iterator>::Item)` in `impl Iterator for Map<I, F>` is about
    /// `I::Item`). Computed once per item.
    pub fn for_item(tcx: &TyCtxt<'_>, def: DefId) -> std::sync::Arc<ParamEnv> {
        tcx.q.param_env[def.0 as usize]
            .get_or_init(|| {
                let mut preds: Vec<Predicate> = tcx.predicates_of(def).iter().copied().collect();
                elaborate(tcx, &mut preds);
                let env = ParamEnv {
                    def: Some(def),
                    preds,
                };
                if !env.preds.iter().any(pred_has_aliases) {
                    return std::sync::Arc::new(env);
                }
                let infcx = InferCtxt::new();
                let solver = Solver::new(tcx, &infcx, &env, &NoClosures);
                // Variables of this temporary context must not leak into the environment:
                // resolved, or the predicate stays as written.
                let mut pending = Vec::new();
                let normalized: Vec<Predicate> = env
                    .preds
                    .iter()
                    .map(|&p| solver.normalize_predicate(p, &mut pending))
                    .collect();
                // What a projection's value depends on (`type Item = B` with `B` fixed by the
                // impl's `F: FnMut(I::Item) -> Option<B>`): worked out from the same
                // where-clauses.
                for _ in 0..8 {
                    if pending.is_empty() {
                        break;
                    }
                    let mut next = Vec::new();
                    for o in pending.drain(..) {
                        match o {
                            Predicate::Trait(tr) => {
                                if let SelectResult::Ok(sel) = solver.select(tr) {
                                    next.extend(sel.nested);
                                }
                            }
                            Predicate::Projection(a, t) => {
                                if let Projected::Normalized(n, nested) = solver.project(a) {
                                    let _ = infcx.unify(n, t);
                                    next.extend(nested);
                                }
                            }
                            _ => {}
                        }
                    }
                    pending = next;
                }
                let preds: Vec<Predicate> = env
                    .preds
                    .iter()
                    .zip(normalized)
                    .map(|(&p, n)| {
                        let n = match n {
                            Predicate::Trait(t) => Predicate::Trait(infcx.resolve_trait_ref(t)),
                            Predicate::Projection(a, t) => Predicate::Projection(
                                AliasTy {
                                    args: infcx.resolve_args(a.args),
                                    ..a
                                },
                                infcx.resolve_vars(t),
                            ),
                            other => other,
                        };
                        if pred_has_infer(&n) { p } else { n }
                    })
                    .collect();
                // `HYPRC_DEBUG_ENV=<part of a path>`: show what an item's where-clauses become.
                if let Ok(filter) = std::env::var("HYPRC_DEBUG_ENV")
                    && tcx.def_path(def).contains(&filter)
                {
                    eprintln!("param env of `{}`:", tcx.def_path(def));
                    let show = |p: &Predicate| pred_to_string(tcx, *p);
                    for (before, after) in env.preds.iter().zip(&preds) {
                        eprintln!("  {}\n    => {}", show(before), show(after));
                    }
                }
                std::sync::Arc::new(ParamEnv {
                    def: Some(def),
                    preds,
                })
            })
            .clone()
    }
}

/// A predicate for debugging output: `Trait<Self, Args…>`, `Assoc<Self, Args…> == T`.
pub fn pred_to_string(tcx: &TyCtxt<'_>, p: Predicate) -> String {
    let args = |a: Args| {
        a.as_slice()
            .iter()
            .map(|g| match g {
                GenericArg::Ty(t) => t.to_string(),
                GenericArg::Const(c) => format!("{c:?}"),
            })
            .collect::<Vec<_>>()
            .join(", ")
    };
    match p {
        Predicate::Trait(t) => format!("{}<{}>", tcx.def_path(t.def), args(t.args)),
        Predicate::Projection(a, t) => format!("{}<{}> == {t}", tcx.def_path(a.def), args(a.args)),
        other => format!("{other:?}"),
    }
}

fn debug_solver() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("HYPRC_DEBUG_SOLVER").is_ok())
}

/// The type variables in a type.
fn ty_vars(t: Ty) -> Vec<u32> {
    struct Collect(Vec<u32>);
    impl TypeFolder for Collect {
        fn fold_ty(&mut self, t: Ty) -> Ty {
            if let TyKind::Infer(InferTy::TyVar(v)) = *t.kind() {
                self.0.push(v);
                return t;
            }
            if !t.has_infer() {
                return t;
            }
            crate::fold::super_fold_ty(t, self)
        }
    }
    let mut c = Collect(Vec::new());
    c.fold_ty(t);
    c.0
}

fn pred_has_infer(p: &Predicate) -> bool {
    let args_have = |a: Args| {
        a.as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| t.has_infer()))
    };
    match *p {
        Predicate::Trait(tr) => args_have(tr.args),
        Predicate::Projection(a, t) => args_have(a.args) || t.has_infer(),
        _ => false,
    }
}

fn pred_has_aliases(p: &Predicate) -> bool {
    let args_have = |a: Args| {
        a.as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| t.has_aliases()))
    };
    match *p {
        Predicate::Trait(tr) => args_have(tr.args),
        Predicate::Projection(a, t) => args_have(a.args) || t.has_aliases(),
        _ => false,
    }
}

/// Adds supertrait predicates (transitively) and associated-type bounds of traits.
pub fn elaborate(tcx: &TyCtxt<'_>, preds: &mut Vec<Predicate>) {
    let mut i = 0;
    while i < preds.len() {
        if let Predicate::Trait(tr) = preds[i] {
            let trait_self = Ty::param(tcx.generics_of(tr.def).parent_count, kw::SelfUpper);
            for p in tcx.predicates_of(tr.def).iter() {
                // Supertraits: `Self: Super` in the trait's predicates.
                if let Predicate::Trait(sup) = p
                    && sup.def != tr.def
                    && sup.self_ty() == trait_self
                {
                    let sup = Predicate::Trait(sup.subst(tr.args));
                    if !preds.contains(&sup) && preds.len() < 4096 {
                        preds.push(sup);
                    }
                }
                if let Predicate::Projection(a, t) = p
                    && a.args.get(0) == Some(GenericArg::Ty(trait_self))
                {
                    let proj = Predicate::Projection(
                        AliasTy {
                            args: a.args.subst(tr.args),
                            ..*a
                        },
                        t.subst(tr.args),
                    );
                    if !preds.contains(&proj) && preds.len() < 4096 {
                        preds.push(proj);
                    }
                }
            }
        }
        i += 1;
    }
}

#[derive(Clone, Debug)]
pub enum SelectionKind {
    Impl {
        def: DefId,
        args: Args,
    },
    Param,
    Builtin,
    /// The type is `dyn Trait` and the trait is (a supertrait of) its principal.
    Object,
    Closure(ClosureKind),
    FnPointer,
}

#[derive(Clone, Debug)]
pub struct Selection {
    pub kind: SelectionKind,
    pub nested: Vec<Predicate>,
}

#[derive(Clone, Debug)]
pub enum SelectResult {
    Ok(Selection),
    Ambiguous,
    Err,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Eval {
    Holds,
    Ambiguous,
    Fails,
}

#[derive(Clone, Debug)]
enum Candidate {
    Param(TraitRef),
    Impl(DefId),
    Builtin(Vec<Predicate>),
    Object(TraitRef),
    Closure(ClosureKind),
    FnPointer,
}

pub enum Projected {
    Normalized(Ty, Vec<Predicate>),
    Ambiguous,
    /// Can't be normalized (a projection on a type parameter): it stays an alias.
    Rigid,
    Error,
}

/// Closure information the solver needs (signatures and kinds are known to type checking).
pub trait ClosureInfo {
    fn closure_sig(&self, c: ClosureRef, args: Args) -> Option<FnSig>;
    fn closure_kind(&self, c: ClosureRef, args: Args) -> Option<ClosureKind>;
    fn closure_upvars(&self, c: ClosureRef, args: Args) -> Option<Vec<Ty>>;
}

pub struct NoClosures;

impl ClosureInfo for NoClosures {
    fn closure_sig(&self, _: ClosureRef, args: Args) -> Option<FnSig> {
        closure_sig_from_args(args)
    }
    fn closure_kind(&self, _: ClosureRef, args: Args) -> Option<ClosureKind> {
        closure_kind_from_args(args)
    }
    fn closure_upvars(&self, _: ClosureRef, args: Args) -> Option<Vec<Ty>> {
        closure_upvars_from_args(args)
    }
}

/// Closure types carry `[parent args…, kind, sig, upvars]`: the last three arguments.
pub fn closure_sig_from_args(args: Args) -> Option<FnSig> {
    let s = args.as_slice();
    match s.get(s.len().checked_sub(2)?)?.as_ty()?.kind() {
        TyKind::FnPtr(sig) => Some(*sig),
        _ => None,
    }
}

pub fn closure_kind_from_args(args: Args) -> Option<ClosureKind> {
    let s = args.as_slice();
    match s.get(s.len().checked_sub(3)?)?.as_ty()? {
        t if t == Ty::I8 => Some(ClosureKind::Fn),
        t if t == Ty::I16 => Some(ClosureKind::FnMut),
        t if t == Ty::I32 => Some(ClosureKind::FnOnce),
        _ => None,
    }
}

pub fn closure_kind_ty(k: ClosureKind) -> Ty {
    match k {
        ClosureKind::Fn => Ty::I8,
        ClosureKind::FnMut => Ty::I16,
        ClosureKind::FnOnce => Ty::I32,
    }
}

pub fn closure_upvars_from_args(args: Args) -> Option<Vec<Ty>> {
    let s = args.as_slice();
    let last = s.last()?.as_ty()?;
    match last.kind() {
        TyKind::Tuple(ts) => Some(ts.as_slice().to_vec()),
        _ if last.is_unit() => Some(Vec::new()),
        _ => None,
    }
}

pub struct Solver<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    pub infcx: &'a InferCtxt,
    pub env: &'a ParamEnv,
    pub closures: &'a dyn ClosureInfo,
    /// Nesting of selection, evaluation and projection, whichever path led here: past
    /// [`MAX_NESTING`] the answer is "ambiguous" (rustc's overflow) instead of a stack
    /// overflow.
    nesting: std::cell::Cell<u32>,
}

const MAX_DEPTH: u32 = 64;
const MAX_NESTING: u32 = 256;

/// Leaves one level of solver nesting when dropped.
struct Nest<'s>(&'s std::cell::Cell<u32>);

impl Drop for Nest<'_> {
    fn drop(&mut self) {
        self.0.set(self.0.get() - 1);
    }
}

impl<'a, 'h> Solver<'a, 'h> {
    pub fn new(
        tcx: &'a TyCtxt<'h>,
        infcx: &'a InferCtxt,
        env: &'a ParamEnv,
        closures: &'a dyn ClosureInfo,
    ) -> Self {
        Solver {
            tcx,
            infcx,
            env,
            closures,
            nesting: std::cell::Cell::new(0),
        }
    }

    fn lang(&self, name: &str) -> Option<DefId> {
        self.tcx.lang_item(name)
    }

    fn is_lang(&self, def: DefId, name: &str) -> bool {
        self.lang(name) == Some(def)
    }

    /// Fresh inference variables for an item's generic parameters.
    pub fn fresh_args(&self, def: DefId) -> Args {
        let params = self.tcx.all_params(def);
        let v: Vec<GenericArg> = params
            .iter()
            .map(|p| match p.kind {
                crate::collect::GenericParamDefKind::Type { .. } => {
                    GenericArg::Ty(self.infcx.new_ty_var(Span::DUMMY))
                }
                crate::collect::GenericParamDefKind::Const { .. } => {
                    let ty = self.tcx.const_param_ty(def, p.index);
                    GenericArg::Const(self.infcx.new_const_var(ty))
                }
            })
            .collect();
        Args::new(&v)
    }

    // ---------------------------------------------------------------------------------------
    // Selection

    pub fn select(&self, tr: TraitRef) -> SelectResult {
        self.select_depth(tr, 0)
    }

    /// Works on obligations right away (a few rounds), for their effect on inference
    /// variables: projections unify with their values, selections bring their own.
    pub fn solve_now(&self, mut preds: Vec<Predicate>) {
        for _ in 0..4 {
            if preds.is_empty() {
                return;
            }
            let mut next = Vec::new();
            for p in preds {
                match p {
                    Predicate::Trait(tr) => {
                        if let SelectResult::Ok(sel) = self.select(tr) {
                            next.extend(sel.nested);
                        }
                    }
                    Predicate::Projection(a, t) => {
                        if let Projected::Normalized(n, nested) = self.project(a) {
                            let _ = self.infcx.unify(n, t);
                            next.extend(nested);
                        }
                    }
                    _ => {}
                }
            }
            preds = next;
        }
    }

    /// Enters one level of nesting, or `None` past the limit.
    fn nest(&self) -> Option<Nest<'_>> {
        let n = self.nesting.get();
        if n >= MAX_NESTING {
            return None;
        }
        self.nesting.set(n + 1);
        Some(Nest(&self.nesting))
    }

    fn has_unresolved_projection(&self, t: Ty) -> bool {
        if !t.has_aliases() {
            return false;
        }
        let t = self.infcx.shallow_resolve(t);
        if !t.has_infer() {
            return false;
        }
        match *t.kind() {
            TyKind::Alias(AliasKind::Projection, _) => true,
            TyKind::Tuple(ts) => ts
                .as_slice()
                .iter()
                .any(|&f| self.has_unresolved_projection(f)),
            TyKind::Ref(inner, _) | TyKind::RawPtr(inner, _) => {
                self.has_unresolved_projection(inner)
            }
            _ => false,
        }
    }

    fn select_depth(&self, tr: TraitRef, depth: u32) -> SelectResult {
        if depth > MAX_DEPTH {
            return SelectResult::Ambiguous;
        }
        let Some(_nest) = self.nest() else {
            return SelectResult::Ambiguous;
        };
        let tr = self.normalize_trait_ref(self.infcx.resolve_trait_ref(tr));
        let self_ty = self.infcx.shallow_resolve(tr.self_ty());
        if self_ty.is_error()
            || tr
                .args
                .as_slice()
                .iter()
                .any(|a| a.as_ty().is_some_and(|t| t.is_error()))
        {
            return SelectResult::Ok(Selection {
                kind: SelectionKind::Builtin,
                nested: Vec::new(),
            });
        }
        // An unknown self type could be anything: ambiguous without looking (as in rustc;
        // assembling every impl here and evaluating each is exponential).
        if self_ty.is_ty_var() {
            return SelectResult::Ambiguous;
        }
        // A projection on unknown types (`<?X as IntoIterator>::IntoIter`) stands for a type
        // not known yet either.
        if tr
            .args
            .as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| self.has_unresolved_projection(t)))
        {
            return SelectResult::Ambiguous;
        }
        let mut candidates = self.assemble(tr, self_ty);
        if candidates.is_empty() {
            return SelectResult::Err;
        }
        // Where-clauses win over impls (rustc's winnowing), when they apply at all.
        if candidates.iter().any(|c| matches!(c, Candidate::Param(_))) {
            candidates.retain(|c| matches!(c, Candidate::Param(_)));
            // The same where-clause twice is one candidate.
            let mut uniq: Vec<Candidate> = Vec::new();
            for c in candidates {
                if let Candidate::Param(p) = &c
                    && uniq.iter().any(|u| matches!(u, Candidate::Param(q) if self.infcx.resolve_trait_ref(*q) == self.infcx.resolve_trait_ref(*p)))
                {
                    continue;
                }
                uniq.push(c);
            }
            candidates = uniq;
        }
        // As in rustc: a built-in answer that needs nothing more wins (`dyn Debug:
        // PointeeSized`), and a `dyn` type's own traits win over impls.
        if candidates.len() > 1 {
            if let Some(i) = candidates
                .iter()
                .position(|c| matches!(c, Candidate::Builtin(n) if n.is_empty()))
            {
                let c = candidates.swap_remove(i);
                candidates = vec![c];
            } else if candidates.iter().any(|c| matches!(c, Candidate::Object(_))) {
                candidates.retain(|c| !matches!(c, Candidate::Impl(_)));
            }
        }
        if candidates.len() > 1 {
            // Several impls: keep those whose where-clauses can still hold.
            // (Specialization below then picks the most specific.)
            candidates.retain(|c| {
                self.infcx.probe(|| match self.confirm(tr, c) {
                    Some((nested, _)) => nested
                        .iter()
                        .all(|p| self.evaluate_depth(*p, depth + 1) != Eval::Fails),
                    None => false,
                })
            });
        }
        // An embedded inference variable can distinguish otherwise separate impls. This is
        // common for arrays: `[T; ?N]: Default` has one impl per supported length, and a later
        // use of the value can still determine `N`. Do not run the quadratic specialization
        // comparison over all of those candidates or reject an empty provisional set before
        // that later constraint has arrived.
        if tr.args.has_infer() && candidates.len() != 1 {
            return SelectResult::Ambiguous;
        }
        // Specialization: of impls that all apply, the one specializing all others.
        if candidates.len() > 1 && candidates.iter().all(|c| matches!(c, Candidate::Impl(_))) {
            let imps: Vec<DefId> = candidates
                .iter()
                .filter_map(|c| {
                    if let Candidate::Impl(d) = c {
                        Some(*d)
                    } else {
                        None
                    }
                })
                .collect();
            if let Some(&best) = imps.iter().find(|&&a| {
                imps.iter().all(|&b| {
                    a == b || (self.tcx.impl_specializes(a, b) && !self.tcx.impl_specializes(b, a))
                })
            }) {
                candidates = vec![Candidate::Impl(best)];
            }
        }
        if self_ty.is_ty_var() && candidates.len() != 1 {
            return SelectResult::Ambiguous;
        }
        match candidates.len() {
            0 => SelectResult::Err,
            1 => {
                let c = candidates.pop().unwrap();
                match self.confirm(tr, &c) {
                    Some((nested, impl_args)) => {
                        let kind = match (&c, impl_args) {
                            (Candidate::Impl(d), Some(args)) => {
                                SelectionKind::Impl { def: *d, args }
                            }
                            _ => self.kind_of(&c),
                        };
                        SelectResult::Ok(Selection { kind, nested })
                    }
                    None => SelectResult::Err,
                }
            }
            _ => SelectResult::Ambiguous,
        }
    }

    fn kind_of(&self, c: &Candidate) -> SelectionKind {
        match c {
            Candidate::Param(_) => SelectionKind::Param,
            Candidate::Impl(d) => SelectionKind::Impl {
                def: *d,
                args: Args::EMPTY,
            },
            Candidate::Builtin(_) => SelectionKind::Builtin,
            Candidate::Object(_) => SelectionKind::Object,
            Candidate::Closure(k) => SelectionKind::Closure(*k),
            Candidate::FnPointer => SelectionKind::FnPointer,
        }
    }

    fn assemble(&self, tr: TraitRef, self_ty: Ty) -> Vec<Candidate> {
        let mut out = Vec::new();
        // Where-clauses.
        for p in &self.env.preds {
            if let Predicate::Trait(p) = p
                && p.def == tr.def
                && self
                    .infcx
                    .probe(|| self.infcx.unify_args(p.args, tr.args).is_ok())
            {
                out.push(Candidate::Param(*p));
            }
        }
        // A projection or opaque type without a value here: what its declaration promises
        // (`type IntoIter: Iterator<Item = Self::Item>`, `-> impl FnMut(u8)`).
        if let TyKind::Alias(kind @ (AliasKind::Projection | AliasKind::Opaque), alias) =
            *self_ty.kind()
        {
            for p in self.alias_bounds(kind, alias) {
                if let Predicate::Trait(b) = p
                    && b.def == tr.def
                    && self
                        .infcx
                        .probe(|| self.infcx.unify_args(b.args, tr.args).is_ok())
                {
                    out.push(Candidate::Param(b));
                }
            }
        }
        // `dyn Trait` implements its principal trait, the supertraits, and its auto traits.
        if let TyKind::Dynamic(preds) = *self_ty.kind() {
            for obj_tr in self.object_traits(self_ty, preds) {
                if obj_tr.def == tr.def
                    && self
                        .infcx
                        .probe(|| self.infcx.unify_args(obj_tr.args, tr.args).is_ok())
                {
                    out.push(Candidate::Object(obj_tr));
                }
            }
        }
        self.assemble_builtin(tr, self_ty, &mut out);
        if matches!(
            self_ty.kind(),
            TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
        ) && out.iter().any(|c| matches!(c, Candidate::Builtin(_)))
        {
            return out;
        }
        // Impls.
        let mut negative = false;
        self.tcx.for_each_relevant_impl(tr.def, self_ty, |imp| {
            let fits = self.infcx.probe(|| {
                let args = self.fresh_args(imp);
                let Some(impl_tr) = self.tcx.impl_trait_ref(imp) else { return false };
                let impl_tr = impl_tr.subst(args);
                if self.infcx.unify_args(impl_tr.args, tr.args).is_ok() {
                    return true;
                }
                if impl_tr.has_aliases() {
                    for (a, b) in impl_tr.args.as_slice().iter().zip(tr.args.as_slice()) {
                        if !a.as_ty().is_some_and(|t| t.has_aliases()) {
                            if match (*a, *b) {
                                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.infcx.unify(x, y).is_err(),
                                (GenericArg::Const(x), GenericArg::Const(y)) => self.infcx.unify_const(x, y).is_err(),
                                _ => true,
                            } {
                                return false;
                            }
                        }
                    }
                    let norm = self.normalize_trait_ref(self.infcx.resolve_trait_ref(impl_tr));
                    if self.infcx.unify_args(norm.args, tr.args).is_ok() {
                        return true;
                    }
                }
                false
            });
            if fits {
                let item = self.tcx.hir.get_item(imp);
                if item.is_some_and(|i| i.attrs.rustc.contains(&hyprc_span::Symbol::intern("rustc_reservation_impl"))) {
                    return;
                }
                let is_neg = matches!(item.map(|i| &i.kind), Some(hyprc_hir::ItemKind::Impl(i)) if i.negative);
                if is_neg {
                    negative = true;
                } else {
                    out.push(Candidate::Impl(imp));
                }
            }
        });
        if negative && !out.iter().any(|c| matches!(c, Candidate::Param(_))) {
            out.retain(|c| !matches!(c, Candidate::Builtin(_)));
        }
        // An auto trait with no impl and no negative impl: structural.
        if !negative && out.is_empty() && self.tcx.is_auto_trait(tr.def) {
            if let Some(nested) = self.auto_trait_components(tr, self_ty) {
                out.push(Candidate::Builtin(nested));
            }
        }
        out
    }

    /// The declared bounds of a projection or opaque type, about it (with its arguments).
    fn alias_bounds(&self, kind: AliasKind, alias: AliasTy) -> Vec<Predicate> {
        let bounds: Vec<Predicate> = match kind {
            AliasKind::Projection => self.tcx.item_bounds(alias.def).iter().copied().collect(),
            AliasKind::Opaque => self.tcx.opaque_bounds(alias.def, alias.index),
            _ => return Vec::new(),
        };
        let mut preds: Vec<Predicate> = bounds.iter().map(|p| p.subst(alias.args)).collect();
        elaborate(self.tcx, &mut preds);
        // The bounds' own equalities apply inside them: `type TryType: Try<Residual = Self>`
        // makes the supertrait `FromResidual<<TryType as Try>::Residual>` `FromResidual<Self>`.
        let eqs: Vec<(AliasTy, Ty)> = preds
            .iter()
            .filter_map(|p| match *p {
                Predicate::Projection(a, t) => Some((a, t)),
                _ => None,
            })
            .collect();
        if eqs.is_empty() {
            return preds;
        }
        struct Subst<'e>(&'e [(AliasTy, Ty)], u32);
        impl TypeFolder for Subst<'_> {
            fn fold_ty(&mut self, t: Ty) -> Ty {
                if !t.has_aliases() || self.1 > 8 {
                    return t;
                }
                if let TyKind::Alias(AliasKind::Projection, a) = *t.kind()
                    && let Some(&(_, v)) = self
                        .0
                        .iter()
                        .find(|(b, _)| b.def == a.def && b.args == a.args)
                {
                    self.1 += 1;
                    let r = self.fold_ty(v);
                    self.1 -= 1;
                    return r;
                }
                crate::fold::super_fold_ty(t, self)
            }
        }
        preds
            .into_iter()
            .map(|p| match p {
                Predicate::Trait(tr) => Predicate::Trait(TraitRef::new(
                    tr.def,
                    crate::fold::fold_args(tr.args, &mut Subst(&eqs, 0)),
                )),
                other => other,
            })
            .collect()
    }

    /// The traits a `dyn` type implements: its principal (with `Self` = the dyn type), the
    /// principal's supertraits, and its auto traits.
    pub fn object_traits(&self, self_ty: Ty, preds: PredList) -> Vec<TraitRef> {
        let mut out = Vec::new();
        for p in preds.as_slice() {
            match *p {
                ExistentialPredicate::Trait { def, args } => {
                    let mut full = vec![GenericArg::Ty(self_ty)];
                    full.extend_from_slice(args.as_slice());
                    out.push(TraitRef::new(def, Args::new(&full)));
                }
                ExistentialPredicate::AutoTrait(def) => {
                    out.push(TraitRef::new(def, Args::from_tys(&[self_ty])))
                }
                ExistentialPredicate::Projection { .. } => {}
            }
        }
        let mut preds: Vec<Predicate> = out.iter().map(|t| Predicate::Trait(*t)).collect();
        elaborate(self.tcx, &mut preds);
        preds
            .into_iter()
            .filter_map(|p| match p {
                Predicate::Trait(t) => Some(t),
                _ => None,
            })
            .collect()
    }

    fn assemble_builtin(&self, tr: TraitRef, self_ty: Ty, out: &mut Vec<Candidate>) {
        let def = tr.def;
        // `T: Alias` for a trait alias: its bounds hold for `T`.
        if self.tcx.hir.def_kind(def) == hyprc_hir::DefKind::TraitAlias {
            let trait_self = Ty::param(self.tcx.generics_of(def).parent_count, kw::SelfUpper);
            let nested = self
                .tcx
                .predicates_of(def)
                .iter()
                .filter(|p| match p {
                    Predicate::Trait(t) => t.self_ty() == trait_self && t.def != def,
                    Predicate::Projection(a, _) => {
                        a.args.get(0) == Some(GenericArg::Ty(trait_self))
                    }
                    _ => false,
                })
                .map(|p| p.subst(tr.args))
                .collect();
            out.push(Candidate::Builtin(nested));
            return;
        }
        if self.is_lang(def, "sized") {
            if let Some(nested) = self.sized_components(self_ty) {
                out.push(Candidate::Builtin(nested));
            }
        } else if self.is_lang(def, "meta_sized") || self.is_lang(def, "pointee_sized") {
            let ok =
                !matches!(self_ty.kind(), TyKind::Foreign(_)) || self.is_lang(def, "pointee_sized");
            if ok {
                out.push(Candidate::Builtin(Vec::new()));
            }
        } else if self.is_lang(def, "copy")
            || self.is_lang(def, "clone")
            || self.is_lang(def, "trivial_clone")
        {
            if let Some(nested) = self.copy_components(tr, self_ty) {
                out.push(Candidate::Builtin(nested));
            }
        } else if let Some(kind) = self.tcx.fn_trait_kind(def) {
            match *self_ty.kind() {
                TyKind::Closure(c, args) => {
                    if let Some(k) = self.closures.closure_kind(c, args) {
                        if k <= kind || kind == ClosureKind::FnOnce {
                            out.push(Candidate::Closure(k));
                        }
                    } else {
                        out.push(Candidate::Closure(kind));
                    }
                }
                TyKind::FnDef(..) | TyKind::FnPtr(_) => {
                    let sig = self.fn_sig_of(self_ty);
                    if let Some(sig) = sig
                        && !sig.unsafe_
                        && matches!(sig.abi, Abi::Rust)
                    {
                        out.push(Candidate::FnPointer);
                    }
                }
                _ => {}
            }
        } else if self.is_lang(def, "tuple_trait") {
            if matches!(self_ty.kind(), TyKind::Tuple(_)) || self_ty.is_unit() {
                out.push(Candidate::Builtin(Vec::new()));
            }
        } else if self.is_lang(def, "pointee_trait")
            || self.is_lang(def, "discriminant_kind")
            || self.is_lang(def, "destruct")
            || self.is_lang(def, "fn_ptr_trait") && matches!(self_ty.kind(), TyKind::FnPtr(_))
        {
            out.push(Candidate::Builtin(Vec::new()));
        } else if self.is_lang(def, "unsize") {
            let target = tr.args.ty(1);
            if let Some(nested) =
                self.unsize_components(self_ty, self.infcx.shallow_resolve(target))
            {
                out.push(Candidate::Builtin(nested));
            }
        } else if self.is_lang(def, "freeze") || self.is_lang(def, "unpin") {
            // Structural like auto traits; handled with them when there are no impls.
        } else if self.is_lang(def, "bikeshed_guaranteed_no_drop") {
            out.push(Candidate::Builtin(Vec::new()));
        }
    }

    pub fn fn_sig_of(&self, ty: Ty) -> Option<FnSig> {
        match *ty.kind() {
            TyKind::FnDef(d, args) => Some(self.tcx.fn_sig(d).subst(args)),
            TyKind::FnPtr(sig) => Some(sig),
            TyKind::Closure(c, args) => self.closures.closure_sig(c, args),
            _ => None,
        }
    }

    fn sized_trait(&self) -> Option<DefId> {
        self.lang("sized")
    }

    /// `T: Sized` built-in: `None` if not sized (or unknown).
    fn sized_components(&self, ty: Ty) -> Option<Vec<Predicate>> {
        match *ty.kind() {
            TyKind::Str | TyKind::Slice(_) | TyKind::Dynamic(_) | TyKind::Foreign(_) => None,
            TyKind::Param(..) => None,
            // A projection without a value here: `Sized` as its declaration says. Opaque
            // types are `Sized`.
            TyKind::Alias(AliasKind::Projection, a) => {
                self.tcx.assoc_ty_is_sized(a.def).then(Vec::new)
            }
            TyKind::Alias(..) => Some(Vec::new()),
            TyKind::Infer(InferTy::TyVar(_)) => None,
            TyKind::Tuple(ts) => match ts.as_slice().last() {
                Some(&last) => Some(vec![Predicate::Trait(TraitRef::new(
                    self.sized_trait()?,
                    Args::from_tys(&[last]),
                ))]),
                None => Some(Vec::new()),
            },
            TyKind::Adt(d, args) => {
                let adt = self.tcx.adt_def(d);
                // A struct is unsized if its last field is.
                if adt.is_struct()
                    && let Some(last) = adt.variants.first().and_then(|v| v.fields.last())
                {
                    let t = last.ty.subst(args);
                    if t.has_params()
                        || matches!(
                            t.kind(),
                            TyKind::Str
                                | TyKind::Slice(_)
                                | TyKind::Dynamic(_)
                                | TyKind::Adt(..)
                                | TyKind::Tuple(_)
                        )
                    {
                        return Some(vec![Predicate::Trait(TraitRef::new(
                            self.sized_trait()?,
                            Args::from_tys(&[t]),
                        ))]);
                    }
                }
                Some(Vec::new())
            }
            _ => Some(Vec::new()),
        }
    }

    /// `T: Copy`/`Clone` built-in for function types, tuples and closures, as in rustc;
    /// primitives, pointers, shared references, `!` and arrays get theirs from impls in core.
    /// Integer and float variables are built-in too (every candidate type is `Copy`), so
    /// they don't come out ambiguous between the integer types' impls.
    fn copy_components(&self, tr: TraitRef, ty: Ty) -> Option<Vec<Predicate>> {
        let same = |t: Ty| Predicate::Trait(TraitRef::new(tr.def, Args::from_tys(&[t])));
        match *ty.kind() {
            TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_)) => Some(Vec::new()),
            TyKind::FnDef(..) | TyKind::FnPtr(_) => Some(Vec::new()),
            TyKind::Tuple(ts) => Some(ts.as_slice().iter().map(|&t| same(t)).collect()),
            TyKind::Pat(base, _) => Some(vec![same(base)]),
            TyKind::Closure(c, args) => {
                let upvars = self.closures.closure_upvars(c, args)?;
                Some(upvars.into_iter().map(same).collect())
            }
            _ => None,
        }
    }

    /// Auto traits (`Send`, `Sync`, …) hold if they hold for every component.
    fn auto_trait_components(&self, tr: TraitRef, ty: Ty) -> Option<Vec<Predicate>> {
        let same = |t: Ty| Predicate::Trait(TraitRef::new(tr.def, Args::from_tys(&[t])));
        match *ty.kind() {
            TyKind::Param(..) | TyKind::Alias(..) | TyKind::Infer(InferTy::TyVar(_)) => None,
            TyKind::Dynamic(preds) => {
                if preds
                    .as_slice()
                    .iter()
                    .any(|p| matches!(p, ExistentialPredicate::AutoTrait(d) if *d == tr.def))
                {
                    Some(Vec::new())
                } else {
                    None
                }
            }
            TyKind::Adt(d, args) => {
                let adt = self.tcx.adt_def(d);
                Some(
                    adt.variants
                        .iter()
                        .flat_map(|v| v.fields.iter().map(|f| same(f.ty.subst(args))))
                        .collect(),
                )
            }
            TyKind::Tuple(ts) => Some(ts.as_slice().iter().map(|&t| same(t)).collect()),
            TyKind::Array(e, _) | TyKind::Slice(e) | TyKind::Ref(e, _) | TyKind::RawPtr(e, _) => {
                Some(vec![same(e)])
            }
            TyKind::Closure(c, args) => Some(
                self.closures
                    .closure_upvars(c, args)
                    .unwrap_or_default()
                    .into_iter()
                    .map(same)
                    .collect(),
            ),
            TyKind::Pat(base, _) => Some(vec![same(base)]),
            _ => Some(Vec::new()),
        }
    }

    /// `T: Unsize<U>`: arrays to slices, sized types to `dyn Trait`.
    fn unsize_components(&self, from: Ty, to: Ty) -> Option<Vec<Predicate>> {
        match (*from.kind(), *to.kind()) {
            (TyKind::Array(e, _), TyKind::Slice(e2)) => {
                self.infcx.unify(e, e2).ok().map(|_| Vec::new())
            }
            (TyKind::Dynamic(_), TyKind::Dynamic(_)) => Some(Vec::new()),
            (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => {
                let adt = self.tcx.adt_def(d1);
                if !adt.is_struct() {
                    return None;
                }
                let v = adt.non_enum_variant();
                let last = v.fields.last()?;
                let last_from = last.ty.subst(a1);
                let last_to = last.ty.subst(a2);
                for f in &v.fields[..v.fields.len() - 1] {
                    let f1 = f.ty.subst(a1);
                    let f2 = f.ty.subst(a2);
                    self.infcx.unify(f1, f2).ok()?;
                }
                let unsize = self.lang("unsize")?;
                Some(vec![Predicate::Trait(TraitRef::new(
                    unsize,
                    Args::from_tys(&[last_from, last_to]),
                ))])
            }
            (_, TyKind::Dynamic(preds)) => {
                let mut nested = Vec::new();
                for t in self.object_traits_for_unsize(from, preds) {
                    nested.push(Predicate::Trait(t));
                }
                if let Some(sized) = self.sized_trait() {
                    nested.push(Predicate::Trait(TraitRef::new(
                        sized,
                        Args::from_tys(&[from]),
                    )));
                }
                Some(nested)
            }
            _ => None,
        }
    }

    fn object_traits_for_unsize(&self, from: Ty, preds: PredList) -> Vec<TraitRef> {
        let mut out = Vec::new();
        for p in preds.as_slice() {
            match *p {
                ExistentialPredicate::Trait { def, args } => {
                    let mut full = vec![GenericArg::Ty(from)];
                    full.extend_from_slice(args.as_slice());
                    out.push(TraitRef::new(def, Args::new(&full)));
                }
                ExistentialPredicate::AutoTrait(def) => {
                    out.push(TraitRef::new(def, Args::from_tys(&[from])))
                }
                ExistentialPredicate::Projection { .. } => {}
            }
        }
        out
    }

    /// Commits to a candidate: unifies for real; returns its nested obligations (and for
    /// an impl, the impl's arguments).
    fn confirm(&self, tr: TraitRef, c: &Candidate) -> Option<(Vec<Predicate>, Option<Args>)> {
        match c {
            Candidate::Param(p) => self
                .infcx
                .unify_args(p.args, tr.args)
                .ok()
                .map(|_| (Vec::new(), None)),
            Candidate::Object(o) => self
                .infcx
                .unify_args(o.args, tr.args)
                .ok()
                .map(|_| (Vec::new(), None)),
            Candidate::Builtin(nested) => Some((nested.clone(), None)),
            Candidate::Impl(imp) => {
                let args = self.fresh_args(*imp);
                let impl_tr = self.tcx.impl_trait_ref(*imp)?.subst(args);
                let mut nested: Vec<Predicate> = Vec::new();
                if self
                    .infcx
                    .probe(|| self.infcx.unify_args(impl_tr.args, tr.args).is_ok())
                {
                    let _ = self.infcx.unify_args(impl_tr.args, tr.args);
                } else if impl_tr.has_aliases() {
                    for (a, b) in impl_tr.args.as_slice().iter().zip(tr.args.as_slice()) {
                        if !a.as_ty().is_some_and(|t| t.has_aliases()) {
                            match (*a, *b) {
                                (GenericArg::Ty(x), GenericArg::Ty(y)) => {
                                    self.infcx.unify(x, y).ok()?
                                }
                                (GenericArg::Const(x), GenericArg::Const(y)) => {
                                    self.infcx.unify_const(x, y).ok()?
                                }
                                _ => return None,
                            }
                        }
                    }
                    let norm = self.normalize_trait_ref_with(
                        self.infcx.resolve_trait_ref(impl_tr),
                        &mut nested,
                    );
                    self.infcx.unify_args(norm.args, tr.args).ok()?;
                } else {
                    return None;
                }
                let preds: Vec<Predicate> = self
                    .tcx
                    .predicates_of(*imp)
                    .iter()
                    .map(|p| p.subst(args))
                    .collect();
                nested.extend(preds);
                Some((nested, Some(args)))
            }
            Candidate::Closure(_) | Candidate::FnPointer => {
                // `F: Fn<Args>`: the arguments tuple must match the signature's inputs.
                let self_ty = self.infcx.shallow_resolve(tr.self_ty());
                let sig = self.fn_sig_of(self_ty)?;
                let inputs: Vec<Ty> = sig
                    .inputs()
                    .iter()
                    .map(|&t| self.infcx.resolve_vars(t))
                    .collect();
                let raw_tuple = Ty::tuple(&inputs);
                let mut nested = Vec::new();
                let args_tuple = self.normalize_keep(raw_tuple);
                if let Some(GenericArg::Ty(t)) = tr.args.get(1) {
                    let t = self.normalize_keep(self.infcx.resolve_vars(t));
                    if self.infcx.unify(t, args_tuple).is_err() {
                        let args_tuple_norm = self.normalize(args_tuple, &mut nested);
                        let t_norm = self.normalize(t, &mut nested);
                        self.infcx.unify(t_norm, args_tuple_norm).ok()?;
                    }
                }
                Some((nested, None))
            }
        }
    }

    /// An item of an impl, or (specialization) of a less specific impl it specializes that
    /// has it: the item, and the arguments of the impl it's in.
    pub fn impl_item(
        &self,
        imp: DefId,
        impl_args: Args,
        name: Symbol,
        value: bool,
    ) -> Option<(DefId, Args)> {
        if let Some(i) = self.tcx.assoc_item(imp, name, value) {
            return Some((i, impl_args));
        }
        let tr = self.tcx.impl_trait_ref(imp)?.subst(impl_args);
        let parents: Vec<DefId> = self
            .tcx
            .trait_impls(tr.def)
            .iter()
            .copied()
            .filter(|&p| {
                p != imp
                    && self.tcx.assoc_item(p, name, value).is_some()
                    && self.tcx.impl_specializes(imp, p)
            })
            .collect();
        // The closest: the parent that specializes the other parents.
        let &p = parents
            .iter()
            .find(|&&a| {
                parents
                    .iter()
                    .all(|&b| a == b || self.tcx.impl_specializes(a, b))
            })
            .or(parents.first())?;
        let p_args = self.fresh_args(p);
        let ptr = self.tcx.impl_trait_ref(p)?.subst(p_args);
        self.infcx.unify_args(ptr.args, tr.args).ok()?;
        Some((
            self.tcx.assoc_item(p, name, value)?,
            self.infcx.resolve_args(p_args),
        ))
    }

    /// The impl and its arguments a successful impl selection used (the confirmation adds a
    /// marker obligation carrying them; see `select_impl`).
    pub fn select_impl(&self, tr: TraitRef) -> Option<(DefId, Args)> {
        let r = self.infcx.commit_if_ok(|| match self.select(tr) {
            SelectResult::Ok(sel) => Ok(sel),
            _ => Err(()),
        });
        let sel = r.ok()?;
        match sel.kind {
            SelectionKind::Impl { def, args } => Some((def, self.infcx.resolve_args(args))),
            _ => None,
        }
    }

    // ---------------------------------------------------------------------------------------
    // Evaluation (does it hold? no side effects)

    pub fn evaluate(&self, p: Predicate) -> Eval {
        self.evaluate_depth(p, 0)
    }

    fn evaluate_depth(&self, p: Predicate, depth: u32) -> Eval {
        let r = self.evaluate_inner(p, depth);
        // `HYPRC_DEBUG_SOLVER=1`: every evaluation, nested by depth.
        if debug_solver() {
            let shown = match p {
                Predicate::Trait(t) => Predicate::Trait(self.infcx.resolve_trait_ref(t)),
                Predicate::Projection(a, t) => Predicate::Projection(
                    AliasTy {
                        args: self.infcx.resolve_args(a.args),
                        ..a
                    },
                    self.infcx.resolve_vars(t),
                ),
                o => o,
            };
            eprintln!(
                "{:indent$}eval {} => {r:?}",
                "",
                pred_to_string(self.tcx, shown),
                indent = self.nesting.get() as usize * 2
            );
        }
        r
    }

    fn evaluate_inner(&self, p: Predicate, depth: u32) -> Eval {
        if depth > 16 {
            return Eval::Ambiguous;
        }
        let Some(_nest) = self.nest() else {
            return Eval::Ambiguous;
        };
        self.infcx.probe(|| match p {
            Predicate::Trait(tr) => match self.select_depth(tr, depth) {
                SelectResult::Ok(sel) => {
                    let mut nested = sel.nested;
                    for _ in 0..4 {
                        let mut progress = false;
                        let mut remaining = Vec::new();
                        for n in nested {
                            match self.evaluate_depth(n, depth + 1) {
                                Eval::Holds => {
                                    progress = true;
                                }
                                Eval::Ambiguous => {
                                    remaining.push(n);
                                }
                                Eval::Fails => {
                                    remaining.push(n);
                                }
                            }
                        }
                        if remaining.is_empty() {
                            return Eval::Holds;
                        }
                        if !progress {
                            for n in &remaining {
                                if self.evaluate_depth(*n, depth + 1) == Eval::Fails {
                                    return Eval::Fails;
                                }
                            }
                            return Eval::Ambiguous;
                        }
                        nested = remaining;
                    }
                    Eval::Ambiguous
                }
                SelectResult::Ambiguous => Eval::Ambiguous,
                SelectResult::Err => Eval::Fails,
            },
            Predicate::Projection(alias, ty) => match self.project(alias) {
                // Both sides in normal form (`<<U as IntoIterator>::IntoIter as Iterator>::Item`
                // is `<U as IntoIterator>::Item`).
                Projected::Normalized(t, nested) => {
                    if !nested.is_empty() {
                        self.solve_now(nested);
                    }
                    let ty = self.normalize_keep(ty);
                    let t = self.normalize_keep(self.infcx.resolve_vars(t));
                    if self.infcx.unify(t, ty).is_ok() {
                        Eval::Holds
                    } else if t.has_aliases() || ty.has_aliases() {
                        Eval::Ambiguous
                    } else {
                        Eval::Fails
                    }
                }
                Projected::Rigid => {
                    let a = Ty::new(TyKind::Alias(AliasKind::Projection, alias));
                    let ty = self.normalize_keep(ty);
                    if self.infcx.unify(a, ty).is_ok() {
                        Eval::Holds
                    } else if a.has_aliases() || ty.has_aliases() {
                        Eval::Ambiguous
                    } else {
                        Eval::Fails
                    }
                }
                Projected::Ambiguous => Eval::Ambiguous,
                Projected::Error => Eval::Fails,
            },
            Predicate::NegTrait(_) | Predicate::MaybeSized(_) => Eval::Holds,
        })
    }

    // ---------------------------------------------------------------------------------------
    // Projection

    /// Normalizes one projection `<T as Trait>::Assoc`.
    pub fn project(&self, alias: AliasTy) -> Projected {
        let Some(_nest) = self.nest() else {
            return Projected::Ambiguous;
        };
        // `<<Map<I, F> as Iterator>::Item as IntoIterator>::IntoIter`: the arguments first
        // (`<U as IntoIterator>::IntoIter`), so a rigid answer is in normal form too.
        if alias
            .args
            .as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| t.has_aliases()))
        {
            let n = self.normalize_trait_ref(TraitRef::new(alias.def, alias.args));
            if n.args != alias.args {
                let normalized = AliasTy {
                    args: n.args,
                    ..alias
                };
                return match self.project(normalized) {
                    Projected::Rigid => Projected::Normalized(
                        Ty::new(TyKind::Alias(AliasKind::Projection, normalized)),
                        Vec::new(),
                    ),
                    other => other,
                };
            }
        }
        let Some(trait_) = self.tcx.assoc_container(alias.def) else {
            return Projected::Error;
        };
        if !self.tcx.is_trait(trait_) {
            return Projected::Error;
        }
        let trait_count = self.tcx.generics_of(trait_).count() as usize;
        let trait_args = alias.args.truncate(trait_count);
        let own_args = &alias.args.as_slice()[trait_count.min(alias.args.len())..];
        let tr = TraitRef::new(trait_, trait_args);
        let self_ty = self.infcx.shallow_resolve(tr.self_ty());
        if self_ty.is_error() {
            return Projected::Normalized(Ty::ERROR, Vec::new());
        }
        // An unknown self type: matching a where-clause would pick it arbitrarily.
        if self_ty.is_ty_var() {
            return Projected::Ambiguous;
        }
        // A where-clause `<T as Trait>::Assoc == U`.
        for p in &self.env.preds {
            if let Predicate::Projection(a, t) = p
                && a.def == alias.def
                && self
                    .infcx
                    .probe(|| self.infcx.unify_args(a.args, alias.args).is_ok())
            {
                let _ = self.infcx.unify_args(a.args, alias.args);
                return Projected::Normalized(*t, Vec::new());
            }
        }
        // The self type is itself a projection or opaque type whose declaration fixes this
        // one: `type IntoIter: Iterator<Item = Self::Item>`.
        if let TyKind::Alias(kind @ (AliasKind::Projection | AliasKind::Opaque), outer) =
            *self_ty.kind()
        {
            for p in self.alias_bounds(kind, outer) {
                if let Predicate::Projection(a, t) = p
                    && a.def == alias.def
                    && self
                        .infcx
                        .probe(|| self.infcx.unify_args(a.args, alias.args).is_ok())
                {
                    let _ = self.infcx.unify_args(a.args, alias.args);
                    return Projected::Normalized(t, Vec::new());
                }
            }
        }
        // `dyn Trait<Assoc = U>`
        if let TyKind::Dynamic(preds) = *self_ty.kind() {
            for p in preds.as_slice() {
                if let ExistentialPredicate::Projection { def, term, .. } = *p
                    && def == alias.def
                {
                    return Projected::Normalized(term, Vec::new());
                }
            }
        }
        let name = self.tcx.hir.name(alias.def);
        // Built-in associated types.
        if self.tcx.lang_item("fn_once_output") == Some(alias.def) {
            if let Some(sig) = self.fn_sig_of(self_ty) {
                return Projected::Normalized(sig.output(), Vec::new());
            }
        }
        if self.tcx.lang_item("metadata_type") == Some(alias.def) {
            let meta = match *self_ty.kind() {
                TyKind::Slice(_) | TyKind::Str => Some(Ty::USIZE),
                TyKind::Dynamic(_) => self
                    .tcx
                    .lang_item("dyn_metadata")
                    .map(|d| Ty::adt(d, Args::from_tys(&[self_ty]))),
                TyKind::Param(..) | TyKind::Alias(..) | TyKind::Infer(_) => None,
                _ => Some(Ty::UNIT),
            };
            if let Some(m) = meta {
                return Projected::Normalized(m, Vec::new());
            }
        }
        if self.tcx.lang_item("discriminant_type") == Some(alias.def) {
            let d = match *self_ty.kind() {
                TyKind::Adt(def, _) if self.tcx.adt_def(def).is_enum() => {
                    let adt = self.tcx.adt_def(def);
                    Some(adt.repr.int.map_or(Ty::ISIZE, crate::lower_ty::prim_ty))
                }
                TyKind::Param(..) | TyKind::Alias(..) | TyKind::Infer(_) => None,
                _ => Some(Ty::U8),
            };
            if let Some(d) = d {
                return Projected::Normalized(d, Vec::new());
            }
        }
        match self.select(tr) {
            SelectResult::Ok(sel) => match sel.kind {
                SelectionKind::Impl {
                    def: imp,
                    args: impl_args,
                } => {
                    let nested = sel.nested;
                    match self.impl_item(imp, impl_args, name, false) {
                        Some((item, impl_args)) => {
                            let mut args = impl_args.as_slice().to_vec();
                            args.extend_from_slice(own_args);
                            Projected::Normalized(
                                self.tcx.type_of(item).subst(Args::new(&args)),
                                nested,
                            )
                        }
                        None => {
                            // The trait's default.
                            match self.tcx.hir.get_item(alias.def).map(|i| &i.kind) {
                                Some(hyprc_hir::ItemKind::TyAlias { ty: Some(_), .. }) => {
                                    Projected::Normalized(
                                        self.tcx.type_of(alias.def).subst(alias.args),
                                        nested,
                                    )
                                }
                                _ => Projected::Error,
                            }
                        }
                    }
                }
                SelectionKind::Param => Projected::Rigid,
                _ => Projected::Rigid,
            },
            SelectResult::Ambiguous => {
                if matches!(self_ty.kind(), TyKind::Param(..) | TyKind::Alias(..)) {
                    Projected::Rigid
                } else {
                    Projected::Ambiguous
                }
            }
            SelectResult::Err => {
                if matches!(self_ty.kind(), TyKind::Param(..) | TyKind::Alias(..)) {
                    Projected::Rigid
                } else {
                    Projected::Error
                }
            }
        }
    }

    /// Normalizes every projection in a type that can be. Projections that can't be
    /// decided yet become inference variables with an obligation in `pending`.
    pub fn normalize(&self, ty: Ty, pending: &mut Vec<Predicate>) -> Ty {
        if !ty.has_aliases() {
            return ty;
        }
        let mut n = Normalizer {
            s: self,
            pending,
            depth: 0,
            keep_ambiguous: false,
            reveal: false,
        };
        n.fold_ty(ty)
    }

    /// Normalizes for code generation: opaque types are their hidden types too.
    pub fn normalize_revealing(&self, ty: Ty, pending: &mut Vec<Predicate>) -> Ty {
        if !ty.has_aliases() {
            return ty;
        }
        let mut n = Normalizer {
            s: self,
            pending,
            depth: 0,
            keep_ambiguous: false,
            reveal: true,
        };
        n.fold_ty(ty)
    }

    /// A where-clause with the projections in its types normalized where they have a value
    /// (a projection predicate's own projection stays: it's what the predicate defines).
    fn normalize_predicate(&self, p: Predicate, pending: &mut Vec<Predicate>) -> Predicate {
        match p {
            Predicate::Trait(tr) => Predicate::Trait(self.normalize_trait_ref_with(tr, pending)),
            Predicate::Projection(alias, ty) => {
                let a =
                    self.normalize_trait_ref_with(TraitRef::new(alias.def, alias.args), pending);
                let mut n = Normalizer {
                    s: self,
                    pending,
                    depth: 0,
                    keep_ambiguous: true,
                    reveal: false,
                };
                Predicate::Projection(
                    AliasTy {
                        args: a.args,
                        ..alias
                    },
                    n.fold_ty(ty),
                )
            }
            other => other,
        }
    }

    /// Normalizes the projections in a trait reference that have a value now, leaving the
    /// rest (selection can't register obligations for them).
    fn normalize_trait_ref(&self, tr: TraitRef) -> TraitRef {
        self.normalize_trait_ref_with(tr, &mut Vec::new())
    }

    /// A type with the projections that have a value now normalized (no new variables).
    pub fn normalize_keep(&self, t: Ty) -> Ty {
        if !t.has_aliases() {
            return t;
        }
        let mut pending = Vec::new();
        let mut n = Normalizer {
            s: self,
            pending: &mut pending,
            depth: 0,
            keep_ambiguous: true,
            reveal: false,
        };
        n.fold_ty(t)
    }

    /// [`Self::normalize_trait_ref`], keeping the obligations the values depend on.
    fn normalize_trait_ref_with(&self, tr: TraitRef, pending: &mut Vec<Predicate>) -> TraitRef {
        if !tr
            .args
            .as_slice()
            .iter()
            .any(|a| a.as_ty().is_some_and(|t| t.has_aliases()))
        {
            return tr;
        }
        let mut n = Normalizer {
            s: self,
            pending,
            depth: 0,
            keep_ambiguous: true,
            reveal: false,
        };
        let args: Vec<GenericArg> = tr
            .args
            .as_slice()
            .iter()
            .map(|a| match *a {
                GenericArg::Ty(t) => GenericArg::Ty(n.fold_ty(t)),
                c => c,
            })
            .collect();
        TraitRef::new(tr.def, Args::new(&args))
    }
}

struct Normalizer<'s, 'a, 'h> {
    s: &'s Solver<'a, 'h>,
    pending: &'s mut Vec<Predicate>,
    depth: u32,
    /// Leave projections without a value as they are (no new variables).
    keep_ambiguous: bool,
    /// Replace opaque types with their hidden types (after type checking).
    reveal: bool,
}

impl TypeFolder for Normalizer<'_, '_, '_> {
    fn fold_ty(&mut self, t: Ty) -> Ty {
        let t = self.s.infcx.shallow_resolve(t);
        if !t.has_aliases() {
            return t;
        }
        let t = crate::fold::super_fold_ty(t, self);
        if self.reveal
            && let TyKind::Alias(AliasKind::Opaque, a) = *t.kind()
            && self.depth <= 32
        {
            let hidden = self.s.tcx.opaque_hidden_type(a.def, a.index).subst(a.args);
            self.depth += 1;
            let r = self.fold_ty(hidden);
            self.depth -= 1;
            return r;
        }
        if let TyKind::Alias(AliasKind::Projection, alias) = *t.kind() {
            if self.depth > 32 {
                return t;
            }
            match self.s.project(alias) {
                // Without a place for obligations, the value must be fully known now: work
                // out what it depends on (`type Item = B` with `F: FnMut(I::Item) -> B`),
                // else leave the projection.
                Projected::Normalized(n, nested) if self.keep_ambiguous => {
                    if !nested.is_empty() {
                        self.s.solve_now(nested);
                    }
                    // Variables the projection itself had are fine; new ones still open mean
                    // the value isn't known yet.
                    let n = self.s.infcx.resolve_vars(n);
                    if n.has_infer() {
                        let before = ty_vars(self.s.infcx.resolve_vars(t));
                        if ty_vars(n).iter().any(|v| !before.contains(v)) {
                            return t;
                        }
                    }
                    self.depth += 1;
                    let r = self.fold_ty(n);
                    self.depth -= 1;
                    return r;
                }
                Projected::Normalized(n, nested) => {
                    self.pending.extend(nested);
                    self.depth += 1;
                    let r = self.fold_ty(n);
                    self.depth -= 1;
                    return r;
                }
                Projected::Ambiguous if self.keep_ambiguous => return t,
                Projected::Ambiguous => {
                    let v = self.s.infcx.new_ty_var(Span::DUMMY);
                    self.pending.push(Predicate::Projection(alias, v));
                    return v;
                }
                Projected::Rigid => return t,
                Projected::Error => return Ty::ERROR,
            }
        }
        t
    }
}
