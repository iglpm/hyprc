//! Type inference: variables, unification, resolution.
//!
//! Variables live in union-find tables. Every change goes to an undo log, so a probe (try a
//! method candidate, try an impl) can be rolled back by truncating the log.

use crate::fold::{TypeFolder, super_fold_const, super_fold_ty};
use crate::ty::*;
use hyprc_hir::Mutability;
use std::cell::RefCell;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VarState<T: Copy> {
    /// Points to another variable of the same table.
    Redirect(u32),
    Unknown,
    Known(T),
}

#[derive(Clone, Copy, Debug)]
enum Undo {
    TyVar(u32, VarState<Ty>),
    IntVar(u32, VarState<Ty>),
    FloatVar(u32, VarState<Ty>),
    ConstVar(u32, VarState<Const>),
    NewTyVar,
    NewIntVar,
    NewFloatVar,
    NewConstVar,
}

#[derive(Default)]
struct Tables {
    ty: Vec<VarState<Ty>>,
    int: Vec<VarState<Ty>>,
    float: Vec<VarState<Ty>>,
    consts: Vec<VarState<Const>>,
    /// Where each type variable came from, for "type annotations needed".
    ty_origins: Vec<hyprc_span::Span>,
    undo: Vec<Undo>,
    /// Inside a probe: changes are logged.
    in_snapshot: u32,
}

#[derive(Clone, Copy, Debug)]
pub struct Snapshot(usize);

#[derive(Clone, Copy, Debug)]
pub enum TypeError {
    Mismatch(Ty, Ty),
    /// `T = Vec<T>`
    Cyclic(Ty),
    ConstMismatch(Const, Const),
    MutabilityMismatch,
    ArgCount,
}

#[derive(Default)]
pub struct InferCtxt {
    t: RefCell<Tables>,
}

impl InferCtxt {
    pub fn new() -> InferCtxt {
        InferCtxt::default()
    }

    pub fn new_ty_var(&self, origin: hyprc_span::Span) -> Ty {
        let mut t = self.t.borrow_mut();
        t.ty.push(VarState::Unknown);
        t.ty_origins.push(origin);
        if t.in_snapshot > 0 {
            t.undo.push(Undo::NewTyVar);
        }
        Ty::var(t.ty.len() as u32 - 1)
    }

    pub fn new_int_var(&self) -> Ty {
        let mut t = self.t.borrow_mut();
        t.int.push(VarState::Unknown);
        if t.in_snapshot > 0 {
            t.undo.push(Undo::NewIntVar);
        }
        Ty::new(TyKind::Infer(InferTy::IntVar(t.int.len() as u32 - 1)))
    }

    pub fn new_float_var(&self) -> Ty {
        let mut t = self.t.borrow_mut();
        t.float.push(VarState::Unknown);
        if t.in_snapshot > 0 {
            t.undo.push(Undo::NewFloatVar);
        }
        Ty::new(TyKind::Infer(InferTy::FloatVar(t.float.len() as u32 - 1)))
    }

    pub fn new_const_var(&self, ty: Ty) -> Const {
        let mut t = self.t.borrow_mut();
        t.consts.push(VarState::Unknown);
        if t.in_snapshot > 0 {
            t.undo.push(Undo::NewConstVar);
        }
        Const::new(ty, ConstKind::Infer(t.consts.len() as u32 - 1))
    }

    pub fn ty_var_origin(&self, v: u32) -> hyprc_span::Span {
        self.t
            .borrow()
            .ty_origins
            .get(v as usize)
            .copied()
            .unwrap_or(hyprc_span::Span::DUMMY)
    }

    pub fn num_ty_vars(&self) -> usize {
        self.t.borrow().ty.len()
    }

    // ---------------------------------------------------------------------------------------
    // Snapshots

    pub fn snapshot(&self) -> Snapshot {
        let mut t = self.t.borrow_mut();
        t.in_snapshot += 1;
        Snapshot(t.undo.len())
    }

    pub fn rollback_to(&self, s: Snapshot) {
        let mut t = self.t.borrow_mut();
        while t.undo.len() > s.0 {
            match t.undo.pop().unwrap() {
                Undo::TyVar(v, old) => t.ty[v as usize] = old,
                Undo::IntVar(v, old) => t.int[v as usize] = old,
                Undo::FloatVar(v, old) => t.float[v as usize] = old,
                Undo::ConstVar(v, old) => t.consts[v as usize] = old,
                Undo::NewTyVar => {
                    t.ty.pop();
                    t.ty_origins.pop();
                }
                Undo::NewIntVar => {
                    t.int.pop();
                }
                Undo::NewFloatVar => {
                    t.float.pop();
                }
                Undo::NewConstVar => {
                    t.consts.pop();
                }
            }
        }
        t.in_snapshot -= 1;
    }

    pub fn commit(&self, s: Snapshot) {
        let mut t = self.t.borrow_mut();
        t.in_snapshot -= 1;
        if t.in_snapshot == 0 {
            t.undo.clear();
        }
        let _ = s;
    }

    /// Runs `f` and undoes everything it did to the tables.
    pub fn probe<R>(&self, f: impl FnOnce() -> R) -> R {
        let s = self.snapshot();
        let r = f();
        self.rollback_to(s);
        r
    }

    /// Runs `f`; keeps its changes if it succeeds, undoes them if it fails.
    pub fn commit_if_ok<T, E>(&self, f: impl FnOnce() -> Result<T, E>) -> Result<T, E> {
        let s = self.snapshot();
        let r = f();
        match &r {
            Ok(_) => self.commit(s),
            Err(_) => self.rollback_to(s),
        }
        r
    }

    // ---------------------------------------------------------------------------------------
    // Variables

    fn find_ty(&self, v: u32) -> u32 {
        let t = self.t.borrow();
        let mut v = v;
        while let VarState::Redirect(p) = t.ty[v as usize] {
            v = p;
        }
        v
    }

    fn find_int(&self, v: u32) -> u32 {
        let t = self.t.borrow();
        let mut v = v;
        while let VarState::Redirect(p) = t.int[v as usize] {
            v = p;
        }
        v
    }

    fn find_float(&self, v: u32) -> u32 {
        let t = self.t.borrow();
        let mut v = v;
        while let VarState::Redirect(p) = t.float[v as usize] {
            v = p;
        }
        v
    }

    fn find_const(&self, v: u32) -> u32 {
        let t = self.t.borrow();
        let mut v = v;
        while let VarState::Redirect(p) = t.consts[v as usize] {
            v = p;
        }
        v
    }

    fn set_ty(&self, v: u32, s: VarState<Ty>) {
        let mut t = self.t.borrow_mut();
        let old = t.ty[v as usize];
        if t.in_snapshot > 0 {
            t.undo.push(Undo::TyVar(v, old));
        }
        t.ty[v as usize] = s;
    }

    fn set_int(&self, v: u32, s: VarState<Ty>) {
        let mut t = self.t.borrow_mut();
        let old = t.int[v as usize];
        if t.in_snapshot > 0 {
            t.undo.push(Undo::IntVar(v, old));
        }
        t.int[v as usize] = s;
    }

    fn set_float(&self, v: u32, s: VarState<Ty>) {
        let mut t = self.t.borrow_mut();
        let old = t.float[v as usize];
        if t.in_snapshot > 0 {
            t.undo.push(Undo::FloatVar(v, old));
        }
        t.float[v as usize] = s;
    }

    fn set_const(&self, v: u32, s: VarState<Const>) {
        let mut t = self.t.borrow_mut();
        let old = t.consts[v as usize];
        if t.in_snapshot > 0 {
            t.undo.push(Undo::ConstVar(v, old));
        }
        t.consts[v as usize] = s;
    }

    /// Resolves the outermost layer of a type: a variable with a value becomes the value.
    pub fn shallow_resolve(&self, ty: Ty) -> Ty {
        match *ty.kind() {
            TyKind::Infer(InferTy::TyVar(v)) => {
                let root = self.find_ty(v);
                match self.t.borrow().ty[root as usize] {
                    VarState::Known(t) => return self.shallow_resolve(t),
                    _ => {}
                }
                if root == v { ty } else { Ty::var(root) }
            }
            TyKind::Infer(InferTy::IntVar(v)) => {
                let root = self.find_int(v);
                if let VarState::Known(t) = self.t.borrow().int[root as usize] {
                    return t;
                }
                if root == v {
                    ty
                } else {
                    Ty::new(TyKind::Infer(InferTy::IntVar(root)))
                }
            }
            TyKind::Infer(InferTy::FloatVar(v)) => {
                let root = self.find_float(v);
                if let VarState::Known(t) = self.t.borrow().float[root as usize] {
                    return t;
                }
                if root == v {
                    ty
                } else {
                    Ty::new(TyKind::Infer(InferTy::FloatVar(root)))
                }
            }
            _ => ty,
        }
    }

    pub fn shallow_resolve_const(&self, c: Const) -> Const {
        if let ConstKind::Infer(v) = c.kind() {
            let root = self.find_const(v);
            if let VarState::Known(k) = self.t.borrow().consts[root as usize] {
                return self.shallow_resolve_const(k);
            }
            if root != v {
                return Const::new(c.ty(), ConstKind::Infer(root));
            }
        }
        c
    }

    /// Replaces every variable with a value by that value, everywhere in the type.
    pub fn resolve_vars(&self, ty: Ty) -> Ty {
        if !ty.has_infer() {
            return ty;
        }
        Resolver { infcx: self }.fold_ty(ty)
    }

    pub fn resolve_args(&self, args: Args) -> Args {
        if !args.has_infer() {
            return args;
        }
        crate::fold::fold_args(args, &mut Resolver { infcx: self })
    }

    pub fn resolve_const(&self, c: Const) -> Const {
        Resolver { infcx: self }.fold_const(c)
    }

    pub fn resolve_trait_ref(&self, t: TraitRef) -> TraitRef {
        TraitRef {
            def: t.def,
            args: self.resolve_args(t.args),
        }
    }

    pub fn is_unresolved_var(&self, ty: Ty) -> bool {
        matches!(
            self.shallow_resolve(ty).kind(),
            TyKind::Infer(InferTy::TyVar(_))
        )
    }

    /// Integer and float variables without a value default to `i32` and `f64`.
    pub fn default_numeric_vars(&self) {
        let n_int = self.t.borrow().int.len();
        for v in 0..n_int as u32 {
            let root = self.find_int(v);
            if matches!(self.t.borrow().int[root as usize], VarState::Unknown) {
                self.set_int(root, VarState::Known(Ty::I32));
            }
        }
        let n_float = self.t.borrow().float.len();
        for v in 0..n_float as u32 {
            let root = self.find_float(v);
            if matches!(self.t.borrow().float[root as usize], VarState::Unknown) {
                self.set_float(root, VarState::Known(Ty::F64));
            }
        }
    }

    /// Unknown type variables (roots), for fallback and "annotations needed".
    pub fn unresolved_ty_vars(&self) -> Vec<u32> {
        let n = self.t.borrow().ty.len();
        (0..n as u32)
            .filter(|&v| {
                self.find_ty(v) == v && matches!(self.t.borrow().ty[v as usize], VarState::Unknown)
            })
            .collect()
    }

    /// Gives an unknown variable a value (fallback: `!` → `()`, errors).
    pub fn force_ty_var(&self, v: u32, ty: Ty) {
        let root = self.find_ty(v);
        if matches!(self.t.borrow().ty[root as usize], VarState::Unknown) {
            self.set_ty(root, VarState::Known(ty));
        }
    }

    // ---------------------------------------------------------------------------------------
    // Unification

    fn occurs(&self, v: u32, ty: Ty) -> bool {
        if !ty.has_infer() {
            return false;
        }
        let mut found = false;
        let ty = self.resolve_vars(ty);
        ty.walk(&mut |t| {
            if let TyKind::Infer(InferTy::TyVar(w)) = *t.kind()
                && self.find_ty(w) == v
            {
                found = true;
            }
        });
        found
    }

    /// Makes two types equal, binding variables as needed.
    pub fn unify(&self, a: Ty, b: Ty) -> Result<(), TypeError> {
        let a = self.shallow_resolve(a);
        let b = self.shallow_resolve(b);
        if a == b {
            return Ok(());
        }
        use InferTy::*;
        match (*a.kind(), *b.kind()) {
            (TyKind::Error, _) | (_, TyKind::Error) => Ok(()),
            (TyKind::Infer(TyVar(x)), TyKind::Infer(TyVar(y))) => {
                let (x, y) = (self.find_ty(x), self.find_ty(y));
                if x != y {
                    self.set_ty(x, VarState::Redirect(y));
                }
                Ok(())
            }
            (TyKind::Infer(TyVar(x)), _) => self.bind_ty_var(x, b),
            (_, TyKind::Infer(TyVar(y))) => self.bind_ty_var(y, a),
            (TyKind::Infer(IntVar(x)), TyKind::Infer(IntVar(y))) => {
                let (x, y) = (self.find_int(x), self.find_int(y));
                if x != y {
                    self.set_int(x, VarState::Redirect(y));
                }
                Ok(())
            }
            (TyKind::Infer(IntVar(x)), TyKind::Int(_) | TyKind::Uint(_)) => {
                self.set_int(self.find_int(x), VarState::Known(b));
                Ok(())
            }
            (TyKind::Int(_) | TyKind::Uint(_), TyKind::Infer(IntVar(y))) => {
                self.set_int(self.find_int(y), VarState::Known(a));
                Ok(())
            }
            (TyKind::Infer(FloatVar(x)), TyKind::Infer(FloatVar(y))) => {
                let (x, y) = (self.find_float(x), self.find_float(y));
                if x != y {
                    self.set_float(x, VarState::Redirect(y));
                }
                Ok(())
            }
            (TyKind::Infer(FloatVar(x)), TyKind::Float(_)) => {
                self.set_float(self.find_float(x), VarState::Known(b));
                Ok(())
            }
            (TyKind::Float(_), TyKind::Infer(FloatVar(y))) => {
                self.set_float(self.find_float(y), VarState::Known(a));
                Ok(())
            }
            (TyKind::Adt(d1, a1), TyKind::Adt(d2, a2)) if d1 == d2 => self.unify_args(a1, a2),
            (TyKind::FnDef(d1, a1), TyKind::FnDef(d2, a2)) if d1 == d2 => self.unify_args(a1, a2),
            (TyKind::Closure(c1, a1), TyKind::Closure(c2, a2)) if c1 == c2 => {
                self.unify_args(a1, a2)
            }
            (TyKind::Coroutine(c1, a1), TyKind::Coroutine(c2, a2)) if c1 == c2 => {
                self.unify_args(a1, a2)
            }
            (TyKind::Foreign(d1), TyKind::Foreign(d2)) if d1 == d2 => Ok(()),
            (TyKind::Array(e1, c1), TyKind::Array(e2, c2)) => {
                self.unify(e1, e2)?;
                self.unify_const(c1, c2)
            }
            (TyKind::Slice(e1), TyKind::Slice(e2)) => self.unify(e1, e2),
            (TyKind::Pat(b1, r1), TyKind::Pat(b2, r2)) if r1 == r2 => self.unify(b1, b2),
            (TyKind::RawPtr(e1, m1), TyKind::RawPtr(e2, m2))
            | (TyKind::Ref(e1, m1), TyKind::Ref(e2, m2)) => {
                if m1 != m2 {
                    return Err(TypeError::Mismatch(a, b));
                }
                self.unify(e1, e2)
            }
            (TyKind::FnPtr(s1), TyKind::FnPtr(s2)) => {
                if s1.inputs().len() != s2.inputs().len()
                    || s1.unsafe_ != s2.unsafe_
                    || s1.c_variadic != s2.c_variadic
                {
                    return Err(TypeError::Mismatch(a, b));
                }
                for (x, y) in s1
                    .inputs_and_output
                    .as_slice()
                    .iter()
                    .zip(s2.inputs_and_output.as_slice())
                {
                    self.unify(*x, *y)?;
                }
                Ok(())
            }
            (TyKind::Tuple(t1), TyKind::Tuple(t2)) => {
                let (t1, t2) = (t1.as_slice(), t2.as_slice());
                if t1.len() != t2.len() {
                    return Err(TypeError::Mismatch(a, b));
                }
                for (x, y) in t1.iter().zip(t2) {
                    self.unify(*x, *y).map_err(|_| TypeError::Mismatch(a, b))?;
                }
                Ok(())
            }
            (TyKind::Dynamic(p1), TyKind::Dynamic(p2)) => {
                let (p1, p2) = (p1.as_slice(), p2.as_slice());
                if p1.len() != p2.len() {
                    return Err(TypeError::Mismatch(a, b));
                }
                for (x, y) in p1.iter().zip(p2) {
                    match (x, y) {
                        (
                            ExistentialPredicate::Trait { def: d1, args: a1 },
                            ExistentialPredicate::Trait { def: d2, args: a2 },
                        ) if d1 == d2 => self.unify_args(*a1, *a2)?,
                        (
                            ExistentialPredicate::Projection {
                                def: d1,
                                args: a1,
                                term: t1,
                            },
                            ExistentialPredicate::Projection {
                                def: d2,
                                args: a2,
                                term: t2,
                            },
                        ) if d1 == d2 => {
                            self.unify_args(*a1, *a2)?;
                            self.unify(*t1, *t2)?;
                        }
                        (
                            ExistentialPredicate::AutoTrait(d1),
                            ExistentialPredicate::AutoTrait(d2),
                        ) if d1 == d2 => {}
                        _ => return Err(TypeError::Mismatch(a, b)),
                    }
                }
                Ok(())
            }
            (TyKind::Alias(k1, x1), TyKind::Alias(k2, x2))
                if k1 == k2 && x1.def == x2.def && x1.index == x2.index =>
            {
                self.unify_args(x1.args, x2.args)
            }
            _ => Err(TypeError::Mismatch(a, b)),
        }
    }

    fn bind_ty_var(&self, v: u32, ty: Ty) -> Result<(), TypeError> {
        let v = self.find_ty(v);
        if self.occurs(v, ty) {
            return Err(TypeError::Cyclic(ty));
        }
        self.set_ty(v, VarState::Known(ty));
        Ok(())
    }

    pub fn unify_args(&self, a: Args, b: Args) -> Result<(), TypeError> {
        let (a, b) = (a.as_slice(), b.as_slice());
        if a.len() != b.len() {
            return Err(TypeError::ArgCount);
        }
        for (x, y) in a.iter().zip(b) {
            match (*x, *y) {
                (GenericArg::Ty(x), GenericArg::Ty(y)) => self.unify(x, y)?,
                (GenericArg::Const(x), GenericArg::Const(y)) => self.unify_const(x, y)?,
                _ => return Err(TypeError::ArgCount),
            }
        }
        Ok(())
    }

    pub fn unify_const(&self, a: Const, b: Const) -> Result<(), TypeError> {
        let a = self.shallow_resolve_const(a);
        let b = self.shallow_resolve_const(b);
        if a == b {
            return Ok(());
        }
        match (a.kind(), b.kind()) {
            (ConstKind::Error, _) | (_, ConstKind::Error) => Ok(()),
            (ConstKind::Infer(x), ConstKind::Infer(y)) => {
                let (x, y) = (self.find_const(x), self.find_const(y));
                if x != y {
                    self.set_const(x, VarState::Redirect(y));
                }
                Ok(())
            }
            (ConstKind::Infer(x), _) => {
                self.set_const(self.find_const(x), VarState::Known(b));
                Ok(())
            }
            (_, ConstKind::Infer(y)) => {
                self.set_const(self.find_const(y), VarState::Known(a));
                Ok(())
            }
            (ConstKind::Value(x), ConstKind::Value(y)) if x == y => Ok(()),
            // Unevaluated constants compare by identity until they can be evaluated.
            (ConstKind::Unevaluated { .. }, _) | (_, ConstKind::Unevaluated { .. }) => Ok(()),
            _ => Err(TypeError::ConstMismatch(a, b)),
        }
    }

    pub fn unify_trait_refs(&self, a: TraitRef, b: TraitRef) -> Result<(), TypeError> {
        if a.def != b.def {
            return Err(TypeError::Mismatch(Ty::ERROR, Ty::ERROR));
        }
        self.unify_args(a.args, b.args)
    }

    pub fn mutability_ok(&self, from: Mutability, to: Mutability) -> bool {
        from == Mutability::Mut || to == Mutability::Not
    }
}

struct Resolver<'a> {
    infcx: &'a InferCtxt,
}

impl TypeFolder for Resolver<'_> {
    fn fold_ty(&mut self, t: Ty) -> Ty {
        if !t.has_infer() {
            return t;
        }
        let r = self.infcx.shallow_resolve(t);
        if r != t {
            return self.fold_ty(r);
        }
        super_fold_ty(t, self)
    }

    fn fold_const(&mut self, c: Const) -> Const {
        let r = self.infcx.shallow_resolve_const(c);
        if r != c {
            return self.fold_const(r);
        }
        super_fold_const(c, self)
    }
}
