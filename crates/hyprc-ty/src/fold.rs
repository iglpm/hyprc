//! Rebuilding types: substitution of generic parameters, and any other transformation
//! through [`TypeFolder`]. Types whose flags say a folder can't change them are returned
//! as they are without walking them.

use crate::ty::*;

pub trait TypeFolder {
    fn fold_ty(&mut self, t: Ty) -> Ty {
        super_fold_ty(t, self)
    }

    fn fold_const(&mut self, c: Const) -> Const {
        super_fold_const(c, self)
    }
}

pub fn super_fold_ty<F: TypeFolder + ?Sized>(t: Ty, f: &mut F) -> Ty {
    let new = match *t.kind() {
        TyKind::Adt(d, args) => TyKind::Adt(d, fold_args(args, f)),
        TyKind::FnDef(d, args) => TyKind::FnDef(d, fold_args(args, f)),
        TyKind::Closure(c, args) => TyKind::Closure(c, fold_args(args, f)),
        TyKind::Coroutine(c, args) => TyKind::Coroutine(c, fold_args(args, f)),
        TyKind::Alias(k, a) => TyKind::Alias(
            k,
            AliasTy {
                args: fold_args(a.args, f),
                ..a
            },
        ),
        TyKind::Array(e, c) => TyKind::Array(f.fold_ty(e), f.fold_const(c)),
        TyKind::Slice(e) => TyKind::Slice(f.fold_ty(e)),
        TyKind::Pat(e, r) => TyKind::Pat(f.fold_ty(e), r),
        TyKind::RawPtr(e, m) => TyKind::RawPtr(f.fold_ty(e), m),
        TyKind::Ref(e, m) => TyKind::Ref(f.fold_ty(e), m),
        TyKind::FnPtr(sig) => TyKind::FnPtr(fold_sig(sig, f)),
        TyKind::Tuple(ts) => TyKind::Tuple(fold_list(ts, f)),
        TyKind::Dynamic(preds) => TyKind::Dynamic(fold_preds(preds, f)),
        _ => return t,
    };
    if new == *t.kind() { t } else { Ty::new(new) }
}

pub fn super_fold_const<F: TypeFolder + ?Sized>(c: Const, f: &mut F) -> Const {
    let ty = f.fold_ty(c.ty());
    let kind = match c.kind() {
        ConstKind::Unevaluated { def, body, args } => ConstKind::Unevaluated {
            def,
            body,
            args: fold_args(args, f),
        },
        k => k,
    };
    if ty == c.ty() && kind == c.kind() {
        c
    } else {
        Const::new(ty, kind)
    }
}

pub fn fold_args<F: TypeFolder + ?Sized>(args: Args, f: &mut F) -> Args {
    let s = args.as_slice();
    let mut changed = false;
    let new: Vec<GenericArg> = s
        .iter()
        .map(|a| {
            let n = match *a {
                GenericArg::Ty(t) => GenericArg::Ty(f.fold_ty(t)),
                GenericArg::Const(c) => GenericArg::Const(f.fold_const(c)),
            };
            changed |= n != *a;
            n
        })
        .collect();
    if changed { Args::new(&new) } else { args }
}

pub fn fold_list<F: TypeFolder + ?Sized>(list: TyList, f: &mut F) -> TyList {
    let s = list.as_slice();
    let mut changed = false;
    let new: Vec<Ty> = s
        .iter()
        .map(|&t| {
            let n = f.fold_ty(t);
            changed |= n != t;
            n
        })
        .collect();
    if changed { TyList::new(&new) } else { list }
}

pub fn fold_sig<F: TypeFolder + ?Sized>(sig: FnSig, f: &mut F) -> FnSig {
    FnSig {
        inputs_and_output: fold_list(sig.inputs_and_output, f),
        ..sig
    }
}

pub fn fold_preds<F: TypeFolder + ?Sized>(preds: PredList, f: &mut F) -> PredList {
    let new: Vec<ExistentialPredicate> = preds
        .as_slice()
        .iter()
        .map(|p| match *p {
            ExistentialPredicate::Trait { def, args } => ExistentialPredicate::Trait {
                def,
                args: fold_args(args, f),
            },
            ExistentialPredicate::Projection { def, args, term } => {
                ExistentialPredicate::Projection {
                    def,
                    args: fold_args(args, f),
                    term: f.fold_ty(term),
                }
            }
            p => p,
        })
        .collect();
    if new.as_slice() == preds.as_slice() {
        preds
    } else {
        PredList::new(&new)
    }
}

pub fn fold_trait_ref<F: TypeFolder + ?Sized>(t: TraitRef, f: &mut F) -> TraitRef {
    TraitRef {
        def: t.def,
        args: fold_args(t.args, f),
    }
}

pub fn fold_predicate<F: TypeFolder + ?Sized>(p: Predicate, f: &mut F) -> Predicate {
    match p {
        Predicate::Trait(t) => Predicate::Trait(fold_trait_ref(t, f)),
        Predicate::NegTrait(t) => Predicate::NegTrait(fold_trait_ref(t, f)),
        Predicate::Projection(a, t) => Predicate::Projection(
            AliasTy {
                args: fold_args(a.args, f),
                ..a
            },
            f.fold_ty(t),
        ),
        Predicate::MaybeSized(t) => Predicate::MaybeSized(f.fold_ty(t)),
    }
}

/// Replaces generic parameters by arguments.
pub struct Subst<'a> {
    pub args: &'a [GenericArg],
}

impl TypeFolder for Subst<'_> {
    fn fold_ty(&mut self, t: Ty) -> Ty {
        if !t.has_params() {
            return t;
        }
        if let TyKind::Param(i, _) = *t.kind() {
            return match self.args.get(i as usize) {
                Some(GenericArg::Ty(t)) => *t,
                _ => t,
            };
        }
        super_fold_ty(t, self)
    }

    fn fold_const(&mut self, c: Const) -> Const {
        if let ConstKind::Param(i, _) = c.kind() {
            return match self.args.get(i as usize) {
                Some(GenericArg::Const(c)) => *c,
                _ => c,
            };
        }
        super_fold_const(c, self)
    }
}

impl Ty {
    /// Substitutes generic parameters (`Param(i)` becomes `args[i]`).
    pub fn subst(self, args: Args) -> Ty {
        if !self.has_params() || args.is_empty() {
            return self;
        }
        Subst {
            args: args.as_slice(),
        }
        .fold_ty(self)
    }

    pub fn fold<F: TypeFolder>(self, f: &mut F) -> Ty {
        f.fold_ty(self)
    }
}

impl Args {
    pub fn subst(self, args: Args) -> Args {
        if !self.has_params() || args.is_empty() {
            return self;
        }
        fold_args(
            self,
            &mut Subst {
                args: args.as_slice(),
            },
        )
    }
}

impl Const {
    pub fn subst(self, args: Args) -> Const {
        Subst {
            args: args.as_slice(),
        }
        .fold_const(self)
    }
}

impl FnSig {
    pub fn subst(self, args: Args) -> FnSig {
        if args.is_empty() {
            return self;
        }
        fold_sig(
            self,
            &mut Subst {
                args: args.as_slice(),
            },
        )
    }
}

impl TraitRef {
    pub fn subst(self, args: Args) -> TraitRef {
        if args.is_empty() {
            return self;
        }
        fold_trait_ref(
            self,
            &mut Subst {
                args: args.as_slice(),
            },
        )
    }
}

impl Predicate {
    pub fn subst(self, args: Args) -> Predicate {
        if args.is_empty() {
            return self;
        }
        fold_predicate(
            self,
            &mut Subst {
                args: args.as_slice(),
            },
        )
    }
}
