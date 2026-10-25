//! MIR (`mir`), building it from typed HIR (`build`), layouts (`layout`), and
//! monomorphization: which instances of which functions a program needs (`mono`).

pub mod build;
pub mod layout;
pub mod mir;
pub mod mono;
pub mod print;
pub mod shim;

use hyprc_hir::DefId;
use hyprc_ty::collect::AdtDef;
use hyprc_ty::infer::InferCtxt;
use hyprc_ty::traits::{NoClosures, ParamEnv, Solver};
use hyprc_ty::{Args, Ty, TyCtxt};

/// Normalizes projections in a type, with an item's where-clauses in scope.
pub fn normalize_in(tcx: &TyCtxt<'_>, owner: DefId, t: Ty) -> Ty {
    if !t.has_aliases() {
        return t;
    }
    let env = ParamEnv::for_item(tcx, owner);
    normalize_with(tcx, &env, t)
}

/// Normalizes projections in a concrete (monomorphic) type.
pub fn normalize_erasing(tcx: &TyCtxt<'_>, t: Ty) -> Ty {
    if !t.has_aliases() {
        return t;
    }
    normalize_with(tcx, &ParamEnv::empty(), t)
}

fn normalize_with(tcx: &TyCtxt<'_>, env: &ParamEnv, t: Ty) -> Ty {
    let infcx = InferCtxt::new();
    let solver = Solver::new(tcx, &infcx, env, &NoClosures);
    let mut pending = Vec::new();
    // After type checking: opaque types are what they hide.
    let n = solver.normalize_revealing(t, &mut pending);
    infcx.resolve_vars(n)
}

/// Substitutes an instance's arguments into a type from its body and normalizes.
pub fn monomorphize(tcx: &TyCtxt<'_>, args: Args, t: Ty) -> Ty {
    normalize_erasing(tcx, t.subst(args))
}

/// The discriminant values of an enum's variants.
pub fn discriminants(tcx: &TyCtxt<'_>, adt: &AdtDef) -> Vec<i128> {
    let mut out = Vec::with_capacity(adt.variants.len());
    let mut next: i128 = 0;
    let repr_ty = discriminant_ty(adt);
    for v in &adt.variants {
        if let Some(b) = v.discr_body {
            let c = tcx.eval_const_body(b, repr_ty, Args::EMPTY);
            if let Some(bits) = c.try_to_bits() {
                next = if repr_ty.is_signed() {
                    hyprc_ty::consteval::sext(bits, repr_ty, tcx.pointer_width)
                } else {
                    bits as i128
                };
            }
        }
        out.push(next);
        next = next.wrapping_add(1);
    }
    out
}

/// The type of an enum's discriminant: its `repr`, else `isize`.
pub fn discriminant_ty(adt: &AdtDef) -> Ty {
    adt.repr
        .int
        .map(hyprc_ty::lower_ty::prim_ty)
        .unwrap_or(Ty::ISIZE)
}
