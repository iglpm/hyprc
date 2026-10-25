//! MIR for functions the compiler provides rather than the source: calls through the `Fn*`
//! traits on closures and function pointers, and built-in `Clone`. Built per instance, so
//! every type in them is concrete.

use crate::mir::*;
use crate::mono::{Instance, InstanceKind};
use hyprc_hir::{DefId, DefKind, Mutability};
use hyprc_span::{Span, Symbol};
use hyprc_ty::collect::ClosureKind;
use hyprc_ty::infer::InferCtxt;
use hyprc_ty::traits::{
    Eval, NoClosures, ParamEnv, Solver, closure_kind_from_args, closure_sig_from_args,
};
use hyprc_ty::{Args, Predicate, TraitRef, Ty, TyCtxt, TyKind};

struct ShimBuilder {
    locals: Vec<LocalDecl>,
    blocks: Vec<BasicBlockData>,
}

impl ShimBuilder {
    fn new(ret: Ty, params: &[Ty]) -> Self {
        let mut b = ShimBuilder {
            locals: Vec::new(),
            blocks: Vec::new(),
        };
        b.local(ret);
        for &p in params {
            b.local(p);
        }
        b.block();
        b
    }

    fn local(&mut self, ty: Ty) -> Local {
        self.locals.push(LocalDecl {
            ty,
            mutable: true,
            name: None,
            span: Span::DUMMY,
        });
        Local(self.locals.len() as u32 - 1)
    }

    fn block(&mut self) -> BasicBlock {
        self.blocks.push(BasicBlockData {
            stmts: Vec::new(),
            terminator: None,
        });
        BasicBlock(self.blocks.len() as u32 - 1)
    }

    fn assign(&mut self, bb: BasicBlock, p: Place, rv: Rvalue) {
        self.blocks[bb.index()].stmts.push(Statement {
            kind: StatementKind::Assign(p, rv),
            span: Span::DUMMY,
        });
    }

    fn terminate(&mut self, bb: BasicBlock, kind: TerminatorKind) {
        self.blocks[bb.index()].terminator = Some(Terminator {
            kind,
            span: Span::DUMMY,
        });
    }

    /// Calls `func(args)` into `dest` at the end of `bb`; returns the block after it.
    fn call(
        &mut self,
        bb: BasicBlock,
        func: Operand,
        args: Vec<Operand>,
        dest: Place,
    ) -> BasicBlock {
        let next = self.block();
        self.terminate(
            bb,
            TerminatorKind::Call {
                func,
                args,
                destination: dest,
                target: Some(next),
            },
        );
        next
    }

    fn finish(self, def: DefId, arg_count: usize) -> Body {
        Body {
            source: MirSource::Shim(def),
            locals: self.locals,
            arg_count,
            blocks: self.blocks,
            span: Span::DUMMY,
            c_variadic: false,
        }
    }
}

/// The MIR of a shim instance (`None` for other instances).
pub fn build_shim(tcx: &TyCtxt<'_>, inst: Instance) -> Option<Body> {
    match inst.kind {
        InstanceKind::ClosureCallShim(method) => closure_call_shim(tcx, method, inst.args),
        InstanceKind::FnPtrCallShim(method) => fn_ptr_call_shim(tcx, method, inst.args),
        InstanceKind::CloneShim => clone_shim(tcx, inst.args),
        _ => None,
    }
}

/// Which of `call`, `call_mut`, `call_once` a method is.
fn method_kind(tcx: &TyCtxt<'_>, method: DefId) -> Option<ClosureKind> {
    tcx.fn_trait_kind(tcx.assoc_container(method)?)
}

/// `self` of `Fn::call` (`&F`), `FnMut::call_mut` (`&mut F`), `FnOnce::call_once` (`F`).
fn self_ty(kind: ClosureKind, f: Ty) -> Ty {
    match kind {
        ClosureKind::Fn => Ty::reference(f, Mutability::Not),
        ClosureKind::FnMut => Ty::reference(f, Mutability::Mut),
        ClosureKind::FnOnce => f,
    }
}

/// The argument tuple's fields, moved out one by one.
fn untuple(tuple_local: Local, tuple_ty: Ty) -> Vec<Operand> {
    let p = Place::local(tuple_local);
    tuple_ty
        .tuple_fields()
        .iter()
        .enumerate()
        .map(|(i, &t)| Operand::Move(p.field(i as u32, t)))
        .collect()
}

/// `<closure as Fn*>::call*(self, (args…))`: the closure's body with its environment in the
/// form it takes it (`&C`, `&mut C` or `C`) and the arguments untupled.
fn closure_call_shim(tcx: &TyCtxt<'_>, method: DefId, args: Args) -> Option<Body> {
    let closure_ty = args.ty(0);
    let tuple_ty = args.ty(1);
    let TyKind::Closure(_, cargs) = *closure_ty.kind() else {
        return None;
    };
    let called_as = method_kind(tcx, method)?;
    let closure_kind = closure_kind_from_args(cargs)?;
    let ret = crate::normalize_erasing(tcx, closure_sig_from_args(cargs)?.output());
    let mut b = ShimBuilder::new(ret, &[self_ty(called_as, closure_ty), tuple_ty]);
    let this = Local(1);
    let bb = BasicBlock::START;
    let env = if called_as == closure_kind {
        Operand::Move(Place::local(this))
    } else {
        // A closure called as a trait it more than implements: borrow the environment.
        let m = if closure_kind == ClosureKind::FnMut {
            Mutability::Mut
        } else {
            Mutability::Not
        };
        let place = if called_as == ClosureKind::FnOnce {
            Place::local(this)
        } else {
            Place::local(this).deref()
        };
        let r = b.local(Ty::reference(closure_ty, m));
        b.assign(bb, Place::local(r), Rvalue::Ref(m, place));
        Operand::Move(Place::local(r))
    };
    let mut call_args = vec![env];
    call_args.extend(untuple(Local(2), tuple_ty));
    let func = Operand::constant(closure_ty, ConstValue::ZeroSized);
    let mut next = b.call(bb, func, call_args, Place::ret());
    // `call_once` on a closure that borrowed its environment: the environment ends here.
    if called_as == ClosureKind::FnOnce && closure_kind != ClosureKind::FnOnce {
        let after = b.block();
        b.terminate(
            next,
            TerminatorKind::Drop {
                place: Place::local(this),
                target: after,
            },
        );
        next = after;
    }
    b.terminate(next, TerminatorKind::Return);
    Some(b.finish(method, 2))
}

/// `<fn item or fn pointer as Fn*>::call*(self, (args…))`: a direct call.
fn fn_ptr_call_shim(tcx: &TyCtxt<'_>, method: DefId, args: Args) -> Option<Body> {
    let f = args.ty(0);
    let tuple_ty = args.ty(1);
    let called_as = method_kind(tcx, method)?;
    let sig = match *f.kind() {
        TyKind::FnDef(d, a) => tcx.fn_sig(d).subst(a),
        TyKind::FnPtr(sig) => sig,
        _ => return None,
    };
    let ret = crate::normalize_erasing(tcx, sig.output());
    let mut b = ShimBuilder::new(ret, &[self_ty(called_as, f), tuple_ty]);
    let this = Place::local(Local(1));
    let bb = BasicBlock::START;
    let call_args = untuple(Local(2), tuple_ty);
    match *f.kind() {
        // Tuple struct and variant constructors build the value.
        TyKind::FnDef(d, cargs)
            if matches!(tcx.hir.def_kind(d), DefKind::Struct | DefKind::Variant) =>
        {
            let (adt, v) = match tcx.hir.def_kind(d) {
                DefKind::Variant => {
                    let adt = tcx.hir.parent(d)?;
                    (adt, tcx.adt_def(adt).variant_index(d).unwrap_or(0) as u32)
                }
                _ => (d, 0),
            };
            b.assign(
                bb,
                Place::ret(),
                Rvalue::Aggregate(AggregateKind::Adt(adt, v, cargs, None), call_args),
            );
            b.terminate(bb, TerminatorKind::Return);
        }
        TyKind::FnDef(..) => {
            let next = b.call(
                bb,
                Operand::constant(f, ConstValue::ZeroSized),
                call_args,
                Place::ret(),
            );
            b.terminate(next, TerminatorKind::Return);
        }
        _ => {
            let callee = if called_as == ClosureKind::FnOnce {
                this
            } else {
                this.deref()
            };
            let next = b.call(bb, Operand::Copy(callee), call_args, Place::ret());
            b.terminate(next, TerminatorKind::Return);
        }
    }
    Some(b.finish(method, 2))
}

fn is_copy(tcx: &TyCtxt<'_>, t: Ty) -> bool {
    let Some(copy) = tcx.lang_item("copy") else {
        return false;
    };
    let infcx = InferCtxt::new();
    let env = ParamEnv::empty();
    let solver = Solver::new(tcx, &infcx, &env, &NoClosures);
    solver.evaluate(Predicate::Trait(TraitRef::new(copy, Args::from_tys(&[t])))) == Eval::Holds
}

/// `Clone::clone(&self)` for tuples, closures and function types: a copy when the type is
/// `Copy`, else each field cloned.
fn clone_shim(tcx: &TyCtxt<'_>, args: Args) -> Option<Body> {
    let t = args.ty(0);
    let clone_trait = tcx.lang_item("clone")?;
    let clone_fn = tcx.assoc_item(clone_trait, Symbol::intern("clone"), true)?;
    let mut b = ShimBuilder::new(t, &[Ty::reference(t, Mutability::Not)]);
    let src = Place::local(Local(1)).deref();
    let mut bb = BasicBlock::START;
    let fields: Vec<Ty> = match *t.kind() {
        TyKind::Tuple(_) => t.tuple_fields().to_vec(),
        TyKind::Closure(_, cargs) => hyprc_ty::traits::closure_upvars_from_args(cargs)?,
        _ => Vec::new(),
    };
    if fields.is_empty() || is_copy(tcx, t) {
        b.assign(bb, Place::ret(), Rvalue::Use(Operand::Copy(src)));
    } else {
        let mut ops = Vec::with_capacity(fields.len());
        for (i, &ft) in fields.iter().enumerate() {
            let field = src.field(i as u32, ft);
            if is_copy(tcx, ft) {
                ops.push(Operand::Copy(field));
                continue;
            }
            let r = b.local(Ty::reference(ft, Mutability::Not));
            b.assign(bb, Place::local(r), Rvalue::Ref(Mutability::Not, field));
            let v = b.local(ft);
            let func = Operand::constant(
                Ty::fn_def(clone_fn, Args::from_tys(&[ft])),
                ConstValue::ZeroSized,
            );
            bb = b.call(
                bb,
                func,
                vec![Operand::Move(Place::local(r))],
                Place::local(v),
            );
            ops.push(Operand::Move(Place::local(v)));
        }
        let kind = match *t.kind() {
            TyKind::Closure(c, cargs) => AggregateKind::Closure(c, cargs),
            _ => AggregateKind::Tuple,
        };
        b.assign(bb, Place::ret(), Rvalue::Aggregate(kind, ops));
    }
    b.terminate(bb, TerminatorKind::Return);
    Some(b.finish(clone_fn, 1))
}
