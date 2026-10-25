//! Monomorphization: from the program's roots, every function instance (function and
//! generic arguments) that can run, with trait method calls resolved to impl methods.

use crate::mir::*;
use crate::{build, monomorphize};
use hyprc_hir as hir;
use hyprc_hir::{BodyId, DefId, DefKind};
use hyprc_span::{FxHashMap, FxHashSet};
use hyprc_ty::infer::InferCtxt;
use hyprc_ty::traits::{NoClosures, ParamEnv, SelectResult, SelectionKind, Solver};
use hyprc_ty::{Args, ClosureRef, TraitRef, Ty, TyCtxt, TyKind};
use std::sync::{Arc, Mutex};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum InstanceKind {
    /// A function with a body.
    Item(DefId),
    /// A closure's body.
    Closure(ClosureRef),
    /// A function defined elsewhere (an `extern` block): just a symbol.
    Foreign(DefId),
    /// A compiler intrinsic (`#[rustc_intrinsic]`), expanded at the call.
    Intrinsic(DefId),
    /// A method called through a `dyn` vtable: the trait method.
    Virtual(DefId),
    /// `<closure as Fn*>::call*(env, (args…))` (by the trait method): unpacks the argument
    /// tuple and calls the closure's body.
    ClosureCallShim(DefId),
    /// `<fn ptr or fn item as Fn*>::call*(f, (args…))`.
    FnPtrCallShim(DefId),
    /// `Clone::clone` for a type the compiler implements it for (tuples, closures, function
    /// types): a copy, or each field cloned.
    CloneShim,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Instance {
    pub kind: InstanceKind,
    pub args: Args,
}

impl Instance {
    pub fn item(def: DefId, args: Args) -> Instance {
        Instance {
            kind: InstanceKind::Item(def),
            args,
        }
    }
}

/// Which MIR body an instance runs.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum MirKey {
    Body(BodyId),
    Closure(BodyId, u32),
}

pub struct MonoCtxt<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    pub overflow_checks: bool,
    mir: Mutex<FxHashMap<MirKey, Arc<Body>>>,
    shims: Mutex<FxHashMap<Instance, Arc<Body>>>,
}

impl<'a, 'h> MonoCtxt<'a, 'h> {
    pub fn new(tcx: &'a TyCtxt<'h>, overflow_checks: bool) -> Self {
        MonoCtxt {
            tcx,
            overflow_checks,
            mir: Mutex::new(FxHashMap::default()),
            shims: Mutex::new(FxHashMap::default()),
        }
    }

    /// The HIR body of a function definition.
    pub fn body_of(&self, def: DefId) -> Option<BodyId> {
        let item = self.tcx.hir.get_item(def)?;
        match &item.kind {
            hir::ItemKind::Fn(f) => f.body,
            hir::ItemKind::Const { body, .. } | hir::ItemKind::Static { body, .. } => *body,
            _ => None,
        }
    }

    pub fn mir(&self, key: MirKey) -> Arc<Body> {
        if let Some(b) = self.mir.lock().unwrap().get(&key) {
            return b.clone();
        }
        let body = Arc::new(match key {
            MirKey::Body(b) => build::build(self.tcx, b, self.overflow_checks),
            MirKey::Closure(b, i) => {
                build::build_closure(self.tcx, b, hyprc_hir::ClosureId(i), self.overflow_checks)
            }
        });
        self.mir.lock().unwrap().entry(key).or_insert(body).clone()
    }

    pub fn instance_mir(&self, inst: Instance) -> Option<Arc<Body>> {
        match inst.kind {
            InstanceKind::Item(def) => Some(self.mir(MirKey::Body(self.body_of(def)?))),
            InstanceKind::Closure(c) => Some(self.mir(MirKey::Closure(BodyId(c.body), c.index))),
            InstanceKind::ClosureCallShim(_)
            | InstanceKind::FnPtrCallShim(_)
            | InstanceKind::CloneShim => {
                if let Some(b) = self.shims.lock().unwrap().get(&inst) {
                    return Some(b.clone());
                }
                let body = Arc::new(crate::shim::build_shim(self.tcx, inst)?);
                Some(
                    self.shims
                        .lock()
                        .unwrap()
                        .entry(inst)
                        .or_insert(body)
                        .clone(),
                )
            }
            _ => None,
        }
    }

    /// Does the instance have a MIR body to compile?
    pub fn has_body(&self, inst: Instance) -> bool {
        matches!(
            inst.kind,
            InstanceKind::Item(_)
                | InstanceKind::Closure(_)
                | InstanceKind::ClosureCallShim(_)
                | InstanceKind::FnPtrCallShim(_)
                | InstanceKind::CloneShim
        )
    }

    /// Resolves a call of `def` with (concrete) `args` to what runs.
    pub fn resolve(&self, def: DefId, args: Args) -> Option<Instance> {
        let tcx = self.tcx;
        let item = tcx.hir.get_item(def);
        if let Some(it) = item {
            if it.attrs.rustc_intrinsic {
                return Some(Instance {
                    kind: InstanceKind::Intrinsic(def),
                    args,
                });
            }
            if let hir::ItemKind::Fn(f) = &it.kind {
                if f.foreign {
                    return Some(Instance {
                        kind: InstanceKind::Foreign(def),
                        args,
                    });
                }
                if f.sig.abi == hir::Abi::Other(hyprc_span::Symbol::intern("rust-intrinsic")) {
                    return Some(Instance {
                        kind: InstanceKind::Intrinsic(def),
                        args,
                    });
                }
            }
        }
        let container = tcx.assoc_container(def);
        let Some(trait_) = container.filter(|&c| tcx.is_trait(c)) else {
            return Some(Instance::item(def, args));
        };
        // A trait method: find the impl for the concrete self type.
        let trait_count = tcx.generics_of(trait_).count() as usize;
        let trait_args = args.truncate(trait_count);
        let own_args = &args.as_slice()[trait_count.min(args.len())..];
        let self_ty = trait_args.ty(0);
        if matches!(self_ty.kind(), TyKind::Dynamic(_)) {
            return Some(Instance {
                kind: InstanceKind::Virtual(def),
                args,
            });
        }
        let infcx = InferCtxt::new();
        let env = ParamEnv::empty();
        let solver = Solver::new(tcx, &infcx, &env, &NoClosures);
        let tr = TraitRef::new(trait_, trait_args);
        match solver.select(tr) {
            SelectResult::Ok(sel) => match sel.kind {
                SelectionKind::Impl {
                    def: imp,
                    args: impl_args,
                } => {
                    let impl_args = infcx.resolve_args(impl_args);
                    let name = tcx.hir.name(def);
                    // The impl's method, or (specialization) the one it inherits.
                    match solver.impl_item(imp, impl_args, name, true) {
                        Some((m, impl_args)) => Some(Instance::item(m, impl_args.extend(own_args))),
                        // Not overridden: the trait's default body.
                        None => Some(Instance::item(def, args)),
                    }
                }
                SelectionKind::Closure(_) => match *self_ty.kind() {
                    TyKind::Closure(..) => Some(Instance {
                        kind: InstanceKind::ClosureCallShim(def),
                        args,
                    }),
                    _ => None,
                },
                SelectionKind::FnPointer => Some(Instance {
                    kind: InstanceKind::FnPtrCallShim(def),
                    args,
                }),
                SelectionKind::Builtin => {
                    if tcx.lang_item("clone") == Some(trait_) {
                        Some(Instance {
                            kind: InstanceKind::CloneShim,
                            args,
                        })
                    } else {
                        Some(Instance::item(def, args))
                    }
                }
                _ => Some(Instance::item(def, args)),
            },
            _ => None,
        }
    }

    /// Every instance reachable from `roots`.
    pub fn collect(&self, roots: Vec<Instance>) -> (Vec<Instance>, Vec<DefId>) {
        let mut seen: FxHashSet<Instance> = FxHashSet::default();
        let mut statics: Vec<DefId> = Vec::new();
        let mut work = roots;
        let mut out = Vec::new();
        while let Some(inst) = work.pop() {
            if !seen.insert(inst) {
                continue;
            }
            out.push(inst);
            let body = if self.has_body(inst) {
                self.instance_mir(inst)
            } else {
                None
            };
            let Some(body) = body else { continue };
            let mut visit_const = |c: &Constant, called: bool, work: &mut Vec<Instance>| {
                let ty = monomorphize(self.tcx, inst.args, c.ty);
                match *ty.kind() {
                    TyKind::FnDef(d, a) => {
                        if matches!(self.tcx.hir.def_kind(d), DefKind::Struct | DefKind::Variant) {
                            return;
                        }
                        if let Some(i) = self.resolve(d, a) {
                            work.push(i);
                        }
                    }
                    TyKind::Closure(cref, a) if called => {
                        work.push(Instance {
                            kind: InstanceKind::Closure(cref),
                            args: a,
                        });
                    }
                    _ => {}
                }
                if let ConstValue::StaticRef(d) = c.kind
                    && !statics.contains(&d)
                {
                    statics.push(d);
                }
            };
            for bb in &body.blocks {
                for s in &bb.stmts {
                    if let StatementKind::Assign(_, rv) = &s.kind {
                        for_each_operand(rv, &mut |o| {
                            if let Operand::Constant(c) = o {
                                visit_const(c, false, &mut work);
                            }
                        });
                        if let Rvalue::Cast(CastKind::ClosureFnPointer, op, _) = rv {
                            let ty = self.operand_ty(&body, op, inst.args);
                            if let TyKind::Closure(cref, a) = *ty.kind() {
                                work.push(Instance {
                                    kind: InstanceKind::Closure(cref),
                                    args: a,
                                });
                            }
                        }
                    }
                }
                if let Some(t) = &bb.terminator
                    && let TerminatorKind::Call { func, args, .. } = &t.kind
                {
                    match func {
                        Operand::Constant(c) => visit_const(c, true, &mut work),
                        op => {
                            let ty = self.operand_ty(&body, op, inst.args);
                            if let TyKind::Closure(cref, a) = *ty.kind() {
                                work.push(Instance {
                                    kind: InstanceKind::Closure(cref),
                                    args: a,
                                });
                            }
                        }
                    }
                    for a in args {
                        if let Operand::Constant(c) = a {
                            visit_const(c, false, &mut work);
                        }
                    }
                }
            }
        }
        (out, statics)
    }

    pub fn operand_ty(&self, body: &Body, op: &Operand, args: Args) -> Ty {
        match op {
            Operand::Constant(c) => monomorphize(self.tcx, args, c.ty),
            Operand::Copy(p) | Operand::Move(p) => {
                monomorphize(self.tcx, args, place_ty(self.tcx, body, p))
            }
        }
    }
}

/// The type of a place in a (generic) body.
pub fn place_ty(tcx: &TyCtxt<'_>, body: &Body, p: &Place) -> Ty {
    let mut t = body.local_ty(p.local);
    for e in &p.projection {
        t = projection_ty(tcx, t, e);
    }
    t
}

pub fn projection_ty(tcx: &TyCtxt<'_>, t: Ty, e: &PlaceElem) -> Ty {
    match e {
        PlaceElem::Deref => match *t.kind() {
            TyKind::Ref(inner, _) | TyKind::RawPtr(inner, _) => inner,
            TyKind::Adt(d, args) if tcx.adt_def(d).is_box => args.ty(0),
            _ => Ty::ERROR,
        },
        PlaceElem::Field(_, ty) => *ty,
        PlaceElem::Index(_) | PlaceElem::ConstantIndex { .. } => {
            t.builtin_index().unwrap_or(Ty::ERROR)
        }
        PlaceElem::Subslice { from, to, from_end } => match *t.kind() {
            TyKind::Array(e, n) if !from_end => {
                let len = n.try_to_usize().unwrap_or(0);
                Ty::array(
                    e,
                    hyprc_ty::Const::from_usize(len.saturating_sub(from + to)),
                )
            }
            TyKind::Array(e, _) | TyKind::Slice(e) => Ty::slice(e),
            _ => Ty::ERROR,
        },
        PlaceElem::Downcast(_) => t,
    }
}

pub fn for_each_operand(rv: &Rvalue, f: &mut dyn FnMut(&Operand)) {
    match rv {
        Rvalue::Use(o) | Rvalue::Repeat(o, _) | Rvalue::Cast(_, o, _) | Rvalue::UnaryOp(_, o) => {
            f(o)
        }
        Rvalue::BinaryOp(_, a, b) | Rvalue::CheckedBinaryOp(_, a, b) => {
            f(a);
            f(b);
        }
        Rvalue::Aggregate(_, ops) => ops.iter().for_each(f),
        _ => {}
    }
}

/// The program's roots: `main` for binaries, and every function that must exist by name
/// (`#[no_mangle]`, `#[export_name]`).
pub fn roots(tcx: &TyCtxt<'_>, mcx: &MonoCtxt<'_, '_>) -> Vec<Instance> {
    let mut out = Vec::new();
    for item in tcx.hir.items.iter().flatten() {
        if let hir::ItemKind::Fn(f) = &item.kind
            && f.body.is_some()
            && (item.attrs.no_mangle || item.attrs.export_name.is_some())
            && tcx.generics_of(item.def).count() == 0
        {
            out.push(Instance::item(item.def, Args::EMPTY));
        }
    }
    if !tcx.hir.no_main
        && let Some(main) = tcx.hir.entry
        && mcx.body_of(main).is_some()
    {
        out.push(Instance::item(main, Args::EMPTY));
    }
    out
}
