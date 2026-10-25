//! Building MIR from typed HIR.

mod expr;
mod matches;

use crate::mir::*;
use hyprc_hir as hir;
use hyprc_hir::{BodyId, ClosureId, ExprId, LocalId, LoopId, Mutability};
use hyprc_span::{FxHashMap, Span};
use hyprc_ty::typeck::{CaptureKind, TypeckResults};
use hyprc_ty::{Args, ClosureRef, Ty, TyCtxt, TyKind};
use std::sync::Arc;

pub(crate) struct LoopScope {
    pub break_block: BasicBlock,
    pub continue_block: BasicBlock,
    pub dest: Place,
}

pub(crate) struct Builder<'a, 'h> {
    pub tcx: &'a TyCtxt<'h>,
    pub hir: &'h hir::Body,
    pub body_id: BodyId,
    pub tr: Arc<TypeckResults>,
    pub locals: Vec<LocalDecl>,
    pub blocks: Vec<BasicBlockData>,
    /// HIR locals → MIR places (usually a local; in closures, captured variables are
    /// places in the environment).
    pub var_map: FxHashMap<LocalId, Place>,
    pub loops: FxHashMap<LoopId, LoopScope>,
    pub span: Span,
    /// Generating a closure body: which closure, and its environment argument's form.
    pub closure: Option<(ClosureId, ClosureRef)>,
    pub overflow_checks: bool,
}

/// Builds the MIR of a body (a function, constant or static).
pub fn build(tcx: &TyCtxt<'_>, body_id: BodyId, overflow_checks: bool) -> Body {
    let hb = tcx.hir.body(body_id);
    let tr = tcx.typeck(body_id);
    let mut b = Builder::new(tcx, hb, body_id, tr, overflow_checks);
    let source = match hb.kind {
        hir::BodyKind::AnonConst => MirSource::AnonConst(hb.owner, body_id.0),
        _ => MirSource::Item(hb.owner),
    };
    let ret_ty = match hb.kind {
        hir::BodyKind::Fn => b.tcx.fn_sig(hb.owner).output(),
        hir::BodyKind::Const | hir::BodyKind::Static => b.tcx.type_of(hb.owner),
        hir::BodyKind::AnonConst => b.tr.expr_ty(hb.value),
    };
    let ret_ty = crate::normalize_in(tcx, hb.owner, ret_ty);
    b.new_local(ret_ty, None, hb.span, true);
    let param_tys: Vec<Ty> = hb.params.iter().map(|p| b.tr.pat_ty(*p)).collect();
    let mut c_variadic = false;
    if hb.kind == hir::BodyKind::Fn {
        c_variadic = tcx.fn_sig(hb.owner).c_variadic;
    }
    let args = b.declare_params(&hb.params.clone(), &param_tys);
    let start = b.new_block();
    let mut block = start;
    block = b.bind_params(block, &hb.params.clone(), &args);
    let value = hb.value;
    let end = b.expr_into(Place::ret(), block, value);
    b.terminate(end, TerminatorKind::Return, hb.span);
    b.finish(source, param_tys.len(), c_variadic)
}

/// Builds the MIR of a closure in a body. Parameters: the environment (`self`), then the
/// closure's own parameters.
pub fn build_closure(
    tcx: &TyCtxt<'_>,
    body_id: BodyId,
    id: ClosureId,
    overflow_checks: bool,
) -> Body {
    let hb = tcx.hir.body(body_id);
    let tr = tcx.typeck(body_id);
    let mut b = Builder::new(tcx, hb, body_id, tr.clone(), overflow_checks);
    let data = &hb.closures[id.index()];
    let result = tr.closures[id.index()]
        .clone()
        .expect("closure was type checked");
    let cref = ClosureRef {
        owner: hb.owner,
        body: body_id.0,
        index: id.0,
    };
    b.closure = Some((id, cref));
    b.new_local(result.sig.output(), None, data.span, true);
    // The environment: by value for `FnOnce`, else by reference.
    let env_ty = match result.kind {
        hyprc_ty::collect::ClosureKind::FnOnce => result.ty,
        hyprc_ty::collect::ClosureKind::FnMut => Ty::reference(result.ty, Mutability::Mut),
        hyprc_ty::collect::ClosureKind::Fn => Ty::reference(result.ty, Mutability::Not),
    };
    let env = b.new_local(env_ty, None, data.span, false);
    let env_place = if result.kind == hyprc_ty::collect::ClosureKind::FnOnce {
        Place::local(env)
    } else {
        Place::local(env).deref()
    };
    for (i, up) in result.upvars.iter().enumerate() {
        let field_ty = match up.kind {
            CaptureKind::ByValue => up.ty,
            CaptureKind::ByRef(m) => Ty::reference(up.ty, m),
        };
        let p = env_place.field(i as u32, field_ty);
        let place = match up.kind {
            CaptureKind::ByValue => p,
            CaptureKind::ByRef(_) => p.deref(),
        };
        b.var_map.insert(up.local, place);
    }
    let pats: Vec<hir::PatId> = data.params.iter().map(|(p, _)| *p).collect();
    let param_tys: Vec<Ty> = result.sig.inputs().to_vec();
    let args = b.declare_params(&pats, &param_tys);
    let start = b.new_block();
    let block = b.bind_params(start, &pats, &args);
    let end = b.expr_into(Place::ret(), block, data.body);
    b.terminate(end, TerminatorKind::Return, data.span);
    b.finish(MirSource::Closure(cref), param_tys.len() + 1, false)
}

impl<'a, 'h> Builder<'a, 'h> {
    fn new(
        tcx: &'a TyCtxt<'h>,
        hir: &'h hir::Body,
        body_id: BodyId,
        tr: Arc<TypeckResults>,
        overflow_checks: bool,
    ) -> Self {
        Builder {
            tcx,
            hir,
            body_id,
            tr,
            locals: Vec::new(),
            blocks: Vec::new(),
            var_map: FxHashMap::default(),
            loops: FxHashMap::default(),
            span: hir.span,
            closure: None,
            overflow_checks,
        }
    }

    fn finish(self, source: MirSource, arg_count: usize, c_variadic: bool) -> Body {
        let mut blocks = self.blocks;
        // Blocks left open (after `return` or `break`) are unreachable.
        for b in blocks.iter_mut() {
            if b.terminator.is_none() {
                b.terminator = Some(Terminator {
                    kind: TerminatorKind::Unreachable,
                    span: self.span,
                });
            }
        }
        Body {
            source,
            locals: self.locals,
            arg_count,
            blocks,
            span: self.span,
            c_variadic,
        }
    }

    /// Normalizes a type from typeck results (projections the body's where-clauses fix).
    pub(crate) fn norm(&self, t: Ty) -> Ty {
        crate::normalize_in(self.tcx, self.hir.owner, t)
    }

    pub(crate) fn expr_ty(&self, e: ExprId) -> Ty {
        self.norm(self.tr.expr_ty(e))
    }

    pub(crate) fn expr_ty_adjusted(&self, e: ExprId) -> Ty {
        self.norm(self.tr.expr_ty_adjusted(e))
    }

    pub(crate) fn new_local(
        &mut self,
        ty: Ty,
        name: Option<hyprc_span::Symbol>,
        span: Span,
        mutable: bool,
    ) -> Local {
        self.locals.push(LocalDecl {
            ty,
            mutable,
            name,
            span,
        });
        Local(self.locals.len() as u32 - 1)
    }

    pub(crate) fn temp(&mut self, ty: Ty, span: Span) -> Local {
        self.new_local(ty, None, span, true)
    }

    pub(crate) fn new_block(&mut self) -> BasicBlock {
        self.blocks.push(BasicBlockData {
            stmts: Vec::new(),
            terminator: None,
        });
        BasicBlock(self.blocks.len() as u32 - 1)
    }

    pub(crate) fn push(&mut self, block: BasicBlock, kind: StatementKind, span: Span) {
        let b = &mut self.blocks[block.index()];
        if b.terminator.is_none() {
            b.stmts.push(Statement { kind, span });
        }
    }

    pub(crate) fn assign(&mut self, block: BasicBlock, place: Place, rv: Rvalue, span: Span) {
        self.push(block, StatementKind::Assign(place, rv), span);
    }

    pub(crate) fn terminate(&mut self, block: BasicBlock, kind: TerminatorKind, span: Span) {
        let b = &mut self.blocks[block.index()];
        if b.terminator.is_none() {
            b.terminator = Some(Terminator { kind, span });
        }
    }

    pub(crate) fn goto(&mut self, from: BasicBlock, to: BasicBlock, span: Span) {
        self.terminate(from, TerminatorKind::Goto(to), span);
    }

    fn declare_params(&mut self, pats: &[hir::PatId], tys: &[Ty]) -> Vec<Local> {
        let mut out = Vec::new();
        for (i, &p) in pats.iter().enumerate() {
            let ty = self.norm(tys.get(i).copied().unwrap_or(Ty::ERROR));
            let name = match &self.hir.pat(p).kind {
                hir::PatKind::Binding {
                    local, sub: None, ..
                } => Some(self.hir.local(*local).name.name),
                _ => None,
            };
            let l = self.new_local(ty, name, self.hir.pat(p).span, true);
            out.push(l);
        }
        out
    }

    fn bind_params(
        &mut self,
        mut block: BasicBlock,
        pats: &[hir::PatId],
        args: &[Local],
    ) -> BasicBlock {
        for (&p, &arg) in pats.iter().zip(args) {
            match &self.hir.pat(p).kind {
                // A plain binding is the argument itself.
                hir::PatKind::Binding {
                    mode: hir::BindingMode::Value { .. },
                    local,
                    sub: None,
                } if !self.tr.pat_adjustments.contains_key(&p) => {
                    self.var_map.insert(*local, Place::local(arg));
                }
                _ => {
                    block = self.bind_irrefutable(block, p, Place::local(arg));
                }
            }
        }
        block
    }

    /// The MIR place of a HIR local, declaring it on first use.
    pub(crate) fn var_place(&mut self, l: LocalId) -> Place {
        if let Some(p) = self.var_map.get(&l) {
            return p.clone();
        }
        let data = self.hir.local(l);
        let ty = self.norm(self.tr.local_tys[l.index()]);
        let local = self.new_local(ty, Some(data.name.name), data.span, data.mutable);
        let p = Place::local(local);
        self.var_map.insert(l, p.clone());
        p
    }

    /// Is a type `Copy` (so reading a place copies rather than moves)?
    pub(crate) fn is_copy(&self, t: Ty) -> bool {
        match t.kind() {
            TyKind::Bool
            | TyKind::Char
            | TyKind::Int(_)
            | TyKind::Uint(_)
            | TyKind::Float(_)
            | TyKind::RawPtr(..)
            | TyKind::FnDef(..)
            | TyKind::FnPtr(_)
            | TyKind::Never => true,
            TyKind::Ref(_, Mutability::Not) => true,
            TyKind::Ref(_, Mutability::Mut) => false,
            _ => {
                let Some(copy) = self.tcx.lang_item("copy") else {
                    return false;
                };
                let infcx = hyprc_ty::infer::InferCtxt::new();
                let env = hyprc_ty::traits::ParamEnv::for_item(self.tcx, self.hir.owner);
                let solver = hyprc_ty::traits::Solver::new(
                    self.tcx,
                    &infcx,
                    &env,
                    &hyprc_ty::traits::NoClosures,
                );
                solver.evaluate(hyprc_ty::Predicate::Trait(hyprc_ty::TraitRef::new(
                    copy,
                    Args::from_tys(&[t]),
                ))) == hyprc_ty::traits::Eval::Holds
            }
        }
    }

    pub(crate) fn operand_from_place(&self, p: Place, ty: Ty) -> Operand {
        if self.is_copy(ty) {
            Operand::Copy(p)
        } else {
            Operand::Move(p)
        }
    }
}
