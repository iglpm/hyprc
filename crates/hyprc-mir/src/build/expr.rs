//! Expressions to MIR.

use super::{Builder, LoopScope};
use crate::mir::*;
use hyprc_hir as hir;
use hyprc_hir::{BinOpKind, BorrowKind, DefKind, ExprId, ExprKind, Mutability, Res};
use hyprc_span::Span;
use hyprc_syntax::token::LitKind;
use hyprc_ty::typeck::{Adjust, Adjustment};
use hyprc_ty::{Args, Const, ConstKind, Ty, TyKind};
use std::sync::Arc;

/// A value being built: a place to read from, or an operand.
pub(crate) enum Val {
    Place(Place),
    Op(Operand),
}

impl<'a, 'h> Builder<'a, 'h> {
    fn span_of(&self, e: ExprId) -> Span {
        self.hir.expr(e).span
    }

    fn adjustments(&self, e: ExprId) -> Vec<Adjustment> {
        self.tr.adjustments.get(&e).cloned().unwrap_or_default()
    }

    // ---------------------------------------------------------------------------------------
    // Entry points

    /// Evaluates `e` (adjustments included) into `dest`; returns the block after.
    pub(crate) fn expr_into(&mut self, dest: Place, block: BasicBlock, e: ExprId) -> BasicBlock {
        if self.tr.adjustments.contains_key(&e) {
            let span = self.span_of(e);
            let (b, op) = self.as_operand(block, e);
            self.assign(b, dest, Rvalue::Use(op), span);
            return b;
        }
        self.expr_into_unadjusted(dest, block, e)
    }

    pub(crate) fn as_operand(&mut self, block: BasicBlock, e: ExprId) -> (BasicBlock, Operand) {
        let ty = self.expr_ty_adjusted(e);
        let (b, v) = self.as_val(block, e, false);
        match v {
            Val::Op(o) => (b, o),
            Val::Place(p) => (b, self.operand_from_place(p, ty)),
        }
    }

    pub(crate) fn as_place(
        &mut self,
        block: BasicBlock,
        e: ExprId,
        mutable: bool,
    ) -> (BasicBlock, Place) {
        let ty = self.expr_ty_adjusted(e);
        let (b, v) = self.as_val(block, e, mutable);
        match v {
            Val::Place(p) => (b, p),
            Val::Op(o) => {
                let t = self.temp(ty, self.span_of(e));
                self.assign(b, Place::local(t), Rvalue::Use(o), self.span_of(e));
                (b, Place::local(t))
            }
        }
    }

    /// An operand in a temporary local (for indices, which must be locals).
    fn as_local_operand(&mut self, block: BasicBlock, e: ExprId) -> (BasicBlock, Local) {
        let ty = self.expr_ty_adjusted(e);
        let (b, op) = self.as_operand(block, e);
        let t = self.temp(ty, self.span_of(e));
        self.assign(b, Place::local(t), Rvalue::Use(op), self.span_of(e));
        (b, t)
    }

    fn as_val(&mut self, block: BasicBlock, e: ExprId, mutable: bool) -> (BasicBlock, Val) {
        let adjs = self.adjustments(e);
        // A `&mut` borrow among the adjustments makes the place before it mutable.
        let needs_mut = mutable
            || adjs.iter().any(|a| {
                matches!(
                    a.kind,
                    Adjust::Borrow(Mutability::Mut) | Adjust::RawBorrow(Mutability::Mut)
                )
            });
        let (mut b, mut v) = self.as_val_unadjusted(block, e, needs_mut);
        let span = self.span_of(e);
        for (i, a) in adjs.iter().enumerate() {
            let later_mut = mutable
                || adjs[i + 1..].iter().any(|a| {
                    matches!(
                        a.kind,
                        Adjust::Borrow(Mutability::Mut) | Adjust::RawBorrow(Mutability::Mut)
                    )
                });
            let target = self.norm(a.target);
            match a.kind {
                Adjust::Deref(None) => {
                    let (nb, p) = self.val_to_place(b, v, span);
                    b = nb;
                    v = Val::Place(p.deref());
                }
                Adjust::Deref(Some(o)) => {
                    let (nb, p) = self.val_to_place(b, v, span);
                    b = nb;
                    let (nb, p) = self.overloaded_deref(
                        b,
                        p,
                        o.method,
                        o.args,
                        later_mut || o.mutbl == Mutability::Mut,
                        target,
                        span,
                    );
                    b = nb;
                    v = Val::Place(p);
                }
                Adjust::Borrow(m) => {
                    let (nb, p) = self.val_to_place(b, v, span);
                    b = nb;
                    let t = self.temp(target, span);
                    self.assign(b, Place::local(t), Rvalue::Ref(m, p), span);
                    v = Val::Place(Place::local(t));
                }
                Adjust::RawBorrow(m) => {
                    let (nb, p) = self.val_to_place(b, v, span);
                    b = nb;
                    let t = self.temp(target, span);
                    self.assign(b, Place::local(t), Rvalue::RawPtr(m, p), span);
                    v = Val::Place(Place::local(t));
                }
                Adjust::Unsize
                | Adjust::ReifyFnPointer
                | Adjust::ClosureFnPointer
                | Adjust::MutToConstPointer => {
                    let kind = match a.kind {
                        Adjust::Unsize => CastKind::Unsize,
                        Adjust::ReifyFnPointer => CastKind::ReifyFnPointer,
                        Adjust::ClosureFnPointer => CastKind::ClosureFnPointer,
                        _ => CastKind::PtrToPtr,
                    };
                    let src_ty = if i == 0 {
                        self.expr_ty(e)
                    } else {
                        self.norm(adjs[i - 1].target)
                    };
                    let op = self.val_to_operand(v, src_ty);
                    let t = self.temp(target, span);
                    self.assign(b, Place::local(t), Rvalue::Cast(kind, op, target), span);
                    v = Val::Place(Place::local(t));
                }
                Adjust::NeverToAny => {
                    // The expression diverged; whatever follows is unreachable.
                    let t = self.temp(target, span);
                    v = Val::Place(Place::local(t));
                }
            }
        }
        (b, v)
    }

    fn val_to_place(&mut self, block: BasicBlock, v: Val, span: Span) -> (BasicBlock, Place) {
        match v {
            Val::Place(p) => (block, p),
            Val::Op(o) => {
                let ty = match &o {
                    Operand::Constant(c) => c.ty,
                    _ => Ty::ERROR,
                };
                let t = self.temp(ty, span);
                self.assign(block, Place::local(t), Rvalue::Use(o), span);
                (block, Place::local(t))
            }
        }
    }

    fn val_to_operand(&self, v: Val, ty: Ty) -> Operand {
        match v {
            Val::Op(o) => o,
            Val::Place(p) => self.operand_from_place(p, ty),
        }
    }

    /// `*Deref::deref(&place)` (or `deref_mut`).
    #[allow(clippy::too_many_arguments)]
    fn overloaded_deref(
        &mut self,
        block: BasicBlock,
        place: Place,
        method: hyprc_hir::DefId,
        args: Args,
        mutable: bool,
        target: Ty,
        span: Span,
    ) -> (BasicBlock, Place) {
        let (method, m) = if mutable {
            let dm = self
                .tcx
                .lang_item("deref_mut")
                .and_then(|t| self.tcx.assoc_item(t, hyprc_span::sym::deref_mut, true));
            (dm.unwrap_or(method), Mutability::Mut)
        } else {
            (method, Mutability::Not)
        };
        let self_ty = args.ty(0);
        let r = self.temp(Ty::reference(self_ty, m), span);
        self.assign(block, Place::local(r), Rvalue::Ref(m, place), span);
        let out = self.temp(Ty::reference(target, m), span);
        let next = self.new_block();
        let func = Operand::constant(Ty::fn_def(method, args), ConstValue::ZeroSized);
        self.terminate(
            block,
            TerminatorKind::Call {
                func,
                args: vec![Operand::Move(Place::local(r))],
                destination: Place::local(out),
                target: Some(next),
            },
            span,
        );
        (next, Place::local(out).deref())
    }

    // ---------------------------------------------------------------------------------------
    // Without adjustments

    fn as_val_unadjusted(
        &mut self,
        block: BasicBlock,
        e: ExprId,
        mutable: bool,
    ) -> (BasicBlock, Val) {
        let span = self.span_of(e);
        let ty = self.expr_ty(e);
        match &self.hir.expr(e).kind {
            ExprKind::Path(hir::QPath::Resolved(None, p)) if matches!(p.res, Res::Local(_)) => {
                let Res::Local(l) = p.res else { unreachable!() };
                (block, Val::Place(self.var_place(hir::LocalId(l))))
            }
            ExprKind::Path(hir::QPath::Resolved(None, p))
                if matches!(p.res, Res::Def(DefKind::Static { .. }, _)) =>
            {
                let Res::Def(DefKind::Static { mutable: m }, d) = p.res else {
                    unreachable!()
                };
                let mutbl = if m { Mutability::Mut } else { Mutability::Not };
                let ptr_ty = Ty::ptr(ty, mutbl);
                let t = self.temp(ptr_ty, span);
                self.assign(
                    block,
                    Place::local(t),
                    Rvalue::Use(Operand::constant(ptr_ty, ConstValue::StaticRef(d))),
                    span,
                );
                (block, Val::Place(Place::local(t).deref()))
            }
            ExprKind::Field(base, _) => {
                let idx = self.tr.field_indices.get(&e).copied().unwrap_or(0) as u32;
                let (b, p) = self.as_place(block, *base, mutable);
                (b, Val::Place(p.field(idx, ty)))
            }
            ExprKind::Index(base, idx) => {
                if let Some(callee) = self.tr.overloaded.get(&e).copied() {
                    // `*Index::index(&base, idx)` / `*IndexMut::index_mut(&mut base, idx)`.
                    let (b, p) = self.as_place(block, *base, mutable);
                    let (b, i) = self.as_operand(b, *idx);
                    let (method, m) = if mutable {
                        let im = self
                            .tcx
                            .lang_item("index_mut")
                            .and_then(|t| self.tcx.assoc_item(t, hyprc_span::sym::index_mut, true));
                        (im.unwrap_or(callee.def), Mutability::Mut)
                    } else {
                        (callee.def, Mutability::Not)
                    };
                    let base_ty = callee.args.ty(0);
                    let r = self.temp(Ty::reference(base_ty, m), span);
                    self.assign(b, Place::local(r), Rvalue::Ref(m, p), span);
                    let out = self.temp(Ty::reference(ty, m), span);
                    let next = self.new_block();
                    let func =
                        Operand::constant(Ty::fn_def(method, callee.args), ConstValue::ZeroSized);
                    self.terminate(
                        b,
                        TerminatorKind::Call {
                            func,
                            args: vec![Operand::Move(Place::local(r)), i],
                            destination: Place::local(out),
                            target: Some(next),
                        },
                        span,
                    );
                    return (next, Val::Place(Place::local(out).deref()));
                }
                let (b, p) = self.as_place(block, *base, mutable);
                let (b, i) = self.as_local_operand(b, *idx);
                let b = self.bounds_check(b, &p, i, span);
                (b, Val::Place(p.project(PlaceElem::Index(i))))
            }
            ExprKind::Unary(hir::UnOp::Deref, x) => {
                if let Some(callee) = self.tr.overloaded.get(&e).copied() {
                    let (b, p) = self.as_place(block, *x, mutable);
                    let (b, p) =
                        self.overloaded_deref(b, p, callee.def, callee.args, mutable, ty, span);
                    return (b, Val::Place(p));
                }
                let xt = self.expr_ty_adjusted(*x);
                let (b, p) = if matches!(xt.kind(), TyKind::Adt(..)) {
                    // `*b` on a `Box`: a built-in deref of its pointer.
                    self.as_place(block, *x, mutable)
                } else {
                    let (b, op) = self.as_operand(block, *x);
                    match op {
                        Operand::Copy(p) | Operand::Move(p) => (b, p),
                        Operand::Constant(c) => {
                            let t = self.temp(c.ty, span);
                            self.assign(
                                b,
                                Place::local(t),
                                Rvalue::Use(Operand::Constant(c)),
                                span,
                            );
                            (b, Place::local(t))
                        }
                    }
                };
                (b, Val::Place(p.deref()))
            }
            ExprKind::Lit(l) => (block, Val::Op(self.lit_operand(l, ty))),
            ExprKind::Path(q) => {
                if let Some(op) = self.path_operand(e, q, ty) {
                    return (block, Val::Op(op));
                }
                let t = self.temp(ty, span);
                let b = self.expr_into_unadjusted(Place::local(t), block, e);
                (b, Val::Place(Place::local(t)))
            }
            _ => {
                let t = self.temp(ty, span);
                let b = self.expr_into_unadjusted(Place::local(t), block, e);
                (b, Val::Place(Place::local(t)))
            }
        }
    }

    /// `index < len`, or a panic.
    fn bounds_check(
        &mut self,
        block: BasicBlock,
        base: &Place,
        index: Local,
        span: Span,
    ) -> BasicBlock {
        let len = self.temp(Ty::USIZE, span);
        self.assign(block, Place::local(len), Rvalue::Len(base.clone()), span);
        let ok = self.temp(Ty::BOOL, span);
        self.assign(
            block,
            Place::local(ok),
            Rvalue::BinaryOp(
                BinOp::Lt,
                Operand::Copy(Place::local(index)),
                Operand::Copy(Place::local(len)),
            ),
            span,
        );
        let next = self.new_block();
        self.terminate(
            block,
            TerminatorKind::Assert {
                cond: Operand::Move(Place::local(ok)),
                expected: true,
                msg: AssertKind::BoundsCheck {
                    len: Operand::Copy(Place::local(len)),
                    index: Operand::Copy(Place::local(index)),
                },
                target: next,
            },
            span,
        );
        next
    }

    pub(crate) fn lit_operand(&self, l: &hir::Lit, ty: Ty) -> Operand {
        let ty = self.norm(ty);
        let kind = match l.kind {
            LitKind::Integer => {
                let v = hyprc_ty::consteval::parse_int_lit(l.symbol.as_str()).unwrap_or(0);
                if ty.is_float() {
                    float_bits(ty, v as f64)
                } else {
                    ConstValue::Scalar(v)
                }
            }
            LitKind::Float => {
                let v: f64 = l.symbol.as_str().replace('_', "").parse().unwrap_or(0.0);
                float_bits(ty, v)
            }
            LitKind::Bool => ConstValue::Scalar((l.symbol == hyprc_span::kw::True) as u128),
            LitKind::Char | LitKind::Byte => ConstValue::Scalar(
                hyprc_ty::consteval::parse_char_lit(l.symbol.as_str()).unwrap_or(0) as u128,
            ),
            LitKind::Str | LitKind::StrRaw(_) => {
                let s = if matches!(l.kind, LitKind::StrRaw(_)) {
                    l.symbol.as_str().to_string()
                } else {
                    unescape(l.symbol.as_str())
                };
                ConstValue::Bytes(Arc::from(s.into_bytes()))
            }
            LitKind::ByteStr | LitKind::ByteStrRaw(_) => {
                let bytes = if matches!(l.kind, LitKind::ByteStrRaw(_)) {
                    l.symbol.as_str().as_bytes().to_vec()
                } else {
                    unescape_bytes(l.symbol.as_str())
                };
                ConstValue::Bytes(Arc::from(bytes))
            }
            LitKind::CStr | LitKind::CStrRaw(_) => {
                let mut bytes = if matches!(l.kind, LitKind::CStrRaw(_)) {
                    l.symbol.as_str().as_bytes().to_vec()
                } else {
                    unescape_bytes(l.symbol.as_str())
                };
                bytes.push(0);
                ConstValue::Bytes(Arc::from(bytes))
            }
            LitKind::Err => ConstValue::Scalar(0),
        };
        Operand::constant(ty, kind)
    }

    /// Paths that are constants: function items, unit structs and variants, constants.
    fn path_operand(&mut self, e: ExprId, q: &hir::QPath, ty: Ty) -> Option<Operand> {
        let ty = self.norm(ty);
        match *ty.kind() {
            TyKind::FnDef(..) => return Some(Operand::constant(ty, ConstValue::ZeroSized)),
            _ => {}
        }
        let res = match q {
            hir::QPath::Resolved(_, p) => p.res,
            hir::QPath::TypeRelative(..) => match self.tr.type_dependent.get(&e) {
                Some(c) => Res::Def(self.tcx.hir.def_kind(c.def), c.def),
                None => return None,
            },
            hir::QPath::LangItem(name, _) => {
                let d = *self.tcx.lang_items().get(name)?;
                Res::Def(self.tcx.hir.def_kind(d), d)
            }
        };
        let args = self
            .tr
            .node_args
            .get(&e)
            .copied()
            .or_else(|| self.tr.type_dependent.get(&e).map(|c| c.args))
            .unwrap_or(Args::EMPTY);
        match res {
            Res::Def(DefKind::Const | DefKind::AssocConst, d) => {
                Some(Operand::constant(ty, ConstValue::Item(d, args)))
            }
            Res::ConstParam { index, owner } => {
                let name = self
                    .tcx
                    .all_params(owner)
                    .iter()
                    .find(|p| p.index == index)
                    .map_or(hyprc_span::kw::Empty, |p| p.name);
                Some(Operand::constant(
                    ty,
                    ConstValue::Unevaluated(Const::new(ty, ConstKind::Param(index, name))),
                ))
            }
            _ => None,
        }
    }

    // ---------------------------------------------------------------------------------------
    // Into a place

    pub(crate) fn expr_into_unadjusted(
        &mut self,
        dest: Place,
        block: BasicBlock,
        e: ExprId,
    ) -> BasicBlock {
        let span = self.span_of(e);
        let ty = self.expr_ty(e);
        let expr = &self.hir.expr(e).kind;
        match expr {
            ExprKind::Lit(_)
            | ExprKind::Field(..)
            | ExprKind::Index(..)
            | ExprKind::Unary(hir::UnOp::Deref, _) => {
                let (b, v) = self.as_val_unadjusted(block, e, false);
                let op = self.val_to_operand(v, ty);
                self.assign(b, dest, Rvalue::Use(op), span);
                b
            }
            ExprKind::Path(q) => {
                if let Some(op) = self.path_operand(e, q, ty) {
                    self.assign(block, dest, Rvalue::Use(op), span);
                    return block;
                }
                self.path_into(dest, block, e, q, ty, span)
            }
            ExprKind::Call(f, args) => self.call_into(dest, block, e, *f, args, span),
            ExprKind::MethodCall { receiver, args, .. } => {
                let Some(callee) = self.tr.type_dependent.get(&e).copied() else {
                    self.terminate(block, TerminatorKind::Unreachable, span);
                    return self.new_block();
                };
                let mut b = block;
                let mut ops = Vec::with_capacity(args.len() + 1);
                let (nb, r) = self.as_operand(b, *receiver);
                b = nb;
                ops.push(r);
                for &a in args.iter() {
                    let (nb, o) = self.as_operand(b, a);
                    b = nb;
                    ops.push(o);
                }
                self.emit_call(
                    b,
                    dest,
                    Operand::constant(Ty::fn_def(callee.def, callee.args), ConstValue::ZeroSized),
                    ops,
                    span,
                )
            }
            ExprKind::Binary(op, l, r) => self.binary_into(dest, block, e, *op, *l, *r, ty, span),
            ExprKind::Unary(op, x) => {
                if let Some(callee) = self.tr.overloaded.get(&e).copied() {
                    let (b, o) = self.as_operand(block, *x);
                    return self.emit_call(
                        b,
                        dest,
                        Operand::constant(
                            Ty::fn_def(callee.def, callee.args),
                            ConstValue::ZeroSized,
                        ),
                        vec![o],
                        span,
                    );
                }
                let (mut b, o) = self.as_operand(block, *x);
                let mop = match op {
                    hir::UnOp::Neg => UnOp::Neg,
                    _ => UnOp::Not,
                };
                if mop == UnOp::Neg && self.overflow_checks && ty.is_signed() {
                    // `-MIN` overflows.
                    let min = int_min(ty, self.tcx.pointer_width);
                    let ok = self.temp(Ty::BOOL, span);
                    self.assign(
                        b,
                        Place::local(ok),
                        Rvalue::BinaryOp(
                            BinOp::Ne,
                            o.clone(),
                            Operand::constant(ty, ConstValue::Scalar(min)),
                        ),
                        span,
                    );
                    let next = self.new_block();
                    self.terminate(
                        b,
                        TerminatorKind::Assert {
                            cond: Operand::Move(Place::local(ok)),
                            expected: true,
                            msg: AssertKind::OverflowNeg,
                            target: next,
                        },
                        span,
                    );
                    b = next;
                }
                self.assign(b, dest, Rvalue::UnaryOp(mop, o), span);
                b
            }
            ExprKind::Cast(x, _) => {
                let to = self.norm(ty);
                let from = self.expr_ty_adjusted(*x);
                let (b, o) = self.as_operand(block, *x);
                let kind = cast_kind(self, from, to);
                match kind {
                    Some(k) => self.assign(b, dest, Rvalue::Cast(k, o, to), span),
                    None => self.assign(b, dest, Rvalue::Use(o), span),
                }
                b
            }
            ExprKind::Type(x, _) | ExprKind::ConstBlock(x) => self.expr_into(dest, block, *x),
            ExprKind::AddrOf(kind, m, x) => {
                let (b, p) = self.as_place(block, *x, *m == Mutability::Mut);
                let rv = match kind {
                    BorrowKind::Raw => Rvalue::RawPtr(*m, p),
                    _ => Rvalue::Ref(*m, p),
                };
                self.assign(b, dest, rv, span);
                b
            }
            ExprKind::Tuple(es) => {
                let (b, ops) = self.operands(block, es);
                self.assign(b, dest, Rvalue::Aggregate(AggregateKind::Tuple, ops), span);
                b
            }
            ExprKind::Array(es) => {
                let elem = match *self.norm(ty).kind() {
                    TyKind::Array(t, _) => t,
                    _ => Ty::ERROR,
                };
                let (b, ops) = self.operands(block, es);
                self.assign(
                    b,
                    dest,
                    Rvalue::Aggregate(AggregateKind::Array(elem), ops),
                    span,
                );
                b
            }
            ExprKind::Repeat(x, _) => {
                let len = match *self.norm(ty).kind() {
                    TyKind::Array(_, n) => n,
                    _ => Const::from_usize(0),
                };
                let (b, o) = self.as_operand(block, *x);
                self.assign(b, dest, Rvalue::Repeat(o, len), span);
                b
            }
            ExprKind::Struct { fields, tail, .. } => {
                self.struct_into(dest, block, e, fields, tail, ty, span)
            }
            ExprKind::If { cond, then, els } => {
                let then_block = self.new_block();
                let else_block = self.new_block();
                self.test_cond(block, *cond, then_block, else_block);
                let join = self.new_block();
                let t_end = self.expr_into(dest.clone(), then_block, *then);
                self.goto(t_end, join, span);
                let e_end = match els {
                    Some(x) => self.expr_into(dest, else_block, *x),
                    None => else_block,
                };
                self.goto(e_end, join, span);
                join
            }
            ExprKind::Match {
                scrutinee, arms, ..
            } => self.match_into(dest, block, *scrutinee, arms, span),
            ExprKind::Loop { body, id, .. } => {
                let head = self.new_block();
                let exit = self.new_block();
                self.goto(block, head, span);
                self.loops.insert(
                    *id,
                    LoopScope {
                        break_block: exit,
                        continue_block: head,
                        dest: dest.clone(),
                    },
                );
                let tmp = self.temp(Ty::UNIT, span);
                let end = self.block_into(Place::local(tmp), head, body);
                self.goto(end, head, span);
                self.loops.remove(id);
                exit
            }
            ExprKind::Block(blk, label) => {
                let Some(id) = label else {
                    return self.block_into(dest, block, blk);
                };
                let exit = self.new_block();
                self.loops.insert(
                    *id,
                    LoopScope {
                        break_block: exit,
                        continue_block: exit,
                        dest: dest.clone(),
                    },
                );
                let end = self.block_into(dest, block, blk);
                self.goto(end, exit, span);
                self.loops.remove(id);
                exit
            }
            ExprKind::Let { pat, init } => {
                // A `let` as a value: whether it matched.
                let yes = self.new_block();
                let no = self.new_block();
                let join = self.new_block();
                let (b, place) = self.as_place(block, *init, false);
                self.test_and_bind(b, *pat, place, yes, no);
                self.assign(
                    yes,
                    dest.clone(),
                    Rvalue::Use(Operand::constant(Ty::BOOL, ConstValue::Scalar(1))),
                    span,
                );
                self.goto(yes, join, span);
                self.assign(
                    no,
                    dest,
                    Rvalue::Use(Operand::constant(Ty::BOOL, ConstValue::Scalar(0))),
                    span,
                );
                self.goto(no, join, span);
                join
            }
            ExprKind::Assign(l, r) => {
                let (b, o) = self.as_operand(block, *r);
                let (b, p) = self.as_place(b, *l, true);
                self.assign(b, p, Rvalue::Use(o), span);
                self.assign(b, dest, Rvalue::Use(Operand::unit()), span);
                b
            }
            ExprKind::AssignOp(op, l, r) => {
                if let Some(callee) = self.tr.overloaded.get(&e).copied() {
                    // `AddAssign::add_assign(&mut l, r)`
                    let (b, p) = self.as_place(block, *l, true);
                    let lt = self.expr_ty_adjusted(*l);
                    let rf = self.temp(Ty::reference(lt, Mutability::Mut), span);
                    self.assign(b, Place::local(rf), Rvalue::Ref(Mutability::Mut, p), span);
                    let (b, o) = self.as_operand(b, *r);
                    return self.emit_call(
                        b,
                        dest,
                        Operand::constant(
                            Ty::fn_def(callee.def, callee.args),
                            ConstValue::ZeroSized,
                        ),
                        vec![Operand::Move(Place::local(rf)), o],
                        span,
                    );
                }
                // Primitives: the right side first.
                let (b, o) = self.as_operand(block, *r);
                let (b, p) = self.as_place(b, *l, true);
                let lt = self.expr_ty_adjusted(*l);
                let b = self.arith_into(
                    p.clone(),
                    b,
                    BinOp::from_hir(*op),
                    Operand::Copy(p),
                    o,
                    lt,
                    span,
                );
                self.assign(b, dest, Rvalue::Use(Operand::unit()), span);
                b
            }
            ExprKind::Break { target, value } => {
                let Some(target) = target else {
                    self.terminate(block, TerminatorKind::Unreachable, span);
                    return self.new_block();
                };
                let Some(scope) = self.loops.get(target) else {
                    self.terminate(block, TerminatorKind::Unreachable, span);
                    return self.new_block();
                };
                let (dest_place, exit) = (scope.dest.clone(), scope.break_block);
                let b = match value {
                    Some(v) => self.expr_into(dest_place, block, *v),
                    None => {
                        self.assign(block, dest_place, Rvalue::Use(Operand::unit()), span);
                        block
                    }
                };
                self.goto(b, exit, span);
                self.new_block()
            }
            ExprKind::Continue { target } => {
                if let Some(scope) = target.and_then(|t| self.loops.get(&t)) {
                    let head = scope.continue_block;
                    self.goto(block, head, span);
                }
                self.new_block()
            }
            ExprKind::Return(v) => {
                let b = match v {
                    Some(v) => self.expr_into(Place::ret(), block, *v),
                    None => {
                        self.assign(block, Place::ret(), Rvalue::Use(Operand::unit()), span);
                        block
                    }
                };
                self.terminate(b, TerminatorKind::Return, span);
                self.new_block()
            }
            ExprKind::Become(x) => {
                let b = self.expr_into(Place::ret(), block, *x);
                self.terminate(b, TerminatorKind::Return, span);
                self.new_block()
            }
            ExprKind::Closure(id) => {
                let Some(result) = self.tr.closures[id.index()].clone() else {
                    self.terminate(block, TerminatorKind::Unreachable, span);
                    return self.new_block();
                };
                let mut ops = Vec::with_capacity(result.upvars.len());
                for up in &result.upvars {
                    let p = self.var_place(up.local);
                    ops.push(match up.kind {
                        hyprc_ty::typeck::CaptureKind::ByValue => {
                            self.operand_from_place(p, self.norm(up.ty))
                        }
                        hyprc_ty::typeck::CaptureKind::ByRef(m) => {
                            let t = self.temp(Ty::reference(self.norm(up.ty), m), span);
                            self.assign(block, Place::local(t), Rvalue::Ref(m, p), span);
                            Operand::Move(Place::local(t))
                        }
                    });
                }
                let (cref, args) = match *self.norm(result.ty).kind() {
                    TyKind::Closure(c, a) | TyKind::Coroutine(c, a) => (c, a),
                    _ => (
                        hyprc_ty::ClosureRef {
                            owner: self.hir.owner,
                            body: self.body_id.0,
                            index: id.0,
                        },
                        Args::EMPTY,
                    ),
                };
                self.assign(
                    block,
                    dest,
                    Rvalue::Aggregate(AggregateKind::Closure(cref, args), ops),
                    span,
                );
                block
            }
            ExprKind::Yield(_) | ExprKind::Await(_) => {
                self.tcx.emit(
                    hyprc_span::Diag::error(
                        "coroutines (`async`, `yield`) aren't supported by hyprc yet",
                    )
                    .span(span, ""),
                );
                block
            }
            ExprKind::FormatArgs(_) => {
                self.tcx.emit(
                    hyprc_span::Diag::error(
                        "`format_args!` isn't supported by hyprc's code generation yet",
                    )
                    .span(span, ""),
                );
                block
            }
            ExprKind::InlineAsm(_) => {
                self.tcx.emit(
                    hyprc_span::Diag::error("inline assembly isn't supported by hyprc yet")
                        .span(span, ""),
                );
                block
            }
            ExprKind::OffsetOf(..) => {
                let Some((container, steps)) = self.tr.offset_of.get(&e).cloned() else {
                    self.terminate(block, TerminatorKind::Unreachable, span);
                    return self.new_block();
                };
                let steps = steps
                    .into_iter()
                    .map(|(v, f, t)| (v, f, self.norm(t)))
                    .collect();
                self.assign(
                    block,
                    dest,
                    Rvalue::OffsetOf(self.norm(container), steps),
                    span,
                );
                block
            }
            ExprKind::Err => {
                self.terminate(block, TerminatorKind::Unreachable, span);
                self.new_block()
            }
        }
    }

    fn operands(&mut self, mut block: BasicBlock, es: &[ExprId]) -> (BasicBlock, Vec<Operand>) {
        let mut ops = Vec::with_capacity(es.len());
        for &x in es {
            let (b, o) = self.as_operand(block, x);
            block = b;
            ops.push(o);
        }
        (block, ops)
    }

    fn path_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        e: ExprId,
        q: &hir::QPath,
        ty: Ty,
        span: Span,
    ) -> BasicBlock {
        let res = match q {
            hir::QPath::Resolved(_, p) => p.res,
            hir::QPath::TypeRelative(..) => self
                .tr
                .type_dependent
                .get(&e)
                .map_or(Res::Err, |c| Res::Def(self.tcx.hir.def_kind(c.def), c.def)),
            hir::QPath::LangItem(name, _) => self
                .tcx
                .lang_items()
                .get(name)
                .map_or(Res::Err, |&d| Res::Def(self.tcx.hir.def_kind(d), d)),
        };
        let ty = self.norm(ty);
        match res {
            // Unit structs and variants.
            Res::Def(DefKind::Ctor(_, hyprc_hir::CtorKind::Const), _)
            | Res::Def(DefKind::Variant | DefKind::Struct, _)
            | Res::SelfCtor(_) => {
                if let TyKind::Adt(adt, args) = *ty.kind() {
                    let def = res.def_id().unwrap_or(adt);
                    let adt_def = self.tcx.adt_def(adt);
                    let v = adt_def.variant_index(def).unwrap_or(0) as u32;
                    self.assign(
                        block,
                        dest,
                        Rvalue::Aggregate(AggregateKind::Adt(adt, v, args, None), Vec::new()),
                        span,
                    );
                }
                block
            }
            _ => {
                let (b, v) = self.as_val_unadjusted(block, e, false);
                let op = self.val_to_operand(v, ty);
                self.assign(b, dest, Rvalue::Use(op), span);
                b
            }
        }
    }

    pub(crate) fn emit_call(
        &mut self,
        block: BasicBlock,
        dest: Place,
        func: Operand,
        args: Vec<Operand>,
        span: Span,
    ) -> BasicBlock {
        let next = self.new_block();
        self.terminate(
            block,
            TerminatorKind::Call {
                func,
                args,
                destination: dest,
                target: Some(next),
            },
            span,
        );
        next
    }

    fn call_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        e: ExprId,
        f: ExprId,
        args: &[ExprId],
        span: Span,
    ) -> BasicBlock {
        // Overloaded: `Fn::call(&f, (args…))`.
        if let Some(callee) = self.tr.overloaded.get(&e).copied() {
            let (b, fo) = self.as_operand(block, f);
            let (b, ops) = self.operands(b, args);
            let tuple_ty = callee.args.ty(1);
            let t = self.temp(tuple_ty, span);
            self.assign(
                b,
                Place::local(t),
                Rvalue::Aggregate(AggregateKind::Tuple, ops),
                span,
            );
            return self.emit_call(
                b,
                dest,
                Operand::constant(Ty::fn_def(callee.def, callee.args), ConstValue::ZeroSized),
                vec![fo, Operand::Move(Place::local(t))],
                span,
            );
        }
        let callee_ty = self.expr_ty_adjusted(f);
        // Constructors build the value directly.
        if let TyKind::FnDef(d, cargs) = *callee_ty.kind()
            && matches!(self.tcx.hir.def_kind(d), DefKind::Struct | DefKind::Variant)
        {
            let (b, ops) = self.operands(block, args);
            let (adt, v) = match self.tcx.hir.def_kind(d) {
                DefKind::Variant => {
                    let adt = self.tcx.hir.parent(d).unwrap();
                    (
                        adt,
                        self.tcx.adt_def(adt).variant_index(d).unwrap_or(0) as u32,
                    )
                }
                _ => (d, 0),
            };
            self.assign(
                b,
                dest,
                Rvalue::Aggregate(AggregateKind::Adt(adt, v, cargs, None), ops),
                span,
            );
            return b;
        }
        let (mut b, fo) = self.as_operand(block, f);
        let mut ops = Vec::with_capacity(args.len() + 1);
        // A closure called directly: its environment goes first.
        if let TyKind::Closure(c, _) = *callee_ty.kind() {
            let kind = self.tcx.typeck(hyprc_hir::BodyId(c.body)).closures[c.index as usize]
                .as_ref()
                .map(|r| r.kind);
            let env = match (kind, &fo) {
                (Some(hyprc_ty::collect::ClosureKind::FnOnce), _) => fo.clone(),
                (k, Operand::Copy(p) | Operand::Move(p)) => {
                    let m = if k == Some(hyprc_ty::collect::ClosureKind::FnMut) {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    };
                    let t = self.temp(Ty::reference(callee_ty, m), span);
                    self.assign(b, Place::local(t), Rvalue::Ref(m, p.clone()), span);
                    Operand::Move(Place::local(t))
                }
                (_, o) => o.clone(),
            };
            ops.push(env);
        }
        for &a in args {
            let (nb, o) = self.as_operand(b, a);
            b = nb;
            ops.push(o);
        }
        self.emit_call(b, dest, fo, ops, span)
    }

    #[allow(clippy::too_many_arguments)]
    fn binary_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        e: ExprId,
        op: BinOpKind,
        l: ExprId,
        r: ExprId,
        ty: Ty,
        span: Span,
    ) -> BasicBlock {
        match op {
            BinOpKind::And | BinOpKind::Or => {
                // Short-circuit: `a && b` is `if a { b } else { false }`.
                let rhs = self.new_block();
                let short = self.new_block();
                let join = self.new_block();
                let (b, lo) = self.as_operand(block, l);
                let (t, f) = if op == BinOpKind::And {
                    (rhs, short)
                } else {
                    (short, rhs)
                };
                self.terminate(
                    b,
                    TerminatorKind::SwitchInt {
                        discr: lo,
                        targets: vec![(0, f)],
                        otherwise: t,
                    },
                    span,
                );
                self.assign(
                    short,
                    dest.clone(),
                    Rvalue::Use(Operand::constant(
                        Ty::BOOL,
                        ConstValue::Scalar((op == BinOpKind::Or) as u128),
                    )),
                    span,
                );
                self.goto(short, join, span);
                let rb = self.expr_into(dest, rhs, r);
                self.goto(rb, join, span);
                return join;
            }
            _ => {}
        }
        if let Some(callee) = self.tr.overloaded.get(&e).copied() {
            let (b, lo) = self.as_operand(block, l);
            let (b, ro) = self.as_operand(b, r);
            let func =
                Operand::constant(Ty::fn_def(callee.def, callee.args), ConstValue::ZeroSized);
            if op.is_comparison() {
                // `PartialEq::eq(&a, &b)`; `!=` is `ne`.
                let (b, la) = self.ref_of(b, lo, callee.args.ty(0), span);
                let (b, ra) = self.ref_of(b, ro, callee.args.ty(1), span);
                return self.emit_call(b, dest, func, vec![la, ra], span);
            }
            return self.emit_call(b, dest, func, vec![lo, ro], span);
        }
        let (b, lo) = self.as_operand(block, l);
        let (b, ro) = self.as_operand(b, r);
        let lt = self.expr_ty_adjusted(l);
        let _ = ty;
        self.arith_into(dest, b, BinOp::from_hir(op), lo, ro, lt, span)
    }

    fn ref_of(
        &mut self,
        block: BasicBlock,
        o: Operand,
        ty: Ty,
        span: Span,
    ) -> (BasicBlock, Operand) {
        let p = match o {
            Operand::Copy(p) | Operand::Move(p) => p,
            Operand::Constant(c) => {
                let t = self.temp(ty, span);
                self.assign(
                    block,
                    Place::local(t),
                    Rvalue::Use(Operand::Constant(c)),
                    span,
                );
                Place::local(t)
            }
        };
        let r = self.temp(Ty::reference(ty, Mutability::Not), span);
        self.assign(
            block,
            Place::local(r),
            Rvalue::Ref(Mutability::Not, p),
            span,
        );
        (block, Operand::Move(Place::local(r)))
    }

    /// A primitive binary operation, with overflow and division checks as configured.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn arith_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        op: BinOp,
        l: Operand,
        r: Operand,
        lt: Ty,
        span: Span,
    ) -> BasicBlock {
        let mut b = block;
        let int = lt.is_integral();
        if int && matches!(op, BinOp::Div | BinOp::Rem) {
            // Division by zero always panics; `MIN / -1` overflows.
            let is_zero = self.temp(Ty::BOOL, span);
            let rt = lt;
            self.assign(
                b,
                Place::local(is_zero),
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    r.clone(),
                    Operand::constant(rt, ConstValue::Scalar(0)),
                ),
                span,
            );
            let next = self.new_block();
            let msg = if op == BinOp::Div {
                AssertKind::DivisionByZero
            } else {
                AssertKind::RemainderByZero
            };
            self.terminate(
                b,
                TerminatorKind::Assert {
                    cond: Operand::Move(Place::local(is_zero)),
                    expected: false,
                    msg,
                    target: next,
                },
                span,
            );
            b = next;
            if lt.is_signed() {
                let min = int_min(lt, self.tcx.pointer_width);
                let all_ones = mask_of(lt, self.tcx.pointer_width);
                let lhs_min = self.temp(Ty::BOOL, span);
                self.assign(
                    b,
                    Place::local(lhs_min),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        l.clone(),
                        Operand::constant(lt, ConstValue::Scalar(min)),
                    ),
                    span,
                );
                let rhs_neg1 = self.temp(Ty::BOOL, span);
                self.assign(
                    b,
                    Place::local(rhs_neg1),
                    Rvalue::BinaryOp(
                        BinOp::Eq,
                        r.clone(),
                        Operand::constant(lt, ConstValue::Scalar(all_ones)),
                    ),
                    span,
                );
                let both = self.temp(Ty::BOOL, span);
                self.assign(
                    b,
                    Place::local(both),
                    Rvalue::BinaryOp(
                        BinOp::BitAnd,
                        Operand::Move(Place::local(lhs_min)),
                        Operand::Move(Place::local(rhs_neg1)),
                    ),
                    span,
                );
                let next = self.new_block();
                self.terminate(
                    b,
                    TerminatorKind::Assert {
                        cond: Operand::Move(Place::local(both)),
                        expected: false,
                        msg: AssertKind::Overflow(op),
                        target: next,
                    },
                    span,
                );
                b = next;
            }
        }
        if int
            && self.overflow_checks
            && matches!(
                op,
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr
            )
        {
            let pair_ty = Ty::tuple(&[lt, Ty::BOOL]);
            let t = self.temp(pair_ty, span);
            self.assign(b, Place::local(t), Rvalue::CheckedBinaryOp(op, l, r), span);
            let next = self.new_block();
            self.terminate(
                b,
                TerminatorKind::Assert {
                    cond: Operand::Copy(Place::local(t).field(1, Ty::BOOL)),
                    expected: false,
                    msg: AssertKind::Overflow(op),
                    target: next,
                },
                span,
            );
            self.assign(
                next,
                dest,
                Rvalue::Use(Operand::Copy(Place::local(t).field(0, lt))),
                span,
            );
            return next;
        }
        self.assign(b, dest, Rvalue::BinaryOp(op, l, r), span);
        b
    }

    fn struct_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        e: ExprId,
        fields: &[hir::ExprField],
        tail: &hir::StructTail,
        ty: Ty,
        span: Span,
    ) -> BasicBlock {
        let ty = self.norm(ty);
        let TyKind::Adt(adt, args) = *ty.kind() else {
            return block;
        };
        let adt_def = self.tcx.adt_def(adt);
        let (_, vidx) = self.tr.variant_of_expr(e).unwrap_or((adt, 0));
        let indices = self.tr.struct_fields.get(&e).cloned().unwrap_or_default();
        let variant = &adt_def.variants[vidx];
        let mut b = block;
        let mut ops: Vec<Option<Operand>> = vec![None; variant.fields.len()];
        for (f, &i) in fields.iter().zip(&indices) {
            let (nb, o) = self.as_operand(b, f.expr);
            b = nb;
            if i < ops.len() {
                ops[i] = Some(o);
            }
        }
        if adt_def.is_union() {
            let (i, o) = ops
                .iter()
                .enumerate()
                .find_map(|(i, o)| o.clone().map(|o| (i, o)))
                .unwrap_or((0, Operand::unit()));
            self.assign(
                b,
                dest,
                Rvalue::Aggregate(AggregateKind::Adt(adt, 0, args, Some(i as u32)), vec![o]),
                span,
            );
            return b;
        }
        if let hir::StructTail::Base(base) = tail {
            let (nb, bp) = self.as_place(b, *base, false);
            b = nb;
            for (i, o) in ops.iter_mut().enumerate() {
                if o.is_none() {
                    let fty = crate::normalize_erasing(self.tcx, variant.fields[i].ty.subst(args));
                    let fty = self.norm(fty);
                    *o = Some(self.operand_from_place(bp.field(i as u32, fty), fty));
                }
            }
        }
        let ops: Vec<Operand> = ops
            .into_iter()
            .map(|o| o.unwrap_or_else(Operand::unit))
            .collect();
        self.assign(
            b,
            dest,
            Rvalue::Aggregate(AggregateKind::Adt(adt, vidx as u32, args, None), ops),
            span,
        );
        b
    }

    pub(crate) fn block_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        blk: &hir::Block,
    ) -> BasicBlock {
        let mut b = block;
        for s in &blk.stmts {
            b = self.stmt(b, s);
        }
        match blk.tail {
            Some(t) => self.expr_into(dest, b, t),
            None => {
                self.assign(b, dest, Rvalue::Use(Operand::unit()), blk.span);
                b
            }
        }
    }

    fn stmt(&mut self, block: BasicBlock, s: &hir::Stmt) -> BasicBlock {
        match &s.kind {
            hir::StmtKind::Let { pat, init, els, .. } => {
                let Some(init) = init else {
                    // `let x;`: declared now, assigned later.
                    self.declare_bindings(*pat);
                    return block;
                };
                if let Some(els) = els {
                    // `let pat = init else { … };`
                    let (b, place) = self.as_place(block, *init, false);
                    let yes = self.new_block();
                    let no = self.new_block();
                    self.test_and_bind(b, *pat, place, yes, no);
                    let tmp = self.temp(Ty::UNIT, s.span);
                    let end = self.block_into(Place::local(tmp), no, els);
                    self.terminate(end, TerminatorKind::Unreachable, s.span);
                    return yes;
                }
                // A plain binding: evaluate straight into the variable.
                if let hir::PatKind::Binding {
                    mode: hir::BindingMode::Value { .. },
                    local,
                    sub: None,
                } = &self.hir.pat(*pat).kind
                    && !self.tr.pat_adjustments.contains_key(pat)
                {
                    let p = self.var_place(*local);
                    return self.expr_into(p, block, *init);
                }
                let (b, place) = self.as_place(block, *init, false);
                self.bind_irrefutable(b, *pat, place)
            }
            hir::StmtKind::Expr(x) => {
                let ty = self.expr_ty(*x);
                let t = self.temp(ty, s.span);
                self.expr_into(Place::local(t), block, *x)
            }
        }
    }

    /// Branches on a condition: `if` conditions may contain `let` and `&&` chains.
    pub(crate) fn test_cond(
        &mut self,
        block: BasicBlock,
        cond: ExprId,
        yes: BasicBlock,
        no: BasicBlock,
    ) {
        let span = self.span_of(cond);
        match &self.hir.expr(cond).kind {
            ExprKind::Let { pat, init } => {
                let (b, place) = self.as_place(block, *init, false);
                self.test_and_bind(b, *pat, place, yes, no);
            }
            ExprKind::Binary(BinOpKind::And, l, r) if self.has_let(cond) => {
                let mid = self.new_block();
                self.test_cond(block, *l, mid, no);
                self.test_cond(mid, *r, yes, no);
            }
            _ => {
                let (b, o) = self.as_operand(block, cond);
                self.terminate(
                    b,
                    TerminatorKind::SwitchInt {
                        discr: o,
                        targets: vec![(0, no)],
                        otherwise: yes,
                    },
                    span,
                );
            }
        }
    }

    fn has_let(&self, e: ExprId) -> bool {
        match &self.hir.expr(e).kind {
            ExprKind::Let { .. } => true,
            ExprKind::Binary(BinOpKind::And, l, r) => self.has_let(*l) || self.has_let(*r),
            _ => false,
        }
    }
}

/// How an `as` cast converts.
pub(crate) fn cast_kind(b: &Builder<'_, '_>, from: Ty, to: Ty) -> Option<CastKind> {
    if from == to {
        return None;
    }
    let is_int = |t: Ty| {
        matches!(
            t.kind(),
            TyKind::Int(_) | TyKind::Uint(_) | TyKind::Bool | TyKind::Char
        )
    };
    let is_float = |t: Ty| matches!(t.kind(), TyKind::Float(_));
    let is_ptr = |t: Ty| {
        matches!(
            t.kind(),
            TyKind::RawPtr(..) | TyKind::Ref(..) | TyKind::FnPtr(_)
        )
    };
    Some(match (*from.kind(), *to.kind()) {
        _ if is_int(from) && is_int(to) => CastKind::IntToInt,
        _ if is_int(from) && is_float(to) => CastKind::IntToFloat,
        _ if is_float(from) && is_int(to) => CastKind::FloatToInt,
        _ if is_float(from) && is_float(to) => CastKind::FloatToFloat,
        (TyKind::FnDef(..), TyKind::FnPtr(_)) => CastKind::ReifyFnPointer,
        (TyKind::FnDef(..), _) => CastKind::ReifyFnPointer,
        (TyKind::Closure(..), TyKind::FnPtr(_)) => CastKind::ClosureFnPointer,
        _ if is_ptr(from) && is_ptr(to) => CastKind::PtrToPtr,
        _ if is_ptr(from) && is_int(to) => CastKind::PtrToAddr,
        _ if is_int(from) && is_ptr(to) => CastKind::AddrToPtr,
        (TyKind::Adt(..), _) if is_int(to) => {
            let _ = b;
            CastKind::IntToInt
        }
        _ => CastKind::Transmute,
    })
}

fn float_bits(ty: Ty, v: f64) -> ConstValue {
    match ty.kind() {
        TyKind::Float(hyprc_hir::FloatTy::F32) => ConstValue::Scalar((v as f32).to_bits() as u128),
        _ => ConstValue::Scalar(v.to_bits() as u128),
    }
}

pub(crate) fn mask_of(t: Ty, pw: u32) -> u128 {
    let bits = hyprc_ty::consteval::int_bits(t, pw);
    if bits >= 128 {
        u128::MAX
    } else {
        (1u128 << bits) - 1
    }
}

pub(crate) fn int_min(t: Ty, pw: u32) -> u128 {
    let bits = hyprc_ty::consteval::int_bits(t, pw);
    (1u128 << (bits - 1)) & mask_of(t, pw)
}

fn unescape(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut chars = s.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('n') => out.push('\n'),
            Some('r') => out.push('\r'),
            Some('t') => out.push('\t'),
            Some('\\') => out.push('\\'),
            Some('0') => out.push('\0'),
            Some('\'') => out.push('\''),
            Some('"') => out.push('"'),
            Some('x') => {
                let hex: String = [chars.next().unwrap_or('0'), chars.next().unwrap_or('0')]
                    .iter()
                    .collect();
                out.push(u8::from_str_radix(&hex, 16).unwrap_or(0) as char);
            }
            Some('u') => {
                chars.next();
                let mut hex = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    if c != '_' {
                        hex.push(c);
                    }
                }
                out.push(
                    char::from_u32(u32::from_str_radix(&hex, 16).unwrap_or(0))
                        .unwrap_or('\u{fffd}'),
                );
            }
            Some('\n') => {
                while chars.peek().is_some_and(|c| c.is_whitespace()) {
                    chars.next();
                }
            }
            Some(other) => out.push(other),
            None => {}
        }
    }
    out
}

fn unescape_bytes(s: &str) -> Vec<u8> {
    let mut out = Vec::with_capacity(s.len());
    let b = s.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] != b'\\' {
            out.push(b[i]);
            i += 1;
            continue;
        }
        i += 1;
        match b.get(i) {
            Some(b'n') => out.push(b'\n'),
            Some(b'r') => out.push(b'\r'),
            Some(b't') => out.push(b'\t'),
            Some(b'\\') => out.push(b'\\'),
            Some(b'0') => out.push(0),
            Some(b'\'') => out.push(b'\''),
            Some(b'"') => out.push(b'"'),
            Some(b'x') => {
                let hex = std::str::from_utf8(&b[i + 1..(i + 3).min(b.len())]).unwrap_or("0");
                out.push(u8::from_str_radix(hex, 16).unwrap_or(0));
                i += 2;
            }
            Some(b'\n') => {
                while i + 1 < b.len() && (b[i + 1] as char).is_ascii_whitespace() {
                    i += 1;
                }
            }
            Some(&c) => out.push(c),
            None => {}
        }
        i += 1;
    }
    out
}
