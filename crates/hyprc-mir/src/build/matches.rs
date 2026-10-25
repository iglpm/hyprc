//! Pattern matching to MIR.
//!
//! Arms are tried in order. A pattern with or-patterns inside is expanded into its
//! alternatives (each a choice at every `|`); an alternative is tested completely before
//! anything is bound, then bound, then its guard runs. A failing test or guard goes on to
//! the next alternative, then the next arm. Simple and correct; a decision tree that shares
//! tests between arms is a later optimization.

use super::Builder;
use crate::mir::*;
use hyprc_hir as hir;
use hyprc_hir::{BindingMode, Mutability, PatId, PatKind, RangeEnd};
use hyprc_span::{FxHashMap, Span};
use hyprc_ty::{Ty, TyKind};

type Choices = FxHashMap<PatId, usize>;

impl<'a, 'h> Builder<'a, 'h> {
    pub(crate) fn match_into(
        &mut self,
        dest: Place,
        block: BasicBlock,
        scrutinee: hir::ExprId,
        arms: &[hir::Arm],
        span: Span,
    ) -> BasicBlock {
        let (b, place) = self.as_place(block, scrutinee, false);
        let join = self.new_block();
        let mut next = b;
        for arm in arms {
            let body_block = self.new_block();
            for choices in self.alternatives(arm.pat) {
                let fail = self.new_block();
                let ok = self.test_pattern(next, arm.pat, place.clone(), fail, &choices);
                let ok = self.bind_pattern(ok, arm.pat, place.clone(), &choices);
                match arm.guard {
                    Some(g) => self.test_cond(ok, g, body_block, fail),
                    None => self.goto(ok, body_block, arm.span),
                }
                next = fail;
            }
            let end = self.expr_into(dest.clone(), body_block, arm.body);
            self.goto(end, join, arm.span);
        }
        self.terminate(next, TerminatorKind::Unreachable, span);
        join
    }

    /// Tests and binds `pat`: on success to `yes` (bindings done), else to `no`.
    pub(crate) fn test_and_bind(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: Place,
        yes: BasicBlock,
        no: BasicBlock,
    ) {
        let mut next = block;
        let span = self.hir.pat(pat).span;
        for choices in self.alternatives(pat) {
            let fail = self.new_block();
            let ok = self.test_pattern(next, pat, place.clone(), fail, &choices);
            let ok = self.bind_pattern(ok, pat, place.clone(), &choices);
            self.goto(ok, yes, span);
            next = fail;
        }
        self.goto(next, no, span);
    }

    /// Binds an irrefutable pattern (`let`, parameters).
    pub(crate) fn bind_irrefutable(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: Place,
    ) -> BasicBlock {
        let yes = self.new_block();
        let no = self.new_block();
        self.test_and_bind(block, pat, place, yes, no);
        self.terminate(no, TerminatorKind::Unreachable, self.hir.pat(pat).span);
        yes
    }

    /// `let x;`: the variables exist, unassigned.
    pub(crate) fn declare_bindings(&mut self, pat: PatId) {
        let mut locals = Vec::new();
        self.collect_locals(pat, &mut locals);
        for l in locals {
            let _ = self.var_place(l);
        }
    }

    fn collect_locals(&self, pat: PatId, out: &mut Vec<hir::LocalId>) {
        match &self.hir.pat(pat).kind {
            PatKind::Binding { local, sub, .. } => {
                out.push(*local);
                if let Some(s) = sub {
                    self.collect_locals(*s, out);
                }
            }
            PatKind::Struct { fields, .. } => {
                fields.iter().for_each(|f| self.collect_locals(f.pat, out))
            }
            PatKind::TupleStruct { pats, .. } | PatKind::Tuple { pats, .. } | PatKind::Or(pats) => {
                pats.iter().for_each(|&p| self.collect_locals(p, out))
            }
            PatKind::Box(s) | PatKind::Deref(s) | PatKind::Ref(s, _) => {
                self.collect_locals(*s, out)
            }
            PatKind::Slice {
                before,
                rest,
                after,
                ..
            } => {
                before
                    .iter()
                    .chain(after)
                    .for_each(|&p| self.collect_locals(p, out));
                if let Some(r) = rest {
                    self.collect_locals(*r, out);
                }
            }
            _ => {}
        }
    }

    /// Every combination of choices at the or-patterns in `pat`.
    fn alternatives(&self, pat: PatId) -> Vec<Choices> {
        let mut out = vec![Choices::default()];
        self.expand(pat, &mut out);
        out
    }

    fn expand(&self, pat: PatId, acc: &mut Vec<Choices>) {
        let children: Vec<PatId> = match &self.hir.pat(pat).kind {
            PatKind::Or(alts) => {
                let mut result = Vec::new();
                for (i, &a) in alts.iter().enumerate() {
                    let mut branch: Vec<Choices> = acc
                        .iter()
                        .map(|c| {
                            let mut c = c.clone();
                            c.insert(pat, i);
                            c
                        })
                        .collect();
                    self.expand(a, &mut branch);
                    result.extend(branch);
                    if result.len() > 4096 {
                        break;
                    }
                }
                *acc = result;
                return;
            }
            PatKind::Binding { sub: Some(s), .. } => vec![*s],
            PatKind::Struct { fields, .. } => fields.iter().map(|f| f.pat).collect(),
            PatKind::TupleStruct { pats, .. } | PatKind::Tuple { pats, .. } => pats.clone(),
            PatKind::Box(s) | PatKind::Deref(s) | PatKind::Ref(s, _) => vec![*s],
            PatKind::Slice {
                before,
                rest,
                after,
                ..
            } => before
                .iter()
                .chain(rest.iter())
                .chain(after)
                .copied()
                .collect(),
            _ => Vec::new(),
        };
        for c in children {
            self.expand(c, acc);
        }
    }

    /// The place a pattern matches after its implicit dereferences (match ergonomics).
    fn adjusted_place(&self, pat: PatId, place: Place) -> Place {
        let mut p = place;
        if let Some(adjs) = self.tr.pat_adjustments.get(&pat) {
            for _ in adjs {
                p = p.deref();
            }
        }
        p
    }

    fn pat_ty(&self, pat: PatId) -> Ty {
        self.norm(self.tr.pat_ty(pat))
    }

    /// The type of field `i` of the (adjusted) type a struct-like pattern matches.
    fn field_ty(&self, parent: Ty, variant: usize, i: usize) -> Ty {
        match *parent.kind() {
            TyKind::Adt(d, args) => {
                let adt = self.tcx.adt_def(d);
                adt.variants
                    .get(variant)
                    .and_then(|v| v.fields.get(i))
                    .map_or(Ty::ERROR, |f| {
                        self.norm(crate::normalize_erasing(self.tcx, f.ty.subst(args)))
                    })
            }
            TyKind::Tuple(ts) => ts.as_slice().get(i).copied().unwrap_or(Ty::ERROR),
            _ => Ty::ERROR,
        }
    }

    /// Indices of the fields a tuple-like pattern's subpatterns match, around a `..`.
    fn seq_indices(n_pats: usize, rest: Option<usize>, n_fields: usize) -> Vec<usize> {
        match rest {
            None => (0..n_pats).collect(),
            Some(pos) => (0..n_pats)
                .map(|i| if i < pos { i } else { n_fields - (n_pats - i) })
                .collect(),
        }
    }

    fn n_fields(&self, ty: Ty, variant: usize) -> usize {
        match *ty.kind() {
            TyKind::Adt(d, _) => self
                .tcx
                .adt_def(d)
                .variants
                .get(variant)
                .map_or(0, |v| v.fields.len()),
            TyKind::Tuple(ts) => ts.as_slice().len(),
            _ => 0,
        }
    }

    /// Emits the tests of `pat` against `place`; returns the block where they all passed.
    fn test_pattern(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: Place,
        fail: BasicBlock,
        choices: &Choices,
    ) -> BasicBlock {
        let place = self.adjusted_place(pat, place);
        let ty = self.pat_ty(pat);
        let span = self.hir.pat(pat).span;
        match &self.hir.pat(pat).kind.clone() {
            PatKind::Wild | PatKind::Never | PatKind::Err => block,
            PatKind::Binding { sub, .. } => match sub {
                Some(s) => self.test_pattern(block, *s, place, fail, choices),
                None => block,
            },
            PatKind::Or(alts) => {
                let i = choices.get(&pat).copied().unwrap_or(0);
                self.test_pattern(block, alts[i], place, fail, choices)
            }
            PatKind::Tuple { pats, rest } => {
                let idx = Self::seq_indices(pats.len(), *rest, self.n_fields(ty, 0));
                let mut b = block;
                for (&sp, &fi) in pats.iter().zip(&idx) {
                    let fty = self.field_ty(ty, 0, fi);
                    b = self.test_pattern(b, sp, place.field(fi as u32, fty), fail, choices);
                }
                b
            }
            PatKind::TupleStruct { pats, rest, .. } => {
                let (b, vplace, v) = self.test_variant(block, pat, place, ty, fail, span);
                let idx = Self::seq_indices(pats.len(), *rest, self.n_fields(ty, v));
                let mut b = b;
                for (&sp, &fi) in pats.iter().zip(&idx) {
                    let fty = self.field_ty(ty, v, fi);
                    b = self.test_pattern(b, sp, vplace.field(fi as u32, fty), fail, choices);
                }
                b
            }
            PatKind::Struct { fields, .. } => {
                let (b, vplace, v) = self.test_variant(block, pat, place, ty, fail, span);
                let indices = self.tr.pat_fields.get(&pat).cloned().unwrap_or_default();
                let mut b = b;
                for (f, &fi) in fields.iter().zip(&indices) {
                    if fi == usize::MAX {
                        continue;
                    }
                    let fty = self.field_ty(ty, v, fi);
                    b = self.test_pattern(b, f.pat, vplace.field(fi as u32, fty), fail, choices);
                }
                b
            }
            PatKind::Path(_) => {
                if let Some(&(d, args)) = self.tr.pat_consts.get(&pat) {
                    let c = Operand::constant(ty, ConstValue::Item(d, args));
                    return self.test_eq(block, place, ty, c, fail, span);
                }
                let (b, _, _) = self.test_variant(block, pat, place, ty, fail, span);
                b
            }
            PatKind::Lit(e) => {
                let (b, o) = self.as_operand(block, *e);
                if matches!(ty.kind(), TyKind::Ref(inner, _) if matches!(inner.kind(), TyKind::Str | TyKind::Slice(_)))
                {
                    self.tcx.emit(hyprc_span::Diag::error("matching on string and slice literals needs `core`, which hyprc can't compile yet").span(span, ""));
                    return b;
                }
                self.test_eq(b, place, ty, o, fail, span)
            }
            PatKind::Range { lo, hi, end } => {
                let mut b = block;
                if let Some(lo) = lo {
                    let (nb, lo_op) = self.as_operand(b, *lo);
                    b = nb;
                    b = self.test_cmp(
                        b,
                        BinOp::Ge,
                        Operand::Copy(place.clone()),
                        lo_op,
                        fail,
                        span,
                    );
                }
                if let Some(hi) = hi {
                    let (nb, hi_op) = self.as_operand(b, *hi);
                    b = nb;
                    let op = if matches!(end, RangeEnd::Included(_)) {
                        BinOp::Le
                    } else {
                        BinOp::Lt
                    };
                    b = self.test_cmp(b, op, Operand::Copy(place.clone()), hi_op, fail, span);
                }
                b
            }
            PatKind::Box(s) | PatKind::Ref(s, _) => {
                self.test_pattern(block, *s, place.deref(), fail, choices)
            }
            PatKind::Deref(s) => self.test_pattern(block, *s, place.deref(), fail, choices),
            PatKind::Slice {
                before,
                rest,
                after,
                has_rest,
            } => {
                let (elem, array_len) = match *ty.kind() {
                    TyKind::Array(e, n) => (e, n.try_to_usize()),
                    TyKind::Slice(e) => (e, None),
                    _ => (Ty::ERROR, None),
                };
                let min = (before.len() + after.len()) as u64;
                let mut b = block;
                if array_len.is_none() {
                    // Slices: the length must fit.
                    let len = self.temp(Ty::USIZE, span);
                    self.assign(b, Place::local(len), Rvalue::Len(place.clone()), span);
                    let op = if *has_rest { BinOp::Ge } else { BinOp::Eq };
                    b = self.test_cmp(
                        b,
                        op,
                        Operand::Copy(Place::local(len)),
                        Operand::constant(Ty::USIZE, ConstValue::Scalar(min as u128)),
                        fail,
                        span,
                    );
                }
                for (i, &sp) in before.iter().enumerate() {
                    let p = place.project(PlaceElem::ConstantIndex {
                        offset: i as u64,
                        min_length: min,
                        from_end: false,
                    });
                    b = self.test_pattern(b, sp, p, fail, choices);
                }
                for (i, &sp) in after.iter().enumerate() {
                    let from_end = (after.len() - i) as u64;
                    let p = match array_len {
                        Some(n) => place.project(PlaceElem::ConstantIndex {
                            offset: n - from_end,
                            min_length: min,
                            from_end: false,
                        }),
                        None => place.project(PlaceElem::ConstantIndex {
                            offset: from_end,
                            min_length: min,
                            from_end: true,
                        }),
                    };
                    b = self.test_pattern(b, sp, p, fail, choices);
                }
                let _ = (elem, rest);
                b
            }
        }
    }

    /// For enums: tests the discriminant. Returns the block, the place viewed as the
    /// variant, and the variant index.
    fn test_variant(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: Place,
        ty: Ty,
        fail: BasicBlock,
        span: Span,
    ) -> (BasicBlock, Place, usize) {
        let (_, v) = self
            .tr
            .variant_of_pat(pat)
            .unwrap_or((hyprc_hir::DefId(0), 0));
        let TyKind::Adt(d, _) = *ty.kind() else {
            return (block, place, v);
        };
        let adt = self.tcx.adt_def(d);
        if !adt.is_enum() {
            return (block, place, v);
        }
        let discrs = crate::discriminants(self.tcx, &adt);
        let dty = crate::discriminant_ty(&adt);
        let dval = discrs.get(v).copied().unwrap_or(0);
        let t = self.temp(dty, span);
        self.assign(
            block,
            Place::local(t),
            Rvalue::Discriminant(place.clone()),
            span,
        );
        let ok = self.new_block();
        let bits = (dval as u128) & crate::build::expr::mask_of(dty, self.tcx.pointer_width);
        self.terminate(
            block,
            TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::local(t)),
                targets: vec![(bits, ok)],
                otherwise: fail,
            },
            span,
        );
        (ok, place.project(PlaceElem::Downcast(v as u32)), v)
    }

    fn test_eq(
        &mut self,
        block: BasicBlock,
        place: Place,
        ty: Ty,
        value: Operand,
        fail: BasicBlock,
        span: Span,
    ) -> BasicBlock {
        let _ = ty;
        self.test_cmp(block, BinOp::Eq, Operand::Copy(place), value, fail, span)
    }

    fn test_cmp(
        &mut self,
        block: BasicBlock,
        op: BinOp,
        l: Operand,
        r: Operand,
        fail: BasicBlock,
        span: Span,
    ) -> BasicBlock {
        let t = self.temp(Ty::BOOL, span);
        self.assign(block, Place::local(t), Rvalue::BinaryOp(op, l, r), span);
        let ok = self.new_block();
        self.terminate(
            block,
            TerminatorKind::SwitchInt {
                discr: Operand::Move(Place::local(t)),
                targets: vec![(0, fail)],
                otherwise: ok,
            },
            span,
        );
        ok
    }

    /// Binds the variables of a pattern known to match.
    fn bind_pattern(
        &mut self,
        block: BasicBlock,
        pat: PatId,
        place: Place,
        choices: &Choices,
    ) -> BasicBlock {
        let place = self.adjusted_place(pat, place);
        let ty = self.pat_ty(pat);
        let span = self.hir.pat(pat).span;
        match &self.hir.pat(pat).kind.clone() {
            PatKind::Binding { local, sub, .. } => {
                let mode = self
                    .tr
                    .binding_modes
                    .get(&pat)
                    .copied()
                    .unwrap_or(BindingMode::Value { mutable: false });
                let dest = self.var_place(*local);
                match mode {
                    BindingMode::Value { .. } => {
                        let op = self.operand_from_place(place.clone(), ty);
                        self.assign(block, dest, Rvalue::Use(op), span);
                    }
                    BindingMode::Ref { mutable } => {
                        let m = if mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Not
                        };
                        self.assign(block, dest, Rvalue::Ref(m, place.clone()), span);
                    }
                }
                match sub {
                    Some(s) => self.bind_pattern(block, *s, place, choices),
                    None => block,
                }
            }
            PatKind::Or(alts) => {
                let i = choices.get(&pat).copied().unwrap_or(0);
                self.bind_pattern(block, alts[i], place, choices)
            }
            PatKind::Tuple { pats, rest } => {
                let idx = Self::seq_indices(pats.len(), *rest, self.n_fields(ty, 0));
                let mut b = block;
                for (&sp, &fi) in pats.iter().zip(&idx) {
                    let fty = self.field_ty(ty, 0, fi);
                    b = self.bind_pattern(b, sp, place.field(fi as u32, fty), choices);
                }
                b
            }
            PatKind::TupleStruct { pats, rest, .. } => {
                let (vplace, v) = self.variant_place(pat, place, ty);
                let idx = Self::seq_indices(pats.len(), *rest, self.n_fields(ty, v));
                let mut b = block;
                for (&sp, &fi) in pats.iter().zip(&idx) {
                    let fty = self.field_ty(ty, v, fi);
                    b = self.bind_pattern(b, sp, vplace.field(fi as u32, fty), choices);
                }
                b
            }
            PatKind::Struct { fields, .. } => {
                let (vplace, v) = self.variant_place(pat, place, ty);
                let indices = self.tr.pat_fields.get(&pat).cloned().unwrap_or_default();
                let mut b = block;
                for (f, &fi) in fields.iter().zip(&indices) {
                    if fi == usize::MAX {
                        continue;
                    }
                    let fty = self.field_ty(ty, v, fi);
                    b = self.bind_pattern(b, f.pat, vplace.field(fi as u32, fty), choices);
                }
                b
            }
            PatKind::Box(s) | PatKind::Ref(s, _) | PatKind::Deref(s) => {
                self.bind_pattern(block, *s, place.deref(), choices)
            }
            PatKind::Slice {
                before,
                rest,
                after,
                ..
            } => {
                let array_len = match *ty.kind() {
                    TyKind::Array(_, n) => n.try_to_usize(),
                    _ => None,
                };
                let min = (before.len() + after.len()) as u64;
                let mut b = block;
                for (i, &sp) in before.iter().enumerate() {
                    let p = place.project(PlaceElem::ConstantIndex {
                        offset: i as u64,
                        min_length: min,
                        from_end: false,
                    });
                    b = self.bind_pattern(b, sp, p, choices);
                }
                if let Some(r) = rest {
                    let p = place.project(PlaceElem::Subslice {
                        from: before.len() as u64,
                        to: after.len() as u64,
                        from_end: array_len.is_none(),
                    });
                    b = self.bind_pattern(b, *r, p, choices);
                }
                for (i, &sp) in after.iter().enumerate() {
                    let from_end = (after.len() - i) as u64;
                    let p = match array_len {
                        Some(n) => place.project(PlaceElem::ConstantIndex {
                            offset: n - from_end,
                            min_length: min,
                            from_end: false,
                        }),
                        None => place.project(PlaceElem::ConstantIndex {
                            offset: from_end,
                            min_length: min,
                            from_end: true,
                        }),
                    };
                    b = self.bind_pattern(b, sp, p, choices);
                }
                b
            }
            _ => block,
        }
    }

    fn variant_place(&self, pat: PatId, place: Place, ty: Ty) -> (Place, usize) {
        let (_, v) = self
            .tr
            .variant_of_pat(pat)
            .unwrap_or((hyprc_hir::DefId(0), 0));
        if let TyKind::Adt(d, _) = *ty.kind()
            && self.tcx.adt_def(d).is_enum()
        {
            return (place.project(PlaceElem::Downcast(v as u32)), v);
        }
        (place, v)
    }
}
