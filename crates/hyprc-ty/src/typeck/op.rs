//! Operators and casts.

use super::{Callee, Expectation, FnCtxt};
use crate::traits::Eval;
use crate::ty::*;
use hyprc_hir::{BinOpKind, ExprId, Mutability, UnOp};
use hyprc_span::{Diag, Span, Symbol};

fn op_lang(op: BinOpKind) -> (&'static str, &'static str) {
    use BinOpKind::*;
    match op {
        Add => ("add", "add"),
        Sub => ("sub", "sub"),
        Mul => ("mul", "mul"),
        Div => ("div", "div"),
        Rem => ("rem", "rem"),
        BitAnd => ("bitand", "bitand"),
        BitOr => ("bitor", "bitor"),
        BitXor => ("bitxor", "bitxor"),
        Shl => ("shl", "shl"),
        Shr => ("shr", "shr"),
        Eq => ("eq", "eq"),
        Ne => ("eq", "ne"),
        Lt => ("partial_ord", "lt"),
        Le => ("partial_ord", "le"),
        Gt => ("partial_ord", "gt"),
        Ge => ("partial_ord", "ge"),
        And | Or => ("", ""),
    }
}

fn assign_op_lang(op: BinOpKind) -> (&'static str, &'static str) {
    use BinOpKind::*;
    match op {
        Add => ("add_assign", "add_assign"),
        Sub => ("sub_assign", "sub_assign"),
        Mul => ("mul_assign", "mul_assign"),
        Div => ("div_assign", "div_assign"),
        Rem => ("rem_assign", "rem_assign"),
        BitAnd => ("bitand_assign", "bitand_assign"),
        BitOr => ("bitor_assign", "bitor_assign"),
        BitXor => ("bitxor_assign", "bitxor_assign"),
        Shl => ("shl_assign", "shl_assign"),
        Shr => ("shr_assign", "shr_assign"),
        _ => ("", ""),
    }
}

/// Can the built-in operator apply to these (shallowly resolved) types?
fn builtin_binop(op: BinOpKind, l: Ty, r: Ty) -> bool {
    let int = |t: Ty| t.is_integral();
    let num = |t: Ty| t.is_numeric();
    let same_kind = |a: Ty, b: Ty| (int(a) && int(b)) || (a.is_float() && b.is_float()) || (a == b);
    use BinOpKind::*;
    match op {
        Add | Sub | Mul | Div | Rem => num(l) && num(r) && same_kind(l, r),
        BitAnd | BitOr | BitXor => (int(l) && int(r)) || (l == Ty::BOOL && r == Ty::BOOL),
        Shl | Shr => int(l) && int(r),
        Eq | Ne | Lt | Le | Gt | Ge => {
            (num(l) && num(r) && same_kind(l, r))
                || (l == r && (l.is_scalar() || matches!(l.kind(), TyKind::RawPtr(..))))
                || (matches!(l.kind(), TyKind::RawPtr(..))
                    && matches!(r.kind(), TyKind::RawPtr(..)))
        }
        And | Or => l == Ty::BOOL && r == Ty::BOOL,
    }
}

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn check_binop(
        &self,
        e: ExprId,
        op: BinOpKind,
        l: ExprId,
        r: ExprId,
        expected: Expectation,
    ) -> Ty {
        let span = self.span(e);
        if matches!(op, BinOpKind::And | BinOpKind::Or) {
            self.check_expr_has_type(l, Ty::BOOL);
            let d = self.diverges.get();
            self.check_expr_has_type(r, Ty::BOOL);
            // The right side may not run: it doesn't make the expression diverge.
            self.diverges.set(d);
            return Ty::BOOL;
        }
        let lt = self.check_expr_with(l, Expectation::None);
        let lt_s = self.structurally_resolve(lt);
        let rhs_hint = if lt_s.is_numeric() && !matches!(op, BinOpKind::Shl | BinOpKind::Shr) {
            Expectation::HasType(lt_s)
        } else {
            Expectation::None
        };
        let rt = self.check_expr_with(r, rhs_hint);
        let rt_s = self.structurally_resolve(rt);
        let _ = expected;
        if lt_s.is_error() || rt_s.is_error() {
            return Ty::ERROR;
        }
        if builtin_binop(op, lt_s, rt_s) {
            if !matches!(op, BinOpKind::Shl | BinOpKind::Shr) {
                if let (TyKind::RawPtr(a, m1), TyKind::RawPtr(b, m2)) = (lt_s.kind(), rt_s.kind()) {
                    self.demand_eq(self.span(r), *a, *b);
                    if m1 != m2 {
                        let target = Ty::ptr(*a, Mutability::Not);
                        if *m1 == Mutability::Mut {
                            let _ = self.try_coerce(l, lt_s, target);
                        }
                        if *m2 == Mutability::Mut {
                            let _ = self.try_coerce(r, rt_s, target);
                        }
                    }
                } else {
                    self.demand_eq(self.span(r), lt_s, rt_s);
                }
            }
            return if op.is_comparison() { Ty::BOOL } else { lt_s };
        }
        // Integer variables against a concrete type through a trait (`1 + x` where `x: u8`).
        if (lt_s.is_ty_var() || rt_s.is_ty_var()) && !op.is_comparison() {
            // Wait for more information: assume built-in if one side is numeric.
            if lt_s.is_numeric() || rt_s.is_numeric() {
                let _ = self.infcx.unify(lt_s, rt_s);
                return lt_s;
            }
        }
        self.check_overloaded_binop(e, op, l, r, lt, rt, span)
    }

    fn check_overloaded_binop(
        &self,
        e: ExprId,
        op: BinOpKind,
        l: ExprId,
        r: ExprId,
        mut lt: Ty,
        mut rt: Ty,
        span: Span,
    ) -> Ty {
        let (lang, method) = op_lang(op);
        let Some(trait_) = self.tcx.lang_item(lang) else {
            self.report_binop(op, lt, rt, span);
            return Ty::ERROR;
        };
        let mut args = Args::from_tys(&[lt, rt]);
        let mut tr = TraitRef::new(trait_, args);
        if self.evaluate(Predicate::Trait(tr)) == Eval::Fails {
            let coerced = if self
                .infcx
                .commit_if_ok(|| self.try_coerce(r, rt, lt))
                .is_ok()
            {
                rt = lt;
                true
            } else if self
                .infcx
                .commit_if_ok(|| self.try_coerce(l, lt, rt))
                .is_ok()
            {
                lt = rt;
                true
            } else {
                false
            };
            if coerced {
                args = Args::from_tys(&[lt, rt]);
                tr = TraitRef::new(trait_, args);
            }
        }
        if self.evaluate(Predicate::Trait(tr)) == Eval::Fails {
            self.report_binop(op, lt, rt, span);
            return Ty::ERROR;
        }
        self.register(Predicate::Trait(tr), span);
        if let Some(m) = self.tcx.assoc_item(trait_, Symbol::intern(method), true) {
            self.r
                .borrow_mut()
                .overloaded
                .insert(e, Callee { def: m, args });
        }
        if op.is_comparison() {
            return Ty::BOOL;
        }
        let Some(output) = self.tcx.assoc_item(trait_, hyprc_span::sym::Output, false) else {
            return Ty::ERROR;
        };
        self.normalize(Ty::new(TyKind::Alias(
            AliasKind::Projection,
            AliasTy {
                def: output,
                args,
                index: 0,
            },
        )))
    }

    fn report_binop(&self, op: BinOpKind, lt: Ty, rt: Ty, span: Span) {
        let (l, r) = (self.resolve(lt), self.resolve(rt));
        if l.has_errors() || r.has_errors() {
            return;
        }
        let msg = if op.is_comparison() {
            format!(
                "binary operation `{}` cannot be applied to type `{l}`",
                op.as_str()
            )
        } else {
            format!(
                "cannot apply binary operator `{}` to types `{l}` and `{r}`",
                op.as_str()
            )
        };
        self.emit(Diag::error(msg).code("E0369").span(span, ""));
    }

    pub(crate) fn check_assign_op(&self, e: ExprId, op: BinOpKind, l: ExprId, r: ExprId) -> Ty {
        let span = self.span(e);
        let lt = self.check_expr(l);
        let lt_s = self.structurally_resolve(lt);
        let hint = if lt_s.is_numeric() && !matches!(op, BinOpKind::Shl | BinOpKind::Shr) {
            Expectation::HasType(lt_s)
        } else {
            Expectation::None
        };
        let rt = self.check_expr_with(r, hint);
        let rt_s = self.structurally_resolve(rt);
        if lt_s.is_error() || rt_s.is_error() {
            return Ty::UNIT;
        }
        if builtin_binop(op, lt_s, rt_s) {
            if !matches!(op, BinOpKind::Shl | BinOpKind::Shr) {
                self.demand_eq(self.span(r), lt_s, rt_s);
            }
            return Ty::UNIT;
        }
        let (lang, method) = assign_op_lang(op);
        let Some(trait_) = self.tcx.lang_item(lang) else {
            self.report_binop(op, lt, rt, span);
            return Ty::UNIT;
        };
        let args = Args::from_tys(&[lt, rt]);
        let tr = TraitRef::new(trait_, args);
        if self.evaluate(Predicate::Trait(tr)) == Eval::Fails {
            self.emit(
                Diag::error(format!(
                    "binary assignment operation `{}=` cannot be applied to type `{}`",
                    op.as_str(),
                    self.resolve(lt)
                ))
                .code("E0368")
                .span(span, ""),
            );
            return Ty::UNIT;
        }
        self.register(Predicate::Trait(tr), span);
        if let Some(m) = self.tcx.assoc_item(trait_, Symbol::intern(method), true) {
            self.r
                .borrow_mut()
                .overloaded
                .insert(e, Callee { def: m, args });
        }
        Ty::UNIT
    }

    pub(crate) fn check_unop(&self, e: ExprId, op: UnOp, x: ExprId, expected: Expectation) -> Ty {
        let span = self.span(e);
        match op {
            UnOp::Deref => {
                let t = self.check_expr(x);
                let t = self.structurally_resolve(t);
                let inner = match *t.kind() {
                    TyKind::Ref(inner, _) => inner,
                    TyKind::RawPtr(inner, _) => {
                        self.require_unsafe(span, "dereference of raw pointer");
                        inner
                    }
                    TyKind::Adt(d, args) if self.tcx.adt_def(d).is_box => args.ty(0),
                    TyKind::Error => Ty::ERROR,
                    _ => {
                        // Overloaded: `*Deref::deref(&x)`.
                        let steps = self.autoderef_steps(t, span);
                        if let Some((target, Some(Some(o)))) = steps.get(1).copied() {
                            self.r.borrow_mut().overloaded.insert(
                                e,
                                Callee {
                                    def: o.method,
                                    args: o.args,
                                },
                            );
                            return target;
                        }
                        let rt = self.resolve(t);
                        if !rt.has_errors() {
                            self.emit(
                                Diag::error(format!("type `{rt}` cannot be dereferenced"))
                                    .code("E0614")
                                    .span(span, ""),
                            );
                        }
                        Ty::ERROR
                    }
                };
                if let Some(h) = expected.only_has_type() {
                    let _ = self.infcx.unify(inner, h);
                }
                inner
            }
            UnOp::Neg | UnOp::Not => {
                let t = self.check_expr_with(x, expected);
                let t = self.structurally_resolve(t);
                let builtin = match op {
                    UnOp::Neg => {
                        t.is_signed()
                            || t.is_float()
                            || matches!(t.kind(), TyKind::Infer(InferTy::IntVar(_)))
                    }
                    _ => t.is_integral() || t == Ty::BOOL,
                };
                if builtin || t.is_error() {
                    if op == UnOp::Neg && matches!(t.kind(), TyKind::Uint(_)) {
                        self.emit(
                            Diag::error(format!("cannot apply unary operator `-` to type `{t}`"))
                                .code("E0600")
                                .span(span, ""),
                        );
                    }
                    return t;
                }
                let (lang, method) = if op == UnOp::Neg {
                    ("neg", "neg")
                } else {
                    ("not", "not")
                };
                let Some(trait_) = self.tcx.lang_item(lang) else {
                    self.emit(
                        Diag::error(format!(
                            "cannot apply unary operator `{}` to type `{}`",
                            if op == UnOp::Neg { "-" } else { "!" },
                            self.resolve(t)
                        ))
                        .code("E0600")
                        .span(span, ""),
                    );
                    return Ty::ERROR;
                };
                let args = Args::from_tys(&[t]);
                self.register_trait(trait_, args, span);
                if let Some(m) = self.tcx.assoc_item(trait_, Symbol::intern(method), true) {
                    self.r
                        .borrow_mut()
                        .overloaded
                        .insert(e, Callee { def: m, args });
                }
                let Some(output) = self.tcx.assoc_item(trait_, hyprc_span::sym::Output, false)
                else {
                    return Ty::ERROR;
                };
                self.normalize(Ty::new(TyKind::Alias(
                    AliasKind::Projection,
                    AliasTy {
                        def: output,
                        args,
                        index: 0,
                    },
                )))
            }
        }
    }

    pub(crate) fn check_cast(&self, e: ExprId, x: ExprId, from: Ty, to: Ty) {
        // Casts that are coercions (`&T as *const T`, `fn item as fn ptr`): coerce.
        let from_s = self.structurally_resolve(from);
        let to_s = self.structurally_resolve(to);
        let is_numeric = |t: Ty| {
            matches!(
                t.kind(),
                TyKind::Int(_)
                    | TyKind::Uint(_)
                    | TyKind::Float(_)
                    | TyKind::Infer(InferTy::IntVar(_) | InferTy::FloatVar(_))
            )
        };
        if !from_s.has_infer()
            && !to_s.has_infer()
            && !matches!(
                (from_s.kind(), to_s.kind()),
                (TyKind::RawPtr(..), TyKind::RawPtr(..))
            )
            && !is_numeric(from_s)
            && !is_numeric(to_s)
        {
            if self
                .infcx
                .commit_if_ok(|| self.try_coerce(x, from_s, to_s))
                .is_ok()
            {
                self.r.borrow_mut().casts.push((e, to_s, to_s));
                return;
            }
        }
        // An integer variable cast to anything: it stays `i32` unless unified elsewhere.
        self.r.borrow_mut().casts.push((e, from, to));
    }

    /// Checks recorded casts once types are known.
    pub(crate) fn check_casts(&self) {
        let casts = self.r.borrow().casts.clone();
        for (e, from, to) in casts {
            let from_s = self.structurally_resolve(from);
            let to_s = self.structurally_resolve(to);
            let f_inner = match from_s.kind() {
                TyKind::RawPtr(f, _) | TyKind::Ref(f, _) => Some(*f),
                _ => None,
            };
            if let (Some(f), TyKind::RawPtr(t, _)) = (f_inner, to_s.kind()) {
                if t.is_ty_var() {
                    let _ = self.infcx.unify(*t, f);
                }
            }
            let from = self.resolve(from);
            let to = self.resolve(to);
            if from.has_errors() || to.has_errors() || from.has_infer() || to.has_infer() {
                continue;
            }
            let x = match self.body.expr(e).kind {
                hyprc_hir::ExprKind::Cast(inner, _) => inner,
                _ => e,
            };
            if self.try_coerce(x, from, to).is_ok() {
                continue;
            }
            if !valid_cast(self, from, to) {
                self.emit(
                    Diag::error(format!("non-primitive cast: `{from}` as `{to}`"))
                        .code("E0605")
                        .span(self.span(e), "an `as` expression can only be used to convert between primitive types or to coerce to a specific trait object"),
                );
            }
        }
    }
}

fn valid_cast(fcx: &FnCtxt<'_, '_>, from: Ty, to: Ty) -> bool {
    use TyKind::*;
    if from == to {
        return true;
    }
    let is_int = |t: Ty| matches!(t.kind(), Int(_) | Uint(_));
    let is_num = |t: Ty| matches!(t.kind(), Int(_) | Uint(_) | Float(_));
    match (*from.kind(), *to.kind()) {
        _ if is_num(from) && is_num(to) => true,
        (Bool | Char, _) if is_int(to) => true,
        (Uint(hyprc_hir::UintTy::U8), Char) => true,
        (RawPtr(..), RawPtr(..)) => true,
        (RawPtr(..), _) if is_int(to) => true,
        (_, RawPtr(..)) if is_int(from) => true,
        (Ref(..), RawPtr(..)) => true,
        (FnDef(..) | FnPtr(_), RawPtr(..)) => true,
        (FnDef(..) | FnPtr(_), _) if is_int(to) => true,
        (FnDef(..), FnPtr(_)) | (Closure(..), FnPtr(_)) => true,
        (Adt(d, _), _) if is_int(to) => {
            let adt = fcx.tcx.adt_def(d);
            adt.is_enum() && adt.variants.iter().all(|v| v.fields.is_empty())
        }
        (Never, _) => true,
        _ => false,
    }
}
