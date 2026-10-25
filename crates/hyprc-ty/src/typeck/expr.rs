//! Expressions.

use super::{Adjust, Adjustment, Expectation, FnCtxt, LoopCtxt};
use crate::lower_ty::TyLowerer;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{BorrowKind, ExprId, ExprKind, Mutability};
use hyprc_span::{Diag, Span};
use hyprc_syntax::token::LitKind;

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn write_ty(&self, e: ExprId, t: Ty) {
        self.r.borrow_mut().expr_tys[e.index()] = t;
    }

    pub(crate) fn add_adjustments(&self, e: ExprId, adj: Vec<Adjustment>) {
        if adj.is_empty() {
            return;
        }
        self.r
            .borrow_mut()
            .adjustments
            .entry(e)
            .or_default()
            .extend(adj);
    }

    pub(crate) fn span(&self, e: ExprId) -> Span {
        self.body.expr(e).span
    }

    /// Lowers a type written in the body (`_` and missing arguments infer).
    pub(crate) fn lower_ty(&self, t: &hir::Ty) -> Ty {
        let infer = |span: Span| self.next_ty_var(span);
        let infer_const = |ty: Ty| self.infcx.new_const_var(ty);
        let t = TyLowerer::with_infer(self.tcx, self.owner, &infer, &infer_const).lower(t);
        self.normalize(t)
    }

    /// The type in front of `::item` in an expression (`Vec::new`, `ControlFlow::from_try`):
    /// parameters without arguments are inferred, not defaulted.
    pub(crate) fn lower_value_path_ty(&self, t: &hir::Ty) -> Ty {
        let infer = |span: Span| self.next_ty_var(span);
        let infer_const = |ty: Ty| self.infcx.new_const_var(ty);
        let mut lowerer = TyLowerer::with_infer(self.tcx, self.owner, &infer, &infer_const);
        lowerer.value_path = true;
        let t = lowerer.lower(t);
        self.normalize(t)
    }

    pub(crate) fn check_expr(&self, e: ExprId) -> Ty {
        self.check_expr_with(e, Expectation::None)
    }

    pub(crate) fn check_expr_with(&self, e: ExprId, expected: Expectation) -> Ty {
        let old = self.diverges.replace(false);
        let ty = self.check_expr_kind(e, expected);
        self.write_ty(e, ty);
        if self.shallow(ty).is_never() {
            self.diverges.set(true);
        }
        self.diverges.set(self.diverges.get() | old);
        ty
    }

    /// Checks `e` and requires exactly `ty` (no coercion).
    pub(crate) fn check_expr_has_type(&self, e: ExprId, ty: Ty) -> Ty {
        let t = self.check_expr_with(e, Expectation::HasType(ty));
        if self.shallow(t).is_never() {
            self.add_adjustments(
                e,
                vec![Adjustment {
                    kind: Adjust::NeverToAny,
                    target: ty,
                }],
            );
            return ty;
        }
        self.demand_eq(self.span(e), ty, t);
        ty
    }

    /// Checks `e` and coerces it to `ty`.
    pub(crate) fn check_expr_coercible_to(&self, e: ExprId, ty: Ty) -> Ty {
        let t = self.check_expr_with(e, Expectation::HasType(ty));
        self.demand_coerce(e, t, ty);
        ty
    }

    fn check_expr_kind(&self, e: ExprId, expected: Expectation) -> Ty {
        let expr = self.body.expr(e);
        let span = expr.span;
        match &expr.kind {
            ExprKind::Lit(l) => self.check_lit(l, expected),
            ExprKind::Path(q) => self.check_path_expr(e, q, expected),
            ExprKind::Call(f, args) => self.check_call(e, *f, args, expected),
            ExprKind::MethodCall {
                receiver,
                segment,
                args,
            } => self.check_method_call(e, *receiver, segment, args, expected),
            ExprKind::Binary(op, l, r) => self.check_binop(e, *op, *l, *r, expected),
            ExprKind::Unary(op, x) => self.check_unop(e, *op, *x, expected),
            ExprKind::Cast(x, t) => {
                let target = self.lower_ty(t);
                if let Some(h) = expected.only_has_type() {
                    let _ = self.infcx.unify(target, h);
                }
                let from = self.check_expr_with(*x, Expectation::Castable(target));
                self.check_cast(e, *x, from, target);
                target
            }
            ExprKind::Type(x, t) => {
                let target = self.lower_ty(t);
                self.check_expr_has_type(*x, target)
            }
            ExprKind::AddrOf(kind, m, x) => {
                let hint = expected
                    .only_has_type()
                    .and_then(|t| match *self.shallow(t).kind() {
                        TyKind::Ref(inner, _) | TyKind::RawPtr(inner, _) => Some(inner),
                        _ => None,
                    });
                // An unsized hint (`&[T]`, `&dyn Tr` expected) only helps an array literal:
                // `&[&a, &b]` as `&[&dyn Debug]` coerces each element (rustc's rvalue hint).
                let is_array_lit = matches!(
                    self.body.expr(*x).kind,
                    ExprKind::Array(_) | ExprKind::Repeat(..)
                );
                let is_closure = self.is_closure_or_ref(*x);
                let hint = hint.filter(|h| match *self.shallow(*h).kind() {
                    TyKind::Slice(_) => is_array_lit,
                    TyKind::Str => false,
                    TyKind::Dynamic(_) => is_closure,
                    TyKind::Adt(d, args) => {
                        let adt = self.tcx.adt_def(d);
                        if adt.is_struct()
                            && let Some(last) = adt.variants.first().and_then(|v| v.fields.last())
                        {
                            let t = last.ty.subst(args);
                            !matches!(
                                self.shallow(t).kind(),
                                TyKind::Str
                                    | TyKind::Slice(_)
                                    | TyKind::Dynamic(_)
                                    | TyKind::Adt(..)
                                    | TyKind::Tuple(_)
                            )
                        } else {
                            true
                        }
                    }
                    _ => true,
                });
                let t = match hint {
                    Some(h) => self.check_expr_with(*x, Expectation::HasType(h)),
                    None => self.check_expr(*x),
                };
                match kind {
                    BorrowKind::Raw => Ty::ptr(t, *m),
                    _ => Ty::reference(t, *m),
                }
            }
            ExprKind::Field(base, name) => self.check_field(e, *base, *name),
            ExprKind::Index(base, idx) => self.check_index(e, *base, *idx),
            ExprKind::Tuple(es) => {
                let hints: Vec<Option<Ty>> = match expected.only_has_type().map(|t| self.shallow(t))
                {
                    Some(t) if t.tuple_fields().len() == es.len() => {
                        t.tuple_fields().iter().map(|&t| Some(t)).collect()
                    }
                    _ => vec![None; es.len()],
                };
                let tys: Vec<Ty> = es
                    .iter()
                    .zip(hints)
                    .map(|(&x, h)| match h {
                        Some(h) => self.check_expr_coercible_to(x, h),
                        None => self.check_expr(x),
                    })
                    .collect();
                Ty::tuple(&tys)
            }
            ExprKind::Array(es) => {
                let elem = match expected
                    .only_has_type()
                    .map(|t| self.shallow(t))
                    .map(|t| *t.kind())
                {
                    Some(TyKind::Array(t, _)) | Some(TyKind::Slice(t)) => t,
                    _ => self.next_ty_var(span),
                };
                for &x in es {
                    self.check_expr_coercible_to(x, elem);
                }
                Ty::array(elem, Const::from_usize(es.len() as u64))
            }
            ExprKind::Repeat(x, count) => {
                let elem = match expected
                    .only_has_type()
                    .map(|t| self.shallow(t))
                    .map(|t| *t.kind())
                {
                    Some(TyKind::Array(t, _)) => t,
                    _ => self.next_ty_var(span),
                };
                self.check_expr_coercible_to(*x, elem);
                let infer = |s: Span| self.next_ty_var(s);
                let infer_const = |ty: Ty| self.infcx.new_const_var(ty);
                let len = TyLowerer::with_infer(self.tcx, self.owner, &infer, &infer_const)
                    .lower_const_arg(count, Ty::USIZE);
                Ty::array(elem, len)
            }
            ExprKind::Struct { path, fields, tail } => {
                self.check_struct(e, path, fields, tail, expected)
            }
            ExprKind::If { cond, then, els } => self.check_if(*cond, *then, *els, expected, span),
            ExprKind::Let { pat, init } => {
                let t = self.check_expr(*init);
                self.check_pat_top(*pat, t, false);
                Ty::BOOL
            }
            ExprKind::Loop { body, id, source } => {
                let can_break_value = matches!(source, hir::LoopSource::Loop);
                let break_ty = if can_break_value {
                    expected.only_has_type()
                } else {
                    Some(Ty::UNIT)
                };
                self.loops.borrow_mut()[id.index()] = Some(LoopCtxt {
                    break_ty,
                    may_break: false,
                });
                self.check_block(body, Expectation::HasType(Ty::UNIT));
                let ctx = self.loops.borrow_mut()[id.index()].take().unwrap();
                if !ctx.may_break {
                    self.diverges.set(true);
                    return Ty::NEVER;
                }
                self.diverges.set(false);
                ctx.break_ty.unwrap_or(Ty::UNIT)
            }
            ExprKind::Match {
                scrutinee, arms, ..
            } => self.check_match(*scrutinee, arms, expected, span),
            ExprKind::Block(b, label) => {
                if let Some(id) = label {
                    self.loops.borrow_mut()[id.index()] = Some(LoopCtxt {
                        break_ty: expected.only_has_type(),
                        may_break: false,
                    });
                }
                let t = self.check_block(b, expected);
                if let Some(id) = label {
                    let ctx = self.loops.borrow_mut()[id.index()].take().unwrap();
                    if ctx.may_break {
                        let bt = ctx.break_ty.unwrap_or(Ty::UNIT);
                        if let Some(tail) = b.tail {
                            self.demand_coerce(tail, t, bt);
                        } else if !self.shallow(t).is_never() {
                            self.demand_eq(span, bt, t);
                        }
                        self.diverges.set(false);
                        return bt;
                    }
                }
                t
            }
            ExprKind::Assign(l, r) => {
                let lt = self.check_expr(*l);
                self.check_expr_coercible_to(*r, lt);
                Ty::UNIT
            }
            ExprKind::AssignOp(op, l, r) => self.check_assign_op(e, *op, *l, *r),
            ExprKind::Break { target, value } => {
                let Some(target) = target else {
                    if let Some(v) = value {
                        self.check_expr(*v);
                    }
                    return Ty::NEVER;
                };
                let break_ty = self.loops.borrow()[target.index()]
                    .as_ref()
                    .map(|c| c.break_ty);
                let Some(break_ty) = break_ty else {
                    // A break out of a closure (rejected by rustc too).
                    return Ty::NEVER;
                };
                let ty = match (value, break_ty) {
                    (Some(v), Some(bt)) => self.check_expr_coercible_to(*v, bt),
                    (Some(v), None) => self.check_expr(*v),
                    (None, Some(bt)) => {
                        self.demand_eq(span, bt, Ty::UNIT);
                        Ty::UNIT
                    }
                    (None, None) => Ty::UNIT,
                };
                if let Some(ctx) = self.loops.borrow_mut()[target.index()].as_mut() {
                    ctx.may_break = true;
                    if ctx.break_ty.is_none() {
                        ctx.break_ty = Some(ty);
                    }
                }
                Ty::NEVER
            }
            ExprKind::Continue { .. } => Ty::NEVER,
            ExprKind::Return(v) => {
                let ret = *self.ret_tys.borrow().last().unwrap_or(&Ty::UNIT);
                match v {
                    Some(v) => {
                        self.check_expr_coercible_to(*v, ret);
                    }
                    None => {
                        if !self.demand_eq_silent(ret, Ty::UNIT) {
                            self.emit(Diag::error("mismatched types").code("E0069").span(
                                span,
                                format!("expected `{}`, found `()`", self.resolve(ret)),
                            ));
                        }
                    }
                }
                Ty::NEVER
            }
            ExprKind::Become(x) => {
                self.check_expr(*x);
                Ty::NEVER
            }
            ExprKind::Closure(id) => self.check_closure(e, *id, expected),
            ExprKind::ConstBlock(x) => self.check_expr_with(*x, expected),
            ExprKind::Yield(v) => {
                if let Some(v) = v {
                    self.check_expr(*v);
                }
                Ty::UNIT
            }
            ExprKind::Await(x) => self.check_await(*x, span),
            ExprKind::FormatArgs(f) => {
                for &a in &f.args {
                    self.check_expr(a);
                }
                match self.tcx.lang_item("format_arguments") {
                    Some(d) => Ty::adt(d, Args::EMPTY),
                    None => {
                        self.err(
                            span,
                            "`format_args!` needs the `format_arguments` lang item (core)",
                        );
                        Ty::ERROR
                    }
                }
            }
            ExprKind::InlineAsm(asm) => {
                if asm
                    .tokens
                    .tokens()
                    .iter()
                    .any(|t| t.sym.as_str() == "noreturn")
                {
                    Ty::NEVER
                } else {
                    Ty::UNIT
                }
            }
            ExprKind::OffsetOf(t, fields) => {
                let container = self.lower_ty(t);
                self.check_offset_of(e, container, fields);
                Ty::USIZE
            }
            ExprKind::Err => Ty::ERROR,
        }
    }

    pub(crate) fn demand_eq_silent(&self, a: Ty, b: Ty) -> bool {
        self.infcx.unify(a, b).is_ok()
    }

    fn check_lit(&self, l: &hir::Lit, expected: Expectation) -> Ty {
        match l.kind {
            LitKind::Integer => {
                if !l.suffix.as_str().is_empty() {
                    return match hyprc_hir::PrimTy::from_name(l.suffix) {
                        Some(p) => crate::lower_ty::prim_ty(p),
                        None => {
                            self.err(
                                l.span,
                                format!("invalid suffix `{}` for number literal", l.suffix),
                            );
                            Ty::ERROR
                        }
                    };
                }
                if let Some(h) = expected.hint() {
                    let h = self.shallow(h);
                    if h.is_integral() || matches!(h.kind(), TyKind::Infer(InferTy::IntVar(_))) {
                        return h;
                    }
                    // `1 as f64`, `0 as *const T`, `65 as char`: the literal is an integer.
                    if matches!(expected, Expectation::HasType(_)) && h.is_float() {
                        // `let x: f64 = 1;` is an error in rustc; keep an integer var.
                    }
                }
                self.infcx.new_int_var()
            }
            LitKind::Float => {
                match l.suffix.as_str() {
                    "f32" => return Ty::F32,
                    "f64" => return Ty::F64,
                    "f16" => return Ty::F16,
                    "f128" => return Ty::F128,
                    "" => {}
                    s => {
                        self.err(l.span, format!("invalid suffix `{s}` for float literal"));
                        return Ty::ERROR;
                    }
                }
                if let Some(h) = expected.hint() {
                    let h = self.shallow(h);
                    if h.is_float() {
                        return h;
                    }
                }
                self.infcx.new_float_var()
            }
            LitKind::Str | LitKind::StrRaw(_) => Ty::reference(Ty::STR, Mutability::Not),
            LitKind::ByteStr | LitKind::ByteStrRaw(_) => {
                let len = byte_str_len(l.symbol.as_str(), matches!(l.kind, LitKind::ByteStrRaw(_)));
                Ty::reference(
                    Ty::array(Ty::U8, Const::from_usize(len as u64)),
                    Mutability::Not,
                )
            }
            LitKind::CStr | LitKind::CStrRaw(_) => match self.tcx.lang_item("CStr") {
                Some(d) => Ty::reference(Ty::adt(d, Args::EMPTY), Mutability::Not),
                None => {
                    self.err(l.span, "C string literals need the `CStr` lang item (core)");
                    Ty::ERROR
                }
            },
            LitKind::Char => Ty::CHAR,
            LitKind::Byte => Ty::U8,
            LitKind::Bool => Ty::BOOL,
            LitKind::Err => Ty::ERROR,
        }
    }

    // ---------------------------------------------------------------------------------------
    // Blocks and control flow

    pub(crate) fn check_block(&self, b: &hir::Block, expected: Expectation) -> Ty {
        let check = || {
            for s in &b.stmts {
                self.check_stmt(s);
            }
            match b.tail {
                Some(t) => {
                    let ty = self.check_expr_with(t, expected);
                    if self.diverges.get() && !self.shallow(ty).is_never() {
                        // Code after a diverging statement: the block has the tail's type.
                    }
                    ty
                }
                None => {
                    if self.diverges.get() {
                        Ty::NEVER
                    } else {
                        Ty::UNIT
                    }
                }
            }
        };
        let old = self.diverges.replace(false);
        if let Some(s) = b.scope {
            self.block_scopes.borrow_mut().push(s);
        }
        let t = if b.unsafe_ {
            self.enter_unsafe(check)
        } else {
            check()
        };
        if b.scope.is_some() {
            self.block_scopes.borrow_mut().pop();
        }
        self.diverges.set(self.diverges.get() | old);
        t
    }

    fn check_stmt(&self, s: &hir::Stmt) {
        match &s.kind {
            hir::StmtKind::Let { pat, ty, init, els } => {
                let decl = match ty {
                    Some(t) => self.lower_ty(t),
                    None => self.next_ty_var(s.span),
                };
                if let Some(init) = init {
                    if ty.is_some() {
                        self.check_expr_coercible_to(*init, decl);
                    } else {
                        let t = self.check_expr_with(*init, Expectation::None);
                        if self.shallow(t).is_never() {
                            // `let x = return;`: `x` gets a fresh (fallback `()`) type.
                            self.add_adjustments(
                                *init,
                                vec![Adjustment {
                                    kind: Adjust::NeverToAny,
                                    target: decl,
                                }],
                            );
                            self.diverging_vars.borrow_mut().push(decl);
                        } else {
                            self.demand_eq(self.span(*init), decl, t);
                        }
                    }
                }
                self.check_pat_top(*pat, decl, init.is_none() || els.is_some());
                if let Some(els) = els {
                    let saved = self.diverges.get();
                    let t = self.check_block(els, Expectation::HasType(Ty::NEVER));
                    if !self.shallow(t).is_never() {
                        self.emit(
                            Diag::error("`else` clause of `let...else` does not diverge")
                                .code("E0308")
                                .span(els.span, ""),
                        );
                    }
                    self.diverges.set(saved);
                }
            }
            hir::StmtKind::Expr(e) => {
                self.check_expr_with(*e, Expectation::None);
            }
        }
    }

    fn check_if(
        &self,
        cond: ExprId,
        then: ExprId,
        els: Option<ExprId>,
        expected: Expectation,
        span: Span,
    ) -> Ty {
        self.check_expr_has_type(cond, Ty::BOOL);
        let cond_diverges = self.diverges.replace(false);
        let Some(els) = els else {
            let t = self.check_expr_with(then, Expectation::HasType(Ty::UNIT));
            self.demand_coerce(then, t, Ty::UNIT);
            self.diverges.set(cond_diverges);
            return Ty::UNIT;
        };
        let t1 = self.check_expr_with(then, expected);
        let then_diverges = self.diverges.replace(false);
        let t2 = self.check_expr_with(els, expected);
        let else_diverges = self.diverges.get();
        self.diverges
            .set(cond_diverges || (then_diverges && else_diverges));
        self.coerce_branches(&[(then, t1), (els, t2)], expected, span)
    }

    fn check_match(
        &self,
        scrutinee: ExprId,
        arms: &[hir::Arm],
        expected: Expectation,
        span: Span,
    ) -> Ty {
        let st = self.check_expr(scrutinee);
        let scrut_diverges = self.diverges.replace(false);
        let mut branch_tys = Vec::new();
        let mut all_diverge = !arms.is_empty();
        for arm in arms {
            self.check_pat_top(arm.pat, st, true);
            if let Some(g) = arm.guard {
                self.check_expr_has_type(g, Ty::BOOL);
            }
            self.diverges.set(false);
            let t = self.check_expr_with(arm.body, expected);
            all_diverge &= self.diverges.get();
            branch_tys.push((arm.body, t));
        }
        self.diverges.set(scrut_diverges || all_diverge);
        if arms.is_empty() {
            self.diverges.set(true);
            return Ty::NEVER;
        }
        self.coerce_branches(&branch_tys, expected, span)
    }

    // ---------------------------------------------------------------------------------------
    // Calls

    pub(crate) fn check_call(
        &self,
        e: ExprId,
        f: ExprId,
        args: &[ExprId],
        expected: Expectation,
    ) -> Ty {
        let callee = self.check_expr(f);
        let callee = self.structurally_resolve(callee);
        let span = self.span(e);
        let mut legacy_indices = None;
        let sig = match *callee.kind() {
            TyKind::FnDef(d, fargs) => {
                let sig = self.tcx.fn_sig(d).subst(fargs);
                if sig.unsafe_ {
                    self.require_unsafe(span, "call to unsafe function");
                }
                if let Some(item) = self.tcx.hir.get_item(d) {
                    legacy_indices = item.attrs.legacy_const_generics.clone();
                }
                Some(self.normalize_sig(sig))
            }
            TyKind::FnPtr(sig) => {
                if sig.unsafe_ {
                    self.require_unsafe(span, "call to unsafe function");
                }
                Some(sig)
            }
            TyKind::Closure(c, cargs) => self.closure_sig_now(c, cargs),
            TyKind::Error => None,
            _ => {
                // Overloaded: something implementing `Fn*` (possibly behind references).
                match self.check_overloaded_call(e, f, callee, args) {
                    Some(t) => return t,
                    None => {
                        self.emit(
                            Diag::error(format!(
                                "expected function, found `{}`",
                                self.resolve(callee)
                            ))
                            .code("E0618")
                            .span(self.span(f), "call expression requires function"),
                        );
                        for &a in args {
                            self.check_expr(a);
                        }
                        return Ty::ERROR;
                    }
                }
            }
        };
        let Some(sig) = sig else {
            for &a in args {
                self.check_expr(a);
            }
            return Ty::ERROR;
        };
        if let Some(indices) = legacy_indices
            && args.len() == sig.inputs().len() + indices.len()
        {
            let mut runtime_args = Vec::with_capacity(sig.inputs().len());
            for (idx, &arg) in args.iter().enumerate() {
                if indices.contains(&idx) {
                    let arg_ty = self.check_expr(arg);
                    if let TyKind::FnDef(_, fargs) = *callee.kind() {
                        for g in fargs.as_slice() {
                            if let GenericArg::Const(c) = g {
                                let c_res = self.infcx.resolve_const(*c);
                                if matches!(c_res.kind(), ConstKind::Infer(_)) {
                                    let val = match &self.body.expr(arg).kind {
                                        hir::ExprKind::Lit(lit) => {
                                            lit.symbol.as_str().parse::<u128>().unwrap_or(0)
                                        }
                                        _ => 0,
                                    };
                                    let _ = self
                                        .infcx
                                        .unify_const(*c, Const::new(arg_ty, ConstKind::Value(val)));
                                    break;
                                }
                            }
                        }
                    }
                } else {
                    runtime_args.push(arg);
                }
            }
            let expected_inputs = self.expected_inputs_for(sig.inputs(), sig.output(), expected);
            self.check_args_with(
                span,
                sig.inputs(),
                &expected_inputs,
                &runtime_args,
                sig.c_variadic,
            );
        } else {
            let expected_inputs = self.expected_inputs_for(sig.inputs(), sig.output(), expected);
            self.check_args_with(span, sig.inputs(), &expected_inputs, args, sig.c_variadic);
        }
        sig.output()
    }

    /// What the arguments are expected to be, given what the call's result is expected to be
    /// (`Ok(x)` as `Result<&T, E>`: `x` is a `&T`, so a `&mut T` coerces). Only hints: the
    /// unification is undone (rustc's `expected_inputs_for_expected_output`).
    pub(crate) fn expected_inputs_for(
        &self,
        inputs: &[Ty],
        output: Ty,
        expected: Expectation,
    ) -> Vec<Option<Ty>> {
        let Some(h) = expected.only_has_type() else {
            return vec![None; inputs.len()];
        };
        let h = self.resolve(h);
        if h.is_ty_var() || h.has_errors() {
            return vec![None; inputs.len()];
        }
        self.infcx.probe(|| {
            if self.infcx.unify(output, h).is_err() {
                return vec![None; inputs.len()];
            }
            inputs
                .iter()
                .map(|&t| {
                    let t = self.infcx.resolve_vars(t);
                    (!t.is_ty_var()
                        && !matches!(
                            t.kind(),
                            TyKind::Slice(_) | TyKind::Str | TyKind::Dynamic(_)
                        ))
                    .then_some(t)
                })
                .collect()
        })
    }

    /// Arguments against parameters; closures last, so the others inform them.
    pub(crate) fn check_args(&self, span: Span, inputs: &[Ty], args: &[ExprId], c_variadic: bool) {
        self.check_args_with(span, inputs, &[], args, c_variadic);
    }

    /// [`Self::check_args`] with expected types for the arguments (see
    /// [`Self::expected_inputs_for`]): an argument coerces to its expected type, which the
    /// parameter's type must then be.
    pub(crate) fn check_args_with(
        &self,
        span: Span,
        inputs: &[Ty],
        expected_inputs: &[Option<Ty>],
        args: &[ExprId],
        c_variadic: bool,
    ) {
        let count_ok = if c_variadic {
            args.len() >= inputs.len()
        } else {
            args.len() == inputs.len()
        };
        if !count_ok {
            let s = |n: usize| if n == 1 { "" } else { "s" };
            self.emit(
                Diag::error(format!(
                    "this function takes {}{} argument{} but {} argument{} {} supplied",
                    if c_variadic { "at least " } else { "" },
                    inputs.len(),
                    s(inputs.len()),
                    args.len(),
                    s(args.len()),
                    if args.len() == 1 { "was" } else { "were" }
                ))
                .code("E0061")
                .span(span, ""),
            );
        }
        for pass in 0..2 {
            // What's known so far decides more of the parameter types (closures need them).
            self.select_where_possible();
            for (i, &a) in args.iter().enumerate() {
                let is_closure = self.is_closure_or_ref(a);
                if (pass == 0) == is_closure {
                    continue;
                }
                match inputs.get(i) {
                    Some(&t) => match expected_inputs.get(i).copied().flatten() {
                        Some(want) if want != t => {
                            self.check_expr_coercible_to(a, want);
                            self.demand_eq(self.span(a), t, want);
                        }
                        _ => {
                            self.check_expr_coercible_to(a, t);
                        }
                    },
                    None => {
                        // C variadic arguments: promoted like C does.
                        let t = self.check_expr(a);
                        let t = self.shallow(t);
                        if matches!(t.kind(), TyKind::Infer(InferTy::IntVar(_))) {
                            let _ = self.infcx.unify(t, Ty::I32);
                        } else if matches!(t.kind(), TyKind::Infer(InferTy::FloatVar(_))) {
                            let _ = self.infcx.unify(t, Ty::F64);
                        }
                    }
                }
            }
        }
    }

    fn is_closure_or_ref(&self, mut e: ExprId) -> bool {
        while let ExprKind::AddrOf(_, _, inner) = self.body.expr(e).kind {
            e = inner;
        }
        matches!(self.body.expr(e).kind, ExprKind::Closure(_))
    }

    /// `offset_of!(T, a.b)`: each field of the path (`Enum, Variant.field` for enums).
    fn check_offset_of(&self, e: ExprId, container: Ty, fields: &[hyprc_span::Ident]) {
        let mut steps = Vec::with_capacity(fields.len());
        let mut cur = container;
        let mut i = 0;
        while i < fields.len() {
            let name = fields[i];
            let ty = self.structurally_resolve(cur);
            let found = match *ty.kind() {
                TyKind::Adt(d, args) => {
                    let adt = self.tcx.adt_def(d);
                    let (vi, field) = if adt.is_enum() {
                        let vi = adt
                            .variants
                            .iter()
                            .position(|v| self.tcx.hir.name(v.def) == name.name);
                        i += 1;
                        (vi, fields.get(i).copied())
                    } else {
                        (Some(0), Some(name))
                    };
                    match (vi, field) {
                        (Some(vi), Some(f)) => adt.variants[vi]
                            .fields
                            .iter()
                            .position(|fd| fd.name == f.name)
                            .map(|fi| {
                                (
                                    vi as u32,
                                    fi as u32,
                                    self.normalize(adt.variants[vi].fields[fi].ty.subst(args)),
                                )
                            }),
                        _ => None,
                    }
                }
                TyKind::Tuple(ts) => name
                    .name
                    .as_str()
                    .parse::<usize>()
                    .ok()
                    .and_then(|fi| ts.as_slice().get(fi).map(|&t| (0, fi as u32, t))),
                TyKind::Error => return,
                _ => None,
            };
            let Some(step) = found else {
                self.emit(
                    Diag::error(format!(
                        "no field `{}` on type `{}`",
                        name.name,
                        self.resolve(cur)
                    ))
                    .code("E0609")
                    .span(name.span, "unknown field"),
                );
                return;
            };
            cur = step.2;
            steps.push(step);
            i += 1;
        }
        self.r.borrow_mut().offset_of.insert(e, (container, steps));
    }

    // ---------------------------------------------------------------------------------------
    // Places: fields and indexing

    fn is_visible(&self, vis: hir::Vis) -> bool {
        match vis {
            hir::Vis::Public => true,
            hir::Vis::Restricted(m) => {
                let mut cur = Some(self.owner);
                while let Some(c) = cur {
                    if c == m {
                        return true;
                    }
                    cur = self.tcx.hir.parent(c);
                }
                false
            }
        }
    }

    fn check_field(&self, e: ExprId, base: ExprId, name: hyprc_span::Ident) -> Ty {
        let base_ty = self.check_expr(base);
        let span = self.span(e);
        let steps = self.autoderef_steps(base_ty, span);
        let mut private_field = None;
        for (i, (ty, _)) in steps.iter().enumerate() {
            let ty = self.structurally_resolve(*ty);
            match *ty.kind() {
                TyKind::Adt(d, args) => {
                    let adt = self.tcx.adt_def(d);
                    if adt.is_enum() {
                        continue;
                    }
                    let Some(v) = adt.variants.first() else {
                        continue;
                    };
                    if let Some(idx) = v.fields.iter().position(|f| f.name == name.name) {
                        let field = &v.fields[idx];
                        if !self.is_visible(field.vis) {
                            private_field.get_or_insert(field.span);
                            continue;
                        }
                        let fty = self.normalize(field.ty.subst(args));
                        self.record_autoderef(base, &steps[..=i]);
                        self.r.borrow_mut().field_indices.insert(e, idx);
                        if adt.is_union() {
                            self.require_unsafe(span, "access to union field");
                        }
                        return fty;
                    }
                }
                TyKind::Tuple(ts) => {
                    if let Ok(idx) = name.name.as_str().parse::<usize>()
                        && let Some(&t) = ts.as_slice().get(idx)
                    {
                        self.record_autoderef(base, &steps[..=i]);
                        self.r.borrow_mut().field_indices.insert(e, idx);
                        return t;
                    }
                }
                TyKind::Error => return Ty::ERROR,
                _ => {}
            }
        }
        let bt = self.resolve(base_ty);
        if !bt.has_errors() {
            if bt.has_infer() {
                self.emit(
                    Diag::error("type annotations needed")
                        .code("E0282")
                        .span(self.span(base), "type must be known at this point"),
                );
            } else if let Some(_) = private_field {
                self.emit(
                    Diag::error(format!("field `{name}` of struct is private"))
                        .code("E0616")
                        .span(name.span, "private field"),
                );
            } else {
                self.emit(
                    Diag::error(format!("no field `{name}` on type `{bt}`"))
                        .code("E0609")
                        .span(name.span, "unknown field"),
                );
            }
        }
        Ty::ERROR
    }

    fn check_index(&self, e: ExprId, base: ExprId, idx: ExprId) -> Ty {
        let base_ty = self.check_expr(base);
        let idx_ty = self.check_expr(idx);
        let span = self.span(e);
        let steps = self.autoderef_steps(base_ty, span);
        for (i, (ty, _)) in steps.iter().enumerate() {
            let ty = self.structurally_resolve(*ty);
            // Built-in: arrays and slices by `usize`.
            if let Some(elem) = match *ty.kind() {
                TyKind::Array(t, _) | TyKind::Slice(t) => Some(t),
                _ => None,
            } {
                let it = self.shallow(idx_ty);
                if it == Ty::USIZE || matches!(it.kind(), TyKind::Infer(InferTy::IntVar(_))) {
                    let _ = self.infcx.unify(it, Ty::USIZE);
                    self.record_autoderef(base, &steps[..=i]);
                    return elem;
                }
            }
            // Overloaded: `Index<I>`.
            if let Some(index_trait) = self.tcx.lang_item("index") {
                let tr = TraitRef::new(index_trait, Args::from_tys(&[ty, idx_ty]));
                if self.evaluate(Predicate::Trait(tr)) != crate::traits::Eval::Fails {
                    self.record_autoderef(base, &steps[..=i]);
                    self.register(Predicate::Trait(tr), span);
                    let Some(output) =
                        self.tcx
                            .assoc_item(index_trait, hyprc_span::sym::Output, false)
                    else {
                        return Ty::ERROR;
                    };
                    let out = Ty::new(TyKind::Alias(
                        AliasKind::Projection,
                        AliasTy {
                            def: output,
                            args: tr.args,
                            index: 0,
                        },
                    ));
                    if let Some(method) =
                        self.tcx
                            .assoc_item(index_trait, hyprc_span::sym::index, true)
                    {
                        self.r.borrow_mut().overloaded.insert(
                            e,
                            super::Callee {
                                def: method,
                                args: tr.args,
                            },
                        );
                    }
                    return self.normalize(out);
                }
            }
            // Arrays index like slices (unsizing).
            if let TyKind::Array(elem, _) = *ty.kind()
                && let Some(index_trait) = self.tcx.lang_item("index")
            {
                let slice = Ty::slice(elem);
                let tr = TraitRef::new(index_trait, Args::from_tys(&[slice, idx_ty]));
                if self.evaluate(Predicate::Trait(tr)) != crate::traits::Eval::Fails {
                    let mut adj = self.autoderef_adjustments(&steps[..=i]);
                    let r = Ty::reference(ty, Mutability::Not);
                    adj.push(Adjustment {
                        kind: Adjust::Borrow(Mutability::Not),
                        target: r,
                    });
                    adj.push(Adjustment {
                        kind: Adjust::Unsize,
                        target: Ty::reference(slice, Mutability::Not),
                    });
                    adj.push(Adjustment {
                        kind: Adjust::Deref(None),
                        target: slice,
                    });
                    self.add_adjustments(base, adj);
                    self.register(Predicate::Trait(tr), span);
                    let Some(output) =
                        self.tcx
                            .assoc_item(index_trait, hyprc_span::sym::Output, false)
                    else {
                        return Ty::ERROR;
                    };
                    if let Some(method) =
                        self.tcx
                            .assoc_item(index_trait, hyprc_span::sym::index, true)
                    {
                        self.r.borrow_mut().overloaded.insert(
                            e,
                            super::Callee {
                                def: method,
                                args: tr.args,
                            },
                        );
                    }
                    let out = Ty::new(TyKind::Alias(
                        AliasKind::Projection,
                        AliasTy {
                            def: output,
                            args: tr.args,
                            index: 0,
                        },
                    ));
                    return self.normalize(out);
                }
            }
        }
        let bt = self.resolve(base_ty);
        if !bt.has_errors() {
            self.emit(
                Diag::error(format!("cannot index into a value of type `{bt}`"))
                    .code("E0608")
                    .span(span, ""),
            );
        }
        Ty::ERROR
    }

    // ---------------------------------------------------------------------------------------
    // Struct expressions

    fn check_struct(
        &self,
        e: ExprId,
        path: &hir::QPath,
        fields: &[hir::ExprField],
        tail: &hir::StructTail,
        expected: Expectation,
    ) -> Ty {
        let span = self.span(e);
        let Some((adt_ty, variant_def, variant_idx)) = self.resolve_struct_path(path, span) else {
            for f in fields {
                self.check_expr(f.expr);
            }
            if let hir::StructTail::Base(b) = tail {
                self.check_expr(*b);
            }
            return Ty::ERROR;
        };
        if let Some(h) = expected.only_has_type() {
            let _ = self
                .infcx
                .probe(|| self.infcx.unify(h, adt_ty).is_ok())
                .then(|| self.infcx.unify(h, adt_ty));
        }
        let TyKind::Adt(adt_def_id, args) = *adt_ty.kind() else {
            return Ty::ERROR;
        };
        for p in self.tcx.predicates_of(adt_def_id).iter() {
            self.register(p.subst(args), span);
        }
        let adt = self.tcx.adt_def(adt_def_id);
        let variant = &adt.variants[variant_idx];
        let mut seen = vec![false; variant.fields.len()];
        let mut indices = Vec::with_capacity(fields.len());
        for f in fields {
            match variant.fields.iter().position(|fd| fd.name == f.name.name) {
                Some(i) => {
                    if seen[i] {
                        self.emit(
                            Diag::error(format!("field `{}` specified more than once", f.name))
                                .code("E0062")
                                .span(f.name.span, "used more than once"),
                        );
                    }
                    seen[i] = true;
                    indices.push(i);
                }
                None => {
                    indices.push(usize::MAX);
                    self.emit(
                        Diag::error(format!(
                            "{} `{}` has no field named `{}`",
                            if adt.is_enum() { "variant" } else { "struct" },
                            self.tcx.def_path(variant.def),
                            f.name
                        ))
                        .code("E0560")
                        .span(f.name.span, "unknown field"),
                    );
                }
            }
        }
        // Pass 1: non-closure fields to constrain type parameters first
        for (f, &i) in fields.iter().zip(&indices) {
            if i != usize::MAX && !self.is_closure_or_ref(f.expr) {
                let fty = self.normalize(variant.fields[i].ty.subst(args));
                self.check_expr_coercible_to(f.expr, fty);
            }
        }
        // Pass 2: closures and remaining fields
        for (f, &i) in fields.iter().zip(&indices) {
            if i != usize::MAX && self.is_closure_or_ref(f.expr) {
                let fty = self.normalize(variant.fields[i].ty.subst(args));
                self.check_expr_coercible_to(f.expr, fty);
            } else if i == usize::MAX {
                self.check_expr(f.expr);
            }
        }
        match tail {
            hir::StructTail::Base(b) => {
                self.check_expr_coercible_to(*b, adt_ty);
            }
            hir::StructTail::Defaults => {}
            hir::StructTail::None => {
                if !adt.is_union() {
                    let missing: Vec<String> = variant
                        .fields
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !seen[*i])
                        .map(|(_, f)| format!("`{}`", f.name))
                        .collect();
                    if !missing.is_empty() {
                        self.emit(
                            Diag::error(format!(
                                "missing field{} {} in initializer of `{}`",
                                if missing.len() == 1 { "" } else { "s" },
                                missing.join(", "),
                                self.tcx.def_path(variant.def)
                            ))
                            .code("E0063")
                            .span(span, ""),
                        );
                    }
                }
            }
        }
        self.r.borrow_mut().struct_fields.insert(e, indices);
        self.r
            .borrow_mut()
            .variants
            .insert(e.0, (variant_def, variant_idx));
        adt_ty
    }

    fn check_await(&self, x: ExprId, span: Span) -> Ty {
        let t = self.check_expr(x);
        // `<T as IntoFuture>::Output`.
        let (Some(into_future), Some(output)) = (
            self.tcx.lang_item("into_future"),
            self.tcx.lang_item("future_output"),
        ) else {
            self.err(
                span,
                "`.await` needs the `IntoFuture` and `Future::Output` lang items",
            );
            return Ty::ERROR;
        };
        let trait_ = self.tcx.assoc_container(into_future).unwrap_or(into_future);
        let tr = TraitRef::new(trait_, Args::from_tys(&[t]));
        self.register(Predicate::Trait(tr), span);
        let fut = self.next_ty_var(span);
        if let Some(into_fut_ty) =
            self.tcx
                .assoc_item(trait_, hyprc_span::Symbol::intern("IntoFuture"), false)
        {
            let alias = AliasTy {
                def: into_fut_ty,
                args: tr.args,
                index: 0,
            };
            self.register(Predicate::Projection(alias, fut), span);
        }
        let out = Ty::new(TyKind::Alias(
            AliasKind::Projection,
            AliasTy {
                def: output,
                args: Args::from_tys(&[fut]),
                index: 0,
            },
        ));
        self.normalize(out)
    }
}

/// The number of bytes a byte string literal's text decodes to.
fn byte_str_len(text: &str, raw: bool) -> usize {
    if raw {
        return text.len();
    }
    let mut n = 0;
    let b = text.as_bytes();
    let mut i = 0;
    while i < b.len() {
        if b[i] == b'\\' {
            match b.get(i + 1) {
                Some(b'x') => i += 4,
                Some(b'\n') => {
                    i += 2;
                    while i < b.len() && (b[i] as char).is_ascii_whitespace() {
                        i += 1;
                    }
                    continue;
                }
                _ => i += 2,
            }
        } else {
            i += 1;
        }
        n += 1;
    }
    n
}
