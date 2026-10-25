//! Patterns, with match ergonomics.

use super::{Expectation, FnCtxt};
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{BindingMode, CtorKind, DefKind, Mutability, PatId, PatKind, Res};
use hyprc_span::{Diag, Span};

/// The binding mode non-reference patterns get after skipping references.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum DefaultBm {
    Move,
    Ref(Mutability),
}

impl<'a, 'h> FnCtxt<'a, 'h> {
    pub(crate) fn check_pat_top(&self, p: PatId, expected: Ty, _refutable: bool) {
        self.check_pat(p, expected, DefaultBm::Move);
    }

    fn write_pat_ty(&self, p: PatId, t: Ty) {
        self.r.borrow_mut().pat_tys[p.index()] = t;
    }

    /// Patterns that look through references (match ergonomics) peel them off.
    fn peels_refs(&self, kind: &PatKind) -> bool {
        match kind {
            PatKind::Struct { .. }
            | PatKind::TupleStruct { .. }
            | PatKind::Tuple { .. }
            | PatKind::Slice { .. }
            | PatKind::Range { .. } => true,
            PatKind::Path(q) => !self.path_is_const(q),
            PatKind::Lit(e) => {
                // String literals match `&str` as written; other literals peel.
                !matches!(&self.body.expr(*e).kind, hir::ExprKind::Lit(l) if matches!(l.kind, hyprc_syntax::token::LitKind::Str | hyprc_syntax::token::LitKind::StrRaw(_) | hyprc_syntax::token::LitKind::ByteStr | hyprc_syntax::token::LitKind::ByteStrRaw(_)))
            }
            _ => false,
        }
    }

    fn path_is_const(&self, q: &hir::QPath) -> bool {
        match q {
            hir::QPath::Resolved(_, p) => matches!(
                p.res,
                Res::Def(
                    DefKind::Const | DefKind::AssocConst | DefKind::Static { .. },
                    _
                )
            ),
            // `Self::MAX`: a constant unless it names a variant of an enum.
            hir::QPath::TypeRelative(base, seg) => {
                let base_ty = self.structurally_resolve(self.lower_value_path_ty(base));
                !matches!(*base_ty.kind(), TyKind::Adt(d, _) if self.tcx.adt_def(d).variants.iter().any(|v| v.name == seg.ident.name))
            }
            hir::QPath::LangItem(..) => false,
        }
    }

    /// A constant pattern's item, arguments and type.
    fn const_pat(&self, q: &hir::QPath, span: Span) -> Option<(hyprc_hir::DefId, Args, Ty)> {
        let (def, args) = match q {
            hir::QPath::Resolved(_, p) => match p.res {
                Res::Def(DefKind::Const | DefKind::AssocConst, d) => {
                    let seg_args = p.segments.last().and_then(|s| s.args.as_deref());
                    let args = self.lowerer_args(d, seg_args, &[], None, span);
                    (d, args)
                }
                _ => return None,
            },
            hir::QPath::TypeRelative(base, seg) => {
                let base_ty = self.lower_value_path_ty(base);
                match self.resolve_type_relative(base_ty, seg, span)? {
                    (DefKind::AssocConst, d, args) => (d, args),
                    _ => {
                        self.err(span, "expected a constant, struct or enum variant");
                        return None;
                    }
                }
            }
            hir::QPath::LangItem(..) => return None,
        };
        let ty = self.normalize(self.tcx.type_of(def).subst(args));
        Some((def, args, ty))
    }

    fn check_pat(&self, p: PatId, expected: Ty, def_bm: DefaultBm) {
        let pat = self.body.pat(p);
        let span = pat.span;
        let (expected, def_bm) = if self.peels_refs(&pat.kind) {
            let mut t = self.structurally_resolve(expected);
            let mut bm = def_bm;
            let mut peeled = Vec::new();
            while let TyKind::Ref(inner, m) = *t.kind() {
                peeled.push(t);
                bm = match (bm, m) {
                    (DefaultBm::Move, m) => DefaultBm::Ref(m),
                    (DefaultBm::Ref(Mutability::Mut), m) => DefaultBm::Ref(m),
                    (DefaultBm::Ref(Mutability::Not), _) => DefaultBm::Ref(Mutability::Not),
                };
                t = self.structurally_resolve(inner);
            }
            if !peeled.is_empty() {
                self.r.borrow_mut().pat_adjustments.insert(p, peeled);
            }
            (t, bm)
        } else {
            (expected, def_bm)
        };
        self.write_pat_ty(p, expected);
        match &pat.kind {
            PatKind::Wild | PatKind::Err => {}
            PatKind::Never => {}
            PatKind::Binding { mode, local, sub } => {
                let mode = match (*mode, def_bm) {
                    (BindingMode::Value { mutable: false }, DefaultBm::Ref(m)) => {
                        BindingMode::Ref {
                            mutable: m == Mutability::Mut,
                        }
                    }
                    (m, _) => m,
                };
                let local_ty = match mode {
                    BindingMode::Value { .. } => expected,
                    BindingMode::Ref { mutable } => Ty::reference(
                        expected,
                        if mutable {
                            Mutability::Mut
                        } else {
                            Mutability::Not
                        },
                    ),
                };
                self.r.borrow_mut().binding_modes.insert(p, mode);
                let current = self.r.borrow().local_tys[local.index()];
                if current == Ty::ERROR {
                    self.r.borrow_mut().local_tys[local.index()] = local_ty;
                } else {
                    // An or-pattern binding the same name again.
                    self.demand_eq(span, current, local_ty);
                }
                if let Some(sub) = sub {
                    self.check_pat(*sub, expected, def_bm);
                }
            }
            PatKind::Tuple { pats, rest } => {
                let t = self.structurally_resolve(expected);
                let fields: Vec<Ty> = match *t.kind() {
                    TyKind::Tuple(ts) => ts.as_slice().to_vec(),
                    _ if t.is_ty_var() && rest.is_none() => {
                        let vars: Vec<Ty> = pats.iter().map(|_| self.next_ty_var(span)).collect();
                        let _ = self.infcx.unify(t, Ty::tuple(&vars));
                        vars
                    }
                    _ if t.is_unit() => Vec::new(),
                    TyKind::Error => {
                        for &sp in pats {
                            self.check_pat(sp, Ty::ERROR, def_bm);
                        }
                        return;
                    }
                    _ => {
                        let vars: Vec<Ty> = pats.iter().map(|_| self.next_ty_var(span)).collect();
                        self.demand_eq(span, t, Ty::tuple(&vars));
                        vars
                    }
                };
                self.check_seq(pats, *rest, &fields, def_bm, span);
            }
            PatKind::TupleStruct { path, pats, rest } => {
                let Some((adt_ty, variant, vidx)) = self.resolve_pat_path(path, span, true) else {
                    for &sp in pats {
                        self.check_pat(sp, Ty::ERROR, def_bm);
                    }
                    return;
                };
                self.demand_eq(span, expected, adt_ty);
                self.r
                    .borrow_mut()
                    .variants
                    .insert(p.0 | 0x8000_0000, (variant, vidx));
                let TyKind::Adt(d, args) = *adt_ty.kind() else {
                    return;
                };
                let adt = self.tcx.adt_def(d);
                let fields: Vec<Ty> = adt.variants[vidx]
                    .fields
                    .iter()
                    .map(|f| self.normalize(f.ty.subst(args)))
                    .collect();
                self.check_seq(pats, *rest, &fields, def_bm, span);
            }
            PatKind::Struct { path, fields, rest } => {
                let Some((adt_ty, variant, vidx)) = self.resolve_pat_path(path, span, false) else {
                    for f in fields {
                        self.check_pat(f.pat, Ty::ERROR, def_bm);
                    }
                    return;
                };
                self.demand_eq(span, expected, adt_ty);
                self.r
                    .borrow_mut()
                    .variants
                    .insert(p.0 | 0x8000_0000, (variant, vidx));
                let TyKind::Adt(d, args) = *adt_ty.kind() else {
                    return;
                };
                let adt = self.tcx.adt_def(d);
                let v = &adt.variants[vidx];
                let mut indices = Vec::new();
                for f in fields {
                    match v.fields.iter().position(|fd| fd.name == f.name.name) {
                        Some(i) => {
                            indices.push(i);
                            let fty = self.normalize(v.fields[i].ty.subst(args));
                            self.check_pat(f.pat, fty, def_bm);
                        }
                        None => {
                            indices.push(usize::MAX);
                            self.emit(
                                Diag::error(format!(
                                    "variant `{}` does not have a field named `{}`",
                                    self.tcx.def_path(v.def),
                                    f.name
                                ))
                                .code("E0026")
                                .span(f.name.span, ""),
                            );
                            self.check_pat(f.pat, Ty::ERROR, def_bm);
                        }
                    }
                }
                if !*rest && !adt.is_union() && indices.len() < v.fields.len() {
                    let missing: Vec<String> = v
                        .fields
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| !indices.contains(i))
                        .map(|(_, f)| format!("`{}`", f.name))
                        .collect();
                    self.emit(
                        Diag::error(format!(
                            "pattern does not mention field{} {}",
                            if missing.len() == 1 { "" } else { "s" },
                            missing.join(", ")
                        ))
                        .code("E0027")
                        .span(span, ""),
                    );
                }
                self.r.borrow_mut().pat_fields.insert(p, indices);
            }
            PatKind::Path(q) => {
                if self.path_is_const(q) {
                    match self.const_pat(q, span) {
                        Some((def, args, ty)) => {
                            self.r.borrow_mut().pat_consts.insert(p, (def, args));
                            self.demand_eq(span, expected, ty);
                        }
                        // A static (an error rustc reports too) or an unresolved path.
                        None => {
                            let ty = self.const_pat_ty(q, span);
                            self.demand_eq(span, expected, ty);
                        }
                    }
                    return;
                }
                let Some((adt_ty, variant, vidx)) = self.resolve_pat_path(q, span, false) else {
                    return;
                };
                self.demand_eq(span, expected, adt_ty);
                self.r
                    .borrow_mut()
                    .variants
                    .insert(p.0 | 0x8000_0000, (variant, vidx));
            }
            PatKind::Box(sub) => {
                let t = self.structurally_resolve(expected);
                let inner = match *t.kind() {
                    TyKind::Adt(d, args) if self.tcx.adt_def(d).is_box => args.ty(0),
                    _ => {
                        if !t.has_errors() {
                            self.err(
                                span,
                                format!(
                                    "mismatched types: expected `{}`, found `Box<_>`",
                                    self.resolve(t)
                                ),
                            );
                        }
                        Ty::ERROR
                    }
                };
                self.check_pat(*sub, inner, DefaultBm::Move);
            }
            PatKind::Deref(sub) => {
                let steps = self.autoderef_steps(expected, span);
                let inner = steps.get(1).map_or(Ty::ERROR, |s| s.0);
                self.check_pat(*sub, inner, def_bm);
            }
            PatKind::Ref(sub, m) => {
                let t = self.structurally_resolve(expected);
                let inner = match *t.kind() {
                    TyKind::Ref(inner, tm) if tm == *m => inner,
                    _ => {
                        let v = self.next_ty_var(span);
                        self.demand_eq(span, t, Ty::reference(v, *m));
                        v
                    }
                };
                self.check_pat(*sub, inner, DefaultBm::Move);
            }
            PatKind::Lit(e) => {
                let t = self.check_expr_with(*e, Expectation::HasType(expected));
                // `b"x"` against a slice: the literal is a slice there.
                let t = match (
                    *self.shallow(t).kind(),
                    *self.structurally_resolve(expected).kind(),
                ) {
                    (TyKind::Ref(arr, _), TyKind::Ref(slice, _))
                        if matches!(self.shallow(arr).kind(), TyKind::Array(..))
                            && matches!(self.shallow(slice).kind(), TyKind::Slice(_)) =>
                    {
                        expected
                    }
                    _ => t,
                };
                self.demand_eq(span, expected, t);
            }
            PatKind::Range { lo, hi, .. } => {
                for e in [lo, hi].into_iter().flatten() {
                    let t = self.check_expr_with(*e, Expectation::HasType(expected));
                    self.demand_eq(self.span(*e), expected, t);
                }
                let t = self.structurally_resolve(expected);
                if !(t.is_numeric() || t == Ty::CHAR || t.is_error() || t.is_ty_var()) {
                    self.emit(
                        Diag::error("only `char` and numeric types are allowed in range patterns")
                            .code("E0029")
                            .span(span, ""),
                    );
                }
            }
            PatKind::Slice {
                before,
                rest,
                after,
                ..
            } => {
                let t = self.structurally_resolve(expected);
                let (elem, len) = match *t.kind() {
                    TyKind::Array(e, n) => {
                        if rest.is_none() {
                            let expected_len =
                                Const::from_usize((before.len() + after.len()) as u64);
                            let _ = self.infcx.unify_const(n, expected_len);
                        }
                        (e, n.try_to_usize())
                    }
                    TyKind::Slice(e) => (e, None),
                    TyKind::Error => (Ty::ERROR, None),
                    _ => {
                        let v = self.next_ty_var(span);
                        if !self.demand_eq(span, t, Ty::slice(v)) {
                            (Ty::ERROR, None)
                        } else {
                            (v, None)
                        }
                    }
                };
                for &sp in before.iter().chain(after) {
                    self.check_pat(sp, elem, def_bm);
                }
                if let Some(r) = rest {
                    let rest_ty = match (*t.kind(), len) {
                        (TyKind::Array(..), Some(n)) => {
                            let m = n.saturating_sub((before.len() + after.len()) as u64);
                            Ty::array(elem, Const::from_usize(m))
                        }
                        _ => Ty::slice(elem),
                    };
                    self.check_pat(*r, rest_ty, def_bm);
                }
            }
            PatKind::Or(alts) => {
                for &a in alts {
                    self.check_pat(a, expected, def_bm);
                }
            }
        }
    }

    fn check_seq(
        &self,
        pats: &[PatId],
        rest: Option<usize>,
        fields: &[Ty],
        def_bm: DefaultBm,
        span: Span,
    ) {
        match rest {
            None => {
                if pats.len() != fields.len() {
                    self.emit(
                        Diag::error(format!("this pattern has {} field{}, but the corresponding type has {} field{}", pats.len(), if pats.len() == 1 { "" } else { "s" }, fields.len(), if fields.len() == 1 { "" } else { "s" }))
                            .code("E0023")
                            .span(span, ""),
                    );
                }
                for (i, &sp) in pats.iter().enumerate() {
                    self.check_pat(sp, fields.get(i).copied().unwrap_or(Ty::ERROR), def_bm);
                }
            }
            Some(pos) => {
                let tail = pats.len() - pos;
                for (i, &sp) in pats.iter().enumerate() {
                    let fi = if i < pos {
                        i
                    } else {
                        fields.len().saturating_sub(tail) + (i - pos)
                    };
                    self.check_pat(sp, fields.get(fi).copied().unwrap_or(Ty::ERROR), def_bm);
                }
            }
        }
    }

    /// The ADT and variant of a struct-like pattern path. `tuple`: a tuple-struct pattern.
    fn resolve_pat_path(
        &self,
        q: &hir::QPath,
        span: Span,
        tuple: bool,
    ) -> Option<(Ty, hyprc_hir::DefId, usize)> {
        // Constructors resolve through the value namespace in patterns.
        if let hir::QPath::Resolved(None, p) = q
            && let Res::Def(DefKind::Ctor(_, kind), _) = p.res
            && tuple != (kind == CtorKind::Fn)
            && kind == CtorKind::Const
            && tuple
        {
            self.err(
                span,
                "expected tuple struct or tuple variant, found unit struct or variant",
            );
            return None;
        }
        if let hir::QPath::TypeRelative(..) = q {
            // `Self::Variant(..)`, `Alias::Variant`.
            return self.resolve_struct_path(q, span);
        }
        self.resolve_struct_path(q, span)
    }

    fn const_pat_ty(&self, q: &hir::QPath, _span: Span) -> Ty {
        match q {
            hir::QPath::Resolved(_, p) => match p.res {
                Res::Def(DefKind::Const | DefKind::AssocConst | DefKind::Static { .. }, d) => {
                    self.normalize(self.tcx.type_of(d))
                }
                _ => Ty::ERROR,
            },
            _ => Ty::ERROR,
        }
    }
}
