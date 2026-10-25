//! Evaluating constant expressions that types depend on (array lengths, const generic
//! arguments, enum discriminants) where that's possible straight from the HIR: literals,
//! arithmetic, casts, other constants. Anything else stays unevaluated until monomorphized
//! code is const-evaluated by the MIR interpreter.

use crate::TyCtxt;
use crate::lower_ty::TyLowerer;
use crate::ty::*;
use hyprc_hir as hir;
use hyprc_hir::{BinOpKind, BodyId, DefKind, Res, UnOp};
use hyprc_syntax::token::LitKind;

const Q_CONST: u8 = 20;

/// Parses an integer literal's text (`0x_ff`, `1_000`, `0b1`) into its value.
pub fn parse_int_lit(text: &str) -> Option<u128> {
    let t = text.replace('_', "");
    let (digits, radix) = if let Some(r) = t.strip_prefix("0x") {
        (r.to_string(), 16)
    } else if let Some(r) = t.strip_prefix("0o") {
        (r.to_string(), 8)
    } else if let Some(r) = t.strip_prefix("0b") {
        (r.to_string(), 2)
    } else {
        (t, 10)
    };
    u128::from_str_radix(&digits, radix).ok()
}

/// The bits of a `char` literal's text (escapes processed).
pub fn parse_char_lit(text: &str) -> Option<u32> {
    let s = hyprc_resolve_unescape(text)?;
    let mut chars = s.chars();
    let c = chars.next()?;
    if chars.next().is_some() {
        return None;
    }
    Some(c as u32)
}

fn hyprc_resolve_unescape(text: &str) -> Option<String> {
    // The same escapes as strings.
    let mut out = String::new();
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '0' => out.push('\0'),
            '\'' => out.push('\''),
            '"' => out.push('"'),
            'x' => {
                let hex: String = [chars.next()?, chars.next()?].iter().collect();
                out.push(u8::from_str_radix(&hex, 16).ok()? as char);
            }
            'u' => {
                chars.next()?;
                let mut hex = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    if c != '_' {
                        hex.push(c);
                    }
                }
                out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            _ => return None,
        }
    }
    Some(out)
}

#[derive(Clone, Copy, Debug)]
enum Val {
    /// An integer, `bool` or `char` value, as bits of the given type.
    Bits(u128, Ty),
    /// A const parameter.
    Param(Const),
}

fn mask(v: u128, ty: Ty, pointer_width: u32) -> u128 {
    let bits = int_bits(ty, pointer_width);
    if bits >= 128 {
        v
    } else {
        v & ((1u128 << bits) - 1)
    }
}

pub fn int_bits(ty: Ty, pointer_width: u32) -> u32 {
    use hyprc_hir::{IntTy, UintTy};
    match *ty.kind() {
        TyKind::Bool => 1,
        TyKind::Char => 32,
        TyKind::Int(IntTy::I8) | TyKind::Uint(UintTy::U8) => 8,
        TyKind::Int(IntTy::I16) | TyKind::Uint(UintTy::U16) => 16,
        TyKind::Int(IntTy::I32) | TyKind::Uint(UintTy::U32) => 32,
        TyKind::Int(IntTy::I64) | TyKind::Uint(UintTy::U64) => 64,
        TyKind::Int(IntTy::I128) | TyKind::Uint(UintTy::U128) => 128,
        TyKind::Int(IntTy::Isize) | TyKind::Uint(UintTy::Usize) => pointer_width,
        _ => 128,
    }
}

/// Sign-extends `bits` of a signed type to 128 bits.
pub fn sext(v: u128, ty: Ty, pointer_width: u32) -> i128 {
    let bits = int_bits(ty, pointer_width);
    if bits >= 128 {
        return v as i128;
    }
    let shift = 128 - bits;
    ((v << shift) as i128) >> shift
}

impl TyCtxt<'_> {
    fn const_size_of(&self, ty: Ty) -> Option<u128> {
        let bytes = match *ty.kind() {
            TyKind::Bool | TyKind::Int(hir::IntTy::I8) | TyKind::Uint(hir::UintTy::U8) => 1,
            TyKind::Int(hir::IntTy::I16)
            | TyKind::Uint(hir::UintTy::U16)
            | TyKind::Float(hir::FloatTy::F16) => 2,
            TyKind::Char
            | TyKind::Int(hir::IntTy::I32)
            | TyKind::Uint(hir::UintTy::U32)
            | TyKind::Float(hir::FloatTy::F32) => 4,
            TyKind::Int(hir::IntTy::I64)
            | TyKind::Uint(hir::UintTy::U64)
            | TyKind::Float(hir::FloatTy::F64) => 8,
            TyKind::Int(hir::IntTy::I128)
            | TyKind::Uint(hir::UintTy::U128)
            | TyKind::Float(hir::FloatTy::F128) => 16,
            TyKind::Int(hir::IntTy::Isize)
            | TyKind::Uint(hir::UintTy::Usize)
            | TyKind::Ref(..)
            | TyKind::RawPtr(..)
            | TyKind::FnPtr(_) => (self.pointer_width / 8) as u128,
            TyKind::Never => 0,
            TyKind::Tuple(ts) if ts.as_slice().is_empty() => 0,
            TyKind::Array(elem, len) => {
                self.const_size_of(elem)?.checked_mul(len.try_to_bits()?)?
            }
            _ => return None,
        };
        Some(bytes)
    }

    /// Evaluates a body as a constant of type `ty`. Generic or too complex: unevaluated.
    pub fn eval_const_body(&self, body: BodyId, ty: Ty, args: Args) -> Const {
        let b = self.hir.body(body);
        let owner = b.owner;
        let r = self.guarded(
            Q_CONST,
            hyprc_hir::DefId(body.0 | 0x8000_0000),
            || None,
            || self.eval(b, b.value, ty, args, 0),
        );
        match r {
            Some(Val::Bits(v, _)) => {
                Const::new(ty, ConstKind::Value(mask(v, ty, self.pointer_width)))
            }
            Some(Val::Param(c)) => c,
            None => Const::new(
                ty,
                ConstKind::Unevaluated {
                    def: owner,
                    body: body.0,
                    args,
                },
            ),
        }
    }

    fn eval(
        &self,
        b: &hir::Body,
        e: hir::ExprId,
        expected: Ty,
        args: Args,
        depth: u32,
    ) -> Option<Val> {
        if depth > 64 {
            return None;
        }
        let pw = self.pointer_width;
        let expr = b.expr(e);
        match &expr.kind {
            hir::ExprKind::Lit(l) => {
                let ty = lit_ty(l, expected);
                let v = match l.kind {
                    LitKind::Integer => parse_int_lit(l.symbol.as_str())?,
                    LitKind::Bool => (l.symbol == hyprc_span::kw::True) as u128,
                    LitKind::Char => parse_char_lit(l.symbol.as_str())? as u128,
                    LitKind::Byte => parse_char_lit(l.symbol.as_str())? as u128,
                    _ => return None,
                };
                Some(Val::Bits(v, ty))
            }
            hir::ExprKind::Unary(op, inner) => {
                let Val::Bits(v, ty) = self.eval(b, *inner, expected, args, depth + 1)? else {
                    return None;
                };
                Some(Val::Bits(
                    match op {
                        UnOp::Neg => mask(v.wrapping_neg(), ty, pw),
                        UnOp::Not if ty == Ty::BOOL => (v == 0) as u128,
                        UnOp::Not => mask(!v, ty, pw),
                        UnOp::Deref => return None,
                    },
                    ty,
                ))
            }
            hir::ExprKind::Binary(op, l, r) => {
                let Val::Bits(a, ty) = self.eval(b, *l, expected, args, depth + 1)? else {
                    return None;
                };
                let rhs_expected = if matches!(op, BinOpKind::Shl | BinOpKind::Shr) {
                    Ty::U32
                } else {
                    ty
                };
                let Val::Bits(c, _) = self.eval(b, *r, rhs_expected, args, depth + 1)? else {
                    return None;
                };
                let signed = ty.is_signed();
                let (sa, sc) = (sext(a, ty, pw), sext(c, ty, pw));
                let v = match op {
                    BinOpKind::Add => a.wrapping_add(c),
                    BinOpKind::Sub => a.wrapping_sub(c),
                    BinOpKind::Mul => a.wrapping_mul(c),
                    BinOpKind::Div if c == 0 => return None,
                    BinOpKind::Div => {
                        if signed {
                            sa.wrapping_div(sc) as u128
                        } else {
                            a / c
                        }
                    }
                    BinOpKind::Rem if c == 0 => return None,
                    BinOpKind::Rem => {
                        if signed {
                            sa.wrapping_rem(sc) as u128
                        } else {
                            a % c
                        }
                    }
                    BinOpKind::BitAnd | BinOpKind::And => a & c,
                    BinOpKind::BitOr | BinOpKind::Or => a | c,
                    BinOpKind::BitXor => a ^ c,
                    BinOpKind::Shl => a.checked_shl(c as u32)?,
                    BinOpKind::Shr => {
                        if signed {
                            (sa >> (c as u32).min(127)) as u128
                        } else {
                            a.checked_shr(c as u32)?
                        }
                    }
                    BinOpKind::Eq => return Some(Val::Bits((a == c) as u128, Ty::BOOL)),
                    BinOpKind::Ne => return Some(Val::Bits((a != c) as u128, Ty::BOOL)),
                    BinOpKind::Lt => {
                        return Some(Val::Bits(
                            (if signed { sa < sc } else { a < c }) as u128,
                            Ty::BOOL,
                        ));
                    }
                    BinOpKind::Le => {
                        return Some(Val::Bits(
                            (if signed { sa <= sc } else { a <= c }) as u128,
                            Ty::BOOL,
                        ));
                    }
                    BinOpKind::Gt => {
                        return Some(Val::Bits(
                            (if signed { sa > sc } else { a > c }) as u128,
                            Ty::BOOL,
                        ));
                    }
                    BinOpKind::Ge => {
                        return Some(Val::Bits(
                            (if signed { sa >= sc } else { a >= c }) as u128,
                            Ty::BOOL,
                        ));
                    }
                };
                Some(Val::Bits(mask(v, ty, pw), ty))
            }
            hir::ExprKind::Cast(inner, t) => {
                let target = if matches!(t.kind, hir::TyKind::Infer) {
                    if expected.is_integral() || expected == Ty::BOOL || expected == Ty::CHAR {
                        expected
                    } else {
                        Ty::USIZE
                    }
                } else {
                    crate::lower_ty::TyLowerer::new(self, b.owner).lower(t)
                };
                let Val::Bits(v, from) = self.eval(b, *inner, target, args, depth + 1)? else {
                    return None;
                };
                if !(target.is_integral() || target == Ty::BOOL || target == Ty::CHAR) {
                    return None;
                }
                let v = if from.is_signed() {
                    sext(v, from, pw) as u128
                } else {
                    v
                };
                Some(Val::Bits(mask(v, target, pw), target))
            }
            hir::ExprKind::Block(blk, _) if blk.stmts.is_empty() => {
                let tail = blk.tail?;
                self.eval(b, tail, expected, args, depth + 1)
            }
            hir::ExprKind::ConstBlock(inner) => self.eval(b, *inner, expected, args, depth + 1),
            hir::ExprKind::Call(callee, call_args) if call_args.is_empty() => {
                let hir::ExprKind::Path(hir::QPath::Resolved(_, path)) = &b.expr(*callee).kind
                else {
                    return None;
                };
                let Res::Def(_, def) = path.res else {
                    return None;
                };
                if self.hir.name(def).as_str() != "size_of" {
                    return None;
                }
                let generic = path.segments.last()?.args.as_deref()?;
                let hir::GenericArg::Type(hir_ty) = generic.args.first()? else {
                    return None;
                };
                let ty = TyLowerer::new(self, b.owner).lower(hir_ty).subst(args);
                Some(Val::Bits(self.const_size_of(ty)?, Ty::USIZE))
            }
            hir::ExprKind::Path(hir::QPath::Resolved(None, path)) => match path.res {
                Res::ConstParam { index, owner } => {
                    let c = args.get(index as usize).and_then(|a| a.as_const());
                    match c {
                        Some(c) if c.try_to_bits().is_some() => {
                            Some(Val::Bits(c.try_to_bits().unwrap(), c.ty()))
                        }
                        Some(c) => Some(Val::Param(c)),
                        None => {
                            let ty = self.const_param_ty(owner, index);
                            let name = path
                                .segments
                                .last()
                                .map_or(hyprc_span::kw::Empty, |s| s.ident.name);
                            Some(Val::Param(Const::new(ty, ConstKind::Param(index, name))))
                        }
                    }
                }
                Res::Def(DefKind::Const | DefKind::AssocConst, d) => {
                    let item = self.hir.get_item(d)?;
                    let hir::ItemKind::Const { body: Some(cb), .. } = &item.kind else {
                        return None;
                    };
                    let ty = self.type_of(d);
                    match self.eval_const_body(*cb, ty, Args::EMPTY).kind() {
                        ConstKind::Value(v) => Some(Val::Bits(v, ty)),
                        _ => None,
                    }
                }
                _ => None,
            },
            hir::ExprKind::Path(hir::QPath::TypeRelative(base, seg)) => {
                let base_ty = crate::lower_ty::TyLowerer::new(self, b.owner).lower(base);
                let st = crate::collect::simplify(base_ty)?;
                for &imp in self.inherent_impls(st) {
                    if let Some(item) = self.assoc_item(imp, seg.ident.name, true) {
                        let item_hir = self.hir.get_item(item)?;
                        let hir::ItemKind::Const { body: Some(cb), .. } = &item_hir.kind else {
                            continue;
                        };
                        let ty = self.type_of(item);
                        match self.eval_const_body(*cb, ty, Args::EMPTY).kind() {
                            ConstKind::Value(v) => return Some(Val::Bits(v, ty)),
                            _ => {}
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }
}

/// The type of an integer literal in a constant: its suffix, or what's expected.
fn lit_ty(l: &hir::Lit, expected: Ty) -> Ty {
    if l.kind == LitKind::Bool {
        return Ty::BOOL;
    }
    if l.kind == LitKind::Char {
        return Ty::CHAR;
    }
    if l.kind == LitKind::Byte {
        return Ty::U8;
    }
    match l.suffix.as_str() {
        "" => {
            if expected.is_integral() {
                expected
            } else {
                Ty::I32
            }
        }
        s => match hyprc_hir::PrimTy::from_name(hyprc_span::Symbol::intern(s)) {
            Some(p) => crate::lower_ty::prim_ty(p),
            None => expected,
        },
    }
}
