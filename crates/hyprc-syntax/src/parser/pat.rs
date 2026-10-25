//! Patterns.

use super::{PResult, Parser, PathStyle};
use crate::ast::*;
use crate::token::{Delim, LitKind, TokenKind};
use hyprc_span::{Ident, Span, kw};

fn mk_pat(kind: PatKind, span: Span) -> P<Pat> {
    Box::new(Pat {
        id: NodeId::DUMMY,
        kind,
        span,
    })
}

fn mk_expr(kind: ExprKind, span: Span) -> P<Expr> {
    Box::new(Expr {
        id: NodeId::DUMMY,
        kind,
        span,
        attrs: Vec::new(),
    })
}

impl Parser<'_> {
    /// A pattern that may be an or-pattern, with an optional leading `|`: `match` arms,
    /// `let`, `if let`, `for`.
    pub fn parse_pat_allow_top_alt(&mut self) -> PResult<P<Pat>> {
        let lo = self.token.span;
        // A leading `|` (also the first half of `||`, which can't start a pattern otherwise).
        if !self.eat(TokenKind::Or) && self.check(TokenKind::OrOr) {
            self.break_and_eat(TokenKind::Or);
        }
        let first = self.parse_pat_no_top_alt()?;
        if !self.check(TokenKind::Or) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(TokenKind::Or) {
            alts.push(self.parse_pat_no_top_alt()?);
        }
        Ok(mk_pat(PatKind::Or(alts), lo.to(self.prev_token.span)))
    }

    /// A pattern that isn't an or-pattern at the top: function and closure parameters.
    pub fn parse_pat_no_top_alt(&mut self) -> PResult<P<Pat>> {
        self.parse_pat_with_range(true)
    }

    fn parse_pat_with_range(&mut self, allow_range: bool) -> PResult<P<Pat>> {
        self.enter()?;
        let r = self.parse_pat_with_range_inner(allow_range);
        self.depth -= 1;
        r
    }

    fn parse_pat_with_range_inner(&mut self, allow_range: bool) -> PResult<P<Pat>> {
        let lo = self.token.span;
        let t = self.token;
        let kind = match t.kind {
            TokenKind::Ident if t.sym == kw::Underscore => {
                self.bump();
                PatKind::Wild
            }
            TokenKind::And | TokenKind::AndAnd => {
                self.break_and_eat(TokenKind::And);
                let mutbl = if self.eat_keyword(kw::Mut) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                };
                let sub = self.parse_pat_with_range(false)?;
                PatKind::Ref(sub, mutbl)
            }
            TokenKind::Open(Delim::Paren) => {
                let (pats, trailing) = self.parse_pat_list(Delim::Paren)?;
                if pats.len() == 1 && !trailing && !matches!(pats[0].kind, PatKind::Rest) {
                    PatKind::Paren(pats.into_iter().next().unwrap())
                } else {
                    PatKind::Tuple(pats)
                }
            }
            TokenKind::Open(Delim::Bracket) => {
                PatKind::Slice(self.parse_pat_list(Delim::Bracket)?.0)
            }
            TokenKind::Open(Delim::Invisible) => {
                self.bump();
                let p = self.parse_pat_allow_top_alt()?;
                self.expect(TokenKind::Close(Delim::Invisible))?;
                return self.maybe_range_pat(p, lo, allow_range);
            }
            TokenKind::DotDot | TokenKind::DotDotEq | TokenKind::DotDotDot => {
                // `..` alone, or a range without a start: `..=5`, `..5`.
                let end = if self.check(TokenKind::DotDot) {
                    RangeEnd::Excluded
                } else {
                    RangeEnd::Included(RangeSyntax::DotDotEq)
                };
                self.bump();
                if self.can_begin_range_pat_end() {
                    let hi = self.parse_range_pat_end()?;
                    PatKind::Range(None, Some(hi), end)
                } else {
                    PatKind::Rest
                }
            }
            TokenKind::Not => {
                self.bump();
                PatKind::Never
            }
            TokenKind::Ident if t.sym == kw::Mut => {
                self.bump();
                // `mut ref x` is an error in rustc; accept `mut x`.
                let ident = self.parse_ident()?;
                let sub = if self.eat(TokenKind::At) {
                    Some(self.parse_pat_no_top_alt()?)
                } else {
                    None
                };
                PatKind::Ident(
                    BindingMode {
                        by_ref: ByRef::No,
                        mutbl: Mutability::Mut,
                    },
                    ident,
                    sub,
                )
            }
            TokenKind::Ident if t.sym == kw::Ref => {
                self.bump();
                let mutbl = if self.eat_keyword(kw::Mut) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                };
                let ident = self.parse_ident()?;
                let sub = if self.eat(TokenKind::At) {
                    Some(self.parse_pat_no_top_alt()?)
                } else {
                    None
                };
                PatKind::Ident(
                    BindingMode {
                        by_ref: ByRef::Yes(mutbl),
                        mutbl: Mutability::Not,
                    },
                    ident,
                    sub,
                )
            }
            TokenKind::Ident if t.sym == kw::Box && self.box_pat_follows() => {
                self.bump();
                PatKind::Box(self.parse_pat_with_range(false)?)
            }
            TokenKind::Ident if t.sym == kw::Builtin && self.look_kind(1) == TokenKind::Pound => {
                // `builtin # deref(p)`
                self.bump();
                self.bump();
                let name = self.parse_ident_any()?;
                self.expect(TokenKind::Open(Delim::Paren))?;
                let p = self.parse_pat_allow_top_alt()?;
                self.expect(TokenKind::Close(Delim::Paren))?;
                if name.as_str() == "deref" {
                    PatKind::Deref(p)
                } else {
                    PatKind::Err
                }
            }
            TokenKind::Ident
                if t.sym == kw::Const && self.look_kind(1) == TokenKind::Open(Delim::Brace) =>
            {
                let e = self.parse_pat_lit_expr()?;
                return self.maybe_range_pat_expr(e, lo, allow_range);
            }
            TokenKind::Literal(_) | TokenKind::Minus => {
                let e = self.parse_pat_lit_expr()?;
                return self.maybe_range_pat_expr(e, lo, allow_range);
            }
            TokenKind::Ident if t.sym == kw::True || t.sym == kw::False => {
                let e = self.parse_pat_lit_expr()?;
                return self.maybe_range_pat_expr(e, lo, allow_range);
            }
            TokenKind::Lt | TokenKind::Shl => {
                let (qself, path) = self.parse_qpath(PathStyle::Expr)?;
                return self.parse_pat_after_path(Some(qself), path, lo, allow_range);
            }
            _ if self.check_path_start() => {
                // A lone identifier is a binding, unless a path or a pattern on a path follows.
                if self.check_ident()
                    && !matches!(
                        self.look_kind(1),
                        TokenKind::PathSep
                            | TokenKind::Open(Delim::Paren)
                            | TokenKind::Open(Delim::Brace)
                            | TokenKind::Not
                            | TokenKind::DotDot
                            | TokenKind::DotDotEq
                            | TokenKind::DotDotDot
                    )
                {
                    let ident = self.parse_ident()?;
                    let sub = if self.eat(TokenKind::At) {
                        Some(self.parse_pat_no_top_alt()?)
                    } else {
                        None
                    };
                    PatKind::Ident(BindingMode::NONE, ident, sub)
                } else {
                    let path = self.parse_path(PathStyle::Expr)?;
                    return self.parse_pat_after_path(None, path, lo, allow_range);
                }
            }
            _ => return Err(self.expected("pattern")),
        };
        Ok(mk_pat(kind, lo.to(self.prev_token.span)))
    }

    /// `box p` (not `box::x`, a path, or `box` as an identifier).
    fn box_pat_follows(&self) -> bool {
        let n = self.look(1);
        !matches!(
            n.kind,
            TokenKind::PathSep
                | TokenKind::Comma
                | TokenKind::Close(_)
                | TokenKind::Colon
                | TokenKind::Eq
                | TokenKind::At
                | TokenKind::Or
                | TokenKind::FatArrow
        ) && !n.is_keyword(kw::If)
            && !n.is_keyword(kw::In)
    }

    fn parse_pat_after_path(
        &mut self,
        qself: Option<P<QSelf>>,
        path: Path,
        lo: Span,
        allow_range: bool,
    ) -> PResult<P<Pat>> {
        let kind = match self.token.kind {
            TokenKind::Not
                if qself.is_none() && matches!(self.look_kind(1), TokenKind::Open(_)) =>
            {
                self.bump();
                let args = self.parse_delim_args()?;
                PatKind::MacCall(Box::new(MacCall { path, args }))
            }
            TokenKind::Open(Delim::Paren) => {
                let (pats, _) = self.parse_pat_list(Delim::Paren)?;
                PatKind::TupleStruct(qself, path, pats)
            }
            TokenKind::Open(Delim::Brace) => {
                let (fields, rest) = self.parse_pat_fields()?;
                PatKind::Struct(qself, path, fields, rest)
            }
            _ => {
                let span = lo.to(self.prev_token.span);
                let e = mk_expr(ExprKind::Path(qself, path), span);
                if allow_range && self.check_range_op() {
                    return self.parse_range_pat_rest(Some(e), lo);
                }
                let ExprKind::Path(qself, path) = e.kind else {
                    unreachable!()
                };
                PatKind::Path(qself, path)
            }
        };
        Ok(mk_pat(kind, lo.to(self.prev_token.span)))
    }

    fn check_range_op(&self) -> bool {
        matches!(
            self.token.kind,
            TokenKind::DotDot | TokenKind::DotDotEq | TokenKind::DotDotDot
        )
    }

    fn maybe_range_pat(&mut self, p: P<Pat>, lo: Span, allow_range: bool) -> PResult<P<Pat>> {
        if allow_range && self.check_range_op() {
            let e = match p.kind {
                PatKind::Expr(e) => e,
                PatKind::Path(qself, path) => mk_expr(ExprKind::Path(qself, path), p.span),
                kind => return Ok(mk_pat(kind, p.span)),
            };
            return self.parse_range_pat_rest(Some(e), lo);
        }
        Ok(p)
    }

    fn maybe_range_pat_expr(&mut self, e: P<Expr>, lo: Span, allow_range: bool) -> PResult<P<Pat>> {
        if allow_range && self.check_range_op() {
            return self.parse_range_pat_rest(Some(e), lo);
        }
        let span = e.span;
        Ok(mk_pat(PatKind::Expr(e), span))
    }

    /// After the start of a range pattern: `..=hi`, `...hi`, `..hi`, or `..`.
    fn parse_range_pat_rest(&mut self, start: Option<P<Expr>>, lo: Span) -> PResult<P<Pat>> {
        let end_kind = match self.token.kind {
            TokenKind::DotDot => RangeEnd::Excluded,
            TokenKind::DotDotEq => RangeEnd::Included(RangeSyntax::DotDotEq),
            _ => RangeEnd::Included(RangeSyntax::DotDotDot),
        };
        self.bump();
        let end = if self.can_begin_range_pat_end() {
            Some(self.parse_range_pat_end()?)
        } else {
            None
        };
        Ok(mk_pat(
            PatKind::Range(start, end, end_kind),
            lo.to(self.prev_token.span),
        ))
    }

    fn can_begin_range_pat_end(&self) -> bool {
        match self.token.kind {
            TokenKind::Literal(_)
            | TokenKind::Minus
            | TokenKind::Lt
            | TokenKind::Shl
            | TokenKind::PathSep => true,
            TokenKind::Open(Delim::Invisible) => true,
            TokenKind::Ident => {
                (self.check_path_start() && !self.token.is_keyword(kw::Underscore))
                    || self.token.is_keyword(kw::True)
                    || self.token.is_keyword(kw::False)
                    || (self.token.is_keyword(kw::Const)
                        && self.look_kind(1) == TokenKind::Open(Delim::Brace))
            }
            TokenKind::RawIdent => true,
            _ => false,
        }
    }

    fn parse_range_pat_end(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        match self.token.kind {
            TokenKind::Lt | TokenKind::Shl => {
                let (qself, path) = self.parse_qpath(PathStyle::Expr)?;
                Ok(mk_expr(
                    ExprKind::Path(Some(qself), path),
                    lo.to(self.prev_token.span),
                ))
            }
            TokenKind::Open(Delim::Invisible) => {
                self.bump();
                let e = self.parse_expr()?;
                self.expect(TokenKind::Close(Delim::Invisible))?;
                Ok(e)
            }
            TokenKind::Ident
                if !(self.token.is_keyword(kw::True)
                    || self.token.is_keyword(kw::False)
                    || self.token.is_keyword(kw::Const)) =>
            {
                let path = self.parse_path(PathStyle::Expr)?;
                Ok(mk_expr(
                    ExprKind::Path(None, path),
                    lo.to(self.prev_token.span),
                ))
            }
            TokenKind::RawIdent | TokenKind::PathSep => {
                let path = self.parse_path(PathStyle::Expr)?;
                Ok(mk_expr(
                    ExprKind::Path(None, path),
                    lo.to(self.prev_token.span),
                ))
            }
            _ => self.parse_pat_lit_expr(),
        }
    }

    /// A literal, `-literal`, or `const { … }` in a pattern.
    fn parse_pat_lit_expr(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        if self.check_keyword(kw::Const) {
            self.bump();
            let block = self.parse_block()?;
            let value = mk_expr(ExprKind::Block(block, None), lo.to(self.prev_token.span));
            return Ok(mk_expr(
                ExprKind::ConstBlock(AnonConst {
                    id: NodeId::DUMMY,
                    value,
                }),
                lo.to(self.prev_token.span),
            ));
        }
        if self.eat(TokenKind::Minus) {
            let lit = self.parse_lit()?;
            let inner = mk_expr(ExprKind::Lit(lit), lit.span);
            return Ok(mk_expr(
                ExprKind::Unary(UnOp::Neg, inner),
                lo.to(self.prev_token.span),
            ));
        }
        let lit = self.parse_lit()?;
        Ok(mk_expr(ExprKind::Lit(lit), lit.span))
    }

    /// `(p, q, ..)` or `[p, q, ..]`; also reports whether there was a trailing comma.
    fn parse_pat_list(&mut self, delim: Delim) -> PResult<(Vec<P<Pat>>, bool)> {
        self.expect(TokenKind::Open(delim))?;
        let mut pats = Vec::new();
        let mut trailing = false;
        while !self.check(TokenKind::Close(delim)) {
            pats.push(self.parse_pat_allow_top_alt()?);
            trailing = false;
            if !self.eat(TokenKind::Comma) {
                break;
            }
            trailing = true;
        }
        self.expect(TokenKind::Close(delim))?;
        Ok((pats, trailing))
    }

    fn parse_pat_fields(&mut self) -> PResult<(Vec<PatField>, PatFieldsRest)> {
        self.expect(TokenKind::Open(Delim::Brace))?;
        let mut fields = Vec::new();
        let mut rest = PatFieldsRest::None;
        while !self.check(TokenKind::Close(Delim::Brace)) {
            let attrs = self.parse_outer_attributes()?;
            if self.check(TokenKind::DotDot) {
                self.bump();
                rest = PatFieldsRest::Rest;
                // A trailing comma after `..` is allowed.
                self.eat(TokenKind::Comma);
                break;
            }
            let lo = self.token.span;
            let field = if (self.token.is_ident()
                || matches!(self.token.kind, TokenKind::Literal(LitKind::Integer)))
                && self.look_kind(1) == TokenKind::Colon
            {
                let ident = Ident::new(self.token.sym, self.token.span);
                self.bump();
                self.bump();
                let pat = self.parse_pat_allow_top_alt()?;
                PatField {
                    ident,
                    pat,
                    is_shorthand: false,
                    attrs,
                    id: NodeId::DUMMY,
                    span: lo.to(self.prev_token.span),
                }
            } else {
                // Shorthand: `x`, `ref x`, `mut x`, `ref mut x`, `box x`.
                let boxed = if self.check_keyword(kw::Box) && self.look(1).is_ident() {
                    self.bump();
                    true
                } else {
                    false
                };
                let by_ref = if self.eat_keyword(kw::Ref) {
                    ByRef::Yes(if self.eat_keyword(kw::Mut) {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    })
                } else {
                    ByRef::No
                };
                let mutbl = if self.eat_keyword(kw::Mut) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                };
                let ident = self.parse_ident()?;
                let span = lo.to(self.prev_token.span);
                let mut pat = mk_pat(
                    PatKind::Ident(BindingMode { by_ref, mutbl }, ident, None),
                    span,
                );
                if boxed {
                    pat = mk_pat(PatKind::Box(pat), span);
                }
                PatField {
                    ident,
                    pat,
                    is_shorthand: true,
                    attrs,
                    id: NodeId::DUMMY,
                    span,
                }
            };
            fields.push(field);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok((fields, rest))
    }
}
