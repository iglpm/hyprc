//! Expressions, statements and blocks.

use super::item::ItemCtx;
use super::{PResult, Parser, PathStyle, Restrictions};
use crate::ast::*;
use crate::token::{Delim, LitKind, TokenKind};
use hyprc_span::{Ident, Span, Symbol, kw};

/// Binding strength, weakest first.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Prec {
    Assign = 1,
    Range = 2,
    Or = 3,
    And = 4,
    Compare = 5,
    BitOr = 6,
    BitXor = 7,
    BitAnd = 8,
    Shift = 9,
    Sum = 10,
    Product = 11,
    Cast = 12,
}

#[derive(Clone, Copy, Debug)]
enum AssocOp {
    Binary(BinOpKind),
    Assign,
    AssignOp(BinOpKind),
    Range(RangeLimits),
    Cast,
}

impl AssocOp {
    fn prec(self) -> Prec {
        use BinOpKind::*;
        match self {
            AssocOp::Assign | AssocOp::AssignOp(_) => Prec::Assign,
            AssocOp::Range(_) => Prec::Range,
            AssocOp::Cast => Prec::Cast,
            AssocOp::Binary(op) => match op {
                Or => Prec::Or,
                And => Prec::And,
                Eq | Lt | Le | Ne | Ge | Gt => Prec::Compare,
                BitOr => Prec::BitOr,
                BitXor => Prec::BitXor,
                BitAnd => Prec::BitAnd,
                Shl | Shr => Prec::Shift,
                Add | Sub => Prec::Sum,
                Mul | Div | Rem => Prec::Product,
            },
        }
    }
}

fn mk(kind: ExprKind, span: Span) -> P<Expr> {
    Box::new(Expr {
        id: NodeId::DUMMY,
        kind,
        span,
        attrs: Vec::new(),
    })
}

/// Expressions that end a statement without a `;`: `if`, `match`, blocks, loops.
pub fn expr_is_block_like(e: &Expr) -> bool {
    matches!(
        e.kind,
        ExprKind::If(..)
            | ExprKind::Match(_, _, MatchKind::Prefix)
            | ExprKind::Block(..)
            | ExprKind::While(..)
            | ExprKind::Loop(..)
            | ExprKind::ForLoop { .. }
            | ExprKind::TryBlock(..)
            | ExprKind::ConstBlock(..)
            | ExprKind::Gen(..)
    ) || matches!(&e.kind, ExprKind::MacCall(m) if m.args.delim == Delim::Brace)
}

impl Parser<'_> {
    pub fn parse_expr(&mut self) -> PResult<P<Expr>> {
        self.with_res(Restrictions::default(), |p| p.parse_expr_assoc(None))
    }

    pub(crate) fn parse_expr_res(&mut self, r: Restrictions) -> PResult<P<Expr>> {
        self.with_res(r, |p| p.parse_expr_assoc(None))
    }

    /// Statement-like expressions end at their block in statement position.
    fn expr_is_complete(&self, e: &Expr) -> bool {
        self.restrictions.contains(Restrictions::STMT_EXPR) && expr_is_block_like(e)
    }

    fn check_assoc_op(&self) -> Option<AssocOp> {
        use BinOpKind::*;
        let t = self.token;
        Some(match t.kind {
            TokenKind::Plus => AssocOp::Binary(Add),
            TokenKind::Minus => AssocOp::Binary(Sub),
            TokenKind::Star => AssocOp::Binary(Mul),
            TokenKind::Slash => AssocOp::Binary(Div),
            TokenKind::Percent => AssocOp::Binary(Rem),
            TokenKind::Caret => AssocOp::Binary(BitXor),
            TokenKind::And => AssocOp::Binary(BitAnd),
            TokenKind::Or => AssocOp::Binary(BitOr),
            TokenKind::Shl => AssocOp::Binary(Shl),
            TokenKind::Shr => AssocOp::Binary(Shr),
            TokenKind::EqEq => AssocOp::Binary(Eq),
            TokenKind::Ne => AssocOp::Binary(Ne),
            TokenKind::Lt | TokenKind::LArrow => AssocOp::Binary(Lt),
            TokenKind::Le => AssocOp::Binary(Le),
            TokenKind::Gt => AssocOp::Binary(Gt),
            TokenKind::Ge => AssocOp::Binary(Ge),
            TokenKind::AndAnd => AssocOp::Binary(And),
            TokenKind::OrOr => AssocOp::Binary(Or),
            TokenKind::Eq => AssocOp::Assign,
            TokenKind::PlusEq => AssocOp::AssignOp(Add),
            TokenKind::MinusEq => AssocOp::AssignOp(Sub),
            TokenKind::StarEq => AssocOp::AssignOp(Mul),
            TokenKind::SlashEq => AssocOp::AssignOp(Div),
            TokenKind::PercentEq => AssocOp::AssignOp(Rem),
            TokenKind::CaretEq => AssocOp::AssignOp(BitXor),
            TokenKind::AndEq => AssocOp::AssignOp(BitAnd),
            TokenKind::OrEq => AssocOp::AssignOp(BitOr),
            TokenKind::ShlEq => AssocOp::AssignOp(Shl),
            TokenKind::ShrEq => AssocOp::AssignOp(Shr),
            TokenKind::DotDot => AssocOp::Range(RangeLimits::HalfOpen),
            TokenKind::DotDotEq | TokenKind::DotDotDot => AssocOp::Range(RangeLimits::Closed),
            TokenKind::Ident if t.sym == kw::As => AssocOp::Cast,
            _ => return None,
        })
    }

    /// Binary operators with precedence at least `min` (`None`: all of them).
    fn parse_expr_assoc(&mut self, min: Option<Prec>) -> PResult<P<Expr>> {
        self.enter()?;
        let r = self.parse_expr_assoc_inner(min);
        self.depth -= 1;
        r
    }

    fn parse_expr_assoc_inner(&mut self, min: Option<Prec>) -> PResult<P<Expr>> {
        let attrs = self.parse_outer_attributes()?;
        let lo = attrs.first().map_or(self.token.span, |a| a.span);
        let mut lhs = if matches!(
            self.token.kind,
            TokenKind::DotDot | TokenKind::DotDotEq | TokenKind::DotDotDot
        ) {
            self.parse_expr_prefix_range()?
        } else {
            self.parse_expr_prefix()?
        };
        if !attrs.is_empty() {
            let mut all = attrs;
            all.append(&mut lhs.attrs);
            lhs.attrs = all;
            lhs.span = lo.to(lhs.span);
        }
        self.parse_expr_assoc_rest(min, lhs)
    }

    fn parse_expr_assoc_rest(&mut self, min: Option<Prec>, mut lhs: P<Expr>) -> PResult<P<Expr>> {
        loop {
            if self.expr_is_complete(&lhs) {
                return Ok(lhs);
            }
            let Some(op) = self.check_assoc_op() else {
                return Ok(lhs);
            };
            let prec = op.prec();
            if min.is_some_and(|m| prec < m) {
                return Ok(lhs);
            }
            let op_span = self.token.span;
            // `a <- b` is `a < -b`.
            if self.token.kind == TokenKind::LArrow {
                self.break_and_eat(TokenKind::Lt);
            } else {
                self.bump();
            }
            let lo = lhs.span;
            // Statement restrictions don't apply to the right-hand side.
            let rhs_res = self.restrictions.without(Restrictions::STMT_EXPR);
            lhs = match op {
                AssocOp::Cast => {
                    let ty = self.parse_ty_no_plus()?;
                    mk(ExprKind::Cast(lhs, ty), lo.to(self.prev_token.span))
                }
                AssocOp::Range(limits) => {
                    let rhs = if self.can_begin_range_end() {
                        Some(self.with_res(rhs_res, |p| p.parse_expr_assoc(Some(Prec::Or)))?)
                    } else {
                        None
                    };
                    let span = lo.to(self.prev_token.span);
                    mk(ExprKind::Range(Some(lhs), rhs, limits), span)
                }
                AssocOp::Assign => {
                    let rhs = self.with_res(rhs_res, |p| p.parse_expr_assoc(Some(Prec::Assign)))?;
                    let span = lo.to(rhs.span);
                    mk(ExprKind::Assign(lhs, rhs, op_span), span)
                }
                AssocOp::AssignOp(kind) => {
                    let rhs = self.with_res(rhs_res, |p| p.parse_expr_assoc(Some(Prec::Assign)))?;
                    let span = lo.to(rhs.span);
                    mk(
                        ExprKind::AssignOp(
                            BinOp {
                                kind,
                                span: op_span,
                            },
                            lhs,
                            rhs,
                        ),
                        span,
                    )
                }
                AssocOp::Binary(kind) => {
                    // Left-associative: the right operand binds tighter.
                    let next = next_prec(prec);
                    let rhs = self.with_res(rhs_res, |p| p.parse_expr_assoc(Some(next)))?;
                    let span = lo.to(rhs.span);
                    mk(
                        ExprKind::Binary(
                            BinOp {
                                kind,
                                span: op_span,
                            },
                            lhs,
                            rhs,
                        ),
                        span,
                    )
                }
            };
        }
    }

    /// After `..`: does an end follow? Not before `{` in a condition (`for i in 0.. {`).
    fn can_begin_range_end(&self) -> bool {
        if self.check(TokenKind::Open(Delim::Brace))
            && self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL)
        {
            return false;
        }
        self.can_begin_expr()
    }

    fn parse_expr_prefix_range(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        let limits = if self.check(TokenKind::DotDot) {
            RangeLimits::HalfOpen
        } else {
            RangeLimits::Closed
        };
        self.bump();
        let end = if self.can_begin_range_end() {
            let r = self.restrictions.without(Restrictions::STMT_EXPR);
            Some(self.with_res(r, |p| p.parse_expr_assoc(Some(Prec::Or)))?)
        } else {
            None
        };
        Ok(mk(
            ExprKind::Range(None, end, limits),
            lo.to(self.prev_token.span),
        ))
    }

    pub(crate) fn can_begin_expr(&self) -> bool {
        let t = self.token;
        match t.kind {
            TokenKind::Literal(_)
            | TokenKind::Open(_)
            | TokenKind::Not
            | TokenKind::Minus
            | TokenKind::Star
            | TokenKind::And
            | TokenKind::AndAnd
            | TokenKind::Or
            | TokenKind::OrOr
            | TokenKind::DotDot
            | TokenKind::DotDotEq
            | TokenKind::DotDotDot
            | TokenKind::Lt
            | TokenKind::Shl
            | TokenKind::PathSep
            | TokenKind::Pound
            | TokenKind::Lifetime
            | TokenKind::RawLifetime
            | TokenKind::RawIdent => true,
            TokenKind::Ident => {
                !t.sym.is_reserved(self.edition2018())
                    || matches!(
                        t.sym,
                        kw::Underscore
                            | kw::SelfLower
                            | kw::SelfUpper
                            | kw::Super
                            | kw::Crate
                            | kw::DollarCrate
                            | kw::True
                            | kw::False
                            | kw::If
                            | kw::Match
                            | kw::Loop
                            | kw::While
                            | kw::For
                            | kw::Unsafe
                            | kw::Async
                            | kw::Move
                            | kw::Return
                            | kw::Break
                            | kw::Continue
                            | kw::Yield
                            | kw::Let
                            | kw::Const
                            | kw::Static
                            | kw::Do
                            | kw::Become
                            | kw::Try
                            | kw::Box
                            | kw::Gen
                            | kw::Use
                    )
            }
            _ => false,
        }
    }

    /// Unary operators, then postfix (`.f`, `()`, `[]`, `?`).
    fn parse_expr_prefix(&mut self) -> PResult<P<Expr>> {
        self.enter()?;
        let r = self.parse_expr_prefix_inner();
        self.depth -= 1;
        r
    }

    fn parse_expr_prefix_inner(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        let unary = |p: &mut Self, op: UnOp| -> PResult<P<Expr>> {
            p.bump();
            let e = p.parse_expr_prefix()?;
            Ok(mk(ExprKind::Unary(op, e), lo.to(p.prev_token.span)))
        };
        match self.token.kind {
            TokenKind::Not => unary(self, UnOp::Not),
            TokenKind::Minus => unary(self, UnOp::Neg),
            TokenKind::Star => unary(self, UnOp::Deref),
            TokenKind::And | TokenKind::AndAnd => {
                self.break_and_eat(TokenKind::And);
                let (kind, mutbl) = self.parse_borrow_modifiers();
                let e = self.parse_expr_prefix()?;
                Ok(mk(
                    ExprKind::AddrOf(kind, mutbl, e),
                    lo.to(self.prev_token.span),
                ))
            }
            // `&..`, `!..x`: a range as an operand.
            TokenKind::DotDot | TokenKind::DotDotEq | TokenKind::DotDotDot => {
                self.parse_expr_prefix_range()
            }
            _ => self.parse_expr_dot_or_call(),
        }
    }

    /// After `&`: `mut`, `raw const`, `raw mut`, `pin mut`, `pin const`.
    fn parse_borrow_modifiers(&mut self) -> (BorrowKind, Mutability) {
        let t = self.token;
        if t.kind == TokenKind::Ident && (t.sym == kw::Raw || t.sym.as_str() == "pin") {
            let next = self.look(1);
            if next.is_keyword(kw::Const) || next.is_keyword(kw::Mut) {
                let kind = if t.sym == kw::Raw {
                    BorrowKind::Raw
                } else {
                    BorrowKind::Pin
                };
                self.bump();
                let mutbl = if self.eat_keyword(kw::Mut) {
                    Mutability::Mut
                } else {
                    self.bump();
                    Mutability::Not
                };
                return (kind, mutbl);
            }
        }
        let mutbl = if self.eat_keyword(kw::Mut) {
            Mutability::Mut
        } else {
            Mutability::Not
        };
        (BorrowKind::Ref, mutbl)
    }

    fn parse_expr_dot_or_call(&mut self) -> PResult<P<Expr>> {
        let e = self.parse_expr_bottom()?;
        self.parse_expr_dot_or_call_with(e)
    }

    fn parse_expr_dot_or_call_with(&mut self, mut e: P<Expr>) -> PResult<P<Expr>> {
        loop {
            let lo = e.span;
            if self.eat(TokenKind::Question) {
                e = mk(ExprKind::Try(e), lo.to(self.prev_token.span));
                continue;
            }
            if self.eat(TokenKind::Dot) {
                e = self.parse_dot_suffix(e)?;
                continue;
            }
            if self.expr_is_complete(&e) {
                return Ok(e);
            }
            match self.token.kind {
                TokenKind::Open(Delim::Paren) => {
                    let args = self.parse_call_args()?;
                    e = mk(ExprKind::Call(e, args), lo.to(self.prev_token.span));
                }
                TokenKind::Open(Delim::Bracket) => {
                    self.bump();
                    let idx = self.parse_expr()?;
                    self.expect(TokenKind::Close(Delim::Bracket))?;
                    let span = lo.to(self.prev_token.span);
                    e = mk(ExprKind::Index(e, idx, span), span);
                }
                _ => return Ok(e),
            }
        }
    }

    fn parse_call_args(&mut self) -> PResult<Vec<P<Expr>>> {
        self.expect(TokenKind::Open(Delim::Paren))?;
        let mut args = Vec::new();
        while !self.check(TokenKind::Close(Delim::Paren)) {
            args.push(self.parse_expr()?);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Paren))?;
        Ok(args)
    }

    /// After `e.`: a field, a tuple index, a method call, `.await`, `.use`, `.match`.
    fn parse_dot_suffix(&mut self, e: P<Expr>) -> PResult<P<Expr>> {
        let lo = e.span;
        let t = self.token;
        match t.kind {
            TokenKind::Ident if t.sym == kw::Await && self.edition2018() => {
                self.bump();
                let span = lo.to(self.prev_token.span);
                Ok(mk(ExprKind::Await(e, self.prev_token.span), span))
            }
            TokenKind::Ident
                if t.sym == kw::Use && self.look_kind(1) != TokenKind::Open(Delim::Paren) =>
            {
                self.bump();
                Ok(mk(
                    ExprKind::Use(e, self.prev_token.span),
                    lo.to(self.prev_token.span),
                ))
            }
            TokenKind::Ident
                if t.sym == kw::Match && self.look_kind(1) == TokenKind::Open(Delim::Brace) =>
            {
                self.bump();
                let arms = self.parse_match_arms()?;
                Ok(mk(
                    ExprKind::Match(e, arms, MatchKind::Postfix),
                    lo.to(self.prev_token.span),
                ))
            }
            TokenKind::Literal(LitKind::Integer) if t.suffix == kw::Empty => {
                self.bump();
                Ok(mk(
                    ExprKind::Field(e, Ident::new(t.sym, t.span)),
                    lo.to(t.span),
                ))
            }
            TokenKind::Literal(LitKind::Float) if t.suffix == kw::Empty => {
                // `x.0.1` lexes as `x`, `.`, `0.1`: two field accesses.
                self.bump();
                let text = t.sym.as_str();
                let mut e = e;
                let mut off = t.span.lo;
                for part in text.split('.') {
                    if part.is_empty() {
                        continue;
                    }
                    let span = Span::new(off, off + part.len() as u32);
                    off += part.len() as u32 + 1;
                    e = mk(
                        ExprKind::Field(e, Ident::new(Symbol::intern(part), span)),
                        lo.to(span),
                    );
                }
                Ok(e)
            }
            TokenKind::Ident | TokenKind::RawIdent => {
                let seg_ident = Ident::new(t.sym, t.span);
                self.bump();
                let args = if self.check(TokenKind::PathSep)
                    && matches!(
                        self.look_kind(1),
                        TokenKind::Lt | TokenKind::Shl | TokenKind::LArrow
                    ) {
                    self.bump();
                    Some(Box::new(self.parse_angle_args()?))
                } else {
                    None
                };
                if self.check(TokenKind::Open(Delim::Paren)) {
                    let args_list = self.parse_call_args()?;
                    let span = lo.to(self.prev_token.span);
                    let seg = PathSegment {
                        ident: seg_ident,
                        id: NodeId::DUMMY,
                        args,
                    };
                    return Ok(mk(
                        ExprKind::MethodCall(Box::new(MethodCall {
                            seg,
                            receiver: e,
                            args: args_list,
                            span,
                        })),
                        span,
                    ));
                }
                Ok(mk(
                    ExprKind::Field(e, seg_ident),
                    lo.to(self.prev_token.span),
                ))
            }
            _ => Err(self.expected("identifier or integer after `.`")),
        }
    }

    /// Used by const generic arguments that start with `const`.
    pub(crate) fn parse_expr_bottom_public(&mut self) -> PResult<P<Expr>> {
        self.parse_expr_bottom()
    }

    fn parse_expr_bottom(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        let t = self.token;
        match t.kind {
            TokenKind::Literal(_) => {
                let lit = self.parse_lit()?;
                return Ok(mk(ExprKind::Lit(lit), lit.span));
            }
            TokenKind::Open(Delim::Paren) => return self.parse_expr_tuple_parens(),
            TokenKind::Open(Delim::Bracket) => return self.parse_expr_array(),
            TokenKind::Open(Delim::Brace) => {
                return self.parse_expr_block(None, lo, BlockCheckMode::Default);
            }
            TokenKind::Open(Delim::Invisible) => {
                self.bump();
                let mut e = self.parse_expr()?;
                self.expect(TokenKind::Close(Delim::Invisible))?;
                // Macro `expr` fragments retain their opaque precedence, but a captured
                // block must remain block-like in statement position. Wrapping `{ ... }`
                // in a synthetic parenthesis makes the following statement look adjacent
                // (`{ ... } next`) and rejects valid transcribers such as `probe_loop!`.
                if expr_is_block_like(&e) {
                    e.span = lo.to(self.prev_token.span);
                    return Ok(e);
                }
                return Ok(mk(ExprKind::Paren(e), lo.to(self.prev_token.span)));
            }
            TokenKind::Or | TokenKind::OrOr => return self.parse_expr_closure(),
            TokenKind::Lt | TokenKind::Shl => {
                let (qself, path) = self.parse_qpath(PathStyle::Expr)?;
                return self.parse_expr_path_rest(Some(qself), path, lo);
            }
            TokenKind::PathSep => {
                let path = self.parse_path(PathStyle::Expr)?;
                return self.parse_expr_path_rest(None, path, lo);
            }
            TokenKind::Lifetime | TokenKind::RawLifetime => {
                // `'label: loop { … }`
                let label = Label {
                    ident: Ident::new(t.sym, t.span),
                };
                self.bump();
                self.expect(TokenKind::Colon)?;
                return self.parse_expr_labeled(label, lo);
            }
            TokenKind::RawIdent => {
                let path = self.parse_path(PathStyle::Expr)?;
                return self.parse_expr_path_rest(None, path, lo);
            }
            TokenKind::Ident => {}
            _ => return Err(self.expected("expression")),
        }
        // Keywords.
        match t.sym {
            kw::True | kw::False => {
                let lit = self.parse_lit()?;
                Ok(mk(ExprKind::Lit(lit), lit.span))
            }
            kw::If => self.parse_expr_if(),
            kw::Match => {
                self.bump();
                let scrutinee = self.parse_expr_res(Restrictions::NO_STRUCT_LITERAL)?;
                let arms = self.parse_match_arms()?;
                Ok(mk(
                    ExprKind::Match(scrutinee, arms, MatchKind::Prefix),
                    lo.to(self.prev_token.span),
                ))
            }
            kw::Loop | kw::While | kw::For
                if !(t.sym == kw::For && self.look_kind(1) == TokenKind::Lt) =>
            {
                self.parse_expr_labeled_inner(None, lo)
            }
            kw::For => self.parse_expr_closure(),
            kw::Unsafe if self.look_kind(1) == TokenKind::Open(Delim::Brace) => {
                self.bump();
                self.parse_expr_block(None, lo, BlockCheckMode::Unsafe)
            }
            kw::Const if self.look_kind(1) == TokenKind::Open(Delim::Brace) => {
                self.bump();
                let block = self.parse_block()?;
                let value = mk(ExprKind::Block(block, None), lo.to(self.prev_token.span));
                Ok(mk(
                    ExprKind::ConstBlock(AnonConst {
                        id: NodeId::DUMMY,
                        value,
                    }),
                    lo.to(self.prev_token.span),
                ))
            }
            kw::Async
                if self.edition2018()
                    || self.look_kind(1) == TokenKind::Open(Delim::Brace)
                    || self.look(1).is_keyword(kw::Move) =>
            {
                self.parse_expr_async_or_gen()
            }
            kw::Gen if self.edition >= super::Edition::E2024 && self.is_gen_block_start() => {
                self.parse_expr_async_or_gen()
            }
            kw::Try if self.look_kind(1) == TokenKind::Open(Delim::Brace) => {
                self.bump();
                let block = self.parse_block()?;
                Ok(mk(ExprKind::TryBlock(block), lo.to(self.prev_token.span)))
            }
            kw::Move | kw::Static => self.parse_expr_closure(),
            kw::Const
                if matches!(self.look_kind(1), TokenKind::Or | TokenKind::OrOr)
                    || self.look(1).is_keyword(kw::Move)
                    || self.look(1).is_keyword(kw::Async) =>
            {
                self.parse_expr_closure()
            }
            kw::Use if matches!(self.look_kind(1), TokenKind::Or | TokenKind::OrOr) => {
                self.parse_expr_closure()
            }
            kw::Return => {
                self.bump();
                let e = if self.can_begin_expr() {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                Ok(mk(ExprKind::Ret(e), lo.to(self.prev_token.span)))
            }
            kw::Become => {
                self.bump();
                let e = self.parse_expr()?;
                Ok(mk(ExprKind::Become(e), lo.to(self.prev_token.span)))
            }
            kw::Do if self.look(1).sym == kw::Yeet && self.look_kind(1) == TokenKind::Ident => {
                self.bump();
                self.bump();
                let e = if self.can_begin_expr() {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                Ok(mk(ExprKind::Yeet(e), lo.to(self.prev_token.span)))
            }
            kw::Break => {
                self.bump();
                let label = if self.check_lifetime() {
                    let l = Label {
                        ident: Ident::new(self.token.sym, self.token.span),
                    };
                    self.bump();
                    Some(l)
                } else {
                    None
                };
                let value = if self.can_begin_expr()
                    && !(self.check(TokenKind::Open(Delim::Brace))
                        && self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL))
                {
                    Some(self.parse_expr_res(self.restrictions.without(Restrictions::STMT_EXPR))?)
                } else {
                    None
                };
                Ok(mk(
                    ExprKind::Break(label, value),
                    lo.to(self.prev_token.span),
                ))
            }
            kw::Continue => {
                self.bump();
                let label = if self.check_lifetime() {
                    let l = Label {
                        ident: Ident::new(self.token.sym, self.token.span),
                    };
                    self.bump();
                    Some(l)
                } else {
                    None
                };
                Ok(mk(ExprKind::Continue(label), lo.to(self.prev_token.span)))
            }
            kw::Yield => {
                self.bump();
                let e = if self.can_begin_expr() {
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                Ok(mk(ExprKind::Yield(e), lo.to(self.prev_token.span)))
            }
            kw::Let => self.parse_expr_let(),
            kw::Underscore => {
                self.bump();
                Ok(mk(ExprKind::Underscore, lo))
            }
            kw::Builtin if self.look_kind(1) == TokenKind::Pound => self.parse_expr_builtin(),
            _ => {
                if self.check_path_start() {
                    let path = self.parse_path(PathStyle::Expr)?;
                    self.parse_expr_path_rest(None, path, lo)
                } else {
                    Err(self.expected("expression"))
                }
            }
        }
    }

    /// `gen {`, `gen move {`
    fn is_gen_block_start(&self) -> bool {
        self.look_kind(1) == TokenKind::Open(Delim::Brace)
            || (self.look(1).is_keyword(kw::Move)
                && self.look_kind(2) == TokenKind::Open(Delim::Brace))
    }

    /// After a path: a macro call, a struct literal, or the path itself.
    fn parse_expr_path_rest(
        &mut self,
        qself: Option<P<QSelf>>,
        path: Path,
        lo: Span,
    ) -> PResult<P<Expr>> {
        if qself.is_none()
            && self.check(TokenKind::Not)
            && matches!(self.look_kind(1), TokenKind::Open(_))
        {
            self.bump();
            let args = self.parse_delim_args()?;
            return Ok(mk(
                ExprKind::MacCall(Box::new(MacCall { path, args })),
                lo.to(self.prev_token.span),
            ));
        }
        if self.check(TokenKind::Open(Delim::Brace))
            && !self.restrictions.contains(Restrictions::NO_STRUCT_LITERAL)
        {
            return self.parse_expr_struct(qself, path, lo);
        }
        Ok(mk(ExprKind::Path(qself, path), lo.to(self.prev_token.span)))
    }

    fn parse_expr_struct(
        &mut self,
        qself: Option<P<QSelf>>,
        path: Path,
        lo: Span,
    ) -> PResult<P<Expr>> {
        self.expect(TokenKind::Open(Delim::Brace))?;
        let mut fields = Vec::new();
        let mut rest = StructRest::None;
        while !self.check(TokenKind::Close(Delim::Brace)) {
            if self.check(TokenKind::DotDot) {
                let dlo = self.token.span;
                self.bump();
                if self.check(TokenKind::Close(Delim::Brace)) {
                    rest = StructRest::Rest(dlo);
                } else {
                    rest = StructRest::Base(self.parse_expr()?);
                }
                break;
            }
            let attrs = self.parse_outer_attributes()?;
            let flo = self.token.span;
            let (ident, is_shorthand) = match self.token.kind {
                TokenKind::Literal(LitKind::Integer) if self.look_kind(1) == TokenKind::Colon => {
                    let i = Ident::new(self.token.sym, self.token.span);
                    self.bump();
                    (i, false)
                }
                _ => {
                    let i = self.parse_ident_any()?;
                    (i, !self.check(TokenKind::Colon))
                }
            };
            let expr = if is_shorthand {
                mk(ExprKind::Path(None, Path::from_ident(ident)), ident.span)
            } else {
                self.expect(TokenKind::Colon)?;
                self.parse_expr()?
            };
            fields.push(ExprField {
                attrs,
                id: NodeId::DUMMY,
                span: flo.to(self.prev_token.span),
                ident,
                expr,
                is_shorthand,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok(mk(
            ExprKind::Struct(Box::new(StructExpr {
                qself,
                path,
                fields,
                rest,
            })),
            lo.to(self.prev_token.span),
        ))
    }

    fn parse_expr_tuple_parens(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        self.expect(TokenKind::Open(Delim::Paren))?;
        let mut es = Vec::new();
        let mut trailing = false;
        while !self.check(TokenKind::Close(Delim::Paren)) {
            es.push(self.parse_expr()?);
            trailing = false;
            if !self.eat(TokenKind::Comma) {
                break;
            }
            trailing = true;
        }
        self.expect(TokenKind::Close(Delim::Paren))?;
        let span = lo.to(self.prev_token.span);
        if es.len() == 1 && !trailing {
            Ok(mk(ExprKind::Paren(es.pop().unwrap()), span))
        } else {
            Ok(mk(ExprKind::Tup(es), span))
        }
    }

    fn parse_expr_array(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        self.expect(TokenKind::Open(Delim::Bracket))?;
        if self.eat(TokenKind::Close(Delim::Bracket)) {
            return Ok(mk(ExprKind::Array(Vec::new()), lo.to(self.prev_token.span)));
        }
        let first = self.parse_expr()?;
        if self.eat(TokenKind::Semi) {
            let count = self.parse_expr()?;
            self.expect(TokenKind::Close(Delim::Bracket))?;
            return Ok(mk(
                ExprKind::Repeat(
                    first,
                    AnonConst {
                        id: NodeId::DUMMY,
                        value: count,
                    },
                ),
                lo.to(self.prev_token.span),
            ));
        }
        let mut es = vec![first];
        while self.eat(TokenKind::Comma) {
            if self.check(TokenKind::Close(Delim::Bracket)) {
                break;
            }
            es.push(self.parse_expr()?);
        }
        self.expect(TokenKind::Close(Delim::Bracket))?;
        Ok(mk(ExprKind::Array(es), lo.to(self.prev_token.span)))
    }

    fn parse_expr_block(
        &mut self,
        label: Option<Label>,
        lo: Span,
        rules: BlockCheckMode,
    ) -> PResult<P<Expr>> {
        let (attrs, mut block) = self.parse_block_with_inner_attrs()?;
        block.rules = rules;
        let mut e = mk(ExprKind::Block(block, label), lo.to(self.prev_token.span));
        e.attrs = attrs;
        Ok(e)
    }

    fn parse_expr_labeled(&mut self, label: Label, lo: Span) -> PResult<P<Expr>> {
        if self.check(TokenKind::Open(Delim::Brace)) {
            return self.parse_expr_block(Some(label), lo, BlockCheckMode::Default);
        }
        if self.check_keyword(kw::Unsafe) && self.look_kind(1) == TokenKind::Open(Delim::Brace) {
            self.bump();
            return self.parse_expr_block(Some(label), lo, BlockCheckMode::Unsafe);
        }
        self.parse_expr_labeled_inner(Some(label), lo)
    }

    /// `loop`, `while`, `for`, with an optional label already parsed.
    fn parse_expr_labeled_inner(&mut self, label: Option<Label>, lo: Span) -> PResult<P<Expr>> {
        if self.eat_keyword(kw::Loop) {
            let (attrs, block) = self.parse_block_with_inner_attrs()?;
            let mut e = mk(ExprKind::Loop(block, label), lo.to(self.prev_token.span));
            e.attrs = attrs;
            return Ok(e);
        }
        if self.eat_keyword(kw::While) {
            let cond = self.parse_expr_cond()?;
            let (attrs, block) = self.parse_block_with_inner_attrs()?;
            let mut e = mk(
                ExprKind::While(cond, block, label),
                lo.to(self.prev_token.span),
            );
            e.attrs = attrs;
            return Ok(e);
        }
        if self.eat_keyword(kw::For) {
            let kind = if self.check_keyword(kw::Await) && self.edition2018() {
                self.bump();
                ForLoopKind::ForAwait
            } else {
                ForLoopKind::For
            };
            let pat = self.parse_pat_allow_top_alt()?;
            self.expect_keyword(kw::In)?;
            let iter = self.parse_expr_res(Restrictions::NO_STRUCT_LITERAL)?;
            let (attrs, body) = self.parse_block_with_inner_attrs()?;
            let mut e = mk(
                ExprKind::ForLoop {
                    pat,
                    iter,
                    body,
                    label,
                    kind,
                },
                lo.to(self.prev_token.span),
            );
            e.attrs = attrs;
            return Ok(e);
        }
        Err(self.expected("`loop`, `while`, `for`, or a block after a label"))
    }

    /// The condition of `if` or `while`: no struct literals, `let` allowed.
    fn parse_expr_cond(&mut self) -> PResult<P<Expr>> {
        self.parse_expr_res(Restrictions::NO_STRUCT_LITERAL.union(Restrictions::ALLOW_LET))
    }

    fn parse_expr_if(&mut self) -> PResult<P<Expr>> {
        self.enter()?;
        let r = self.parse_expr_if_inner();
        self.depth -= 1;
        r
    }

    fn parse_expr_if_inner(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        self.expect_keyword(kw::If)?;
        let cond = self.parse_expr_cond()?;
        let then = self.parse_block()?;
        let els = if self.eat_keyword(kw::Else) {
            let elo = self.token.span;
            if self.check_keyword(kw::If) {
                Some(self.parse_expr_if()?)
            } else {
                Some(self.parse_expr_block(None, elo, BlockCheckMode::Default)?)
            }
        } else {
            None
        };
        Ok(mk(
            ExprKind::If(cond, then, els),
            lo.to(self.prev_token.span),
        ))
    }

    /// `let pat = scrutinee`: the scrutinee binds tighter than `&&` and `||`.
    fn parse_expr_let(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        self.expect_keyword(kw::Let)?;
        let pat = self.parse_pat_allow_top_alt()?;
        self.expect(TokenKind::Eq)?;
        let r = self
            .restrictions
            .without(Restrictions::ALLOW_LET)
            .without(Restrictions::STMT_EXPR);
        let scrutinee = self.with_res(r, |p| p.parse_expr_assoc(Some(Prec::Compare)))?;
        let span = lo.to(self.prev_token.span);
        Ok(mk(ExprKind::Let(pat, scrutinee, span), span))
    }

    fn parse_match_arms(&mut self) -> PResult<Vec<Arm>> {
        self.expect(TokenKind::Open(Delim::Brace))?;
        let _inner = self.parse_inner_attributes()?;
        let mut arms = Vec::new();
        while !self.check(TokenKind::Close(Delim::Brace)) {
            let attrs = self.parse_outer_attributes()?;
            let lo = attrs.first().map_or(self.token.span, |a| a.span);
            let pat = self.parse_pat_allow_top_alt()?;
            let guard = if self.eat_keyword(kw::If) {
                Some(self.parse_expr_res(Restrictions::ALLOW_LET)?)
            } else {
                None
            };
            let body = if self.eat(TokenKind::FatArrow) {
                let body = self.parse_expr_res(Restrictions::STMT_EXPR)?;
                let needs_comma = !expr_is_block_like(&body);
                if !self.eat(TokenKind::Comma)
                    && needs_comma
                    && !self.check(TokenKind::Close(Delim::Brace))
                {
                    return Err(self.expected("`,` following `match` arm"));
                }
                Some(body)
            } else {
                // A never pattern: `Err(!)` needs no body.
                if !self.eat(TokenKind::Comma) && !self.check(TokenKind::Close(Delim::Brace)) {
                    return Err(self.expected("`=>`"));
                }
                None
            };
            arms.push(Arm {
                attrs,
                pat,
                guard,
                body,
                span: lo.to(self.prev_token.span),
                id: NodeId::DUMMY,
            });
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok(arms)
    }

    /// `async {}`, `async move {}`, `async gen {}`, `gen {}`, or an async closure.
    fn parse_expr_async_or_gen(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        // Look past `async`/`gen`/`move` for a block.
        let mut i = 0;
        let mut is_async = false;
        let mut is_gen = false;
        loop {
            let t = self.look(i);
            if t.is_keyword(kw::Async) {
                is_async = true;
            } else if t.is_keyword(kw::Gen) {
                is_gen = true;
            } else {
                break;
            }
            i += 1;
        }
        let has_move = self.look(i).is_keyword(kw::Move);
        let after = if has_move { i + 1 } else { i };
        if self.look_kind(after) != TokenKind::Open(Delim::Brace) {
            return self.parse_expr_closure();
        }
        for _ in 0..i {
            self.bump();
        }
        let capture = if has_move {
            self.bump();
            CaptureBy::Value {
                move_kw: self.prev_token.span,
            }
        } else {
            CaptureBy::Ref
        };
        let kind = match (is_async, is_gen) {
            (true, true) => GenBlockKind::AsyncGen,
            (false, true) => GenBlockKind::Gen,
            _ => GenBlockKind::Async,
        };
        let (attrs, block) = self.parse_block_with_inner_attrs()?;
        let mut e = mk(
            ExprKind::Gen(capture, block, kind),
            lo.to(self.prev_token.span),
        );
        e.attrs = attrs;
        Ok(e)
    }

    fn parse_expr_closure(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        let binder = if self.check_keyword(kw::For) {
            self.bump();
            self.parse_generic_params_list()?
        } else {
            Vec::new()
        };
        let constness = if self.eat_keyword(kw::Const) {
            Constness::Yes(self.prev_token.span)
        } else {
            Constness::No
        };
        let movability = if self.eat_keyword(kw::Static) {
            Movability::Static
        } else {
            Movability::Movable
        };
        let mut coroutine_kind = None;
        loop {
            let span = self.token.span;
            if self.check_keyword(kw::Async) {
                self.bump();
                coroutine_kind = Some(match coroutine_kind {
                    Some(CoroutineKind::Gen { .. }) => CoroutineKind::AsyncGen { span },
                    _ => CoroutineKind::Async { span },
                });
            } else if self.check_keyword(kw::Gen) && self.edition >= super::Edition::E2024 {
                self.bump();
                coroutine_kind = Some(match coroutine_kind {
                    Some(CoroutineKind::Async { .. }) => CoroutineKind::AsyncGen { span },
                    _ => CoroutineKind::Gen { span },
                });
            } else {
                break;
            }
        }
        let capture_clause = if self.eat_keyword(kw::Move) {
            CaptureBy::Value {
                move_kw: self.prev_token.span,
            }
        } else if self.eat_keyword(kw::Use) {
            CaptureBy::Use {
                use_kw: self.prev_token.span,
            }
        } else {
            CaptureBy::Ref
        };
        let decl_lo = self.token.span;
        let mut inputs = Vec::new();
        if !self.eat(TokenKind::OrOr) {
            self.expect(TokenKind::Or)?;
            while !self.check_start(TokenKind::Or) {
                let attrs = self.parse_outer_attributes()?;
                let plo = self.token.span;
                let pat = self.parse_pat_no_top_alt()?;
                let ty = if self.eat(TokenKind::Colon) {
                    self.parse_ty()?
                } else {
                    Box::new(Ty {
                        id: NodeId::DUMMY,
                        kind: TyKind::Infer,
                        span: self.prev_token.span.shrink_to_hi(),
                    })
                };
                inputs.push(Param {
                    attrs,
                    ty,
                    pat,
                    id: NodeId::DUMMY,
                    span: plo.to(self.prev_token.span),
                });
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            if !self.break_and_eat(TokenKind::Or) {
                return Err(self.expected("`|`"));
            }
        }
        let output = self.parse_ret_ty(true)?;
        let fn_decl_span = decl_lo.to(self.prev_token.span);
        let body = match output {
            FnRetTy::Default(_) => {
                let r = self
                    .restrictions
                    .without(Restrictions::STMT_EXPR)
                    .without(Restrictions::ALLOW_LET);
                self.with_res(r, |p| p.parse_expr_assoc(None))?
            }
            FnRetTy::Ty(_) => {
                let blo = self.token.span;
                self.parse_expr_block(None, blo, BlockCheckMode::Default)?
            }
        };
        let closure = Closure {
            binder,
            capture_clause,
            constness,
            coroutine_kind,
            movability,
            fn_decl: Box::new(FnDecl { inputs, output }),
            body,
            fn_decl_span,
        };
        Ok(mk(
            ExprKind::Closure(Box::new(closure)),
            lo.to(self.prev_token.span),
        ))
    }

    /// `builtin # offset_of(T, field)`, `builtin # type_ascribe(e, T)`, and friends.
    fn parse_expr_builtin(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        self.bump();
        self.expect(TokenKind::Pound)?;
        let name = self.parse_ident_any()?;
        self.expect(TokenKind::Open(Delim::Paren))?;
        let kind = match name.as_str() {
            "offset_of" => {
                let ty = self.parse_ty()?;
                self.expect(TokenKind::Comma)?;
                let mut fields = Vec::new();
                loop {
                    // A field path passed through a macro's `expr` fragment comes in
                    // invisible delimiters.
                    while self.eat(TokenKind::Open(Delim::Invisible)) {}
                    match self.token.kind {
                        TokenKind::Literal(LitKind::Float) => {
                            let t = self.token;
                            self.bump();
                            for part in t.sym.as_str().split('.') {
                                fields.push(Ident::new(Symbol::intern(part), t.span));
                            }
                        }
                        TokenKind::Literal(LitKind::Integer) => {
                            fields.push(Ident::new(self.token.sym, self.token.span));
                            self.bump();
                        }
                        _ => fields.push(self.parse_ident_any()?),
                    }
                    while self.eat(TokenKind::Close(Delim::Invisible)) {}
                    if !self.eat(TokenKind::Dot) {
                        break;
                    }
                }
                self.eat(TokenKind::Comma);
                ExprKind::OffsetOf(ty, fields)
            }
            "type_ascribe" => {
                let e = self.parse_expr()?;
                self.expect(TokenKind::Comma)?;
                let ty = self.parse_ty()?;
                self.eat(TokenKind::Comma);
                ExprKind::Type(e, ty)
            }
            "format_args" | "format_args_nl" | "const_format_args" => {
                let template = self.parse_expr()?;
                let mut args = Vec::new();
                while self.eat(TokenKind::Comma) {
                    if self.check(TokenKind::Close(Delim::Paren)) {
                        break;
                    }
                    let name = if self.token.is_ident() && self.look_kind(1) == TokenKind::Eq {
                        let n = Ident::new(self.token.sym, self.token.span);
                        self.bump();
                        self.bump();
                        Some(n)
                    } else {
                        None
                    };
                    args.push(FormatArgument {
                        name,
                        expr: self.parse_expr()?,
                    });
                }
                ExprKind::FormatArgs(Box::new(FormatArgs {
                    template,
                    args,
                    span: lo.to(self.token.span),
                    newline: name.as_str() == "format_args_nl",
                    is_const: name.as_str() == "const_format_args",
                }))
            }
            "asm" | "naked_asm" => {
                let kind = if name.as_str() == "asm" {
                    AsmMacro::Asm
                } else {
                    AsmMacro::NakedAsm
                };
                let tokens = self.collect_until_close_paren();
                ExprKind::InlineAsm(Box::new(InlineAsm {
                    kind,
                    tokens,
                    span: lo.to(self.token.span),
                }))
            }
            _ => {
                // `field_of`, `wrap_binder`, `unwrap_binder`, …: keep the tokens as a macro
                // call the expander knows by name.
                let mut depth = 0usize;
                while !(depth == 0 && self.check(TokenKind::Close(Delim::Paren)))
                    && !self.check(TokenKind::Eof)
                {
                    match self.token.kind {
                        TokenKind::Open(_) => depth += 1,
                        TokenKind::Close(_) => depth -= 1,
                        _ => {}
                    }
                    self.bump();
                }
                ExprKind::Err
            }
        };
        self.expect(TokenKind::Close(Delim::Paren))?;
        Ok(mk(kind, lo.to(self.prev_token.span)))
    }

    /// The tokens up to the `)` closing the current group (not eaten).
    pub(crate) fn collect_until_close_paren(&mut self) -> TokenStream {
        let mut tokens = Vec::new();
        let mut depth = 0usize;
        while !(depth == 0 && self.check(TokenKind::Close(Delim::Paren)))
            && !self.check(TokenKind::Eof)
        {
            match self.token.kind {
                TokenKind::Open(_) => depth += 1,
                TokenKind::Close(_) => depth -= 1,
                _ => {}
            }
            tokens.push(self.token);
            self.bump();
        }
        TokenStream::new(tokens)
    }

    /// Statements until `Eof`: the output of a macro called in statement position.
    pub fn parse_stmts_fragment(&mut self) -> Vec<Stmt> {
        let mut stmts = Vec::new();
        while !self.check(TokenKind::Eof) {
            if self.check(TokenKind::Semi) {
                let span = self.token.span;
                self.bump();
                stmts.push(Stmt {
                    id: NodeId::DUMMY,
                    kind: StmtKind::Empty,
                    span,
                });
                continue;
            }
            match self.parse_full_stmt() {
                Ok(Some(stmt)) => stmts.push(stmt),
                Ok(None) => {
                    let e = self.expected("statement");
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
            }
        }
        stmts
    }

    // -----------------------------------------------------------------------------------------
    // Blocks and statements

    pub fn parse_block(&mut self) -> PResult<P<Block>> {
        let (_attrs, block) = self.parse_block_with_inner_attrs()?;
        Ok(block)
    }

    pub(crate) fn parse_block_with_inner_attrs(&mut self) -> PResult<(Vec<Attribute>, P<Block>)> {
        let lo = self.token.span;
        if self.check(TokenKind::Open(Delim::Invisible)) {
            // A `$b:block` fragment.
            self.bump();
            let r = self.parse_block_with_inner_attrs()?;
            self.expect(TokenKind::Close(Delim::Invisible))?;
            return Ok(r);
        }
        self.expect(TokenKind::Open(Delim::Brace))?;
        let attrs = self.parse_inner_attributes()?;
        // Statements inside a block of a `$s:stmt` fragment have their `;`s as usual.
        let fragment = std::mem::replace(&mut self.stmt_fragment, false);
        let stmts = self.parse_block_stmts();
        self.stmt_fragment = fragment;
        let stmts = stmts?;
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok((
            attrs,
            Box::new(Block {
                stmts,
                id: NodeId::DUMMY,
                rules: BlockCheckMode::Default,
                span: lo.to(self.prev_token.span),
            }),
        ))
    }

    fn parse_block_stmts(&mut self) -> PResult<Vec<Stmt>> {
        let mut stmts = Vec::new();
        while !self.check(TokenKind::Close(Delim::Brace)) && !self.check(TokenKind::Eof) {
            if self.check(TokenKind::Semi) {
                let span = self.token.span;
                self.bump();
                stmts.push(Stmt {
                    id: NodeId::DUMMY,
                    kind: StmtKind::Empty,
                    span,
                });
                continue;
            }
            match self.parse_full_stmt() {
                Ok(Some(stmt)) => stmts.push(stmt),
                Ok(None) => {
                    let e = self.expected("statement");
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
            }
        }
        Ok(stmts)
    }

    /// One statement, with its `;` if it has one.
    pub fn parse_full_stmt(&mut self) -> PResult<Option<Stmt>> {
        let attrs = self.parse_outer_attributes()?;
        let lo = attrs.first().map_or(self.token.span, |a| a.span);

        let super_ = if self.check_keyword(kw::Super) && self.look(1).is_keyword(kw::Let) {
            self.bump();
            Some(self.prev_token.span)
        } else {
            None
        };
        if self.check_keyword(kw::Let) {
            self.bump();
            let pat = self.parse_pat_allow_top_alt()?;
            let ty = if self.eat(TokenKind::Colon) {
                Some(self.parse_ty()?)
            } else {
                None
            };
            let kind = if self.eat(TokenKind::Eq) {
                let init = self.parse_expr()?;
                if self.eat_keyword(kw::Else) {
                    LocalKind::InitElse(init, self.parse_block()?)
                } else {
                    LocalKind::Init(init)
                }
            } else {
                LocalKind::Decl
            };
            if !self.stmt_fragment {
                self.expect(TokenKind::Semi)?;
            }
            let span = lo.to(self.prev_token.span);
            let local = Local {
                id: NodeId::DUMMY,
                super_,
                pat,
                ty,
                kind,
                span,
                attrs,
            };
            return Ok(Some(Stmt {
                id: NodeId::DUMMY,
                kind: StmtKind::Let(Box::new(local)),
                span,
            }));
        }

        if self.is_item_start() {
            return match self.parse_item_with_attrs(attrs, ItemCtx::Free)? {
                Some(item) => {
                    let span = item.span;
                    Ok(Some(Stmt {
                        id: NodeId::DUMMY,
                        kind: StmtKind::Item(item),
                        span,
                    }))
                }
                None => Ok(None),
            };
        }

        if self.is_macro_call_start() {
            let mac = self.parse_mac_call()?;
            let brace = mac.args.delim == Delim::Brace;
            if (brace && !matches!(self.token.kind, TokenKind::Dot | TokenKind::Question))
                || self.check(TokenKind::Semi)
                || self.check(TokenKind::Eof)
                || (self.check(TokenKind::Close(Delim::Brace)) && !brace)
            {
                let style = if !self.stmt_fragment && self.eat(TokenKind::Semi) {
                    MacStmtStyle::Semicolon
                } else if brace {
                    MacStmtStyle::Braces
                } else {
                    MacStmtStyle::NoBraces
                };
                let span = lo.to(self.prev_token.span);
                return Ok(Some(Stmt {
                    id: NodeId::DUMMY,
                    kind: StmtKind::MacCall(Box::new(MacCallStmt {
                        mac: Box::new(mac),
                        style,
                        attrs,
                    })),
                    span,
                }));
            }
            // `m!(…).method()`, `m!(…) + 1`: an expression.
            let span = mac.path.span.to(self.prev_token.span);
            let mut e = mk(ExprKind::MacCall(Box::new(mac)), span);
            e.attrs = attrs;
            let e = self.with_res(Restrictions::STMT_EXPR, |p| -> PResult<P<Expr>> {
                let e = p.parse_expr_dot_or_call_with(e)?;
                p.parse_expr_assoc_rest(None, e)
            })?;
            return self.finish_expr_stmt(e, lo).map(Some);
        }

        // An item after attributes we didn't recognize as an item start is an error, but
        // expressions may have attributes too.
        let mut e = self.with_res(Restrictions::STMT_EXPR, |p| p.parse_expr_assoc(None))?;
        if !attrs.is_empty() {
            let mut all = attrs;
            all.append(&mut e.attrs);
            e.attrs = all;
        }
        self.finish_expr_stmt(e, lo).map(Some)
    }

    /// A `$s:stmt` fragment: one statement without its trailing `;`.
    pub fn parse_stmt_fragment(&mut self) -> PResult<Option<Stmt>> {
        self.stmt_fragment = true;
        let r = self.parse_full_stmt();
        self.stmt_fragment = false;
        r
    }

    fn finish_expr_stmt(&mut self, e: P<Expr>, lo: Span) -> PResult<Stmt> {
        if self.stmt_fragment {
            let span = lo.to(e.span);
            return Ok(Stmt {
                id: NodeId::DUMMY,
                kind: StmtKind::Expr(e),
                span,
            });
        }
        if self.eat(TokenKind::Semi) {
            let span = lo.to(self.prev_token.span);
            return Ok(Stmt {
                id: NodeId::DUMMY,
                kind: StmtKind::Semi(e),
                span,
            });
        }
        let span = lo.to(e.span);
        if self.check(TokenKind::Close(Delim::Brace))
            || self.check(TokenKind::Eof)
            || expr_is_block_like(&e)
        {
            return Ok(Stmt {
                id: NodeId::DUMMY,
                kind: StmtKind::Expr(e),
                span,
            });
        }
        Err(self.expected("`;` or `}`"))
    }
}

fn next_prec(p: Prec) -> Prec {
    match p {
        Prec::Assign => Prec::Range,
        Prec::Range => Prec::Or,
        Prec::Or => Prec::And,
        Prec::And => Prec::Compare,
        Prec::Compare => Prec::BitOr,
        Prec::BitOr => Prec::BitXor,
        Prec::BitXor => Prec::BitAnd,
        Prec::BitAnd => Prec::Shift,
        Prec::Shift => Prec::Sum,
        Prec::Sum => Prec::Product,
        Prec::Product => Prec::Cast,
        Prec::Cast => Prec::Cast,
    }
}
