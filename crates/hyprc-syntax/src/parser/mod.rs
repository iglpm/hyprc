//! A recursive-descent parser for all of Rust's syntax, nightly features included (the
//! standard library is written in them).
//!
//! It reads a token slice, so the same parser handles files and macro arguments. Glued
//! punctuation is split on demand (`break_and_eat`), and backtracking is restoring an index.

mod expr;
mod item;
mod pat;
mod ty;

use crate::ast::*;
use crate::token::{AttrStyle, Delim, LitKind, Token, TokenKind};
use hyprc_span::{Diag, DiagCtxt, Ident, Span, Symbol, kw};

pub use hyprc_span::Edition;

/// A parse error not yet reported: the caller decides whether to report it (or to try
/// another way to parse the same tokens).
pub struct PErr(pub Box<Diag>);

pub type PResult<T> = Result<T, PErr>;

#[derive(Clone, Copy, PartialEq, Eq, Default)]
pub(crate) struct Restrictions(u8);

impl Restrictions {
    /// Parsing an expression statement: a block-like expression ends it (`match x {} - 1` is
    /// two statements).
    pub const STMT_EXPR: Restrictions = Restrictions(1);
    /// In `if`/`while`/`match`/`for` headers: `S {` starts the body, not a struct literal.
    pub const NO_STRUCT_LITERAL: Restrictions = Restrictions(2);
    /// `let` expressions are allowed (conditions and let chains).
    pub const ALLOW_LET: Restrictions = Restrictions(4);

    pub const fn contains(self, other: Restrictions) -> bool {
        self.0 & other.0 == other.0
    }

    pub const fn union(self, other: Restrictions) -> Restrictions {
        Restrictions(self.0 | other.0)
    }

    pub const fn without(self, other: Restrictions) -> Restrictions {
        Restrictions(self.0 & !other.0)
    }
}

pub struct Parser<'a> {
    tokens: &'a [Token],
    /// Index of the token after `token`.
    pos: usize,
    /// The current token. Usually `tokens[pos - 1]`, but after splitting a glued token it is
    /// the rest of that token.
    pub token: Token,
    pub prev_token: Token,
    pub(crate) restrictions: Restrictions,
    pub edition: Edition,
    pub dcx: &'a DiagCtxt,
    /// The span of the whole input, for `Eof` errors.
    eof_span: Span,
    /// Errors reported so far; past `MAX_ERRORS` the parser gives up on the input.
    errors: std::cell::Cell<u32>,
    /// Nesting depth of expressions, types and patterns, to fail cleanly on absurdly deep
    /// input instead of overflowing the stack.
    pub(crate) depth: u32,
    /// Parsing a `$s:stmt` fragment: statements end without their `;`.
    pub(crate) stmt_fragment: bool,
    /// The current token is the rest of a glued token split by `break_and_eat`.
    split: bool,
}

/// After this many errors in one input, the rest of it is skipped: more would only be noise,
/// and a recovery bug can't turn into an endless stream of diagnostics.
const MAX_ERRORS: u32 = 100;
/// Deeper nesting than this is reported, not parsed. Parsing threads get stacks big enough
/// for it (see `PARSER_STACK_SIZE`).
pub const MAX_DEPTH: u32 = 1000;
/// Stack size for threads that parse.
pub const PARSER_STACK_SIZE: usize = 64 << 20;

#[derive(Clone, Copy)]
pub(crate) struct Snapshot {
    split: bool,
    pos: usize,
    token: Token,
    prev_token: Token,
    restrictions: Restrictions,
}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [Token], edition: Edition, dcx: &'a DiagCtxt) -> Parser<'a> {
        let eof_span = tokens.last().map_or(Span::DUMMY, |t| t.span);
        let mut p = Parser {
            tokens,
            pos: 0,
            token: Token::dummy(),
            prev_token: Token::dummy(),
            restrictions: Restrictions::default(),
            edition,
            dcx,
            eof_span,
            errors: std::cell::Cell::new(0),
            depth: 0,
            stmt_fragment: false,
            split: false,
        };
        p.bump();
        p
    }

    // -----------------------------------------------------------------------------------------
    // Token access

    pub fn bump(&mut self) {
        self.split = false;
        self.prev_token = self.token;
        self.token = match self.tokens.get(self.pos) {
            Some(&t) => t,
            None => Token::new(TokenKind::Eof, self.eof_span.shrink_to_hi()),
        };
        self.pos += 1;
    }

    /// The token `n` after the current one (`look(0)` is the current token).
    #[inline]
    pub fn look(&self, n: usize) -> Token {
        if n == 0 {
            return self.token;
        }
        match self.tokens.get(self.pos + n - 1) {
            Some(&t) => t,
            None => Token::new(TokenKind::Eof, self.eof_span.shrink_to_hi()),
        }
    }

    #[inline]
    pub fn look_kind(&self, n: usize) -> TokenKind {
        self.look(n).kind
    }

    /// How many tokens were consumed: the index of the current token. `None` when the
    /// current token is the rest of a split one (a fragment can't end inside a token).
    pub fn consumed(&self) -> Option<usize> {
        if self.split { None } else { Some(self.pos - 1) }
    }

    pub(crate) fn snapshot(&self) -> Snapshot {
        Snapshot {
            split: self.split,
            pos: self.pos,
            token: self.token,
            prev_token: self.prev_token,
            restrictions: self.restrictions,
        }
    }

    pub(crate) fn restore(&mut self, s: Snapshot) {
        self.split = s.split;
        self.pos = s.pos;
        self.token = s.token;
        self.prev_token = s.prev_token;
        self.restrictions = s.restrictions;
    }

    #[inline]
    pub fn check(&self, kind: TokenKind) -> bool {
        self.token.kind == kind
    }

    #[inline]
    pub fn eat(&mut self, kind: TokenKind) -> bool {
        if self.token.kind == kind {
            self.bump();
            true
        } else {
            false
        }
    }

    pub fn expect(&mut self, kind: TokenKind) -> PResult<()> {
        if self.eat(kind) {
            Ok(())
        } else if self.break_and_eat(kind) {
            Ok(())
        } else {
            Err(self.expected(&format!("`{}`", kind.punct_str().unwrap_or("?"))))
        }
    }

    /// Eats `kind` from the front of the current token, splitting glued punctuation: with
    /// `>>` current, `break_and_eat(Gt)` leaves `>`.
    pub fn break_and_eat(&mut self, kind: TokenKind) -> bool {
        if self.token.kind == kind {
            self.bump();
            return true;
        }
        if let Some((first, rest)) = self.token.split_first()
            && first == kind
        {
            let span = self.token.span;
            let first_len = first.punct_str().map_or(1, |s| s.len() as u32);
            self.prev_token = Token::new(
                first,
                Span {
                    hi: span.lo + first_len,
                    ..span
                },
            );
            self.token = Token {
                kind: rest,
                span: Span {
                    lo: span.lo + first_len,
                    ..span
                },
                ..self.token
            };
            self.split = true;
            return true;
        }
        false
    }

    /// Does the current token start with `kind`, possibly glued to more?
    pub fn check_start(&self, kind: TokenKind) -> bool {
        self.token.kind == kind
            || self
                .token
                .split_first()
                .is_some_and(|(first, _)| first == kind)
    }

    #[inline]
    pub fn check_keyword(&self, kw: Symbol) -> bool {
        self.token.is_keyword(kw)
    }

    pub fn eat_keyword(&mut self, kw: Symbol) -> bool {
        if self.token.is_keyword(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    pub fn expect_keyword(&mut self, kw: Symbol) -> PResult<()> {
        if self.eat_keyword(kw) {
            Ok(())
        } else {
            Err(self.expected(&format!("`{kw}`")))
        }
    }

    pub fn is_keyword_ahead(&self, n: usize, kws: &[Symbol]) -> bool {
        let t = self.look(n);
        t.kind == TokenKind::Ident && kws.contains(&t.sym)
    }

    pub(crate) fn edition2018(&self) -> bool {
        self.edition >= Edition::E2018
    }

    /// A non-reserved identifier.
    pub fn check_ident(&self) -> bool {
        self.token.is_non_reserved_ident(self.edition2018())
    }

    pub fn ident_ahead(&self, n: usize) -> bool {
        self.look(n).is_non_reserved_ident(self.edition2018())
    }

    pub fn parse_ident(&mut self) -> PResult<Ident> {
        if self.check_ident() {
            let ident = Ident::new(self.token.sym, self.token.span);
            self.bump();
            Ok(ident)
        } else {
            Err(self.expected("identifier"))
        }
    }

    /// An identifier, or `_`.
    pub fn parse_ident_or_underscore(&mut self) -> PResult<Ident> {
        if self.check_keyword(kw::Underscore) {
            let ident = Ident::new(kw::Underscore, self.token.span);
            self.bump();
            return Ok(ident);
        }
        self.parse_ident()
    }

    /// Any identifier, keywords included (field names after `.`, macro fragment names).
    pub fn parse_ident_any(&mut self) -> PResult<Ident> {
        if self.token.is_ident() {
            let ident = Ident::new(self.token.sym, self.token.span);
            self.bump();
            Ok(ident)
        } else {
            Err(self.expected("identifier"))
        }
    }

    pub fn check_lifetime(&self) -> bool {
        self.token.is_lifetime()
    }

    pub fn expect_lifetime(&mut self) -> PResult<Lifetime> {
        if self.check_lifetime() {
            let lt = Lifetime {
                id: NodeId::DUMMY,
                ident: Ident::new(self.token.sym, self.token.span),
            };
            self.bump();
            Ok(lt)
        } else {
            Err(self.expected("lifetime"))
        }
    }

    pub(crate) fn with_res<T>(&mut self, r: Restrictions, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = std::mem::replace(&mut self.restrictions, r);
        let res = f(self);
        self.restrictions = old;
        res
    }

    // -----------------------------------------------------------------------------------------
    // Errors

    pub fn describe_token(t: &Token) -> String {
        match t.kind {
            TokenKind::Eof => "end of file".to_string(),
            TokenKind::Ident if t.sym.is_reserved(true) => format!("keyword `{}`", t.sym),
            TokenKind::Ident | TokenKind::RawIdent => {
                format!("identifier `{}`", crate::token::token_text(t))
            }
            TokenKind::Literal(_) => format!("literal `{}`", crate::token::token_text(t)),
            TokenKind::Lifetime | TokenKind::RawLifetime => format!("lifetime `{}`", t.sym),
            TokenKind::DocComment(..) => "doc comment".to_string(),
            TokenKind::Open(Delim::Invisible) | TokenKind::Close(Delim::Invisible) => {
                "macro fragment".to_string()
            }
            _ => format!("`{}`", crate::token::token_text(t)),
        }
    }

    pub fn expected(&self, what: &str) -> PErr {
        let found = Self::describe_token(&self.token);
        self.error_at(self.token.span, format!("expected {what}, found {found}"))
    }

    pub fn error_at(&self, span: Span, msg: impl Into<String>) -> PErr {
        PErr(Box::new(Diag::error(msg).span(span, "")))
    }

    pub fn emit(&mut self, err: PErr) {
        let n = self.errors.get() + 1;
        self.errors.set(n);
        if n <= MAX_ERRORS {
            self.dcx.emit(*err.0);
        }
        if n == MAX_ERRORS {
            self.dcx.emit(
                Diag::error("too many errors in this file; skipping the rest of it")
                    .span(self.token.span, ""),
            );
        }
        if n >= MAX_ERRORS {
            self.skip_to_eof();
        }
    }

    fn skip_to_eof(&mut self) {
        self.pos = self.tokens.len().saturating_sub(1);
        self.bump();
    }

    /// Enters one level of nesting; fails when the input nests deeper than `MAX_DEPTH`.
    pub(crate) fn enter(&mut self) -> PResult<()> {
        self.depth += 1;
        if self.depth > MAX_DEPTH {
            self.depth -= 1;
            return Err(self.error_at(self.token.span, "this expression is nested too deeply"));
        }
        Ok(())
    }

    // -----------------------------------------------------------------------------------------
    // Delimited groups

    /// The index (in `tokens`) of the current token when it is an `Open` (those are never
    /// the rest of a split token, so they are always `tokens[pos - 1]`).
    fn open_index(&self) -> Option<usize> {
        match self.token.kind {
            TokenKind::Open(_) => Some(self.pos - 1),
            _ => None,
        }
    }

    /// The index of the `Close` matching the `Open` at `open`. A scan, so creating a parser
    /// costs nothing: the macro matcher starts one at every nonterminal.
    fn close_of(&self, open: usize) -> Option<usize> {
        let mut depth = 0usize;
        for (i, t) in self.tokens[open..].iter().enumerate() {
            match t.kind {
                TokenKind::Open(_) => depth += 1,
                TokenKind::Close(_) => {
                    depth -= 1;
                    if depth == 0 {
                        return Some(open + i);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// Skips the group starting at the current `Open` token, close included.
    pub fn skip_group(&mut self) {
        if let Some(i) = self.open_index() {
            if let Some(close) = self.close_of(i) {
                self.pos = close;
                self.bump(); // the `Close`
                self.bump(); // past it
                return;
            }
        }
        self.bump();
    }

    /// The tokens inside the group starting at the current `Open` token; moves past it.
    pub fn parse_delim_args(&mut self) -> PResult<DelimArgs> {
        let TokenKind::Open(delim) = self.token.kind else {
            return Err(self.expected("one of `(`, `[`, or `{`"));
        };
        let Some(i) = self.open_index() else {
            return Err(self.expected("one of `(`, `[`, or `{`"));
        };
        let Some(close) = self.close_of(i) else {
            return Err(self.expected("a closing delimiter"));
        };
        let open_span = self.token.span;
        let tokens = TokenStream::new(self.tokens[i + 1..close].to_vec());
        let close_span = self.tokens[close].span;
        self.skip_group();
        Ok(DelimArgs {
            open: open_span,
            close: close_span,
            delim,
            tokens,
        })
    }

    /// Skips tokens until a `;` (eaten) or a `}` closing the enclosing group (not eaten),
    /// stepping over nested groups. Used to resume after an error.
    pub(crate) fn recover_to_semi_or_close(&mut self) {
        loop {
            match self.token.kind {
                TokenKind::Eof | TokenKind::Close(_) => return,
                TokenKind::Semi => {
                    self.bump();
                    return;
                }
                TokenKind::Open(Delim::Brace) => {
                    self.skip_group();
                    // An item's body ends it: `fn f() { … }`.
                    if self.token.kind != TokenKind::Dot && self.token.kind != TokenKind::Question {
                        return;
                    }
                }
                TokenKind::Open(_) => self.skip_group(),
                _ => self.bump(),
            }
        }
    }

    // -----------------------------------------------------------------------------------------
    // Attributes

    pub fn parse_outer_attributes(&mut self) -> PResult<Vec<Attribute>> {
        let mut attrs = Vec::new();
        loop {
            match self.token.kind {
                TokenKind::Pound if self.look_kind(1) == TokenKind::Open(Delim::Bracket) => {
                    attrs.push(self.parse_attribute(AttrStyle::Outer)?);
                }
                TokenKind::DocComment(AttrStyle::Outer, kind) => {
                    attrs.push(Attribute {
                        kind: AttrKind::DocComment(kind, self.token.sym),
                        style: AttrStyle::Outer,
                        span: self.token.span,
                    });
                    self.bump();
                }
                _ => return Ok(attrs),
            }
        }
    }

    pub fn parse_inner_attributes(&mut self) -> PResult<Vec<Attribute>> {
        let mut attrs = Vec::new();
        loop {
            match self.token.kind {
                TokenKind::Pound
                    if self.look_kind(1) == TokenKind::Not
                        && self.look_kind(2) == TokenKind::Open(Delim::Bracket) =>
                {
                    attrs.push(self.parse_attribute(AttrStyle::Inner)?);
                }
                TokenKind::DocComment(AttrStyle::Inner, kind) => {
                    attrs.push(Attribute {
                        kind: AttrKind::DocComment(kind, self.token.sym),
                        style: AttrStyle::Inner,
                        span: self.token.span,
                    });
                    self.bump();
                }
                _ => return Ok(attrs),
            }
        }
    }

    fn parse_attribute(&mut self, style: AttrStyle) -> PResult<Attribute> {
        let lo = self.token.span;
        self.expect(TokenKind::Pound)?;
        if style == AttrStyle::Inner {
            self.expect(TokenKind::Not)?;
        }
        self.expect(TokenKind::Open(Delim::Bracket))?;
        let item = self.parse_attr_item()?;
        self.expect(TokenKind::Close(Delim::Bracket))?;
        Ok(Attribute {
            kind: AttrKind::Normal(Box::new(item)),
            style,
            span: lo.to(self.prev_token.span),
        })
    }

    /// `path`, `path(tokens)`, `path = expr`, or `unsafe(…)` around any of them. Also what
    /// `cfg_attr` expands to.
    pub fn parse_attr_item(&mut self) -> PResult<AttrItem> {
        if self.check_keyword(kw::Unsafe) && self.look_kind(1) == TokenKind::Open(Delim::Paren) {
            let unsafe_span = self.token.span;
            self.bump();
            self.expect(TokenKind::Open(Delim::Paren))?;
            let path = self.parse_path(PathStyle::Mod)?;
            let args = self.parse_attr_args()?;
            self.expect(TokenKind::Close(Delim::Paren))?;
            return Ok(AttrItem {
                unsafety: Safety::Unsafe(unsafe_span),
                path,
                args,
            });
        }
        let path = self.parse_path(PathStyle::Mod)?;
        let args = self.parse_attr_args()?;
        Ok(AttrItem {
            unsafety: Safety::Default,
            path,
            args,
        })
    }

    fn parse_attr_args(&mut self) -> PResult<AttrArgs> {
        Ok(match self.token.kind {
            TokenKind::Open(Delim::Paren | Delim::Bracket | Delim::Brace) => {
                AttrArgs::Delimited(self.parse_delim_args()?)
            }
            TokenKind::Eq => {
                let eq = self.token.span;
                self.bump();
                AttrArgs::Eq(eq, self.parse_expr()?)
            }
            _ => AttrArgs::Empty,
        })
    }

    // -----------------------------------------------------------------------------------------
    // Visibility

    pub fn parse_visibility(&mut self) -> PResult<Visibility> {
        if !self.check_keyword(kw::Pub) {
            // `crate` as a visibility was removed from the language; `crate::` starts a path.
            return Ok(Visibility::inherited(self.token.span.shrink_to_lo()));
        }
        let lo = self.token.span;
        self.bump();
        if self.check(TokenKind::Open(Delim::Paren)) {
            // `pub(crate)`, `pub(self)`, `pub(super)`, `pub(in path)`; but `pub (u8, u8)` in a
            // tuple struct is a public field of a tuple type.
            let t1 = self.look(1);
            let t2 = self.look(2);
            if t1.is_keyword(kw::In) {
                self.bump();
                self.bump();
                let path = self.parse_path(PathStyle::Mod)?;
                self.expect(TokenKind::Close(Delim::Paren))?;
                return Ok(Visibility {
                    kind: VisibilityKind::Restricted {
                        path: Box::new(path),
                        id: NodeId::DUMMY,
                        shorthand: false,
                    },
                    span: lo.to(self.prev_token.span),
                });
            }
            if (t1.is_keyword(kw::Crate)
                || t1.is_keyword(kw::SelfLower)
                || t1.is_keyword(kw::Super))
                && t2.kind == TokenKind::Close(Delim::Paren)
            {
                self.bump();
                let ident = Ident::new(self.token.sym, self.token.span);
                self.bump();
                self.bump();
                return Ok(Visibility {
                    kind: VisibilityKind::Restricted {
                        path: Box::new(Path::from_ident(ident)),
                        id: NodeId::DUMMY,
                        shorthand: true,
                    },
                    span: lo.to(self.prev_token.span),
                });
            }
        }
        Ok(Visibility {
            kind: VisibilityKind::Public,
            span: lo,
        })
    }

    // -----------------------------------------------------------------------------------------
    // Literals

    /// Is the current token a literal (including `true`/`false`)?
    pub fn check_lit(&self) -> bool {
        self.token.is_lit() || self.check_keyword(kw::True) || self.check_keyword(kw::False)
    }

    pub fn parse_lit(&mut self) -> PResult<Lit> {
        let t = self.token;
        let lit = match t.kind {
            TokenKind::Literal(kind) => Lit {
                kind,
                symbol: t.sym,
                suffix: t.suffix,
                span: t.span,
            },
            TokenKind::Ident if t.sym == kw::True || t.sym == kw::False => Lit {
                kind: LitKind::Bool,
                symbol: t.sym,
                suffix: kw::Empty,
                span: t.span,
            },
            _ => return Err(self.expected("literal")),
        };
        self.bump();
        Ok(lit)
    }

    /// A string literal, as in `extern "C"`.
    pub fn parse_str_lit(&mut self) -> Option<StrLit> {
        let t = self.token;
        match t.kind {
            TokenKind::Literal(style @ (LitKind::Str | LitKind::StrRaw(_))) => {
                self.bump();
                Some(StrLit {
                    symbol: t.sym,
                    suffix: t.suffix,
                    style,
                    span: t.span,
                })
            }
            _ => None,
        }
    }

    // -----------------------------------------------------------------------------------------
    // Crates

    /// Parses a whole file: inner attributes, then items until the end.
    pub fn parse_crate(&mut self) -> Crate {
        let lo = self.token.span;
        let attrs = match self.parse_inner_attributes() {
            Ok(attrs) => attrs,
            Err(e) => {
                self.emit(e);
                Vec::new()
            }
        };
        let items = self.parse_items_until(TokenKind::Eof);
        Crate {
            attrs,
            items,
            span: lo.to(self.token.span),
        }
    }

    /// Items until `end` (`Eof` or the `}` of an inline module), not eaten. Errors are
    /// reported and skipped over.
    pub fn parse_items_until(&mut self, end: TokenKind) -> Vec<P<Item>> {
        let mut items = Vec::new();
        while !self.check(end) && !self.check(TokenKind::Eof) {
            let before = self.pos;
            match self.parse_item() {
                Ok(Some(item)) => items.push(item),
                Ok(None) => {
                    let err = self.expected("item");
                    self.emit(err);
                    self.recover_to_semi_or_close();
                    if self.token.is_close() && !self.check(end) {
                        self.bump();
                    }
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                    if self.token.is_close() && !self.check(end) {
                        self.bump();
                    }
                }
            }
            if self.pos == before {
                self.bump();
            }
        }
        items
    }
}

/// How generic arguments are written in a path.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PathStyle {
    /// In expressions and patterns: `Vec::<u8>::new()`, only with `::`.
    Expr,
    /// In types: `Vec<u8>`, `Fn(u8) -> u8`.
    Type,
    /// In `use`, visibilities, attributes and macro calls: no generic arguments.
    Mod,
}

/// Parses a file's tokens into a crate (well, a module's items). Reports errors to `dcx`.
pub fn parse_file(tokens: &[Token], edition: Edition, dcx: &DiagCtxt) -> Crate {
    let mut p = Parser::new(tokens, edition, dcx);
    p.parse_crate()
}
