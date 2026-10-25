//! Items: functions, types, traits, impls, modules, `use`, macros.

use super::{PResult, Parser, PathStyle};
use crate::ast::*;
use crate::token::{Delim, Token, TokenKind};
use hyprc_span::{Ident, Span, kw};

/// Where an item is: some kinds only exist in some places, and function parameters must be
/// named in some places but not others.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ItemCtx {
    Free,
    Trait,
    Impl,
    Foreign,
}

impl Parser<'_> {
    pub fn parse_item(&mut self) -> PResult<Option<P<Item>>> {
        let attrs = self.parse_outer_attributes()?;
        self.parse_item_with_attrs(attrs, ItemCtx::Free)
    }

    pub(crate) fn parse_item_with_attrs(
        &mut self,
        attrs: Vec<Attribute>,
        ctx: ItemCtx,
    ) -> PResult<Option<P<Item>>> {
        let lo = attrs.first().map_or(self.token.span, |a| a.span);
        let start = self.snapshot();
        let vis = self.parse_visibility()?;
        let (mut attrs, vis) = (attrs, vis);
        match self.parse_item_kind(&mut attrs, &vis, ctx)? {
            Some((ident, kind)) => {
                let span = lo.to(self.prev_token.span);
                Ok(Some(Box::new(Item {
                    attrs,
                    id: NodeId::DUMMY,
                    span,
                    vis,
                    ident,
                    kind,
                })))
            }
            None => {
                if !attrs.is_empty() || !matches!(vis.kind, VisibilityKind::Inherited) {
                    return Err(self.expected("item after attributes"));
                }
                self.restore(start);
                Ok(None)
            }
        }
    }

    /// Does an item start here? (For statements: items and expressions share keywords.)
    pub(crate) fn is_item_start(&self) -> bool {
        let t = self.token;
        if t.kind != TokenKind::Ident {
            return false;
        }
        let s = t.sym;
        if s == kw::Use
            || s == kw::Struct
            || s == kw::Enum
            || s == kw::Trait
            || s == kw::Impl
            || s == kw::Mod
            || s == kw::Type
            || s == kw::Pub
            || s == kw::Fn
        {
            return true;
        }
        if s == kw::Extern {
            // `extern crate`, `extern fn`, `extern "C" fn`, `extern { … }`, `extern "C" { … }`
            return true;
        }
        if s == kw::Static {
            // `static ||` and `static move ||` are coroutine closures.
            let n = self.look(1);
            return !(n.kind == TokenKind::Or
                || n.kind == TokenKind::OrOr
                || n.is_keyword(kw::Move));
        }
        if s == kw::Const {
            // `const {` is an inline const block, `const ||` a const closure.
            return !matches!(
                self.look_kind(1),
                TokenKind::Open(Delim::Brace) | TokenKind::Or | TokenKind::OrOr
            ) && !self.is_keyword_ahead(1, &[kw::Move, kw::Static]);
        }
        if s == kw::Unsafe {
            // `unsafe {` is a block.
            return self.is_keyword_ahead(
                1,
                &[
                    kw::Fn,
                    kw::Impl,
                    kw::Trait,
                    kw::Extern,
                    kw::Auto,
                    kw::Mod,
                    kw::Const,
                    kw::Async,
                    kw::Safe,
                    kw::Static,
                ],
            );
        }
        if s == kw::Async || s == kw::Gen {
            return self.check_fn_front_matter();
        }
        if s == kw::Union {
            return self.ident_ahead(1);
        }
        if s == kw::Auto {
            return self.is_keyword_ahead(1, &[kw::Trait]);
        }
        if s == kw::MacroRules {
            return self.look_kind(1) == TokenKind::Not && self.look(2).is_ident();
        }
        if s == kw::Macro {
            return self.look(1).is_ident();
        }
        if s == kw::Default {
            return self.is_keyword_ahead(
                1,
                &[
                    kw::Fn,
                    kw::Impl,
                    kw::Unsafe,
                    kw::Const,
                    kw::Type,
                    kw::Async,
                    kw::Extern,
                ],
            );
        }
        if s == kw::Safe {
            return self.is_keyword_ahead(1, &[kw::Fn, kw::Static]);
        }
        false
    }

    /// `const`, `async`, `gen`, `unsafe`, `safe`, `extern "abi"` in any order, then `fn`.
    pub(crate) fn check_fn_front_matter(&self) -> bool {
        let mut i = 0;
        loop {
            let t = self.look(i);
            if t.kind != TokenKind::Ident {
                return false;
            }
            match t.sym {
                kw::Fn => return true,
                kw::Const | kw::Unsafe | kw::Safe | kw::Async | kw::Gen => i += 1,
                kw::Extern => {
                    i += 1;
                    if matches!(self.look_kind(i), TokenKind::Literal(_)) {
                        i += 1;
                    }
                }
                _ => return false,
            }
            if i > 6 {
                return false;
            }
        }
    }

    fn parse_defaultness(&mut self) -> Defaultness {
        if self.check_keyword(kw::Final)
            && self.is_keyword_ahead(
                1,
                &[
                    kw::Fn,
                    kw::Unsafe,
                    kw::Const,
                    kw::Async,
                    kw::Extern,
                    kw::Safe,
                ],
            )
        {
            let span = self.token.span;
            self.bump();
            return Defaultness::FinalKw(span);
        }
        if self.check_keyword(kw::Default)
            && self.is_keyword_ahead(
                1,
                &[
                    kw::Fn,
                    kw::Impl,
                    kw::Unsafe,
                    kw::Const,
                    kw::Type,
                    kw::Async,
                    kw::Extern,
                    kw::Safe,
                    kw::Pub,
                ],
            )
        {
            let span = self.token.span;
            self.bump();
            Defaultness::Default(span)
        } else {
            Defaultness::Final
        }
    }

    /// Parses what follows the visibility. `None` if no item starts here.
    fn parse_item_kind(
        &mut self,
        attrs: &mut Vec<Attribute>,
        vis: &Visibility,
        ctx: ItemCtx,
    ) -> PResult<Option<(Ident, ItemKind)>> {
        let none = Ident::new(kw::Empty, self.token.span.shrink_to_lo());
        let defaultness = self.parse_defaultness();

        if self.eat_keyword(kw::Use) {
            let tree = self.parse_use_tree()?;
            self.expect(TokenKind::Semi)?;
            return Ok(Some((none, ItemKind::Use(tree))));
        }

        if self.check_fn_front_matter() {
            let (ident, f) = self.parse_fn(attrs, ctx, defaultness)?;
            return Ok(Some((ident, ItemKind::Fn(Box::new(f)))));
        }

        if self.check_keyword(kw::Extern) && self.is_keyword_ahead(1, &[kw::Crate]) {
            self.bump();
            self.bump();
            let orig = if self.eat_keyword(kw::SelfLower) {
                Ident::new(kw::SelfLower, self.prev_token.span)
            } else {
                self.parse_ident()?
            };
            let (ident, orig_name) = if self.eat_keyword(kw::As) {
                (self.parse_ident_or_underscore()?, Some(orig.name))
            } else {
                (orig, None)
            };
            self.expect(TokenKind::Semi)?;
            return Ok(Some((ident, ItemKind::ExternCrate(orig_name))));
        }

        // `extern "C" { … }` and `unsafe extern "C" { … }`.
        {
            let unsafe_first =
                self.check_keyword(kw::Unsafe) && self.is_keyword_ahead(1, &[kw::Extern]);
            let ext_at = if unsafe_first { 1 } else { 0 };
            if self.is_keyword_ahead(ext_at, &[kw::Extern]) {
                let after = if matches!(self.look_kind(ext_at + 1), TokenKind::Literal(_)) {
                    ext_at + 2
                } else {
                    ext_at + 1
                };
                if self.look_kind(after) == TokenKind::Open(Delim::Brace) {
                    let safety = if unsafe_first {
                        let s = self.token.span;
                        self.bump();
                        Safety::Unsafe(s)
                    } else {
                        Safety::Default
                    };
                    let extern_span = self.token.span;
                    self.bump();
                    let abi = self.parse_str_lit();
                    self.expect(TokenKind::Open(Delim::Brace))?;
                    attrs.extend(self.parse_inner_attributes()?);
                    let mut items = Vec::new();
                    while !self.check(TokenKind::Close(Delim::Brace)) && !self.check(TokenKind::Eof)
                    {
                        match self.parse_foreign_item() {
                            Ok(Some(item)) => items.push(item),
                            Ok(None) => {
                                let e = self.expected("item");
                                self.emit(e);
                                self.recover_to_semi_or_close();
                            }
                            Err(e) => {
                                self.emit(e);
                                self.recover_to_semi_or_close();
                            }
                        }
                    }
                    self.expect(TokenKind::Close(Delim::Brace))?;
                    return Ok(Some((
                        none,
                        ItemKind::ForeignMod(ForeignMod {
                            extern_span,
                            safety,
                            abi,
                            items,
                        }),
                    )));
                }
            }
        }

        // `static`, `unsafe static`, `safe static` (the last two in extern blocks).
        if self.check_keyword(kw::Static)
            || ((self.check_keyword(kw::Unsafe) || self.check_keyword(kw::Safe))
                && self.is_keyword_ahead(1, &[kw::Static]))
        {
            let safety = if self.eat_keyword(kw::Unsafe) {
                Safety::Unsafe(self.prev_token.span)
            } else if self.eat_keyword(kw::Safe) {
                Safety::Safe(self.prev_token.span)
            } else {
                Safety::Default
            };
            self.expect_keyword(kw::Static)?;
            let mutability = if self.eat_keyword(kw::Mut) {
                Mutability::Mut
            } else {
                Mutability::Not
            };
            let ident = self.parse_ident()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            let expr = if self.eat(TokenKind::Eq) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            self.expect(TokenKind::Semi)?;
            return Ok(Some((
                ident,
                ItemKind::Static(Box::new(StaticItem {
                    ty,
                    safety,
                    mutability,
                    expr,
                })),
            )));
        }

        // `const NAME: T = …;` and `const _: T = …;`
        if self.check_keyword(kw::Const)
            && (self.ident_ahead(1) || self.is_keyword_ahead(1, &[kw::Underscore]))
            && !self.is_keyword_ahead(1, &[kw::Impl, kw::Trait, kw::Auto, kw::Unsafe])
        {
            self.bump();
            let ident = self.parse_ident_or_underscore()?;
            let mut generics = self.parse_generics()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            let expr = if self.eat(TokenKind::Eq) {
                Some(self.parse_expr()?)
            } else {
                None
            };
            generics.where_clause = self.parse_where_clause()?;
            self.expect(TokenKind::Semi)?;
            return Ok(Some((
                ident,
                ItemKind::Const(Box::new(ConstItem {
                    defaultness,
                    generics,
                    ty,
                    expr,
                })),
            )));
        }

        // Traits: `[impl(restr)] [const] [unsafe] [auto] trait`.
        {
            let mut i = 0;
            if self.check_keyword(kw::Impl) && self.look_kind(1) == TokenKind::Open(Delim::Paren) {
                // `impl(crate) trait`: skip the restriction when looking ahead.
                let mut depth = 0;
                loop {
                    match self.look_kind(i) {
                        TokenKind::Open(_) => depth += 1,
                        TokenKind::Close(_) => {
                            depth -= 1;
                            if depth == 0 {
                                i += 1;
                                break;
                            }
                        }
                        TokenKind::Eof => break,
                        _ => {}
                    }
                    i += 1;
                }
            }
            while self.is_keyword_ahead(i, &[kw::Const, kw::Unsafe, kw::Auto]) {
                i += 1;
            }
            if self.is_keyword_ahead(i, &[kw::Trait]) {
                return self.parse_trait(attrs).map(Some);
            }
        }

        // Impls: `[default] [const] [unsafe] impl`.
        {
            let mut i = 0;
            while self.is_keyword_ahead(i, &[kw::Const, kw::Unsafe]) {
                i += 1;
            }
            if self.is_keyword_ahead(i, &[kw::Impl]) {
                let imp = self.parse_impl(attrs, defaultness)?;
                return Ok(Some((none, ItemKind::Impl(Box::new(imp)))));
            }
        }

        if self.check_keyword(kw::Mod)
            || (self.check_keyword(kw::Unsafe) && self.is_keyword_ahead(1, &[kw::Mod]))
        {
            let safety = if self.eat_keyword(kw::Unsafe) {
                Safety::Unsafe(self.prev_token.span)
            } else {
                Safety::Default
            };
            self.expect_keyword(kw::Mod)?;
            let ident = self.parse_ident()?;
            if self.eat(TokenKind::Semi) {
                return Ok(Some((ident, ItemKind::Mod(safety, ModKind::Unloaded))));
            }
            let lo = self.token.span;
            self.expect(TokenKind::Open(Delim::Brace))?;
            attrs.extend(self.parse_inner_attributes()?);
            let items = self.parse_items_until(TokenKind::Close(Delim::Brace));
            self.expect(TokenKind::Close(Delim::Brace))?;
            let span = lo.to(self.prev_token.span);
            return Ok(Some((
                ident,
                ItemKind::Mod(
                    safety,
                    ModKind::Loaded {
                        items,
                        inline: true,
                        span,
                    },
                ),
            )));
        }

        if self.eat_keyword(kw::Type) {
            let (ident, alias) = self.parse_type_alias(defaultness)?;
            return Ok(Some((ident, ItemKind::TyAlias(Box::new(alias)))));
        }

        if self.eat_keyword(kw::Enum) {
            let ident = self.parse_ident()?;
            let mut generics = self.parse_generics()?;
            generics.where_clause = self.parse_where_clause()?;
            self.expect(TokenKind::Open(Delim::Brace))?;
            let mut variants = Vec::new();
            while !self.check(TokenKind::Close(Delim::Brace)) {
                variants.push(self.parse_variant()?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::Close(Delim::Brace))?;
            return Ok(Some((
                ident,
                ItemKind::Enum(EnumDef { variants }, generics),
            )));
        }

        if self.check_keyword(kw::Struct) {
            self.bump();
            let ident = self.parse_ident()?;
            let (data, generics) = self.parse_struct_body(true)?;
            return Ok(Some((ident, ItemKind::Struct(data, generics))));
        }

        if self.check_keyword(kw::Union) && self.ident_ahead(1) {
            self.bump();
            let ident = self.parse_ident()?;
            let (data, generics) = self.parse_struct_body(false)?;
            return Ok(Some((ident, ItemKind::Union(data, generics))));
        }

        if self.check_keyword(kw::MacroRules)
            && self.look_kind(1) == TokenKind::Not
            && self.look(2).is_ident()
        {
            self.bump();
            self.bump();
            let ident = self.parse_ident_any()?;
            let body = self.parse_delim_args()?;
            if body.delim != Delim::Brace {
                self.expect(TokenKind::Semi)?;
            }
            return Ok(Some((
                ident,
                ItemKind::MacroDef(MacroDef {
                    body,
                    macro_rules: true,
                }),
            )));
        }

        if self.check_keyword(kw::Macro) && self.look(1).is_ident() {
            self.bump();
            let ident = self.parse_ident_any()?;
            let body = if self.check(TokenKind::Open(Delim::Brace)) {
                self.parse_delim_args()?
            } else {
                // `macro m(args) { body }` is one rule: `(args) => { body }`.
                let args = self.parse_delim_args()?;
                if args.delim != Delim::Paren {
                    return Err(
                        self.error_at(args.open, "expected `(` or `{` after the macro's name")
                    );
                }
                let body = self.parse_delim_args()?;
                let mut tokens: Vec<Token> =
                    Vec::with_capacity(args.tokens.0.len() + body.tokens.0.len() + 5);
                tokens.push(Token::new(TokenKind::Open(Delim::Paren), args.open));
                tokens.extend_from_slice(args.tokens.tokens());
                tokens.push(Token::new(TokenKind::Close(Delim::Paren), args.close));
                tokens.push(Token::new(TokenKind::FatArrow, args.close));
                tokens.push(Token::new(TokenKind::Open(body.delim), body.open));
                tokens.extend_from_slice(body.tokens.tokens());
                tokens.push(Token::new(TokenKind::Close(body.delim), body.close));
                DelimArgs {
                    open: args.open,
                    close: body.close,
                    delim: Delim::Brace,
                    tokens: TokenStream::new(tokens),
                }
            };
            return Ok(Some((
                ident,
                ItemKind::MacroDef(MacroDef {
                    body,
                    macro_rules: false,
                }),
            )));
        }

        // `builtin # global_asm(…)`, what `global_asm!` expands to.
        if self.check_keyword(kw::Builtin) && self.look_kind(1) == TokenKind::Pound {
            let lo = self.token.span;
            self.bump();
            self.bump();
            let _name = self.parse_ident_any()?;
            self.expect(TokenKind::Open(Delim::Paren))?;
            let tokens = self.collect_until_close_paren();
            self.expect(TokenKind::Close(Delim::Paren))?;
            self.eat(TokenKind::Semi);
            let asm = InlineAsm {
                kind: AsmMacro::GlobalAsm,
                tokens,
                span: lo.to(self.prev_token.span),
            };
            return Ok(Some((none, ItemKind::GlobalAsm(Box::new(asm)))));
        }

        // A macro call: `path! { … }`, `path!(…);`.
        if self.is_macro_call_start() {
            let mac = self.parse_mac_call()?;
            if mac.args.delim != Delim::Brace {
                self.expect(TokenKind::Semi)?;
            }
            return Ok(Some((none, ItemKind::MacCall(Box::new(mac)))));
        }

        if !matches!(vis.kind, VisibilityKind::Inherited) || defaultness != Defaultness::Final {
            return Err(self.expected("item"));
        }
        let _ = ctx;
        Ok(None)
    }

    /// A path followed by `!` and a delimiter (or `!` and an identifier for `macro_rules!`
    /// lookalikes, which are errors anyway).
    pub(crate) fn is_macro_call_start(&self) -> bool {
        let mut i = 0;
        if self.look_kind(0) == TokenKind::PathSep {
            i = 1;
        }
        loop {
            let t = self.look(i);
            // Keywords lex as identifiers: `if !(x)` is not a macro call.
            if !(t.is_non_reserved_ident(self.edition2018())
                || (t.kind == TokenKind::Ident && t.sym.is_path_segment_keyword()))
            {
                return false;
            }
            match self.look_kind(i + 1) {
                TokenKind::PathSep => i += 2,
                TokenKind::Not => {
                    return matches!(self.look_kind(i + 2), TokenKind::Open(_));
                }
                _ => return false,
            }
        }
    }

    pub(crate) fn parse_mac_call(&mut self) -> PResult<MacCall> {
        let path = self.parse_path(PathStyle::Mod)?;
        self.expect(TokenKind::Not)?;
        let args = self.parse_delim_args()?;
        Ok(MacCall { path, args })
    }

    // -----------------------------------------------------------------------------------------
    // `use`

    fn parse_use_tree(&mut self) -> PResult<UseTree> {
        let lo = self.token.span;
        let mut prefix = Path {
            span: lo.shrink_to_lo(),
            segments: Vec::new(),
        };
        // `use {a, b}`, `use *`, `use ::{a, b}`, `use ::*`.
        if self.check(TokenKind::Open(Delim::Brace))
            || self.check(TokenKind::Star)
            || (self.check(TokenKind::PathSep)
                && matches!(
                    self.look_kind(1),
                    TokenKind::Open(Delim::Brace) | TokenKind::Star
                ))
        {
            if self.eat(TokenKind::PathSep) {
                prefix.segments.push(PathSegment::from_ident(Ident::new(
                    kw::PathRoot,
                    self.prev_token.span,
                )));
            }
            let kind = self.parse_use_tree_glob_or_nested()?;
            return Ok(UseTree {
                prefix,
                kind,
                span: lo.to(self.prev_token.span),
            });
        }
        prefix = self.parse_path_until_use_glob()?;
        let kind = if self.eat(TokenKind::PathSep) {
            self.parse_use_tree_glob_or_nested()?
        } else if self.eat_keyword(kw::As) {
            UseTreeKind::Simple(Some(self.parse_ident_or_underscore()?))
        } else {
            UseTreeKind::Simple(None)
        };
        Ok(UseTree {
            prefix,
            kind,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_use_tree_glob_or_nested(&mut self) -> PResult<UseTreeKind> {
        if self.eat(TokenKind::Star) {
            return Ok(UseTreeKind::Glob);
        }
        let lo = self.token.span;
        self.expect(TokenKind::Open(Delim::Brace))?;
        let mut items = Vec::new();
        while !self.check(TokenKind::Close(Delim::Brace)) {
            items.push((self.parse_use_tree()?, NodeId::DUMMY));
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok(UseTreeKind::Nested {
            items,
            span: lo.to(self.prev_token.span),
        })
    }

    /// A `use` path: segments up to (not including) a `::` followed by `*` or `{`.
    fn parse_path_until_use_glob(&mut self) -> PResult<Path> {
        let lo = self.token.span;
        let mut segments = Vec::new();
        if self.eat(TokenKind::PathSep) {
            segments.push(PathSegment::from_ident(Ident::new(
                kw::PathRoot,
                self.prev_token.span,
            )));
        }
        loop {
            segments.push(PathSegment::from_ident(self.parse_path_segment_ident()?));
            if self.check(TokenKind::PathSep)
                && !matches!(
                    self.look_kind(1),
                    TokenKind::Star | TokenKind::Open(Delim::Brace)
                )
            {
                self.bump();
            } else {
                break;
            }
        }
        Ok(Path {
            span: lo.to(self.prev_token.span),
            segments,
        })
    }

    // -----------------------------------------------------------------------------------------
    // Functions

    fn parse_fn_header(&mut self) -> PResult<FnHeader> {
        let mut header = FnHeader::default();
        loop {
            let span = self.token.span;
            if self.eat_keyword(kw::Const) {
                header.constness = Constness::Yes(span);
            } else if self.eat_keyword(kw::Async) {
                header.coroutine_kind = Some(match header.coroutine_kind {
                    Some(CoroutineKind::Gen { .. }) => CoroutineKind::AsyncGen { span },
                    _ => CoroutineKind::Async { span },
                });
            } else if self.eat_keyword(kw::Gen) {
                header.coroutine_kind = Some(match header.coroutine_kind {
                    Some(CoroutineKind::Async { .. }) => CoroutineKind::AsyncGen { span },
                    _ => CoroutineKind::Gen { span },
                });
            } else if self.eat_keyword(kw::Unsafe) {
                header.safety = Safety::Unsafe(span);
            } else if self.eat_keyword(kw::Safe) {
                header.safety = Safety::Safe(span);
            } else if self.eat_keyword(kw::Extern) {
                header.ext = match self.parse_str_lit() {
                    Some(abi) => Extern::Explicit(abi, span.to(abi.span)),
                    None => Extern::Implicit(span),
                };
            } else {
                break;
            }
        }
        self.expect_keyword(kw::Fn)?;
        Ok(header)
    }

    fn parse_fn(
        &mut self,
        attrs: &mut Vec<Attribute>,
        ctx: ItemCtx,
        defaultness: Defaultness,
    ) -> PResult<(Ident, Fn)> {
        let lo = self.token.span;
        let header = self.parse_fn_header()?;
        let ident = self.parse_ident()?;
        let mut generics = self.parse_generics()?;
        // Parameter names may be left out in trait methods in the 2015 edition.
        let req_name = !(ctx == ItemCtx::Trait && self.edition == super::Edition::E2015);
        let decl = self.parse_fn_decl(req_name, true)?;
        generics.where_clause = self.parse_where_clause()?;
        let sig_span = lo.to(self.prev_token.span);
        let body = if self.eat(TokenKind::Semi) {
            None
        } else {
            let (inner, block) = self.parse_block_with_inner_attrs()?;
            attrs.extend(inner);
            Some(block)
        };
        Ok((
            ident,
            Fn {
                defaultness,
                generics,
                sig: FnSig {
                    header,
                    decl,
                    span: sig_span,
                },
                body,
            },
        ))
    }

    /// `(params) -> ret`
    pub(crate) fn parse_fn_decl(&mut self, req_name: bool, allow_self: bool) -> PResult<P<FnDecl>> {
        self.expect(TokenKind::Open(Delim::Paren))?;
        let mut inputs = Vec::new();
        let mut first = true;
        while !self.check(TokenKind::Close(Delim::Paren)) {
            let attrs = self.parse_outer_attributes()?;
            let param = if first
                && allow_self
                && let Some(p) = self.parse_self_param(attrs.clone())?
            {
                p
            } else {
                self.parse_param(attrs, req_name)?
            };
            inputs.push(param);
            first = false;
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Paren))?;
        let output = self.parse_ret_ty(true)?;
        Ok(Box::new(FnDecl { inputs, output }))
    }

    pub(crate) fn parse_ret_ty(&mut self, allow_plus: bool) -> PResult<FnRetTy> {
        if self.eat(TokenKind::RArrow) {
            let ty = if allow_plus {
                self.parse_ty()?
            } else {
                self.parse_ty_no_plus()?
            };
            Ok(FnRetTy::Ty(ty))
        } else {
            Ok(FnRetTy::Default(self.token.span.shrink_to_lo()))
        }
    }

    fn parse_self_param(&mut self, attrs: Vec<Attribute>) -> PResult<Option<Param>> {
        let lo = self.token.span;
        let is_self = |p: &Self, n: usize| {
            p.look(n).is_keyword(kw::SelfLower) && p.look_kind(n + 1) != TokenKind::PathSep
        };
        let self_ident = |p: &Self, n: usize| Ident::new(kw::SelfLower, p.look(n).span);
        let mk = |p: &mut Self, ident: Ident, mutbl: Mutability, ty: P<Ty>| Param {
            attrs: attrs.clone(),
            ty,
            pat: Box::new(Pat {
                id: NodeId::DUMMY,
                kind: PatKind::Ident(
                    BindingMode {
                        by_ref: ByRef::No,
                        mutbl,
                    },
                    ident,
                    None,
                ),
                span: ident.span,
            }),
            id: NodeId::DUMMY,
            span: lo.to(p.prev_token.span),
        };
        let implicit = |span: Span| {
            Box::new(Ty {
                id: NodeId::DUMMY,
                kind: TyKind::ImplicitSelf,
                span,
            })
        };

        // `&self`, `&mut self`, `&'a self`, `&'a mut self`, `&pin mut self`, `&pin const self`.
        if self.check(TokenKind::And) {
            let (lt, mutbl, pinned, n) = if is_self(self, 1) {
                (None, Mutability::Not, false, 1)
            } else if self.look(1).is_keyword(kw::Mut) && is_self(self, 2) {
                (None, Mutability::Mut, false, 2)
            } else if self.look(1).is_lifetime() && is_self(self, 2) {
                (Some(1), Mutability::Not, false, 2)
            } else if self.look(1).is_lifetime()
                && self.look(2).is_keyword(kw::Mut)
                && is_self(self, 3)
            {
                (Some(1), Mutability::Mut, false, 3)
            } else if self.look(1).sym.as_str() == "pin"
                && self.look(1).kind == TokenKind::Ident
                && (self.look(2).is_keyword(kw::Mut) || self.look(2).is_keyword(kw::Const))
                && is_self(self, 3)
            {
                let m = if self.look(2).is_keyword(kw::Mut) {
                    Mutability::Mut
                } else {
                    Mutability::Not
                };
                (None, m, true, 3)
            } else {
                return Ok(None);
            };
            let lifetime = lt.map(|n| Lifetime {
                id: NodeId::DUMMY,
                ident: Ident::new(self.look(n).sym, self.look(n).span),
            });
            let ident = self_ident(self, n);
            for _ in 0..=n {
                self.bump();
            }
            let span = lo.to(self.prev_token.span);
            let inner = MutTy {
                ty: implicit(span),
                mutbl,
            };
            let kind = if pinned {
                TyKind::PinnedRef(lifetime, inner)
            } else {
                TyKind::Ref(lifetime, inner)
            };
            let ty = Box::new(Ty {
                id: NodeId::DUMMY,
                kind,
                span,
            });
            return Ok(Some(mk(self, ident, Mutability::Not, ty)));
        }
        // `self`, `mut self`, `self: T`, `mut self: T`.
        let (mutbl, n) = if is_self(self, 0) {
            (Mutability::Not, 0)
        } else if self.check_keyword(kw::Mut) && is_self(self, 1) {
            (Mutability::Mut, 1)
        } else {
            return Ok(None);
        };
        let ident = self_ident(self, n);
        for _ in 0..=n {
            self.bump();
        }
        let ty = if self.eat(TokenKind::Colon) {
            self.parse_ty()?
        } else {
            implicit(ident.span)
        };
        Ok(Some(mk(self, ident, mutbl, ty)))
    }

    /// `pat: Ty`, or just `Ty` where names are optional, or `...` (C variadics).
    pub(crate) fn parse_param(&mut self, attrs: Vec<Attribute>, req_name: bool) -> PResult<Param> {
        let lo = self.token.span;
        if self.check(TokenKind::DotDotDot) {
            self.bump();
            let span = self.prev_token.span;
            return Ok(Param {
                attrs,
                ty: Box::new(Ty {
                    id: NodeId::DUMMY,
                    kind: TyKind::CVarArgs,
                    span,
                }),
                pat: Box::new(Pat {
                    id: NodeId::DUMMY,
                    kind: PatKind::Wild,
                    span,
                }),
                id: NodeId::DUMMY,
                span,
            });
        }
        let named = req_name || self.is_named_param();
        let (pat, ty) = if named {
            let pat = self.parse_pat_no_top_alt()?;
            self.expect(TokenKind::Colon)?;
            let ty = if self.check(TokenKind::DotDotDot) {
                self.bump();
                Box::new(Ty {
                    id: NodeId::DUMMY,
                    kind: TyKind::CVarArgs,
                    span: self.prev_token.span,
                })
            } else {
                self.parse_ty()?
            };
            (pat, ty)
        } else {
            let ty = self.parse_ty()?;
            let pat = Box::new(Pat {
                id: NodeId::DUMMY,
                kind: PatKind::Wild,
                span: ty.span.shrink_to_lo(),
            });
            (pat, ty)
        };
        Ok(Param {
            attrs,
            ty,
            pat,
            id: NodeId::DUMMY,
            span: lo.to(self.prev_token.span),
        })
    }

    /// Where names are optional (`fn(u8)` types, 2015 trait methods): `name:` or `&name:` or
    /// `mut name:` starts a named parameter.
    fn is_named_param(&self) -> bool {
        let mut depth: u32 = 0;
        let mut idx = 0;
        while idx < 40 {
            match self.look_kind(idx) {
                TokenKind::Open(Delim::Paren) | TokenKind::Open(Delim::Bracket) => depth += 1,
                TokenKind::Close(Delim::Paren) | TokenKind::Close(Delim::Bracket) => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                }
                TokenKind::Comma | TokenKind::Eof => {
                    if depth == 0 {
                        return false;
                    }
                }
                TokenKind::Colon if depth == 0 => return true,
                _ => {}
            }
            idx += 1;
        }
        false
    }

    // -----------------------------------------------------------------------------------------
    // Structs, enums, unions

    /// After the name: generics, where clause and fields, and `;` when needed.
    fn parse_struct_body(&mut self, allow_tuple: bool) -> PResult<(VariantData, Generics)> {
        let mut generics = self.parse_generics()?;
        if self.check_keyword(kw::Where) {
            generics.where_clause = self.parse_where_clause()?;
            if self.eat(TokenKind::Semi) {
                return Ok((VariantData::Unit(NodeId::DUMMY), generics));
            }
            let fields = self.parse_record_fields()?;
            return Ok((VariantData::Struct { fields }, generics));
        }
        if allow_tuple && self.eat(TokenKind::Semi) {
            return Ok((VariantData::Unit(NodeId::DUMMY), generics));
        }
        if allow_tuple && self.check(TokenKind::Open(Delim::Paren)) {
            let fields = self.parse_tuple_fields()?;
            generics.where_clause = self.parse_where_clause()?;
            self.expect(TokenKind::Semi)?;
            return Ok((VariantData::Tuple(fields, NodeId::DUMMY), generics));
        }
        let fields = self.parse_record_fields()?;
        Ok((VariantData::Struct { fields }, generics))
    }

    fn parse_record_fields(&mut self) -> PResult<Vec<FieldDef>> {
        self.expect(TokenKind::Open(Delim::Brace))?;
        let mut fields = Vec::new();
        while !self.check(TokenKind::Close(Delim::Brace)) {
            let attrs = self.parse_outer_attributes()?;
            let lo = attrs.first().map_or(self.token.span, |a| a.span);
            let vis = self.parse_visibility()?;
            let safety = if self.check_keyword(kw::Unsafe) && self.ident_ahead(1) {
                self.bump();
                Safety::Unsafe(self.prev_token.span)
            } else {
                Safety::Default
            };
            let ident = self.parse_ident_or_underscore()?;
            self.expect(TokenKind::Colon)?;
            let ty = self.parse_ty()?;
            let default = if self.eat(TokenKind::Eq) {
                Some(AnonConst {
                    id: NodeId::DUMMY,
                    value: self.parse_expr()?,
                })
            } else {
                None
            };
            fields.push(FieldDef {
                attrs,
                id: NodeId::DUMMY,
                span: lo.to(self.prev_token.span),
                vis,
                safety,
                ident: Some(ident),
                ty,
                default,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok(fields)
    }

    fn parse_tuple_fields(&mut self) -> PResult<Vec<FieldDef>> {
        self.expect(TokenKind::Open(Delim::Paren))?;
        let mut fields = Vec::new();
        while !self.check(TokenKind::Close(Delim::Paren)) {
            let attrs = self.parse_outer_attributes()?;
            let lo = attrs.first().map_or(self.token.span, |a| a.span);
            let vis = self.parse_visibility()?;
            let ty = self.parse_ty()?;
            let default = if self.eat(TokenKind::Eq) {
                Some(AnonConst {
                    id: NodeId::DUMMY,
                    value: self.parse_expr()?,
                })
            } else {
                None
            };
            fields.push(FieldDef {
                attrs,
                id: NodeId::DUMMY,
                span: lo.to(self.prev_token.span),
                vis,
                safety: Safety::Default,
                ident: None,
                ty,
                default,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::Close(Delim::Paren))?;
        Ok(fields)
    }

    fn parse_variant(&mut self) -> PResult<Variant> {
        let attrs = self.parse_outer_attributes()?;
        let lo = attrs.first().map_or(self.token.span, |a| a.span);
        let vis = self.parse_visibility()?;
        let ident = self.parse_ident()?;
        let data = if self.check(TokenKind::Open(Delim::Brace)) {
            VariantData::Struct {
                fields: self.parse_record_fields()?,
            }
        } else if self.check(TokenKind::Open(Delim::Paren)) {
            VariantData::Tuple(self.parse_tuple_fields()?, NodeId::DUMMY)
        } else {
            VariantData::Unit(NodeId::DUMMY)
        };
        let disr_expr = if self.eat(TokenKind::Eq) {
            Some(AnonConst {
                id: NodeId::DUMMY,
                value: self.parse_expr()?,
            })
        } else {
            None
        };
        Ok(Variant {
            attrs,
            id: NodeId::DUMMY,
            span: lo.to(self.prev_token.span),
            vis,
            ident,
            data,
            disr_expr,
        })
    }

    // -----------------------------------------------------------------------------------------
    // Type aliases, traits, impls

    fn parse_type_alias(&mut self, defaultness: Defaultness) -> PResult<(Ident, TyAlias)> {
        let ident = self.parse_ident()?;
        let mut generics = self.parse_generics()?;
        let bounds = if self.eat(TokenKind::Colon) {
            self.parse_generic_bounds()?
        } else {
            Vec::new()
        };
        generics.where_clause = self.parse_where_clause()?;
        let ty = if self.eat(TokenKind::Eq) {
            Some(self.parse_ty()?)
        } else {
            None
        };
        let after_where = self.parse_where_clause()?;
        self.expect(TokenKind::Semi)?;
        Ok((
            ident,
            TyAlias {
                defaultness,
                generics,
                bounds,
                ty,
                after_where,
            },
        ))
    }

    fn parse_trait(&mut self, attrs: &mut Vec<Attribute>) -> PResult<(Ident, ItemKind)> {
        let impl_restriction = if self.check_keyword(kw::Impl) {
            self.bump();
            self.expect(TokenKind::Open(Delim::Paren))?;
            self.eat_keyword(kw::In);
            let path = self.parse_path(PathStyle::Mod)?;
            self.expect(TokenKind::Close(Delim::Paren))?;
            Some(Box::new(path))
        } else {
            None
        };
        let mut constness = Constness::No;
        let mut safety = Safety::Default;
        let mut is_auto = false;
        loop {
            let span = self.token.span;
            if self.eat_keyword(kw::Const) {
                constness = Constness::Yes(span);
            } else if self.eat_keyword(kw::Unsafe) {
                safety = Safety::Unsafe(span);
            } else if self.eat_keyword(kw::Auto) {
                is_auto = true;
            } else {
                break;
            }
        }
        self.expect_keyword(kw::Trait)?;
        let ident = self.parse_ident()?;
        let mut generics = self.parse_generics()?;
        let bounds = if self.eat(TokenKind::Colon) {
            self.parse_generic_bounds()?
        } else {
            Vec::new()
        };
        if self.eat(TokenKind::Eq) {
            // `trait Alias = Bounds;`
            let bounds = self.parse_generic_bounds()?;
            generics.where_clause = self.parse_where_clause()?;
            self.expect(TokenKind::Semi)?;
            return Ok((ident, ItemKind::TraitAlias(generics, bounds)));
        }
        generics.where_clause = self.parse_where_clause()?;
        let items = self.parse_assoc_items(attrs, ItemCtx::Trait)?;
        Ok((
            ident,
            ItemKind::Trait(Box::new(Trait {
                impl_restriction,
                constness,
                safety,
                is_auto,
                generics,
                bounds,
                items,
            })),
        ))
    }

    fn parse_impl(
        &mut self,
        attrs: &mut Vec<Attribute>,
        defaultness: Defaultness,
    ) -> PResult<Impl> {
        let mut constness = Constness::No;
        let mut safety = Safety::Default;
        loop {
            let span = self.token.span;
            if self.eat_keyword(kw::Const) {
                constness = Constness::Yes(span);
            } else if self.eat_keyword(kw::Unsafe) {
                safety = Safety::Unsafe(span);
            } else {
                break;
            }
        }
        self.expect_keyword(kw::Impl)?;
        let mut generics = if self.choose_generics_over_qpath(0) {
            self.parse_generics()?
        } else {
            Generics::default()
        };
        // `impl const Trait for T` (older syntax).
        if self.check_keyword(kw::Const) && self.look_kind(1) != TokenKind::Open(Delim::Brace) {
            constness = Constness::Yes(self.token.span);
            self.bump();
        }
        let polarity = if self.check(TokenKind::Not)
            && !matches!(self.look_kind(1), TokenKind::Open(Delim::Brace))
        {
            self.bump();
            ImplPolarity::Negative(self.prev_token.span)
        } else {
            ImplPolarity::Positive
        };
        let first = self.parse_ty_for_impl()?;
        let (of_trait, self_ty) = if self.eat_keyword(kw::For) {
            let path = match first.kind {
                TyKind::Path(None, path) => path,
                _ => return Err(self.error_at(first.span, "expected a trait, found type")),
            };
            let self_ty = self.parse_ty_for_impl()?;
            (
                Some(TraitRef {
                    path,
                    ref_id: NodeId::DUMMY,
                }),
                self_ty,
            )
        } else {
            (None, first)
        };
        generics.where_clause = self.parse_where_clause()?;
        let items = self.parse_assoc_items(attrs, ItemCtx::Impl)?;
        Ok(Impl {
            defaultness,
            safety,
            generics,
            constness,
            polarity,
            of_trait,
            self_ty,
            items,
        })
    }

    /// `impl<` starts generics unless it starts a qualified path: `impl <T as Tr>::X {}`.
    pub(crate) fn choose_generics_over_qpath(&self, start: usize) -> bool {
        if self.look_kind(start) != TokenKind::Lt {
            return false;
        }
        let t1 = self.look(start + 1);
        let t2 = self.look(start + 2);
        match t1.kind {
            TokenKind::Gt | TokenKind::Pound => true,
            TokenKind::Lifetime | TokenKind::RawLifetime => true,
            TokenKind::Ident | TokenKind::RawIdent => {
                if t1.is_keyword(kw::Const) && t2.is_ident() {
                    return true;
                }
                t1.is_non_reserved_ident(self.edition2018())
                    && matches!(
                        t2.kind,
                        TokenKind::Gt
                            | TokenKind::Comma
                            | TokenKind::Colon
                            | TokenKind::Eq
                            | TokenKind::Ge
                            | TokenKind::Shr
                    )
            }
            _ => false,
        }
    }

    fn parse_assoc_items(
        &mut self,
        attrs: &mut Vec<Attribute>,
        ctx: ItemCtx,
    ) -> PResult<Vec<P<AssocItem>>> {
        self.expect(TokenKind::Open(Delim::Brace))?;
        attrs.extend(self.parse_inner_attributes()?);
        let mut items = Vec::new();
        while !self.check(TokenKind::Close(Delim::Brace)) && !self.check(TokenKind::Eof) {
            if self.eat(TokenKind::Semi) {
                continue;
            }
            match self.parse_assoc_item(ctx) {
                Ok(Some(item)) => items.push(item),
                Ok(None) => {
                    let e = self.expected("associated item");
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
            }
        }
        self.expect(TokenKind::Close(Delim::Brace))?;
        Ok(items)
    }

    /// Associated items until `Eof`: the output of a macro called in a trait or impl.
    pub fn parse_assoc_items_fragment(&mut self, in_trait: bool) -> Vec<P<AssocItem>> {
        let ctx = if in_trait {
            ItemCtx::Trait
        } else {
            ItemCtx::Impl
        };
        let mut items = Vec::new();
        while !self.check(TokenKind::Eof) {
            if self.eat(TokenKind::Semi) {
                continue;
            }
            match self.parse_assoc_item(ctx) {
                Ok(Some(item)) => items.push(item),
                Ok(None) => {
                    let e = self.expected("associated item");
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
            }
        }
        items
    }

    /// Foreign items until `Eof`: the output of a macro called in an `extern` block.
    pub fn parse_foreign_items_fragment(&mut self) -> Vec<P<ForeignItem>> {
        let mut items = Vec::new();
        while !self.check(TokenKind::Eof) {
            match self.parse_foreign_item() {
                Ok(Some(item)) => items.push(item),
                Ok(None) => {
                    let e = self.expected("item");
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
                Err(e) => {
                    self.emit(e);
                    self.recover_to_semi_or_close();
                }
            }
        }
        items
    }

    fn parse_assoc_item(&mut self, ctx: ItemCtx) -> PResult<Option<P<AssocItem>>> {
        let attrs = self.parse_outer_attributes()?;
        let Some(item) = self.parse_item_with_attrs(attrs, ctx)? else {
            return Ok(None);
        };
        let Item {
            attrs,
            id,
            span,
            vis,
            ident,
            kind,
        } = *item;
        let kind = match kind {
            ItemKind::Const(c) => AssocItemKind::Const(c),
            ItemKind::Fn(f) => AssocItemKind::Fn(f),
            ItemKind::TyAlias(t) => AssocItemKind::Type(t),
            ItemKind::MacCall(m) => AssocItemKind::MacCall(m),
            _ => return Err(self.error_at(span, "this item cannot appear in a trait or impl")),
        };
        Ok(Some(Box::new(Item {
            attrs,
            id,
            span,
            vis,
            ident,
            kind,
        })))
    }

    fn parse_foreign_item(&mut self) -> PResult<Option<P<ForeignItem>>> {
        let attrs = self.parse_outer_attributes()?;
        let Some(item) = self.parse_item_with_attrs(attrs, ItemCtx::Foreign)? else {
            return Ok(None);
        };
        let Item {
            attrs,
            id,
            span,
            vis,
            ident,
            kind,
        } = *item;
        let kind = match kind {
            ItemKind::Static(s) => ForeignItemKind::Static(s),
            ItemKind::Fn(f) => ForeignItemKind::Fn(f),
            ItemKind::TyAlias(t) => ForeignItemKind::TyAlias(t),
            ItemKind::MacCall(m) => ForeignItemKind::MacCall(m),
            _ => return Err(self.error_at(span, "this item cannot appear in an `extern` block")),
        };
        Ok(Some(Box::new(Item {
            attrs,
            id,
            span,
            vis,
            ident,
            kind,
        })))
    }
}
