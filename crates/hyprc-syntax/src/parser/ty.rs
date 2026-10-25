//! Types, paths, generics, bounds and `where` clauses.

use super::{Edition, PResult, Parser, PathStyle};
use crate::ast::*;
use crate::token::{Delim, TokenKind};
use hyprc_span::{Ident, Span, kw};

impl Parser<'_> {
    pub fn parse_ty(&mut self) -> PResult<P<Ty>> {
        self.parse_ty_common(true, false)
    }

    /// A type where `+` ends it: after `&`, `*const`, `as`, and in `Fn() -> T`.
    pub fn parse_ty_no_plus(&mut self) -> PResult<P<Ty>> {
        self.parse_ty_common(false, false)
    }

    pub(crate) fn parse_ty_for_impl(&mut self) -> PResult<P<Ty>> {
        self.parse_ty_common(true, false)
    }

    fn mk_ty(&self, kind: TyKind, lo: Span) -> P<Ty> {
        Box::new(Ty {
            id: NodeId::DUMMY,
            kind,
            span: lo.to(self.prev_token.span),
        })
    }

    fn is_dyn_start(&self) -> bool {
        if !self.check_keyword(kw::Dyn) {
            return false;
        }
        if self.edition >= Edition::E2018 {
            return true;
        }
        // In 2015 `dyn` is a keyword only where a bound follows it, and not where `dyn` could
        // be a type itself (`dyn::Path`, `dyn<T>`).
        let t = self.look(1);
        let begins_bound = (t.is_ident() && !t.is_keyword(kw::As))
            || t.is_lifetime()
            || matches!(
                t.kind,
                TokenKind::Question | TokenKind::Open(Delim::Paren) | TokenKind::Star
            );
        let continues_type = matches!(t.kind, TokenKind::PathSep | TokenKind::Lt | TokenKind::Shl);
        begins_bound && !continues_type
    }

    fn parse_ty_common(&mut self, allow_plus: bool, _allow_c_variadic: bool) -> PResult<P<Ty>> {
        self.enter()?;
        let r = self.parse_ty_common_inner(allow_plus, _allow_c_variadic);
        self.depth -= 1;
        r
    }

    fn parse_ty_common_inner(
        &mut self,
        allow_plus: bool,
        _allow_c_variadic: bool,
    ) -> PResult<P<Ty>> {
        let lo = self.token.span;
        let t = self.token;
        let kind = match t.kind {
            TokenKind::Open(Delim::Paren) => {
                self.bump();
                let mut tys = Vec::new();
                let mut trailing = false;
                while !self.check(TokenKind::Close(Delim::Paren)) {
                    tys.push(self.parse_ty()?);
                    trailing = false;
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                    trailing = true;
                }
                self.expect(TokenKind::Close(Delim::Paren))?;
                if tys.len() == 1 && !trailing {
                    let inner = tys.pop().unwrap();
                    // `(Trait) + Send`: a bound in parentheses followed by more bounds.
                    if allow_plus && self.check(TokenKind::Plus) {
                        if let TyKind::Path(None, path) = &inner.kind {
                            let first = GenericBound::Trait(PolyTraitRef {
                                bound_generic_params: Vec::new(),
                                modifiers: TraitBoundModifiers::default(),
                                trait_ref: TraitRef {
                                    path: path.clone(),
                                    ref_id: NodeId::DUMMY,
                                },
                                span: inner.span,
                                parens: true,
                            });
                            self.bump();
                            let mut bounds = vec![first];
                            bounds.extend(self.parse_generic_bounds()?);
                            return Ok(self
                                .mk_ty(TyKind::TraitObject(bounds, TraitObjectSyntax::None), lo));
                        }
                    }
                    TyKind::Paren(inner)
                } else {
                    TyKind::Tup(tys)
                }
            }
            TokenKind::Not => {
                self.bump();
                TyKind::Never
            }
            TokenKind::Star => {
                self.bump();
                let mutbl = if self.eat_keyword(kw::Mut) {
                    Mutability::Mut
                } else if self.eat_keyword(kw::Const) {
                    Mutability::Not
                } else {
                    return Err(self.expected("`mut` or `const` keyword in raw pointer type"));
                };
                TyKind::Ptr(MutTy {
                    ty: self.parse_ty_no_plus()?,
                    mutbl,
                })
            }
            TokenKind::Open(Delim::Bracket) => {
                self.bump();
                let elem = self.parse_ty()?;
                let kind = if self.eat(TokenKind::Semi) {
                    let len = self.parse_expr()?;
                    TyKind::Array(
                        elem,
                        AnonConst {
                            id: NodeId::DUMMY,
                            value: len,
                        },
                    )
                } else {
                    TyKind::Slice(elem)
                };
                self.expect(TokenKind::Close(Delim::Bracket))?;
                kind
            }
            TokenKind::And | TokenKind::AndAnd => {
                self.break_and_eat(TokenKind::And);
                let lifetime = if self.check_lifetime() {
                    Some(self.expect_lifetime()?)
                } else {
                    None
                };
                let pinned = self.token.kind == TokenKind::Ident
                    && self.token.sym.as_str() == "pin"
                    && (self.look(1).is_keyword(kw::Mut) || self.look(1).is_keyword(kw::Const));
                if pinned {
                    self.bump();
                    let mutbl = if self.eat_keyword(kw::Mut) {
                        Mutability::Mut
                    } else {
                        self.expect_keyword(kw::Const)?;
                        Mutability::Not
                    };
                    TyKind::PinnedRef(
                        lifetime,
                        MutTy {
                            ty: self.parse_ty_no_plus()?,
                            mutbl,
                        },
                    )
                } else {
                    let mutbl = if self.eat_keyword(kw::Mut) {
                        Mutability::Mut
                    } else {
                        Mutability::Not
                    };
                    TyKind::Ref(
                        lifetime,
                        MutTy {
                            ty: self.parse_ty_no_plus()?,
                            mutbl,
                        },
                    )
                }
            }
            TokenKind::Ident if t.sym == kw::Underscore => {
                self.bump();
                TyKind::Infer
            }
            TokenKind::Ident if t.sym == kw::Impl => {
                self.bump();
                let bounds = if allow_plus {
                    self.parse_generic_bounds()?
                } else {
                    vec![self.parse_generic_bound()?]
                };
                TyKind::ImplTrait(NodeId::DUMMY, bounds)
            }
            TokenKind::Ident if self.is_dyn_start() => {
                self.bump();
                let syntax = if self.check(TokenKind::Star)
                    && !self.look(1).is_keyword(kw::Const)
                    && !self.look(1).is_keyword(kw::Mut)
                {
                    self.bump();
                    TraitObjectSyntax::DynStar
                } else {
                    TraitObjectSyntax::Dyn
                };
                let bounds = if allow_plus {
                    self.parse_generic_bounds()?
                } else {
                    vec![self.parse_generic_bound()?]
                };
                TyKind::TraitObject(bounds, syntax)
            }
            TokenKind::Ident if t.sym == kw::Typeof => {
                self.bump();
                self.expect(TokenKind::Open(Delim::Paren))?;
                let e = self.parse_expr()?;
                self.expect(TokenKind::Close(Delim::Paren))?;
                TyKind::Typeof(AnonConst {
                    id: NodeId::DUMMY,
                    value: e,
                })
            }
            TokenKind::Ident if t.sym == kw::Unsafe && self.look_kind(1) == TokenKind::Lt => {
                // `unsafe<'a> T`
                self.bump();
                let generic_params = self.parse_generic_params_list()?;
                let inner_ty = self.parse_ty()?;
                TyKind::UnsafeBinder(Box::new(UnsafeBinderTy {
                    generic_params,
                    inner_ty,
                }))
            }
            TokenKind::Ident if self.check_bare_fn_start() => self.parse_bare_fn(Vec::new(), lo)?,
            TokenKind::Ident if t.sym == kw::For => {
                // `for<'a> fn(&'a u8)` or `for<'a> Trait<'a>`.
                self.bump();
                let params = self.parse_generic_params_list()?;
                if self.check_bare_fn_start() {
                    self.parse_bare_fn(params, lo)?
                } else {
                    let path = self.parse_path(PathStyle::Type)?;
                    let bound = GenericBound::Trait(PolyTraitRef {
                        bound_generic_params: params,
                        modifiers: TraitBoundModifiers::default(),
                        trait_ref: TraitRef {
                            path,
                            ref_id: NodeId::DUMMY,
                        },
                        span: lo.to(self.prev_token.span),
                        parens: false,
                    });
                    let mut bounds = vec![bound];
                    if allow_plus && self.eat(TokenKind::Plus) {
                        bounds.extend(self.parse_generic_bounds()?);
                    }
                    TyKind::TraitObject(bounds, TraitObjectSyntax::None)
                }
            }
            TokenKind::Lt | TokenKind::Shl => {
                let (qself, path) = self.parse_qpath(PathStyle::Type)?;
                TyKind::Path(Some(qself), path)
            }
            TokenKind::Lifetime | TokenKind::RawLifetime => {
                // `'a + Trait` (a 2015 trait object).
                let bounds = self.parse_generic_bounds()?;
                TyKind::TraitObject(bounds, TraitObjectSyntax::None)
            }
            TokenKind::Question => {
                // `?Sized` where a type is expected (`Box<?Sized>` is an error, `impl ?Sized` is not
                // here). Parse it as a bare trait object for recovery.
                let bounds = self.parse_generic_bounds()?;
                TyKind::TraitObject(bounds, TraitObjectSyntax::None)
            }
            TokenKind::DotDotDot => {
                self.bump();
                TyKind::CVarArgs
            }
            TokenKind::Open(Delim::Invisible) => {
                self.bump();
                let ty = self.parse_ty()?;
                self.expect(TokenKind::Close(Delim::Invisible))?;
                return self.maybe_more_bounds(ty, allow_plus, lo);
            }
            _ if self.check_path_start() => {
                let path = self.parse_path(PathStyle::Type)?;
                if self.check(TokenKind::Not) && matches!(self.look_kind(1), TokenKind::Open(_)) {
                    self.bump();
                    let args = self.parse_delim_args()?;
                    TyKind::MacCall(Box::new(MacCall { path, args }))
                } else if allow_plus && self.check(TokenKind::Plus) {
                    let first = GenericBound::Trait(PolyTraitRef {
                        bound_generic_params: Vec::new(),
                        modifiers: TraitBoundModifiers::default(),
                        span: path.span,
                        trait_ref: TraitRef {
                            path,
                            ref_id: NodeId::DUMMY,
                        },
                        parens: false,
                    });
                    self.bump();
                    let mut bounds = vec![first];
                    bounds.extend(self.parse_generic_bounds()?);
                    TyKind::TraitObject(bounds, TraitObjectSyntax::None)
                } else {
                    TyKind::Path(None, path)
                }
            }
            _ => return Err(self.expected("type")),
        };
        let ty = self.mk_ty(kind, lo);
        // `u32 is 1..` (pattern types).
        if self.token.kind == TokenKind::Ident && self.token.sym.as_str() == "is" && allow_plus {
            let snapshot = self.snapshot();
            self.bump();
            match self.parse_ty_pat() {
                Ok(pat) => return Ok(self.mk_ty(TyKind::Pat(ty, pat), lo)),
                Err(_) => self.restore(snapshot),
            }
        }
        Ok(ty)
    }

    fn maybe_more_bounds(&mut self, ty: P<Ty>, allow_plus: bool, lo: Span) -> PResult<P<Ty>> {
        if allow_plus && self.check(TokenKind::Plus) {
            if let TyKind::Path(None, path) = &ty.kind {
                let first = GenericBound::Trait(PolyTraitRef {
                    bound_generic_params: Vec::new(),
                    modifiers: TraitBoundModifiers::default(),
                    trait_ref: TraitRef {
                        path: path.clone(),
                        ref_id: NodeId::DUMMY,
                    },
                    span: ty.span,
                    parens: false,
                });
                self.bump();
                let mut bounds = vec![first];
                bounds.extend(self.parse_generic_bounds()?);
                return Ok(self.mk_ty(TyKind::TraitObject(bounds, TraitObjectSyntax::None), lo));
            }
        }
        Ok(ty)
    }

    /// `1..`, `..0 | 1..`, `!null`
    fn parse_ty_pat(&mut self) -> PResult<P<TyPat>> {
        let lo = self.token.span;
        let first = self.parse_ty_pat_one()?;
        if !self.check(TokenKind::Or) {
            return Ok(first);
        }
        let mut alts = vec![first];
        while self.eat(TokenKind::Or) {
            alts.push(self.parse_ty_pat_one()?);
        }
        Ok(Box::new(TyPat {
            id: NodeId::DUMMY,
            kind: TyPatKind::Or(alts),
            span: lo.to(self.prev_token.span),
        }))
    }

    fn parse_ty_pat_one(&mut self) -> PResult<P<TyPat>> {
        let lo = self.token.span;
        if self.check(TokenKind::Not)
            && self.look(1).is_ident()
            && self.look(1).sym.as_str() == "null"
        {
            self.bump();
            self.bump();
            return Ok(Box::new(TyPat {
                id: NodeId::DUMMY,
                kind: TyPatKind::NotNull,
                span: lo.to(self.prev_token.span),
            }));
        }
        let pat = self.parse_pat_no_top_alt()?;
        Ok(ty_pat_of(*pat))
    }

    /// `fn`, `unsafe fn`, `extern "C" fn`, `unsafe extern fn`, `safe fn`.
    fn check_bare_fn_start(&self) -> bool {
        let mut i = 0;
        loop {
            let t = self.look(i);
            if t.kind != TokenKind::Ident {
                return false;
            }
            match t.sym {
                kw::Fn => return true,
                kw::Unsafe | kw::Safe => {
                    // `unsafe<` is an unsafe binder.
                    if self.look_kind(i + 1) == TokenKind::Lt {
                        return false;
                    }
                    i += 1
                }
                kw::Extern => {
                    i += 1;
                    if matches!(self.look_kind(i), TokenKind::Literal(_)) {
                        i += 1;
                    }
                }
                _ => return false,
            }
            if i > 4 {
                return false;
            }
        }
    }

    fn parse_bare_fn(&mut self, generic_params: Vec<GenericParam>, lo: Span) -> PResult<TyKind> {
        let mut safety = Safety::Default;
        let mut ext = Extern::None;
        loop {
            let span = self.token.span;
            if self.eat_keyword(kw::Unsafe) {
                safety = Safety::Unsafe(span);
            } else if self.eat_keyword(kw::Safe) {
                safety = Safety::Safe(span);
            } else if self.eat_keyword(kw::Extern) {
                ext = match self.parse_str_lit() {
                    Some(abi) => Extern::Explicit(abi, span.to(abi.span)),
                    None => Extern::Implicit(span),
                };
            } else {
                break;
            }
        }
        let decl_lo = self.token.span;
        self.expect_keyword(kw::Fn)?;
        let decl = self.parse_fn_decl(false, false)?;
        let _ = lo;
        Ok(TyKind::BareFn(Box::new(BareFnTy {
            safety,
            ext,
            generic_params,
            decl,
            decl_span: decl_lo.to(self.prev_token.span),
        })))
    }

    pub(crate) fn can_begin_type(&self) -> bool {
        let t = self.token;
        match t.kind {
            TokenKind::Open(Delim::Paren | Delim::Bracket | Delim::Invisible)
            | TokenKind::Not
            | TokenKind::Star
            | TokenKind::And
            | TokenKind::AndAnd
            | TokenKind::Lt
            | TokenKind::Shl
            | TokenKind::PathSep
            | TokenKind::Question
            | TokenKind::Lifetime
            | TokenKind::RawLifetime
            | TokenKind::RawIdent => true,
            TokenKind::Ident => {
                !t.sym.is_reserved(self.edition2018())
                    || matches!(
                        t.sym,
                        kw::Underscore
                            | kw::SelfUpper
                            | kw::SelfLower
                            | kw::Super
                            | kw::Crate
                            | kw::DollarCrate
                            | kw::Impl
                            | kw::Dyn
                            | kw::Fn
                            | kw::Unsafe
                            | kw::Extern
                            | kw::For
                            | kw::Typeof
                    )
            }
            _ => false,
        }
    }

    // -----------------------------------------------------------------------------------------
    // Paths

    pub(crate) fn check_path_start(&self) -> bool {
        let t = self.token;
        match t.kind {
            TokenKind::PathSep | TokenKind::RawIdent => true,
            TokenKind::Ident => {
                t.sym.is_path_segment_keyword() || t.is_non_reserved_ident(self.edition2018())
            }
            _ => false,
        }
    }

    /// An identifier or one of the keywords that can be a path segment.
    pub(crate) fn parse_path_segment_ident(&mut self) -> PResult<Ident> {
        let t = self.token;
        if t.kind == TokenKind::Ident && t.sym.is_path_segment_keyword() {
            self.bump();
            return Ok(Ident::new(t.sym, t.span));
        }
        self.parse_ident()
    }

    pub fn parse_path(&mut self, style: PathStyle) -> PResult<Path> {
        if matches!(self.token.kind, TokenKind::Open(Delim::Invisible)) {
            // A `$p:path` fragment.
            self.bump();
            let path = self.parse_path(style)?;
            self.expect(TokenKind::Close(Delim::Invisible))?;
            if self.check(TokenKind::PathSep) && self.look(1).is_ident() {
                let mut path = path;
                self.bump();
                self.parse_path_segments(&mut path.segments, style)?;
                path.span = path.span.to(self.prev_token.span);
                return Ok(path);
            }
            return Ok(path);
        }
        let lo = self.token.span;
        let mut segments = Vec::new();
        if self.eat(TokenKind::PathSep) {
            segments.push(PathSegment::from_ident(Ident::new(kw::PathRoot, lo)));
        }
        self.parse_path_segments(&mut segments, style)?;
        Ok(Path {
            span: lo.to(self.prev_token.span),
            segments,
        })
    }

    pub(crate) fn parse_path_segments(
        &mut self,
        segments: &mut Vec<PathSegment>,
        style: PathStyle,
    ) -> PResult<()> {
        loop {
            let ident = self.parse_path_segment_ident()?;
            let args = self.parse_path_segment_args(style)?;
            segments.push(PathSegment {
                ident,
                id: NodeId::DUMMY,
                args,
            });
            if self.check(TokenKind::PathSep) && self.path_continues_after_sep() {
                self.bump();
            } else {
                return Ok(());
            }
        }
    }

    /// After a `::`: another segment follows (not `*`, `{`, or generic arguments, which the
    /// caller handles).
    fn path_continues_after_sep(&self) -> bool {
        let t = self.look(1);
        t.is_ident()
    }

    fn parse_path_segment_args(&mut self, style: PathStyle) -> PResult<Option<P<GenericArgs>>> {
        match style {
            PathStyle::Mod => Ok(None),
            PathStyle::Expr => {
                if self.check(TokenKind::PathSep)
                    && matches!(
                        self.look_kind(1),
                        TokenKind::Lt | TokenKind::Shl | TokenKind::LArrow
                    )
                {
                    self.bump();
                    return Ok(Some(Box::new(self.parse_angle_args()?)));
                }
                Ok(None)
            }
            PathStyle::Type => {
                if self.check(TokenKind::PathSep)
                    && matches!(
                        self.look_kind(1),
                        TokenKind::Lt
                            | TokenKind::Shl
                            | TokenKind::LArrow
                            | TokenKind::Open(Delim::Paren)
                    )
                {
                    self.bump();
                }
                // Like rustc: `<`, `<<` and `<-` start generic arguments, `<=` doesn't
                // (`x as u32 <= y` is a comparison).
                if matches!(
                    self.token.kind,
                    TokenKind::Lt | TokenKind::Shl | TokenKind::LArrow
                ) {
                    return Ok(Some(Box::new(self.parse_angle_args()?)));
                }
                if self.check(TokenKind::Open(Delim::Paren)) {
                    let lo = self.token.span;
                    // `Trait(..)`: return type notation.
                    if self.look_kind(1) == TokenKind::DotDot
                        && self.look_kind(2) == TokenKind::Close(Delim::Paren)
                    {
                        self.bump();
                        self.bump();
                        self.bump();
                        return Ok(Some(Box::new(GenericArgs::ParenthesizedElided(
                            lo.to(self.prev_token.span),
                        ))));
                    }
                    self.bump();
                    let mut inputs = Vec::new();
                    while !self.check(TokenKind::Close(Delim::Paren)) {
                        inputs.push(self.parse_ty()?);
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::Close(Delim::Paren))?;
                    let output = self.parse_ret_ty(false)?;
                    return Ok(Some(Box::new(GenericArgs::Parenthesized {
                        inputs,
                        output,
                        span: lo.to(self.prev_token.span),
                    })));
                }
                Ok(None)
            }
        }
    }

    /// `<args>`; the current token starts with `<`.
    pub(crate) fn parse_angle_args(&mut self) -> PResult<GenericArgs> {
        let lo = self.token.span;
        if !self.break_and_eat(TokenKind::Lt) {
            return Err(self.expected("`<`"));
        }
        let mut args = Vec::new();
        while !self.check_start(TokenKind::Gt) {
            args.push(self.parse_angle_arg()?);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        if !self.break_and_eat(TokenKind::Gt) {
            return Err(self.expected("`>` or `,`"));
        }
        Ok(GenericArgs::AngleBracketed {
            args,
            span: lo.to(self.prev_token.span),
        })
    }

    fn parse_angle_arg(&mut self) -> PResult<AngleBracketedArg> {
        let lo = self.token.span;
        // `Name = T`, `Name: Bound`
        if self.check_ident() && matches!(self.look_kind(1), TokenKind::Eq | TokenKind::Colon) {
            let ident = self.parse_ident()?;
            return self.parse_assoc_constraint(ident, None, lo);
        }
        if self.check_lifetime() {
            return Ok(AngleBracketedArg::Arg(GenericArg::Lifetime(
                self.expect_lifetime()?,
            )));
        }
        if self.check_const_arg() {
            let value = self.parse_const_arg()?;
            return Ok(AngleBracketedArg::Arg(GenericArg::Const(AnonConst {
                id: NodeId::DUMMY,
                value,
            })));
        }
        let ty = self.parse_ty()?;
        // `Name<Args> = T` (a constraint on a generic associated type).
        if matches!(self.token.kind, TokenKind::Eq | TokenKind::Colon) {
            if let TyKind::Path(None, path) = &ty.kind
                && path.segments.len() == 1
            {
                let seg = &path.segments[0];
                let gen_args = seg.args.as_deref().cloned();
                return self.parse_assoc_constraint(seg.ident, gen_args, lo);
            }
        }
        Ok(AngleBracketedArg::Arg(GenericArg::Type(ty)))
    }

    fn parse_assoc_constraint(
        &mut self,
        ident: Ident,
        gen_args: Option<GenericArgs>,
        lo: Span,
    ) -> PResult<AngleBracketedArg> {
        let kind = if self.eat(TokenKind::Colon) {
            AssocItemConstraintKind::Bound(self.parse_generic_bounds()?)
        } else {
            self.expect(TokenKind::Eq)?;
            if self.check_const_arg() {
                let value = self.parse_const_arg()?;
                AssocItemConstraintKind::Equality(Term::Const(AnonConst {
                    id: NodeId::DUMMY,
                    value,
                }))
            } else {
                AssocItemConstraintKind::Equality(Term::Ty(self.parse_ty()?))
            }
        };
        Ok(AngleBracketedArg::Constraint(AssocItemConstraint {
            id: NodeId::DUMMY,
            ident,
            gen_args,
            kind,
            span: lo.to(self.prev_token.span),
        }))
    }

    /// A const generic argument written so it can't be a type: `{ … }`, a literal, `-1`.
    fn check_const_arg(&self) -> bool {
        match self.token.kind {
            TokenKind::Open(Delim::Brace) => true,
            TokenKind::Literal(_) => true,
            TokenKind::Minus => matches!(self.look_kind(1), TokenKind::Literal(_)),
            TokenKind::Ident => {
                self.token.sym == kw::True
                    || self.token.sym == kw::False
                    || (self.token.sym == kw::Const
                        && self.look_kind(1) == TokenKind::Open(Delim::Brace))
            }
            _ => false,
        }
    }

    pub(crate) fn parse_const_arg(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        if self.check(TokenKind::Open(Delim::Brace)) {
            let block = self.parse_block()?;
            return Ok(Box::new(Expr {
                id: NodeId::DUMMY,
                kind: ExprKind::Block(block, None),
                span: lo.to(self.prev_token.span),
                attrs: Vec::new(),
            }));
        }
        if self.check_keyword(kw::Const) {
            return self.parse_expr_bottom_public();
        }
        if self.eat(TokenKind::Minus) {
            let lit = self.parse_lit()?;
            let inner = Box::new(Expr {
                id: NodeId::DUMMY,
                kind: ExprKind::Lit(lit),
                span: lit.span,
                attrs: Vec::new(),
            });
            return Ok(Box::new(Expr {
                id: NodeId::DUMMY,
                kind: ExprKind::Unary(UnOp::Neg, inner),
                span: lo.to(self.prev_token.span),
                attrs: Vec::new(),
            }));
        }
        let lit = self.parse_lit()?;
        Ok(Box::new(Expr {
            id: NodeId::DUMMY,
            kind: ExprKind::Lit(lit),
            span: lit.span,
            attrs: Vec::new(),
        }))
    }

    /// `<Ty as Trait>::rest` or `<Ty>::rest`.
    pub(crate) fn parse_qpath(&mut self, style: PathStyle) -> PResult<(P<QSelf>, Path)> {
        let lo = self.token.span;
        if !self.break_and_eat(TokenKind::Lt) {
            return Err(self.expected("`<`"));
        }
        let ty = self.parse_ty()?;
        let mut segments = Vec::new();
        if self.eat_keyword(kw::As) {
            let trait_path = self.parse_path(PathStyle::Type)?;
            segments = trait_path.segments;
        }
        let position = segments.len();
        if !self.break_and_eat(TokenKind::Gt) {
            return Err(self.expected("`>`"));
        }
        let path_span = lo.to(self.prev_token.span);
        self.expect(TokenKind::PathSep)?;
        self.parse_path_segments(&mut segments, style)?;
        let qself = Box::new(QSelf {
            ty,
            path_span,
            position,
        });
        Ok((
            qself,
            Path {
                span: lo.to(self.prev_token.span),
                segments,
            },
        ))
    }

    // -----------------------------------------------------------------------------------------
    // Generics

    /// `<…>` after an item's name, or nothing.
    pub fn parse_generics(&mut self) -> PResult<Generics> {
        let lo = self.token.span;
        if !self.check_start(TokenKind::Lt) {
            return Ok(Generics {
                span: lo.shrink_to_lo(),
                ..Generics::default()
            });
        }
        let params = self.parse_generic_params_list()?;
        Ok(Generics {
            params,
            where_clause: WhereClause::default(),
            span: lo.to(self.prev_token.span),
        })
    }

    /// `<'a, T: Bound = Default, const N: usize>`
    pub(crate) fn parse_generic_params_list(&mut self) -> PResult<Vec<GenericParam>> {
        if !self.break_and_eat(TokenKind::Lt) {
            return Err(self.expected("`<`"));
        }
        let mut params = Vec::new();
        while !self.check_start(TokenKind::Gt) {
            let attrs = self.parse_outer_attributes()?;
            let lo = self.token.span;
            if self.check_lifetime() {
                let lt = self.expect_lifetime()?;
                let mut bounds = Vec::new();
                if self.eat(TokenKind::Colon) {
                    while self.check_lifetime() {
                        bounds.push(GenericBound::Outlives(self.expect_lifetime()?));
                        if !self.eat(TokenKind::Plus) {
                            break;
                        }
                    }
                }
                params.push(GenericParam {
                    id: NodeId::DUMMY,
                    ident: lt.ident,
                    attrs,
                    bounds,
                    kind: GenericParamKind::Lifetime,
                    span: lo.to(self.prev_token.span),
                });
            } else if self.check_keyword(kw::Const) {
                self.bump();
                let ident = self.parse_ident()?;
                self.expect(TokenKind::Colon)?;
                let ty = self.parse_ty()?;
                let default = if self.eat(TokenKind::Eq) {
                    let value = if self.check_const_arg() {
                        self.parse_const_arg()?
                    } else {
                        self.parse_path_expr_simple()?
                    };
                    Some(AnonConst {
                        id: NodeId::DUMMY,
                        value,
                    })
                } else {
                    None
                };
                params.push(GenericParam {
                    id: NodeId::DUMMY,
                    ident,
                    attrs,
                    bounds: Vec::new(),
                    kind: GenericParamKind::Const { ty, default },
                    span: lo.to(self.prev_token.span),
                });
            } else {
                let ident = self.parse_ident()?;
                let bounds = if self.eat(TokenKind::Colon) {
                    self.parse_generic_bounds()?
                } else {
                    Vec::new()
                };
                let default = if self.eat(TokenKind::Eq) {
                    Some(self.parse_ty()?)
                } else {
                    None
                };
                params.push(GenericParam {
                    id: NodeId::DUMMY,
                    ident,
                    attrs,
                    bounds,
                    kind: GenericParamKind::Type { default },
                    span: lo.to(self.prev_token.span),
                });
            }
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        if !self.break_and_eat(TokenKind::Gt) {
            return Err(self.expected("`>`, `,`, or a generic parameter"));
        }
        Ok(params)
    }

    fn parse_path_expr_simple(&mut self) -> PResult<P<Expr>> {
        let lo = self.token.span;
        let path = self.parse_path(PathStyle::Expr)?;
        Ok(Box::new(Expr {
            id: NodeId::DUMMY,
            kind: ExprKind::Path(None, path),
            span: lo.to(self.prev_token.span),
            attrs: Vec::new(),
        }))
    }

    pub fn parse_where_clause(&mut self) -> PResult<WhereClause> {
        let lo = self.token.span;
        if !self.eat_keyword(kw::Where) {
            return Ok(WhereClause {
                has_where_token: false,
                predicates: Vec::new(),
                span: lo.shrink_to_lo(),
            });
        }
        let mut predicates = Vec::new();
        loop {
            let attrs = self.parse_outer_attributes()?;
            let plo = self.token.span;
            if self.check_lifetime() {
                let lifetime = self.expect_lifetime()?;
                self.expect(TokenKind::Colon)?;
                let mut bounds = Vec::new();
                while self.check_lifetime() {
                    bounds.push(GenericBound::Outlives(self.expect_lifetime()?));
                    if !self.eat(TokenKind::Plus) {
                        break;
                    }
                }
                predicates.push(WherePredicate {
                    attrs,
                    kind: WherePredicateKind::Region { lifetime, bounds },
                    id: NodeId::DUMMY,
                    span: plo.to(self.prev_token.span),
                });
            } else if self.check_keyword(kw::For) || self.can_begin_type() {
                let bound_generic_params =
                    if self.check_keyword(kw::For) && matches!(self.look_kind(1), TokenKind::Lt) {
                        self.bump();
                        self.parse_generic_params_list()?
                    } else {
                        Vec::new()
                    };
                let bounded_ty = self.parse_ty()?;
                let kind = if self.eat(TokenKind::Colon) {
                    let bounds = self.parse_generic_bounds()?;
                    WherePredicateKind::Bound {
                        bound_generic_params,
                        bounded_ty,
                        bounds,
                    }
                } else if self.eat(TokenKind::Eq) || self.eat(TokenKind::EqEq) {
                    let rhs_ty = self.parse_ty()?;
                    WherePredicateKind::Eq {
                        lhs_ty: bounded_ty,
                        rhs_ty,
                    }
                } else {
                    return Err(self.expected("`:`"));
                };
                predicates.push(WherePredicate {
                    attrs,
                    kind,
                    id: NodeId::DUMMY,
                    span: plo.to(self.prev_token.span),
                });
            } else {
                if !attrs.is_empty() {
                    return Err(self.expected("a where predicate after attributes"));
                }
                break;
            }
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        Ok(WhereClause {
            has_where_token: true,
            predicates,
            span: lo.to(self.prev_token.span),
        })
    }

    // -----------------------------------------------------------------------------------------
    // Bounds

    fn can_begin_bound(&self) -> bool {
        let t = self.token;
        match t.kind {
            TokenKind::Lifetime
            | TokenKind::RawLifetime
            | TokenKind::Question
            | TokenKind::Tilde
            | TokenKind::Not
            | TokenKind::PathSep
            | TokenKind::Lt
            | TokenKind::RawIdent => true,
            TokenKind::Open(Delim::Paren) => true,
            TokenKind::Open(Delim::Bracket) => self.look(1).is_keyword(kw::Const),
            TokenKind::Ident => {
                matches!(
                    t.sym,
                    kw::For
                        | kw::Const
                        | kw::Async
                        | kw::Use
                        | kw::SelfUpper
                        | kw::Super
                        | kw::Crate
                        | kw::DollarCrate
                        | kw::SelfLower
                ) || t.is_non_reserved_ident(self.edition2018())
            }
            TokenKind::Open(Delim::Invisible) => true,
            _ => false,
        }
    }

    /// `Bound + Bound + …` (possibly empty, possibly with a trailing `+`).
    pub fn parse_generic_bounds(&mut self) -> PResult<GenericBounds> {
        let mut bounds = Vec::new();
        while self.can_begin_bound() {
            bounds.push(self.parse_generic_bound()?);
            if !self.eat(TokenKind::Plus) {
                break;
            }
        }
        Ok(bounds)
    }

    pub(crate) fn parse_generic_bound(&mut self) -> PResult<GenericBound> {
        let lo = self.token.span;
        if self.check_lifetime() {
            return Ok(GenericBound::Outlives(self.expect_lifetime()?));
        }
        if self.check_keyword(kw::Use) && self.check_start_at(1, TokenKind::Lt) {
            self.bump();
            self.break_and_eat(TokenKind::Lt);
            let mut args = Vec::new();
            while !self.check_start(TokenKind::Gt) {
                if self.check_lifetime() {
                    args.push(PreciseCapturingArg::Lifetime(self.expect_lifetime()?));
                } else {
                    let path = self.parse_path(PathStyle::Mod)?;
                    args.push(PreciseCapturingArg::Arg(path, NodeId::DUMMY));
                }
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            if !self.break_and_eat(TokenKind::Gt) {
                return Err(self.expected("`>`"));
            }
            return Ok(GenericBound::Use(args, lo.to(self.prev_token.span)));
        }
        if self.check(TokenKind::Open(Delim::Paren)) {
            self.bump();
            let inner = self.parse_generic_bound()?;
            self.expect(TokenKind::Close(Delim::Paren))?;
            return Ok(match inner {
                GenericBound::Trait(mut p) => {
                    p.parens = true;
                    p.span = lo.to(self.prev_token.span);
                    GenericBound::Trait(p)
                }
                other => other,
            });
        }
        let mut bound_generic_params =
            if self.check_keyword(kw::For) && self.check_start_at(1, TokenKind::Lt) {
                self.bump();
                self.parse_generic_params_list()?
            } else {
                Vec::new()
            };
        let mut modifiers = TraitBoundModifiers::default();
        // `~const`, `[const]`, `const`
        if self.check(TokenKind::Tilde) && self.look(1).is_keyword(kw::Const) {
            let span = self.token.span.to(self.look(1).span);
            self.bump();
            self.bump();
            modifiers.constness = BoundConstness::Maybe(span);
        } else if self.check(TokenKind::Open(Delim::Bracket))
            && self.look(1).is_keyword(kw::Const)
            && self.look_kind(2) == TokenKind::Close(Delim::Bracket)
        {
            let span = self.token.span.to(self.look(2).span);
            self.bump();
            self.bump();
            self.bump();
            modifiers.constness = BoundConstness::Maybe(span);
        } else if self.check_keyword(kw::Const) {
            modifiers.constness = BoundConstness::Always(self.token.span);
            self.bump();
        }
        if self.check_keyword(kw::Async) && self.edition2018() {
            modifiers.asyncness = true;
            self.bump();
        }
        if self.check(TokenKind::Question) {
            modifiers.polarity = BoundPolarity::Maybe(self.token.span);
            self.bump();
        } else if self.check(TokenKind::Not) {
            modifiers.polarity = BoundPolarity::Negative(self.token.span);
            self.bump();
        }
        // `?for<'a> Trait` is not a thing, but `for<'a>` may come after the modifiers.
        if bound_generic_params.is_empty()
            && self.check_keyword(kw::For)
            && self.check_start_at(1, TokenKind::Lt)
        {
            self.bump();
            bound_generic_params = self.parse_generic_params_list()?;
        }
        let path = if self.check(TokenKind::Open(Delim::Paren)) {
            // `?(Sized)`
            self.bump();
            let p = self.parse_path(PathStyle::Type)?;
            self.expect(TokenKind::Close(Delim::Paren))?;
            p
        } else {
            self.parse_path(PathStyle::Type)?
        };
        Ok(GenericBound::Trait(PolyTraitRef {
            bound_generic_params,
            modifiers,
            trait_ref: TraitRef {
                path,
                ref_id: NodeId::DUMMY,
            },
            span: lo.to(self.prev_token.span),
            parens: false,
        }))
    }

    pub(crate) fn check_start_at(&self, n: usize, kind: TokenKind) -> bool {
        let t = self.look(n);
        t.kind == kind || t.split_first().is_some_and(|(f, _)| f == kind)
    }
}

/// A pattern (from a `$p:pat` fragment, or parsed as one) as a pattern type's pattern.
fn ty_pat_of(pat: Pat) -> P<TyPat> {
    let kind = match pat.kind {
        PatKind::Range(start, end, include_end) => TyPatKind::Range(
            start.map(|e| {
                Box::new(AnonConst {
                    id: NodeId::DUMMY,
                    value: e,
                })
            }),
            end.map(|e| {
                Box::new(AnonConst {
                    id: NodeId::DUMMY,
                    value: e,
                })
            }),
            include_end,
        ),
        PatKind::Or(alts) => TyPatKind::Or(alts.into_iter().map(|p| ty_pat_of(*p)).collect()),
        PatKind::Paren(p) => return ty_pat_of(*p),
        _ => TyPatKind::Err,
    };
    Box::new(TyPat {
        id: NodeId::DUMMY,
        kind,
        span: pat.span,
    })
}
