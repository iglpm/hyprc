//! Conditional compilation: `#[cfg(...)]`, `#[cfg_attr(...)]` and `cfg!(...)`.

use hyprc_span::session::Session;
use hyprc_span::{Diag, DiagCtxt, Span, Symbol, kw};
use hyprc_syntax::ast::{AttrArgs, AttrItem, AttrKind, Attribute, DelimArgs, Safety};
use hyprc_syntax::token::{Delim, LitKind, Token, TokenKind};
use hyprc_syntax::{Edition, Parser};

fn is_named(attr: &Attribute, name: &str) -> bool {
    match &attr.kind {
        AttrKind::Normal(item) => {
            item.path.segments.len() == 1 && item.path.segments[0].ident.as_str() == name
        }
        _ => false,
    }
}

/// A `cfg` predicate.
#[derive(Debug, Clone)]
pub enum CfgPred {
    Name(Symbol, Option<Symbol>),
    All(Vec<CfgPred>),
    Any(Vec<CfgPred>),
    Not(Box<CfgPred>),
    Bool(bool),
    /// `version("1.80")`: true for any version hyprc tracks (it follows the current release).
    Version(Symbol),
    /// `target(os = "linux", arch = "x86_64")`
    Target(Vec<(Symbol, Symbol)>),
    /// `accessible(path)` (unstable): assume accessible.
    Accessible,
}

pub trait CfgContext {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool;
}

impl<T: CfgContext + ?Sized> CfgContext for &T {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        (**self).cfg_set(name, value)
    }
}

impl CfgContext for Session {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        self.cfg.contains(&(name, value))
    }
}

impl CfgContext for hyprc_span::FxHashSet<(Symbol, Option<Symbol>)> {
    fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        self.contains(&(name, value))
    }
}

impl CfgPred {
    pub fn eval_with<C: CfgContext + ?Sized>(&self, ctx: &C) -> bool {
        match self {
            CfgPred::Name(name, value) => ctx.cfg_set(*name, *value),
            CfgPred::All(ps) => ps.iter().all(|p| p.eval_with(ctx)),
            CfgPred::Any(ps) => ps.iter().any(|p| p.eval_with(ctx)),
            CfgPred::Not(p) => !p.eval_with(ctx),
            CfgPred::Bool(b) => *b,
            CfgPred::Version(_) => true,
            CfgPred::Target(pairs) => pairs
                .iter()
                .all(|(k, v)| ctx.cfg_set(Symbol::intern(&format!("target_{k}")), Some(*v))),
            CfgPred::Accessible => true,
        }
    }

    pub fn eval(&self, sess: &Session) -> bool {
        self.eval_with(sess)
    }
}

/// Parses a cfg predicate from the tokens inside `cfg(…)`: exactly one predicate, optionally
/// followed by a comma.
pub fn parse_cfg_pred(tokens: &[Token], span: Span) -> Result<CfgPred, Diag> {
    let mut pos = 0;
    let pred = parse_pred(tokens, &mut pos, span)?;
    if pos < tokens.len() && tokens[pos].kind == TokenKind::Comma {
        pos += 1;
    }
    if pos != tokens.len() {
        return Err(Diag::error("expected a single cfg predicate").span(tokens[pos].span, ""));
    }
    Ok(pred)
}

fn strip_invisible(tokens: &[Token], pos: &mut usize) -> usize {
    let mut n = 0;
    while *pos < tokens.len() && tokens[*pos].kind == TokenKind::Open(Delim::Invisible) {
        *pos += 1;
        n += 1;
    }
    n
}

fn parse_pred(tokens: &[Token], pos: &mut usize, span: Span) -> Result<CfgPred, Diag> {
    let opened = strip_invisible(tokens, pos);
    let Some(t) = tokens.get(*pos).copied() else {
        return Err(Diag::error("expected a cfg predicate").span(span, ""));
    };
    let pred = match t.kind {
        TokenKind::Ident if t.sym == kw::True || t.sym == kw::False => {
            *pos += 1;
            CfgPred::Bool(t.sym == kw::True)
        }
        TokenKind::Ident | TokenKind::RawIdent => {
            *pos += 1;
            // A path: only single segments are meaningful; `a::b` is never set.
            let mut name = t.sym;
            let mut multi = false;
            while tokens.get(*pos).map(|t| t.kind) == Some(TokenKind::PathSep) {
                *pos += 2;
                multi = true;
                name = tokens.get(*pos - 1).map_or(name, |t| t.sym);
            }
            match tokens.get(*pos).map(|t| t.kind) {
                Some(TokenKind::Eq) => {
                    *pos += 1;
                    let val_opened = strip_invisible(tokens, pos);
                    let Some(v) = tokens.get(*pos).copied() else {
                        return Err(Diag::error("expected a string after `=`").span(t.span, ""));
                    };
                    let value = match v.kind {
                        TokenKind::Literal(LitKind::Str | LitKind::StrRaw(_)) => v.sym,
                        _ => {
                            return Err(
                                Diag::error("cfg values must be string literals").span(v.span, "")
                            );
                        }
                    };
                    *pos += 1;
                    for _ in 0..val_opened {
                        if tokens.get(*pos).map(|t| t.kind)
                            == Some(TokenKind::Close(Delim::Invisible))
                        {
                            *pos += 1;
                        }
                    }
                    if multi {
                        CfgPred::Bool(false)
                    } else {
                        CfgPred::Name(name, Some(value))
                    }
                }
                Some(TokenKind::Open(Delim::Paren)) => {
                    let inner = group(tokens, pos);
                    let mut ipos = 0;
                    let mut items = Vec::new();
                    let name_str = name.as_str();
                    match name_str {
                        "all" | "any" | "not" => {
                            while ipos < inner.len() {
                                items.push(parse_pred(inner, &mut ipos, t.span)?);
                                if ipos < inner.len() {
                                    if inner[ipos].kind != TokenKind::Comma {
                                        return Err(Diag::error("expected `,` in cfg predicate")
                                            .span(inner[ipos].span, ""));
                                    }
                                    ipos += 1;
                                }
                            }
                            match name_str {
                                "all" => CfgPred::All(items),
                                "any" => CfgPred::Any(items),
                                _ => {
                                    if items.len() != 1 {
                                        return Err(Diag::error(
                                            "`not` takes exactly one predicate",
                                        )
                                        .span(t.span, ""));
                                    }
                                    CfgPred::Not(Box::new(items.pop().unwrap()))
                                }
                            }
                        }
                        "version" => {
                            let v = inner.first().map_or(kw::Empty, |t| t.sym);
                            CfgPred::Version(v)
                        }
                        "target" => {
                            let mut pairs = Vec::new();
                            while ipos + 2 < inner.len() + 1 && ipos < inner.len() {
                                let k = inner[ipos].sym;
                                let v = inner.get(ipos + 2).map_or(kw::Empty, |t| t.sym);
                                pairs.push((k, v));
                                ipos += 3;
                                if inner.get(ipos).map(|t| t.kind) == Some(TokenKind::Comma) {
                                    ipos += 1;
                                }
                            }
                            CfgPred::Target(pairs)
                        }
                        "accessible" => CfgPred::Accessible,
                        _ => {
                            return Err(Diag::error(format!("invalid predicate `{name_str}`"))
                                .span(t.span, ""));
                        }
                    }
                }
                _ => {
                    if multi {
                        CfgPred::Bool(false)
                    } else {
                        CfgPred::Name(name, None)
                    }
                }
            }
        }
        _ => return Err(Diag::error("expected a cfg predicate").span(t.span, "")),
    };
    for _ in 0..opened {
        if tokens.get(*pos).map(|t| t.kind) == Some(TokenKind::Close(Delim::Invisible)) {
            *pos += 1;
        }
    }
    Ok(pred)
}

/// The tokens inside the group starting at `tokens[*pos]`; moves past the group.
fn group<'t>(tokens: &'t [Token], pos: &mut usize) -> &'t [Token] {
    let start = *pos + 1;
    let mut depth = 0usize;
    let mut i = *pos;
    while i < tokens.len() {
        match tokens[i].kind {
            TokenKind::Open(_) => depth += 1,
            TokenKind::Close(_) => {
                depth -= 1;
                if depth == 0 {
                    *pos = i + 1;
                    return &tokens[start..i];
                }
            }
            _ => {}
        }
        i += 1;
    }
    *pos = tokens.len();
    &tokens[start.min(tokens.len())..]
}

/// Splits tokens at top-level commas.
pub fn split_commas(tokens: &[Token]) -> Vec<&[Token]> {
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (i, t) in tokens.iter().enumerate() {
        match t.kind {
            TokenKind::Open(_) => depth += 1,
            TokenKind::Close(_) => depth = depth.saturating_sub(1),
            TokenKind::Comma if depth == 0 => {
                parts.push(&tokens[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    if start < tokens.len() {
        parts.push(&tokens[start..]);
    }
    parts
}

/// Evaluates a `cfg(…)` attribute's arguments with a CfgContext.
pub fn eval_cfg_args_ctx<C: CfgContext + ?Sized>(
    ctx: &C,
    dcx: &DiagCtxt,
    args: &DelimArgs,
) -> bool {
    match parse_cfg_pred(args.tokens.tokens(), args.open) {
        Ok(p) => p.eval_with(ctx),
        Err(d) => {
            dcx.emit(d);
            true
        }
    }
}

pub fn eval_cfg_args(sess: &Session, dcx: &DiagCtxt, args: &DelimArgs) -> bool {
    eval_cfg_args_ctx(sess, dcx, args)
}

/// Replaces every `#[cfg_attr(pred, a, b)]` by `#[a] #[b]` when `pred` holds and by nothing
/// otherwise, recursively, using a CfgContext.
pub fn expand_cfg_attrs_ctx<C: CfgContext + ?Sized>(
    ctx: &C,
    dcx: &DiagCtxt,
    edition: Edition,
    attrs: &mut Vec<Attribute>,
) {
    if !attrs.iter().any(|a| is_named(a, "cfg_attr")) {
        return;
    }
    let old = std::mem::take(attrs);
    for attr in old {
        if !is_named(&attr, "cfg_attr") {
            attrs.push(attr);
            continue;
        }
        let AttrKind::Normal(item) = &attr.kind else {
            continue;
        };
        let AttrArgs::Delimited(args) = &item.args else {
            dcx.emit(Diag::error("malformed `cfg_attr` attribute").span(attr.span, ""));
            continue;
        };
        let parts = split_commas(args.tokens.tokens());
        let Some((pred_tokens, rest)) = parts.split_first() else {
            dcx.emit(Diag::error("malformed `cfg_attr` attribute").span(attr.span, ""));
            continue;
        };
        let pred = match parse_cfg_pred(pred_tokens, attr.span) {
            Ok(p) => p,
            Err(d) => {
                dcx.emit(d);
                continue;
            }
        };
        if !pred.eval_with(ctx) {
            continue;
        }
        let mut produced = Vec::new();
        for part in rest {
            if part.is_empty() {
                continue;
            }
            let mut toks = part.to_vec();
            toks.push(Token::new(TokenKind::Eof, attr.span.shrink_to_hi()));
            let mut p = Parser::new(&toks, edition, dcx);
            match p.parse_attr_item() {
                Ok(item) => produced.push(Attribute {
                    kind: AttrKind::Normal(Box::new(item)),
                    style: attr.style,
                    span: attr.span,
                }),
                Err(e) => p.emit(e),
            }
        }
        expand_cfg_attrs_ctx(ctx, dcx, edition, &mut produced);
        attrs.extend(produced);
    }
}

pub fn expand_cfg_attrs(sess: &Session, edition: Edition, attrs: &mut Vec<Attribute>) {
    expand_cfg_attrs_ctx(sess, &sess.dcx, edition, attrs)
}

pub fn expand_cfg_attrs_with(
    sess: &Session,
    dcx: &DiagCtxt,
    edition: Edition,
    attrs: &mut Vec<Attribute>,
) {
    expand_cfg_attrs_ctx(sess, dcx, edition, attrs)
}

/// Do all `#[cfg]`s on these (already `cfg_attr`-expanded) attributes hold?
pub fn cfg_holds_ctx<C: CfgContext + ?Sized>(ctx: &C, dcx: &DiagCtxt, attrs: &[Attribute]) -> bool {
    attrs.iter().all(|a| {
        if !is_named(a, "cfg") {
            return true;
        }
        let AttrKind::Normal(item) = &a.kind else {
            return true;
        };
        match &item.args {
            AttrArgs::Delimited(args) => eval_cfg_args_ctx(ctx, dcx, args),
            _ => {
                dcx.emit(Diag::error("`cfg` takes a predicate: `#[cfg(...)]`").span(a.span, ""));
                true
            }
        }
    })
}

pub fn cfg_holds(sess: &Session, attrs: &[Attribute]) -> bool {
    cfg_holds_ctx(sess, &sess.dcx, attrs)
}

pub fn cfg_holds_with(sess: &Session, dcx: &DiagCtxt, attrs: &[Attribute]) -> bool {
    cfg_holds_ctx(sess, dcx, attrs)
}

/// `cfg_attr` expansion and `cfg` check in one step; returns whether to keep the node.
pub fn process_attrs_ctx<C: CfgContext + ?Sized>(
    ctx: &C,
    dcx: &DiagCtxt,
    edition: Edition,
    attrs: &mut Vec<Attribute>,
) -> bool {
    expand_cfg_attrs_ctx(ctx, dcx, edition, attrs);
    cfg_holds_ctx(ctx, dcx, attrs)
}

pub fn process_attrs(sess: &Session, edition: Edition, attrs: &mut Vec<Attribute>) -> bool {
    process_attrs_ctx(sess, &sess.dcx, edition, attrs)
}

/// The value of a `#[name = "value"]` attribute, if it has that shape.
pub fn attr_str_value(attr: &Attribute) -> Option<Symbol> {
    let AttrKind::Normal(item) = &attr.kind else {
        return None;
    };
    match &item.args {
        AttrArgs::Eq(_, e) => match &e.kind {
            hyprc_syntax::ast::ExprKind::Lit(lit)
                if matches!(lit.kind, LitKind::Str | LitKind::StrRaw(_)) =>
            {
                Some(lit.symbol)
            }
            _ => None,
        },
        _ => None,
    }
}

pub fn find_attr<'a>(attrs: &'a [Attribute], name: &str) -> Option<&'a Attribute> {
    attrs.iter().find(|a| is_named(a, name))
}

pub fn has_attr(attrs: &[Attribute], name: &str) -> bool {
    attrs.iter().any(|a| is_named(a, name))
}

/// The attribute item of a normal attribute.
pub fn attr_item(attr: &Attribute) -> Option<&AttrItem> {
    match &attr.kind {
        AttrKind::Normal(item) => Some(item),
        _ => None,
    }
}

/// `#[unsafe(no_mangle)]` and `#[no_mangle]` alike.
pub fn is_unsafe_attr(item: &AttrItem) -> bool {
    matches!(item.unsafety, Safety::Unsafe(_))
}
