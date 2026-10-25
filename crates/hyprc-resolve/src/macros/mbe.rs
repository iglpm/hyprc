//! `macro_rules!` and `macro`: rules, matching and transcription.
//!
//! Matching follows rustc's algorithm exactly, because which macros are accepted (and which
//! are ambiguous) is part of the language: the matcher is flattened into locations and
//! matched by all possible positions at once, token by token. Nonterminals (`$e:expr`, and
//! `$t:tt` too) are parsed by the real parser as black boxes; if one could start at a point
//! where any other position also continues, the call is ambiguous.

use hyprc_span::hygiene::{ExpnId, Transparency};
use hyprc_span::{Diag, DiagCtxt, Edition, FxHashMap, Span, Symbol, SyntaxContext, kw, sym};
use hyprc_syntax::Parser;
use hyprc_syntax::token::{Delim, LitKind, Token, TokenKind};
use std::rc::Rc;
use std::sync::Arc;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FragKind {
    Ident,
    Lifetime,
    Literal,
    Tt,
    Vis,
    Item,
    Block,
    Stmt,
    /// `pat` from 2021 on: or-patterns allowed.
    Pat,
    PatParam,
    /// `expr` from 2024 on: `_` and `const {}` allowed.
    Expr,
    Expr2021,
    Ty,
    Path,
    Meta,
}

impl FragKind {
    fn from_name(name: &str, edition: Edition) -> Option<FragKind> {
        Some(match name {
            "ident" => FragKind::Ident,
            "lifetime" => FragKind::Lifetime,
            "literal" => FragKind::Literal,
            "tt" => FragKind::Tt,
            "vis" => FragKind::Vis,
            "item" => FragKind::Item,
            "block" => FragKind::Block,
            "stmt" => FragKind::Stmt,
            "pat" => FragKind::Pat,
            "pat_param" => FragKind::PatParam,
            "expr" if edition >= Edition::E2024 => FragKind::Expr,
            "expr" | "expr_2021" => FragKind::Expr2021,
            "ty" => FragKind::Ty,
            "path" => FragKind::Path,
            "meta" => FragKind::Meta,
            _ => return None,
        })
    }

    /// Fragments substituted inside invisible delimiters, so they keep their grouping
    /// (`$e * 2` with `$e = 1 + 1`).
    fn wrapped(self) -> bool {
        matches!(
            self,
            FragKind::Expr | FragKind::Expr2021 | FragKind::Ty | FragKind::Pat | FragKind::PatParam
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum RepOp {
    ZeroOrMore,
    OneOrMore,
    ZeroOrOne,
}

/// A matcher or transcriber, as a tree.
#[derive(Clone, Debug)]
enum TTree {
    Token(Token),
    Delimited {
        open: Token,
        close: Token,
        inner: Vec<TTree>,
    },
    /// `$name:kind` in a matcher, `$name` in a transcriber (kind `None`).
    Var {
        name: Symbol,
        kind: Option<FragKind>,
        span: Span,
    },
    Repeat {
        inner: Vec<TTree>,
        sep: Option<Token>,
        op: RepOp,
        span: Span,
    },
    /// `${count($x)}`, `${index()}`, `${len()}`, `${ignore($x)}`, `${concat(a, $b)}`
    MetaVarExpr(MetaVarExpr, Span),
}

#[derive(Clone, Debug)]
enum MetaVarExpr {
    Count(Symbol, usize),
    Index(usize),
    Len(usize),
    Ignore(Symbol),
    Concat(Vec<ConcatPart>),
}

#[derive(Clone, Debug)]
enum ConcatPart {
    Ident(Token),
    Var(Symbol),
}

/// A location in a flattened matcher.
#[derive(Clone, Debug)]
enum Loc {
    Token(Token),
    Delimited,
    Sequence {
        op: RepOp,
        num_vars: usize,
        idx_first_after: usize,
        next_var: usize,
        depth: usize,
    },
    SeqOpNoSep {
        op: RepOp,
        idx_first: usize,
    },
    SeqSep {
        sep: Token,
    },
    SeqOpAfterSep {
        idx_first: usize,
    },
    MetaVar {
        kind: FragKind,
        next_var: usize,
        depth: usize,
    },
    Eof,
}

pub struct Rule {
    locs: Vec<Loc>,
    /// Variable names in matcher order (their index is their slot in the matches).
    vars: Vec<Symbol>,
    transcriber: Vec<TTree>,
    pub span: Span,
}

pub struct MacroRules {
    pub rules: Vec<Rule>,
    pub edition: Edition,
}

/// A matched fragment: its kind and its tokens.
#[derive(Clone, Debug)]
pub struct Fragment {
    pub kind: FragKind,
    pub tokens: Arc<[Token]>,
    pub span: Span,
}

#[derive(Clone, Debug)]
enum NamedMatch {
    Seq(Vec<NamedMatch>),
    Single(Fragment),
}

// -------------------------------------------------------------------------------------------
// Compiling rules

struct DefParser<'t> {
    tokens: &'t [Token],
    pos: usize,
    edition: Edition,
    matcher: bool,
}

fn err(span: Span, msg: impl Into<String>) -> Diag {
    Diag::error(msg).span(span, "")
}

impl DefParser<'_> {
    fn peek(&self) -> Option<Token> {
        self.tokens.get(self.pos).copied()
    }

    fn parse_trees(&mut self, end: Option<Delim>) -> Result<Vec<TTree>, Diag> {
        let mut out = Vec::new();
        while let Some(t) = self.peek() {
            match t.kind {
                TokenKind::Close(d) if Some(d) == end => return Ok(out),
                TokenKind::Close(_) => return Err(err(t.span, "unbalanced delimiter in macro")),
                TokenKind::Open(delim) => {
                    self.pos += 1;
                    let inner = self.parse_trees(Some(delim))?;
                    let close = self
                        .peek()
                        .ok_or_else(|| err(t.span, "unclosed delimiter in macro"))?;
                    self.pos += 1;
                    out.push(TTree::Delimited {
                        open: t,
                        close,
                        inner,
                    });
                }
                TokenKind::Dollar => {
                    self.pos += 1;
                    out.push(self.parse_dollar(t)?);
                }
                _ => {
                    self.pos += 1;
                    out.push(TTree::Token(t));
                }
            }
        }
        if end.is_some() {
            return Err(err(Span::DUMMY, "unclosed delimiter in macro"));
        }
        Ok(out)
    }

    fn parse_dollar(&mut self, dollar: Token) -> Result<TTree, Diag> {
        let Some(next) = self.peek() else {
            return Ok(TTree::Token(dollar));
        };
        match next.kind {
            TokenKind::Open(Delim::Paren) => {
                self.pos += 1;
                let inner = self.parse_trees(Some(Delim::Paren))?;
                self.pos += 1;
                // `$( … ) sep? op`
                let op_of = |t: &Token| match t.kind {
                    TokenKind::Star => Some(RepOp::ZeroOrMore),
                    TokenKind::Plus => Some(RepOp::OneOrMore),
                    TokenKind::Question => Some(RepOp::ZeroOrOne),
                    _ => None,
                };
                let t1 = self
                    .peek()
                    .ok_or_else(|| err(next.span, "expected one of `*`, `+` or `?`"))?;
                if let Some(op) = op_of(&t1) {
                    self.pos += 1;
                    return Ok(TTree::Repeat {
                        inner,
                        sep: None,
                        op,
                        span: dollar.span.to(t1.span),
                    });
                }
                self.pos += 1;
                let t2 = self
                    .peek()
                    .ok_or_else(|| err(t1.span, "expected one of `*`, `+` or `?`"))?;
                match op_of(&t2) {
                    Some(RepOp::ZeroOrOne) => Err(err(
                        t2.span,
                        "the `?` macro repetition operator does not take a separator",
                    )),
                    Some(op) => {
                        self.pos += 1;
                        Ok(TTree::Repeat {
                            inner,
                            sep: Some(t1),
                            op,
                            span: dollar.span.to(t2.span),
                        })
                    }
                    None => Err(err(t2.span, "expected one of `*`, `+` or `?`")),
                }
            }
            TokenKind::Open(Delim::Brace) if !self.matcher => {
                self.pos += 1;
                let start = self.pos;
                let _ = self.parse_trees(Some(Delim::Brace))?;
                let inner = &self.tokens[start..self.pos];
                self.pos += 1;
                Ok(TTree::MetaVarExpr(
                    parse_metavar_expr(inner, next.span)?,
                    dollar.span.to(next.span),
                ))
            }
            TokenKind::Ident | TokenKind::RawIdent => {
                self.pos += 1;
                if next.kind == TokenKind::Ident && next.sym == kw::Crate {
                    // `$crate`: one identifier, resolved to the macro's crate.
                    let span = dollar.span.to(next.span);
                    return Ok(TTree::Token(Token {
                        kind: TokenKind::Ident,
                        sym: kw::DollarCrate,
                        span,
                        ..next
                    }));
                }
                if self.matcher {
                    // `$name:kind`
                    if self.peek().map(|t| t.kind) != Some(TokenKind::Colon) {
                        return Err(err(next.span, "missing fragment specifier"));
                    }
                    self.pos += 1;
                    let kind_tok = self
                        .peek()
                        .ok_or_else(|| err(next.span, "missing fragment specifier"))?;
                    self.pos += 1;
                    let kind = FragKind::from_name(kind_tok.sym.as_str(), self.edition).ok_or_else(|| {
                        err(kind_tok.span, format!("invalid fragment specifier `{}`", kind_tok.sym))
                            .help("valid fragment specifiers are `ident`, `block`, `stmt`, `expr`, `pat`, `ty`, `lifetime`, `literal`, `path`, `meta`, `tt`, `item` and `vis`")
                    })?;
                    Ok(TTree::Var {
                        name: next.sym,
                        kind: Some(kind),
                        span: dollar.span.to(kind_tok.span),
                    })
                } else {
                    Ok(TTree::Var {
                        name: next.sym,
                        kind: None,
                        span: dollar.span.to(next.span),
                    })
                }
            }
            _ => Ok(TTree::Token(dollar)),
        }
    }
}

fn parse_metavar_expr(tokens: &[Token], span: Span) -> Result<MetaVarExpr, Diag> {
    let name = tokens
        .first()
        .filter(|t| t.is_ident())
        .ok_or_else(|| err(span, "expected a meta-variable expression"))?;
    // Arguments inside `( … )`.
    let args: &[Token] = match tokens.get(1).map(|t| t.kind) {
        Some(TokenKind::Open(Delim::Paren)) => &tokens[2..tokens.len().saturating_sub(1)],
        _ => &[],
    };
    let depth = |args: &[Token]| -> usize {
        args.iter()
            .find(|t| matches!(t.kind, TokenKind::Literal(LitKind::Integer)))
            .and_then(|t| t.sym.as_str().parse().ok())
            .unwrap_or(0)
    };
    let var = |args: &[Token]| -> Result<Symbol, Diag> {
        match args {
            [d, v, ..] if d.kind == TokenKind::Dollar && v.is_ident() => Ok(v.sym),
            _ => Err(err(span, "expected a `$variable` argument")),
        }
    };
    Ok(match name.sym.as_str() {
        "count" => {
            let rest = args
                .iter()
                .position(|t| t.kind == TokenKind::Comma)
                .map_or(&[][..], |i| &args[i + 1..]);
            MetaVarExpr::Count(var(args)?, depth(rest))
        }
        "index" => MetaVarExpr::Index(depth(args)),
        "len" => MetaVarExpr::Len(depth(args)),
        "ignore" => MetaVarExpr::Ignore(var(args)?),
        "concat" => {
            let mut parts = Vec::new();
            let mut i = 0;
            while i < args.len() {
                match args[i].kind {
                    TokenKind::Comma => {}
                    TokenKind::Dollar if i + 1 < args.len() => {
                        parts.push(ConcatPart::Var(args[i + 1].sym));
                        i += 1;
                    }
                    _ => parts.push(ConcatPart::Ident(args[i])),
                }
                i += 1;
            }
            MetaVarExpr::Concat(parts)
        }
        other => {
            return Err(err(
                name.span,
                format!("unrecognized meta-variable expression `{other}`"),
            ));
        }
    })
}

fn compute_locs(trees: &[TTree], locs: &mut Vec<Loc>, vars: &mut Vec<Symbol>, depth: usize) {
    for tree in trees {
        match tree {
            TTree::Token(t) => locs.push(Loc::Token(*t)),
            TTree::Delimited {
                open, close, inner, ..
            } => {
                locs.push(Loc::Delimited);
                locs.push(Loc::Token(*open));
                compute_locs(inner, locs, vars, depth);
                locs.push(Loc::Token(*close));
            }
            TTree::Var { name, kind, .. } => {
                locs.push(Loc::MetaVar {
                    kind: kind.unwrap_or(FragKind::Tt),
                    next_var: vars.len(),
                    depth,
                });
                vars.push(*name);
            }
            TTree::Repeat { inner, sep, op, .. } => {
                let idx_seq = locs.len();
                locs.push(Loc::Eof);
                let next_var = vars.len();
                compute_locs(inner, locs, vars, depth + 1);
                let idx_first = idx_seq + 1;
                match sep {
                    Some(sep) => {
                        locs.push(Loc::SeqSep { sep: *sep });
                        locs.push(Loc::SeqOpAfterSep { idx_first });
                    }
                    None => locs.push(Loc::SeqOpNoSep { op: *op, idx_first }),
                }
                locs[idx_seq] = Loc::Sequence {
                    op: *op,
                    num_vars: vars.len() - next_var,
                    idx_first_after: locs.len(),
                    next_var,
                    depth,
                };
            }
            TTree::MetaVarExpr(..) => {}
        }
    }
}

/// Compiles a macro's rules from its body: `(matcher) => {transcriber}` separated by `;`
/// (`macro_rules!`) or `,` (`macro`).
pub fn compile(body: &[Token], edition: Edition, macro_2_0: bool) -> Result<MacroRules, Diag> {
    let mut rules = Vec::new();
    let mut pos = 0;
    let sep = if macro_2_0 {
        TokenKind::Comma
    } else {
        TokenKind::Semi
    };
    while pos < body.len() {
        let open = body[pos];
        let TokenKind::Open(_) = open.kind else {
            return Err(err(open.span, "expected a macro rule `(…) => {…}`"));
        };
        let (matcher_tokens, after) = group_at(body, pos);
        pos = after;
        if body.get(pos).map(|t| t.kind) != Some(TokenKind::FatArrow) {
            return Err(err(
                body.get(pos).map_or(open.span, |t| t.span),
                "expected `=>` after the matcher",
            ));
        }
        pos += 1;
        let Some(topen) = body.get(pos).copied().filter(|t| t.is_open()) else {
            return Err(err(
                body.get(pos).map_or(open.span, |t| t.span),
                "expected a delimited transcriber",
            ));
        };
        let (trans_tokens, after) = group_at(body, pos);
        pos = after;
        let mut mp = DefParser {
            tokens: matcher_tokens,
            pos: 0,
            edition,
            matcher: true,
        };
        let matcher = mp.parse_trees(None)?;
        let mut tp = DefParser {
            tokens: trans_tokens,
            pos: 0,
            edition,
            matcher: false,
        };
        let transcriber = tp.parse_trees(None)?;
        let mut locs = Vec::new();
        let mut vars = Vec::new();
        compute_locs(&matcher, &mut locs, &mut vars, 0);
        locs.push(Loc::Eof);
        rules.push(Rule {
            locs,
            vars,
            transcriber,
            span: open.span.to(topen.span),
        });
        if body.get(pos).map(|t| t.kind) == Some(sep) {
            pos += 1;
        }
    }
    Ok(MacroRules { rules, edition })
}

/// The tokens inside the group opening at `tokens[pos]`, and the index after its close.
fn group_at(tokens: &[Token], pos: usize) -> (&[Token], usize) {
    let mut depth = 0usize;
    for (i, t) in tokens[pos..].iter().enumerate() {
        match t.kind {
            TokenKind::Open(_) => depth += 1,
            TokenKind::Close(_) => {
                depth -= 1;
                if depth == 0 {
                    return (&tokens[pos + 1..pos + i], pos + i + 1);
                }
            }
            _ => {}
        }
    }
    (&tokens[(pos + 1).min(tokens.len())..], tokens.len())
}

// -------------------------------------------------------------------------------------------
// Matching

#[derive(Clone)]
struct MatcherPos {
    idx: usize,
    matches: Rc<Vec<NamedMatch>>,
}

impl MatcherPos {
    fn push_match(&mut self, var: usize, depth: usize, m: NamedMatch) {
        let matches = Rc::make_mut(&mut self.matches);
        if depth == 0 {
            debug_assert_eq!(var, matches.len());
            matches.push(m);
            return;
        }
        let mut curr = &mut matches[var];
        for _ in 0..depth - 1 {
            match curr {
                NamedMatch::Seq(seq) => curr = seq.last_mut().expect("sequence entered"),
                NamedMatch::Single(_) => unreachable!(),
            }
        }
        match curr {
            NamedMatch::Seq(seq) => seq.push(m),
            NamedMatch::Single(_) => unreachable!(),
        }
    }
}

/// Token equality for matching: kind and text, not position or hygiene.
fn token_eq(a: &Token, b: &Token) -> bool {
    a.kind == b.kind
        && match a.kind {
            TokenKind::Ident
            | TokenKind::RawIdent
            | TokenKind::Lifetime
            | TokenKind::RawLifetime
            | TokenKind::DocComment(..) => a.sym == b.sym,
            TokenKind::Literal(_) => a.sym == b.sym && a.suffix == b.suffix,
            _ => true,
        }
}

fn may_begin_with(kind: FragKind, t: &Token, edition2018: bool) -> bool {
    use TokenKind as K;
    let is_ident = t.is_ident();
    match kind {
        FragKind::Tt | FragKind::Item | FragKind::Stmt => !matches!(t.kind, K::Close(_) | K::Eof),
        FragKind::Ident => is_ident && !(t.kind == K::Ident && t.sym == kw::Underscore),
        FragKind::Lifetime => t.is_lifetime(),
        FragKind::Literal => {
            t.is_lit()
                || t.kind == K::Minus
                || (t.kind == K::Ident && (t.sym == kw::True || t.sym == kw::False))
        }
        FragKind::Vis => {
            matches!(
                t.kind,
                K::Comma | K::Ident | K::RawIdent | K::Lifetime | K::Open(Delim::Invisible)
            ) || can_begin_type(t, edition2018)
        }
        FragKind::Block => matches!(
            t.kind,
            K::Open(Delim::Brace) | K::Open(Delim::Invisible) | K::Lifetime
        ),
        FragKind::Path | FragKind::Meta => matches!(
            t.kind,
            K::PathSep | K::Ident | K::RawIdent | K::Open(Delim::Invisible)
        ),
        FragKind::Pat | FragKind::PatParam => {
            matches!(
                t.kind,
                K::Ident
                    | K::RawIdent
                    | K::Open(Delim::Paren | Delim::Bracket | Delim::Invisible)
                    | K::And
                    | K::Minus
                    | K::AndAnd
                    | K::Literal(_)
                    | K::DotDot
                    | K::DotDotEq
                    | K::DotDotDot
                    | K::PathSep
                    | K::Lt
                    | K::Shl
                    | K::Not
            ) || (t.kind == K::Or && kind == FragKind::Pat)
        }
        FragKind::Expr | FragKind::Expr2021 => {
            if t.kind == K::Ident && t.sym == kw::Let {
                return false;
            }
            if kind == FragKind::Expr2021
                && t.kind == K::Ident
                && (t.sym == kw::Underscore || t.sym == kw::Const)
            {
                return false;
            }
            can_begin_expr(t, edition2018)
        }
        FragKind::Ty => can_begin_type(t, edition2018),
    }
}

fn can_begin_expr(t: &Token, edition2018: bool) -> bool {
    use TokenKind as K;
    match t.kind {
        K::Literal(_)
        | K::Open(_)
        | K::Not
        | K::Minus
        | K::Star
        | K::And
        | K::AndAnd
        | K::Or
        | K::OrOr
        | K::DotDot
        | K::DotDotEq
        | K::DotDotDot
        | K::Lt
        | K::Shl
        | K::PathSep
        | K::Pound
        | K::Lifetime
        | K::RawLifetime
        | K::RawIdent => true,
        K::Ident => {
            !t.sym.is_reserved(edition2018)
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

fn can_begin_type(t: &Token, edition2018: bool) -> bool {
    use TokenKind as K;
    match t.kind {
        K::Open(Delim::Paren | Delim::Bracket | Delim::Invisible)
        | K::Not
        | K::Star
        | K::And
        | K::AndAnd
        | K::Lt
        | K::Shl
        | K::PathSep
        | K::Question
        | K::Lifetime
        | K::RawLifetime
        | K::RawIdent => true,
        K::Ident => {
            !t.sym.is_reserved(edition2018)
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

pub enum MatchError {
    /// No rule matched; the best guess at why (the furthest any rule got).
    NoMatch {
        span: Span,
        message: String,
    },
    /// A rule's nonterminal didn't parse: the parser's error.
    Parse(Diag),
    Ambiguity {
        span: Span,
        message: String,
    },
}

/// The length of the token tree at `tokens[0]`.
fn tt_len(tokens: &[Token]) -> usize {
    match tokens.first().map(|t| t.kind) {
        Some(TokenKind::Open(_)) => group_at(tokens, 0).1,
        Some(TokenKind::Eof) | None => 0,
        _ => 1,
    }
}

fn parse_nonterminal(
    kind: FragKind,
    tokens: &[Token],
    edition: Edition,
) -> Result<(Fragment, usize), Diag> {
    let first = tokens[0];
    let simple = |n: usize| -> (Fragment, usize) {
        let span = first.span.to(tokens[n - 1].span);
        (
            Fragment {
                kind,
                tokens: tokens[..n].into(),
                span,
            },
            n,
        )
    };
    match kind {
        FragKind::Tt => return Ok(simple(tt_len(tokens).max(1))),
        FragKind::Ident | FragKind::Lifetime => return Ok(simple(1)),
        FragKind::Literal => {
            let n = if first.kind == TokenKind::Minus { 2 } else { 1 };
            let lit = tokens.get(n - 1).copied().unwrap_or(first);
            let is_lit = lit.is_lit()
                || (lit.kind == TokenKind::Ident && (lit.sym == kw::True || lit.sym == kw::False));
            if !is_lit {
                return Err(err(lit.span, "expected a literal"));
            }
            return Ok(simple(n));
        }
        _ => {}
    }
    let dcx = DiagCtxt::buffered();
    let mut p = Parser::new(tokens, edition, &dcx);
    let res: Result<(), hyprc_syntax::PErr> = match kind {
        FragKind::Vis => p.parse_visibility().map(drop),
        FragKind::Item => match p.parse_item() {
            Ok(Some(_)) => Ok(()),
            Ok(None) => Err(p.expected("item")),
            Err(e) => Err(e),
        },
        FragKind::Block => p.parse_block().map(drop),
        FragKind::Stmt => match p.parse_stmt_fragment() {
            Ok(Some(_)) => Ok(()),
            Ok(None) => Err(p.expected("statement")),
            Err(e) => Err(e),
        },
        FragKind::Pat => p.parse_pat_allow_top_alt().map(drop),
        FragKind::PatParam => p.parse_pat_no_top_alt().map(drop),
        FragKind::Expr | FragKind::Expr2021 => p.parse_expr().map(drop),
        FragKind::Ty => p.parse_ty().map(drop),
        FragKind::Path => p.parse_path(hyprc_syntax::PathStyle::Type).map(drop),
        FragKind::Meta => p.parse_attr_item().map(drop),
        FragKind::Tt | FragKind::Ident | FragKind::Lifetime | FragKind::Literal => unreachable!(),
    };
    if let Err(e) = res {
        return Err(*e.0);
    }
    if let Some(d) = dcx.take().into_iter().next() {
        return Err(d);
    }
    let Some(n) = p.consumed() else {
        return Err(err(
            p.token.span,
            "a macro fragment can't end in the middle of a token",
        ));
    };
    if n == 0 {
        // An empty `vis`.
        return Ok((
            Fragment {
                kind,
                tokens: Arc::from([]),
                span: first.span.shrink_to_lo(),
            },
            0,
        ));
    }
    let span = first.span.to(tokens[n - 1].span);
    Ok((
        Fragment {
            kind,
            tokens: tokens[..n].into(),
            span,
        },
        n,
    ))
}

impl Rule {
    /// Matches a call's tokens (which end with `Eof`) against this rule.
    fn matches(
        &self,
        input: &[Token],
        edition: Edition,
    ) -> Result<Vec<NamedMatch>, (MatchError, usize)> {
        let locs = &self.locs;
        let mut cur: Vec<MatcherPos> = vec![MatcherPos {
            idx: 0,
            matches: Rc::new(Vec::new()),
        }];
        let mut next: Vec<MatcherPos> = Vec::new();
        let mut bb: Vec<MatcherPos> = Vec::new();
        let mut pos = 0usize;
        let e2018 = edition >= Edition::E2018;
        loop {
            next.clear();
            bb.clear();
            let token = input[pos];
            let mut eof: Option<MatcherPos> = None;
            let mut eof_count = 0;
            while let Some(mut mp) = cur.pop() {
                match &locs[mp.idx] {
                    Loc::Token(t) => {
                        if token_eq(t, &token) {
                            mp.idx += 1;
                            next.push(mp);
                        }
                    }
                    Loc::Delimited => {
                        mp.idx += 1;
                        cur.push(mp);
                    }
                    &Loc::Sequence {
                        op,
                        num_vars,
                        idx_first_after,
                        next_var,
                        depth,
                    } => {
                        for v in next_var..next_var + num_vars {
                            mp.push_match(v, depth, NamedMatch::Seq(Vec::new()));
                        }
                        if op != RepOp::OneOrMore {
                            cur.push(MatcherPos {
                                idx: idx_first_after,
                                matches: mp.matches.clone(),
                            });
                        }
                        mp.idx += 1;
                        cur.push(mp);
                    }
                    &Loc::SeqOpNoSep { op, idx_first } => {
                        cur.push(MatcherPos {
                            idx: mp.idx + 1,
                            matches: mp.matches.clone(),
                        });
                        if op != RepOp::ZeroOrOne {
                            mp.idx = idx_first;
                            cur.push(mp);
                        }
                    }
                    Loc::SeqSep { sep } => {
                        cur.push(MatcherPos {
                            idx: mp.idx + 2,
                            matches: mp.matches.clone(),
                        });
                        if token_eq(sep, &token) {
                            mp.idx += 1;
                            next.push(mp);
                        }
                    }
                    &Loc::SeqOpAfterSep { idx_first } => {
                        mp.idx = idx_first;
                        cur.push(mp);
                    }
                    &Loc::MetaVar { kind, .. } => {
                        if may_begin_with(kind, &token, e2018) {
                            bb.push(mp);
                        }
                    }
                    Loc::Eof => {
                        if token.kind == TokenKind::Eof {
                            eof_count += 1;
                            eof = Some(mp);
                        }
                    }
                }
            }
            if token.kind == TokenKind::Eof {
                return match (eof_count, eof) {
                    (1, Some(mp)) => {
                        Ok(Rc::try_unwrap(mp.matches).unwrap_or_else(|rc| (*rc).clone()))
                    }
                    (0, _) => Err((
                        MatchError::NoMatch {
                            span: token.span,
                            message: "unexpected end of macro invocation".into(),
                        },
                        pos,
                    )),
                    _ => Err((
                        MatchError::Ambiguity {
                            span: token.span,
                            message: "ambiguity: multiple successful parses".into(),
                        },
                        pos,
                    )),
                };
            }
            match (next.len(), bb.len()) {
                (0, 0) => {
                    let what = hyprc_syntax::Parser::describe_token(&token);
                    return Err((
                        MatchError::NoMatch {
                            span: token.span,
                            message: format!("no rules expected {what}"),
                        },
                        pos,
                    ));
                }
                (_, 0) => {
                    std::mem::swap(&mut cur, &mut next);
                    pos += 1;
                }
                (0, 1) => {
                    let mut mp = bb.pop().unwrap();
                    let Loc::MetaVar {
                        kind,
                        next_var,
                        depth,
                    } = locs[mp.idx]
                    else {
                        unreachable!()
                    };
                    match parse_nonterminal(kind, &input[pos..], edition) {
                        Ok((frag, consumed)) => {
                            mp.push_match(next_var, depth, NamedMatch::Single(frag));
                            mp.idx += 1;
                            cur.push(mp);
                            pos += consumed;
                        }
                        Err(d) => return Err((MatchError::Parse(d), pos)),
                    }
                }
                _ => {
                    let names: Vec<String> = bb
                        .iter()
                        .filter_map(|mp| match locs[mp.idx] {
                            Loc::MetaVar { next_var, kind, .. } => {
                                Some(format!("`{}:{kind:?}`", self.vars[next_var]).to_lowercase())
                            }
                            _ => None,
                        })
                        .collect();
                    return Err((
                        MatchError::Ambiguity {
                            span: token.span,
                            message: format!(
                                "local ambiguity when calling macro: multiple parsing options: built-in NTs {} or {} other option(s)",
                                names.join(", "),
                                next.len()
                            ),
                        },
                        pos,
                    ));
                }
            }
        }
    }
}

// -------------------------------------------------------------------------------------------
// Transcription

struct Transcriber<'a> {
    rule: &'a Rule,
    matches: &'a [NamedMatch],
    expn: ExpnId,
    transparency: Transparency,
    /// The current iteration index at each repetition depth, and the counts.
    repeats: Vec<(usize, usize)>,
    marks: FxHashMap<SyntaxContext, SyntaxContext>,
    out: Vec<Token>,
}

impl Transcriber<'_> {
    fn mark(&mut self, mut t: Token) -> Token {
        let ctxt = t.span.ctxt;
        let marked = match self.marks.get(&ctxt) {
            Some(&c) => c,
            None => {
                let c = ctxt.apply_mark(self.expn, self.transparency);
                self.marks.insert(ctxt, c);
                c
            }
        };
        t.span = t.span.with_ctxt(marked);
        t
    }

    fn var_index(&self, name: Symbol) -> Option<usize> {
        self.rule.vars.iter().position(|&v| v == name)
    }

    /// The match for a variable at the current repetition position.
    fn lookup(&self, idx: usize) -> &NamedMatch {
        let mut m = &self.matches[idx];
        for &(i, _) in &self.repeats {
            match m {
                NamedMatch::Seq(v) => match v.get(i) {
                    Some(x) => m = x,
                    None => return m,
                },
                NamedMatch::Single(_) => return m,
            }
        }
        m
    }

    /// How many times a repetition runs: the length all repeating variables inside agree on.
    fn repeat_count(&self, trees: &[TTree], span: Span) -> Result<usize, Diag> {
        let mut count: Option<(usize, Symbol)> = None;
        let mut names = Vec::new();
        collect_vars(trees, &mut names);
        for name in names {
            let Some(idx) = self.var_index(name) else {
                continue;
            };
            if let NamedMatch::Seq(v) = self.lookup(idx) {
                match count {
                    None => count = Some((v.len(), name)),
                    Some((n, other)) if n != v.len() => {
                        return Err(err(
                            span,
                            format!(
                                "meta-variable `{other}` repeats {n} times, but `{name}` repeats {} times",
                                v.len()
                            ),
                        ));
                    }
                    _ => {}
                }
            }
        }
        count.map(|(n, _)| n).ok_or_else(|| {
            err(span, "attempted to repeat an expression containing no syntax variables matched as repeating at this depth")
        })
    }

    fn transcribe(&mut self, trees: &[TTree]) -> Result<(), Diag> {
        for tree in trees {
            match tree {
                TTree::Token(t) => {
                    let t = self.mark(*t);
                    self.out.push(t);
                }
                TTree::Delimited {
                    open, close, inner, ..
                } => {
                    let o = self.mark(*open);
                    self.out.push(o);
                    self.transcribe(inner)?;
                    let c = self.mark(*close);
                    self.out.push(c);
                }
                TTree::Var { name, span, .. } => match self.var_index(*name) {
                    None => {
                        // Not a variable of this rule: `$name` stays as written.
                        let dollar = Token::new(TokenKind::Dollar, *span);
                        let d = self.mark(dollar);
                        self.out.push(d);
                        let ident = self.mark(Token::ident(*name, *span));
                        self.out.push(ident);
                    }
                    Some(idx) => match self.lookup(idx).clone() {
                        NamedMatch::Single(frag) => {
                            if frag.kind.wrapped() {
                                self.out
                                    .push(Token::new(TokenKind::Open(Delim::Invisible), frag.span));
                                self.out.extend_from_slice(&frag.tokens);
                                self.out.push(Token::new(
                                    TokenKind::Close(Delim::Invisible),
                                    frag.span,
                                ));
                            } else {
                                self.out.extend_from_slice(&frag.tokens);
                            }
                        }
                        NamedMatch::Seq(_) => {
                            return Err(err(
                                *span,
                                format!("variable `{name}` is still repeating at this depth"),
                            ));
                        }
                    },
                },
                TTree::Repeat {
                    inner,
                    sep,
                    op,
                    span,
                } => {
                    let n = self.repeat_count(inner, *span)?;
                    if *op == RepOp::OneOrMore && n == 0 {
                        // rustc accepts this silently when the matcher allowed it.
                    }
                    for i in 0..n {
                        self.repeats.push((i, n));
                        self.transcribe(inner)?;
                        self.repeats.pop();
                        if i + 1 < n
                            && let Some(sep) = sep
                        {
                            let s = self.mark(*sep);
                            self.out.push(s);
                        }
                    }
                }
                TTree::MetaVarExpr(expr, span) => self.metavar_expr(expr, *span)?,
            }
        }
        Ok(())
    }

    fn metavar_expr(&mut self, expr: &MetaVarExpr, span: Span) -> Result<(), Diag> {
        let int = |n: usize, span: Span| Token {
            kind: TokenKind::Literal(LitKind::Integer),
            joint: false,
            sym: Symbol::intern(&n.to_string()),
            suffix: kw::Empty,
            span,
        };
        match expr {
            MetaVarExpr::Index(depth) => {
                let Some(&(i, _)) = self.repeats.iter().rev().nth(*depth) else {
                    return Err(err(span, "`index` used outside a repetition"));
                };
                let t = self.mark(int(i, span));
                self.out.push(t);
            }
            MetaVarExpr::Len(depth) => {
                let Some(&(_, n)) = self.repeats.iter().rev().nth(*depth) else {
                    return Err(err(span, "`len` used outside a repetition"));
                };
                let t = self.mark(int(n, span));
                self.out.push(t);
            }
            MetaVarExpr::Ignore(_) => {}
            MetaVarExpr::Count(name, depth) => {
                let idx = self
                    .var_index(*name)
                    .ok_or_else(|| err(span, format!("unknown variable `{name}`")))?;
                fn count(m: &NamedMatch, depth: usize) -> usize {
                    match m {
                        NamedMatch::Seq(v) if depth == 0 => v.len(),
                        NamedMatch::Seq(v) => v.iter().map(|x| count(x, depth - 1)).sum(),
                        NamedMatch::Single(_) => 1,
                    }
                }
                let n = count(self.lookup(idx), *depth);
                let t = self.mark(int(n, span));
                self.out.push(t);
            }
            MetaVarExpr::Concat(parts) => {
                let mut s = String::new();
                let mut ctxt_tok: Option<Token> = None;
                for part in parts {
                    match part {
                        ConcatPart::Ident(t) => {
                            s.push_str(t.sym.as_str());
                            ctxt_tok.get_or_insert(*t);
                        }
                        ConcatPart::Var(name) => {
                            let idx = self
                                .var_index(*name)
                                .ok_or_else(|| err(span, format!("unknown variable `{name}`")))?;
                            match self.lookup(idx) {
                                NamedMatch::Single(f) if !f.tokens.is_empty() => {
                                    let t = f.tokens[0];
                                    s.push_str(t.sym.as_str());
                                }
                                _ => {
                                    return Err(err(
                                        span,
                                        "`concat` takes identifiers and literals",
                                    ));
                                }
                            }
                        }
                    }
                }
                let t = Token::ident(Symbol::intern(&s), span);
                let t = self.mark(t);
                self.out.push(t);
            }
        }
        Ok(())
    }
}

fn collect_vars(trees: &[TTree], out: &mut Vec<Symbol>) {
    for t in trees {
        match t {
            TTree::Var { name, .. } => out.push(*name),
            TTree::Delimited { inner, .. } | TTree::Repeat { inner, .. } => {
                collect_vars(inner, out)
            }
            TTree::MetaVarExpr(MetaVarExpr::Count(n, _) | MetaVarExpr::Ignore(n), _) => {
                out.push(*n)
            }
            TTree::MetaVarExpr(MetaVarExpr::Concat(parts), _) => {
                for p in parts {
                    if let ConcatPart::Var(n) = p {
                        out.push(*n);
                    }
                }
            }
            _ => {}
        }
    }
}

/// Doc comments in macro input are `#[doc = r"…"]` attributes to matchers (`$(#[$m:meta])*`
/// takes them), as in rustc.
fn desugar_doc_comments(args: &[Token]) -> Vec<Token> {
    use hyprc_syntax::token::AttrStyle;
    if !args
        .iter()
        .any(|t| matches!(t.kind, TokenKind::DocComment(..)))
    {
        return args.to_vec();
    }
    let mut out = Vec::with_capacity(args.len() + 8);
    for t in args {
        let TokenKind::DocComment(style, _) = t.kind else {
            out.push(*t);
            continue;
        };
        let text = t.sym.as_str();
        // Enough `#`s that the text can't end the raw string.
        let mut hashes = 0u8;
        while text.contains(&format!("\"{}", "#".repeat(hashes as usize))) {
            hashes += 1;
        }
        out.push(Token::new(TokenKind::Pound, t.span));
        if style == AttrStyle::Inner {
            out.push(Token::new(TokenKind::Not, t.span));
        }
        out.push(Token::new(TokenKind::Open(Delim::Bracket), t.span));
        out.push(Token::ident(sym::doc, t.span));
        out.push(Token::new(TokenKind::Eq, t.span));
        out.push(Token {
            kind: TokenKind::Literal(LitKind::StrRaw(hashes)),
            joint: false,
            sym: t.sym,
            suffix: kw::Empty,
            span: t.span,
        });
        out.push(Token::new(TokenKind::Close(Delim::Bracket), t.span));
    }
    out
}

impl MacroRules {
    /// Expands a call: tries each rule in order; the first that matches is transcribed with
    /// its tokens marked by `expn`.
    pub fn expand(
        &self,
        args: &[Token],
        call_span: Span,
        expn: ExpnId,
        transparency: Transparency,
    ) -> Result<Vec<Token>, Diag> {
        let mut input = desugar_doc_comments(args);
        input.push(Token::new(TokenKind::Eof, call_span.shrink_to_hi()));
        let mut best: Option<(MatchError, usize)> = None;
        for rule in &self.rules {
            match rule.matches(&input, self.edition) {
                Ok(matches) => {
                    let mut t = Transcriber {
                        rule,
                        matches: &matches,
                        expn,
                        transparency,
                        repeats: Vec::new(),
                        marks: FxHashMap::default(),
                        out: Vec::with_capacity(rule.transcriber.len() * 2),
                    };
                    t.transcribe(&rule.transcriber)?;
                    return Ok(t.out);
                }
                Err((e, pos)) => {
                    // An ambiguity is an error at once, as in rustc.
                    if let MatchError::Ambiguity { span, message } = e {
                        return Err(Diag::error(message).span(span, ""));
                    }
                    if best.as_ref().is_none_or(|(_, p)| pos > *p) {
                        best = Some((e, pos));
                    }
                }
            }
        }
        Err(match best {
            Some((MatchError::NoMatch { span, message }, _)) => Diag::error(message)
                .span(span, "no rules expected this token in macro call")
                .label(call_span, "when calling this macro"),
            Some((MatchError::Parse(d), _)) => d,
            Some((MatchError::Ambiguity { span, message }, _)) => {
                Diag::error(message).span(span, "")
            }
            None => Diag::error("this macro has no rules").span(call_span, ""),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use hyprc_syntax::token::token_text;

    fn toks(src: &str) -> Vec<Token> {
        let dcx = DiagCtxt::buffered();
        let mut t = hyprc_syntax::tokenize(src, 1, &dcx);
        t.pop();
        t
    }

    fn expand(rules: &str, call: &str) -> Result<String, String> {
        let m = compile(&toks(rules), Edition::E2021, false).map_err(|d| d.message)?;
        let out = m
            .expand(
                &toks(call),
                Span::DUMMY,
                ExpnId::ROOT,
                Transparency::SemiTransparent,
            )
            .map_err(|d| d.message)?;
        Ok(out
            .iter()
            .filter(|t| {
                !matches!(
                    t.kind,
                    TokenKind::Open(Delim::Invisible) | TokenKind::Close(Delim::Invisible)
                )
            })
            .map(token_text)
            .collect::<Vec<_>>()
            .join(" "))
    }

    #[test]
    fn simple_and_repetition() {
        assert_eq!(expand("() => { 1 }", "").unwrap(), "1");
        assert_eq!(
            expand("($a:expr, $b:expr) => { $a + $b }", "1, 2 * 3").unwrap(),
            "1 + 2 * 3"
        );
        assert_eq!(
            expand(
                "($($k:ident = $v:expr),* $(,)?) => { [$(($k, $v)),*] }",
                "a = 1, b = 2,"
            )
            .unwrap(),
            "[ ( a , 1 ) , ( b , 2 ) ]"
        );
        assert_eq!(
            expand("($($x:tt)*) => { $($x)* }", "a >>= ( b )").unwrap(),
            "a >>= ( b )"
        );
    }

    #[test]
    fn nested_repetition_and_rules() {
        let rules =
            "($($n:ident: [$($v:literal),*]);*) => { $(fn $n() { $($v;)* })* }; (x) => { y }";
        assert_eq!(
            expand(rules, "f: [1, 2]; g: []").unwrap(),
            "fn f ( ) { 1 ; 2 ; } fn g ( ) { }"
        );
        assert_eq!(expand(rules, "x").unwrap(), "y");
    }

    #[test]
    fn errors() {
        assert!(
            expand("(a) => {}", "b")
                .unwrap_err()
                .contains("no rules expected")
        );
        assert!(
            expand("($($t:tt)* ; $e:expr) => {}", "a ; 1")
                .unwrap_err()
                .contains("local ambiguity")
        );
        assert_eq!(
            expand("($e:expr) => {}", "").unwrap_err(),
            "unexpected end of macro invocation"
        );
    }

    #[test]
    fn metavar_exprs_and_dollar_crate() {
        assert_eq!(
            expand("($($x:ident),*) => { ${count($x)} }", "a, b, c").unwrap(),
            "3"
        );
        assert_eq!(
            expand(
                "($($x:ident),*) => { $(${ignore($x)} ${index()})* }",
                "a, b"
            )
            .unwrap(),
            "0 1"
        );
        assert_eq!(
            expand("() => { $crate::f() }", "").unwrap(),
            "$crate :: f ( )"
        );
    }
}
