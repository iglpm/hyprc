//! Tokens.
//!
//! Punctuation is glued the way rustc glues it (`>>=` is one token), because that is what
//! `macro_rules!` matchers see: `$t:tt` matches `>>=` whole. The parser splits glued tokens
//! where the grammar needs their parts (`Vec<Vec<u8>>` closes two generic lists).

use hyprc_span::{Span, Symbol, kw};
use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Delim {
    Paren,
    Brace,
    Bracket,
    /// Groups the tokens a macro substituted for one `$fragment`, so `$e * 2` keeps `$e`
    /// together the way parentheses would. Never written in source.
    Invisible,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum LitKind {
    Bool,
    Byte,
    Char,
    Integer,
    Float,
    Str,
    /// The number of `#`s.
    StrRaw(u8),
    ByteStr,
    ByteStrRaw(u8),
    CStr,
    CStrRaw(u8),
    /// A literal the lexer had to recover from; an error was already reported.
    Err,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum AttrStyle {
    Outer,
    Inner,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum CommentKind {
    Line,
    Block,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TokenKind {
    // One- and multi-character punctuation.
    Eq,
    Lt,
    Le,
    EqEq,
    Ne,
    Ge,
    Gt,
    AndAnd,
    OrOr,
    Not,
    Tilde,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    Caret,
    And,
    Or,
    Shl,
    Shr,
    PlusEq,
    MinusEq,
    StarEq,
    SlashEq,
    PercentEq,
    CaretEq,
    AndEq,
    OrEq,
    ShlEq,
    ShrEq,
    At,
    Dot,
    DotDot,
    DotDotDot,
    DotDotEq,
    Comma,
    Semi,
    Colon,
    PathSep,
    RArrow,
    LArrow,
    FatArrow,
    Pound,
    Dollar,
    Question,
    /// A lone `'`: only in macro output (proc macros can make one).
    SingleQuote,
    Open(Delim),
    Close(Delim),
    /// A name or keyword; `sym` is the name.
    Ident,
    /// `r#name`; `sym` is the name without `r#`. Never a keyword.
    RawIdent,
    /// `'name`; `sym` includes the quote.
    Lifetime,
    /// `'r#name`; `sym` is `'name`.
    RawLifetime,
    /// `sym` is the literal's text without quotes or prefix, escapes unprocessed.
    Literal(LitKind),
    /// `sym` is the comment's text after `///`, `//!`, `/**` or `/*!`.
    DocComment(AttrStyle, CommentKind),
    Eof,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Token {
    pub kind: TokenKind,
    /// The next token starts right where this one ends (no whitespace or comment between).
    pub joint: bool,
    pub sym: Symbol,
    /// A literal's suffix (`u8` in `1u8`), `kw::Empty` if none.
    pub suffix: Symbol,
    pub span: Span,
}

impl Token {
    pub const fn new(kind: TokenKind, span: Span) -> Token {
        Token {
            kind,
            joint: false,
            sym: kw::Empty,
            suffix: kw::Empty,
            span,
        }
    }

    pub const fn ident(sym: Symbol, span: Span) -> Token {
        Token {
            kind: TokenKind::Ident,
            joint: false,
            sym,
            suffix: kw::Empty,
            span,
        }
    }

    pub const fn dummy() -> Token {
        Token::new(TokenKind::Eof, Span::DUMMY)
    }

    #[inline]
    pub fn is_ident(&self) -> bool {
        matches!(self.kind, TokenKind::Ident | TokenKind::RawIdent)
    }

    /// A specific keyword (written plainly, not as a raw identifier).
    #[inline]
    pub fn is_keyword(&self, kw: Symbol) -> bool {
        self.kind == TokenKind::Ident && self.sym == kw
    }

    /// An identifier that isn't a reserved word (`r#fn` is fine, `fn` is not).
    pub fn is_non_reserved_ident(&self, edition2018: bool) -> bool {
        match self.kind {
            TokenKind::RawIdent => true,
            TokenKind::Ident => {
                !self.sym.is_reserved(edition2018)
                    && self.sym != kw::Underscore
                    && !self.sym.is_path_segment_keyword()
            }
            _ => false,
        }
    }

    pub fn is_lifetime(&self) -> bool {
        matches!(self.kind, TokenKind::Lifetime | TokenKind::RawLifetime)
    }

    pub fn is_lit(&self) -> bool {
        matches!(self.kind, TokenKind::Literal(_))
    }

    pub fn is_open(&self) -> bool {
        matches!(self.kind, TokenKind::Open(_))
    }

    pub fn is_close(&self) -> bool {
        matches!(self.kind, TokenKind::Close(_))
    }

    /// Splits a glued token into its first character and the rest: `>>=` into `>` and `>=`.
    pub fn split_first(&self) -> Option<(TokenKind, TokenKind)> {
        use TokenKind::*;
        Some(match self.kind {
            Le => (Lt, Eq),
            EqEq => (Eq, Eq),
            Ne => (Not, Eq),
            Ge => (Gt, Eq),
            AndAnd => (And, And),
            OrOr => (Or, Or),
            Shl => (Lt, Lt),
            Shr => (Gt, Gt),
            PlusEq => (Plus, Eq),
            MinusEq => (Minus, Eq),
            StarEq => (Star, Eq),
            SlashEq => (Slash, Eq),
            PercentEq => (Percent, Eq),
            CaretEq => (Caret, Eq),
            AndEq => (And, Eq),
            OrEq => (Or, Eq),
            ShlEq => (Lt, Le),
            ShrEq => (Gt, Ge),
            DotDot => (Dot, Dot),
            DotDotDot => (Dot, DotDot),
            PathSep => (Colon, Colon),
            RArrow => (Minus, Gt),
            LArrow => (Lt, Minus),
            FatArrow => (Eq, Gt),
            _ => return None,
        })
    }
}

impl fmt::Debug for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", token_text(self))
    }
}

impl TokenKind {
    /// The source text of a punctuation or delimiter token.
    pub fn punct_str(self) -> Option<&'static str> {
        use TokenKind::*;
        Some(match self {
            Eq => "=",
            Lt => "<",
            Le => "<=",
            EqEq => "==",
            Ne => "!=",
            Ge => ">=",
            Gt => ">",
            AndAnd => "&&",
            OrOr => "||",
            Not => "!",
            Tilde => "~",
            Plus => "+",
            Minus => "-",
            Star => "*",
            Slash => "/",
            Percent => "%",
            Caret => "^",
            And => "&",
            Or => "|",
            Shl => "<<",
            Shr => ">>",
            PlusEq => "+=",
            MinusEq => "-=",
            StarEq => "*=",
            SlashEq => "/=",
            PercentEq => "%=",
            CaretEq => "^=",
            AndEq => "&=",
            OrEq => "|=",
            ShlEq => "<<=",
            ShrEq => ">>=",
            At => "@",
            Dot => ".",
            DotDot => "..",
            DotDotDot => "...",
            DotDotEq => "..=",
            Comma => ",",
            Semi => ";",
            Colon => ":",
            PathSep => "::",
            RArrow => "->",
            LArrow => "<-",
            FatArrow => "=>",
            Pound => "#",
            Dollar => "$",
            Question => "?",
            SingleQuote => "'",
            Open(Delim::Paren) => "(",
            Open(Delim::Brace) => "{",
            Open(Delim::Bracket) => "[",
            Close(Delim::Paren) => ")",
            Close(Delim::Brace) => "}",
            Close(Delim::Bracket) => "]",
            Open(Delim::Invisible) | Close(Delim::Invisible) => "",
            _ => return None,
        })
    }

    pub fn is_punct(self) -> bool {
        !matches!(self, TokenKind::Open(_) | TokenKind::Close(_)) && self.punct_str().is_some()
    }
}

/// How a token is written, for diagnostics and `stringify!`.
pub fn token_text(t: &Token) -> String {
    use TokenKind::*;
    match t.kind {
        Ident | Lifetime => t.sym.as_str().to_string(),
        RawIdent => format!("r#{}", t.sym),
        RawLifetime => format!("'r#{}", &t.sym.as_str()[1..]),
        Literal(kind) => lit_text(kind, t.sym, t.suffix),
        DocComment(style, CommentKind::Line) => {
            format!(
                "//{}{}",
                if style == AttrStyle::Inner { "!" } else { "/" },
                t.sym
            )
        }
        DocComment(style, CommentKind::Block) => {
            format!(
                "/*{}{}*/",
                if style == AttrStyle::Inner { "!" } else { "*" },
                t.sym
            )
        }
        Eof => "<eof>".to_string(),
        k => k.punct_str().unwrap_or("?").to_string(),
    }
}

pub fn lit_text(kind: LitKind, sym: Symbol, suffix: Symbol) -> String {
    let s = sym.as_str();
    let hashes = |n: u8| "#".repeat(n as usize);
    let mut out = match kind {
        LitKind::Bool | LitKind::Integer | LitKind::Float | LitKind::Err => s.to_string(),
        LitKind::Byte => format!("b'{s}'"),
        LitKind::Char => format!("'{s}'"),
        LitKind::Str => format!("\"{s}\""),
        LitKind::StrRaw(n) => format!("r{0}\"{s}\"{0}", hashes(n)),
        LitKind::ByteStr => format!("b\"{s}\""),
        LitKind::ByteStrRaw(n) => format!("br{0}\"{s}\"{0}", hashes(n)),
        LitKind::CStr => format!("c\"{s}\""),
        LitKind::CStrRaw(n) => format!("cr{0}\"{s}\"{0}", hashes(n)),
    };
    if suffix != kw::Empty {
        out.push_str(suffix.as_str());
    }
    out
}
