//! The lexer: source text to a flat vector of tokens, delimiters included.
//!
//! One pass over the bytes with an ASCII fast path. Identifiers and literals are interned as
//! they are found; keywords are ordinary identifiers whose symbol happens to be a keyword's
//! (keywords are interned first, so checking for one is comparing two `u32`s).

use crate::token::{AttrStyle, CommentKind, Delim, LitKind, Token, TokenKind};
use hyprc_span::{Diag, DiagCtxt, Span, Symbol, kw};

pub struct Lexer<'a> {
    src: &'a str,
    bytes: &'a [u8],
    pos: usize,
    /// Position of `src[0]` in the source map.
    base: u32,
    dcx: &'a DiagCtxt,
    tokens: Vec<Token>,
    /// Open delimiters, to report mismatched ones.
    delims: Vec<(Delim, u32)>,
}

/// Tokenizes a whole file (or any text placed in the source map at `base`). The result ends
/// with an `Eof` token. Unbalanced delimiters are reported and repaired, so the parser can
/// rely on every `Open` having its `Close`.
pub fn tokenize(src: &str, base: u32, dcx: &DiagCtxt) -> Vec<Token> {
    let mut lexer = Lexer {
        src,
        bytes: src.as_bytes(),
        pos: 0,
        base,
        dcx,
        tokens: Vec::with_capacity(src.len() / 5 + 16),
        delims: Vec::new(),
    };
    lexer.skip_shebang();
    lexer.run();
    lexer.tokens
}

#[inline]
fn is_id_start(c: char) -> bool {
    c == '_' || c.is_ascii_alphabetic() || (c > '\x7f' && unicode_ident::is_xid_start(c))
}

#[inline]
fn is_id_continue(c: char) -> bool {
    c == '_' || c.is_ascii_alphanumeric() || (c > '\x7f' && unicode_ident::is_xid_continue(c))
}

/// Rust's whitespace: `Pattern_White_Space`.
#[inline]
fn is_whitespace(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\x0B'
            | '\x0C'
            | '\r'
            | ' '
            | '\u{85}'
            | '\u{200E}'
            | '\u{200F}'
            | '\u{2028}'
            | '\u{2029}'
    )
}

impl<'a> Lexer<'a> {
    #[inline]
    fn peek(&self) -> u8 {
        *self.bytes.get(self.pos).unwrap_or(&0)
    }

    #[inline]
    fn peek_at(&self, n: usize) -> u8 {
        *self.bytes.get(self.pos + n).unwrap_or(&0)
    }

    #[inline]
    fn char_at(&self, pos: usize) -> Option<char> {
        let b = *self.bytes.get(pos)?;
        if b < 0x80 {
            Some(b as char)
        } else {
            self.src[pos..].chars().next()
        }
    }

    #[inline]
    fn span(&self, lo: usize, hi: usize) -> Span {
        Span::new(self.base + lo as u32, self.base + hi as u32)
    }

    fn error(&self, lo: usize, hi: usize, msg: impl Into<String>) {
        self.dcx.emit(Diag::error(msg).span(self.span(lo, hi), ""));
    }

    fn skip_shebang(&mut self) {
        // `#!` on the first line is a shebang unless it starts an inner attribute `#![`.
        if !self.src.starts_with("#!") {
            return;
        }
        let rest = &self.src[2..];
        let after = rest.trim_start_matches(|c: char| is_whitespace(c));
        // Comments between `#!` and `[` still make it an attribute; rare enough to only check
        // the common case.
        if after.starts_with('[') {
            return;
        }
        self.pos = memchr::memchr(b'\n', self.bytes).unwrap_or(self.bytes.len());
    }

    fn push(&mut self, kind: TokenKind, lo: usize) {
        let span = self.span(lo, self.pos);
        self.tokens.push(Token::new(kind, span));
    }

    fn push_sym(&mut self, kind: TokenKind, lo: usize, sym: Symbol, suffix: Symbol) {
        let span = self.span(lo, self.pos);
        self.tokens.push(Token {
            kind,
            joint: false,
            sym,
            suffix,
            span,
        });
    }

    fn run(&mut self) {
        loop {
            // Whitespace and comments; a token right after another is "joint" with it.
            let start = self.pos;
            self.skip_trivia();
            if self.pos == start
                && let Some(last) = self.tokens.last_mut()
            {
                last.joint = true;
            }
            if self.pos >= self.bytes.len() {
                break;
            }
            self.next_token();
        }
        while let Some((delim, open)) = self.delims.pop() {
            let lo = open as usize;
            self.error(lo, lo + 1, "this file contains an unclosed delimiter");
            let pos = self.pos;
            self.push(TokenKind::Close(delim), pos);
        }
        if let Some(last) = self.tokens.last_mut() {
            last.joint = false;
        }
        let end = self.pos;
        self.push(TokenKind::Eof, end);
    }

    /// Skips whitespace and non-doc comments. Doc comments are tokens and stop it.
    fn skip_trivia(&mut self) {
        loop {
            let b = self.peek();
            match b {
                b' ' | b'\t' | b'\n' | b'\r' | 0x0B | 0x0C => self.pos += 1,
                b'/' if self.peek_at(1) == b'/' => {
                    // `///x` (but not `////`) and `//!` are doc comments.
                    let c2 = self.peek_at(2);
                    if (c2 == b'/' && self.peek_at(3) != b'/') || c2 == b'!' {
                        return;
                    }
                    self.pos = memchr::memchr(b'\n', &self.bytes[self.pos..])
                        .map_or(self.bytes.len(), |n| self.pos + n);
                }
                b'/' if self.peek_at(1) == b'*' => {
                    // `/**x` (but not `/***` or `/**/`) and `/*!` are doc comments.
                    let c2 = self.peek_at(2);
                    let c3 = self.peek_at(3);
                    if (c2 == b'*' && c3 != b'*' && c3 != b'/') || c2 == b'!' {
                        return;
                    }
                    self.skip_block_comment();
                }
                0x80.. => match self.char_at(self.pos) {
                    Some(c) if is_whitespace(c) => self.pos += c.len_utf8(),
                    _ => return,
                },
                _ => return,
            }
        }
    }

    /// Skips a (nested) block comment starting at `/*`. Returns the end of its text (before
    /// the final `*/`).
    fn skip_block_comment(&mut self) -> usize {
        let lo = self.pos;
        self.pos += 2;
        let mut depth = 1usize;
        loop {
            let Some(n) = memchr::memchr2(b'*', b'/', &self.bytes[self.pos..]) else {
                self.pos = self.bytes.len();
                self.error(lo, lo + 2, "unterminated block comment");
                return self.pos;
            };
            self.pos += n;
            if self.peek() == b'*' && self.peek_at(1) == b'/' {
                self.pos += 2;
                depth -= 1;
                if depth == 0 {
                    return self.pos - 2;
                }
            } else if self.peek() == b'/' && self.peek_at(1) == b'*' {
                self.pos += 2;
                depth += 1;
            } else {
                self.pos += 1;
            }
        }
    }

    fn next_token(&mut self) {
        let lo = self.pos;
        let b = self.peek();
        use TokenKind::*;
        match b {
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                // Literal prefixes first: b'', b"", br"", r"", r#"", c"", cr"", and r#ident.
                match (b, self.peek_at(1), self.peek_at(2)) {
                    (b'b', b'\'', _) => return self.quoted(lo, 2, b'\'', LitKind::Byte),
                    (b'b', b'"', _) => return self.quoted(lo, 2, b'"', LitKind::ByteStr),
                    (b'c', b'"', _) => return self.quoted(lo, 2, b'"', LitKind::CStr),
                    (b'b', b'r', b'"' | b'#') => {
                        if let Some(()) = self.raw_str(lo, 2, LitKind::ByteStrRaw) {
                            return;
                        }
                    }
                    (b'c', b'r', b'"' | b'#') => {
                        if let Some(()) = self.raw_str(lo, 2, LitKind::CStrRaw) {
                            return;
                        }
                    }
                    (b'r', b'"', _) => {
                        if let Some(()) = self.raw_str(lo, 1, LitKind::StrRaw) {
                            return;
                        }
                    }
                    (b'r', b'#', c) => {
                        if c == b'"' || c == b'#' {
                            if let Some(()) = self.raw_str(lo, 1, LitKind::StrRaw) {
                                return;
                            }
                        } else if self.char_at(lo + 2).is_some_and(is_id_start) {
                            self.pos = lo + 2;
                            let name_lo = self.pos;
                            self.eat_ident_chars();
                            let sym = Symbol::intern(&self.src[name_lo..self.pos]);
                            return self.push_sym(RawIdent, lo, sym, kw::Empty);
                        }
                    }
                    _ => {}
                }
                self.ident(lo);
            }
            b'0'..=b'9' => self.number(lo),
            b'\'' => self.quote(lo),
            b'"' => self.quoted(lo, 1, b'"', LitKind::Str),
            b'/' if matches!(self.peek_at(1), b'/' | b'*') => self.doc_comment(lo),
            b'(' => self.open(Delim::Paren, lo),
            b'[' => self.open(Delim::Bracket, lo),
            b'{' => self.open(Delim::Brace, lo),
            b')' => self.close(Delim::Paren, lo),
            b']' => self.close(Delim::Bracket, lo),
            b'}' => self.close(Delim::Brace, lo),
            0x80.. => {
                let c = self.char_at(lo).unwrap();
                if is_id_start(c) {
                    self.ident(lo);
                } else {
                    self.pos += c.len_utf8();
                    self.error(
                        lo,
                        self.pos,
                        format!("unknown start of token: {}", c.escape_unicode()),
                    );
                }
            }
            _ => self.punct(lo),
        }
    }

    fn eat_ident_chars(&mut self) {
        while let Some(c) = self.char_at(self.pos) {
            if !is_id_continue(c) {
                break;
            }
            self.pos += c.len_utf8();
        }
    }

    fn ident(&mut self, lo: usize) {
        // ASCII fast path.
        let mut i = lo;
        while let Some(&b) = self.bytes.get(i) {
            if b.is_ascii_alphanumeric() || b == b'_' {
                i += 1;
            } else {
                break;
            }
        }
        self.pos = i;
        if self.peek() >= 0x80 {
            self.eat_ident_chars();
        }
        let sym = Symbol::intern(&self.src[lo..self.pos]);
        self.push_sym(TokenKind::Ident, lo, sym, kw::Empty);
    }

    fn open(&mut self, delim: Delim, lo: usize) {
        self.pos += 1;
        self.delims.push((delim, lo as u32));
        self.push(TokenKind::Open(delim), lo);
    }

    fn close(&mut self, delim: Delim, lo: usize) {
        self.pos += 1;
        match self.delims.last() {
            Some(&(open, _)) if open == delim => {
                self.delims.pop();
            }
            Some(&(open, open_lo)) => {
                // Mismatched: if the delimiter is open further out, the inner ones were left
                // unclosed; close them. Otherwise this closer is stray; drop it.
                if self.delims.iter().any(|&(d, _)| d == delim) {
                    self.dcx.emit(
                        Diag::error("mismatched closing delimiter")
                            .span(self.span(lo, lo + 1), "mismatched closing delimiter")
                            .label(
                                self.span(open_lo as usize, open_lo as usize + 1),
                                "unclosed delimiter",
                            ),
                    );
                    while let Some((d, _)) = self.delims.pop() {
                        if d == delim {
                            break;
                        }
                        self.push(TokenKind::Close(d), lo);
                    }
                } else {
                    let _ = open;
                    self.error(lo, lo + 1, "unexpected closing delimiter");
                    return;
                }
            }
            None => {
                self.error(lo, lo + 1, "unexpected closing delimiter");
                return;
            }
        }
        self.push(TokenKind::Close(delim), lo);
    }

    fn punct(&mut self, lo: usize) {
        use TokenKind::*;
        let b0 = self.peek();
        let b1 = self.peek_at(1);
        let b2 = self.peek_at(2);
        let (kind, len) = match (b0, b1, b2) {
            (b'<', b'<', b'=') => (ShlEq, 3),
            (b'>', b'>', b'=') => (ShrEq, 3),
            (b'.', b'.', b'.') => (DotDotDot, 3),
            (b'.', b'.', b'=') => (DotDotEq, 3),
            (b'<', b'=', _) => (Le, 2),
            (b'=', b'=', _) => (EqEq, 2),
            (b'!', b'=', _) => (Ne, 2),
            (b'>', b'=', _) => (Ge, 2),
            (b'&', b'&', _) => (AndAnd, 2),
            (b'|', b'|', _) => (OrOr, 2),
            (b'+', b'=', _) => (PlusEq, 2),
            (b'-', b'=', _) => (MinusEq, 2),
            (b'*', b'=', _) => (StarEq, 2),
            (b'/', b'=', _) => (SlashEq, 2),
            (b'%', b'=', _) => (PercentEq, 2),
            (b'^', b'=', _) => (CaretEq, 2),
            (b'&', b'=', _) => (AndEq, 2),
            (b'|', b'=', _) => (OrEq, 2),
            (b'<', b'<', _) => (Shl, 2),
            (b'>', b'>', _) => (Shr, 2),
            (b'.', b'.', _) => (DotDot, 2),
            (b':', b':', _) => (PathSep, 2),
            (b'-', b'>', _) => (RArrow, 2),
            (b'<', b'-', _) => (LArrow, 2),
            (b'=', b'>', _) => (FatArrow, 2),
            (b'=', ..) => (Eq, 1),
            (b'<', ..) => (Lt, 1),
            (b'>', ..) => (Gt, 1),
            (b'!', ..) => (Not, 1),
            (b'~', ..) => (Tilde, 1),
            (b'+', ..) => (Plus, 1),
            (b'-', ..) => (Minus, 1),
            (b'*', ..) => (Star, 1),
            (b'/', ..) => (Slash, 1),
            (b'%', ..) => (Percent, 1),
            (b'^', ..) => (Caret, 1),
            (b'&', ..) => (And, 1),
            (b'|', ..) => (Or, 1),
            (b'@', ..) => (At, 1),
            (b'.', ..) => (Dot, 1),
            (b',', ..) => (Comma, 1),
            (b';', ..) => (Semi, 1),
            (b':', ..) => (Colon, 1),
            (b'#', ..) => (Pound, 1),
            (b'$', ..) => (Dollar, 1),
            (b'?', ..) => (Question, 1),
            _ => {
                self.pos += 1;
                let what = (b0 as char).escape_default().to_string();
                self.error(lo, lo + 1, format!("unknown start of token: {what}"));
                return;
            }
        };
        self.pos += len;
        self.push(kind, lo);
    }

    fn doc_comment(&mut self, lo: usize) {
        let style = if self.peek_at(2) == b'!' {
            AttrStyle::Inner
        } else {
            AttrStyle::Outer
        };
        if self.peek_at(1) == b'/' {
            let end = memchr::memchr(b'\n', &self.bytes[lo..]).map_or(self.bytes.len(), |n| lo + n);
            let text = self.src[lo + 3..end].trim_end_matches('\r');
            self.pos = end;
            let sym = Symbol::intern(text);
            self.push_sym(
                TokenKind::DocComment(style, CommentKind::Line),
                lo,
                sym,
                kw::Empty,
            );
        } else {
            let text_end = self.skip_block_comment();
            let text = &self.src[(lo + 3).min(text_end)..text_end];
            let sym = Symbol::intern(text);
            self.push_sym(
                TokenKind::DocComment(style, CommentKind::Block),
                lo,
                sym,
                kw::Empty,
            );
        }
    }

    /// A literal suffix (`u8`, `f32`, or any identifier).
    fn suffix(&mut self) -> Symbol {
        if self.char_at(self.pos).is_some_and(is_id_start) {
            let lo = self.pos;
            self.eat_ident_chars();
            Symbol::intern(&self.src[lo..self.pos])
        } else {
            kw::Empty
        }
    }

    fn number(&mut self, lo: usize) {
        let mut kind = LitKind::Integer;
        if self.peek() == b'0' && matches!(self.peek_at(1), b'x' | b'o' | b'b') {
            let hex = self.peek_at(1) == b'x';
            self.pos += 2;
            while let b = self.peek()
                && (b.is_ascii_digit() || b == b'_' || (hex && b.is_ascii_hexdigit()))
            {
                self.pos += 1;
            }
            if self.pos == lo + 2 {
                self.error(lo, self.pos, "no valid digits found for number");
            }
        } else {
            self.eat_decimal_digits();
            // `1.5`, `1.`; but not `1..2`, `1.foo()` or `1._x`.
            if self.peek() == b'.'
                && self.peek_at(1) != b'.'
                && !self.char_at(self.pos + 1).is_some_and(is_id_start)
            {
                self.pos += 1;
                kind = LitKind::Float;
                if self.peek().is_ascii_digit() {
                    self.eat_decimal_digits();
                    self.exponent();
                }
            } else if matches!(self.peek(), b'e' | b'E') && self.exponent_follows() {
                kind = LitKind::Float;
                self.exponent();
            }
        }
        let text_end = self.pos;
        let suffix = self.suffix();
        let sym = Symbol::intern(&self.src[lo..text_end]);
        self.push_sym(TokenKind::Literal(kind), lo, sym, suffix);
    }

    fn eat_decimal_digits(&mut self) {
        while let b = self.peek()
            && (b.is_ascii_digit() || b == b'_')
        {
            self.pos += 1;
        }
    }

    /// After the digits of a number: does `e`/`E` start an exponent (`1e5`, `1e-5`, `1E_5`)?
    fn exponent_follows(&self) -> bool {
        let mut i = 1;
        if matches!(self.peek_at(i), b'+' | b'-') {
            i += 1;
        }
        while self.peek_at(i) == b'_' {
            i += 1;
        }
        self.peek_at(i).is_ascii_digit()
    }

    fn exponent(&mut self) {
        if matches!(self.peek(), b'e' | b'E') && self.exponent_follows() {
            self.pos += 1;
            if matches!(self.peek(), b'+' | b'-') {
                self.pos += 1;
            }
            self.eat_decimal_digits();
        }
    }

    /// A `'`: a lifetime, a label, or a character literal.
    fn quote(&mut self, lo: usize) {
        let first = self.char_at(lo + 1);
        // `'r#name`: a raw lifetime.
        if self.peek_at(1) == b'r'
            && self.peek_at(2) == b'#'
            && self.char_at(lo + 3).is_some_and(is_id_start)
        {
            self.pos = lo + 3;
            self.eat_ident_chars();
            let sym = Symbol::intern(&format!("'{}", &self.src[lo + 3..self.pos]));
            return self.push_sym(TokenKind::RawLifetime, lo, sym, kw::Empty);
        }
        let can_be_lifetime = match first {
            Some(c) => {
                let after = lo + 1 + c.len_utf8();
                (is_id_start(c) || c.is_ascii_digit()) && self.bytes.get(after) != Some(&b'\'')
            }
            None => false,
        };
        if can_be_lifetime {
            self.pos = lo + 1;
            self.eat_ident_chars();
            if self.peek() == b'\'' {
                // `'ab'`: a character literal with more than one character.
                self.pos += 1;
                self.error(
                    lo,
                    self.pos,
                    "character literal may only contain one codepoint",
                );
                let sym = Symbol::intern(&self.src[lo + 1..self.pos - 1]);
                let suffix = self.suffix();
                return self.push_sym(TokenKind::Literal(LitKind::Err), lo, sym, suffix);
            }
            let sym = Symbol::intern(&self.src[lo..self.pos]);
            return self.push_sym(TokenKind::Lifetime, lo, sym, kw::Empty);
        }
        self.quoted(lo, 1, b'\'', LitKind::Char);
    }

    /// A quoted literal whose opening quote is at `lo + prefix - 1`. Escapes are skipped, not
    /// processed: the literal's symbol is its text between the quotes.
    fn quoted(&mut self, lo: usize, prefix: usize, quote: u8, kind: LitKind) {
        self.pos = lo + prefix;
        let content_lo = self.pos;
        loop {
            let Some(n) = memchr::memchr3(quote, b'\\', b'\n', &self.bytes[self.pos..]) else {
                self.pos = self.bytes.len();
                let what = if quote == b'"' { "string" } else { "character" };
                self.error(lo, lo + prefix, format!("unterminated {what} literal"));
                let sym = Symbol::intern(&self.src[content_lo..self.pos]);
                return self.push_sym(TokenKind::Literal(LitKind::Err), lo, sym, kw::Empty);
            };
            self.pos += n;
            match self.peek() {
                b'\\' => {
                    self.pos += 1;
                    // Skip the escaped character (it may be a quote or a multi-byte char).
                    if let Some(c) = self.char_at(self.pos) {
                        self.pos += c.len_utf8();
                    }
                }
                b'\n' if quote == b'\'' => {
                    self.error(lo, self.pos, "unterminated character literal");
                    let sym = Symbol::intern(&self.src[content_lo..self.pos]);
                    return self.push_sym(TokenKind::Literal(LitKind::Err), lo, sym, kw::Empty);
                }
                b'\n' => self.pos += 1,
                _ => break,
            }
        }
        let content_hi = self.pos;
        self.pos += 1;
        let suffix = self.suffix();
        let sym = Symbol::intern(&self.src[content_lo..content_hi]);
        self.push_sym(TokenKind::Literal(kind), lo, sym, suffix);
    }

    /// `r#"…"#` and friends; `prefix` is the length before the `#`s. Returns `None` (having
    /// consumed nothing) if this isn't a raw string after all (`r#ident`).
    fn raw_str(&mut self, lo: usize, prefix: usize, kind: fn(u8) -> LitKind) -> Option<()> {
        let mut i = lo + prefix;
        let mut hashes = 0usize;
        while self.bytes.get(i) == Some(&b'#') {
            hashes += 1;
            i += 1;
        }
        if self.bytes.get(i) != Some(&b'"') {
            if hashes == 0 {
                return None;
            }
            // `r#name` is a raw identifier, handled by the caller.
            if hashes == 1 && prefix == 1 {
                return None;
            }
            self.pos = i;
            self.error(
                lo,
                i,
                "found invalid character; only `#` is allowed in raw string delimitation",
            );
            return Some(());
        }
        if hashes > 255 {
            self.error(
                lo,
                i,
                "too many `#` symbols: raw strings may be delimited by up to 255",
            );
        }
        let content_lo = i + 1;
        let mut search = content_lo;
        loop {
            let Some(n) = memchr::memchr(b'"', &self.bytes[search..]) else {
                self.pos = self.bytes.len();
                self.error(lo, content_lo, "unterminated raw string");
                let sym = Symbol::intern(&self.src[content_lo..]);
                self.push_sym(TokenKind::Literal(LitKind::Err), lo, sym, kw::Empty);
                return Some(());
            };
            let quote = search + n;
            let closing = &self.bytes[quote + 1..];
            if closing.len() >= hashes && closing[..hashes].iter().all(|&b| b == b'#') {
                self.pos = quote + 1 + hashes;
                let suffix = self.suffix();
                let sym = Symbol::intern(&self.src[content_lo..quote]);
                self.push_sym(
                    TokenKind::Literal(kind(hashes.min(255) as u8)),
                    lo,
                    sym,
                    suffix,
                );
                return Some(());
            }
            search = quote + 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::token::token_text;

    fn lex(src: &str) -> Vec<String> {
        let dcx = DiagCtxt::buffered();
        let toks = tokenize(src, 1, &dcx);
        assert!(dcx.take().is_empty(), "errors lexing {src:?}");
        toks.iter()
            .filter(|t| t.kind != TokenKind::Eof)
            .map(token_text)
            .collect()
    }

    #[test]
    fn punctuation_is_glued() {
        assert_eq!(lex("a >>= b"), ["a", ">>=", "b"]);
        assert_eq!(lex("x..=y"), ["x", "..=", "y"]);
        assert_eq!(lex("a::<B>"), ["a", "::", "<", "B", ">"]);
        assert_eq!(lex("|| -> => <-"), ["||", "->", "=>", "<-"]);
    }

    #[test]
    fn numbers() {
        assert_eq!(
            lex("1 1.0 1. 1e5 1.5e-3f64 0xffu8 0b1010_1010 1_000i64"),
            [
                "1",
                "1.0",
                "1.",
                "1e5",
                "1.5e-3f64",
                "0xffu8",
                "0b1010_1010",
                "1_000i64"
            ]
        );
        assert_eq!(lex("1..2"), ["1", "..", "2"]);
        assert_eq!(lex("1.foo()"), ["1", ".", "foo", "(", ")"]);
        assert_eq!(lex("x.0.1"), ["x", ".", "0.1"]);
        assert_eq!(lex("1f32"), ["1f32"]);
    }

    #[test]
    fn strings_chars_lifetimes() {
        assert_eq!(
            lex(r#""a\"b" 'c' '\'' '\u{1F600}' b'x' b"y" c"z""#),
            [
                r#""a\"b""#,
                "'c'",
                r"'\''",
                r"'\u{1F600}'",
                "b'x'",
                "b\"y\"",
                "c\"z\""
            ]
        );
        assert_eq!(
            lex(r###"r"raw" r#"a "quoted" b"# br##"x"##"###),
            ["r\"raw\"", "r#\"a \"quoted\" b\"#", "br##\"x\"##"]
        );
        assert_eq!(lex("'a 'static 'r#fn '_"), ["'a", "'static", "'r#fn", "'_"]);
        assert_eq!(lex("r#match"), ["r#match"]);
        assert_eq!(lex("'é'"), ["'é'"]);
    }

    #[test]
    fn comments() {
        assert_eq!(lex("a // c\nb /* x /* nested */ y */ c"), ["a", "b", "c"]);
        assert_eq!(
            lex("/// doc\n//! inner\n//// not doc\nx"),
            ["/// doc", "//! inner", "x"]
        );
        assert_eq!(
            lex("/** d */ /*! i */ /**/ /***/ x"),
            ["/** d */", "/*! i */", "x"]
        );
    }

    #[test]
    fn shebang_and_joint() {
        let dcx = DiagCtxt::buffered();
        let toks = tokenize("#!/usr/bin/env igl\nfn", 1, &dcx);
        assert_eq!(toks.len(), 2);
        let toks = tokenize("a>>b > c", 1, &dcx);
        assert!(toks[0].joint && toks[1].joint && !toks[2].joint);
    }
}
