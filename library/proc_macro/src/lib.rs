//! Hyprc proc_macro implementation.
#![no_std]
#![allow(unused_imports, dead_code, non_camel_case_types)]

extern crate alloc;
extern crate std;

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::fmt;
use core::str::FromStr;

#[derive(Clone, Default)]
pub struct TokenStream {
    inner: Vec<TokenTree>,
}

impl TokenStream {
    pub const fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn from_str_checked(src: &str) -> Result<TokenStream, LexError> {
        let _ = src;
        Ok(TokenStream::new())
    }

    pub fn from_str_unchecked(src: &str) -> TokenStream {
        let _ = src;
        TokenStream::new()
    }
}

impl FromStr for TokenStream {
    type Err = LexError;
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        TokenStream::from_str_checked(src)
    }
}

impl fmt::Display for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, tree) in self.inner.iter().enumerate() {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}", tree)?;
        }
        Ok(())
    }
}

impl fmt::Debug for TokenStream {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TokenStream({:?})", self.inner)
    }
}

impl From<TokenTree> for TokenStream {
    fn from(tree: TokenTree) -> Self {
        let mut v = Vec::new();
        v.push(tree);
        Self { inner: v }
    }
}

impl FromIterator<TokenTree> for TokenStream {
    fn from_iter<I: IntoIterator<Item = TokenTree>>(trees: I) -> Self {
        let mut v = Vec::new();
        for tree in trees {
            v.push(tree);
        }
        Self { inner: v }
    }
}

impl FromIterator<TokenStream> for TokenStream {
    fn from_iter<I: IntoIterator<Item = TokenStream>>(streams: I) -> Self {
        let mut v = Vec::new();
        for s in streams {
            v.extend(s.inner);
        }
        Self { inner: v }
    }
}

impl Extend<TokenTree> for TokenStream {
    fn extend<I: IntoIterator<Item = TokenTree>>(&mut self, trees: I) {
        self.inner.extend(trees);
    }
}

impl Extend<TokenStream> for TokenStream {
    fn extend<I: IntoIterator<Item = TokenStream>>(&mut self, streams: I) {
        for s in streams {
            self.inner.extend(s.inner);
        }
    }
}

impl IntoIterator for TokenStream {
    type Item = TokenTree;
    type IntoIter = token_stream::IntoIter;
    fn into_iter(self) -> Self::IntoIter {
        token_stream::IntoIter { inner: self.inner.into_iter() }
    }
}

pub mod token_stream {
    use super::*;

    #[derive(Clone, Debug)]
    pub struct IntoIter {
        pub(crate) inner: alloc::vec::IntoIter<TokenTree>,
    }

    impl Iterator for IntoIter {
        type Item = TokenTree;
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next()
        }
        fn size_hint(&self) -> (usize, Option<usize>) {
            self.inner.size_hint()
        }
    }
}

#[derive(Clone, Debug)]
pub enum TokenTree {
    Group(Group),
    Ident(Ident),
    Punct(Punct),
    Literal(Literal),
}

impl TokenTree {
    pub fn span(&self) -> Span {
        match self {
            TokenTree::Group(g) => g.span(),
            TokenTree::Ident(i) => i.span(),
            TokenTree::Punct(p) => p.span(),
            TokenTree::Literal(l) => l.span(),
        }
    }

    pub fn set_span(&mut self, span: Span) {
        match self {
            TokenTree::Group(g) => g.set_span(span),
            TokenTree::Ident(i) => i.set_span(span),
            TokenTree::Punct(p) => p.set_span(span),
            TokenTree::Literal(l) => l.set_span(span),
        }
    }
}

impl fmt::Display for TokenTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenTree::Group(g) => write!(f, "{}", g),
            TokenTree::Ident(i) => write!(f, "{}", i),
            TokenTree::Punct(p) => write!(f, "{}", p),
            TokenTree::Literal(l) => write!(f, "{}", l),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Group {
    delimiter: Delimiter,
    stream: TokenStream,
    span: Span,
}

impl Group {
    pub fn new(delimiter: Delimiter, stream: TokenStream) -> Self {
        Self { delimiter, stream, span: Span::call_site() }
    }

    pub fn delimiter(&self) -> Delimiter {
        self.delimiter
    }

    pub fn stream(&self) -> TokenStream {
        self.stream.clone()
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }

    pub fn span_open(&self) -> Span {
        self.span
    }

    pub fn span_close(&self) -> Span {
        self.span
    }
}

impl fmt::Display for Group {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (open, close) = match self.delimiter {
            Delimiter::Parenthesis => ("(", ")"),
            Delimiter::Brace => ("{", "}"),
            Delimiter::Bracket => ("[", "]"),
            Delimiter::None => ("", ""),
        };
        write!(f, "{}{}{}", open, self.stream, close)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
    None,
}

#[derive(Clone, Debug)]
pub struct Ident {
    sym: String,
    span: Span,
    is_raw: bool,
}

impl Ident {
    pub fn new(string: &str, span: Span) -> Self {
        Self { sym: String::from(string), span, is_raw: false }
    }

    pub fn new_raw(string: &str, span: Span) -> Self {
        Self { sym: String::from(string), span, is_raw: true }
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_raw {
            write!(f, "r#{}", self.sym)
        } else {
            write!(f, "{}", self.sym)
        }
    }
}

#[derive(Clone, Debug)]
pub struct Punct {
    ch: char,
    spacing: Spacing,
    span: Span,
}

impl Punct {
    pub fn new(ch: char, spacing: Spacing) -> Self {
        Self { ch, spacing, span: Span::call_site() }
    }

    pub fn as_char(&self) -> char {
        self.ch
    }

    pub fn spacing(&self) -> Spacing {
        self.spacing
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl fmt::Display for Punct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.ch)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Spacing {
    Alone,
    Joint,
}

#[derive(Clone, Debug)]
pub struct Literal {
    text: String,
    span: Span,
}

impl Literal {
    pub fn from_str(src: &str) -> Result<Literal, LexError> {
        Ok(Self { text: String::from(src), span: Span::call_site() })
    }

    pub fn from_str_checked(src: &str) -> Result<Literal, LexError> {
        Ok(Self { text: String::from(src), span: Span::call_site() })
    }

    pub fn from_str_unchecked(src: &str) -> Literal {
        Self { text: String::from(src), span: Span::call_site() }
    }

    pub fn subspan<R: core::ops::RangeBounds<usize>>(&self, range: R) -> Option<Span> {
        let _ = range;
        Some(self.span)
    }

    pub fn string(string: &str) -> Self {
        let mut s = String::from("\"");
        s.push_str(string);
        s.push('"');
        Self { text: s, span: Span::call_site() }
    }

    pub fn c_string(string: &core::ffi::CStr) -> Self {
        let mut s = String::from("c\"");
        if let Ok(st) = string.to_str() {
            s.push_str(st);
        }
        s.push('"');
        Self { text: s, span: Span::call_site() }
    }

    pub fn byte_string(bytes: &[u8]) -> Self {
        let _ = bytes;
        Self { text: String::from("b\"\""), span: Span::call_site() }
    }

    pub fn character(ch: char) -> Self {
        let mut s = String::from("'");
        s.push(ch);
        s.push('\'');
        Self { text: s, span: Span::call_site() }
    }

    pub fn byte_character(byte: u8) -> Self {
        let _ = byte;
        Self { text: String::from("b'0'"), span: Span::call_site() }
    }

    pub fn u8_suffixed(n: u8) -> Self { Self { text: alloc::format!("{n}u8"), span: Span::call_site() } }
    pub fn u16_suffixed(n: u16) -> Self { Self { text: alloc::format!("{n}u16"), span: Span::call_site() } }
    pub fn u32_suffixed(n: u32) -> Self { Self { text: alloc::format!("{n}u32"), span: Span::call_site() } }
    pub fn u64_suffixed(n: u64) -> Self { Self { text: alloc::format!("{n}u64"), span: Span::call_site() } }
    pub fn u128_suffixed(n: u128) -> Self { Self { text: alloc::format!("{n}u128"), span: Span::call_site() } }
    pub fn usize_suffixed(n: usize) -> Self { Self { text: alloc::format!("{n}usize"), span: Span::call_site() } }

    pub fn u8_unsuffixed(n: u8) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn u16_unsuffixed(n: u16) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn u32_unsuffixed(n: u32) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn u64_unsuffixed(n: u64) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn u128_unsuffixed(n: u128) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn usize_unsuffixed(n: usize) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }

    pub fn i8_suffixed(n: i8) -> Self { Self { text: alloc::format!("{n}i8"), span: Span::call_site() } }
    pub fn i16_suffixed(n: i16) -> Self { Self { text: alloc::format!("{n}i16"), span: Span::call_site() } }
    pub fn i32_suffixed(n: i32) -> Self { Self { text: alloc::format!("{n}i32"), span: Span::call_site() } }
    pub fn i64_suffixed(n: i64) -> Self { Self { text: alloc::format!("{n}i64"), span: Span::call_site() } }
    pub fn i128_suffixed(n: i128) -> Self { Self { text: alloc::format!("{n}i128"), span: Span::call_site() } }
    pub fn isize_suffixed(n: isize) -> Self { Self { text: alloc::format!("{n}isize"), span: Span::call_site() } }

    pub fn i8_unsuffixed(n: i8) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn i16_unsuffixed(n: i16) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn i32_unsuffixed(n: i32) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn i64_unsuffixed(n: i64) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn i128_unsuffixed(n: i128) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn isize_unsuffixed(n: isize) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }

    pub fn f32_suffixed(n: f32) -> Self { Self { text: alloc::format!("{n}f32"), span: Span::call_site() } }
    pub fn f32_unsuffixed(n: f32) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }
    pub fn f64_suffixed(n: f64) -> Self { Self { text: alloc::format!("{n}f64"), span: Span::call_site() } }
    pub fn f64_unsuffixed(n: f64) -> Self { Self { text: alloc::format!("{n}"), span: Span::call_site() } }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn set_span(&mut self, span: Span) {
        self.span = span;
    }
}

impl FromStr for Literal {
    type Err = LexError;
    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str_checked(src)
    }
}

impl fmt::Display for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.text)
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Span;

impl Span {
    pub fn call_site() -> Self { Span }
    pub fn mixed_site() -> Self { Span }
    pub fn def_site() -> Self { Span }
    pub fn parent(&self) -> Option<Span> { None }
    pub fn source(&self) -> Span { *self }
    pub fn byte_range(&self) -> core::ops::Range<usize> { 0..0 }
    pub fn start(&self) -> LineColumn { LineColumn { line: 0, column: 0 } }
    pub fn end(&self) -> LineColumn { LineColumn { line: 0, column: 0 } }
    pub fn line(&self) -> usize { 0 }
    pub fn column(&self) -> usize { 0 }
    pub fn join(&self, other: Span) -> Option<Span> { let _ = other; Some(*self) }
    pub fn resolved_at(&self, other: Span) -> Span { let _ = other; *self }
    pub fn located_at(&self, other: Span) -> Span { let _ = other; *self }
    pub fn source_text(&self) -> Option<String> { None }
    pub fn source_file(&self) -> SourceFile { SourceFile }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LineColumn {
    pub line: usize,
    pub column: usize,
}

#[derive(Clone, Debug)]
pub struct SourceFile;

impl SourceFile {
    pub fn is_real(&self) -> bool { false }
    pub fn path(&self) -> std::path::PathBuf { std::path::PathBuf::new() }
}

#[derive(Clone, Debug)]
pub struct LexError;

impl LexError {
    pub fn span(&self) -> Span { Span }
}

impl fmt::Display for LexError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "lex error")
    }
}

pub fn is_available() -> bool {
    false
}
