//! Macros the compiler implements itself. The standard library declares them with
//! `#[rustc_builtin_macro]`; their bodies are empty and the name selects the implementation.
//!
//! Most produce tokens. The ones whose result isn't expressible as plain Rust
//! (`format_args!`, `asm!`) produce `builtin # name(…)` syntax that the parser turns into
//! dedicated expression nodes, lowered later.

use hyprc_span::{Diag, Span, Symbol, kw, source_map};
use hyprc_syntax::token::{Delim, LitKind, Token, TokenKind};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BuiltinMacro {
    Stringify,
    Concat,
    ConcatBytes,
    ConcatIdents,
    Line,
    Column,
    File,
    ModulePath,
    Cfg,
    CompileError,
    Include,
    IncludeStr,
    IncludeBytes,
    Env,
    OptionEnv,
    FormatArgs,
    FormatArgsNl,
    ConstFormatArgs,
    Assert,
    CorePanic,
    StdPanic,
    UnreachablePanic,
    /// `pattern_type!(u32 is 1..)`: the type syntax itself.
    PatternType,
    Asm,
    GlobalAsm,
    NakedAsm,
    CfgSelect,
    TraceMacros,
    LogSyntax,
    Format,
    Print,
    Println,
    Eprint,
    Eprintln,
    Vec,
    Matches,
    Todo,
    Unimplemented,
    Write,
    Writeln,
    // Attributes and derives.
    Derive,
    Test,
    Bench,
    TestCase,
    GlobalAllocator,
    CfgAccessible,
    CfgEval,
    AllocErrorHandler,
    DeriveClone,
    DeriveCopy,
    DeriveDebug,
    DeriveDefault,
    DeriveEq,
    DeriveHash,
    DeriveOrd,
    DerivePartialEq,
    DerivePartialOrd,
    DeriveConstParamTy,
    DeriveCoercePointee,
    DeriveFrom,
    /// Built-ins hyprc doesn't implement yet: calling one is an error that says so.
    Unsupported(Symbol),
}

impl BuiltinMacro {
    pub fn from_name(name: &str) -> BuiltinMacro {
        use BuiltinMacro::*;
        match name {
            "stringify" => Stringify,
            "concat" => Concat,
            "concat_bytes" => ConcatBytes,
            "concat_idents" => ConcatIdents,
            "line" => Line,
            "column" => Column,
            "file" => File,
            "module_path" => ModulePath,
            "cfg" => Cfg,
            "compile_error" => CompileError,
            "include" => Include,
            "include_str" => IncludeStr,
            "include_bytes" => IncludeBytes,
            "env" => Env,
            "option_env" => OptionEnv,
            "format_args" => FormatArgs,
            "format_args_nl" => FormatArgsNl,
            "const_format_args" => ConstFormatArgs,
            "assert" | "debug_assert" | "debug_assert_eq" | "debug_assert_ne" => Assert,
            "panic" | "core_panic" | "panic_2015" | "panic_2021" => CorePanic,
            "std_panic" => StdPanic,
            "unreachable" | "unreachable_2015" | "unreachable_2021" => UnreachablePanic,
            "pattern_type" => PatternType,
            "asm" => Asm,
            "global_asm" => GlobalAsm,
            "naked_asm" => NakedAsm,
            "cfg_select" => CfgSelect,
            "trace_macros" => TraceMacros,
            "log_syntax" => LogSyntax,
            "format" => Format,
            "print" => Print,
            "println" => Println,
            "eprint" => Eprint,
            "eprintln" => Eprintln,
            "write" => Write,
            "writeln" => Writeln,
            "vec" => Vec,
            "matches" => Matches,
            "todo" => Todo,
            "unimplemented" => Unimplemented,
            "derive" => Derive,
            "test" => Test,
            "bench" => Bench,
            "test_case" => TestCase,
            "global_allocator" => GlobalAllocator,
            "cfg_accessible" => CfgAccessible,
            "cfg_eval" => CfgEval,
            "alloc_error_handler" => AllocErrorHandler,
            "Clone" => DeriveClone,
            "Copy" => DeriveCopy,
            "Debug" => DeriveDebug,
            "Default" => DeriveDefault,
            "Eq" => DeriveEq,
            "Hash" => DeriveHash,
            "Ord" => DeriveOrd,
            "PartialEq" => DerivePartialEq,
            "PartialOrd" => DerivePartialOrd,
            "ConstParamTy" => DeriveConstParamTy,
            "CoercePointee" => DeriveCoercePointee,
            "From" => DeriveFrom,
            other => Unsupported(Symbol::intern(other)),
        }
    }
}

pub(crate) fn lit(kind: LitKind, text: &str, span: Span) -> Token {
    Token {
        kind: TokenKind::Literal(kind),
        joint: false,
        sym: Symbol::intern(text),
        suffix: kw::Empty,
        span,
    }
}

pub(crate) fn str_lit(s: &str, span: Span) -> Token {
    lit(LitKind::Str, &escape_str(s), span)
}

pub(crate) fn escape_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c => out.push(c),
        }
    }
    out
}

/// The text of tokens as `stringify!` prints it: tokens separated by spaces except where
/// they were written joined.
pub fn tokens_to_string(tokens: &[Token]) -> String {
    let mut out = String::new();
    for (i, t) in tokens.iter().enumerate() {
        if matches!(
            t.kind,
            TokenKind::Open(Delim::Invisible) | TokenKind::Close(Delim::Invisible)
        ) {
            continue;
        }
        let text = hyprc_syntax::token::token_text(t);
        if i > 0 && !out.is_empty() {
            let prev = &tokens[i - 1];
            let no_space = prev.joint
                || matches!(prev.kind, TokenKind::Open(Delim::Paren | Delim::Bracket))
                || matches!(
                    t.kind,
                    TokenKind::Close(Delim::Paren | Delim::Bracket)
                        | TokenKind::Comma
                        | TokenKind::Semi
                        | TokenKind::Dot
                )
                || prev.kind == TokenKind::Dot
                || (t.kind == TokenKind::Open(Delim::Paren)
                    && prev.is_ident()
                    && !prev.sym.is_reserved(true));
            if !no_space {
                out.push(' ');
            }
        }
        out.push_str(&text);
    }
    out
}

/// Decodes a string literal's text (escapes processed). `None` if it has invalid escapes.
pub fn unescape_str(text: &str, raw: bool) -> Option<String> {
    if raw {
        return Some(text.to_string());
    }
    let mut out = String::with_capacity(text.len());
    let mut chars = text.chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next()? {
            'n' => out.push('\n'),
            'r' => out.push('\r'),
            't' => out.push('\t'),
            '\\' => out.push('\\'),
            '0' => out.push('\0'),
            '\'' => out.push('\''),
            '"' => out.push('"'),
            'x' => {
                let hex: String = [chars.next()?, chars.next()?].iter().collect();
                out.push(u8::from_str_radix(&hex, 16).ok()? as char);
            }
            'u' => {
                if chars.next()? != '{' {
                    return None;
                }
                let mut hex = String::new();
                for c in chars.by_ref() {
                    if c == '}' {
                        break;
                    }
                    if c != '_' {
                        hex.push(c);
                    }
                }
                out.push(char::from_u32(u32::from_str_radix(&hex, 16).ok()?)?);
            }
            '\n' => {
                // Line continuation: skip the newline and leading whitespace.
                while chars.peek().is_some_and(|c| c.is_whitespace()) {
                    chars.next();
                }
            }
            '\r' if chars.peek() == Some(&'\n') => {
                chars.next();
                while chars.peek().is_some_and(|c| c.is_whitespace()) {
                    chars.next();
                }
            }
            _ => return None,
        }
    }
    Some(out)
}

/// What `concat!` and friends get as the text of a literal token.
pub fn literal_value(t: &Token) -> Option<String> {
    match t.kind {
        TokenKind::Literal(LitKind::Str) => unescape_str(t.sym.as_str(), false),
        TokenKind::Literal(LitKind::StrRaw(_)) => Some(t.sym.as_str().to_string()),
        TokenKind::Literal(LitKind::Char) => unescape_str(t.sym.as_str(), false),
        TokenKind::Literal(LitKind::Integer | LitKind::Float) => {
            let s = t.sym.as_str().replace('_', "");
            Some(s)
        }
        TokenKind::Ident if t.sym == kw::True || t.sym == kw::False => {
            Some(t.sym.as_str().to_string())
        }
        _ => None,
    }
}

/// `file!()`, `line!()`, `column!()`: where the outermost macro call is, in source.
pub fn call_site_loc(span: Span) -> (String, usize, usize) {
    match source_map().lookup(span.lo) {
        Some(loc) => (loc.file.name.clone(), loc.line, loc.col),
        None => ("<unknown>".to_string(), 0, 0),
    }
}

pub fn err(span: Span, msg: impl Into<String>) -> Diag {
    Diag::error(msg).span(span, "")
}
