//! Format strings (`format_args!`), parsed as `std::fmt` documents them.

use crate::hir::{FormatSpec, FormatTrait};
use hyprc_span::Symbol;

#[derive(Debug, Clone, PartialEq)]
pub enum ArgRef {
    /// `{}`: the next positional argument.
    Next,
    Index(usize),
    Name(Symbol),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Count {
    Lit(usize),
    Arg(ArgRef),
}

#[derive(Debug, Clone, PartialEq)]
pub enum Piece {
    Lit(String),
    Arg {
        arg: ArgRef,
        trait_: FormatTrait,
        spec: FormatSpec,
        width: Option<Count>,
        precision: Option<Count>,
    },
    Error(String),
}

pub fn parse(s: &str, newline: bool) -> Vec<Piece> {
    let mut out = Vec::new();
    let mut lit = String::new();
    let chars: Vec<char> = s.chars().collect();
    let mut i = 0;
    while i < chars.len() {
        let c = chars[i];
        if c == '{' {
            if chars.get(i + 1) == Some(&'{') {
                lit.push('{');
                i += 2;
                continue;
            }
            if !lit.is_empty() {
                out.push(Piece::Lit(std::mem::take(&mut lit)));
            }
            let Some(end) = chars[i + 1..].iter().position(|&c| c == '}') else {
                out.push(Piece::Error(
                    "expected `}` but string was terminated".into(),
                ));
                return out;
            };
            let inner: String = chars[i + 1..i + 1 + end].iter().collect();
            out.push(parse_placeholder(&inner));
            i += end + 2;
            continue;
        }
        if c == '}' {
            if chars.get(i + 1) == Some(&'}') {
                lit.push('}');
                i += 2;
                continue;
            }
            out.push(Piece::Error("unmatched `}` found".into()));
            i += 1;
            continue;
        }
        lit.push(c);
        i += 1;
    }
    if newline {
        lit.push('\n');
    }
    if !lit.is_empty() {
        out.push(Piece::Lit(lit));
    }
    out
}

fn parse_arg(s: &str) -> ArgRef {
    let s = s.trim();
    if s.is_empty() {
        ArgRef::Next
    } else if let Ok(n) = s.parse::<usize>() {
        ArgRef::Index(n)
    } else {
        ArgRef::Name(Symbol::intern(s.trim_start_matches("r#")))
    }
}

fn parse_placeholder(inner: &str) -> Piece {
    let (arg, spec) = match inner.split_once(':') {
        Some((a, s)) => (a, s),
        None => (inner, ""),
    };
    let arg = parse_arg(arg);
    let mut fs = FormatSpec::default();
    let c: Vec<char> = spec.chars().collect();
    let mut i = 0;
    // [[fill]align]
    let is_align = |c: char| matches!(c, '<' | '^' | '>');
    let align_of = |c: char| match c {
        '<' => 1,
        '>' => 2,
        _ => 3,
    };
    if c.len() >= 2 && is_align(c[1]) {
        fs.fill = Some(c[0]);
        fs.align = align_of(c[1]);
        i = 2;
    } else if !c.is_empty() && is_align(c[0]) {
        fs.align = align_of(c[0]);
        i = 1;
    }
    // [sign]
    match c.get(i) {
        Some('+') => {
            fs.sign_plus = true;
            i += 1;
        }
        Some('-') => {
            fs.sign_minus = true;
            i += 1;
        }
        _ => {}
    }
    if c.get(i) == Some(&'#') {
        fs.alternate = true;
        i += 1;
    }
    // `0` padding (unless it's a width of `0$`).
    if c.get(i) == Some(&'0') && c.get(i + 1) != Some(&'$') {
        fs.zero_pad = true;
        i += 1;
    }
    // [width]
    // A count: digits (`18`, `1$`) or a name followed by `$` (`width$`).
    let read_count = |i: &mut usize| -> Option<Count> {
        let start = *i;
        if c.get(*i).is_some_and(|ch| ch.is_ascii_digit()) {
            while *i < c.len() && c[*i].is_ascii_digit() {
                *i += 1;
            }
        } else {
            while *i < c.len() && (c[*i].is_alphanumeric() || c[*i] == '_') {
                *i += 1;
            }
        }
        if *i == start {
            return None;
        }
        let word: String = c[start..*i].iter().collect();
        if c.get(*i) == Some(&'$') {
            *i += 1;
            return Some(Count::Arg(parse_arg(&word)));
        }
        match word.parse::<usize>() {
            Ok(n) => Some(Count::Lit(n)),
            Err(_) => {
                // Not a count: it's the type (`{:x}`). Undo.
                *i = start;
                None
            }
        }
    };
    let width = read_count(&mut i);
    let mut precision = None;
    if c.get(i) == Some(&'.') {
        i += 1;
        if c.get(i) == Some(&'*') {
            i += 1;
            precision = Some(Count::Arg(ArgRef::Next));
        } else {
            precision = read_count(&mut i);
        }
    }
    let ty: String = c[i..].iter().collect::<String>().trim().to_string();
    let trait_ = match ty.as_str() {
        "" => FormatTrait::Display,
        "?" => FormatTrait::Debug,
        "x?" => {
            fs.debug_hex = 1;
            FormatTrait::Debug
        }
        "X?" => {
            fs.debug_hex = 2;
            FormatTrait::Debug
        }
        "x" => FormatTrait::LowerHex,
        "X" => FormatTrait::UpperHex,
        "o" => FormatTrait::Octal,
        "b" => FormatTrait::Binary,
        "e" => FormatTrait::LowerExp,
        "E" => FormatTrait::UpperExp,
        "p" => FormatTrait::Pointer,
        other => return Piece::Error(format!("unknown format trait `{other}`")),
    };
    // `{:.*}` takes the precision before the value.
    let (precision, arg) = match (precision, arg) {
        (Some(Count::Arg(ArgRef::Next)), ArgRef::Next) => {
            (Some(Count::Arg(ArgRef::Next)), ArgRef::Next)
        }
        (p, a) => (p, a),
    };
    Piece::Arg {
        arg,
        trait_,
        spec: fs,
        width,
        precision,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn pieces() {
        let p = parse("a{}b{{}}{x:>5}{0:#x}{:.3$}", false);
        assert_eq!(p[0], Piece::Lit("a".into()));
        assert!(matches!(
            &p[1],
            Piece::Arg {
                arg: ArgRef::Next,
                trait_: FormatTrait::Display,
                ..
            }
        ));
        assert_eq!(p[2], Piece::Lit("b{}".into()));
        match &p[3] {
            Piece::Arg {
                arg: ArgRef::Name(n),
                spec,
                width,
                ..
            } => {
                assert_eq!(n.as_str(), "x");
                assert_eq!(spec.align, 2);
                assert_eq!(*width, Some(Count::Lit(5)));
            }
            other => panic!("{other:?}"),
        }
        assert!(
            matches!(&p[4], Piece::Arg { arg: ArgRef::Index(0), trait_: FormatTrait::LowerHex, spec, .. } if spec.alternate)
        );
        assert!(matches!(
            &p[5],
            Piece::Arg {
                precision: Some(Count::Arg(ArgRef::Index(3))),
                ..
            }
        ));
        assert_eq!(parse("x", true), vec![Piece::Lit("x\n".into())]);
    }
}
