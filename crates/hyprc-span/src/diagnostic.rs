//! Diagnostics, rendered the way rustc renders them, so they read the same to people and to
//! tools that already know rustc's output.

use crate::{Span, source_map};
use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};

const MAX_PRINTED_ERRORS: usize = 100;

#[derive(Clone, Copy, PartialEq, Eq, Debug, PartialOrd, Ord)]
pub enum Level {
    Error,
    Warning,
    Note,
    Help,
}

impl Level {
    fn as_str(self) -> &'static str {
        match self {
            Level::Error => "error",
            Level::Warning => "warning",
            Level::Note => "note",
            Level::Help => "help",
        }
    }

    fn color(self) -> &'static str {
        match self {
            Level::Error => "\x1b[1;31m",
            Level::Warning => "\x1b[1;33m",
            Level::Note => "\x1b[1;32m",
            Level::Help => "\x1b[1;36m",
        }
    }
}

#[derive(Clone, Debug)]
pub struct Label {
    pub span: Span,
    pub message: String,
    pub primary: bool,
}

#[derive(Clone, Debug)]
#[must_use = "a diagnostic does nothing until it is emitted"]
pub struct Diag {
    pub level: Level,
    pub code: Option<&'static str>,
    pub message: String,
    pub labels: Vec<Label>,
    /// Notes and helps shown under the snippet: `= note: …`.
    pub children: Vec<(Level, String)>,
}

impl Diag {
    pub fn new(level: Level, message: impl Into<String>) -> Diag {
        Diag {
            level,
            code: None,
            message: message.into(),
            labels: Vec::new(),
            children: Vec::new(),
        }
    }

    pub fn error(message: impl Into<String>) -> Diag {
        Diag::new(Level::Error, message)
    }

    pub fn warning(message: impl Into<String>) -> Diag {
        Diag::new(Level::Warning, message)
    }

    pub fn code(mut self, code: &'static str) -> Diag {
        self.code = Some(code);
        self
    }

    /// The span the diagnostic is about, with an optional label (`""` for none).
    pub fn span(mut self, span: Span, label: impl Into<String>) -> Diag {
        self.labels.push(Label {
            span,
            message: label.into(),
            primary: true,
        });
        self
    }

    pub fn label(mut self, span: Span, label: impl Into<String>) -> Diag {
        self.labels.push(Label {
            span,
            message: label.into(),
            primary: false,
        });
        self
    }

    pub fn note(mut self, note: impl Into<String>) -> Diag {
        self.children.push((Level::Note, note.into()));
        self
    }

    pub fn help(mut self, help: impl Into<String>) -> Diag {
        self.children.push((Level::Help, help.into()));
        self
    }

    pub fn primary_span(&self) -> Option<Span> {
        self.labels.iter().find(|l| l.primary).map(|l| l.span)
    }
}

/// Collects and prints diagnostics. Shared by all threads of a session.
pub struct DiagCtxt {
    errors: AtomicUsize,
    warnings: AtomicUsize,
    color: bool,
    /// Held while printing, so diagnostics from different threads don't interleave.
    out: Mutex<()>,
    /// When set, diagnostics are kept instead of printed (tests, speculative parsing).
    buffer: Option<Mutex<Vec<Diag>>>,
}

impl DiagCtxt {
    pub fn new(color: bool) -> DiagCtxt {
        DiagCtxt {
            errors: AtomicUsize::new(0),
            warnings: AtomicUsize::new(0),
            color,
            out: Mutex::new(()),
            buffer: None,
        }
    }

    /// A context that keeps its diagnostics for [`DiagCtxt::take`] instead of printing them.
    pub fn buffered() -> DiagCtxt {
        DiagCtxt {
            buffer: Some(Mutex::new(Vec::new())),
            ..DiagCtxt::new(false)
        }
    }

    pub fn emit(&self, diag: Diag) {
        match diag.level {
            Level::Error => {
                let error_index = self.errors.fetch_add(1, Ordering::Relaxed);
                if self.buffer.is_none() && error_index >= MAX_PRINTED_ERRORS {
                    if error_index == MAX_PRINTED_ERRORS {
                        let limit = Diag::error(format!(
                            "too many errors emitted; suppressing diagnostics after {MAX_PRINTED_ERRORS} errors"
                        ));
                        let text = render_human(&limit, self.color);
                        let _guard = self.out.lock().unwrap_or_else(|e| e.into_inner());
                        let _ = std::io::stderr().lock().write_all(text.as_bytes());
                    }
                    return;
                }
                // `HYPRC_PANIC_ON_ERROR=1`: where in hyprc an error comes from (with
                // `RUST_BACKTRACE=1`). Not for buffered (speculative) contexts.
                if self.buffer.is_none() && std::env::var_os("HYPRC_PANIC_ON_ERROR").is_some() {
                    panic!("error: {}", diag.message);
                }
            }
            Level::Warning => {
                self.warnings.fetch_add(1, Ordering::Relaxed);
            }
            _ => {}
        }
        if let Some(buffer) = &self.buffer {
            buffer.lock().unwrap_or_else(|e| e.into_inner()).push(diag);
            return;
        }
        let text = render_human(&diag, self.color);
        let _guard = self.out.lock().unwrap_or_else(|e| e.into_inner());
        let _ = std::io::stderr().lock().write_all(text.as_bytes());
    }

    pub fn error_count(&self) -> usize {
        self.errors.load(Ordering::Relaxed)
    }

    pub fn warning_count(&self) -> usize {
        self.warnings.load(Ordering::Relaxed)
    }

    pub fn has_errors(&self) -> bool {
        self.error_count() > 0
    }

    pub fn take(&self) -> Vec<Diag> {
        match &self.buffer {
            Some(b) => std::mem::take(&mut *b.lock().unwrap_or_else(|e| e.into_inner())),
            None => Vec::new(),
        }
    }
}

/// rustc's human-readable format:
///
/// ```text
/// error[E0425]: cannot find value `x` in this scope
///  --> src/main.rs:2:5
///   |
/// 2 |     x
///   |     ^ not found in this scope
/// ```
pub fn render_human(diag: &Diag, color: bool) -> String {
    let (bold, blue, reset) = if color {
        ("\x1b[1m", "\x1b[1;34m", "\x1b[0m")
    } else {
        ("", "", "")
    };
    let level_color = if color { diag.level.color() } else { "" };
    let mut out = String::new();
    let _ = write!(out, "{level_color}{}", diag.level.as_str());
    if let Some(code) = diag.code {
        let _ = write!(out, "[{code}]");
    }
    let _ = writeln!(out, "{reset}{bold}: {}{reset}", diag.message);

    // Group labels by file and line; spans that are dummies or outside every file are dropped.
    struct Resolved {
        file: std::sync::Arc<crate::SourceFile>,
        line: usize,
        col: usize,
        end_line: usize,
        end_col: usize,
        label: Label,
    }
    let sm = source_map();
    let mut resolved: Vec<Resolved> = diag
        .labels
        .iter()
        .filter(|l| !l.span.is_dummy())
        .filter_map(|l| {
            let file = sm.file_of(l.span.lo)?;
            let (line, col) = file.line_col(l.span.lo);
            let (end_line, end_col) = file.line_col(l.span.hi);
            Some(Resolved {
                file,
                line,
                col,
                end_line,
                end_col,
                label: l.clone(),
            })
        })
        .collect();
    // Primary label first: its location is the one in `-->`.
    resolved.sort_by_key(|r| !r.label.primary);
    let gutter = resolved
        .iter()
        .map(|r| r.end_line.max(r.line))
        .max()
        .map_or(1, |n| n.to_string().len());
    let pad = " ".repeat(gutter);

    let mut files: Vec<std::sync::Arc<crate::SourceFile>> = Vec::new();
    for r in &resolved {
        if !files.iter().any(|f| f.id == r.file.id) {
            files.push(r.file.clone());
        }
    }
    for (fi, file) in files.iter().enumerate() {
        let first = resolved.iter().find(|r| r.file.id == file.id).unwrap();
        let arrow = if fi == 0 { "-->" } else { ":::" };
        let _ = writeln!(
            out,
            "{pad}{blue}{arrow}{reset} {}:{}:{}",
            file.name, first.line, first.col
        );
        let _ = writeln!(out, "{pad} {blue}|{reset}");
        let mut lines: Vec<usize> = resolved
            .iter()
            .filter(|r| r.file.id == file.id)
            .flat_map(|r| {
                if r.end_line > r.line {
                    vec![r.line, r.end_line]
                } else {
                    vec![r.line]
                }
            })
            .collect();
        lines.sort_unstable();
        lines.dedup();
        let mut prev: Option<usize> = None;
        for &line in &lines {
            if let Some(p) = prev
                && line > p + 1
            {
                let _ = writeln!(out, "{blue}...{reset}");
            }
            prev = Some(line);
            let text = file.line_text(line).replace('\t', "    ");
            let _ = writeln!(out, "{blue}{line:>gutter$} |{reset} {text}");
            let raw = file.line_text(line);
            for r in resolved.iter().filter(|r| r.file.id == file.id) {
                let (start, end) = if r.line == line && r.end_line == line {
                    (r.col, r.end_col.max(r.col + 1))
                } else if r.line == line {
                    (r.col, raw.chars().count() + 1)
                } else if r.end_line == line {
                    (1, r.end_col.max(2))
                } else {
                    continue;
                };
                // Tabs were widened to four spaces above; widen the column the same way.
                let widen = |col: usize| {
                    raw.chars()
                        .take(col - 1)
                        .map(|c| if c == '\t' { 4 } else { 1 })
                        .sum::<usize>()
                };
                let (s, e) = (widen(start), widen(end).max(widen(start) + 1));
                let (mark, mcolor) = if r.label.primary {
                    ('^', level_color)
                } else {
                    ('-', blue)
                };
                let msg = if r.end_line == line || r.line == r.end_line {
                    &r.label.message[..]
                } else {
                    ""
                };
                let _ = writeln!(
                    out,
                    "{pad} {blue}|{reset} {}{mcolor}{}{}{reset}",
                    " ".repeat(s),
                    mark.to_string().repeat(e - s),
                    if msg.is_empty() {
                        String::new()
                    } else {
                        format!(" {msg}")
                    },
                );
            }
        }
    }
    // Labels without a place to show them still say something: as notes.
    let lost: Vec<&str> = diag
        .labels
        .iter()
        .filter(|l| !l.message.is_empty() && !resolved.iter().any(|r| r.label.span == l.span))
        .map(|l| &l.message[..])
        .collect();
    if !diag.children.is_empty() || !lost.is_empty() {
        if !resolved.is_empty() {
            let _ = writeln!(out, "{pad} {blue}|{reset}");
        }
        for msg in lost {
            let _ = writeln!(out, "{pad} {blue}={reset} {bold}note{reset}: {msg}");
        }
        for (level, msg) in &diag.children {
            let _ = writeln!(
                out,
                "{pad} {blue}={reset} {bold}{}{reset}: {msg}",
                level.as_str()
            );
        }
    }
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn renders_like_rustc() {
        let file = source_map().add_file("main.rs".into(), None, "fn main() {\n    x\n}\n".into());
        let lo = file.start + 16;
        let d = Diag::error("cannot find value `x` in this scope")
            .code("E0425")
            .span(Span::new(lo, lo + 1), "not found in this scope");
        let text = render_human(&d, false);
        assert_eq!(
            text,
            "error[E0425]: cannot find value `x` in this scope\n \
             --> main.rs:2:5\n  |\n2 |     x\n  |     ^ not found in this scope\n\n"
        );
    }
}
