//! Source files and spans.
//!
//! Every file loaded into a session is placed in one global byte-address space: a file of `n`
//! bytes takes the positions `start..=start + n` (one extra so the end of file has a position
//! of its own). A [`Span`] is then just two `u32` positions plus a syntax context, and finding
//! its file is a binary search over the files' start positions.

use std::fmt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock, RwLock};

/// Macro hygiene: which expansion a token came from. `ROOT` for tokens written in source.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Default, PartialOrd, Ord)]
pub struct SyntaxContext(pub u32);

impl SyntaxContext {
    pub const ROOT: SyntaxContext = SyntaxContext(0);
}

impl fmt::Debug for SyntaxContext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct Span {
    pub lo: u32,
    pub hi: u32,
    pub ctxt: SyntaxContext,
}

impl Span {
    /// Points nowhere: for things the compiler made up.
    pub const DUMMY: Span = Span {
        lo: 0,
        hi: 0,
        ctxt: SyntaxContext::ROOT,
    };

    #[inline]
    pub const fn new(lo: u32, hi: u32) -> Span {
        Span {
            lo,
            hi,
            ctxt: SyntaxContext::ROOT,
        }
    }

    #[inline]
    pub fn to(self, end: Span) -> Span {
        Span {
            lo: self.lo.min(end.lo),
            hi: self.hi.max(end.hi),
            ctxt: self.ctxt,
        }
    }

    #[inline]
    pub fn shrink_to_lo(self) -> Span {
        Span {
            hi: self.lo,
            ..self
        }
    }

    #[inline]
    pub fn shrink_to_hi(self) -> Span {
        Span {
            lo: self.hi,
            ..self
        }
    }

    #[inline]
    pub fn with_ctxt(self, ctxt: SyntaxContext) -> Span {
        Span { ctxt, ..self }
    }

    pub fn is_dummy(self) -> bool {
        self.lo == 0 && self.hi == 0
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_dummy() {
            return f.write_str("<dummy>");
        }
        match source_map().lookup(self.lo) {
            Some(loc) => write!(f, "{}:{}:{}", loc.file.name, loc.line, loc.col),
            None => write!(f, "{}..{}", self.lo, self.hi),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct FileId(pub u32);

pub struct SourceFile {
    pub id: FileId,
    /// The name diagnostics show: the path as given on the command line or found by `mod`.
    pub name: String,
    pub path: Option<PathBuf>,
    /// The file's text, kept for the whole session (spans point into it).
    pub src: &'static str,
    /// Position of the file's first byte.
    pub start: u32,
    lines: OnceLock<Vec<u32>>,
}

impl SourceFile {
    pub fn end(&self) -> u32 {
        self.start + self.src.len() as u32
    }

    /// Offsets of the first byte of each line, computed on first use (only diagnostics and
    /// debug info need them).
    pub fn lines(&self) -> &[u32] {
        self.lines.get_or_init(|| {
            let mut lines = Vec::with_capacity(self.src.len() / 32 + 1);
            lines.push(0);
            for (i, b) in self.src.bytes().enumerate() {
                if b == b'\n' {
                    lines.push(i as u32 + 1);
                }
            }
            lines
        })
    }

    /// The 1-based line and the 1-based column (in chars) of a position in this file.
    pub fn line_col(&self, pos: u32) -> (usize, usize) {
        let off = pos.saturating_sub(self.start).min(self.src.len() as u32);
        let lines = self.lines();
        let line = lines.partition_point(|&l| l <= off) - 1;
        let line_start = lines[line] as usize;
        let col = self.src[line_start..off as usize].chars().count();
        (line + 1, col + 1)
    }

    /// The text of a 1-based line, without its line break.
    pub fn line_text(&self, line: usize) -> &'static str {
        let lines = self.lines();
        let Some(&start) = lines.get(line.wrapping_sub(1)) else {
            return "";
        };
        let end = lines.get(line).map_or(self.src.len(), |&e| e as usize);
        self.src[start as usize..end].trim_end_matches(['\n', '\r'])
    }

    pub fn slice(&self, span: Span) -> &'static str {
        let lo = (span.lo.saturating_sub(self.start) as usize).min(self.src.len());
        let hi = (span.hi.saturating_sub(self.start) as usize).clamp(lo, self.src.len());
        &self.src[lo..hi]
    }
}

/// Where a position is, for humans.
pub struct Loc {
    pub file: Arc<SourceFile>,
    pub line: usize,
    pub col: usize,
}

#[derive(Default)]
pub struct SourceMap {
    files: RwLock<Vec<Arc<SourceFile>>>,
}

pub fn source_map() -> &'static SourceMap {
    static MAP: OnceLock<SourceMap> = OnceLock::new();
    MAP.get_or_init(SourceMap::default)
}

impl SourceMap {
    /// Adds a file. Position 0 is never a file's (it is [`Span::DUMMY`]'s), so the first file
    /// starts at 1.
    pub fn add_file(&self, name: String, path: Option<PathBuf>, src: String) -> Arc<SourceFile> {
        let src: &'static str = Box::leak(src.into_boxed_str());
        let mut files = self.files.write().unwrap_or_else(|e| e.into_inner());
        let start = files.last().map_or(1, |f| f.end() + 1);
        assert!(
            (start as u64) + (src.len() as u64) < u32::MAX as u64,
            "more than 4 GiB of source in one session"
        );
        let file = Arc::new(SourceFile {
            id: FileId(files.len() as u32),
            name,
            path,
            src,
            start,
            lines: OnceLock::new(),
        });
        files.push(file.clone());
        file
    }

    pub fn load_file(&self, path: &Path) -> std::io::Result<Arc<SourceFile>> {
        let mut src = std::fs::read_to_string(path)?;
        // A byte order mark is not part of the source.
        if src.starts_with('\u{feff}') {
            src.drain(..3);
        }
        Ok(self.add_file(path.display().to_string(), Some(path.to_path_buf()), src))
    }

    pub fn file(&self, id: FileId) -> Arc<SourceFile> {
        self.files.read().unwrap_or_else(|e| e.into_inner())[id.0 as usize].clone()
    }

    pub fn file_of(&self, pos: u32) -> Option<Arc<SourceFile>> {
        let files = self.files.read().unwrap_or_else(|e| e.into_inner());
        let idx = files.partition_point(|f| f.start <= pos).checked_sub(1)?;
        let file = &files[idx];
        (pos <= file.end()).then(|| file.clone())
    }

    pub fn lookup(&self, pos: u32) -> Option<Loc> {
        let file = self.file_of(pos)?;
        let (line, col) = file.line_col(pos);
        Some(Loc { file, line, col })
    }

    pub fn snippet(&self, span: Span) -> Option<&'static str> {
        Some(self.file_of(span.lo)?.slice(span))
    }
}
