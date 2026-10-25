//! The bottom of hyprc: source files and the spans that point into them, interned symbols, and
//! diagnostics.
//!
//! Everything here is global and thread-safe, because every later stage runs in parallel:
//! files are parsed on all cores, bodies are type-checked and compiled on all cores, and they
//! all share one source map and one symbol table.

mod diagnostic;
mod edition;
pub mod hygiene;
pub mod session;
mod source_map;
mod symbol;
pub mod target;

pub use diagnostic::{Diag, DiagCtxt, Label, Level, render_human};
pub use edition::Edition;
pub use source_map::{FileId, Loc, SourceFile, SourceMap, Span, SyntaxContext, source_map};
pub use symbol::{Ident, Symbol, kw, sym};

/// Hash maps keyed by compiler-internal values (symbols, ids): FxHash, which is several times
/// faster than SipHash on small keys and needs no protection against adversarial input here.
pub type FxHashMap<K, V> = std::collections::HashMap<K, V, rustc_hash::FxBuildHasher>;
pub type FxHashSet<K> = std::collections::HashSet<K, rustc_hash::FxBuildHasher>;
pub use rustc_hash::FxBuildHasher;
