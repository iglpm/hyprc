//! The HIR and the lowering from the expanded, resolved AST.

pub mod hir;
mod lower;

pub use hir::*;
pub use lower::lower_crate;
