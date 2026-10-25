//! Macros: `macro_rules!`/`macro` (the `mbe` engine) and the compiler's built-in macros.

pub mod builtin;
pub mod mbe;

use std::sync::Arc;

/// How a macro expands.
#[derive(Clone)]
pub enum MacroImpl {
    Rules(Arc<mbe::MacroRules>),
    Builtin(builtin::BuiltinMacro),
    /// The definition didn't compile (the error was reported); calls expand to nothing.
    Broken,
}
