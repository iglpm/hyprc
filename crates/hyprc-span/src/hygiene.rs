//! Macro hygiene, as rustc models it.
//!
//! Every macro expansion gets an [`ExpnId`]. Tokens the macro's definition contributed carry
//! a [`SyntaxContext`] that records the expansion ("a mark") with a transparency:
//!
//! - `macro_rules!` marks are *semi-transparent*: local variables and labels a macro defines
//!   are invisible to the caller's code and vice versa, but items aren't hygienic.
//! - `macro` (2.0) marks are *opaque*: every name is resolved where the macro was defined.
//! - Built-in and proc macros using `Span::call_site()` are *transparent*: no hygiene at all.
//!
//! A context is a chain of marks. Name resolution compares contexts after dropping the marks
//! that don't apply: locals compare [`SyntaxContext::normalize_to_macro_rules`], items compare
//! [`SyntaxContext::normalize_to_macros_2_0`].

use crate::{Edition, Span, SyntaxContext};
use std::sync::{OnceLock, RwLock};

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, PartialOrd, Ord)]
pub struct ExpnId(pub u32);

impl ExpnId {
    /// Code written in source, not produced by any macro.
    pub const ROOT: ExpnId = ExpnId(0);
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Transparency {
    Transparent,
    SemiTransparent,
    Opaque,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExpnKind {
    Root,
    /// A function-like macro (`m!()`), an attribute macro or a derive.
    Macro,
    /// Compiler desugaring (`for`, `?`, `async`).
    Desugaring,
}

#[derive(Clone, Debug)]
pub struct ExpnData {
    pub kind: ExpnKind,
    /// The macro's name, for diagnostics and `module_path!`-style queries.
    pub name: crate::Symbol,
    pub parent: ExpnId,
    pub call_site: Span,
    /// Where the macro was defined.
    pub def_site: Span,
    /// The crate whose `$crate` this expansion's definition tokens refer to (a `u32` crate
    /// number; meaning is up to the resolver).
    pub def_crate: u32,
    /// The edition of the macro's definition: its tokens follow that edition's rules.
    pub edition: Edition,
    /// Expansions of `#[allow_internal_unstable]` macros may use unstable features.
    pub allow_internal_unstable: bool,
    /// The macro's definition (a resolver `DefId` as `u32`; `u32::MAX` if none).
    pub macro_def: u32,
}

#[derive(Clone, Copy, Debug)]
struct ContextData {
    outer_expn: ExpnId,
    outer_transparency: Transparency,
    parent: SyntaxContext,
    /// This context with only opaque marks kept.
    opaque: SyntaxContext,
    /// This context with opaque and semi-transparent marks kept.
    opaque_and_semi: SyntaxContext,
}

struct HygieneData {
    expns: Vec<ExpnData>,
    contexts: Vec<ContextData>,
    /// (parent, expn, transparency) → context, so equal chains get equal contexts.
    interned: crate::FxHashMap<(SyntaxContext, ExpnId, Transparency), SyntaxContext>,
}

fn data() -> &'static RwLock<HygieneData> {
    static DATA: OnceLock<RwLock<HygieneData>> = OnceLock::new();
    DATA.get_or_init(|| {
        RwLock::new(HygieneData {
            expns: vec![ExpnData {
                kind: ExpnKind::Root,
                name: crate::kw::Empty,
                parent: ExpnId::ROOT,
                call_site: Span::DUMMY,
                def_site: Span::DUMMY,
                def_crate: 0,
                edition: Edition::E2021,
                allow_internal_unstable: false,
                macro_def: u32::MAX,
            }],
            contexts: vec![ContextData {
                outer_expn: ExpnId::ROOT,
                outer_transparency: Transparency::Opaque,
                parent: SyntaxContext::ROOT,
                opaque: SyntaxContext::ROOT,
                opaque_and_semi: SyntaxContext::ROOT,
            }],
            interned: Default::default(),
        })
    })
}

impl ExpnId {
    pub fn fresh(data_: ExpnData) -> ExpnId {
        let mut d = data().write().unwrap_or_else(|e| e.into_inner());
        d.expns.push(data_);
        ExpnId(d.expns.len() as u32 - 1)
    }

    pub fn data(self) -> ExpnData {
        data().read().unwrap_or_else(|e| e.into_inner()).expns[self.0 as usize].clone()
    }

    /// Is `self` `ancestor` or expanded (transitively) from inside it?
    pub fn is_descendant_of(self, ancestor: ExpnId) -> bool {
        let d = data().read().unwrap_or_else(|e| e.into_inner());
        let mut e = self;
        loop {
            if e == ancestor {
                return true;
            }
            if e == ExpnId::ROOT {
                return false;
            }
            e = d.expns[e.0 as usize].parent;
        }
    }
}

impl HygieneData {
    fn intern(&mut self, parent: SyntaxContext, expn: ExpnId, t: Transparency) -> SyntaxContext {
        if let Some(&c) = self.interned.get(&(parent, expn, t)) {
            return c;
        }
        let p = self.contexts[parent.0 as usize];
        // The normalized forms drop the marks a normalization ignores. When the parent is
        // already normalized, the new context is its own normalized form (`None` below);
        // otherwise it is the mark applied to the normalized parent. Recurse before
        // allocating ours, so indices stay simple.
        let opaque = match t {
            Transparency::Opaque if p.opaque == parent => None,
            Transparency::Opaque => Some(self.intern(p.opaque, expn, t)),
            _ => Some(p.opaque),
        };
        let opaque_and_semi = match t {
            Transparency::Transparent => Some(p.opaque_and_semi),
            _ if p.opaque_and_semi == parent => None,
            _ => Some(self.intern(p.opaque_and_semi, expn, t)),
        };
        let new = SyntaxContext(self.contexts.len() as u32);
        self.contexts.push(ContextData {
            outer_expn: expn,
            outer_transparency: t,
            parent,
            opaque: opaque.unwrap_or(new),
            opaque_and_semi: opaque_and_semi.unwrap_or(new),
        });
        self.interned.insert((parent, expn, t), new);
        new
    }
}

impl SyntaxContext {
    /// Adds a mark for `expn` to this context.
    pub fn apply_mark(self, expn: ExpnId, transparency: Transparency) -> SyntaxContext {
        if expn == ExpnId::ROOT {
            return self;
        }
        let mut d = data().write().unwrap_or_else(|e| e.into_inner());
        d.intern(self, expn, transparency)
    }

    pub fn outer_expn(self) -> ExpnId {
        data().read().unwrap_or_else(|e| e.into_inner()).contexts[self.0 as usize].outer_expn
    }

    pub fn outer_transparency(self) -> Transparency {
        data().read().unwrap_or_else(|e| e.into_inner()).contexts[self.0 as usize]
            .outer_transparency
    }

    pub fn parent(self) -> SyntaxContext {
        data().read().unwrap_or_else(|e| e.into_inner()).contexts[self.0 as usize].parent
    }

    /// The context to compare for local variables and labels.
    pub fn normalize_to_macro_rules(self) -> SyntaxContext {
        data().read().unwrap_or_else(|e| e.into_inner()).contexts[self.0 as usize].opaque_and_semi
    }

    /// The context to compare for items.
    pub fn normalize_to_macros_2_0(self) -> SyntaxContext {
        data().read().unwrap_or_else(|e| e.into_inner()).contexts[self.0 as usize].opaque
    }

    /// The marks of this context, outermost first: (expansion, transparency).
    pub fn marks(self) -> Vec<(ExpnId, Transparency)> {
        let d = data().read().unwrap_or_else(|e| e.into_inner());
        let mut out = Vec::new();
        let mut c = self;
        while c != SyntaxContext::ROOT {
            let cd = d.contexts[c.0 as usize];
            out.push((cd.outer_expn, cd.outer_transparency));
            c = cd.parent;
        }
        out
    }

    /// The expansion whose definition `$crate` in this context refers to: the outermost
    /// non-transparent mark.
    pub fn dollar_crate_expn(self) -> ExpnId {
        let d = data().read().unwrap_or_else(|e| e.into_inner());
        let mut c = self;
        while c != SyntaxContext::ROOT {
            let cd = d.contexts[c.0 as usize];
            if cd.outer_transparency != Transparency::Transparent {
                return cd.outer_expn;
            }
            c = cd.parent;
        }
        ExpnId::ROOT
    }
}

impl Span {
    /// The edition this span's code follows: its macro's, or the crate's for source code.
    pub fn expn_edition(self) -> Option<Edition> {
        let e = self.ctxt.outer_expn();
        if e == ExpnId::ROOT {
            None
        } else {
            Some(e.data().edition)
        }
    }

    pub fn from_expansion(self) -> bool {
        self.ctxt != SyntaxContext::ROOT
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn expn() -> ExpnId {
        ExpnId::fresh(ExpnData {
            kind: ExpnKind::Macro,
            name: crate::Symbol::intern("m"),
            parent: ExpnId::ROOT,
            call_site: Span::DUMMY,
            def_site: Span::DUMMY,
            def_crate: 0,
            edition: Edition::E2021,
            allow_internal_unstable: false,
            macro_def: u32::MAX,
        })
    }

    #[test]
    fn normalization() {
        let root = SyntaxContext::ROOT;
        let e1 = expn();
        let semi = root.apply_mark(e1, Transparency::SemiTransparent);
        assert_ne!(semi, root);
        // `macro_rules!` marks count for locals but not for items.
        assert_eq!(semi.normalize_to_macro_rules(), semi);
        assert_eq!(semi.normalize_to_macros_2_0(), root);
        let e2 = expn();
        let opaque = semi.apply_mark(e2, Transparency::Opaque);
        assert_eq!(opaque.normalize_to_macro_rules(), opaque);
        let only_opaque = root.apply_mark(e2, Transparency::Opaque);
        assert_eq!(opaque.normalize_to_macros_2_0(), only_opaque);
        let transparent = root.apply_mark(e1, Transparency::Transparent);
        assert_eq!(transparent.normalize_to_macro_rules(), root);
        // Interning: the same chain is the same context.
        assert_eq!(root.apply_mark(e1, Transparency::SemiTransparent), semi);
        assert_eq!(
            opaque.marks(),
            vec![
                (e2, Transparency::Opaque),
                (e1, Transparency::SemiTransparent)
            ]
        );
    }
}
