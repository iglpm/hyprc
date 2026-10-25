//! Types, item signatures, trait solving and type checking.
//!
//! [`TyCtxt`] holds the HIR and answers questions about items ("queries": the generics of
//! an item, its type, its where-clauses, an ADT's fields, an impl's trait). Answers are
//! computed on first use and cached per definition, from any thread: type checking runs
//! on all cores, each body independently.

pub mod collect;
pub mod consteval;
pub mod fold;
pub mod infer;
pub mod intern;
pub mod lower_ty;
pub mod print;
pub mod traits;
pub mod ty;
pub mod typeck;

pub use ty::*;

use hyprc_hir as hir;
use hyprc_hir::{BodyId, DefId};
use hyprc_span::{Diag, DiagCtxt, FxHashMap, Symbol};
use std::cell::RefCell;
use std::sync::{Arc, OnceLock};

/// The type-level view of a crate, shared by all threads.
pub struct TyCtxt<'h> {
    pub hir: &'h hir::Crate,
    pub dcx: &'h DiagCtxt,
    pub pointer_width: u32,
    q: collect::Queries,
    typeck: Vec<OnceLock<Arc<typeck::TypeckResults>>>,
}

thread_local! {
    /// Queries being computed on this thread, to catch cycles (`type A = A;`).
    static ACTIVE: RefCell<Vec<(u8, DefId)>> = const { RefCell::new(Vec::new()) };
}

impl<'h> TyCtxt<'h> {
    pub fn new(hir: &'h hir::Crate, dcx: &'h DiagCtxt, pointer_width: u32) -> TyCtxt<'h> {
        let n = hir.items.len();
        let names: Vec<String> = (0..n).map(|i| hir.def_path(DefId(i as u32))).collect();
        let names = Arc::new(names);
        print::set_namer(Arc::new(move |d: DefId| {
            names
                .get(d.0 as usize)
                .cloned()
                .unwrap_or_else(|| format!("{d:?}"))
        }));
        TyCtxt {
            hir,
            dcx,
            pointer_width,
            q: collect::Queries::new(n),
            typeck: (0..hir.bodies.len()).map(|_| OnceLock::new()).collect(),
        }
    }

    pub fn emit(&self, d: Diag) {
        self.dcx.emit(d);
    }

    pub fn lang_item(&self, name: &str) -> Option<DefId> {
        self.hir.lang_item(name)
    }

    pub fn lang_items(&self) -> &FxHashMap<Symbol, DefId> {
        &self.hir.lang_items
    }

    pub fn def_path(&self, def: DefId) -> String {
        self.hir.def_path(def)
    }

    /// Runs `f` as query `kind` for `def`, unless that query is already running for it on
    /// this thread (a cycle): then `on_cycle` is the answer.
    pub(crate) fn guarded<T>(
        &self,
        kind: u8,
        def: DefId,
        on_cycle: impl FnOnce() -> T,
        f: impl FnOnce() -> T,
    ) -> T {
        let cyclic = ACTIVE.with(|a| a.borrow().contains(&(kind, def)));
        if cyclic {
            return on_cycle();
        }
        ACTIVE.with(|a| a.borrow_mut().push((kind, def)));
        let r = f();
        ACTIVE.with(|a| a.borrow_mut().pop());
        r
    }

    /// The type-check results of a body (computed on first use).
    pub fn typeck(&self, body: BodyId) -> Arc<typeck::TypeckResults> {
        self.typeck[body.index()]
            .get_or_init(|| {
                // `HYPRC_SLOW_TYPECK=<ms>`: report bodies that take longer (finding blowups).
                static SLOW: std::sync::OnceLock<Option<u128>> = std::sync::OnceLock::new();
                let slow = *SLOW.get_or_init(|| {
                    std::env::var("HYPRC_SLOW_TYPECK")
                        .ok()
                        .and_then(|v| v.parse().ok())
                });
                let start = slow.map(|_| std::time::Instant::now());
                if slow == Some(0) {
                    eprintln!(
                        "hyprc: type checking `{}` (body {})",
                        self.def_path(self.hir.body(body).owner),
                        body.0
                    );
                }
                let r = Arc::new(typeck::check_body(self, body));
                if let (Some(ms), Some(start)) = (slow, start) {
                    let took = start.elapsed().as_millis();
                    if took >= ms {
                        let owner = self.hir.body(body).owner;
                        eprintln!(
                            "hyprc: type checking `{}` took {took} ms",
                            self.def_path(owner)
                        );
                    }
                }
                r
            })
            .clone()
    }

    /// Type-checks every local crate body, on all cores.
    pub fn typeck_all(&self) {
        use rayon::prelude::*;
        (0..self.hir.bodies.len()).into_par_iter().for_each(|i| {
            let body = self.hir.body(BodyId(i as u32));
            if self.hir.is_local(body.owner) {
                let _ = self.typeck(BodyId(i as u32));
            }
        });
    }
}
