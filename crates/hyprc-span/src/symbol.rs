//! Interned strings.
//!
//! A [`Symbol`] is a `u32` index into one process-wide string table. Interning happens on every
//! identifier and literal the lexer sees, from many threads at once, so the table is sharded:
//! a string's hash picks one of [`SHARDS`] locks, and the strings themselves live in an
//! append-only, chunked array that readers index without any lock at all. Strings are copied
//! into per-shard arenas and never freed; a compiler process is short-lived and needs every
//! name until it exits.

use crate::Span;
use std::fmt;
use std::hash::{BuildHasher, Hash, Hasher};
use std::mem::MaybeUninit;
use std::sync::atomic::{AtomicPtr, AtomicU32, Ordering};
use std::sync::{Mutex, OnceLock};

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(u32);

impl Symbol {
    pub fn intern(s: &str) -> Symbol {
        interner().intern(s)
    }

    /// The string this symbol stands for. Lock-free.
    pub fn as_str(self) -> &'static str {
        interner().strings.get(self.0)
    }

    pub const fn as_u32(self) -> u32 {
        self.0
    }

    pub const fn from_u32(v: u32) -> Symbol {
        Symbol(v)
    }

    /// A keyword in every edition (`fn`, `struct`, …), or reserved in every edition.
    pub fn is_reserved(self, edition2018: bool) -> bool {
        (self.0 >= kw::As.0 && self.0 <= kw::Yield.0)
            || (edition2018 && self.0 >= kw::Async.0 && self.0 <= kw::Try.0)
    }

    /// `self`, `super`, `crate`, `Self` and `$crate`: keywords that may start a path.
    pub fn is_path_segment_keyword(self) -> bool {
        self == kw::SelfLower
            || self == kw::Super
            || self == kw::Crate
            || self == kw::SelfUpper
            || self == kw::DollarCrate
            || self == kw::PathRoot
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

/// A name with the place it was written. The span's syntax context carries macro hygiene.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Ident {
    pub name: Symbol,
    pub span: Span,
}

impl Ident {
    pub const fn new(name: Symbol, span: Span) -> Ident {
        Ident { name, span }
    }

    pub fn with_dummy_span(name: Symbol) -> Ident {
        Ident {
            name,
            span: Span::DUMMY,
        }
    }

    pub fn as_str(&self) -> &'static str {
        self.name.as_str()
    }
}

impl fmt::Debug for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

impl fmt::Display for Ident {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.name)
    }
}

const SHARDS: usize = 64;
/// Size of the first chunk of the string table; each further chunk doubles.
const FIRST_CHUNK_BITS: u32 = 12;
const CHUNKS: usize = 32 - FIRST_CHUNK_BITS as usize;
const ARENA_BLOCK: usize = 64 * 1024;

struct Interner {
    shards: [Mutex<Shard>; SHARDS],
    strings: StringTable,
}

struct Shard {
    /// Symbol indices, hashed by their string.
    table: hashbrown::HashTable<u32>,
    arena: Arena,
}

fn interner() -> &'static Interner {
    static INTERNER: OnceLock<Interner> = OnceLock::new();
    INTERNER.get_or_init(|| {
        let interner = Interner {
            shards: std::array::from_fn(|_| {
                Mutex::new(Shard {
                    table: hashbrown::HashTable::new(),
                    arena: Arena::default(),
                })
            }),
            strings: StringTable::new(),
        };
        // Predefined symbols get the indices their constants were given, in order.
        for (i, s) in PREDEFINED.iter().enumerate() {
            let sym = interner.intern(s);
            assert_eq!(sym.0 as usize, i, "duplicate predefined symbol `{s}`");
        }
        interner
    })
}

fn hash_str(s: &str) -> u64 {
    let mut h = rustc_hash::FxBuildHasher.build_hasher();
    s.hash(&mut h);
    h.finish()
}

impl Interner {
    fn intern(&self, s: &str) -> Symbol {
        let hash = hash_str(s);
        // The top bits pick the shard; hashbrown uses the low and the next 7 top bits.
        let shard = &self.shards[(hash >> 52) as usize % SHARDS];
        let mut shard = shard.lock().unwrap_or_else(|e| e.into_inner());
        let strings = &self.strings;
        if let Some(&idx) = shard.table.find(hash, |&idx| strings.get(idx) == s) {
            return Symbol(idx);
        }
        let stored: &'static str = shard.arena.alloc_str(s);
        let idx = strings.push(stored);
        let Shard { table, .. } = &mut *shard;
        table.insert_unique(hash, idx, |&idx| hash_str(strings.get(idx)));
        Symbol(idx)
    }
}

/// Append-only array of `&'static str` that can be read without locks while it grows:
/// chunk `k` holds `FIRST << k` entries and never moves once allocated.
struct StringTable {
    chunks: [AtomicPtr<MaybeUninit<&'static str>>; CHUNKS],
    len: AtomicU32,
}

impl StringTable {
    fn new() -> StringTable {
        StringTable {
            chunks: std::array::from_fn(|_| AtomicPtr::new(std::ptr::null_mut())),
            len: AtomicU32::new(0),
        }
    }

    #[inline]
    fn locate(idx: u32) -> (usize, usize) {
        let x = idx as u64 + (1u64 << FIRST_CHUNK_BITS);
        let k = 63 - x.leading_zeros() - FIRST_CHUNK_BITS;
        (k as usize, (x - (1u64 << (k + FIRST_CHUNK_BITS))) as usize)
    }

    fn push(&self, s: &'static str) -> u32 {
        let idx = self.len.fetch_add(1, Ordering::Relaxed);
        let (k, off) = Self::locate(idx);
        let mut chunk = self.chunks[k].load(Ordering::Acquire);
        if chunk.is_null() {
            let size = 1usize << (k as u32 + FIRST_CHUNK_BITS);
            let fresh: Box<[MaybeUninit<&'static str>]> = Box::new_uninit_slice(size);
            let fresh = Box::into_raw(fresh) as *mut MaybeUninit<&'static str>;
            match self.chunks[k].compare_exchange(
                std::ptr::null_mut(),
                fresh,
                Ordering::AcqRel,
                Ordering::Acquire,
            ) {
                Ok(_) => chunk = fresh,
                Err(existing) => {
                    // SAFETY: `fresh` came from `Box::into_raw` of a slice of `size` and was
                    // never shared.
                    drop(unsafe { Box::from_raw(std::ptr::slice_from_raw_parts_mut(fresh, size)) });
                    chunk = existing;
                }
            }
        }
        // SAFETY: `off` is within chunk `k`, and index `idx` was handed to this call alone.
        unsafe { (*chunk.add(off)).write(s) };
        idx
    }

    #[inline]
    fn get(&self, idx: u32) -> &'static str {
        let (k, off) = Self::locate(idx);
        let chunk = self.chunks[k].load(Ordering::Acquire);
        debug_assert!(!chunk.is_null());
        // SAFETY: a `Symbol` only exists after `push` wrote its slot, and whoever handed the
        // symbol to this thread synchronized with that write.
        unsafe { (*chunk.add(off)).assume_init() }
    }
}

#[derive(Default)]
struct Arena {
    block: Vec<u8>,
}

impl Arena {
    fn alloc_str(&mut self, s: &str) -> &'static str {
        if s.len() > ARENA_BLOCK / 4 {
            return Box::leak(s.into());
        }
        if self.block.capacity() - self.block.len() < s.len() {
            // The old block stays alive (leaked): strings handed out point into it.
            let old = std::mem::replace(&mut self.block, Vec::with_capacity(ARENA_BLOCK));
            std::mem::forget(old);
        }
        let start = self.block.len();
        self.block.extend_from_slice(s.as_bytes());
        // SAFETY: the block never reallocates (capacity was checked above) and is never freed;
        // the bytes are a copy of a `str`.
        unsafe {
            let ptr = self.block.as_ptr().add(start);
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(ptr, s.len()))
        }
    }
}

macro_rules! predefined {
    (
        Keywords { $($kw:ident: $kws:literal,)* }
        Symbols { $($sym:ident $(: $syms:literal)?,)* }
    ) => {
        const PREDEFINED: &[&str] = &[$($kws,)* $(predefined!(@str $sym $(: $syms)?),)*];

        #[allow(non_upper_case_globals)]
        pub mod kw {
            use super::Symbol;
            #[allow(non_camel_case_types, dead_code)]
            #[repr(u32)]
            enum Index { $($kw,)* }
            $(pub const $kw: Symbol = Symbol(Index::$kw as u32);)*
        }

        #[allow(non_upper_case_globals)]
        pub mod sym {
            use super::Symbol;
            const BASE: u32 = [$($kws,)*].len() as u32;
            #[allow(non_camel_case_types, dead_code)]
            #[repr(u32)]
            enum Index { $($sym,)* }
            $(pub const $sym: Symbol = Symbol(BASE + Index::$sym as u32);)*
        }
    };
    (@str $sym:ident) => { stringify!($sym) };
    (@str $sym:ident: $s:literal) => { $s };
}

// The order of keywords matters: `is_reserved` checks ranges of them.
predefined! {
    Keywords {
        // Special symbols.
        Empty: "",
        PathRoot: "{{root}}",
        DollarCrate: "$crate",
        Underscore: "_",
        // Keywords in every edition.
        As: "as",
        Break: "break",
        Const: "const",
        Continue: "continue",
        Crate: "crate",
        Else: "else",
        Enum: "enum",
        Extern: "extern",
        False: "false",
        Fn: "fn",
        For: "for",
        If: "if",
        Impl: "impl",
        In: "in",
        Let: "let",
        Loop: "loop",
        Match: "match",
        Mod: "mod",
        Move: "move",
        Mut: "mut",
        Pub: "pub",
        Ref: "ref",
        Return: "return",
        SelfLower: "self",
        SelfUpper: "Self",
        Static: "static",
        Struct: "struct",
        Super: "super",
        Trait: "trait",
        True: "true",
        Type: "type",
        Unsafe: "unsafe",
        Use: "use",
        Where: "where",
        While: "while",
        // Reserved in every edition.
        Abstract: "abstract",
        Become: "become",
        Box: "box",
        Do: "do",
        Final: "final",
        Macro: "macro",
        Override: "override",
        Priv: "priv",
        Typeof: "typeof",
        Unsized: "unsized",
        Virtual: "virtual",
        Yield: "yield",
        // Keywords from 2018 on.
        Async: "async",
        Await: "await",
        Dyn: "dyn",
        Try: "try",
        // Keywords from 2024 on.
        Gen: "gen",
        // Weak keywords: special only in some positions.
        Auto: "auto",
        Builtin: "builtin",
        Catch: "catch",
        Default: "default",
        MacroRules: "macro_rules",
        Raw: "raw",
        Reuse: "reuse",
        Safe: "safe",
        Union: "union",
        Yeet: "yeet",
        StaticLifetime: "'static",
        UnderscoreLifetime: "'_",
    }
    Symbols {
        // Primitive types.
        bool, char, str,
        i8, i16, i32, i64, i128, isize,
        u8, u16, u32, u64, u128, usize,
        f16, f32, f64, f128,
        // Crates and modules the compiler knows by name.
        core, std, alloc, proc_macro, compiler_builtins, test,
        prelude, prelude_import, rust_2015, rust_2018, rust_2021, rust_2024, v1,
        // Attributes.
        allow, warn, deny, forbid, expect,
        cfg, cfg_attr, derive, doc, path, inline, cold, no_mangle, export_name, link_name,
        link, link_section, repr, lang, macro_export, macro_use, no_std, no_core, no_main,
        no_implicit_prelude, feature, recursion_limit, crate_type, crate_name, global_allocator,
        panic_handler, track_caller, must_use, deprecated, used, naked, target_feature,
        rustc_builtin_macro, rustc_intrinsic, rustc_diagnostic_item, rustc_box,
        automatically_derived, non_exhaustive, ignore, should_panic, bench, test_case,
        proc_macro_derive, proc_macro_attribute, unstable, stable, rustc_const_unstable,
        rustc_const_stable, transparent, packed, align, simd, thread_local, start, main,
        // cfg names.
        target_os, target_family, target_arch, target_env, target_vendor, target_endian,
        target_pointer_width, target_has_atomic,
        unix, windows, debug_assertions, panic, overflow_checks, miri, doctest, any, all, not,
        // Things the parser and expander look at.
        r#macro_rules: "macro_rules!", vis, item, block, stmt, pat, pat_param, expr, expr_2021,
        ty, ident, lifetime, literal, meta, tt,
        offset_of, format_args, concat, stringify, include, include_str, include_bytes, env,
        option_env, line, column, file, module_path, compile_error, assert, unreachable,
        global_asm, asm, naked_asm, matches, todo, unimplemented, println, print, eprintln,
        eprint, format, write, writeln, vec, debug_assert, cfg_select, trace_macros,
        log_syntax, concat_bytes, concat_idents,
        // Lang item and well-known names.
        Option, Some, None, Result, Ok, Err, Box, Vec, String, Copy, Clone, Send, Sync, Sized,
        Drop, Fn, FnMut, FnOnce, Iterator, IntoIterator, into_iter, next, Future, IntoFuture,
        into_future, poll, Try, from_output, branch, from_residual, Default, Debug, Display,
        PartialEq, Eq, PartialOrd, Ord, Hash, Range, RangeFrom, RangeTo, RangeFull,
        RangeInclusive, RangeToInclusive, new, deref, deref_mut, index, index_mut,
        add, sub, mul, div, rem, neg, bitand, bitor, bitxor, shl, shr,
        Add, Sub, Mul, Div, Rem, Neg, Not, BitAnd, BitOr, BitXor, Shl, Shr, Deref, DerefMut,
        Index, IndexMut, Output, Target, Item, eq, ne, lt, le, gt, ge, partial_cmp, cmp,
        clone, drop, call, call_mut, call_once, from, into, len, ptr,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn predefined_round_trip() {
        assert_eq!(Symbol::intern("fn"), kw::Fn);
        assert_eq!(kw::Fn.as_str(), "fn");
        assert_eq!(Symbol::intern("usize"), sym::usize);
        assert_eq!(sym::not.as_str(), "not");
        assert_eq!(Symbol::intern("'static"), kw::StaticLifetime);
    }

    #[test]
    fn interning_from_many_threads() {
        let handles: Vec<_> = (0..8)
            .map(|t| {
                std::thread::spawn(move || {
                    (0..20_000)
                        .map(|i| {
                            let s = format!("name_{}", (i * 7 + t) % 5000);
                            (s.clone(), Symbol::intern(&s))
                        })
                        .collect::<Vec<_>>()
                })
            })
            .collect();
        for h in handles {
            for (s, sym) in h.join().unwrap() {
                assert_eq!(sym.as_str(), s);
                assert_eq!(Symbol::intern(&s), sym);
            }
        }
    }

    #[test]
    fn table_chunks() {
        assert_eq!(StringTable::locate(0), (0, 0));
        assert_eq!(StringTable::locate(4095), (0, 4095));
        assert_eq!(StringTable::locate(4096), (1, 0));
        assert_eq!(StringTable::locate(4096 + 8191), (1, 8191));
        assert_eq!(StringTable::locate(4096 + 8192), (2, 0));
    }
}
