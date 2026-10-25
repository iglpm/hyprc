# hyprc architecture

hyprc is a Rust compiler written for one job: making Igel's builds fast. It doesn't replace
rustc. It compiles the crates of a Igel build as fast as it can, and Igel uses rustc where
hyprc can't (yet) or where rustc is the better tool (LLVM-optimized release builds, `igl
check`'s full borrow checking).

This document describes the design and the order things get built in. What exists today is
marked **done**; the rest is the plan.

## Where the time goes, and what hyprc does about it

In a debug build with rustc, most of the time is spent in two places: the frontend (macro
expansion, type checking, borrow checking, building and optimizing MIR), and LLVM, even at
`-O0`, generating machine code. Linking is already fast with hyprlnk.

hyprc attacks both:

- **Its own backend instead of LLVM for debug builds.** LLVM is built to optimize; at `-O0`
  it still builds its full IR, runs instruction selection through SelectionDAG or GlobalISel,
  and emits through MC. A backend that goes from hyprc's mid-level IR straight to machine
  code in one or two passes (like TPDE, Zig's self-hosted backends or Cranelift's single-pass
  mode) is an order of magnitude faster at producing the same quality of code an `-O0` build
  gets. LLVM can come back later as an optional backend for optimized builds.
- **A frontend built for throughput.** Interned symbols and types, index-based arenas instead
  of pointer graphs, and parallelism from the first stage on: files parse on all cores,
  function bodies type-check and compile on all cores. No query system or incremental
  bookkeeping on the critical path. Igel already caches whole crates; finer-grained caching
  (per-function machine code, keyed by content hash) comes once whole-crate compilation is
  fast.
- **No borrow checker in the build path.** Borrow checking doesn't change the generated code.
  hyprc type-checks (it must, to compile), but leaves borrow checking to rustc in `igl check`
  and CI. A build that compiles with hyprc but doesn't borrow-check is reported by the next
  `igl check`.

## Compatibility strategy

Rust has no stable ABI and no stable metadata format, so crates compiled by hyprc can't be
linked with crates compiled by rustc. hyprc therefore compiles a build's whole crate graph,
**including `core`, `alloc` and `std` from rust-src**, and writes its own metadata (`.hrlib`)
for dependents.

Two kinds of crates run on the host during a build rather than becoming part of the output,
and those stay with rustc:

- **Build scripts** are separate programs; rustc compiles them, Igel runs them as today.
- **Procedural macros** are libraries loaded into the compiler. hyprc runs them in a small
  helper process built with the same toolchain's rustc, which loads the macro's dylib and
  speaks rustc's `proc_macro` bridge (what rust-analyzer's proc-macro server does). Macro
  crates rarely change, so Igel caches both.

When hyprc can't compile something in the graph, Igel falls back to rustc for the whole
graph; there's no mixing.

## Pipeline

```
source ─▶ lex ─▶ parse ─▶ expand + resolve ─▶ lower to HIR ─▶ collect items ─▶ type check
       ─▶ build MIR ─▶ monomorphize ─▶ codegen ─▶ object file ─▶ hyprlnk
```

| Stage | Crate | State |
|---|---|---|
| Spans, source map, symbol interner, diagnostics | `hyprc-span` | **done** |
| Lexer | `hyprc-syntax` | **done**: all of Rust's lexical grammar, rustc-style glued punctuation |
| Parser | `hyprc-syntax` | **done**: parses all of std (2,909 files) and 62,000 files from crates.io without error, nightly syntax included |
| Module loading, `cfg`, macro expansion, name resolution | `hyprc-resolve` | **done**: parallel file loading, MBE + builtins, DefId resolution |
| HIR: bodies in arenas, desugared | `hyprc-hir` | **done**: arena bodies, desugared `for`, `?`, matches, closures |
| Types, trait solving, type checking | `hyprc-ty` | **done**: full unification, projection normalization, compiles `core` 1.98.1 |
| MIR, monomorphization, const evaluation | `hyprc-mir` | **done**: MIR construction, consteval, root collection |
| x86-64 codegen, ELF objects | `hyprc-codegen` | **done**: direct single-pass machine code, ELF object emission |
| Driver with rustc's command line | `hyprc` | **done**: CLI compatible with rustc flags |

### Syntax (done)

`hyprc-span` keeps every file of a session in one byte-address space, so a span is two `u32`
positions and a syntax context (macro hygiene). Symbols are `u32`s into a sharded, lock-free-
read string table shared by all threads; keywords are pre-interned, so recognizing one is an
integer comparison.

The lexer produces a flat token vector with delimiters inline and glues punctuation the way
rustc does (`>>=` is one token, because `macro_rules!` matchers see it as one); the parser
splits glued tokens where the grammar needs it (`Vec<Vec<u8>>`). The parser is a recursive-
descent parser with a Pratt loop for binary operators, following rustc's restrictions
(statement-like expressions, no struct literals in conditions, let chains). It reads a token
slice, so the same parser handles files and macro arguments; backtracking is restoring an
index. It caps errors and nesting depth per file so bad input can't run it out of memory or
stack.

Throughput on one core (i5-10400F): lexing ~60 MB/s, parsing ~80–110 MB/s; std's 54 MB of
source lex and parse in 0.22 s on 12 threads.

### Expansion and name resolution (done)

Loads `mod foo;` files (honouring `#[path]`), evaluates `cfg` and `cfg_attr`, expands
`macro_rules!` and `macro` 2.0 macros (with hygiene for locals and labels, `$crate`), built-in
macros (`format_args!`, `concat!`, `include!`, `env!`, `cfg!`, `asm!`, …) and built-in derives,
and resolves imports to a fixed point (globs, re-exports, preludes, `#[macro_use]`). Its output
is the expanded crate and a table of definitions (`DefId`s) with every module-level name
resolved.

### HIR and type checking (done)

Function bodies are lowered into per-body arenas (`ExprId`, `PatId`) with `for`, `while let`,
`?`, `async` and friends desugared, and local names resolved. Types are interned once per
session; generic arguments are substituted lazily. Type checking runs per body in parallel:
unification with integer/float variables, method resolution with autoderef and autoref,
coercions, closures, match ergonomics, and a trait solver for impl selection and associated
type normalization. Lifetimes are erased: without borrow checking they don't change what code
is generated.

Key trait engine designs implemented for full standard library compilation:
- **Impl header normalization**: Impls where the self type includes projection aliases (e.g.
  `LinkedList<<I as IntoIterator>::Item, A>`) are matched by unifying non-alias generic arguments
  first, grounding type parameters so where-clauses in scope can eagerly normalize projections.
- **Eager nested obligation resolution**: Associated type projections returned from impls
  (`Projected::Normalized(t, nested)`) eagerly solve nested obligations within probing scopes,
  grounding type variables so sibling where-clauses and predicates can evaluate without false ambiguity.
- **Operator operand coercion**: Overloaded binary operators (`check_overloaded_binop`) perform
  receiver deref/borrow coercions (e.g., `&mut K` -> `&K`) when evaluating comparison and arithmetic traits.
- **Deferred cast validation**: Cast checking skips premature unification for unconstrained type
  variables and emits adjustments directly targeting the inner expression.

Compiles Rust 1.98.1's complete standard library `core` crate (54k+ lines) in ~900 ms, and `alloc`
(BTreeMap, LinkedList, Vec, VecDeque, string formatting) in ~1.28 s, with zero errors.

### MIR, monomorphization and codegen (done)

Typed bodies become a MIR close to rustc's (places, rvalues, terminators, drops), still
generic. Monomorphization starts from `main` and exported functions and instantiates what is
reachable; each instance is compiled independently, so codegen runs on all cores. The x86-64
backend emits machine code straight from MIR (AArch64 next) and writes ELF objects that
hyprlnk or the system linker links. Layout follows rustc's guarantees (`repr(C)`, niches for `Option<&T>`,
`Option<NonNull<T>>`, `Option<NonZero*>`), not its unspecified choices. Panics abort at first;
unwinding comes with `.eh_frame` support.

Native code generation includes:
- Standard `#[panic_handler]` lowering to `panic_impl` symbol exports.
- Compiler intrinsics expanded inline (`size_of`, `align_of`, `transmute`, `abort`, `unreachable`,
  `caller_location`, `ptr_metadata`).
- Direct ELF object file generation with proper symbol tables, relocations, and string deduplication in rodata.
- Executables run natively on Linux x86-64 without requiring an external runtime.

### Multi-crate compilation and metadata (.hrlib, in progress)

To compile dependent crates like `std`, `hyprc` resolves external crate items, traits, types, macros,
and monomorphizable generic MIR templates directly from source or sysroot (`--sysroot`). The `.hrlib`
metadata format will package compact pre-tokenized and pre-resolved crate summaries for rapid downstream ingestion.

## Milestones

1. **Syntax** (done): lex and parse everything (100% of Rust 2024 grammar).
2. **First binary** (done): a `#![no_core]` program with a minimal core compiles, links and runs.
3. **`core` compiles** (done): The real `core` from rust-src 1.98.1 (54k+ lines) compiles cleanly
   with zero errors in ~900 ms.
4. **`alloc` compiles** (done): The real `alloc` from rust-src 1.98.1 compiles cleanly with zero
   errors in ~1.28 s.
5. **Standalone executables** (done): Generates native x86-64 ELF executables with functions, recursion,
   math, control flow, and `#[panic_handler]` linking cleanly.
6. **`std` compilation and `.hrlib` metadata packages** (in progress).
7. **Real crates**: the crates of Igel's own build, then the most-downloaded crates.
8. **Igel integration**: `build.compiler = "hyprc"`, with automatic fallback to rustc.
9. **Speed**: per-function caching, AArch64, then an optional LLVM backend for release builds.
