# hyprc

`hyprc` is a high-throughput Rust compiler built for one job: making [Igel](https://github.com/runepm/igel)'s edit-compile-test loop as fast as physically possible.

It does not aim to replace `rustc` for release binaries or whole-program optimization. It doesn't run LLVM passes on debug builds, and it doesn't run borrow checking on the critical path (that belongs in `igl check` and CI). Instead, `hyprc` compiles crate graphs straight from source to machine code an order of magnitude faster than `rustc`.

## Why `rustc` debug builds are slow, and what `hyprc` does about it

When running `cargo build` in debug mode, time is lost in two bottlenecks:

1. **Frontend bookkeeping and serialization**: Recursive macro expansion, incremental dependency graph tracking, query caches, and borrow-checking thousands of functions that haven't changed.
2. **LLVM code generation**: Even at `-O0`, LLVM constructs heavy SSA intermediate representations, executes instruction selection (SelectionDAG / GlobalISel), runs register allocation, and emits machine code through MC. LLVM is an optimizer; it was never designed for sub-second edit-compile loops.

`hyprc` replaces both:

- **Direct machine code generation**: Emits x86-64 machine instructions and ELF object files in a single pass straight from MIR. No LLVM, no intermediate textual IR, no register allocation thrashing.
- **Data-oriented, parallel frontend**:
  - Lock-free, sharded symbol table with pre-interned keywords (keyword checks are single integer comparisons).
  - Whole-crate flat span space (`u32` byte-offset pairs + syntax context).
  - Parallel file discovery and parsing across all available cores using `rayon`.
  - Arena-allocated HIR (`ExprId`, `PatId`) with desugared control flow (`for`, `while let`, `?`, `async`).
  - Fast unification-based type checking and trait solver with eager projection normalization.
- **Zero borrow-checking overhead on the build path**: Borrow checking enforces safety invariants but doesn't change generated machine code. `hyprc` validates types, shapes, trait bounds, and unsafe operations. Full borrow analysis runs in `igl check`; Igel must only run a `hyprc` artifact after the same source fingerprint has passed that check.

## Performance Snapshot

Compiling standard library crates from source (Rust 1.98.1 `rust-src`, heavily generic, macro-dense, trait-intensive systems code):

### `core` (54,000+ lines):
```
$ hyprc --edition=2024 --crate-name=core --crate-type=lib library/core/src/lib.rs --hyprc-time

time:   314.21ms  parse, expand, resolve
time:   148.09ms  lower to HIR
time:   449.83ms  type check
time:     0.96ms  build MIR, collect instances
time:     0.04ms  code generation
--------------------------------------------------
Total:  ~913 ms (0 errors)
```

### `alloc` (collections, BTreeMap, LinkedList, Vec, VecDeque, string formatting):
```
$ hyprc --edition=2024 --crate-name=alloc --crate-type=lib --sysroot ~/.rustup/toolchains/... library/alloc/src/lib.rs --hyprc-time

time:   326.64ms  parse, expand, resolve
time:   163.92ms  lower to HIR
time:   794.62ms  type check
time:     1.35ms  build MIR, collect instances
time:     0.03ms  code generation
--------------------------------------------------
Total:  ~1.28 s (0 errors)
```

Both `core` and `alloc` parse, expand, type-check, and emit in ~1 second.

## Pipeline Architecture

```
source
  │
  ▼
[ hyprc-span ]     Global source map, interned symbols, diagnostics
  │
  ▼
[ hyprc-syntax ]   Lexer & recursive-descent Pratt parser (glued punctuation, backtrack-free)
  │
  ▼
[ hyprc-resolve ]  Parallel file loader, CFG expansion, macro engine (MBE + builtins), DefId resolution
  │
  ▼
[ hyprc-hir ]      Arenas for desugared item and function bodies
  │
  ▼
[ hyprc-ty ]       Type inference (unification), method resolution, trait solver & normalization
  │
  ▼
[ hyprc-mir ]      Control flow graph, const evaluation, monomorphization instance collector
  │
  ▼
[ hyprc-codegen ]  Direct x86-64 machine code generation & ELF writer
  │
  ▼
[ hyprlnk / cc ]   Binary linkage
```

### Crates Breakdown

| Crate | Responsibilities |
|---|---|
| [`hyprc-span`](crates/hyprc-span) | Session options, byte-offset source map, target specs, lock-free symbol table, diagnostics reporter. |
| [`hyprc-syntax`](crates/hyprc-syntax) | Lexer with rustc-compatible token gluing (`>>=`, `..=`), recursive-descent parser with Pratt expression parsing. |
| [`hyprc-resolve`](crates/hyprc-resolve) | Multi-core out-of-line module reader, `cfg` evaluator, declarative macro expander (`macro_rules!`), fixed-point import resolver. |
| [`hyprc-hir`](crates/hyprc-hir) | Desugared High-Level Intermediate Representation stored in compact index arenas. |
| [`hyprc-ty`](crates/hyprc-ty) | Type interner, shallow inference context, autoderef/autoref, closure capture analysis, trait goal solver. |
| [`hyprc-mir`](crates/hyprc-mir) | Basic blocks, places, rvalues, statements, terminators, MIR const evaluator, monomorphization instance tree. |
| [`hyprc-codegen`](crates/hyprc-codegen) | Single-pass x86-64 instruction encoder, memory layouts, ELF object writer, linker driver. |
| [`hyprc`](src) | CLI driver accepting rustc-compatible flags. |

## Building & Testing

Prerequisites: A working Rust toolchain (1.89+).

```bash
# Build release compiler
cargo build --release

# Run unit and integration tests
cargo test --all-targets

# Run the run-pass test suite (compiles & runs executables)
cargo test --test run_pass
```

## CLI Usage

`hyprc` accepts standard `rustc` CLI options, making it a drop-in driver for build runners:

```bash
# Compile a single file to an executable
hyprc --edition=2024 main.rs -o main

# Compile a library crate
hyprc --crate-name=foo --crate-type=lib --edition=2024 src/lib.rs -o libfoo.rlib --hyprc-time

# Print compiler pass timings
hyprc main.rs --hyprc-time

# Inspect definitions or HIR dump
hyprc src/lib.rs --hyprc-dump=defs
```

Supported flags include:
- `--crate-name <NAME>`
- `--crate-type <bin|lib|rlib|staticlib|cdylib>`
- `--edition <2015|2018|2021|2024>`
- `--emit <link|obj|metadata|dep-info>`
- `-o <FILE>`, `--out-dir <DIR>`
- `--cfg <SPEC>`
- `--extern <NAME=PATH>`
- `-L [<KIND>=]<PATH>`
- `-C <opt-level|linker|link-arg|panic>`
- `--sysroot <PATH>`
- `--target <TRIPLE>`
- `--hyprc-time` (prints millisecond breakdown per pipeline phase)

## Integration with Igel

`hyprc` is designed to be orchestrated by `igl`:

1. `igl` evaluates the crate graph and invokes `hyprc` for debug builds.
2. If a crate requires unstable compiler plugins or features `hyprc` does not yet support, `igl` transparently falls back to `rustc` for that crate.
3. Procedural macro crates run through a lightweight host runner, keeping compilation decoupled from host compiler internals.
4. Final object files link via `hyprlnk` or system linker for instantaneous link times.

## Roadmap

- [x] Milestone 1: Full syntax parser (100% of Rust 2024 grammar).
- [x] Milestone 2: Minimal `#![no_core]` binaries compile, link, and run.
- [x] Milestone 3: Full standard library `core` crate compiles cleanly with 0 errors (<1s).
- [x] Milestone 4: Full standard library `alloc` crate compiles cleanly with 0 errors (~1.2s).
- [x] Milestone 5: Standalone binary executable generation with direct x86-64 machine code and `#[panic_handler]`.
- [ ] Milestone 6: `std` crate compilation and `.hrlib` multi-crate metadata serializer.
- [ ] Milestone 7: Top 100 crates.io packages compiling natively.
- [ ] Milestone 8: Native AArch64 machine code generation.
- [ ] Milestone 9: Content-addressed per-function machine code cache.

## License

Licensed under either of [MIT](LICENSE-MIT.md) or [Apache-2.0](LICENSE-APACHE.md) at your option.
