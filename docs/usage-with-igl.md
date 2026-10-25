# Using hyprc with Igel

`hyprc` is designed to serve as the high-throughput debug compiler engine for [Igel](https://github.com/runepm/igel).

When developers run `igl build` during development, Igel aims for sub-second turnarounds. Rather than shelling out to `rustc` with LLVM at `-O0` for every intermediate change, Igel delegates debug compilation to `hyprc`.

This document explains how `hyprc` is invoked, how flags and dependencies are passed, how sysroot resolution works, and how to troubleshoot compilation issues.

---

## 1. Invocation Model

`hyprc` accepts a command-line interface that mirrors `rustc`. Igel invokes `hyprc` using standard compiler arguments:

```bash
hyprc \
  --edition=2024 \
  --crate-name=my_crate \
  --crate-type=bin \
  --sysroot=/home/user/.rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu \
  -o target/debug/my_crate \
  src/main.rs
```

### Key Differences from `rustc`:
- **Borrow checking**: `hyprc` does not run the borrow checker during debug builds. Types, traits, sizes, layout invariants, and unsafe operations are checked, while lifetime verification is deferred to `igl check`. Igel must only run an artifact whose exact source fingerprint has passed that rustc-backed check.
- **Backend**: `hyprc` does not invoke LLVM. It converts MIR directly into x86-64 machine instructions and ELF objects in a single pass.
- **Linking**: For binaries, `hyprc` invokes `hyprlnk` (or `cc` as fallback) to produce native Linux ELF executables. For libraries (`--crate-type=lib` or `rlib`), it writes the `.rlib` archive / object directly without attempting to link a `main` entrypoint.

---

## 2. Standard Library Discovery (`--sysroot`)

`hyprc` compiles Rust code from source, including standard library crates like `core` and `alloc`.

When `--sysroot <PATH>` is specified (pointing to a Rust toolchain with `rust-src` installed), `hyprc` automatically discovers upstream crates:

```bash
# Compile alloc using sysroot core
hyprc \
  --edition=2024 \
  --crate-name=alloc \
  --crate-type=lib \
  --sysroot ~/.rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu \
  ~/.rustup/toolchains/1.98.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/alloc/src/lib.rs \
  -o /tmp/liballoc.rlib \
  --hyprc-time
```

`hyprc` will automatically inspect `$SYSROOT/lib/rustlib/src/rust/library/core/src/lib.rs` to satisfy dependencies without needing manual metadata extraction.

---

## 3. Fallback Mechanics in Igel

Igel maintains an automated fallback policy:

```
[igl build]
     │
     ▼
Can hyprc compile this crate?
 ├── YES ──▶ Run hyprc (0.1s - 1.2s build time) ──▶ Native machine code
 └── NO  ──▶ Fall back to rustc ──────────────────▶ Standard LLVM build
```

Fallback triggers include:
1. Crates utilizing compiler plugins or internal `rustc_*` features not yet supported by `hyprc`.
2. Procedural macro definition crates (`proc-macro = true` in Cargo.toml), which are compiled by host `rustc` and executed via Igel's proc-macro server.
3. Release builds (`igl build --release`), where full LLVM whole-program optimizations are desired.

---

## 4. Diagnostics & Debugging Flags

When debugging compiler internals or investigating how `hyprc` resolves types in a given crate, several inspection flags are built-in:

### Phase Timings: `--hyprc-time`
Prints the exact wall-clock time spent in each pipeline phase:
```bash
hyprc src/main.rs --hyprc-time
```
Output:
```
time:   326.64ms  parse, expand, resolve
time:   163.92ms  lower to HIR
time:   794.62ms  type check
time:     1.35ms  build MIR, collect instances
time:     0.03ms  code generation
time:     3.10ms  link
```

### Definitions Dump: `--hyprc-dump=defs`
Dumps all resolved `DefId`s, module trees, visibility, and macro definitions after name resolution:
```bash
hyprc src/lib.rs --hyprc-dump=defs
```

### HIR Dump: `--hyprc-dump=hir`
Dumps the desugared High-Level Intermediate Representation:
```bash
hyprc src/lib.rs --hyprc-dump=hir
```

### Types Dump: `--hyprc-dump=types`
Dumps the inferred type of every local variable and expression across all function bodies:
```bash
hyprc src/lib.rs --hyprc-dump=types
```

### MIR Dump: `--hyprc-dump=mir`
Dumps the monomorphized MIR control-flow graphs, basic blocks, places, and statements:
```bash
hyprc src/main.rs --hyprc-dump=mir
```

### Internal Environment Variables
- `HYPRC_DEBUG_SOLVER=1`: Dumps every trait evaluation obligation attempted by the solver, indented by depth.
- `HYPRC_DEBUG_METHOD=<name>`: Traces autoderef steps and trait evaluation candidates for a specific method call.
- `HYPRC_DEBUG_ENV=<filter>`: Displays the elaborated where-clauses and normalized projection bounds for an item's parameter environment.
