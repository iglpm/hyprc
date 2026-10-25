//! Parses the standard library's source (rust-src of the active toolchain) and expects no
//! errors: the library uses nearly every piece of syntax, nightly features included. Skipped
//! when rust-src isn't installed.

use hyprc_span::DiagCtxt;
use hyprc_syntax::Edition;
use std::path::{Path, PathBuf};

fn library_dir() -> Option<PathBuf> {
    let out = std::process::Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .ok()?;
    let sysroot = String::from_utf8(out.stdout).ok()?;
    let dir = Path::new(sysroot.trim()).join("lib/rustlib/src/rust/library");
    dir.is_dir().then_some(dir)
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    for entry in std::fs::read_dir(dir).unwrap().flatten() {
        let path = entry.path();
        if path.is_symlink() {
            continue;
        }
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "rs") {
            out.push(path);
        }
    }
}

#[test]
fn standard_library_parses() {
    let Some(dir) = library_dir() else {
        eprintln!("rust-src not installed; skipping");
        return;
    };
    let mut files = Vec::new();
    collect(&dir, &mut files);
    // Big stacks, like the compiler's parsing threads.
    let failures = std::thread::Builder::new()
        .stack_size(hyprc_syntax::PARSER_STACK_SIZE)
        .spawn(move || {
            let mut failures = Vec::new();
            for path in &files {
                let src = std::fs::read_to_string(path).unwrap();
                // Vendored crates in `library/vendor` use older editions; the library itself
                // is 2024, and nothing in it parses differently in older editions.
                let edition = if path.components().any(|c| c.as_os_str() == "vendor") {
                    Edition::E2021
                } else {
                    Edition::E2024
                };
                let dcx = DiagCtxt::buffered();
                let tokens = hyprc_syntax::tokenize(&src, 1, &dcx);
                let _ = hyprc_syntax::parse_file(&tokens, edition, &dcx);
                if let Some(d) = dcx.take().first() {
                    failures.push(format!("{}: {}", path.display(), d.message));
                }
            }
            failures
        })
        .unwrap()
        .join()
        .unwrap();
    assert!(
        failures.is_empty(),
        "{} files failed to parse:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
