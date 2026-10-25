//! Compiles each program in `tests/run-pass` with hyprc, runs it, and compares its output
//! with the `.stdout` file next to it (recorded from rustc by `tests/bless.sh`).

use std::path::Path;
use std::process::Command;

#[test]
fn run_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/run-pass");
    let out_dir = std::env::temp_dir().join(format!("hyprc-run-pass-{}", std::process::id()));
    std::fs::create_dir_all(&out_dir).unwrap();
    let hyprc = env!("CARGO_BIN_EXE_hyprc");
    let mut entries: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|e| e == "rs"))
        .collect();
    entries.sort();
    let mut failures = Vec::new();
    for src in &entries {
        let name = src.file_stem().unwrap().to_string_lossy().to_string();
        let expected = match std::fs::read_to_string(src.with_extension("stdout")) {
            Ok(e) => e,
            Err(_) => {
                failures.push(format!("{name}: no .stdout (run tests/bless.sh)"));
                continue;
            }
        };
        let exe = out_dir.join(&name);
        let c = Command::new(hyprc)
            .args(["--edition", "2021", "-C", "overflow-checks=off"])
            .arg(src)
            .arg("-o")
            .arg(&exe)
            .output()
            .unwrap();
        if !c.status.success() {
            failures.push(format!(
                "{name}: compile failed:\n{}",
                String::from_utf8_lossy(&c.stderr)
            ));
            continue;
        }
        let r = Command::new(&exe).output().unwrap();
        let got = String::from_utf8_lossy(&r.stdout);
        if got != expected {
            failures.push(format!(
                "{name}: output differs\n--- expected\n{expected}--- got\n{got}"
            ));
        }
    }
    let _ = std::fs::remove_dir_all(&out_dir);
    assert!(
        failures.is_empty(),
        "{} of {} failed:\n\n{}",
        failures.len(),
        entries.len(),
        failures.join("\n\n")
    );
}
