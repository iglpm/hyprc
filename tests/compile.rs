use std::path::Path;
use std::process::Command;

#[test]
fn unsafe_operations_require_unsafe_context() {
    let source =
        Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/compile-fail/unsafe_inline_asm.rs");
    let output = Command::new(env!("CARGO_BIN_EXE_hyprc"))
        .args(["--edition", "2021", "--emit", "metadata"])
        .arg(source)
        .output()
        .unwrap();

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error[E0133]: use of inline assembly is unsafe"),
        "unexpected diagnostic:\n{stderr}"
    );
}
