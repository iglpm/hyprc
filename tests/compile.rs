use std::path::Path;
use std::process::Command;

fn compile(source: &str) -> std::process::Output {
    compile_with_edition(source, "2021")
}

fn compile_with_edition(source: &str, edition: &str) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_hyprc"))
        .args(["--edition", edition, "--emit", "metadata"])
        .arg(Path::new(env!("CARGO_MANIFEST_DIR")).join(source))
        .output()
        .unwrap()
}

#[test]
fn built_in_derives_resolve_core_in_rust_2015() {
    let output = compile_with_edition("tests/compile-pass/derive_2015.rs", "2015");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn unix_threads_have_a_safe_spawn_join_and_local_storage_surface() {
    let output = compile("tests/compile-pass/threading.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn cast_targets_do_not_leak_into_branch_inference() {
    let output = compile("tests/compile-pass/cast_branch_inference.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn no_std_crate_can_explicitly_link_std() {
    let output = compile("tests/compile-pass/explicit_std.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn standard_sync_primitives_have_the_expected_safe_surface() {
    let output = compile("tests/compile-pass/std_sync.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn formatting_macros_keep_their_nested_delimiters_balanced() {
    let output = compile("tests/compile-pass/formatting_macros.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn os_strings_and_paths_support_real_build_script_comparisons() {
    let output = compile("tests/compile-pass/os_paths.rs");
    assert!(
        output.status.success(),
        "unexpected diagnostic:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn source_metadata_carries_transitive_dependencies() {
    let dir = std::env::temp_dir().join(format!("hyprc-transitive-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let leaf = dir.join("leaf.rs");
    let middle = dir.join("middle.rs");
    let top = dir.join("top.rs");
    std::fs::write(&leaf, "pub fn leaf() -> u32 { 1 }").unwrap();
    std::fs::write(&middle, "pub fn middle() -> u32 { leaf::leaf() }").unwrap();
    std::fs::write(&top, "pub fn top() -> u32 { middle::middle() }").unwrap();

    let hyprc = env!("CARGO_BIN_EXE_hyprc");
    let build = |name: &str, source: &Path, dependency: Option<(&str, &Path)>| {
        let mut command = Command::new(hyprc);
        command
            .args([
                "--edition",
                "2021",
                "--crate-name",
                name,
                "--crate-type",
                "lib",
            ])
            .args(["--emit", "metadata", "--out-dir"])
            .arg(&dir)
            .arg("-L")
            .arg(format!("dependency={}", dir.display()));
        if let Some((dependency_name, dependency_path)) = dependency {
            command
                .arg("--extern")
                .arg(format!("{dependency_name}={}", dependency_path.display()));
        }
        command.arg(source).output().unwrap()
    };

    assert!(build("leaf", &leaf, None).status.success());
    let leaf_meta = dir.join("libleaf.rmeta");
    let middle_output = build("middle", &middle, Some(("leaf", &leaf_meta)));
    assert!(
        middle_output.status.success(),
        "{}",
        String::from_utf8_lossy(&middle_output.stderr)
    );
    let middle_meta = dir.join("libmiddle.rmeta");
    let top_output = build("top", &top, Some(("middle", &middle_meta)));
    let _ = std::fs::remove_dir_all(&dir);
    assert!(
        top_output.status.success(),
        "{}",
        String::from_utf8_lossy(&top_output.stderr)
    );
}

#[test]
fn unsafe_operations_require_unsafe_context() {
    let output = compile("tests/compile-fail/unsafe_inline_asm.rs");

    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("error[E0133]: use of inline assembly is unsafe"),
        "unexpected diagnostic:\n{stderr}"
    );
}
