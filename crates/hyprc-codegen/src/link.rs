//! Linking: runs the C compiler driver (`cc`, or `-C linker`) the way rustc does, which
//! finds the C runtime and libc and runs the linker (`-fuse-ld` picks hyprlnk or another).

use std::path::{Path, PathBuf};
use std::process::Command;

pub struct LinkRequest<'a> {
    pub objects: Vec<PathBuf>,
    pub output: &'a Path,
    pub linker: Option<&'a Path>,
    pub args: &'a [String],
    pub libs: &'a [(String, String)],
    pub search_paths: &'a [(String, PathBuf)],
    /// `#![no_core]`/`#![no_std]` programs without the standard library's startup code still
    /// link with libc (they call `printf`).
    pub pie: bool,
}

pub fn link(req: &LinkRequest<'_>) -> Result<(), String> {
    let linker = req
        .linker
        .map_or_else(|| PathBuf::from("cc"), Path::to_path_buf);
    let mut cmd = Command::new(&linker);
    cmd.args(&req.objects);
    cmd.arg("-o").arg(req.output);
    if req.pie {
        cmd.arg("-pie");
    } else {
        cmd.arg("-no-pie");
    }
    cmd.arg("-Wl,-z,noexecstack");
    for (kind, p) in req.search_paths {
        if kind == "native" || kind == "all" {
            cmd.arg(format!("-L{}", p.display()));
        }
    }
    for (kind, name) in req.libs {
        match kind.as_str() {
            "static" => cmd.arg(format!("-l:lib{name}.a")),
            _ => cmd.arg(format!("-l{name}")),
        };
    }
    cmd.args(req.args);
    let out = cmd
        .output()
        .map_err(|e| format!("couldn't run the linker `{}`: {e}", linker.display()))?;
    if !out.status.success() {
        return Err(format!(
            "linking with `{}` failed: {}\n{}",
            linker.display(),
            out.status,
            String::from_utf8_lossy(&out.stderr)
        ));
    }
    Ok(())
}
