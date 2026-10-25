//! The compiler session: options from the command line, the target, the active `cfg`s, and
//! the diagnostics context. One per compiler invocation, shared by all threads.

use crate::target::Target;
use crate::{DiagCtxt, Edition, FxHashSet, Symbol};
use std::path::PathBuf;

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum CrateType {
    Bin,
    Lib,
    Rlib,
    Dylib,
    Cdylib,
    Staticlib,
    ProcMacro,
}

impl CrateType {
    pub fn parse(s: &str) -> Option<CrateType> {
        Some(match s {
            "bin" => CrateType::Bin,
            "lib" => CrateType::Lib,
            "rlib" => CrateType::Rlib,
            "dylib" => CrateType::Dylib,
            "cdylib" => CrateType::Cdylib,
            "staticlib" => CrateType::Staticlib,
            "proc-macro" => CrateType::ProcMacro,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum EmitKind {
    Link,
    Metadata,
    Obj,
    Asm,
    DepInfo,
    LlvmIr,
    LlvmBc,
    Mir,
}

impl EmitKind {
    pub fn parse(s: &str) -> Option<EmitKind> {
        Some(match s {
            "link" => EmitKind::Link,
            "metadata" => EmitKind::Metadata,
            "obj" => EmitKind::Obj,
            "asm" => EmitKind::Asm,
            "dep-info" => EmitKind::DepInfo,
            "llvm-ir" => EmitKind::LlvmIr,
            "llvm-bc" => EmitKind::LlvmBc,
            "mir" => EmitKind::Mir,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ErrorFormat {
    Human,
    Json,
    Short,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum PanicStrategy {
    Unwind,
    Abort,
}

#[derive(Clone, Debug)]
pub struct ExternEntry {
    pub name: String,
    /// `None` for `--extern name` without a path (found in the sysroot or search paths).
    pub path: Option<PathBuf>,
}

/// Everything the command line can say, in rustc's terms.
#[derive(Clone, Debug)]
pub struct Options {
    pub input: Option<PathBuf>,
    pub crate_name: Option<String>,
    pub crate_types: Vec<CrateType>,
    pub edition: Edition,
    /// `--cfg name` and `--cfg name="value"`.
    pub cfgs: Vec<(String, Option<String>)>,
    pub externs: Vec<ExternEntry>,
    /// `-L [kind=]path`
    pub search_paths: Vec<(String, PathBuf)>,
    pub out_dir: Option<PathBuf>,
    pub output: Option<PathBuf>,
    pub emit: Vec<(EmitKind, Option<PathBuf>)>,
    pub opt_level: String,
    pub debuginfo: u32,
    pub debug_assertions: bool,
    pub overflow_checks: bool,
    pub panic: PanicStrategy,
    pub target: Target,
    pub linker: Option<PathBuf>,
    pub link_args: Vec<String>,
    pub codegen_units: Option<usize>,
    pub error_format: ErrorFormat,
    pub json_artifacts: bool,
    pub color: bool,
    pub cap_lints: Option<String>,
    pub sysroot: Option<PathBuf>,
    pub extra_filename: String,
    pub metadata: Vec<String>,
    /// `-l [kind=]name`
    pub link_libs: Vec<(String, String)>,
    pub test: bool,
    pub verbose: bool,
    /// `-Z` / `-C` options hyprc doesn't use, kept for reporting.
    pub ignored: Vec<String>,
    pub threads: usize,
    /// `--hyprc-time`: print how long each stage took.
    pub time_passes: bool,
}

impl Default for Options {
    fn default() -> Options {
        Options {
            input: None,
            crate_name: None,
            crate_types: Vec::new(),
            edition: Edition::E2015,
            cfgs: Vec::new(),
            externs: Vec::new(),
            search_paths: Vec::new(),
            out_dir: None,
            output: None,
            emit: Vec::new(),
            opt_level: "0".to_string(),
            debuginfo: 0,
            debug_assertions: true,
            overflow_checks: true,
            panic: PanicStrategy::Unwind,
            target: Target::host(),
            linker: None,
            link_args: Vec::new(),
            codegen_units: None,
            error_format: ErrorFormat::Human,
            json_artifacts: false,
            color: false,
            cap_lints: None,
            sysroot: None,
            extra_filename: String::new(),
            metadata: Vec::new(),
            link_libs: Vec::new(),
            test: false,
            verbose: false,
            ignored: Vec::new(),
            threads: 0,
            time_passes: false,
        }
    }
}

pub struct Session {
    pub opts: Options,
    pub dcx: DiagCtxt,
    /// Active `cfg`s: names alone (`unix`) and name/value pairs (`target_os = "linux"`).
    pub cfg: FxHashSet<(Symbol, Option<Symbol>)>,
}

impl Session {
    pub fn new(opts: Options) -> Session {
        let dcx = DiagCtxt::new(opts.color);
        let cfg = default_cfg(&opts);
        Session { opts, dcx, cfg }
    }

    pub fn edition(&self) -> Edition {
        self.opts.edition
    }

    pub fn target(&self) -> &Target {
        &self.opts.target
    }

    pub fn cfg_set(&self, name: Symbol, value: Option<Symbol>) -> bool {
        self.cfg.contains(&(name, value))
    }
}

/// The `cfg`s rustc sets for a target and options, plus `--cfg`s.
fn default_cfg(opts: &Options) -> FxHashSet<(Symbol, Option<Symbol>)> {
    let mut set = FxHashSet::default();
    let mut add = |name: &str, value: Option<&str>| {
        set.insert((Symbol::intern(name), value.map(Symbol::intern)));
    };
    let t = &opts.target;
    add("target_arch", Some(&t.arch_name));
    add("target_os", Some(&t.os));
    add("target_env", Some(&t.env));
    add("target_vendor", Some(&t.vendor));
    add("target_abi", Some(&t.abi));
    add(
        "target_endian",
        Some(if t.endian == crate::target::Endian::Little {
            "little"
        } else {
            "big"
        }),
    );
    add("target_pointer_width", Some(&t.pointer_width.to_string()));
    for family in &t.families {
        add("target_family", Some(family));
        add(family, None);
    }
    for f in &t.features {
        add("target_feature", Some(f));
    }
    for w in &t.atomic_widths {
        add("target_has_atomic", Some(w));
        add("target_has_atomic_load_store", Some(w));
        add("target_has_atomic_primitive_alignment", Some(w));
    }
    if !t.atomic_widths.is_empty() {
        add("target_has_atomic", None);
        add("target_has_atomic_load_store", None);
    }
    add("target_thread_local", None);
    add(
        "target_object_format",
        Some(if t.os == "macos" || t.os == "ios" {
            "mach-o"
        } else if t.os == "windows" {
            "coff"
        } else {
            "elf"
        }),
    );
    // Where `f16`/`f128` arithmetic works without surprises (as rustc decides per target).
    match t.arch_name.as_str() {
        "x86_64" => {
            add("target_has_reliable_f16", None);
            add("target_has_reliable_f16_math", None);
            add("target_has_reliable_f128", None);
        }
        "aarch64" => {
            add("target_has_reliable_f16", None);
            add("target_has_reliable_f16_math", None);
            add("target_has_reliable_f128", None);
            add("target_has_reliable_f128_math", None);
        }
        _ => {}
    }
    add(
        "panic",
        Some(if opts.panic == PanicStrategy::Unwind {
            "unwind"
        } else {
            "abort"
        }),
    );
    add("relocation_model", Some("pic"));
    add("fmt_debug", Some("full"));
    if opts.debug_assertions {
        add("debug_assertions", None);
        add("ub_checks", None);
    }
    if opts.overflow_checks {
        add("overflow_checks", None);
    }
    if opts.test {
        add("test", None);
    }
    for (name, value) in &opts.cfgs {
        add(name, value.as_deref());
    }
    set
}
