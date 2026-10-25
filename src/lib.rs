//! `hyprc`: the fast Rust compiler for the Igel build system.

pub mod args;

use args::{Command, DevFlags};
use hyprc_span::session::{Options, Session};
use std::ffi::OsString;
use std::time::Instant;

pub const VERSION: &str = env!("CARGO_PKG_VERSION");

/// Run hyprc on a full command line (like `rustc`) and return the exit code.
pub fn main_with_args<I, T>(args: I) -> i32
where
    I: IntoIterator<Item = T>,
    T: Into<OsString>,
{
    let mut raw_args: Vec<String> = args
        .into_iter()
        .map(|a| a.into().to_string_lossy().into_owned())
        .collect();
    if !raw_args.is_empty() {
        raw_args.remove(0);
    }

    if std::env::var_os("HYPRC_DEBUG_LOG").is_some() {
        eprintln!("HYPRC_DEBUG: {:?}", raw_args);
    }

    match args::parse(raw_args) {
        Ok(Command::Help) => {
            println!("{}", HELP.trim_start());
            0
        }
        Ok(Command::Version { verbose }) => {
            println!("rustc 1.85.0 (hyprc {VERSION})");
            if verbose {
                println!(
                    "binary: rustc\ncommit-hash: unknown\ncommit-date: unknown\nhost: {}\nrelease: 1.85.0",
                    hyprc_span::target::Target::host().triple
                );
            }
            0
        }
        Ok(Command::Print(what, opts)) => print_info(&what, &opts),
        Ok(Command::Compile(opts, dev)) => {
            let pool = rayon::ThreadPoolBuilder::new()
                .stack_size(hyprc_syntax::PARSER_STACK_SIZE)
                .num_threads(opts.threads)
                .build()
                .expect("thread pool");
            pool.install(|| compile(*opts, dev))
        }
        Err(msg) => {
            eprintln!("error: {msg}");
            1
        }
    }
}

pub fn print_info(what: &[String], opts: &Options) -> i32 {
    for w in what {
        match w.as_str() {
            "crate-name" => {
                let name = opts.crate_name.clone().or_else(|| {
                    opts.input
                        .as_ref()
                        .and_then(|p| p.file_stem())
                        .map(|s| s.to_string_lossy().replace('-', "_"))
                });
                println!("{}", name.unwrap_or_default());
            }
            "cfg" => {
                let sess = Session::new(opts.clone());
                let mut lines: Vec<String> = sess
                    .cfg
                    .iter()
                    .map(|(n, v)| match v {
                        Some(v) => format!("{n}=\"{v}\""),
                        None => n.to_string(),
                    })
                    .collect();
                lines.sort();
                for l in lines {
                    println!("{l}");
                }
            }
            "sysroot" => {
                let sys = opts
                    .sysroot
                    .as_ref()
                    .map(|p| p.display().to_string())
                    .or_else(|| {
                        std::process::Command::new("rustc")
                            .args(["--print", "sysroot"])
                            .output()
                            .ok()
                            .and_then(|o| String::from_utf8(o.stdout).ok())
                            .map(|s| s.trim().to_string())
                    })
                    .unwrap_or_default();
                println!("{sys}");
            }
            other => {
                eprintln!("error: `--print {other}` isn't supported by hyprc");
                return 1;
            }
        }
    }
    0
}

struct Timer {
    on: bool,
    last: Instant,
}

impl Timer {
    fn stage(&mut self, name: &str) {
        if self.on {
            let now = Instant::now();
            eprintln!(
                "time: {:>8.2}ms  {name}",
                (now - self.last).as_secs_f64() * 1000.0
            );
            self.last = now;
        }
    }
}

pub fn compile(opts: Options, dev: DevFlags) -> i32 {
    let Some(input) = opts.input.clone() else {
        eprintln!("error: no input filename given");
        return 1;
    };
    let crate_name = opts.crate_name.clone().unwrap_or_else(|| {
        input
            .file_stem()
            .map(|s| s.to_string_lossy().replace('-', "_"))
            .unwrap_or_else(|| "main".to_string())
    });
    let mut timer = Timer {
        on: opts.time_passes,
        last: Instant::now(),
    };
    let sess = Session::new(opts);
    let resolver = hyprc_resolve::resolve_crate(&sess, &crate_name, &input);
    timer.stage("parse, expand, resolve");
    if dev.dump.iter().any(|d| d == "defs") {
        dump_defs(&resolver);
    }
    if sess.dcx.has_errors() {
        return abort(&sess);
    }
    let krate = hyprc_hir::lower_crate(&resolver);
    timer.stage("lower to HIR");
    if dev.dump.iter().any(|d| d == "hir") {
        dump_hir(&krate);
    }
    if sess.dcx.has_errors() {
        return abort(&sess);
    }
    let tcx = hyprc_ty::TyCtxt::new(&krate, &sess.dcx, sess.target().pointer_width);
    tcx.typeck_all();
    timer.stage("type check");
    if dev.dump.iter().any(|d| d == "types") {
        dump_types(&tcx);
    }
    if sess.dcx.has_errors() {
        return abort(&sess);
    }
    let wants_obj = sess
        .opts
        .emit
        .iter()
        .any(|(k, _)| *k == hyprc_span::session::EmitKind::Obj);
    let wants_link = sess
        .opts
        .emit
        .iter()
        .any(|(k, _)| *k == hyprc_span::session::EmitKind::Link);
    let wants_metadata = sess
        .opts
        .emit
        .iter()
        .any(|(k, _)| *k == hyprc_span::session::EmitKind::Metadata);
    let wants_dep_info = sess
        .opts
        .emit
        .iter()
        .any(|(k, _)| *k == hyprc_span::session::EmitKind::DepInfo);
    let is_bin = sess.opts.crate_types.iter().any(|t| {
        matches!(
            t,
            hyprc_span::session::CrateType::Bin | hyprc_span::session::CrateType::Cdylib
        )
    });

    // Metadata and dependency discovery need parsing and type checking, but no MIR or machine
    // code. Besides avoiding unsupported codegen in unreachable generic bodies, this makes
    // `igl check --compiler hyprc` and dependency scans substantially cheaper.
    let object = if wants_obj || (wants_link && is_bin) {
        let mcx = hyprc_mir::mono::MonoCtxt::new(&tcx, sess.opts.overflow_checks);
        let roots = hyprc_mir::mono::roots(&tcx, &mcx);
        let (instances, statics) = mcx.collect(roots);
        timer.stage("build MIR, collect instances");
        if dev.dump.iter().any(|d| d == "mir") {
            for inst in &instances {
                println!("// {inst:?}");
                if let Some(body) = mcx.instance_mir(*inst) {
                    println!("{}", hyprc_mir::print::body_to_string(&body));
                }
            }
            println!("// statics: {statics:?}");
        }
        if sess.dcx.has_errors() {
            return abort(&sess);
        }
        let cx = hyprc_codegen::CodegenCx::new(&tcx, &mcx);
        let c_main = if !tcx.hir.no_main {
            tcx.hir
                .entry
                .map(|d| hyprc_mir::mono::Instance::item(d, hyprc_ty::Args::EMPTY))
        } else {
            None
        };
        let out = hyprc_codegen::codegen(&cx, &instances, &statics, c_main);
        timer.stage("code generation");
        for e in &out.errors {
            sess.dcx.emit(hyprc_span::Diag::error(e.clone()));
        }
        if sess.dcx.has_errors() {
            return abort(&sess);
        }
        Some(out.object)
    } else {
        None
    };

    // Outputs: rustc's naming conventions and emission.
    let out_dir = sess
        .opts
        .out_dir
        .clone()
        .unwrap_or_else(|| std::path::PathBuf::from("."));
    let _ = std::fs::create_dir_all(&out_dir);
    let exe = sess
        .opts
        .output
        .clone()
        .unwrap_or_else(|| out_dir.join(format!("{crate_name}{}", sess.opts.extra_filename)));
    let obj_path = if wants_obj && !wants_link {
        exe.clone()
    } else {
        exe.with_extension("hyprc.o")
    };
    if let Some(ref object) = object
        && let Err(e) = std::fs::write(&obj_path, object)
    {
        eprintln!("error: couldn't write `{}`: {e}", obj_path.display());
        return 1;
    }

    // Emit dep-info if requested
    let dep_info_path = out_dir.join(format!("{crate_name}{}.d", sess.opts.extra_filename));
    if wants_dep_info {
        let content = format!(
            "{}: {}\n{}:\n",
            exe.display(),
            input.display(),
            input.display()
        );
        let _ = std::fs::write(&dep_info_path, content);
        if sess.opts.json_artifacts {
            emit_json_artifact(&dep_info_path, "dep-info");
        }
    }

    // Write metadata (.rmeta) if requested or for library crates
    let rmeta_path = out_dir.join(format!("lib{crate_name}{}.rmeta", sess.opts.extra_filename));
    if wants_metadata || (!is_bin && wants_link) {
        // Record crate metadata header pointing to source root and active cfgs
        let mut meta_content = format!(
            "HYPRC_META\nsource={}\nedition={}\n",
            input.display(),
            sess.opts.edition.as_str()
        );
        for (name, val) in &sess.cfg {
            if let Some(v) = val {
                meta_content.push_str(&format!("cfg={name}=\"{v}\"\n"));
            } else {
                meta_content.push_str(&format!("cfg={name}\n"));
            }
        }
        for dependency in &sess.opts.externs {
            if let Some(path) = &dependency.path {
                meta_content.push_str(&format!("extern={}={}\n", dependency.name, path.display()));
            }
        }
        let _ = std::fs::write(&rmeta_path, meta_content);
        if sess.opts.json_artifacts {
            emit_json_artifact(&rmeta_path, "metadata");
        }
    }

    if wants_link && is_bin {
        let req = hyprc_codegen::link::LinkRequest {
            objects: vec![obj_path.clone()],
            output: &exe,
            linker: sess.opts.linker.as_deref(),
            args: &sess.opts.link_args,
            libs: &sess.opts.link_libs,
            search_paths: &sess.opts.search_paths,
            pie: true,
        };
        let r = hyprc_codegen::link::link(&req);
        if !wants_obj {
            let _ = std::fs::remove_file(&obj_path);
        }
        if let Err(e) = r {
            eprintln!("error: {e}");
            return 1;
        }
        if sess.opts.json_artifacts {
            emit_json_artifact(&exe, "link");
        }
        timer.stage("link");
    } else if !is_bin && !wants_obj {
        let lib_path = sess.opts.output.clone().unwrap_or_else(|| {
            out_dir.join(format!("lib{crate_name}{}.rlib", sess.opts.extra_filename))
        });
        // Hyprc monomorphizes dependency bodies into the final executable from source-backed
        // metadata, so library objects are unused. Keep an rlib-shaped metadata artifact for
        // Cargo-compatible build graphs without spending time generating dead machine code.
        if object.is_some() {
            let _ = std::fs::copy(&obj_path, &lib_path);
            let _ = std::fs::remove_file(&obj_path);
        } else {
            let _ = std::fs::copy(&rmeta_path, &lib_path);
        }
        if sess.opts.json_artifacts {
            emit_json_artifact(&lib_path, "link");
        }
    }
    0
}

fn emit_json_artifact(path: &std::path::Path, emit: &str) {
    eprintln!(
        "{{\"$message_type\":\"artifact\",\"artifact\":\"{}\",\"emit\":\"{emit}\"}}",
        path.display()
    );
}

fn dump_types(tcx: &hyprc_ty::TyCtxt<'_>) {
    for (i, body) in tcx.hir.bodies.iter().enumerate() {
        let r = tcx.typeck(hyprc_hir::BodyId(i as u32));
        println!("body{i} of {}:", tcx.def_path(body.owner));
        for (j, l) in body.locals.iter().enumerate() {
            println!("  {}: {}", l.name, r.local_tys[j]);
        }
        for (j, t) in r.expr_tys.iter().enumerate() {
            let adj = r
                .adjustments
                .get(&hyprc_hir::ExprId(j as u32))
                .map(|a| format!(" adj {a:?}"))
                .unwrap_or_default();
            println!("  e{j}: {t}{adj}");
        }
    }
}

fn abort(sess: &Session) -> i32 {
    let n = sess.dcx.error_count();
    eprintln!(
        "error: aborting crate {:?} due to {}",
        sess.opts.crate_name.as_deref().unwrap_or("<unknown>"),
        if n == 1 {
            "1 previous error".to_string()
        } else {
            format!("{n} previous errors")
        }
    );
    1
}

fn dump_hir(krate: &hyprc_hir::Crate) {
    for item in krate.items.iter().flatten() {
        println!(
            "{:?} {}: {:#?}",
            item.def,
            krate.def_path(item.def),
            item.kind
        );
    }
    for (i, body) in krate.bodies.iter().enumerate() {
        println!(
            "body{i} of {} ({:?}): value {:?}",
            krate.def_path(body.owner),
            body.kind,
            body.value
        );
        for (j, e) in body.exprs.iter().enumerate() {
            println!("  e{j}: {:?}", e.kind);
        }
        for (j, p) in body.pats.iter().enumerate() {
            println!("  p{j}: {:?}", p.kind);
        }
        for (j, l) in body.locals.iter().enumerate() {
            println!("  l{j}: {} mut={}", l.name, l.mutable);
        }
    }
}

fn dump_defs(r: &hyprc_resolve::Resolver<'_>) {
    for (i, d) in r.defs.iter().enumerate() {
        let id = hyprc_resolve::DefId(i as u32);
        println!(
            "{id:?} {:?} {} parent={:?} vis={:?}",
            d.kind,
            r.def_path_str(id),
            d.parent,
            d.vis
        );
        if let Some(m) = r.modules.get(&id) {
            let mut names: Vec<_> = m.resolutions.iter().collect();
            names.sort_by_key(|((n, ns), _)| (n.as_str(), *ns));
            for ((name, ns), b) in names {
                println!("    {name} ({ns:?}) => {:?} [{:?}]", b.res, b.kind);
            }
        }
    }
    println!("lang items: {}", r.lang_items.len());
}

pub const HELP: &str = "
Usage: hyprc [OPTIONS] INPUT

hyprc takes rustc's options. The ones that change what it does:

    --crate-name NAME      Name of the crate
    --crate-type TYPE      bin, lib, rlib, staticlib, cdylib
    --edition 2015|2018|2021|2024
    --emit KIND[=PATH]     link, obj, metadata, dep-info
    -o FILE                Write the output to FILE
    --out-dir DIR          Write outputs to DIR
    --cfg SPEC             Set a cfg: `name` or `name=\"value\"`
    --extern NAME=PATH     A dependency
    -L [KIND=]PATH         A library search path
    -C opt-level=N, -C linker=PATH, -C link-arg=ARG, -C panic=abort|unwind, ...
    --target TRIPLE
    --error-format human|json

hyprc's own:
    --hyprc-time           Print how long each stage takes
    --hyprc-dump=defs      Print the definitions after name resolution
";
