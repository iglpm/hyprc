//! rustc's command line, as hyprc understands it.
//!
//! Igel (and Cargo) drive rustc with these flags; hyprc accepts the same, so it can stand in
//! for rustc without the build system knowing. Flags that only affect what rustc does
//! internally (most `-Z`, many `-C`) are accepted and ignored.

use hyprc_span::Edition;
use hyprc_span::session::{CrateType, EmitKind, ErrorFormat, ExternEntry, Options, PanicStrategy};
use hyprc_span::target::Target;
use std::path::PathBuf;

pub enum Command {
    Compile(Box<Options>, DevFlags),
    Version { verbose: bool },
    Print(Vec<String>, Box<Options>),
    Help,
}

/// hyprc's own flags, for looking at its stages.
#[derive(Default, Clone)]
pub struct DevFlags {
    /// `--hyprc-dump=defs`: print definitions and module scopes after resolution.
    pub dump: Vec<String>,
}

fn split_kv(s: &str) -> (&str, Option<&str>) {
    match s.split_once('=') {
        Some((k, v)) => (k, Some(v)),
        None => (s, None),
    }
}

pub fn parse(args: Vec<String>) -> Result<Command, String> {
    let mut o = Options::default();
    let mut dev = DevFlags::default();
    let mut prints = Vec::new();
    let mut version = false;
    let mut verbose = false;
    let mut i = 0;
    // `--flag value` or `--flag=value`.
    let take = |i: &mut usize, flag: &str, args: &[String]| -> Result<String, String> {
        let a = &args[*i];
        if let Some(v) = a.strip_prefix(flag).and_then(|r| r.strip_prefix('=')) {
            return Ok(v.to_string());
        }
        // Short flags written joined: `-Copt-level=0`, `-Lnative=…`.
        if flag.len() == 2 && a.len() > 2 && a.starts_with(flag) {
            return Ok(a[2..].to_string());
        }
        *i += 1;
        args.get(*i)
            .cloned()
            .ok_or_else(|| format!("argument for `{flag}` missing"))
    };
    let matches = |a: &str, flag: &str| {
        a == flag
            || a.starts_with(&format!("{flag}="))
            || (flag.len() == 2 && a.starts_with(flag) && a.len() > 2)
    };
    while i < args.len() {
        let a = args[i].clone();
        match a.as_str() {
            "-h" | "--help" => return Ok(Command::Help),
            "-V" | "--version" => version = true,
            "-v" | "--verbose" => {
                verbose = true;
                o.verbose = true;
            }
            "-vV" | "-Vv" => {
                version = true;
                verbose = true;
            }
            "-O" => o.opt_level = "2".to_string(),
            "-g" => o.debuginfo = 2,
            "--test" => o.test = true,
            _ if matches(&a, "--crate-name") => {
                o.crate_name = Some(take(&mut i, "--crate-name", &args)?)
            }
            _ if matches(&a, "--crate-type") => {
                for t in take(&mut i, "--crate-type", &args)?.split(',') {
                    o.crate_types.push(
                        CrateType::parse(t).ok_or_else(|| format!("unknown crate type: `{t}`"))?,
                    );
                }
            }
            _ if matches(&a, "--edition") => {
                let e = take(&mut i, "--edition", &args)?;
                o.edition = Edition::parse(&e).ok_or_else(|| format!("argument for `--edition` must be one of: 2015|2018|2021|2024. (instead was `{e}`)"))?;
            }
            _ if matches(&a, "--emit") => {
                for part in take(&mut i, "--emit", &args)?.split(',') {
                    let (k, path) = split_kv(part);
                    let kind = EmitKind::parse(k)
                        .ok_or_else(|| format!("unknown emission type: `{k}`"))?;
                    o.emit.push((kind, path.map(PathBuf::from)));
                }
            }
            _ if matches(&a, "--out-dir") => {
                o.out_dir = Some(PathBuf::from(take(&mut i, "--out-dir", &args)?))
            }
            _ if matches(&a, "-o") => o.output = Some(PathBuf::from(take(&mut i, "-o", &args)?)),
            _ if matches(&a, "--cfg") => {
                let spec = take(&mut i, "--cfg", &args)?;
                let (name, value) = split_kv(&spec);
                o.cfgs.push((
                    name.to_string(),
                    value.map(|v| v.trim_matches('"').to_string()),
                ));
            }
            _ if matches(&a, "--check-cfg") => {
                let _ = take(&mut i, "--check-cfg", &args)?;
            }
            _ if matches(&a, "-L") => {
                let spec = take(&mut i, "-L", &args)?;
                let (kind, path) = match spec.split_once('=') {
                    Some((k, p))
                        if ["dependency", "crate", "native", "framework", "all"].contains(&k) =>
                    {
                        (k.to_string(), p.to_string())
                    }
                    _ => ("all".to_string(), spec.clone()),
                };
                o.search_paths.push((kind, PathBuf::from(path)));
            }
            _ if matches(&a, "-l") => {
                let spec = take(&mut i, "-l", &args)?;
                let (kind, name) = match spec.split_once('=') {
                    Some((k, n)) => (k.to_string(), n.to_string()),
                    None => ("dylib".to_string(), spec.clone()),
                };
                o.link_libs.push((kind, name));
            }
            _ if matches(&a, "--extern") => {
                let spec = take(&mut i, "--extern", &args)?;
                // `--extern [opts:]name[=path]`
                let spec = spec
                    .rsplit_once(':')
                    .filter(|(opts, _)| !opts.contains('/') && !opts.contains('='))
                    .map_or(spec.as_str(), |(_, s)| s)
                    .to_string();
                let (name, path) = split_kv(&spec);
                o.externs.push(ExternEntry {
                    name: name.to_string(),
                    path: path.map(PathBuf::from),
                });
            }
            _ if matches(&a, "--target") => {
                let t = take(&mut i, "--target", &args)?;
                o.target = Target::from_triple(&t)
                    .ok_or_else(|| format!("unknown target triple `{t}`"))?;
            }
            _ if matches(&a, "--error-format") => {
                o.error_format = match take(&mut i, "--error-format", &args)?.as_str() {
                    "json" => ErrorFormat::Json,
                    "short" => ErrorFormat::Short,
                    _ => ErrorFormat::Human,
                };
            }
            _ if matches(&a, "--json") => {
                let v = take(&mut i, "--json", &args)?;
                o.json_artifacts = v.split(',').any(|p| p == "artifacts");
            }
            _ if matches(&a, "--color") => {
                o.color = match take(&mut i, "--color", &args)?.as_str() {
                    "always" => true,
                    "never" => false,
                    _ => std::io::IsTerminal::is_terminal(&std::io::stderr()),
                };
            }
            _ if matches(&a, "--cap-lints") => {
                o.cap_lints = Some(take(&mut i, "--cap-lints", &args)?)
            }
            _ if matches(&a, "--sysroot") => {
                o.sysroot = Some(PathBuf::from(take(&mut i, "--sysroot", &args)?))
            }
            _ if matches(&a, "--print") => prints.push(take(&mut i, "--print", &args)?),
            _ if matches(&a, "--remap-path-prefix")
                || matches(&a, "--diagnostic-width")
                || matches(&a, "--explain") =>
            {
                let flag = a.split('=').next().unwrap().to_string();
                let _ = take(&mut i, &flag, &args)?;
            }
            _ if matches(&a, "-A")
                || matches(&a, "-W")
                || matches(&a, "-D")
                || matches(&a, "-F")
                || matches(&a, "--force-warn") =>
            {
                let flag = if a.starts_with("--force-warn") {
                    "--force-warn".to_string()
                } else {
                    a[..2].to_string()
                };
                let _ = take(&mut i, &flag, &args)?;
            }
            _ if matches(&a, "-C") || matches(&a, "--codegen") => {
                let flag = if a.starts_with("--codegen") {
                    "--codegen"
                } else {
                    "-C"
                };
                let spec = take(&mut i, flag, &args)?;
                let (k, v) = split_kv(&spec);
                let v = v.unwrap_or("");
                match k {
                    "opt-level" => o.opt_level = v.to_string(),
                    "debuginfo" => {
                        o.debuginfo = match v {
                            "0" | "none" | "" => 0,
                            "1" | "limited" | "line-tables-only" | "line-directives-only" => 1,
                            _ => 2,
                        }
                    }
                    "codegen-units" => o.codegen_units = v.parse().ok(),
                    "linker" => o.linker = Some(PathBuf::from(v)),
                    "link-arg" => o.link_args.push(v.to_string()),
                    "link-args" => o.link_args.extend(v.split_whitespace().map(str::to_string)),
                    "panic" => {
                        o.panic = if v == "abort" {
                            PanicStrategy::Abort
                        } else {
                            PanicStrategy::Unwind
                        }
                    }
                    "debug-assertions" => {
                        o.debug_assertions = matches!(v, "" | "y" | "yes" | "on" | "true")
                    }
                    "overflow-checks" => {
                        o.overflow_checks = matches!(v, "" | "y" | "yes" | "on" | "true")
                    }
                    "metadata" => o.metadata.push(v.to_string()),
                    "extra-filename" => o.extra_filename = v.to_string(),
                    _ => o.ignored.push(format!("-C {spec}")),
                }
            }
            _ if matches(&a, "-Z") => {
                let spec = take(&mut i, "-Z", &args)?;
                if let Some(n) = spec.strip_prefix("threads=") {
                    o.threads = n.parse().unwrap_or(0);
                } else {
                    o.ignored.push(format!("-Z {spec}"));
                }
            }
            "--hyprc-time" => o.time_passes = true,
            _ if a.starts_with("--hyprc-dump=") => dev
                .dump
                .extend(a["--hyprc-dump=".len()..].split(',').map(str::to_string)),
            "-" => return Err("reading source from stdin isn't supported".to_string()),
            _ if a.starts_with('-') => return Err(format!("unknown flag: `{a}`")),
            _ => {
                if o.input.is_some() {
                    return Err(format!(
                        "multiple input filenames provided (first two filenames are `{}` and `{a}`)",
                        o.input.as_ref().unwrap().display()
                    ));
                }
                o.input = Some(PathBuf::from(a));
            }
        }
        i += 1;
    }
    // rustc's defaults: debug builds keep debug assertions and overflow checks.
    if o.opt_level != "0" && !args.iter().any(|a| a.contains("debug-assertions")) {
        o.debug_assertions = false;
    }
    if o.opt_level != "0" && !args.iter().any(|a| a.contains("overflow-checks")) {
        o.overflow_checks = o.debug_assertions;
    }
    if version {
        return Ok(Command::Version { verbose });
    }
    if !prints.is_empty() {
        return Ok(Command::Print(prints, Box::new(o)));
    }
    if o.crate_types.is_empty() {
        o.crate_types.push(CrateType::Bin);
    }
    if o.emit.is_empty() {
        o.emit.push((EmitKind::Link, None));
    }
    Ok(Command::Compile(Box::new(o), dev))
}
