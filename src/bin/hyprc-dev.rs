//! Developer tools for hyprc: corpus tests and measurements. Not installed for users.
//!
//! `hyprc-dev parse <dir|file>…` lexes and parses every `.rs` file under the given paths on
//! all cores and reports which files fail and how fast it went.

use hyprc_span::DiagCtxt;
use hyprc_syntax::Edition;
use rayon::prelude::*;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() {
    // Parsing recurses; give the workers stacks for the deepest input the parser accepts.
    rayon::ThreadPoolBuilder::new()
        .stack_size(hyprc_syntax::PARSER_STACK_SIZE)
        .build_global()
        .expect("thread pool");
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.first().map(String::as_str) {
        Some("parse") => parse_corpus(&args[1..]),
        _ => {
            eprintln!("usage: hyprc-dev parse [--quiet] [--trace] [--max-errors N] <dir|file>…");
            std::process::exit(2);
        }
    }
}

fn collect_rs(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_file() {
        if path.extension().is_some_and(|e| e == "rs") {
            out.push(path.to_path_buf());
        }
        return;
    }
    let Ok(rd) = std::fs::read_dir(path) else {
        return;
    };
    let mut entries: Vec<_> = rd.flatten().map(|e| e.path()).collect();
    entries.sort();
    for p in entries {
        if p.is_symlink() {
            continue;
        }
        collect_rs(&p, out);
    }
}

/// The edition of the package a file belongs to: the nearest `Cargo.toml`'s `edition`, 2015
/// when it has none (Cargo's default).
fn edition_for(
    file: &Path,
    cache: &std::sync::Mutex<std::collections::HashMap<PathBuf, Edition>>,
) -> Edition {
    let mut dir = file.parent();
    while let Some(d) = dir {
        if let Some(&e) = cache.lock().unwrap().get(d) {
            return e;
        }
        let manifest = d.join("Cargo.toml");
        if let Ok(text) = std::fs::read_to_string(&manifest) {
            let mut edition = None;
            let mut workspace = false;
            for line in text.lines() {
                let line = line.trim();
                if let Some(rest) = line.strip_prefix("edition") {
                    let rest = rest.trim_start();
                    if let Some(v) = rest.strip_prefix('=') {
                        let v = v.trim().trim_matches('"');
                        edition = Edition::parse(v);
                    } else if rest.starts_with(".workspace") {
                        workspace = true;
                    }
                    if edition.is_some() || workspace {
                        break;
                    }
                }
            }
            if let Some(e) = edition {
                cache.lock().unwrap().insert(d.to_path_buf(), e);
                return e;
            }
            if !workspace && text.contains("[package]") {
                cache
                    .lock()
                    .unwrap()
                    .insert(d.to_path_buf(), Edition::E2015);
                return Edition::E2015;
            }
        }
        dir = d.parent();
    }
    Edition::E2021
}

fn line_col(src: &str, off: usize) -> (usize, usize) {
    let off = off.min(src.len());
    let before = &src[..off];
    let line = before.bytes().filter(|&b| b == b'\n').count() + 1;
    let col = before.rfind('\n').map_or(off, |n| off - n - 1) + 1;
    (line, col)
}

fn parse_corpus(args: &[String]) {
    let mut quiet = false;
    let mut trace = false;
    let mut max_errors = 50usize;
    let mut roots = Vec::new();
    let mut it = args.iter();
    while let Some(a) = it.next() {
        match a.as_str() {
            "--quiet" | "-q" => quiet = true,
            "--trace" => trace = true,
            "--max-errors" => max_errors = it.next().and_then(|n| n.parse().ok()).unwrap_or(50),
            _ => roots.push(PathBuf::from(a)),
        }
    }
    let mut files = Vec::new();
    for r in &roots {
        collect_rs(r, &mut files);
    }
    let cache = std::sync::Mutex::new(std::collections::HashMap::new());
    let bytes = AtomicU64::new(0);
    let lex_ns = AtomicU64::new(0);
    let parse_ns = AtomicU64::new(0);
    let tokens = AtomicU64::new(0);
    let start = Instant::now();
    let mut failures: Vec<(PathBuf, String)> = files
        .par_iter()
        .filter_map(|path| {
            if trace {
                eprintln!("start {}", path.display());
            }
            let src = std::fs::read_to_string(path).ok()?;
            let src = src.strip_prefix('\u{feff}').unwrap_or(&src);
            let edition = edition_for(path, &cache);
            bytes.fetch_add(src.len() as u64, Ordering::Relaxed);
            let dcx = DiagCtxt::buffered();
            let t0 = Instant::now();
            let toks = hyprc_syntax::tokenize(src, 1, &dcx);
            let t1 = Instant::now();
            let krate = hyprc_syntax::parse_file(&toks, edition, &dcx);
            let t2 = Instant::now();
            std::hint::black_box(&krate);
            lex_ns.fetch_add((t1 - t0).as_nanos() as u64, Ordering::Relaxed);
            parse_ns.fetch_add((t2 - t1).as_nanos() as u64, Ordering::Relaxed);
            tokens.fetch_add(toks.len() as u64, Ordering::Relaxed);
            let diags = dcx.take();
            let first = diags.first()?;
            let off = first
                .primary_span()
                .map_or(0, |s| s.lo.saturating_sub(1) as usize);
            let (line, col) = line_col(src, off);
            Some((
                path.clone(),
                format!(
                    "{}:{line}:{col}: {} ({} errors, edition {})",
                    path.display(),
                    first.message,
                    diags.len(),
                    edition.as_str()
                ),
            ))
        })
        .collect();
    let wall = start.elapsed();
    failures.sort();
    if !quiet {
        for (_, msg) in failures.iter().take(max_errors) {
            println!("{msg}");
        }
    }
    let mb = bytes.load(Ordering::Relaxed) as f64 / 1e6;
    let lex_s = lex_ns.load(Ordering::Relaxed) as f64 / 1e9;
    let parse_s = parse_ns.load(Ordering::Relaxed) as f64 / 1e9;
    println!(
        "{} files, {:.1} MB, {} tokens: {} failed ({:.3}%)",
        files.len(),
        mb,
        tokens.load(Ordering::Relaxed),
        failures.len(),
        100.0 * failures.len() as f64 / files.len().max(1) as f64
    );
    println!(
        "wall {:.2}s on {} threads; per core: lex {:.0} MB/s, parse {:.0} MB/s",
        wall.as_secs_f64(),
        rayon::current_num_threads(),
        mb / lex_s.max(1e-9),
        mb / parse_s.max(1e-9),
    );
}
