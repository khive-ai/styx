use std::fs;
use std::path::PathBuf;

use anyhow::{Context, Result};
use clap::Parser;

use styx::emit::lean_to_rust::emit_rust_skeletons;
use styx::lean_parser::parse_lean_source;

/// styx: translate Rust (via StyxIR) or Rust source directly to Lean 4.
#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    /// Input file (StyxIR .styx JSON from styx-rustc).
    #[arg(value_name = "INPUT")]
    input: Option<PathBuf>,

    /// Output directory
    #[arg(short, long, value_name = "DIR", default_value = "out")]
    output_dir: PathBuf,

    /// Lean namespace to emit into (e.g. MyCrate)
    #[arg(short, long, value_name = "NS")]
    namespace: Option<String>,

    /// Emit all loops using `partial_fixpoint` (Aeneas-compat)
    #[arg(long)]
    aeneas_compat: bool,

    /// Rust source directory for direct type parsing (BTreeMap, Arc, etc.)
    #[arg(long, value_name = "DIR")]
    rust_src: Option<PathBuf>,

    /// Direct Rust→Lean mode: parse Rust source files directly (no StyxIR).
    /// Takes a directory of .rs files.
    #[arg(long, value_name = "DIR")]
    direct: Option<PathBuf>,

    /// StyxIR mode: read a .styx JSON file (from styx-rustc) instead of
    /// positional input. This is the primary translation path.
    #[arg(long, value_name = "FILE")]
    styx_ir: Option<PathBuf>,

    /// Reachability anchor: only extract items reachable from this function.
    #[arg(long, value_name = "PATH")]
    start_from: Option<String>,

    /// Emit `#check <name>` after each generated `def` and `structure`.
    #[arg(long)]
    emit_checks: bool,

    /// Emit a `Bridge_Template.lean` with correspondence proof outlines.
    #[arg(long)]
    bridge_template: bool,

    /// Read an existing BinaryBridge Lean file to extract actual spec type paths.
    #[arg(long, value_name = "FILE")]
    spec_map: Option<PathBuf>,

    /// Emit compatibility `abbrev` aliases at the end of `Funs.lean`.
    /// Format: `alias_name=canonical_name`.
    #[arg(long = "compat-alias", value_name = "ALIAS=CANONICAL")]
    compat_aliases: Vec<String>,

    /// Skip stdlib definitions in FunsExternal (Try, FromResidual, Option, Result).
    #[arg(long)]
    no_stdlib: bool,

    /// Lean→Rust skeleton mode: read a Lean source file and emit Rust struct/enum skeletons.
    #[arg(long, value_name = "FILE")]
    lean_to_rust: Option<PathBuf>,

    /// Lean module path for provenance comments in `--lean-to-rust` output.
    #[arg(long, value_name = "MODULE_PATH", default_value = "")]
    lean_module: String,
}

fn main() -> Result<()> {
    let args = Args::parse();

    if let Some(ref lean_path) = args.lean_to_rust {
        return run_lean_to_rust_mode(&args, lean_path);
    }

    if let Some(ref styx_ir_path) = args.styx_ir {
        return run_styx_ir_mode(&args, styx_ir_path);
    }

    if let Some(ref direct_src) = args.direct {
        return run_direct_mode(&args, direct_src);
    }

    // Positional input treated as StyxIR
    if let Some(ref input) = args.input {
        return run_styx_ir_mode(&args, input);
    }

    anyhow::bail!(
        "No input specified. Use --styx-ir <file> or --direct <dir>.\n\
         Example: styx --styx-ir input.styx -o out --namespace MyLib"
    );
}

fn run_direct_mode(args: &Args, src_dir: &PathBuf) -> Result<()> {
    use styx::emit::direct::{emit_bridge_template_direct, emit_direct, parse_spec_map_direct};
    use styx::rust_parser::parse_rust_crate;

    if !src_dir.is_dir() {
        anyhow::bail!("--direct path is not a directory: {}", src_dir.display());
    }

    let namespace = args
        .namespace
        .clone()
        .unwrap_or_else(|| "StyxOut".to_string());

    eprintln!("styx: direct mode — scanning {}", src_dir.display());

    let parsed = parse_rust_crate(src_dir)
        .with_context(|| format!("failed to parse Rust source: {}", src_dir.display()))?;

    eprintln!(
        "styx: parsed {} types, {} functions",
        parsed.types.len(),
        parsed.fns.len()
    );

    let mut files = emit_direct(&parsed, &namespace, &args.output_dir, args.emit_checks);

    if args.bridge_template {
        let spec_map = args.spec_map.as_ref().map(|p| parse_spec_map_direct(p));
        let bridge_content = emit_bridge_template_direct(&parsed, &namespace, spec_map.as_ref());
        let ns_dir = args.output_dir.join(&namespace);
        files.insert(ns_dir.join("Bridge_Template.lean"), bridge_content);
    }

    for (path, contents) in &files {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!("failed to create output directory: {}", parent.display())
            })?;
        }
        fs::write(path, contents)
            .with_context(|| format!("failed to write output file: {}", path.display()))?;
    }

    eprintln!(
        "styx: wrote {} files to {}",
        files.len(),
        args.output_dir.display()
    );
    Ok(())
}

fn run_lean_to_rust_mode(args: &Args, lean_path: &PathBuf) -> Result<()> {
    if !lean_path.exists() {
        anyhow::bail!("--lean-to-rust: file not found: {}", lean_path.display());
    }

    let source = fs::read_to_string(lean_path)
        .with_context(|| format!("failed to read Lean file: {}", lean_path.display()))?;

    let (defs, errors) = parse_lean_source(&source);

    for e in &errors {
        eprintln!("styx: lean-to-rust warning: {e}");
    }

    if defs.is_empty() {
        eprintln!(
            "styx: lean-to-rust: no structure/inductive definitions found in {}",
            lean_path.display()
        );
        return Ok(());
    }

    eprintln!(
        "styx: lean-to-rust: parsed {} definitions from {}",
        defs.len(),
        lean_path.display()
    );

    let output = emit_rust_skeletons(&defs, &args.lean_module);

    let output_dir_str = args.output_dir.to_string_lossy();
    if output_dir_str != "out" {
        let out_path = args.output_dir.join("skeletons.rs");
        if let Some(parent) = out_path.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!("failed to create output directory: {}", parent.display())
            })?;
        }
        fs::write(&out_path, &output)
            .with_context(|| format!("failed to write skeleton file: {}", out_path.display()))?;
        eprintln!("styx: lean-to-rust: wrote {}", out_path.display());
    } else {
        print!("{output}");
    }

    Ok(())
}

fn run_styx_ir_mode(args: &Args, styx_path: &PathBuf) -> Result<()> {
    use styx::emit::styxir::emit_styx_package;
    use styx::ir::StyxPackage;

    let json = fs::read_to_string(styx_path)
        .with_context(|| format!("failed to read StyxIR file: {}", styx_path.display()))?;
    let pkg: StyxPackage = serde_json::from_str(&json)
        .with_context(|| format!("failed to parse StyxIR: {}", styx_path.display()))?;

    let namespace = args.namespace.clone().unwrap_or_else(|| {
        let n = pkg.crate_name.clone();
        if n.trim().is_empty() {
            "StyxOut".to_string()
        } else {
            n
        }
    });

    eprintln!(
        "styx: StyxIR mode — {} types, {} functions from {}",
        pkg.types.len(),
        pkg.functions.len(),
        styx_path.display()
    );

    let pkg = if let Some(ref anchor) = args.start_from {
        let filtered = styx::reachability::filter_reachable(&pkg, anchor);
        eprintln!(
            "styx: reachability filter ({}) — {} types, {} functions",
            anchor,
            filtered.types.len(),
            filtered.functions.len()
        );
        filtered
    } else {
        pkg
    };

    let mut pkg = pkg;
    styx::passes::desugar_returns::desugar_returns(&mut pkg);
    styx::passes::desugar_mut_self::desugar_mut_self(&mut pkg);

    let skip_stdlib = args.no_stdlib || args.aeneas_compat;
    let files = emit_styx_package(
        &pkg,
        &namespace,
        &args.output_dir,
        args.aeneas_compat,
        args.emit_checks,
        skip_stdlib,
    );

    for (path, contents) in &files {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).with_context(|| {
                format!("failed to create output directory: {}", parent.display())
            })?;
        }
        fs::write(path, contents)
            .with_context(|| format!("failed to write output file: {}", path.display()))?;
    }

    eprintln!(
        "styx: wrote {} files to {}",
        files.len(),
        args.output_dir.display()
    );
    Ok(())
}
