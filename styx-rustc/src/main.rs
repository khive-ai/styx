// styx-rustc: Rust → StyxIR extractor via rustc THIR
//
// Phase 2 Charon replacement. Hooks into the Rust compiler as a rustc_driver,
// reads THIR after type checking, and produces StyxIR (.styx JSON).
//
// Pipeline: Rust → styx-rustc (THIR) → StyxIR (.styx JSON) → styx → Lean4

#![feature(rustc_private)]

extern crate rustc_abi;
extern crate rustc_ast;
extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;
extern crate rustc_span;

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;
use std::process::ExitCode;

use rustc_driver::Compilation;
use rustc_hir::def::DefKind;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_session::config::ErrorOutputType;

mod extract_types;
mod extract_funs;
mod extract_traits;
mod ty_convert;

use styx::ir::{StyxPackage, StyxType, StyxTypeDefKind};

// ============================================================================
// CLI
// ============================================================================

#[derive(Debug, Default, serde::Deserialize)]
struct StyxOpts {
    output: Option<PathBuf>,
    /// Single anchor (for backwards compatibility).
    start_from: Option<String>,
    /// Multiple anchors — functions reachable from ANY anchor are included.
    /// Like Charon's multiple --start-from flags.
    #[serde(default)]
    start_from_all: Vec<String>,
}

fn parse_opts() -> StyxOpts {
    match std::env::var("STYX_RUSTC_ARGS") {
        Ok(json) => serde_json::from_str(&json).unwrap_or_default(),
        Err(_) => StyxOpts::default(),
    }
}

// ============================================================================
// rustc_driver Callbacks
// ============================================================================

struct StyxCallbacks {
    opts: StyxOpts,
}

impl rustc_driver::Callbacks for StyxCallbacks {
    fn config(&mut self, config: &mut interface::Config) {
        // Preserve THIR bodies after unsafety checking
        config.opts.unstable_opts.no_steal_thir = true;
    }

    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        let crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
        eprintln!("[styx-rustc] Extracting crate: {crate_name}");

        let package = extract_crate(tcx, &crate_name, &self.opts);

        let output_path = self.opts.output.clone()
            .unwrap_or_else(|| PathBuf::from(format!("{crate_name}.styx")));
        let json = serde_json::to_string_pretty(&package)
            .expect("StyxIR serialization failed");
        std::fs::write(&output_path, &json)
            .unwrap_or_else(|e| panic!("Failed to write {}: {e}", output_path.display()));

        eprintln!(
            "[styx-rustc] Wrote {}: {} types, {} functions, {} traits, {} impls",
            output_path.display(),
            package.types.len(),
            package.functions.len(),
            package.trait_decls.len(),
            package.trait_impls.len(),
        );

        Compilation::Stop
    }
}

// ============================================================================
// Crate extraction
// ============================================================================

fn extract_crate<'tcx>(
    tcx: TyCtxt<'tcx>,
    crate_name: &str,
    opts: &StyxOpts,
) -> StyxPackage {
    let mut package = StyxPackage {
        crate_name: crate_name.to_string(),
        types: Vec::new(),
        functions: Vec::new(),
        trait_decls: Vec::new(),
        trait_impls: Vec::new(),
        globals: Vec::new(),
        decl_groups: Vec::new(),
    };

    // Iterate all local definitions via def_id iteration
    for local_def_id in tcx.iter_local_def_id() {
        let def_kind = tcx.def_kind(local_def_id);
        match def_kind {
            // Type definitions
            DefKind::Struct | DefKind::Enum => {
                if let Some(ty_def) = extract_types::extract_adt_def(tcx, local_def_id) {
                    package.types.push(ty_def);
                }
            }
            DefKind::TyAlias => {
                if let Some(ty_def) = extract_types::extract_type_alias(tcx, local_def_id) {
                    package.types.push(ty_def);
                }
            }
            // Function definitions (free functions and methods)
            DefKind::Fn | DefKind::AssocFn => {
                if let Some(fun_def) = extract_funs::extract_fun_def(tcx, local_def_id) {
                    package.functions.push(fun_def);
                }
            }
            // Trait declarations
            DefKind::Trait => {
                if let Some(trait_decl) = extract_traits::extract_trait_decl(tcx, local_def_id) {
                    package.trait_decls.push(trait_decl);
                }
            }
            // Trait implementations (of_trait: false are inherent impls -- skip)
            DefKind::Impl { of_trait: true } => {
                if let Some(trait_impl) = extract_traits::extract_trait_impl(tcx, local_def_id) {
                    package.trait_impls.push(trait_impl);
                }
            }
            // Global constants and statics
            DefKind::Const | DefKind::Static { .. } => {
                if let Some(global_def) = extract_traits::extract_global_def(tcx, local_def_id) {
                    package.globals.push(global_def);
                }
            }
            _ => {}
        }
    }

    // Apply reachability filter if start_from is specified.
    // Collect all anchor paths: single start_from + multi start_from_all.
    let mut anchors: Vec<&str> = Vec::new();
    if let Some(ref s) = opts.start_from {
        anchors.push(s.as_str());
    }
    for s in &opts.start_from_all {
        anchors.push(s.as_str());
    }
    if !anchors.is_empty() {
        filter_reachable_multi(&mut package, &anchors);
    }

    package
}

// ============================================================================
// Reachability filter
// ============================================================================

/// Collect TypeId values (as u32) from a StyxType, recursively through
/// all generic args, references, pointers, tuples, arrays, and fn pointers.
fn collect_type_ids(ty: &StyxType, out: &mut HashSet<u32>) {
    match ty {
        StyxType::Adt { type_id, generic_args, .. } => {
            if let Some(tid) = type_id {
                out.insert(tid.0);
            }
            for arg in generic_args {
                collect_type_ids(arg, out);
            }
        }
        StyxType::Ref { inner, .. } | StyxType::RawPtr { inner, .. } => {
            collect_type_ids(inner, out);
        }
        StyxType::Tuple(fields) => {
            for f in fields {
                collect_type_ids(f, out);
            }
        }
        StyxType::Array { elem, .. } | StyxType::Slice(elem) => {
            collect_type_ids(elem, out);
        }
        StyxType::FnPtr { params, ret } => {
            for p in params {
                collect_type_ids(p, out);
            }
            collect_type_ids(ret, out);
        }
        // Scalar, Str, TypeParam, AssocType, DynTrait, Never, Unit, Unsupported
        _ => {}
    }
}

/// Collect all FunIds called from a function body (for call-graph reachability).
fn collect_body_callees(body: &styx::ir::StyxBody, out: &mut HashSet<u32>) {
    collect_block_callees(&body.block, out);
}

fn collect_block_callees(block: &styx::ir::StyxBlock, out: &mut HashSet<u32>) {
    for stmt in &block.stmts {
        collect_stmt_callees(stmt, out);
    }
}

fn collect_stmt_callees(stmt: &styx::ir::StyxStmt, out: &mut HashSet<u32>) {
    use styx::ir::StyxStmt;
    match stmt {
        StyxStmt::Assign { value, .. } => collect_expr_callees(value, out),
        StyxStmt::FieldAssign { value, .. } => collect_expr_callees(value, out),
        StyxStmt::Expr(e) | StyxStmt::Return(e) => collect_expr_callees(e, out),
        StyxStmt::If { cond, then_block, else_block } => {
            collect_expr_callees(cond, out);
            collect_block_callees(then_block, out);
            collect_block_callees(else_block, out);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_expr_callees(scrutinee, out);
            for arm in arms {
                collect_block_callees(&arm.body, out);
            }
        }
        StyxStmt::Loop { body, cond } => {
            collect_block_callees(body, out);
            if let Some(c) = cond { collect_expr_callees(c, out); }
        }
        StyxStmt::Assert { cond, .. } => collect_expr_callees(cond, out),
        _ => {}
    }
}

fn collect_expr_callees(expr: &styx::ir::StyxExpr, out: &mut HashSet<u32>) {
    use styx::ir::{StyxExprKind, StyxCallee};
    match &expr.kind {
        StyxExprKind::Call { callee, args, .. } => {
            if let StyxCallee::Function { local_id: Some(fid), .. } = callee {
                out.insert(fid.0);
            }
            for a in args { collect_expr_callees(a, out); }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_expr_callees(lhs, out);
            collect_expr_callees(rhs, out);
        }
        StyxExprKind::UnOp { operand, .. } => collect_expr_callees(operand, out),
        StyxExprKind::Field { base, .. } => collect_expr_callees(base, out),
        StyxExprKind::TupleField { base, .. } => collect_expr_callees(base, out),
        StyxExprKind::Index { base, index } => {
            collect_expr_callees(base, out);
            collect_expr_callees(index, out);
        }
        StyxExprKind::StructInit { fields, .. } => {
            for (_, e) in fields { collect_expr_callees(e, out); }
        }
        StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields { collect_expr_callees(e, out); }
        }
        StyxExprKind::Tuple(elems) | StyxExprKind::Array { elements: elems, .. } => {
            for e in elems { collect_expr_callees(e, out); }
        }
        StyxExprKind::Cast { operand, .. } | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand) | StyxExprKind::QuestionMark { inner: operand, .. } => {
            collect_expr_callees(operand, out);
        }
        StyxExprKind::Closure { body, .. } => collect_expr_callees(body, out),
        StyxExprKind::Block { stmts, expr } => {
            for s in stmts { collect_stmt_callees(s, out); }
            if let Some(e) = expr { collect_expr_callees(e, out); }
        }
        _ => {}
    }
}

/// Filter the package to only include types and functions reachable from
/// one or more anchor functions.
///
/// Algorithm:
///   1. Find each anchor function by suffix-matching `rust_path`.
///   2. Seed the type set from all anchors' param types and return types.
///   3. Expand transitively through type definitions.
///   4. Retain only reachable types, functions, and trait impls.
fn filter_reachable_multi(pkg: &mut StyxPackage, anchor_paths: &[&str]) {
    // Step 1 — find all anchor functions.
    let mut reachable: HashSet<u32> = HashSet::new();
    let mut found_any = false;

    for anchor_path in anchor_paths {
        let normalized = anchor_path
            .strip_prefix("crate::")
            .unwrap_or(anchor_path);
        let anchor = pkg.functions.iter().find(|f| {
            f.rust_path == *anchor_path
                || f.rust_path == normalized
                || f.rust_path.ends_with(*anchor_path)
                || f.rust_path.ends_with(normalized)
        });

        match anchor {
            Some(f) => {
                eprintln!("[styx-rustc] Reachability anchor: {}", f.rust_path);
                found_any = true;
                // Step 2 — seed from anchor signature.
                for param in &f.params {
                    collect_type_ids(&param.ty, &mut reachable);
                }
                collect_type_ids(&f.ret_ty, &mut reachable);
            }
            None => {
                eprintln!(
                    "[styx-rustc] Warning: anchor '{anchor_path}' not found, skipping"
                );
            }
        }
    }

    if !found_any {
        eprintln!("[styx-rustc] Warning: no anchors found, emitting all");
        return;
    }

    // Step 3 — transitive expansion through type definitions.
    // Build a lookup map once, then drive a worklist.
    let type_map: HashMap<u32, &styx::ir::StyxTypeDef> = pkg.types.iter()
        .map(|t| (t.id.0, t))
        .collect();

    let mut worklist: Vec<u32> = reachable.iter().copied().collect();
    while let Some(tid) = worklist.pop() {
        let td = match type_map.get(&tid) {
            Some(t) => t,
            None => continue,
        };
        let mut new_ids: HashSet<u32> = HashSet::new();
        match &td.kind {
            StyxTypeDefKind::Struct { fields } => {
                for f in fields {
                    collect_type_ids(&f.ty, &mut new_ids);
                }
            }
            StyxTypeDefKind::Enum { variants } => {
                for v in variants {
                    for f in &v.fields {
                        collect_type_ids(&f.ty, &mut new_ids);
                    }
                }
            }
            StyxTypeDefKind::Alias { target } => {
                collect_type_ids(target, &mut new_ids);
            }
            StyxTypeDefKind::Opaque => {}
        }
        for id in new_ids {
            if reachable.insert(id) {
                worklist.push(id);
            }
        }
    }

    eprintln!("[styx-rustc] Reachable type IDs after type closure: {}", reachable.len());

    // Step 3b — fixpoint expansion through function signatures.
    // A function that touches a reachable type is kept; its other parameter/return types
    // become reachable too. Iterate until fixpoint so type-in-return-only types are included.
    loop {
        let before = reachable.len();
        let mut added: HashSet<u32> = HashSet::new();
        for f in &pkg.functions {
            let mut sig_ids: HashSet<u32> = HashSet::new();
            for p in &f.params {
                collect_type_ids(&p.ty, &mut sig_ids);
            }
            collect_type_ids(&f.ret_ty, &mut sig_ids);
            // If any type in the signature is reachable, all of them become reachable.
            if sig_ids.iter().any(|t| reachable.contains(t)) {
                for t in sig_ids {
                    added.insert(t);
                }
            }
        }
        for t in added {
            reachable.insert(t);
        }
        // Re-expand type set transitively through any newly-added type definitions.
        let type_map: HashMap<u32, &styx::ir::StyxTypeDef> = pkg.types.iter()
            .map(|t| (t.id.0, t))
            .collect();
        let mut worklist: Vec<u32> = reachable.iter().copied().collect();
        while let Some(tid) = worklist.pop() {
            let td = match type_map.get(&tid) {
                Some(t) => t,
                None => continue,
            };
            let mut new_ids: HashSet<u32> = HashSet::new();
            match &td.kind {
                StyxTypeDefKind::Struct { fields } => {
                    for f in fields { collect_type_ids(&f.ty, &mut new_ids); }
                }
                StyxTypeDefKind::Enum { variants } => {
                    for v in variants {
                        for f in &v.fields { collect_type_ids(&f.ty, &mut new_ids); }
                    }
                }
                StyxTypeDefKind::Alias { target } => {
                    collect_type_ids(target, &mut new_ids);
                }
                StyxTypeDefKind::Opaque => {}
            }
            for id in new_ids {
                if reachable.insert(id) { worklist.push(id); }
            }
        }
        if reachable.len() == before { break; }
    }
    eprintln!("[styx-rustc] Reachable type IDs after fixpoint: {}", reachable.len());

    // Step 3c — call-based function reachability.
    // A function whose signature only touches non-local types (e.g., a helper taking &mut Vec<u64>)
    // should still be kept if it's called from a type-reachable function. Walk call graphs
    // from type-reachable functions and add transitively called FunIds.
    let mut reachable_funs: HashSet<u32> = HashSet::new();
    // Seed: functions whose signatures touch a reachable type
    for f in &pkg.functions {
        let mut sig_ids: HashSet<u32> = HashSet::new();
        for p in &f.params {
            collect_type_ids(&p.ty, &mut sig_ids);
        }
        collect_type_ids(&f.ret_ty, &mut sig_ids);
        if sig_ids.iter().any(|t| reachable.contains(t)) {
            reachable_funs.insert(f.id.0);
        }
    }
    // Transitive closure: for each reachable function, scan its body for called FunIds.
    let fun_by_id: HashMap<u32, &styx::ir::StyxFunDef> = pkg.functions.iter()
        .map(|f| (f.id.0, f))
        .collect();
    let mut work: Vec<u32> = reachable_funs.iter().copied().collect();
    while let Some(fid) = work.pop() {
        let f = match fun_by_id.get(&fid) {
            Some(f) => f,
            None => continue,
        };
        if let Some(body) = &f.body {
            let mut called: HashSet<u32> = HashSet::new();
            collect_body_callees(body, &mut called);
            for cid in called {
                if fun_by_id.contains_key(&cid) && reachable_funs.insert(cid) {
                    work.push(cid);
                }
            }
        }
    }
    eprintln!("[styx-rustc] Reachable functions (type+call): {}", reachable_funs.len());

    // Step 4a — filter types.
    let before_types = pkg.types.len();
    pkg.types.retain(|t| reachable.contains(&t.id.0));
    eprintln!(
        "[styx-rustc] Types: {} → {}",
        before_types,
        pkg.types.len()
    );

    // Step 4b — filter functions: keep those in the type+call reachable set.
    let before_fns = pkg.functions.len();
    pkg.functions.retain(|f| reachable_funs.contains(&f.id.0));
    eprintln!(
        "[styx-rustc] Functions: {} → {}",
        before_fns,
        pkg.functions.len()
    );

    // Step 4c — filter trait impls: keep those whose self_ty touches a reachable type.
    let before_impls = pkg.trait_impls.len();
    pkg.trait_impls.retain(|imp| {
        let mut impl_types: HashSet<u32> = HashSet::new();
        collect_type_ids(&imp.self_ty, &mut impl_types);
        impl_types.iter().any(|t| reachable.contains(t))
    });
    eprintln!(
        "[styx-rustc] TraitImpls: {} → {}",
        before_impls,
        pkg.trait_impls.len()
    );
}

// ============================================================================
// Entry point
// ============================================================================

fn main() -> ExitCode {
    let _early_dcx = rustc_session::EarlyDiagCtxt::new(ErrorOutputType::default());

    let args: Vec<String> = std::env::args().collect();

    // Detect RUSTC_WORKSPACE_WRAPPER mode: cargo passes the real rustc as args[1].
    // In this mode: args = [styx-rustc, /path/to/rustc, <rustc-args...>]
    // We need to determine if this is a probe command or the primary crate build.
    let is_wrapper_mode = args.get(1).is_some_and(|a| a.contains("rustc") && !a.contains("styx"));

    if is_wrapper_mode {
        let real_rustc = &args[1];
        let rustc_args = &args[2..];

        // Cargo sends probe commands (--print=file-names, etc.). Delegate those to real rustc.
        let is_probe = rustc_args.iter().any(|a| a.starts_with("--print=") || a == "-")
            || !rustc_args.iter().any(|a| a.ends_with(".rs"));

        if is_probe {
            // Passthrough to real rustc
            let status = std::process::Command::new(real_rustc)
                .args(rustc_args)
                .status()
                .expect("failed to run rustc");
            return if status.success() { ExitCode::SUCCESS } else { ExitCode::FAILURE };
        }

        // Check if this is the primary crate (CARGO_PRIMARY_PACKAGE=1)
        let is_primary = std::env::var("CARGO_PRIMARY_PACKAGE").as_deref() == Ok("1");

        if !is_primary {
            // Dependency crate — delegate to real rustc
            let status = std::process::Command::new(real_rustc)
                .args(rustc_args)
                .status()
                .expect("failed to run rustc");
            return if status.success() { ExitCode::SUCCESS } else { ExitCode::FAILURE };
        }

        // Primary crate — run our extraction via rustc_driver.
        // Reconstruct args: [styx-rustc, <rustc-args...>] (skip the real rustc path)
        let driver_args: Vec<String> = std::iter::once(args[0].clone())
            .chain(rustc_args.iter().cloned())
            .collect();

        return run_extraction(&driver_args);
    }

    // Direct invocation: args = [styx-rustc, <rustc-args...>]
    run_extraction(&args)
}

fn run_extraction(args: &[String]) -> ExitCode {
    let opts = parse_opts();
    let mut callbacks = StyxCallbacks { opts };

    rustc_driver::install_ice_hook(
        "https://github.com/ohdearquant/proofs/issues",
        |_| (),
    );

    let exit_code = rustc_driver::catch_with_exit_code(|| {
        rustc_driver::run_compiler(args, &mut callbacks)
    });

    if exit_code == 0 {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
