//! Reachability filter for StyxPackage.
//!
//! Given an anchor function path, computes the transitive closure of
//! types and functions reachable from it. This matches Charon's
//! `--start-from` behavior: only extract what the anchor touches.

use std::collections::HashSet;

use crate::ir::*;

/// Filter a StyxPackage to only include items reachable from `anchor_path`.
/// The anchor is matched against function `rust_path` fields.
pub fn filter_reachable(pkg: &StyxPackage, anchor_path: &str) -> StyxPackage {
    // Find the anchor function
    let anchor_fn = pkg
        .functions
        .iter()
        .find(|f| f.rust_path.contains(anchor_path));
    if anchor_fn.is_none() {
        eprintln!(
            "[reachability] Warning: anchor '{}' not found, returning full package",
            anchor_path
        );
        return pkg.clone();
    }

    // Build reachability sets
    let mut reachable_fns: HashSet<String> = HashSet::new();
    let mut reachable_types: HashSet<String> = HashSet::new();
    let mut worklist: Vec<String> = vec![anchor_fn.unwrap().rust_path.clone()];

    // BFS over function call graph + type references
    while let Some(fn_path) = worklist.pop() {
        if !reachable_fns.insert(fn_path.clone()) {
            continue; // Already visited
        }

        if let Some(fun) = pkg.functions.iter().find(|f| f.rust_path == fn_path) {
            // Collect types from signature
            for param in &fun.params {
                collect_type_refs(&param.ty, &mut reachable_types);
            }
            collect_type_refs(&fun.ret_ty, &mut reachable_types);

            // Collect callees and types from body
            if let Some(body) = &fun.body {
                collect_body_refs(body, &mut worklist, &mut reachable_types);
            }
        }
    }

    // Also include types referenced by reachable types (transitive)
    let mut type_worklist: Vec<String> = reachable_types.iter().cloned().collect();
    while let Some(ty_path) = type_worklist.pop() {
        if let Some(ty_def) = pkg.types.iter().find(|t| t.rust_path == ty_path) {
            collect_typedef_refs(ty_def, &mut reachable_types, &mut type_worklist);
        }
    }

    // Filter the package
    StyxPackage {
        crate_name: pkg.crate_name.clone(),
        types: pkg
            .types
            .iter()
            .filter(|t| reachable_types.contains(&t.rust_path))
            .cloned()
            .collect(),
        functions: pkg
            .functions
            .iter()
            .filter(|f| reachable_fns.contains(&f.rust_path))
            .cloned()
            .collect(),
        trait_decls: pkg.trait_decls.clone(),
        trait_impls: pkg.trait_impls.clone(),
        globals: pkg.globals.clone(),
        decl_groups: Vec::new(),
    }
}

fn collect_type_refs(ty: &StyxType, types: &mut HashSet<String>) {
    match ty {
        StyxType::Adt {
            rust_path,
            generic_args,
            ..
        } => {
            types.insert(rust_path.clone());
            for arg in generic_args {
                collect_type_refs(arg, types);
            }
        }
        StyxType::Tuple(fields) => {
            for f in fields {
                collect_type_refs(f, types);
            }
        }
        StyxType::Array { elem, .. } => collect_type_refs(elem, types),
        StyxType::Slice(elem) => collect_type_refs(elem, types),
        StyxType::Ref { inner, .. } => collect_type_refs(inner, types),
        StyxType::RawPtr { inner, .. } => collect_type_refs(inner, types),
        StyxType::FnPtr { params, ret } => {
            for p in params {
                collect_type_refs(p, types);
            }
            collect_type_refs(ret, types);
        }
        StyxType::DynTrait { generic_args, .. } => {
            for a in generic_args {
                collect_type_refs(a, types);
            }
        }
        _ => {}
    }
}

fn collect_body_refs(body: &StyxBody, fn_worklist: &mut Vec<String>, types: &mut HashSet<String>) {
    for local in &body.locals {
        collect_type_refs(&local.ty, types);
    }
    collect_block_refs(&body.block, fn_worklist, types);
}

fn collect_block_refs(
    block: &StyxBlock,
    fn_worklist: &mut Vec<String>,
    types: &mut HashSet<String>,
) {
    for stmt in &block.stmts {
        collect_stmt_refs(stmt, fn_worklist, types);
    }
}

fn collect_stmt_refs(stmt: &StyxStmt, fn_worklist: &mut Vec<String>, types: &mut HashSet<String>) {
    match stmt {
        StyxStmt::Assign { value, .. } => collect_expr_refs(value, fn_worklist, types),
        StyxStmt::FieldAssign { value, .. } => collect_expr_refs(value, fn_worklist, types),
        StyxStmt::Expr(e) => collect_expr_refs(e, fn_worklist, types),
        StyxStmt::Return(e) => collect_expr_refs(e, fn_worklist, types),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            collect_expr_refs(cond, fn_worklist, types);
            collect_block_refs(then_block, fn_worklist, types);
            collect_block_refs(else_block, fn_worklist, types);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_expr_refs(scrutinee, fn_worklist, types);
            for arm in arms {
                collect_block_refs(&arm.body, fn_worklist, types);
            }
        }
        StyxStmt::Loop { body, cond } => {
            if let Some(c) = cond {
                collect_expr_refs(c, fn_worklist, types);
            }
            collect_block_refs(body, fn_worklist, types);
        }
        StyxStmt::Assert { cond, .. } => collect_expr_refs(cond, fn_worklist, types),
        _ => {}
    }
}

fn collect_expr_refs(expr: &StyxExpr, fn_worklist: &mut Vec<String>, types: &mut HashSet<String>) {
    collect_type_refs(&expr.ty, types);

    match &expr.kind {
        StyxExprKind::Call {
            callee,
            args,
            type_args,
        } => {
            // Add callee to function worklist
            match callee {
                StyxCallee::Function { rust_path, .. } => {
                    fn_worklist.push(rust_path.clone());
                }
                StyxCallee::TraitMethod { .. } => {}
                StyxCallee::Builtin(_) => {}
                StyxCallee::ClosureCall(inner) => {
                    collect_expr_refs(inner, fn_worklist, types);
                }
            }
            for a in args {
                collect_expr_refs(a, fn_worklist, types);
            }
            for t in type_args {
                collect_type_refs(t, types);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_expr_refs(lhs, fn_worklist, types);
            collect_expr_refs(rhs, fn_worklist, types);
        }
        StyxExprKind::UnOp { operand, .. } => {
            collect_expr_refs(operand, fn_worklist, types);
        }
        StyxExprKind::Field { base, .. } => {
            collect_expr_refs(base, fn_worklist, types);
        }
        StyxExprKind::TupleField { base, .. } => {
            collect_expr_refs(base, fn_worklist, types);
        }
        StyxExprKind::Index { base, index } => {
            collect_expr_refs(base, fn_worklist, types);
            collect_expr_refs(index, fn_worklist, types);
        }
        StyxExprKind::StructInit { fields, .. } => {
            for (_, e) in fields {
                collect_expr_refs(e, fn_worklist, types);
            }
        }
        StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_expr_refs(e, fn_worklist, types);
            }
        }
        StyxExprKind::Tuple(elems) => {
            for e in elems {
                collect_expr_refs(e, fn_worklist, types);
            }
        }
        StyxExprKind::Array { elements, .. } => {
            for e in elements {
                collect_expr_refs(e, fn_worklist, types);
            }
        }
        StyxExprKind::Cast { operand, .. } => {
            collect_expr_refs(operand, fn_worklist, types);
        }
        StyxExprKind::Ref { operand, .. } => {
            collect_expr_refs(operand, fn_worklist, types);
        }
        StyxExprKind::Deref(inner) => {
            collect_expr_refs(inner, fn_worklist, types);
        }
        StyxExprKind::Closure { body, .. } => {
            collect_expr_refs(body, fn_worklist, types);
        }
        StyxExprKind::Block { stmts, expr } => {
            for s in stmts {
                collect_stmt_refs(s, fn_worklist, types);
            }
            if let Some(e) = expr {
                collect_expr_refs(e, fn_worklist, types);
            }
        }
        StyxExprKind::QuestionMark { inner, .. } => {
            collect_expr_refs(inner, fn_worklist, types);
        }
        _ => {}
    }
}

fn collect_typedef_refs(
    ty_def: &StyxTypeDef,
    types: &mut HashSet<String>,
    worklist: &mut Vec<String>,
) {
    match &ty_def.kind {
        StyxTypeDefKind::Struct { fields } => {
            for f in fields {
                let mut new_types = HashSet::new();
                collect_type_refs(&f.ty, &mut new_types);
                for t in new_types {
                    if types.insert(t.clone()) {
                        worklist.push(t);
                    }
                }
            }
        }
        StyxTypeDefKind::Enum { variants } => {
            for v in variants {
                for f in &v.fields {
                    let mut new_types = HashSet::new();
                    collect_type_refs(&f.ty, &mut new_types);
                    for t in new_types {
                        if types.insert(t.clone()) {
                            worklist.push(t);
                        }
                    }
                }
            }
        }
        StyxTypeDefKind::Alias { target } => {
            let mut new_types = HashSet::new();
            collect_type_refs(target, &mut new_types);
            for t in new_types {
                if types.insert(t.clone()) {
                    worklist.push(t);
                }
            }
        }
        StyxTypeDefKind::Opaque => {}
    }
}
