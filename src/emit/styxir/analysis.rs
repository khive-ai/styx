use crate::ir::*;

// ---------------------------------------------------------------------------
// Funs.lean
// ---------------------------------------------------------------------------

/// Track which functions have sorry in their bodies and must be opaque.
pub(crate) struct EmitResult {
    pub(crate) funs_lean: String,
    /// Functions that contained sorry and were made opaque.
    pub(crate) sorry_fns: Vec<usize>, // indices into pkg.functions
}

/// Collect local function IDs that a function body calls.
pub(crate) fn collect_call_deps(body: &StyxBody) -> std::collections::HashSet<u32> {
    let mut deps = std::collections::HashSet::new();
    collect_block_call_deps(&body.block, &mut deps);
    deps
}

pub(crate) fn collect_block_call_deps(block: &StyxBlock, deps: &mut std::collections::HashSet<u32>) {
    for stmt in &block.stmts {
        collect_stmt_call_deps(stmt, deps);
    }
}

pub(crate) fn collect_stmt_call_deps(stmt: &StyxStmt, deps: &mut std::collections::HashSet<u32>) {
    match stmt {
        StyxStmt::Assign { value, .. } => collect_expr_call_deps(value, deps),
        StyxStmt::Expr(e) | StyxStmt::Return(e) => collect_expr_call_deps(e, deps),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            collect_expr_call_deps(cond, deps);
            collect_block_call_deps(then_block, deps);
            collect_block_call_deps(else_block, deps);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_expr_call_deps(scrutinee, deps);
            for arm in arms {
                collect_block_call_deps(&arm.body, deps);
            }
        }
        StyxStmt::Loop { body, cond } => {
            collect_block_call_deps(body, deps);
            if let Some(c) = cond {
                collect_expr_call_deps(c, deps);
            }
        }
        StyxStmt::FieldAssign { value, .. } => collect_expr_call_deps(value, deps),
        StyxStmt::Assert { cond, .. } => collect_expr_call_deps(cond, deps),
        _ => {}
    }
}

/// Collect all Local variable IDs referenced in an expression tree.
/// Used to infer closure param → Local ID bindings when params lack local_id.
/// Collect (local_id → type) from an expression tree. Used by T1 tuple-destructure
/// detection to match body locals against closure-param tuple fields.
pub(crate) fn collect_local_types(expr: &StyxExpr, out: &mut std::collections::BTreeMap<u32, StyxType>) {
    if let StyxExprKind::Local(id) = &expr.kind {
        out.entry(id.0).or_insert_with(|| expr.ty.clone());
    }
    match &expr.kind {
        StyxExprKind::Call { args, .. } => {
            for a in args {
                collect_local_types(a, out);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_local_types(lhs, out);
            collect_local_types(rhs, out);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand)
        | StyxExprKind::QuestionMark { inner: operand, .. } => {
            collect_local_types(operand, out);
        }
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            collect_local_types(base, out);
        }
        StyxExprKind::Index { base, index } => {
            collect_local_types(base, out);
            collect_local_types(index, out);
        }
        StyxExprKind::StructInit { fields, .. } | StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_local_types(e, out);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                collect_local_types(e, out);
            }
        }
        StyxExprKind::Closure { body, .. } => collect_local_types(body, out),
        StyxExprKind::Block { stmts, expr } => {
            for s in stmts {
                collect_local_types_in_stmt(s, out);
            }
            if let Some(e) = expr {
                collect_local_types(e, out);
            }
        }
        _ => {}
    }
}

pub(crate) fn collect_local_types_in_stmt(
    stmt: &StyxStmt,
    out: &mut std::collections::BTreeMap<u32, StyxType>,
) {
    match stmt {
        StyxStmt::Assign { value, .. } | StyxStmt::Expr(value) | StyxStmt::Return(value) => {
            collect_local_types(value, out);
        }
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            collect_local_types(cond, out);
            for s in &then_block.stmts {
                collect_local_types_in_stmt(s, out);
            }
            for s in &else_block.stmts {
                collect_local_types_in_stmt(s, out);
            }
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_local_types(scrutinee, out);
            for arm in arms {
                for s in &arm.body.stmts {
                    collect_local_types_in_stmt(s, out);
                }
            }
        }
        _ => {}
    }
}

pub(crate) fn collect_local_ids(expr: &StyxExpr, ids: &mut std::collections::BTreeSet<u32>) {
    match &expr.kind {
        StyxExprKind::Local(id) => {
            ids.insert(id.0);
        }
        StyxExprKind::Call { args, .. } => {
            for a in args {
                collect_local_ids(a, ids);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_local_ids(lhs, ids);
            collect_local_ids(rhs, ids);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand)
        | StyxExprKind::QuestionMark { inner: operand, .. } => {
            collect_local_ids(operand, ids);
        }
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            collect_local_ids(base, ids);
        }
        StyxExprKind::Index { base, index } => {
            collect_local_ids(base, ids);
            collect_local_ids(index, ids);
        }
        StyxExprKind::StructInit { fields, .. } | StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_local_ids(e, ids);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                collect_local_ids(e, ids);
            }
        }
        StyxExprKind::Closure { body, .. } => collect_local_ids(body, ids),
        StyxExprKind::Block { stmts, expr } => {
            for s in stmts {
                collect_local_ids_in_stmt(s, ids);
            }
            if let Some(e) = expr {
                collect_local_ids(e, ids);
            }
        }
        _ => {}
    }
}

pub(crate) fn collect_local_ids_in_stmt(stmt: &StyxStmt, ids: &mut std::collections::BTreeSet<u32>) {
    match stmt {
        StyxStmt::Assign { value, .. } | StyxStmt::FieldAssign { value, .. } => {
            collect_local_ids(value, ids);
        }
        StyxStmt::Expr(e) => collect_local_ids(e, ids),
        StyxStmt::Return(e) | StyxStmt::Assert { cond: e, .. } => collect_local_ids(e, ids),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            collect_local_ids(cond, ids);
            collect_local_ids_in_block(then_block, ids);
            collect_local_ids_in_block(else_block, ids);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_local_ids(scrutinee, ids);
            for arm in arms {
                collect_local_ids_in_block(&arm.body, ids);
            }
        }
        StyxStmt::Loop { body, cond } => {
            collect_local_ids_in_block(body, ids);
            if let Some(c) = cond {
                collect_local_ids(c, ids);
            }
        }
        _ => {}
    }
}

/// Peel a single Ref layer from a StyxType, if present.
/// Used by T1 type matching so that `Ref(U64)` matches `U64` (and vice versa)
/// when comparing inferred body-local types against closure tuple field types.
pub(crate) fn peel_ref(ty: &StyxType) -> &StyxType {
    match ty {
        StyxType::Ref { inner, .. } => inner.as_ref(),
        other => other,
    }
}

/// Structural equality for StyxType (subset needed for closure param inference).
/// StyxType does not derive PartialEq, so we implement it manually for the cases
/// the closure emitter needs.
/// Ref-transparent: `Ref(X)` compares equal to `X` (references are erased in Lean).
pub(crate) fn styx_types_equal(a: &StyxType, b: &StyxType) -> bool {
    // Peel Refs from both sides before comparing — Rust &T and T are the same in Lean.
    let a = peel_ref(a);
    let b = peel_ref(b);
    match (a, b) {
        (StyxType::Scalar(s1), StyxType::Scalar(s2)) => s1 == s2,
        (StyxType::Str, StyxType::Str) => true,
        (
            StyxType::Adt {
                rust_path: p1,
                type_id: id1,
                generic_args: ga1,
                ..
            },
            StyxType::Adt {
                rust_path: p2,
                type_id: id2,
                generic_args: ga2,
                ..
            },
        ) => {
            p1 == p2
                && id1 == id2
                && ga1.len() == ga2.len()
                && ga1
                    .iter()
                    .zip(ga2.iter())
                    .all(|(a, b)| styx_types_equal(a, b))
        }
        (StyxType::Tuple(f1), StyxType::Tuple(f2)) => {
            f1.len() == f2.len()
                && f1
                    .iter()
                    .zip(f2.iter())
                    .all(|(a, b)| styx_types_equal(a, b))
        }
        (
            StyxType::Ref {
                inner: i1,
                is_mut: m1,
            },
            StyxType::Ref {
                inner: i2,
                is_mut: m2,
            },
        ) => m1 == m2 && styx_types_equal(i1, i2),
        (StyxType::Slice(e1), StyxType::Slice(e2)) => styx_types_equal(e1, e2),
        _ => false,
    }
}

/// Detect emitted saturating-arithmetic calls by textual match. Used to classify
/// Block { Assign(DUMMY, saturating_call), trailing: self.field } as a pure
/// mutation whose observable effect is erased in Lean's functional semantics.
pub(crate) fn is_pure_saturating_num_call(s: &str) -> bool {
    s.contains(".saturating_add ")
        || s.ends_with(".saturating_add")
        || s.contains(".saturating_sub ")
        || s.ends_with(".saturating_sub")
        || s.contains("core.num.saturating_add ")
        || s.contains("core.num.saturating_sub ")
}

/// When a closure param has type `Ref(Tuple[T0, T1, ...])` (or bare `Tuple[...]`)
/// and the closure body local has a type that matches field k of that Tuple,
/// return the Lean 1-indexed field number (k+1).  Returns `None` if the pattern
/// doesn't match (param type is not a Tuple, or body type isn't a Tuple field).
///
/// This handles `|&(id, _)| id` closures in which styx-rustc emits the
/// destructured field as a bare `Local(N): U64` rather than a `TupleField` expr.
pub(crate) fn closure_tuple_field_index(param_ty: &StyxType, body_ty: &StyxType) -> Option<usize> {
    // Peel all Ref layers (handles &&(T, U) as well as &(T, U))
    let mut inner = param_ty;
    loop {
        match inner {
            StyxType::Ref { inner: next, .. } => inner = next.as_ref(),
            other => {
                inner = other;
                break;
            }
        }
    }
    if let StyxType::Tuple(fields) = inner {
        // Also peel one Ref from body_ty when matching (closures may capture &T fields)
        let body_inner = match body_ty {
            StyxType::Ref { inner, .. } => inner.as_ref(),
            other => other,
        };
        fields
            .iter()
            .position(|f| {
                // Try direct match, then peel one Ref from the field type
                let f_inner = match f {
                    StyxType::Ref { inner, .. } => inner.as_ref(),
                    other => other,
                };
                styx_types_equal(f, body_ty)
                    || styx_types_equal(f_inner, body_ty)
                    || styx_types_equal(f, body_inner)
                    || styx_types_equal(f_inner, body_inner)
            })
            .map(|i| i + 1) // Lean tuple projection is 1-indexed
    } else {
        None
    }
}

pub(crate) fn collect_local_ids_in_block(block: &StyxBlock, ids: &mut std::collections::BTreeSet<u32>) {
    for s in &block.stmts {
        collect_local_ids_in_stmt(s, ids);
    }
}

/// Collect local IDs that are ASSIGNED (as Assign targets) within a block.
/// Used to distinguish payload-binding locals from locally-computed temporaries.
pub(crate) fn collect_assigned_ids_in_block(block: &StyxBlock, ids: &mut std::collections::BTreeSet<u32>) {
    for s in &block.stmts {
        collect_assigned_ids_in_stmt(s, ids);
    }
}

pub(crate) fn collect_assigned_ids_in_stmt(stmt: &StyxStmt, ids: &mut std::collections::BTreeSet<u32>) {
    match stmt {
        StyxStmt::Assign { target, .. } if target.0 != u32::MAX => {
            ids.insert(target.0);
        }
        StyxStmt::FieldAssign { target, .. } => {
            ids.insert(target.0);
        }
        StyxStmt::If {
            then_block,
            else_block,
            ..
        } => {
            collect_assigned_ids_in_block(then_block, ids);
            collect_assigned_ids_in_block(else_block, ids);
        }
        StyxStmt::Match { arms, .. } => {
            for arm in arms {
                collect_assigned_ids_in_block(&arm.body, ids);
            }
        }
        StyxStmt::Loop { body, .. } => collect_assigned_ids_in_block(body, ids),
        _ => {}
    }
}

/// Collect local IDs that are ASSIGNED (as Assign targets) within an expression tree.
/// Used by closure param inference (F6a) to exclude body-internal temporaries from
/// inferred_ids.  A `let mut revoked_cap = cap.clone()` inside a closure body emits
/// as `StyxStmt::Assign { target: local_37, .. }` nested inside an If block inside
/// a Block expr — this helper descends through all expression/block nesting.
pub(crate) fn collect_assigned_ids_in_expr(expr: &StyxExpr, ids: &mut std::collections::BTreeSet<u32>) {
    match &expr.kind {
        StyxExprKind::Block { stmts, expr: tail } => {
            for s in stmts {
                collect_assigned_ids_in_stmt(s, ids);
            }
            if let Some(e) = tail {
                collect_assigned_ids_in_expr(e, ids);
            }
        }
        StyxExprKind::Closure { body, .. } => collect_assigned_ids_in_expr(body, ids),
        StyxExprKind::Call { args, .. } => {
            for a in args {
                collect_assigned_ids_in_expr(a, ids);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_assigned_ids_in_expr(lhs, ids);
            collect_assigned_ids_in_expr(rhs, ids);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand)
        | StyxExprKind::QuestionMark { inner: operand, .. } => {
            collect_assigned_ids_in_expr(operand, ids);
        }
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            collect_assigned_ids_in_expr(base, ids);
        }
        StyxExprKind::Index { base, index } => {
            collect_assigned_ids_in_expr(base, ids);
            collect_assigned_ids_in_expr(index, ids);
        }
        StyxExprKind::StructInit { fields, .. } | StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_assigned_ids_in_expr(e, ids);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                collect_assigned_ids_in_expr(e, ids);
            }
        }
        _ => {}
    }
}

pub(crate) fn collect_expr_call_deps(expr: &StyxExpr, deps: &mut std::collections::HashSet<u32>) {
    match &expr.kind {
        StyxExprKind::Call { callee, args, .. } => {
            if let StyxCallee::Function {
                local_id: Some(fid),
                ..
            } = callee
            {
                deps.insert(fid.0);
            }
            for a in args {
                collect_expr_call_deps(a, deps);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_expr_call_deps(lhs, deps);
            collect_expr_call_deps(rhs, deps);
        }
        StyxExprKind::UnOp { operand, .. } => collect_expr_call_deps(operand, deps),
        StyxExprKind::Field { base, .. } => collect_expr_call_deps(base, deps),
        StyxExprKind::TupleField { base, .. } => collect_expr_call_deps(base, deps),
        StyxExprKind::Index { base, index } => {
            collect_expr_call_deps(base, deps);
            collect_expr_call_deps(index, deps);
        }
        StyxExprKind::StructInit { fields, .. } => {
            for (_, e) in fields {
                collect_expr_call_deps(e, deps);
            }
        }
        StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_expr_call_deps(e, deps);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                collect_expr_call_deps(e, deps);
            }
        }
        StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand)
        | StyxExprKind::QuestionMark { inner: operand, .. } => {
            collect_expr_call_deps(operand, deps);
        }
        StyxExprKind::Closure { body, .. } => collect_expr_call_deps(body, deps),
        StyxExprKind::Block { stmts, expr } => {
            for s in stmts {
                collect_stmt_call_deps(s, deps);
            }
            if let Some(e) = expr {
                collect_expr_call_deps(e, deps);
            }
        }
        _ => {}
    }
}

/// Topological sort of functions by local call dependencies.
pub(crate) fn topo_sort_funs(funs: &[StyxFunDef]) -> Vec<usize> {
    use std::collections::{HashMap, HashSet, VecDeque};

    // Build FunId → index map
    let id_to_idx: HashMap<u32, usize> =
        funs.iter().enumerate().map(|(i, f)| (f.id.0, i)).collect();
    let local_ids: HashSet<u32> = funs.iter().map(|f| f.id.0).collect();

    // Build dependency graph: index → set of indices it depends on
    let mut deps: Vec<HashSet<usize>> = Vec::with_capacity(funs.len());
    for fun in funs {
        let mut my_deps = HashSet::new();
        if let Some(body) = &fun.body {
            for dep_id in collect_call_deps(body) {
                if dep_id != fun.id.0 && local_ids.contains(&dep_id)
                    && let Some(&idx) = id_to_idx.get(&dep_id) {
                        my_deps.insert(idx);
                    }
            }
        }
        deps.push(my_deps);
    }

    // Kahn's algorithm
    let mut in_degree: Vec<usize> = deps.iter().map(|d| d.len()).collect();
    let mut queue: VecDeque<usize> = in_degree
        .iter()
        .enumerate()
        .filter(|&(_, &deg)| deg == 0)
        .map(|(i, _)| i)
        .collect();
    let mut ordered = Vec::with_capacity(funs.len());

    while let Some(idx) = queue.pop_front() {
        ordered.push(idx);
        // For all functions that depend on idx, decrement their in-degree
        for (other_idx, other_deps) in deps.iter().enumerate() {
            if other_deps.contains(&idx) {
                in_degree[other_idx] -= 1;
                if in_degree[other_idx] == 0 {
                    queue.push_back(other_idx);
                }
            }
        }
    }

    // Append any remaining (cycles) in original order
    let ordered_set: HashSet<usize> = ordered.iter().copied().collect();
    for i in 0..funs.len() {
        if !ordered_set.contains(&i) {
            ordered.push(i);
        }
    }

    ordered
}
