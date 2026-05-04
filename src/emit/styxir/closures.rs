use crate::naming::escape_lean_keyword;
use super::*;
use super::body::LOCAL_NAMES;

// ---------------------------------------------------------------------------
// Option::map + IndexVec closure desugaring
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// Iterator::all + IndexVec closure desugaring
// ---------------------------------------------------------------------------

/// Emit a StyxExpr (closure body) in statement mode, recursively flattening
/// StyxExprKind::Block nodes to handle both `stmts` and trailing `expr`.
///
/// The Closure IR body may be deeply nested Blocks:
///   Block { stmts: [Expr(Block { stmts: [If { guard }] })], expr: Some(match_block) }
/// `emit_block_stmts` only handles a flat StyxBlock (no trailing expr).
/// This function recursively flattens and emits all statements + trailing expr.
pub(crate) fn emit_closure_body_stmts(
    w: &mut crate::emit::indent::IndentWriter,
    expr: &StyxExpr,
    types: &TypeLookup,
) {
    match &expr.kind {
        StyxExprKind::Block {
            stmts,
            expr: trailing,
        } => {
            // Emit all block statements
            let block = StyxBlock {
                stmts: stmts.clone(),
            };
            if !stmts.is_empty() {
                emit_block_stmts(w, &block, types);
            }
            // Emit the trailing expression (the block's value) as a final Return
            if let Some(tail) = trailing {
                emit_closure_body_stmts(w, tail, types);
            }
        }
        _ => {
            // Leaf expression — wrap as Return and emit via emit_stmt
            let ret_stmt = StyxStmt::Return(expr.clone());
            emit_stmt(w, &ret_stmt, true, types);
        }
    }
}

/// Desugar `Iterator::{all,any,find,map}(iter, |params| body)` into do-notation.
///
/// The problem: closures passed to these iterator methods must return `Result T`, and
/// `←` inside a `fun` binder requires a `do` block. When the closure body uses either
/// (a) IndexVec.index (which returns Result), or (b) tuple-destructure over tuple-typed
/// iterator items (e.g. `Vec<(U64, Capability)>`), the emitter must generate:
///   `(fun params => do\n  [let (..) := param]\n  <body_stmts>)`
/// using statement-mode emission rather than inline expression emission.
///
/// `method_name` selects the emitted Iterator method: "all", "any", "find", or "map".
/// All four share the same closure shape (`ItemT → Result T`); only the outer call
/// name differs. `find` returns `Result (Option Item)` and `map` returns `Result B`
/// at the iterator layer, but the per-element closure shape is identical.
pub(crate) fn emit_iter_closure_as_do(
    method_name: &str,
    iter: &StyxExpr,
    params: &[StyxParam],
    body: &StyxExpr,
    types: &TypeLookup,
) -> String {
    let iter_str = emit_expr_lifted(iter, types);

    // Find the value param (skip FnPtr captures — closure env pointers)
    let is_fn_env = |ty: &StyxType| -> bool {
        match ty {
            StyxType::FnPtr { .. } => true,
            StyxType::Ref { inner, .. } => matches!(inner.as_ref(), StyxType::FnPtr { .. }),
            _ => false,
        }
    };
    let value_param_idx = params.iter().position(|p| !is_fn_env(&p.ty));
    let value_param = value_param_idx
        .and_then(|i| params.get(i))
        .map(|p| escape_lean_keyword(&p.name))
        .unwrap_or_else(|| "arg1".to_string());

    // Collect inferred body locals (not in outer scope, not body-assigned).
    // These are the tuple field locals that need to be bound.
    let mut body_locals = std::collections::BTreeSet::new();
    collect_local_ids(body, &mut body_locals);
    let mut body_assigned = std::collections::BTreeSet::new();
    collect_assigned_ids_in_expr(body, &mut body_assigned);
    let mut inferred_ids: Vec<u32> = Vec::new();
    LOCAL_NAMES.with(|map| {
        let m = map.borrow();
        for &id in &body_locals {
            if !m.contains_key(&id) && !body_assigned.contains(&id) {
                inferred_ids.push(id);
            }
        }
    });
    inferred_ids.sort_unstable();

    // Detect T1: param type peels to Tuple — bind inferred locals to natural names
    // and emit `let (local_X, local_Y, ...) := param_name` as the first do statement.
    let param_ty = value_param_idx.and_then(|i| params.get(i)).map(|p| &p.ty);
    let tuple_fields_opt: Option<&Vec<StyxType>> = param_ty.and_then(|ty| match ty {
        StyxType::Tuple(fs) => Some(fs),
        StyxType::Ref { inner, .. } => match inner.as_ref() {
            StyxType::Tuple(fs) => Some(fs),
            _ => None,
        },
        _ => None,
    });

    // Collect local types from the body to type-match fields
    let mut local_types: std::collections::BTreeMap<u32, StyxType> =
        std::collections::BTreeMap::new();
    collect_local_types(body, &mut local_types);

    // Build tuple destructure: map inferred locals to field indices.
    // When the item type is a tuple, we emit the destructure directly in the
    // `fun` binder (as `fun (local_X, _unused_N) => ...`) instead of via a
    // `let (x, y) := arg1` inside `do`. The latter leaves pattern metavariables
    // that Lean cannot resolve when `ItemT` is inferred through an opaque
    // `core.slice.iter.Iter T` signature. A pattern in the fun binder ties the
    // ItemT type to the destructure directly.
    let mut field_assignments: Vec<(u32, usize)> = Vec::new();
    if let Some(fields) = tuple_fields_opt
        && !inferred_ids.is_empty() {
            let mut used_fields = std::collections::BTreeSet::new();
            for &lid in &inferred_ids {
                if let Some(lt) = local_types.get(&lid) {
                    for (fi, ft) in fields.iter().enumerate() {
                        if !used_fields.contains(&fi) && styx_types_equal(ft, lt) {
                            field_assignments.push((lid, fi));
                            used_fields.insert(fi);
                            break;
                        }
                    }
                }
            }
        }

    // Build the fun-binder pattern. If we have tuple field assignments, emit a
    // direct tuple pattern. Otherwise, fall back to the plain param name.
    let fun_binder = if !field_assignments.is_empty() {
        let parts: Vec<String> = (0..tuple_fields_opt.unwrap().len())
            .map(|fi| {
                field_assignments
                    .iter()
                    .find(|(_, f)| *f == fi)
                    .map(|(lid, _)| format!("local_{}", lid))
                    .unwrap_or_else(|| format!("_unused_{}", fi))
            })
            .collect();
        format!("({})", parts.join(", "))
    } else if let Some(ty) = param_ty {
        format!("({value_param} : {})", super::type_fmt::emit_type(ty))
    } else {
        value_param.clone()
    };

    // Register closure param in LOCAL_NAMES for body emission.
    // Priority: (1) explicit local_id from StyxIR param, (2) tuple field assignments,
    // (3) inferred first undeclared body local.
    let mut saved: Vec<(u32, Option<String>)> = Vec::new();
    let explicit_local_id = value_param_idx
        .and_then(|i| params.get(i))
        .and_then(|p| p.local_id.as_ref())
        .map(|lid| lid.0);
    if let Some(lid) = explicit_local_id {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            let old = m.insert(lid, value_param.clone());
            saved.push((lid, old));
        });
    } else if !field_assignments.is_empty() {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            for &(lid, _fi) in &field_assignments {
                let name = format!("local_{}", lid);
                let old = m.insert(lid, name);
                saved.push((lid, old));
            }
        });
    } else if let Some(&first_id) = inferred_ids.first() {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            let old = m.insert(first_id, value_param.clone());
            saved.push((first_id, old));
        });
    }

    // Emit the closure body in STATEMENT mode.
    let body_str = {
        let mut tmp = crate::emit::indent::IndentWriter::new();
        emit_closure_body_stmts(&mut tmp, body, types);
        tmp.finish()
    };

    // Restore LOCAL_NAMES
    LOCAL_NAMES.with(|map| {
        let mut m = map.borrow_mut();
        for (lid, old) in saved {
            match old {
                Some(n) => {
                    m.insert(lid, n);
                }
                None => {
                    m.remove(&lid);
                }
            }
        }
    });

    // Format: (std.iter.Iterator.{method} [ItemT annotation] iter (fun {binder} => do\n    body_stmts))
    //
    // The inner `do` block's statements are indented 4 spaces (the outer function
    // body sits at indent level 1 = 2 spaces; the inner do needs strictly greater
    // column, and 4 spaces matches existing compiled output).
    //
    // When the item type is a tuple, Lean cannot infer ItemT from the opaque
    // core.slice.iter.Iter IterT return type + a destructured fun binder.
    // Emit `(ItemT := ...)` explicitly to resolve the metavariable.
    let item_ty_annotation = param_ty
        .filter(|_| tuple_fields_opt.is_some())
        .map(|ty| {
            let base = match ty {
                StyxType::Ref { inner, .. } => inner.as_ref(),
                other => other,
            };
            format!(" (ItemT := {})", super::type_fmt::emit_type(base))
        })
        .unwrap_or_default();

    let body_trimmed = body_str.trim_end();
    let body_indented = body_trimmed
        .lines()
        .map(|line| format!("    {line}"))
        .collect::<Vec<_>>()
        .join("\n");
    format!(
        "(std.iter.Iterator.{method_name}{item_ty_annotation} {iter_str} (fun {fun_binder} => do\n{body_indented}))"
    )
}

/// Returns true if the iterator-closure dispatch needs the `do`-block desugaring.
///
/// Fires when either:
/// - the body contains an IndexVec.index call (existing trigger), or
/// - the closure value-param peels to a tuple type (tuple-destructure needed for
///   iterators over `(K, V)` pairs like `RevocationState::iter()`).
pub(crate) fn closure_needs_iter_desugar(params: &[StyxParam], body: &StyxExpr) -> bool {
    if closure_body_has_index(body) {
        return true;
    }
    let is_fn_env = |ty: &StyxType| -> bool {
        match ty {
            StyxType::FnPtr { .. } => true,
            StyxType::Ref { inner, .. } => matches!(inner.as_ref(), StyxType::FnPtr { .. }),
            _ => false,
        }
    };
    let value_param_idx = params.iter().position(|p| !is_fn_env(&p.ty));
    let param_ty = value_param_idx.and_then(|i| params.get(i)).map(|p| &p.ty);
    let is_tuple = match param_ty {
        Some(StyxType::Tuple(_)) => true,
        Some(StyxType::Ref { inner, .. }) => matches!(inner.as_ref(), StyxType::Tuple(_)),
        _ => false,
    };
    if !is_tuple {
        return false;
    }
    // Only desugar tuple params when the body has inferred locals (orphans not
    // in the outer scope). Closures that already destructure via `let (a,b) := arg1`
    // inside their body work fine without do-block routing (e.g., find_oob_read).
    let mut body_locals = std::collections::BTreeSet::new();
    collect_local_ids(body, &mut body_locals);
    let mut body_assigned = std::collections::BTreeSet::new();
    collect_assigned_ids_in_expr(body, &mut body_assigned);
    
    super::body::LOCAL_NAMES.with(|map| {
        let m = map.borrow();
        body_locals.iter().any(|id| !m.contains_key(id) && !body_assigned.contains(id))
    })
}

/// Returns true if `expr` contains any `Index` or `IndexMut` trait method call
/// anywhere in its expression tree (including inside nested closures).
/// Helper: recursively check if a StyxStmt contains any Index call.
pub(crate) fn closure_stmt_has_index(s: &StyxStmt) -> bool {
    match s {
        StyxStmt::Assign { value, .. } => closure_body_has_index(value),
        StyxStmt::FieldAssign { value, .. } => closure_body_has_index(value),
        StyxStmt::Return(e) | StyxStmt::Expr(e) => closure_body_has_index(e),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            closure_body_has_index(cond)
                || then_block.stmts.iter().any(closure_stmt_has_index)
                || else_block.stmts.iter().any(closure_stmt_has_index)
        }
        StyxStmt::Match {
            scrutinee, arms, ..
        } => {
            closure_body_has_index(scrutinee)
                || arms.iter().any(|arm| {
                    arm.guard
                        .as_ref()
                        .is_some_and(closure_body_has_index)
                        || arm.body.stmts.iter().any(closure_stmt_has_index)
                })
        }
        _ => false,
    }
}

pub(crate) fn closure_body_has_index(expr: &StyxExpr) -> bool {
    match &expr.kind {
        StyxExprKind::Call { callee, args, .. } => {
            let is_index = matches!(callee,
                StyxCallee::TraitMethod { trait_path, method_name, .. }
                    if (trait_path.contains("ops::Index") || trait_path.contains("ops::index::Index"))
                        && method_name == "index"
            );
            if is_index {
                return true;
            }
            args.iter().any(closure_body_has_index)
        }
        StyxExprKind::Ref { operand, .. } | StyxExprKind::Deref(operand) => {
            closure_body_has_index(operand)
        }
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            closure_body_has_index(base)
        }
        StyxExprKind::Closure { body, .. } => closure_body_has_index(body),
        StyxExprKind::Block { stmts, expr } => {
            stmts.iter().any(closure_stmt_has_index)
                || expr.as_ref().is_some_and(|e| closure_body_has_index(e))
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            closure_body_has_index(lhs) || closure_body_has_index(rhs)
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::QuestionMark { inner: operand, .. } => closure_body_has_index(operand),
        _ => false,
    }
}

/// Returns true if the expression (stripping Ref/Deref wrappers) is directly
/// an `Index`/`IndexMut` trait method call.
pub(crate) fn is_index_call_expr(expr: &StyxExpr) -> bool {
    match &expr.kind {
        StyxExprKind::Ref { operand, .. } | StyxExprKind::Deref(operand) => {
            is_index_call_expr(operand)
        }
        StyxExprKind::Call { callee, .. } => matches!(callee,
            StyxCallee::TraitMethod { trait_path, method_name, .. }
                if (trait_path.contains("ops::Index") || trait_path.contains("ops::index::Index"))
                    && (method_name == "index" || method_name == "index_mut")
        ),
        _ => false,
    }
}

/// Strip trailing Ref/Deref wrappers from an expression (transparent in Lean).
pub(crate) fn strip_transparent(expr: &StyxExpr) -> &StyxExpr {
    match &expr.kind {
        StyxExprKind::Ref { operand, .. } | StyxExprKind::Deref(operand) => {
            strip_transparent(operand)
        }
        _ => expr,
    }
}

/// Emit the `.some` arm for an Option::map-desugared match.
///
/// `body` is the closure body expression. Strategy:
/// - If the body (after stripping Ref/Deref) is directly an Index call: monadic bind.
///   `do\n  let _omr ← INDEX_CALL\n  ok (.some _omr)`
/// - Otherwise (body is field access / call wrapping an index): use do-notation's
///   ability to process `(← e)` inside expressions.
///   `do\n  ok (.some BODY)`
pub(crate) fn emit_option_map_some_arm(body: &StyxExpr, types: &TypeLookup) -> String {
    let inner = strip_transparent(body);
    if is_index_call_expr(inner) {
        // Emit the index call itself (emit_expr does not add ← here)
        let call_str = emit_expr(inner, types);
        format!("do\n  let _omr ← {call_str}\n  ok (.some _omr)")
    } else {
        // Body has (← IndexCall) inside sub-expressions.
        // Lean 4 do-notation handles (← e) in expression position.
        let body_str = emit_expr(body, types);
        format!("do\n  ok (.some {body_str})")
    }
}

/// Desugar `Option::is_some_and(opt, |param| body_with_indexvec)` into a match expression.
///
/// Lean cannot use `←` inside `fun` binders, so we rewrite:
///   `Option.is_some_and opt (fun P2 => body)`
/// into:
///   `match opt with\n| .none => ok false\n| .some P2 => do ...`
pub(crate) fn emit_option_is_some_and_as_match(
    opt: &StyxExpr,
    params: &[StyxParam],
    body: &StyxExpr,
    types: &TypeLookup,
) -> String {
    let opt_str = emit_expr_lifted(opt, types);

    // Find the value param (skip FnPtr captures)
    let value_param_idx = params
        .iter()
        .position(|p| !matches!(&p.ty, StyxType::FnPtr { .. }));
    let value_param = value_param_idx
        .and_then(|i| params.get(i))
        .map(|p| escape_lean_keyword(&p.name))
        .unwrap_or_else(|| {
            eprintln!("[styx warn] option_is_some_and_as_match: no value param found, falling back to 'idx'");
            "idx".to_string()
        });

    // Infer local_id for param if missing (same pattern as emit_option_map_as_match)
    let mut resolve_id: Option<u32> = None;
    if let Some(idx) = value_param_idx
        && let Some(p) = params.get(idx) {
            if let Some(lid) = &p.local_id {
                resolve_id = Some(lid.0);
            } else {
                let mut body_locals = std::collections::BTreeSet::new();
                collect_local_ids(body, &mut body_locals);
                LOCAL_NAMES.with(|map| {
                    let m = map.borrow();
                    for &id in &body_locals {
                        if !m.contains_key(&id) {
                            resolve_id = Some(id);
                            break;
                        }
                    }
                });
            }
        }

    let mut saved: Option<(u32, Option<String>)> = None;
    if let Some(lid) = resolve_id {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            let old = m.insert(lid, value_param.clone());
            saved = Some((lid, old));
        });
    }

    // Emit the body — it returns a Bool (possibly via IndexVec), so wrap in do
    let some_arm = emit_option_is_some_and_some_arm(body, types);

    // Restore LOCAL_NAMES
    if let Some((lid, old)) = saved {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            match old {
                Some(n) => {
                    m.insert(lid, n);
                }
                None => {
                    m.remove(&lid);
                }
            }
        });
    }

    format!("match {opt_str} with\n| .none => ok false\n| .some {value_param} => {some_arm}")
}

pub(crate) fn emit_option_is_some_and_some_arm(body: &StyxExpr, types: &TypeLookup) -> String {
    let inner = strip_transparent(body);
    if is_index_call_expr(inner) {
        // Body IS an IndexVec call directly — desugar to let-bind then ok bool
        let call_str = emit_expr(inner, types);
        format!("do\n  let _isa ← {call_str}\n  ok _isa")
    } else if matches!(&inner.kind, StyxExprKind::Call { .. }) {
        // Body IS a direct function call returning Result Bool (e.g., holds_cap, Capability::is_valid).
        // emit_expr would produce the bare call; wrapping with ok() would give Result (Result Bool).
        // Instead, bind with ← to extract the Bool, then wrap once with ok.
        let call_str = emit_expr(inner, types);
        format!("do\n  let _isa ← {call_str}\n  ok _isa")
    } else {
        // Body has (← Call) inside sub-expressions — emit with do; Lean handles ← in expression position
        let body_str = emit_expr(body, types);
        format!("do\n  ok {body_str}")
    }
}

/// Desugar `Option::map(opt, |idx| body_with_indexvec)` into a match expression.
///
/// Lean cannot use `←` inside `fun` binders, so we rewrite:
///   `Option.map opt (fun P2 => body)`
/// into:
///   `match opt with\n| .none => ok .none\n| .some P2 => do ...`
pub(crate) fn emit_option_map_as_match(
    opt: &StyxExpr,
    params: &[StyxParam],
    body: &StyxExpr,
    types: &TypeLookup,
) -> String {
    let opt_str = emit_expr_lifted(opt, types);

    // Find the value param (skip FnPtr captures — these are closure env pointers)
    let value_param_idx = params
        .iter()
        .position(|p| !matches!(&p.ty, StyxType::FnPtr { .. }));
    let value_param = value_param_idx
        .and_then(|i| params.get(i))
        .map(|p| escape_lean_keyword(&p.name))
        .unwrap_or_else(|| {
            eprintln!(
                "[styx warn] option_map_as_match: no value param found, falling back to 'idx'"
            );
            "idx".to_string()
        });

    // Register the closure param in LOCAL_NAMES so that Local(id) refs in the body
    // resolve to the correct param name (same logic as the general Closure emitter).
    //
    // Closure params often lack local_id (null in JSON). When that happens,
    // we infer the ID by collecting undeclared Local refs from the body.
    let mut resolve_id: Option<u32> = None;

    if let Some(i) = value_param_idx
        && let Some(p) = params.get(i) {
            if let Some(lid) = &p.local_id {
                resolve_id = Some(lid.0);
            } else {
                // Infer: collect Local IDs in the body not in the outer scope
                let mut body_locals = std::collections::BTreeSet::new();
                collect_local_ids(body, &mut body_locals);
                let mut candidates: Vec<u32> = Vec::new();
                LOCAL_NAMES.with(|map| {
                    let m = map.borrow();
                    for &id in &body_locals {
                        if !m.contains_key(&id) {
                            candidates.push(id);
                        }
                    }
                });
                // Assign the first candidate to this param
                if let Some(&inferred) = candidates.first() {
                    resolve_id = Some(inferred);
                }
            }
        }

    let mut saved: Option<(u32, Option<String>)> = None;
    if let Some(lid) = resolve_id {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            let old = m.insert(lid, value_param.clone());
            saved = Some((lid, old));
        });
    }

    let some_arm = emit_option_map_some_arm(body, types);

    // Restore LOCAL_NAMES
    if let Some((lid, old)) = saved {
        LOCAL_NAMES.with(|map| {
            let mut m = map.borrow_mut();
            match old {
                Some(n) => {
                    m.insert(lid, n);
                }
                None => {
                    m.remove(&lid);
                }
            }
        });
    }

    format!("match {opt_str} with\n| .none => ok .none\n| .some {value_param} => {some_arm}")
}
