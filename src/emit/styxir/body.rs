use std::collections::BTreeSet;
use crate::emit::indent::IndentWriter;
use crate::naming::escape_lean_keyword;
use super::*;

// ---------------------------------------------------------------------------
// Body / statement / expression emission
// ---------------------------------------------------------------------------

/// Thread-local name map for local variables within the current function.
/// Set by `emit_fun_def` before calling `emit_body`.
/// This avoids threading a parameter through 20+ recursive emit functions.
std::thread_local! {
    pub(crate) static LOCAL_NAMES: std::cell::RefCell<std::collections::HashMap<u32, String>>
        = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Thread-local set of function parameter local IDs for the current function.
/// Used to exclude function parameters from option-condition payload detection:
/// a parameter can be referenced in a then-block but is NOT the pattern-bound payload.
std::thread_local! {
    pub(crate) static PARAM_IDS: std::cell::RefCell<std::collections::HashSet<u32>>
        = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Thread-local table of locals seen in the current function body.
/// Stores (LocalId, StyxType) pairs accumulated during loop state collection.
/// Populated on demand when collect_modified_locals_loop encounters an Assign
/// or rebind pattern — so types are available for the `go` function signature.
std::thread_local! {
    pub(crate) static BODY_LOCALS: std::cell::RefCell<std::collections::HashMap<u32, StyxType>>
        = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Register the type of a local variable in the body-locals table.
pub(crate) fn register_local_type(id: u32, ty: StyxType) {
    BODY_LOCALS.with(|bl| {
        bl.borrow_mut().insert(id, ty);
    });
}

/// Set the body-locals table from the StyxBody.locals list (covers parameters).
pub(crate) fn set_body_locals(locals: Vec<(u32, String, StyxType)>) {
    BODY_LOCALS.with(|bl| {
        let mut map = bl.borrow_mut();
        map.clear();
        for (id, _, ty) in locals {
            map.insert(id, ty);
        }
    });
}

/// Look up the StyxType of a local variable by its raw id.
pub(crate) fn local_type(id: u32) -> Option<StyxType> {
    BODY_LOCALS.with(|bl| bl.borrow().get(&id).cloned())
}

/// Thread-local set of locals that are in scope at the current emission point.
/// Updated as each Assign stmt is emitted so that Loop state collection can
/// filter out loop-internal temporaries (first assigned inside the loop body).
///
/// Only variables in this set when a Loop is encountered are eligible as
/// loop-carried state parameters in the generated `go_N` function.
std::thread_local! {
    pub(crate) static IN_SCOPE_LOCALS: std::cell::RefCell<std::collections::HashSet<u32>>
        = std::cell::RefCell::new(std::collections::HashSet::new());
}

/// Mark a local as in-scope (called when `let local_N := ...` is emitted).
pub(crate) fn mark_in_scope(id: u32) {
    IN_SCOPE_LOCALS.with(|s| {
        s.borrow_mut().insert(id);
    });
}

/// Returns true if local `id` is in scope at the current emission point.
pub(crate) fn is_in_scope(id: u32) -> bool {
    IN_SCOPE_LOCALS.with(|s| s.borrow().contains(&id))
}

/// Thread-local stack of active loop contexts (for break/continue translation).
pub(crate) struct LoopCtx {
    pub go_name: String,
    /// Names of the loop-carried state variables (order matches the go signature).
    pub state_args: Vec<String>,
}

std::thread_local! {
    pub(crate) static LOOP_CONTEXT: std::cell::RefCell<Vec<LoopCtx>>
        = const { std::cell::RefCell::new(Vec::new()) };
}

/// Pending call-site info for a for-in error-channel loop.
/// Set by emit_stmt(Loop) when it detects an error-channel for-in loop.
/// Consumed by emit_block_stmts, which emits the error-propagating match
/// and wraps the remaining stmts in the `.Ok` arm.
pub(crate) struct ForIterErrorPending {
    pub go_name: String,
    pub args_call: String,
    pub state_names: Vec<String>,
}

std::thread_local! {
    pub(crate) static FOR_ITER_ERROR_PENDING: std::cell::RefCell<Option<ForIterErrorPending>>
        = const { std::cell::RefCell::new(None) };
}

/// When a for-in error-channel Loop is nested inside a Match arm body and the arm body
/// has no remaining stmts after the Loop, the continuation stmts live one level up (in
/// the outer Expr(Block)/Return(Block)/Assign flatten loop). Those loops pre-load this
/// thread-local with the stmts that follow the current stmt so that emit_block_stmts can
/// inject them into the .Ok arm of the error-propagating match.
std::thread_local! {
    pub(crate) static FOR_ITER_OUTER_CONT: std::cell::RefCell<Option<Vec<crate::ir::StyxStmt>>>
        = const { std::cell::RefCell::new(None) };
    /// Set to true when FOR_ITER_OUTER_CONT was consumed by emit_block_stmts; read and
    /// cleared by the outer flatten loop so it knows to stop emitting further stmts.
    pub(crate) static FOR_ITER_OUTER_CONT_USED: std::cell::RefCell<bool>
        = const { std::cell::RefCell::new(false) };
}

/// Counter for generating unique `go_N` names within a single function body.
/// Reset to 0 at the start of each `emit_body` call.
static LOOP_COUNTER: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Look up the name for a local variable by its LocalId.
/// Falls back to "local_{id}" if no mapping exists.
pub(crate) fn local_name(id: u32) -> String {
    LOCAL_NAMES.with(|map| {
        map.borrow()
            .get(&id)
            .cloned()
            .unwrap_or_else(|| format!("local_{id}"))
    })
}

/// Returns true if the given local ID belongs to a function parameter (not a pattern-bound local).
pub(crate) fn is_param_id(id: u32) -> bool {
    PARAM_IDS.with(|set| set.borrow().contains(&id))
}

/// Set the local name map for the current function emission scope.
pub(crate) fn set_local_names(names: std::collections::HashMap<u32, String>) {
    LOCAL_NAMES.with(|map| {
        *map.borrow_mut() = names;
    });
}

/// Set the parameter ID set for the current function emission scope.
pub(crate) fn set_param_ids(ids: std::collections::HashSet<u32>) {
    PARAM_IDS.with(|set| {
        *set.borrow_mut() = ids;
    });
}

/// Detect a for-in iterator loop shape inside a Loop(cond=None) body.
///
/// styx-rustc encodes for-in loops as one of:
///   a) [pre..., Match(Iterator::next(iter)) { None=>exit, Some(x)=>body }]
///   b) [Return(Block { [pre..., Match(Iterator::next)] })]  (common wrapper)
///   c) [Expr(Block { [pre..., Match(Iterator::next)] })]    (alternate wrapper)
///
/// Returns (pre_stmts, scrutinee, none_arm, some_arm) on success.
/// The caller emits pre_stmts nontail, then handles the match itself:
///   none_arm → emit_exit (loop exit with final state)
///   some_arm → emit nontail body + emit_continue (recurse)
fn detect_for_iter_loop(
    body: &StyxBlock,
) -> Option<(&[StyxStmt], &StyxExpr, &StyxMatchArm, &StyxMatchArm)> {
    // Extract the effective stmts: unwrap one level of Return/Expr(Block) if present.
    let effective_stmts: &[StyxStmt] = if body.stmts.len() == 1 {
        match &body.stmts[0] {
            StyxStmt::Return(expr) | StyxStmt::Expr(expr) => {
                if let StyxExprKind::Block { stmts, expr: block_tail } = &expr.kind {
                    if block_tail.is_none() { stmts } else { &body.stmts }
                } else {
                    &body.stmts
                }
            }
            _ => &body.stmts,
        }
    } else {
        &body.stmts
    };

    // The Match must be the last stmt in effective_stmts
    let last_idx = effective_stmts.len().checked_sub(1)?;
    let StyxStmt::Match { scrutinee, arms } = &effective_stmts[last_idx] else {
        return None;
    };
    // Scrutinee must be an Iterator::next call
    let StyxExprKind::Call { callee, .. } = &scrutinee.kind else { return None; };
    if !matches!(callee, StyxCallee::TraitMethod { method_name, .. } if method_name == "next") {
        return None;
    }
    // Must have exactly 2 arms (None and Some)
    if arms.len() != 2 {
        return None;
    }
    // Identify None arm (variant_id 0) and Some arm (variant_id 1)
    let arm0 = &arms[0];
    let arm1 = &arms[1];
    let variant_id_of = |arm: &StyxMatchArm| -> Option<u32> {
        if let StyxPattern::Variant { variant_id, .. } = &arm.pattern {
            Some(variant_id.0)
        } else {
            None
        }
    };
    let (none_arm, some_arm) = match (variant_id_of(arm0), variant_id_of(arm1)) {
        (Some(0), Some(1)) => (arm0, arm1),
        (Some(1), Some(0)) => (arm1, arm0),
        _ => return None,
    };
    // None arm must be a loop exit: empty body OR contains Break(0)
    // None arm must be a loop exit: empty body, direct Break(0),
    // or Break(0) wrapped in Return(Block{...}) — styx-rustc's common encoding.
    let stmt_contains_break = |s: &StyxStmt| -> bool {
        if matches!(s, StyxStmt::Break { depth: 0 }) { return true; }
        if let StyxStmt::Return(expr) = s
            && let StyxExprKind::Block { stmts, .. } = &expr.kind {
                return stmts.iter().any(|s2| matches!(s2, StyxStmt::Break { depth: 0 }));
            }
        false
    };
    let none_is_exit = none_arm.body.stmts.is_empty()
        || none_arm.body.stmts.iter().any(stmt_contains_break);
    if !none_is_exit {
        return None;
    }
    let pre_stmts = &effective_stmts[..last_idx];
    Some((pre_stmts, scrutinee, none_arm, some_arm))
}

/// Extract the item type T from `Option<T>` or `Option<&T>` (reference erased).
/// Used to annotate the `.some` binding in for-in loop emission so Lean can
/// resolve field accesses on struct items (e.g., `local_19.source`).
/// `std.iter.Iterator.next` has both `{IterT ItemT}` as implicit — Lean can't
/// infer `ItemT` from the opaque iterator type, so we provide the annotation.
fn option_item_ty(ty: &StyxType) -> Option<&StyxType> {
    if let StyxType::Adt { rust_path, generic_args, .. } = ty
        && rust_path.contains("option::Option") {
            // Return the first generic arg (the item type, possibly a &T ref)
            return generic_args.first();
        }
    None
}

/// Scan stmts for a `core::result::Result<T, E>` typed expression in an early-return
/// position (Assign(MAX) or Return). Returns the error type E if found.
/// Used to detect error-channel for-in loops before emitting the go_N signature.
fn find_result_err_ty_in_stmts(stmts: &[StyxStmt]) -> Option<StyxType> {
    stmts.iter().find_map(find_result_err_ty_in_stmt)
}

fn find_result_err_ty_in_stmt(stmt: &StyxStmt) -> Option<StyxType> {
    match stmt {
        StyxStmt::Assign { target, value, .. } if target.0 == u32::MAX => {
            find_result_err_ty_in_expr(value)
        }
        StyxStmt::Return(expr) => find_result_err_ty_in_expr(expr),
        StyxStmt::Expr(expr) => find_result_err_ty_in_expr(expr),
        StyxStmt::If { then_block, else_block, .. } => {
            find_result_err_ty_in_stmts(&then_block.stmts)
                .or_else(|| find_result_err_ty_in_stmts(&else_block.stmts))
        }
        StyxStmt::Match { arms, .. } => {
            arms.iter().find_map(|arm| find_result_err_ty_in_stmts(&arm.body.stmts))
        }
        _ => None,
    }
}

fn find_result_err_ty_in_expr(expr: &StyxExpr) -> Option<StyxType> {
    // Path 1: expr.ty carries generic_args — works when styx-rustc includes them.
    if let StyxType::Adt { rust_path, generic_args, .. } = &expr.ty
        && rust_path.contains("result::Result") && generic_args.len() == 2 {
            return Some(generic_args[1].clone());
        }
    // Path 2: EnumInit with variant_id==1 (Err) and one field.
    // Works even when generic_args is empty (external type): the field's own type IS E.
    if let StyxExprKind::EnumInit { variant_id, fields, .. } = &expr.kind
        && variant_id.0 == 1 && fields.len() == 1
            && let StyxType::Adt { rust_path, .. } = &expr.ty
                && rust_path.contains("result::Result") {
                    return Some(fields[0].1.ty.clone());
                }
    // Path 3: recurse into Block expressions (handles Block{[Assign(MAX, EnumInit)]} wrappers).
    if let StyxExprKind::Block { stmts, expr: tail } = &expr.kind {
        if let Some(ty) = find_result_err_ty_in_stmts(stmts) {
            return Some(ty);
        }
        if let Some(e) = tail {
            return find_result_err_ty_in_expr(e);
        }
    }
    None
}

pub(crate) fn emit_body(w: &mut IndentWriter, body: &StyxBody, types: &TypeLookup) {
    // Seed BODY_LOCALS from the declared parameter locals.
    let locals_seed: Vec<(u32, String, StyxType)> = body
        .locals
        .iter()
        .map(|l| (l.id.0, l.name.clone(), l.ty.clone()))
        .collect();
    set_body_locals(locals_seed);
    // Pre-scan the entire body to register all Assign target types in BODY_LOCALS.
    // This ensures loop state collection (collect_modified_locals_loop) can look up
    // the correct type for any local, including temporaries like loop counters that
    // are initialized before the loop (`let local_11 := 0#usize`).
    prescan_assign_types(&body.block.stmts);
    // Reset per-function loop counter so go_0, go_1, … are reused across functions.
    LOOP_COUNTER.store(0, std::sync::atomic::Ordering::Relaxed);
    // Seed IN_SCOPE_LOCALS from function parameters so they're available as loop state.
    IN_SCOPE_LOCALS.with(|s| {
        let mut scope = s.borrow_mut();
        scope.clear();
        for l in &body.locals {
            scope.insert(l.id.0);
        }
    });
    emit_block_stmts(w, &body.block, types);
}

/// Walk all statements in the block (and recursively nested blocks) to register
/// the StyxType of every directly-assigned local in BODY_LOCALS.
/// This must be called before any emit_stmt(Loop) so that go_N signatures are typed.
fn prescan_assign_types(stmts: &[StyxStmt]) {
    for stmt in stmts {
        match stmt {
            StyxStmt::Assign { target, value, .. } if target.0 != u32::MAX => {
                register_local_type(target.0, value.ty.clone());
                prescan_assign_types_in_expr(value);
            }
            StyxStmt::Expr(e) => {
                prescan_assign_types_in_expr(e);
            }
            StyxStmt::Return(e) => {
                prescan_assign_types_in_expr(e);
            }
            StyxStmt::If { then_block, else_block, .. } => {
                prescan_assign_types(&then_block.stmts);
                prescan_assign_types(&else_block.stmts);
            }
            StyxStmt::Match { arms, .. } => {
                for arm in arms {
                    prescan_assign_types(&arm.body.stmts);
                }
            }
            StyxStmt::Loop { body, .. } => {
                prescan_assign_types(&body.stmts);
            }
            _ => {}
        }
    }
}

fn prescan_assign_types_in_expr(expr: &StyxExpr) {
    if let StyxExprKind::Block { stmts, expr: tail } = &expr.kind {
        prescan_assign_types(stmts);
        if let Some(e) = tail {
            prescan_assign_types_in_expr(e);
        }
    }
}

/// Emit a block as an inline expression string (for use in if/match arms within expressions).
pub(crate) fn emit_block_inline(block: &StyxBlock, types: &TypeLookup) -> String {
    if block.stmts.is_empty() {
        return "()".to_string();
    }
    // Single Return statement — just emit the expression
    if block.stmts.len() == 1
        && let StyxStmt::Return(e) = &block.stmts[0] {
            return emit_expr(e, types);
        }
    // For complex blocks, wrap in do notation
    // Build: (do let x ← e1; let y ← e2; result)
    let fake_block = StyxExpr {
        kind: StyxExprKind::Block {
            stmts: block.stmts.clone(),
            expr: None,
        },
        ty: StyxType::Unit,
        span: StyxSpan::default(),
    };
    emit_expr(&fake_block, types)
}

pub(crate) fn emit_block_stmts(w: &mut IndentWriter, block: &StyxBlock, types: &TypeLookup) {
    if block.stmts.is_empty() {
        w.writeln("ok ()");
        return;
    }
    let mut i = 0;
    while i < block.stmts.len() {
        let is_last = i == block.stmts.len() - 1;
        let has_remaining_after = i + 1 < block.stmts.len();
        // Pre-load outer continuation ONLY when stmts follow the current one.
        // Crucially, when there are NO following stmts, we leave FOR_ITER_OUTER_CONT
        // unchanged so that an outer context's pre-load (for the enclosing block) stays
        // visible to any inner arm body that needs it.
        if has_remaining_after {
            FOR_ITER_OUTER_CONT.with(|c| {
                *c.borrow_mut() = Some(block.stmts[i + 1..].to_vec());
            });
        }
        emit_stmt(w, &block.stmts[i], is_last, types);
        i += 1;
        if has_remaining_after {
            FOR_ITER_OUTER_CONT.with(|c| *c.borrow_mut() = None);
        }
        // If a nested arm body consumed FOR_ITER_OUTER_CONT, those stmts were already
        // emitted inside the match arm — stop processing this block (and consume the flag).
        let cont_used = FOR_ITER_OUTER_CONT_USED.with(|u| {
            let v = *u.borrow();
            *u.borrow_mut() = false;
            v
        });
        if cont_used {
            return;
        }
        // Check if a for-in error-channel loop set the pending call site.
        // If so, emit the error-propagating match and wrap remaining stmts inside .Ok arm.
        let pending = FOR_ITER_ERROR_PENDING.with(|p| p.borrow_mut().take());
        if let Some(pending) = pending {
            let remaining = &block.stmts[i..];
            if remaining.is_empty() {
                // Loop was the last stmt in this block; check if an outer context
                // pre-loaded continuation stmts for the enclosing block level.
                let outer = FOR_ITER_OUTER_CONT.with(|c| c.borrow_mut().take());
                if let Some(outer_stmts) = outer {
                    emit_for_iter_error_callsite(w, &pending, &outer_stmts, types);
                    FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow_mut() = true);
                } else {
                    emit_for_iter_error_callsite(w, &pending, &[], types);
                }
            } else {
                emit_for_iter_error_callsite(w, &pending, remaining, types);
            }
            return;
        }
    }
}

/// Emit the call site for a for-in error-channel loop.
/// Emits:
///   let for_res ← go_N [args]
///   match for_res with
///   | .Ok [state] => do
///     <remaining_stmts>
///   | .Err for_err_e => ok (.Err for_err_e)
fn emit_for_iter_error_callsite(
    w: &mut IndentWriter,
    pending: &ForIterErrorPending,
    remaining_stmts: &[StyxStmt],
    types: &TypeLookup,
) {
    let call = if pending.args_call.is_empty() {
        pending.go_name.clone()
    } else {
        format!("{} {}", pending.go_name, pending.args_call)
    };
    w.writeln(format!("let for_res \u{2190} {call}"));
    let ok_pat = if pending.state_names.is_empty() {
        "_".to_string()
    } else if pending.state_names.len() == 1 {
        pending.state_names[0].clone()
    } else {
        format!("({})", pending.state_names.join(", "))
    };
    w.writeln("match for_res with");
    // Use fully-qualified constructors to avoid collision with the open Aeneas Result
    // namespace where .Ok/.Err are ambiguous (Lean picks Aeneas.Result.ok/fail instead
    // of core.result.Result.Ok/Err, causing a type mismatch in the match expression).
    w.writeln(format!("| core.result.Result.Ok {ok_pat} => do"));
    w.indent();
    w.indent();
    if remaining_stmts.is_empty() {
        w.writeln("ok ()");
    } else {
        for (j, stmt) in remaining_stmts.iter().enumerate() {
            let is_last = j == remaining_stmts.len() - 1;
            emit_stmt(w, stmt, is_last, types);
        }
    }
    w.dedent();
    w.dedent();
    w.writeln("| core.result.Result.Err for_err_e => ok (core.result.Result.Err for_err_e)");
}

/// Emit a block's statements with all stmts forced to non-last position.
/// Used inside loop bodies where a `go_N` call follows all body stmts,
/// so no stmt is the tail-returning position.
/// NOTE: Does NOT check FOR_ITER_ERROR_PENDING — used inside go_N bodies.
fn emit_block_stmts_nontail(w: &mut IndentWriter, block: &StyxBlock, types: &TypeLookup) {
    for stmt in &block.stmts {
        emit_stmt(w, stmt, false, types);
    }
    // Empty block: emit nothing (the go_N call that follows acts as the body return).
}

/// Check if an expression is a function call (returns Result in monadic context).
/// Non-call expressions are pure and should use `:=` instead of `←` in do-blocks.
pub(crate) fn is_monadic_expr(expr: &StyxExpr) -> bool {
    // Clone calls are simplified to their argument by emit_expr (identity in functional semantics).
    // Propagate monadicness through the clone: if the arg is pure, clone is pure.
    // e.g., Clone::clone(self.resources) → self.resources (pure field), so use := not ←.
    if let StyxExprKind::Call { callee, args, .. } = &expr.kind
        && args.len() == 1
            && (matches!(callee,
                StyxCallee::TraitMethod { trait_path, method_name, .. }
                    if method_name == "clone" && (trait_path.contains("clone::Clone") || trait_path.contains("Clone"))
            ) || matches!(callee,
                StyxCallee::Function { rust_path, .. }
                    if rust_path.contains("clone::Clone::clone") || rust_path.contains("Clone::clone")
            ))
        {
            return is_monadic_expr(&args[0]);
        }
    matches!(&expr.kind, StyxExprKind::Call { .. }) || is_monadic_binop(expr)
}

/// Check if a BinOp is a monadic operation (arithmetic/shift on UScalar/IScalar).
/// Aeneas defines HAdd/HSub/HMul/HDiv/HRem/HShiftLeft/HShiftRight for UScalar/IScalar
/// to return `Result UScalar`/`Result IScalar` (because they can overflow/fail).
/// Bitwise (BitAnd/BitOr/BitXor) and comparisons (Eq/Lt/Le/etc.) return values directly.
pub(crate) fn is_monadic_binop(expr: &StyxExpr) -> bool {
    if let StyxExprKind::BinOp { op, lhs, .. } = &expr.kind {
        let is_arith = matches!(
            op,
            StyxBinOp::Add
                | StyxBinOp::Sub
                | StyxBinOp::Mul
                | StyxBinOp::Div
                | StyxBinOp::Rem
                | StyxBinOp::Shl
                | StyxBinOp::Shr
        );
        if !is_arith {
            return false;
        }
        // Check operand is a UScalar/IScalar (not Bool, Char, etc.)
        match scalar_of_ty(&lhs.ty) {
            Some(s) => is_unsigned_scalar(&s) || is_signed_scalar(&s),
            None => false,
        }
    } else {
        false
    }
}

/// Check if a block's statements contain an If that requires statement-level handling.
/// Forces the outer Block to be flattened so emit_stmt processes the If directly.
///
/// Patterns:
///   `If { then: [Return(..)], else: empty }` — direct early return
///   `If { then: [Assign { target: MAX, .. }], else: empty }` — return via slot assignment
///   `If { cond: Option<T>, else: empty }` — if-let-Some (needs match, not if)
///
/// The Option-condition pattern must be handled by emit_stmt (not the inline emit_expr
/// Block handler) so that the multi-line match statement can be emitted correctly.
pub(crate) fn block_has_early_return_if(stmts: &[StyxStmt]) -> bool {
    stmts.iter().any(|s| {
        if let StyxStmt::If {
            cond,
            then_block,
            else_block,
        } = s
        {
            // Option-condition pattern: always needs match emission regardless of else emptiness.
            // `if let Some(x) = fn() { ... } else { ... }` must become match on Option, not if.
            let is_option_cond = matches!(&cond.ty,
                StyxType::Adt { rust_path, .. }
                    if rust_path == "std::option::Option" || rust_path == "core::option::Option"
            );
            if is_option_cond {
                return true;
            }
            // Early-return patterns only apply when else is empty
            if !else_block.stmts.is_empty() {
                return false;
            }
            then_block.stmts.iter().any(|ts| {
                matches!(ts, StyxStmt::Return(_))
                    || matches!(ts, StyxStmt::Assign { target, .. } if target.0 == u32::MAX)
            })
        } else {
            false
        }
    })
}

pub(crate) fn block_has_loop(stmts: &[StyxStmt]) -> bool {
    stmts.iter().any(|s| match s {
        StyxStmt::Loop { .. } => true,
        StyxStmt::Match { arms, .. } => {
            arms.iter().any(|arm| block_has_loop(&arm.body.stmts))
        }
        StyxStmt::If { then_block, else_block, .. } => {
            block_has_loop(&then_block.stmts) || block_has_loop(&else_block.stmts)
        }
        StyxStmt::Return(expr) => {
            if let StyxExprKind::Block { stmts: inner, .. } = &expr.kind {
                block_has_loop(inner)
            } else {
                false
            }
        }
        StyxStmt::Expr(expr) => {
            if let StyxExprKind::Block { stmts: inner, .. } = &expr.kind {
                block_has_loop(inner)
            } else {
                false
            }
        }
        _ => false,
    })
}

fn arm_has_non_inline_stmt(stmts: &[StyxStmt]) -> bool {
    stmts.iter().any(|s| match s {
        StyxStmt::FieldAssign { .. } | StyxStmt::Loop { .. }
        | StyxStmt::Break { .. } | StyxStmt::Continue { .. } => true,
        StyxStmt::Return(expr) => {
            if let StyxExprKind::Block { stmts: inner, .. } = &expr.kind {
                inner.iter().any(|s| matches!(s, StyxStmt::Break { .. } | StyxStmt::Continue { .. }))
            } else {
                false
            }
        }
        StyxStmt::Match { arms, .. } => {
            arms.iter().any(|arm| arm_has_non_inline_stmt(&arm.body.stmts))
        }
        _ => false,
    })
}

pub(crate) fn block_has_match_needing_do(stmts: &[StyxStmt]) -> bool {
    stmts.iter().any(|s| match s {
        StyxStmt::Match { arms, .. } => {
            arms.iter().any(|arm| arm_has_non_inline_stmt(&arm.body.stmts))
        }
        _ => false,
    })
}

/// Returns true if any statement in the block is an If that requires statement-level handling.
/// Used by Return/Assign/Expr flatten logic: If stmts that contain monadic expressions (← calls)
/// need emit_stmt(If) not inline emit_expr so that do-notation with `←` inside arms works.
///
/// Pure Ifs (e.g., `if a > b { 1 } else { 0 }`) can be emitted inline and should NOT
/// trigger flattening — doing so loses the binding variable when used as an Assign value.
pub(crate) fn block_has_if(stmts: &[StyxStmt]) -> bool {
    stmts.iter().any(|s| {
        if let StyxStmt::If { cond, then_block, else_block } = s {
            // The If needs statement-level handling if:
            // 1. Condition is monadic (function call returning Result Bool)
            // 2. Any branch contains a monadic expression (← call inside the branch)
            if is_monadic_expr(cond) {
                return true;
            }
            block_branch_has_monadic(then_block) || block_branch_has_monadic(else_block)
        } else {
            false
        }
    })
}

/// Returns true if the block contains any statement that requires `←` binding
/// (i.e., contains a monadic expression). Used by block_has_if to determine
/// whether an If needs statement-level vs. inline expression emission.
fn block_branch_has_monadic(block: &StyxBlock) -> bool {
    block.stmts.iter().any(|s| match s {
        StyxStmt::Assign { value, .. } => is_monadic_expr(value),
        StyxStmt::Expr(e) => is_monadic_expr(e),
        StyxStmt::Return(e) => is_monadic_expr(e),
        StyxStmt::If { cond, then_block, else_block } => {
            is_monadic_expr(cond)
                || block_branch_has_monadic(then_block)
                || block_branch_has_monadic(else_block)
        }
        _ => false,
    })
}

/// Collect all local IDs that are assigned (written) inside a loop body.
/// Used to determine loop-carried state for the `go` function signature.
/// Excludes the return slot (u32::MAX) — it is never a loop-state variable.
fn collect_modified_locals_loop(stmts: &[StyxStmt], out: &mut BTreeSet<u32>) {
    for stmt in stmts {
        match stmt {
            StyxStmt::Assign { target, value, .. } if target.0 != u32::MAX => {
                out.insert(target.0);
                // Register the local's type from the assigned value.
                register_local_type(target.0, value.ty.clone());
                // Also recurse into the value expression for nested Block assignments.
                collect_modified_in_expr(value, out);
            }
            StyxStmt::FieldAssign { target, value, .. } => {
                out.insert(target.0);
                collect_modified_in_expr(value, out);
            }
            StyxStmt::Expr(expr) => {
                collect_modified_in_expr(expr, out);
            }
            StyxStmt::Return(expr) => {
                collect_modified_in_expr(expr, out);
            }
            StyxStmt::If {
                then_block,
                else_block,
                ..
            } => {
                collect_modified_locals_loop(&then_block.stmts, out);
                collect_modified_locals_loop(&else_block.stmts, out);
            }
            StyxStmt::Match { arms, .. } => {
                for arm in arms {
                    collect_modified_locals_loop(&arm.body.stmts, out);
                }
            }
            StyxStmt::Loop { body, .. } => {
                collect_modified_locals_loop(&body.stmts, out);
            }
            _ => {}
        }
    }
}

/// Recursively collect modified locals from an expression.
///
/// Two key patterns:
///
/// 1. Explicit assign:   `Expr(Block { [Assign(N, expr)], expr: None })`
///    Target N is directly written.
///
/// 2. "Rebind" pattern:  `Expr(Block { [Assign(MAX, computed_val)], expr: Some(Local(N)) })`
///    styx-rustc encodes `local_N = computed_val` as a Block that stores the result in the
///    return slot (MAX) and returns Local(N) as the Block expression. The Block's tail Local
///    is the variable being "updated" — it IS the loop-carried state variable.
///    We also register the local's type (= the Block's own type) in BODY_LOCALS so that
///    emit_stmt(Loop) can emit a typed signature for go_N.
fn collect_modified_in_expr(expr: &StyxExpr, out: &mut BTreeSet<u32>) {
    if let StyxExprKind::Block { stmts, expr: tail } = &expr.kind {
        // Detect rebind pattern: Block { [Assign(MAX, value)], expr: Some(Local(N)) }
        // This encodes `local_N = value` — N is the modified local.
        // The tail Local's own .ty carries the correct type for N.
        if stmts.len() == 1
            && let StyxStmt::Assign { target, .. } = &stmts[0]
                && target.0 == u32::MAX
                    && let Some(tail_expr) = tail
                        && let StyxExprKind::Local(lid) = &tail_expr.kind {
                            out.insert(lid.0);
                            // Register N's type from the Local expression's own type,
                            // which is always correct (the BinOp value is typed Unit
                            // in this context, but the Local ref preserves the actual type).
                            register_local_type(lid.0, tail_expr.ty.clone());
                        }
        // Also recurse into stmts for any nested patterns.
        collect_modified_locals_loop(stmts, out);
        if let Some(e) = tail {
            collect_modified_in_expr(e, out);
        }
    }
}

/// Unwrap the styx-rustc return-block pattern:
///   Return(Block { stmts: [Assign(MAX, inner_value)], expr: Some(unit) })
/// Returns (actual_expr, emitted_string) where actual_expr is the inner value expr
/// and emitted_string is emit_expr(actual_expr). Falls back to emit_expr(ret_expr)
/// if the pattern doesn't match.
pub(crate) fn unwrap_return_block<'a>(ret_expr: &'a StyxExpr, types: &TypeLookup) -> (&'a StyxExpr, String) {
    if let StyxExprKind::Block { stmts, .. } = &ret_expr.kind
        && stmts.len() == 1 {
            // Pattern 1: Block { [Assign(MAX, value)], expr: unit }
            if let StyxStmt::Assign { target, value, .. } = &stmts[0]
                && target.0 == u32::MAX {
                    return (value, emit_expr(value, types));
                }
            // Pattern 2: Block { [Expr(value)], expr: unit }
            // styx-rustc sometimes wraps return values as Expr instead of Assign(MAX)
            if let StyxStmt::Expr(inner) = &stmts[0] {
                return (inner, emit_expr(inner, types));
            }
        }
    (ret_expr, emit_expr(ret_expr, types))
}

pub(crate) fn emit_stmt(w: &mut IndentWriter, stmt: &StyxStmt, is_last: bool, types: &TypeLookup) {
    match stmt {
        StyxStmt::Assign { target, value, .. } => {
            // Flatten blocks with early-return Ifs, loops, or any If into do-notation.
            // Without flattening, loops or Ifs nested inside Assign value expressions route
            // through emit_expr which emits `sorry /- loop -/` or invalid `←` inside non-do.
            if let StyxExprKind::Block { stmts, expr } = &value.kind
                && (block_has_early_return_if(stmts) || block_has_loop(stmts) || block_has_if(stmts) || block_has_match_needing_do(stmts)) {
                    let total = stmts.len();
                    for (i, s) in stmts.iter().enumerate() {
                        let block_last = i == total - 1 && expr.is_none();
                        let has_cont = i + 1 < total;
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| {
                                *c.borrow_mut() = Some(stmts[i + 1..].to_vec());
                            });
                        }
                        emit_stmt(w, s, is_last && block_last, types);
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| *c.borrow_mut() = None);
                        }
                        // Read-only check: don't reset USED so the outer emit_block_stmts
                        // can also detect it and stop processing its remaining stmts.
                        let cont_used = FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow());
                        if cont_used {
                            return;
                        }
                    }
                    if let Some(e) = expr {
                        if is_last {
                            let v = emit_expr(e, types);
                            if is_monadic_expr(e) {
                                w.writeln(v);
                            } else {
                                w.writeln(format!("ok {v}"));
                            }
                        } else if target.0 != u32::MAX {
                            let v = emit_expr(e, types);
                            let bind = if is_monadic_expr(e) { "←" } else { ":=" };
                            let name = local_name(target.0);
                            w.writeln(format!("let {name} {bind} {v}"));
                            LOCAL_NAMES.with(|map| {
                                map.borrow_mut().insert(target.0, name);
                            });
                            mark_in_scope(target.0);
                        }
                    }
                    return;
                }
            let val = emit_expr(value, types);
            let bind = if is_monadic_expr(value) { "←" } else { ":=" };
            if is_last {
                if is_monadic_expr(value) {
                    // Monadic call at tail position — emit directly (it returns Result)
                    w.writeln(val);
                } else {
                    w.writeln(format!("ok {val}"));
                }
            } else if target.0 == u32::MAX {
                // Detect early-return pattern: `let _ := (.Err ...)` or `let _ := (.Ok ...)`
                // This comes from Rust's `return Err(e)` / `return Ok(v)` in non-tail position.
                // In Lean do-blocks, `return` exits the entire function.
                if val.starts_with("(.Err") || val.starts_with("(.Ok") {
                    w.writeln(format!("return ok {val}"));
                } else {
                    w.writeln(format!("let _ {bind} {val}"));
                }
            } else {
                let name = local_name(target.0);
                w.writeln(format!("let {name} {bind} {val}"));
                LOCAL_NAMES.with(|map| {
                    map.borrow_mut().insert(target.0, name);
                });
                mark_in_scope(target.0);
            }
        }
        StyxStmt::Expr(expr) => {
            // Flatten blocks with early-return Ifs, loops, or any If into do-notation.
            // The StyxIR represents `if cond { return Err(...) }` as:
            //   Expr(Block { stmts: [If { then: [Assign(MAX, .Err)], else: [] }], expr: () })
            // Without flattening, this becomes `let _ := (if cond then (.Err e) else ())` which
            // doesn't actually return. With flattening, the If is processed by emit_stmt which
            // correctly emits `return ok (.Err ...)`.
            // Loops nested inside Expr(Block) also need flattening so emit_stmt(Loop) fires.
            // Any If in a block needs flattening so `←` inside arms works in do-notation.
            if let StyxExprKind::Block {
                stmts,
                expr: blk_expr,
            } = &expr.kind
                && (block_has_early_return_if(stmts) || block_has_loop(stmts) || block_has_if(stmts) || block_has_match_needing_do(stmts)) {
                    let total = stmts.len();
                    for (i, s) in stmts.iter().enumerate() {
                        let block_last = i == total - 1 && blk_expr.is_none();
                        let has_cont = i + 1 < total;
                        // Pre-load outer continuation only when stmts follow; never overwrite
                        // with None so an outer context's pre-load stays visible to inner calls.
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| {
                                *c.borrow_mut() = Some(stmts[i + 1..].to_vec());
                            });
                        }
                        emit_stmt(w, s, is_last && block_last, types);
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| *c.borrow_mut() = None);
                        }
                        // Read-only check: don't reset USED so the outer emit_block_stmts
                        // can also detect it and stop processing its remaining stmts.
                        let cont_used = FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow());
                        if cont_used {
                            return;
                        }
                    }
                    if let Some(e) = blk_expr
                        && is_last {
                            let v = emit_expr(e, types);
                            if is_monadic_expr(e) {
                                w.writeln(v);
                            } else {
                                w.writeln(format!("ok {v}"));
                            }
                        }
                    return;
                }
            // Rebind pattern: Expr(Block { [Assign(MAX, computed_val)], expr: Some(Local(N)) })
            // styx-rustc encodes `local_N = computed_val` as a Block that stores the result in
            // the return slot (MAX) and returns Local(N) as the Block expression. This appears
            // in loop bodies where variables are updated via assignment. We must emit:
            //   let local_N := computed_val        (or ← for monadic)
            // instead of the default `let _ := (let _ := ...; local_N)` which discards the
            // computed value and passes the OLD local_N into the go_N continuation.
            if !is_last
                && let StyxExprKind::Block { stmts: blk_stmts, expr: blk_tail } = &expr.kind
                    && blk_stmts.len() == 1
                        && let StyxStmt::Assign { target, value: computed_val, .. } = &blk_stmts[0]
                            && target.0 == u32::MAX
                                && let Some(tail_expr) = blk_tail
                                    && let StyxExprKind::Local(lid) = &tail_expr.kind {
                                        let name = local_name(lid.0);
                                        let v = emit_expr(computed_val, types);
                                        let bind = if is_monadic_expr(computed_val) { "←" } else { ":=" };
                                        w.writeln(format!("let {name} {bind} {v}"));
                                        LOCAL_NAMES.with(|map| {
                                            map.borrow_mut().insert(lid.0, name);
                                        });
                                        return;
                                    }
            let val = emit_expr(expr, types);
            let bind = if is_monadic_expr(expr) { "←" } else { ":=" };
            if is_last {
                w.writeln(val);
            } else {
                w.writeln(format!("let _ {bind} {val}"));
            }
        }
        StyxStmt::Return(expr) => {
            // Flatten Return(Block { [If { ... }] }) into statement-level match/if emission.
            // These need emit_stmt(If) not inline emit_expr so that match arms and `←` inside
            // arms work correctly in do-notation. Also flatten Return(Block { [Loop] }) so
            // emit_stmt(Loop) fires correctly.
            if let StyxExprKind::Block {
                stmts,
                expr: block_expr,
            } = &expr.kind
                && (block_has_early_return_if(stmts) || block_has_loop(stmts) || block_has_if(stmts) || block_has_match_needing_do(stmts)) {
                    let total = stmts.len();
                    for (i, s) in stmts.iter().enumerate() {
                        let block_last = i == total - 1 && block_expr.is_none();
                        let has_cont = i + 1 < total;
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| {
                                *c.borrow_mut() = Some(stmts[i + 1..].to_vec());
                            });
                        }
                        emit_stmt(w, s, is_last && block_last, types);
                        if has_cont {
                            FOR_ITER_OUTER_CONT.with(|c| *c.borrow_mut() = None);
                        }
                        // Read-only check: don't reset USED so the outer emit_block_stmts
                        // can also detect it and stop processing its remaining stmts.
                        let cont_used = FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow());
                        if cont_used {
                            return;
                        }
                    }
                    if let Some(e) = block_expr
                        && is_last {
                            let v = emit_expr(e, types);
                            if is_monadic_expr(e) {
                                w.writeln(v);
                            } else {
                                w.writeln(format!("ok {v}"));
                            }
                        }
                    return;
                }
            let val = emit_expr(expr, types);
            // If the expression returns Result, emit directly — wrapping in `ok` would double-wrap.
            // This covers: local function calls, stdlib calls (Vec.len, etc.), trait method calls,
            // and monadic binops.
            let is_result_call = matches!(&expr.kind, StyxExprKind::Call { .. });
            if is_result_call || is_monadic_binop(expr) {
                w.writeln(val);
            } else {
                w.writeln(format!("ok {val}"));
            }
        }
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            // FIRST: Option-condition pattern — MUST be checked before is_early_return.
            // `if let Some(x) = call()` needs match, not if (Option<T> is not Bool).
            // Handles both:
            //   - empty else:     | .none => ok ()   | .some payload => do ... ok ()
            //   - non-empty else: | .none => do <else_block> | .some payload => do <then_block>
            let is_option_cond = matches!(&cond.ty,
                StyxType::Adt { rust_path, .. }
                    if rust_path == "std::option::Option" || rust_path == "core::option::Option"
            );
            if is_option_cond {
                let mut cond_refs = std::collections::BTreeSet::new();
                collect_local_ids(cond, &mut cond_refs);
                let mut then_refs = std::collections::BTreeSet::new();
                collect_local_ids_in_block(then_block, &mut then_refs);
                let mut then_assigns = std::collections::BTreeSet::new();
                collect_assigned_ids_in_block(then_block, &mut then_assigns);
                // Payload local: referenced in then_block but not in cond, not defined there,
                // not a function parameter, and not a local already assigned in the outer
                // function body (those are in scope via a prior `let` binding, not the
                // pattern-bound value — BODY_LOCALS contains all Assign targets from prescan).
                let payload_candidates: Vec<u32> = then_refs
                    .iter()
                    .filter(|&&id| {
                        !cond_refs.contains(&id)
                            && !then_assigns.contains(&id)
                            && !is_param_id(id)
                            && !BODY_LOCALS.with(|bl| bl.borrow().contains_key(&id))
                    })
                    .copied()
                    .collect();
                // Determine the Option's inner payload type (stripping Ref layers).
                let option_inner_ty: Option<&StyxType> = if let StyxType::Adt { generic_args, .. } = &cond.ty {
                    generic_args.first()
                } else {
                    None
                };
                // Peel Ref layers from the option inner type to get the base type.
                let option_base_ty = option_inner_ty.map(|ty| {
                    let mut t = ty;
                    loop {
                        match t {
                            StyxType::Ref { inner, .. } => t = inner.as_ref(),
                            _ => break,
                        }
                    }
                    t
                });
                // If the payload type is a Tuple and the payload local's type matches
                // a specific field, emit a tuple-destructuring pattern in | .some.
                // E.g., Option<(U64, Capability)> with local_35: U64 → | .some (local_35, _)
                let payload_name = if let Some(StyxType::Tuple(fields)) = option_base_ty {
                    if let Some(&pid) = payload_candidates.first() {
                        // Look up this local's type from the then_block expressions.
                        let mut local_types_map = std::collections::BTreeMap::new();
                        for stmt in &then_block.stmts {
                            collect_local_types_in_stmt(stmt, &mut local_types_map);
                        }
                        if let Some(local_ty) = local_types_map.get(&pid) {
                            // Strip Ref from local_ty for comparison
                            let local_base = match local_ty {
                                StyxType::Ref { inner, .. } => inner.as_ref(),
                                other => other,
                            };
                            // Find which field index this local matches
                            let field_idx = fields.iter().position(|f| {
                                let f_base = match f {
                                    StyxType::Ref { inner, .. } => inner.as_ref(),
                                    other => other,
                                };
                                styx_types_equal(f, local_ty)
                                    || styx_types_equal(f_base, local_ty)
                                    || styx_types_equal(f, local_base)
                                    || styx_types_equal(f_base, local_base)
                            });
                            if let Some(fi) = field_idx {
                                // Build tuple pattern: (local_N, _) or (_, local_N)
                                let mut parts: Vec<String> = vec!["_".to_string(); fields.len()];
                                parts[fi] = local_name(pid);
                                format!("({})", parts.join(", "))
                            } else {
                                local_name(pid)
                            }
                        } else {
                            local_name(pid)
                        }
                    } else {
                        "_".to_string()
                    }
                } else if let Some(&pid) = payload_candidates.first() {
                    local_name(pid)
                } else {
                    "_".to_string() // mutation discarded in functional semantics
                };
                let cond_str = emit_expr_lifted(cond, types);
                if else_block.stmts.is_empty() {
                    // Empty else: both arms return Result Unit.
                    // Emit all then_block stmts. Both arms must return Result Unit (matching
                    // .none => ok ()). Three patterns can appear here:
                    // - Assign{DUMMY, Call(f)}: discarded result → DUMMY_NOLAST → let _ ←
                    // - Expr(Call(f)):           discarded result → is_last=false → let _ ←
                    // - Return(Call(f)):         from `f(...)?` desugaring — the ? propagates
                    //   error via monad binding; value is discarded. Must emit `let _ ← f(...)`,
                    //   NOT bare `f(...)` (which is Result Bool ≠ Result Unit).
                    w.writeln(format!("match {cond_str} with"));
                    w.writeln("  | .none => ok ()");
                    w.writeln(format!("  | .some {payload_name} => do"));
                    w.indent();
                    w.indent();
                    for stmt in &then_block.stmts {
                        if let StyxStmt::Return(expr) = stmt {
                            // Return inside option-condition arm: discard the value with let _ ←.
                            let val = emit_expr(expr, types);
                            let bind = if is_monadic_expr(expr) { "←" } else { ":=" };
                            w.writeln(format!("let _ {bind} {val}"));
                        } else {
                            emit_stmt(w, stmt, false, types);
                        }
                    }
                    w.writeln("ok ()");
                    w.dedent();
                    w.dedent();
                } else {
                    // Non-empty else: emit both branches as do-blocks.
                    // .none => do <else_block>   .some payload => do <then_block>
                    // Each branch uses emit_block_stmts so tail position is handled correctly.
                    w.writeln(format!("match {cond_str} with"));
                    w.writeln("  | .none => do");
                    w.indent();
                    w.indent();
                    emit_block_stmts(w, else_block, types);
                    w.dedent();
                    w.dedent();
                    w.writeln(format!("  | .some {payload_name} => do"));
                    w.indent();
                    w.indent();
                    emit_block_stmts(w, then_block, types);
                    w.dedent();
                    w.dedent();
                }
                return;
            }

            // Early return pattern: `if cond { return Err(...) }` (else empty)
            // Emit as `if cond then return (.Err ...)` in do-notation.
            // In Lean's Result monad, `return x` = `ok x`, so NO extra `ok` wrapping.
            let is_early_return = then_block.stmts.len() == 1
                && else_block.stmts.is_empty()
                && matches!(&then_block.stmts[0], StyxStmt::Return(_));

            if is_early_return
                && let StyxStmt::Return(ret_expr) = &then_block.stmts[0] {
                    let cond_str = emit_expr_lifted(cond, types);
                    // Unwrap Block { [Expr(value)], expr: unit } pattern.
                    // styx-rustc wraps return values in a Block with the value as Expr.
                    let (actual_expr, val) = unwrap_return_block(ret_expr, types);

                    // Simple case: value is a single expression (no let bindings needed).
                    // Emit on one line: `if cond then return val`
                    let is_simple = !val.contains("let ");
                    if is_simple {
                        let is_result_call = matches!(&actual_expr.kind, StyxExprKind::Call { .. });
                        if is_result_call || is_monadic_binop(actual_expr) {
                            w.writeln(format!("if {cond_str} then do return (← {val})"));
                        } else {
                            w.writeln(format!("if {cond_str} then return {val}"));
                        }
                        return;
                    }
                    // Complex case: return value is a Block with intermediate let bindings.
                    // Emit: if cond then do
                    //          let x ← e1
                    //          let y := e2
                    //          return (.Err ...)
                    if let StyxExprKind::Block {
                        stmts: blk_stmts, ..
                    } = &ret_expr.kind
                        && !blk_stmts.is_empty() {
                            w.writeln(format!("if {cond_str} then do"));
                            w.indent();
                            // Emit all stmts except the last as let bindings
                            for (i, s) in blk_stmts.iter().enumerate() {
                                if i < blk_stmts.len() - 1 {
                                    emit_stmt(w, s, false, types);
                                } else {
                                    // Last stmt: emit as `return value`
                                    match s {
                                        StyxStmt::Expr(e) => {
                                            let v = emit_expr(e, types);
                                            w.writeln(format!("return {v}"));
                                        }
                                        StyxStmt::Assign {
                                            target, value: v, ..
                                        } if target.0 == u32::MAX => {
                                            let ev = emit_expr(v, types);
                                            w.writeln(format!("return {ev}"));
                                        }
                                        _ => {
                                            emit_stmt(w, s, true, types);
                                        }
                                    }
                                }
                            }
                            w.dedent();
                            return;
                        }
                    // Fallback: just emit the raw value
                    w.writeln(format!("if {cond_str} then return {val}"));
                    return;
                }

            // Use emit_expr_lifted so that monadic conditions (function calls returning
            // Result Bool, like `has_failure`) are bound with `←` before the `if`.
            // Pure conditions (comparisons, logical ops) are unaffected because
            // emit_expr_lifted only adds `(← ...)` when is_monadic_expr is true.
            let cond_str = emit_expr_lifted(cond, types);
            w.writeln(format!("if {cond_str} then"));
            w.indent();
            w.writeln("do");
            w.indent();
            emit_block_stmts(w, then_block, types);
            w.dedent();
            w.dedent();
            w.writeln("else");
            w.indent();
            w.writeln("do");
            w.indent();
            emit_block_stmts(w, else_block, types);
            w.dedent();
            w.dedent();
        }
        StyxStmt::Match { scrutinee, arms } => {
            // Detect scalar-literal match: Lean can't pattern match on UScalar values
            // (they're opaque wrappers, not inductives). Emit if-else chains instead.
            let has_scalar_literal = arms.iter().any(|a| {
                matches!(
                    &a.pattern,
                    StyxPattern::Literal(StyxLiteral::UInt(..) | StyxLiteral::Int(..))
                )
            });
            if has_scalar_literal {
                let scrut = emit_expr(scrutinee, types);
                let mut first = true;
                for arm in arms {
                    match &arm.pattern {
                        StyxPattern::Literal(lit) => {
                            let val = emit_literal(lit);
                            let keyword = if first { "if" } else { "else if" };
                            first = false;
                            w.writeln(format!("{keyword} {scrut} == {val} then do"));
                            w.indent();
                            emit_block_stmts(w, &arm.body, types);
                            w.dedent();
                        }
                        StyxPattern::Wildcard | StyxPattern::Binding { .. } => {
                            w.writeln("else do");
                            w.indent();
                            emit_block_stmts(w, &arm.body, types);
                            w.dedent();
                        }
                        _ => {
                            // Fallback: emit as regular match arm (may not compile)
                            let pat = emit_pattern(&arm.pattern, types);
                            w.writeln(format!("-- scalar match fallback: {pat}"));
                            w.writeln("else do");
                            w.indent();
                            emit_block_stmts(w, &arm.body, types);
                            w.dedent();
                        }
                    }
                }
            } else {
                let scrut = emit_expr(scrutinee, types);
                let scrut_str = if is_monadic_expr(scrutinee) {
                    format!("(\u{2190} {scrut})")
                } else {
                    scrut
                };
                w.writeln(format!("match {scrut_str} with"));
                // Deduplicate: Lean rejects redundant match alternatives.
                // When Rust matches on an error enum with multiple variants that all
                // collapse to the same Lean pattern (e.g., `Err _`), styx emits duplicate
                // arms. Skip any arm whose pattern was already emitted.
                let mut seen_pats: std::collections::HashSet<String> =
                    std::collections::HashSet::new();
                for arm in arms {
                    let pat = emit_pattern(&arm.pattern, types);
                    if !seen_pats.insert(pat.clone()) {
                        continue; // duplicate arm — skip
                    }
                    w.writeln(format!("  | {pat} => do"));
                    w.indent();
                    w.indent();
                    // Save/reset USED before each arm body to prevent a for-in loop in
                    // one arm from causing early exit in the next arm's emit_block_stmts.
                    // If the arm itself sets USED=true (consumed outer continuation), keep it.
                    // Otherwise restore the pre-arm state so it propagates to the outer.
                    let used_before_arm = FOR_ITER_OUTER_CONT_USED.with(|u| {
                        let v = *u.borrow();
                        *u.borrow_mut() = false;
                        v
                    });
                    emit_block_stmts(w, &arm.body, types);
                    let arm_set_used = FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow());
                    if !arm_set_used && used_before_arm {
                        FOR_ITER_OUTER_CONT_USED.with(|u| *u.borrow_mut() = true);
                    }
                    w.dedent();
                    w.dedent();
                }
            }
        }
        StyxStmt::Loop { body, cond } => {
            // Detect the "infinite loop as while" encoding used by styx-rustc.
            // styx-rustc encodes `while cond { body }` as:
            //   Loop(cond=None) { Return(Block { [If(cond, body, [])] }) }
            // We detect this and treat it as a conditioned loop, which means:
            //   then-branch: body stmts + go_N recursive call (continue)
            //   else-branch: ok state (exit)
            // This avoids the incorrect "always recurse after if/else" structure.
            let extracted_while: Option<(&StyxExpr, &StyxBlock, &StyxBlock)> =
                if cond.is_none() && body.stmts.len() == 1 {
                    if let StyxStmt::Return(ret_expr) = &body.stmts[0] {
                        if let StyxExprKind::Block { stmts: blk_stmts, .. } = &ret_expr.kind {
                            if blk_stmts.len() == 1 {
                                if let StyxStmt::If { cond: if_cond, then_block, else_block } = &blk_stmts[0] {
                                    // "while" pattern: infinite loop wrapping a single If
                                    Some((if_cond, then_block, else_block))
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                } else {
                    None
                };

            // Early for-in detection: must happen before sig emission so we can
            // include the error-channel wrapper in the go_N return type.
            let for_iter_detection = if cond.is_none() && extracted_while.is_none() {
                detect_for_iter_loop(body)
            } else {
                None
            };
            // If the Some arm contains an early `return Err(e)`, this is an error-channel
            // for-in loop: go_N returns Result (core.result.Result STATE ErrT).
            let err_ty_opt: Option<String> = if let Some((_, _, _, some_arm)) = &for_iter_detection {
                find_result_err_ty_in_stmts(&some_arm.body.stmts).map(|ty| emit_type(&ty))
            } else {
                None
            };
            let has_error_channel = err_ty_opt.is_some();

            // Collect all locals written inside the loop body.
            // These become loop-carried state — parameters and return values
            // of the auxiliary `go_N` function that Lean uses for the loop.
            let mut modified = BTreeSet::new();
            collect_modified_locals_loop(&body.stmts, &mut modified);
            // The return slot (u32::MAX) is never a state variable.
            modified.remove(&u32::MAX);
            // Filter to only variables in scope BEFORE this loop.
            // Variables first assigned inside the loop body are loop-internal temporaries
            // (recomputed each iteration) and should NOT be loop-carried state.
            // Example: in LinearMemory::read_range, local_77/local_85 are page/offset
            // computations that styx-rustc assigns inside the loop — they are NOT initialized
            // before the loop. Only local_54 (addr) is a true loop-carried state variable.
            modified.retain(|id| is_in_scope(*id));

            let state_names: Vec<String> = modified
                .iter()
                .map(|id| local_name(*id))
                .collect();

            // Build typed parameter list for the go function.
            // For locals whose type is unknown (shouldn't happen in practice),
            // fall back to `_` so Lean can attempt inference.
            let state_args_typed: Vec<String> = modified
                .iter()
                .map(|id| {
                    let name = local_name(*id);
                    let ty_str = local_type(*id)
                        .map(|ty| emit_type(&ty))
                        .unwrap_or_else(|| "_".to_string());
                    format!("({name} : {ty_str})")
                })
                .collect();

            let go_name = format!(
                "go_{}",
                LOOP_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
            );
            let args_sig = state_args_typed.join(" ");
            let args_call = state_names.join(" ");

            // Build the return type of go: the state tuple wrapped in Result.
            // - 0 state vars → PUnit
            // - 1 state var  → T
            // - N state vars → (T1 × T2 × ...)
            let ret_inner = if state_names.is_empty() {
                "PUnit".to_string()
            } else if state_names.len() == 1 {
                modified
                    .iter()
                    .next()
                    .and_then(|id| local_type(*id))
                    .map(|ty| emit_type(&ty))
                    .unwrap_or_else(|| "_".to_string())
            } else {
                let tys: Vec<String> = modified
                    .iter()
                    .map(|id| {
                        local_type(*id)
                            .map(|ty| emit_type(&ty))
                            .unwrap_or_else(|| "_".to_string())
                    })
                    .collect();
                format!("({})", tys.join(" × "))
            };

            // For error-channel for-in loops, wrap ret_inner as:
            //   core.result.Result <STATE> <ErrT>
            // so go_N can carry early returns through the inner Result.
            let ret_type_for_sig = if let Some(ref err_ty) = err_ty_opt {
                format!("(core.result.Result {} {})", ret_inner, err_ty)
            } else {
                ret_inner.clone()
            };

            // Emit: `let rec go_N (x : T) ... : Result RET := do`
            let sig = if args_sig.is_empty() {
                format!("let rec {go_name} : Result {ret_type_for_sig} := do")
            } else {
                format!("let rec {go_name} {args_sig} : Result {ret_type_for_sig} := do")
            };
            w.writeln(sig);
            w.indent();

            // Push loop context so nested Break/Continue can resolve go_name and state.
            LOOP_CONTEXT.with(|ctx| {
                ctx.borrow_mut().push(LoopCtx {
                    go_name: go_name.clone(),
                    state_args: state_names.clone(),
                });
            });

            // Helper closure: emit the "loop continue" call (go_N state).
            let emit_continue = |w: &mut IndentWriter| {
                if state_names.is_empty() {
                    w.writeln(go_name.clone());
                } else {
                    w.writeln(format!("{go_name} {args_call}"));
                }
            };
            // Helper closure: emit the "loop exit" value.
            // For normal loops: ok state / ok PUnit.unit
            // For error-channel loops: ok (.Ok state) / ok (.Ok PUnit.unit)
            let state_tuple = if state_names.len() <= 1 {
                args_call.clone() // 0 vars: ""; 1 var: just the name
            } else {
                state_names.join(", ") // N vars: "a, b, c"
            };
            let emit_exit = |w: &mut IndentWriter| {
                if has_error_channel {
                    if state_names.is_empty() {
                        w.writeln("ok (.Ok PUnit.unit)");
                    } else if state_names.len() == 1 {
                        w.writeln(format!("ok (.Ok {})", state_names[0]));
                    } else {
                        w.writeln(format!("ok (.Ok ({}))", state_tuple));
                    }
                } else if state_names.is_empty() {
                    w.writeln("ok PUnit.unit");
                } else if state_names.len() == 1 {
                    w.writeln(format!("ok {}", state_names[0]));
                } else {
                    w.writeln(format!("ok ({})", state_tuple));
                }
            };

            if let Some((while_cond, then_block, else_block)) = extracted_while {
                // "Infinite loop as while" pattern:
                //   Loop(None) { Return(Block { [If(cond, body, [])] }) }
                // Emit:
                //   if COND then do
                //     <then_body — all non-tail>
                //     go_N state           ← continue
                //   else do
                //     <else_body OR ok state>  ← exit
                let cond_str = emit_expr_lifted(while_cond, types);
                w.writeln(format!("if {cond_str} then do"));
                w.indent();
                emit_block_stmts_nontail(w, then_block, types);
                emit_continue(w);
                w.dedent();
                w.writeln("else do");
                w.indent();
                // In the "while as infinite loop" encoding, the else_block typically
                // contains a single `Return(unit_expr)` that encodes `break` / loop exit.
                // We detect this and skip emitting it — emit_exit produces the correct
                // `ok state` value, so emitting the Return would produce a duplicate `ok`.
                let else_has_only_return = else_block.stmts.len() == 1
                    && matches!(&else_block.stmts[0], StyxStmt::Return(_));
                if else_block.stmts.is_empty() || else_has_only_return {
                    emit_exit(w);
                } else {
                    emit_block_stmts_nontail(w, else_block, types);
                    emit_exit(w);
                }
                w.dedent();
            } else if let Some(cond_expr) = cond {
                // Explicit conditioned loop: Loop(cond=Some(expr)) { body }
                // Emit:
                //   if COND then do
                //     <body — all non-tail>
                //     go_N state
                //   else do
                //     ok state
                let cond_str = emit_expr_lifted(cond_expr, types);
                w.writeln(format!("if {cond_str} then do"));
                w.indent();
                emit_block_stmts_nontail(w, body, types);
                emit_continue(w);
                w.dedent();
                w.writeln("else do");
                w.indent();
                emit_exit(w);
                w.dedent();
            } else if let Some((pre_stmts, scrutinee, none_arm, some_arm)) = for_iter_detection {
                // For-in iterator loop: Loop(None) ending with Match(Iterator::next)
                //   None arm → loop exit (emit_exit)
                //   Some arm → iteration body + recurse (emit_continue)
                for stmt in pre_stmts {
                    emit_stmt(w, stmt, false, types);
                }
                let scrut = emit_expr(scrutinee, types);
                let scrut_str = if is_monadic_expr(scrutinee) {
                    format!("(\u{2190} {scrut})")
                } else {
                    scrut
                };
                w.writeln(format!("match {scrut_str} with"));
                let none_pat = emit_pattern(&none_arm.pattern, types);
                w.writeln(format!("  | {none_pat} => do"));
                w.indent();
                w.indent();
                emit_exit(w);
                w.dedent();
                w.dedent();
                // Annotate the .some binding with its item type so Lean can
                // resolve field accesses (e.g. local_19.source). Iterator.next
                // has both {IterT ItemT} implicit — Lean can't infer ItemT from
                // an opaque iterator, so we add the annotation explicitly.
                let some_arm_pat_str: String = {
                    let base = emit_pattern(&some_arm.pattern, types);
                    // For a simple `.some local_N` binding, inject `: ItemT`.
                    if let StyxPattern::Variant { variant_id, field_bindings, .. } = &some_arm.pattern {
                        if variant_id.0 == 1 && field_bindings.len() == 1 {
                            if let Some(pb) = &field_bindings[0] {
                                if let Some(item_ty) = option_item_ty(&scrutinee.ty) {
                                    let ty_str = emit_type(item_ty);
                                    let var = local_name(pb.local.0);
                                    format!(".some ({var} : {ty_str})")
                                } else { base }
                            } else { base }
                        } else { base }
                    } else { base }
                };
                w.writeln(format!("  | {some_arm_pat_str} => do"));
                w.indent();
                w.indent();
                emit_block_stmts_nontail(w, &some_arm.body, types);
                emit_continue(w);
                w.dedent();
                w.dedent();
            } else {
                // General infinite loop (`loop { ... }`): must break or return from body.
                // Body stmts are non-tail because go_N tail-call follows.
                emit_block_stmts_nontail(w, body, types);
                emit_continue(w);
            }

            w.dedent();
            w.writeln("partial_fixpoint");

            // Pop loop context.
            LOOP_CONTEXT.with(|ctx| {
                ctx.borrow_mut().pop();
            });

            // Call site: invoke go_N and destructure the returned state.
            // For error-channel for-in loops, set FOR_ITER_ERROR_PENDING instead of
            // emitting the call site directly — emit_block_stmts will emit the
            // error-propagating match and wrap remaining stmts in the .Ok arm.
            if has_error_channel {
                FOR_ITER_ERROR_PENDING.with(|p| {
                    *p.borrow_mut() = Some(ForIterErrorPending {
                        go_name: go_name.clone(),
                        args_call: args_call.clone(),
                        state_names: state_names.clone(),
                    });
                });
            } else if state_names.is_empty() {
                if args_call.is_empty() {
                    w.writeln(format!("let _ \u{2190} {go_name}"));
                } else {
                    w.writeln(format!("let _ \u{2190} {go_name} {args_call}"));
                }
            } else if state_names.len() == 1 {
                w.writeln(format!(
                    "let {} \u{2190} {go_name} {}",
                    state_names[0], args_call
                ));
            } else {
                w.writeln(format!(
                    "let ({}) \u{2190} {go_name} {}",
                    state_names.join(", "),
                    args_call
                ));
            }
        }
        StyxStmt::Break { depth } => {
            if *depth > 0 {
                w.writeln("sorry /- multi-level break -/");
            } else {
                LOOP_CONTEXT.with(|ctx| {
                    let ctx = ctx.borrow();
                    if let Some(lc) = ctx.last() {
                        if lc.state_args.is_empty() {
                            w.writeln("ok PUnit.unit");
                        } else if lc.state_args.len() == 1 {
                            w.writeln(format!("ok {}", lc.state_args[0]));
                        } else {
                            w.writeln(format!("ok ({})", lc.state_args.join(", ")));
                        }
                    } else {
                        w.writeln("sorry /- break outside loop -/");
                    }
                });
            }
        }
        StyxStmt::Continue { depth } => {
            if *depth > 0 {
                w.writeln("sorry /- multi-level continue -/");
            } else {
                LOOP_CONTEXT.with(|ctx| {
                    let ctx = ctx.borrow();
                    if let Some(lc) = ctx.last() {
                        if lc.state_args.is_empty() {
                            w.writeln(lc.go_name.clone());
                        } else {
                            w.writeln(format!(
                                "{} {}",
                                lc.go_name,
                                lc.state_args.join(" ")
                            ));
                        }
                    } else {
                        w.writeln("sorry /- continue outside loop -/");
                    }
                });
            }
        }
        StyxStmt::Drop { .. } => {
            // No-op in Lean
        }
        StyxStmt::Assert { cond, expected } => {
            let cond_str = emit_expr(cond, types);
            w.writeln(format!("massert ({cond_str} == {expected})"));
        }
        StyxStmt::FieldAssign {
            target,
            field_path,
            value,
            ..
        } => {
            // Lean struct-update: `let target := { target with field := value }`
            // For nested paths (self.a.b = v), build inside-out:
            //   let self_ := { self_ with a := { self_.a with b := v } }
            let val = emit_expr_lifted(value, types);
            let target_name = local_name(target.0);
            if field_path.len() == 1 {
                let fname = escape_lean_keyword(&field_path[0].name);
                w.writeln(format!(
                    "let {target_name} := {{ {target_name} with {fname} := {val} }}"
                ));
            } else if field_path.len() >= 2 {
                // Build inside-out: innermost field first
                let mut expr = val.to_string();
                for i in (0..field_path.len()).rev() {
                    let fname = escape_lean_keyword(&field_path[i].name);
                    let prefix = if i == 0 {
                        target_name.clone()
                    } else {
                        let path_parts: Vec<String> = field_path[..i]
                            .iter()
                            .map(|f| escape_lean_keyword(&f.name))
                            .collect();
                        format!("{target_name}.{}", path_parts.join("."))
                    };
                    expr = format!("{{ {prefix} with {fname} := {expr} }}");
                }
                w.writeln(format!("let {target_name} := {expr}"));
            }
        }
    }
}

/// Infer explicit type arguments for Aeneas stdlib functions that require them.
///
/// Aeneas Vec/Slice operations take (T : Type) and sometimes (A : Type) as explicit
/// parameters. Lean cannot infer them because the value arg type is wrapped in `Result`.
/// We extract T from the first value argument's type (when it's a Vec/Slice/Ref to one).
///
/// Returns a space-separated string like "Message Global" for Vec operations, or "" for
/// functions that don't need type args.
pub(crate) fn infer_stdlib_type_args(callee: &str, args: &[StyxExpr]) -> String {
    // IndexVec.index: (T : Type) (I : Type) (A : Type) (Clause0_Output : Type) vec idx
    // For Vec<T> indexed by Usize, I=Usize, A=Global, Clause0_Output=T
    if callee == "alloc.vec.IndexVec.index" {
        if let Some(first) = args.first()
            && let Some(elem_ty) = extract_vec_elem_type(&first.ty) {
                return format!("{elem_ty} Usize Global {elem_ty}");
            }
        return String::new();
    }
    // Vec.index_mut_usize: (T : Type) vec idx  — takes only T as explicit type arg
    if callee == "alloc.vec.Vec.index_mut_usize" {
        if let Some(first) = args.first()
            && let Some(elem_ty) = extract_vec_elem_type(&first.ty) {
                return elem_ty;
            }
        return String::new();
    }

    // IndexMutVec.index_mut: (T : Type) (_I : Type) (_A : Type) vec idx
    // Transparent def only takes T, _I, _A (5-arg signature, no Clause0_Output)
    if callee == "alloc.vec.IndexMutVec.index_mut" {
        if let Some(first) = args.first()
            && let Some(elem_ty) = extract_vec_elem_type(&first.ty) {
                return format!("{elem_ty} Usize Global");
            }
        return String::new();
    }

    // Vec<T> operations: all take (T : Type) (A : Type) except specific ones
    let is_vec_op =
        callee.starts_with("alloc.vec.Vec.") || callee.starts_with("alloc.vec.CloneVec.");
    let is_slice_op = callee.starts_with("core.slice.");
    let is_array_op = callee.starts_with("core.array.");

    if !is_vec_op && !is_slice_op && !is_array_op {
        return String::new();
    }

    // Extract element type from the first value argument
    let first_arg = match args.first() {
        Some(a) => a,
        None => return String::new(),
    };
    let elem_ty = match extract_vec_elem_type(&first_arg.ty) {
        Some(t) => t,
        None => return String::new(),
    };

    if is_vec_op {
        // Vec ops: T, Global allocator (Global is an Aeneas-defined inductive type)
        format!("{elem_ty} Global")
    } else if is_slice_op {
        // Slice ops: just T
        elem_ty
    } else if is_array_op {
        // Array ops: T, N (const param) — skip N inference (hard)
        elem_ty
    } else {
        String::new()
    }
}

/// Extract the element type from a Vec<T>, Slice<T>, or reference to one.
pub(crate) fn extract_vec_elem_type(ty: &StyxType) -> Option<String> {
    match ty {
        StyxType::Ref { inner, .. } => extract_vec_elem_type(inner),
        StyxType::Adt {
            rust_path,
            generic_args,
            ..
        } => {
            let is_vec = matches!(
                rust_path.as_str(),
                "alloc::vec::Vec"
                    | "std::vec::Vec"
                    | "alloc::collections::VecDeque"
                    | "std::collections::VecDeque"
                    | "alloc::collections::vec_deque::VecDeque"
                    | "std::collections::vec_deque::VecDeque"
            );
            if !is_vec {
                return None;
            }
            let first = generic_args.iter().find(|t| !is_allocator_type(t))?;
            Some(emit_type(first))
        }
        StyxType::Slice(elem) => Some(emit_type(elem)),
        StyxType::Array { elem, .. } => Some(emit_type(elem)),
        _ => None,
    }
}

/// Unwrap Ref/RawPtr wrappers to get the inner type.
/// Needed because StyxIR preserves Ref types on args even though Lean erases them.
pub(crate) fn unwrap_ref_type(ty: &StyxType) -> &StyxType {
    match ty {
        StyxType::Ref { inner, .. } | StyxType::RawPtr { inner, .. } => unwrap_ref_type(inner),
        _ => ty,
    }
}

/// Infer type arguments for Try/FromResidual and Option/Result method stdlib calls.
/// These functions take explicit type params in Lean that are implicit in Rust.
pub(crate) fn infer_try_type_args(callee: &str, args: &[StyxExpr]) -> String {
    let first_arg = match args.first() {
        Some(a) => a,
        None => return String::new(),
    };
    // Unwrap Ref wrappers: StyxIR preserves &T types but Lean erases references.
    let first_ty = unwrap_ref_type(&first_arg.ty);

    // --- Try/FromResidual ---
    let is_try = callee == "core.result.TryResultResultInfallible.branch"
        || callee == "core.result.TryResultResultInfallible.from_output";
    let is_from_residual = callee == "core.result.FromResidualResultResultInfallible.from_residual";

    if is_try || is_from_residual {
        return match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Result") && generic_args.len() >= 2 => {
                let t = emit_type(&generic_args[0]);
                let e = emit_type(&generic_args[1]);
                if is_from_residual {
                    format!("{t} {e} {e} (core.convert.FromSame {e})")
                } else {
                    format!("{t} {e}")
                }
            }
            _ => String::new(),
        };
    }

    // --- Option methods: need (T : Type) ---
    // Match both std.option.* and core.option.* (StyxIR may use either prefix)
    let option_1ty = [
        "std.option.Option.is_some",
        "std.option.Option.is_none",
        "std.option.Option.unwrap_or",
        "std.option.Option.expect",
        "std.option.Option.unwrap",
        "core.option.Option.is_some",
        "core.option.Option.is_none",
        "core.option.Option.unwrap_or",
        "core.option.Option.expect",
        "core.option.Option.unwrap",
    ];
    if option_1ty.contains(&callee) {
        return match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Option") && !generic_args.is_empty() => {
                emit_type(&generic_args[0])
            }
            _ => String::new(),
        };
    }

    // Option.ok_or: need (T : Type) (E : Type) — T from Option<T>, E from second arg
    if callee == "std.option.Option.ok_or" || callee == "core.option.Option.ok_or" {
        let t = match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Option") && !generic_args.is_empty() => {
                emit_type(&generic_args[0])
            }
            _ => return String::new(),
        };
        let e = if args.len() >= 2 {
            emit_type(unwrap_ref_type(&args[1].ty))
        } else {
            "E".to_string()
        };
        return format!("{t} {e}");
    }

    // Option.map: need (T : Type) (U : Type) — T from Option<T>, U from return Option<U>
    if callee == "std.option.Option.map" || callee == "core.option.Option.map" {
        return match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Option") && !generic_args.is_empty() => {
                let t = emit_type(&generic_args[0]);
                format!("{t} _")
            }
            _ => String::new(),
        };
    }

    // --- Result methods: need (T : Type) (E : Type) ---
    let result_2ty = [
        "std.result.Result.is_ok",
        "std.result.Result.is_err",
        "std.result.Result.ok",
        "core.result.Result.is_ok",
        "core.result.Result.is_err",
        "core.result.Result.ok",
    ];
    if result_2ty.contains(&callee) {
        return match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Result") && generic_args.len() >= 2 => {
                let t = emit_type(&generic_args[0]);
                let e = emit_type(&generic_args[1]);
                format!("{t} {e}")
            }
            _ => String::new(),
        };
    }

    // Result.map_err: need (T E F) — T,E from Result<T,E>, F from closure return
    if callee == "std.result.Result.map_err" || callee == "core.result.Result.map_err" {
        return match first_ty {
            StyxType::Adt {
                rust_path,
                generic_args,
                ..
            } if rust_path.contains("Result") && generic_args.len() >= 2 => {
                let t = emit_type(&generic_args[0]);
                let e = emit_type(&generic_args[1]);
                format!("{t} {e} _")
            }
            _ => String::new(),
        };
    }

    String::new()
}

/// Wrap a sub-expression with `(← ...)` if it's a Result-returning Call or monadic BinOp.
/// This lifts monadic values into pure expression contexts inside `do` blocks.
pub(crate) fn emit_expr_lifted(expr: &StyxExpr, types: &TypeLookup) -> String {
    // Ref { inner: Call } — Lean erases references, but the inner call may return Result.
    // Example: `&mut iter` where `iter = core.slice.iter(...)` → `(← (core.slice.iter ...))`
    // This handles patterns like Iterator.all(Ref(core.slice.iter(...)), pred) where
    // the slice iterator is taken by &mut for the FnMut call.
    if let StyxExprKind::Ref { operand, .. } = &expr.kind
        && matches!(&operand.kind, StyxExprKind::Call { .. }) {
            return emit_expr_lifted(operand, types);
        }
    if matches!(&expr.kind, StyxExprKind::Call { .. }) {
        // Skip lifting for clone (identity) — handled by emit_expr returning the arg directly
        let is_clone = if let StyxExprKind::Call { callee, args, .. } = &expr.kind {
            args.len() == 1
                && (matches!(callee,
                    StyxCallee::TraitMethod { trait_path, method_name, .. }
                        if method_name == "clone" && (trait_path.contains("clone::Clone") || trait_path.contains("Clone"))
                ) || matches!(callee,
                    StyxCallee::Function { rust_path, .. }
                        if rust_path.contains("clone::Clone::clone") || rust_path.contains("Clone::clone")
                ))
        } else {
            false
        };
        if is_clone {
            return emit_expr(expr, types);
        }
        // Skip lifting for known pure constants (def, not Result T).
        // These are zero-arg function calls in StyxIR that resolve to plain `def` in Lean.
        let is_pure_constant = if let StyxExprKind::Call { callee, args, .. } = &expr.kind {
            args.is_empty()
                && matches!(callee,
                    StyxCallee::Function { rust_path, .. }
                        if is_pure_constant_path(rust_path)
                )
        } else {
            false
        };
        if is_pure_constant {
            return emit_expr(expr, types);
        }
        let inner = emit_expr(expr, types);
        format!("(← {inner})")
    } else if is_monadic_binop(expr) {
        let inner = emit_expr(expr, types);
        format!("(← {inner})")
    } else if let StyxExprKind::Index { base, .. } = &expr.kind {
        // Slice index via Slice.index_usize returns Result T — needs `←` lifting.
        let is_slice = match &base.ty {
            StyxType::Slice(_) => true,
            StyxType::Ref { inner, .. } => matches!(inner.as_ref(), StyxType::Slice(_)),
            _ => false,
        };
        if is_slice {
            let inner = emit_expr(expr, types);
            format!("(← {inner})")
        } else {
            emit_expr(expr, types)
        }
    } else {
        emit_expr(expr, types)
    }
}

/// Returns true if `rust_path` refers to a known pure constant (def, not Result).
/// These zero-arg functions should NOT be wrapped with `←` in do blocks.
pub(crate) fn is_pure_constant_path(rust_path: &str) -> bool {
    matches!(
        rust_path,
        "state::memory::PAGE_BITS"
            | "state::memory::PAGE_SIZE"
            | "types::rights::ALL_RIGHTS_MASK"
            | "types::capability::Key::SIZE"
            | "types::capability::Hash32::SIZE"
            | "types::security::SecurityLevel::TOP"
            | "types::security::SecurityLevel::BOT"
            | "state::plugin::DEFAULT_QUOTA"
    )
}

