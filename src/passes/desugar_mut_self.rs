//! DesugarMutSelf: detect and normalize `&mut self` methods for Lean/Aeneas output.
//!
//! ## What this pass does
//!
//! Walks every function whose first parameter has `is_mut_self == true` and:
//! 1. **Rewrites discarded Vec mutations** into `Assign + FieldAssign` pairs so that
//!    the Lean emitter can generate valid do-notation (see `rewrite_vec_mutations_top_level`).
//! 2. **Strips the `Ref` wrapper** from `params[0].ty` so the emitter sees the bare
//!    Self type rather than `&mut Self`.
//!
//! ## Vec mutation rewrite (added 2026-04-13)
//!
//! Rust `Vec::push(&mut self.field, item)` is modelled in Aeneas as a monadic function
//! `Vec.push : Vec T → T → Result (Vec T)`.  When styx-rustc generates a discarded call:
//! ```text
//! Expr(Call(VecPush, [Field(Local(self), "field"), item]))   ← result thrown away
//! ```
//! the emitter would output `let _ ← Vec.push self.field item` which discards the new
//! `Vec T` and leaves `self.field` unchanged — a type/semantic error.
//!
//! This pass rewrites the discarded call into:
//! ```text
//! Assign { target: field_new, value: Call(VecPush, ...) }          ← let field_new ← ...
//! FieldAssign { target: self, field_path: ["field"], value: field_new }  ← self.field := field_new
//! ```
//!
//! For `Vec.remove` (result is `T × Vec T`) the writeback uses the second element:
//! ```text
//! Assign { target: field_pair, value: Call(VecRemove, ...) }        ← let field_pair ← ...
//! Assign { target: field_new, value: TupleField(field_pair, 1) }    ← let field_new := field_pair.2
//! FieldAssign { target: self, field_path: ["field"], value: field_new }  ← self.field := field_new
//! ```
//!
//! **Scope**: only top-level statements of the function body are rewritten.  Vec mutations
//! nested inside `If`/`Match`/`Loop` require state threading through branches and are left
//! for a future pass — such functions remain opaque.
//!
//! ## Styx convention (reconciled with actual generated output)
//!
//! The styx emitter uses a **dual-function pattern** — NOT Aeneas write-back tuples:
//!
//! For a Rust method `fn foo_mut(&mut self, ...) -> Result<(), E>`:
//!   - The `_mut` variant takes `Self` by value and returns `Result Unit` (or the
//!     original `Result<T, E>` as-is). The `ret_ty` is left unchanged.
//!   - The non-`_mut` counterpart returns `Result Self` (functional state transformer).
//!
//! Concretely, the existing `FunsExternal.lean` declares:
//! ```text
//! opaque foo_mut (self : T) ... : Result Unit
//! ```
//! NOT `Result (Unit × T)`. The Tuple writeback pattern was considered but rejected
//! because the generated Lean files already establish the Unit-return convention.
//!
//! Pre-conditions:
//!   - `StyxParam::is_mut_self == true` marks the `&mut self` receiver
//!   - `StyxType::Ref { inner, .. }` may wrap the Self type in `params[0].ty`
//!
//! Post-conditions:
//!   - `params[0].ty` is the bare Self type (Ref wrapper stripped if present)
//!   - `ret_ty` is unchanged (Unit or whatever the Rust function returns)

use crate::ir::*;
use std::collections::HashSet;

/// Run the `&mut self` desugaring pass on all methods in the package.
///
/// TIER 1 functions (no direct field mutations) get their signature transformed
/// in place. TIER 2 functions (direct field mutations) are diagnosed but not
/// yet transformed.
pub fn desugar_mut_self(pkg: &mut StyxPackage) {
    for fun_def in &mut pkg.functions {
        let self_local = match find_mut_self_local(fun_def) {
            Some(id) => id,
            None => continue,
        };

        // Count mutation sites (zero for bodyless/opaque functions).
        let mutation_count: usize = match &fun_def.body {
            None => 0,
            Some(b) => {
                let mut sites: Vec<MutationSite> = Vec::new();
                collect_mutation_sites_block(&b.block, self_local, &mut sites);
                sites.len()
            }
        };

        let tier = if mutation_count > 0 { 2u8 } else { 1u8 };

        // TIER 3 (field assign — recursive): rewrite `self.field = value` and
        // `self.field op= rhs` patterns at any nesting depth inside the body.
        //
        // Two IR patterns are handled (both share the same DUMMY-assign + trailing-
        // field-read structure that styx-rustc emits for all `self.field =` writes):
        //
        // A. Compound-assign (`self.field op= rhs`):
        //   Stmt::Expr(Block {
        //     stmts: [Assign(DUMMY, BinOp(op, Field(self, field), rhs))],
        //     expr:  Some(Field(self, field))
        //   })
        //
        // B. Plain assign (`self.field = value`):
        //   Stmt::Expr(Block {
        //     stmts: [Assign(DUMMY, <any value expr>)],
        //     expr:  Some(Field(self, field))
        //   })
        //
        // Both are rewritten to:
        //   FieldAssign { target: self_local, field_path: [field], value: <new_value> }
        //
        // which emits as:  `let self := { self with field := <new_value> }`
        //
        // TIER 3 now recurses into If/Match/Loop branches so that functions like
        // `set_blocked_mut` (body: `if cond { self.field = X }`) are fully rewritten.
        if let Some(body) = &mut fun_def.body {
            let rewrote = rewrite_field_assigns_recursive(&mut body.block, self_local);
            if rewrote > 0 && std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                eprintln!(
                    "[desugar_mut_self] TIER3 rewrote {} field-assign(s) in: {}",
                    rewrote, fun_def.rust_path,
                );
            }
        }

        // TIER 3b: monadic field-assign splitter.
        //
        // When `self.field = <monadic_expr>` (e.g., `self.epoch = checked_add(...)`,
        // `self.memory_used = saturating_add(...)`), the pure-value guard in
        // `try_extract_any_field_assign` skips it.  We detect and split it here:
        //
        //   let local_tmp_N ← <monadic_expr>
        //   let self := { self with field := local_tmp_N }
        //
        // This runs AFTER `rewrite_field_assigns_recursive` (TIER 3 handles pure
        // values first) and BEFORE the Vec mutation rewrite so that the next_id
        // counter doesn't collide.
        if let Some(body) = &mut fun_def.body {
            let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
            let (new_block, new_locals) =
                rewrite_monadic_field_assigns_recursive(&body.block, self_local, &mut next_id);
            if !new_locals.is_empty() {
                if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                    eprintln!(
                        "[desugar_mut_self] TIER3b monadic-split {} field-assign(s) in: {}",
                        new_locals.len(),
                        fun_def.rust_path,
                    );
                }
                body.block = new_block;
                body.locals.extend(new_locals);
            }
        }

        // Repair lost pattern binders from `find_*_insert_pos` tuple destructures.
        //
        // styx-rustc emits `let (pos, exists) = self.find_*_insert_pos(id)` as:
        //   Assign { target: u32::MAX, value: Call(find_*_insert_pos, ...) : Tuple(Usize, Bool) }
        // but subsequent statements still reference `local_N` (pos) and `local_M` (exists)
        // without binders. This pass detects those DUMMY tuple assigns and replaces them with:
        //   Assign { target: pair_tmp, value: Call(...) }
        //   Assign { target: local_N, value: TupleField(pair_tmp, 0) }
        //   Assign { target: local_M, value: TupleField(pair_tmp, 1) }
        //
        // Runs BEFORE the Vec mutation rewrite so that local_N and local_M are in scope
        // when the Vec.insert arguments are processed.
        if let Some(body) = &mut fun_def.body {
            let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
            let mut known_locals: HashSet<LocalId> = body.locals.iter().map(|l| l.id).collect();
            let (new_block, new_locals) =
                repair_lost_pattern_binders(&body.block, &mut known_locals, &mut next_id);
            if !new_locals.is_empty() {
                if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                    eprintln!(
                        "[desugar_mut_self] repaired {} lost binder(s) in: {}",
                        new_locals.len(),
                        fun_def.rust_path,
                    );
                }
                body.block = new_block;
                body.locals.extend(new_locals);
            }
        }

        // Attempt to rewrite discarded Vec mutations at the top level of the body.
        //
        // `Expr(Call(VecPush|VecInsert|VecRemove, [Field(Local(self), "field"), ...]))`
        // → `Assign { field_new, Call(...) } + FieldAssign { self.field := field_new }`
        //
        // This runs BEFORE the `has_discarded_vec` guard so that successfully rewritten
        // functions will pass the guard and get their Ref stripped.  Functions with Vec
        // mutations nested inside If/Match/Loop branches still fail the guard and stay
        // opaque.
        if let Some(body) = &mut fun_def.body {
            let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
            let (new_block, new_locals) =
                rewrite_vec_mutations_top_level(&body.block, self_local, &mut next_id);
            if !new_locals.is_empty() {
                if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                    eprintln!(
                        "[desugar_mut_self] rewrote {} Vec mutation(s) in: {}",
                        // count FieldAssign stmts added (each PushInsert adds 1, Remove adds 1)
                        new_locals.len().saturating_sub(
                            new_locals
                                .iter()
                                .filter(|l| l.name.ends_with("_pair"))
                                .count()
                        ),
                        fun_def.rust_path,
                    );
                }
                body.block = new_block;
                body.locals.extend(new_locals);
            }
        }

        // Guard: check for discarded Vec mutations in the body.
        //
        // A discarded Vec mutation is `Stmt::Expr(Call(VecPush|VecInsert|VecRemove, ...))`.
        // The Rust `Vec::push` returns `()`, but Aeneas/StyxIR models it as
        // `Result (Vec T)`. If the result is discarded (not bound with Assign and
        // not written back via FieldAssign), the emitted Lean body will have a type
        // mismatch: the body returns `Result (Vec T)` where `Result Unit` is expected.
        //
        // Functions with discarded Vec mutations must stay opaque. We deliberately
        // do NOT strip Ref for them — this ensures `is_mut_self_desugared = false`
        // in the emitter, which triggers condition A and keeps them in FunsExternal.
        // After the rewrite above, top-level mutations are transformed; only nested
        // ones (inside If/Match/Loop) still trigger this guard.
        let has_discarded_vec = match &fun_def.body {
            None => false,
            Some(b) => has_discarded_vec_mutation_block(&b.block),
        };

        if has_discarded_vec {
            // Don't strip Ref — function stays opaque via emitter condition A.
            if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                eprintln!(
                    "[desugar_mut_self] TIER{tier} discarded-vec (skipped): {}",
                    fun_def.rust_path,
                );
            }
            continue;
        }

        // Safe to strip Ref. The body is correct:
        //   TIER 1: pure delegation wrapper (no Vec mutations in body at all).
        //   TIER 2: styx-rustc generated proper Assign+FieldAssign writeback for Vec mutations.
        //     Pattern: Assign { target: tmp, value: Field(self, "field") }  -- copy
        //              Assign { target: tmp, value: Call(Vec.push, [tmp, ...]) }  -- bound result
        //              FieldAssign { target: self, path: ["field"], value: tmp }  -- writeback
        //     The ret_ty is already Result (T × Self) with `ok (result, self)` in the body.
        //
        // Stripping Ref sets is_mut_self_desugared = true in the emitter, which prevents
        // condition A from firing. Condition B (has_vec_mutation && body_text.contains "let _ ←")
        // still catches any residual discarded mutations if somehow one slipped through.
        let self_type: StyxType = match &fun_def.params[0].ty {
            StyxType::Ref { inner, .. } => *inner.clone(),
            other => other.clone(), // Already bare (styx-rustc stripped Ref)
        };

        // Strip Ref from params[0].ty in place.
        fun_def.params[0].ty = self_type;

        if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
            if tier == 1 {
                eprintln!(
                    "[desugar_mut_self] TIER1 ref-stripped: {}",
                    fun_def.rust_path,
                );
            } else {
                eprintln!(
                    "[desugar_mut_self] TIER2 ref-stripped: {} — {} mutation site(s)",
                    fun_def.rust_path, mutation_count,
                );
            }
        }
    }
}

// ============================================================================
// Helpers
// ============================================================================

/// A detected field-mutation site: `self.field_path = value`.
#[derive(Debug)]
struct MutationSite {
    field_path: Vec<String>,
    span: StyxSpan,
}

/// Return the `LocalId` for the `&mut self` receiver, if this function has one.
///
/// The receiver is `params[0]` when `is_mut_self == true`. Its `local_id`
/// field carries the LocalId assigned by the frontend (currently `None` for all
/// functions emitted by styx-rustc, which doesn't fill that field).
///
/// When `local_id` is absent, we look at `body.locals[0]` — the first param
/// local in the body, which has its ID set from the HirId binding pattern.
/// This ID matches the `LocalId` used by `VarRef` expressions in the body (the
/// self receiver uses `ExprKind::VarRef { id: HirId { local_id: X } }` →
/// `StyxExprKind::Local(LocalId(X))`), so the pattern-matching in the Vec
/// mutation rewrite produces correct matches.
///
/// If the body has no locals (impossible in practice), we fall back to `LocalId(1)`.
fn find_mut_self_local(fun_def: &StyxFunDef) -> Option<LocalId> {
    let first = fun_def.params.first()?;
    if !first.is_mut_self {
        return None;
    }
    // Prefer the explicit local_id from the frontend (set if params[0].local_id.is_some()).
    if let Some(id) = first.local_id {
        return Some(id);
    }
    // styx-rustc does not fill in local_id for params.  Fall back to the body's first
    // local — it has the HirId-based LocalId that matches VarRef in the body.
    if let Some(body) = &fun_def.body
        && let Some(first_local) = body.locals.first() {
            if std::env::var("STYX_DEBUG_MUT_SELF").is_ok() {
                eprintln!(
                    "WARNING: {} — no local_id on &mut self param; using body local {} ({:?})",
                    fun_def.rust_path, first_local.id.0, first_local.name,
                );
            }
            return Some(first_local.id);
        }
    // Last resort (no body and no local_id — happens for bodyless extern functions,
    // but those are filtered out by find_mut_self_local's None guard).
    eprintln!(
        "WARNING: {} — no local_id on &mut self param; falling back to LocalId(1)",
        fun_def.rust_path,
    );
    Some(LocalId(1))
}

/// Walk a block, collecting FieldAssign statements that target `self_local`.
fn collect_mutation_sites_block(
    block: &StyxBlock,
    self_local: LocalId,
    sites: &mut Vec<MutationSite>,
) {
    for stmt in &block.stmts {
        collect_mutation_sites_stmt(stmt, self_local, sites);
    }
}

fn collect_mutation_sites_stmt(
    stmt: &StyxStmt,
    self_local: LocalId,
    sites: &mut Vec<MutationSite>,
) {
    match stmt {
        // `self.field_path = value` — the primary pattern we're looking for.
        StyxStmt::FieldAssign {
            target,
            field_path,
            value,
        } => {
            if *target == self_local {
                sites.push(MutationSite {
                    field_path: field_path.iter().map(|fa| fa.name.clone()).collect(),
                    span: value.span.clone(),
                });
            }
            // Still recurse into the value expression in case there are nested
            // closures with their own &mut self captures (unlikely but safe).
            collect_mutation_sites_expr(value, self_local, sites);
        }

        StyxStmt::Assign { value, .. } => {
            collect_mutation_sites_expr(value, self_local, sites);
        }
        StyxStmt::Expr(e) => collect_mutation_sites_expr(e, self_local, sites),
        StyxStmt::Return(e) => collect_mutation_sites_expr(e, self_local, sites),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            collect_mutation_sites_expr(cond, self_local, sites);
            collect_mutation_sites_block(then_block, self_local, sites);
            collect_mutation_sites_block(else_block, self_local, sites);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_mutation_sites_expr(scrutinee, self_local, sites);
            for arm in arms {
                collect_mutation_sites_block(&arm.body, self_local, sites);
            }
        }
        StyxStmt::Loop { cond, body } => {
            if let Some(c) = cond {
                collect_mutation_sites_expr(c, self_local, sites);
            }
            collect_mutation_sites_block(body, self_local, sites);
        }
        StyxStmt::Assert { cond, .. } => {
            collect_mutation_sites_expr(cond, self_local, sites);
        }
        StyxStmt::Break { .. } | StyxStmt::Continue { .. } | StyxStmt::Drop { .. } => {}
    }
}

fn collect_mutation_sites_expr(
    expr: &StyxExpr,
    self_local: LocalId,
    sites: &mut Vec<MutationSite>,
) {
    match &expr.kind {
        StyxExprKind::Block {
            stmts,
            expr: trailing,
        } => {
            for s in stmts {
                collect_mutation_sites_stmt(s, self_local, sites);
            }
            if let Some(e) = trailing {
                collect_mutation_sites_expr(e, self_local, sites);
            }
        }
        StyxExprKind::Call { args, .. } => {
            for a in args {
                collect_mutation_sites_expr(a, self_local, sites);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_mutation_sites_expr(lhs, self_local, sites);
            collect_mutation_sites_expr(rhs, self_local, sites);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand) => {
            collect_mutation_sites_expr(operand, self_local, sites);
        }
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            collect_mutation_sites_expr(base, self_local, sites);
        }
        StyxExprKind::Index { base, index } => {
            collect_mutation_sites_expr(base, self_local, sites);
            collect_mutation_sites_expr(index, self_local, sites);
        }
        StyxExprKind::StructInit { fields, .. } | StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                collect_mutation_sites_expr(e, self_local, sites);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                collect_mutation_sites_expr(e, self_local, sites);
            }
        }
        StyxExprKind::Closure { body, .. } => {
            collect_mutation_sites_expr(body, self_local, sites);
        }
        StyxExprKind::QuestionMark { inner, .. } => {
            collect_mutation_sites_expr(inner, self_local, sites);
        }
        StyxExprKind::Literal(_)
        | StyxExprKind::Local(_)
        | StyxExprKind::Global(_)
        | StyxExprKind::Unit
        | StyxExprKind::Absurd => {}
    }
}

// ============================================================================
// Discarded Vec mutation detection
// ============================================================================

/// Returns `true` if any Vec-mutation call appears as a discarded expression
/// (`StyxStmt::Expr(Call(VecMutation, ...))`) anywhere in the block.
///
/// Covers both `StyxCallee::Builtin(VecPush|VecInsert|VecRemove)` and
/// `StyxCallee::Function` calls to standard Vec / VecDeque mutation methods
/// (e.g., `std::vec::Vec::push`, `std::collections::VecDeque::push_back`).
///
/// Such patterns produce type errors in Lean because the Aeneas model returns
/// `Result (Vec T)` rather than `()`, and the function return type won't match.
fn has_discarded_vec_mutation_block(block: &StyxBlock) -> bool {
    block.stmts.iter().any(has_discarded_vec_mutation_stmt)
}

fn has_discarded_vec_mutation_stmt(stmt: &StyxStmt) -> bool {
    match stmt {
        StyxStmt::Expr(e) => has_vec_mutation_call_expr(e),
        StyxStmt::Return(e) => has_vec_mutation_call_expr(e),
        StyxStmt::If {
            then_block,
            else_block,
            ..
        } => {
            has_discarded_vec_mutation_block(then_block)
                || has_discarded_vec_mutation_block(else_block)
        }
        StyxStmt::Match { arms, .. } => arms
            .iter()
            .any(|arm| has_discarded_vec_mutation_block(&arm.body)),
        StyxStmt::Loop { body, .. } => has_discarded_vec_mutation_block(body),
        _ => false,
    }
}

/// Returns `true` if `expr` is (or contains, in a block) a discarded Vec-mutation call.
///
/// Recursion covers inline Block expressions which may embed If/Loop/Expr statements.
fn has_vec_mutation_call_expr(expr: &StyxExpr) -> bool {
    match &expr.kind {
        StyxExprKind::Call { callee, .. } => is_vec_mutation_callee(callee),
        // Inline block expression: recurse into its statements.
        StyxExprKind::Block {
            stmts,
            expr: trailing,
        } => {
            stmts.iter().any(has_discarded_vec_mutation_stmt)
                || trailing.as_deref().is_some_and(has_vec_mutation_call_expr)
        }
        _ => false,
    }
}

/// Returns `true` for callees that represent Vec / VecDeque mutation operations.
///
/// Matches both the builtin enum variants (assigned by styx-rustc for many
/// Vec ops) and the `Function` variant with a std rust_path (used when the
/// call comes through a non-generic monomorphisation or VecDeque path that
/// the frontend doesn't map to a builtin).
fn is_vec_mutation_callee(callee: &StyxCallee) -> bool {
    match callee {
        StyxCallee::Builtin(b) => {
            matches!(
                b,
                StyxBuiltinFn::VecPush | StyxBuiltinFn::VecInsert | StyxBuiltinFn::VecRemove
            )
        }
        StyxCallee::Function { rust_path, .. } => is_std_vec_mutation_path(rust_path),
        _ => false,
    }
}

/// Heuristic: does this rust_path look like a standard collection mutation method?
///
/// Covers `std::vec::Vec`, `alloc::vec::Vec`, `std::collections::VecDeque`,
/// and `alloc::collections::VecDeque` — the four namespaces styx-rustc can
/// emit for push/insert/remove/pop variants.
fn is_std_vec_mutation_path(path: &str) -> bool {
    let is_std_vec = path.contains("vec::Vec") || path.contains("VecDeque");
    if !is_std_vec {
        return false;
    }
    // Method names that mutate the collection and return the new collection
    // (or an element+collection pair).  In the Aeneas model these return
    // `Result (Vec T)` or `Result (T × Vec T)`, never `()`.
    path.contains("::push")
        || path.contains("::push_back")
        || path.contains("::push_front")
        || path.contains("::insert")
        || path.contains("::remove")
        || path.contains("::pop")
        || path.contains("::pop_back")
        || path.contains("::pop_front")
        || path.contains("::append")
        || path.contains("::extend")
        || path.contains("::drain")
        || path.contains("::retain")
        || path.contains("::truncate")
        || path.contains("::clear")
}

// ============================================================================
// TIER 3: field-assign rewrite — recursive (2026-04-15, extended 2026-04-15)
// ============================================================================

/// Rewrite `self.field = value` (plain assign) and `self.field op= rhs`
/// (compound-assign) at **any nesting depth** in `block`.
///
/// # IR Pattern (both plain and compound-assign)
///
/// styx-rustc emits both `self.field = value` and `self.field op= rhs` as:
/// ```text
/// Stmt::Expr(
///   Block {
///     stmts: [Assign { target: DUMMY, value: <new_value> }],
///     expr:  Some(Field(self_local, field))   // dead field-read (lhs marker)
///   }
/// )
/// ```
/// The `DUMMY` target (`LocalId(u32::MAX)`) signals a field write.
/// The trailing `expr: Some(Field(self_local, field))` identifies the target field.
///
/// # Rewrite
///
/// ```text
/// FieldAssign { target: self_local, field_path: [field], value: <new_value> }
/// ```
///
/// which emits as `let self := { self with field := <new_value> }`.
///
/// # Recursion
///
/// This function recurses into `If` then/else branches, `Match` arms, and `Loop`
/// bodies so that field mutations nested at any depth are rewritten.  This unlocks
/// functions like `set_blocked_mut`, `unblock_mut`, `clear_previous`, etc. where
/// the mutation appears inside a conditional branch.
///
/// Returns the total number of statements rewritten.
fn rewrite_field_assigns_recursive(block: &mut StyxBlock, self_local: LocalId) -> usize {
    let mut rewrites = 0usize;

    for stmt in block.stmts.iter_mut() {
        // First try to rewrite the statement itself.
        if let StyxStmt::Expr(ref expr) = *stmt
            && let Some((field_name, field_id, field_ty, new_value)) =
                try_extract_any_field_assign(expr, self_local)
            {
                *stmt = StyxStmt::FieldAssign {
                    target: self_local,
                    field_path: vec![FieldAccess {
                        name: field_name,
                        field_id,
                    }],
                    value: StyxExpr {
                        kind: new_value,
                        ty: field_ty,
                        span: StyxSpan::default(),
                    },
                };
                rewrites += 1;
                continue;
            }

        // Recurse into composite statement bodies.
        match stmt {
            StyxStmt::If {
                then_block,
                else_block,
                ..
            } => {
                rewrites += rewrite_field_assigns_recursive(then_block, self_local);
                rewrites += rewrite_field_assigns_recursive(else_block, self_local);
            }
            StyxStmt::Match { arms, .. } => {
                for arm in arms.iter_mut() {
                    rewrites += rewrite_field_assigns_recursive(&mut arm.body, self_local);
                }
            }
            StyxStmt::Loop { body, .. } => {
                rewrites += rewrite_field_assigns_recursive(body, self_local);
            }
            // For Assign/FieldAssign/Return etc. we don't recurse — the only
            // composite bodies that can contain field-assign statements are
            // If/Match/Loop.
            _ => {}
        }
    }
    rewrites
}

/// Try to extract ANY `self.field = value` assignment from a `Block` expression.
///
/// This is a generalisation of the original compound-assign extractor.  It accepts
/// **any pure value expression** (not just `BinOp`), so it handles:
///
/// - `self.field = EnumVariant` (e.g., `self.status = WorkflowStatus::Failure`)
/// - `self.field = local` (e.g., `self.blocked_on = Some(on)`)
/// - `self.field = None` / `self.field = Some(x)`
/// - `self.field op= rhs` (compound-assign, BinOp — already handled, still works)
///
/// # Pattern
///
/// ```text
/// Expr(Block {
///   stmts: [Assign { target: DUMMY (u32::MAX), value: <pure_expr> }],
///   expr:  Some(Field { base: Deref(Local(self_local)) | Local(self_local), field_name, ... })
/// })
/// ```
///
/// The trailing field-read serves as the lhs marker — it identifies which field
/// of `self` is being written.
///
/// # Guard: monadic values are NOT rewritten
///
/// If the new value requires monadic bind (e.g., it's a `Call`, `Block`, or
/// `QuestionMark` expression), this function returns `None` to leave the
/// statement unchanged.  Such functions will still be handled by the emitter's
/// existing text-transform passes or remain opaque with a diagnostic message.
/// The reason: `let self := { self with field := <monadic> }` is not valid
/// Lean — monadic values need `let tmp ← <monadic>` before use in struct update.
///
/// Returns `(field_name, field_id, field_ty, new_value_kind)`.
fn try_extract_any_field_assign(
    expr: &StyxExpr,
    self_local: LocalId,
) -> Option<(String, FieldId, StyxType, StyxExprKind)> {
    let StyxExprKind::Block {
        stmts,
        expr: trailing,
    } = &expr.kind
    else {
        return None;
    };

    // Exactly one stmt + exactly one trailing expr.
    if stmts.len() != 1 {
        return None;
    }
    let Some(trailing) = trailing else {
        return None;
    };

    // Stmt[0] must be Assign { target: DUMMY, value: <new_value> }
    let StyxStmt::Assign {
        target,
        value: new_value_expr,
        ..
    } = &stmts[0]
    else {
        return None;
    };
    if target.0 != u32::MAX {
        return None;
    }

    // The trailing expression must be a field read of `self_local`.
    // This identifies which field is being written.
    let (field_name, field_id, field_ty) = extract_self_field_direct(trailing, self_local)?;

    // Guard: only rewrite pure (non-monadic) values.
    // Monadic values (Call, Block, QuestionMark, Index) need monadic bind and
    // cannot be inlined into `{ self with field := <value> }`.
    if !is_pure_expr(new_value_expr) {
        return None;
    }

    // All checks pass — the new value is whatever was in the DUMMY assign.
    Some((field_name, field_id, field_ty, new_value_expr.kind.clone()))
}

/// Extract a **monadic** `self.field = <monadic_expr>` assignment.
///
/// This is the complement of `try_extract_any_field_assign` — it handles the cases
/// that `try_extract_any_field_assign` rejects (where `!is_pure_expr`).
///
/// The caller is responsible for generating:
/// ```lean
/// let local_tmp_N ← <monadic_expr>
/// let self := { self with field := local_tmp_N }
/// ```
///
/// Returns `(field_name, field_id, field_ty, monadic_expr)` where `monadic_expr`
/// is the full `StyxExpr` to be bound with `←`.
fn try_extract_monadic_field_assign(
    expr: &StyxExpr,
    self_local: LocalId,
) -> Option<(String, FieldId, StyxType, StyxExpr)> {
    let StyxExprKind::Block {
        stmts,
        expr: trailing,
    } = &expr.kind
    else {
        return None;
    };

    // Exactly one stmt + exactly one trailing expr (same structure as pure case).
    if stmts.len() != 1 {
        return None;
    }
    let Some(trailing) = trailing else {
        return None;
    };

    // Stmt[0] must be Assign { target: DUMMY, value: <monadic_value> }
    let StyxStmt::Assign {
        target,
        value: new_value_expr,
        ..
    } = &stmts[0]
    else {
        return None;
    };
    if target.0 != u32::MAX {
        return None;
    }

    // The trailing expression must be a field read of `self_local`.
    let (field_name, field_id, field_ty) = extract_self_field_direct(trailing, self_local)?;

    // Only handle monadic values — pure values are handled by try_extract_any_field_assign.
    if is_pure_expr(new_value_expr) {
        return None;
    }

    // Only handle simple Call expressions (direct monadic calls like saturating_add,
    // saturating_sub, Option::expect, checked_add that return T directly via ←).
    //
    // Block values (e.g., early-return match patterns like `match checked_add { Some(v) => v, None => return Err }`)
    // are NOT safe to split — the Block may contain early returns that must remain
    // at the expression level for the emitter to emit `ok ()` (the "dead-read" path).
    // Splitting a Block would produce `let tmp := (match ...)` with mismatched arm types.
    //
    // QuestionMark desugaring (Try::branch blocks) IS a Block in the IR, so those
    // are also excluded here and handled by the existing emitter post-processing
    // (Phase 3: `:= (match (← ...)` → `← (match (← ...)`).
    if !matches!(new_value_expr.kind, StyxExprKind::Call { .. }) {
        return None;
    }

    Some((field_name, field_id, field_ty, new_value_expr.clone()))
}

/// Rewrite `self.field = <monadic_expr>` assignments by splitting into:
/// ```lean
/// let local_tmp_N ← <monadic_expr>
/// let self := { self with field := local_tmp_N }
/// ```
///
/// This handles the case where a field's new value requires a monadic bind
/// (e.g., `self.epoch = self.epoch.checked_add(1)?` or
/// `self.memory_used = self.memory_used.saturating_add(size)`).
///
/// These cannot be inlined into Lean struct-update syntax because
/// `{ self with field := (← expr) }` is not valid Lean.
///
/// Returns `(new_block, new_locals)` — callers must extend `body.locals` with
/// `new_locals` and replace `body.block` with `new_block` when non-empty.
///
/// `next_id` is updated to allocate consecutive `LocalId`s for temporaries.
fn rewrite_monadic_field_assigns_recursive(
    block: &StyxBlock,
    self_local: LocalId,
    next_id: &mut u32,
) -> (StyxBlock, Vec<StyxLocal>) {
    let mut new_stmts: Vec<StyxStmt> = Vec::with_capacity(block.stmts.len() + 4);
    let mut new_locals: Vec<StyxLocal> = Vec::new();
    let mut changed = false;

    for stmt in &block.stmts {
        if let StyxStmt::Expr(ref expr) = *stmt
            && let Some((field_name, field_id, field_ty, monadic_expr)) =
                try_extract_monadic_field_assign(expr, self_local)
            {
                // Allocate a fresh temporary local.
                let tmp_id = LocalId(*next_id);
                *next_id += 1;
                let tmp_name = format!("local_tmp_{}", tmp_id.0);

                new_locals.push(StyxLocal {
                    id: tmp_id,
                    name: tmp_name.clone(),
                    ty: field_ty.clone(),
                });

                // let local_tmp_N ← <monadic_expr>
                new_stmts.push(StyxStmt::Assign {
                    target: tmp_id,
                    name: Some(tmp_name),
                    value: monadic_expr,
                });

                // let self := { self with field := local_tmp_N }
                new_stmts.push(StyxStmt::FieldAssign {
                    target: self_local,
                    field_path: vec![FieldAccess {
                        name: field_name,
                        field_id,
                    }],
                    value: StyxExpr::local(tmp_id, field_ty),
                });

                changed = true;
                continue;
            }

        // Recurse into composite statement bodies (same nesting as rewrite_field_assigns_recursive).
        match stmt {
            StyxStmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let (new_then, then_locals) =
                    rewrite_monadic_field_assigns_recursive(then_block, self_local, next_id);
                let (new_else, else_locals) =
                    rewrite_monadic_field_assigns_recursive(else_block, self_local, next_id);
                let any = !then_locals.is_empty() || !else_locals.is_empty();
                new_locals.extend(then_locals);
                new_locals.extend(else_locals);
                if any {
                    changed = true;
                    new_stmts.push(StyxStmt::If {
                        cond: cond.clone(),
                        then_block: new_then,
                        else_block: new_else,
                    });
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            StyxStmt::Match { scrutinee, arms } => {
                let mut new_arms = Vec::with_capacity(arms.len());
                let mut arm_changed = false;
                for arm in arms {
                    let (new_body, arm_locals) =
                        rewrite_monadic_field_assigns_recursive(&arm.body, self_local, next_id);
                    if !arm_locals.is_empty() {
                        arm_changed = true;
                        new_locals.extend(arm_locals);
                        new_arms.push(crate::ir::StyxMatchArm {
                            body: new_body,
                            ..arm.clone()
                        });
                    } else {
                        new_arms.push(arm.clone());
                    }
                }
                if arm_changed {
                    changed = true;
                }
                new_stmts.push(StyxStmt::Match {
                    scrutinee: scrutinee.clone(),
                    arms: new_arms,
                });
            }
            StyxStmt::Loop { cond, body } => {
                let (new_body, loop_locals) =
                    rewrite_monadic_field_assigns_recursive(body, self_local, next_id);
                if !loop_locals.is_empty() {
                    changed = true;
                    new_locals.extend(loop_locals);
                    new_stmts.push(StyxStmt::Loop {
                        cond: cond.clone(),
                        body: new_body,
                    });
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            _ => {
                new_stmts.push(stmt.clone());
            }
        }
    }

    if changed {
        (StyxBlock { stmts: new_stmts }, new_locals)
    } else {
        (block.clone(), Vec::new())
    }
}

/// Return `true` if `expr` is a **pure** (non-monadic) expression that can be
/// placed directly inside a Lean struct-update `{ self with field := <expr> }`.
///
/// Pure expressions:
/// - `Literal` (integers, bools, strings)
/// - `Local` (variable reference)
/// - `EnumInit` with pure fields (e.g., `.Some(x)`, `.none`)
/// - `StructInit` with pure fields
/// - `BinOp` / `UnOp` on pure operands (e.g., `a &&& b`, `~~~a`)
/// - `Field`, `TupleField`, `Deref`, `Ref` wrapping a pure expression
/// - `Tuple`, `Array` with pure elements
/// - `Cast` of a pure expression
///
/// Monadic (NOT pure):
/// - `Call` — function calls return `Result T` and need `←` bind
/// - `Block` — statement blocks are monadic
/// - `QuestionMark` — `?` desugaring uses `←` bind
/// - `Index` — indexing can panic/fail
fn is_pure_expr(expr: &StyxExpr) -> bool {
    match &expr.kind {
        StyxExprKind::Literal(_) => true,
        StyxExprKind::Local(_) => true,
        StyxExprKind::Global(_) => true,
        StyxExprKind::Unit => true,

        StyxExprKind::EnumInit { fields, .. } => fields.iter().all(|(_, e)| is_pure_expr(e)),
        StyxExprKind::StructInit { fields, .. } => fields.iter().all(|(_, e)| is_pure_expr(e)),
        StyxExprKind::Tuple(elems) => elems.iter().all(is_pure_expr),
        StyxExprKind::Array { elements, .. } => elements.iter().all(is_pure_expr),

        StyxExprKind::BinOp { lhs, rhs, .. } => is_pure_expr(lhs) && is_pure_expr(rhs),
        StyxExprKind::UnOp { operand, .. } => is_pure_expr(operand),
        StyxExprKind::Cast { operand, .. } => is_pure_expr(operand),

        StyxExprKind::Field { base, .. } => is_pure_expr(base),
        StyxExprKind::TupleField { base, .. } => is_pure_expr(base),
        StyxExprKind::Deref(inner) => is_pure_expr(inner),
        StyxExprKind::Ref { operand, .. } => is_pure_expr(operand),

        // Closures are technically pure but we conservatively reject them —
        // they're unlikely to appear as field values, and handling captures
        // adds complexity without benefit for the current use cases.
        StyxExprKind::Closure { .. } => false,

        // Monadic — cannot be placed inside struct update.
        StyxExprKind::Call { .. } => false,
        StyxExprKind::Block { .. } => false,
        StyxExprKind::QuestionMark { .. } => false,
        StyxExprKind::Index { .. } => false,

        // Absurd (unreachable) — treat as pure (unit-like, no value).
        StyxExprKind::Absurd => true,
    }
}

/// Extract `(field_name, field_id, field_ty)` from a field access on `self_local`.
///
/// Handles two forms that styx-rustc generates for `&mut self` methods:
///
/// 1. **Direct** (bare Self receiver, after Ref strip): `Field { base: Local(self_local), ... }`
/// 2. **Deref** (Ref still in place): `Field { base: Deref(Local(self_local)), ... }`
///
/// The second form is the common case for compound-assign ops (`self.bits |= mask`)
/// because styx-rustc emits the `&mut self` parameter as `Local(2): &mut Self` and
/// accesses fields through a `Deref` projection.  This pass runs BEFORE Ref stripping,
/// so the Deref form is what we actually encounter in practice.
fn extract_self_field_direct(
    expr: &StyxExpr,
    self_local: LocalId,
) -> Option<(String, FieldId, StyxType)> {
    if let StyxExprKind::Field {
        base,
        field_name,
        field_id,
    } = &expr.kind
    {
        // Case 1: Field { base: Local(self_local) }  — bare, after Ref strip or TIER 1
        if let StyxExprKind::Local(id) = &base.kind
            && *id == self_local {
                return Some((field_name.clone(), *field_id, expr.ty.clone()));
            }
        // Case 2: Field { base: Deref(Local(self_local)) }  — through &mut self Ref
        // styx-rustc emits `self.field` in &mut self methods as a Deref projection
        // because `self` has type `&mut Self` in the IR.
        if let StyxExprKind::Deref(inner) = &base.kind
            && let StyxExprKind::Local(id) = &inner.kind
                && *id == self_local {
                    return Some((field_name.clone(), *field_id, expr.ty.clone()));
                }
    }
    None
}

// ============================================================================
// Vec mutation rewrite (2026-04-13)
// ============================================================================

/// Classifies the kind of Vec mutation for the rewrite.
///
/// - `PushInsert`: `Vec.push` / `Vec.insert` — result is `Vec T` (after `←` bind)
/// - `Remove`: `Vec.remove` — result is `T × Vec T`; we extract `.2` for writeback
#[derive(Debug, Clone, PartialEq, Eq)]
enum VecMutKind {
    /// `Vec.push(v, item)` or `Vec.insert(v, idx, item)` → `Result (Vec T)`.
    /// After `←` binding, the bound value is the new `Vec T`.
    PushInsert,
    /// `Vec.remove(v, idx)` → `Result (T × Vec T)`.
    /// After `←` binding, the bound value is a pair; `.2` is the new `Vec T`.
    Remove,
}

/// Try to classify a `StyxCallee` as a Vec mutation that can be rewritten.
///
/// Returns `None` for:
/// - Non-Vec callees
/// - `pop_front` / `pop_back` / `pop` — these return `Option T` in Rust but
///   the Aeneas model is complex; the emitter already blocks them via text guards
/// - `clear`, `retain`, `truncate`, `extend`, `append`, `drain` — return `()` or
///   complex types; leave opaque for now
fn classify_vec_mut_callee(callee: &StyxCallee) -> Option<VecMutKind> {
    match callee {
        StyxCallee::Builtin(StyxBuiltinFn::VecPush) => Some(VecMutKind::PushInsert),
        StyxCallee::Builtin(StyxBuiltinFn::VecInsert) => Some(VecMutKind::PushInsert),
        StyxCallee::Builtin(StyxBuiltinFn::VecRemove) => Some(VecMutKind::Remove),
        StyxCallee::Function { rust_path, .. } => {
            if !is_std_vec_mutation_path(rust_path) {
                return None;
            }
            // push / insert variants — result is Vec T
            if rust_path.contains("::push") || rust_path.contains("::insert") {
                Some(VecMutKind::PushInsert)
            // remove variant — result is (T, Vec T)
            } else if rust_path.contains("::remove") {
                Some(VecMutKind::Remove)
            } else {
                // pop/pop_back/pop_front/clear/retain/etc. — too complex, leave opaque
                None
            }
        }
        _ => None,
    }
}

/// If `expr`'s first argument is a field access on `self_local`, extract the
/// field name, field id, and field type.
///
/// Handles both the direct case `Field { base: Local(self_local) }` and the
/// Ref-wrapped case `Ref { operand: Field { base: Local(self_local) } }` (which
/// styx-rustc may emit for `&mut self.field` before erasing the `&mut`).
fn extract_self_field_arg(
    args: &[StyxExpr],
    self_local: LocalId,
) -> Option<(String, FieldId, StyxType)> {
    let first = args.first()?;
    // Helper: check if an expr is Local(self_local) or Deref(Local(self_local))
    let is_self_base = |e: &StyxExpr| -> bool {
        match &e.kind {
            StyxExprKind::Local(id) => *id == self_local,
            StyxExprKind::Deref(inner) => matches!(&inner.kind, StyxExprKind::Local(id) if *id == self_local),
            _ => false,
        }
    };
    // Direct: Field { base: Local(self_local) | Deref(Local(self_local)), field_name, field_id }
    if let StyxExprKind::Field {
        base,
        field_name,
        field_id,
    } = &first.kind
        && is_self_base(base) {
            return Some((field_name.clone(), *field_id, first.ty.clone()));
        }
    // Ref-wrapped: Ref { operand: Field { base: Local(self_local) | Deref(Local(self_local)) } }
    if let StyxExprKind::Ref { operand, .. } = &first.kind
        && let StyxExprKind::Field {
            base,
            field_name,
            field_id,
        } = &operand.kind
            && is_self_base(base) {
                return Some((field_name.clone(), *field_id, operand.ty.clone()));
            }
    None
}

/// Rewrite discarded Vec mutations **at the top level** of `block` into proper
/// `Assign + FieldAssign` pairs.
///
/// Only top-level `StyxStmt::Expr(Call(VecMut, [Field(Local(self_local), ...), ...]))`
/// statements are transformed.  Mutations nested inside `If`/`Match`/`Loop` require
/// state threading through all branches and are intentionally left unchanged — such
/// functions will still fail the `has_discarded_vec` guard and remain opaque.
///
/// Returns `(new_block, new_locals)`:
/// - `new_block`: the transformed block (same as `block` if nothing changed)
/// - `new_locals`: fresh `StyxLocal` entries to append to `fun_def.body.locals`
///   (empty if nothing changed)
///
/// `next_id` is updated to allocate consecutive `LocalId`s for temporaries.
fn rewrite_vec_mutations_top_level(
    block: &StyxBlock,
    self_local: LocalId,
    next_id: &mut u32,
) -> (StyxBlock, Vec<StyxLocal>) {
    let mut new_stmts: Vec<StyxStmt> = Vec::with_capacity(block.stmts.len() + 4);
    let mut new_locals: Vec<StyxLocal> = Vec::new();

    for stmt in &block.stmts {
        if let Some((rewritten, locals)) = rewrite_vec_mutation_stmt(stmt, self_local, next_id) {
            new_stmts.extend(rewritten);
            new_locals.extend(locals);
            continue;
        }
        // Recurse into If/Match/Loop to rewrite nested Vec mutations.
        match stmt {
            StyxStmt::If {
                cond,
                then_block,
                else_block,
            } => {
                let (new_then, then_locals) =
                    rewrite_vec_mutations_top_level(then_block, self_local, next_id);
                let (new_else, else_locals) =
                    rewrite_vec_mutations_top_level(else_block, self_local, next_id);
                if !then_locals.is_empty() || !else_locals.is_empty() {
                    new_locals.extend(then_locals);
                    new_locals.extend(else_locals);
                    new_stmts.push(StyxStmt::If {
                        cond: cond.clone(),
                        then_block: new_then,
                        else_block: new_else,
                    });
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            StyxStmt::Match {
                scrutinee,
                arms,
            } => {
                let mut any_changed = false;
                let mut new_arms: Vec<StyxMatchArm> = Vec::with_capacity(arms.len());
                for arm in arms {
                    let (new_body, arm_locals) =
                        rewrite_vec_mutations_top_level(&arm.body, self_local, next_id);
                    if !arm_locals.is_empty() {
                        any_changed = true;
                        new_locals.extend(arm_locals);
                    }
                    new_arms.push(StyxMatchArm {
                        pattern: arm.pattern.clone(),
                        guard: arm.guard.clone(),
                        body: new_body,
                    });
                }
                if any_changed {
                    new_stmts.push(StyxStmt::Match {
                        scrutinee: scrutinee.clone(),
                        arms: new_arms,
                    });
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            StyxStmt::Loop { cond, body } => {
                let (new_body, loop_locals) =
                    rewrite_vec_mutations_top_level(body, self_local, next_id);
                if !loop_locals.is_empty() {
                    new_locals.extend(loop_locals);
                    new_stmts.push(StyxStmt::Loop {
                        cond: cond.clone(),
                        body: new_body,
                    });
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            StyxStmt::Return(expr) => {
                if let Some((new_expr, ret_locals)) =
                    rewrite_vec_mutations_in_expr(expr, self_local, next_id)
                {
                    new_locals.extend(ret_locals);
                    new_stmts.push(StyxStmt::Return(new_expr));
                } else {
                    new_stmts.push(stmt.clone());
                }
            }
            _ => {
                new_stmts.push(stmt.clone());
            }
        }
    }

    if new_locals.is_empty() {
        (block.clone(), Vec::new())
    } else {
        (StyxBlock { stmts: new_stmts }, new_locals)
    }
}

fn rewrite_vec_mutations_in_expr(
    expr: &StyxExpr,
    self_local: LocalId,
    next_id: &mut u32,
) -> Option<(StyxExpr, Vec<StyxLocal>)> {
    if let StyxExprKind::Block { stmts, expr: trailing } = &expr.kind {
        let inner_block = StyxBlock { stmts: stmts.clone() };
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&inner_block, self_local, next_id);
        if !new_locals.is_empty() {
            return Some((
                StyxExpr {
                    kind: StyxExprKind::Block {
                        stmts: new_block.stmts,
                        expr: trailing.clone(),
                    },
                    ty: expr.ty.clone(),
                    span: expr.span.clone(),
                },
                new_locals,
            ));
        }
    }
    None
}

fn rewrite_vec_mutation_stmt(
    stmt: &StyxStmt,
    self_local: LocalId,
    next_id: &mut u32,
) -> Option<(Vec<StyxStmt>, Vec<StyxLocal>)> {
    let call_expr = match stmt {
        StyxStmt::Expr(e) => e,
        _ => return None,
    };
    let (callee, args) = match &call_expr.kind {
        StyxExprKind::Call { callee, args, .. } => (callee, args),
        _ => return None,
    };
    let kind = classify_vec_mut_callee(callee)?;
    let (field_name, field_id, field_ty) = extract_self_field_arg(args, self_local)?;

    let mut new_stmts = Vec::new();
    let mut new_locals = Vec::new();

    match kind {
        VecMutKind::PushInsert => {
            let tmp_id = LocalId(*next_id);
            *next_id += 1;
            let tmp_name = format!("{field_name}_new");

            new_locals.push(StyxLocal {
                id: tmp_id,
                name: tmp_name.clone(),
                ty: field_ty.clone(),
            });
            new_stmts.push(StyxStmt::Assign {
                target: tmp_id,
                name: Some(tmp_name),
                value: call_expr.clone(),
            });
            new_stmts.push(StyxStmt::FieldAssign {
                target: self_local,
                field_path: vec![FieldAccess {
                    name: field_name,
                    field_id,
                }],
                value: StyxExpr::local(tmp_id, field_ty),
            });
        }
        VecMutKind::Remove => {
            let pair_id = LocalId(*next_id);
            *next_id += 1;
            let vec_id = LocalId(*next_id);
            *next_id += 1;
            let pair_name = format!("{field_name}_pair");
            let vec_name = format!("{field_name}_new");

            new_locals.push(StyxLocal {
                id: pair_id,
                name: pair_name.clone(),
                ty: field_ty.clone(),
            });
            new_locals.push(StyxLocal {
                id: vec_id,
                name: vec_name.clone(),
                ty: field_ty.clone(),
            });

            let pair_expr = StyxExpr::local(pair_id, field_ty.clone());
            let vec_from_pair = StyxExpr {
                kind: StyxExprKind::TupleField {
                    base: Box::new(pair_expr),
                    index: 1,
                },
                ty: field_ty.clone(),
                span: StyxSpan::default(),
            };

            new_stmts.push(StyxStmt::Assign {
                target: pair_id,
                name: Some(pair_name),
                value: call_expr.clone(),
            });
            new_stmts.push(StyxStmt::Assign {
                target: vec_id,
                name: Some(vec_name),
                value: vec_from_pair,
            });
            new_stmts.push(StyxStmt::FieldAssign {
                target: self_local,
                field_path: vec![FieldAccess {
                    name: field_name,
                    field_id,
                }],
                value: StyxExpr::local(vec_id, field_ty),
            });
        }
    }

    Some((new_stmts, new_locals))
}

// ============================================================================
// Lost pattern binder repair (2026-04-26)
// ============================================================================

/// Return true if `expr` is a Call whose callee rust_path matches
/// `.*::find_.*_insert_pos` — the styx-rustc pattern for the tuple destructure
/// `let (pos, exists) = self.find_*_insert_pos(id)`.
fn is_find_insert_pos_call(expr: &StyxExpr) -> bool {
    if let StyxExprKind::Call { callee, .. } = &expr.kind
        && let StyxCallee::Function { rust_path, .. } = callee {
            return rust_path.contains("::find_") && rust_path.contains("_insert_pos");
        }
    false
}

/// Collect all `LocalId` values referenced (used, not just declared) in `block`.
/// Recursively descends into If/Match/Loop/Block-expression sub-structures.
fn collect_all_local_refs_in_block(block: &StyxBlock, refs: &mut HashSet<LocalId>) {
    for stmt in &block.stmts {
        collect_all_local_refs_in_stmt(stmt, refs);
    }
}

fn collect_all_local_refs_in_stmt(stmt: &StyxStmt, refs: &mut HashSet<LocalId>) {
    match stmt {
        StyxStmt::Assign { value, .. } => collect_all_local_refs_in_expr(value, refs),
        StyxStmt::FieldAssign { value, .. } => collect_all_local_refs_in_expr(value, refs),
        StyxStmt::Expr(e) => collect_all_local_refs_in_expr(e, refs),
        StyxStmt::Return(e) => collect_all_local_refs_in_expr(e, refs),
        StyxStmt::If { cond, then_block, else_block } => {
            collect_all_local_refs_in_expr(cond, refs);
            collect_all_local_refs_in_block(then_block, refs);
            collect_all_local_refs_in_block(else_block, refs);
        }
        StyxStmt::Match { scrutinee, arms } => {
            collect_all_local_refs_in_expr(scrutinee, refs);
            for arm in arms {
                collect_all_local_refs_in_block(&arm.body, refs);
            }
        }
        StyxStmt::Loop { cond, body } => {
            if let Some(c) = cond {
                collect_all_local_refs_in_expr(c, refs);
            }
            collect_all_local_refs_in_block(body, refs);
        }
        StyxStmt::Assert { cond, .. } => collect_all_local_refs_in_expr(cond, refs),
        StyxStmt::Break { .. } | StyxStmt::Continue { .. } | StyxStmt::Drop { .. } => {}
    }
}

fn collect_all_local_refs_in_expr(expr: &StyxExpr, refs: &mut HashSet<LocalId>) {
    match &expr.kind {
        StyxExprKind::Local(id) => { refs.insert(*id); }
        StyxExprKind::Call { args, .. } => {
            for a in args { collect_all_local_refs_in_expr(a, refs); }
        }
        StyxExprKind::Block { stmts, expr: trailing } => {
            for s in stmts { collect_all_local_refs_in_stmt(s, refs); }
            if let Some(e) = trailing { collect_all_local_refs_in_expr(e, refs); }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            collect_all_local_refs_in_expr(lhs, refs);
            collect_all_local_refs_in_expr(rhs, refs);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand) => collect_all_local_refs_in_expr(operand, refs),
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            collect_all_local_refs_in_expr(base, refs);
        }
        StyxExprKind::Index { base, index } => {
            collect_all_local_refs_in_expr(base, refs);
            collect_all_local_refs_in_expr(index, refs);
        }
        StyxExprKind::StructInit { fields, .. } | StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields { collect_all_local_refs_in_expr(e, refs); }
        }
        StyxExprKind::Tuple(elems) | StyxExprKind::Array { elements: elems, .. } => {
            for e in elems { collect_all_local_refs_in_expr(e, refs); }
        }
        StyxExprKind::Closure { body, .. } => collect_all_local_refs_in_expr(body, refs),
        StyxExprKind::QuestionMark { inner, .. } => collect_all_local_refs_in_expr(inner, refs),
        StyxExprKind::Literal(_)
        | StyxExprKind::Global(_)
        | StyxExprKind::Unit
        | StyxExprKind::Absurd => {}
    }
}

/// Repair DUMMY assigns from `find_*_insert_pos` calls with Tuple-typed results.
///
/// Finds every `Assign { target: u32::MAX, value: Call(find_*_insert_pos, ..) : Tuple(T0, T1) }`
/// in the top-level of `block` and replaces it with:
///   `Assign { target: pair_tmp, value: <call> }`
///   `Assign { target: missing[0], value: TupleField(pair_tmp, 0) : T0 }`
///   `Assign { target: missing[1], value: TupleField(pair_tmp, 1) : T1 }`
///
/// The `missing` locals are determined by scanning all Local references in the block,
/// subtracting both `known` (body.locals) AND all non-DUMMY Assign targets in the block
/// (locals already bound by explicit let-bindings before or after the DUMMY assign).
/// The remainder is sorted by LocalId and the first N are taken (N = tuple arity).
/// This exploits the compiler's sequential ID assignment: lower LocalId ↔ earlier
/// declared pattern variable ↔ earlier tuple element.
///
/// The `known` set is updated with every synthesized local so that multiple DUMMY assigns
/// in the same function are repaired with distinct missing locals.
fn repair_lost_pattern_binders(
    block: &StyxBlock,
    known: &mut HashSet<LocalId>,
    next_id: &mut u32,
) -> (StyxBlock, Vec<StyxLocal>) {
    // Pre-scan all non-DUMMY Assign targets in the block.
    // These locals already have binders (e.g. `let local_12 ← cap.id()`) and must
    // not be mistaken for "missing" projection targets.
    for stmt in &block.stmts {
        if let StyxStmt::Assign { target, .. } = stmt
            && target.0 != u32::MAX {
                known.insert(*target);
            }
    }

    // Pre-compute all Local refs to find candidates for missing binders.
    let mut all_refs: HashSet<LocalId> = HashSet::new();
    collect_all_local_refs_in_block(block, &mut all_refs);

    let mut missing: Vec<LocalId> = all_refs
        .into_iter()
        .filter(|id| id.0 != u32::MAX && !known.contains(id))
        .collect();
    missing.sort_by_key(|id| id.0);
    missing.dedup();

    if missing.is_empty() {
        return (block.clone(), Vec::new());
    }

    let mut new_stmts: Vec<StyxStmt> = Vec::with_capacity(block.stmts.len() + 8);
    let mut new_locals: Vec<StyxLocal> = Vec::new();
    let mut changed = false;

    for stmt in &block.stmts {
        // Detect: DUMMY assign from a find_*_insert_pos call with Tuple result type.
        if let StyxStmt::Assign { target, value, .. } = stmt
            && target.0 == u32::MAX && is_find_insert_pos_call(value)
                && let StyxType::Tuple(ref elems) = value.ty {
                    // Take the first N missing locals (N = tuple arity).
                    // known is updated as we go so each DUMMY assign gets distinct locals.
                    let proj_ids: Vec<LocalId> = missing
                        .iter()
                        .filter(|id| !known.contains(*id))
                        .cloned()
                        .take(elems.len())
                        .collect();

                    if proj_ids.len() == elems.len() {
                        // Allocate a fresh local for the whole tuple.
                        let pair_id = LocalId(*next_id);
                        *next_id += 1;

                        new_locals.push(StyxLocal {
                            id: pair_id,
                            name: "insert_pos_pair".to_string(),
                            ty: value.ty.clone(),
                        });
                        known.insert(pair_id);

                        // let insert_pos_pair ← find_*_insert_pos(...)
                        new_stmts.push(StyxStmt::Assign {
                            target: pair_id,
                            name: Some("insert_pos_pair".to_string()),
                            value: value.clone(),
                        });

                        // let local_N := insert_pos_pair.i
                        for (i, (proj_id, elem_ty)) in
                            proj_ids.iter().zip(elems.iter()).enumerate()
                        {
                            let proj_name = format!("local_{}", proj_id.0);
                            new_locals.push(StyxLocal {
                                id: *proj_id,
                                name: proj_name.clone(),
                                ty: elem_ty.clone(),
                            });
                            known.insert(*proj_id);

                            new_stmts.push(StyxStmt::Assign {
                                target: *proj_id,
                                name: Some(proj_name),
                                value: StyxExpr {
                                    kind: StyxExprKind::TupleField {
                                        base: Box::new(StyxExpr::local(
                                            pair_id,
                                            value.ty.clone(),
                                        )),
                                        index: i as u32,
                                    },
                                    ty: elem_ty.clone(),
                                    span: StyxSpan::default(),
                                },
                            });
                        }

                        changed = true;
                        continue;
                    }
                }

        new_stmts.push(stmt.clone());
    }

    if changed {
        (StyxBlock { stmts: new_stmts }, new_locals)
    } else {
        (block.clone(), Vec::new())
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    // -----------------------------------------------------------------------
    // Helpers for building minimal StyxIR nodes
    // -----------------------------------------------------------------------

    fn self_param(self_local: LocalId) -> StyxParam {
        StyxParam {
            name: "self_".to_string(),
            ty: StyxType::Ref {
                is_mut: true,
                inner: Box::new(StyxType::Unit), // placeholder Self type
            },
            is_mut_self: true,
            local_id: Some(self_local),
        }
    }

    fn field_expr(self_local: LocalId, field_name: &str) -> StyxExpr {
        StyxExpr {
            kind: StyxExprKind::Field {
                base: Box::new(StyxExpr::local(self_local, StyxType::Unit)),
                field_name: field_name.to_string(),
                field_id: FieldId(0),
            },
            ty: StyxType::Unit, // placeholder Vec<T>
            span: StyxSpan::default(),
        }
    }

    fn item_local(id: u32) -> StyxExpr {
        StyxExpr::local(LocalId(id), StyxType::Unit)
    }

    fn vec_push_call(vec_expr: StyxExpr, item: StyxExpr) -> StyxExpr {
        StyxExpr {
            kind: StyxExprKind::Call {
                callee: StyxCallee::Builtin(StyxBuiltinFn::VecPush),
                args: vec![vec_expr, item],
                type_args: vec![],
            },
            ty: StyxType::Unit, // placeholder Result (Vec T)
            span: StyxSpan::default(),
        }
    }

    fn vec_insert_call(vec_expr: StyxExpr, idx: StyxExpr, item: StyxExpr) -> StyxExpr {
        StyxExpr {
            kind: StyxExprKind::Call {
                callee: StyxCallee::Builtin(StyxBuiltinFn::VecInsert),
                args: vec![vec_expr, idx, item],
                type_args: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        }
    }

    fn vec_remove_call(vec_expr: StyxExpr, idx: StyxExpr) -> StyxExpr {
        StyxExpr {
            kind: StyxExprKind::Call {
                callee: StyxCallee::Builtin(StyxBuiltinFn::VecRemove),
                args: vec![vec_expr, idx],
                type_args: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        }
    }

    fn make_body(stmts: Vec<StyxStmt>, num_locals: u32) -> StyxBody {
        let locals = (0..num_locals)
            .map(|i| StyxLocal {
                id: LocalId(i),
                name: format!("local_{i}"),
                ty: StyxType::Unit,
            })
            .collect();
        StyxBody {
            locals,
            block: StyxBlock { stmts },
        }
    }

    fn make_fun(rust_path: &str, self_local: LocalId, body: StyxBody) -> StyxFunDef {
        StyxFunDef {
            id: FunId(0),
            rust_path: rust_path.to_string(),
            name: rust_path.to_string(),
            generics: StyxGenerics::empty(),
            params: vec![self_param(self_local)],
            ret_ty: StyxType::Unit,
            body: Some(body),
            is_recursive: false,
            span: StyxSpan::default(),
        }
    }

    // -----------------------------------------------------------------------
    // Vec.push rewrite tests
    // -----------------------------------------------------------------------

    #[test]
    fn test_rewrite_vec_push_top_level() {
        let self_id = LocalId(1);
        let item_id = LocalId(2);

        // Build: Expr(Call(VecPush, [Field(Local(self), "pending"), Local(item)]))
        let push_call = vec_push_call(field_expr(self_id, "pending"), item_local(item_id.0));
        let body = make_body(vec![StyxStmt::Expr(push_call)], 3);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        // Should produce 2 stmts: Assign + FieldAssign
        assert_eq!(new_block.stmts.len(), 2, "expected Assign + FieldAssign");
        assert!(matches!(&new_block.stmts[0], StyxStmt::Assign { .. }));
        assert!(
            matches!(&new_block.stmts[1], StyxStmt::FieldAssign { target, .. } if *target == self_id)
        );
        // One new local
        assert_eq!(new_locals.len(), 1);
        assert_eq!(new_locals[0].name, "pending_new");
    }

    #[test]
    fn test_rewrite_vec_insert_top_level() {
        let self_id = LocalId(1);
        let idx_id = LocalId(2);
        let item_id = LocalId(3);

        let insert_call = vec_insert_call(
            field_expr(self_id, "entries"),
            item_local(idx_id.0),
            item_local(item_id.0),
        );
        let body = make_body(vec![StyxStmt::Expr(insert_call)], 4);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        assert_eq!(new_block.stmts.len(), 2);
        assert_eq!(new_locals.len(), 1);
        assert_eq!(new_locals[0].name, "entries_new");
    }

    #[test]
    fn test_rewrite_vec_remove_top_level() {
        let self_id = LocalId(1);
        let idx_id = LocalId(2);

        let remove_call = vec_remove_call(field_expr(self_id, "caps"), item_local(idx_id.0));
        let body = make_body(vec![StyxStmt::Expr(remove_call)], 3);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        // Remove → 3 stmts: Assign(pair) + Assign(vec) + FieldAssign
        assert_eq!(
            new_block.stmts.len(),
            3,
            "expected pair-assign, vec-assign, FieldAssign"
        );
        assert!(matches!(&new_block.stmts[0], StyxStmt::Assign { target, .. } if target.0 == 3));
        assert!(matches!(&new_block.stmts[1], StyxStmt::Assign { target, .. } if target.0 == 4));
        // The middle Assign should use TupleField index 1 (emits as .2)
        if let StyxStmt::Assign { value, .. } = &new_block.stmts[1] {
            assert!(matches!(
                &value.kind,
                StyxExprKind::TupleField { index: 1, .. }
            ));
        }
        assert!(
            matches!(&new_block.stmts[2], StyxStmt::FieldAssign { target, .. } if *target == self_id)
        );
        // Two new locals: pair + vec
        assert_eq!(new_locals.len(), 2);
        assert_eq!(new_locals[0].name, "caps_pair");
        assert_eq!(new_locals[1].name, "caps_new");
    }

    #[test]
    fn test_no_rewrite_if_not_self_field() {
        let self_id = LocalId(1);
        let other_id = LocalId(3); // different local, not self

        // Push on a non-self local — should NOT be rewritten
        let push_call = StyxExpr {
            kind: StyxExprKind::Call {
                callee: StyxCallee::Builtin(StyxBuiltinFn::VecPush),
                args: vec![item_local(other_id.0), item_local(2)],
                type_args: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        };
        let body = make_body(vec![StyxStmt::Expr(push_call)], 4);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        // No rewrite — block unchanged
        assert_eq!(
            new_block.stmts.len(),
            1,
            "should not rewrite non-self field push"
        );
        assert!(new_locals.is_empty());
    }

    #[test]
    fn test_no_rewrite_nested_in_if() {
        let self_id = LocalId(1);

        // Push nested inside an If — top-level rewrite should NOT touch it
        let push_call = vec_push_call(field_expr(self_id, "pending"), item_local(2));
        let if_stmt = StyxStmt::If {
            cond: StyxExpr::unit(),
            then_block: StyxBlock {
                stmts: vec![StyxStmt::Expr(push_call)],
            },
            else_block: StyxBlock::empty(),
        };
        let body = make_body(vec![if_stmt], 3);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        // Top-level stmt is If, not Expr — no rewrite
        assert_eq!(new_block.stmts.len(), 1);
        assert!(new_locals.is_empty(), "nested push should not be rewritten");
        // The nested If still has the push — has_discarded_vec will catch it
        assert!(has_discarded_vec_mutation_block(&new_block));
    }

    #[test]
    fn test_mixed_top_level_and_nested() {
        let self_id = LocalId(1);

        // First stmt: top-level push (rewriteable)
        let push = vec_push_call(field_expr(self_id, "pending"), item_local(2));
        // Second stmt: if containing another push (not rewriteable at top level)
        let nested_push = vec_push_call(field_expr(self_id, "log"), item_local(2));
        let if_stmt = StyxStmt::If {
            cond: StyxExpr::unit(),
            then_block: StyxBlock {
                stmts: vec![StyxStmt::Expr(nested_push)],
            },
            else_block: StyxBlock::empty(),
        };

        let body = make_body(vec![StyxStmt::Expr(push), if_stmt], 3);

        let mut next_id = body.locals.iter().map(|l| l.id.0 + 1).max().unwrap_or(0);
        let (new_block, new_locals) =
            rewrite_vec_mutations_top_level(&body.block, self_id, &mut next_id);

        // Top-level push → 2 stmts; If → 1 stmt = 3 total
        assert_eq!(
            new_block.stmts.len(),
            3,
            "Assign + FieldAssign + original If"
        );
        assert_eq!(new_locals.len(), 1);
        // The If is still there and still has nested discarded vec — function stays opaque
        assert!(
            has_discarded_vec_mutation_block(&new_block),
            "nested push inside If should still fail discarded-vec guard"
        );
    }

    // -----------------------------------------------------------------------
    // TIER 3: scalar compound-assign tests
    // -----------------------------------------------------------------------

    /// Build a scalar compound-assign expression as styx-rustc would emit it.
    ///
    /// Represents `self.field op= rhs` → `Block { [Assign(DUMMY, BinOp(op, self.field, rhs))], self.field }`
    fn scalar_compound_assign_expr(
        self_local: LocalId,
        field_name: &str,
        op: StyxBinOp,
        rhs: StyxExpr,
    ) -> StyxExpr {
        let lhs = field_expr(self_local, field_name);
        let binop = StyxExpr {
            kind: StyxExprKind::BinOp {
                op,
                lhs: Box::new(lhs.clone()),
                rhs: Box::new(rhs),
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        };
        StyxExpr {
            kind: StyxExprKind::Block {
                stmts: vec![StyxStmt::Assign {
                    target: LocalId(u32::MAX),
                    name: None,
                    value: binop,
                }],
                expr: Some(Box::new(lhs)),
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        }
    }

    #[test]
    fn test_tier3_scalar_bitor_assign_top_level() {
        let self_id = LocalId(1);
        let mask_id = LocalId(2);

        // Simulate: self.bits |= mask  →  Block { [Assign(DUMMY, BitOr(self.bits, mask))], self.bits }
        let compound =
            scalar_compound_assign_expr(self_id, "bits", StyxBinOp::BitOr, item_local(mask_id.0));
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(compound)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 1, "should rewrite 1 compound-assign");
        assert_eq!(
            block.stmts.len(),
            1,
            "stmt count unchanged (rewrite in-place)"
        );
        // The stmt must now be FieldAssign targeting self_id
        let Some(StyxStmt::FieldAssign {
            target,
            field_path,
            value,
        }) = block.stmts.first()
        else {
            panic!("expected FieldAssign, got {:?}", block.stmts[0]);
        };
        assert_eq!(*target, self_id);
        assert_eq!(field_path.len(), 1);
        assert_eq!(field_path[0].name, "bits");
        // Value must be a BinOp (the new bits expression)
        assert!(matches!(
            &value.kind,
            StyxExprKind::BinOp {
                op: StyxBinOp::BitOr,
                ..
            }
        ));
    }

    #[test]
    fn test_tier3_scalar_bitand_assign_top_level() {
        let self_id = LocalId(1);
        let mask_id = LocalId(2);

        // Simulate: self.bits &= !mask
        let compound =
            scalar_compound_assign_expr(self_id, "bits", StyxBinOp::BitAnd, item_local(mask_id.0));
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(compound)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 1);
        assert!(matches!(&block.stmts[0],
            StyxStmt::FieldAssign { target, field_path, value }
            if *target == self_id
                && field_path[0].name == "bits"
                && matches!(&value.kind, StyxExprKind::BinOp { op: StyxBinOp::BitAnd, .. })
        ));
    }

    #[test]
    fn test_tier3_no_rewrite_non_self_field() {
        let self_id = LocalId(1);
        let other_id = LocalId(3); // not self

        // Compound assign on a non-self local — should NOT be rewritten
        let compound =
            scalar_compound_assign_expr(other_id, "bits", StyxBinOp::BitOr, item_local(2));
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(compound)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 0, "should not rewrite non-self field assignment");
        assert!(matches!(&block.stmts[0], StyxStmt::Expr(_)));
    }

    /// Build a plain field-assign expression: `Block { [Assign(DUMMY, value)], Field(self, field) }`
    /// This represents `self.field = value` in styx-rustc IR (plain assign, no BinOp).
    fn plain_field_assign_expr(self_local: LocalId, field_name: &str, value: StyxExpr) -> StyxExpr {
        let lhs_field = field_expr(self_local, field_name);
        StyxExpr {
            kind: StyxExprKind::Block {
                stmts: vec![StyxStmt::Assign {
                    target: LocalId(u32::MAX),
                    name: None,
                    value,
                }],
                expr: Some(Box::new(lhs_field)),
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        }
    }

    #[test]
    fn test_tier3_plain_enum_assign_top_level() {
        // Simulate: self.status = .Failure (pure EnumInit value)
        let self_id = LocalId(1);
        let enum_value = StyxExpr {
            kind: StyxExprKind::EnumInit {
                type_id: crate::ir::TypeId(42),
                variant_id: crate::ir::VariantId(1),
                fields: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        };
        let assign_expr = plain_field_assign_expr(self_id, "status", enum_value);
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(assign_expr)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 1, "plain EnumInit assign should be rewritten");
        assert!(matches!(
            &block.stmts[0],
            StyxStmt::FieldAssign { target, field_path, value }
            if *target == self_id
                && field_path[0].name == "status"
                && matches!(&value.kind, StyxExprKind::EnumInit { .. })
        ));
    }

    #[test]
    fn test_tier3_plain_local_assign_top_level() {
        // Simulate: self.blocked_on = some_local (pure Local value)
        let self_id = LocalId(1);
        let new_val = item_local(5); // Local(5)
        let assign_expr = plain_field_assign_expr(self_id, "blocked_on", new_val);
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(assign_expr)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 1, "plain Local assign should be rewritten");
        assert!(matches!(
            &block.stmts[0],
            StyxStmt::FieldAssign { target, field_path, value }
            if *target == self_id
                && field_path[0].name == "blocked_on"
                && matches!(&value.kind, StyxExprKind::Local(LocalId(5)))
        ));
    }

    #[test]
    fn test_tier3_plain_assign_nested_in_if() {
        // Simulate: if cond { self.status = .Failure } else {}
        // The assign is nested inside an If branch — must be recursively rewritten.
        let self_id = LocalId(1);
        let enum_value = StyxExpr {
            kind: StyxExprKind::EnumInit {
                type_id: crate::ir::TypeId(42),
                variant_id: crate::ir::VariantId(2),
                fields: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        };
        let assign_expr = plain_field_assign_expr(self_id, "status", enum_value);
        let cond = item_local(2);
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::If {
                cond,
                then_block: StyxBlock {
                    stmts: vec![StyxStmt::Expr(assign_expr)],
                },
                else_block: StyxBlock { stmts: vec![] },
            }],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(
            rewrites, 1,
            "nested plain assign in If-then should be rewritten"
        );
        let StyxStmt::If { then_block, .. } = &block.stmts[0] else {
            panic!("expected If stmt");
        };
        assert!(matches!(
            &then_block.stmts[0],
            StyxStmt::FieldAssign { target, field_path, .. }
            if *target == self_id && field_path[0].name == "status"
        ));
    }

    #[test]
    fn test_tier3_monadic_assign_not_rewritten() {
        // Simulate: self.epoch = checked_add(...) — a Call (monadic), should NOT be rewritten.
        let self_id = LocalId(1);
        let call_value = StyxExpr {
            kind: StyxExprKind::Call {
                callee: crate::ir::StyxCallee::Function {
                    rust_path: "core::num::checked_add".to_string(),
                    local_id: None,
                },
                type_args: vec![],
                args: vec![],
            },
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        };
        let assign_expr = plain_field_assign_expr(self_id, "epoch", call_value);
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Expr(assign_expr)],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(rewrites, 0, "monadic (Call) assign should NOT be rewritten");
        assert!(matches!(&block.stmts[0], StyxStmt::Expr(_)));
    }

    #[test]
    fn test_tier3_plain_assign_nested_in_match() {
        // Simulate: match x { Some(v) => { self.field = v } None => {} }
        // Plain assign nested inside a Match arm body.
        let self_id = LocalId(1);
        let new_val = item_local(10);
        let assign_expr = plain_field_assign_expr(self_id, "state", new_val);

        let arm_some = crate::ir::StyxMatchArm {
            pattern: crate::ir::StyxPattern::Variant {
                type_id: crate::ir::TypeId(0),
                variant_id: crate::ir::VariantId(1),
                field_bindings: vec![Some(crate::ir::PatternBinding {
                    local: LocalId(10),
                    field_name: "0".to_string(),
                })],
                rust_path: Some("core::option::Option".to_string()),
            },
            guard: None,
            body: StyxBlock {
                stmts: vec![StyxStmt::Expr(assign_expr)],
            },
        };
        let arm_none = crate::ir::StyxMatchArm {
            pattern: crate::ir::StyxPattern::Variant {
                type_id: crate::ir::TypeId(0),
                variant_id: crate::ir::VariantId(0),
                field_bindings: vec![],
                rust_path: Some("core::option::Option".to_string()),
            },
            guard: None,
            body: StyxBlock { stmts: vec![] },
        };

        let scrutinee = item_local(3);
        let mut block = StyxBlock {
            stmts: vec![StyxStmt::Match {
                scrutinee,
                arms: vec![arm_some, arm_none],
            }],
        };

        let rewrites = rewrite_field_assigns_recursive(&mut block, self_id);

        assert_eq!(
            rewrites, 1,
            "plain assign nested in Match arm should be rewritten"
        );
        let StyxStmt::Match { arms, .. } = &block.stmts[0] else {
            panic!("expected Match");
        };
        assert!(matches!(
            &arms[0].body.stmts[0],
            StyxStmt::FieldAssign { target, field_path, .. }
            if *target == self_id && field_path[0].name == "state"
        ));
    }

    #[test]
    fn test_full_desugar_mut_self_with_scalar_assign() {
        let self_id = LocalId(1);
        let mask_id = LocalId(2);

        // Simulate: self.bits |= mask
        let compound =
            scalar_compound_assign_expr(self_id, "bits", StyxBinOp::BitOr, item_local(mask_id.0));
        // Then return true (was_absent)
        let ret = StyxStmt::Return(item_local(3));
        let mut pkg = StyxPackage {
            crate_name: "test".to_string(),
            types: vec![],
            functions: vec![make_fun(
                "types::rights::Rights::insert",
                self_id,
                make_body(vec![StyxStmt::Expr(compound), ret], 4),
            )],
            trait_decls: vec![],
            trait_impls: vec![],
            globals: vec![],
            decl_groups: vec![],
        };

        desugar_mut_self(&mut pkg);

        let fun = &pkg.functions[0];
        // Ref must be stripped (no discarded Vec mutations)
        assert!(
            !matches!(&fun.params[0].ty, StyxType::Ref { is_mut: true, .. }),
            "Ref should be stripped after scalar compound-assign rewrite"
        );
        // Body should have FieldAssign (from |= rewrite) + Return
        let body = fun.body.as_ref().unwrap();
        assert_eq!(body.block.stmts.len(), 2);
        assert!(
            matches!(&body.block.stmts[0], StyxStmt::FieldAssign { target, .. } if *target == self_id),
            "first stmt should be FieldAssign; got {:?}",
            body.block.stmts[0]
        );
        assert!(matches!(&body.block.stmts[1], StyxStmt::Return(_)));
    }

    #[test]
    fn test_full_desugar_mut_self_with_vec_push() {
        let self_id = LocalId(1);
        let item_id = LocalId(2);

        let push_call = vec_push_call(field_expr(self_id, "pending"), item_local(item_id.0));

        let mut pkg = StyxPackage {
            crate_name: "test".to_string(),
            types: vec![],
            functions: vec![make_fun(
                "test::Foo::enqueue",
                self_id,
                make_body(vec![StyxStmt::Expr(push_call)], 3),
            )],
            trait_decls: vec![],
            trait_impls: vec![],
            globals: vec![],
            decl_groups: vec![],
        };

        desugar_mut_self(&mut pkg);

        let fun = &pkg.functions[0];
        // Ref should be stripped (is_mut_self_desugared = true)
        assert!(
            !matches!(&fun.params[0].ty, StyxType::Ref { is_mut: true, .. }),
            "Ref should be stripped after successful Vec push rewrite"
        );
        // Body should have Assign + FieldAssign
        let body = fun.body.as_ref().unwrap();
        assert_eq!(body.block.stmts.len(), 2);
        assert!(matches!(&body.block.stmts[0], StyxStmt::Assign { .. }));
        assert!(matches!(&body.block.stmts[1], StyxStmt::FieldAssign { .. }));
    }

    // ---- TIER 3b: monadic field-assign splitter ----

    #[test]
    fn test_tier3b_monadic_call_assign_split() {
        // Simulate: self.epoch = checked_add(...) — a Call (monadic).
        // Expected: Assign(tmp ← call) + FieldAssign(self.epoch := tmp)
        let self_id = LocalId(1);
        let call_value = StyxExpr {
            kind: StyxExprKind::Call {
                callee: crate::ir::StyxCallee::Function {
                    rust_path: "core::num::checked_add".to_string(),
                    local_id: None,
                },
                type_args: vec![],
                args: vec![],
            },
            ty: StyxType::Scalar(crate::ir::ScalarTy::U64),
            span: StyxSpan::default(),
        };
        let assign_expr = plain_field_assign_expr(self_id, "epoch", call_value);
        let block = StyxBlock {
            stmts: vec![StyxStmt::Expr(assign_expr)],
        };

        let mut next_id = 10u32;
        let (new_block, new_locals) =
            rewrite_monadic_field_assigns_recursive(&block, self_id, &mut next_id);

        assert_eq!(new_locals.len(), 1, "should allocate one temporary");
        assert_eq!(
            new_block.stmts.len(),
            2,
            "should produce Assign + FieldAssign"
        );
        assert!(
            matches!(&new_block.stmts[0], StyxStmt::Assign { target, .. } if target.0 == 10),
            "first stmt should be Assign to tmp id=10"
        );
        assert!(
            matches!(
                &new_block.stmts[1],
                StyxStmt::FieldAssign { target, field_path, .. }
                if *target == self_id && field_path[0].name == "epoch"
            ),
            "second stmt should be FieldAssign on self.epoch"
        );
        // Check the FieldAssign value is Local(tmp_id)
        if let StyxStmt::FieldAssign { value, .. } = &new_block.stmts[1] {
            assert!(
                matches!(&value.kind, StyxExprKind::Local(id) if id.0 == 10),
                "FieldAssign value should be Local(10)"
            );
        }
        assert_eq!(next_id, 11, "next_id should be incremented");
    }

    #[test]
    fn test_tier3b_pure_assign_not_split() {
        // Pure assigns should NOT be touched by the monadic splitter.
        let self_id = LocalId(1);
        let pure_value = item_local(5);
        let assign_expr = plain_field_assign_expr(self_id, "field", pure_value);
        let block = StyxBlock {
            stmts: vec![StyxStmt::Expr(assign_expr)],
        };

        let mut next_id = 10u32;
        let (_, new_locals) =
            rewrite_monadic_field_assigns_recursive(&block, self_id, &mut next_id);

        assert!(
            new_locals.is_empty(),
            "pure assigns should not be touched by monadic splitter"
        );
        assert_eq!(next_id, 10, "next_id should be unchanged");
    }

    #[test]
    fn test_full_desugar_mut_self_monadic_field_assign() {
        // Integration test: full desugar_mut_self with a monadic field assign.
        // Simulate: self.epoch = checked_add(self.epoch, 1) — a Call (monadic).
        let self_id = LocalId(2);
        let call_value = StyxExpr {
            kind: StyxExprKind::Call {
                callee: crate::ir::StyxCallee::Function {
                    rust_path: "core::num::u64::checked_add".to_string(),
                    local_id: None,
                },
                type_args: vec![],
                args: vec![],
            },
            ty: StyxType::Scalar(crate::ir::ScalarTy::U64),
            span: StyxSpan::default(),
        };
        let assign_expr = plain_field_assign_expr(self_id, "epoch", call_value);
        let mut pkg = StyxPackage {
            crate_name: "test".to_string(),
            types: vec![],
            functions: vec![make_fun(
                "state::kernel::KeyState::rotate",
                self_id,
                make_body(vec![StyxStmt::Expr(assign_expr)], 5),
            )],
            trait_decls: vec![],
            trait_impls: vec![],
            globals: vec![],
            decl_groups: vec![],
        };

        desugar_mut_self(&mut pkg);

        let fun = &pkg.functions[0];
        // Ref should be stripped (no discarded Vec mutations, monadic assign is rewritten)
        assert!(
            !matches!(&fun.params[0].ty, StyxType::Ref { is_mut: true, .. }),
            "Ref should be stripped after monadic field-assign rewrite"
        );
        let body = fun.body.as_ref().unwrap();
        // Should have Assign(tmp ← call) + FieldAssign(self.epoch := tmp)
        assert_eq!(
            body.block.stmts.len(),
            2,
            "body should have Assign + FieldAssign"
        );
        assert!(
            matches!(&body.block.stmts[0], StyxStmt::Assign { .. }),
            "first stmt should be Assign; got {:?}",
            body.block.stmts[0]
        );
        assert!(
            matches!(&body.block.stmts[1], StyxStmt::FieldAssign { .. }),
            "second stmt should be FieldAssign; got {:?}",
            body.block.stmts[1]
        );
        // The temporary should be registered in locals
        assert!(
            body.locals.iter().any(|l| l.name.starts_with("local_tmp_")),
            "a local_tmp_N local should be registered"
        );
    }
}
