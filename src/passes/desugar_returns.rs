//! DesugarReturns: convert dead-assign early returns to `StyxStmt::Return`
//! and truncate dead code after unconditional returns.
//!
//! This pass runs on `StyxPackage` before Lean emission, replacing the
//! string-matching hacks in the emitter with a correct IR transformation.
//!
//! Pre-conditions:
//!   - `LocalId(u32::MAX)` is styx-rustc's sentinel for dead assignments
//!   - Result-typed dead assigns represent early returns from `?` or `return`
//!
//! Post-conditions:
//!   - No `Assign { target: LocalId(u32::MAX), value }` with Result-typed value remains
//!   - After an unconditional `Return`, no further statements exist in that block
//!   - Expression-context blocks (StyxExprKind::Block) are NOT transformed

use crate::ir::*;

/// Run the desugar pass on all function bodies in the package.
pub fn desugar_returns(pkg: &mut StyxPackage) {
    for fun_def in &mut pkg.functions {
        if let Some(body) = &mut fun_def.body {
            desugar_block(&mut body.block);
        }
    }
}

/// Transform a statement-context block:
/// 1. Recurse into nested statements
/// 2. Convert dead-assign Result values to Return (Rule R1)
/// 3. Truncate dead code after unconditional Return (Rule R2)
fn desugar_block(block: &mut StyxBlock) {
    // Step 1: recurse into nested structures
    for stmt in &mut block.stmts {
        desugar_stmt(stmt);
    }

    // Step 2: R1 — convert dead-assign early returns
    for stmt in &mut block.stmts {
        if let StyxStmt::Assign { target, value, .. } = stmt
            && target.0 == u32::MAX && is_result_type(&value.ty) {
                let dummy = StyxExpr {
                    kind: StyxExprKind::Unit,
                    ty: StyxType::Unit,
                    span: StyxSpan {
                        file: String::new(),
                        line: 0,
                        col: 0,
                    },
                };
                let real_value = std::mem::replace(value, dummy);
                *stmt = StyxStmt::Return(real_value);
            }
    }

    // Step 3: R2 — truncate dead code after first unconditional Return
    if let Some(ret_pos) = block
        .stmts
        .iter()
        .position(|s| matches!(s, StyxStmt::Return(_)))
    {
        block.stmts.truncate(ret_pos + 1);
    }
}

/// Recurse into a statement's nested blocks and expressions.
fn desugar_stmt(stmt: &mut StyxStmt) {
    match stmt {
        StyxStmt::Assign { value, .. } => desugar_expr(value),
        StyxStmt::FieldAssign { value, .. } => desugar_expr(value),
        StyxStmt::Expr(e) => desugar_expr(e),
        StyxStmt::Return(e) => desugar_expr(e),
        StyxStmt::If {
            cond,
            then_block,
            else_block,
        } => {
            desugar_expr(cond);
            desugar_block(then_block);
            desugar_block(else_block);
        }
        StyxStmt::Match { scrutinee, arms } => {
            desugar_expr(scrutinee);
            for arm in arms {
                desugar_block(&mut arm.body);
            }
        }
        StyxStmt::Loop { cond, body } => {
            if let Some(c) = cond {
                desugar_expr(c);
            }
            desugar_block(body);
        }
        StyxStmt::Assert { cond, .. } => desugar_expr(cond),
        StyxStmt::Break { .. } | StyxStmt::Continue { .. } | StyxStmt::Drop { .. } => {}
    }
}

/// Recurse into expression trees. Does NOT apply R1/R2 to Block expressions
/// (those are expression-context, not statement-context).
fn desugar_expr(expr: &mut StyxExpr) {
    match &mut expr.kind {
        // Block expressions: recurse into stmts but do NOT apply R1/R2.
        // These are expression-context — u32::MAX assigns are let-bindings,
        // not early returns. Converting them to Return here would be wrong.
        StyxExprKind::Block {
            stmts,
            expr: trailing,
        } => {
            for s in stmts.iter_mut() {
                desugar_stmt(s);
            }
            if let Some(e) = trailing {
                desugar_expr(e);
            }
        }
        StyxExprKind::Call { args, .. } => {
            for a in args {
                desugar_expr(a);
            }
        }
        StyxExprKind::BinOp { lhs, rhs, .. } => {
            desugar_expr(lhs);
            desugar_expr(rhs);
        }
        StyxExprKind::UnOp { operand, .. }
        | StyxExprKind::Cast { operand, .. }
        | StyxExprKind::Ref { operand, .. }
        | StyxExprKind::Deref(operand) => desugar_expr(operand),
        StyxExprKind::Field { base, .. } | StyxExprKind::TupleField { base, .. } => {
            desugar_expr(base)
        }
        StyxExprKind::Index { base, index } => {
            desugar_expr(base);
            desugar_expr(index);
        }
        StyxExprKind::StructInit { fields, .. } => {
            for (_, e) in fields {
                desugar_expr(e);
            }
        }
        StyxExprKind::EnumInit { fields, .. } => {
            for (_, e) in fields {
                desugar_expr(e);
            }
        }
        StyxExprKind::Tuple(elems)
        | StyxExprKind::Array {
            elements: elems, ..
        } => {
            for e in elems {
                desugar_expr(e);
            }
        }
        StyxExprKind::Closure { body, .. } => desugar_expr(body),
        StyxExprKind::QuestionMark { inner, .. } => desugar_expr(inner),
        // Leaf expressions — nothing to recurse into
        StyxExprKind::Literal(_)
        | StyxExprKind::Local(_)
        | StyxExprKind::Global(_)
        | StyxExprKind::Unit
        | StyxExprKind::Absurd => {}
    }
}

fn is_result_type(ty: &StyxType) -> bool {
    matches!(ty, StyxType::Adt { rust_path, .. }
        if rust_path == "core::result::Result"
            || rust_path == "std::result::Result"
            || rust_path.ends_with("::Result"))
}
