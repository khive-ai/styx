// Function body extraction: TyCtxt + THIR → StyxFunDef
//
// Reads THIR for each function and converts to StyxIR.
// Requires -Zno-steal-thir (set in Callbacks::config).

use rustc_hir::def_id::LocalDefId;
use rustc_hir::RangeEnd;
use rustc_middle::thir::{self, ExprKind, PatRangeBoundary, StmtKind};
use rustc_middle::ty::{self, TyCtxt};
use rustc_ast::ast::LitKind;

use styx::ir::*;
use crate::ty_convert;
use crate::extract_types;

/// Extract a function definition from a local def_id.
pub fn extract_fun_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<StyxFunDef> {
    let global_id = def_id.to_def_id();
    let def_path = tcx.def_path_str(global_id);
    let name = tcx.item_name(global_id).to_string();
    let span = tcx.def_span(global_id);

    // Get function signature
    let fn_sig = tcx.fn_sig(global_id).skip_binder().skip_binder();

    // Determine the parent type for associated functions to detect &mut self.
    // For associated functions (methods), the parent is the impl block's self type.
    let parent_self_ty: Option<rustc_middle::ty::Ty<'_>> = tcx.impl_of_assoc(global_id)
        .map(|impl_did| tcx.type_of(impl_did).skip_binder());

    let params: Vec<StyxParam> = fn_sig
        .inputs()
        .iter()
        .enumerate()
        .map(|(i, &ty)| {
            // Detect &mut Self: first parameter is a mutable reference to the impl's self type
            let is_mut_self = if i == 0 {
                if let (ty::Ref(_, inner, mutability), Some(self_ty)) =
                    (ty.kind(), parent_self_ty)
                {
                    mutability.is_mut() && *inner == self_ty
                } else {
                    false
                }
            } else {
                false
            };
            StyxParam {
                name: format!("arg{i}"),
                ty: ty_convert::convert_ty(tcx, ty),
                is_mut_self,
                local_id: None,
            }
        })
        .collect();

    let ret_ty = ty_convert::convert_ty(tcx, fn_sig.output());
    let generics = extract_types::extract_generics(tcx, def_id);

    // Try to extract the THIR body
    let body = match tcx.thir_body(def_id) {
        Ok((thir_steal, root_expr_id)) => {
            let thir = thir_steal.borrow();
            Some(extract_body(tcx, &thir, root_expr_id))
        }
        Err(_) => {
            eprintln!("[styx-rustc] Warning: no THIR for {def_path}");
            None
        }
    };

    Some(StyxFunDef {
        id: FunId(def_id.local_def_index.as_u32()),
        rust_path: def_path,
        name,
        generics,
        params,
        ret_ty,
        body,
        is_recursive: false,
        span: extract_types::convert_span(tcx, span),
    })
}

fn extract_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &thir::Thir<'tcx>,
    root_expr: thir::ExprId,
) -> StyxBody {
    let locals: Vec<StyxLocal> = thir
        .params
        .iter()
        .enumerate()
        .map(|(i, param)| {
            let ty = ty_convert::convert_ty(tcx, param.ty);
            let name = param
                .pat
                .as_ref()
                .and_then(|pat| extract_binding_name(&pat.kind))
                .unwrap_or_else(|| format!("arg{i}"));
            // Use the HirId from the binding pattern — this matches the IDs
            // used by VarRef in the body (local_id.as_u32()).
            let id = param
                .pat
                .as_ref()
                .and_then(|pat| extract_binding_hir_id(&pat.kind))
                .unwrap_or(LocalId(i as u32));
            StyxLocal { id, name, ty }
        })
        .collect();

    let block = extract_block_from_expr(tcx, thir, root_expr);
    StyxBody { locals, block }
}

fn extract_binding_name(pat_kind: &thir::PatKind<'_>) -> Option<String> {
    match pat_kind {
        thir::PatKind::Binding { name, .. } => Some(name.to_string()),
        thir::PatKind::AscribeUserType { subpattern, .. } => extract_binding_name(&subpattern.kind),
        _ => None,
    }
}

/// Extract the HirId-based LocalId from a binding pattern.
/// This matches the IDs used by ExprKind::VarRef in the body.
fn extract_binding_hir_id(pat_kind: &thir::PatKind<'_>) -> Option<LocalId> {
    match pat_kind {
        thir::PatKind::Binding { var, .. } => Some(LocalId(var.0.local_id.as_u32())),
        thir::PatKind::AscribeUserType { subpattern, .. } => extract_binding_hir_id(&subpattern.kind),
        _ => None,
    }
}

/// Extract the LocalId from a let-binding pattern.
/// For `let x = ...`, returns the LocalId of the bound variable.
/// Returns None for patterns that don't directly bind a single variable
/// (e.g., tuple destructuring, struct patterns).
///
/// Handles transparent wrappers:
///   - `AscribeUserType { subpattern }` — type annotation wrapper
///   - `Deref { subpattern }` — auto-deref pattern wrapper
fn extract_let_target(pat_kind: &thir::PatKind<'_>) -> Option<LocalId> {
    match pat_kind {
        thir::PatKind::Binding { var, .. } => Some(LocalId(var.0.local_id.as_u32())),
        // AscribeUserType wraps the inner pattern with a type annotation
        thir::PatKind::AscribeUserType { subpattern, .. } => {
            extract_let_target(&subpattern.kind)
        }
        // Deref wraps the inner pattern for auto-deref patterns
        thir::PatKind::Deref { subpattern } => {
            extract_let_target(&subpattern.kind)
        }
        other => {
            // Diagnostic: log which PatKind variants fall through to the None sentinel.
            // Only log each variant name once to avoid flooding stderr.
            use std::sync::atomic::{AtomicBool, Ordering};
            static LOGGED_WILD: AtomicBool = AtomicBool::new(false);
            let variant = match other {
                thir::PatKind::Wild => { if !LOGGED_WILD.swap(true, Ordering::Relaxed) { eprintln!("[styx-rustc] extract_let_target: Wild → u32::MAX"); } }
                _ => {
                    // For all other patterns, emit the debug repr once.
                    // Use a shared flag to avoid spamming; the variant name is in the debug output.
                    static LOGGED_OTHER: AtomicBool = AtomicBool::new(false);
                    if !LOGGED_OTHER.swap(true, Ordering::Relaxed) {
                        let dbg = format!("{other:?}");
                        let short = if dbg.len() > 80 { &dbg[..80] } else { &dbg };
                        eprintln!("[styx-rustc] extract_let_target: unhandled pattern → u32::MAX (first occurrence): {short}...");
                    }
                }
            };
            let _ = variant;
            None
        }
    }
}

fn extract_block_from_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &thir::Thir<'tcx>,
    expr_id: thir::ExprId,
) -> StyxBlock {
    let expr = &thir[expr_id];
    match &expr.kind {
        ExprKind::Block { block } => {
            let block_data = &thir[*block];
            let mut stmts = Vec::new();
            for &stmt_id in &block_data.stmts {
                stmts.extend(extract_stmt(tcx, thir, stmt_id));
            }
            if let Some(tail_expr) = block_data.expr {
                stmts.push(StyxStmt::Return(extract_expr(tcx, thir, tail_expr)));
            }
            StyxBlock { stmts }
        }
        ExprKind::Scope { value, .. } => extract_block_from_expr(tcx, thir, *value),
        _ => StyxBlock {
            stmts: vec![StyxStmt::Return(extract_expr(tcx, thir, expr_id))],
        },
    }
}

fn extract_stmt<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &thir::Thir<'tcx>,
    stmt_id: thir::StmtId,
) -> Vec<StyxStmt> {
    let stmt = &thir[stmt_id];
    match &stmt.kind {
        StmtKind::Let { initializer, pattern, .. } => {
            if let Some(init_expr) = initializer {
                // Extract the variable ID from the binding pattern if possible.
                let target = extract_let_target(&pattern.kind)
                    .unwrap_or(LocalId(u32::MAX));
                // Also extract the source-level variable name for readability.
                let name = extract_binding_name(&pattern.kind);
                vec![StyxStmt::Assign {
                    target,
                    name,
                    value: extract_expr(tcx, thir, *init_expr),
                }]
            } else {
                vec![]
            }
        }
        StmtKind::Expr { expr, .. } => {
            vec![StyxStmt::Expr(extract_expr(tcx, thir, *expr))]
        }
    }
}

fn extract_expr<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &thir::Thir<'tcx>,
    expr_id: thir::ExprId,
) -> StyxExpr {
    let expr = &thir[expr_id];
    let ty = ty_convert::convert_ty(tcx, expr.ty);
    let span = extract_types::convert_span(tcx, expr.span);

    let kind = match &expr.kind {
        // Transparent wrappers
        ExprKind::Scope { value, .. } => return extract_expr(tcx, thir, *value),
        ExprKind::Use { source } => return extract_expr(tcx, thir, *source),

        // Literals
        ExprKind::Literal { lit, neg } => extract_literal(&lit.node, *neg, &expr.ty),
        ExprKind::NonHirLiteral { lit, .. } => {
            // ScalarInt — derive scalar type from the expression's type
            match expr.ty.kind() {
                ty::Int(int_ty) => {
                    let val = lit.to_int(lit.size());
                    StyxExprKind::Literal(StyxLiteral::Int(val as i128, ty_convert::convert_int_ty(*int_ty)))
                }
                ty::Uint(uint_ty) => {
                    let val = lit.to_uint(lit.size());
                    StyxExprKind::Literal(StyxLiteral::UInt(val, ty_convert::convert_uint_ty(*uint_ty)))
                }
                ty::Bool => {
                    let val = lit.to_uint(lit.size());
                    StyxExprKind::Literal(StyxLiteral::Bool(val != 0))
                }
                ty::Char => {
                    let val = lit.to_uint(lit.size());
                    StyxExprKind::Literal(StyxLiteral::Char(char::from_u32(val as u32).unwrap_or('\0')))
                }
                _ => {
                    let val = lit.to_uint(lit.size());
                    StyxExprKind::Literal(StyxLiteral::UInt(val, ScalarTy::U64))
                }
            }
        }
        ExprKind::ZstLiteral { .. } => StyxExprKind::Unit,

        // Variable reference
        ExprKind::VarRef { id } => StyxExprKind::Local(LocalId(id.0.local_id.as_u32())),

        // Function call
        ExprKind::Call { fun, args, .. } => {
            let fun_ty = thir[*fun].ty;
            let arg_exprs: Vec<_> = args.iter().map(|&a| extract_expr(tcx, thir, a)).collect();
            // Resolve callee and capture generic type arguments for this call site.
            // type_args are the instantiated type parameters (e.g., Vec::<Right> carries Right).
            // Even though the current Lean emitter infers type args heuristically, we preserve
            // them here for correctness and future-proofing.
            let (callee, call_type_args) = match fun_ty.kind() {
                ty::FnDef(def_id, generic_args) => {
                    // Extract instantiated type arguments (skip lifetimes and const args).
                    let type_args: Vec<StyxType> = generic_args
                        .types()
                        .map(|t| ty_convert::convert_ty(tcx, t))
                        .collect();
                    let callee = match tcx.trait_of_assoc(*def_id) {
                        Some(trait_did) => {
                            let trait_path = tcx.def_path_str(trait_did);
                            let trait_id = trait_did.as_local().map(|l| {
                                styx::ir::TraitDeclId(l.local_def_index.as_u32())
                            });
                            let method_name = tcx.item_name(*def_id).to_string();
                            // self_ty is the first generic argument (index 0)
                            let self_ty = ty_convert::convert_ty(tcx, generic_args.type_at(0));
                            StyxCallee::TraitMethod {
                                trait_path,
                                trait_id,
                                method_name,
                                self_ty,
                            }
                        }
                        None => {
                            let rust_path = tcx.def_path_str(*def_id);
                            let local_id = def_id.as_local().map(|l| {
                                FunId(l.local_def_index.as_u32())
                            });
                            StyxCallee::Function { rust_path, local_id }
                        }
                    };
                    (callee, type_args)
                }
                // Genuine dynamic dispatch: function pointers, closures, async closures.
                // Emit as ClosureCall — the callee expression IS the function value.
                ty::FnPtr(..) | ty::Closure(..) | ty::CoroutineClosure(..) => {
                    let callee_expr = extract_expr(tcx, thir, *fun);
                    (StyxCallee::ClosureCall(Box::new(callee_expr)), vec![])
                }
                // Unexpected callee type — log and fall through to ClosureCall.
                // In well-typed THIR this should not occur for non-async code.
                other => {
                    eprintln!(
                        "[styx-rustc] Unexpected callee type in Call: {:?} (treating as closure call)",
                        other
                    );
                    let callee_expr = extract_expr(tcx, thir, *fun);
                    (StyxCallee::ClosureCall(Box::new(callee_expr)), vec![])
                }
            };
            StyxExprKind::Call {
                callee,
                type_args: call_type_args,
                args: arg_exprs,
            }
        }

        // Binary op
        ExprKind::Binary { op, lhs, rhs } => match convert_binop(*op) {
            Some(sop) => StyxExprKind::BinOp {
                op: sop,
                lhs: Box::new(extract_expr(tcx, thir, *lhs)),
                rhs: Box::new(extract_expr(tcx, thir, *rhs)),
            },
            None => {
                eprintln!("[styx-rustc] Unsupported BinOp: {op:?}");
                StyxExprKind::Absurd
            }
        },

        // Unary op
        ExprKind::Unary { op, arg } => match *op {
            rustc_middle::mir::UnOp::Not => StyxExprKind::UnOp {
                op: StyxUnOp::Not,
                operand: Box::new(extract_expr(tcx, thir, *arg)),
            },
            rustc_middle::mir::UnOp::Neg => StyxExprKind::UnOp {
                op: StyxUnOp::Neg,
                operand: Box::new(extract_expr(tcx, thir, *arg)),
            },
            other => {
                eprintln!("[styx-rustc] Unsupported UnOp: {other:?}");
                StyxExprKind::Absurd
            }
        },

        // If
        ExprKind::If { cond, then, else_opt, .. } => {
            return StyxExpr {
                kind: StyxExprKind::Block {
                    stmts: vec![StyxStmt::If {
                        cond: extract_expr(tcx, thir, *cond),
                        then_block: extract_block_from_expr(tcx, thir, *then),
                        else_block: else_opt
                            .map(|e| extract_block_from_expr(tcx, thir, e))
                            .unwrap_or_else(StyxBlock::empty),
                    }],
                    expr: None,
                },
                ty,
                span,
            };
        }

        // Match
        ExprKind::Match { scrutinee, arms, .. } => {
            let scrutinee_expr = extract_expr(tcx, thir, *scrutinee);
            let match_arms: Vec<_> = arms
                .iter()
                .map(|&arm_id| {
                    let arm = &thir[arm_id];
                    StyxMatchArm {
                        pattern: extract_pattern(tcx, &arm.pattern),
                        guard: arm.guard.map(|g| extract_expr(tcx, thir, g)),
                        body: extract_block_from_expr(tcx, thir, arm.body),
                    }
                })
                .collect();
            StyxExprKind::Block {
                stmts: vec![StyxStmt::Match {
                    scrutinee: scrutinee_expr,
                    arms: match_arms,
                }],
                expr: None,
            }
        }

        // Block
        ExprKind::Block { block } => {
            let block_data = &thir[*block];
            let mut stmts = Vec::new();
            for &stmt_id in &block_data.stmts {
                stmts.extend(extract_stmt(tcx, thir, stmt_id));
            }
            let tail = block_data.expr.map(|e| Box::new(extract_expr(tcx, thir, e)));
            StyxExprKind::Block { stmts, expr: tail }
        }

        // Field access
        ExprKind::Field { lhs, name, .. } => {
            let lhs_ty = thir[*lhs].ty;
            let field_name = resolve_field_name(tcx, lhs_ty, *name);
            StyxExprKind::Field {
                base: Box::new(extract_expr(tcx, thir, *lhs)),
                field_name,
                field_id: FieldId(name.as_u32()),
            }
        }

        // ADT construction
        ExprKind::Adt(adt_expr) => {
            let fields: Vec<_> = adt_expr
                .fields
                .iter()
                .map(|f| (FieldId(f.name.as_u32()), extract_expr(tcx, thir, f.expr)))
                .collect();
            let type_id = if adt_expr.adt_def.did().is_local() {
                TypeId(adt_expr.adt_def.did().expect_local().local_def_index.as_u32())
            } else {
                TypeId(u32::MAX) // External type — no local ID
            };
            if adt_expr.variant_index.as_u32() == 0
                && tcx.adt_def(adt_expr.adt_def.did()).is_struct()
            {
                StyxExprKind::StructInit {
                    type_id,
                    fields,
                }
            } else {
                StyxExprKind::EnumInit {
                    type_id,
                    variant_id: VariantId(adt_expr.variant_index.as_u32()),
                    fields,
                }
            }
        }

        // Tuple
        ExprKind::Tuple { fields } => {
            StyxExprKind::Tuple(fields.iter().map(|&f| extract_expr(tcx, thir, f)).collect())
        }

        // Borrow
        ExprKind::Borrow { borrow_kind, arg } => StyxExprKind::Ref {
            operand: Box::new(extract_expr(tcx, thir, *arg)),
            is_mut: matches!(borrow_kind, rustc_middle::mir::BorrowKind::Mut { .. }),
        },

        // Deref
        ExprKind::Deref { arg } => StyxExprKind::Deref(Box::new(extract_expr(tcx, thir, *arg))),

        // Return
        ExprKind::Return { value } => {
            let val = value
                .map(|v| extract_expr(tcx, thir, v))
                .unwrap_or_else(StyxExpr::unit);
            return StyxExpr {
                kind: StyxExprKind::Block {
                    stmts: vec![StyxStmt::Return(val)],
                    expr: None,
                },
                ty,
                span,
            };
        }

        // Loop
        ExprKind::Loop { body, .. } => {
            return StyxExpr {
                kind: StyxExprKind::Block {
                    stmts: vec![StyxStmt::Loop {
                        cond: None,
                        body: extract_block_from_expr(tcx, thir, *body),
                    }],
                    expr: None,
                },
                ty,
                span,
            };
        }

        // Break / Continue
        ExprKind::Break { .. } => {
            return StyxExpr {
                kind: StyxExprKind::Block {
                    stmts: vec![StyxStmt::Break { depth: 0 }],
                    expr: None,
                },
                ty,
                span,
            };
        }
        ExprKind::Continue { .. } => {
            return StyxExpr {
                kind: StyxExprKind::Block {
                    stmts: vec![StyxStmt::Continue { depth: 0 }],
                    expr: None,
                },
                ty,
                span,
            };
        }

        // Cast
        ExprKind::Cast { source } => StyxExprKind::Cast {
            operand: Box::new(extract_expr(tcx, thir, *source)),
            target_ty: ty.clone(),
        },

        // Index
        ExprKind::Index { lhs, index } => StyxExprKind::Index {
            base: Box::new(extract_expr(tcx, thir, *lhs)),
            index: Box::new(extract_expr(tcx, thir, *index)),
        },

        // PointerCoercion: &[T; N] -> &[T] (Unsize), etc. — transparent in Lean
        ExprKind::PointerCoercion { source, .. } => {
            return extract_expr(tcx, thir, *source);
        }

        // NeverToAny: coerce ! to any type (unreachable paths)
        ExprKind::NeverToAny { source } => {
            return extract_expr(tcx, thir, *source);
        }

        // Array literal: [a, b, c]
        ExprKind::Array { fields } => StyxExprKind::Array {
            elem_ty: ty.clone(),
            elements: fields.iter().map(|&f| extract_expr(tcx, thir, f)).collect(),
        },

        // Array repeat: [val; count]
        ExprKind::Repeat { value, count } => {
            let val = extract_expr(tcx, thir, *value);
            let count_val = ty_convert::convert_const_generic(tcx, *count);
            let n = match &count_val {
                StyxConstGeneric::Value(v) => *v as usize,
                _ => 1,
            };
            StyxExprKind::Array {
                elem_ty: ty.clone(),
                elements: std::iter::repeat_with(|| val.clone()).take(n).collect(),
            }
        }

        // Closure expression
        ExprKind::Closure(closure_expr) => {
            match tcx.thir_body(closure_expr.closure_id) {
                Ok((thir_steal, root)) => {
                    let closure_thir = thir_steal.borrow();
                    let body_expr = extract_expr(tcx, &closure_thir, root);
                    StyxExprKind::Closure {
                        params: closure_thir.params.iter().enumerate().map(|(i, p)| {
                            StyxParam {
                                name: p.pat.as_ref()
                                    .and_then(|pat| extract_binding_name(&pat.kind))
                                    .unwrap_or_else(|| format!("arg{i}")),
                                ty: ty_convert::convert_ty(tcx, p.ty),
                                is_mut_self: false,
                                local_id: p.pat.as_ref()
                                    .and_then(|pat| extract_binding_hir_id(&pat.kind)),
                            }
                        }).collect(),
                        body: Box::new(body_expr),
                        captures: vec![],
                    }
                }
                Err(_) => StyxExprKind::Absurd,
            }
        }

        // Assignment: lhs = rhs
        ExprKind::Assign { lhs, rhs } => {
            let rhs_expr = extract_expr(tcx, thir, *rhs);
            let lhs_expr = extract_expr(tcx, thir, *lhs);
            StyxExprKind::Block {
                stmts: vec![StyxStmt::Assign {
                    target: LocalId(u32::MAX),
                    name: None,
                    value: rhs_expr,
                }],
                expr: Some(Box::new(lhs_expr)),
            }
        }

        // Compound assignment: lhs += rhs, lhs -= rhs, etc.
        ExprKind::AssignOp { op, lhs, rhs } => {
            let lhs_expr = extract_expr(tcx, thir, *lhs);
            let rhs_expr = extract_expr(tcx, thir, *rhs);
            let bin_op = match op {
                rustc_middle::mir::AssignOp::AddAssign => StyxBinOp::Add,
                rustc_middle::mir::AssignOp::SubAssign => StyxBinOp::Sub,
                rustc_middle::mir::AssignOp::MulAssign => StyxBinOp::Mul,
                rustc_middle::mir::AssignOp::DivAssign => StyxBinOp::Div,
                rustc_middle::mir::AssignOp::RemAssign => StyxBinOp::Rem,
                rustc_middle::mir::AssignOp::BitAndAssign => StyxBinOp::BitAnd,
                rustc_middle::mir::AssignOp::BitOrAssign => StyxBinOp::BitOr,
                rustc_middle::mir::AssignOp::BitXorAssign => StyxBinOp::BitXor,
                rustc_middle::mir::AssignOp::ShlAssign => StyxBinOp::Shl,
                rustc_middle::mir::AssignOp::ShrAssign => StyxBinOp::Shr,
            };
            StyxExprKind::Block {
                stmts: vec![StyxStmt::Assign {
                    target: LocalId(u32::MAX),
                    name: None,
                    value: StyxExpr {
                        kind: StyxExprKind::BinOp {
                            op: bin_op,
                            lhs: Box::new(lhs_expr.clone()),
                            rhs: Box::new(rhs_expr),
                        },
                        ty: ty.clone(),
                        span: span.clone(),
                    },
                }],
                expr: Some(Box::new(lhs_expr)),
            }
        }

        // Logical short-circuit: a && b, a || b
        ExprKind::LogicalOp { op, lhs, rhs } => {
            let styx_op = match op {
                thir::LogicalOp::And => StyxBinOp::And,
                thir::LogicalOp::Or => StyxBinOp::Or,
            };
            StyxExprKind::BinOp {
                op: styx_op,
                lhs: Box::new(extract_expr(tcx, thir, *lhs)),
                rhs: Box::new(extract_expr(tcx, thir, *rhs)),
            }
        }

        // Let expression: let pat = expr (used in if-let)
        ExprKind::Let { expr: inner, .. } => {
            return extract_expr(tcx, thir, *inner);
        }

        // Named constant reference
        ExprKind::NamedConst { def_id, .. } => {
            let path = tcx.def_path_str(*def_id);
            StyxExprKind::Call {
                callee: StyxCallee::Function {
                    rust_path: path,
                    local_id: None,
                },
                type_args: vec![],
                args: vec![],
            }
        }

        // ConstParam reference
        ExprKind::ConstParam { .. } => StyxExprKind::Absurd, // Rare

        // UpvarRef: captured variable inside a closure body — treat as local
        ExprKind::UpvarRef { var_hir_id, .. } => {
            StyxExprKind::Local(LocalId(var_hir_id.0.local_id.as_u32()))
        }

        // Box expression: Box::new(val) — transparent in Lean (erased)
        ExprKind::Box { value } => {
            return extract_expr(tcx, thir, *value);
        }

        // Fallback for unhandled expressions — log the variant for gap analysis
        other => {
            // Count by variant for gap analysis
            static LOGGED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
            if !LOGGED.swap(true, std::sync::atomic::Ordering::Relaxed) {
                eprintln!("[styx-rustc] Note: some THIR ExprKind variants hit fallback (printed once)");
            }
            let variant_name = format!("{other:?}");
            // Truncate for readability
            let short = if variant_name.len() > 60 { &variant_name[..60] } else { &variant_name };
            eprintln!("[styx-rustc] Unhandled ExprKind: {short}...");
            StyxExprKind::Absurd
        }
    };

    StyxExpr { kind, ty, span }
}

/// Convert a THIR `Value` (constant) to a `StyxLiteral`.
///
/// `ty::Value` carries both the type and the valtree. We inspect the type to
/// choose the right `StyxLiteral` variant and extract the bit representation
/// via `ScalarInt`.
fn value_to_literal<'tcx>(value: ty::Value<'tcx>) -> StyxLiteral {
    let Some(scalar) = value.valtree.try_to_scalar_int() else {
        // Non-scalar constant (e.g. string, struct) — fall back to UInt 0
        return StyxLiteral::UInt(0, ScalarTy::U64);
    };
    match value.ty.kind() {
        ty::Bool => StyxLiteral::Bool(scalar.try_to_bool().unwrap_or(false)),
        ty::Char => {
            let v = scalar.to_uint(scalar.size());
            StyxLiteral::Char(char::from_u32(v as u32).unwrap_or('\0'))
        }
        ty::Int(int_ty) => {
            let v = scalar.to_int(scalar.size());
            StyxLiteral::Int(v, ty_convert::convert_int_ty(*int_ty))
        }
        ty::Uint(uint_ty) => {
            let v = scalar.to_uint(scalar.size());
            StyxLiteral::UInt(v, ty_convert::convert_uint_ty(*uint_ty))
        }
        _ => StyxLiteral::UInt(scalar.to_uint(scalar.size()), ScalarTy::U64),
    }
}

/// Convert a `PatRangeBoundary` to an optional `StyxLiteral`.
///
/// `NegInfinity` / `PosInfinity` boundaries produce `None` (open range end).
fn range_boundary_to_literal<'tcx>(
    boundary: PatRangeBoundary<'tcx>,
    ty: ty::Ty<'tcx>,
) -> Option<StyxLiteral> {
    match boundary {
        PatRangeBoundary::Finite(valtree) => {
            let value = ty::Value { ty, valtree };
            Some(value_to_literal(value))
        }
        PatRangeBoundary::NegInfinity | PatRangeBoundary::PosInfinity => None,
    }
}

/// Extract a field binding from a `FieldPat`.
///
/// The sub-pattern inside a `FieldPat` can itself be any pattern; if it is a
/// `Binding` we record the bound local, otherwise we treat the field as
/// unbound (`None`).
fn field_pat_to_binding(fp: &thir::FieldPat<'_>) -> Option<PatternBinding> {
    // The inner pattern might be wrapped in AscribeUserType; peel those first.
    let inner = peel_ascriptions(&fp.pattern);
    if let thir::PatKind::Binding { name, var, .. } = &inner.kind {
        Some(PatternBinding {
            local: LocalId(var.0.local_id.as_u32()),
            field_name: name.to_string(),
        })
    } else {
        None
    }
}

/// Peel any `AscribeUserType` or `ExpandedConstant` wrappers from a pattern,
/// returning the innermost concrete pattern.
fn peel_ascriptions<'a, 'tcx>(pat: &'a thir::Pat<'tcx>) -> &'a thir::Pat<'tcx> {
    match &pat.kind {
        thir::PatKind::AscribeUserType { subpattern, .. } => peel_ascriptions(subpattern),
        thir::PatKind::ExpandedConstant { subpattern, .. } => peel_ascriptions(subpattern),
        _ => pat,
    }
}

/// Convert a THIR `Pat` to a `StyxPattern`.
///
/// This is the main pattern extraction function. It is called for every match
/// arm pattern. All pattern variants supported by THIR are handled; unrecognised
/// or exotic patterns fall back to `StyxPattern::Wildcard` with a warning.
fn extract_pattern<'tcx>(
    tcx: TyCtxt<'tcx>,
    pat: &thir::Pat<'tcx>,
) -> StyxPattern {
    // Peel transparent wrappers first.
    let pat = peel_ascriptions(pat);

    match &pat.kind {
        // `_` — wildcard
        thir::PatKind::Wild | thir::PatKind::Missing => StyxPattern::Wildcard,

        // `x`, `ref x`, `x @ subpat`
        thir::PatKind::Binding { name: _, var, subpattern, .. } => {
            let local = LocalId(var.0.local_id.as_u32());
            let sub = subpattern
                .as_deref()
                .map(|p| Box::new(extract_pattern(tcx, p)));
            StyxPattern::Binding { local, subpattern: sub }
        }

        // Enum variant: `Foo::Bar(...)` or `Foo::Bar { ... }`
        thir::PatKind::Variant { adt_def, variant_index, subpatterns, .. } => {
            let variant = adt_def.variant(*variant_index);
            let field_count = variant.fields.len();
            // Build a Vec<Option<PatternBinding>> aligned to field positions.
            let mut field_bindings: Vec<Option<PatternBinding>> = vec![None; field_count];
            for fp in subpatterns {
                let idx = fp.field.as_usize();
                if idx < field_count {
                    field_bindings[idx] = field_pat_to_binding(fp);
                }
            }
            let type_id = if adt_def.did().is_local() {
                TypeId(adt_def.did().expect_local().local_def_index.as_u32())
            } else {
                TypeId(u32::MAX)
            };
            let rust_path = Some(tcx.def_path_str(adt_def.did()));
            StyxPattern::Variant {
                type_id,
                variant_id: VariantId(variant_index.as_u32()),
                field_bindings,
                rust_path,
            }
        }

        // Struct or tuple-struct (single-variant ADT): `Foo { x, y }` or `Foo(a, b)`
        thir::PatKind::Leaf { subpatterns } => {
            // Derive the type_id from pat.ty if it is an ADT.
            let (type_id, total_fields) = if let ty::Adt(adt_def, _) = pat.ty.kind() {
                let tid = if adt_def.did().is_local() {
                    TypeId(adt_def.did().expect_local().local_def_index.as_u32())
                } else {
                    TypeId(u32::MAX)
                };
                (tid, adt_def.non_enum_variant().fields.len())
            } else {
                (TypeId(0), 0)
            };
            let field_patterns: Vec<(FieldId, StyxPattern)> = subpatterns
                .iter()
                .map(|fp| (FieldId(fp.field.as_u32()), extract_pattern(tcx, &fp.pattern)))
                .collect();
            // has_rest = true when not all struct fields are mentioned in the pattern
            let has_rest = field_patterns.len() < total_fields;
            StyxPattern::Struct {
                type_id,
                field_patterns,
                has_rest,
            }
        }

        // Constant literal pattern: `42`, `true`, `'a'`
        thir::PatKind::Constant { value } => {
            StyxPattern::Literal(value_to_literal(*value))
        }

        // Range pattern: `0..=9`, `'a'..='z'`
        thir::PatKind::Range(range) => {
            let lo = range_boundary_to_literal(range.lo, range.ty);
            let hi = range_boundary_to_literal(range.hi, range.ty);
            let inclusive = matches!(range.end, RangeEnd::Included);
            StyxPattern::Range { lo, hi, inclusive }
        }

        // Reference/deref pattern: `&P`, `&mut P`
        thir::PatKind::Deref { subpattern } | thir::PatKind::DerefPattern { subpattern, .. } => {
            StyxPattern::Ref(Box::new(extract_pattern(tcx, subpattern)))
        }

        // Or-pattern: `A | B | C`
        thir::PatKind::Or { pats } => {
            StyxPattern::Or(pats.iter().map(|p| extract_pattern(tcx, p)).collect())
        }

        // Tuple pattern: `(a, b, c)` — encoded as Leaf on unit/tuple types in some
        // THIR builds, but may also appear as Leaf with an ADT type.
        // For plain tuples (non-ADT), Leaf subpatterns map to tuple positions.
        // We handle this above in Leaf; this arm catches structural tuple patterns
        // where the compiler emits them explicitly (rare).

        // Never pattern `!` — emitted as Wildcard (unreachable arm).
        thir::PatKind::Never => StyxPattern::Wildcard,

        // Slice patterns `[a, b, .., z]` — not common in lion-core; emit Wildcard.
        thir::PatKind::Slice { .. } => {
            eprintln!("[styx-rustc] Warning: slice pattern not yet supported, using Wildcard");
            StyxPattern::Wildcard
        }

        // Errors and anything else we don't recognise.
        _ => {
            eprintln!("[styx-rustc] Warning: unhandled PatKind, using Wildcard");
            StyxPattern::Wildcard
        }
    }
}

fn extract_literal<'tcx>(lit: &LitKind, neg: bool, expr_ty: &rustc_middle::ty::Ty<'tcx>) -> StyxExprKind {
    match lit {
        LitKind::Bool(b) => StyxExprKind::Literal(StyxLiteral::Bool(*b)),
        LitKind::Int(val, _) => {
            let v = val.get() as i128;
            // Use the expression's type to determine the correct scalar type
            match expr_ty.kind() {
                ty::Int(int_ty) => StyxExprKind::Literal(StyxLiteral::Int(
                    if neg { -v } else { v },
                    ty_convert::convert_int_ty(*int_ty),
                )),
                ty::Uint(uint_ty) => StyxExprKind::Literal(StyxLiteral::UInt(
                    v as u128,
                    ty_convert::convert_uint_ty(*uint_ty),
                )),
                _ => {
                    if neg {
                        StyxExprKind::Literal(StyxLiteral::Int(-v, ScalarTy::I64))
                    } else {
                        StyxExprKind::Literal(StyxLiteral::UInt(v as u128, ScalarTy::U64))
                    }
                }
            }
        }
        LitKind::Char(c) => StyxExprKind::Literal(StyxLiteral::Char(*c)),
        LitKind::Str(s, _) => StyxExprKind::Literal(StyxLiteral::Str(s.to_string())),
        _ => StyxExprKind::Absurd,
    }
}

fn convert_binop(op: rustc_middle::mir::BinOp) -> Option<StyxBinOp> {
    use rustc_middle::mir::BinOp;
    match op {
        BinOp::Add | BinOp::AddUnchecked | BinOp::AddWithOverflow => Some(StyxBinOp::Add),
        BinOp::Sub | BinOp::SubUnchecked | BinOp::SubWithOverflow => Some(StyxBinOp::Sub),
        BinOp::Mul | BinOp::MulUnchecked | BinOp::MulWithOverflow => Some(StyxBinOp::Mul),
        BinOp::Div => Some(StyxBinOp::Div),
        BinOp::Rem => Some(StyxBinOp::Rem),
        BinOp::BitAnd => Some(StyxBinOp::BitAnd),
        BinOp::BitOr => Some(StyxBinOp::BitOr),
        BinOp::BitXor => Some(StyxBinOp::BitXor),
        BinOp::Shl | BinOp::ShlUnchecked => Some(StyxBinOp::Shl),
        BinOp::Shr | BinOp::ShrUnchecked => Some(StyxBinOp::Shr),
        BinOp::Eq => Some(StyxBinOp::Eq),
        BinOp::Ne => Some(StyxBinOp::Ne),
        BinOp::Lt => Some(StyxBinOp::Lt),
        BinOp::Le => Some(StyxBinOp::Le),
        BinOp::Gt => Some(StyxBinOp::Gt),
        BinOp::Ge => Some(StyxBinOp::Ge),
        _ => None,
    }
}

/// Resolve a field index to its name by looking up the ADT definition.
fn resolve_field_name<'tcx>(
    _tcx: TyCtxt<'tcx>,
    lhs_ty: rustc_middle::ty::Ty<'tcx>,
    field_idx: rustc_abi::FieldIdx,
) -> String {
    // Peel references to get the underlying type
    let base_ty = lhs_ty.peel_refs();
    if let ty::Adt(adt_def, _) = base_ty.kind() {
        if adt_def.is_struct() {
            // Structs have a single variant — safe to look up directly
            let variant = adt_def.non_enum_variant();
            if let Some(field) = variant.fields.get(field_idx) {
                return field.name.to_string();
            }
        } else {
            // Enums: THIR Field access after Downcast doesn't expose the
            // variant index in the expression type. We can't reliably determine
            // which variant's field names to use. Return positional name.
            return format!("field_{}", field_idx.as_u32());
        }
    }
    // Tuple types — field names are positional
    if let ty::Tuple(_) = base_ty.kind() {
        return format!("{}", field_idx.as_u32());
    }
    // Fallback
    format!("field_{}", field_idx.as_u32())
}
