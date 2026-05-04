use std::collections::BTreeMap;
use crate::naming::escape_lean_keyword;
use super::*;
use super::body::LOCAL_NAMES;

pub(crate) fn emit_expr(expr: &StyxExpr, types: &TypeLookup) -> String {
    match &expr.kind {
        StyxExprKind::Literal(lit) => emit_literal(lit),
        StyxExprKind::Local(id) => local_name(id.0),
        StyxExprKind::Global(_) => "global_".to_string(),
        StyxExprKind::Unit => "()".to_string(),
        StyxExprKind::Absurd => "sorry".to_string(),

        StyxExprKind::Call { callee, args, .. } => {
            // Special case: Option::map(opt, |idx| body) where body has IndexVec.index
            // Lean cannot use ← inside `fun`, so desugar to a match expression.
            if let StyxCallee::Function { rust_path, .. } = callee {
                let is_option_map =
                    rust_path.contains("option::Option") && rust_path.ends_with("::map");
                if is_option_map && args.len() == 2
                    && let StyxExprKind::Closure { params, body, .. } = &args[1].kind
                        && closure_body_has_index(body) {
                            return emit_option_map_as_match(&args[0], params, body, types);
                        }
                // Special case: Option::is_some_and(opt, |param| body) where body has IndexVec.index
                // Same issue as Option::map — can't use ← inside fun, desugar to match.
                let is_option_is_some_and =
                    rust_path.contains("option::Option") && rust_path.ends_with("::is_some_and");
                if is_option_is_some_and && args.len() == 2
                    && let StyxExprKind::Closure { params, body, .. } = &args[1].kind
                        && closure_body_has_index(body) {
                            return emit_option_is_some_and_as_match(&args[0], params, body, types);
                        }
            }

            // Special case: Iterator::{all,any,find,map}(iter, |params| body) where the
            // closure body needs do-notation desugaring (IndexVec.index call, or a tuple
            // value-param that requires destructuring over (K, V) iterator items).
            // The closure body uses nested-let expression syntax which doesn't support ←.
            // Lean requires do-notation (statement mode) for ← inside a fun body.
            // Emit: (std.iter.Iterator.{method} iter (fun params => do\n  <body_stmts>))
            if let StyxCallee::TraitMethod {
                trait_path,
                method_name,
                ..
            } = callee
            {
                let is_iter_closure_method = matches!(
                    method_name.as_str(),
                    "all" | "any" | "find" | "map"
                ) && (trait_path.contains("iter::Iterator")
                    || trait_path.contains("std::iter::Iterator")
                    || trait_path.contains("core::iter::Iterator"));
                if is_iter_closure_method && args.len() == 2
                    && let StyxExprKind::Closure { params, body, .. } = &args[1].kind
                        && closure_needs_iter_desugar(params, body) {
                            return emit_iter_closure_as_do(
                                method_name, &args[0], params, body, types,
                            );
                        }
            }

            // Clone is identity in pure functional Lean — just return the argument
            let is_clone = matches!(callee,
                StyxCallee::TraitMethod { trait_path, method_name, .. }
                    if method_name == "clone" && (trait_path.contains("clone::Clone") || trait_path.contains("Clone"))
            ) || matches!(callee,
                StyxCallee::Function { rust_path, .. }
                    if rust_path.contains("clone::Clone::clone") || rust_path.contains("Clone::clone")
            );
            if is_clone && args.len() == 1 {
                return emit_expr(&args[0], types);
            }

            // Trait method dispatch: route based on self_ty for Default, Deref
            if let StyxCallee::TraitMethod {
                trait_path,
                method_name,
                self_ty,
                ..
            } = callee
            {
                // Default::default → type-specific impl
                if method_name == "default" && trait_path.contains("Default")
                    && let Some(concrete) = map_default_callee(self_ty) {
                        return concrete;
                    }
                // Deref::deref on Vec → identity (Vec = Slice in Aeneas)
                if method_name == "deref" && trait_path.contains("Deref") && args.len() == 1
                    && matches!(self_ty, StyxType::Adt { rust_path, .. } if rust_path.contains("Vec"))
                    {
                        return emit_expr(&args[0], types);
                    }
                // DerefMut::deref_mut on Vec → identity
                if method_name == "deref_mut" && trait_path.contains("DerefMut") && args.len() == 1
                    && matches!(self_ty, StyxType::Adt { rust_path, .. } if rust_path.contains("Vec"))
                    {
                        return emit_expr(&args[0], types);
                    }
            }

            // PartialEq::eq → type-directed dispatch (like Default::default)
            if let StyxCallee::TraitMethod {
                trait_path,
                method_name,
                self_ty,
                ..
            } = callee
            {
                if method_name == "eq" && trait_path.contains("PartialEq") && args.len() == 2
                    && let Some(eq_expr) = map_partial_eq_callee(self_ty, &args[0], &args[1], types)
                    {
                        return eq_expr;
                    }
                if method_name == "ne" && trait_path.contains("PartialEq") && args.len() == 2
                    && let Some(eq_expr) = map_partial_eq_callee(self_ty, &args[0], &args[1], types)
                    {
                        return format!("(!(← {eq_expr}))");
                    }
            }

            let callee_str = emit_callee(callee);

            // Vec::with_capacity(n) → Vec.new T: drop capacity arg, use return type
            if callee_str == "alloc.vec.Vec.new" && !args.is_empty() {
                let type_arg = extract_type_arg_from_return(&expr.ty)
                    .unwrap_or_else(|| emit_type(&expr.ty));
                return format!("(alloc.vec.Vec.new {type_arg})");
            }

            // Args may themselves be Calls — lift them with (← ...)
            let args_str: Vec<String> = args.iter().map(|a| emit_expr_lifted(a, types)).collect();

            // Infer generic type arguments for Aeneas stdlib functions.
            // Vec/Slice methods take (T : Type) and often (A : Type) as explicit params.
            // We extract T from the first value argument's type (when it's a Vec/Slice/Ref).
            let mut type_args_prefix = infer_stdlib_type_args(&callee_str, args);

            // Try/FromResidual: infer (T : Type) (E : Type) from the Result<T,E> argument
            if type_args_prefix.is_empty() {
                type_args_prefix = infer_try_type_args(&callee_str, args);
            }

            // Into.into: infer (T U : Type) from arg type and call return type
            // AeneasStdlib signature: std.convert.Into.into (T U : Type) (inst : ...) (x : T) : Result U
            if type_args_prefix.is_empty()
                && (callee_str == "std.convert.Into.into"
                    || callee_str == "core.convert.Into.into")
                && let Some(first_arg) = args.first() {
                    let src_ty = emit_type(unwrap_ref_type(&first_arg.ty));
                    // Target type U is inside Result U (the call's return type)
                    let tgt_ty = extract_type_arg_from_return(&expr.ty)
                        .unwrap_or_else(|| emit_type(&expr.ty));
                    type_args_prefix = format!("{src_ty} {tgt_ty}");
                }

            if args_str.is_empty() {
                // Zero-arg call: extract generic type arg from return type
                // e.g., Vec::new() returning Vec<T> → (alloc.vec.Vec.new T)
                let type_arg = extract_type_arg_from_return(&expr.ty);
                if let Some(ta) = type_arg {
                    format!("({callee_str} {ta})")
                } else {
                    format!("({callee_str})")
                }
            } else if !type_args_prefix.is_empty() {
                format!("({callee_str} {type_args_prefix} {})", args_str.join(" "))
            } else {
                format!("({callee_str} {})", args_str.join(" "))
            }
        }

        StyxExprKind::BinOp { op, lhs, rhs } => {
            let l = emit_expr_lifted(lhs, types);
            let r = emit_expr_lifted(rhs, types);
            // Ordering comparisons (<, <=, >, >=) return Prop in Lean4.
            // Wrap with `decide` to get Bool. Aeneas provides DecidableRel
            // instances for UScalar/IScalar.
            // Eq (==) and Ne (!=) already return Bool via BEq — no wrapping needed.
            match op {
                StyxBinOp::Lt => return format!("(decide ({l} < {r}))"),
                StyxBinOp::Le => return format!("(decide ({l} <= {r}))"),
                StyxBinOp::Gt => return format!("(decide ({l} > {r}))"),
                StyxBinOp::Ge => return format!("(decide ({l} >= {r}))"),
                _ => {}
            }
            let op_str = match op {
                StyxBinOp::Add => "+",
                StyxBinOp::Sub => "-",
                StyxBinOp::Mul => "*",
                StyxBinOp::Div => "/",
                StyxBinOp::Rem => "%",
                StyxBinOp::BitAnd => "&&&",
                StyxBinOp::BitOr => "|||",
                StyxBinOp::BitXor => "^^^",
                StyxBinOp::Shl => "<<<",
                StyxBinOp::Shr => ">>>",
                StyxBinOp::Eq => "==",
                StyxBinOp::Ne => "!=",
                StyxBinOp::Lt | StyxBinOp::Le | StyxBinOp::Gt | StyxBinOp::Ge => unreachable!(), // handled above
                StyxBinOp::And => "&&",
                StyxBinOp::Or => "||",
            };
            format!("({l} {op_str} {r})")
        }

        StyxExprKind::UnOp { op, operand } => {
            let o = emit_expr_lifted(operand, types);
            match op {
                StyxUnOp::Not => {
                    // For non-Bool scalar types, `!` is bitwise NOT (~~~), not Bool.not (!)
                    let is_bitwise =
                        matches!(scalar_of_ty(&operand.ty), Some(s) if s != ScalarTy::Bool);
                    if is_bitwise {
                        format!("(~~~{o})")
                    } else {
                        format!("(!{o})")
                    }
                }
                StyxUnOp::Neg => format!("(-{o})"),
            }
        }

        StyxExprKind::Field {
            base,
            field_name,
            field_id,
            ..
        } => {
            let b = emit_expr_lifted(base, types);
            // Positional fields come from two sources:
            //   - Rust tuple types: field_name = "0", "1", ... (bare numeric string)
            //   - Enum variant unnamed fields: field_name = "field_0", "field_1", ...
            // In both cases the index is 0-based; Lean tuple projection is 1-based (.1, .2).
            let is_positional = field_name.parse::<u32>().is_ok()
                || field_name.starts_with("field_") && field_name[6..].parse::<u32>().is_ok();
            if is_positional {
                format!("{b}.{}", field_id.0 + 1)
            } else {
                let fname = escape_lean_keyword(field_name);
                format!("{b}.{fname}")
            }
        }

        StyxExprKind::TupleField { base, index } => {
            // Lean tuple projection is 1-based (.1, .2); Rust TupleField index is 0-based.
            let b = emit_expr_lifted(base, types);
            format!("{b}.{}", index + 1)
        }

        StyxExprKind::Index { base, index } => {
            let b = emit_expr_lifted(base, types);
            let i = emit_expr_lifted(index, types);
            // For Slice<T> or &Slice<T>, use Slice.index_usize (Aeneas-compatible, bounds-checked).
            // Lean's bracket notation `s[i]` requires a compile-time bounds proof, but
            // Slice.index_usize returns `Result T` and handles runtime bounds checking.
            let is_slice_base = match &base.ty {
                StyxType::Slice(_) => true,
                StyxType::Ref { inner, .. } => matches!(inner.as_ref(), StyxType::Slice(_)),
                _ => false,
            };
            if is_slice_base {
                // Slice.index_usize : {T : Type} → Slice T → Usize → Result T
                format!("(Slice.index_usize {b} {i})")
            } else {
                format!("({b}[{i}])")
            }
        }

        StyxExprKind::StructInit { type_id, fields } => {
            let field_strs: Vec<String> = fields
                .iter()
                .map(|(fid, expr)| {
                    let val = emit_expr_lifted(expr, types);
                    let fname = lookup_field_name(types, type_id, fid)
                        .unwrap_or_else(|| format!("field_{}", fid.0));
                    let fname = escape_lean_keyword(&fname);
                    format!("{fname} := {val}")
                })
                .collect();
            format!("{{ {} }}", field_strs.join(", "))
        }

        StyxExprKind::EnumInit {
            type_id,
            variant_id,
            fields,
        } => {
            let user_variant = lookup_variant_name(types, type_id, variant_id);
            let vname = user_variant
                .clone()
                .or_else(|| std_enum_variant_name(&expr.ty, variant_id))
                .unwrap_or_else(|| format!("variant_{}", variant_id.0));

            let ctor = if let Some(type_name) = if user_variant.is_some() {
                match &expr.ty {
                    StyxType::Adt { rust_path, .. } => Some(rust_path_to_lean(rust_path)),
                    _ => None,
                }
            } else {
                None
            } {
                format!("{type_name}.{vname}")
            } else {
                format!(".{vname}")
            };
            let args: Vec<String> = fields
                .iter()
                .map(|(_, e)| emit_expr_lifted(e, types))
                .collect();
            if args.is_empty() {
                format!("({ctor})")
            } else {
                format!("({ctor} {})", args.join(" "))
            }
        }

        StyxExprKind::Tuple(elems) => {
            let parts: Vec<String> = elems.iter().map(|e| emit_expr_lifted(e, types)).collect();
            format!("({})", parts.join(", "))
        }

        StyxExprKind::Array { elements, .. } => {
            let parts: Vec<String> = elements
                .iter()
                .map(|e| emit_expr_lifted(e, types))
                .collect();
            format!("#[{}]", parts.join(", "))
        }

        StyxExprKind::Cast { operand, target_ty } => {
            // Lift monadic calls: if the operand is a Result-returning call,
            // wrap with `(← ...)` so we cast the unwrapped value
            let inner = emit_expr_lifted(operand, types);
            // Determine source and target scalar types
            let src_scalar = scalar_of_ty(&operand.ty);
            let tgt_scalar = scalar_of_ty(target_ty);
            match (src_scalar, tgt_scalar) {
                (Some(src), Some(tgt)) => {
                    // Same type — no-op
                    if src == tgt {
                        inner
                    } else if is_unsigned_scalar(&src) && is_unsigned_scalar(&tgt) {
                        format!("(UScalar.cast .{} {inner})", scalar_lean_name(&tgt))
                    } else if is_signed_scalar(&src) && is_signed_scalar(&tgt) {
                        format!("(IScalar.cast .{} {inner})", scalar_lean_name(&tgt))
                    } else {
                        // Mixed signed/unsigned cast — drop for now
                        inner
                    }
                }
                _ => inner,
            }
        }

        StyxExprKind::Ref { operand, .. } => emit_expr(operand, types),
        StyxExprKind::Deref(inner) => emit_expr(inner, types),

        StyxExprKind::Closure { params, body, .. } => {
            let mut param_names = Vec::new();
            let mut saved_shadows = Vec::new();

            // Closure params in StyxIR may lack local_id (null from JSON).
            // When that happens, Local(N) refs in the body that aren't in the
            // outer scope correspond to closure params. We collect undeclared
            // Local IDs from the body, sort them, and bind to params in order.
            //
            // FnMut/Fn closure calls in Rust MIR always have an extra first
            // parameter: `arg0: &mut FnPtr(...)` (the closure vtable/env pointer).
            // In Lean, closures capture upvars automatically — this env pointer
            // has no Lean equivalent. We exclude it from param_names so that:
            //   (a) it doesn't appear in `fun arg0 item => ...` (wrong arity)
            //   (b) its inferred local ID isn't stolen from the real item param
            //
            // Filter: exclude params whose type is `FnPtr` OR `Ref { inner: FnPtr }`.
            let is_fn_env = |ty: &StyxType| -> bool {
                match ty {
                    StyxType::FnPtr { .. } => true,
                    StyxType::Ref { inner, .. } => matches!(inner.as_ref(), StyxType::FnPtr { .. }),
                    _ => false,
                }
            };

            // Build the list of "real" params (skipping FnEnv params).
            // real_param_indices maps real_param position → original params[] index.
            let real_param_indices: Vec<usize> = params
                .iter()
                .enumerate()
                .filter(|(_, p)| !is_fn_env(&p.ty))
                .map(|(i, _)| i)
                .collect();

            let params_missing_ids: Vec<usize> = real_param_indices
                .iter()
                .filter(|&&i| params[i].local_id.is_none())
                .copied()
                .collect();

            let mut inferred_ids: Vec<u32> = Vec::new();
            if !params_missing_ids.is_empty() {
                let mut body_locals = std::collections::BTreeSet::new();
                collect_local_ids(body, &mut body_locals);
                // F6a: collect locals that are ASSIGNED inside the body (body-internal
                // temporaries like `let mut revoked_cap = cap.clone()`).  These must
                // not be treated as closure param aliases — they are produced inside
                // the body and would never appear as undefined outer-scope refs.
                let mut body_assigned = std::collections::BTreeSet::new();
                collect_assigned_ids_in_expr(body, &mut body_assigned);
                // Filter out locals that are already in the outer scope OR assigned
                // within the body itself (body-local temporaries).
                LOCAL_NAMES.with(|map| {
                    let m = map.borrow();
                    for &id in &body_locals {
                        if !m.contains_key(&id) && !body_assigned.contains(&id) {
                            inferred_ids.push(id);
                        }
                    }
                });
            }

            // T1 (2026-04-14): tuple-destructured closure param.
            // Rust source: `|&(id, cap)| body` — styx-rustc emits 1 real param with
            // type `Ref(Tuple[T0, T1, ...])` plus multiple fresh body locals, each
            // representing a tuple field. The existing single-local fast-path handles
            // `|&(id, _)| id` by binding one local to `arg1.N`, but multi-local bodies
            // need genuine destructuring: `fun arg1 => let (a, b) := arg1; body`.
            //
            // Detect: exactly 1 params_missing_ids, param type peels to Tuple, and
            // at least 1 inferred local's type matches a distinct tuple field.
            // The >= 1 threshold (vs >= 2) also covers |(_, cap)| body where only
            // one field local appears in the body — the other field gets bound to "_".
            let mut tuple_destructure: Option<(usize, Vec<(u32, usize)>)> = None;
            if params_missing_ids.len() == 1 && !inferred_ids.is_empty() {
                let pi = params_missing_ids[0];
                let p = &params[pi];
                let tuple_fields: Option<&Vec<StyxType>> = match &p.ty {
                    StyxType::Tuple(fs) => Some(fs),
                    StyxType::Ref { inner, .. } => match inner.as_ref() {
                        StyxType::Tuple(fs) => Some(fs),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(fields) = tuple_fields {
                    // Map each inferred local to a tuple field position by type match.
                    // Collect body-local types from a BTreeMap of id → type.
                    let mut local_types: std::collections::BTreeMap<u32, StyxType> =
                        std::collections::BTreeMap::new();
                    collect_local_types(body, &mut local_types);
                    let mut assignments: Vec<(u32, usize)> = Vec::new();
                    let mut used_fields = std::collections::BTreeSet::new();
                    for &lid in &inferred_ids {
                        if let Some(lt) = local_types.get(&lid) {
                            for (fi, ft) in fields.iter().enumerate() {
                                if used_fields.contains(&fi) {
                                    continue;
                                }
                                if styx_types_equal(ft, lt) {
                                    assignments.push((lid, fi));
                                    used_fields.insert(fi);
                                    break;
                                }
                            }
                        }
                    }
                    // Fire T1 if at least 1 inferred local type-matches a tuple field.
                    // This covers both:
                    //   - 2+ fields used (both type-match → full destructure pattern)
                    //   - 1 field used (e.g. |(_, cap)| cap.method() → let (_, local_N) := arg1)
                    if !assignments.is_empty() {
                        tuple_destructure = Some((pi, assignments));
                    }
                }
            }

            // T1: if tuple destructuring applies, bind inferred locals to per-field
            // pattern names (local_<lid>) and record the param_name + pattern prefix.
            // The pattern prefix is prepended to the body string after emission.
            let mut tuple_destructure_prefix: Option<String> = None;
            let mut tuple_destructured_ids: std::collections::BTreeSet<u32> =
                std::collections::BTreeSet::new();
            if let Some((pi, assignments)) = &tuple_destructure {
                let p = &params[*pi];
                let lean_name = escape_lean_keyword(&p.name);
                // Build ordered field → binding-name vector
                let field_count = match &p.ty {
                    StyxType::Tuple(fs) => fs.len(),
                    StyxType::Ref { inner, .. } => match inner.as_ref() {
                        StyxType::Tuple(fs) => fs.len(),
                        _ => 0,
                    },
                    _ => 0,
                };
                let mut names: Vec<String> = (0..field_count).map(|_| "_".to_string()).collect();
                for (lid, fi) in assignments {
                    names[*fi] = format!("local_{}", lid);
                    tuple_destructured_ids.insert(*lid);
                }
                let pat = names.join(", ");
                tuple_destructure_prefix = Some(format!("let ({pat}) := {lean_name}; "));
            }

            // Temporarily bind closure params in LOCAL_NAMES so that VarRef
            // inside the closure body resolves to the correct param names.
            // Only real (non-FnEnv) params are bound and added to param_names.
            LOCAL_NAMES.with(|map| {
                let mut m = map.borrow_mut();
                let mut inferred_idx = 0;
                for &i in &real_param_indices {
                    let p = &params[i];
                    let lean_name = escape_lean_keyword(&p.name);
                    // Add scalar type annotations so Lean can infer implicit type params
                    // for polymorphic combinators like Iterator.fold (e.g. arg2 : U16).
                    // Also handle Ref(Scalar) — Rust's &T iterator items.
                    // Do NOT annotate all params — tuple annotations break find_oob etc.
                    let scalar_ty_for_annotation: Option<&StyxType> = match &p.ty {
                        StyxType::Scalar(_) => Some(&p.ty),
                        StyxType::Ref { inner, .. }
                            if matches!(inner.as_ref(), StyxType::Scalar(_)) =>
                        {
                            Some(inner.as_ref())
                        }
                        _ => None,
                    };
                    let annotated_name = if let Some(sty) = scalar_ty_for_annotation {
                        format!("({lean_name} : {})", emit_type(sty))
                    } else {
                        lean_name.clone()
                    };
                    param_names.push(annotated_name);
                    if let Some(lid) = &p.local_id {
                        if let Some(old) = m.insert(lid.0, lean_name) {
                            saved_shadows.push((lid.0, Some(old)));
                        } else {
                            saved_shadows.push((lid.0, None));
                        }
                    } else if params_missing_ids.contains(&i) && inferred_idx < inferred_ids.len() {
                        // T1: if tuple destructuring applies, bind each destructured local
                        // to its per-field name (local_<lid>) instead of arg1.k. The enclosing
                        // `let (a, b) := arg1;` prefix makes those names valid in the body.
                        if tuple_destructure.is_some() {
                            for (lid, _) in tuple_destructure.as_ref().unwrap().1.iter() {
                                let bind_name = format!("local_{}", lid);
                                if let Some(old) = m.insert(*lid, bind_name) {
                                    saved_shadows.push((*lid, Some(old)));
                                } else {
                                    saved_shadows.push((*lid, None));
                                }
                            }
                            // Still advance inferred_idx for bookkeeping, even though
                            // we're binding differently — prevents double-iteration.
                            inferred_idx = inferred_ids.len();
                            continue;
                        }
                        // Bind inferred local ID to this param.
                        let lid = inferred_ids[inferred_idx];
                        inferred_idx += 1;
                        // Attempt field-projection binding for tuple-patterned closures.
                        // styx-rustc collapses `|(_, cap)|` destructuring into a bare Local
                        // without an explicit TupleField node. We need to bind `local_lid`
                        // to the correct tuple field projection (`param.K`) rather than to
                        // the whole param.
                        //
                        // Two cases:
                        //   (a) body is exactly `Local(lid)` — single-local body like `|cap| cap`
                        //   (b) body is a complex expression — `|(_, cap)| cap.method()`
                        //
                        // For (b) we look up the local's type and match it against the tuple field.
                        // `closure_tuple_field_index` now peels multiple Ref layers so it handles
                        // `&&(U64, Capability)` params where local_51: Capability = field 2.
                        //
                        // Example: body = BinOp(And, Call(is_valid, Local(51)), ...), param = &&(U64, Capability)
                        //   local_51: Capability matches field 2 → binds 51 → "arg1.2"
                        let local_ty = {
                            let mut lt = std::collections::BTreeMap::new();
                            collect_local_types(body, &mut lt);
                            lt.remove(&lid)
                        };
                        let actual_name = if let StyxExprKind::Local(body_lid) = &body.kind {
                            if body_lid.0 == lid {
                                if let Some(k) = closure_tuple_field_index(&p.ty, &body.ty) {
                                    format!("{}.{}", lean_name, k)
                                } else {
                                    lean_name.clone()
                                }
                            } else {
                                lean_name.clone()
                            }
                        } else if let Some(lt) = local_ty {
                            // Complex body: attempt field projection if the local's type
                            // matches a field of the (possibly multi-ref) param tuple.
                            if let Some(k) = closure_tuple_field_index(&p.ty, &lt) {
                                format!("{}.{}", lean_name, k)
                            } else {
                                lean_name.clone()
                            }
                        } else {
                            lean_name.clone()
                        };
                        if let Some(old) = m.insert(lid, actual_name) {
                            saved_shadows.push((lid, Some(old)));
                        } else {
                            saved_shadows.push((lid, None));
                        }
                    }
                }
            });

            let body_str = emit_expr(body, types);

            // Restore LOCAL_NAMES: remove closure params, re-insert shadowed entries
            LOCAL_NAMES.with(|map| {
                let mut m = map.borrow_mut();
                for (id, old_name) in &saved_shadows {
                    match old_name {
                        Some(name) => {
                            m.insert(*id, name.clone());
                        }
                        None => {
                            m.remove(id);
                        }
                    }
                }
            });

            // F5 (2026-04-14): qualify Option constructors inside closure bodies.
            //
            // When a closure's body type is `Option T`, the bare `.none`/`.some X` dot-notation
            // constructors rely on Lean's local expected-type inference. But when the closure is
            // passed to `Iterator.find_map` (whose overall return type is `Result (Option T)`),
            // Lean 4 resolves `.none`/`.some` against `Result` rather than `Option`, producing
            // `Unknown constant Aeneas.Std.Result.none`.
            //
            // Fix: in Option-typed closure bodies, replace `(.none)` → `(Option.none)` and
            // `(.some ` → `(Option.some ` to make the type unambiguous. This is safe because:
            //   - We only apply inside closures where `body.ty` is `Option` or `Result (Option _)`
            //   - `(.none)` and `(.some ` patterns in emitted Lean are always Option constructors
            //     when the body type is Option (no other type uses these names)
            //   - The substitution is idempotent and does not affect `ok`-wrapped arms (those
            //     appear as `ok (.none)` → detected by `=> (.` in desugar_pure_arms match arms,
            //     not by closure body post-processing)
            let body_str = {
                // Check if the closure body type is Option<_> or Result<Option<_>, _>.
                // In both cases, `.none`/`.some` inside the body refer to Option constructors
                // and must be fully qualified to avoid Lean resolving them against `Result`.
                let body_is_option = matches!(&body.ty, StyxType::Adt { rust_path, .. }
                    if rust_path == "core::option::Option" || rust_path == "std::option::Option");
                let body_wraps_option = !body_is_option
                    && matches!(&body.ty, StyxType::Adt { rust_path, generic_args, .. }
                    if (rust_path == "core::result::Result" || rust_path == "std::result::Result")
                    && matches!(generic_args.first(), Some(StyxType::Adt { rust_path: opt_path, .. })
                        if opt_path == "core::option::Option" || opt_path == "std::option::Option"));
                if (body_is_option || body_wraps_option)
                    && (body_str.contains("(.none)") || body_str.contains("(.some "))
                {
                    body_str
                        .replace("(.none)", "(Option.none)")
                        .replace("(.some ", "(Option.some ")
                } else {
                    body_str
                }
            };

            // T1: inject tuple destructuring prefix before the body.
            // `fun arg1 => let (a, b) := arg1; body`
            let body_str = if let Some(prefix) = tuple_destructure_prefix {
                format!("{prefix}{body_str}")
            } else {
                body_str
            };

            // Lean 4 cannot lift `←` over `fun` binders.
            // If the body contains monadic bind notation (from emit_expr_lifted on args),
            // wrap it in a `do` block so that `←` is valid.
            // Example: `fun cap => (check (← (IndexVec.index vec cap)))` → invalid
            //          `fun cap => do (check (← (IndexVec.index vec cap)))` → valid
            if body_str.contains('←') {
                format!("(fun {} => do {})", param_names.join(" "), body_str)
            } else {
                format!("(fun {} => {body_str})", param_names.join(" "))
            }
        }

        StyxExprKind::Block { stmts, expr } => {
            // Empty block — just emit the trailing expression
            if stmts.is_empty() {
                if let Some(e) = expr {
                    return emit_expr(e, types);
                }
                return "()".to_string();
            }
            // Field-assign-as-expr: styx-rustc sometimes emits `self.field = val` as
            //   Block { stmts: [Assign(DUMMY, val)], expr: Some(Field { base: Deref(..), .. }) }
            // This produces dead reads like `(let _ := val; self.field)`. Since the mutation
            // is invisible in Lean's functional semantics, emit `ok ()` (unit success).
            if stmts.len() == 1
                && let (StyxStmt::Assign { target, value, .. }, Some(trailing)) = (&stmts[0], expr)
                    && target.0 == u32::MAX {
                        if let StyxExprKind::Field { base, .. } = &trailing.kind
                            && matches!(base.kind, StyxExprKind::Deref(_)) {
                                return "ok ()".to_string();
                            }
                        // Saturating arithmetic pattern: `self.field = self.field.saturating_op(x)`
                        // lowers to Block { Assign(DUMMY, saturating_call), trailing: self.field }.
                        // The trailing field-read is the lhs of the mutation, so emit `ok ()`
                        // (the mutation is invisible in Lean's functional semantics).
                        let rhs_s = emit_expr(value, types);
                        let expr_s = emit_expr(trailing, types);
                        if is_pure_saturating_num_call(&rhs_s) && rhs_s.contains(&expr_s) {
                            return "ok ()".to_string();
                        }
                    }
            // Check if the last statement is a Return — if so, it provides the value
            let _last_is_return = matches!(stmts.last(), Some(StyxStmt::Return(_)));

            // Build nested let-bindings: (let _ := s1; (let _ := s2; body))
            // NOTE: use := (not ←) because we're in expression context, not a do-block
            let mut n_lets = 0usize;
            let mut prefix = String::new();
            for s in stmts {
                match s {
                    StyxStmt::Assign { target, value, .. } => {
                        if target.0 == u32::MAX {
                            prefix.push_str(&format!("(let _ := {}; ", emit_expr(value, types)));
                        } else {
                            prefix.push_str(&format!(
                                "(let {} := {}; ",
                                local_name(target.0),
                                emit_expr(value, types)
                            ));
                        }
                        n_lets += 1;
                    }
                    StyxStmt::Expr(e) => {
                        prefix.push_str(&format!("(let _ := {}; ", emit_expr(e, types)));
                        n_lets += 1;
                    }
                    StyxStmt::Return(e) => {
                        // Return is the block's final value — no let binding
                        prefix.push_str(&emit_expr(e, types));
                    }
                    StyxStmt::If {
                        cond,
                        then_block,
                        else_block,
                    } => {
                        let c = emit_expr(cond, types);
                        let t = emit_block_inline(then_block, types);
                        let e = emit_block_inline(else_block, types);
                        prefix.push_str(&format!("(if {c} then {t} else {e})"));
                    }
                    StyxStmt::Match { scrutinee, arms } => {
                        let scrut = emit_expr(scrutinee, types);
                        let mut ms = format!("(match {scrut} with");
                        // Deduplicate: Lean rejects redundant match alternatives.
                        let mut seen_pats_inline: std::collections::HashSet<String> =
                            std::collections::HashSet::new();
                        for arm in arms {
                            let pat = emit_pattern(&arm.pattern, types);
                            if !seen_pats_inline.insert(pat.clone()) {
                                continue; // duplicate arm — skip
                            }
                            let body = emit_block_inline(&arm.body, types);
                            ms.push_str(&format!(" | {pat} => {body}"));
                        }
                        ms.push(')');
                        prefix.push_str(&ms);
                    }
                    StyxStmt::Loop { .. } => prefix.push_str("sorry /- loop -/"),
                    StyxStmt::Break { .. } | StyxStmt::Continue { .. } => { /* control flow */ }
                    StyxStmt::Drop { .. } => { /* no-op */ }
                    _ => {
                        prefix.push_str("sorry /- stmt -/");
                    }
                }
            }
            // Append trailing expression (only if last stmt wasn't Return/If/Match)
            let last_is_control = matches!(
                stmts.last(),
                Some(StyxStmt::Return(_) | StyxStmt::If { .. } | StyxStmt::Match { .. })
            );
            if !last_is_control {
                if let Some(e) = expr {
                    prefix.push_str(&emit_expr(e, types));
                } else {
                    prefix.push_str("()");
                }
            }
            // Close the let-binding parens
            prefix.push_str(&")".repeat(n_lets));
            prefix
        }

        StyxExprKind::QuestionMark { inner, .. } => {
            // In do-notation, (← inner) binds Ok(v) to v and propagates Err upward.
            // This is exactly Rust's `?` operator semantics.
            let i = emit_expr(inner, types);
            format!("(← {i})")
        }
    }
}

/// Map well-known std/core function/trait method paths to Aeneas-compatible Lean names.
/// Returns Some(mapped) or None if no mapping exists.
pub(crate) fn map_std_callee(lean_path: &str) -> Option<&'static str> {
    match lean_path {
        // BTreeMap methods (alloc:: → std:: namespace, batch 4)
        "alloc.collections.BTreeMap.new" | "alloc.collections.btree_map.BTreeMap.new" => {
            Some("std.collections.BTreeMap.new")
        }
        "alloc.collections.BTreeMap.get" | "alloc.collections.btree_map.BTreeMap.get" => {
            Some("std.collections.BTreeMap.get")
        }
        "alloc.collections.BTreeMap.insert" | "alloc.collections.btree_map.BTreeMap.insert" => {
            Some("std.collections.BTreeMap.insert")
        }
        "alloc.collections.BTreeMap.len" | "alloc.collections.btree_map.BTreeMap.len" => {
            Some("std.collections.BTreeMap.len")
        }
        "alloc.collections.BTreeMap.is_empty" | "alloc.collections.btree_map.BTreeMap.is_empty" => {
            Some("std.collections.BTreeMap.is_empty")
        }
        "alloc.collections.BTreeMap.values" | "alloc.collections.btree_map.BTreeMap.values" => {
            Some("std.collections.BTreeMap.values")
        }
        "alloc.collections.BTreeMap.iter" | "alloc.collections.btree_map.BTreeMap.iter" => {
            Some("std.collections.BTreeMap.iter")
        }
        "alloc.collections.BTreeMap.entry" | "alloc.collections.btree_map.BTreeMap.entry" => {
            Some("std.collections.BTreeMap.entry")
        }
        "alloc.collections.BTreeMap.remove" | "alloc.collections.btree_map.BTreeMap.remove" => {
            Some("std.collections.BTreeMap.remove")
        }
        "alloc.collections.BTreeMap.contains_key"
        | "alloc.collections.btree_map.BTreeMap.contains_key" => {
            Some("std.collections.BTreeMap.contains_key")
        }
        // Vec methods (VecDeque mapped to Vec in types)
        // std:: re-export paths
        "std.collections.VecDeque.new" | "std.collections.vec_deque.VecDeque.new" => {
            Some("alloc.vec.Vec.new")
        }
        "std.collections.VecDeque.is_empty" | "std.collections.vec_deque.VecDeque.is_empty" => {
            Some("alloc.vec.Vec.is_empty")
        }
        "std.collections.VecDeque.len" | "std.collections.vec_deque.VecDeque.len" => {
            Some("alloc.vec.Vec.len")
        }
        "std.collections.VecDeque.push_back" | "std.collections.vec_deque.VecDeque.push_back" => {
            Some("alloc.vec.Vec.push")
        }
        "std.collections.VecDeque.pop_front" | "std.collections.vec_deque.VecDeque.pop_front" => {
            Some("alloc.vec.Vec.pop_front")
        }
        // alloc:: internal paths (Charon may use these when compiling with --edition 2021+)
        "alloc.collections.VecDeque.new" | "alloc.collections.vec_deque.VecDeque.new" => {
            Some("alloc.vec.Vec.new")
        }
        "alloc.collections.VecDeque.is_empty" | "alloc.collections.vec_deque.VecDeque.is_empty" => {
            Some("alloc.vec.Vec.is_empty")
        }
        "alloc.collections.VecDeque.len" | "alloc.collections.vec_deque.VecDeque.len" => {
            Some("alloc.vec.Vec.len")
        }
        "alloc.collections.VecDeque.push_back"
        | "alloc.collections.vec_deque.VecDeque.push_back" => Some("alloc.vec.Vec.push"),
        "alloc.collections.VecDeque.pop_front"
        | "alloc.collections.vec_deque.VecDeque.pop_front" => Some("alloc.vec.Vec.pop_front"),
        // Vec direct
        "alloc.vec.Vec.new" | "std.vec.Vec.new" => Some("alloc.vec.Vec.new"),
        "std.vec.from_elem" | "alloc.vec.from_elem" => Some("alloc.vec.Vec.from_elem"),
        "alloc.vec.Vec.with_capacity" | "std.vec.Vec.with_capacity" => Some("alloc.vec.Vec.new"),
        "alloc.vec.Vec.len" | "std.vec.Vec.len" => Some("alloc.vec.Vec.len"),
        "alloc.vec.Vec.push" | "std.vec.Vec.push" => Some("alloc.vec.Vec.push"),
        "alloc.vec.Vec.insert" | "std.vec.Vec.insert" => Some("alloc.vec.Vec.insert"),
        "alloc.vec.Vec.remove" | "std.vec.Vec.remove" => Some("alloc.vec.Vec.remove"),
        "alloc.vec.Vec.is_empty" | "std.vec.Vec.is_empty" => Some("alloc.vec.Vec.is_empty"),
        "alloc.vec.Vec.dedup" | "std.vec.Vec.dedup" => Some("alloc.vec.Vec.dedup"),
        "alloc.vec.Vec.sort_unstable" | "std.vec.Vec.sort_unstable" => {
            Some("alloc.vec.Vec.sort_unstable")
        }
        // Deref/DerefMut: identity (reference erasure in Lean)
        "core.ops.deref.Deref.deref" | "std.ops.Deref.deref" => Some("core.ops.deref.Deref.deref"),
        "core.ops.deref.DerefMut.deref_mut" | "std.ops.DerefMut.deref_mut" => {
            Some("core.ops.deref.DerefMut.deref_mut")
        }
        // Index/IndexMut
        "core.ops.index.Index.index" | "std.ops.Index.index" => Some("alloc.vec.IndexVec.index"),
        "core.ops.index.IndexMut.index_mut" | "std.ops.IndexMut.index_mut" => {
            Some("alloc.vec.IndexMutVec.index_mut")
        }
        // Arc (Aeneas erases Arc<T>=T; Arc::new is an identity wrapper)
        "std.sync.Arc.new" | "alloc.sync.Arc.new" => Some("alloc.sync.Arc.new"),
        // Clone
        "core.clone.Clone.clone" | "std.clone.Clone.clone" => Some("core.clone.Clone.clone"),
        // Try trait (? operator desugaring)
        "std.ops.Try.branch" | "core.ops.try_trait.Try.branch" => {
            Some("core.result.TryResultResultInfallible.branch")
        }
        "std.ops.Try.from_output" | "core.ops.try_trait.Try.from_output" => {
            Some("core.result.TryResultResultInfallible.from_output")
        }
        "std.ops.FromResidual.from_residual" | "core.ops.try_trait.FromResidual.from_residual" => {
            Some("core.result.FromResidualResultResultInfallible.from_residual")
        }
        // Option methods (std → core namespace)
        "std.option.Option.is_some" => Some("core.option.Option.is_some"),
        "std.option.Option.is_none" => Some("core.option.Option.is_none"),
        "std.option.Option.expect" => Some("core.option.Option.expect"),
        "std.option.Option.unwrap" => Some("core.option.Option.unwrap"),
        "std.option.Option.unwrap_or" => Some("core.option.Option.unwrap_or"),
        "std.option.Option.ok_or" => Some("core.option.Option.ok_or"),
        "std.option.Option.map" => Some("core.option.Option.map"),
        "std.option.Option.is_some_and" | "core.option.Option.is_some_and" => {
            Some("core.option.Option.is_some_and")
        }
        // Result methods (std → core namespace)
        "std.result.Result.is_ok" => Some("core.result.Result.is_ok"),
        "std.result.Result.is_err" => Some("core.result.Result.is_err"),
        "std.result.Result.ok" => Some("core.result.Result.ok"),
        "std.result.Result.map_err" => Some("core.result.Result.map_err"),
        // Default
        "std.default.Default.default" => Some("core.default.Default.default"),
        // Cmp
        "std.cmp.PartialEq.eq" => Some("core.cmp.PartialEq.eq"),
        "std.cmp.Ord.cmp" => Some("core.cmp.Ord.cmp"),
        "std.cmp.Ordering" => Some("core.cmp.Ordering"),
        // Intrinsics
        "std.intrinsics.discriminant_value" => Some("core.intrinsics.discriminant_value"),
        // Saturating arithmetic (std → core namespace)
        "core.num.saturating_add" => Some("core.num.saturating_add"),
        // BTreeMap entry API (F3, issue #273):
        // entry() → monadic (returns Result (Entry K V))
        "std.collections.BTreeMap.entry" | "alloc.collections.btree.map.BTreeMap.entry" => {
            Some("alloc.collections.btree.map.BTreeMap.entry")
        }
        // Entry::or_insert_with → monadic wrapper (returns Result V)
        "std.collections.btree_map.Entry.or_insert_with"
        | "alloc.collections.btree_map.Entry.or_insert_with" => {
            Some("alloc.collections.btree.map.BTreeMap.entry_or_insert_with")
        }
        // Box::new → identity in Lean (Box<T> ≈ T in Aeneas model)
        "std.boxed.Box.new" | "alloc.boxed.Box.new" => Some("alloc.boxed.Box.new"),
        // BTreeMap::get_mut → monadic (returns Result (Option V))
        "std.collections.BTreeMap.get_mut" | "alloc.collections.btree.map.BTreeMap.get_mut" => {
            Some("alloc.collections.btree.map.BTreeMap.get_mut")
        }
        // PartialEq/PartialOrd — emit as FunsExternal-declared per-type impl
        // (handled specially in emit_expr for Call; this mapping is a fallback)
        _ => None,
    }
}

/// Route Default::default calls to type-specific implementations based on self_ty.
/// Returns the raw Lean expression (caller handles `←` lifting via emit_expr_lifted).
pub(crate) fn map_default_callee(self_ty: &StyxType) -> Option<String> {
    match self_ty {
        StyxType::Scalar(ScalarTy::U32) => {
            Some("core.default.impls.DefaultU32.default".to_string())
        }
        StyxType::Scalar(ScalarTy::U64) => {
            Some("core.default.impls.DefaultU64.default".to_string())
        }
        StyxType::Scalar(ScalarTy::Usize) => {
            Some("core.default.impls.DefaultUsize.default".to_string())
        }
        StyxType::Scalar(ScalarTy::Bool) => {
            Some("core.default.impls.DefaultBool.default".to_string())
        }
        StyxType::Adt { rust_path, .. } if rust_path.contains("Vec") => {
            Some("(core.default.impls.DefaultVec.default _)".to_string())
        }
        StyxType::Adt { rust_path, .. } if rust_path.contains("Option") => {
            Some("(core.default.impls.DefaultOption.default _)".to_string())
        }
        _ => {
            // Fallback: emit generic Default.default with explicit type arg
            let ty_str = emit_type(self_ty);
            Some(format!("(core.default.Default.default {ty_str})"))
        }
    }
}

/// Route PartialEq::eq calls to type-specific implementations.
/// For scalars: `ok (a == b)` (BEq instance available).
/// For ADT types with generated PartialEq impls: call the impl directly.
/// For arrays/vecs: call Aeneas stdlib comparison.
pub(crate) fn map_partial_eq_callee(
    self_ty: &StyxType,
    lhs: &StyxExpr,
    rhs: &StyxExpr,
    types: &TypeLookup,
) -> Option<String> {
    // Unwrap reference wrappers: PartialEq::eq takes &T, but we compare T.
    // Prefer the LHS expression type over self_ty for type args, because self_ty
    // may have wrong const generics (e.g., PAGE_SIZE=4096 vs extracted 0).
    let inner_ty = {
        let lhs_ty = unwrap_ref_type(&lhs.ty);
        match lhs_ty {
            StyxType::Scalar(_)
            | StyxType::Str
            | StyxType::Array { .. }
            | StyxType::Adt { .. } => lhs_ty,
            _ => unwrap_ref_type(self_ty),
        }
    };
    let a = emit_expr(lhs, types);
    let b = emit_expr(rhs, types);

    match inner_ty {
        // Scalar/string types: BEq available, use ==
        StyxType::Scalar(_) | StyxType::Str => Some(format!("ok ({a} == {b})")),
        // Array U8 32 (Key, Hash32, SealedTag, SymbolicTag bytes fields):
        // Compare arrays element-by-element. Use existing PartialEqArrayArray.eq
        StyxType::Array { elem, len } => {
            let elem_str = emit_type(elem);
            let n_str = match len {
                StyxConstGeneric::Value(n) => format!("{n}#usize"),
                _ => "_".to_string(),
            };
            Some(format!(
                "(core.array.equality.PartialEqArrayArray.eq {elem_str} {elem_str} {n_str} {a} {b})"
            ))
        }
        // String: structural equality
        StyxType::Adt { rust_path, .. } if rust_path.contains("String") => {
            Some(format!("ok ({a} == {b})"))
        }
        // Vec<T>: compare lists (Vec.val is List)
        StyxType::Adt {
            rust_path,
            generic_args,
            ..
        } if rust_path.contains("Vec") => {
            let elem = generic_args.iter().find(|t| !is_allocator_type(t));
            if let Some(e) = elem {
                let elem_str = emit_type(e);
                Some(format!("(alloc.vec.PartialEq.eq {elem_str} {a} {b})"))
            } else {
                None
            }
        }
        // Option<T>: compare options
        StyxType::Adt {
            rust_path,
            generic_args,
            ..
        } if rust_path.contains("Option") => {
            if let Some(inner) = generic_args.first() {
                let inner_str = emit_type(inner);
                Some(format!("(core.option.PartialEq.eq {inner_str} {a} {b})"))
            } else {
                None
            }
        }
        // ADT types: use the generic opaque PartialEq.eq with explicit type args.
        // Cannot call type-specific PartialEq*Foo*.eq because it may be defined
        // after the caller in the topo-sorted output (forward reference).
        StyxType::Adt { .. } => {
            let ty_str = emit_type(inner_ty);
            Some(format!("(core.cmp.PartialEq.eq {ty_str} {ty_str} {a} {b})"))
        }
        _ => None,
    }
}

pub(crate) fn emit_callee(callee: &StyxCallee) -> String {
    let raw = match callee {
        StyxCallee::Function { rust_path, .. } => rust_path_to_lean(rust_path),
        StyxCallee::TraitMethod {
            trait_path,
            method_name,
            ..
        } => {
            let trait_lean = rust_path_to_lean(trait_path);
            format!("{trait_lean}.{method_name}")
        }
        StyxCallee::Builtin(builtin) => return emit_builtin(builtin),
        StyxCallee::ClosureCall(expr) => return emit_expr(expr, &BTreeMap::new()),
    };
    // Apply std callee mapping
    map_std_callee(&raw).map_or(raw, |s| s.to_string())
}

pub(crate) fn emit_builtin(builtin: &StyxBuiltinFn) -> String {
    match builtin {
        StyxBuiltinFn::VecNew => "alloc.vec.Vec.new".to_string(),
        StyxBuiltinFn::VecPush => "alloc.vec.Vec.push".to_string(),
        StyxBuiltinFn::VecLen => "alloc.vec.Vec.len".to_string(),
        StyxBuiltinFn::VecIndex => "alloc.vec.IndexVec.index".to_string(),
        StyxBuiltinFn::VecIndexMut => "alloc.vec.IndexMutVec.index_mut".to_string(),
        StyxBuiltinFn::VecInsert => "alloc.vec.Vec.insert".to_string(),
        StyxBuiltinFn::VecRemove => "alloc.vec.Vec.remove".to_string(),
        StyxBuiltinFn::ArrayRepeat => "core.array.repeat".to_string(),
        StyxBuiltinFn::ArrayIndex => "core.array.index".to_string(),
        StyxBuiltinFn::ArrayIndexMut => "core.array.index_mut".to_string(),
        StyxBuiltinFn::SliceLen => "Slice.len".to_string(),
        StyxBuiltinFn::SliceIndex => "Slice.index".to_string(),
        StyxBuiltinFn::BoxNew => "alloc.boxed.Box.new".to_string(),
        StyxBuiltinFn::Panic => "core.panicking.panic".to_string(),
        StyxBuiltinFn::Assert => "core.panicking.assert".to_string(),
    }
}

pub(crate) fn emit_literal(lit: &StyxLiteral) -> String {
    match lit {
        StyxLiteral::UInt(val, ty) => format!("{val}#{}", scalar_suffix(ty)),
        StyxLiteral::Int(val, ty) => format!("{val}#{}", scalar_suffix(ty)),
        StyxLiteral::Bool(b) => format!("{b}"),
        StyxLiteral::Char(c) => format!("'{c}'"),
        StyxLiteral::Str(s) => format!("\"{s}\""),
    }
}

pub(crate) fn emit_pattern(pat: &StyxPattern, types: &TypeLookup) -> String {
    match pat {
        StyxPattern::Wildcard => "_".to_string(),
        StyxPattern::Variant {
            type_id,
            variant_id,
            field_bindings,
            rust_path,
        } => {
            // Try local TypeLookup first, then std type fallback via rust_path
            let vname = lookup_variant_name(types, type_id, variant_id)
                .or_else(|| {
                    rust_path.as_ref().and_then(|rp| {
                        let dummy_ty = StyxType::Adt {
                            rust_path: rp.clone(),
                            type_id: Some(*type_id),
                            generic_args: vec![],
                            const_args: vec![],
                        };
                        std_enum_variant_name(&dummy_ty, variant_id)
                    })
                })
                .unwrap_or_else(|| format!("variant_{}", variant_id.0));
            // Collect field bindings: named locals or _ for wildcards
            let bindings: Vec<String> = field_bindings
                .iter()
                .map(|b| match b {
                    Some(pb) => local_name(pb.local.0),
                    None => "_".to_string(),
                })
                .collect();
            // core.result.Result: use fully-qualified ctor to avoid collision
            // with the open Aeneas.Std Result (which also has Ok/Err constructors).
            // `.Ok v` resolves ambiguously; `core.result.Result.Ok v` is unambiguous.
            let is_core_result = rust_path
                .as_ref()
                .map(|rp| rp.contains("result::Result") || rp.contains("core::result"))
                .unwrap_or_else(|| {
                    // Fallback: look up the type's rust_path from TypeLookup
                    types
                        .get(&type_id.0)
                        .map(|td| {
                            td.rust_path.contains("result::Result")
                                || td.rust_path.contains("core::result")
                        })
                        .unwrap_or(false)
                });
            if is_core_result && (vname == "Ok" || vname == "Err") {
                let full_ctor = format!("core.result.Result.{vname}");
                if bindings.is_empty() {
                    return full_ctor.to_string();
                } else {
                    return format!("{full_ctor} {}", bindings.join(" "));
                }
            }
            // Option: qualify `.some`/`.none` → `Option.some`/`Option.none`
            // to avoid ambiguity under `open Aeneas.Std Result Error`.
            let is_option = rust_path
                .as_ref()
                .map(|rp| rp.contains("option::Option"))
                .unwrap_or_else(|| {
                    types
                        .get(&type_id.0)
                        .map(|td| td.rust_path.contains("option::Option"))
                        .unwrap_or(false)
                });
            if is_option && (vname == "some" || vname == "none" || vname == "Some" || vname == "None") {
                let lean_ctor = if vname.starts_with('S') || vname == "some" { "some" } else { "none" };
                let full_ctor = format!("Option.{lean_ctor}");
                if bindings.is_empty() {
                    return full_ctor.to_string();
                } else {
                    return format!("{full_ctor} {}", bindings.join(" "));
                }
            }
            if bindings.is_empty() {
                format!(".{vname}")
            } else {
                format!(".{vname} {}", bindings.join(" "))
            }
        }
        StyxPattern::Literal(lit) => emit_literal(lit),
        StyxPattern::Binding { local, .. } => local_name(local.0),
        StyxPattern::Tuple(pats) => {
            let parts: Vec<String> = pats.iter().map(|p| emit_pattern(p, types)).collect();
            format!("({})", parts.join(", "))
        }
        StyxPattern::Struct {
            type_id,
            field_patterns,
            has_rest,
        } => {
            if field_patterns.is_empty() {
                // No fields mentioned — wildcard is safest for type inference
                return "_".to_string();
            }
            // Detect tuple types: if no field has a real name in TypeLookup,
            // emit as positional tuple pattern `(p1, p2)` instead of
            // struct pattern `{ f := p }`.
            let is_tuple = field_patterns
                .iter()
                .all(|(fid, _)| lookup_field_name(types, type_id, fid).is_none());
            if is_tuple {
                let parts: Vec<String> = field_patterns
                    .iter()
                    .map(|(_, pat)| emit_pattern(pat, types))
                    .collect();
                return format!("({})", parts.join(", "));
            }
            let mut fields: Vec<String> = field_patterns
                .iter()
                .map(|(fid, pat)| {
                    let fname = lookup_field_name(types, type_id, fid)
                        .unwrap_or_else(|| format!("field_{}", fid.0));
                    let pat_str = emit_pattern(pat, types);
                    format!("{} := {}", escape_lean_keyword(&fname), pat_str)
                })
                .collect();
            if *has_rest {
                fields.push("..".to_string());
            }
            format!("{{ {} }}", fields.join(", "))
        }
        StyxPattern::Ref(inner) => emit_pattern(inner, types),
        StyxPattern::Or(alts) => {
            let parts: Vec<String> = alts.iter().map(|p| emit_pattern(p, types)).collect();
            parts.join(" | ")
        }
        StyxPattern::Range { lo, hi, inclusive } => {
            let lo_str = lo.as_ref().map_or("_".to_string(), emit_literal);
            let hi_str = hi.as_ref().map_or("_".to_string(), emit_literal);
            if *inclusive {
                format!("{lo_str}..={hi_str}")
            } else {
                format!("{lo_str}..{hi_str}")
            }
        }
    }
}
