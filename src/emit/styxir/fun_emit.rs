use crate::emit::indent::IndentWriter;
use crate::naming::escape_lean_keyword;
use super::*;

fn action_new_needs_step_error_mapping(body_text: &str, ret_ty: &str) -> bool {
    if !ret_ty.contains("StepError") {
        return false;
    }
    let action_new_count = body_text.match_indices("Action.new").count();
    if action_new_count == 0 {
        return false;
    }

    let mapped_action_new_count = body_text
        .match_indices("(match (← (types.policy.Action.new")
        .count();
    mapped_action_new_count < action_new_count
}

pub(crate) fn emit_funs_file(
    pkg: &StyxPackage,
    namespace: &str,
    aeneas_compat: bool,
    emit_checks: bool,
    _skip_stdlib: bool,
) -> EmitResult {
    let mut w = IndentWriter::new();
    emit_header(&mut w);
    w.writeln(format!("import {namespace}.Types"));
    w.writeln(format!("import {namespace}.FunsExternal"));
    // AeneasStdlib is imported transitively via FunsExternal
    emit_options(&mut w);
    w.newline();
    w.writeln(format!("namespace {namespace}"));
    w.newline();

    let types = build_type_lookup(pkg);
    let mut sorry_fns = Vec::new();
    let mut emitted_names = std::collections::HashSet::new();

    // Topological sort: emit callees before callers
    let order = topo_sort_funs(&pkg.functions);
    // Track which function Lean names were successfully emitted (not opaque).
    // Used to determine which trait impl structures can reference them.
    let mut emitted_fun_names: std::collections::HashSet<String> = std::collections::HashSet::new();
    for &idx in &order {
        let fun_def = &pkg.functions[idx];
        // Deduplicate: skip if a function with the same Lean name was already emitted
        let lean_name = rust_path_to_lean(&fun_def.rust_path);
        if !emitted_names.insert(lean_name.clone()) {
            w.writeln(format!("-- skipped duplicate: {lean_name}"));
            w.newline();
            continue;
        }
        let made_opaque = emit_fun_def(&mut w, fun_def, &types, aeneas_compat, emit_checks);
        if made_opaque {
            sorry_fns.push(idx);
        } else {
            emitted_fun_names.insert(lean_name);
        }
    }

    // Emit trait impl structures for supported traits (Clone, PartialEq, etc.).
    // Maps FunId.0 → lean function name for fast lookup.
    let fun_id_to_name: std::collections::HashMap<u32, String> = pkg
        .functions
        .iter()
        .map(|f| (f.id.0, rust_path_to_lean(&f.rust_path)))
        .collect();
    for imp in &pkg.trait_impls {
        emit_trait_impl_struct(&mut w, imp, &fun_id_to_name, &emitted_fun_names);
    }

    w.writeln(format!("end {namespace}"));
    EmitResult {
        funs_lean: w.finish(),
        sorry_fns,
    }
}

/// Emit a trait impl structure for a supported trait.
/// Skips traits we don't know how to emit (anything except Clone, PartialEq, Ord, etc.).
pub(crate) fn emit_trait_impl_struct(
    w: &mut IndentWriter,
    imp: &StyxTraitImpl,
    fun_id_to_name: &std::collections::HashMap<u32, String>,
    emitted_fun_names: &std::collections::HashSet<String>,
) {
    // Extract trait short name (e.g., "Clone" from "std::clone::Clone")
    let trait_short = imp.trait_path.rsplit("::").next().unwrap_or("");
    // Only emit structures for known traits that Aeneas provides.
    // Skip marker traits (StructuralPartialEq etc.) and traits we don't yet handle.
    let supported = matches!(trait_short, "Clone" | "PartialEq" | "Default");
    if !supported {
        return;
    }

    // Compute self type short name and module path
    let (self_module, self_short, self_lean_type) = match trait_impl_self_type_info(&imp.self_ty) {
        Some(info) => info,
        None => return, // not a nominal ADT type
    };

    // Compute Aeneas-style impl struct name. Pattern depends on the trait:
    //   Clone T         → CloneT          (1 type arg)
    //   PartialEq T     → PartialEqTT     (2 type args — other defaults to Self)
    //   Default T       → DefaultT        (1 type arg)
    let impl_struct_name = match trait_short {
        "PartialEq" => format!("{trait_short}{self_short}{self_short}"),
        _ => format!("{trait_short}{self_short}"),
    };
    let full_impl_name = if self_module.is_empty() {
        impl_struct_name.clone()
    } else {
        format!("{self_module}.{impl_struct_name}")
    };

    // Compute trait Lean type (e.g., "core.clone.Clone")
    let trait_lean = trait_path_to_lean(&imp.trait_path);

    // Compute the Lean type arg list (e.g., "Right Right" for PartialEq, "Right" for Clone)
    let type_args = match trait_short {
        "PartialEq" => format!("{self_lean_type} {self_lean_type}"),
        _ => self_lean_type.clone(),
    };

    // Build method mappings: method_name := full_method_path
    let mut method_lines: Vec<String> = Vec::new();
    let mut all_methods_emitted = true;
    for m in &imp.methods {
        let method_fn_name = match fun_id_to_name.get(&m.fun_id.0) {
            Some(n) => n.clone(),
            None => {
                all_methods_emitted = false;
                break;
            }
        };
        // Only reference functions that were successfully emitted (not opaque).
        // If a method is opaque, we can't build the impl struct.
        if !emitted_fun_names.contains(&method_fn_name) {
            all_methods_emitted = false;
            break;
        }
        let escaped_name = escape_lean_keyword(&m.name);
        method_lines.push(format!("  {escaped_name} := {method_fn_name}"));
    }

    if !all_methods_emitted || method_lines.is_empty() {
        return;
    }

    // Emit the impl struct
    w.writeln(format!(
        "@[reducible, rust_trait_impl \"{}\"]",
        imp.trait_path
    ));
    w.writeln(format!(
        "def {full_impl_name} : {trait_lean} {type_args} := {{"
    ));
    for line in &method_lines {
        w.writeln(line);
    }
    w.writeln("}");
    w.newline();
}

/// Extract (module_path, short_name, lean_type) from a self type of a trait impl.
/// Returns None if the self type is not a nominal ADT that we can handle.
pub(crate) fn trait_impl_self_type_info(ty: &StyxType) -> Option<(String, String, String)> {
    let rust_path = match ty {
        StyxType::Adt { rust_path, .. } => rust_path.as_str(),
        _ => return None,
    };
    // Strip generics
    let no_gens = strip_generics(rust_path);
    // Skip std types
    if no_gens.starts_with("std::")
        || no_gens.starts_with("core::")
        || no_gens.starts_with("alloc::")
    {
        return None;
    }
    // Extract short name (last segment)
    let (module, short) = match no_gens.rfind("::") {
        Some(pos) => (&no_gens[..pos], &no_gens[pos + 2..]),
        None => ("", no_gens.as_str()),
    };
    // Strip lion_core prefix and convert :: to .
    let module_lean = module
        .replace("::", ".")
        .strip_prefix("lion_core.")
        .map(|s| s.to_string())
        .unwrap_or_else(|| module.replace("::", "."));
    let module_escaped = if module_lean.is_empty() {
        String::new()
    } else {
        module_lean
            .split('.')
            .map(escape_lean_keyword)
            .collect::<Vec<_>>()
            .join(".")
    };
    // Lean type: same as module_escaped + "." + short
    let lean_type = if module_escaped.is_empty() {
        short.to_string()
    } else {
        format!("{module_escaped}.{short}")
    };
    Some((module_escaped, short.to_string(), lean_type))
}

/// Convert a Rust trait path to its Lean equivalent (Aeneas standard library).
pub(crate) fn trait_path_to_lean(trait_path: &str) -> String {
    // Common mappings
    match trait_path {
        "std::clone::Clone" | "core::clone::Clone" => "core.clone.Clone".to_string(),
        "std::cmp::PartialEq" | "core::cmp::PartialEq" => "core.cmp.PartialEq".to_string(),
        "std::cmp::Eq" | "core::cmp::Eq" => "core.cmp.Eq".to_string(),
        "std::cmp::PartialOrd" | "core::cmp::PartialOrd" => "core.cmp.PartialOrd".to_string(),
        "std::cmp::Ord" | "core::cmp::Ord" => "core.cmp.Ord".to_string(),
        "std::default::Default" | "core::default::Default" => "core.default.Default".to_string(),
        _ => {
            // Fallback: just replace :: with . and strip std/core prefix if needed
            trait_path.replace("::", ".")
        }
    }
}

/// Detect pure field accessor methods: `fn field(&self) -> T { self.field }`
/// These clash with Lean's auto-generated struct field accessors and should be skipped.
pub(crate) fn is_field_accessor(def: &StyxFunDef) -> bool {
    // Must have exactly 1 parameter (self)
    if def.params.len() != 1 {
        return false;
    }
    let body = match &def.body {
        Some(b) => b,
        None => return false,
    };
    // Body must be a single Return statement
    if body.block.stmts.len() != 1 {
        return false;
    }
    let ret_expr = match &body.block.stmts[0] {
        StyxStmt::Return(e) => e,
        _ => return false,
    };
    // Return value must be a field access on the first parameter
    // THIR produces Deref(Local(id)) for &self methods, or just Local(id)
    let field_name = match &ret_expr.kind {
        StyxExprKind::Field {
            base, field_name, ..
        } => {
            let local_id = match &base.kind {
                StyxExprKind::Local(id) => Some(id.0),
                StyxExprKind::Deref(inner) => match &inner.kind {
                    StyxExprKind::Local(id) => Some(id.0),
                    _ => None,
                },
                _ => None,
            };
            match local_id {
                Some(lid) => {
                    let first_param_id = body.locals.first().map(|l| l.id.0);
                    if Some(lid) != first_param_id {
                        return false;
                    }
                    field_name
                }
                None => return false,
            }
        }
        _ => return false,
    };
    // The function's last path segment must match the field name
    let fn_last_seg = def.rust_path.rsplit("::").next().unwrap_or("");
    fn_last_seg == field_name
}

/// Check if function name matches a field of its self-parameter's struct type.
/// This catches accessors with complex reborrow patterns that `is_field_accessor` misses.
pub(crate) fn is_field_name_clash(def: &StyxFunDef, types: &TypeLookup) -> bool {
    if def.params.is_empty() {
        return false;
    }
    let fn_last_seg = def.rust_path.rsplit("::").next().unwrap_or("");
    if fn_last_seg.is_empty() {
        return false;
    }
    // Get the self type (unwrap references)
    let self_ty = &def.params[0].ty;
    let inner_ty = match self_ty {
        StyxType::Ref { inner, .. } => inner.as_ref(),
        other => other,
    };
    let type_id = match inner_ty {
        StyxType::Adt {
            type_id: Some(tid), ..
        } => tid,
        _ => return false,
    };
    // Look up the type definition and check if it has a field with this name
    if let Some(td) = types.get(&type_id.0) {
        match &td.kind {
            StyxTypeDefKind::Struct { fields } => fields.iter().any(|f| f.name == fn_last_seg),
            _ => false,
        }
    } else {
        false
    }
}


/// Check if a function takes &mut self (mutation methods can't be faithfully emitted)
pub(crate) fn is_mut_self_method(def: &StyxFunDef) -> bool {
    def.params
        .first()
        .is_some_and(|p| p.is_mut_self || matches!(&p.ty, StyxType::Ref { is_mut: true, .. }))
}

/// Emit a function definition. Returns true if the function was made opaque
/// due to sorry in its body.
pub(crate) fn emit_fun_def(
    w: &mut IndentWriter,
    def: &StyxFunDef,
    types: &TypeLookup,
    _aeneas_compat: bool,
    emit_checks: bool,
) -> bool {
    // Skip pure field accessors — they clash with Lean's struct field accessors
    if is_field_accessor(def) || is_field_name_clash(def, types) {
        let lean_name = rust_path_to_lean(&def.rust_path);
        w.writeln(format!("-- skipped field accessor: {lean_name}"));
        w.newline();
        return false;
    }

    let lean_name = rust_path_to_lean(&def.rust_path);
    let ret_ty = emit_type(&def.ret_ty);

    // Build local name map: LocalId → user-facing name.
    // Body locals have real names from THIR (e.g., "self_", "right", "other").
    // For Lean emission, we use these real names to match Aeneas output conventions.
    // Names that collide with Lean namespace prefixes (e.g., "state" shadowing "state.xxx")
    // are renamed with a trailing underscore.
    let body_locals = def.body.as_ref().map(|b| &b.locals);
    // Namespace prefixes used in the generated code that parameters must not shadow.
    let ns_prefixes: &[&str] = &[
        "state", "types", "step", "kernel", "error", "crypto", "plugin", "core", "alloc", "std",
    ];
    let local_name_map: std::collections::HashMap<u32, String> = body_locals
        .map(|locals| {
            locals
                .iter()
                .map(|l| {
                    let mut name = escape_lean_keyword(&l.name);
                    if ns_prefixes.contains(&name.as_str()) {
                        name.push('_');
                    }
                    (l.id.0, name)
                })
                .collect()
        })
        .unwrap_or_default();

    let params: Vec<String> = def
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            // Prefer the body local's real name for parameters
            let mut pname = body_locals
                .and_then(|locals| locals.get(i))
                .map(|l| escape_lean_keyword(&l.name))
                .unwrap_or_else(|| escape_lean_keyword(&p.name));
            // Rename parameters that shadow namespace prefixes
            if ns_prefixes.contains(&pname.as_str()) {
                pname.push('_');
            }
            let pty = emit_type(&p.ty);
            format!("({pname} : {pty})")
        })
        .collect();

    // Skip functions whose signature references unresolvable external types
    let sig_check = format!("{} {} {}", lean_name, params.join(" "), ret_ty);
    if contains_unknown_namespace(&sig_check) {
        w.writeln(format!(
            "-- skipped (unresolvable types in signature): {lean_name}"
        ));
        w.newline();
        return false;
    }

    let generics = emit_generics_binder(&def.generics);
    let params_str = if params.is_empty() {
        String::new()
    } else {
        format!(" {}", params.join(" "))
    };

    let mut made_opaque = false;

    match &def.body {
        Some(body) => {
            // Set local name map for this function's body emission
            set_local_names(local_name_map.clone());

            // Set parameter ID set: the first N locals (where N = params.len()) are parameters.
            // These are excluded from option-condition payload detection so that a function
            // parameter shadowed by a .some arm doesn't get picked as the payload name.
            let param_ids: std::collections::HashSet<u32> = body_locals
                .map(|locals| {
                    locals
                        .iter()
                        .take(def.params.len())
                        .map(|l| l.id.0)
                        .collect()
                })
                .unwrap_or_default();
            set_param_ids(param_ids);

            // Emit body to a temporary writer to check for sorry
            let mut tmp = IndentWriter::new();
            emit_body(&mut tmp, body, types);
            let mut body_text = tmp.finish();

            // Fix derived PartialEq with data-carrying variants:
            // Pattern: ok (discr && (match (self, other) with | (.V a, .V b) => ok (a == b) | _ => true))
            // Issue: match arms return `Result Bool` (via ok) but `&&` expects `Bool`.
            // Fix: wrap match with `← do` to lift Result, change `_ => true` to `_ => ok true`.
            let partial_eq_fixed =
                if body_text.contains("discriminant_value") && body_text.contains("&& (match") {
                    // Lift the match into monadic context
                    body_text = body_text.replace("&& (match", "&& (← do match");
                    // Ensure wildcard arms return Result Bool, not Bool
                    body_text = body_text.replace("| _ => true))", "| _ => ok true))");
                    // Handle unreachable wildcard arm (3 closing parens: unreachable() + match + ok)
                    body_text = body_text
                        .replace("| _ => (std.intrinsics.unreachable)))", "| _ => ok true))");
                    // Generic PartialEq.eq / alloc.vec.PartialEq.eq in derived PartialEq arms:
                    // These compare ADT fields (NodeState, SecurityLevel, Vec) that lack BEq instances.
                    // For now, guard functions that still contain these after the fix.
                    // TODO: route to concrete PartialEq impls (e.g., PartialEqNodeState.eq)
                    true
                } else {
                    false
                };

            // map_err: desugar to monadic match with fail .panic on Err path.
            // Ok constructor is polymorphic in E, so Lean infers correct error type.
            let map_err_count = desugar_map_err(&mut body_text);
            let map_err_fixed = map_err_count > 0;

            // Fix Slice/Array return type mismatch: as_bytes methods return Slice U8
            // but body accesses Array field. Wrap with Array.to_slice.
            let slice_fixed = if ret_ty.contains("Slice") && body_text.contains("ok self.bytes") {
                body_text = body_text.replace("ok self.bytes", "ok (Array.to_slice self.bytes)");
                true
            } else {
                false
            };

            // Fix option_is_some: Option.is_some takes Option T, but inner call returns Result (Option T).
            // Add ← to unwrap inner monadic call. No ok wrapper needed: is_some returns Result Bool.
            let option_is_some_fixed = if body_text.contains("Option.is_some Usize (state.") {
                let mut changed = false;
                changed |=
                    insert_bind_before(&mut body_text, "state.kernel.RevocationState.find_index");
                changed |=
                    insert_bind_before(&mut body_text, "state.workflow.WorkflowDef.node_index");
                changed
            } else {
                false
            };

            // Fix Capability field access in verify_cap_seal:
            // - Capability.payload is a `def` returning `Result CapPayload` → needs ←
            // - Capability.epoch is a structure projection returning `U64` → remove spurious ←
            let verify_cap_seal_fixed = if body_text.contains("KeyState.verify_with_epoch")
                || body_text.contains("KeyState.verify_seal")
            {
                let mut fixed = false;
                // Add ← to Capability.payload (returns Result CapPayload)
                if body_text.contains("(types.capability.Capability.payload cap)")
                    && !body_text.contains("(← (types.capability.Capability.payload cap)")
                {
                    fixed |= insert_bind_before(
                        &mut body_text,
                        "types.capability.Capability.payload cap",
                    );
                }
                // Remove spurious ← from Capability.epoch (pure structure projection)
                if body_text.contains("(← (types.capability.Capability.epoch cap))") {
                    body_text = body_text.replace(
                        "(← (types.capability.Capability.epoch cap))",
                        "(types.capability.Capability.epoch cap)",
                    );
                    fixed = true;
                }
                fixed
            } else {
                false
            };

            // Fix binary_search: returns Result (core.result.Result Usize Usize), needs ←
            // when used inside Result.is_ok or other consumers expecting the inner type.
            let binary_search_fixed = if body_text.contains("core.slice.binary_search")
                && !body_text.contains("(← (core.slice.binary_search")
            {
                insert_bind_before(&mut body_text, "core.slice.binary_search")
            } else {
                false
            };

            // Fix find_index: returns Result (Option Usize), needs ← when used in match.
            let find_index_fixed = if body_text.contains("RevocationState.find_index")
                && !body_text.contains("(← (state.kernel.RevocationState.find_index")
                && !body_text.contains("\u{2190} (state.kernel.RevocationState.find_index")
            {
                insert_bind_before(&mut body_text, "state.kernel.RevocationState.find_index")
            } else {
                false
            };

            // Fix MetaState.free_mut: returns Result (core.result.Result Unit MemoryError), needs ←
            // when used as match scrutinee — arms match on inner core.result.Result, not outer Result.
            // Pattern: `match (state.memory.MetaState.free_mut ...) with | .Ok _ => ... | .Err _ => ...`
            // Fix: `match (← (state.memory.MetaState.free_mut ...)) with ...`
            let meta_free_fixed = if body_text.contains("match (state.memory.MetaState.free_mut")
                && !body_text.contains("match (← (state.memory.MetaState.free_mut")
            {
                insert_bind_before(&mut body_text, "state.memory.MetaState.free_mut")
            } else {
                false
            };

            // Fix MetaState::free_mut body (F1+F2, issue #273):
            // F1: BTreeMap.get_mut returns Result (Option V) — match scrutinee needs ← to unwrap Result.
            // F2+arm: the .some arm body models `*status = Freed` (side effect erased in Lean value model)
            //   + insert_freed_addr (monadic). Simplify to a do-block that binds insert_freed_addr and
            //   returns Ok(()). Also remove the duplicate .some _ arm (Rust Some(Freed) case, unreachable
            //   after unifying both Some arms into one).
            let _get_mut_bind_fixed = {
                let mut fixed = false;
                // F1: BTreeMap.get_mut match scrutinee needs ← (only if not already present).
                if body_text.contains("match (std.collections.BTreeMap.get_mut")
                    && !body_text.contains("match (← (std.collections.BTreeMap.get_mut")
                {
                    if insert_bind_before(&mut body_text, "std.collections.BTreeMap.get_mut") {
                        fixed = true;
                    }
                    // Simplify the .some arm body: replace the DUMMY-assign+insert block with an inline do.
                    // The Lean model erases *status = Freed (BTreeMap is value-typed in Lean);
                    // only insert_freed_addr carries observable semantics.
                    let old_arm = "| .some local_38 => (let _ := (let _ := (.Freed); local_38); (let _ := (state.memory.MetaState.insert_freed_addr self.freed_set addr); (.Ok ())))";
                    let new_arm = "| .some _ => do let _ ← (state.memory.MetaState.insert_freed_addr self.freed_set addr); ok (.Ok ())";
                    if body_text.contains(old_arm) {
                        body_text = body_text.replace(old_arm, new_arm);
                        fixed = true;
                    }
                }
                // F2 (dedup): Remove the duplicate .some _ arm — runs regardless of whether F1 fired.
                // In MetaState::free_mut, after the BTreeMap.get_mut match arm rewrite, there are
                // two `.some _` arms: one that does insert_freed_addr, one that returns DoubleFree.
                // Lean rejects duplicate patterns ("Redundant alternative: some val✝").
                // The DoubleFree arm is unreachable (already checked by is_freed_addr guard above).
                //
                // Two forms to check — at this point desugar_pure_arms has NOT yet run:
                //   pre-desugar:  | .some _ => (.Err (.DoubleFree addr))
                //   post-desugar: | .some _ => ok (.Err (.DoubleFree addr))
                // We check both so the removal works regardless of ordering.
                let dup_arm_pre = " | .some _ => (.Err (.DoubleFree addr))";
                let dup_arm_post = " | .some _ => ok (.Err (.DoubleFree addr))";
                if body_text.contains(dup_arm_pre) {
                    body_text = body_text.replace(dup_arm_pre, "");
                    fixed = true;
                } else if body_text.contains(dup_arm_post) {
                    body_text = body_text.replace(dup_arm_post, "");
                    fixed = true;
                }
                fixed
            };

            // Fix crypto.verify_seal in match arms: returns Result Bool, needs ← binding.
            // insert_bind_before is insufficient when (← (crypto.verify_seal already exists elsewhere,
            // so we scan all occurrences and wrap only unbound ones.
            // Pattern: KeyState.verify_seal has one bound (if condition) + one unbound (match arm).
            let verify_seal_fixed = if body_text.contains("crypto.verify_seal") {
                let mut fixed = false;
                let search_pattern = "(crypto.verify_seal ";
                let mut search_from = 0;
                loop {
                    let Some(rel) = body_text[search_from..].find(search_pattern) else {
                        break;
                    };
                    let abs_pos = search_from + rel;
                    if body_text[..abs_pos].ends_with("(← ") {
                        search_from = abs_pos + search_pattern.len();
                        continue;
                    }
                    if let Some(close) = match_paren_bytes(body_text.as_bytes(), abs_pos) {
                        let call = body_text[abs_pos..=close].to_string();
                        let wrapped = format!("(← {})", call);
                        body_text.replace_range(abs_pos..=close, &wrapped);
                        search_from = abs_pos + wrapped.len();
                        fixed = true;
                    } else {
                        search_from = abs_pos + search_pattern.len();
                    }
                }
                fixed
            } else {
                false
            };

            // Fix result_without_bind: monadic call used without ← bind.
            // WorkflowInstance.is_pending/is_active: get_node_state returns Result NodeState
            // NOTE: new emitter already emits (← (get_node_state ...)) via emit_expr_lifted,
            // so insert_bind_before returns false (already present). Mark as fixed when ← exists.
            let node_state_fixed = if body_text.contains("get_node_state self") {
                if body_text.contains("(← (state.workflow.WorkflowInstance.get_node_state") {
                    true // Already correctly emitted — mark as fixed so guard doesn't fire
                } else {
                    insert_bind_before(
                        &mut body_text,
                        "state.workflow.WorkflowInstance.get_node_state",
                    )
                }
            } else {
                false
            };

            // Fix result_without_bind: properly_mediated calls Authorized.validate without ←
            // Result.is_ok expects core.result.Result T E, but validate returns Result (c.r.R T E).
            // No ok wrapper: Result.is_ok returns Result Bool.
            let validate_fixed =
                if body_text.contains("Result.is_ok") && body_text.contains(".validate auth") {
                    insert_bind_before(&mut body_text, "step.authorization.Authorized.validate")
                } else {
                    false
                };

            // Fix Option.is_none: inner RevocationState.get returns Result (Option T), needs ←
            // NOTE: new emitter already emits (← (RevocationState.get ...)) via emit_expr_lifted,
            // so insert_bind_before returns false (already present). Mark as fixed when ← exists.
            let is_none_fixed = if body_text.contains("Option.is_none")
                && body_text.contains("RevocationState.get (state.kernel.KernelState")
            {
                if body_text
                    .contains("(← (state.kernel.RevocationState.get (state.kernel.KernelState")
                {
                    true // Already correctly emitted — mark as fixed so guard doesn't fire
                } else {
                    insert_bind_before(
                        &mut body_text,
                        "state.kernel.RevocationState.get (state.kernel.KernelState",
                    )
                }
            } else {
                false
            };

            // Fix result_in_match: PolicyState.eval returns Result PolicyDecision, needs ← in match
            let eval_in_match_fixed = if body_text.contains("match (types.policy.PolicyState.eval")
            {
                insert_bind_before(&mut body_text, "types.policy.PolicyState.eval")
            } else {
                false
            };

            // Fix RevocationState.get in match discriminee: returns Result (Option Capability), needs ←
            // has_ancestor_with_fuel uses `match (RevocationState.get self cap_id) with | .none => ...`
            let revoc_get_fixed = if body_text.contains("match (state.kernel.RevocationState.get ")
            {
                if body_text.contains("(← (state.kernel.RevocationState.get ") {
                    true // already correctly bound
                } else {
                    insert_bind_before(&mut body_text, "state.kernel.RevocationState.get ")
                }
            } else {
                false
            };

            // Fix err_subblock: early-return in a nested expression block, two patterns:
            // Pattern 1: ok (let _ := (.Err ERR); ())  →  return (.Err ERR)
            // Pattern 2: ok (if COND then (let _ := (.Err ERR); ()) else ())  →  if COND then return (.Err ERR)
            let err_subblock_fixed = {
                let has_p1 = body_text.contains("ok (let _ := (.Err ");
                let has_p2 =
                    body_text.contains("ok (if ") && body_text.contains(" then (let _ := (.Err ");
                if has_p1 || has_p2 {
                    let mut fixed = false;
                    // Pattern 1: ok (let _ := (.Err ERR); ())  →  return (.Err ERR)
                    if has_p1 {
                        let search = "ok (let _ := (.Err ";
                        let mut from = 0;
                        loop {
                            let Some(rel) = body_text[from..].find(search) else {
                                break;
                            };
                            let abs = from + rel;
                            // err_paren_pos points at the '(' of (.Err ERR)
                            let err_paren_pos = abs + "ok (let _ := ".len();
                            let Some(close) =
                                match_paren_bytes(body_text.as_bytes(), err_paren_pos)
                            else {
                                from = abs + search.len();
                                continue;
                            };
                            if !body_text[close + 1..].starts_with("; ())") {
                                from = abs + search.len();
                                continue;
                            }
                            // Extract content inside (.Err ERR); content starts with ".Err ..."
                            let content = body_text[err_paren_pos + 1..close].to_string();
                            let replacement = format!("return ({content})");
                            body_text.replace_range(abs..close + 6, &replacement);
                            from = abs + replacement.len();
                            fixed = true;
                        }
                    }
                    // Pattern 2: ok (if COND then (let _ := (.Err ERR); ()) else ())
                    //          →  if COND then return (.Err ERR)
                    if has_p2 || body_text.contains("ok (if ") {
                        let then_marker = " then (let _ := (.Err ";
                        let mut from = 0;
                        loop {
                            let Some(rel) = body_text[from..].find("ok (if ") else {
                                break;
                            };
                            let abs = from + rel;
                            let cond_start = abs + "ok (if ".len();
                            let Some(then_rel) = body_text[cond_start..].find(then_marker) else {
                                from = abs + "ok (if ".len();
                                continue;
                            };
                            let cond = body_text[cond_start..cond_start + then_rel].to_string();
                            // err_paren_pos points at '(' of (.Err ERR)
                            let err_paren_pos = cond_start + then_rel + " then (let _ := ".len();
                            let Some(close) =
                                match_paren_bytes(body_text.as_bytes(), err_paren_pos)
                            else {
                                from = abs + "ok (if ".len();
                                continue;
                            };
                            if !body_text[close + 1..].starts_with("; ()) else ())") {
                                from = abs + "ok (if ".len();
                                continue;
                            }
                            // content starts with ".Err ..." — don't add extra dot
                            let content = body_text[err_paren_pos + 1..close].to_string();
                            let replacement = format!("if {cond} then return ({content})");
                            // Replace: ok (if COND then (let _ := (.Err ERR); ()) else ())
                            //         abs..close + len("; ()) else ())") = close+15
                            body_text.replace_range(abs..close + 15, &replacement);
                            from = abs + replacement.len();
                            fixed = true;
                        }
                    }
                    fixed
                } else {
                    false
                }
            };

            // Pattern P3: Restructure match-arm Err propagation as if-let early return.
            // Input (emitter produces match with dead Err-in-let pattern):
            //   match (← (ITER)) with
            //   \n  | .none => ok ()
            //   \n  | .some LOCAL => do
            //   \n    let _ := (let _ := (.Err CONTENT); ())
            //   \n    ok ()
            // Output (correct Lean4 early-return idiom):
            //   let _opt_N ← ITER
            //   if let .some LOCAL := _opt_N then
            //     return (.Err CONTENT)
            //
            // Pattern P4: same but with conditional Err:
            // Input:
            //   | .some LOCAL => do
            //   \n    let _ := (if COND then (let _ := (.Err CONTENT); ()) else ())
            //   \n    ok ()
            // Output:
            //   if let .some LOCAL := _opt_N then
            //     if COND then return (.Err CONTENT)
            let _arm_early_return_fixed = {
                let some_do_sfx = " => do\n";
                let has_simple = body_text.contains("let _ := (let _ := (.Err ");
                let has_cond = body_text.contains(" then (let _ := (.Err ");
                let match_arrow_hdr = "match (\u{2190} ("; // "match (← ("
                if (has_simple || has_cond) && body_text.contains(match_arrow_hdr) {
                    let mut opt_ctr = 0u32;
                    let mut fixed = false;
                    let mut from = 0usize;
                    loop {
                        // Find the match header "match (← ("
                        let Some(rel) = body_text[from..].find(match_arrow_hdr) else { break };
                        let abs = from + rel;
                        // expr_open is the '(' of the match discriminee expression
                        let expr_open = abs + "match (\u{2190} ".len();
                        let Some(expr_close) =
                            match_paren_bytes(body_text.as_bytes(), expr_open)
                        else {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        };
                        // After expr_close, must be ") with\n  ...| .none => ok ()\n  ...| .some "
                        // Allow variable indentation (2 or 4 spaces)
                        let after_close = &body_text[expr_close + 1..];
                        let none_arm_sfx = "| .none => ok ()";
                        let some_arm_sfx = "| .some ";
                        if !after_close.starts_with(") with\n") {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        }
                        let with_end = expr_close + 1 + ") with\n".len();
                        // skip leading spaces for none arm
                        let none_ws = body_text[with_end..].chars().take_while(|c| *c == ' ').count();
                        let none_arm_start = with_end + none_ws;
                        if !body_text[none_arm_start..].starts_with(none_arm_sfx) {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        }
                        let after_none = none_arm_start + none_arm_sfx.len();
                        // After ".none => ok ()" expect "\n  ...| .some "
                        if !body_text[after_none..].starts_with('\n') {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        }
                        let some_line_start = after_none + 1;
                        let some_ws = body_text[some_line_start..].chars().take_while(|c| *c == ' ').count();
                        let some_arm_abs = some_line_start + some_ws;
                        if !body_text[some_arm_abs..].starts_with(some_arm_sfx) {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        }
                        let local_start = some_arm_abs + some_arm_sfx.len();
                        let Some(do_rel) = body_text[local_start..].find(some_do_sfx) else {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        };
                        let local_name =
                            body_text[local_start..local_start + do_rel].to_string();
                        // Allow simple names (e.g. `local_35`) or tuple-destructure
                        // patterns (e.g. `(local_35, _)` from iter-over-tuples).
                        // Reject only names that contain newlines or look like
                        // multi-word non-patterns (spaces not inside a tuple wrapper).
                        let is_tuple_pat = local_name.trim().starts_with('(')
                            && local_name.trim().ends_with(')');
                        if local_name.contains('\n')
                            || (!is_tuple_pat && local_name.contains(' '))
                            || (!is_tuple_pat && local_name.contains('('))
                        {
                            from = abs + match_arrow_hdr.len();
                            continue;
                        }
                        let body_line_start = local_start + do_rel + some_do_sfx.len();
                        let ws = body_text[body_line_start..]
                            .chars()
                            .take_while(|c| *c == ' ')
                            .count();
                        let body_start = body_line_start + ws;
                        let rest = &body_text[body_start..];
                        let p3_pfx = "let _ := (let _ := (.Err ";
                        let p4_pfx = "let _ := (if ";
                        let iter_expr = body_text[expr_open + 1..expr_close].to_string();
                        let opt_var = format!("_opt_{opt_ctr}");
                        opt_ctr += 1;
                        if has_simple && rest.starts_with(p3_pfx) {
                            // P3: err_paren points to '(' of (.Err CONTENT)
                            // body_start text: "let _ := (let _ := (.Err CONTENT); ())\n    ok ()"
                            //                                    ^ err_paren here
                            let err_paren = body_start + "let _ := (let _ := ".len();
                            let Some(err_close) =
                                match_paren_bytes(body_text.as_bytes(), err_paren)
                            else {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            };
                            // after err_close: "; ())\n    ok ()"
                            // "; ()" = semicolon + space + () then ")" closes outer let-bind paren
                            if !body_text[err_close + 1..].starts_with("; ())") {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            }
                            let after_wrap = err_close + 1 + "; ())".len();
                            let Some(nl) = body_text[after_wrap..].find('\n') else {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            };
                            let ok_line = after_wrap + nl + 1;
                            let ok_ws = body_text[ok_line..]
                                .chars()
                                .take_while(|c| *c == ' ')
                                .count();
                            let ok_pos = ok_line + ok_ws;
                            if !body_text[ok_pos..].starts_with("ok ()") {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            }
                            // CONTENT is already ".Err VAL" (don't add extra .Err)
                            let err_content =
                                body_text[err_paren + 1..err_close].to_string();
                            let end = ok_pos + "ok ()".len();
                            // Emit: let _opt_N ← ITER\nif let .some LOCAL := _opt_N then\n  return (.Err CONTENT)
                            let rep = format!(
                                "let {opt_var} \u{2190} {iter_expr}\nif let .some {local_name} := {opt_var} then\n  return ({err_content})"
                            );
                            body_text.replace_range(abs..end, &rep);
                            from = abs + rep.len();
                            fixed = true;
                        } else if has_cond && rest.starts_with(p4_pfx) {
                            // P4: body is "let _ := (if COND then (let _ := (.Err CONTENT); ()) else ())\n    ok ()"
                            let cond_start = body_start + "let _ := (if ".len();
                            let then_m = " then (let _ := (.Err ";
                            let Some(then_rel) = body_text[cond_start..].find(then_m) else {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            };
                            let cond = body_text[cond_start..cond_start + then_rel].to_string();
                            let err_paren = cond_start + then_rel + " then (let _ := ".len();
                            let Some(err_close) =
                                match_paren_bytes(body_text.as_bytes(), err_paren)
                            else {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            };
                            // after err_close: "; ()) else ())\n    ok ()"
                            if !body_text[err_close + 1..].starts_with("; ()) else ())") {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            }
                            let after_wrap = err_close + 1 + "; ()) else ())".len();
                            let Some(nl) = body_text[after_wrap..].find('\n') else {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            };
                            let ok_line = after_wrap + nl + 1;
                            let ok_ws = body_text[ok_line..]
                                .chars()
                                .take_while(|c| *c == ' ')
                                .count();
                            let ok_pos = ok_line + ok_ws;
                            if !body_text[ok_pos..].starts_with("ok ()") {
                                from = abs + match_arrow_hdr.len();
                                continue;
                            }
                            let err_content =
                                body_text[err_paren + 1..err_close].to_string();
                            let end = ok_pos + "ok ()".len();
                            let rep = format!(
                                "let {opt_var} \u{2190} {iter_expr}\nif let .some {local_name} := {opt_var} then\n  if {cond} then return ({err_content})"
                            );
                            body_text.replace_range(abs..end, &rep);
                            from = abs + rep.len();
                            fixed = true;
                        } else {
                            from = abs + match_arrow_hdr.len();
                        }
                    }
                    fixed
                } else {
                    false
                }
            };

            // Fix result_in_if: PolicyDecision.is_permit returns Result Bool, needs ← in if condition
            let is_permit_fixed = if body_text.contains("if (types.policy.PolicyDecision.is_permit")
            {
                insert_bind_before(&mut body_text, "types.policy.PolicyDecision.is_permit")
            } else {
                false
            };

            // Fix actor runtime if-conditions: is_blocked / blocked_on field / can_receive.
            // Needed for PluginInternal::check_preconditions.
            //   A. `if (is_blocked local_N) then` → hoist let-bind, `if _isblocked then`
            //   B. `(← (blocked_on local_N))` → `local_N.blocked_on` (field, not fn)
            //   C. `if (!(← (can_receive local_N))) then` → hoist let-bind, `if !_canrecv then`
            let actor_rt_if_fixed = if body_text.contains("state.actor.ActorRuntime.is_blocked")
                || body_text.contains("state.actor.ActorRuntime.blocked_on")
                || body_text.contains("state.actor.ActorRuntime.can_receive")
            {
                desugar_actor_runtime_if_conditions(&mut body_text)
            } else {
                false
            };
            let _ = actor_rt_if_fixed;

            // Collapse hmac/digest/typenum/generic_array type trees into opaque aliases.
            // GenericArray<U8, typenum::U32> → (Array U8 32#usize)
            while body_text.contains("hmac.digest.typenum.") || body_text.contains("hmac.digest.generic_array.") {
                let ga_prefix = "(hmac.digest.generic_array.GenericArray U8 (hmac.digest.typenum.";
                if let Some(start) = body_text.find(ga_prefix) {
                    let mut depth = 0i32;
                    let mut end = start;
                    for (i, ch) in body_text[start..].char_indices() {
                        match ch {
                            '(' => depth += 1,
                            ')' => {
                                depth -= 1;
                                if depth == 0 { end = start + i + 1; break; }
                            }
                            _ => {}
                        }
                    }
                    if end > start {
                        body_text.replace_range(start..end, "(Array U8 32#usize)");
                        continue;
                    }
                }
                break;
            }

            // IndexVec: desugar IndexVec.index calls to proper monadic form.
            // Adds ← to let bindings and function arguments, fixes match discriminees.
            let indexvec_fixed = desugar_indexvec(&mut body_text);

            // Collapse redundant double-bind created by desugar_indexvec:
            // `← (← (EXPR))` → `← (EXPR)` (remove action-lift layer leaving single bind).
            // desugar_indexvec converts `:= (← (IndexVec...))` to `← (← (IndexVec...))`.
            // The inner (←) is an action lift from the emitter; the outer ← is the let-bind.
            // In Lean `let x ← (← e)` double-binds; correct form is `let x ← e`.
            {
                let needle = "\u{2190} (\u{2190} (";
                while let Some(pos) = body_text.find(needle) {
                    let arrow_start = pos;
                    let inner_open = pos + needle.len() - 1;
                    if let Some(inner_close) = crate::emit::styxir::desugar::match_paren_bytes(body_text.as_bytes(), inner_open) {
                        let outer_close = inner_close + 1;
                        if outer_close < body_text.len() && body_text.as_bytes()[outer_close] == b')' {
                            let inner = &body_text[inner_open..=inner_close];
                            let replacement = format!("\u{2190} {inner}");
                            body_text.replace_range(arrow_start..=outer_close, &replacement);
                            continue;
                        }
                    }
                    break;
                }
            }

            // IndexMutVec: desugar supported mutable-index shapes into valid monadic form.
            // Returns true only when all IndexMutVec occurrences are in supported shapes.
            let index_mut_vec_fixed = desugar_index_mut_vec(&mut body_text);

            // Compound: copy_from_slice(IndexMutVec.index_mut vec range, src) → copy_from_slice_to_range
            let mut copy_from_slice_range_fixed = false;
            {
                let cfs_needle = "let _ \u{2190} (core.slice.copy_from_slice ";
                let imv_needle = "(alloc.vec.IndexMutVec.index_mut ";
                while let Some(line_start) = body_text.find(cfs_needle) {
                    let after_cfs = &body_text[line_start + cfs_needle.len()..];
                    let Some(type_end) = after_cfs.find(' ') else { break; };
                    let elem_type = after_cfs[..type_end].to_string();
                    let rest = &after_cfs[type_end + 1..];
                    if !rest.starts_with(imv_needle) { break; }
                    let imv_args = &rest[imv_needle.len()..];
                    let parts: Vec<&str> = imv_args.splitn(5, ' ').collect();
                    if parts.len() < 4 { break; }
                    let vec_var = parts[3].to_string();
                    let after_vec = &imv_args[parts[..4].iter().map(|s| s.len() + 1).sum::<usize>()..];
                    let Some(range_end) = after_vec.find("})") else { break; };
                    let range_str = &after_vec[..range_end + 1];
                    let field_0 = range_str.split("field_0 := ").nth(1).and_then(|s| s.split(',').next()).unwrap_or("").trim();
                    let field_1_raw = range_str.split("field_1 := ").nth(1).unwrap_or("");
                    let field_1_end = field_1_raw.find('}').unwrap_or(field_1_raw.len());
                    let field_1 = field_1_raw[..field_1_end].trim().trim_end_matches(')');
                    if field_0.is_empty() || field_1.is_empty() { break; }
                    let after_range = &after_vec[range_end + 2..];
                    let after_range = after_range.trim_start_matches(')').trim_start();
                    let line_end_rel = body_text[line_start..].find('\n').unwrap_or(body_text.len() - line_start);
                    let src = after_range.trim_end_matches(')').trim();
                    let replacement = format!("let {vec_var} \u{2190} (core.slice.copy_from_slice_to_range {elem_type} {vec_var} {field_0} {field_1} {src})");
                    body_text.replace_range(line_start..line_start + line_end_rel, &replacement);
                    copy_from_slice_range_fixed = true;
                }
            }

            // monadic dispatch: strip ok(match...) for dispatch functions where all arms are monadic
            let dispatch_fixed = desugar_monadic_dispatch(&mut body_text);

            // pure arms: wrap constructor arms in ok() after dispatch desugar strips ok(match...)
            let pure_arms_fixed = desugar_pure_arms(&mut body_text);

            // Fix wildcard match arms in Hash body functions: `| _ => ()` must be `| _ => ok ()`
            // because Hash::hash returns `Result Unit`. Derived Hash impls emit a wildcard arm
            // for enums with data-carrying variants (the non-Plugin/non-data variants):
            //   match self with | .Plugin local_34 => (std.hash.Hash.hash local_34 state_) | _ => ()
            // After removing std.hash. from unknown_prefixes these bodies emit transparently,
            // but the bare `()` arm is a Unit literal, not a Result Unit. Wrap it with ok().
            let hash_wildcard_fixed =
                if body_text.contains("std.hash.Hash.hash") && body_text.contains("| _ => ()") {
                    body_text = body_text.replace("| _ => ()", "| _ => ok ()");
                    true
                } else {
                    false
                };
            let _ = hash_wildcard_fixed;

            // Fix array literals passed to Slice-expecting functions.
            // #[(.Read), (.Write)] → ⟨[Right.Read, Right.Write], by simp⟩
            // This converts Lean Array to Aeneas Slice (subtype of List).
            let rights_array_fixed = if body_text.contains("from_slice #[") {
                let mut fixed = false;
                // Replace #[(Right.X), ...] with ⟨[Right.X, ...], by simp⟩
                // First qualify constructors, then convert array syntax to list
                for (old, new_val) in &[
                    ("(.Read)", "types.rights.Right.Read"),
                    ("(.Write)", "types.rights.Right.Write"),
                    ("(.Execute)", "types.rights.Right.Execute"),
                ] {
                    while body_text.contains(*old) {
                        body_text = body_text.replacen(*old, new_val, 1);
                        fixed = true;
                    }
                }
                // Convert #[a, b] to ⟨[a, b], by scalar_tac⟩ for Slice construction
                while let Some(start) = body_text.find("#[") {
                    if let Some(end) = body_text[start..].find(']') {
                        let inner = &body_text[start + 2..start + end].to_string();
                        let replacement = format!("⟨[{}], by scalar_tac⟩", inner);
                        body_text.replace_range(start..start + end + 1, &replacement);
                        fixed = true;
                    } else {
                        break;
                    }
                }
                fixed
            } else {
                false
            };

            // Qualify dotted constructors for StepError / HostCallPreconditionError.
            // These names are unique — no other type has these constructors.
            // Without qualification, `open Aeneas.Std Result` prevents Lean from
            // resolving the expected type for `.HostCallPreconditionFailed` etc.
            // Qualify dotted constructors for StepError / HostCallPreconditionError /
            // PluginPreconditionError. These names are unique — no other type has these
            // constructors. Without qualification, `open Aeneas.Std Result` prevents Lean
            // from resolving the expected type for `.HostCallPreconditionFailed` etc.
            // F5 (2026-04-14): also qualify `.PluginPreconditionFailed` for PluginInternal
            // find_oob_read/write where the inner StepError constructor needs type context.
            let step_error_fixed = if body_text.contains(".HostCallPreconditionFailed")
                || body_text.contains(".PluginPreconditionFailed")
            {
                for (old, new_val) in &[
                    (
                        "(.HostCallPreconditionFailed",
                        "(step.StepError.HostCallPreconditionFailed",
                    ),
                    (
                        "(.PluginPreconditionFailed ",
                        "(step.StepError.PluginPreconditionFailed ",
                    ),
                    (
                        "(.NoCapabilityId)",
                        "(step.HostCallPrecondition.NoCapabilityId)",
                    ),
                    ("(.NoAddress)", "(step.HostCallPrecondition.NoAddress)"),
                    (
                        "(.NotImplemented ",
                        "(step.HostCallPrecondition.NotImplemented ",
                    ),
                ] {
                    while body_text.contains(*old) {
                        body_text = body_text.replacen(*old, new_val, 1);
                    }
                }
                true
            } else {
                false
            };

            // F5 (2026-04-14): fix `addr_in_bounds` used as an `if` condition in closures.
            // `addr_in_bounds` returns `Result Bool`, so it needs `←` wrapping when used as an
            // `if` condition (Lean expects `Bool` / `Prop`, not `Result Bool`).
            // This affects HostCall::find_oob_read/write and PluginInternal::find_oob_read/write
            // where the closure body `fun arg1 => let (a,b) := arg1; if (addr_in_bounds ...) ...`
            // needs `do` and `←` for the monadic condition.
            //
            // Use insert_bind_before to properly wrap the call with balanced parens:
            //   (addr_in_bounds X) → (← (addr_in_bounds X))
            // Then add `do` to tuple-destructuring closures that now contain `←` but lack `do`.
            let addr_in_bounds_fixed = if body_text
                .contains("(state.memory.LinearMemory.addr_in_bounds ")
                && !body_text.contains("(← (state.memory.LinearMemory.addr_in_bounds ")
            {
                let bound =
                    insert_bind_before(&mut body_text, "state.memory.LinearMemory.addr_in_bounds");
                if bound {
                    // After adding ←, closures that lacked `do` now need it.
                    // Target the specific tuple-destructuring closure pattern from T1 (2026-04-14):
                    // `(fun arg1 => let (` — the `do` keyword is absent.
                    let pat_no_do = "(fun arg1 => let (";
                    let pat_with_do = "(fun arg1 => do let (";
                    if body_text.contains(pat_no_do) && !body_text.contains(pat_with_do) {
                        body_text = body_text.replace(pat_no_do, pat_with_do);
                    }
                }
                bound
            } else {
                false
            };

            // F5 part 2 (2026-04-14): Extract `←` from inside constructor arguments to let bindings.
            // In PluginInternal::find_oob_read/write, the closure has:
            //   (Option.some (step.StepError.PluginPreconditionFailed (.XxxOutOfBounds a b (← (memory_bounds plugin_)))))
            // Lean 4 prohibits `←` inside constructor arguments — it must be pulled out as a `let ← bind`.
            // Transform: replace `(← (state.plugin.PluginState.memory_bounds plugin_))` with a fresh
            // binding inserted just before the if-expression inside the `do` block.
            //
            // Pattern:
            //   ... let (a, b) := arg1; (if ... then ... else ... (← (memory_bounds ...)) ...)
            // becomes:
            //   ... let (a, b) := arg1; let local_mb ← (state.plugin.PluginState.memory_bounds plugin_); (if ...)
            let memory_bounds_extracted = {
                let mb_bind_target = "(← (state.plugin.PluginState.memory_bounds ";
                let mb_call_prefix = "state.plugin.PluginState.memory_bounds ";
                if body_text.contains(mb_bind_target) {
                    // Find all occurrences of the memory_bounds call inside constructors.
                    // We need to:
                    // 1. Find the `(← (state.plugin.PluginState.memory_bounds ...))`
                    // 2. Find its full span using paren matching
                    // 3. Replace it with a fresh name `local_mb`
                    // 4. Insert `let local_mb ← (state.plugin.PluginState.memory_bounds ...);` before the `(if`
                    let pattern = format!("(← ({}", mb_call_prefix);
                    let mut extracted = false;
                    let mut mb_idx = 0u32;
                    loop {
                        // Find the `←` wrapper: `(← (state.plugin.PluginState.memory_bounds X))`
                        // First find the outer `(←` which is the bind wrapper
                        if let Some(outer_start) = body_text.find(&pattern) {
                            // The outer_start points to `(← (memory_bounds ...)`
                            // We need to find the span of the OUTER paren `(← ...)`
                            if let Some(outer_end) =
                                match_paren_bytes(body_text.as_bytes(), outer_start)
                            {
                                let mb_expr = body_text[outer_start..=outer_end].to_string();
                                let local_name = format!("local_mb{}", mb_idx);
                                mb_idx += 1;
                                // Replace inline occurrence with local_name
                                body_text.replace_range(outer_start..=outer_end, &local_name);
                                // Now find the insertion point: after `let (local_17, local_18) := arg1; `
                                // i.e., find the `; (if ` pattern and insert before the `(`
                                let if_pattern = "; (if ";
                                if let Some(if_pos) = body_text.find(if_pattern) {
                                    let insert_at = if_pos + "; ".len(); // insert after "; "
                                    // Build the let binding: `let local_mbN ← mb_call_expr; `
                                    // Reconstruct the original call from the bind expression
                                    // mb_expr was `(← (memory_bounds X))`, so inner call is `(memory_bounds X)`
                                    // Strip leading `(← ` and trailing `)` to get the inner `(memory_bounds X)`
                                    let inner_call = &mb_expr[4..mb_expr.len() - 1]; // strip `(← ` prefix and `)` suffix
                                    let let_bind = format!("let {} ← {}; ", local_name, inner_call);
                                    body_text.insert_str(insert_at, &let_bind);
                                    extracted = true;
                                } else {
                                    // Couldn't find insertion point; restore the replacement
                                    // (unlikely - log it and break)
                                    break;
                                }
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }
                    extracted
                } else {
                    false
                }
            };

            // F5 part 3 (2026-04-14): Add `ok` wrapping to Option.none / Option.some in
            // find_map closure bodies. The closure is typed `→ Result (Option T)`, but after
            // emitting the if-then-else arms return bare `Option.none`/`Option.some X`.
            // Lean reports: "Application type mismatch: none has type Option ?m.X but expected Result (Option T)"
            //
            // Fix: inside closures that contain `addr_in_bounds` (i.e., the find_oob pattern):
            //   (Option.none) → (ok Option.none)
            //   (Option.some X) → (ok (Option.some X))
            //
            // Use a targeted pattern so we don't accidentally wrap Option values in other functions.
            // The trigger is the presence of `addr_in_bounds` in the body (already ensured by previous pass).
            let find_map_ok_fixed = if addr_in_bounds_fixed
                || body_text.contains("(← (state.memory.LinearMemory.addr_in_bounds ")
            {
                let mut changed = false;
                // Wrap (Option.none) → (ok Option.none)
                let old_none = "(Option.none)";
                let new_none = "(ok Option.none)";
                if body_text.contains(old_none) {
                    body_text = body_text.replace(old_none, new_none);
                    changed = true;
                }
                // Wrap (Option.some X) → (ok (Option.some X))
                // Pattern: `(Option.some ` ... `)` — use paren matching
                let some_prefix = "(Option.some ";
                let ok_some_prefix = "(ok (Option.some ";
                while body_text.contains(some_prefix) && !body_text.contains(ok_some_prefix) {
                    if let Some(pos) = body_text.find(some_prefix) {
                        if let Some(close) = match_paren_bytes(body_text.as_bytes(), pos) {
                            let inner = body_text[pos..=close].to_string();
                            let wrapped = format!("(ok {})", inner);
                            body_text.replace_range(pos..=close, &wrapped);
                            changed = true;
                        } else {
                            break;
                        }
                    } else {
                        break;
                    }
                }
                changed
            } else {
                false
            };
            let _ = memory_bounds_extracted;
            let _ = find_map_ok_fixed;

            // try_operator: desugar Rust `?` (TryResult.branch + FromResidual) → monadic bind (←).
            let try_op_count = desugar_try_operators(&mut body_text);
            let try_op_fixed = try_op_count > 0;

            // Desugar match on UScalar literals to if-else chains (Lean can't match on scalars)
            let uscalar_match_fixed = desugar_uscalar_match(&mut body_text);
            // F1 (issue #273): Insert ← bind around BTreeMap.get_mut in match discriminees.
            let get_mut_bind_fixed = desugar_get_mut_bind(&mut body_text);
            // F2 (issue #273): Fix duplicate .some _ arm → .none => for get_mut match.
            let _dup_arm_fixed = desugar_free_mut_dup_arm(&mut body_text);
            // F4 (issue #273): Rewrite (let _ := val; (local_N[local_M])) → ok ().
            let index_assign_fixed = desugar_index_assign_expr(&mut body_text);
            let _ = (get_mut_bind_fixed, index_assign_fixed); // suppress unused warnings
            // Desugar match on U64 discriminant values with catch-all binding (T5).
            // Fixes execute_declassify[_mut] where `match new_level_val { 0 => ..., other => return Err(...) }`
            // emits a catch-all that Lean can't compile (undefined local from binding + bare .Err tail).
            let _u64_discriminant_fixed = desugar_u64_discriminant_match(&mut body_text);
            // Desugar Iterator::find closure with compound monadic boolean condition.
            // Pattern: (fun arg1 => do ((← (E1)) && ((← (E2)) == V)))
            // Fix: sequential let-binds + ok(b0 && (b1 == V))
            let _find_closure_bool_fixed = desugar_find_closure_compound_bool(&mut body_text);
            // Loop Vec accumulator: thread locally-created Vec through let rec go_N loop.
            let loop_vec_accum_fixed = desugar_loop_vec_accumulator(&mut body_text);
            // Desugar binary_search in if-condition → match Ok/Err.
            let binary_search_if_fixed = desugar_binary_search_if(&mut body_text);
            // Desugar binary_search + Vec.insert/remove for unit-returning functions.
            let binary_search_unit_fixed = desugar_binary_search_unit(&mut body_text);
            // Wrap KernelState.revocation_mut calls with monadic bind.
            let _revocation_mut_bind_fixed = desugar_revocation_mut_bind(&mut body_text);
            // Vec::with_capacity(n) → Vec.new T: strip capacity argument.
            // Pattern: `let LOCAL ← (alloc.vec.Vec.new (CAP_EXPR))`
            // Fix: find element type T from `Vec.push T A LOCAL item` in body, then
            //   rewrite `Vec.new (CAP_EXPR)` → `Vec.new T`.
            let vec_new_capacity_fixed = {
                let mut changed = false;
                let prefix = "alloc.vec.Vec.new ";
                let extract_type_arg = |body: &str, callee: &str| -> Option<String> {
                    let pos = body.find(callee)?;
                    let after = &body[pos + callee.len()..];
                    if after.starts_with('(') {
                        // Parenthesized type like `(U64 × Capability)` — match to closing paren
                        let close = crate::emit::styxir::match_paren_bytes(after.as_bytes(), 0)?;
                        Some(after[..=close].to_string())
                    } else {
                        // Simple type like `U64` — take until next space
                        let end = after.find(' ').unwrap_or(after.len());
                        Some(after[..end].to_string())
                    }
                };
                let elem_type = extract_type_arg(&body_text, "alloc.vec.Vec.push ")
                    .or_else(|| extract_type_arg(&body_text, "alloc.vec.Vec.from_elem "))
                    .or_else(|| extract_type_arg(&body_text, "alloc.vec.Vec.insert "));
                if let Some(ref etype) = elem_type {
                    // Replace Vec.new (CAPACITY_EXPR) with Vec.new T
                    // Capacity patterns: `(UScalar.cast ...)` or `(← (...))`
                    for cap_start in ["(UScalar.cast", "(\u{2190}"] {
                        let needle = format!("{prefix}{cap_start}");
                        while let Some(pos) = body_text.find(&needle) {
                            let paren_start = pos + prefix.len();
                            if let Some(close) = crate::emit::styxir::match_paren_bytes(
                                body_text.as_bytes(), paren_start,
                            ) {
                                body_text.replace_range(paren_start..=close, etype);
                                changed = true;
                            } else {
                                break;
                            }
                        }
                    }
                }
                changed
            };
            // Check for known type-mismatch patterns in the body
            // Detect return type / body scalar mismatch (Usize vs U64).
            // Exception: bodies that use UScalar.cast .Usize handle the conversion correctly —
            // e.g., offset_in_page: BitAnd(addr, Sub(Shl(1#u64, PAGE_BITS), 1#u64)) emits with
            // UScalar.cast .Usize wrapping the result, so no type mismatch occurs.
            let ret_usize_body_u64 = ret_ty.contains("Usize")
                && body_text.contains("#u64")
                && !body_text.contains("UScalar.cast .Usize");
            // Detect pattern match on UScalar literals (Lean can't pattern match those)
            // Check AFTER desugaring — only fires if desugar didn't handle some pattern
            let has_uscalar_pat = body_text.contains("| 0#u8 =>")
                || body_text.contains("| 0#u16 =>")
                || body_text.contains("| 0#u32 =>")
                || body_text.contains("| 1#u8 =>")
                || body_text.contains("| 1#u16 =>")
                || body_text.contains("| 1#u32 =>");
            // Desugar array literal #[el, ...] to ⟨[el, ...], by simp⟩
            // Lean's #[...] creates Lean.Array, but Aeneas uses Array/Slice/Vec which use
            // { l : List α // l.length ≤ Usize.max } proofs requiring `by simp`.
            // Note: `by decide` works for fixed-size arrays but NOT for Slice/Vec literals
            // since Usize.max is not a concrete numeral that Lean's decide can evaluate.
            let array_literal_fixed = if body_text.contains("#[") {
                let mut fixed = false;
                while let Some(start) = body_text.find("#[") {
                    if let Some(rel_end) = body_text[start..].find(']') {
                        let end = start + rel_end;
                        let inner = body_text[start + 2..end].to_string();
                        let replacement = format!("(⟨[{}], by simp⟩)", inner);
                        body_text.replace_range(start..end + 1, &replacement);
                        fixed = true;
                    } else {
                        break;
                    }
                }
                fixed
            } else {
                false
            };
            // Second-pass ok-wrap: desugar_pure_arms section E ran before the #[...] → ⟨⟩
            // substitution, so angle-bracket arms created by array_literal_fixed were missed.
            // Repeat the same match-arm detection here to wrap them with ok().
            if array_literal_fixed && body_text.contains("=> (⟨") {
                let pat = "=> (⟨";
                let mut s = 0;
                loop {
                    let Some(rel) = body_text[s..].find(pat) else {
                        break;
                    };
                    let abs = s + rel;
                    let ae = abs + 3; // position of "("
                    if ae >= 3 && body_text[..ae].ends_with("ok ") {
                        s = abs + pat.len();
                        continue;
                    }
                    let before = &body_text[..abs];
                    let lp = before.rfind("| ");
                    let lf = before.rfind("fun ");
                    let is_arm = match (lp, lf) {
                        (Some(p), Some(f)) => p > f,
                        (Some(_), None) => true,
                        _ => false,
                    };
                    if !is_arm {
                        s = abs + pat.len();
                        continue;
                    }
                    body_text.insert_str(ae, "ok ");
                    s = ae + 3 + pat.len() - 3;
                }
            }
            // Third-pass ok-wrap: handle match arms of the form `=> (← expr).N` where the
            // field projection on a lifted Result gives a non-Result value that needs ok().
            // Example: get_children Ok arm → `(← IndexVec.index ...).2 : Vec U64`
            //          but return type is `Result (Slice U64)`, so needs `ok ((← ...).2)`.
            // Only applies to tuple-field projections (.1, .2, .3, …) since named-field
            // projections on Results are emitted differently and don't need this fix.
            if body_text.contains("=> (← ") {
                let pat = "=> (← ";
                let mut s = 0;
                loop {
                    let Some(rel) = body_text[s..].find(pat) else {
                        break;
                    };
                    let abs = s + rel;
                    let paren_start = abs + 3; // position of the '(' before '←'
                    // Skip if already wrapped in ok
                    if paren_start >= 3 && body_text[..paren_start].ends_with("ok ") {
                        s = abs + pat.len();
                        continue;
                    }
                    // Check it's in a match arm (preceded by '| ' with no intervening 'fun ')
                    let before = &body_text[..abs];
                    let lp = before.rfind("| ");
                    let lf = before.rfind("fun ");
                    let is_arm = match (lp, lf) {
                        (Some(p), Some(f)) => p > f,
                        (Some(_), None) => true,
                        _ => false,
                    };
                    if !is_arm {
                        s = abs + pat.len();
                        continue;
                    }
                    // Find balanced close of the outer '(' starting at paren_start
                    let mut depth = 0i32;
                    let mut end_paren: Option<usize> = None;
                    for (i, c) in body_text[paren_start..].char_indices() {
                        match c {
                            '(' => depth += 1,
                            ')' => {
                                depth -= 1;
                                if depth == 0 {
                                    end_paren = Some(paren_start + i);
                                    break;
                                }
                            }
                            _ => {}
                        }
                    }
                    let Some(ep) = end_paren else {
                        s = abs + pat.len();
                        continue;
                    };
                    // After the closing ')' look for a tuple field accessor `.N` (digit)
                    let rest = &body_text[ep + 1..];
                    let has_digit_field = rest.starts_with('.')
                        && rest.chars().nth(1).is_some_and(|c| c.is_ascii_digit());
                    if !has_digit_field {
                        s = abs + pat.len();
                        continue;
                    }
                    // Find end of the field accessor: stop at space, ')', or '|'
                    let mut field_end = ep + 1;
                    for (i, c) in rest.char_indices() {
                        if c == ' ' || c == ')' || c == '|' {
                            field_end = ep + 1 + i;
                            break;
                        }
                        field_end = ep + 1 + i + c.len_utf8();
                    }
                    // Insert from right to left to keep indices valid:
                    // 1. Insert ')' at field_end
                    // 2. Insert 'ok (' at paren_start
                    body_text.insert(field_end, ')');
                    body_text.insert_str(paren_start, "ok (");
                    s = paren_start + 4 + (ep - paren_start) + 1; // advance past inserted ok(
                }
            }
            // Fourth-pass paren-removal: match arms that contain `=> (match ...)` or
            // `=> (if ...)` (parenthesized expression as arm value) prevent Lean from desugaring
            // `←` inside the nested match/if arms. Removing the outer parens makes the inner
            // match/if a do-arm expression, allowing `←` in function arguments within its arms.
            // Condition: only run when the body has an arm-level `(match `/ `(if ` with `←`.
            let mut paren_removal_fixed = false;
            for keyword in &["(match ", "(if "] {
                let arm_pat = &format!("=> {keyword}");
                if body_text.contains(arm_pat.as_str()) && body_text.contains('←') {
                    let mut s = 0;
                    loop {
                        let Some(rel) = body_text[s..].find(arm_pat.as_str()) else {
                            break;
                        };
                        let abs = s + rel;
                        let paren_start = abs + 3; // position of the '(' before keyword
                        // Check it's a match arm (preceded by '| ' with no intervening 'fun ')
                        let before = &body_text[..abs];
                        let lp = before.rfind("| ");
                        let lf = before.rfind("fun ");
                        let is_arm = match (lp, lf) {
                            (Some(p), Some(f)) => p > f,
                            (Some(_), None) => true,
                            _ => false,
                        };
                        if !is_arm {
                            s = abs + arm_pat.len();
                            continue;
                        }
                        // Find matching ')' for the '(' at paren_start
                        let mut depth = 0i32;
                        let mut end_paren: Option<usize> = None;
                        for (i, c) in body_text[paren_start..].char_indices() {
                            match c {
                                '(' => depth += 1,
                                ')' => {
                                    depth -= 1;
                                    if depth == 0 {
                                        end_paren = Some(paren_start + i);
                                        break;
                                    }
                                }
                                _ => {}
                            }
                        }
                        let Some(ep) = end_paren else {
                            s = abs + arm_pat.len();
                            continue;
                        };
                        // Only remove parens if the inner expression contains `←` (otherwise no benefit)
                        let inner = &body_text[paren_start..=ep];
                        if !inner.contains('←') {
                            s = abs + arm_pat.len();
                            continue;
                        }
                        // Result.map_err desugars to a parenthesized nested match whose `←`
                        // is only in the discriminee. Keep those parens so the inner match
                        // arms do not consume following arms of the outer match.
                        if inner.contains(
                            "core.result.Result.Err map_err => ok (core.result.Result.Err",
                        ) {
                            s = abs + arm_pat.len();
                            continue;
                        }
                        // Remove: first the ')' at ep (right), then '(' at paren_start (left)
                        body_text.remove(ep);
                        body_text.remove(paren_start);
                        paren_removal_fixed = true;
                        s = paren_start + (ep - paren_start - 1); // adjust for removed chars
                    }
                }
            }
            // Vec-push result rebinding (Task B, 2026-04-15): when `let _ ← (Vec.push ... local_N ...)`
            // discards the updated Vec and `local_N` was extracted from `self.FIELD`, the struct
            // reconstruction at the end uses the OLD local_N (pre-push). Rebind to preserve mutation.
            // Example: enqueue_pending and deliver use VecDeque.push_back (mapped → Vec.push).
            //   BEFORE: let _ ← (alloc.vec.Vec.push T A local_N item)
            //   AFTER:  let local_N ← (alloc.vec.Vec.push T A local_N item)
            // Only applies when (1) the source variable was extracted from self and (2) it is used
            // in the struct reconstruction (`:= local_N`). This loop handles multiple occurrences.
            // Vec-push result rebinding: when `let _ ← (Vec.push ... local_N ...)` discards the
            // updated Vec and `local_N` was extracted from `self.FIELD`, rebind to preserve mutation.
            //   BEFORE: let _ ← (alloc.vec.Vec.push T A local_N item)
            //   AFTER:  let local_N ← (alloc.vec.Vec.push T A local_N item)
            // Applies to enqueue_pending and other functional-update patterns where the returned
            // ActorRuntime reconstructs the struct with the field sourced from local_N.
            let vec_push_rebound = if body_text.contains("let _ \u{2190} (alloc.vec.Vec.push") {
                let push_needle = "let _ \u{2190} (alloc.vec.Vec.push ";
                let mut rebindings: Vec<(String, String)> = Vec::new();
                let mut search_from = 0;
                loop {
                    let Some(rel) = body_text[search_from..].find(push_needle) else {
                        break;
                    };
                    let abs = search_from + rel;
                    // Pattern after "alloc.vec.Vec.push ": TYPE ALLOC local_N ITEM)
                    let after_push = abs + push_needle.len();
                    let rest = &body_text[after_push..];
                    let tokens: Vec<&str> = rest.split_whitespace().collect();
                    // tokens[0] = TYPE, tokens[1] = ALLOC, tokens[2] = local_N (the vec variable)
                    if tokens.len() >= 3 {
                        let var = tokens[2].to_string();
                        // Rewrite when: (1) looks like a local var, (2) extracted from self (`:= self.`
                        // for pure copy or `← self.` for monadic bind), (3) used in struct reconstruction.
                        let self_extract_assign = format!("let {var} := self.");
                        let self_extract_bind = format!("let {var} \u{2190} self.");
                        let used_in_struct = format!(":= {var}");
                        if var.starts_with("local_")
                            && (body_text.contains(&self_extract_assign)
                                || body_text.contains(&self_extract_bind))
                            && body_text.contains(&used_in_struct)
                        {
                            let old_str = "let _ \u{2190} (alloc.vec.Vec.push ".to_string();
                            let new_str = format!("let {var} \u{2190} (alloc.vec.Vec.push ");
                            rebindings.push((old_str, new_str));
                        }
                    }
                    search_from = abs + push_needle.len();
                }
                // Apply rebindings (each pair replaces the first occurrence of old_str)
                let mut changed = false;
                for (old_str, new_str) in rebindings {
                    if let Some(pos) = body_text.find(&old_str) {
                        body_text.replace_range(pos..pos + old_str.len(), &new_str);
                        changed = true;
                    }
                }
                changed
            } else {
                false
            };
            // pop_front desugar: Vec.pop_front returns (T × Vec T), not Option T.
            // The emitter wraps the result in Option.expect which type-errors in Lean.
            // Pattern (one line):
            //   let ELEM ← (core.option.Option.expect TYPE (← (alloc.vec.Vec.pop_front TYPE ALLOC VEC_VAR)) "MSG")
            // Target:
            //   let (ELEM, VEC_VAR) ← (alloc.vec.Vec.pop_front TYPE ALLOC VEC_VAR)
            // Both deliver and consume use this pattern exactly once each.
            let pop_front_fixed = if body_text.contains("core.option.Option.expect")
                && body_text.contains("alloc.vec.Vec.pop_front")
            {
                // Find the line containing the pattern.  We work line-by-line to keep the
                // parsing tractable; there is exactly one such line per affected function.
                let expect_needle = "core.option.Option.expect";
                let pf_needle = "alloc.vec.Vec.pop_front";
                let let_prefix = "let ";
                let arrow_marker = " \u{2190} "; // " ← "
                let mut changed = false;
                let mut lines: Vec<String> = body_text.lines().map(|l| l.to_string()).collect();
                for line in &mut lines {
                    if !line.contains(expect_needle) || !line.contains(pf_needle) {
                        continue;
                    }
                    // Extract ELEM variable: the identifier between "let " and " ← ("
                    let Some(let_pos) = line.find(let_prefix) else {
                        continue;
                    };
                    let after_let = &line[let_pos + let_prefix.len()..];
                    let Some(arrow_pos) = after_let.find(arrow_marker) else {
                        continue;
                    };
                    let elem_var = after_let[..arrow_pos].trim().to_string();
                    if elem_var.is_empty() {
                        continue;
                    }
                    // Extract VEC_VAR: last "local_NNN" token before the closing )) of pop_front.
                    // The pop_front call looks like: (alloc.vec.Vec.pop_front TYPE ALLOC VEC_VAR)
                    // followed by )) "MSG") to close Option.expect.
                    // Find the pop_front call position within the line.
                    let Some(pf_pos) = line.find(pf_needle) else {
                        continue;
                    };
                    // The pop_front call ends at the first ')' after VEC_VAR.
                    // Tokens after pf_needle: TYPE ALLOC VEC_VAR then ')'.
                    let after_pf = &line[pf_pos + pf_needle.len()..];
                    let tokens: Vec<&str> = after_pf.split_whitespace().collect();
                    // tokens[0]=TYPE, tokens[1]=ALLOC, tokens[2]=VEC_VAR (may have trailing ')')
                    if tokens.len() < 3 {
                        continue;
                    }
                    let vec_var = tokens[2].trim_end_matches(')').to_string();
                    if vec_var.is_empty() {
                        continue;
                    }
                    let indent_len = line.len() - line.trim_start().len();
                    let indent = &line[..indent_len];
                    let type_tok = tokens[0];
                    let alloc_tok = tokens[1];
                    if vec_var.contains('.') {
                        // self.FIELD → introduce a synthetic local, then update self.
                        // e.g. self.pending → let (ELEM, pending_new) ← pop_front ... self.pending
                        //                     let self := { self with pending := pending_new }
                        let field_name = vec_var.rsplit('.').next().unwrap_or("field");
                        let local_name = format!("{field_name}_new");
                        let new_line = format!(
                            "{}let ({elem_var}, {local_name}) \u{2190} ({pf_needle} {type_tok} {alloc_tok} {vec_var})",
                            indent,
                        );
                        let writeback = format!(
                            "{}let self := {{ self with {field_name} := {local_name} }}",
                            indent,
                        );
                        *line = format!("{new_line}\n{writeback}");
                        changed = true;
                    } else {
                        let new_line = format!(
                            "{}let ({elem_var}, {vec_var}) \u{2190} ({pf_needle} {type_tok} {alloc_tok} {vec_var})",
                            indent,
                        );
                        *line = new_line;
                        changed = true;
                    }
                    // Only one pop_front per function — stop after first match.
                    break;
                }
                if changed {
                    body_text = lines.join("\n");
                }
                changed
            } else if body_text.contains("alloc.vec.Vec.pop_front")
                && !body_text.contains("core.option.Option.expect")
            {
                let trimmed = body_text.trim();
                if trimmed.starts_with("(alloc.vec.Vec.pop_front ") && trimmed.ends_with(')') {
                    body_text = format!("let (pop_result_, _) ← {trimmed}\nok pop_result_");
                    true
                } else {
                    false
                }
            } else {
                false
            };
            // Check AFTER desugaring — only fires if desugar didn't handle some pattern
            let has_array_literal_byte =
                body_text.contains("#[0#u8,") || body_text.contains("#[0#u16,");
            // Early-return in inline blocks: FIXED by block-flattening in emit_stmt.
            // StyxStmt::Expr(Block { [If { Return(.Err) }] }) is now flattened into
            // do-notation with proper `return (.Err ...)` instead of dead `let _ := (.Err ...)`.
            // Detect &mut self methods with mutation patterns the emitter can't handle:
            // 1. Vec-mutating ops (push/insert/pop_front) return (T × Vec) pairs in Aeneas
            //    but the emitter discards the modified vec, causing type errors.
            // 2. Broken field-assign-as-expression: styx-rustc emits `self.field = val` as
            //    `(let _ := val; self.field)` instead of FieldAssign, producing dead reads.
            // Check for Vec mutation ops that return (T × Vec) pairs but the body
            // discards the modified vec (no writeback). Applies to both &mut self AND
            // non-mut methods that use functional-update patterns.
            let has_vec_mutation = body_text.contains("Vec.push")
                || body_text.contains("Vec.insert")
                || body_text.contains("Vec.pop_front")
                || body_text.contains("Vec.remove")
                || body_text.contains("Vec.retain")
                || body_text.contains("Vec.sort")
                || body_text.contains("Vec.extend");
            // TIER 1 &mut self methods have been desugared: desugar_mut_self stripped the
            // Ref wrapper from params[0].ty, so the bare StyxType (not Ref) is present.
            // We can detect this to avoid a false-positive on the "; self." pattern check:
            // legitimate delegation bodies may contain "self.method()" after a semicolon,
            // which is NOT the broken field-mutation pattern. TIER 2 functions (undesugared)
            // still have Ref in params[0].ty and need the "; self." guard.
            let is_mut_self_desugared = def.params.first().is_some_and(|p| {
                p.is_mut_self && !matches!(&p.ty, StyxType::Ref { is_mut: true, .. })
            });
            // Condition A: undesugared &mut self with Vec mutation or broken field mutation.
            // After desugar_mut_self strips Ref for TIER 1 and TIER 2, is_mut_self_desugared
            // is true for all properly-handled functions. The !is_mut_self_desugared guard here
            // prevents false positives for desugared TIER 2 functions (Vec mutations already have
            // correct Assign+FieldAssign writeback patterns generated by styx-rustc).
            // Condition B: discarded Vec mutation result — still blocks even for desugared functions.
            // Condition C: pop_front — always blocked (complex T×Vec return type).
            let has_discarded_vec_in_text = body_text.contains("let _ ← Vec.push")
                || body_text.contains("let _ ← Vec.insert")
                || body_text.contains("let _ ← Vec.remove")
                || body_text.contains("let _ ← Vec.retain")
                || body_text.contains("let _ ← Vec.sort")
                || body_text.contains("let _ ← Vec.extend")
                || body_text.contains("let _ ← (Vec.push")
                || body_text.contains("let _ ← (Vec.insert")
                || body_text.contains("let _ ← (Vec.remove")
                || body_text.contains("let _ ← (alloc.vec.Vec.push")
                || body_text.contains("let _ ← (alloc.vec.Vec.insert")
                // Bare Vec.push at statement level (not bound with let): loop accumulators
                || body_text.lines().any(|l| {
                    let t = l.trim();
                    t.starts_with("(alloc.vec.Vec.push ") || t.starts_with("alloc.vec.Vec.push ")
                });
            let has_mut_writeback_issue = (is_mut_self_method(def) && !is_mut_self_desugared && !binary_search_unit_fixed && !pop_front_fixed && (
                has_vec_mutation
                || body_text.contains("; self.") // broken field mutation
            )) || (!loop_vec_accum_fixed && !binary_search_unit_fixed && has_discarded_vec_in_text)
                || (!pop_front_fixed && body_text.contains("Vec.pop_front"));
            // --- Quick-win text passes (2026-04-16 EMPACO batch) ---

            // (A) Pure struct field accessors: return field type directly, not Result.
            // `← Foo.field x` → `:= Foo.field x` for known pure projections.
            // Three patterns covered:
            //   1. `← Foo.field`         (plain, no paren around arg list)
            //   2. `← (Foo.field`        (assignment with parens around call)
            //   3. `(← (Foo.field`       (nested in expression, full monadic)
            let pure_field_accessors = [
                "types.capability.Capability.parent",
            ];
            let mut pure_field_accessors_fixed = false;
            for accessor in &pure_field_accessors {
                // Pattern 3 first (most specific): `(← (Foo.field` → `(Foo.field`
                let monadic_paren = format!("(← ({accessor}");
                let pure_paren = format!("({accessor}");
                if body_text.contains(&monadic_paren) {
                    body_text = body_text.replace(&monadic_paren, &pure_paren);
                    pure_field_accessors_fixed = true;
                }
                // Pattern 2: `← (Foo.field` → `:= (Foo.field`
                let monadic_wrap = format!("← ({accessor}");
                let pure_wrap = format!(":= ({accessor}");
                if body_text.contains(&monadic_wrap) {
                    body_text = body_text.replace(&monadic_wrap, &pure_wrap);
                    pure_field_accessors_fixed = true;
                }
                // Pattern 1: `← Foo.field` → `:= Foo.field`
                let monadic = format!("← {accessor}");
                let pure = format!(":= {accessor}");
                if body_text.contains(&monadic) {
                    body_text = body_text.replace(&monadic, &pure);
                    pure_field_accessors_fixed = true;
                }
            }

            // (B) Arc.new identity erasure: Arc<T>=T in Lean, so Arc.new is identity.
            // `(← (alloc.sync.Arc.new X))` → `X` for single-arg case.
            // PolicyState.new body: `ok { decide := (← (alloc.sync.Arc.new decide)) }`
            if body_text.contains("alloc.sync.Arc.new") {
                // Simple single-arg pattern: (← (alloc.sync.Arc.new ARGNAME))
                let re_pattern = "(← (alloc.sync.Arc.new ";
                while let Some(start) = body_text.find(re_pattern) {
                    let arg_start = start + re_pattern.len();
                    // Find the arg name (up to the closing parens))
                    if let Some(rel_end) = body_text[arg_start..].find("))") {
                        let arg = body_text[arg_start..arg_start + rel_end].to_string();
                        let full_end = arg_start + rel_end + 2; // past "))"
                        body_text.replace_range(start..full_end, &arg);
                    } else {
                        break;
                    }
                }
            }

            // (C) Const generic PAGE_SIZE normalization: styx-rustc extracts 0, not 4096.
            // Body may use `Array U8 4096#usize` but Types.lean has `Array U8 0#usize`.
            let page_size_normalized = body_text.contains("Array U8 4096#usize");
            body_text = body_text.replace("Array U8 4096#usize", "Array U8 0#usize");

            // (D) MetaState.free_mut: qualify bare `.Freed` enum ctor.
            if body_text.contains("(.Freed)") && !body_text.contains("ResourceStatus.Freed") {
                body_text = body_text.replace("(.Freed)", "(state.memory.ResourceStatus.Freed)");
            }

            // (E) held_caps_ref: method returning Result (Vec U64) used as Slice arg to
            // core.slice.iter. Fix: bind with ← and use IntoIteratorSharedAVec.into_iter instead
            // of core.slice.iter (Vec != Slice).
            // Affects: execute_cap_call, execute_cap_call_mut (issue #309).
            if body_text.contains("core.slice.iter U64 (state.plugin.PluginState.held_caps_ref ") {
                body_text = body_text.replace(
                    "core.slice.iter U64 (state.plugin.PluginState.held_caps_ref ",
                    "alloc.vec.IntoIteratorSharedAVecSharedATIter.into_iter U64 Global (← (state.plugin.PluginState.held_caps_ref ",
                );
                // Close the extra open paren we introduced for the ← binding.
                // Pattern was: `held_caps_ref local_48))` — now needs an extra `)`.
                body_text = body_text.replace(
                    "PluginState.held_caps_ref local_48))",
                    "PluginState.held_caps_ref local_48)))",
                );
            }

            // (F) PartialEq.eq on Action type: generic call cannot resolve impl since
            // PartialEqActionAction is a `def` not an `instance`.
            // Fix: route directly to the concrete eq function.
            // Affects: execute_host_call, execute_host_call_mut (issue #309).
            if body_text.contains("core.cmp.PartialEq.eq types.policy.Action types.policy.Action ") {
                body_text = body_text.replace(
                    "core.cmp.PartialEq.eq types.policy.Action types.policy.Action ",
                    "types.policy.PartialEqAction.eq ",
                );
            }

            // (F1) Strip spurious outer ← wrapping `!` negation of a Bool.
            // Pattern: `if (← (!(← expr)))` → `if (!(← expr))`.
            // The inner `(← expr)` binds Result Bool → Bool; `!bool` is Bool (not Result Bool),
            // so the outer `← ` would cause a type error.
            // Affects: execute_host_call, execute_host_call_mut (issue #309).
            if body_text.contains("if (\u{2190} (!(") {
                // `(← ` is 5 bytes; search for the specific pattern.
                let arrow_not_pattern = "if (\u{2190} (!("; // `if (← (!(`
                let _replacement_prefix = "if (!(";           // `if (!(`
                let mut from = 0usize;
                loop {
                    let Some(rel) = body_text[from..].find(arrow_not_pattern) else { break };
                    let abs = from + rel;
                    // abs points to `if (← (!(`
                    // We need to find the matching `)` for the outer `(← ...)`
                    // The outer `(` is at abs + "if ".len() = abs + 3
                    let outer_open = abs + 3; // position of `(` after `if `
                    let Some(outer_close) = match_paren_bytes(body_text.as_bytes(), outer_open) else {
                        from = abs + arrow_not_pattern.len();
                        continue;
                    };
                    // The inner `(!( ... )` starts at outer_open + 5 (skip `(← `)
                    // We want to extract from `(!` to outer_close - 1 (one `)` less)
                    // i.e., we want `(!(← expr))` which is outer_open+5..outer_close (exclusive)
                    let inner_start = outer_open + 5; // skip `(← `, 5 bytes
                    let inner_expr = body_text[inner_start..outer_close].to_string();
                    // Build replacement: `if (inner_expr`
                    // outer was `if (← (!(← expr)))`, inner_expr is `(!(← expr))`
                    let replacement = format!("if {}", inner_expr);
                    // Replace: `if (← (!(← expr)))` with `if (!(← expr))`
                    // Span: from abs to outer_close (inclusive)
                    body_text.replace_range(abs..=outer_close, &replacement);
                    from = abs + replacement.len();
                }
            }

            // (F2) Strip spurious ← wraps from pure struct field accessors that have no
            // Lean function declaration (field accessors that clash with auto-generated ones).
            // Pattern: `(← (ACCESSOR ARG))` → `(ACCESSOR ARG)`.
            // Uses paren matching to preserve correct balance.
            // Note: `←` is a 3-byte UTF-8 sequence; `(← ` is 5 bytes total.
            // Affects: execute_host_call, execute_host_call_mut (issue #309).
            {
                // Each entry: (outer_prefix_to_search, byte_len_of_arrow_bind_prefix)
                // The arrow bind prefix is `(← ` which is 5 bytes: `(` + 3-byte_← + space.
                const ARROW_BIND_LEN: usize = 5; // `(← ` in bytes
                let accessor_prefixes: &[&str] = &[
                    "(← (types.policy.Action.subject ",
                    "(← (types.policy.Action.target ",
                    "(← (step.host_call.HostCall.caller ",
                ];
                for prefix in accessor_prefixes {
                    let mut from = 0usize;
                    loop {
                        let Some(rel) = body_text[from..].find(prefix) else { break };
                        let abs = from + rel;
                        // abs points to outer `(` of `(← (ACCESSOR ...))`.
                        let Some(outer_close) = match_paren_bytes(body_text.as_bytes(), abs) else {
                            from = abs + prefix.len();
                            continue;
                        };
                        // Inner `(ACCESSOR` starts at abs + ARROW_BIND_LEN (skip `(← `).
                        let inner_open = abs + ARROW_BIND_LEN;
                        let Some(inner_close) = match_paren_bytes(body_text.as_bytes(), inner_open) else {
                            from = abs + prefix.len();
                            continue;
                        };
                        // Extract inner expression: `(ACCESSOR ARG)`
                        let inner_expr = body_text[inner_open..=inner_close].to_string();
                        // Replace outer `(← (ACCESSOR ARG))` with `(ACCESSOR ARG)`
                        body_text.replace_range(abs..=outer_close, &inner_expr);
                        from = abs + inner_expr.len();
                    }
                }
            }

            // (G) kernel_mut used without ← inside alloc_cap_id call.
            // state.kernel.KernelState.alloc_cap_id takes KernelState but kernel_mut returns Result KernelState.
            // Fix: wrap kernel_mut call with (← ...).
            // Affects: kernel::Kernel::delegate_cap (issue #309).
            if body_text.contains("state.kernel.KernelState.alloc_cap_id (state.state.State.kernel_mut ") {
                body_text = body_text.replace(
                    "state.kernel.KernelState.alloc_cap_id (state.state.State.kernel_mut ",
                    "state.kernel.KernelState.alloc_cap_id (← (state.state.State.kernel_mut ",
                );
                // Close the extra open paren for (←).
                // Pattern: `kernel_mut self.state))` — needs one more `)`.
                body_text = body_text.replace(
                    "State.kernel_mut self.state))",
                    "State.kernel_mut self.state)))",
                );
            }

            // (H) hmac_key used without ← inside seal_payload call.
            // crypto.seal_payload takes Key but hmac_key returns Result Key.
            // Fix: wrap hmac_key call with (← ...).
            // Affects: kernel::Kernel::delegate_cap (issue #309).
            if body_text.contains("crypto.seal_payload (state.kernel.KernelState.hmac_key ") {
                body_text = body_text.replace(
                    "crypto.seal_payload (state.kernel.KernelState.hmac_key ",
                    "crypto.seal_payload (← (state.kernel.KernelState.hmac_key ",
                );
                // Close the extra open paren for (←).
                // Pattern: `hmac_key (state.state.State.kernel self.state))` — needs one more `)`.
                body_text = body_text.replace(
                    "KernelState.hmac_key (state.state.State.kernel self.state))",
                    "KernelState.hmac_key (state.state.State.kernel self.state)))",
                );
            }

            // (I) Option.cloned missing explicit type arg.
            // std.option.Option.cloned takes (T : Type) as explicit arg. Without it Lean cannot
            // elaborate the call. Add the Capability type arg for the host_call_atomic use-site.
            // Affects: step::Step::host_call_atomic (issue #309).
            if body_text.contains("(std.option.Option.cloned (← (state.state.State.get_cap ") {
                body_text = body_text.replace(
                    "(std.option.Option.cloned (← (state.state.State.get_cap ",
                    "(std.option.Option.cloned types.capability.Capability (← (state.state.State.get_cap ",
                );
            }

            // has_adt_partial_eq guard REMOVED (2026-04-15)
            let has_type_issues = (!array_literal_fixed && body_text.contains("#[0#u64,")) // array literal with wrong element type
                || body_text.contains("STYX_Unsupported") // unsupported types
                // early return inside a nested expression: Err(..) in sub-block not lifted to do-level
                || body_text.contains("let _ := (.Err")
                // Slice/Array guard removed — slice_fixed handles as_bytes via Array.to_slice
                || ret_usize_body_u64 // scalar mismatch
                || has_uscalar_pat // pattern match on UScalar literals
                || (!array_literal_fixed && has_array_literal_byte) // Aeneas Array literal
                // has_inline_early_return guard no longer needed — the block-flattening
                // in emit_stmt now handles early returns by hoisting If stmts into do-notation
                // Result.some guard removed — pattern no longer generated
                || has_mut_writeback_issue // &mut self + Vec mutation
                // Constants are no longer wrapped with ← (is_pure_constant_path fix)
                // IndexVec: desugar_indexvec handles let-binding ← and match-arm ← for most cases.
                // IndexMutVec is allowed only when desugar_index_mut_vec proves all mutable-index
                // occurrences are in supported bound shapes. Unsupported shapes stay opaque.
                || (!indexvec_fixed && body_text.contains("IndexVec.index"))
                || (!index_mut_vec_fixed
                    && (body_text.contains("IndexMutVec.index_mut")
                        || body_text.contains("Vec.index_mut_usize")))
                // is_some_and: now declared in AeneasStdlib + mapped in map_std_callee — guard removed
                || body_text.contains("4096#usize") // const generic PAGE_SIZE mismatch (extracted as 0)
                // Result.map_err guard removed — desugared to monadic match by desugar_map_err
                // State.empty, State.insert_plugin, MetaState.insert_freed_addr,
                // PluginState.insert_cap_sorted/remove_cap_sorted, Rights.complement:
                // ALL now declared (FunsExternal opaque or Funs.lean transparent).
                // Guards removed — these are valid callee targets.
                // Result.Permit/Break/none guards removed — patterns no longer generated
                || (body_text.contains("if (") && (
                    body_text.contains("if (types.rights.Rights.is_empty") // Result Bool in if without ←
                    || body_text.contains("if (alloc.vec.Vec.is_empty") // Result Bool in if without ←
                    || (!is_permit_fixed && body_text.contains("if (types.policy.PolicyDecision.is_permit")) // Result Bool in if without ←
                    || (body_text.contains("any_valid_targeting") && !body_text.contains("(← (state.kernel.RevocationState.any_valid_targeting")) // only if not ←-bound
                ))
                || (!option_is_some_fixed && body_text.contains("Option.is_some Usize (state.")) // is_some on Result (missing ←)
                || (!is_none_fixed && body_text.contains("Option.is_none") && body_text.contains("RevocationState.get (state.kernel.KernelState")) // is_none on Result arg (missing ←)
                || body_text.contains("PolicyState.new (fun") // closure type mismatch
                // MetaState.get_status: now transparent — guard only when NOT ←-bound
                || (body_text.contains("MetaState.get_status") && !body_text.contains("(← (state.memory.MetaState.get_status"))
                // find_oob_read/write: guard only when NOT already ←-bound.
                // Two bind forms: old "(← (step.host_call.HostCall.find_oob_read" (paren-wrapped)
                // and new "← step.host_call.HostCall.find_oob_read" (from P3 if-let restructure).
                || (body_text.contains("find_oob_read")
                    && !body_text.contains("(← (step.host_call.HostCall.find_oob_read")
                    && !body_text.contains("(← (step.plugin_internal.PluginInternal.find_oob_read")
                    && !body_text.contains("\u{2190} step.host_call.HostCall.find_oob_read")
                    && !body_text.contains("\u{2190} step.plugin_internal.PluginInternal.find_oob_read"))
                || (body_text.contains("find_oob_write")
                    && !body_text.contains("(← (step.host_call.HostCall.find_oob_write")
                    && !body_text.contains("(← (step.plugin_internal.PluginInternal.find_oob_write")
                    && !body_text.contains("\u{2190} step.host_call.HostCall.find_oob_write")
                    && !body_text.contains("\u{2190} step.plugin_internal.PluginInternal.find_oob_write"))
                || body_text.contains("TryResultResultInfallible") // ? operator: match arms have different types (ControlFlow.Break/Continue)
                || body_text.contains("FromResidualResultResultInfallible") // same
                || (!eval_in_match_fixed && body_text.contains("match (types.policy.PolicyState.eval")) // eval returns Result, used in match without ←
                // Capability.parent, .Read guards removed — patterns no longer generated
                // revocation_mut guard REMOVED: KernelState.revocation_mut is now transparent in Funs.lean
                // get_actor_mut / get_plugin_mut: guards removed (2026-04-13).
                // The Option-condition emit_stmt case now handles `if let Some(x) = get_actor_mut(...)`
                // by emitting `match (← get_actor_mut ...) with | .none => ok () | .some x => do ...`
                || (!verify_seal_fixed && body_text.contains("crypto.verify_seal")) // returns Result Bool, used in if/match
                // dispatch_cap_delegate/revoke/set_plugin_level/set_resource_level/tick guards removed
                // — desugar_monadic_dispatch strips ok(match...) so these calls are valid at do-level
                // Capability.payload guard removed — declared in Funs.lean (transparent)
                // Capability.signature/epoch: structure field projections — always valid
                // (Lean auto-generates projection functions for structure fields)
                // || body_text.contains("Capability.signature cap") // REMOVED: pure projection
                // || body_text.contains("Capability.epoch cap") // REMOVED: pure projection
                // Capability.parent: Option U64 field — guard only when used directly in if()
                // without ← binding. `let x ← Capability.parent; if let .some y := x` is fine.
                || (body_text.contains("if (Capability.parent ") || body_text.contains("if (types.capability.Capability.parent "))
                // execute_* guards removed — desugar_monadic_dispatch strips ok(match...) so
                // monadic callees are valid at do-block level. Opaque callees have FunsExternal decls.
                || (!revoc_get_fixed && body_text.contains("match (state.kernel.RevocationState.get")) // Result in match without ←
                || (!node_state_fixed && body_text.contains(".get_node_state self")) // returns Result, used without ←
                // Capability.payload cap guard: only catch bare calls (without ←)
                || (body_text.contains("Capability.payload cap") && !body_text.contains("← (types.capability.Capability.payload"))
                || (!validate_fixed && body_text.contains(".validate auth") && !body_text.contains("(← (step.authorization.Authorized.validate"))
                // std.cmp.PartialOrd guard removed — in unknown_fns list
                // core.slice.binary_search: declared in AeneasStdlib (returns Result (core.result.Result Usize Usize))
                // if-condition desugar (desugar_binary_search_if) converts to match Ok/Err.
                || (!binary_search_if_fixed && body_text.contains("if (← (core.slice.binary_search"))
                // core.num.checked_add guard removed — in unknown_fns list
                // KeyState.rotated guard removed — it's transparent in Funs.lean (calls opaque rotate via ←)
                // core.result.Result match: | .Ok / | .Err collide with open Aeneas.Std Result
                || body_text.contains("| .Ok ") || body_text.contains("| .Err ")
                // monadic bind inside match inside ok: ok (match ... (← ...) ...)
                // Exception: ok (match (← DISCR) with | PURE ...) is valid (Lean lifts from discriminee)
                || (body_text.contains("ok (match") && body_text.contains("(←")
                    && !eval_in_match_fixed)
                // Action.new returns Result (core.result.Result Action PolicyError).
                // It is valid in StepError-returning functions only after Result.map_err
                // has been desugared to an explicit PolicyError -> StepError match.
                || action_new_needs_step_error_mapping(&body_text, &ret_ty)
                // Vec::with_capacity(n): Vec.new(cap) → Vec.new T (see vec_new_capacity_fixed)
                || (!vec_new_capacity_fixed && (body_text.contains("Vec.new (UScalar.cast")
                    || body_text.contains("Vec.new (←")));
            // STYX_DEBUG_BODY=fn_name: dump body_text for specific function to stderr
            if let Ok(dbg_fn) = std::env::var("STYX_DEBUG_BODY")
                && !dbg_fn.is_empty() && lean_name.contains(&dbg_fn) {
                    eprintln!("BODY[{}]:\n{}\n---", lean_name, body_text);
                }
            let force_opaque = is_force_opaque(&def.rust_path);
            if body_text.contains("sorry")
                || contains_unknown_namespace(&body_text)
                || has_type_issues
                || force_opaque
            {
                let reason = if body_text.contains("sorry") {
                    "sorry"
                } else if force_opaque {
                    "body type errors (force opaque)"
                } else if has_type_issues {
                    "type issues"
                } else {
                    "external crate calls"
                };
                // STYX_DEBUG_OPAQUE: print reason + blocker to stderr for diagnostics
                if std::env::var("STYX_DEBUG_OPAQUE").is_ok() {
                    let detail = if reason == "type issues" {
                        // Show which specific type_issues pattern matched
                        let mut blockers = Vec::new();
                        if body_text.contains("STYX_Unsupported") {
                            blockers.push("unsupported_ty");
                        }
                        if body_text.contains("IndexVec.index")
                            || body_text.contains("IndexMutVec.index_mut")
                            || body_text.contains("Vec.index_mut_usize")
                        {
                            blockers.push("indexvec");
                        }
                        if body_text.contains("let _ := (.Err") {
                            blockers.push("early_return");
                        }
                        if body_text.contains("TryResultResultInfallible")
                            || body_text.contains("FromResidualResultResultInfallible")
                        {
                            blockers.push("try_operator");
                        }
                        if has_mut_writeback_issue {
                            blockers.push("mut_writeback");
                        }
                        if ret_usize_body_u64 {
                            blockers.push("usize_u64");
                        }
                        if has_uscalar_pat {
                            blockers.push("uscalar_pat");
                        }
                        if has_array_literal_byte {
                            blockers.push("array_literal");
                        }
                        if body_text.contains("Result.some") {
                            blockers.push("result_some");
                        }
                        if body_text.contains("is_some_and") {
                            blockers.push("is_some_and");
                        }
                        if body_text.contains(".KernelState {") {
                            blockers.push("constructor_syntax");
                        }
                        if body_text.contains("Result.map_err") {
                            blockers.push("map_err");
                            if std::env::var("STYX_DEBUG_MAP_ERR").is_ok() {
                                let snippet: String = body_text.chars().take(800).collect();
                                use std::io::Write;
                                let mut f = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open("/tmp/styx_map_err_bodies.txt")
                                    .unwrap();
                                writeln!(f, "=== {} ===\n{}\n", lean_name, snippet).ok();
                            }
                        }
                        if body_text.contains("revocation_mut") {
                            blockers.push("revocation_mut");
                        }
                        // Dotted ctor check: bare `.Read)` (not qualified like `Right.Read)`)
                        // indicates an unresolved enum constructor that Lean cannot infer.
                        // Qualified forms like `types.rights.Right.Read)` are fine.
                        {
                            let has_bare_dotted_ctor = |ctor: &str| -> bool {
                                let pattern = format!(".{})", ctor);
                                let singleton_pat = format!("singleton (.{})", ctor);
                                if !body_text.contains(&pattern) || body_text.contains(&singleton_pat) {
                                    return false;
                                }
                                // Check each occurrence: is the char before `.` a space, `(`, or start?
                                // If preceded by a word char, it's qualified (e.g. Right.Read) — not bare.
                                for (pos, _) in body_text.match_indices(&pattern) {
                                    if pos == 0 { return true; }
                                    let prev = body_text.as_bytes()[pos - 1];
                                    if prev == b' ' || prev == b'(' || prev == b'\n' || prev == b'\t' {
                                        return true;
                                    }
                                }
                                false
                            };
                            if has_bare_dotted_ctor("Read") || has_bare_dotted_ctor("Write")
                                || has_bare_dotted_ctor("Delete") {
                                blockers.push("dotted_ctor");
                            }
                        }
                        if body_text.contains("get_actor ") || body_text.contains("get_actor_mut") {
                            blockers.push("calls_opaque_fn");
                        }
                        if body_text.contains("deliver_mut") || body_text.contains("unblock_mut") {
                            blockers.push("calls_opaque_fn");
                        }
                        if body_text.contains("get_workflow ") {
                            blockers.push("calls_opaque_fn");
                        }
                        if body_text.contains("ok (match") && body_text.contains("(←") {
                            blockers.push("monadic_in_match");
                        }
                        if body_text.contains("state.state.State.empty")
                            || body_text.contains("state.state.State.insert_plugin")
                            || body_text.contains("MetaState.insert_freed_addr")
                            || body_text.contains("PluginState.insert_cap_sorted")
                            || body_text.contains("PluginState.remove_cap_sorted")
                            || body_text.contains("Rights.complement")
                        {
                            blockers.push("nonexistent_fn");
                        }
                        if body_text.contains("Result.Permit")
                            || body_text.contains("Result.Break")
                            || body_text.contains("Result.none")
                        {
                            blockers.push("nonexistent_variant");
                        }
                        if body_text.contains("if (types.rights.Rights.is_empty")
                            || body_text.contains("if (alloc.vec.Vec.is_empty")
                            || body_text.contains(".is_permit")
                            || body_text.contains("any_valid_targeting")
                        {
                            blockers.push("result_in_if");
                        }
                        if body_text.contains("crypto.verify_seal") {
                            blockers.push("crypto_result_in_if");
                        }
                        if body_text.contains("dispatch_cap_delegate")
                            || body_text.contains("dispatch_cap_revoke")
                            || body_text.contains("dispatch_set_plugin_level")
                            || body_text.contains("dispatch_set_resource_level")
                            || body_text.contains("dispatch_tick")
                        {
                            blockers.push("dispatch_result");
                        }
                        if body_text.contains("cap.payload")
                            || body_text.contains("Capability.payload cap")
                        {
                            blockers.push("payload_result");
                        }
                        if body_text.contains("execute_cap_call")
                            || body_text.contains("execute_cap_send")
                            || body_text.contains("execute_kernel_alloc")
                            || body_text.contains("execute_mem_free")
                            || body_text.contains("execute_cap_revoke")
                            || body_text.contains("execute_declassify")
                            || body_text.contains("execute_plugin_internal")
                            || body_text.contains("execute_host_call")
                            || body_text.contains("execute_kernel_internal")
                            || body_text.contains("execute_thread_switch")
                        {
                            blockers.push("execute_opaque");
                        }
                        if body_text.contains("Option.is_some Usize (state.") {
                            blockers.push("option_is_some");
                        }
                        if body_text.contains("PolicyState.new (fun") {
                            blockers.push("closure_type");
                        }
                        if body_text.contains("MetaState.get_status")
                            || body_text.contains("find_oob_read")
                            || body_text.contains("find_oob_write")
                        {
                            blockers.push("result_as_pure");
                        }
                        if body_text.contains("match (types.policy.PolicyState.eval")
                            || body_text.contains("match (state.kernel.RevocationState.get")
                        {
                            blockers.push("result_in_match");
                        }
                        if body_text.contains(".get_node_state self")
                            || body_text.contains(".validate auth")
                        {
                            blockers.push("result_without_bind");
                        }
                        if body_text.contains("std.cmp.PartialOrd") {
                            blockers.push("partial_ord");
                        }
                        if action_new_needs_step_error_mapping(&body_text, &ret_ty) {
                            blockers.push("action_new_policy_error");
                        }
                        if !binary_search_unit_fixed && body_text.contains("core.slice.binary_search ") {
                            blockers.push("binary_search");
                        }
                        if body_text.contains("core.num.checked_add")
                            || body_text.contains("KeyState.rotated")
                        {
                            blockers.push("checked_add");
                        }
                        if body_text.contains("#[0#u64,") {
                            blockers.push("array_u64");
                        }
                        if body_text.contains("; self.") && is_mut_self_method(def) {
                            blockers.push("field_assign_expr");
                        }
                        if blockers.is_empty() {
                            blockers.push("UNKNOWN");
                        }
                        let tag = format!("type_issues({})", blockers.join("+"));
                        if blockers.contains(&"UNKNOWN") {
                            let snippet: String = body_text.chars().take(4000).collect();
                            format!("{tag}|body={snippet}")
                        } else {
                            tag
                        }
                    } else if reason == "external crate calls" {
                        let body_snippet: String = body_text.chars().take(2000).collect();
                        if std::env::var("STYX_DEBUG_EXTCRATE").is_ok() {
                            use std::io::Write;
                            let mut f = std::fs::OpenOptions::new()
                                .create(true)
                                .append(true)
                                .open("/tmp/styx_extcrate_bodies.txt")
                                .unwrap();
                            writeln!(f, "=== {} ===\n{}\n", lean_name, body_snippet).ok();
                        }
                        reason.to_string()
                    } else if reason == "body type errors (force opaque)" {
                        if std::env::var("STYX_DUMP_FORCE_OPAQUE").is_ok() {
                            let snippet: String = body_text.chars().take(4000).collect();
                            format!("{reason}|body={snippet}")
                        } else {
                            reason.to_string()
                        }
                    } else {
                        reason.to_string()
                    };
                    eprintln!("OPAQUE|{}|{}", lean_name, detail);
                }

                w.writeln(format!("-- {reason} in body: declared in FunsExternal"));
                made_opaque = true;
            } else {
                w.writeln(format!("@[rust_fun \"{}\"]", def.rust_path));
                w.writeln(format!(
                    "def {lean_name}{generics}{params_str} : Result {ret_ty} := do"
                ));
                w.indent();
                if partial_eq_fixed
                    || map_err_fixed
                    || try_op_fixed
                    || slice_fixed
                    || option_is_some_fixed
                    || node_state_fixed
                    || validate_fixed
                    || is_none_fixed
                    || eval_in_match_fixed
                    || is_permit_fixed
                    || dispatch_fixed
                    || indexvec_fixed
                    || pure_arms_fixed
                    || rights_array_fixed
                    || uscalar_match_fixed
                    || verify_cap_seal_fixed
                    || array_literal_fixed
                    || binary_search_fixed
                    || find_index_fixed
                    || step_error_fixed
                    || meta_free_fixed
                    || verify_seal_fixed
                    || revoc_get_fixed
                    || err_subblock_fixed
                    || paren_removal_fixed
                    || get_mut_bind_fixed
                    || addr_in_bounds_fixed
                    || vec_push_rebound
                    || pop_front_fixed
                    || page_size_normalized
                    || index_mut_vec_fixed
                    || pure_field_accessors_fixed
                    || binary_search_if_fixed
                    || binary_search_unit_fixed
                    || vec_new_capacity_fixed
                    || loop_vec_accum_fixed
                {
                    // Write the text-transformed body directly
                    for line in body_text.lines() {
                        w.writeln(line);
                    }
                } else {
                    // Re-emit from IR (body_text doesn't have proper indentation)
                    emit_body(w, body, types);
                }
                w.dedent();
                // Termination annotation for recursive functions with U64 fuel parameter.
                // Lean 4 can't automatically determine that `fuel - 1` decreases the measure
                // for U64 scalars, so we emit `termination_by fuel.val` + `decreasing_by scalar_tac`.
                // Recursive functions with U64 fuel use `partial_fixpoint` (the Aeneas-standard
                // pattern). Lean 4's well-founded termination checker can't automatically derive
                // a decreasing measure for monadic `← (fuel - 1#u64)` binds, but `partial_fixpoint`
                // defers termination and works for any `Result`-returning recursive function.
                let has_fuel_u64 = params.contains(&"(fuel : U64)".to_string());
                let is_self_recursive = body_text.contains(&format!("{lean_name} "));
                if has_fuel_u64 && is_self_recursive {
                    w.writeln("partial_fixpoint");
                }
            }
        }
        None => {
            // No body — declared in FunsExternal
            w.writeln(format!(
                "-- no body: declared in FunsExternal ({lean_name})"
            ));
            made_opaque = true;
        }
    }
    if emit_checks {
        w.writeln(format!("#check {lean_name}"));
    }
    w.newline();
    made_opaque
}
