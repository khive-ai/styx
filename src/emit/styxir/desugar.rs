/// Desugar `IndexVec.index` calls into proper monadic form.
///
/// `IndexVec.index` returns `Result T` but is often emitted in pure contexts:
/// - `let x := (IndexVec.index ...)` — needs `←`
/// - Inside match arms as argument to pure functions — needs `←`
/// - Match discriminees calling monadic functions (node_index) — needs `←`
///
/// Also fixes `.none` match arms that need `ok` wrapping when sibling `.some`
/// arms return monadic values.
pub(crate) fn desugar_indexvec(body: &mut String) -> bool {
    if !body.contains("IndexVec.index") {
        return false;
    }
    let mut changed = false;

    // A. Add ← to match discriminees that are monadic calls (node_index)
    let nd = "(state.workflow.WorkflowDef.node_index";
    let nd_bound = "(← (state.workflow.WorkflowDef.node_index";
    if body.contains(nd) && !body.contains(nd_bound) {
        changed |= insert_bind_before(body, "state.workflow.WorkflowDef.node_index");
    }

    // B. Fix let bindings: let x := (IndexVec.index) → let x ← (IndexVec.index)
    let let_pat = ":= (alloc.vec.IndexVec.index ";
    while body.contains(let_pat) {
        *body = body.replacen(let_pat, "← (alloc.vec.IndexVec.index ", 1);
        changed = true;
    }

    // C. Add ← before IndexVec.index when used as argument to another function.
    //    Skip when at top level of a match arm (preceded by "=> ") or inside a
    //    `fun` closure (Lean cannot lift ← over binders).
    let iv_marker = "(alloc.vec.IndexVec.index ";
    let mut search_from = 0;
    loop {
        let search_body = &body[search_from..];
        let Some(rel_pos) = search_body.find(iv_marker) else {
            break;
        };
        let abs_pos = search_from + rel_pos;

        // Already bound?
        if abs_pos >= 4 && body[..abs_pos].ends_with("(← ") {
            // Count as fixed regardless of closure context.
            // When IndexVec.index is already (← (IndexVec.index ...)) inside a `fun` closure,
            // the Closure emitter (line ~5195) guarantees the `fun` body is wrapped in `do`:
            //   `(fun params => do ... (← (IndexVec.index ...)) ...)`
            // which is valid Lean 4. Setting changed=true here suppresses the opaque guard
            // for functions like plugins_low_equiv / resources_low_equiv / preserves_isolation
            // where Iterator::all takes a closure whose body accesses IndexVec via ←.
            changed = true; // Already properly bound — count as fixed.
            search_from = abs_pos + iv_marker.len();
            continue;
        }

        let before = &body[..abs_pos];

        // Check: inside a `fun` closure WITHOUT a `do` body? Count unmatched `fun` vs `)` to detect.
        // `(fun params => expr)` — `←` is INVALID (Lean cannot lift ← over binders).
        // `(fun params => do expr)` — `←` IS valid (the `do` block makes it monadic).
        // The Closure emitter always emits `(fun params => do ...)` when the body has `←`,
        // so we only need to skip when the fun body does NOT have `do`.
        let in_closure_without_do = {
            // Find the last `fun ` before this position that isn't closed.
            // Walk backwards through ASCII-safe bytes (parens are always single-byte).
            let mut depth = 0i32;
            let before_bytes = before.as_bytes();
            let mut i = before.len();
            let mut fun_pos: Option<usize> = None;
            while i > 4 {
                i -= 1;
                match before_bytes[i] {
                    b')' => depth += 1,
                    b'(' => {
                        if depth > 0 {
                            depth -= 1;
                        }
                        // Check if this open-paren starts "(fun " — must be on char boundary
                        if depth == 0
                            && i + 5 <= before.len()
                            && before.is_char_boundary(i)
                            && before.is_char_boundary(i + 5)
                            && &before[i..i + 5] == "(fun "
                        {
                            fun_pos = Some(i);
                            break;
                        }
                    }
                    _ => {}
                }
            }
            if let Some(fp) = fun_pos {
                // Found enclosing `(fun `. Check if the fun body is a `do` block.
                // Pattern: `(fun params => do ...)` — search for `=> do` after the `(fun`.
                // We look from the `(fun` position forward to the IndexVec occurrence.
                let fun_to_here = &before[fp..];
                // `=> do ` or `=> do\n` indicates the fun body is a do-block.
                let has_do_body = fun_to_here.contains("=> do ") || fun_to_here.contains("=> do\n");
                !has_do_body // in_closure_without_do = true only when no `do` body
            } else {
                false // Not inside any fun closure
            }
        };
        if in_closure_without_do {
            search_from = abs_pos + iv_marker.len();
            continue;
        }

        // Check context: is this a direct match arm result?
        let before_trimmed = before.trim_end();
        let is_direct_arm = before_trimmed.ends_with("=>");
        if is_direct_arm {
            // Exception: if immediately followed by tuple projection (.1 or .2 after close paren),
            // we CAN wrap with ← — Lean 4 allows (← (IndexVec.index ...)).2 in match arms.
            let end_opt = match_paren_bytes(body.as_bytes(), abs_pos);
            let has_proj = end_opt
                .map(|e| {
                    let after = &body[e + 1..];
                    after.starts_with(".1") || after.starts_with(".2")
                })
                .unwrap_or(false);
            if !has_proj {
                search_from = abs_pos + iv_marker.len();
                continue;
            }
            // Fall through to wrap — the close paren will be found again below.
        }

        // Find end of IndexVec.index call via paren matching
        let Some(end) = match_paren_bytes(body.as_bytes(), abs_pos) else {
            search_from = abs_pos + iv_marker.len();
            continue;
        };

        // Wrap: (IndexVec.index ...) → (← (IndexVec.index ...))
        let iv_call = body[abs_pos..=end].to_string();
        let replacement = format!("(← {})", iv_call);
        body.replace_range(abs_pos..=end, &replacement);
        search_from = abs_pos + replacement.len();
        changed = true;
    }

    // D. Fix pure .none match arms when sibling .some arm uses IndexVec.index.
    //    These need ok() wrapping to match the monadic Result type of .some arms.
    if changed {
        for (old, new_val) in &[
            ("| .none => (.", "| .none => ok (."),
            ("| .none => true)", "| .none => ok true)"),
            ("| .none => true\n", "| .none => ok true\n"),
            ("| .none => 0#u64)", "| .none => ok 0#u64)"),
            ("| .none => 0#u64\n", "| .none => ok 0#u64\n"),
        ] {
            if body.contains(*old) && !body.contains(*new_val) {
                *body = body.replacen(*old, new_val, 1);
            }
        }
    }

    changed
}

/// Strip `ok (match ...)` → `match ...` for dispatch functions.
///
/// In dispatch functions (KernelOp.execute, Step.execute, etc.), the body is:
///   ok (match self with | .A => (callee_a) | .B => (callee_b) | ...)
///
/// The callees return `Result (core.result.Result T E)`, so wrapping in `ok` is wrong
/// (pure context for monadic calls). Removing `ok (...)` puts the match at do-block level
/// where monadic calls are valid.
///
/// Only applied when the ENTIRE body starts with `ok (match`.
pub(crate) fn desugar_monadic_dispatch(body: &mut String) -> bool {
    // Find "ok (match" anywhere in the body (not just at the start).
    // This handles both:
    //   1. Body starts with "ok (match ..." — original case
    //   2. Body has let bindings then "ok (match ..." — terminal match in do-block
    let Some(ok_pos) = body.find("ok (match ") else {
        return false;
    };
    let prefix = &body[..ok_pos];
    let after_ok = &body[ok_pos + 3..]; // skip "ok "
    // Verify the match extends to the end of the body (terminal expression)
    if after_ok.starts_with('(') && after_ok.trim_end().ends_with(')') {
        // Verify this is the OUTERMOST paren by checking paren balance
        let after_ok_trimmed = after_ok.trim_end();
        if let Some(close) = match_paren_bytes(after_ok_trimmed.as_bytes(), 0)
            && close == after_ok_trimmed.len() - 1 {
                // The paren wrapping the match extends to the very end — safe to strip
                let inner = &after_ok_trimmed[1..after_ok_trimmed.len() - 1];
                *body = format!("{}{}", prefix, inner);
                return true;
            }
    }
    false
}

/// Wrap pure constructor arms in `ok` inside do-block match expressions.
///
/// After `desugar_monadic_dispatch` strips `ok (match ...)`, constructor arms like
/// `=> (.Err x)` are at do-block level but produce a pure value. Lean needs `Result T`
/// at do-level, so these arms must be wrapped: `=> ok (.Err x)`.
///
/// The `open Aeneas.Std Result` in scope means dot-notation constructors (`.Err`, `.some`,
/// `.Deny`, etc.) would resolve against `Aeneas.Std.Result` instead of the intended type.
/// Wrapping in `ok` sets the expected type for the constructor, fixing the resolution.
///
/// Heuristic: `=> (.` means a dot-notation constructor (pure). `=> (lowercase.path.` means
/// a function call (already monadic). Only wraps the former.
pub(crate) fn desugar_pure_arms(body: &mut String) -> bool {
    if !body.contains("match ") {
        return false;
    }

    let mut changed = false;
    let is_leading_match = body.trim_start().starts_with("match ");

    // A. Fix monadic match discriminees: match (call ...) → match (← (call ...))
    //    Only safe for leading match (do-level).
    if is_leading_match {
        for call in &[
            "core.num.checked_add",
            "step.Step.subject",
            "std.collections.BTreeMap.get",
        ] {
            let pat = format!("match ({} ", call);
            let bound = format!("match (← ({} ", call);
            if body.contains(&pat) && !body.contains(&bound) {
                changed |= insert_bind_before(body, call);
            }
        }
    }

    // B. Wrap pure constructor arms: | PAT => (.X args) → | PAT => ok (.X args)
    //    Works for any match position, but only wraps match arms (not lambdas).
    if body.contains("=> (.") {
        let pat = "=> (.";
        let mut search_from = 0;
        loop {
            let Some(rel_pos) = body[search_from..].find(pat) else {
                break;
            };
            let abs_pos = search_from + rel_pos;

            // Don't double-wrap: check if "ok " already precedes the "("
            let arrow_end = abs_pos + 3; // position of "("
            if arrow_end >= 3 && body[..arrow_end].ends_with("ok ") {
                search_from = abs_pos + pat.len();
                continue;
            }

            // Distinguish match arms from lambda bodies by checking whether
            // the nearest preceding keyword is `| ` (match arm) or `fun ` (lambda).
            let before = &body[..abs_pos];
            let last_pipe = before.rfind("| ");
            let last_fun = before.rfind("fun ");
            let is_match_arm = match (last_pipe, last_fun) {
                (Some(p), Some(f)) => p > f, // pipe is closer → match arm
                (Some(_), None) => true,
                _ => false,
            };

            if !is_match_arm {
                search_from = abs_pos + pat.len();
                continue;
            }

            // Insert "ok " after "=> "
            body.insert_str(arrow_end, "ok ");
            search_from = arrow_end + 3 + pat.len() - 3; // skip past "ok (."
            changed = true;
        }
    }

    // C. Wrap bare literal arms: => false, => true, => () in monadic match.
    //    Only for leading match at do-level — non-leading matches may be inside
    //    pure expressions like `!(match ...)` where arms must be Bool, not Result Bool.
    if is_leading_match {
        for (old, new_val) in &[
            ("=> false)", "=> ok false)"),
            ("=> false\n", "=> ok false\n"),
            ("=> true)", "=> ok true)"),
            ("=> true\n", "=> ok true\n"),
        ] {
            if body.contains(*old) && !body.contains(*new_val) {
                *body = body.replacen(*old, new_val, 1);
                changed = true;
            }
        }
        // Also handle end-of-body case (no trailing \n or )) when desugar_monadic_dispatch
        // has already stripped the wrapper — the body ends directly with the arm value.
        for (suffix, replacement) in &[
            ("=> false", "=> ok false"),
            ("=> true", "=> ok true"),
            // Numeric zero literals returned as "no value" from absent map keys
            ("=> 0#u8", "=> ok 0#u8"),
            ("=> 0#u16", "=> ok 0#u16"),
            ("=> 0#u32", "=> ok 0#u32"),
            ("=> 0#u64", "=> ok 0#u64"),
            ("=> 0#usize", "=> ok 0#usize"),
        ] {
            if body.ends_with(suffix) && !body.ends_with(&format!("ok {}", &suffix[3..])) {
                let len = body.len() - suffix.len();
                body.replace_range(len.., replacement);
                changed = true;
            }
        }
    }

    // D. Wrap negated monadic bind arms: => (!(← e)) → => ok (!(← e)).
    //    When a match arm applies boolean NOT to a monadic call result, the arm
    //    has type Bool (not Result Bool). Lean needs ok(...) to lift to Result.
    if is_leading_match && body.contains("=> (!(← ") && !body.contains("=> ok (!(← ") {
        *body = body.replacen("=> (!(← ", "=> ok (!(← ", 1);
        changed = true;
    }

    // E. Wrap angle-bracket constructor arms: | PAT => (⟨...⟩) → | PAT => ok (⟨...⟩)
    //    Aeneas Slice/Array use anonymous constructor syntax ⟨list, proof⟩.
    //    In a do-block match, pure ⟨...⟩ arms need `ok` wrapping just like dot-notation ones.
    //    Only wrap match arms (not lambda bodies) and only when not already wrapped.
    if body.contains("=> (⟨") {
        let pat = "=> (⟨";
        let mut search_from = 0;
        loop {
            let Some(rel_pos) = body[search_from..].find(pat) else {
                break;
            };
            let abs_pos = search_from + rel_pos;

            // Don't double-wrap: check if "ok " already precedes the "("
            let arrow_end = abs_pos + 3; // position of "("
            if arrow_end >= 3 && body[..arrow_end].ends_with("ok ") {
                search_from = abs_pos + pat.len();
                continue;
            }

            // Only wrap match arms (pipe closer than fun keyword)
            let before = &body[..abs_pos];
            let last_pipe = before.rfind("| ");
            let last_fun = before.rfind("fun ");
            let is_match_arm = match (last_pipe, last_fun) {
                (Some(p), Some(f)) => p > f,
                (Some(_), None) => true,
                _ => false,
            };

            if !is_match_arm {
                search_from = abs_pos + pat.len();
                continue;
            }

            body.insert_str(arrow_end, "ok ");
            search_from = arrow_end + 3 + pat.len() - 3;
            changed = true;
        }
    }

    changed
}

/// Desugar `core.result.Result.map_err` calls into a monadic match.
///
/// Pattern:
///   (core.result.Result.map_err T E _ (← (CALL)) MAPPER)
///
/// Replacement for Action.new map_err calls, where the visible inner error type
/// must change from PolicyError to the caller's error type:
///   (match (← (CALL)) with
///     | core.result.Result.Ok map_ok => ok (core.result.Result.Ok map_ok)
///     | core.result.Result.Err map_err => ok (core.result.Result.Err (MAPPER map_err)))
///
/// The Ok constructor is polymorphic in E, so Lean infers the mapped error type
/// from the function's return type, while the Err arm explicitly applies the
/// Rust mapper closure. Other map_err calls keep the older conservative panic
/// desugar until their mapper bodies are emitted reliably.
pub(crate) fn desugar_map_err(body: &mut String) -> usize {
    let marker = "(core.result.Result.map_err ";
    let bind_prefix = "(← (";
    let mut count = 0;

    loop {
        let Some(start) = body.find(marker) else {
            break;
        };
        let Some(map_err_end) = match_paren_bytes(body.as_bytes(), start) else {
            break;
        };

        // Find the inner call: (← (CALL)) within the map_err expression
        let search_region = &body[start..=map_err_end];
        let Some(bind_rel) = search_region.find(bind_prefix) else {
            break;
        };
        let bind_abs = start + bind_rel;
        let inner_paren = bind_abs + bind_prefix.len() - 1;
        let Some(inner_close) = match_paren_bytes(body.as_bytes(), inner_paren) else {
            break;
        };
        let Some(bind_close) = match_paren_bytes(body.as_bytes(), bind_abs) else {
            break;
        };
        let inner_call = body[inner_paren + 1..inner_close].to_string();
        let mapper = body[bind_close + 1..map_err_end].trim().to_string();
        if mapper.is_empty() {
            break;
        }

        // Check if map_err is nested inside a try_operator (TryResultResultInfallible.branch).
        // The old check looked for any earlier try marker and stripped unrelated later map_err
        // calls. Limit this to a branch expression whose parentheses actually enclose map_err.
        let in_try = body[..start]
            .rfind("core.result.TryResultResultInfallible.branch")
            .and_then(|branch_pos| {
                let branch_start = body[..branch_pos].rfind('(')?;
                let branch_end = match_paren_bytes(body.as_bytes(), branch_start)?;
                Some(start <= branch_end)
            })
            .unwrap_or(false);
        let should_apply_mapper = inner_call.contains("types.policy.Action.new")
            || inner_call.contains("Action.new");
        let replacement = if should_apply_mapper {
            if in_try {
                // Keep map_err semantics under the surrounding try operator. The try desugar
                // will bind and match this mapped inner Result later.
                format!(
                    "(match (← ({})) with | core.result.Result.Ok map_ok => ok (core.result.Result.Ok map_ok) | core.result.Result.Err map_err => ok (core.result.Result.Err ({} map_err)))",
                    inner_call, mapper
                )
            } else {
                // Standalone: desugar to a mapped inner Result.
                format!(
                    "(match (← ({})) with | core.result.Result.Ok map_ok => ok (core.result.Result.Ok map_ok) | core.result.Result.Err map_err => ok (core.result.Result.Err ({} map_err)))",
                    inner_call, mapper
                )
            }
        } else if in_try {
            // Historical behavior: strip to inner call and let try_operator handle
            // propagation. This avoids surfacing mapper bodies the emitter does not
            // yet render as Result-returning Lean terms.
            format!("({})", inner_call)
        } else {
            // Historical conservative fallback for non-Action.new map_err sites.
            format!(
                "(match (← ({})) with | core.result.Result.Ok map_ok => ok (core.result.Result.Ok map_ok) | core.result.Result.Err _map_err => fail .panic)",
                inner_call
            )
        };
        body.replace_range(start..=map_err_end, &replacement);
        count += 1;
    }

    count
}

/// Desugar Rust's `?` operator from LLBC representation to a proper Result match.
///
/// Pattern (each on a single `let` line):
///   (match (core.result.TryResultResultInfallible.branch T E (← (CALL)))
///     with | .Break v => (core.result.FromResidualResultResultInfallible.from_residual ...)
///          | .Continue v2 => v2)
///
/// Replacement:
///   (match (← (CALL)) with
///     | core.result.Result.Ok try_ok => ok try_ok
///     | core.result.Result.Err _try_err => fail .panic)
///
/// The inner call returns `Result (core.result.Result T E)`. `←` unwraps the outer
/// Aeneas Result; the match unwraps the inner core.result.Result. Uses qualified
/// constructor names to avoid collision with Aeneas's `open Result`.
pub(crate) fn desugar_try_operators(body: &mut String) -> usize {
    let marker = "core.result.TryResultResultInfallible.branch";
    let bind_prefix = "(← ("; // outer(, ←, space, inner(
    let mut count = 0;

    loop {
        let Some(branch_pos) = body.find(marker) else {
            break;
        };

        // Find the `(match ` that encloses this branch call
        let Some(match_start) = body[..branch_pos].rfind("(match (") else {
            break;
        };
        let Some(match_close) = match_paren_bytes(body.as_bytes(), match_start) else {
            break;
        };

        // Find `(← (` after branch — wraps the inner call (last arg to branch)
        let after_branch = &body[branch_pos..];
        let Some(bind_rel) = after_branch.find(bind_prefix) else {
            break;
        };
        let bind_start = branch_pos + bind_rel; // outer ( of (← (CALL))

        // Inner ( is the last byte of bind_prefix
        let inner_paren = bind_start + bind_prefix.len() - 1;
        let Some(inner_close) = match_paren_bytes(body.as_bytes(), inner_paren) else {
            break;
        };
        let inner_call = body[inner_paren + 1..inner_close].to_string();

        // Replace entire (match ... Continue v => v) with a proper Result match.
        // Both arms are monadic: `ok` wraps the Ok value, `fail` propagates through `←`.
        // We use `fail .panic` because `←` (bind) propagates fail automatically,
        // giving us the early-return semantics of Rust's `?` operator.
        let replacement = format!(
            "(match (← ({})) with | core.result.Result.Ok try_ok => ok try_ok | core.result.Result.Err _try_err => fail .panic)",
            inner_call
        );
        body.replace_range(match_start..=match_close, &replacement);
        count += 1;
    }

    // The match arms are now monadic (both return `Result T`), so the outer
    // `let VAR :=` must use `←` to bind the monadic result.
    // Only apply at do-notation level (start of line), not inside nested (let ...; ...) expressions.
    let bind_match = " := (match (← (";
    let bind_prefix_len = " := ".len();
    let mut search_start = 0;
    loop {
        let Some(rel_pos) = body[search_start..].find(bind_match) else {
            break;
        };
        let pos = search_start + rel_pos;
        // Check if this `:=` is at do-notation level by looking for a preceding `(`
        // between the last newline and this position.
        let line_start = body[..pos].rfind('\n').map_or(0, |p| p + 1);
        let before_on_line = &body[line_start..pos];
        if before_on_line.contains('(') {
            // Inside a parenthesized expression — skip
            search_start = pos + bind_prefix_len;
            continue;
        }
        body.replace_range(pos..pos + bind_prefix_len, " ← ");
        search_start = pos + " ← ".len();
    }

    // Phase 3: fix remaining try-let bindings inside match arms.
    // Phase 2 skips these in single-line bodies because `before_on_line.contains('(')`
    // is always true. Here we use the `try_ok => ok try_ok` marker to confirm the
    // match is a try-operator, making the `:=` → `←` replacement safe at any depth.
    let mut phase3_start = 0;
    loop {
        let Some(rel_pos) = body[phase3_start..].find(" := (match (← (") else {
            break;
        };
        let pos = phase3_start + rel_pos;
        // Skip `let _ := ` — underscore discards the result, `:=` is correct.
        // Named bindings (let local_N := ) need ← to unwrap the Result.
        // `pos` points at the space before `:=`, so body[..pos] ends with the var name.
        if body[..pos].ends_with(" _") {
            phase3_start = pos + " := (match (← (".len();
            continue;
        }
        // Check for the try-ok marker within a reasonable window
        let search_end = std::cmp::min(pos + 600, body.len());
        if body[pos..search_end].contains("try_ok => ok try_ok") {
            body.replace_range(pos..pos + " := ".len(), " ← ");
            phase3_start = pos + " ← ".len();
            count += 1;
        } else {
            phase3_start = pos + " := (match (← (".len();
        }
    }

    // Phase 4: `(let X ← ...)` needs `(do let X ← ...)`.
    // Lean's `←` is do-notation syntax, not valid in plain `(let ... in ...)`.
    // Adding `do` creates a nested do-block where `←` is valid.
    let mut phase4_start = 0;
    loop {
        let Some(rel_pos) = body[phase4_start..].find(" ← (match") else {
            break;
        };
        let abs_pos = phase4_start + rel_pos;
        // Find the preceding `(let ` for this `←`
        let before = &body[..abs_pos];
        if let Some(let_pos) = before.rfind("(let ") {
            // Verify no intervening `(` or `;` between `(let IDENT` and ` ← `
            let between = &body[let_pos + 5..abs_pos];
            if !between.contains('(') && !between.contains(';') {
                body.insert_str(let_pos + 1, "do ");
                phase4_start = let_pos + "do ".len() + 5;
                continue;
            }
        }
        phase4_start = abs_pos + " ← (match".len();
    }

    count
}

/// F1 (issue #273): Insert `←` binding around `BTreeMap.get_mut` used as a match discriminee.
///
/// styx-rustc emits:
///   `match (std.collections.BTreeMap.get_mut self.resources addr) with ...`
///
/// The `get_mut` call returns `Result (Option V)` in Aeneas-land, so it must be
/// `←`-bound before being used as a match discriminee:
///   `match (← (std.collections.BTreeMap.get_mut self.resources addr)) with ...`
///
/// Applies to both the `std.` and `alloc.` namespaces.
pub(crate) fn desugar_get_mut_bind(body: &mut String) -> bool {
    let targets: &[(&str, &str)] = &[
        (
            "match (std.collections.BTreeMap.get_mut ",
            "match (← (std.collections.BTreeMap.get_mut ",
        ),
        (
            "match (alloc.collections.btree.map.BTreeMap.get_mut ",
            "match (← (alloc.collections.btree.map.BTreeMap.get_mut ",
        ),
    ];
    let mut changed = false;
    for (needle, replacement) in targets {
        if body.contains(needle) {
            // Each occurrence: the original `match (FN ARGS)` becomes `match (← (FN ARGS)`.
            // We need to close the inner paren after the original closing paren.
            // Strategy: insert `← (` after `match (` and add `)` before `) with`.
            // Simpler: replace `match (BTreeMap.get_mut ARGS) with` →
            //          `match (← (BTreeMap.get_mut ARGS)) with`
            // We do this by replacing the prefix `match (FN ` → `match (← (FN `
            // and then replacing `) with` → `)) with` for the first occurrence after.
            let new_body = body.replace(needle, replacement);
            // Fix the closing paren: `) with` that follows the get_mut call.
            // After replacing prefix, the pattern is `← (BTreeMap.get_mut ARGS) with`
            // and we need `← (BTreeMap.get_mut ARGS)) with`.
            // Find the `) with` that closes the outer `match (` paren.
            let fixed = fix_get_mut_close_paren(&new_body);
            *body = fixed;
            changed = true;
        }
    }
    changed
}

/// Add the missing closing paren for `get_mut_bind` desugaring.
///
/// After `match (FN ` → `match (← (FN `, the body has one extra open paren.
/// We need to add a `)` before `) with` in the affected position.
pub(crate) fn fix_get_mut_close_paren(body: &str) -> String {
    // Pattern: `(← (BTreeMap.get_mut ...ARGS) with`
    // We need:  `(← (BTreeMap.get_mut ...ARGS)) with`
    // The body text may already have the mapped name (alloc.* namespace)
    // if map_std_callee ran during emit_callee (which happens before post-processing).
    let markers: &[&str] = &[
        "(← (std.collections.BTreeMap.get_mut ",
        "(← (alloc.collections.btree.map.BTreeMap.get_mut ",
    ];
    let mut result = body.to_string();
    for marker in markers {
        if let Some(start) = result.find(marker) {
            // `marker` = "(← (FN_NAME " (e.g. "(← (alloc.collections.btree.map.BTreeMap.get_mut ")
            // We need to find the `)` that closes the inner fn call `(FN_NAME ARGS)`.
            // Start tracking from just after the `(` before the fn name (= start + len("(← (")).
            // "(← (" byte length: '(' = 1, '←' = 3 (UTF-8), ' ' = 1, '(' = 1 → 6 bytes total.
            const PREFIX_LEN: usize = 6; // "(← (" in bytes
            // inner_start is past the opening paren of the fn call
            let inner_start = start + PREFIX_LEN;
            // Walk from inner_start to find the closing `)` of the call (depth=1 from inner paren)
            let bytes = result.as_bytes();
            let mut depth = 1usize;
            let mut i = inner_start;
            while i < bytes.len() {
                match bytes[i] {
                    b'(' => depth += 1,
                    b')' => {
                        depth -= 1;
                        if depth == 0 {
                            // This `)` closes `(← (FN ...` — insert extra `)` here
                            // so it becomes `(← (FN ...))` closing both parens.
                            // BUT we need `) with` after; let's insert before the `)`.
                            // Actually we want: close the INNER call paren first, then outer.
                            // Original: `match (← (get_mut ARGS) with`
                            // Want: `match (← (get_mut ARGS)) with`
                            // So insert `)` at position i (before the existing `)`)
                            // → gives `(← (get_mut ARGS))) with` — too many
                            // Correct: insert `)` AFTER position i
                            result.insert(i + 1, ')');
                            break;
                        }
                    }
                    _ => {}
                }
                i += 1;
            }
            break; // only fix the first occurrence per marker
        }
    }
    result
}

/// F2 (issue #273): Fix duplicate `.some _` match arm after F1 bind insertion.
///
/// When styx-rustc emits two `Some(...)` arms from a Rust match that had
///   `Some(x @ Variant1) => ...` and `Some(Variant2) => ...`
/// the Lean output contains two `.some` arms (one named, one wildcard):
///   `| .some local_N => ...A...  | .some _ => ...B...`
///
/// The second `.some _` arm is unreachable and triggers a Lean error.
/// We rename it to `.none =>` which corresponds to the Rust wildcard `None =>` case.
/// (The `BTreeMap.get_mut` returns `Option V`, so `.none` = key not found.)
pub(crate) fn desugar_free_mut_dup_arm(body: &mut String) -> bool {
    // Pattern: `| .some _ => ` preceded by a `| .some <ident> => ` arm
    // We look for `| .some _ =>` that appears after `| .some local_` in the same match.
    // Scope guard: only apply when the body is specifically a MetaState.free_mut or
    // BTreeMap entry pattern. Without this guard, the global replace would corrupt
    // for-in iterator .some _ arms in unrelated functions that also contain .some local_.
    let needle = "| .some _ =>";
    if body.contains(needle) && body.contains("| .some local_")
        && body.contains("MetaState.free_mut")
    {
        *body = body.replace(needle, "| .none =>");
        return true;
    }
    false
}

/// F4 (issue #273): Rewrite index-assign-as-expression to `ok ()`.
///
/// styx-rustc lowers `page[off] = val` as a statement-expression:
///   `(let _ := VAL; (local_N[local_M]))`
/// where `(local_N[local_M])` is an index read used as the "result" value.
///
/// This pattern is semantically equivalent to unit: the write happens, the
/// function returns `()`. We rewrite it to `ok ()` in do-notation.
pub(crate) fn desugar_index_assign_expr(body: &mut String) -> bool {
    // Pattern: `(let _ := EXPR; (local_N[local_M]))`
    // The suffix "; (local_" after the assigned value, followed by N[local_M]))
    const PREFIX: &str = "(let _ := ";
    const SUFFIX_PAT: &str = "; (local_";
    if !body.contains(PREFIX) || !body.contains(SUFFIX_PAT) {
        return false;
    }
    let mut changed = false;
    let mut result = body.clone();
    // Find all occurrences of `(let _ := EXPR; (local_N[local_M]))`
    while let Some(start) = result.find(PREFIX) {
        // Find "; (local_" after `start`
        if let Some(sep_rel) = result[start..].find(SUFFIX_PAT) {
            let sep = start + sep_rel;
            // The text after "; (local_" is "N[local_M]))" — find the closing parens
            // The full pattern ends with `))`  (closes `(local_N[...])` and `(let _ := ...`)
            // Find "])" after sep to locate end
            let after_sep = sep + SUFFIX_PAT.len();
            // Walk to find "[" then "]" then ")" then ")"
            if let Some(bracket_rel) = result[after_sep..].find('[') {
                let bracket = after_sep + bracket_rel;
                if let Some(close_bracket_rel) = result[bracket..].find(']') {
                    let close_bracket = bracket + close_bracket_rel;
                    // After ']' we expect "))": closes `(local_N[...])` and outer `(let _ := ...)`
                    let after_bracket = close_bracket + 1;
                    if result[after_bracket..].starts_with("))") {
                        let end = after_bracket + 2; // end of the full pattern
                        result.replace_range(start..end, "ok ()");
                        changed = true;
                        // Don't continue — start over with fresh offsets
                        continue;
                    }
                }
            }
        }
        break; // no more matches found
    }
    if changed {
        *body = result;
    }
    changed
}

/// Desugar match on UScalar literals to if-else chains.
/// Lean can't pattern match on `0#u8`, `1#u8` etc. directly; convert:
///   `match value with | 0#u8 => A | 1#u8 => B | _ => C`
/// to:
///   `if value == 0#u8 then A else if value == 1#u8 then B else C`
pub(crate) fn desugar_uscalar_match(body: &mut String) -> bool {
    use std::fmt::Write;
    let mut changed = false;
    // Look for `match <var> with | N#uX =>` pattern
    let suffixes = ["#u8", "#u16", "#u32", "#u64"];
    loop {
        // Find a match arm with a scalar literal pattern
        let mut found = false;
        for suffix in &suffixes {
            let pat = format!("| 0{} =>", suffix);
            if !body.contains(&pat) {
                continue;
            }
            // Find the start of the match expression containing this arm
            let arm_pos = body.find(&pat).unwrap();
            // Walk backward to find `match <var> with`
            let before = &body[..arm_pos];
            let Some(match_kw) = before.rfind("match ") else {
                continue;
            };
            // Extract the discriminee variable between `match ` and ` with`
            let after_match = &body[match_kw + 6..];
            let Some(with_pos) = after_match.find(" with") else {
                continue;
            };
            let discr = after_match[..with_pos].trim().to_string();
            // Find the end of the entire match expression.
            // We need to find all arms: | N#uX => EXPR | ... | _ => EXPR
            // The match may be wrapped in parens or be at top level.
            let arms_start = match_kw + 6 + with_pos + 5; // skip " with"
            let rest = &body[arms_start..];
            // Parse arms: collect (pattern, body) pairs
            let mut arms: Vec<(String, String)> = Vec::new();
            let mut wildcard_body: Option<String> = None;
            let mut wildcard_binding: Option<String> = None;
            let mut pos = 0;
            while pos < rest.len() {
                // Skip whitespace
                while pos < rest.len() && rest.as_bytes()[pos].is_ascii_whitespace() {
                    pos += 1;
                }
                if pos >= rest.len() {
                    break;
                }
                // Expect `| `
                if !rest[pos..].starts_with("| ") {
                    break;
                }
                pos += 2; // skip `| `
                // Read pattern until ` =>`
                let arm_rest = &rest[pos..];
                let Some(arrow) = arm_rest.find(" =>") else {
                    break;
                };
                let pattern = arm_rest[..arrow].trim().to_string();
                pos += arrow + 3; // skip pattern + ` =>`
                // Skip space after =>
                while pos < rest.len() && rest.as_bytes()[pos] == b' ' {
                    pos += 1;
                }
                // Read arm body: either a parenthesized expression or until next `| ` or end
                let arm_body_start = pos;
                if pos < rest.len() && rest.as_bytes()[pos] == b'(' {
                    // Parenthesized: find matching close paren
                    if let Some(close) = match_paren_bytes(rest.as_bytes(), pos) {
                        let arm_body = rest[arm_body_start..=close].to_string();
                        pos = close + 1;
                        if pattern == "_" || pattern.starts_with("local_") {
                            if pattern.starts_with("local_") {
                                wildcard_binding = Some(pattern.clone());
                            }
                            wildcard_body = Some(arm_body);
                        } else {
                            arms.push((pattern, arm_body));
                        }
                    } else {
                        break;
                    }
                } else {
                    // Non-paren: read until ` | ` at depth 0, newline, or `)` at depth -1
                    let mut end = pos;
                    let rest_bytes = rest.as_bytes();
                    let mut depth = 0i32;
                    while end < rest.len() {
                        // Check for ` | ` at depth 0 (next arm marker)
                        if depth == 0 && end + 3 <= rest.len() && &rest[end..end + 3] == " | " {
                            break;
                        }
                        match rest_bytes[end] {
                            b'(' => {
                                depth += 1;
                            }
                            b')' => {
                                if depth == 0 {
                                    break;
                                } // closing paren of enclosing expr
                                depth -= 1;
                            }
                            b'\n' => break,
                            _ => {}
                        }
                        end += 1;
                    }
                    let arm_body = rest[arm_body_start..end].trim_end().to_string();
                    pos = end;
                    if pattern == "_" || pattern.starts_with("local_") {
                        wildcard_body = Some(arm_body);
                    } else {
                        arms.push((pattern, arm_body));
                    }
                }
            }
            if arms.is_empty() {
                continue;
            }
            // Build if-else chain
            let mut result = String::new();
            let mut catchall_is_return = false;
            for (i, (pat, arm_body)) in arms.iter().enumerate() {
                if i == 0 {
                    write!(result, "if {} == {} then {}", discr, pat, arm_body).unwrap();
                } else {
                    write!(result, " else if {} == {} then {}", discr, pat, arm_body).unwrap();
                }
            }
            if let Some(wb) = &wildcard_body {
                // T5 (2026-04-14): when the catch-all pattern is `local_N`, the Rust source
                // bound the value to a name (e.g., `other`) and uses it in the arm body.
                // The emitter leaked the bound name into wildcard_body as `local_N`, but the
                // if-chain has no such local. Substitute the binding with the scrutinee so
                // references like `.InvalidSecurityLevel local_47` become `.InvalidSecurityLevel local_18`.
                // Also rewrite bare `(let _ := (.Err ...); ())` tails to `ok (.Err ...)` since
                // the enclosing expression is a Result-bound let and `()` doesn't type-check.
                let wb_fixed = {
                    let mut s = wb.clone();
                    // Find the catch-all pattern from the arms parse — scan rest backwards.
                    // Simpler: look at wb for `local_N` tokens that aren't defined by the
                    // enclosing body and substitute with `discr`. We use the captured
                    // `wildcard_pat` from the arms loop (see below).
                    if let Some(bind_name) = &wildcard_binding {
                        // Word-boundary substitution: `local_N` → `discr` where `local_N` stands alone.
                        let mut out = String::with_capacity(s.len());
                        let bytes = s.as_bytes();
                        let needle = bind_name.as_bytes();
                        let mut i = 0;
                        while i < bytes.len() {
                            let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
                            if i + needle.len() <= bytes.len()
                                && &bytes[i..i + needle.len()] == needle
                                && (i == 0 || !is_ident(bytes[i - 1]))
                                && (i + needle.len() == bytes.len()
                                    || !is_ident(bytes[i + needle.len()]))
                            {
                                out.push_str(&discr);
                                i += needle.len();
                            } else {
                                out.push(bytes[i] as char);
                                i += 1;
                            }
                        }
                        s = out;
                    }
                    // Rewrite bare (let _ := (.Err ...); ()) → return (.Err ...)
                    // The Rust catch-all arm uses `return Err(...)` — an early exit from the
                    // function. In Lean do-notation this must be `return (.Err ...)`, NOT
                    // `ok (.Err ...)`. Using `return` keeps the if-chain type as `Result T _`
                    // (same as numeric arms which produce `ok (.Variant)`), so the enclosing
                    // `let local_N ←` bind extracts T directly without a double-Result wrap.
                    if let Some(start) = s.find("(let _ := (.Err ") {
                        // Find matching ")" at depth 0 relative to '(let'
                        let from = start + "(let _ := ".len();
                        let bytes = s.as_bytes();
                        if let Some(err_close) = match_paren_bytes(bytes, from) {
                            let err_text = &s[from..=err_close];
                            // wb = "(let _ := (.Err ...); ())" — starts and ends with matched parens
                            // captured by match_paren_bytes. After err_close in s: ); ()).
                            // We replace from start to end-of-string to consume the outer wrapper `)`.
                            // Verify the suffix is exactly `; ())` before consuming.
                            let after_err = &s[err_close..];
                            if after_err.starts_with("); ())") {
                                // ); ()) = err_close `)` + "; ()" + outer `)`
                                let end = err_close + "); ())".len();
                                let replaced = format!("return {}", err_text);
                                s.replace_range(start..end, &replaced);
                            } else if after_err.starts_with("); ()") {
                                // Same without outer `)`
                                let end = err_close + "); ()".len();
                                let replaced = format!("return {}", err_text);
                                s.replace_range(start..end, &replaced);
                            }
                        }
                    }
                    s
                };
                // When the catch-all is a `return`-exit, the if-chain is monadic.
                // The enclosing `let local_N :=` must become `let local_N ←`. We do this
                // AFTER the main replace_range below because ` ← ` (5 bytes, UTF-8 `←` = 3 bytes)
                // is longer than ` := ` (4 bytes) — modifying body here would corrupt the
                // position variables (match_kw, arms_start, pos) computed from the original body.
                catchall_is_return = wb_fixed.contains("return (");
                write!(result, " else {}", wb_fixed).unwrap();
            }
            // Replace the match expression.
            // If the match was parenthesized as `(match ... with ...)`, the arms parser stops
            // before the closing `)`. Consume both the `(` before `match_kw` and the `)` at
            // `match_end` so the if-chain replaces the full parenthesized expression.
            let match_end = arms_start + pos;
            let (rep_start, rep_end) = if match_kw > 0
                && body.as_bytes().get(match_kw - 1) == Some(&b'(')
                && body.as_bytes().get(match_end) == Some(&b')')
            {
                (match_kw - 1, match_end + 1)
            } else {
                (match_kw, match_end)
            };
            body.replace_range(rep_start..rep_end, &result);
            // Apply `:=` → `←` AFTER the main replacement so the byte-length difference
            // between ` ← ` (5) and ` := ` (4) doesn't corrupt `match_end`/`rep_start`.
            if catchall_is_return {
                // Find the nearest `let <ident> :=` before rep_start in the updated body.
                let before = &body[..rep_start];
                if let Some(let_pos) = before.rfind("let ") {
                    let after_let = &body[let_pos + 4..rep_start];
                    if let Some(assign_rel) = after_let.rfind(" := ") {
                        let var_name = after_let[..assign_rel].trim_start();
                        let is_plain = !var_name.is_empty()
                            && var_name
                                .chars()
                                .all(|c| c.is_ascii_alphanumeric() || c == '_');
                        if is_plain {
                            let assign_abs = let_pos + 4 + assign_rel;
                            body.replace_range(assign_abs..assign_abs + " := ".len(), " ← ");
                        }
                    }
                }
            }
            changed = true;
            found = true;
            break; // restart outer loop — positions shifted
        }
        if !found {
            break;
        }
    }
    changed
}

/// Wrap a monadic function call with `←`: `(target args)` → `(← (target args))`.
/// `body` is the full body text; `target` is the function name prefix to match after `(`.
/// Returns true if a replacement was made.
pub(crate) fn insert_bind_before(body: &mut String, target: &str) -> bool {
    let pattern = format!("({}", target);
    // Don't double-bind if already `(← (target`
    let already = format!("(← ({}", target);
    if body.contains(&already) {
        return false;
    }
    if let Some(pos) = body.find(&pattern)
        && let Some(close) = match_paren_bytes(body.as_bytes(), pos) {
            let inner = body[pos..=close].to_string();
            let fixed = format!("(← {})", inner);
            body.replace_range(pos..=close, &fixed);
            return true;
        }
    false
}

/// Desugar `is_blocked` / `blocked_on` / `can_receive` in `PluginInternal::check_preconditions`.
///
/// Three type errors in the emitted body:
///
/// A. `if (state.actor.ActorRuntime.is_blocked LOCALVAR) then ...`
///    `is_blocked` returns `Result Bool`, not `Bool`.  Lean cannot use it directly as an `if`
///    condition.  Fix: hoist to `let _isblocked ← ...; if _isblocked then ...`.
///
/// B. `(← (state.actor.ActorRuntime.blocked_on LOCALVAR))`
///    `blocked_on` is a *field* accessor that styx skips (emits `-- skipped field accessor`).
///    No Lean function `state.actor.ActorRuntime.blocked_on` exists.  Fix: replace with the
///    direct field projection `LOCALVAR.blocked_on`.
///
/// C. `if (!(← (state.actor.ActorRuntime.can_receive LOCALVAR))) then ...`
///    Same as A: `can_receive` returns `Result Bool`.  Additionally the `←` is nested inside
///    `!()` which is itself inside `if`.  Fix: hoist to
///    `let _canrecv ← ...; if !_canrecv then ...`.
pub(crate) fn desugar_actor_runtime_if_conditions(body: &mut String) -> bool {
    let mut changed = false;

    // --- Pass B: replace (← (state.actor.ActorRuntime.blocked_on LOCALVAR)) with LOCALVAR.blocked_on ---
    // Must run before pass A because A may shift the text.
    {
        // bind_prefix = "(← (state.actor.ActorRuntime.blocked_on "
        // Byte layout of "(← (":
        //   '(' = 1 byte at offset 0
        //   '←' = 3 bytes (U+2190, UTF-8: E2 86 90) at offset 1
        //   ' ' = 1 byte at offset 4
        //   '(' = 1 byte at offset 5  ← inner_open relative to start
        const BIND_ARROW_INNER_OFFSET: usize = 5; // "(← (" prefix = 5 bytes to inner '('
        let bind_prefix = "(← (state.actor.ActorRuntime.blocked_on ";
        while let Some(start) = body.find(bind_prefix) {
            // Find the outer closing ')' for `(← (...))` using paren matching on the outer `(`.
            if let Some(outer_close) = match_paren_bytes(body.as_bytes(), start) {
                // Inner call `(state.actor.ActorRuntime.blocked_on LOCALVAR)` starts at start+5
                let inner_open = start + BIND_ARROW_INNER_OFFSET;
                if body.as_bytes().get(inner_open) != Some(&b'(') {
                    break; // sanity check: inner_open must be '('
                }
                if let Some(inner_close) = match_paren_bytes(body.as_bytes(), inner_open) {
                    // args are after the function name and a space
                    let fn_prefix = "state.actor.ActorRuntime.blocked_on ";
                    let args_start = inner_open + 1 + fn_prefix.len();
                    let local_var = body[args_start..inner_close].trim().to_string();
                    let replacement = format!("{}.blocked_on", local_var);
                    body.replace_range(start..=outer_close, &replacement);
                    changed = true;
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    // --- Pass A: hoist `if (is_blocked LOCALVAR) then` to let-bind + `if _isblocked then` ---
    {
        let if_prefix = "if (state.actor.ActorRuntime.is_blocked ";
        let mut bind_ctr = 0u32;
        while let Some(start) = body.find(if_prefix) {
            // Find the end of `(state.actor.ActorRuntime.is_blocked LOCALVAR)` paren
            let call_open = start + "if ".len(); // position of the `(` opening the call
            if let Some(call_close) = match_paren_bytes(body.as_bytes(), call_open) {
                // Extract the full call expression including parens
                let call_expr = body[call_open + 1..call_close].to_string(); // `state.actor.ActorRuntime.is_blocked LOCALVAR`
                let bind_var = format!("_isblocked{}", bind_ctr);
                bind_ctr += 1;
                // Find start of the line (for indentation)
                let line_start = body[..start].rfind('\n').map_or(0, |p| p + 1);
                let indent: String = body[line_start..start]
                    .chars()
                    .take_while(|c| *c == ' ')
                    .collect();
                // Build the let-bind line
                let let_line = format!("let {} \u{2190} {};\n{}", bind_var, call_expr, indent);
                // Replace `if (state.actor...LOCALVAR)` with `if BIND_VAR`
                let new_if = format!("if {}", bind_var);
                // Insert let-bind before the `if` and replace the `if (...)` condition
                let after_cond = call_close + 1; // byte after the `)`
                body.replace_range(start..after_cond, &format!("{}{}", let_line, new_if));
                changed = true;
            } else {
                break;
            }
        }
    }

    // --- Pass C: hoist `if (!(← (can_receive LOCALVAR))) then` to let-bind + `if !_canrecv then` ---
    {
        let if_neg_prefix = "if (!(← (state.actor.ActorRuntime.can_receive ";
        let mut bind_ctr = 0u32;
        while let Some(start) = body.find(if_neg_prefix) {
            // Structure: `if (!(← (state.actor.ActorRuntime.can_receive LOCALVAR)))` then
            // Outer: `(!(← (...)))` — the `(` after `if ` is the outermost paren
            let outer_open = start + "if ".len();
            if let Some(outer_close) = match_paren_bytes(body.as_bytes(), outer_open) {
                // Inner call: `(state.actor.ActorRuntime.can_receive LOCALVAR)` — we just need to extract
                let fn_prefix = "state.actor.ActorRuntime.can_receive ";
                // Find the fn_prefix inside the outer expression
                let outer_content = &body[outer_open..=outer_close];
                if let Some(fn_rel) = outer_content.find(fn_prefix) {
                    let fn_abs = outer_open + fn_rel;
                    // The call starts one `(` before fn_abs
                    let call_open = fn_abs - 1; // the `(` of `(state.actor...)`
                    if call_open < outer_open {
                        break;
                    }
                    if let Some(call_close) = match_paren_bytes(body.as_bytes(), call_open) {
                        let call_expr = body[call_open + 1..call_close].to_string();
                        let bind_var = format!("_canrecv{}", bind_ctr);
                        bind_ctr += 1;
                        let line_start = body[..start].rfind('\n').map_or(0, |p| p + 1);
                        let indent: String = body[line_start..start]
                            .chars()
                            .take_while(|c| *c == ' ')
                            .collect();
                        let let_line = format!("let {} \u{2190} {};\n{}", bind_var, call_expr, indent);
                        let new_if = format!("if !{}", bind_var);
                        let after_cond = outer_close + 1;
                        body.replace_range(start..after_cond, &format!("{}{}", let_line, new_if));
                        changed = true;
                    } else {
                        break;
                    }
                } else {
                    break;
                }
            } else {
                break;
            }
        }
    }

    // --- Pass D: re-scope escaped `if let .some VAR := OPT_VAR` into enclosing `then do` block ---
    //
    // After P3/P4 desugaring, pattern:
    //   if COND then do\n
    //     let OPT_VAR ← EXPR\n      ← inside do (extra indentation)
    //   if let .some LOCAL := OPT_VAR then\n  ← ESCAPED (same or less indent as `if COND`)
    //     BODY...
    //
    // Lean 4 reports "Unknown identifier `OPT_VAR`" because OPT_VAR is bound inside the `do`
    // block but used outside it.  Fix: move the `if let .some LOCAL := OPT_VAR then BODY` block
    // inside the `then do` block by adding one level of indentation (2 spaces) to its lines.
    //
    // This is triggered by the presence of `_opt_3` escaping scope — specific to
    // `PluginInternal::check_preconditions` where `get_actor` is called inside `consume_mailbox`.
    {
        let lines: Vec<&str> = body.lines().collect();
        let mut result: Vec<String> = Vec::new();
        let mut i = 0;
        let mut pass_changed = false;

        while i < lines.len() {
            let line = lines[i];
            let trimmed = line.trim_start();
            // Find `if COND then do` line
            if trimmed.starts_with("if ") && (line.ends_with("then do") || trimmed.ends_with("then do")) {
                let do_line_indent = line.as_bytes().iter().take_while(|b| **b == b' ').count();
                result.push(line.to_string());
                i += 1;

                // Collect lines inside the do block (indented more than do_line_indent)
                let mut do_block: Vec<&str> = Vec::new();
                while i < lines.len() {
                    let inner = lines[i];
                    let inner_trimmed = inner.trim_start();
                    if inner_trimmed.is_empty() {
                        do_block.push(inner);
                        i += 1;
                        continue;
                    }
                    let inner_indent = inner.as_bytes().iter().take_while(|b| **b == b' ').count();
                    if inner_indent > do_line_indent {
                        do_block.push(inner);
                        i += 1;
                    } else {
                        break;
                    }
                }
                // Collect variable names bound inside the do block (let OPT_VAR ←)
                let mut do_bound_vars: Vec<String> = Vec::new();
                for do_line in &do_block {
                    let dt = do_line.trim_start();
                    if let Some(rest) = dt.strip_prefix("let ") {
                        // Pattern: `let VAR ←` or `let VAR :=`
                        let varname: String = rest.chars().take_while(|c| c.is_ascii_alphanumeric() || *c == '_').collect();
                        if !varname.is_empty() {
                            do_bound_vars.push(varname);
                        }
                    }
                }
                // Emit the do block lines first
                for dl in &do_block {
                    result.push(dl.to_string());
                }
                // Now check: if the NEXT line(s) reference a do-bound variable and are at
                // do_line_indent or less (i.e., they escaped the do block), pull them in.
                // We look for `if let .some LOCAL := OPT_VAR` where OPT_VAR is in do_bound_vars.
                while i < lines.len() {
                    let next = lines[i];
                    let next_trimmed = next.trim_start();
                    let next_indent = next.as_bytes().iter().take_while(|b| **b == b' ').count();
                    if next_trimmed.is_empty() || next_indent > do_line_indent {
                        break;
                    }
                    // Check if this line references a do-bound var
                    let refs_do_var = do_bound_vars.iter().any(|v| {
                        // Check for `if let .some LOCAL := VAR` pattern
                        next_trimmed.contains(&format!(":= {}", v))
                    });
                    if !refs_do_var {
                        break;
                    }
                    // This line and its body need to be indented into the do block.
                    // Determine how many lines form the body of the `if let ... then` block.
                    // Collect lines until we return to do_line_indent or less WITHOUT
                    // a do-bound-var reference (i.e., back to outer scope).
                    let extra_indent = "  "; // 2 spaces extra
                    result.push(format!("{}{}", extra_indent, next));
                    i += 1;
                    // Collect the body of the if-let (lines indented more than next_indent)
                    while i < lines.len() {
                        let body_line = lines[i];
                        let body_trimmed = body_line.trim_start();
                        if body_trimmed.is_empty() {
                            result.push(body_line.to_string());
                            i += 1;
                            continue;
                        }
                        let body_indent = body_line.as_bytes().iter().take_while(|b| **b == b' ').count();
                        if body_indent > next_indent {
                            result.push(format!("{}{}", extra_indent, body_line));
                            i += 1;
                        } else {
                            break;
                        }
                    }
                    pass_changed = true;
                }
            } else {
                result.push(line.to_string());
                i += 1;
            }
        }
        if pass_changed {
            *body = result.join("\n");
            // Preserve trailing newline if original had one
            if body.ends_with('\n') {
                // already there
            }
            changed = true;
        }
    }

    changed
}

/// Find the matching close paren for an opening '(' at `open_pos` (byte offset).
/// Works on raw bytes — safe for UTF-8 since '(' and ')' are ASCII.
pub(crate) fn match_paren_bytes(bytes: &[u8], open_pos: usize) -> Option<usize> {
    if bytes.get(open_pos) != Some(&b'(') {
        return None;
    }
    let mut depth: i32 = 0;
    for i in open_pos..bytes.len() {
        match bytes[i] {
            b'(' => depth += 1,
            b')' => {
                depth -= 1;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

// ─── T5 (2026-04-14): U64 discriminant-match desugaring ─────────────────────
// For match on an integer scrutinee with literal arms + catch-all, rewrite as
// if/else-if chain. Fixes execute_declassify[_mut] where the catch-all binds
// an undeclared Lean local and emits bare `(.Err ...)` tails.

pub(crate) fn leading_spaces_t5(line: &str) -> usize {
    line.as_bytes().iter().take_while(|b| **b == b' ').count()
}

pub(crate) fn is_ident_byte_t5(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

pub(crate) fn replace_ident_token_t5(input: &str, from: &str, to: &str) -> String {
    if from.is_empty() || from == to {
        return input.to_string();
    }
    let bytes = input.as_bytes();
    let needle = from.as_bytes();
    let mut out = String::with_capacity(input.len());
    let mut i = 0;
    while i < bytes.len() {
        if i + needle.len() <= bytes.len()
            && &bytes[i..i + needle.len()] == needle
            && (i == 0 || !is_ident_byte_t5(bytes[i - 1]))
            && (i + needle.len() == bytes.len() || !is_ident_byte_t5(bytes[i + needle.len()]))
        {
            out.push_str(to);
            i += needle.len();
        } else {
            out.push(bytes[i] as char);
            i += 1;
        }
    }
    out
}

struct DiscriminantArm {
    pat: String,
    body: Vec<String>,
}

pub(crate) fn parse_uscalar_literal_t5(pat: &str) -> Option<String> {
    let p = pat.trim().trim_matches(|c| c == '(' || c == ')');
    if p.chars().all(|c| c.is_ascii_digit()) {
        return Some(p.to_string());
    }
    let (n, suffix) = p.split_once("#u")?;
    if !n.is_empty()
        && n.chars().all(|c| c.is_ascii_digit())
        && !suffix.is_empty()
        && suffix.chars().all(|c| c.is_ascii_digit())
    {
        Some(p.to_string())
    } else {
        None
    }
}

pub(crate) fn parse_catch_all_binding_t5(pat: &str) -> Option<Option<String>> {
    let p = pat.trim();
    if p == "_" {
        return Some(None);
    }
    let mut chars = p.chars();
    match chars.next() {
        Some(c) if c.is_ascii_alphabetic() || c == '_' => {}
        _ => return None,
    }
    if chars.all(|c| c.is_ascii_alphanumeric() || c == '_') {
        Some(Some(p.to_string()))
    } else {
        None
    }
}

pub(crate) fn normalize_match_arm_body_t5(
    body: &[String],
    match_indent: usize,
    catch_all_binding: Option<&str>,
    scrutinee: &str,
    wrap_bare_err_tail: bool,
) -> Vec<String> {
    let body_indent = body
        .iter()
        .filter(|line| !line.trim().is_empty())
        .map(|line| leading_spaces_t5(line))
        .min()
        .unwrap_or(match_indent + 2);

    let mut out = Vec::with_capacity(body.len());
    for line in body {
        if line.trim().is_empty() {
            out.push(String::new());
            continue;
        }
        let mut stripped = if leading_spaces_t5(line) >= body_indent {
            line[body_indent..].to_string()
        } else {
            line.trim_start().to_string()
        };
        if let Some(binding) = catch_all_binding {
            stripped = replace_ident_token_t5(&stripped, binding, scrutinee);
        }
        out.push(stripped);
    }

    if wrap_bare_err_tail
        && let Some(idx) = out.iter().rposition(|line| !line.trim().is_empty()) {
            let rel_indent = leading_spaces_t5(&out[idx]);
            let trimmed = out[idx].trim_start();
            if trimmed.starts_with("(.Err") {
                out[idx] = format!("{}ok {}", " ".repeat(rel_indent), trimmed);
            } else if let Some(rest) = trimmed.strip_prefix("let _ := ") {
                let rest = rest.trim_start();
                if rest.starts_with("(.Err") {
                    out[idx] = format!("{}ok {}", " ".repeat(rel_indent), rest);
                } else if rest.starts_with("ok (.Err") {
                    out[idx] = format!("{}{}", " ".repeat(rel_indent), rest);
                }
            }
        }
    out
}

/// Rewrite `match scrut with | 0 => ... | 1 => ... | x => ...` into an
/// if/else-if/else chain. Only fires when all non-final arms are numeric
/// literals (optionally with `#uN` suffix) and the final arm is `_` or a
/// plain identifier.
pub(crate) fn desugar_u64_discriminant_match(body: &mut String) -> bool {
    let lines: Vec<&str> = body.lines().collect();
    let mut out = Vec::with_capacity(lines.len());
    let mut i = 0;
    let mut changed = false;

    while i < lines.len() {
        let line = lines[i];
        let trimmed = line.trim_start();
        if !(trimmed.starts_with("match ") && trimmed.ends_with(" with")) {
            out.push(line.to_string());
            i += 1;
            continue;
        }

        let indent = leading_spaces_t5(line);
        let scrutinee = trimmed["match ".len()..trimmed.len() - " with".len()]
            .trim()
            .to_string();
        if scrutinee.is_empty() {
            out.push(line.to_string());
            i += 1;
            continue;
        }

        let mut j = i + 1;
        let mut arms: Vec<DiscriminantArm> = Vec::new();
        while j < lines.len() {
            let arm_line = lines[j];
            let arm_trimmed = arm_line.trim_start();
            if leading_spaces_t5(arm_line) != indent || !arm_trimmed.starts_with("| ") {
                break;
            }
            let Some((pat, rhs)) = arm_trimmed[2..].split_once("=>") else {
                break;
            };
            let mut arm_body = Vec::new();
            if !rhs.trim().is_empty() {
                arm_body.push(format!("{}{}", " ".repeat(indent + 2), rhs.trim_start()));
            }
            j += 1;
            while j < lines.len() {
                let next = lines[j];
                let next_trimmed = next.trim_start();
                let next_indent = leading_spaces_t5(next);
                if next_indent == indent && next_trimmed.starts_with("| ") {
                    break;
                }
                if !next_trimmed.is_empty() && next_indent <= indent {
                    break;
                }
                arm_body.push(next.to_string());
                j += 1;
            }
            arms.push(DiscriminantArm {
                pat: pat.trim().to_string(),
                body: arm_body,
            });
        }

        let eligible = arms.len() >= 2
            && arms[..arms.len() - 1]
                .iter()
                .all(|arm| parse_uscalar_literal_t5(&arm.pat).is_some())
            && parse_catch_all_binding_t5(&arms[arms.len() - 1].pat).is_some();

        if !eligible {
            out.push(line.to_string());
            i += 1;
            continue;
        }

        changed = true;
        for (arm_idx, arm) in arms.iter().enumerate() {
            let indent_str = " ".repeat(indent);
            if arm_idx + 1 == arms.len() {
                out.push(format!("{indent_str}else"));
                let binding = parse_catch_all_binding_t5(&arm.pat).unwrap();
                let body_lines = normalize_match_arm_body_t5(
                    &arm.body,
                    indent,
                    binding.as_deref(),
                    &scrutinee,
                    true,
                );
                for body_line in body_lines {
                    if body_line.is_empty() {
                        out.push(String::new());
                    } else {
                        out.push(format!("{indent_str}  {body_line}"));
                    }
                }
            } else {
                let lit = parse_uscalar_literal_t5(&arm.pat).unwrap();
                let kw = if arm_idx == 0 { "if" } else { "else if" };
                out.push(format!("{indent_str}{kw} {scrutinee} == {lit} then"));
                let body_lines =
                    normalize_match_arm_body_t5(&arm.body, indent, None, &scrutinee, false);
                for body_line in body_lines {
                    if body_line.is_empty() {
                        out.push(String::new());
                    } else {
                        out.push(format!("{indent_str}  {body_line}"));
                    }
                }
            }
        }
        i = j;
    }

    if changed {
        *body = out.join("\n");
    }
    changed
}

/// Desugar Iterator::find closure bodies with compound monadic boolean conditions.
///
/// The emitter produces closures of the form:
///   (fun arg1 => do ((← (E1)) && ((← (E2)) == V)))
///
/// This is invalid Lean: `&&` is a pure `Bool → Bool → Bool` operator, and the
/// `do` block requires the final expression to have type `Result Bool`. Having
/// `(← e1) && (← e2)` as the entire return expression means the `do`-block
/// produces `Bool` instead of `Result Bool`.
///
/// Fix: desugar to sequential let-bindings:
///   (fun arg1 => do let _b0 ← E1; let _b1 ← E2; ok (_b0 && (_b1 == V)))
///
/// The pattern is anchored on `=> do ((← (` inside a `fun` binder, followed
/// by `&&` at the outermost level of the outer double-paren.
///
/// Also handles the simpler case without `== V`:
///   (fun arg1 => do ((← (E1)) && (← (E2))))
/// becomes:
///   (fun arg1 => do let _b0 ← E1; let _b1 ← E2; ok (_b0 && _b1))
pub(crate) fn desugar_find_closure_compound_bool(body: &mut String) -> bool {
    // Quick bailout: pattern requires "=> do ((" and "&&"
    let trigger = "=> do ((";
    if !body.contains(trigger) || !body.contains("&&") {
        return false;
    }

    let mut changed = false;
    let mut search_from = 0usize;
    let mut bind_ctr = 0u32;

    loop {
        // Find next "=> do ((" from search_from
        let Some(rel) = body[search_from..].find(trigger) else {
            break;
        };
        let trigger_abs = search_from + rel;
        // outer_paren is the position of the first `(` in `((`
        let outer_paren = trigger_abs + trigger.len() - 2; // "=> do " is 6 bytes, then "(("
        // outer_paren must point at '('
        if body.as_bytes().get(outer_paren) != Some(&b'(') {
            search_from = trigger_abs + trigger.len();
            continue;
        }

        // Match the outer paren to find the end of the do-block expression
        let Some(outer_close) = match_paren_bytes(body.as_bytes(), outer_paren) else {
            search_from = trigger_abs + trigger.len();
            continue;
        };

        // The outer content is: `(← (E1)) && ...` or `(← (E1)) && ((← (E2)) == V)`
        // We need the inner content (inside outer parens), starting with `(← (`
        let inner_start = outer_paren + 1;
        let inner_content = &body[inner_start..outer_close];

        // Inner must start with `(← (`
        const BIND_PFX: &str = "(← (";
        if !inner_content.starts_with(BIND_PFX) {
            search_from = trigger_abs + trigger.len();
            continue;
        }

        // Find the inner call: (← (E1)) — match the outer `(` of `(← (`
        let e1_outer_abs = inner_start; // position of `(` opening `(← (E1))`
        let Some(e1_outer_close) = match_paren_bytes(body.as_bytes(), e1_outer_abs) else {
            search_from = trigger_abs + trigger.len();
            continue;
        };

        // After `(← (E1))` there must be ` && `
        let after_e1 = e1_outer_close + 1;
        if !body[after_e1..].starts_with(" && ") {
            search_from = trigger_abs + trigger.len();
            continue;
        }

        // Extract E1: the content inside `(← (E1))` is from `e1_outer_abs+4` to the inner close
        // `(← (E1))` structure: `(` `←` ` ` `(` E1 `)` `)`
        // The `←` char is 3 bytes (U+2190 in UTF-8: E2 86 90)
        const ARROW_LEN: usize = 3; // ← in UTF-8
        let e1_inner_open = e1_outer_abs + 1 + ARROW_LEN + 1; // `(` + `←` + ` ` + `(`
        // But we need to find the inner `(E1)` paren. Start from after `(← `
        // body[e1_outer_abs] = `(`, body[e1_outer_abs+1..] = `← (E1))`
        // e1_outer_abs+1 = `←` start, +1+ARROW_LEN = ` `, +1+ARROW_LEN+1 = `(` of E1
        if e1_inner_open >= body.len() || body.as_bytes()[e1_inner_open] != b'(' {
            search_from = trigger_abs + trigger.len();
            continue;
        }
        let Some(e1_inner_close) = match_paren_bytes(body.as_bytes(), e1_inner_open) else {
            search_from = trigger_abs + trigger.len();
            continue;
        };
        let e1_expr = body[e1_inner_open + 1..e1_inner_close].to_string(); // E1 without parens

        // Now parse what's after ` && ` at position after_e1 + 4
        let rhs_start = after_e1 + 4; // skip " && "
        if rhs_start >= outer_close {
            search_from = trigger_abs + trigger.len();
            continue;
        }

        // RHS is either:
        //   (a) `(← (E2))` — simple boolean AND
        //   (b) `((← (E2)) == V)` — AND with equality check
        let rhs_slice = &body[rhs_start..outer_close];

        // Try to parse case (b): rhs wrapped in extra parens `((← (E2)) == V)`
        let (e2_expr, cmp_rhs) = if rhs_slice.starts_with("((← (") {
            // case (b): `((← (E2)) == V)` — the rhs is wrapped in an outer `(`
            let rhs_outer_open = rhs_start;
            let Some(rhs_outer_close) = match_paren_bytes(body.as_bytes(), rhs_outer_open) else {
                search_from = trigger_abs + trigger.len();
                continue;
            };
            // Inside: `(← (E2)) == V`
            let inside = &body[rhs_outer_open + 1..rhs_outer_close];
            // First token: `(← (E2))`
            if !inside.starts_with(BIND_PFX) {
                search_from = trigger_abs + trigger.len();
                continue;
            }
            let e2_bind_open = rhs_outer_open + 1;
            let Some(e2_bind_close) = match_paren_bytes(body.as_bytes(), e2_bind_open) else {
                search_from = trigger_abs + trigger.len();
                continue;
            };
            // E2 inner paren
            let e2_inner_open = e2_bind_open + 1 + ARROW_LEN + 1;
            if e2_inner_open >= body.len() || body.as_bytes()[e2_inner_open] != b'(' {
                search_from = trigger_abs + trigger.len();
                continue;
            }
            let Some(e2_inner_close) = match_paren_bytes(body.as_bytes(), e2_inner_open) else {
                search_from = trigger_abs + trigger.len();
                continue;
            };
            let e2 = body[e2_inner_open + 1..e2_inner_close].to_string();
            // After `(← (E2))` should be ` == V`
            let after_e2_bind = e2_bind_close + 1;
            if !body[after_e2_bind..].starts_with(" == ") {
                search_from = trigger_abs + trigger.len();
                continue;
            }
            let cmp_val = body[after_e2_bind + 4..rhs_outer_close].trim().to_string();
            (e2, Some(cmp_val))
        } else if rhs_slice.starts_with(BIND_PFX) {
            // case (a): `(← (E2))` directly
            let e2_bind_open = rhs_start;
            let Some(e2_bind_close) = match_paren_bytes(body.as_bytes(), e2_bind_open) else {
                search_from = trigger_abs + trigger.len();
                continue;
            };
            if e2_bind_close != outer_close - 1 {
                // The bind doesn't reach to the end of the outer paren
                // (outer_close closes the outer `(` that wraps everything)
                // Actually the outer content ends at outer_close, so e2_bind_close + 1 == outer_close
                if e2_bind_close + 1 != outer_close {
                    search_from = trigger_abs + trigger.len();
                    continue;
                }
            }
            let e2_inner_open = e2_bind_open + 1 + ARROW_LEN + 1;
            if e2_inner_open >= body.len() || body.as_bytes()[e2_inner_open] != b'(' {
                search_from = trigger_abs + trigger.len();
                continue;
            }
            let Some(e2_inner_close) = match_paren_bytes(body.as_bytes(), e2_inner_open) else {
                search_from = trigger_abs + trigger.len();
                continue;
            };
            let e2 = body[e2_inner_open + 1..e2_inner_close].to_string();
            (e2, None)
        } else {
            search_from = trigger_abs + trigger.len();
            continue;
        };

        // Build replacement: sequential let-binds + ok(...)
        let b0 = format!("_b{}", bind_ctr);
        let b1 = format!("_b{}", bind_ctr + 1);
        bind_ctr += 2;

        let bool_expr = match &cmp_rhs {
            Some(v) => format!("({b0} && ({b1} == {v}))"),
            None => format!("({b0} && {b1})"),
        };

        // The replacement covers from `outer_paren` to `outer_close` (inclusive)
        let replacement = format!(
            "let {b0} \u{2190} ({e1_expr}); let {b1} \u{2190} ({e2_expr}); ok {bool_expr}"
        );

        // We need to replace `((← (E1)) && ...)` with the desugared form.
        // The region to replace: outer_paren..=outer_close
        body.replace_range(outer_paren..=outer_close, &replacement);

        search_from = outer_paren + replacement.len();
        changed = true;
    }

    changed
}

/// Desugar `IndexMutVec.index_mut` calls into proper monadic form.
///
/// Handles two body shapes:
///
/// Shape A1: Option.map with closure containing a mutable-index projection
///   `(core.option.Option.map T _ OPTION_EXPR (fun (idx : T) => CALL.N))`
///   → monadic match that binds the call result and projects `.N`
///
/// Shape B: assignment tail / bare mut-index call
///   `(let _ := VALUE; CALL)` where CALL is a mutable-index call
///   → `(do let _ := VALUE; let _imut_K ← CALL; ok ())`
///
/// Returns true only when EVERY mutable-index marker in the body is in a
/// supported shape and has been successfully rewritten. Returns false when any
/// unsupported occurrence remains (e.g. revoke_mut's chained `.revoke()` call),
/// keeping the function opaque via the conditional guard in fun_emit.rs.
pub(crate) fn desugar_index_mut_vec(body: &mut String) -> bool {
    const MARKERS: &[&str] = &[
        "(alloc.vec.IndexMutVec.index_mut ",
        "(alloc.vec.Vec.index_mut_usize ",
    ];

    if !MARKERS.iter().any(|m| body.contains(m)) {
        return false;
    }

    let mut imut_ctr = 0u32;
    let mut changed = false;

    // --- Shape A1: (core.option.Option.map T _ OPTION_EXPR (fun (PARAM : TYPE) => CALL.N)) ---
    let map_prefix = "(core.option.Option.map ";
    let mut pos = 0;
    loop {
        let Some(rel) = body[pos..].find(map_prefix) else { break };
        let map_start = pos + rel;

        let Some(map_end) = match_paren_bytes(body.as_bytes(), map_start) else {
            pos = map_start + 1;
            continue;
        };

        let map_span = body[map_start..=map_end].to_string();

        // Only process if this Option.map contains one of our markers
        if !MARKERS.iter().any(|m| map_span.contains(m)) {
            pos = map_end + 1;
            continue;
        }

        // Locate the (fun ( closure and the marker position
        let Some(fun_rel) = map_span.find("(fun (") else {
            pos = map_end + 1;
            continue;
        };
        // Marker must be inside the closure, not in OPTION_EXPR
        let marker_in_span = MARKERS.iter().filter_map(|m| map_span.find(m)).min();
        let Some(marker_rel) = marker_in_span else {
            pos = map_end + 1;
            continue;
        };
        if marker_rel < fun_rel {
            // Marker is in OPTION_EXPR, not in closure body — skip
            pos = map_end + 1;
            continue;
        }

        // Parse the closure: (fun (PARAM : TYPE) => BODY)
        let fun_abs = map_start + fun_rel;
        let Some(fun_close) = match_paren_bytes(body.as_bytes(), fun_abs) else {
            pos = map_end + 1;
            continue;
        };
        let fun_span = &map_span[fun_rel..fun_rel + (fun_close - fun_abs) + 1];
        // fun_span is "(fun (PARAM : TYPE) => BODY)"
        let Some(arrow_pos) = fun_span.find(") => ") else {
            pos = map_end + 1;
            continue;
        };
        // param_str is "PARAM : TYPE"
        let param_str = &fun_span[6..arrow_pos]; // skip "(fun ("
        let param_name = if let Some(c) = param_str.find(" : ") {
            &param_str[..c]
        } else {
            param_str.trim()
        };

        // Closure body is after ") => " and before the final ")"
        let closure_body = fun_span[arrow_pos + 5..fun_span.len() - 1].trim();

        // Closure body must be exactly "CALL.DIGITS"
        let marker_match = MARKERS.iter().find(|m| closure_body.starts_with(*m));
        let Some(_) = marker_match else {
            pos = map_end + 1;
            continue;
        };
        let call_bytes = closure_body.as_bytes();
        let Some(call_close_rel) = match_paren_bytes(call_bytes, 0) else {
            pos = map_end + 1;
            continue;
        };
        let call_expr = &closure_body[..=call_close_rel];
        let after_call = &closure_body[call_close_rel + 1..];
        if !after_call.starts_with('.') {
            pos = map_end + 1;
            continue;
        }
        let proj_str = &after_call[1..];
        let proj_len = proj_str
            .find(|c: char| !c.is_ascii_digit())
            .unwrap_or(proj_str.len());
        if proj_len == 0 || !proj_str[proj_len..].trim().is_empty() {
            pos = map_end + 1;
            continue;
        }
        let proj = &proj_str[..proj_len];

        // Parse OPTION_EXPR: after "map_prefix + T + _ ", take next paren expression
        let after_prefix = &map_span[map_prefix.len()..];
        // Skip T token
        let t_end = if after_prefix.starts_with('(') {
            match_paren_bytes(after_prefix.as_bytes(), 0)
                .map(|e| e + 1)
                .unwrap_or(0)
        } else {
            after_prefix.find(' ').unwrap_or(after_prefix.len())
        };
        let after_t = &after_prefix[t_end..];
        let after_t_trimmed = after_t.trim_start_matches(' ');
        if !after_t_trimmed.starts_with("_ ") {
            pos = map_end + 1;
            continue;
        }
        let after_us = &after_t_trimmed[2..]; // skip "_ "
        if !after_us.starts_with('(') {
            pos = map_end + 1;
            continue;
        }
        let Some(opt_end_rel) = match_paren_bytes(after_us.as_bytes(), 0) else {
            pos = map_end + 1;
            continue;
        };
        let option_expr = &after_us[..=opt_end_rel];

        // Pick a unique bind variable
        let mut bind_var = format!("_imut_{imut_ctr}");
        while body.contains(&bind_var) {
            imut_ctr += 1;
            bind_var = format!("_imut_{imut_ctr}");
        }

        let replacement = format!(
            "(match {option_expr} with\n | .none => ok (.none)\n | .some {param_name} => do\n   let {bind_var} \u{2190} {call_expr}\n   ok (.some {bind_var}.{proj}))"
        );

        body.replace_range(map_start..=map_end, &replacement);
        imut_ctr += 1;
        changed = true;
        pos = map_start + replacement.len();
    }

    // --- Shape B: (let _ := VALUE; CALL) where CALL is a mutable-index marker ---
    let let_prefix = "(let _ := ";
    let mut pos = 0;
    loop {
        let Some(rel) = body[pos..].find(let_prefix) else { break };
        let let_start = pos + rel;

        let Some(outer_end) = match_paren_bytes(body.as_bytes(), let_start) else {
            pos = let_start + 1;
            continue;
        };

        let outer_span = body[let_start..=outer_end].to_string();
        if !MARKERS.iter().any(|m| outer_span.contains(m)) {
            pos = outer_end + 1;
            continue;
        }

        // Parse inner: strip "(let _ := " prefix and trailing ")"
        let inner = &outer_span[let_prefix.len()..outer_span.len() - 1];

        // Find "; MARKER" where MARKER starts the call expression
        let semi_pos = MARKERS
            .iter()
            .filter_map(|m| inner.find(&format!("; {m}")))
            .min();
        let Some(sp) = semi_pos else {
            pos = outer_end + 1;
            continue;
        };
        let value_str = &inner[..sp];
        let call_part = &inner[sp + 2..]; // skip "; "

        // Verify call_part starts with a marker
        if !MARKERS.iter().any(|m| call_part.starts_with(m)) {
            pos = outer_end + 1;
            continue;
        }

        let call_bytes = call_part.as_bytes();
        let Some(call_close_rel) = match_paren_bytes(call_bytes, 0) else {
            pos = outer_end + 1;
            continue;
        };
        let call_expr = &call_part[..=call_close_rel];

        // Nothing after CALL inside the outer let expression
        if !call_part[call_close_rel + 1..].trim().is_empty() {
            pos = outer_end + 1;
            continue;
        }

        // Pick a unique bind variable
        let mut bind_var = format!("_imut_{imut_ctr}");
        while body.contains(&bind_var) {
            imut_ctr += 1;
            bind_var = format!("_imut_{imut_ctr}");
        }

        let replacement = format!(
            "(do\n  let _ := {value_str}\n  let {bind_var} \u{2190} {call_expr}\n  ok ())"
        );

        body.replace_range(let_start..=outer_end, &replacement);
        imut_ctr += 1;
        changed = true;
        pos = let_start + replacement.len();
    }

    // --- Shape C: (OuterCall ... (MARKER ...).N ...) → (OuterCall ... (← (MARKER ...)).N ...)
    // Handles IndexMutVec nested as argument to another call with .N projection.
    // Lean 4 do-notation lifts ← in any expression position inside a do block.
    for marker in MARKERS {
        let mut scan = 0;
        loop {
            let Some(rel) = body[scan..].find(marker) else { break };
            let abs = scan + rel;

            if abs >= 4 && body[..abs].ends_with("(\u{2190} ") {
                scan = abs + marker.len();
                continue;
            }
            if abs >= 3 && body[..abs].ends_with("\u{2190} ") {
                scan = abs + marker.len();
                continue;
            }

            let Some(close) = match_paren_bytes(body.as_bytes(), abs) else {
                scan = abs + 1;
                continue;
            };

            let after_close = &body[close + 1..];
            if after_close.starts_with('.')
                && after_close[1..]
                    .chars()
                    .next()
                    .is_some_and(|c| c.is_ascii_digit())
            {
                body.insert_str(abs + 1, "\u{2190} ");
                changed = true;
                scan = abs + marker.len() + 4;
            } else {
                scan = close + 1;
            }
        }
    }

    // Final check: any UNBOUND markers remaining?
    // Bound markers are preceded by "← " (space-arrow-space).
    // Unbound markers mean an unsupported shape remains → keep opaque.
    // Use both paren-prefixed markers AND bare markers (the IR emitter may produce
    // `(← alloc.vec.IndexMutVec.index_mut ...)` where the leading `(` wraps `←`,
    // so the paren-prefixed marker doesn't match).
    let bare_markers: &[&str] = &[
        "alloc.vec.IndexMutVec.index_mut ",
        "alloc.vec.Vec.index_mut_usize ",
    ];
    let mut any_marker_present = false;
    for marker in bare_markers {
        let mut scan = 0;
        while let Some(rel) = body[scan..].find(marker) {
            any_marker_present = true;
            let abs = scan + rel;
            let prefix = &body[..abs];
            let is_bound = prefix.ends_with("\u{2190} ")
                || prefix.ends_with("\u{2190} (")
                || prefix.ends_with("(\u{2190} ")
                || prefix.ends_with("(\u{2190} (");
            if !is_bound {
                return false;
            }
            scan = abs + marker.len();
        }
    }

    changed || any_marker_present
}

/// Desugar `if (← (core.slice.binary_search ...)) then/else` into `match ... Ok/Err`.
///
/// `binary_search` returns `Result (core.result.Result Usize Usize)`, not `Bool`.
/// Using it in an `if` condition is a type error. The `Ok(idx)` variant means "found at
/// index", `Err(idx)` means "not found, would insert at index".
///
/// Pattern:
///   if (← (core.slice.binary_search T slice key)) then\n  do\n    THEN\nelse\n  do\n    ELSE
/// Fix:
///   match (← (core.slice.binary_search T slice key)) with
///     | core.result.Result.Ok IDX_VAR => do\n    THEN
///     | core.result.Result.Err _ => do\n    ELSE
pub(crate) fn desugar_binary_search_if(body: &mut String) -> bool {
    let needles = &[
        "if (\u{2190} (core.slice.binary_search ",
        "if (\u{2190} (core.slice.binary_search_by_key ",
    ];
    let (needle, if_start) = needles.iter()
        .filter_map(|n| body.find(n).map(|pos| (*n, pos)))
        .min_by_key(|(_, pos)| *pos)
        .unwrap_or(("", 0));
    if needle.is_empty() {
        return false;
    }
    let after_needle = if_start + needle.len();
    let rest = &body[after_needle..];
    let Some(then_rel) = rest.find(")) then") else {
        return false;
    };
    let then_abs = after_needle + then_rel + ")) then".len();

    let body_after_then = &body[then_abs..];
    let Some(else_rel) = body_after_then.find("\nelse") else {
        return false;
    };
    let else_abs = then_abs + else_rel;

    // Keep the opening paren: "if (← ..." → "match (← ..." (strip "if " not "if (")
    let bs_call = body[if_start + "if ".len()..after_needle + then_rel + "))".len()].to_string();
    let then_body = body[then_abs..else_abs].to_string();
    let full_context = &body[..else_abs];
    let idx_var = find_unbound_local_in_vec_op(&then_body, full_context).unwrap_or_else(|| "bs_idx".to_string());
    // Strip "\nelse" prefix from the else portion — keep only the body after "else"
    let else_rest = &body[else_abs..];
    let else_body = else_rest.strip_prefix("\nelse").unwrap_or(else_rest);

    let replacement = format!(
        "match {} with\n  | core.result.Result.Ok {idx_var} =>{}\n  | core.result.Result.Err _ =>{}",
        bs_call,
        then_body,
        else_body,
    );

    *body = format!("{}{}", &body[..if_start], replacement);
    true
}

fn find_unbound_local_in_vec_op(text: &str, full_context: &str) -> Option<String> {
    // Strategy 1: look for local_N as index arg in known patterns
    let re_patterns = [
        "alloc.vec.Vec.remove ",
        "alloc.vec.Vec.insert ",
        "Vec.remove ",
        "Vec.insert ",
    ];
    for pat in &re_patterns {
        if let Some(pos) = text.find(pat) {
            let after = &text[pos + pat.len()..];
            let tokens: Vec<&str> = after.split_whitespace().collect();
            if tokens.len() >= 4 {
                let candidate = tokens[3].trim_end_matches(')');
                if candidate.starts_with("local_") {
                    let let_def = format!("let {} ", candidate);
                    let let_bind = format!("let {} \u{2190}", candidate);
                    if !full_context.contains(&let_def) && !full_context.contains(&let_bind) {
                        return Some(candidate.to_string());
                    }
                }
            }
        }
    }
    // Strategy 2: find any local_N in then-branch not defined anywhere in full context
    for word in text.split(|c: char| !c.is_alphanumeric() && c != '_') {
        if word.starts_with("local_") && word.len() > 6 && word[6..].chars().all(|c| c.is_ascii_digit()) {
            let let_def = format!("let {} ", word);
            let let_bind = format!("let {} \u{2190}", word);
            let param_def = format!("({} : ", word);
            let assign_def = format!("{} := ", word);
            if !full_context.contains(&let_def) && !full_context.contains(&let_bind)
                && !full_context.contains(&param_def) && !full_context.contains(&assign_def) {
                return Some(word.to_string());
            }
        }
    }
    None
}

/// Desugar loop Vec accumulator pattern: thread a locally-created Vec through a
/// `let rec go_N` loop that pushes to it.
///
/// Before:
///   let VEC ← (alloc.vec.Vec.new T)
///   ...
///   let rec go_0 (COUNTER : Usize) : Result Usize := do
///     if ... then do
///       [let _ ←] (alloc.vec.Vec.push T Global VEC ELEM)
///       ...
///       go_0 COUNTER
///     else do
///       ok COUNTER
///   partial_fixpoint
///   let COUNTER ← go_0 COUNTER
///   ok VEC
///
/// After:
///   let VEC ← (alloc.vec.Vec.new T)
///   ...
///   let rec go_0 (COUNTER : Usize) (VEC : alloc.vec.Vec T) : Result (Usize × alloc.vec.Vec T) := do
///     if ... then do
///       let VEC ← (alloc.vec.Vec.push T Global VEC ELEM)
///       ...
///       go_0 COUNTER VEC
///     else do
///       ok (COUNTER, VEC)
///   partial_fixpoint
///   let (COUNTER, VEC) ← go_0 COUNTER VEC
///   ok VEC
pub(crate) fn desugar_loop_vec_accumulator(body: &mut String) -> bool {
    if !body.contains("alloc.vec.Vec.push") || !body.contains("let rec go_") {
        return false;
    }

    let vec_new_needle = "\u{2190} (alloc.vec.Vec.new ";
    let Some(vec_new_pos) = body.find(vec_new_needle) else {
        return false;
    };
    let before_arrow = &body[..vec_new_pos];
    let Some(let_pos) = before_arrow.rfind("let ") else {
        return false;
    };
    let vec_var = before_arrow[let_pos + 4..].trim().to_string();
    if vec_var.is_empty() || !vec_var.starts_with("local_") {
        return false;
    }

    // Extract element type T from `alloc.vec.Vec.new T)` — handle parenthesized types
    // like `(U64 × types.capability.Capability)` using paren matching.
    let type_start = vec_new_pos + vec_new_needle.len();
    let type_end = {
        let bytes = body.as_bytes();
        let mut depth = 0i32;
        let mut end = type_start;
        // The closing `)` for Vec.new matches the `(` from `(alloc.vec.Vec.new T)`.
        // We need to find where the type argument ends, which is the `)` that closes
        // the `(alloc.vec.Vec.new ...` call — at depth 0.
        while end < bytes.len() {
            match bytes[end] {
                b'(' => depth += 1,
                b')' => {
                    if depth == 0 {
                        break;
                    }
                    depth -= 1;
                }
                _ => {}
            }
            end += 1;
        }
        if end >= bytes.len() {
            return false;
        }
        end - type_start
    };
    let elem_type = body[type_start..type_start + type_end].trim().to_string();
    if elem_type.is_empty() {
        return false;
    }

    let Some(loop_start) = body.find("let rec go_") else {
        return false;
    };

    let push_pattern = format!("alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    let push_pattern2 = format!("alloc.vec.Vec.push {elem_type} Global {vec_var})");
    let loop_body = &body[loop_start..];
    if !loop_body.contains(&push_pattern) && !loop_body.contains(&push_pattern2) {
        return false;
    }

    let ok_vec = format!("ok {vec_var}");
    if !body.trim_end().ends_with(&ok_vec) {
        return false;
    }

    // Parse loop header: `let rec GO (PARAMS) : Result RET := do`
    let header_end_needle = ":= do";
    let Some(header_rel_end) = loop_body.find(header_end_needle) else {
        return false;
    };
    let header = &loop_body[..header_rel_end];

    let go_name_start = "let rec ".len();
    let Some(go_space) = header[go_name_start..].find(' ') else {
        return false;
    };
    let go_name_end = go_name_start + go_space;
    let go_name = header[go_name_start..go_name_end].to_string();

    let Some(result_pos) = header.find(": Result ") else {
        return false;
    };
    let params_str = header[go_name_end..result_pos].trim().to_string();
    let ret_type_str = header[result_pos + ": Result ".len()..].trim().to_string();
    if ret_type_str.is_empty() {
        return false;
    }

    let counter_names: Vec<String> = params_str
        .split('(')
        .filter(|s| s.contains(':'))
        .filter_map(|s| {
            let name = s.split(':').next()?.trim().to_string();
            if name.is_empty() {
                None
            } else {
                // Strip trailing ')' if present
                Some(name.trim_end_matches(')').trim().to_string())
            }
        })
        .collect();
    if counter_names.is_empty() {
        return false;
    }

    let vec_type = format!("alloc.vec.Vec {elem_type}");

    let mut result = body.clone();

    // Modify loop header: add Vec param and tuple return type
    let old_header_suffix = format!(
        "{params_str} : Result {ret_type_str} {header_end_needle}"
    );
    let new_header_suffix = format!(
        "{params_str} ({vec_var} : {vec_type}) : Result ({ret_type_str} \u{00d7} {vec_type}) {header_end_needle}"
    );
    if !result.contains(&old_header_suffix) {
        return false;
    }
    result = result.replacen(&old_header_suffix, &new_header_suffix, 1);

    // Rebind Vec.push: `let _ ← (Vec.push ...)` → `let VEC ← (Vec.push ...)`
    let let_discard = format!("let _ \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    let let_rebind = format!("let {vec_var} \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    result = result.replace(&let_discard, &let_rebind);

    // Bare push and conditional push handling.
    // Two passes: first handle if-else and match conditionals, then simple bare pushes.
    let bare_push = format!("(alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    let bare_push_let = format!("let {vec_var} \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");

    // Pass A: Restructure if-else conditional pushes.
    // Pattern: `if COND then\n  do\n    (Vec.push ...)\nelse\n  do\n    ok ()`
    // → `let VEC ← if COND then\n  (Vec.push ...)\nelse\n  ok VEC`
    {
        let lines: Vec<String> = result.lines().map(|l| l.to_string()).collect();
        let mut new_lines: Vec<String> = Vec::new();
        let mut i = 0;
        while i < lines.len() {
            let trimmed = lines[i].trim();
            // Detect if-line: ends with "then"
            if trimmed.ends_with("then") && i + 2 < lines.len() {
                let do_line = lines[i + 1].trim();
                let push_line = lines[i + 2].trim();
                if do_line == "do" && push_line.starts_with(&bare_push) {
                    // Found if/do/push — look for else/do/ok()
                    let mut else_idx = i + 3;
                    while else_idx < lines.len()
                        && !lines[else_idx].trim().starts_with("else")
                        && !lines[else_idx].trim().starts_with("let ")
                        && !lines[else_idx].trim().starts_with("go_")
                    {
                        else_idx += 1;
                    }
                    if else_idx + 2 < lines.len()
                        && lines[else_idx].trim() == "else"
                        && lines[else_idx + 1].trim() == "do"
                        && lines[else_idx + 2].trim() == "ok ()"
                    {
                        let if_indent = &lines[i][..lines[i].len() - trimmed.len()];
                        let cond = trimmed.strip_suffix(" then").unwrap_or(trimmed);
                        new_lines.push(format!(
                            "{if_indent}let {vec_var} \u{2190} {cond} then"
                        ));
                        new_lines.push(format!("{if_indent}  {push_line}"));
                        new_lines.push(format!("{if_indent}else"));
                        new_lines.push(format!("{if_indent}  ok {vec_var}"));
                        i = else_idx + 3;
                        continue;
                    }
                }
            }
            new_lines.push(lines[i].to_string());
            i += 1;
        }
        result = new_lines.join("\n");
    }

    // Pass B: Restructure match-arm conditional pushes.
    // Rebind `let _ ← Vec.push` first, then fix match arms.
    let let_discard_b = format!("let _ \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    let let_rebind_b = format!("let {vec_var} \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");
    result = result.replace(&let_discard_b, &let_rebind_b);

    // Now fix match arms: `| .some VAL => do\n  let VEC ← Vec.push\n  ok ()`
    // → `| .some VAL =>\n  Vec.push`
    // and `| .none => ok ()` → `| .none => ok VEC`
    {
        let push_let_pat = format!("let {vec_var} \u{2190} (alloc.vec.Vec.push {elem_type} Global {vec_var} ");
        let lines: Vec<String> = result.lines().map(|l| l.to_string()).collect();
        let mut new_lines: Vec<String> = Vec::new();
        let mut i = 0;
        let in_loop = result.contains("let rec go_");
        while i < lines.len() {
            let trimmed = lines[i].trim();
            // Detect `let VEC ← Vec.push` followed by `ok ()` in a match-arm do-block
            if trimmed.starts_with(&push_let_pat)
                && i + 1 < lines.len()
                && lines[i + 1].trim() == "ok ()"
                && i >= 1
                && new_lines
                    .last()
                    .is_some_and(|l| l.trim() == "do" || l.trim().ends_with("=> do"))
            {
                // Pop or fix the `do` line — remove trailing ` do` from match arm header
                if let Some(last) = new_lines.last_mut() {
                    let lt = last.trim();
                    if lt == "do" {
                        new_lines.pop();
                    } else if lt.ends_with(" do") {
                        let stripped = last.trim_end();
                        let without_do = &stripped[..stripped.len() - 3]; // strip " do"
                        *last = without_do.to_string();
                    }
                }
                // Prepend `let VEC ←` to the enclosing match line
                for j in (0..new_lines.len()).rev() {
                    if new_lines[j].trim().starts_with("match ") {
                        let m_indent =
                            &new_lines[j][..new_lines[j].len() - new_lines[j].trim().len()];
                        let m_trimmed = new_lines[j].trim();
                        new_lines[j] =
                            format!("{m_indent}let {vec_var} \u{2190} {m_trimmed}");
                        break;
                    }
                }
                // Emit just the push call (strip `let VEC ←` prefix)
                let let_arrow = format!("let {vec_var} \u{2190} ");
                let indent = &lines[i][..lines[i].len() - trimmed.len()];
                let push_call = &trimmed[let_arrow.len()..];
                new_lines.push(format!("{indent}{push_call}"));
                i += 2; // skip ok ()
                continue;
            }
            // Fix `=> ok ()` → `=> ok VEC` inside loop body match arms
            if in_loop && trimmed.ends_with("=> ok ()") && trimmed.starts_with("| .none") {
                let indent = &lines[i][..lines[i].len() - trimmed.len()];
                let fixed = trimmed.replace("=> ok ()", &format!("=> ok {vec_var}"));
                new_lines.push(format!("{indent}{fixed}"));
                i += 1;
                continue;
            }
            new_lines.push(lines[i].to_string());
            i += 1;
        }
        result = new_lines.join("\n");
    }

    // Pass C: Remaining bare pushes at statement level (not in conditionals)
    // Skip pushes that are inside if-expressions (prev line ends with "then" or "else")
    {
        let lines: Vec<String> = result.lines().map(|l| l.to_string()).collect();
        let mut new_lines: Vec<String> = Vec::new();
        for (idx, line) in lines.iter().enumerate() {
            let trimmed = line.trim();
            if trimmed.starts_with(&bare_push) {
                let prev_trimmed = if idx > 0 {
                    lines[idx - 1].trim()
                } else {
                    ""
                };
                let in_if_expr = prev_trimmed.ends_with("then")
                    || prev_trimmed == "else"
                    || prev_trimmed.ends_with("=>");
                if in_if_expr {
                    new_lines.push(line.to_string());
                } else {
                    let indent = &line[..line.len() - trimmed.len()];
                    new_lines.push(format!(
                        "{indent}{bare_push_let}{}",
                        &trimmed[bare_push.len()..]
                    ));
                }
            } else {
                new_lines.push(line.to_string());
            }
        }
        result = new_lines.join("\n");
    }

    // Append Vec to recursive calls: `go_N args` → `go_N args VEC`
    let definition_prefix = format!("let rec {go_name} ");
    let call_site_prefix = format!("\u{2190} {go_name} ");
    {
        let rec_call_prefix = format!("{go_name} ");
        let mut new_lines: Vec<String> = Vec::new();
        for line in result.lines() {
            let trimmed = line.trim();
            if trimmed.starts_with(&rec_call_prefix)
                && !line.contains(&definition_prefix)
                && !line.contains(&call_site_prefix)
            {
                new_lines.push(format!("{line} {vec_var}"));
            } else {
                new_lines.push(line.to_string());
            }
        }
        result = new_lines.join("\n");
    }

    // Change loop else return: `ok COUNTER` → `ok (COUNTER, VEC)`
    {
        let pf_needle = "partial_fixpoint";
        let (old_ok, new_ok) = if counter_names.len() == 1 {
            (
                format!("ok {}", counter_names[0]),
                format!("ok ({}, {vec_var})", counter_names[0]),
            )
        } else {
            let counter_list = counter_names.join(", ");
            (
                format!("ok ({counter_list})"),
                format!("ok ({counter_list}, {vec_var})"),
            )
        };
        let mut new_lines: Vec<String> = Vec::new();
        let mut in_loop = false;
        let mut past_loop = false;
        for line in result.lines() {
            if line.contains("let rec go_") {
                in_loop = true;
            }
            if line.trim() == pf_needle {
                past_loop = true;
            }
            let trimmed = line.trim();
            if in_loop && !past_loop && trimmed == old_ok {
                let indent = &line[..line.len() - trimmed.len()];
                new_lines.push(format!("{indent}{new_ok}"));
            } else {
                new_lines.push(line.to_string());
            }
        }
        result = new_lines.join("\n");
    }

    // Change call site: `let COUNTER ← go_N COUNTER` → `let (COUNTER, VEC) ← go_N COUNTER VEC`
    if counter_names.len() == 1 {
        let old_call = format!(
            "let {} \u{2190} {go_name} {}",
            counter_names[0], counter_names[0]
        );
        let new_call = format!(
            "let ({}, {vec_var}) \u{2190} {go_name} {} {vec_var}",
            counter_names[0], counter_names[0]
        );
        result = result.replacen(&old_call, &new_call, 1);
    } else {
        let counter_list = counter_names.join(", ");
        let counter_args = counter_names.join(" ");
        let old_call = format!(
            "let ({counter_list}) \u{2190} {go_name} {counter_args}"
        );
        let new_call = format!(
            "let ({counter_list}, {vec_var}) \u{2190} {go_name} {counter_args} {vec_var}"
        );
        result = result.replacen(&old_call, &new_call, 1);
    }

    if result == *body {
        return false;
    }

    *body = result;
    true
}

/// Wrap `(KernelState.revocation_mut EXPR)` in monadic bind `(← (KernelState.revocation_mut EXPR))`.
pub(crate) fn desugar_revocation_mut_bind(body: &mut String) -> bool {
    let needle = "(state.kernel.KernelState.revocation_mut ";
    let bind_prefix = "(\u{2190} (state.kernel.KernelState.revocation_mut ";
    if !body.contains(needle) || body.contains(bind_prefix) {
        return false;
    }
    let mut changed = false;
    let mut result = body.clone();
    let mut search_from = 0;
    while let Some(rel_pos) = result[search_from..].find(needle) {
        let pos = search_from + rel_pos;
        if let Some(close) = match_paren_bytes(result.as_bytes(), pos) {
            let call = result[pos..close + 1].to_string();
            let wrapped = format!("(\u{2190} {call})");
            result = format!("{}{}{}", &result[..pos], wrapped, &result[close + 1..]);
            search_from = pos + wrapped.len();
            changed = true;
        } else {
            break;
        }
    }
    if changed {
        *body = result;
    }
    changed
}

/// Desugar binary_search + Vec.insert/remove patterns for unit-returning functions.
///
/// Pattern A (insert_cap_sorted, insert_freed_addr, grant_cap):
///   match (← (binary_search ...)) with | Ok _ => () | Err pos => (Vec.insert ...)
/// → match ... with | Ok _ => ok () | Err pos => do let _ ← Vec.insert ...; ok ()
///
/// Pattern B (remove_cap_sorted):
///   match ... with | Ok idx => do (Vec.remove ...) | Err _ => do ok ()
/// → match ... with | Ok idx => do let _ ← Vec.remove ...; ok () | Err _ => do ok ()
pub(crate) fn desugar_binary_search_unit(body: &mut String) -> bool {
    if !body.contains("core.slice.binary_search ") {
        return false;
    }
    let mut changed = false;

    // Pattern A: bare `=> ()` after Ok in binary_search match
    if body.contains("=> ()") && body.contains("core.slice.binary_search ") {
        let result = body.replace(
            "=> ()",
            "=> ok ()",
        );
        if result != *body {
            *body = result;
            changed = true;
        }
    }

    // Pattern A continued: bare `(alloc.vec.Vec.insert ...)` in Err arm — wrap in do+bind
    if body.contains("alloc.vec.Vec.insert") && !body.contains("let _ ← (alloc.vec.Vec.insert")
        && let Some(arm_start) = body.find("core.result.Result.Err ") {
            let after_arm = &body[arm_start..];
            if let Some(arrow_pos) = after_arm.find("=> ") {
                let after_arrow = &after_arm[arrow_pos + 3..];
                if after_arrow.starts_with("(alloc.vec.Vec.insert ")
                    && let Some(close) = match_paren_bytes(after_arrow.as_bytes(), 0) {
                        let insert_call = &after_arrow[..close + 1];
                        let replacement = format!("do\n    let _ ← {insert_call}\n    ok ()");
                        let full_old = after_arm[..arrow_pos + 3 + close + 1].to_string();
                        let full_new = format!(
                            "{}{}",
                            &after_arm[..arrow_pos + 3],
                            replacement
                        );
                        *body = body.replacen(&full_old, &full_new, 1);
                        changed = true;
                    }
            }
        }

    // Pattern B: bare `(alloc.vec.Vec.remove ...)` in Ok arm — wrap in bind.
    // Only match when the remove call is NOT already preceded by `←` (already bound).
    if body.contains("alloc.vec.Vec.remove") {
        let old_pat = body.clone();
        if let Some(ok_pos) = old_pat.find("core.result.Result.Ok ") {
            let after_ok = &old_pat[ok_pos..];
            if let Some(remove_pos) = after_ok.find("(alloc.vec.Vec.remove ") {
                let abs_pos = ok_pos + remove_pos;
                let prefix = old_pat[..abs_pos].trim_end();
                let already_bound = prefix.ends_with("\u{2190}");
                if !already_bound
                    && let Some(close) = match_paren_bytes(old_pat.as_bytes(), abs_pos) {
                        let remove_call = &old_pat[abs_pos..close + 1];
                        let replacement = format!("let _ ← {remove_call}\n    ok ()");
                        *body = body.replacen(remove_call, &replacement, 1);
                        changed = true;
                    }
            }
        }
    }

    changed
}
