use super::*;

// ---------------------------------------------------------------------------
// Unit tests for issue #273 desugar passes
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests_issue_273 {
    use super::*;

    // --- desugar_get_mut_bind + fix_get_mut_close_paren (F1) ---

    #[test]
    fn get_mut_bind_std_namespace_inserts_arrow_and_closes_paren() {
        // Note: desugar_get_mut_bind operates on raw body text.
        // map_std_callee (which rewrites std.* → alloc.*) runs during emit_callee,
        // BEFORE post-processing passes. So in production the body already uses alloc.*
        // by the time this pass runs. In this unit test we exercise the std.* needle path
        // directly — the output keeps std.* (no map_std_callee in unit test scope).
        let mut body =
            "match (std.collections.BTreeMap.get_mut self.resources addr) with\n  | .some x => ok x\n  | .none => ok .none".to_string();
        let changed = desugar_get_mut_bind(&mut body);
        assert!(changed, "should return true when pattern is found");
        assert!(
            body.contains("match (← (std.collections.BTreeMap.get_mut self.resources addr)) with"),
            "body after fix: {body}"
        );
    }

    #[test]
    fn get_mut_bind_alloc_namespace_inserts_arrow_and_closes_paren() {
        let mut body =
            "match (alloc.collections.btree.map.BTreeMap.get_mut self.pages k) with\n  | .some v => ok v\n  | .none => ok .none".to_string();
        let changed = desugar_get_mut_bind(&mut body);
        assert!(changed, "should return true for alloc namespace");
        assert!(
            body.contains(
                "match (← (alloc.collections.btree.map.BTreeMap.get_mut self.pages k)) with"
            ),
            "body after fix: {body}"
        );
    }

    #[test]
    fn get_mut_bind_no_op_when_pattern_absent() {
        let mut body = "match x with | .some v => ok v | .none => ok .none".to_string();
        let original = body.clone();
        let changed = desugar_get_mut_bind(&mut body);
        assert!(
            !changed,
            "should return false when BTreeMap.get_mut is absent"
        );
        assert_eq!(body, original);
    }

    #[test]
    fn get_mut_bind_already_has_bind_is_idempotent() {
        // If the body already has `← (`, neither std nor alloc needles match
        let mut body =
            "match (← (alloc.collections.btree.map.BTreeMap.get_mut self.resources addr)) with\n  | .some x => ok x\n  | .none => ok .none".to_string();
        let original = body.clone();
        let changed = desugar_get_mut_bind(&mut body);
        assert!(!changed, "already-bound call should not be re-bound");
        assert_eq!(body, original);
    }

    #[test]
    fn fix_get_mut_close_paren_inserts_after_args() {
        // Simulated body after prefix replacement (std namespace):
        let input =
            "match (← (std.collections.BTreeMap.get_mut self.r addr) with | .some x => ok x"
                .to_string();
        let output = fix_get_mut_close_paren(&input);
        assert!(
            output.contains("get_mut self.r addr)) with"),
            "should add closing paren after args: {output}"
        );
    }

    #[test]
    fn fix_get_mut_close_paren_inserts_after_args_alloc() {
        let input = "match (← (alloc.collections.btree.map.BTreeMap.get_mut self.pages k) with | .some v => ok v".to_string();
        let output = fix_get_mut_close_paren(&input);
        assert!(
            output.contains("get_mut self.pages k)) with"),
            "should add closing paren for alloc namespace: {output}"
        );
    }

    // --- desugar_free_mut_dup_arm (F2) ---

    #[test]
    fn dup_arm_replaces_second_some_with_none() {
        let mut body = "| .some local_38 => ok .ok | .some _ => ok .err".to_string();
        let changed = desugar_free_mut_dup_arm(&mut body);
        assert!(
            changed,
            "should return true when duplicate some arm is present"
        );
        assert!(
            body.contains("| .none => ok .err"),
            "duplicate some arm should become none: {body}"
        );
        assert!(
            body.contains("| .some local_38 =>"),
            "named some arm should be preserved: {body}"
        );
    }

    #[test]
    fn dup_arm_no_op_without_named_some() {
        // Only wildcard some, no named `local_` — should NOT fire (could be valid single arm)
        let mut body = "| .some _ => ok .none".to_string();
        let original = body.clone();
        let changed = desugar_free_mut_dup_arm(&mut body);
        assert!(!changed, "should not fire without a named .some local_ arm");
        assert_eq!(body, original);
    }

    #[test]
    fn dup_arm_no_op_without_wildcard_some() {
        let mut body = "| .some local_5 => ok .ok | .none => ok .err".to_string();
        let original = body.clone();
        let changed = desugar_free_mut_dup_arm(&mut body);
        assert!(
            !changed,
            "should not fire when no wildcard .some _ arm is present"
        );
        assert_eq!(body, original);
    }

    // --- desugar_index_assign_expr (F4) ---

    #[test]
    fn index_assign_expr_basic_rewrite() {
        let mut body = "(let _ := val; (local_47[local_23]))".to_string();
        let changed = desugar_index_assign_expr(&mut body);
        assert!(changed, "should return true for index-assign pattern");
        assert_eq!(body, "ok ()");
    }

    #[test]
    fn index_assign_expr_numeric_locals() {
        let mut body = "(let _ := 42#u8; (local_0[local_1]))".to_string();
        let changed = desugar_index_assign_expr(&mut body);
        assert!(changed, "should work with numeric literals as value");
        assert_eq!(body, "ok ()");
    }

    #[test]
    fn index_assign_expr_no_match_without_suffix() {
        // Missing "))": should not rewrite
        let mut body = "(let _ := val; (local_47[local_23])".to_string();
        let original = body.clone();
        let changed = desugar_index_assign_expr(&mut body);
        assert!(
            !changed,
            "should not rewrite when double-close-paren is absent"
        );
        assert_eq!(body, original);
    }

    #[test]
    fn index_assign_expr_no_match_without_bracket() {
        // No `[` in (local_...) part: should not rewrite
        let mut body = "(let _ := val; (local_47))".to_string();
        let original = body.clone();
        let changed = desugar_index_assign_expr(&mut body);
        assert!(
            !changed,
            "should not rewrite when no bracket access present"
        );
        assert_eq!(body, original);
    }

    #[test]
    fn index_assign_expr_no_op_when_absent() {
        let mut body = "ok ()".to_string();
        let original = body.clone();
        let changed = desugar_index_assign_expr(&mut body);
        assert!(!changed);
        assert_eq!(body, original);
    }

    fn adt(rust_path: &str) -> StyxType {
        StyxType::Adt {
            rust_path: rust_path.to_string(),
            type_id: None,
            generic_args: Vec::new(),
            const_args: Vec::new(),
        }
    }

    #[test]
    fn closure_param_annotation_uses_styxir_type() {
        let policy_error = adt("lion_core::types::policy::PolicyError");
        let closure = StyxExpr {
            kind: StyxExprKind::Closure {
                params: vec![StyxParam {
                    name: "arg1".to_string(),
                    ty: policy_error.clone(),
                    is_mut_self: false,
                    local_id: None,
                }],
                body: Box::new(StyxExpr::unit()),
                captures: Vec::new(),
            },
            ty: StyxType::FnPtr {
                params: vec![policy_error],
                ret: Box::new(StyxType::Unit),
            },
            span: StyxSpan::default(),
        };

        let emitted = emit_expr(&closure, &std::collections::BTreeMap::new());
        assert_eq!(
            emitted,
            "(fun (arg1 : types.policy.PolicyError) => ())"
        );
    }

    #[test]
    fn map_err_desugar_preserves_mapper_closure() {
        let mut body = "(core.result.Result.map_err types.policy.Action types.policy.PolicyError step.StepError (← (types.policy.Action.new caller target rights kind)) local_17)".to_string();
        let count = desugar_map_err(&mut body);

        assert_eq!(count, 1);
        assert!(
            body.contains(
                "| core.result.Result.Err map_err => ok (core.result.Result.Err (local_17 map_err))"
            ),
            "body after desugar: {body}"
        );
        assert!(
            !body.contains("fail .panic"),
            "standalone map_err must return a mapped inner Err: {body}"
        );
    }

    #[test]
    fn map_err_after_prior_try_is_not_misclassified_as_nested_try() {
        let mut body = "let local_69 ← (match (core.result.TryResultResultInfallible.branch U64 step.StepError (← (core.option.Option.ok_or U64 step.StepError opt err))) with | .Break v => residual | .Continue v2 => v2); (core.result.Result.map_err types.policy.Action types.policy.PolicyError step.StepError (← (types.policy.Action.new caller target rights kind)) local_17)".to_string();
        let count = desugar_map_err(&mut body);

        assert_eq!(count, 1);
        assert!(
            body.contains("(match (← (types.policy.Action.new caller target rights kind)) with"),
            "later map_err should be desugared, not stripped to Action.new: {body}"
        );
        assert!(
            body.contains("(local_17 map_err)"),
            "mapper should still be applied after an earlier try expression: {body}"
        );
    }
}
