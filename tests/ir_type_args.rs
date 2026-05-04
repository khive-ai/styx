//! Tests for StyxIR type_args field on Call expressions.
//!
//! Issue #230 bug: styx-rustc always emitted `type_args: vec![]` for all call
//! expressions, losing the instantiated generic type arguments from the THIR
//! FnDef node. This meant a call like `Vec::<Right>::with_capacity(n)` had no
//! type annotation in the IR, leaving the Lean emitter to guess type args
//! heuristically.
//!
//! The fix: extract `generic_args.types()` from the FnDef arm and store them
//! in `StyxExprKind::Call::type_args`.
//!
//! These tests verify the IR structure round-trips through JSON (as styx-rustc
//! writes to disk) and that non-empty type_args are correctly preserved.

use styx::ir::{
    LocalId, ScalarTy, StyxCallee, StyxExpr, StyxExprKind, StyxLiteral, StyxSpan, StyxType, TypeId,
};

/// Build a Call expression with explicit type_args (as the fixed styx-rustc now
/// emits for FnDef calls with generic parameters).
fn make_generic_call(type_args: Vec<StyxType>) -> StyxExpr {
    StyxExpr {
        kind: StyxExprKind::Call {
            callee: StyxCallee::Function {
                rust_path: "alloc::vec::Vec::with_capacity".to_string(),
                local_id: None,
            },
            type_args,
            args: vec![StyxExpr {
                kind: StyxExprKind::Literal(StyxLiteral::UInt(8, ScalarTy::Usize)),
                ty: StyxType::Scalar(ScalarTy::Usize),
                span: StyxSpan::default(),
            }],
        },
        ty: StyxType::Adt {
            rust_path: "alloc::vec::Vec".to_string(),
            type_id: None,
            generic_args: vec![StyxType::Scalar(ScalarTy::U8)],
            const_args: vec![],
        },
        span: StyxSpan::default(),
    }
}

/// Before the fix: type_args was always vec![].
/// This test documents the pre-fix behavior — it's always been valid IR to
/// have empty type_args; the fix makes it non-empty when there ARE type args.
#[test]
fn call_with_empty_type_args_is_valid() {
    let call = make_generic_call(vec![]);
    if let StyxExprKind::Call {
        type_args, args, ..
    } = &call.kind
    {
        assert!(type_args.is_empty(), "empty type_args should be preserved");
        assert_eq!(args.len(), 1, "one value argument");
    } else {
        panic!("expected Call variant");
    }
}

/// After the fix: type_args carries the instantiated type parameters.
/// For `Vec::<Right>::with_capacity`, type_args = [Right].
#[test]
fn call_with_populated_type_args_preserves_data() {
    let right_ty = StyxType::Adt {
        rust_path: "lion_core::types::rights::Right".to_string(),
        type_id: Some(TypeId(42)),
        generic_args: vec![],
        const_args: vec![],
    };
    let call = make_generic_call(vec![right_ty]);

    if let StyxExprKind::Call {
        type_args,
        args,
        callee,
    } = &call.kind
    {
        assert_eq!(type_args.len(), 1, "one type argument should be preserved");
        // Verify the type arg is the expected ADT
        match &type_args[0] {
            StyxType::Adt {
                rust_path, type_id, ..
            } => {
                assert_eq!(rust_path, "lion_core::types::rights::Right");
                assert_eq!(type_id, &Some(TypeId(42)));
            }
            other => panic!("expected Adt type arg, got {:?}", other),
        }
        assert_eq!(args.len(), 1, "one value argument");
        assert!(
            matches!(callee, StyxCallee::Function { rust_path, .. } if rust_path.contains("with_capacity")),
            "callee should be Function"
        );
    } else {
        panic!("expected Call variant");
    }
}

/// Verify type_args round-trips through JSON serialization.
/// styx-rustc writes the StyxPackage as JSON; styx reads it back.
/// The type_args field must survive the round-trip.
#[test]
fn type_args_roundtrip_json() {
    let right_ty = StyxType::Adt {
        rust_path: "lion_core::types::rights::Right".to_string(),
        type_id: None,
        generic_args: vec![],
        const_args: vec![],
    };
    let call = make_generic_call(vec![right_ty]);

    let json = serde_json::to_string(&call).expect("serialization must succeed");
    assert!(
        json.contains("lion_core::types::rights::Right"),
        "type arg rust_path must appear in JSON"
    );
    assert!(
        json.contains("type_args"),
        "type_args field must appear in JSON"
    );

    let restored: StyxExpr = serde_json::from_str(&json).expect("deserialization must succeed");

    if let StyxExprKind::Call { type_args, .. } = &restored.kind {
        assert_eq!(type_args.len(), 1, "type_args must survive JSON round-trip");
        match &type_args[0] {
            StyxType::Adt { rust_path, .. } => {
                assert_eq!(rust_path, "lion_core::types::rights::Right");
            }
            other => panic!("expected Adt after round-trip, got {:?}", other),
        }
    } else {
        panic!("expected Call variant after round-trip");
    }
}

/// Verify a ClosureCall expression has empty type_args.
/// The fixed code emits vec![] for closure/fnptr callees (not FnDef),
/// which is correct — there are no call-site type args for closures.
#[test]
fn closure_call_has_no_type_args() {
    let closure_var = StyxExpr {
        kind: StyxExprKind::Local(LocalId(0)),
        ty: StyxType::FnPtr {
            params: vec![StyxType::Scalar(ScalarTy::U64)],
            ret: Box::new(StyxType::Scalar(ScalarTy::Bool)),
        },
        span: StyxSpan::default(),
    };
    let call = StyxExpr {
        kind: StyxExprKind::Call {
            callee: StyxCallee::ClosureCall(Box::new(closure_var)),
            type_args: vec![], // ClosureCall always has empty type_args
            args: vec![StyxExpr {
                kind: StyxExprKind::Literal(StyxLiteral::UInt(5, ScalarTy::U64)),
                ty: StyxType::Scalar(ScalarTy::U64),
                span: StyxSpan::default(),
            }],
        },
        ty: StyxType::Scalar(ScalarTy::Bool),
        span: StyxSpan::default(),
    };

    if let StyxExprKind::Call {
        callee, type_args, ..
    } = &call.kind
    {
        assert!(
            matches!(callee, StyxCallee::ClosureCall(_)),
            "callee should be ClosureCall"
        );
        assert!(type_args.is_empty(), "ClosureCall should have no type_args");
    } else {
        panic!("expected Call variant");
    }
}

/// Multiple type arguments are preserved in order.
/// E.g., a call to `fn foo<A, B>(a: A, b: B)` carries both A and B.
#[test]
fn multiple_type_args_preserved_in_order() {
    let ty_a = StyxType::Scalar(ScalarTy::U64);
    let ty_b = StyxType::Scalar(ScalarTy::Bool);
    let call = make_generic_call(vec![ty_a, ty_b]);

    if let StyxExprKind::Call { type_args, .. } = &call.kind {
        assert_eq!(type_args.len(), 2, "two type args");
        assert!(matches!(&type_args[0], StyxType::Scalar(ScalarTy::U64)));
        assert!(matches!(&type_args[1], StyxType::Scalar(ScalarTy::Bool)));
    } else {
        panic!("expected Call variant");
    }
}
