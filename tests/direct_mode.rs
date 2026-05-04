//! Tests for the direct Rust→Lean emission mode.

use std::path::PathBuf;

use styx::emit::direct::{emit_bridge_template_direct, emit_direct};
use styx::rust_parser::{
    ParsedCrate, ParsedField, ParsedFnSig, ParsedTypeDef, ParsedTypeKind, ParsedVariant, RustType,
};

fn make_test_crate() -> ParsedCrate {
    ParsedCrate {
        types: vec![
            // A struct with fields
            ParsedTypeDef {
                name: "types.security.SecurityLevel".to_string(),
                simple_name: "SecurityLevel".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Enum(vec![
                    ParsedVariant {
                        name: "Low".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "Medium".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "High".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "Critical".to_string(),
                        fields: vec![],
                    },
                ]),
                source_file: "src/types/security.rs".to_string(),
            },
            // A struct
            ParsedTypeDef {
                name: "types.capability.Capability".to_string(),
                simple_name: "Capability".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Struct(vec![
                    ParsedField {
                        name: "id".to_string(),
                        ty: RustType::Named("u64".to_string()),
                    },
                    ParsedField {
                        name: "holder".to_string(),
                        ty: RustType::Named("u64".to_string()),
                    },
                    ParsedField {
                        name: "rights".to_string(),
                        ty: RustType::Named("Rights".to_string()),
                    },
                ]),
                source_file: "src/types/capability.rs".to_string(),
            },
            // A type alias
            ParsedTypeDef {
                name: "types.identifiers.PluginId".to_string(),
                simple_name: "PluginId".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Alias(RustType::Named("u64".to_string())),
                source_file: "src/types/identifiers.rs".to_string(),
            },
            // A generic struct
            ParsedTypeDef {
                name: "types.Queue".to_string(),
                simple_name: "Queue".to_string(),
                type_params: vec!["T".to_string()],
                kind: ParsedTypeKind::Alias(RustType::Generic(
                    "Vec".to_string(),
                    vec![RustType::Named("T".to_string())],
                )),
                source_file: "src/types/mod.rs".to_string(),
            },
        ],
        fns: vec![
            // Free function
            ParsedFnSig {
                name: "kernel_dispatch".to_string(),
                type_params: vec![],
                params: vec![
                    ("state".to_string(), RustType::Named("State".to_string())),
                    (
                        "req".to_string(),
                        RustType::Named("KernelRequest".to_string()),
                    ),
                ],
                ret_type: RustType::Named("KernelResult".to_string()),
                is_method: false,
                self_type: None,
                is_mut_self: false,
                source_file: "src/kernel.rs".to_string(),
            },
            // &self method
            ParsedFnSig {
                name: "Capability.has_right".to_string(),
                type_params: vec![],
                params: vec![
                    (
                        "self".to_string(),
                        RustType::Named("Capability".to_string()),
                    ),
                    ("right".to_string(), RustType::Named("Right".to_string())),
                ],
                ret_type: RustType::Named("bool".to_string()),
                is_method: true,
                self_type: Some("Capability".to_string()),
                is_mut_self: false,
                source_file: "src/types/capability.rs".to_string(),
            },
            // &mut self method
            ParsedFnSig {
                name: "State.apply_free_mut".to_string(),
                type_params: vec![],
                params: vec![
                    ("self".to_string(), RustType::Named("State".to_string())),
                    ("addr".to_string(), RustType::Named("u64".to_string())),
                ],
                ret_type: RustType::Unit,
                is_method: true,
                self_type: Some("State".to_string()),
                is_mut_self: true,
                source_file: "src/state/state.rs".to_string(),
            },
            // Associated function (no self, returns Self)
            ParsedFnSig {
                name: "Capability.new".to_string(),
                type_params: vec![],
                params: vec![
                    ("id".to_string(), RustType::Named("u64".to_string())),
                    ("holder".to_string(), RustType::Named("u64".to_string())),
                ],
                ret_type: RustType::Named("Self".to_string()),
                is_method: false,
                self_type: Some("Capability".to_string()),
                is_mut_self: false,
                source_file: "src/types/capability.rs".to_string(),
            },
        ],
    }
}

#[test]
fn direct_types_basic() {
    let parsed = make_test_crate();
    let files = emit_direct(&parsed, "TestNs", &PathBuf::from("/tmp/test-out"), false);

    let types = files
        .get(&PathBuf::from("/tmp/test-out/TestNs/Types.lean"))
        .expect("Types.lean should be emitted");

    // Header
    assert!(types.contains("namespace TestNs"));
    assert!(types.contains("end TestNs"));

    // Enum
    assert!(types.contains("inductive SecurityLevel where"));
    assert!(types.contains("| Low"));
    assert!(types.contains("| Critical"));

    // Struct
    assert!(types.contains("structure Capability where"));
    assert!(types.contains("id : U64"));
    assert!(types.contains("holder : U64"));
    assert!(types.contains("rights : Rights"));

    // Alias
    assert!(types.contains("abbrev PluginId := U64"));

    // Generic alias
    assert!(types.contains("abbrev Queue (T : Type) := (Vec T)"));
}

#[test]
fn direct_funs_basic() {
    let parsed = make_test_crate();
    let files = emit_direct(&parsed, "TestNs", &PathBuf::from("/tmp/test-out"), false);

    let funs = files
        .get(&PathBuf::from("/tmp/test-out/TestNs/Funs.lean"))
        .expect("Funs.lean should be emitted");

    // Header
    assert!(funs.contains("import TestNs.Types"));
    assert!(funs.contains("namespace TestNs"));
    assert!(funs.contains("end TestNs"));

    // Free function
    assert!(
        funs.contains(
            "opaque kernel_dispatch (state : State) (req : KernelRequest) : Result KernelResult"
        ),
        "free function should be emitted"
    );

    // &self method
    assert!(
        funs.contains(
            "opaque Capability.has_right (self : Capability) (right : Right) : Result Bool"
        ),
        "&self method should be emitted"
    );

    // &mut self method — should return product with self type
    assert!(
        funs.contains("opaque State.apply_free_mut (self : State) (addr : U64) : Result State"),
        "&mut self with Unit return should just return self type"
    );

    // Associated function returning Self — should resolve Self to type name
    assert!(
        funs.contains("opaque Capability.new (id : U64) (holder : U64) : Result Capability"),
        "Self should be resolved to Capability"
    );
    // Self should NOT appear literally
    assert!(
        !funs.contains("Result Self"),
        "Self should be resolved, not left literal"
    );
}

#[test]
fn direct_no_funs_when_empty() {
    let parsed = ParsedCrate {
        types: vec![ParsedTypeDef {
            name: "Foo".to_string(),
            simple_name: "Foo".to_string(),
            type_params: vec![],
            kind: ParsedTypeKind::Struct(vec![]),
            source_file: "src/foo.rs".to_string(),
        }],
        fns: vec![],
    };

    let files = emit_direct(&parsed, "TestNs", &PathBuf::from("/tmp/test-out"), false);

    assert!(
        files
            .get(&PathBuf::from("/tmp/test-out/TestNs/Types.lean"))
            .is_some(),
        "Types.lean should always be emitted"
    );
    assert!(
        files
            .get(&PathBuf::from("/tmp/test-out/TestNs/Funs.lean"))
            .is_none(),
        "Funs.lean should not be emitted when there are no functions"
    );
}

#[test]
fn direct_crate_prefix_stripped() {
    let parsed = ParsedCrate {
        types: vec![ParsedTypeDef {
            name: "Wrapper".to_string(),
            simple_name: "Wrapper".to_string(),
            type_params: vec![],
            kind: ParsedTypeKind::Struct(vec![ParsedField {
                name: "inner".to_string(),
                ty: RustType::Named("crate::types::Foo".to_string()),
            }]),
            source_file: "src/lib.rs".to_string(),
        }],
        fns: vec![],
    };

    let files = emit_direct(&parsed, "TestNs", &PathBuf::from("/tmp/test-out"), false);
    let types = files
        .get(&PathBuf::from("/tmp/test-out/TestNs/Types.lean"))
        .unwrap();

    // crate:: should be stripped
    assert!(
        types.contains("inner : types.Foo"),
        "crate:: prefix should be stripped, got: {}",
        types
    );
    assert!(!types.contains("crate."), "no crate. prefix should remain");
}

// ---------------------------------------------------------------------------
// Bridge template tests (--direct --bridge-template)
// ---------------------------------------------------------------------------

/// Build a minimal `ParsedCrate` exercising all three bridge classification paths:
/// - `Color`      — unit enum → BIJECTIVE
/// - `ErrorCode`  — data enum → INJECTIVE
/// - `Capability` — struct    → RELATIONAL (with bounded U64 + ADT fields)
fn make_bridge_test_crate() -> ParsedCrate {
    ParsedCrate {
        types: vec![
            // Unit enum → BIJECTIVE
            ParsedTypeDef {
                name: "security.Color".to_string(),
                simple_name: "Color".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Enum(vec![
                    ParsedVariant {
                        name: "Red".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "Green".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "Blue".to_string(),
                        fields: vec![],
                    },
                ]),
                source_file: "src/color.rs".to_string(),
            },
            // Data enum → INJECTIVE
            ParsedTypeDef {
                name: "errors.ErrorCode".to_string(),
                simple_name: "ErrorCode".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Enum(vec![
                    ParsedVariant {
                        name: "Ok".to_string(),
                        fields: vec![],
                    },
                    ParsedVariant {
                        name: "InvalidId".to_string(),
                        fields: vec![ParsedField {
                            name: "a0".to_string(),
                            ty: RustType::Named("u64".to_string()),
                        }],
                    },
                    ParsedVariant {
                        name: "Custom".to_string(),
                        fields: vec![ParsedField {
                            name: "a0".to_string(),
                            ty: RustType::Named("String".to_string()),
                        }],
                    },
                ]),
                source_file: "src/errors.rs".to_string(),
            },
            // Struct → RELATIONAL (U64 field + Color ADT field)
            ParsedTypeDef {
                name: "capability.Capability".to_string(),
                simple_name: "Capability".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Struct(vec![
                    ParsedField {
                        name: "id".to_string(),
                        ty: RustType::Named("u64".to_string()),
                    },
                    ParsedField {
                        name: "color".to_string(),
                        ty: RustType::Named("Color".to_string()),
                    },
                    ParsedField {
                        name: "tags".to_string(),
                        ty: RustType::Generic(
                            "Vec".to_string(),
                            vec![RustType::Named("Color".to_string())],
                        ),
                    },
                ]),
                source_file: "src/capability.rs".to_string(),
            },
            // Type alias → should be skipped
            ParsedTypeDef {
                name: "ids.PluginId".to_string(),
                simple_name: "PluginId".to_string(),
                type_params: vec![],
                kind: ParsedTypeKind::Alias(RustType::Named("u64".to_string())),
                source_file: "src/ids.rs".to_string(),
            },
        ],
        fns: vec![],
    }
}

#[test]
fn direct_bridge_unit_enum_bijective() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // Classification header
    assert!(
        out.contains("Color (BIJECTIVE"),
        "Color should be BIJECTIVE; got:\n{out}"
    );
    // Both directions emitted
    assert!(
        out.contains("def colorToSpec"),
        "colorToSpec should be emitted"
    );
    assert!(
        out.contains("def colorFromSpec"),
        "colorFromSpec should be emitted"
    );
    // Roundtrip theorems
    assert!(
        out.contains("theorem color_roundtrip"),
        "roundtrip theorem should be emitted"
    );
    assert!(
        out.contains("theorem color_roundtrip_inv"),
        "roundtrip_inv theorem should be emitted"
    );
    // Equiv bundle
    assert!(
        out.contains("def colorEquiv"),
        "colorEquiv should be emitted"
    );
    assert!(
        out.contains("TestNs.Color ≃ Lion.Color"),
        "Equiv type should use ≃; got:\n{out}"
    );
    // All variant arms
    assert!(
        out.contains("| .Red => .Red"),
        "Red variant arm should be emitted"
    );
    assert!(
        out.contains("| .Green => .Green"),
        "Green variant arm should be emitted"
    );
    assert!(
        out.contains("| .Blue => .Blue"),
        "Blue variant arm should be emitted"
    );
}

#[test]
fn direct_bridge_data_enum_injective() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // Classification header
    assert!(
        out.contains("ErrorCode (INJECTIVE"),
        "ErrorCode should be INJECTIVE; got:\n{out}"
    );
    // Only toSpec (one direction)
    assert!(
        out.contains("def errorCodeToSpec"),
        "errorCodeToSpec should be emitted"
    );
    assert!(
        !out.contains("def errorCodeFromSpec"),
        "errorCodeFromSpec should NOT be emitted for INJECTIVE"
    );
    // Injectivity theorem
    assert!(
        out.contains("theorem errorCodeToSpec_injective"),
        "injectivity theorem should be emitted"
    );
    // Data variant arm uses .val for bounded field
    assert!(
        out.contains("| .InvalidId a0 => .InvalidId a0.val"),
        "bounded u64 field should use .val"
    );
}

#[test]
fn direct_bridge_struct_relational() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // Classification header
    assert!(
        out.contains("Capability (RELATIONAL"),
        "Capability should be RELATIONAL; got:\n{out}"
    );
    // Corresponds structure emitted
    assert!(
        out.contains("structure CapabilityCorresponds"),
        "CapabilityCorresponds structure should be emitted"
    );
    // U64 field uses .val
    assert!(
        out.contains("id_eq : ec.id.val = sc.id"),
        "U64 field should use .val extraction; got:\n{out}"
    );
    // Color ADT field (bijective) → colorToSpec
    assert!(
        out.contains("color_eq : colorToSpec ec.color = sc.color"),
        "Color (bijective) ADT field should use colorToSpec; got:\n{out}"
    );
    // Vec<Color> (bijective inner) → .map colorToSpec
    assert!(
        out.contains("tags_eq : ec.tags.map colorToSpec = sc.tags"),
        "Vec<Color> (bijective inner) should use .map colorToSpec; got:\n{out}"
    );
}

#[test]
fn direct_bridge_alias_skipped() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // PluginId is a type alias — must NOT appear in bridge output
    assert!(
        !out.contains("PluginId"),
        "type aliases should be skipped in bridge output; got:\n{out}"
    );
}

#[test]
fn direct_bridge_namespace_and_structure() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // Must open and close the Bridge namespace
    assert!(
        out.contains("namespace TestNs.Bridge"),
        "Bridge namespace should be opened"
    );
    assert!(
        out.contains("end TestNs.Bridge"),
        "Bridge namespace should be closed"
    );

    // Must import Types
    assert!(out.contains("import TestNs.Types"), "should import Types");

    // Summary line
    assert!(
        out.contains("-- Summary:"),
        "summary line should be present"
    );
}

#[test]
fn direct_bridge_spec_map_applied() {
    use std::collections::HashMap;

    let parsed = make_bridge_test_crate();

    // Provide a spec map that maps Color → Lion.Security.Color
    let mut spec_map: HashMap<String, String> = HashMap::new();
    spec_map.insert("Color".to_string(), "Lion.Security.Color".to_string());

    let out = emit_bridge_template_direct(&parsed, "TestNs", Some(&spec_map));

    // Color should use the mapped spec path, NOT the heuristic Lion.Color
    assert!(
        out.contains("Lion.Security.Color"),
        "spec map should override heuristic path; got:\n{out}"
    );
    assert!(
        !out.contains("Lion.Color"),
        "heuristic Lion.Color should not appear when spec map provides the path; got:\n{out}"
    );
    // No TODO comment for Color since it was found in the map
    // (The spec_known=true path omits the TODO suffix)
    assert!(
        !out.contains("Lion.Security.Color  -- TODO"),
        "known spec path should not have TODO comment; got:\n{out}"
    );
}

#[test]
fn direct_bridge_heuristic_spec_path_has_todo() {
    let parsed = make_bridge_test_crate();
    let out = emit_bridge_template_direct(&parsed, "TestNs", None);

    // Without a spec_map, all spec paths use the heuristic with a TODO comment
    assert!(
        out.contains("-- TODO: verify spec type path"),
        "unknown spec paths should have TODO comment; got:\n{out}"
    );
}

#[test]
fn direct_bridge_parse_spec_map_from_string() {
    use styx::emit::direct::parse_spec_map_direct;

    // Write a temp file with a BinaryBridge-style snippet and parse it.
    let content = r#"
def colorToSpec : Extracted.Color → Lion.Security.Color
  | .Red => .Red

structure CapabilityCorresponds
    (ec : Extracted.Capability)
    (sc : Lion.Capability.Capability) : Prop where
  id_eq : ec.id.val = sc.id
"#;

    let tmp = std::env::temp_dir().join("styx_test_bridge_spec_map.lean");
    std::fs::write(&tmp, content).unwrap();

    let map = parse_spec_map_direct(&tmp);
    std::fs::remove_file(&tmp).ok();

    assert_eq!(
        map.get("Color").map(|s| s.as_str()),
        Some("Lion.Security.Color"),
        "Color should map to Lion.Security.Color"
    );
    assert_eq!(
        map.get("Capability").map(|s| s.as_str()),
        Some("Lion.Capability.Capability"),
        "Capability should map to Lion.Capability.Capability"
    );
}
