//! Integration tests for `--lean-to-rust` skeleton generation.
//!
//! Exercises the full parse → emit pipeline against representative Lean
//! definitions and asserts on the Rust output.

use styx::emit::lean_to_rust::emit_rust_skeletons;
use styx::lean_parser::parse_lean_source;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Parse `source` and emit Rust, asserting no parse errors.
fn parse_and_emit(source: &str, module_path: &str) -> String {
    let (defs, errors) = parse_lean_source(source);
    assert!(errors.is_empty(), "unexpected parse errors: {errors:?}");
    emit_rust_skeletons(&defs, module_path)
}

// ---------------------------------------------------------------------------
// Test 1: simple structure → Rust struct
// ---------------------------------------------------------------------------

#[test]
fn test_simple_structure_to_rust_struct() {
    let lean = r#"
structure PolicyContext where
  subject : Nat
  target : Nat
  rights : Finset Right
  kind : String
"#;

    let rust = parse_and_emit(lean, "Lion.Core.Policy");

    // Doc comment with module path
    assert!(
        rust.contains("/// Corresponds to: Lion.Core.Policy.PolicyContext"),
        "missing doc comment; got:\n{rust}"
    );
    assert!(
        rust.contains("pub struct PolicyContext {"),
        "missing struct decl; got:\n{rust}"
    );
    // subject : Nat → u64 with bounded comment
    assert!(
        rust.contains("pub subject: u64,"),
        "missing subject field; got:\n{rust}"
    );
    assert!(
        rust.contains("// Lean: Nat (bounded by u64)"),
        "missing Nat comment; got:\n{rust}"
    );
    // rights : Finset Right → Vec<Right>
    assert!(
        rust.contains("pub rights: Vec<Right>,"),
        "missing rights field; got:\n{rust}"
    );
    assert!(
        rust.contains("// Lean: Finset Right"),
        "missing Finset comment; got:\n{rust}"
    );
    // kind : String → String (no comment)
    assert!(
        rust.contains("pub kind: String,"),
        "missing kind field; got:\n{rust}"
    );
}

// ---------------------------------------------------------------------------
// Test 2: unit-variant inductive → Rust enum
// ---------------------------------------------------------------------------

#[test]
fn test_unit_inductive_to_rust_enum() {
    let lean = r#"
inductive Right where
  | Read | Write | Execute | Admin
"#;

    let rust = parse_and_emit(lean, "Lion.Core");

    assert!(
        rust.contains("/// Corresponds to: Lion.Core.Right"),
        "missing doc comment; got:\n{rust}"
    );
    assert!(
        rust.contains("pub enum Right {"),
        "missing enum decl; got:\n{rust}"
    );
    assert!(rust.contains("Read,"), "missing Read; got:\n{rust}");
    assert!(rust.contains("Write,"), "missing Write; got:\n{rust}");
    assert!(rust.contains("Execute,"), "missing Execute; got:\n{rust}");
    assert!(rust.contains("Admin,"), "missing Admin; got:\n{rust}");

    // Unit variants have no field block — no `{` inside the variant list
    let enum_body_start = rust.find("pub enum Right {").unwrap();
    let enum_body = &rust[enum_body_start..];
    let first_brace_close = enum_body.find('}').unwrap();
    let body = &enum_body[..first_brace_close];
    // No struct-variant braces inside a unit enum
    assert!(
        !body.contains("{ "),
        "unit enum should have no struct variants; got:\n{rust}"
    );
}

// ---------------------------------------------------------------------------
// Test 3: data-carrying inductive → Rust enum with struct fields
// ---------------------------------------------------------------------------

#[test]
fn test_data_carrying_inductive_to_rust_enum() {
    let lean = r#"
inductive Event where
  | Tick (ts : Nat)
  | Message (sender : Nat) (payload : String)
  | Reset
"#;

    let rust = parse_and_emit(lean, "Lion.Events");

    assert!(
        rust.contains("pub enum Event {"),
        "missing enum decl; got:\n{rust}"
    );
    // Tick has a struct variant with ts: u64
    assert!(
        rust.contains("Tick {"),
        "missing Tick variant; got:\n{rust}"
    );
    assert!(rust.contains("ts: u64,"), "missing ts field; got:\n{rust}");
    // Message has two fields
    assert!(
        rust.contains("Message {"),
        "missing Message variant; got:\n{rust}"
    );
    assert!(
        rust.contains("sender: u64,"),
        "missing sender field; got:\n{rust}"
    );
    assert!(
        rust.contains("payload: String,"),
        "missing payload field; got:\n{rust}"
    );
    // Reset is a unit variant
    assert!(rust.contains("Reset,"), "missing Reset; got:\n{rust}");
}

// ---------------------------------------------------------------------------
// Test 4: type-mapping coverage
// ---------------------------------------------------------------------------

#[test]
fn test_type_mapping_coverage() {
    let lean = r#"
structure AllTypes where
  a : Nat
  b : Bool
  c : String
  d : Int
  e : ByteArray
  f : List String
  g : Option Nat
"#;

    let rust = parse_and_emit(lean, "");

    assert!(rust.contains("pub a: u64,"), "Nat→u64; got:\n{rust}");
    assert!(rust.contains("pub b: bool,"), "Bool→bool; got:\n{rust}");
    assert!(
        rust.contains("pub c: String,"),
        "String→String; got:\n{rust}"
    );
    assert!(rust.contains("pub d: i64,"), "Int→i64; got:\n{rust}");
    assert!(
        rust.contains("pub e: Vec<u8>,"),
        "ByteArray→Vec<u8>; got:\n{rust}"
    );
    assert!(
        rust.contains("pub f: Vec<String>,"),
        "List String→Vec<String>; got:\n{rust}"
    );
    assert!(
        rust.contains("pub g: Option<u64>,"),
        "Option Nat→Option<u64>; got:\n{rust}"
    );
}

// ---------------------------------------------------------------------------
// Test 5: mixed file with both structure and inductive
// ---------------------------------------------------------------------------

#[test]
fn test_mixed_lean_file() {
    let lean = r#"
structure PolicyContext where
  subject : Nat
  target : Nat
  rights : Finset Right
  kind : String

inductive Right where
  | Read | Write | Execute | Admin
"#;

    let rust = parse_and_emit(lean, "Lion.Core.Policy");

    assert!(
        rust.contains("pub struct PolicyContext {"),
        "missing struct; got:\n{rust}"
    );
    assert!(
        rust.contains("pub enum Right {"),
        "missing enum; got:\n{rust}"
    );

    // PolicyContext appears before Right in the output
    let struct_pos = rust.find("pub struct PolicyContext {").unwrap();
    let enum_pos = rust.find("pub enum Right {").unwrap();
    assert!(
        struct_pos < enum_pos,
        "struct should precede enum; got:\n{rust}"
    );
}

// ---------------------------------------------------------------------------
// Test 6: deriving and blank lines don't produce errors
// ---------------------------------------------------------------------------

#[test]
fn test_deriving_and_blank_lines_ignored() {
    let lean = r#"
inductive Color where
  | Red | Green | Blue
  deriving Repr, BEq, Hashable

structure Point where
  x : Nat
  y : Nat
  deriving Repr
"#;

    let (defs, errors) = parse_lean_source(lean);
    assert!(errors.is_empty(), "errors: {errors:?}");
    assert_eq!(defs.len(), 2, "expected 2 defs; got {}", defs.len());

    let rust = emit_rust_skeletons(&defs, "");
    assert!(
        rust.contains("pub enum Color {"),
        "missing Color; got:\n{rust}"
    );
    assert!(
        rust.contains("pub struct Point {"),
        "missing Point; got:\n{rust}"
    );
}
