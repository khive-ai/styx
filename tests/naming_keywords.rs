use styx::naming::{escape_lean_ident, is_lean_keyword};

#[test]
fn lean_keyword_escaping() {
    assert!(is_lean_keyword("theorem"));
    assert_eq!(escape_lean_ident("theorem"), "theorem_");
    assert_eq!(escape_lean_ident("match"), "match_");

    assert!(!is_lean_keyword("foo"));
    assert_eq!(escape_lean_ident("foo"), "foo");

    // Replace characters that are not valid in Lean identifiers.
    assert_eq!(escape_lean_ident("foo-bar"), "foo_bar");
    assert_eq!(escape_lean_ident("foo::bar"), "foo__bar");
}

/// Keywords that appear as Rust identifiers in practice (e.g., Rust field names,
/// variant names, or module names that happen to match Lean 4 keywords).
#[test]
fn lean_keywords_from_rust_names() {
    // `private` — Lean modifier keyword; could appear as a Rust module or field name.
    assert!(is_lean_keyword("private"));
    assert_eq!(escape_lean_ident("private"), "private_");

    // `namespace` — Lean structural keyword.
    assert!(is_lean_keyword("namespace"));
    assert_eq!(escape_lean_ident("namespace"), "namespace_");

    // `def` — Lean definition keyword; Rust enums/variants can be named `def`.
    assert!(is_lean_keyword("def"));
    assert_eq!(escape_lean_ident("def"), "def_");

    // `from` — Lean `calc` block keyword; also common in Rust as a trait method or
    // variant name (e.g., `From::from`). Aeneas escapes it to `from_`.
    assert!(is_lean_keyword("from"));
    assert_eq!(escape_lean_ident("from"), "from_");

    // `where` — Lean clause keyword; appears in Rust type bounds (`T: Trait + where …`).
    assert!(is_lean_keyword("where"));
    assert_eq!(escape_lean_ident("where"), "where_");
}

/// Edge cases: digit-leading names and empty strings.
#[test]
fn lean_ident_edge_cases() {
    // Digit as first character: prefix with `_`.
    assert_eq!(escape_lean_ident("0field"), "_0field");
    assert_eq!(escape_lean_ident("123"), "_123");

    // Empty string: becomes `_`.
    assert_eq!(escape_lean_ident(""), "_");

    // Underscore-only: valid Lean identifier, no change.
    assert_eq!(escape_lean_ident("_"), "_");
    assert_eq!(escape_lean_ident("_foo"), "_foo");

    // Path separator `::` → `__` (double underscore).
    assert_eq!(
        escape_lean_ident("core::result::Result"),
        "core__result__Result"
    );
}
