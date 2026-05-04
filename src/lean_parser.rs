//! Simple line-based parser for Lean 4 `structure` and `inductive` definitions.
//!
//! This is **not** a full Lean parser. It uses indentation-based heuristics to
//! extract type declarations for the purpose of generating Rust skeleton code.
//!
//! Supports:
//! - `structure Name where` followed by indented `field : Type` lines
//! - `inductive Name where` followed by `| Variant` or `| Variant (field : Type)` lines
//! - Skips `deriving`, `instance`, `theorem`, `def`, `axiom` blocks
//! - Stops a block when indentation decreases back to zero (or a new top-level keyword appears)

use std::fmt;

/// A parsed Lean field (name + type string).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanField {
    /// Field name as written in the Lean source.
    pub name: String,
    /// Type as written in the Lean source (raw string).
    pub lean_type: String,
}

/// A parsed inductive variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeanVariant {
    /// Variant name (e.g. `Read`, `Write`).
    pub name: String,
    /// Fields for data-carrying variants (e.g. `| Tagged (tag : String)`).
    pub fields: Vec<LeanField>,
}

/// A parsed Lean type definition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LeanTypeDef {
    /// `structure Name where ...`
    Structure {
        name: String,
        fields: Vec<LeanField>,
    },
    /// `inductive Name where ...`
    Inductive {
        name: String,
        variants: Vec<LeanVariant>,
    },
}

impl LeanTypeDef {
    /// The declared name of the type.
    pub fn name(&self) -> &str {
        match self {
            LeanTypeDef::Structure { name, .. } => name,
            LeanTypeDef::Inductive { name, .. } => name,
        }
    }
}

impl fmt::Display for LeanTypeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LeanTypeDef::Structure { name, .. } => write!(f, "structure {name}"),
            LeanTypeDef::Inductive { name, .. } => write!(f, "inductive {name}"),
        }
    }
}

/// Parse error with source line information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub line: usize,
    pub message: String,
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "line {}: {}", self.line, self.message)
    }
}

/// Top-level keywords that terminate any active block.
const BLOCK_TERMINATORS: &[&str] = &[
    "structure",
    "inductive",
    "def",
    "theorem",
    "lemma",
    "axiom",
    "instance",
    "class",
    "abbrev",
    "opaque",
    "namespace",
    "section",
    "end",
    "open",
    "import",
    "variable",
    "set_option",
    "attribute",
    "mutual",
    "private",
    "protected",
    "noncomputable",
    "#check",
    "#eval",
    "#print",
];

/// Lines to skip entirely (content we don't model).
const SKIP_PREFIXES: &[&str] = &["deriving", "--", "/-", "/--"];

/// Returns the number of leading spaces on a line (tab = 2 spaces for our purposes).
fn leading_spaces(line: &str) -> usize {
    line.chars()
        .take_while(|c| *c == ' ' || *c == '\t')
        .map(|c| if c == '\t' { 2 } else { 1 })
        .sum()
}

/// Return the first token on a line (trimmed, split on whitespace).
fn first_token(line: &str) -> &str {
    line.split_whitespace().next().unwrap_or("")
}

/// True if the line starts a new top-level block that should terminate parsing.
fn is_top_level_terminator(line: &str) -> bool {
    let tok = first_token(line);
    BLOCK_TERMINATORS.contains(&tok)
}

/// True if the line should be skipped entirely within a block.
fn should_skip(line: &str) -> bool {
    let trimmed = line.trim();
    if trimmed.is_empty() {
        return false; // blank lines end a block — handled separately
    }
    SKIP_PREFIXES.iter().any(|&p| trimmed.starts_with(p))
}

/// Parse `field : Type` from an indented structure field line.
/// Returns `None` if the line doesn't match the pattern.
fn parse_field_line(line: &str) -> Option<LeanField> {
    let trimmed = line.trim();
    // Must contain " : "
    let colon_pos = trimmed.find(" : ")?;
    let name = trimmed[..colon_pos].trim().to_string();
    let lean_type = trimmed[colon_pos + 3..].trim().to_string();
    if name.is_empty() || lean_type.is_empty() {
        return None;
    }
    // Field names don't start with `|` and aren't keywords
    if name.starts_with('|') {
        return None;
    }
    Some(LeanField { name, lean_type })
}

/// Parse all inductive variants from a line that may contain multiple `|`-separated entries.
///
/// Formats handled per segment:
/// - `| Variant`
/// - `| Variant (field : Type) (field2 : Type2)`
/// - `| Variant : Type`  (GADT-style, extract name only)
///
/// Returns a `Vec` because a single source line like `| Read | Write | Execute` produces
/// multiple variants.
fn parse_variant_line_multi(line: &str) -> Vec<LeanVariant> {
    let trimmed = line.trim();
    if !trimmed.starts_with('|') {
        return vec![];
    }

    // Split on bare `|` that appear between variants (not inside parens).
    // We collect each `| Name [fields...]` segment.
    let mut variants = Vec::new();
    let mut depth: usize = 0;
    let mut segment_start = 0;
    let chars: Vec<char> = trimmed.chars().collect();
    let len = chars.len();

    let mut i = 0;
    while i < len {
        match chars[i] {
            '(' | '{' => depth += 1,
            ')' | '}' => depth = depth.saturating_sub(1),
            '|' if depth == 0 && i > segment_start => {
                // Flush segment [segment_start..i)
                let seg: String = chars[segment_start..i].iter().collect();
                if let Some(v) = parse_single_variant_segment(&seg) {
                    variants.push(v);
                }
                segment_start = i;
            }
            _ => {}
        }
        i += 1;
    }
    // Flush final segment
    let seg: String = chars[segment_start..].iter().collect();
    if let Some(v) = parse_single_variant_segment(&seg) {
        variants.push(v);
    }

    variants
}

/// Parse a single variant segment like `| Foo (x : T)`.
fn parse_single_variant_segment(seg: &str) -> Option<LeanVariant> {
    let trimmed = seg.trim();
    if !trimmed.starts_with('|') {
        return None;
    }
    let rest = trimmed[1..].trim();
    if rest.is_empty() {
        return None;
    }

    // Split on first space to get variant name
    let (variant_name, remainder) = match rest.find(|c: char| c.is_whitespace()) {
        Some(pos) => (&rest[..pos], rest[pos..].trim()),
        None => (rest, ""),
    };

    if variant_name.is_empty() {
        return None;
    }

    // Skip GADT-style `| Name : Type` — treat as unit variant
    let fields = if remainder.starts_with(':') {
        vec![]
    } else {
        parse_variant_fields(remainder)
    };

    Some(LeanVariant {
        name: variant_name.to_string(),
        fields,
    })
}

/// Parse `(field : Type) (field2 : Type2)` from a variant parameter list.
fn parse_variant_fields(s: &str) -> Vec<LeanField> {
    let mut fields = Vec::new();
    let mut remaining = s.trim();

    while !remaining.is_empty() {
        if remaining.starts_with('(') {
            // Find matching close paren
            let close = remaining.find(')');
            if let Some(pos) = close {
                let inner = &remaining[1..pos];
                if let Some(field) = parse_field_line(inner) {
                    fields.push(field);
                }
                remaining = remaining[pos + 1..].trim();
            } else {
                break;
            }
        } else if remaining.starts_with('{') {
            // Implicit arg `{field : Type}` — skip
            let close = remaining.find('}');
            if let Some(pos) = close {
                remaining = remaining[pos + 1..].trim();
            } else {
                break;
            }
        } else {
            // Remaining is a bare type name (anonymous field) — stop
            break;
        }
    }

    fields
}

/// Parse all `structure` and `inductive` definitions from Lean source text.
///
/// Lines belonging to a block are identified by having greater indentation than
/// the declaration line (which must be at column 0). A blank line or a
/// top-level keyword at column 0 terminates the block.
pub fn parse_lean_source(source: &str) -> (Vec<LeanTypeDef>, Vec<ParseError>) {
    let mut defs = Vec::new();
    let mut errors = Vec::new();

    let lines: Vec<&str> = source.lines().collect();
    let total = lines.len();
    let mut i = 0;

    while i < total {
        let line = lines[i];
        let indent = leading_spaces(line);

        // Only handle top-level declarations (indent == 0)
        if indent != 0 {
            i += 1;
            continue;
        }

        let tok = first_token(line);

        match tok {
            "structure" => {
                if let Some(name) = extract_decl_name(line, "structure") {
                    let (fields, consumed, errs) = parse_structure_body(&lines, i + 1);
                    for e in errs {
                        errors.push(e);
                    }
                    defs.push(LeanTypeDef::Structure { name, fields });
                    i += consumed + 1;
                } else {
                    errors.push(ParseError {
                        line: i + 1,
                        message: format!("could not extract name from: {line}"),
                    });
                    i += 1;
                }
            }
            "inductive" => {
                if let Some(name) = extract_decl_name(line, "inductive") {
                    let (variants, consumed, errs) = parse_inductive_body(&lines, i + 1);
                    for e in errs {
                        errors.push(e);
                    }
                    defs.push(LeanTypeDef::Inductive { name, variants });
                    i += consumed + 1;
                } else {
                    errors.push(ParseError {
                        line: i + 1,
                        message: format!("could not extract name from: {line}"),
                    });
                    i += 1;
                }
            }
            _ => {
                i += 1;
            }
        }
    }

    (defs, errors)
}

/// Extract the declared name from `structure Name [params] where` or
/// `inductive Name [params] where`.
fn extract_decl_name(line: &str, keyword: &str) -> Option<String> {
    let rest = line.trim().strip_prefix(keyword)?.trim();
    // Take the first token (the name), stop at space, `(`, `:`, or `where`
    let name: String = rest
        .chars()
        .take_while(|c| !c.is_whitespace() && *c != '(' && *c != ':')
        .collect();
    if name.is_empty() { None } else { Some(name) }
}

/// Parse structure field lines starting at `start_line` in `lines`.
///
/// Returns `(fields, lines_consumed, errors)`.
fn parse_structure_body(
    lines: &[&str],
    start_line: usize,
) -> (Vec<LeanField>, usize, Vec<ParseError>) {
    let mut fields = Vec::new();
    let mut errors = Vec::new();
    let mut consumed = 0;

    for (offset, &line) in lines[start_line..].iter().enumerate() {
        let indent = leading_spaces(line);
        let trimmed = line.trim();

        // Blank line — ends the block
        if trimmed.is_empty() {
            consumed = offset + 1;
            break;
        }

        // Top-level keyword at column 0 — ends the block (do NOT consume)
        if indent == 0 && is_top_level_terminator(line) {
            consumed = offset;
            break;
        }

        // Skip `deriving` and comments
        if should_skip(line) {
            consumed = offset + 1;
            continue;
        }

        // Must be indented to belong to this block
        if indent == 0 {
            consumed = offset;
            break;
        }

        if let Some(field) = parse_field_line(line) {
            fields.push(field);
        } else {
            errors.push(ParseError {
                line: start_line + offset + 1,
                message: format!("could not parse field: {trimmed}"),
            });
        }

        consumed = offset + 1;
    }

    (fields, consumed, errors)
}

/// Parse inductive variant lines starting at `start_line` in `lines`.
///
/// Returns `(variants, lines_consumed, errors)`.
fn parse_inductive_body(
    lines: &[&str],
    start_line: usize,
) -> (Vec<LeanVariant>, usize, Vec<ParseError>) {
    let mut variants = Vec::new();
    let mut errors = Vec::new();
    let mut consumed = 0;

    for (offset, &line) in lines[start_line..].iter().enumerate() {
        let indent = leading_spaces(line);
        let trimmed = line.trim();

        // Blank line — ends the block
        if trimmed.is_empty() {
            consumed = offset + 1;
            break;
        }

        // Top-level keyword at column 0 — ends the block (do NOT consume)
        if indent == 0 && is_top_level_terminator(line) {
            consumed = offset;
            break;
        }

        // Skip `deriving` and comments
        if should_skip(line) {
            consumed = offset + 1;
            continue;
        }

        // Must be indented or start with `|` at top level
        let is_variant_line = trimmed.starts_with('|');
        if indent == 0 && !is_variant_line {
            consumed = offset;
            break;
        }

        if is_variant_line {
            let parsed = parse_variant_line_multi(line);
            if parsed.is_empty() {
                errors.push(ParseError {
                    line: start_line + offset + 1,
                    message: format!("could not parse variant: {trimmed}"),
                });
            } else {
                variants.extend(parsed);
            }
        }
        // Non-variant indented lines are skipped (e.g. doc comments, where clauses)

        consumed = offset + 1;
    }

    (variants, consumed, errors)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_structure() {
        let src = r#"
structure PolicyContext where
  subject : Nat
  target : Nat
  rights : Finset Right
  kind : String
"#;
        let (defs, errors) = parse_lean_source(src);
        assert!(errors.is_empty(), "errors: {errors:?}");
        assert_eq!(defs.len(), 1);
        match &defs[0] {
            LeanTypeDef::Structure { name, fields } => {
                assert_eq!(name, "PolicyContext");
                assert_eq!(fields.len(), 4);
                assert_eq!(fields[0].name, "subject");
                assert_eq!(fields[0].lean_type, "Nat");
                assert_eq!(fields[2].name, "rights");
                assert_eq!(fields[2].lean_type, "Finset Right");
            }
            other => panic!("expected structure, got {other}"),
        }
    }

    #[test]
    fn test_parse_unit_inductive() {
        let src = r#"
inductive Right where
  | Read | Write | Execute | Admin
"#;
        let (defs, errors) = parse_lean_source(src);
        assert!(errors.is_empty(), "errors: {errors:?}");
        assert_eq!(defs.len(), 1);
        match &defs[0] {
            LeanTypeDef::Inductive { name, variants } => {
                assert_eq!(name, "Right");
                assert_eq!(variants.len(), 4);
                assert_eq!(variants[0].name, "Read");
                assert!(variants[0].fields.is_empty());
            }
            other => panic!("expected inductive, got {other}"),
        }
    }

    #[test]
    fn test_parse_multi_variant_lines() {
        let src = r#"
inductive Right where
  | Read
  | Write
  | Execute
  | Admin
"#;
        let (defs, errors) = parse_lean_source(src);
        assert!(errors.is_empty(), "errors: {errors:?}");
        assert_eq!(defs.len(), 1);
        if let LeanTypeDef::Inductive { variants, .. } = &defs[0] {
            assert_eq!(variants.len(), 4);
            assert_eq!(variants[3].name, "Admin");
        }
    }

    #[test]
    fn test_parse_data_carrying_inductive() {
        let src = r#"
inductive Event where
  | Tick (ts : Nat)
  | Message (sender : Nat) (payload : String)
  | Reset
"#;
        let (defs, errors) = parse_lean_source(src);
        assert!(errors.is_empty(), "errors: {errors:?}");
        assert_eq!(defs.len(), 1);
        if let LeanTypeDef::Inductive { name, variants } = &defs[0] {
            assert_eq!(name, "Event");
            assert_eq!(variants.len(), 3);
            assert_eq!(variants[0].name, "Tick");
            assert_eq!(variants[0].fields[0].name, "ts");
            assert_eq!(variants[1].fields.len(), 2);
            assert!(variants[2].fields.is_empty());
        }
    }

    #[test]
    fn test_multiple_definitions() {
        let src = r#"
structure Foo where
  x : Nat

inductive Bar where
  | A | B
"#;
        let (defs, _) = parse_lean_source(src);
        assert_eq!(defs.len(), 2);
        assert_eq!(defs[0].name(), "Foo");
        assert_eq!(defs[1].name(), "Bar");
    }

    #[test]
    fn test_deriving_skipped() {
        let src = r#"
inductive Color where
  | Red | Green | Blue
  deriving Repr, BEq, Hashable
"#;
        let (defs, errors) = parse_lean_source(src);
        assert!(errors.is_empty(), "errors: {errors:?}");
        if let LeanTypeDef::Inductive { variants, .. } = &defs[0] {
            assert_eq!(variants.len(), 3);
        }
    }

    #[test]
    fn test_parse_field_line() {
        assert_eq!(
            parse_field_line("  subject : Nat"),
            Some(LeanField {
                name: "subject".to_string(),
                lean_type: "Nat".to_string(),
            })
        );
        assert_eq!(
            parse_field_line("  rights : Finset Right"),
            Some(LeanField {
                name: "rights".to_string(),
                lean_type: "Finset Right".to_string(),
            })
        );
        assert_eq!(parse_field_line("  | Read"), None);
    }
}
