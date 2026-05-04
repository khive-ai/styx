//! Tests for function signature parsing from Rust source.

use std::io::Write;

use styx::rust_parser::parse_rust_crate;

/// Create a temporary directory with a Rust source file, parse it, and return
/// the parsed crate.
fn parse_source(code: &str) -> styx::rust_parser::ParsedCrate {
    let dir = tempfile::tempdir().unwrap();
    let file_path = dir.path().join("lib.rs");
    let mut f = std::fs::File::create(&file_path).unwrap();
    write!(f, "{}", code).unwrap();
    drop(f);
    parse_rust_crate(dir.path()).unwrap()
}

#[test]
fn parse_free_function() {
    let parsed = parse_source(
        r#"
pub fn greet(name: String) -> bool {
    true
}
"#,
    );

    assert_eq!(parsed.fns.len(), 1);
    let f = &parsed.fns[0];
    assert_eq!(f.name, "greet");
    assert!(!f.is_method);
    assert!(f.self_type.is_none());
    assert_eq!(f.params.len(), 1);
    assert_eq!(f.params[0].0, "name");
}

#[test]
fn parse_impl_methods() {
    let parsed = parse_source(
        r#"
pub struct Foo {
    pub x: u64,
}

impl Foo {
    pub fn new(x: u64) -> Self {
        Foo { x }
    }

    pub fn get_x(&self) -> u64 {
        self.x
    }

    pub fn set_x(&mut self, val: u64) {
        self.x = val;
    }

    // Private method — should be skipped.
    fn internal_helper(&self) -> bool {
        true
    }
}
"#,
    );

    // Should have struct Foo
    assert_eq!(parsed.types.len(), 1);
    assert_eq!(parsed.types[0].simple_name, "Foo");

    // Should have 3 pub methods (new, get_x, set_x), not internal_helper
    assert_eq!(
        parsed.fns.len(),
        3,
        "expected 3 pub methods, got {:?}",
        parsed.fns.iter().map(|f| &f.name).collect::<Vec<_>>()
    );

    // Associated function (no self)
    let new_fn = parsed.fns.iter().find(|f| f.name == "Foo.new").unwrap();
    assert!(!new_fn.is_method);
    assert_eq!(new_fn.self_type.as_deref(), Some("Foo"));
    assert!(!new_fn.is_mut_self);

    // &self method
    let get_fn = parsed.fns.iter().find(|f| f.name == "Foo.get_x").unwrap();
    assert!(get_fn.is_method);
    assert!(!get_fn.is_mut_self);
    assert_eq!(get_fn.params[0].0, "self");

    // &mut self method
    let set_fn = parsed.fns.iter().find(|f| f.name == "Foo.set_x").unwrap();
    assert!(set_fn.is_method);
    assert!(set_fn.is_mut_self);
}

#[test]
fn skip_trait_impls() {
    let parsed = parse_source(
        r#"
pub struct Bar;

impl std::fmt::Display for Bar {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        Ok(())
    }
}

impl Bar {
    pub fn name(&self) -> &str {
        "bar"
    }
}
"#,
    );

    // Only the inherent impl method should appear.
    assert_eq!(parsed.fns.len(), 1);
    assert_eq!(parsed.fns[0].name, "Bar.name");
}

#[test]
fn skip_cfg_test() {
    let parsed = parse_source(
        r#"
pub fn visible() -> bool { true }

#[cfg(test)]
pub fn test_only() -> bool { false }

#[cfg(test)]
mod tests {
    pub fn in_test_mod() {}
}
"#,
    );

    // Only visible() should be parsed.
    assert_eq!(parsed.fns.len(), 1);
    assert_eq!(parsed.fns[0].name, "visible");
}

#[test]
fn skip_cfg_charon() {
    let parsed = parse_source(
        r#"
pub fn normal() -> u64 { 0 }

#[cfg(charon)]
pub fn export_types(_x: u64) {}
"#,
    );

    assert_eq!(parsed.fns.len(), 1);
    assert_eq!(parsed.fns[0].name, "normal");
}

#[test]
fn non_pub_items_skipped() {
    let parsed = parse_source(
        r#"
struct Private {
    x: u64,
}

pub struct Public {
    pub y: u64,
}

fn private_fn() -> bool { true }

pub fn public_fn() -> bool { true }
"#,
    );

    assert_eq!(parsed.types.len(), 1);
    assert_eq!(parsed.types[0].simple_name, "Public");
    assert_eq!(parsed.fns.len(), 1);
    assert_eq!(parsed.fns[0].name, "public_fn");
}
