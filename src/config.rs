use std::path::PathBuf;

/// Global configuration for emission.
#[derive(Clone, Debug)]
pub struct Config {
    /// Root output directory (files will be placed under `<output_dir>/<namespace>/...`).
    pub output_dir: PathBuf,

    /// Lean namespace to emit into (e.g. `MyCrate`).
    pub namespace: String,

    /// If true, force all loops to use `partial_fixpoint`.
    ///
    /// This matches the Aeneas style and avoids termination proofs.
    pub aeneas_compat: bool,

    /// Optional path to Rust source directory for direct type parsing.
    ///
    /// When set, styx parses `.rs` files for type definitions that Charon
    /// cannot extract (e.g., types using BTreeMap, Arc<dyn>, String).
    /// LLBC-extracted types take priority; Rust-parsed types fill gaps.
    pub rust_src: Option<PathBuf>,

    /// If true, emit `#check <name>` after each emitted `def` and `structure`.
    ///
    /// This gives Lean's kernel a mechanical sanity check on every emitted
    /// definition — `lake build` will fail if any emitted type is ill-formed.
    /// Off by default so golden tests are unaffected.
    pub emit_checks: bool,

    /// If true, emit a `Bridge_Template.lean` with correspondence proof outlines
    /// for every extracted type.
    ///
    /// Classifies types as BIJECTIVE (unit enums), INJECTIVE (data enums), or
    /// RELATIONAL (structs) and generates appropriate proof skeletons.
    pub bridge_template: bool,

    /// Optional path to an existing BinaryBridge Lean file.
    ///
    /// When set, `emit_bridge_template` reads the file and extracts the actual
    /// spec type paths used there (e.g. `Lion.Security.SecurityLevel`).
    /// This allows the template to emit correct paths instead of heuristic
    /// `Lion.X` placeholders with `-- TODO: verify spec type path` comments.
    ///
    /// The parser recognises two line patterns:
    /// - `def {name}ToSpec : Extracted.{ext} → {spec}`
    /// - `structure {name}Corresponds (ex : Extracted.{ext}) (sx : {spec})`
    ///
    /// Types not found in the map fall back to the heuristic with a TODO comment.
    pub spec_map: Option<PathBuf>,

    /// Compatibility aliases to emit at the end of `Funs.lean`.
    ///
    /// Each entry is `(alias_name, canonical_name)`, emitted as:
    /// ```lean
    /// abbrev <alias_name> := <canonical_name>
    /// ```
    ///
    /// Used to bridge collision-ID differences between extraction runs.
    /// For example, proof files written against Aeneas extraction (which
    /// assigned FunDeclId=44) can reference the Styx-generated name (FunDeclId=42)
    /// via an `abbrev` alias.
    pub compat_aliases: Vec<(String, String)>,
}
