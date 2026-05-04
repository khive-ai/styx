use crate::ir::*;
use crate::naming::escape_lean_keyword;
use super::emit_type;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

pub(crate) fn emit_generics_binder(generics: &StyxGenerics) -> String {
    if generics.is_empty() {
        return String::new();
    }
    let mut parts = Vec::new();
    for tp in &generics.type_params {
        parts.push(format!("({} : Type)", tp.name));
    }
    for cp in &generics.const_params {
        let ty = emit_type(&cp.ty);
        parts.push(format!("({} : {ty})", cp.name));
    }
    if parts.is_empty() {
        String::new()
    } else {
        format!(" {}", parts.join(" "))
    }
}

/// Strip all `<...>` generic parameter sections from a Rust path, handling nesting.
/// e.g. `Result<T, E>::ok` → `Result::ok`, `Vec<(U64, Cap)>::len` → `Vec::len`
pub(crate) fn strip_generics(path: &str) -> String {
    let mut result = String::with_capacity(path.len());
    let mut depth = 0u32;
    for ch in path.chars() {
        match ch {
            '<' => depth += 1,
            '>' => {
                depth = depth.saturating_sub(1);
            }
            _ if depth == 0 => result.push(ch),
            _ => {} // inside <...>, skip
        }
    }
    // Collapse consecutive :: left behind by stripped generics
    // e.g. VecDeque::<T>::new → VecDeque::::new → VecDeque::new
    while result.contains("::::") {
        result = result.replace("::::", "::");
    }
    result
}

/// Convert a Rust path like "lion_core::types::security::SecurityLevel" to
/// Lean dotted name like "types.security.SecurityLevel".
///
/// For trait impl methods like `<Type as Trait<Args>>::method`, produces
/// Aeneas-compatible names: `{module}.{TraitName}{ArgNames}{TypeName}.{method}`
/// e.g. `<types::rights::Right as core::clone::Clone>::clone`
///      → `types.rights.CloneRight.clone`
pub(crate) fn rust_path_to_lean(rust_path: &str) -> String {
    // Handle trait impl syntax: <SelfType as Trait<Args>>::method
    if rust_path.starts_with('<')
        && let Some(name) = trait_impl_path_to_lean(rust_path) {
            return name;
        }

    let cleaned = strip_generics(rust_path);
    let path = cleaned
        .replace("::", ".")
        // Strip crate prefix
        .strip_prefix("lion_core.")
        .unwrap_or(cleaned.replace("::", ".").as_str())
        .to_string();
    // Escape any Lean keywords in path segments
    path.split('.')
        .map(escape_lean_keyword)
        .collect::<Vec<_>>()
        .join(".")
}

/// Convert a trait impl method path to Aeneas-compatible naming.
///
/// Input: `<SelfType as Trait<GenericArgs>>::method`
/// Output: `{self_module}.{TraitName}{GenericArgNames}{SelfTypeName}.{method}`
///
/// Examples:
///   `<types::rights::Right as core::clone::Clone>::clone`
///     → `types.rights.CloneRight.clone`
///   `<types::rights::Right as core::cmp::PartialEq<types::rights::Right>>::eq`
///     → `types.rights.PartialEqRightRight.eq`
///   `<error::Error as std::convert::From<types::rights::RightsError>>::from`
///     → `error.FromRightsErrorError.from_`
pub(crate) fn trait_impl_path_to_lean(rust_path: &str) -> Option<String> {
    let inner = rust_path.trim_start_matches('<');
    let (impl_part, method) = inner.rsplit_once(">::")?;

    // Split on " as " to get self type path and trait (with generics)
    let (self_type_raw, trait_with_generics) = impl_part.split_once(" as ")?;
    // Strip reference markers from self type
    let self_type_path = self_type_raw
        .trim()
        .trim_start_matches("&mut ")
        .trim_start_matches('&');

    // Extract trait short name (last segment, no generics)
    let trait_no_generics = strip_generics(trait_with_generics);
    let trait_short = trait_no_generics
        .rsplit("::")
        .next()
        .unwrap_or(&trait_no_generics);

    // Extract generic arg short names from trait
    // e.g. "core::cmp::PartialEq<types::rights::Right>" → ["Right"]
    // e.g. "std::convert::From<types::rights::RightsError>" → ["RightsError"]
    let generic_arg_names: Vec<&str> = extract_trait_generic_arg_names(trait_with_generics);

    // Self type: module path and short name
    let (self_module, self_short) = if let Some(pos) = self_type_path.rfind("::") {
        (&self_type_path[..pos], &self_type_path[pos + 2..])
    } else {
        ("", self_type_path)
    };

    // Build Aeneas impl name: {TraitShort}{GenericArgShortNames}{SelfShort}
    let mut impl_name = trait_short.to_string();
    for arg in &generic_arg_names {
        impl_name.push_str(arg);
    }
    impl_name.push_str(self_short);

    // Escape method name (e.g., "from" → "from_" since it's a Lean keyword)
    let escaped_method = escape_lean_keyword(method);

    // Build full path
    let module_lean = if self_module.is_empty() {
        String::new()
    } else {
        let m = self_module.replace("::", ".");
        let m = m.strip_prefix("lion_core.").unwrap_or(&m);
        format!(
            "{}.",
            m.split('.')
                .map(escape_lean_keyword)
                .collect::<Vec<_>>()
                .join(".")
        )
    };

    Some(format!("{module_lean}{impl_name}.{escaped_method}"))
}

/// Extract the short names of generic arguments from a trait path.
/// e.g. `core::cmp::PartialEq<types::rights::Right>` → vec!["Right"]
/// e.g. `std::convert::From<types::rights::RightsError>` → vec!["RightsError"]
/// e.g. `core::clone::Clone` → vec![]
pub(crate) fn extract_trait_generic_arg_names(trait_path: &str) -> Vec<&str> {
    // Find the first '<' and matching '>'
    let start = match trait_path.find('<') {
        Some(pos) => pos,
        None => return Vec::new(),
    };
    let end = match trait_path.rfind('>') {
        Some(pos) => pos,
        None => return Vec::new(),
    };
    if start >= end {
        return Vec::new();
    }

    let args_str = &trait_path[start + 1..end];
    // Split on ',' for multiple generic args, take the short name of each
    args_str
        .split(',')
        .map(|arg| {
            let trimmed = arg.trim();
            // Strip generics from the arg itself
            let no_generics = if let Some(lt) = trimmed.find('<') {
                &trimmed[..lt]
            } else {
                trimmed
            };
            // Take the last :: segment
            no_generics
                .rsplit("::")
                .next()
                .unwrap_or(no_generics)
                .trim()
        })
        .filter(|s| !s.is_empty())
        .collect()
}

/// Convert a Rust type path to Lean, with Aeneas builtin mapping.
/// Whether a type is a "noise" allocator/phantom parameter that should be stripped.
pub(crate) fn is_allocator_type(ty: &StyxType) -> bool {
    match ty {
        StyxType::Adt { rust_path, .. } => matches!(
            rust_path.as_str(),
            "std::alloc::Global"
                | "alloc::alloc::Global"
                | "std::marker::PhantomData"
                | "core::marker::PhantomData"
        ),
        _ => false,
    }
}

/// Map Rust std paths to Aeneas-compatible Lean names.
/// Returns (lean_name, strip_first_generic) where strip_first_generic indicates
/// the type erases its first arg (Arc<T> → T).
pub(crate) fn rust_path_to_lean_type(rust_path: &str) -> (&'static str, bool) {
    // Smart pointer erasure: Arc<T>/Rc<T>/Box<T> → T
    match rust_path {
        "alloc::sync::Arc" | "std::sync::Arc" | "alloc::rc::Rc" | "std::rc::Rc"
        | "alloc::boxed::Box" | "std::boxed::Box" => return ("", true), // erase
        _ => {}
    }
    // Aeneas builtins
    let lean = match rust_path {
        "alloc::vec::Vec" | "std::vec::Vec" => "alloc.vec.Vec",
        "core::option::Option" | "std::option::Option" => "Option",
        "core::result::Result" | "std::result::Result" => "core.result.Result",
        "alloc::string::String" | "std::string::String" => "String",
        "core::num::NonZero" | "std::num::NonZero" => "Usize", // approximate
        "alloc::collections::VecDeque"
        | "std::collections::VecDeque"
        | "alloc::collections::vec_deque::VecDeque"
        | "std::collections::vec_deque::VecDeque" => "alloc.vec.Vec", // VecDeque ≈ Vec in Lean
        // BTreeMap: declared as opaque std.collections.BTreeMap in Types.lean (batch 4)
        "alloc::collections::BTreeMap"
        | "std::collections::BTreeMap"
        | "alloc::collections::btree_map::BTreeMap" => "std.collections.BTreeMap",
        // HashMap: no Lean declaration, erase to Vec (K × V)
        "std::collections::HashMap" | "std::collections::hash_map::HashMap" => "MAP_ERASE",
        "alloc::collections::BTreeSet"
        | "std::collections::BTreeSet"
        | "std::collections::HashSet" => "SET_ERASE",
        _ => "",
    };
    if !lean.is_empty() {
        return (lean, false);
    }
    ("", false)
}
