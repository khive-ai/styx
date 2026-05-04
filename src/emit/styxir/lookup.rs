use std::collections::BTreeMap;
use crate::ir::*;


// ---------------------------------------------------------------------------
// Type lookup map: TypeId.0 → &StyxTypeDef
// ---------------------------------------------------------------------------

pub(crate) type TypeLookup<'a> = BTreeMap<u32, &'a StyxTypeDef>;

pub(crate) fn build_type_lookup(pkg: &StyxPackage) -> TypeLookup<'_> {
    pkg.types.iter().map(|td| (td.id.0, td)).collect()
}

pub(crate) fn lookup_variant_name(
    types: &TypeLookup,
    type_id: &TypeId,
    variant_id: &VariantId,
) -> Option<String> {
    if let Some(td) = types.get(&type_id.0)
        && let StyxTypeDefKind::Enum { variants } = &td.kind {
            return variants
                .iter()
                .find(|v| v.id.0 == variant_id.0)
                .map(|v| v.name.clone());
        }
    None
}

/// Map well-known std enum variants by expression type + variant index.
/// Uses the StyxType to distinguish Result from Option (both have variant_id overlap).
pub(crate) fn std_enum_variant_name(ty: &StyxType, variant_id: &VariantId) -> Option<String> {
    let path = match ty {
        StyxType::Adt { rust_path, .. } => rust_path.as_str(),
        _ => return None,
    };
    match (path, variant_id.0) {
        ("core::result::Result" | "std::result::Result", 0) => Some("Ok".to_string()),
        ("core::result::Result" | "std::result::Result", 1) => Some("Err".to_string()),
        // Lean 4 Option uses lowercase constructors
        ("core::option::Option" | "std::option::Option", 0) => Some("none".to_string()),
        ("core::option::Option" | "std::option::Option", 1) => Some("some".to_string()),
        ("core::cmp::Ordering" | "std::cmp::Ordering", 0) => Some("Less".to_string()),
        ("core::cmp::Ordering" | "std::cmp::Ordering", 1) => Some("Equal".to_string()),
        ("core::cmp::Ordering" | "std::cmp::Ordering", 2) => Some("Greater".to_string()),
        // ControlFlow (from Try::branch desugaring)
        (
            "core::ops::ControlFlow"
            | "std::ops::ControlFlow"
            | "core::ops::control_flow::ControlFlow"
            | "std::ops::control_flow::ControlFlow",
            0,
        ) => Some("Continue".to_string()),
        (
            "core::ops::ControlFlow"
            | "std::ops::ControlFlow"
            | "core::ops::control_flow::ControlFlow"
            | "std::ops::control_flow::ControlFlow",
            1,
        ) => Some("Break".to_string()),
        // Infallible (used in FromResidual)
        ("core::convert::Infallible" | "std::convert::Infallible", _) => None, // no constructors
        _ => None,
    }
}

pub(crate) fn lookup_field_name(types: &TypeLookup, type_id: &TypeId, field_id: &FieldId) -> Option<String> {
    let td = types.get(&type_id.0)?;
    let fields: &[StyxFieldDef] = match &td.kind {
        StyxTypeDefKind::Struct { fields } => fields,
        StyxTypeDefKind::Enum { variants } => {
            // Field names are shared across variants in the context of StructInit;
            // for enums we search all variant field lists.
            for variant in variants {
                if let Some(f) = variant.fields.iter().find(|f| f.id.0 == field_id.0) {
                    return Some(f.name.clone());
                }
            }
            return None;
        }
        _ => return None,
    };
    fields
        .iter()
        .find(|f| f.id.0 == field_id.0)
        .map(|f| f.name.clone())
}
