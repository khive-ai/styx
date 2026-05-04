use crate::ir::*;
use super::{rust_path_to_lean, rust_path_to_lean_type, is_allocator_type, scalar_lean_name};

// ---------------------------------------------------------------------------
// Type emission
// ---------------------------------------------------------------------------

/// Extract the first generic type argument from a return type.
/// Used for zero-arg constructors like Vec::new() where Vec<T>'s T is the type arg.
pub(crate) fn extract_type_arg_from_return(ty: &StyxType) -> Option<String> {
    match ty {
        StyxType::Adt { generic_args, .. } if !generic_args.is_empty() => {
            Some(emit_type(&generic_args[0]))
        }
        _ => None,
    }
}

pub(crate) fn emit_type(ty: &StyxType) -> String {
    match ty {
        StyxType::Scalar(s) => scalar_lean_name(s).to_string(),
        StyxType::Str => "String".to_string(),
        StyxType::Unit => "Unit".to_string(),
        StyxType::Never => "Empty".to_string(),
        StyxType::Unsupported(_) => "STYX_UnsupportedTy".to_string(),

        StyxType::Adt {
            rust_path,
            generic_args,
            ..
        } => {
            let (mapped, erase) = rust_path_to_lean_type(rust_path);
            // Smart pointer erasure: Arc<T> → T
            if erase {
                return if let Some(inner) = generic_args.first() {
                    emit_type(inner)
                } else {
                    "STYX_UnsupportedTy".to_string()
                };
            }
            // Map erasure: Map<K,V> → alloc.vec.Vec (K × V)
            if mapped == "MAP_ERASE" {
                let useful: Vec<&StyxType> = generic_args
                    .iter()
                    .filter(|a| !is_allocator_type(a))
                    .collect();
                return if useful.len() >= 2 {
                    let k = emit_type(useful[0]);
                    let v = emit_type(useful[1]);
                    format!("(alloc.vec.Vec ({k} × {v}))")
                } else {
                    "STYX_UnsupportedTy".to_string()
                };
            }
            // Set erasure: Set<T> → alloc.vec.Vec T
            if mapped == "SET_ERASE" {
                let useful: Vec<&StyxType> = generic_args
                    .iter()
                    .filter(|a| !is_allocator_type(a))
                    .collect();
                return if let Some(elem) = useful.first() {
                    let t = emit_type(elem);
                    format!("(alloc.vec.Vec {t})")
                } else {
                    "STYX_UnsupportedTy".to_string()
                };
            }
            // Use mapped name if available, otherwise convert the path
            let base = if mapped.is_empty() {
                rust_path_to_lean(rust_path)
            } else {
                mapped.to_string()
            };
            // Filter out allocator/phantom type params
            let args: Vec<String> = generic_args
                .iter()
                .filter(|a| !is_allocator_type(a))
                .map(emit_type)
                .collect();
            if args.is_empty() {
                base
            } else {
                format!("({base} {})", args.join(" "))
            }
        }

        StyxType::Tuple(fields) => {
            if fields.is_empty() {
                "Unit".to_string()
            } else {
                let parts: Vec<String> = fields.iter().map(emit_type).collect();
                format!("({})", parts.join(" × "))
            }
        }

        StyxType::Array { elem, len } => {
            let e = emit_type(elem);
            let n = match len {
                StyxConstGeneric::Value(v) => format!("{v}#usize"),
                StyxConstGeneric::Param { name, .. } => name.clone(),
                StyxConstGeneric::Global(_) => "N".to_string(),
            };
            format!("(Array {e} {n})")
        }

        StyxType::Slice(elem) => {
            let e = emit_type(elem);
            format!("(Slice {e})")
        }

        StyxType::Ref { inner, .. } => emit_type(inner), // References erased
        StyxType::RawPtr { inner, .. } => emit_type(inner),

        StyxType::FnPtr { params, ret } => {
            let param_tys: Vec<String> = params.iter().map(emit_type).collect();
            let ret_ty = emit_type(ret);
            if param_tys.is_empty() {
                format!("(Unit → Result {ret_ty})")
            } else {
                format!("({} → Result {ret_ty})", param_tys.join(" → "))
            }
        }

        StyxType::DynTrait { trait_path, .. } => {
            if trait_path.contains("Fn") {
                "STYX_DynTrait".to_string()
            } else {
                "STYX_UnsupportedTy".to_string()
            }
        }

        StyxType::TypeParam { name, .. } => name.clone(),
        StyxType::AssocType { item_name, .. } => format!("Clause0_{item_name}"),
    }
}
