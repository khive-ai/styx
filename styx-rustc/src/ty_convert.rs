// Type conversion: rustc Ty → StyxType
//
// Converts rustc's internal type representation to our owned StyxType enum.
// This is the bridge between compiler-lifetime-bound types and the
// serializable StyxIR types.

use rustc_middle::ty::{self, Ty, TyCtxt};

use styx::ir::*;

/// Convert a rustc Ty to a StyxType.
pub fn convert_ty<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> StyxType {
    match ty.kind() {
        // Primitive scalars
        ty::Bool => StyxType::Scalar(ScalarTy::Bool),
        ty::Char => StyxType::Scalar(ScalarTy::Char),
        ty::Int(int_ty) => StyxType::Scalar(convert_int_ty(*int_ty)),
        ty::Uint(uint_ty) => StyxType::Scalar(convert_uint_ty(*uint_ty)),

        // String types
        ty::Str => StyxType::Str,

        // ADT (struct, enum, union)
        ty::Adt(adt_def, args) => {
            let rust_path = tcx.def_path_str(adt_def.did());
            let type_id = if adt_def.did().is_local() {
                Some(TypeId(adt_def.did().expect_local().local_def_index.as_u32()))
            } else {
                None
            };
            let generic_args: Vec<_> = args
                .types()
                .map(|t| convert_ty(tcx, t))
                .collect();
            let const_args: Vec<_> = args
                .consts()
                .map(|c| convert_const_generic(tcx, c))
                .collect();
            StyxType::Adt {
                rust_path,
                type_id,
                generic_args,
                const_args,
            }
        }

        // Tuple
        ty::Tuple(fields) => {
            if fields.is_empty() {
                StyxType::Unit
            } else {
                StyxType::Tuple(fields.iter().map(|t| convert_ty(tcx, t)).collect())
            }
        }

        // Array [T; N]
        ty::Array(elem, len) => StyxType::Array {
            elem: Box::new(convert_ty(tcx, *elem)),
            len: convert_const_generic(tcx, *len),
        },

        // Slice [T]
        ty::Slice(elem) => StyxType::Slice(Box::new(convert_ty(tcx, *elem))),

        // Reference &T / &mut T
        ty::Ref(_, inner, mutability) => StyxType::Ref {
            inner: Box::new(convert_ty(tcx, *inner)),
            is_mut: mutability.is_mut(),
        },

        // Raw pointer *const T / *mut T
        ty::RawPtr(inner, mutability) => StyxType::RawPtr {
            inner: Box::new(convert_ty(tcx, *inner)),
            is_mut: mutability.is_mut(),
        },

        // Function pointer fn(A, B) -> C
        ty::FnPtr(sig_tys, _header) => {
            let sig = sig_tys.skip_binder();
            let params = sig.inputs().iter().map(|t| convert_ty(tcx, *t)).collect();
            let ret = Box::new(convert_ty(tcx, sig.output()));
            StyxType::FnPtr { params, ret }
        }

        // Dynamic trait object dyn Trait
        ty::Dynamic(binder, _region) => {
            if let Some(principal) = binder.principal() {
                let def_id = principal.skip_binder().def_id;
                let trait_path = tcx.def_path_str(def_id);
                StyxType::DynTrait {
                    trait_path,
                    generic_args: vec![], // TODO: extract generic args
                }
            } else {
                StyxType::Unsupported("dyn (no principal)".to_string())
            }
        }

        // Type parameter T
        ty::Param(param_ty) => StyxType::TypeParam {
            index: param_ty.index,
            name: param_ty.name.to_string(),
        },

        // Never type !
        ty::Never => StyxType::Never,

        // Alias types (associated types, opaque types, etc.)
        ty::Alias(kind, alias_ty) => {
            match kind {
                ty::AliasTyKind::Projection => {
                    // Associated type: <T as Trait>::Assoc
                    let trait_def_id = tcx.parent(alias_ty.def_id);
                    let trait_path = tcx.def_path_str(trait_def_id);
                    let item_name = tcx.item_name(alias_ty.def_id).to_string();
                    let self_ty = alias_ty.args.type_at(0);
                    StyxType::AssocType {
                        trait_path,
                        item_name,
                        self_ty: Box::new(convert_ty(tcx, self_ty)),
                    }
                }
                _ => StyxType::Unsupported(format!("alias({kind:?})")),
            }
        }

        // Closure types
        ty::Closure(_, args) => {
            let sig = args.as_closure().sig();
            let typing_env = ty::TypingEnv::fully_monomorphized();
            let sig = tcx.normalize_erasing_late_bound_regions(typing_env, sig);
            let params = sig.inputs().iter().map(|t| convert_ty(tcx, *t)).collect();
            let ret = Box::new(convert_ty(tcx, sig.output()));
            StyxType::FnPtr { params, ret }
        }

        // Anything else is unsupported
        _ => StyxType::Unsupported(format!("{ty:?}")),
    }
}

pub fn convert_int_ty(int_ty: ty::IntTy) -> ScalarTy {
    match int_ty {
        ty::IntTy::I8 => ScalarTy::I8,
        ty::IntTy::I16 => ScalarTy::I16,
        ty::IntTy::I32 => ScalarTy::I32,
        ty::IntTy::I64 => ScalarTy::I64,
        ty::IntTy::I128 => ScalarTy::I128,
        ty::IntTy::Isize => ScalarTy::Isize,
    }
}

pub fn convert_uint_ty(uint_ty: ty::UintTy) -> ScalarTy {
    match uint_ty {
        ty::UintTy::U8 => ScalarTy::U8,
        ty::UintTy::U16 => ScalarTy::U16,
        ty::UintTy::U32 => ScalarTy::U32,
        ty::UintTy::U64 => ScalarTy::U64,
        ty::UintTy::U128 => ScalarTy::U128,
        ty::UintTy::Usize => ScalarTy::Usize,
    }
}

pub fn convert_const_generic<'tcx>(tcx: TyCtxt<'tcx>, ct: ty::Const<'tcx>) -> StyxConstGeneric {
    match ct.kind() {
        ty::ConstKind::Value(cv) => {
            // Try to extract a concrete integer value
            if let Some(val) = cv.try_to_target_usize(tcx) {
                StyxConstGeneric::Value(val as u128)
            } else {
                StyxConstGeneric::Value(0) // Fallback
            }
        }
        ty::ConstKind::Param(param) => StyxConstGeneric::Param {
            index: param.index,
            name: param.name.to_string(),
        },
        _ => StyxConstGeneric::Value(0), // Fallback for complex const expressions
    }
}
