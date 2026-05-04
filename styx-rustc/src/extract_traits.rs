// Trait extraction: TyCtxt → StyxTraitDecl / StyxTraitImpl

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self, TyCtxt};

use styx::ir::*;
use crate::ty_convert;
use crate::extract_types;

// ============================================================================
// Trait declarations
// ============================================================================

/// Extract a trait declaration from a local def_id with DefKind::Trait.
pub fn extract_trait_decl<'tcx>(
    tcx: TyCtxt<'tcx>,
    trait_did: LocalDefId,
) -> Option<StyxTraitDecl> {
    let def_id = trait_did.to_def_id();
    let rust_path = tcx.def_path_str(def_id);
    let name = tcx.item_name(def_id).to_string();

    // Associated items: collect Fn items as method signatures.
    let assoc_items = tcx.associated_items(def_id);
    let methods: Vec<StyxTraitMethodSig> = assoc_items
        .in_definition_order()
        .filter(|item| matches!(item.kind, ty::AssocKind::Fn { .. }))
        .filter_map(|item| extract_trait_method_sig(tcx, item))
        .collect();

    // Super-trait bounds from explicit_super_predicates_of.
    let super_preds = tcx.explicit_super_predicates_of(def_id);
    let super_traits: Vec<StyxTraitBound> = super_preds
        .skip_binder()
        .into_iter()
        .filter_map(|(clause, _span)| {
            if let ty::ClauseKind::Trait(trait_pred) = clause.kind().skip_binder() {
                // Skip the self-predicate (the trait itself appears as its own super-predicate).
                if trait_pred.def_id() == def_id {
                    return None;
                }
                let trait_path = tcx.def_path_str(trait_pred.def_id());
                let generic_args = trait_pred
                    .trait_ref
                    .args
                    .types()
                    .skip(1) // skip Self
                    .map(|ty| ty_convert::convert_ty(tcx, ty))
                    .collect();
                Some(StyxTraitBound { trait_path, generic_args })
            } else {
                None
            }
        })
        .collect();

    let generics = extract_types::extract_generics(tcx, trait_did);

    Some(StyxTraitDecl {
        id: TraitDeclId(trait_did.local_def_index.as_u32()),
        rust_path,
        name,
        generics,
        methods,
        super_traits,
    })
}

/// Extract a single trait method signature from an AssocItem in a trait declaration.
fn extract_trait_method_sig<'tcx>(
    tcx: TyCtxt<'tcx>,
    item: &ty::AssocItem,
) -> Option<StyxTraitMethodSig> {
    let name = item.name().to_string();

    // Get function signature (skip outer binder — no late-bound regions needed here).
    let fn_sig = tcx.fn_sig(item.def_id).skip_binder().skip_binder();

    let params: Vec<StyxParam> = fn_sig
        .inputs()
        .iter()
        .enumerate()
        .map(|(i, &ty)| StyxParam {
            name: format!("arg{i}"),
            ty: ty_convert::convert_ty(tcx, ty),
            is_mut_self: false,
            local_id: None,
        })
        .collect();

    let ret_ty = ty_convert::convert_ty(tcx, fn_sig.output());

    // A trait method has a default implementation if it has a body.
    // item.defaultness(tcx).has_value() is true for both Final (inherent/impl) and
    // Default { has_value: true } (trait default), so it correctly signals "has body".
    let has_default = item.defaultness(tcx).has_value()
        && matches!(item.container, ty::AssocContainer::Trait);

    Some(StyxTraitMethodSig { name, params, ret_ty, has_default })
}

// ============================================================================
// Trait implementations
// ============================================================================

/// Extract a trait implementation from a local def_id with DefKind::Impl { of_trait: true }.
pub fn extract_trait_impl<'tcx>(
    tcx: TyCtxt<'tcx>,
    impl_did: LocalDefId,
) -> Option<StyxTraitImpl> {
    let def_id = impl_did.to_def_id();

    // impl_trait_ref panics if called on an inherent impl — caller must ensure of_trait: true.
    let trait_ref = tcx.impl_trait_ref(def_id).skip_binder();
    let trait_path = tcx.def_path_str(trait_ref.def_id);
    let self_ty = ty_convert::convert_ty(tcx, trait_ref.self_ty());

    // trait_id: if the trait is local we can store a TraitDeclId, otherwise None.
    let trait_id = if trait_ref.def_id.is_local() {
        let local = trait_ref.def_id.expect_local();
        Some(TraitDeclId(local.local_def_index.as_u32()))
    } else {
        None
    };

    // Collect method implementations (Fn associated items only).
    let assoc_items = tcx.associated_items(def_id);
    let methods: Vec<StyxTraitMethodImpl> = assoc_items
        .in_definition_order()
        .filter(|item| matches!(item.kind, ty::AssocKind::Fn { .. }))
        .map(|item| StyxTraitMethodImpl {
            name: item.name().to_string(),
            fun_id: FunId(item.def_id.expect_local().local_def_index.as_u32()),
        })
        .collect();

    let generics = extract_types::extract_generics(tcx, impl_did);

    Some(StyxTraitImpl {
        id: TraitImplId(impl_did.local_def_index.as_u32()),
        trait_path,
        trait_id,
        self_ty,
        generics,
        methods,
    })
}

// ============================================================================
// Global constants and statics
// ============================================================================

/// Extract a global const or static from a local def_id.
pub fn extract_global_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<StyxGlobalDef> {
    let global_id = def_id.to_def_id();
    let rust_path = tcx.def_path_str(global_id);
    let name = tcx.item_name(global_id).to_string();
    let span = tcx.def_span(global_id);

    let ty = tcx.type_of(global_id).skip_binder();
    let converted_ty = ty_convert::convert_ty(tcx, ty);

    Some(StyxGlobalDef {
        id: GlobalId(def_id.local_def_index.as_u32()),
        rust_path,
        name,
        ty: converted_ty,
        value: None, // body evaluation deferred; emitter marks as opaque
        span: extract_types::convert_span(tcx, span),
    })
}
