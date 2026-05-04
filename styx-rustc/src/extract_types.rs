// Type extraction: TyCtxt → StyxTypeDef

use rustc_hir::def_id::LocalDefId;
use rustc_middle::ty::{self, TyCtxt};
use rustc_span::Span;

use styx::ir::*;
use crate::ty_convert;

/// Extract an ADT (struct or enum) definition.
pub fn extract_adt_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<StyxTypeDef> {
    let global_id = def_id.to_def_id();
    let def_path = tcx.def_path_str(global_id);
    let name = tcx.item_name(global_id).to_string();
    let span = tcx.def_span(global_id);

    let adt_def = tcx.adt_def(global_id);
    let args = ty::GenericArgs::identity_for_item(tcx, global_id);

    let kind = if adt_def.is_struct() {
        let variant = adt_def.non_enum_variant();
        let fields = extract_fields(tcx, variant, args);
        StyxTypeDefKind::Struct { fields }
    } else if adt_def.is_enum() {
        let variants = adt_def
            .variants()
            .iter_enumerated()
            .map(|(vidx, variant_def)| {
                StyxVariantDef {
                    id: VariantId(vidx.as_u32()),
                    name: variant_def.name.to_string(),
                    fields: extract_fields(tcx, variant_def, args),
                }
            })
            .collect();
        StyxTypeDefKind::Enum { variants }
    } else {
        return None; // unions etc.
    };

    Some(StyxTypeDef {
        id: TypeId(def_id.local_def_index.as_u32()),
        rust_path: def_path,
        name,
        generics: extract_generics(tcx, def_id),
        kind,
        span: convert_span(tcx, span),
    })
}

/// Extract a type alias definition.
pub fn extract_type_alias<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<StyxTypeDef> {
    let global_id = def_id.to_def_id();
    let def_path = tcx.def_path_str(global_id);
    let name = tcx.item_name(global_id).to_string();
    let span = tcx.def_span(global_id);

    let alias_ty = tcx.type_of(global_id).skip_binder();
    let target = ty_convert::convert_ty(tcx, alias_ty);

    Some(StyxTypeDef {
        id: TypeId(def_id.local_def_index.as_u32()),
        rust_path: def_path,
        name,
        generics: extract_generics(tcx, def_id),
        kind: StyxTypeDefKind::Alias { target },
        span: convert_span(tcx, span),
    })
}

fn extract_fields<'tcx>(
    tcx: TyCtxt<'tcx>,
    variant_def: &ty::VariantDef,
    args: ty::GenericArgsRef<'tcx>,
) -> Vec<StyxFieldDef> {
    variant_def
        .fields
        .iter_enumerated()
        .map(|(idx, field_def)| {
            let field_ty = field_def.ty(tcx, args);
            StyxFieldDef {
                id: FieldId(idx.as_u32()),
                name: field_def.name.to_string(),
                ty: ty_convert::convert_ty(tcx, field_ty),
            }
        })
        .collect()
}

/// Extract generic parameters from a definition.
pub fn extract_generics<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) -> StyxGenerics {
    let global_id = def_id.to_def_id();
    let generics = tcx.generics_of(global_id);
    let predicates = tcx.predicates_of(global_id);

    let mut lifetimes = Vec::new();
    let mut type_params = Vec::new();
    let mut const_params = Vec::new();

    for param in &generics.own_params {
        match param.kind {
            ty::GenericParamDefKind::Lifetime => {
                lifetimes.push(param.name.to_string());
            }
            ty::GenericParamDefKind::Type { has_default, .. } => {
                let default = if has_default {
                    let default_ty = tcx.type_of(param.def_id).skip_binder();
                    Some(ty_convert::convert_ty(tcx, default_ty))
                } else {
                    None
                };
                type_params.push(StyxTypeParam {
                    name: param.name.to_string(),
                    default,
                });
            }
            ty::GenericParamDefKind::Const { .. } => {
                let param_ty = tcx.type_of(param.def_id).skip_binder();
                const_params.push(StyxConstParam {
                    name: param.name.to_string(),
                    ty: ty_convert::convert_ty(tcx, param_ty),
                });
            }
        }
    }

    let where_clauses = predicates
        .predicates
        .iter()
        .filter_map(|&(clause, _span)| {
            if let ty::ClauseKind::Trait(trait_pred) = clause.kind().skip_binder() {
                let bounded_ty = ty_convert::convert_ty(tcx, trait_pred.self_ty());
                let trait_path = tcx.def_path_str(trait_pred.def_id());
                let generic_args = trait_pred
                    .trait_ref
                    .args
                    .types()
                    .skip(1)
                    .map(|ty| ty_convert::convert_ty(tcx, ty))
                    .collect();
                Some(StyxWherePredicate {
                    bounded_ty,
                    bounds: vec![StyxTraitBound {
                        trait_path,
                        generic_args,
                    }],
                })
            } else {
                None
            }
        })
        .collect();

    StyxGenerics {
        lifetimes,
        type_params,
        const_params,
        where_clauses,
    }
}

pub fn convert_span(tcx: TyCtxt<'_>, span: Span) -> StyxSpan {
    let source_map = tcx.sess.source_map();
    if let Ok(loc) = source_map.lookup_line(span.lo()) {
        StyxSpan {
            file: source_map
                .filename_for_diagnostics(&loc.sf.name)
                .to_string(),
            line: (loc.line + 1) as u32,
            col: 0,
        }
    } else {
        StyxSpan::default()
    }
}
