use crate::emit::indent::IndentWriter;
use crate::ir::*;
use crate::naming::escape_lean_keyword;
use super::{emit_header, emit_options, emit_type, emit_generics_binder, contains_unknown_namespace, rust_path_to_lean};

// ---------------------------------------------------------------------------
// Types.lean
// ---------------------------------------------------------------------------

pub(crate) fn emit_types_file(pkg: &StyxPackage, namespace: &str, emit_checks: bool) -> String {
    let mut w = IndentWriter::new();
    emit_header(&mut w);
    emit_options(&mut w);
    w.newline();
    w.writeln(format!("namespace {namespace}"));
    w.newline();

    // Placeholder types
    w.writeln("-- Placeholder type for any Rust types that styx can't translate yet.");
    w.writeln("-- Keeps the generated Lean code parsable/typecheckable under `sorry`.");
    w.writeln("opaque STYX_UnsupportedTy : Type");
    w.writeln("opaque STYX_DynTrait : Type");
    w.newline();

    // External crate opaque types referenced by FunsExternal.lean.
    // These types come from dependency crates that styx-rustc doesn't process.
    // The LLBC/Charon path sees them; styx-rustc must declare them as opaques.
    w.writeln("-- External crate opaques (dependency types referenced by FunsExternal)");
    w.writeln("opaque subtle.Choice : Type");
    w.newline();
    w.writeln("-- Collection type opaque declarations (Rust stdlib collections modeled as opaque)");
    w.writeln("opaque std.collections.BTreeMap (K : Type) (V : Type) : Type");
    w.writeln("opaque std.collections.BTreeSet (K : Type) : Type");
    w.writeln("opaque std.collections.HashMap (K : Type) (V : Type) : Type");
    w.writeln("opaque std.collections.VecDeque (T : Type) : Type");
    w.writeln("opaque alloc.collections.btree.map.BTreeMap (K : Type) (V : Type) : Type");
    w.newline();

    // Topological sort: emit types in dependency order
    let sorted = topo_sort_types(&pkg.types);
    for ty_def in &sorted {
        emit_type_def(&mut w, ty_def, emit_checks);
    }

    w.writeln(format!("end {namespace}"));
    w.finish()
}

/// Topological sort of types so that dependencies are defined before dependents.
pub(crate) fn topo_sort_types(types: &[StyxTypeDef]) -> Vec<&StyxTypeDef> {
    use std::collections::{HashMap, HashSet, VecDeque};

    // Build dependency graph: type_id -> set of type_ids it depends on
    let id_set: HashSet<u32> = types.iter().map(|t| t.id.0).collect();
    let mut deps: HashMap<u32, HashSet<u32>> = HashMap::new();

    for td in types {
        let mut my_deps = HashSet::new();
        match &td.kind {
            StyxTypeDefKind::Struct { fields } => {
                for f in fields {
                    collect_type_deps(&f.ty, &id_set, &mut my_deps);
                }
            }
            StyxTypeDefKind::Enum { variants } => {
                for v in variants {
                    for f in &v.fields {
                        collect_type_deps(&f.ty, &id_set, &mut my_deps);
                    }
                }
            }
            StyxTypeDefKind::Alias { target } => {
                collect_type_deps(target, &id_set, &mut my_deps);
            }
            _ => {}
        }
        my_deps.remove(&td.id.0); // remove self-dependency
        deps.insert(td.id.0, my_deps);
    }

    // Kahn's algorithm
    let mut in_degree: HashMap<u32, usize> = types.iter().map(|t| (t.id.0, 0)).collect();
    // Recompute: in_degree[tid] = number of types in id_set that tid depends on
    for td in types {
        let d = deps.get(&td.id.0).map_or(0, |s| s.len());
        in_degree.insert(td.id.0, d);
    }

    let mut queue: VecDeque<u32> = in_degree
        .iter()
        .filter(|&(_, deg)| *deg == 0)
        .map(|(&id, _)| id)
        .collect();
    let mut ordered: Vec<u32> = Vec::new();

    while let Some(tid) = queue.pop_front() {
        ordered.push(tid);
        // For all types that depend on tid, decrement their in-degree
        for td in types {
            if let Some(d) = deps.get(&td.id.0)
                && d.contains(&tid) {
                    let deg = in_degree.get_mut(&td.id.0).unwrap();
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(td.id.0);
                    }
                }
        }
    }

    // If there are cycles, append remaining types (shouldn't happen for Rust ADTs)
    let ordered_set: HashSet<u32> = ordered.iter().copied().collect();
    for td in types {
        if !ordered_set.contains(&td.id.0) {
            ordered.push(td.id.0);
        }
    }

    // Map back to type defs
    let type_map: HashMap<u32, &StyxTypeDef> = types.iter().map(|t| (t.id.0, t)).collect();
    ordered
        .into_iter()
        .filter_map(|id| type_map.get(&id).copied())
        .collect()
}

/// Collect local type IDs that a type depends on.
pub(crate) fn collect_type_deps(
    ty: &StyxType,
    local_ids: &std::collections::HashSet<u32>,
    out: &mut std::collections::HashSet<u32>,
) {
    match ty {
        StyxType::Adt {
            type_id: Some(tid),
            generic_args,
            ..
        } => {
            if local_ids.contains(&tid.0) {
                out.insert(tid.0);
            }
            for arg in generic_args {
                collect_type_deps(arg, local_ids, out);
            }
        }
        StyxType::Adt {
            type_id: None,
            generic_args,
            ..
        } => {
            for arg in generic_args {
                collect_type_deps(arg, local_ids, out);
            }
        }
        StyxType::Ref { inner, .. } | StyxType::RawPtr { inner, .. } => {
            collect_type_deps(inner, local_ids, out);
        }
        StyxType::Tuple(fields) => {
            for f in fields {
                collect_type_deps(f, local_ids, out);
            }
        }
        StyxType::Array { elem, .. } | StyxType::Slice(elem) => {
            collect_type_deps(elem, local_ids, out);
        }
        StyxType::FnPtr { params, ret } => {
            for p in params {
                collect_type_deps(p, local_ids, out);
            }
            collect_type_deps(ret, local_ids, out);
        }
        _ => {}
    }
}

pub(crate) fn emit_type_def(w: &mut IndentWriter, def: &StyxTypeDef, emit_checks: bool) {
    let lean_name = rust_path_to_lean(&def.rust_path);

    match &def.kind {
        StyxTypeDefKind::Struct { fields } => {
            let generics = emit_generics_binder(&def.generics);
            w.writeln(format!("structure {lean_name}{generics} where"));
            w.indent();
            if fields.is_empty() {
                w.writeln("mk ::"); // unit struct
            } else {
                for field in fields {
                    let fname = escape_lean_keyword(&field.name);
                    let fty = emit_type(&field.ty);
                    w.writeln(format!("{fname} : {fty}"));
                }
            }
            w.dedent();
            if emit_checks {
                w.writeln(format!("#check {lean_name}"));
            }
            w.newline();
        }
        StyxTypeDefKind::Enum { variants } => {
            let generics = emit_generics_binder(&def.generics);
            // @[discriminant] tells Aeneas to derive discriminant helper functions
            // Applied to all enums to match LLBC-mode output
            w.writeln("@[discriminant]");
            w.writeln(format!("inductive {lean_name}{generics} where"));
            w.indent();
            for variant in variants {
                let vname = &variant.name;
                if variant.fields.is_empty() {
                    w.writeln(format!("| {vname}"));
                } else {
                    let fields: Vec<String> = variant
                        .fields
                        .iter()
                        .map(|f| {
                            let fname = escape_lean_keyword(&f.name);
                            let fty = emit_type(&f.ty);
                            format!("({fname} : {fty})")
                        })
                        .collect();
                    w.writeln(format!("| {vname} {}", fields.join(" ")));
                }
            }
            w.dedent();
            if emit_checks {
                w.writeln(format!("#check {lean_name}"));
            }
            w.newline();
        }
        StyxTypeDefKind::Alias { target } => {
            let generics = emit_generics_binder(&def.generics);
            let target_ty = emit_type(target);
            // If the target type references unknown external types, make it opaque
            if contains_unknown_namespace(&target_ty) {
                w.writeln(format!("opaque {lean_name}{generics} : Type"));
            } else {
                w.writeln(format!("abbrev {lean_name}{generics} := {target_ty}"));
            }
            if emit_checks {
                w.writeln(format!("#check {lean_name}"));
            }
            w.newline();
        }
        StyxTypeDefKind::Opaque => {
            w.writeln(format!("opaque {lean_name} : Type"));
            if emit_checks {
                w.writeln(format!("#check {lean_name}"));
            }
            w.newline();
        }
    }
}
