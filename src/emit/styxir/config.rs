use crate::ir::*;

/// Check if a type string references namespaces that are NOT part of Aeneas/styx stdlib.
/// Known namespaces: alloc, core, std (from Aeneas), plus the crate's own namespace.
pub(crate) fn contains_unknown_namespace(text: &str) -> bool {
    // External crate names that we can't resolve
    let unknown_prefixes = [
        // "hmac." — REMOVED: hmac.Mac.* declared in AeneasStdlib (2026-04-26)
        "sha2.",
        // "subtle." — REMOVED: subtle.Choice, subtle.ConstantTimeEq.ct_eq declared in AeneasStdlib
        // "digest." — REMOVED: hmac.digest.CtOutput.into_bytes declared (2026-04-26)
        "crypto_common.",
        "block_buffer.",
        // "typenum." — REMOVED: collapsed to Array by emitter text-pass (2026-04-26)
        // "generic_array." — REMOVED: collapsed to Array by emitter text-pass (2026-04-26)
        "std.fmt.Formatter", // Display::fmt bodies use Formatter — sorry (write! macro)
        "std.fmt.rt.",      // format runtime internals
        "std.io.",
        "std.slice.",
        // std.hash.Hash.hash: REMOVED — declared in AeneasStdlib.lean (opaque stub).
        // Derived Hash impls now emit transparently.
        // std.collections.BTreeMap: REMOVED — entry/get_mut/entry_or_insert_with now mapped
        // via map_std_callee to alloc.collections.btree.map.BTreeMap.* (AeneasStdlib decls, batch 4).
        "std.cmp.Ordering", // Ordering type not defined in Lean
    ];
    if unknown_prefixes.iter().any(|p| text.contains(p)) {
        return true;
    }
    // Functions/constants that don't exist in Aeneas/Lean std library
    // Functions/constants not declared in FunsExternal.lean.
    // IMPORTANT: If you add a declaration to FunsExternal, remove it from this list
    // so functions that call it can be emitted transparently.
    //
    // NOTE: Some of these ARE declared in FunsExternal but can't be unblocked yet because
    // the emitter generates wrong namespaces (std.ops.Try.branch → should be core.ops.try_trait.Try.branch)
    // or broken lambda captures (local_17 instead of parameter name). Fix those in the emitter first,
    // then remove from this list.
    let unknown_fns = [
        // Functions that are NOT declared in AeneasStdlib or FunsExternal.
        // Callers containing these names cannot compile because the callee is missing.
        //
        // MAPPED+DECLARED (removed from this list — now in map_std_callee + AeneasStdlib):
        //   std.option.Option.{is_some,is_none,expect,unwrap,unwrap_or,ok_or,map}
        //   std.result.Result.{is_ok,is_err,ok,map_err}
        //   std.ops.Try.branch, std.ops.FromResidual
        //   std.cmp.{PartialEq.eq,Ord.cmp,Ordering}
        //   std.default.Default.default, std.intrinsics.discriminant_value
        //   core.num.saturating_add
        //   core.num.saturating_sub, core.num.count_ones  (AeneasStdlib 2026-04-12)
        //   alloc.vec.Vec.{remove,pop_front,contains,extend_from_slice,sort_unstable,retain}  (2026-04-12)
        //   core.slice.iter, core.slice.binary_search_by_key  (AeneasStdlib 2026-04-13)
        //   std.iter.Iterator.{all,any,find,find_map,map,collect}  (AeneasStdlib 2026-04-13, fixed signatures)
        //   std.convert.Into.into, core.convert.Into.into  (AeneasStdlib 2026-04-13)
        //
        // Still blocked (no AeneasStdlib declaration or fundamental emission issue):
        // "core.slice.binary_search_by_key" — REMOVED: now declared in AeneasStdlib (2026-04-13)
        //   Transparent linear scan with f : T → K (pure closure, matching fun entry => entry.1).
        // "core.slice.iter" — REMOVED: restored in AeneasStdlib (2026-04-13)
        // "std.iter.Iterator.all" — REMOVED: restored in AeneasStdlib (2026-04-13)
        // "std.iter.Iterator.map" — REMOVED: restored in AeneasStdlib (2026-04-13)
        // "std.iter.Iterator.collect" — REMOVED: restored in AeneasStdlib (2026-04-13)
        // "std.convert.Into.into" — REMOVED: restored in AeneasStdlib (2026-04-13)
        // "std.option.Option.cloned" — REMOVED: restored in AeneasStdlib (2026-04-13)
        "std.ops.Fn.call",          // closure call — needs closure conversion pass
        // "std.iter.Extend.extend" — REMOVED: declared in AeneasStdlib (opaque, #306 2026-04-17)
        // "std.iter.Iterator.filter " — REMOVED: declared in AeneasStdlib (2026-04-26)
        "std.cmp.PartialEq.ne",     // ne for ADT types: needs type-specific impl routing
        "core.cmp.PartialEq.ne",    // same, core namespace variant
        // "std.sync.Arc.new" — REMOVED: now declared in AeneasStdlib (identity wrapper, batch 3)
        // "std.sync.Arc"     — REMOVED: Arc<T>=T in Lean; type erased by Aeneas, only Arc.new needed
        // "std.string.String.as_str" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "std.string.String.is_empty" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "std.string.String" — REMOVED: String type stubs now in AeneasStdlib (2026-04-26)
        // "std.string.ToString" — REMOVED: declared in AeneasStdlib (identity on String literals)
        // "std.str.to_lowercase" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "core.str.strip_prefix" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "core.str.parse" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "core.str.trim" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "std.vec.from_elem" — REMOVED: mapped to alloc.vec.Vec.from_elem in map_std_callee (declared in AeneasStdlib)
        // "core.slice.binary_search_by_key" — REMOVED: now declared in AeneasStdlib (2026-04-13)
        // "core.slice.copy_from_slice" — REMOVED: declared in AeneasStdlib (2026-04-26)
        // "core.slice.iter" — REMOVED: now declared in AeneasStdlib (2026-04-13)
        // "core.num.checked_add" — REMOVED: now declared in AeneasStdlib (polymorphic over UScalar)
        "core.num.MAX", // constant — needs model
        // MAPPED: constants now in AeneasStdlib (2026-04-12)
        // "state.memory.PAGE_BITS", "state.memory.PAGE_SIZE",
        // "types.capability.Key.SIZE", "types.capability.Hash32.SIZE",
        // "types.rights.ALL_RIGHTS_MASK", "types.security.SecurityLevel.TOP/BOT",
        // "state.plugin.DEFAULT_QUOTA",
        "thiserror.", // error derive macro artifacts
        // "core.cmp.PartialEq.eq" — REMOVED: now routed to type-specific impls via map_partial_eq_callee
        "core.cmp.PartialOrd", // generic PartialOrd — needs type args
        // NOTE: std.cmp.PartialOrd intentionally NOT here — biba_write_ok uses it and
        // was transparent in baseline (accepted pre-existing error).
        // "core.slice.first" — REMOVED: now declared in AeneasStdlib
        // "std.option.Option.copied" — REMOVED: now declared in AeneasStdlib
        // "std.option.Option.cloned" — REMOVED: declared in AeneasStdlib (identity, like copied)
        // "std.convert.Into.into" — REMOVED: now declared in AeneasStdlib (2026-04-13)
        // "core.intrinsics.discriminant_value" — REMOVED: now declared in AeneasStdlib (returns Isize)
        "core.cmp.Ord.cmp", // generic Ord — needs type args
                            // "core.default.Default.default" — REMOVED: now routed to type-specific impls via map_default_callee
                            // "core.ops.deref.Deref.deref" — REMOVED: now handled as identity for Vec in emit_expr
                            // "core.ops.deref.DerefMut.deref_mut" — REMOVED: same
    ];
    unknown_fns.iter().any(|f| text.contains(f))
}

/// Functions whose emitted bodies have Lean type errors that cannot be fixed
/// by the emitter's current desugar passes. These are guarded as opaque until
/// the underlying emission issue is resolved or the body is manually fixed.
///
/// Errors diagnosed from lake build on 2026-04-13:
///   - field-assign-as-expr (set_blocked_mut, unblock_mut, set_pending_send, KeyState.rotate, etc.)
///   - BTreeMap method calls (MetaState, LinearMemory — BTreeMap opaque type, no method decls)
///   - core.slice.binary_search_by_key used with wrong tuple projection (.field_1)
///   - cannot lift ← over binder (closure/lambda in body)
///   - unknown identifiers: core.slice.binary_search_by_key (still not declared correctly)
///   - Result.some (nonexistent variant), dotted ctor for custom enums
///   - std.option.Option.cloned / std.convert.Into.into used in body (namespace mismatch)
///   - Iterator stubs fixed: all/any/find/find_map/map/collect now use implicit {IterT ItemT}
pub(crate) fn is_force_opaque(rust_path: &str) -> bool {
    let force_opaque_fns: &[&str] = &[
        // BTreeMap/Entry body patterns — testing if still needed
        // "state::memory::LinearMemory::read" — FIXED: BTreeMap.get declared, compiles
        // "state::memory::LinearMemory::write_mut" — TESTING: entry_or_insert_with declared
        // "state::memory::MetaState::free_mut" — TESTING: BTreeMap.get_mut declared
        // "step::host_call::execute_cap_send" — FIXED wave2c Batch 2 (error-channel for-in loop)
        // "step::host_call::execute_cap_send_mut" — FIXED wave2c Batch 2 (error-channel for-in loop)
        // "<types::rights::Rights as std::iter::FromIterator<types::rights::Right>>::from_iter" — FIXED wave2c Batch 1
        // "state::workflow::WorkflowDef::validated" — FIXED wave2c Batch 2 (error-channel for-in loop)
        // "step::execute_plugin_internal" — TESTING: body errors may be resolved
        // "step::execute_plugin_internal_mut" — TESTING: body errors may be resolved
        // "step::reachable" — FIXED wave2c Batch 2 (error-channel for-in loop, ? uses panic semantics)
        // "state::kernel::RevocationState::revoke_mut" — TESTING: .Ok/.Err should resolve in Result monad context
        // "state::kernel::RevocationState::revoke_transitive_fast_mut" — TESTING: same

        // "state::memory::LinearMemory::read_range" — TESTING: struct range with ← may compile now
        // "state::kernel::RevocationState::revoke_transitive_mut" — TESTING: closure tuple destructure
    ];
    force_opaque_fns.contains(&rust_path)
}

pub(crate) fn scalar_of_ty(ty: &StyxType) -> Option<ScalarTy> {
    match ty {
        StyxType::Scalar(s) => Some(*s),
        StyxType::Ref { inner, .. } => scalar_of_ty(inner),
        _ => None,
    }
}

pub(crate) fn is_unsigned_scalar(s: &ScalarTy) -> bool {
    matches!(
        s,
        ScalarTy::U8
            | ScalarTy::U16
            | ScalarTy::U32
            | ScalarTy::U64
            | ScalarTy::U128
            | ScalarTy::Usize
    )
}

pub(crate) fn is_signed_scalar(s: &ScalarTy) -> bool {
    matches!(
        s,
        ScalarTy::I8
            | ScalarTy::I16
            | ScalarTy::I32
            | ScalarTy::I64
            | ScalarTy::I128
            | ScalarTy::Isize
    )
}

pub(crate) fn scalar_lean_name(s: &ScalarTy) -> &'static str {
    match s {
        ScalarTy::U8 => "U8",
        ScalarTy::U16 => "U16",
        ScalarTy::U32 => "U32",
        ScalarTy::U64 => "U64",
        ScalarTy::U128 => "U128",
        ScalarTy::Usize => "Usize",
        ScalarTy::I8 => "I8",
        ScalarTy::I16 => "I16",
        ScalarTy::I32 => "I32",
        ScalarTy::I64 => "I64",
        ScalarTy::I128 => "I128",
        ScalarTy::Isize => "Isize",
        ScalarTy::Bool => "Bool",
        ScalarTy::Char => "Char",
    }
}

pub(crate) fn scalar_suffix(s: &ScalarTy) -> &'static str {
    match s {
        ScalarTy::U8 => "u8",
        ScalarTy::U16 => "u16",
        ScalarTy::U32 => "u32",
        ScalarTy::U64 => "u64",
        ScalarTy::U128 => "u128",
        ScalarTy::Usize => "usize",
        ScalarTy::I8 => "i8",
        ScalarTy::I16 => "i16",
        ScalarTy::I32 => "i32",
        ScalarTy::I64 => "i64",
        ScalarTy::I128 => "i128",
        ScalarTy::Isize => "isize",
        ScalarTy::Bool => "bool",
        ScalarTy::Char => "char",
    }
}
