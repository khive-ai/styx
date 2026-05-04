use crate::emit::indent::IndentWriter;
use crate::ir::*;
use crate::naming::escape_lean_keyword;
use super::{emit_header, emit_options, emit_type, emit_generics_binder, contains_unknown_namespace, rust_path_to_lean};

// ---------------------------------------------------------------------------
// FunsExternal.lean
// ---------------------------------------------------------------------------

pub(crate) fn emit_funs_external(
    pkg: &StyxPackage,
    namespace: &str,
    sorry_fn_indices: &[usize],
    skip_stdlib: bool,
) -> String {
    let mut w = IndentWriter::new();
    emit_header(&mut w);
    w.writeln(format!("import {namespace}.Types"));
    // Always import AeneasStdlib for Lion-core constants (PAGE_BITS, ALL_RIGHTS_MASK, etc.)
    // and stdlib declarations (Vec, Clone, PartialEq, etc.)
    w.writeln(format!("import {namespace}.AeneasStdlib"));
    emit_options(&mut w);
    w.newline();
    w.writeln(format!("namespace {namespace}"));
    w.newline();

    let sorry_set: std::collections::HashSet<usize> = sorry_fn_indices.iter().copied().collect();

    // External functions: those without bodies + those with sorry in bodies
    // Skip functions whose signatures reference unresolvable external types
    for (idx, fun_def) in pkg.functions.iter().enumerate() {
        if fun_def.body.is_none() || sorry_set.contains(&idx) {
            let lean_name = rust_path_to_lean(&fun_def.rust_path);
            let ret_ty = emit_type(&fun_def.ret_ty);
            let params: Vec<String> = fun_def
                .params
                .iter()
                .map(|p| {
                    let pname = escape_lean_keyword(&p.name);
                    let pty = emit_type(&p.ty);
                    format!("({pname} : {pty})")
                })
                .collect();

            // Check if signature references unknown types (std.fmt, etc.)
            let sig = format!("{} {} {}", lean_name, params.join(" "), ret_ty);
            if contains_unknown_namespace(&sig) {
                w.writeln(format!("-- skipped (unresolvable types): {lean_name}"));
                w.newline();
                continue;
            }

            let generics = emit_generics_binder(&fun_def.generics);
            let params_str = if params.is_empty() {
                String::new()
            } else {
                format!(" {}", params.join(" "))
            };
            w.writeln(format!(
                "opaque {lean_name}{generics}{params_str} : Result {ret_ty}"
            ));
            w.newline();
        }
    }

    // ---------------------------------------------------------------------------
    // Stdlib declarations: Try, FromResidual, Option, Result methods.
    // Skipped when --no-stdlib is passed (AeneasStdlib provides them instead).
    // ---------------------------------------------------------------------------
    if !skip_stdlib {
        w.writeln("-- ===== Stdlib: Try/FromResidual (? operator) =====");
        w.newline();
        w.writeln("-- TryResult.branch: transparent definition matching Rust semantics.");
        w.writeln("-- Result<T,E>::branch maps Ok(v) → Continue(v), Err(e) → Break(Err(e))");
        w.writeln("def core.result.TryResultResultInfallible.branch (T : Type) (E : Type)");
        w.writeln("    (arg0 : core.result.Result T E) : Result (core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T) :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Ok v => pure (.Continue v)");
        w.writeln("  | .Err e => pure (.Break (.Err e))");
        w.newline();
        w.writeln("-- TryResult.from_output: wraps value in Ok");
        w.writeln("def core.result.TryResultResultInfallible.from_output (T : Type) (_E : Type) (arg0 : T) : Result (core.result.Result T _E) :=");
        w.writeln("  pure (.Ok arg0)");
        w.newline();
        w.writeln("-- FromResidual: converts residual error back to Result");
        w.writeln("def core.result.FromResidualResultResultInfallible.from_residual");
        w.writeln("    (T : Type) (E : Type) (F : Type) (convertFromInst : core.convert.From E F)");
        w.writeln("    (arg0 : core.result.Result core.convert.Infallible F) : Result (core.result.Result T E) :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Err f => do");
        w.writeln("    let e ← convertFromInst.from_ f");
        w.writeln("    pure (.Err e)");
        w.writeln("  | .Ok i => nomatch i");
        w.newline();

        // ---------------------------------------------------------------------------
        // Stdlib: Option methods
        // ---------------------------------------------------------------------------
        w.writeln("-- ===== Stdlib: Option methods =====");
        w.newline();
        w.writeln("def std.option.Option.is_some (T : Type) (arg0 : Option T) : Result Bool :=");
        w.writeln("  ok (arg0.isSome)");
        w.newline();
        w.writeln("def std.option.Option.is_none (T : Type) (arg0 : Option T) : Result Bool :=");
        w.writeln("  ok (arg0.isNone)");
        w.newline();
        w.writeln(
            "def std.option.Option.unwrap_or (T : Type) (arg0 : Option T) (arg1 : T) : Result T :=",
        );
        w.writeln("  ok (arg0.getD arg1)");
        w.newline();
        w.writeln("def std.option.Option.ok_or (T : Type) (E : Type) (arg0 : Option T) (arg1 : E) : Result (core.result.Result T E) :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .some v => pure (.Ok v)");
        w.writeln("  | .none => pure (.Err arg1)");
        w.newline();
        w.writeln("def std.option.Option.map (T : Type) (U : Type) (arg0 : Option T) (arg1 : T → U) : Result (Option U) :=");
        w.writeln("  ok (arg0.map arg1)");
        w.newline();
        w.writeln("def std.option.Option.expect (T : Type) (arg0 : Option T) (_msg : String) : Result T :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .some v => ok v");
        w.writeln("  | .none => fail .panic");
        w.newline();
        w.writeln("def std.option.Option.unwrap (T : Type) (arg0 : Option T) : Result T :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .some v => ok v");
        w.writeln("  | .none => fail .panic");
        w.newline();
        w.writeln("-- ===== Stdlib: Result methods =====");
        w.newline();
        w.writeln("def std.result.Result.is_ok (T : Type) (E : Type) (arg0 : core.result.Result T E) : Result Bool :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Ok _ => ok true");
        w.writeln("  | .Err _ => ok false");
        w.newline();
        w.writeln("def std.result.Result.is_err (T : Type) (E : Type) (arg0 : core.result.Result T E) : Result Bool :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Ok _ => ok false");
        w.writeln("  | .Err _ => ok true");
        w.newline();
        w.writeln("def std.result.Result.ok (T : Type) (E : Type) (arg0 : core.result.Result T E) : Result (Option T) :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Ok v => pure (.some v)");
        w.writeln("  | .Err _ => pure .none");
        w.newline();
        w.writeln("def std.result.Result.map_err (T : Type) (E : Type) (F : Type) (arg0 : core.result.Result T E) (arg1 : E → F) : Result (core.result.Result T F) :=");
        w.writeln("  match arg0 with");
        w.writeln("  | .Ok v => pure (.Ok v)");
        w.writeln("  | .Err e => pure (.Err (arg1 e))");
        w.newline();
    } // end if !skip_stdlib

    w.writeln(format!("end {namespace}"));
    w.finish()
}
