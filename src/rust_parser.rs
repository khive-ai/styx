//! Direct Rust source file parser for type definitions.
//!
//! Parses `pub struct` and `pub enum` definitions from `.rs` files using `syn`.
//! This bypasses Charon for types that cannot be extracted via LLBC (e.g., types
//! using BTreeMap, HashMap, Arc<dyn Trait>, String).
//!
//! Type definitions are purely structural — no borrow analysis needed.

use std::path::Path;

use anyhow::{Context, Result};

use crate::type_rewrite::RewriteRules;

/// A parsed Rust type definition (struct or enum).
#[derive(Debug, Clone)]
pub struct ParsedTypeDef {
    /// Fully qualified name (e.g., "lion_core.state.State").
    pub name: String,
    /// Simple name (e.g., "State").
    pub simple_name: String,
    /// Generic type parameters (e.g., ["T", "U"]).
    pub type_params: Vec<String>,
    /// The kind of type.
    pub kind: ParsedTypeKind,
    /// Source file path.
    pub source_file: String,
}

/// Struct, enum, or type alias.
#[derive(Debug, Clone)]
pub enum ParsedTypeKind {
    Struct(Vec<ParsedField>),
    Enum(Vec<ParsedVariant>),
    /// Type alias (e.g., `pub type PluginId = u64;`).
    Alias(RustType),
}

/// A struct field.
#[derive(Debug, Clone)]
pub struct ParsedField {
    pub name: String,
    pub ty: RustType,
}

/// An enum variant.
#[derive(Debug, Clone)]
pub struct ParsedVariant {
    pub name: String,
    pub fields: Vec<ParsedField>,
}

/// Representation of a Rust type for rewriting.
#[derive(Debug, Clone)]
pub enum RustType {
    /// Simple named type (e.g., "u64", "SecurityLevel").
    Named(String),
    /// Generic type application (e.g., "Vec<u8>", "BTreeMap<u64, Thing>").
    Generic(String, Vec<RustType>),
    /// Tuple (e.g., "(u64, String)").
    Tuple(Vec<RustType>),
    /// Reference (erased in Lean).
    Ref(Box<RustType>),
    /// Raw pointer (erased in Lean).
    RawPtr(Box<RustType>),
    /// Array type [T; N].
    Array(Box<RustType>, String),
    /// Slice type [T].
    Slice(Box<RustType>),
    /// Unit type ().
    Unit,
    /// Dynamic trait object (dyn Trait).
    DynTrait(String),
    /// Type we couldn't parse.
    Unknown(String),
}

/// A parsed Rust function signature (top-level fn or impl method).
#[derive(Debug, Clone)]
pub struct ParsedFnSig {
    /// Fully qualified name (e.g., "Capability.new" or "kernel_dispatch").
    pub name: String,
    /// Generic type parameters (e.g., ["T", "U"]).
    pub type_params: Vec<String>,
    /// Parameters as (name, type) pairs.
    pub params: Vec<(String, RustType)>,
    /// Return type.
    pub ret_type: RustType,
    /// True if the first parameter is self/&self/&mut self.
    pub is_method: bool,
    /// The impl'd type name (e.g., "Capability") for methods.
    pub self_type: Option<String>,
    /// True if &mut self (return includes updated self).
    pub is_mut_self: bool,
    /// Source file path.
    pub source_file: String,
}

/// Combined parse result for the direct mode.
#[derive(Debug, Clone)]
pub struct ParsedCrate {
    pub types: Vec<ParsedTypeDef>,
    pub fns: Vec<ParsedFnSig>,
}

/// Parse all pub struct/enum definitions from a directory of Rust source files.
pub fn parse_rust_types(src_dir: &Path) -> Result<Vec<ParsedTypeDef>> {
    let mut types = Vec::new();
    parse_dir_recursive(src_dir, &[], &mut types, &mut Vec::new())?;
    Ok(types)
}

/// Parse all pub types and function signatures from a directory of Rust source files.
pub fn parse_rust_crate(src_dir: &Path) -> Result<ParsedCrate> {
    let mut types = Vec::new();
    let mut fns = Vec::new();
    parse_dir_recursive(src_dir, &[], &mut types, &mut fns)?;
    Ok(ParsedCrate { types, fns })
}

fn parse_dir_recursive(
    dir: &Path,
    module_path: &[String],
    types: &mut Vec<ParsedTypeDef>,
    fns: &mut Vec<ParsedFnSig>,
) -> Result<()> {
    if !dir.is_dir() {
        return Ok(());
    }

    let mut entries: Vec<_> = std::fs::read_dir(dir)
        .with_context(|| format!("failed to read directory: {}", dir.display()))?
        .filter_map(|e| e.ok())
        .collect();
    entries.sort_by_key(|e| e.file_name());

    for entry in entries {
        let path = entry.path();
        if path.is_dir() {
            // Recurse into subdirectories as Rust modules.
            let mod_name = path
                .file_name()
                .and_then(|n| n.to_str())
                .unwrap_or("")
                .to_string();
            let mut child_path = module_path.to_vec();
            child_path.push(mod_name);
            parse_dir_recursive(&path, &child_path, types, fns)?;
        } else if path.extension().is_some_and(|ext| ext == "rs") {
            let file_name = path
                .file_stem()
                .and_then(|n| n.to_str())
                .unwrap_or("")
                .to_string();

            // Skip test files, build scripts, charon_export.
            if file_name.starts_with("test") || file_name == "build" || file_name == "charon_export"
            {
                continue;
            }

            // Module path for this file.
            let mut file_module_path = module_path.to_vec();
            if file_name != "mod" && file_name != "lib" {
                file_module_path.push(file_name);
            }

            parse_file(&path, &file_module_path, types, fns)
                .with_context(|| format!("failed to parse: {}", path.display()))?;
        }
    }
    Ok(())
}

fn parse_file(
    path: &Path,
    module_path: &[String],
    types: &mut Vec<ParsedTypeDef>,
    fns: &mut Vec<ParsedFnSig>,
) -> Result<()> {
    let content = std::fs::read_to_string(path)
        .with_context(|| format!("failed to read: {}", path.display()))?;

    let file = syn::parse_file(&content)
        .with_context(|| format!("failed to parse Rust syntax: {}", path.display()))?;

    for item in &file.items {
        // Skip items with #[cfg(test)], #[cfg(charon)], #[cfg(feature = "serde")]
        if item_has_skip_cfg(item) {
            continue;
        }

        match item {
            syn::Item::Struct(s) => {
                if is_pub(&s.vis)
                    && let Some(def) = parse_struct(s, module_path, path) {
                        types.push(def);
                    }
            }
            syn::Item::Enum(e) => {
                if is_pub(&e.vis)
                    && let Some(def) = parse_enum(e, module_path, path) {
                        types.push(def);
                    }
            }
            syn::Item::Type(t) => {
                if is_pub(&t.vis) {
                    let simple_name = t.ident.to_string();
                    let name = build_qualified_name(module_path, &simple_name);
                    let type_params = extract_type_params(&t.generics);
                    let aliased_ty = parse_syn_type(&t.ty);
                    types.push(ParsedTypeDef {
                        name,
                        simple_name,
                        type_params,
                        kind: ParsedTypeKind::Alias(aliased_ty),
                        source_file: path.display().to_string(),
                    });
                }
            }
            syn::Item::Fn(f) => {
                if is_pub(&f.vis)
                    && let Some(sig) = parse_top_level_fn(f, module_path, path) {
                        fns.push(sig);
                    }
            }
            syn::Item::Impl(imp) => {
                // Only inherent impls (no trait impls).
                if imp.trait_.is_none() {
                    parse_impl_block(imp, module_path, path, fns);
                }
            }
            _ => {}
        }
    }

    Ok(())
}

fn is_pub(vis: &syn::Visibility) -> bool {
    matches!(vis, syn::Visibility::Public(_))
}

fn parse_struct(
    s: &syn::ItemStruct,
    module_path: &[String],
    source: &Path,
) -> Option<ParsedTypeDef> {
    let simple_name = s.ident.to_string();
    let name = build_qualified_name(module_path, &simple_name);
    let type_params = extract_type_params(&s.generics);

    let fields = match &s.fields {
        syn::Fields::Named(named) => named
            .named
            .iter()
            .filter_map(|f| {
                let fname = f.ident.as_ref()?.to_string();
                let ty = parse_syn_type(&f.ty);
                Some(ParsedField { name: fname, ty })
            })
            .collect(),
        syn::Fields::Unnamed(unnamed) => unnamed
            .unnamed
            .iter()
            .enumerate()
            .map(|(i, f)| ParsedField {
                name: format!("field{i}"),
                ty: parse_syn_type(&f.ty),
            })
            .collect(),
        syn::Fields::Unit => Vec::new(),
    };

    Some(ParsedTypeDef {
        name,
        simple_name,
        type_params,
        kind: ParsedTypeKind::Struct(fields),
        source_file: source.display().to_string(),
    })
}

fn parse_enum(e: &syn::ItemEnum, module_path: &[String], source: &Path) -> Option<ParsedTypeDef> {
    let simple_name = e.ident.to_string();
    let name = build_qualified_name(module_path, &simple_name);
    let type_params = extract_type_params(&e.generics);

    let variants = e
        .variants
        .iter()
        .map(|v| {
            let vname = v.ident.to_string();
            let fields = match &v.fields {
                syn::Fields::Named(named) => named
                    .named
                    .iter()
                    .filter_map(|f| {
                        let fname = f.ident.as_ref()?.to_string();
                        let ty = parse_syn_type(&f.ty);
                        Some(ParsedField { name: fname, ty })
                    })
                    .collect(),
                syn::Fields::Unnamed(unnamed) => unnamed
                    .unnamed
                    .iter()
                    .enumerate()
                    .map(|(i, f)| ParsedField {
                        name: format!("a{i}"),
                        ty: parse_syn_type(&f.ty),
                    })
                    .collect(),
                syn::Fields::Unit => Vec::new(),
            };
            ParsedVariant {
                name: vname,
                fields,
            }
        })
        .collect();

    Some(ParsedTypeDef {
        name,
        simple_name,
        type_params,
        kind: ParsedTypeKind::Enum(variants),
        source_file: source.display().to_string(),
    })
}

fn build_qualified_name(module_path: &[String], simple_name: &str) -> String {
    if module_path.is_empty() {
        simple_name.to_string()
    } else {
        format!("{}.{}", module_path.join("."), simple_name)
    }
}

fn extract_type_params(generics: &syn::Generics) -> Vec<String> {
    generics
        .params
        .iter()
        .filter_map(|p| match p {
            syn::GenericParam::Type(tp) => Some(tp.ident.to_string()),
            _ => None,
        })
        .collect()
}

/// Format a syn::Expr as a string (for array lengths, const generics).
fn format_expr(expr: &syn::Expr) -> String {
    match expr {
        syn::Expr::Lit(lit) => match &lit.lit {
            syn::Lit::Int(i) => i.base10_digits().to_string(),
            _ => "0 /- styx: unsupported literal -/".to_string(),
        },
        syn::Expr::Path(p) => path_to_string(&p.path),
        _ => "0 /- styx: unsupported const expr -/".to_string(),
    }
}

/// Parse a syn::Type into our RustType representation.
fn parse_syn_type(ty: &syn::Type) -> RustType {
    match ty {
        syn::Type::Path(tp) => parse_type_path(tp),
        syn::Type::Reference(r) => RustType::Ref(Box::new(parse_syn_type(&r.elem))),
        syn::Type::Ptr(p) => RustType::RawPtr(Box::new(parse_syn_type(&p.elem))),
        syn::Type::Tuple(t) => {
            if t.elems.is_empty() {
                RustType::Unit
            } else {
                RustType::Tuple(t.elems.iter().map(parse_syn_type).collect())
            }
        }
        syn::Type::Array(a) => {
            let elem = parse_syn_type(&a.elem);
            let len = format_expr(&a.len);
            RustType::Array(Box::new(elem), len)
        }
        syn::Type::Slice(s) => RustType::Slice(Box::new(parse_syn_type(&s.elem))),
        syn::Type::TraitObject(to) => {
            let trait_name = to
                .bounds
                .iter()
                .find_map(|b| match b {
                    syn::TypeParamBound::Trait(t) => Some(path_to_string(&t.path)),
                    _ => None,
                })
                .unwrap_or_else(|| "Unknown".to_string());
            RustType::DynTrait(trait_name)
        }
        syn::Type::Paren(p) => parse_syn_type(&p.elem),
        _ => RustType::Unknown("unsupported_type".to_string()),
    }
}

fn parse_type_path(tp: &syn::TypePath) -> RustType {
    let path = &tp.path;
    let full_name = path_to_string(path);

    // Get the last segment's generic arguments.
    let last_seg = path.segments.last();
    let args: Vec<RustType> = last_seg
        .map(|seg| match &seg.arguments {
            syn::PathArguments::AngleBracketed(ab) => ab
                .args
                .iter()
                .filter_map(|arg| match arg {
                    syn::GenericArgument::Type(t) => Some(parse_syn_type(t)),
                    _ => None,
                })
                .collect(),
            _ => Vec::new(),
        })
        .unwrap_or_default();

    if args.is_empty() {
        RustType::Named(full_name)
    } else {
        // Strip generic args from the name (they're in the args vec).
        let base = path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect::<Vec<_>>()
            .join("::");
        RustType::Generic(base, args)
    }
}

fn path_to_string(path: &syn::Path) -> String {
    path.segments
        .iter()
        .map(|s| s.ident.to_string())
        .collect::<Vec<_>>()
        .join("::")
}

/// Convert a RustType to Lean syntax, applying rewrite rules.
pub fn rust_type_to_lean(ty: &RustType, rules: &RewriteRules) -> String {
    match ty {
        RustType::Named(name) => {
            // Check rewrite rules first.
            if let Some(lean) = rules.rewrite_named(name) {
                return lean;
            }
            // Rust primitive → Lean.
            match name.as_str() {
                "u8" => "U8".to_string(),
                "u16" => "U16".to_string(),
                "u32" => "U32".to_string(),
                "u64" => "U64".to_string(),
                "u128" => "U128".to_string(),
                "usize" => "Usize".to_string(),
                "i8" => "I8".to_string(),
                "i16" => "I16".to_string(),
                "i32" => "I32".to_string(),
                "i64" => "I64".to_string(),
                "i128" => "I128".to_string(),
                "isize" => "Isize".to_string(),
                "bool" => "Bool".to_string(),
                "char" => "Char".to_string(),
                "()" => "Unit".to_string(),
                "str" => "String".to_string(),
                "Self" => "Self".to_string(),
                _ => {
                    let lean = name.replace("::", ".");
                    // Strip `crate.` prefix — in direct mode, crate paths
                    // should resolve to unqualified names.
                    lean.strip_prefix("crate.").unwrap_or(&lean).to_string()
                }
            }
        }
        RustType::Generic(base, args) => {
            // Check rewrite rules for the generic type.
            if let Some(lean) = rules.rewrite_generic(base, args) {
                return lean;
            }
            let lean_base = base.replace("::", ".");
            let lean_args: Vec<String> = args.iter().map(|a| rust_type_to_lean(a, rules)).collect();
            if lean_args.is_empty() {
                lean_base
            } else {
                format!("({} {})", lean_base, lean_args.join(" "))
            }
        }
        RustType::Tuple(elems) => match elems.len() {
            0 => "Unit".to_string(),
            1 => rust_type_to_lean(&elems[0], rules),
            _ => {
                let mut it = elems.iter().rev();
                let mut acc = rust_type_to_lean(it.next().unwrap(), rules);
                for t in it {
                    acc = format!("({} × {})", rust_type_to_lean(t, rules), acc);
                }
                acc
            }
        },
        RustType::Ref(inner) | RustType::RawPtr(inner) => rust_type_to_lean(inner, rules),
        RustType::Array(elem, len) => {
            format!("(Array {} {})", rust_type_to_lean(elem, rules), len)
        }
        RustType::Slice(elem) => {
            format!("(Slice {})", rust_type_to_lean(elem, rules))
        }
        RustType::Unit => "Unit".to_string(),
        RustType::DynTrait(name) => {
            // Emit opaque placeholder for dynamic trait objects.
            format!("STYX_DynTrait_{}", name.replace("::", "_"))
        }
        RustType::Unknown(raw) => format!("STYX_Unknown /- {} -/", raw),
    }
}

// ---------------------------------------------------------------------------
// cfg attribute filtering
// ---------------------------------------------------------------------------

/// Check whether a syn item carries a #[cfg(...)] that we should skip.
///
/// Skips: cfg(test), cfg(charon), cfg(feature = "serde").
fn item_has_skip_cfg(item: &syn::Item) -> bool {
    let attrs = match item {
        syn::Item::Struct(s) => &s.attrs,
        syn::Item::Enum(e) => &e.attrs,
        syn::Item::Type(t) => &t.attrs,
        syn::Item::Fn(f) => &f.attrs,
        syn::Item::Impl(i) => &i.attrs,
        syn::Item::Mod(m) => &m.attrs,
        _ => return false,
    };
    attrs_have_skip_cfg(attrs)
}

fn attrs_have_skip_cfg(attrs: &[syn::Attribute]) -> bool {
    for attr in attrs {
        if !attr.path().is_ident("cfg") {
            continue;
        }
        // Parse the cfg(...) content by examining the nested tokens.
        if let syn::Meta::List(list) = &attr.meta {
            let content = list.tokens.to_string();
            if content.contains("test")
                || content.contains("charon")
                || (content.contains("feature") && content.contains("serde"))
            {
                return true;
            }
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Function signature parsing
// ---------------------------------------------------------------------------

/// Parse a top-level `pub fn` into a `ParsedFnSig`.
fn parse_top_level_fn(
    f: &syn::ItemFn,
    module_path: &[String],
    source: &Path,
) -> Option<ParsedFnSig> {
    let fn_name = f.sig.ident.to_string();
    let qualified = build_qualified_name(module_path, &fn_name);
    let type_params = extract_type_params(&f.sig.generics);
    let (params, ret) = parse_fn_sig_params(&f.sig, None);

    Some(ParsedFnSig {
        name: qualified,
        type_params,
        params,
        ret_type: ret,
        is_method: false,
        self_type: None,
        is_mut_self: false,
        source_file: source.display().to_string(),
    })
}

/// Parse an `impl Type { ... }` block, extracting pub method signatures.
fn parse_impl_block(
    imp: &syn::ItemImpl,
    _module_path: &[String],
    source: &Path,
    fns: &mut Vec<ParsedFnSig>,
) {
    // Extract the self type name from the impl'd type.
    let self_type_name = match &*imp.self_ty {
        syn::Type::Path(tp) => {
            // Take just the last segment (e.g., "Capability" from "crate::types::Capability").
            tp.path
                .segments
                .last()
                .map(|s| s.ident.to_string())
                .unwrap_or_default()
        }
        _ => return,
    };

    if self_type_name.is_empty() {
        return;
    }

    for item in &imp.items {
        let syn::ImplItem::Fn(method) = item else {
            continue;
        };

        // Skip non-pub methods.
        if !is_pub(&method.vis) {
            continue;
        }

        // Skip methods with skip cfg.
        if attrs_have_skip_cfg(&method.attrs) {
            continue;
        }

        let fn_name = method.sig.ident.to_string();
        let type_params = extract_type_params(&method.sig.generics);
        let (params, ret, has_self, is_mut) = parse_method_sig_params(&method.sig, &self_type_name);

        let qualified = format!("{}.{}", self_type_name, fn_name);

        fns.push(ParsedFnSig {
            name: qualified,
            type_params,
            params,
            ret_type: ret,
            is_method: has_self,
            self_type: Some(self_type_name.clone()),
            is_mut_self: is_mut,
            source_file: source.display().to_string(),
        });
    }
}

/// Parse parameters from a free function signature.
///
/// Returns (params, return_type).
fn parse_fn_sig_params(
    sig: &syn::Signature,
    _self_type: Option<&str>,
) -> (Vec<(String, RustType)>, RustType) {
    let mut params = Vec::new();

    for (i, arg) in sig.inputs.iter().enumerate() {
        match arg {
            syn::FnArg::Typed(pat_ty) => {
                let name = pat_to_param_name(&pat_ty.pat, i);
                let ty = parse_syn_type(&pat_ty.ty);
                params.push((name, ty));
            }
            syn::FnArg::Receiver(_) => {
                // Should not happen for free functions, but handle gracefully.
            }
        }
    }

    let ret = parse_return_type(&sig.output);
    (params, ret)
}

/// Parse parameters from a method signature (handles self).
///
/// Returns (params, return_type, has_self, is_mut_self).
fn parse_method_sig_params(
    sig: &syn::Signature,
    self_type_name: &str,
) -> (Vec<(String, RustType)>, RustType, bool, bool) {
    let mut params = Vec::new();
    let mut has_self = false;
    let mut is_mut = false;

    for (i, arg) in sig.inputs.iter().enumerate() {
        match arg {
            syn::FnArg::Receiver(recv) => {
                has_self = true;
                is_mut = recv.mutability.is_some();
                // Emit self as a regular parameter of the struct type.
                params.push((
                    "self".to_string(),
                    RustType::Named(self_type_name.to_string()),
                ));
            }
            syn::FnArg::Typed(pat_ty) => {
                let name = pat_to_param_name(&pat_ty.pat, i);
                let ty = parse_syn_type(&pat_ty.ty);
                params.push((name, ty));
            }
        }
    }

    let ret = parse_return_type(&sig.output);
    (params, ret, has_self, is_mut)
}

/// Extract a parameter name from a pattern.
fn pat_to_param_name(pat: &syn::Pat, index: usize) -> String {
    match pat {
        syn::Pat::Ident(pi) => pi.ident.to_string(),
        syn::Pat::Wild(_) => format!("_arg{}", index),
        _ => format!("arg{}", index),
    }
}

/// Parse a return type.
fn parse_return_type(output: &syn::ReturnType) -> RustType {
    match output {
        syn::ReturnType::Default => RustType::Unit,
        syn::ReturnType::Type(_, ty) => parse_syn_type(ty),
    }
}
