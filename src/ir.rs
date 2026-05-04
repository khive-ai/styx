// ============================================================================
// StyxIR — Stable Intermediate Representation for Rust-to-Lean4 Translation
// ============================================================================
//
// STATUS: Phase 2 prototype. No consumer exists yet — the current pipeline
// reads Charon LLBC, not StyxIR. This module defines the target IR for the
// THIR-based extraction driver (styx-rustc). Do not remove.
//
// This module defines the IR that sits between the compiler frontend (THIR)
// and the Lean4 emitter. It replaces Charon's LLBC as the canonical
// representation that Styx consumes.
//
// Design principles:
//   1. OWNED — no compiler lifetime references, fully serializable
//   2. SOURCE-SHAPED — if/match/while, NOT basic blocks (avoids MIR reconstruction)
//   3. TYPED — every expression carries its resolved type
//   4. RESOLVED — all method calls, trait impls, operators are concrete
//   5. LEAN-ORIENTED — structure is close to what the Lean emitter needs
//
// The IR is produced by the Styx driver (a rustc_driver::Callbacks impl that
// reads THIR) and consumed by the Lean emitter (tools/styx/src/emit/).
//
// Serialization: serde_json for I/O (bincode planned for Phase 2 fast-path,
// not yet added to Cargo.toml).

#[allow(dead_code)]
use serde::{Deserialize, Serialize};

// ============================================================================
// Identifiers
// ============================================================================

/// A unique identifier for items within a StyxPackage. Indices are dense
/// and 0-based within each category (types, functions, trait impls).
///
/// We use separate newtypes so that a TypeId cannot be confused with a FunId
/// at the type level — a bug class that plagues weakly-typed IR designs.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FunId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraitImplId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TraitDeclId(pub u32);

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct GlobalId(pub u32);

/// Index of a local variable within a function body.
/// Local 0 is the return slot, locals 1..=N are parameters,
/// locals N+1.. are compiler-introduced temporaries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct LocalId(pub u32);

/// Index of a variant within an enum type.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct VariantId(pub u32);

/// Index of a field within a struct or enum variant.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct FieldId(pub u32);

// ============================================================================
// Top-level package
// ============================================================================

/// A fully extracted crate — the top-level unit of StyxIR.
///
/// This is what gets serialized to disk (`.styx` file) and read by the
/// Lean emitter. It contains all type definitions, function definitions,
/// trait declarations, trait implementations, and global constants needed
/// to emit one Lean4 module.
///
/// Populated by: the Styx rustc driver walking `TyCtxt::hir_crate_items()`
/// and requesting `thir_body()` for each function with a body.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxPackage {
    /// Crate name (e.g., "lion_core"). Used as the Lean namespace root.
    pub crate_name: String,

    /// Type definitions indexed by TypeId. Structs, enums, and type aliases.
    /// Ordered topologically: a type only references types with lower IDs.
    ///
    /// Source: `TyCtxt::adt_def()` for each ADT, plus `type_alias_of()` for aliases.
    pub types: Vec<StyxTypeDef>,

    /// Function definitions indexed by FunId. Includes methods (the receiver
    /// is just the first parameter after desugaring).
    ///
    /// Source: `TyCtxt::thir_body(def_id)` for each fn/method with a body.
    /// Functions without bodies (extern, trait default) have `body: None`.
    pub functions: Vec<StyxFunDef>,

    /// Trait declarations. Used to resolve trait method names in call targets
    /// and to emit trait structure types in Lean.
    ///
    /// Source: `TyCtxt::trait_def()` for each trait in the crate.
    pub trait_decls: Vec<StyxTraitDecl>,

    /// Trait implementations. Maps (trait, concrete type) -> method bodies.
    /// Needed to resolve which impl a method call dispatches to.
    ///
    /// Source: `TyCtxt::trait_impls_of()` filtered to local crate impls.
    pub trait_impls: Vec<StyxTraitImpl>,

    /// Global constants and statics. `const X: T = expr;`
    ///
    /// Source: `TyCtxt::const_eval_poly()` or `thir_body()` for const items.
    pub globals: Vec<StyxGlobalDef>,

    /// Declaration ordering. Mirrors Charon's `ordered_decls` — determines
    /// the emission order so that Lean sees definitions before uses.
    ///
    /// Each group may contain one or more mutually-recursive definitions.
    /// Within a group, all items are emitted together (as `mutual ... end`
    /// in Lean or `partial_fixpoint` for recursive functions).
    pub decl_groups: Vec<DeclGroup>,
}

// ============================================================================
// Declaration groups (emission ordering)
// ============================================================================

/// A group of mutually-dependent declarations. Single-item groups are the
/// common case; multi-item groups arise from mutual recursion.
///
/// The emitter walks these in order. Types before functions ensures forward
/// references work. Mixed groups handle cases where a type and its methods
/// are mutually recursive (rare but possible via const generics).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum DeclGroup {
    Type(Vec<TypeId>),
    Fun(Vec<FunId>),
    TraitDecl(Vec<TraitDeclId>),
    TraitImpl(Vec<TraitImplId>),
    Global(Vec<GlobalId>),
    /// Mixed group: contains both types and functions that are
    /// mutually recursive (e.g., a type with a const-generic default
    /// that calls a function returning that type).
    Mixed(Vec<MixedDeclItem>),
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum MixedDeclItem {
    Type(TypeId),
    Fun(FunId),
    TraitDecl(TraitDeclId),
    TraitImpl(TraitImplId),
    Global(GlobalId),
}

// ============================================================================
// Type definitions
// ============================================================================

/// A type definition: struct, enum, or type alias.
///
/// Corresponds to Charon's `TypeDecl`. The key difference: all generic
/// parameters are fully owned strings (not interned compiler symbols), and
/// field types are `StyxType` (our owned type representation).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTypeDef {
    pub id: TypeId,

    /// Fully qualified Rust path (e.g., "lion_core::capability::Capability").
    /// The emitter maps this to a Lean name via the naming module.
    pub rust_path: String,

    /// Short name (e.g., "Capability"). Used as the Lean type name.
    pub name: String,

    /// Generic parameters: type params, const params, lifetime params.
    /// Lifetimes are kept for fidelity but erased during Lean emission.
    pub generics: StyxGenerics,

    /// The kind of type definition.
    pub kind: StyxTypeDefKind,

    /// Source span for error messages.
    pub span: StyxSpan,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxTypeDefKind {
    /// `struct Foo { field: Type, ... }`
    /// Tuple structs have fields named "_0", "_1", etc.
    /// Unit structs have an empty fields vec.
    Struct { fields: Vec<StyxFieldDef> },

    /// `enum Bar { Variant1 { ... }, Variant2(Type), Variant3 }`
    Enum { variants: Vec<StyxVariantDef> },

    /// `type Alias = TargetType;`
    /// The target type is fully resolved (no unresolved associated types).
    Alias { target: StyxType },

    /// Opaque type — body not available (e.g., from an external crate).
    /// Emitted as `opaque` in Lean.
    Opaque,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxFieldDef {
    pub id: FieldId,
    /// Field name. Named fields use the Rust name; tuple struct fields
    /// use "_0", "_1", etc.
    pub name: String,
    pub ty: StyxType,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxVariantDef {
    pub id: VariantId,
    pub name: String,
    /// Variant fields. Unit variants have empty vec.
    /// Tuple variants have fields named "_0", "_1", etc.
    pub fields: Vec<StyxFieldDef>,
}

// ============================================================================
// Function definitions
// ============================================================================

/// A function or method definition.
///
/// Corresponds to Charon's `FunDecl`. Methods are represented as functions
/// whose first parameter is `self` / `&self` / `&mut self` (already
/// desugared by the compiler — the receiver is a normal typed parameter).
///
/// For `&mut self` methods, the Lean emitter rewrites the return type to
/// include the updated self value (Aeneas write-back convention). That
/// rewriting is NOT done here — StyxIR preserves the Rust signature.
/// The emitter handles the transformation because it is Lean-specific.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxFunDef {
    pub id: FunId,

    /// Fully qualified Rust path.
    pub rust_path: String,

    /// Short name for Lean emission.
    pub name: String,

    /// Generic parameters.
    pub generics: StyxGenerics,

    /// Function parameters: (name, type) pairs.
    /// Parameter 0 of methods is the receiver (self).
    /// Names come from THIR debug info or are synthesized ("arg0", "arg1").
    pub params: Vec<StyxParam>,

    /// Return type (fully resolved).
    pub ret_ty: StyxType,

    /// Function body. `None` for extern functions, opaque declarations,
    /// or functions the driver could not extract (emitted as `opaque` in Lean).
    pub body: Option<StyxBody>,

    /// True if this function is in a mutually-recursive group and needs
    /// `partial def` or `partial_fixpoint` in Lean.
    pub is_recursive: bool,

    /// Source span.
    pub span: StyxSpan,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxParam {
    pub name: String,
    pub ty: StyxType,
    /// True if this is `&mut self` — signals the emitter to generate
    /// write-back logic. Computed from THIR's receiver adjustment info.
    pub is_mut_self: bool,
    /// HirId-based local ID for this parameter. Used by the emitter to
    /// bind closure params in the LOCAL_NAMES scope so VarRef in the
    /// closure body resolves to the correct name.
    #[serde(default)]
    pub local_id: Option<LocalId>,
}

// ============================================================================
// Function body
// ============================================================================

/// A function body: local variable declarations + a block of statements.
///
/// Corresponds to Charon's `Body`. The locals table provides typed
/// storage for all variables; the block is a structured (not CFG) sequence
/// of statements.
///
/// Local 0 is the return slot (its type matches `StyxFunDef::ret_ty`).
/// Locals 1..=N are parameters. Locals N+1.. are introduced by the compiler
/// for temporaries, pattern bindings, and desugared constructs.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxBody {
    /// Typed local variable declarations. Indexed by LocalId.
    ///
    /// Source: THIR's `Param` list + compiler-generated temporaries.
    /// Each local gets a name (user-given or "local_N" for temps).
    pub locals: Vec<StyxLocal>,

    /// The function body as a structured block.
    pub block: StyxBlock,
}

/// A local variable declaration within a function body.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxLocal {
    pub id: LocalId,
    /// User-facing name. Parameters use the source name (e.g., "self_",
    /// "pid", "state"). Compiler temps use "local_N" where N = id.0.
    pub name: String,
    /// Fully resolved type.
    pub ty: StyxType,
}

/// A block of statements. This is the basic structural unit — function
/// bodies, if-branches, match arms, and loop bodies are all blocks.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxBlock {
    pub stmts: Vec<StyxStmt>,
}

// ============================================================================
// Statements
// ============================================================================

/// A structured statement. Source-shaped: no gotos, no basic blocks.
///
/// This is the key divergence from Charon's LLBC. LLBC uses a flat
/// `RawStatement` enum with `Sequence` for chaining. StyxIR uses a `Vec`
/// of statements in a block, which is simpler and closer to THIR's
/// structure.
///
/// Each statement variant carries enough information for the Lean emitter
/// to produce correct code without needing to look up external tables.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxStmt {
    /// `let local = expr;` — assign an expression to a local.
    ///
    /// This covers both `let` bindings and reassignments. In LLBC this
    /// was `Assign(Place, Rvalue)` — we collapse Place+Rvalue into a
    /// simpler local+expr pair because StyxIR does not model places
    /// (field projections are in the expression, not the assignment target).
    ///
    /// For compound targets (e.g., `self.field = expr`), we use
    /// `FieldAssign` instead.
    Assign {
        target: LocalId,
        /// Source-level variable name extracted from the binding pattern.
        /// `Some("x")` for `let x = ...`, `None` for desugared/compiler assignments.
        name: Option<String>,
        value: StyxExpr,
    },

    /// `target.field = value` — assign to a struct field.
    ///
    /// Lean doesn't have mutable field assignment. The emitter translates
    /// this to struct-update syntax: `let target := { target with field := value }`.
    ///
    /// Source: THIR `Assign` where the LHS has field projections.
    FieldAssign {
        target: LocalId,
        field_path: Vec<FieldAccess>,
        value: StyxExpr,
    },

    /// Expression evaluated for its side effects (e.g., a function call
    /// whose return value is unused, or an assertion).
    Expr(StyxExpr),

    /// `if cond { then_block } else { else_block }`
    ///
    /// Both branches are always present. An `if` without `else` gets
    /// `else_block = { stmts: [] }`.
    ///
    /// Source: THIR `If` node. In LLBC this was `Switch::If` — we
    /// preserve the high-level form to avoid reconstruction.
    If {
        cond: StyxExpr,
        then_block: StyxBlock,
        else_block: StyxBlock,
    },

    /// `match scrutinee { arms... }`
    ///
    /// Source: THIR `Match` node. Patterns are already compiled to a
    /// decision tree by the compiler (pattern exhaustiveness checked).
    /// In LLBC this was `Switch::Match` with variant IDs — we keep
    /// full patterns for richer Lean output.
    Match {
        scrutinee: StyxExpr,
        arms: Vec<StyxMatchArm>,
    },

    /// `while cond { body }` — structured loop with a boolean condition.
    ///
    /// Source: `loop { if !cond { break } ... }` pattern in THIR, which
    /// the driver recognizes and lifts back to `while`. Also covers
    /// `while let Some(x) = expr { ... }` when desugared.
    ///
    /// The Lean emitter translates this to either `partial_fixpoint` or
    /// a native recursive function with a termination measure.
    Loop {
        /// Loop condition. `None` for `loop { ... }` (infinite loop
        /// that must break or return).
        cond: Option<StyxExpr>,
        body: StyxBlock,
    },

    /// `return expr` — early return from the enclosing function.
    ///
    /// Source: THIR `Return` or desugared `?` operator. The emitter
    /// translates this to `return (ok expr)` or `return (fail err)`
    /// depending on the expression type.
    Return(StyxExpr),

    /// `break` — exit the innermost loop.
    ///
    /// The `depth` field counts how many nested loops to break out of
    /// (0 = innermost). This matches LLBC's `Break(usize)`.
    Break { depth: u32 },

    /// `continue` — jump to the next iteration of the innermost loop.
    Continue { depth: u32 },

    /// A compiler-generated drop. Normally invisible in Lean (GC model),
    /// but recorded so the emitter can handle custom Drop if needed.
    ///
    /// For lion-core (no custom Drop impls), these are all no-ops.
    Drop { local: LocalId },

    /// `assert!(cond)` or `debug_assert!(cond)`.
    ///
    /// The emitter translates to `massert (cond == expected)` in Lean.
    Assert { cond: StyxExpr, expected: bool },
}

/// A field access step in a compound assignment path.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FieldAccess {
    /// The field name (for named fields) or "_N" for tuple fields.
    pub name: String,
    pub field_id: FieldId,
}

// ============================================================================
// Match arms and patterns
// ============================================================================

/// A match arm: pattern + optional guard + body.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxMatchArm {
    pub pattern: StyxPattern,
    /// Match guard: `if expr` after the pattern. Rare in lion-core but
    /// supported for generality.
    pub guard: Option<StyxExpr>,
    pub body: StyxBlock,
}

/// A match pattern. Richer than LLBC's variant-ID-based patterns —
/// we preserve nested structure for readable Lean output.
///
/// THIR already has patterns compiled to a decision tree with resolved
/// types, so these are fully typed and exhaustiveness-checked.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxPattern {
    /// Match a specific enum variant and bind its fields.
    /// e.g., `Ok(val)` or `Step::HostCall { hc, auth, result }`
    Variant {
        type_id: TypeId,
        variant_id: VariantId,
        /// Bindings for variant fields. `None` entries mean the field
        /// is not bound (wildcard or `_`). The vec length matches the
        /// variant's field count.
        field_bindings: Vec<Option<PatternBinding>>,
        /// Rust path of the ADT (e.g., "core::option::Option") for
        /// std type variant name resolution in the emitter.
        #[serde(default)]
        rust_path: Option<String>,
    },

    /// Literal pattern: `0`, `true`, `'a'`, `"hello"`.
    Literal(StyxLiteral),

    /// Wildcard `_` — matches anything, binds nothing.
    Wildcard,

    /// Variable binding: `x` (binds the scrutinee to a local).
    Binding {
        local: LocalId,
        /// If Some, this is an `x @ pattern` binding.
        subpattern: Option<Box<StyxPattern>>,
    },

    /// Tuple destructuring: `(a, b, c)`.
    Tuple(Vec<StyxPattern>),

    /// Struct destructuring: `Foo { x, y, .. }`.
    Struct {
        type_id: TypeId,
        field_patterns: Vec<(FieldId, StyxPattern)>,
        /// True if `..` was used (remaining fields are wildcards).
        has_rest: bool,
    },

    /// Reference pattern: `&x` or `&mut x`. The emitter erases the
    /// reference and matches the inner pattern.
    Ref(Box<StyxPattern>),

    /// Or-pattern: `A | B`. Each alternative must bind the same locals.
    Or(Vec<StyxPattern>),

    /// Range pattern: `0..=9`. Used for integer matching.
    Range {
        lo: Option<StyxLiteral>,
        hi: Option<StyxLiteral>,
        inclusive: bool,
    },
}

/// A pattern binding for a variant field.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct PatternBinding {
    pub local: LocalId,
    /// The field name for documentation. The LocalId is what the emitter
    /// uses for code generation.
    pub field_name: String,
}

// ============================================================================
// Expressions
// ============================================================================

/// A typed expression. Every expression carries its resolved type.
///
/// This is the core of StyxIR. Expressions are source-shaped (not
/// lowered to SSA/ANF) but fully resolved (no unresolved names, no
/// unresolved types, no unresolved method calls).
///
/// The Lean emitter may need to ANF-transform some expressions
/// (hoisting monadic subexpressions to let-bindings). That is the
/// emitter's job, not the IR's — the IR preserves source structure.
///
/// Key difference from LLBC: LLBC separates Place/Operand/Rvalue into
/// three distinct concepts (an MIR heritage). StyxIR unifies them into
/// a single expression tree, which is simpler and closer to THIR.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxExpr {
    /// The expression kind.
    pub kind: StyxExprKind,
    /// The fully resolved type of this expression.
    pub ty: StyxType,
    /// Source span for error reporting.
    pub span: StyxSpan,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxExprKind {
    // --- Atoms ---
    /// A literal value: integers, bools, chars, strings.
    Literal(StyxLiteral),

    /// A local variable reference.
    Local(LocalId),

    /// A reference to a global constant or static.
    Global(GlobalId),

    // --- Compound expressions ---
    /// Function or method call with a resolved callee.
    ///
    /// This replaces LLBC's `Call` statement. In LLBC, calls are
    /// statements that write to a destination place. In StyxIR, calls
    /// are expressions that produce a value — the `Assign` statement
    /// handles storing the result.
    ///
    /// The callee is fully resolved: no dynamic dispatch, no unresolved
    /// trait methods. The generic arguments are instantiated.
    Call {
        callee: StyxCallee,
        /// Generic type arguments that must be passed explicitly in Lean.
        /// These come from the function's generic params, instantiated
        /// at this call site. The emitter prepends them before value args.
        ///
        /// Source: `FnPtr::generics.types` + `TraitRef::generics.types`
        /// from THIR's resolved method info.
        type_args: Vec<StyxType>,
        /// Value arguments (including the receiver for methods).
        args: Vec<StyxExpr>,
    },

    /// Binary operation: `a + b`, `a == b`, `a & b`.
    ///
    /// For overloaded operators, the driver resolves to the trait method
    /// and emits a `Call` instead. `BinOp` is only used for primitive
    /// operations on built-in numeric types and booleans.
    ///
    /// This distinction matters: `u64 + u64` is `BinOp::Add` (maps to
    /// Lean's `+` with overflow semantics), but `Rights & Rights` is
    /// `Call { callee: BitAnd::bitand, ... }`.
    BinOp {
        op: StyxBinOp,
        lhs: Box<StyxExpr>,
        rhs: Box<StyxExpr>,
    },

    /// Unary operation: `!x` (boolean negation or bitwise complement),
    /// `-x` (arithmetic negation).
    UnOp {
        op: StyxUnOp,
        operand: Box<StyxExpr>,
    },

    /// Field access: `expr.field_name`.
    ///
    /// Source: THIR `Field` projection. The field is fully resolved
    /// (name and index known).
    Field {
        base: Box<StyxExpr>,
        field_name: String,
        field_id: FieldId,
    },

    /// Tuple field access: `expr.0`, `expr.1`.
    TupleField { base: Box<StyxExpr>, index: u32 },

    /// Array/slice indexing: `expr[index]`.
    ///
    /// The driver resolves this from the `Index`/`IndexMut` trait impl.
    /// For `Vec<T>`, this is `<Vec<T> as Index<usize>>::index`.
    /// The emitter generates monadic Lean (index can panic/fail).
    Index {
        base: Box<StyxExpr>,
        index: Box<StyxExpr>,
    },

    /// Struct construction: `Foo { field1: expr1, field2: expr2 }`.
    ///
    /// All fields must be present (the compiler ensures this).
    /// For struct update syntax (`Foo { x: 1, ..other }`), the driver
    /// expands to explicit field assignments.
    StructInit {
        type_id: TypeId,
        fields: Vec<(FieldId, StyxExpr)>,
    },

    /// Enum variant construction: `Bar::Variant(expr)` or `Bar::Variant { f: expr }`.
    EnumInit {
        type_id: TypeId,
        variant_id: VariantId,
        fields: Vec<(FieldId, StyxExpr)>,
    },

    /// Tuple construction: `(a, b, c)`.
    Tuple(Vec<StyxExpr>),

    /// Array literal: `[a, b, c]`.
    Array {
        elem_ty: StyxType,
        elements: Vec<StyxExpr>,
    },

    /// Type cast: `expr as TargetType`.
    ///
    /// Only for primitive casts (numeric widening/narrowing). Trait-based
    /// conversions (`From`/`Into`) are `Call` expressions.
    Cast {
        operand: Box<StyxExpr>,
        target_ty: StyxType,
    },

    /// Reference creation: `&expr` or `&mut expr`.
    ///
    /// In Lean, references are erased (pure functional model). The emitter
    /// passes the inner expression through. We keep this node so that the
    /// emitter can distinguish `&mut` for write-back analysis.
    Ref {
        operand: Box<StyxExpr>,
        is_mut: bool,
    },

    /// Dereference: `*expr`.
    ///
    /// Like `Ref`, erased in Lean. Kept for write-back chain analysis.
    Deref(Box<StyxExpr>),

    /// Closure / lambda expression: `|x, y| expr`.
    ///
    /// Source: THIR closure with resolved capture list and body.
    /// For lion-core, closures are almost always inlined in iterator
    /// combinators. The emitter translates to Lean `fun x y => expr`.
    ///
    /// Capture info is included for completeness but typically not used
    /// for Lean emission (Lean closures capture by value automatically).
    Closure {
        params: Vec<StyxParam>,
        body: Box<StyxExpr>,
        captures: Vec<CaptureInfo>,
    },

    /// Block expression: `{ stmt1; stmt2; expr }`.
    ///
    /// The final expression is the block's value. If the block has no
    /// trailing expression, the value is unit `()`.
    Block {
        stmts: Vec<StyxStmt>,
        /// The trailing expression that produces the block's value.
        /// `None` means the block evaluates to unit.
        expr: Option<Box<StyxExpr>>,
    },

    /// A `do`-notation bind produced by `?` desugaring.
    ///
    /// `expr?` desugars (in HIR/THIR) to:
    ///   `match expr { Ok(v) => v, Err(e) => return Err(From::from(e)) }`
    ///
    /// We represent it explicitly because the Lean emitter produces
    /// monadic `let x <- expr; ...` which is much cleaner than the
    /// desugared match.
    ///
    /// The driver recognizes the desugared match pattern in THIR and
    /// lifts it back to this form.
    QuestionMark {
        /// The expression being tried (e.g., `state.get_cap(id)`).
        inner: Box<StyxExpr>,
        /// The `From::from` conversion applied to the error.
        /// `None` if the error type matches directly (no conversion).
        error_conversion: Option<StyxCallee>,
    },

    /// The unit value `()`.
    Unit,

    /// The never/absurd expression (produced by `unreachable!()`, `panic!()`,
    /// or exhaustive match on empty type). The emitter produces `sorry` or
    /// `absurd` depending on context.
    Absurd,
}

// ============================================================================
// Call targets
// ============================================================================

/// A fully resolved call target. No dynamic dispatch, no unresolved names.
///
/// This is one of the most important types in StyxIR — it tells the Lean
/// emitter exactly which function to call, with which generic instantiation.
///
/// In Charon's LLBC, call targets are `FnOperand::Regular(FnPtr)` which
/// bundles a `FunId` + `GenericArgs` + optional `TraitRef`. StyxIR
/// decomposes this into explicit variants for clarity.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxCallee {
    /// A known function (free function or inherent method).
    ///
    /// e.g., `Vec::new`, `Rights::is_empty`, `State::get_cap`.
    /// The `fun_id` points into `StyxPackage::functions` if local,
    /// or is resolved to its qualified path for external functions.
    Function {
        /// Qualified Rust path of the function.
        /// Used by the naming module to produce the Lean name.
        rust_path: String,
        /// `Some(id)` if the function is defined in this package.
        /// `None` if external (e.g., from std or another crate).
        local_id: Option<FunId>,
    },

    /// A trait method call, fully resolved to a specific implementation.
    ///
    /// e.g., `<Right as Ord>::cmp`, `<Vec<T> as Index<usize>>::index`.
    ///
    /// The trait and method are identified by name (not just ID) because
    /// cross-crate trait impls reference traits the driver may not have
    /// IDs for. The Lean emitter uses the names to produce the correct
    /// qualified call.
    TraitMethod {
        /// The trait being called (e.g., "core::cmp::Ord").
        trait_path: String,
        /// Local trait decl ID if the trait is defined in this crate.
        trait_id: Option<TraitDeclId>,
        /// The method name within the trait (e.g., "cmp", "index").
        method_name: String,
        /// The concrete impl type (e.g., "Right" for `<Right as Ord>`).
        /// Used to select the correct Lean impl instance.
        self_ty: StyxType,
    },

    /// A builtin operation that maps to an Aeneas standard library function.
    ///
    /// e.g., `Vec::push` -> `alloc.vec.Vec.push`,
    ///       `Vec::len` -> `alloc.vec.Vec.len`.
    ///
    /// These have fixed Lean names in the Aeneas standard library and
    /// don't need generic argument forwarding (Lean infers them).
    Builtin(StyxBuiltinFn),

    /// A closure call: `closure(args)`. The callee is an expression
    /// (typically a local variable holding a closure value).
    ///
    /// In Lean, this is just function application: `closure arg1 arg2`.
    ClosureCall(Box<StyxExpr>),
}

/// Builtin functions that map to Aeneas standard library operations.
///
/// These are special because:
/// 1. The Lean names are fixed (not derived from Rust paths).
/// 2. Generic args are implicit in Lean (no explicit type application).
/// 3. Some are pure (return T), others are monadic (return Result T).
///
/// This enum covers the builtins that appear in lion-core. Additional
/// builtins can be added as we verify more crates.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxBuiltinFn {
    // --- Vec operations ---
    VecNew,
    VecPush,
    VecLen,
    VecIndex,    // monadic (bounds check)
    VecIndexMut, // monadic, produces (T, Vec<T>) for write-back
    VecInsert,   // monadic
    VecRemove,   // monadic

    // --- Array operations ---
    ArrayRepeat,   // pure
    ArrayIndex,    // monadic
    ArrayIndexMut, // monadic

    // --- Slice operations ---
    SliceLen,
    SliceIndex, // monadic

    // --- Box operations ---
    BoxNew, // transparent in Lean

    // --- Panic/abort ---
    Panic,
    Assert,
}

// ============================================================================
// Types
// ============================================================================

/// A fully resolved Rust type. Owned, serializable, no compiler references.
///
/// This replaces both Charon's `Ty` (for LLBC mode) and the `RustType`
/// enum (for direct mode), unifying the two representations.
///
/// Key design choices:
/// - References are explicit (not erased here) so the emitter can choose
///   when to erase them. StyxIR preserves the Rust type faithfully.
/// - Smart pointers (Arc, Box, Rc) are NOT erased here — the emitter
///   handles that because erasure is a Lean-specific decision.
/// - Generic args are inline (not interned) for simplicity.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxType {
    /// Primitive scalar: u8, u16, u32, u64, u128, usize,
    /// i8, i16, i32, i64, i128, isize, bool, char.
    Scalar(ScalarTy),

    /// String types: `str`, `String`.
    Str,

    /// Named ADT (struct, enum) with generic arguments applied.
    /// For local types, `type_id` is `Some`. For external types
    /// (from std or other crates), `type_id` is `None` and the
    /// emitter uses `rust_path` for name resolution.
    Adt {
        rust_path: String,
        type_id: Option<TypeId>,
        generic_args: Vec<StyxType>,
        /// Const generic arguments (e.g., `[u8; 32]` has const arg 32).
        const_args: Vec<StyxConstGeneric>,
    },

    /// Tuple type: `(A, B, C)`.
    Tuple(Vec<StyxType>),

    /// Array type: `[T; N]`.
    Array {
        elem: Box<StyxType>,
        len: StyxConstGeneric,
    },

    /// Slice type: `[T]`.
    Slice(Box<StyxType>),

    /// Reference: `&T` or `&mut T`.
    Ref { inner: Box<StyxType>, is_mut: bool },

    /// Raw pointer: `*const T` or `*mut T`. Rare in verified code.
    RawPtr { inner: Box<StyxType>, is_mut: bool },

    /// Function pointer: `fn(A, B) -> C`.
    /// Also used for closure types after erasure.
    FnPtr {
        params: Vec<StyxType>,
        ret: Box<StyxType>,
    },

    /// `dyn Trait` — dynamic trait object.
    /// For `dyn Fn(A, B) -> C`, the emitter extracts the function
    /// signature and emits a Lean arrow type.
    /// For other traits, emits an opaque placeholder.
    DynTrait {
        /// Principal trait bound (e.g., "Fn", "Display").
        trait_path: String,
        /// Generic args on the trait (e.g., the tuple of input types for Fn).
        generic_args: Vec<StyxType>,
    },

    /// A generic type parameter: `T`, `U`. Identified by its DeBruijn
    /// index within the current generic scope.
    TypeParam {
        /// DeBruijn index (0 = innermost binding).
        index: u32,
        /// The source name (e.g., "T"). Used for readable Lean output.
        name: String,
    },

    /// An associated type: `<T as Trait>::Assoc`. Kept for types that
    /// can't be fully resolved (e.g., generic contexts).
    AssocType {
        trait_path: String,
        item_name: String,
        /// The Self type (what T resolves to).
        self_ty: Box<StyxType>,
    },

    /// The never type `!`. Uninhabited.
    Never,

    /// Unit type `()`.
    Unit,

    /// Placeholder for types we couldn't resolve. The emitter produces
    /// `STYX_UnsupportedTy` so that generated Lean still parses.
    Unsupported(String),
}

/// Primitive scalar types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ScalarTy {
    U8,
    U16,
    U32,
    U64,
    U128,
    Usize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Isize,
    Bool,
    Char,
}

/// A const generic value: either a concrete value or a type-level parameter.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxConstGeneric {
    /// A concrete integer value (e.g., `32` in `[u8; 32]`).
    Value(u128),
    /// A const generic parameter (e.g., `N` in `[T; N]`).
    Param { index: u32, name: String },
    /// A reference to a global const (e.g., `Self::SIZE`).
    Global(GlobalId),
}

// ============================================================================
// Operators
// ============================================================================

/// Binary operators for primitive types only.
///
/// Overloaded operators (e.g., `BitAnd` for `Rights`) become `Call`
/// expressions targeting the trait method. These are only for builtins:
/// integer arithmetic, comparisons, boolean logic, bitwise on primitives.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StyxBinOp {
    // Arithmetic (monadic in Lean — can overflow)
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    // Bitwise (pure in Lean — no overflow possible)
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
    // Comparison (pure)
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    // Boolean logic (pure, short-circuiting in Rust but not in Lean)
    And,
    Or,
}

/// Unary operators for primitive types.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum StyxUnOp {
    /// Boolean negation (`!b`) or bitwise complement (`!n`).
    Not,
    /// Arithmetic negation (`-n`).
    Neg,
}

// ============================================================================
// Literals
// ============================================================================

/// A literal value. Integers are stored as the widest type and tagged
/// with their actual scalar type so the emitter can produce correct
/// Lean suffixes (e.g., `42#u64`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum StyxLiteral {
    /// Unsigned integer literal with its type tag.
    UInt(u128, ScalarTy),
    /// Signed integer literal with its type tag.
    Int(i128, ScalarTy),
    /// Boolean literal.
    Bool(bool),
    /// Character literal.
    Char(char),
    /// String literal.
    Str(String),
}

// ============================================================================
// Closure captures
// ============================================================================

/// Capture information for a closure. Describes how a free variable
/// is captured: by shared reference, mutable reference, or by move.
///
/// Source: THIR's upvar analysis (available before MIR). In THIR,
/// `ExprKind::Closure` includes a `ClosureExpr` with capture info.
///
/// For lion-core, all closures are small lambdas in iterator combinators
/// that capture by shared reference. The emitter typically ignores
/// captures and inlines the closure as a Lean lambda.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct CaptureInfo {
    /// The captured local variable.
    pub local: LocalId,
    /// How the variable is captured.
    pub mode: CaptureMode,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CaptureMode {
    ByRef,
    ByMutRef,
    ByValue,
}

// ============================================================================
// Generics
// ============================================================================

/// Generic parameters on a type or function definition.
///
/// Lifetimes are included for fidelity but erased during Lean emission.
/// Type params become Lean implicit parameters. Const generics become
/// explicit Lean parameters (e.g., `(N : Nat)`).
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxGenerics {
    /// Lifetime parameter names (e.g., "'a", "'b"). Erased in Lean.
    pub lifetimes: Vec<String>,

    /// Type parameters (e.g., "T", "U").
    pub type_params: Vec<StyxTypeParam>,

    /// Const generic parameters (e.g., `const N: usize`).
    pub const_params: Vec<StyxConstParam>,

    /// Where-clause trait bounds (e.g., `T: Clone + Debug`).
    /// These become Lean typeclass parameters.
    pub where_clauses: Vec<StyxWherePredicate>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTypeParam {
    /// The name (e.g., "T").
    pub name: String,
    /// Default type, if any.
    pub default: Option<StyxType>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxConstParam {
    pub name: String,
    pub ty: StyxType,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxWherePredicate {
    /// The bounded type (e.g., "T" or a concrete type).
    pub bounded_ty: StyxType,
    /// Trait bounds (e.g., ["Clone", "Debug", "Ord"]).
    pub bounds: Vec<StyxTraitBound>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTraitBound {
    /// Qualified trait path (e.g., "core::cmp::Ord").
    pub trait_path: String,
    /// Generic args on the trait bound.
    pub generic_args: Vec<StyxType>,
}

// ============================================================================
// Traits
// ============================================================================

/// A trait declaration. Needed for:
/// 1. Emitting Lean trait structure types
/// 2. Resolving method names in trait method calls
/// 3. Determining if a trait is provided by Aeneas standard library
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTraitDecl {
    pub id: TraitDeclId,
    pub rust_path: String,
    pub name: String,
    pub generics: StyxGenerics,
    /// Method signatures declared in this trait.
    pub methods: Vec<StyxTraitMethodSig>,
    /// Super-trait bounds (e.g., `trait Foo: Bar + Baz`).
    pub super_traits: Vec<StyxTraitBound>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTraitMethodSig {
    pub name: String,
    pub params: Vec<StyxParam>,
    pub ret_ty: StyxType,
    /// True if the trait provides a default implementation.
    pub has_default: bool,
}

/// A trait implementation: connects a concrete type to a trait.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTraitImpl {
    pub id: TraitImplId,
    /// The trait being implemented.
    pub trait_path: String,
    pub trait_id: Option<TraitDeclId>,
    /// The implementing type (e.g., "Right" for `impl Ord for Right`).
    pub self_ty: StyxType,
    pub generics: StyxGenerics,
    /// Method implementations. Each references a FunId for the body.
    pub methods: Vec<StyxTraitMethodImpl>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxTraitMethodImpl {
    pub name: String,
    /// The function containing the implementation body.
    pub fun_id: FunId,
}

// ============================================================================
// Global constants
// ============================================================================

/// A global constant or static: `const X: T = expr;`
///
/// For const items with known values, the driver may evaluate them and
/// store the literal. For complex const fns, the body is stored as
/// an expression.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct StyxGlobalDef {
    pub id: GlobalId,
    pub rust_path: String,
    pub name: String,
    pub ty: StyxType,
    /// The value, if it could be evaluated or extracted.
    pub value: Option<StyxExpr>,
    pub span: StyxSpan,
}

// ============================================================================
// Source spans
// ============================================================================

/// A source location for error messages. Compact, serializable.
///
/// Unlike compiler spans, these are fully owned strings (no interned
/// file references). The file path is relative to the crate root.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct StyxSpan {
    /// File path relative to crate root (e.g., "src/capability.rs").
    pub file: String,
    /// 1-based line number.
    pub line: u32,
    /// 1-based column number.
    pub col: u32,
}

// ============================================================================
// Convenience constructors
// ============================================================================

impl StyxExpr {
    /// Create a unit literal expression `()`.
    pub fn unit() -> Self {
        Self {
            kind: StyxExprKind::Unit,
            ty: StyxType::Unit,
            span: StyxSpan::default(),
        }
    }

    /// Create a local variable reference.
    pub fn local(id: LocalId, ty: StyxType) -> Self {
        Self {
            kind: StyxExprKind::Local(id),
            ty,
            span: StyxSpan::default(),
        }
    }

    /// Create a boolean literal.
    pub fn bool_lit(val: bool) -> Self {
        Self {
            kind: StyxExprKind::Literal(StyxLiteral::Bool(val)),
            ty: StyxType::Scalar(ScalarTy::Bool),
            span: StyxSpan::default(),
        }
    }
}

impl StyxBlock {
    pub fn empty() -> Self {
        Self { stmts: Vec::new() }
    }
}

impl StyxGenerics {
    pub fn empty() -> Self {
        Self {
            lifetimes: Vec::new(),
            type_params: Vec::new(),
            const_params: Vec::new(),
            where_clauses: Vec::new(),
        }
    }

    /// True if there are no generic parameters at all.
    pub fn is_empty(&self) -> bool {
        self.lifetimes.is_empty()
            && self.type_params.is_empty()
            && self.const_params.is_empty()
            && self.where_clauses.is_empty()
    }
}
