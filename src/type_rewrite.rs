//! Type rewrite rules for mapping Rust stdlib types to Lean equivalents.
//!
//! When styx encounters BTreeMap, HashMap, Arc, etc. in Rust source types,
//! these rules transform them into appropriate Lean types.

use crate::rust_parser::{RustType, rust_type_to_lean};

/// Collection of type rewrite rules.
pub struct RewriteRules {
    _custom: Vec<()>, // Reserved for future custom rules.
}

impl RewriteRules {
    /// Create the standard rewrite rules for Rust → Lean translation.
    pub fn standard() -> Self {
        RewriteRules {
            _custom: Vec::new(),
        }
    }

    /// Rewrite a named (non-generic) type. Returns None if no rule applies.
    pub fn rewrite_named(&self, name: &str) -> Option<String> {
        match name {
            // Rust String → Lean String.
            "String" | "std::string::String" | "alloc::string::String" => {
                Some("String".to_string())
            }
            // PhantomData → Unit (zero-size type).
            "PhantomData" | "std::marker::PhantomData" => Some("Unit".to_string()),
            _ => None,
        }
    }

    /// Rewrite a generic type application. Returns None if no rule applies.
    pub fn rewrite_generic(&self, base: &str, args: &[RustType]) -> Option<String> {
        match base {
            // BTreeMap<K, V> → Std.HashMap K V
            "BTreeMap" | "std::collections::BTreeMap" | "alloc::collections::BTreeMap" => {
                if args.len() == 2 {
                    let k = rust_type_to_lean(&args[0], self);
                    let v = rust_type_to_lean(&args[1], self);
                    Some(format!("(Std.HashMap {} {})", k, v))
                } else {
                    None
                }
            }
            // HashMap<K, V> → Std.HashMap K V
            "HashMap" | "std::collections::HashMap" => {
                if args.len() >= 2 {
                    let k = rust_type_to_lean(&args[0], self);
                    let v = rust_type_to_lean(&args[1], self);
                    Some(format!("(Std.HashMap {} {})", k, v))
                } else {
                    None
                }
            }
            // BTreeSet<T> → Std.HashSet T
            "BTreeSet" | "std::collections::BTreeSet" | "alloc::collections::BTreeSet" => {
                if args.len() == 1 {
                    let t = rust_type_to_lean(&args[0], self);
                    Some(format!("(Std.HashSet {})", t))
                } else {
                    None
                }
            }
            // HashSet<T> → Std.HashSet T
            "HashSet" | "std::collections::HashSet" => {
                if args.len() == 1 {
                    let t = rust_type_to_lean(&args[0], self);
                    Some(format!("(Std.HashSet {})", t))
                } else {
                    None
                }
            }
            // Vec<T> → Vec T (Aeneas Vec)
            "Vec" | "alloc::vec::Vec" => {
                if args.len() == 1 {
                    let t = rust_type_to_lean(&args[0], self);
                    Some(format!("(Vec {})", t))
                } else {
                    None
                }
            }
            // Arc<T> → T (erase smart pointer)
            "Arc" | "std::sync::Arc" | "alloc::sync::Arc" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            // Rc<T> → T (erase smart pointer)
            "Rc" | "std::rc::Rc" | "alloc::rc::Rc" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            // Box<T> → T (erase box)
            "Box" | "alloc::boxed::Box" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            // Option<T> → Option T
            "Option" | "core::option::Option" | "std::option::Option" => {
                if args.len() == 1 {
                    let t = rust_type_to_lean(&args[0], self);
                    Some(format!("(Option {})", t))
                } else {
                    None
                }
            }
            // Result<T, E> → core.result.Result T E
            "Result" | "core::result::Result" | "std::result::Result" => {
                if args.len() == 2 {
                    let t = rust_type_to_lean(&args[0], self);
                    let e = rust_type_to_lean(&args[1], self);
                    Some(format!("(core.result.Result {} {})", t, e))
                } else {
                    None
                }
            }
            // Cow<T> → T (erase copy-on-write)
            "Cow" | "std::borrow::Cow" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            // Mutex<T> → T (erase synchronization)
            "Mutex" | "std::sync::Mutex" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            // RwLock<T> → T (erase synchronization)
            "RwLock" | "std::sync::RwLock" => {
                if args.len() == 1 {
                    Some(rust_type_to_lean(&args[0], self))
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}
