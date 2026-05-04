//! styx: StyxIR-to-Lean4 translator.
//!
//! Translates Rust programs (via StyxIR from styx-rustc) into Lean 4 for
//! formal verification. Emits Aeneas-compatible Lean with transparent function
//! bodies where possible, opaque declarations for external/unsupported patterns.

#![allow(
    clippy::while_let_loop,
    clippy::needless_range_loop,
    clippy::manual_strip,
    clippy::ptr_arg,
    clippy::len_without_is_empty,
    clippy::unnecessary_unwrap
)]

pub mod config;
pub mod emit;
pub mod ir;
pub mod lean_parser;
pub mod passes;
pub mod reachability;
pub mod rust_parser;
pub mod type_rewrite;

pub mod naming {
    const LEAN_KEYWORDS: &[&str] = &[
        "def", "theorem", "lemma", "structure", "inductive", "where", "match",
        "if", "then", "else", "do", "return", "let", "have", "fun", "forall",
        "exists", "Type", "Prop", "Sort", "import", "open", "namespace",
        "section", "variable", "class", "instance", "axiom", "opaque", "abbrev",
        "mutual", "end", "in", "with", "deriving", "private", "protected",
        "noncomputable", "unsafe", "partial", "set_option", "attribute", "syntax",
        "macro", "elab", "by", "calc", "show", "sorry", "admit", "true", "false",
        "this", "meta", "from", "to", "at",
    ];

    pub fn is_lean_keyword(s: &str) -> bool {
        LEAN_KEYWORDS.contains(&s)
    }

    pub fn escape_lean_keyword(name: &str) -> String {
        if is_lean_keyword(name) {
            format!("{name}_")
        } else if name.starts_with(|c: char| c.is_ascii_digit()) {
            format!("field_{name}")
        } else {
            name.to_string()
        }
    }

    pub fn escape_lean_ident(raw: &str) -> String {
        if raw.is_empty() {
            return "_".to_string();
        }
        let mut out = String::with_capacity(raw.len());
        for (i, ch) in raw.chars().enumerate() {
            let ok = matches!(ch, 'a'..='z' | 'A'..='Z' | '0'..='9' | '_');
            if i == 0 {
                let ok_first = matches!(ch, 'a'..='z' | 'A'..='Z' | '_');
                if ok && ok_first {
                    out.push(ch);
                } else if ok {
                    out.push('_');
                    out.push(ch);
                } else {
                    out.push('_');
                }
            } else if ok {
                out.push(ch);
            } else {
                out.push('_');
            }
        }
        if is_lean_keyword(&out) {
            out.push('_');
        }
        out
    }
}

pub use config::Config;
pub use emit::indent::IndentWriter;
