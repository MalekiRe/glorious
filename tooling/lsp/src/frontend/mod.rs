//! Vendored copy of the compiler frontend (crates/grandiose/src), taken
//! 2026-07-19 with `crate::` rewritten to `crate::frontend::`.
//!
//! DO NOT fix compiler bugs here and DO NOT fix LSP issues there — the
//! original is owned by the compiler effort and will be reconciled with this
//! copy once it stabilizes. LSP-motivated changes (error resilience, extra
//! spans) belong in this copy and should be listed in ../DIVERGENCES.md so
//! reconciliation is mechanical.

// dead_code: the LSP uses lex/parse/validate but not evaluation, so fields
// only the interpreter reads are unused here. Suppressed at the module edge
// to keep the vendored files byte-identical to their origin.
#[allow(dead_code)]
pub mod ast;
#[allow(dead_code)]
pub mod diagnostic;
#[allow(dead_code)]
pub mod lexer;
#[allow(dead_code)]
pub mod parser;
#[allow(dead_code)]
pub mod source_bundle;
#[allow(dead_code)]
pub mod span;
#[allow(dead_code)]
pub mod validate;
