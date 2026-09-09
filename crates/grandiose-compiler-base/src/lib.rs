//! Compiler vocabulary with no dependency on parsing, semantic analysis, or execution.

pub mod diagnostic;
pub mod identity;
pub mod quantity;

pub use diagnostic::{Diagnostic, DiagnosticClass, DiagnosticCode, Severity, SourceSpan};
pub use identity::{DefKey, Digest, FileKey, ModuleKey, PackageKey, RevisionId,
    implementation_method_key, package_module_alias};
pub use quantity::{Quantity, QuantityError};

/// Whether invoking a callable requires programmer-owned unsafe obligations.
/// This is a type contract, not an effect, implementation trust certificate,
/// or host authorization to execute unsafe bytecode.
#[derive(Clone, Copy, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Safety {
    #[default]
    Safe,
    Unsafe,
}
