//! Source-only compiler stages. No inference, trait solver, MIR, or VM dependency.

pub mod scanner;
pub mod source;

pub use grandiose_compiler_base::{Digest, FileKey, ModuleKey, PackageKey, Safety};
pub use scanner::{DeclarationKind, DeclarationScan, DeclarationShell, ScanDiagnostic,
    TokenRange, Visibility};
pub use source::{LexedFile, LexerDiagnostic, LineIndex, SourcePosition, Span, Token, TokenKind};
