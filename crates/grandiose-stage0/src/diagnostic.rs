use crate::identity::{Digest, FileKey};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Severity {
    Error,
    Warning,
    Note,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiagnosticClass {
    Request,
    InputCorruption,
    Source,
    Recovery,
    Resource,
    Cancellation,
    Cache,
    Invariant,
    Verification,
    Runtime,
}

/// A stable cross-phase code. The textual message is deliberately not the
/// identity used by tests, tooling, or machine-readable output.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DiagnosticCode(pub &'static str);

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceSpan {
    pub file: FileKey,
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Diagnostic {
    pub code: DiagnosticCode,
    pub class: DiagnosticClass,
    pub severity: Severity,
    pub message: String,
    pub primary: Option<SourceSpan>,
    pub input_fingerprint: Option<Digest>,
}

impl Diagnostic {
    pub fn request(code: &'static str, message: impl Into<String>) -> Self {
        Self {
            code: DiagnosticCode(code),
            class: DiagnosticClass::Request,
            severity: Severity::Error,
            message: message.into(),
            primary: None,
            input_fingerprint: None,
        }
    }
}
