//! The versioned compiler contract grand is written against.
//!
//! This module defines the contract between `grand` and `grc`:
//!
//! - `grc --capabilities` prints a [`Capabilities`] JSON object on stdout.
//! - Compilation: `grc --diagnostics json [--phase resolve|check] [-o OUT] SOURCE...`
//!   Diagnostics are emitted on stderr, one [`Diagnostic`] JSON object per
//!   line; non-JSON stderr lines pass through to the user untouched.
//! - Interface scan: `grc --emit interfaces-json SOURCE...` prints a JSON
//!   array of [`Declaration`] on stdout; `--emit std-interfaces-json` does
//!   the same for the implicit prelude.
//! - Persistent session: an optional bounded versioned `grc --serve`
//!   JSON-lines transport, described by [`ServeCapabilities`]. Grand validates
//!   this contract but remains a batch client because one build has no request
//!   stream to amortize.

use std::fmt::Write as _;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Default, Deserialize)]
pub struct Capabilities {
    /// Compiler version string, e.g. "0.1.0".
    pub grc: Option<String>,
    /// Contract revision; bump on incompatible CLI changes.
    #[serde(default)]
    pub contract: u32,
    #[serde(default, rename = "contract-min")]
    pub contract_min: Option<u32>,
    #[serde(default, rename = "contract-max")]
    pub contract_max: Option<u32>,
    #[serde(default, rename = "artifact-major")]
    pub artifact_major: Option<u16>,
    #[serde(default, rename = "artifact-minor")]
    pub artifact_minor: Option<u16>,
    /// Compatibility identity of the released seed/artifact contract used by
    /// this compiler. Both fields are absent for pre-negotiation compilers.
    #[serde(default, rename = "seed-identity-version")]
    pub seed_identity_version: Option<u32>,
    #[serde(default, rename = "seed-identity")]
    pub seed_identity: Option<String>,
    /// Optional persistent subprocess protocol. Grand currently remains a
    /// batch client, but records and validates this shape for editor/build
    /// clients that can amortize multiple requests.
    #[serde(default)]
    pub serve: Option<ServeCapabilities>,
    #[serde(default, rename = "multi-file")]
    pub multi_file: bool,
    /// The first input is a crate root and external `mod` declarations follow
    /// the hybrid self-named-directory layout.
    #[serde(default)]
    pub modules: bool,
    #[serde(default)]
    pub phases: Vec<String>,
    #[serde(default)]
    pub emit: Vec<String>,
    #[serde(default, rename = "diagnostics-json")]
    pub diagnostics_json: bool,
}

#[derive(Debug, Clone, Deserialize)]
pub struct ServeCapabilities {
    pub protocol: u32,
    pub transport: String,
    #[serde(rename = "max-request-bytes")]
    pub max_request_bytes: usize,
    #[serde(rename = "max-arguments")]
    pub max_arguments: usize,
    #[serde(rename = "max-inputs")]
    pub max_inputs: usize,
    #[serde(rename = "max-source-bytes")]
    pub max_source_bytes: usize,
}

impl Capabilities {
    pub fn has_phase(&self, phase: &str) -> bool {
        self.phases.iter().any(|p| p == phase)
    }

    pub fn can_emit(&self, kind: &str) -> bool {
        self.emit.iter().any(|e| e == kind)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum Severity {
    Error,
    Warning,
    Advice,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Label {
    pub file: PathBuf,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub line: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub col: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub start_byte: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub end_byte: Option<usize>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

/// A machine-applicable replacement: `grand fix` applies these.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Fix {
    pub file: PathBuf,
    pub start_byte: usize,
    pub end_byte: usize,
    pub replacement: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    pub severity: Severity,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    pub title: String,
    /// Substantive diagnostic text. Older compilers only supplied this on a
    /// primary label, so it remains optional for contract compatibility.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
    #[serde(default)]
    pub labels: Vec<Label>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub help: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub fix: Option<Fix>,
}

impl Diagnostic {
    pub fn render(&self) -> String {
        let mut out = String::new();
        let severity = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Advice => "advice",
        };
        match &self.code {
            Some(code) => {
                let _ = write!(out, "{severity}[{code}]: {}", self.title);
            }
            None => {
                let _ = write!(out, "{severity}: {}", self.title);
            }
        }
        if self.labels.is_empty() {
            if let Some(message) = &self.message {
                let _ = write!(out, "\n  = {message}");
            }
        }
        for label in &self.labels {
            let _ = write!(out, "\n  --> {}", label.file.display());
            if let Some(line) = label.line {
                let _ = write!(out, ":{line}");
                if let Some(col) = label.col {
                    let _ = write!(out, ":{col}");
                }
            }
            if let Some(message) = &label.message {
                let _ = write!(out, ": {message}");
            }
            out.push_str(&snippet(label));
        }
        if let Some(note) = &self.note {
            let _ = write!(out, "\n  = note: {note}");
        }
        if let Some(help) = &self.help {
            let _ = write!(out, "\n  = help: {help}");
        }
        out
    }
}

/// Render the labeled source line with a caret underline, if the file is
/// readable and a line is known. Best-effort: any failure yields "".
fn snippet(label: &Label) -> String {
    let (Some(line_number), Ok(text)) = (label.line, std::fs::read_to_string(&label.file)) else {
        return String::new();
    };
    let Some(line_text) = text.lines().nth(line_number.saturating_sub(1)) else {
        return String::new();
    };
    let line_start: usize = text
        .lines()
        .take(line_number - 1)
        .map(|l| l.len() + 1)
        .sum();
    let column = label
        .col
        .or_else(|| label.start_byte.map(|b| b.saturating_sub(line_start) + 1))
        .unwrap_or(1)
        .clamp(1, line_text.len().max(1));
    let width = match (label.start_byte, label.end_byte) {
        (Some(start), Some(end)) if end > start => (end - start).min(line_text.len() - column + 1),
        _ => 1,
    };
    format!(
        "\n{line_number:>5} | {line_text}\n      | {}{}",
        " ".repeat(column - 1),
        "^".repeat(width.max(1))
    )
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DeclarationKind {
    Callable,
    Struct,
    Enum,
    Type,
    Effect,
    Trait,
    Impl,
    Global,
    Fixity,
}

/// One top-level declaration from an interface scan.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Declaration {
    /// Compiler-owned namespace/module identity. If absent, callers use the
    /// unqualified spelling.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub identity: Option<String>,
    pub name: String,
    pub kind: DeclarationKind,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub visibility: Option<String>,
    pub file: PathBuf,
    pub line: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    /// Doc-comment text preceding the declaration (`grand doc` renders it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub docs: Option<String>,
}

/// Parse a compiler stderr stream: JSON lines become diagnostics, everything
/// else passes through as opaque compiler text.
pub fn parse_stderr(stderr: &str) -> (Vec<Diagnostic>, String) {
    let mut diagnostics = Vec::new();
    let mut passthrough = String::new();
    for line in stderr.lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with('{') {
            if let Ok(diagnostic) = serde_json::from_str::<Diagnostic>(trimmed) {
                diagnostics.push(diagnostic);
                continue;
            }
        }
        passthrough.push_str(line);
        passthrough.push('\n');
    }
    (diagnostics, passthrough)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn spanless_json_diagnostic_preserves_and_renders_message() {
        let (diagnostics, passthrough) = parse_stderr(
            r#"{"severity":"error","code":"G1OPT999","title":"error","message":"optimizer validation failed","labels":[]}"#,
        );

        assert!(passthrough.is_empty());
        assert_eq!(diagnostics.len(), 1);
        assert_eq!(
            diagnostics[0].render(),
            "error[G1OPT999]: error\n  = optimizer validation failed"
        );
    }

    #[test]
    fn top_level_message_does_not_duplicate_labeled_diagnostic_text() {
        let (diagnostics, passthrough) = parse_stderr(
            r#"{"severity":"error","code":"GRC0001","title":"unknown name","message":"`missing` is not defined","labels":[{"file":"input.glorious","line":1,"message":"`missing` is not defined"}]}"#,
        );

        assert!(passthrough.is_empty());
        let rendered = diagnostics[0].render();
        assert_eq!(rendered.matches("`missing` is not defined").count(), 1);
        assert!(rendered.contains("input.glorious:1"));
    }
}
