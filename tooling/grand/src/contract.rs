//! The versioned compiler contract grand is written against.
//!
//! This module is the normative spec for what the real compiler will
//! eventually implement (docs/compiler-changes-for-tooling.md items 1-5, 7):
//!
//! - `grc --capabilities` prints a [`Capabilities`] JSON object on stdout.
//!   Legacy compilers (today's `grc`) fail this probe and get
//!   [`Capabilities::legacy`]: single-file input, rendered-text diagnostics.
//! - Compilation: `grc --diagnostics json [--phase check] [-o OUT] SOURCE...`
//!   Diagnostics are emitted on stderr, one [`Diagnostic`] JSON object per
//!   line; non-JSON stderr lines pass through to the user untouched.
//! - Interface scan: `grc --emit interfaces-json SOURCE...` prints a JSON
//!   array of [`Declaration`] on stdout; `--emit std-interfaces-json` does
//!   the same for the implicit prelude.

use std::fmt::Write as _;
use std::path::{Path, PathBuf};

use serde::{Deserialize, Serialize};

use crate::bundle::Segment;

#[derive(Debug, Clone, Default, Deserialize)]
pub struct Capabilities {
    /// Compiler version string, e.g. "0.1.0".
    pub grc: Option<String>,
    /// Contract revision; bump on incompatible CLI changes.
    #[serde(default)]
    pub contract: u32,
    #[serde(default, rename = "multi-file")]
    pub multi_file: bool,
    #[serde(default)]
    pub phases: Vec<String>,
    #[serde(default)]
    pub emit: Vec<String>,
    #[serde(default, rename = "diagnostics-json")]
    pub diagnostics_json: bool,
}

impl Capabilities {
    /// What today's `grc` supports: `grc <input.gr> <output.ll>`, nothing else.
    pub fn legacy() -> Capabilities {
        Capabilities::default()
    }

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
    /// Rewrite labels that point into an assembled bundle back to the
    /// original source files (legacy single-input compilers only see the
    /// concatenation; see docs/compiler-changes-for-tooling.md item 1).
    pub fn remap(&mut self, bundle_path: &Path, segments: &[Segment]) {
        if let Some(fix) = &mut self.fix {
            if fix.file == bundle_path {
                if let Some(segment) = segments
                    .iter()
                    .find(|s| fix.start_byte >= s.start_byte && fix.start_byte < s.start_byte + s.byte_len)
                {
                    fix.file = segment.file.clone();
                    fix.start_byte -= segment.start_byte;
                    fix.end_byte = fix.end_byte.saturating_sub(segment.start_byte);
                }
            }
        }
        for label in &mut self.labels {
            if label.file != bundle_path {
                continue;
            }
            let segment = match (label.start_byte, label.line) {
                (Some(byte), _) => segments.iter().find(|s| byte >= s.start_byte && byte < s.start_byte + s.byte_len),
                (None, Some(line)) => segments.iter().find(|s| line >= s.start_line && line < s.start_line + s.line_count),
                _ => None,
            };
            let Some(segment) = segment else { continue };
            label.file = segment.file.clone();
            if let Some(line) = &mut label.line {
                *line -= segment.start_line - 1;
            }
            if let Some(byte) = &mut label.start_byte {
                *byte -= segment.start_byte;
            }
            if let Some(byte) = &mut label.end_byte {
                *byte = byte.saturating_sub(segment.start_byte);
            }
        }
    }

    pub fn render(&self) -> String {
        let mut out = String::new();
        let severity = match self.severity {
            Severity::Error => "error",
            Severity::Warning => "warning",
            Severity::Advice => "advice",
        };
        match &self.code {
            Some(code) => { let _ = write!(out, "{severity}[{code}]: {}", self.title); }
            None => { let _ = write!(out, "{severity}: {}", self.title); }
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
    let line_start: usize = text.lines().take(line_number - 1).map(|l| l.len() + 1).sum();
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
    Global,
    Fixity,
}

/// One top-level declaration from an interface scan.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Declaration {
    pub name: String,
    pub kind: DeclarationKind,
    pub file: PathBuf,
    pub line: usize,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    /// Doc-comment text preceding the declaration (`grand doc` renders it).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub docs: Option<String>,
}

/// Parse a compiler stderr stream: JSON lines become diagnostics, everything
/// else passes through as opaque text (the legacy renderer's output).
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
