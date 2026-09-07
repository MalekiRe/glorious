//! Structured diagnostic publication, canonicalization, and presentation.

use crate::{DiagnosticClass, Digest, InputError, Severity, SourceSpan, Span};
use std::collections::BTreeMap;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileDiagnostic {
    pub code: &'static str,
    pub message: String,
    /// Stable failure classification.  Tooling must not infer this from a
    /// textual message or a numeric-code range.
    pub class: DiagnosticClass,
    pub severity: Severity,
    /// The primary source identity when this fact originated from source.
    pub primary: Option<SourceSpan>,
    /// The immutable request world from which this diagnostic was derived.
    pub input_fingerprint: Option<Digest>,
    /// Source locations which explain the primary fact without competing with
    /// it for the editor's primary highlight.
    pub related: Vec<RelatedDiagnosticLocation>,
    /// Canonical semantic facts suitable for both a human explanation and a
    /// machine client.  These deliberately retain names and values as
    /// separate fields rather than encoding a second sentence in `message`.
    pub facts: Vec<DiagnosticFact>,
    /// Ordered explanation frames from the semantic boundary to the reported
    /// failure.  Frames are canonicalized before publication, so phase and
    /// map traversal order cannot affect a diagnostic product.
    pub explanation: Vec<DiagnosticExplanationFrame>,
}

/// A non-primary source location participating in a compiler diagnostic.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RelatedDiagnosticLocation {
    pub label: String,
    pub span: SourceSpan,
}

/// A typed-by-name semantic observation attached to a diagnostic.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DiagnosticFact {
    pub name: String,
    pub value: String,
}

/// One stable step in a semantic explanation chain.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DiagnosticExplanationFrame {
    pub kind: String,
    pub message: String,
}

impl CompileDiagnostic {
    /// The maximum number of error diagnostics published for one failed
    /// request. Keeping this bound at the service boundary protects hosts and
    /// tools from pathological recovery cascades while preserving a single,
    /// explicit explanation that additional facts were suppressed.
    pub const DEFAULT_ERROR_LIMIT: usize = 100;

    /// Serialize one published diagnostic as a self-contained JSON object.
    ///
    /// The service deliberately owns this small serializer instead of exposing
    /// Rust `Debug` output to editor and build-tool clients. Field order is
    /// fixed, source locations use stable file identities plus byte offsets,
    /// and every control character in a diagnostic message is escaped
    /// according to JSON's string grammar. Callers should emit one returned
    /// value per line (JSON Lines), after the batch has crossed the ordinary
    /// canonicalization and span-validation boundary.
    pub fn to_json_line(&self) -> String {
        let primary = self.primary.map_or_else(
            || "null".to_owned(),
            |primary| {
                format!(
                    "{{\"file\":\"{}\",\"start_byte\":{},\"end_byte\":{}}}",
                    primary.file.0, primary.start, primary.end
                )
            },
        );
        let input_fingerprint = self.input_fingerprint.map_or_else(
            || "null".to_owned(),
            |fingerprint| format!("\"{fingerprint}\""),
        );
        let related = json_array(self.related.iter().map(|related| {
            format!(
                "{{\"label\":\"{}\",\"span\":{{\"file\":\"{}\",\"start_byte\":{},\"end_byte\":{}}}}}",
                json_escape(&related.label),
                related.span.file.0,
                related.span.start,
                related.span.end,
            )
        }));
        let facts = json_array(self.facts.iter().map(|fact| {
            format!(
                "{{\"name\":\"{}\",\"value\":\"{}\"}}",
                json_escape(&fact.name),
                json_escape(&fact.value),
            )
        }));
        let explanation = json_array(self.explanation.iter().map(|frame| {
            format!(
                "{{\"kind\":\"{}\",\"message\":\"{}\"}}",
                json_escape(&frame.kind),
                json_escape(&frame.message),
            )
        }));
        format!(
            "{{\"code\":\"{}\",\"class\":\"{}\",\"severity\":\"{}\",\"message\":\"{}\",\"primary\":{},\"related\":{},\"facts\":{},\"explanation\":{},\"input_fingerprint\":{}}}",
            self.code,
            self.class.json_name(),
            self.severity.json_name(),
            json_escape(&self.message),
            primary,
            related,
            facts,
            explanation,
            input_fingerprint,
        )
    }

    /// Render a deterministic, line-oriented human projection of this
    /// structured fact.  Hosts may choose their own presentation, but the
    /// stage-zero CLI uses this stable fallback rather than discarding
    /// semantic context.
    pub fn text_lines(&self) -> Vec<String> {
        let mut lines = vec![format!("{}: {}", self.code, self.message)];
        lines.extend(self.related.iter().map(|related| {
            format!(
                "  related {} at {}:{}..{}",
                related.label, related.span.file.0, related.span.start, related.span.end
            )
        }));
        lines.extend(
            self.facts
                .iter()
                .map(|fact| format!("  fact {}: {}", fact.name, fact.value)),
        );
        lines.extend(
            self.explanation
                .iter()
                .map(|frame| format!("  because {}: {}", frame.kind, frame.message)),
        );
        lines
    }

    pub fn with_related_location(mut self, label: impl Into<String>, span: SourceSpan) -> Self {
        self.related.push(RelatedDiagnosticLocation {
            label: label.into(),
            span,
        });
        self
    }

    pub fn with_fact(mut self, name: impl Into<String>, value: impl Into<String>) -> Self {
        self.facts.push(DiagnosticFact {
            name: name.into(),
            value: value.into(),
        });
        self
    }

    pub fn with_explanation(mut self, kind: impl Into<String>, message: impl Into<String>) -> Self {
        self.explanation.push(DiagnosticExplanationFrame {
            kind: kind.into(),
            message: message.into(),
        });
        self
    }

    pub(super) fn source(
        code: &'static str,
        message: impl Into<String>,
        span: Option<Span>,
    ) -> Self {
        Self::new(code, message, DiagnosticClass::Source, span)
    }

    pub(super) fn request(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Request, None)
    }

    pub(super) fn invariant(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Invariant, None)
    }

    pub(super) fn verification(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Verification, None)
    }

    pub(super) fn input_corruption(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::InputCorruption, None)
    }

    pub(super) fn resource(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Resource, None)
    }

    pub(super) fn cancellation(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Cancellation, None)
    }

    fn new(
        code: &'static str,
        message: impl Into<String>,
        class: DiagnosticClass,
        span: Option<Span>,
    ) -> Self {
        Self {
            code,
            message: message.into(),
            class,
            severity: Severity::Error,
            primary: span.map(|span| SourceSpan {
                file: span.file,
                start: span.start,
                end: span.end,
            }),
            input_fingerprint: None,
            related: Vec::new(),
            facts: Vec::new(),
            explanation: Vec::new(),
        }
    }

    /// Canonicalize a diagnostic batch at the service boundary.  Individual
    /// compiler phases deliberately retain local recovery behavior, so more
    /// than one phase can independently report the same source fact.  The
    /// published result must neither depend on phase traversal order nor make
    /// clients render that fact repeatedly.
    pub fn canonicalize(mut diagnostics: Vec<Self>) -> Vec<Self> {
        // De-duplication is about identity, while rendering order is about
        // source priority.  Keep those two concerns separate: sorting by the
        // identity key first makes `dedup_by` deterministic, then the public
        // batch is reordered according to the documented source-first order.
        for diagnostic in &mut diagnostics {
            diagnostic.canonicalize_provenance();
        }
        diagnostics.sort_by(|left, right| left.fact_key().cmp(&right.fact_key()));
        let mut merged = Vec::<Self>::with_capacity(diagnostics.len());
        for diagnostic in diagnostics {
            if let Some(previous) = merged
                .last_mut()
                .filter(|previous| previous.fact_key() == diagnostic.fact_key())
            {
                previous.related.extend(diagnostic.related);
                previous.facts.extend(diagnostic.facts);
                previous.explanation.extend(diagnostic.explanation);
                previous.canonicalize_provenance();
            } else {
                merged.push(diagnostic);
            }
        }
        let mut diagnostics = merged;
        diagnostics.sort_by(|left, right| left.presentation_key().cmp(&right.presentation_key()));
        diagnostics
    }

    /// Defend the publication boundary from malformed phase-local locations.
    /// A compiler bug must not make a host or editor trust a source span that
    /// names an absent input or points outside the immutable request snapshot.
    /// Replace the invalid fact with a stable invariant diagnostic instead.
    pub fn validate_primary_spans(
        diagnostics: Vec<Self>,
        source_lengths: &BTreeMap<crate::FileKey, u32>,
    ) -> Vec<Self> {
        diagnostics
            .into_iter()
            .map(|diagnostic| {
                let primary_valid = diagnostic.primary.is_none_or(|primary| {
                    source_lengths
                        .get(&primary.file)
                        .is_some_and(|length| primary.start <= primary.end && primary.end <= *length)
                });
                let related_valid = diagnostic.related.iter().all(|related| {
                    source_lengths.get(&related.span.file).is_some_and(|length| {
                        related.span.start <= related.span.end && related.span.end <= *length
                    })
                });
                if primary_valid && related_valid {
                    diagnostic
                } else {
                    let mut replacement = Self::invariant(
                        "G7014",
                        format!(
                            "compiler produced diagnostic {} with an invalid source provenance span",
                            diagnostic.code
                        ),
                    );
                    replacement.input_fingerprint = diagnostic.input_fingerprint;
                    replacement
                }
            })
            .collect()
    }

    /// Publish at most `limit` error facts from a canonical batch. Warnings
    /// and notes remain useful context and do not consume the error budget.
    /// If the limit is exceeded, the last error slot is reserved for a stable
    /// resource diagnostic that states exactly how many errors were hidden.
    pub fn limit_errors(diagnostics: Vec<Self>, limit: usize) -> Vec<Self> {
        // A terminal resource fact must remain observable, so normalize an
        // accidental zero configuration to the smallest meaningful budget.
        let limit = limit.max(1);
        let diagnostics = Self::canonicalize(diagnostics);
        let error_count = diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .count();
        if error_count <= limit {
            return diagnostics;
        }

        let retained_error_count = limit.saturating_sub(1);
        let mut remaining_errors = retained_error_count;
        let mut published = Vec::with_capacity(diagnostics.len());
        let mut suppressed = 0usize;
        for diagnostic in diagnostics {
            if diagnostic.severity == Severity::Error {
                if remaining_errors == 0 {
                    suppressed += 1;
                    continue;
                }
                remaining_errors -= 1;
            }
            published.push(diagnostic);
        }
        published.push(Self::resource(
            "G7013",
            format!(
                "diagnostic error limit of {limit} reached; {suppressed} additional error(s) suppressed"
            ),
        ));
        Self::canonicalize(published)
    }

    fn fact_key(
        &self,
    ) -> (
        &'static str,
        DiagnosticClass,
        Severity,
        Option<SourceSpan>,
        &str,
    ) {
        // Request provenance is attached after all phase-local diagnostics
        // have been produced.  It identifies the outcome, not a distinct
        // user-facing diagnostic fact, and is intentionally excluded here.
        (
            self.code,
            self.class,
            self.severity,
            self.primary,
            &self.message,
        )
    }

    pub(super) fn canonicalize_provenance(&mut self) {
        self.related.sort();
        self.related.dedup();
        self.facts.sort();
        self.facts.dedup();
        self.explanation.sort();
        self.explanation.dedup();
    }

    fn presentation_key(
        &self,
    ) -> (
        u8,
        Option<SourceSpan>,
        Severity,
        &'static str,
        DiagnosticClass,
        &str,
    ) {
        // Source facts appear before diagnostics without a primary location;
        // the latter still have a deterministic order after the source bundle.
        // `SourceSpan` supplies the stable file/start/end tie-breakers, while
        // severity and code implement the frontend diagnostic contract.
        (
            u8::from(self.primary.is_none()),
            self.primary,
            self.severity,
            self.code,
            self.class,
            &self.message,
        )
    }
}

fn json_array(values: impl IntoIterator<Item = String>) -> String {
    format!("[{}]", values.into_iter().collect::<Vec<_>>().join(","))
}

impl Severity {
    fn json_name(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
            Self::Note => "note",
        }
    }
}

impl DiagnosticClass {
    fn json_name(self) -> &'static str {
        match self {
            Self::Request => "request",
            Self::InputCorruption => "input_corruption",
            Self::Source => "source",
            Self::Recovery => "recovery",
            Self::Resource => "resource",
            Self::Cancellation => "cancellation",
            Self::Cache => "cache",
            Self::Invariant => "invariant",
            Self::Verification => "verification",
            Self::Runtime => "runtime",
        }
    }
}

fn json_escape(value: &str) -> String {
    let mut escaped = String::with_capacity(value.len());
    for character in value.chars() {
        match character {
            '"' => escaped.push_str("\\\""),
            '\\' => escaped.push_str("\\\\"),
            '\u{08}' => escaped.push_str("\\b"),
            '\u{0C}' => escaped.push_str("\\f"),
            '\n' => escaped.push_str("\\n"),
            '\r' => escaped.push_str("\\r"),
            '\t' => escaped.push_str("\\t"),
            character if character.is_control() => {
                use std::fmt::Write;
                write!(&mut escaped, "\\u{:04x}", character as u32)
                    .expect("writing into a String cannot fail");
            }
            character => escaped.push(character),
        }
    }
    escaped
}
impl CompileDiagnostic {
    pub(super) fn from_input_error(error: &InputError) -> Self {
        let (code, class) = match error {
            InputError::EmptySources => ("G7015", DiagnosticClass::Request),
            InputError::DuplicateFileKey(_) => ("G7016", DiagnosticClass::Request),
            InputError::DigestMismatch { .. } => ("G7017", DiagnosticClass::InputCorruption),
            InputError::SourceIdentityMismatch { .. } => {
                ("G7017", DiagnosticClass::InputCorruption)
            }
            InputError::InvalidUtf8(_) => ("G7018", DiagnosticClass::InputCorruption),
            InputError::InvalidLogicalPath(_) => ("G7019", DiagnosticClass::Request),
            InputError::InvalidPackageModuleAlias(_) => ("G7036", DiagnosticClass::Request),
            InputError::DuplicatePackageModuleAlias { .. } => ("G7036", DiagnosticClass::Request),
            InputError::DuplicateCapability(_) => ("G7020", DiagnosticClass::Request),
            InputError::InvalidCapability(_) => ("G7021", DiagnosticClass::Request),
            InputError::InvalidRuntimeManifest => ("G7022", DiagnosticClass::Request),
            InputError::InvalidBootstrapStage { .. } => ("G7023", DiagnosticClass::Request),
            InputError::BootstrapSourceLimit { .. } => ("G7024", DiagnosticClass::Resource),
        };
        Self::new(code, error.to_string(), class, None)
    }
}
