use std::io::{self, Write};

use ariadne::{Color, Label, Report, ReportKind, Source};

use crate::span::Span;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Severity {
    Error,
    Warning,
    Advice,
}

/// One machine-applicable source replacement.
///
/// The span uses the same bundle-global coordinates as the diagnostic until a
/// [`crate::source_bundle::SourceBundle`] localizes it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DiagnosticFix {
    pub span: Span,
    pub replacement: String,
}

#[derive(Clone, Debug)]
pub struct Diagnostic {
    pub severity: Severity,
    pub source_name: String,
    pub title: String,
    pub message: String,
    pub span: Option<Span>,
    pub help: Option<String>,
    pub note: Option<String>,
    pub code: Option<String>,
    pub related: Vec<(Span, String)>,
    pub fix: Option<DiagnosticFix>,
    pub embedded_source: Option<String>,
}

impl Diagnostic {
    pub fn error(title: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        Self {
            severity: Severity::Error,
            source_name: "<source>".into(),
            title: title.into(),
            message: message.into(),
            span: Some(span),
            help: None,
            note: None,
            code: None,
            related: Vec::new(),
            fix: None,
            embedded_source: None,
        }
    }

    pub fn plain(message: impl Into<String>) -> Self {
        Self {
            severity: Severity::Error,
            source_name: "<source>".into(),
            title: "error".into(),
            message: message.into(),
            span: None,
            help: None,
            note: None,
            code: None,
            related: Vec::new(),
            fix: None,
            embedded_source: None,
        }
    }

    pub fn warning(title: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        let mut diagnostic = Self::error(title, message, span);
        diagnostic.severity = Severity::Warning;
        diagnostic
    }

    pub fn advice(title: impl Into<String>, message: impl Into<String>, span: Span) -> Self {
        let mut diagnostic = Self::error(title, message, span);
        diagnostic.severity = Severity::Advice;
        diagnostic
    }

    pub fn with_help(mut self, help: impl Into<String>) -> Self {
        self.help = Some(help.into());
        self
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    pub fn with_source(mut self, source_name: impl Into<String>) -> Self {
        if self.embedded_source.is_none() {
            self.source_name = source_name.into();
        }
        self
    }

    pub fn with_embedded_source(
        mut self,
        source_name: impl Into<String>,
        source: impl Into<String>,
    ) -> Self {
        self.source_name = source_name.into();
        self.embedded_source = Some(source.into());
        self
    }

    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }

    pub fn with_related(mut self, span: Span, message: impl Into<String>) -> Self {
        self.related.push((span, message.into()));
        self
    }

    pub fn with_fix(mut self, span: Span, replacement: impl Into<String>) -> Self {
        self.fix = Some(DiagnosticFix {
            span,
            replacement: replacement.into(),
        });
        self
    }

    pub fn write(&self, source: &str, mut output: impl Write) -> io::Result<()> {
        let source = self.embedded_source.as_deref().unwrap_or(source);
        if let Some(span) = self.span {
            let kind = match self.severity {
                Severity::Error => ReportKind::Error,
                Severity::Warning => ReportKind::Warning,
                Severity::Advice => ReportKind::Advice,
            };
            let primary_color = match self.severity {
                Severity::Error => Color::Red,
                Severity::Warning => Color::Yellow,
                Severity::Advice => Color::Cyan,
            };
            let mut builder = Report::build(kind, (&self.source_name, span.range()))
                .with_message(&self.title)
                .with_label(
                    Label::new((&self.source_name, span.range()))
                        .with_message(&self.message)
                        .with_color(primary_color),
                );
            if let Some(code) = &self.code {
                builder = builder.with_code(code);
            }
            for (related_span, message) in &self.related {
                builder = builder.with_label(
                    Label::new((&self.source_name, related_span.range()))
                        .with_message(message)
                        .with_color(Color::Blue),
                );
            }
            if let Some(help) = &self.help {
                builder = builder.with_help(help);
            }
            if let Some(note) = &self.note {
                builder = builder.with_note(note);
            }
            builder
                .finish()
                .write((&self.source_name, Source::from(source)), &mut output)
        } else {
            writeln!(output, "error: {}", self.message)
        }
    }
}
