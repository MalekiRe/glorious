//! End-to-end semantic service over immutable compilation requests.
//!
//! The command adapter may read files, but this service receives only a
//! `CompilationRequest`; every compiler product derives from its pinned
//! revision snapshot.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::revision::RequestControlError;
use crate::{
    BodySyntax, BootstrapManifest, Budget, BudgetError, CancellationToken, CoherenceSet,
    CompilationMode, CompilationRequest, CompilerDatabase, DatabaseSnapshot, DefKey,
    DefinitionIndex, DependencyNode, DependencyTrace, DiagnosticClass, Digest, ElaboratedHeader,
    ElaboratedInterface, EscapeFlow, FixityTable, GenericArgument, InputError, InstanceGraph,
    InstanceKey, InstanceLimits, InstanceRoot, MirFunction, MirInstance, MirInstruction,
    MirLowering, MirProgram, ModuleGraph, ParsedHeader, PlaceFlow, PublicationGuard,
    RequestSession, RetentionReport, RevisionError, RevisionId, Severity, SourceSpan, Span,
    TrustedRuntimeManifest, Type, TypedBody, UseFlow, VerifiedVmProgram, emit_vm_program,
    implementation_method_key, verify_vm_program,
};

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

    fn source(code: &'static str, message: impl Into<String>, span: Option<Span>) -> Self {
        Self::new(code, message, DiagnosticClass::Source, span)
    }

    fn request(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Request, None)
    }

    fn invariant(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Invariant, None)
    }

    fn verification(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Verification, None)
    }

    fn input_corruption(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::InputCorruption, None)
    }

    fn resource(code: &'static str, message: impl Into<String>) -> Self {
        Self::new(code, message, DiagnosticClass::Resource, None)
    }

    fn cancellation(code: &'static str, message: impl Into<String>) -> Self {
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

    fn canonicalize_provenance(&mut self) {
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
#[derive(Debug)]
pub struct CompilationOutcome {
    pub diagnostics: Vec<CompileDiagnostic>,
    pub artifact: Option<VerifiedVmProgram>,
    pub runtime_manifest: Option<TrustedRuntimeManifest>,
    /// Present only for `CompilationMode::Bootstrap`; this is the canonical
    /// evidence a host bootstrap driver persists and compares.
    pub bootstrap_manifest: Option<BootstrapManifest>,
    /// Deterministic executable-instance discovery evidence.
    pub instance_graph: Option<InstanceGraph>,
}
#[derive(Debug)]
pub enum ServiceError {
    Revision(RevisionError),
    SessionConsumed(RevisionId),
    Cancelled,
    Resource(BudgetError),
    Failed(Vec<CompileDiagnostic>),
}

impl ServiceError {
    /// Return every failure through the same structured diagnostic boundary
    /// used for ordinary compilation errors.  Request and revision failures
    /// happen before a stable source world exists, so they deliberately have
    /// no source span or input fingerprint; callers must not scrape a Rust
    /// `Debug` representation to learn why a request was rejected.
    pub fn diagnostics(&self) -> Vec<CompileDiagnostic> {
        match self {
            Self::Failed(diagnostics) => diagnostics.clone(),
            Self::Revision(RevisionError::Input(error)) => {
                vec![CompileDiagnostic::from_input_error(error)]
            }
            Self::Revision(RevisionError::UnknownRevision(_)) => {
                vec![CompileDiagnostic::request(
                    "G7025",
                    "requested compilation revision is unavailable",
                )]
            }
            Self::Revision(RevisionError::StaleRevision(_)) => {
                vec![CompileDiagnostic::request(
                    "G7026",
                    "requested compilation revision belongs to a different compiler database",
                )]
            }
            Self::Revision(RevisionError::RetiredRevision(_)) => {
                vec![CompileDiagnostic::request(
                    "G7027",
                    "requested compilation revision has been retired",
                )]
            }
            Self::SessionConsumed(_) => vec![CompileDiagnostic::request(
                "G7034",
                "compilation request session has already finished",
            )],
            Self::Cancelled => vec![CompileDiagnostic::cancellation(
                "G7029",
                "compilation request was cancelled before publication",
            )],
            Self::Resource(BudgetError { name, ceiling, .. }) => vec![CompileDiagnostic::resource(
                "G7030",
                format!("compilation request exceeded `{name}` resource limit of {ceiling}"),
            )],
        }
    }
}

impl CompileDiagnostic {
    fn from_input_error(error: &InputError) -> Self {
        let (code, class) = match error {
            InputError::EmptySources => ("G7015", DiagnosticClass::Request),
            InputError::DuplicateFileKey(_) => ("G7016", DiagnosticClass::Request),
            InputError::DigestMismatch { .. } => ("G7017", DiagnosticClass::InputCorruption),
            InputError::SourceIdentityMismatch { .. } => {
                ("G7017", DiagnosticClass::InputCorruption)
            }
            InputError::InvalidUtf8(_) => ("G7018", DiagnosticClass::InputCorruption),
            InputError::InvalidLogicalPath(_) => ("G7019", DiagnosticClass::Request),
            InputError::DuplicateCapability(_) => ("G7020", DiagnosticClass::Request),
            InputError::InvalidCapability(_) => ("G7021", DiagnosticClass::Request),
            InputError::InvalidRuntimeManifest => ("G7022", DiagnosticClass::Request),
            InputError::InvalidBootstrapStage { .. } => ("G7023", DiagnosticClass::Request),
            InputError::BootstrapSourceLimit { .. } => ("G7024", DiagnosticClass::Resource),
        };
        Self::new(code, error.to_string(), class, None)
    }
}
impl From<RevisionError> for ServiceError {
    fn from(value: RevisionError) -> Self {
        Self::Revision(value)
    }
}

impl From<RequestControlError> for ServiceError {
    fn from(value: RequestControlError) -> Self {
        match value {
            RequestControlError::Cancelled => Self::Cancelled,
            RequestControlError::Resource(error) => Self::Resource(error),
        }
    }
}

#[derive(Debug, Default)]
pub struct StageZeroCompiler {
    database: CompilerDatabase,
    instance_limits: InstanceLimits,
}
impl StageZeroCompiler {
    pub fn new() -> Self {
        Self::default()
    }

    /// Construct a compiler with an explicit bound for demand-driven
    /// executable-instance discovery. This is a host resource policy, not a
    /// semantic option: it may reject an otherwise-valid request, but cannot
    /// change the identity of an admitted instance.
    pub fn with_instance_limits(instance_limits: InstanceLimits) -> Self {
        Self {
            database: CompilerDatabase::default(),
            instance_limits,
        }
    }

    /// Report validated frozen-interface reuse accumulated by this compiler
    /// database. This is deliberately cache accounting rather than an output
    /// cache API: callers still compile an exact immutable revision.
    pub fn interface_cache_stats(&self) -> crate::InterfaceCacheStats {
        self.database.interface_cache_stats()
    }

    /// Register a revision-qualified query cache for the same safe-point
    /// reclamation policy as compiler-owned products. The registration is
    /// weak: the host continues to own the query engine's lifetime.
    pub fn register_revision_cache<C: crate::RevisionCache + 'static>(&self, cache: &Arc<C>) {
        self.database.register_revision_cache(cache);
    }

    /// Return the published red/green explanation for one typed compiler
    /// product. This is inspection only; it never opens a revision or starts
    /// a new compilation request.
    pub fn dependency_trace(
        &self,
        revision: RevisionId,
        node: &DependencyNode,
    ) -> Option<DependencyTrace> {
        self.database.dependency_trace(revision, node)
    }

    pub fn dependency_traces(&self, revision: RevisionId) -> Vec<DependencyTrace> {
        self.database.dependency_traces(revision)
    }
    pub fn compile(&self, request: CompilationRequest) -> Result<CompilationOutcome, ServiceError> {
        self.compile_with_parent(request, None)
    }

    /// Import one immutable request world into this compiler's database. The
    /// caller may explicitly link it to the revision it supersedes; this is
    /// the only way incremental clients establish a parent/child relation.
    pub fn import_revision(
        &self,
        request: CompilationRequest,
        parent: Option<RevisionId>,
    ) -> Result<RevisionId, ServiceError> {
        Ok(self.database.import(request, parent)?)
    }

    /// Admit a request-scoped session pinned to one active revision. The
    /// session is the only public way to keep a long-lived service request
    /// alive across subsequent editor/build imports.
    pub fn open_session(&self, revision: RevisionId) -> Result<RequestSession, ServiceError> {
        Ok(self.database.open_session(revision)?)
    }

    /// Admit a request with explicit host operational controls. They bound or
    /// cancel work through this session but never select a different semantic
    /// world than the pinned revision.
    pub fn open_session_with_controls(
        &self,
        revision: RevisionId,
        cancellation: CancellationToken,
        budget: Arc<Budget>,
    ) -> Result<RequestSession, ServiceError> {
        Ok(self
            .database
            .open_session_with_controls(revision, cancellation, budget)?)
    }

    /// Retire a world from new request admission. Existing sessions stay
    /// valid until their owners release them and a safe-point collection run
    /// observes no remaining pins.
    pub fn retire_revision(&self, revision: RevisionId) -> Result<(), ServiceError> {
        Ok(self.database.retire_revision(revision)?)
    }

    pub fn collect_retired(&self) -> RetentionReport {
        self.database.collect_retired()
    }

    /// Compile a newly imported child revision. This is the command-style
    /// convenience path; editors and long-lived hosts may import first and
    /// call [`Self::compile_revision`] later against the exact pinned world.
    pub fn compile_with_parent(
        &self,
        request: CompilationRequest,
        parent: Option<RevisionId>,
    ) -> Result<CompilationOutcome, ServiceError> {
        let revision = self.import_revision(request, parent)?;
        self.compile_revision(revision)
    }

    /// Compile exactly one already-imported immutable revision. No source,
    /// dependency, option, or parent state is read through ambient process
    /// state after this boundary.
    pub fn compile_revision(
        &self,
        revision: RevisionId,
    ) -> Result<CompilationOutcome, ServiceError> {
        let session = self.open_session(revision)?;
        self.compile_session(&session)
    }

    /// Compile through a previously admitted request session. This validates
    /// database ownership but intentionally permits a retired revision: a
    /// request that already pinned its world must never switch to a newer
    /// world or fail merely because the host retired it mid-request.
    pub fn compile_session(
        &self,
        session: &RequestSession,
    ) -> Result<CompilationOutcome, ServiceError> {
        self.database.validate_session(session)?;
        if !session.claim_execution() {
            return Err(ServiceError::SessionConsumed(session.revision()));
        }
        // Every structural checkpoint consumes work from this request. A
        // failed or cancelled transaction still keeps its spent-work record,
        // so callers cannot turn one budget into an unbounded retry loop.
        session.checkpoint(1)?;
        let mut interfaces = self.database.interface_cache().transaction();
        let mut dependencies = self
            .database
            .dependency_ledger()
            .transaction(session.revision(), session.snapshot().parent());
        let outcome = self.compile_snapshot(
            session.snapshot(),
            session,
            &mut interfaces,
            &mut dependencies,
        )?;
        // One final cancellation check linearizes request publication. Before
        // it succeeds, dropping the outcome and transaction publishes neither
        // an artifact nor newly collected frozen interfaces.
        let outcome = PublicationGuard::stage(outcome)
            .commit(session.cancellation())
            .map_err(|_| ServiceError::Cancelled)?;
        interfaces.commit();
        dependencies.commit();
        Ok(outcome)
    }

    fn compile_snapshot(
        &self,
        snapshot: &DatabaseSnapshot,
        session: &RequestSession,
        interfaces: &mut crate::interface::InterfaceCacheTransaction<'_>,
        dependencies: &mut crate::dependency::DependencyTransaction<'_>,
    ) -> Result<CompilationOutcome, ServiceError> {
        session.checkpoint(1)?;
        let input_fingerprint = snapshot.world().fingerprint;
        let source_lengths = snapshot
            .world()
            .sources
            .iter()
            .map(|source| {
                (
                    source.key,
                    u32::try_from(source.bytes.len())
                        .expect("normalized world source length fits in a source span"),
                )
            })
            .collect::<BTreeMap<_, _>>();
        for source in snapshot.world().sources.iter() {
            session.checkpoint(1)?;
            dependencies.record(DependencyNode::Input(source.key), source.digest, vec![]);
        }
        // Every supplied package contributes a separately rooted frozen
        // interface graph.  The root package alone supplies the executable
        // entrypoint, but dependency package interfaces must be present while
        // resolving imports, coherence, and cross-package callable bodies.
        // Building only the root graph silently turned supplied dependency
        // sources into ambient ignored bytes.
        let mut packages = snapshot
            .world()
            .sources
            .iter()
            .map(|source| source.package.clone())
            .collect::<BTreeSet<_>>();
        packages.insert(snapshot.world().root_package.clone());
        let mut graphs = BTreeMap::new();
        for package in packages {
            let graph = ModuleGraph::build_with_interface_transaction(
                snapshot.world(),
                &package,
                interfaces,
            );
            graphs.insert(package, graph);
        }
        session.checkpoint(1)?;
        let mut diagnostics = graphs
            .values()
            .flat_map(|graph| graph.diagnostics.iter())
            .map(|diagnostic| {
                CompileDiagnostic::source(
                    diagnostic.code,
                    diagnostic.message.clone(),
                    diagnostic.span,
                )
            })
            .collect::<Vec<_>>();
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            session.checkpoint(1)?;
            diagnostics.extend(node.interface.diagnostics.iter().map(|diagnostic| {
                CompileDiagnostic::source(
                    diagnostic.code,
                    diagnostic.message.clone(),
                    Some(diagnostic.span),
                )
            }));
        }
        let index = DefinitionIndex::from_interfaces(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| &node.interface.interface),
        );
        // Local collection cannot know the transitive public surface of a
        // module alias or glob until every interface in the module graph has
        // been frozen. Seal that surface before publishing dependency facts:
        // a public member added behind `pub use api::*` must invalidate the
        // facade/root interface even though the facade source did not change.
        for graph in graphs.values_mut() {
            for node in graph.modules.values_mut() {
                node.interface.interface.public_fingerprint =
                    index.sealed_public_fingerprint(&node.interface.interface);
            }
        }
        let Some(root) = graphs
            .get(&snapshot.world().root_package)
            .and_then(|graph| graph.modules.get(&graph.root))
        else {
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        };
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            let mut interface_dependencies = vec![DependencyNode::Input(node.file)];
            interface_dependencies.extend(
                index
                    .sealed_public_dependencies(&node.interface.interface)
                    .into_iter()
                    .map(DependencyNode::Interface),
            );
            dependencies.record(
                DependencyNode::Interface(node.key.clone()),
                node.interface.interface.public_fingerprint,
                interface_dependencies,
            );
        }
        diagnostics.extend(index.validate_imports().into_iter().map(|diagnostic| {
            CompileDiagnostic::source(diagnostic.code, diagnostic.message, Some(diagnostic.span))
        }));
        diagnostics.extend(
            index
                .validate_exported_imports()
                .into_iter()
                .map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message,
                        Some(diagnostic.span),
                    )
                }),
        );
        let coherence = CoherenceSet::collect(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| &node.interface.interface),
            &index,
        );
        diagnostics.extend(coherence.diagnostics.iter().map(|coherence_diagnostic| {
            let diagnostic = CompileDiagnostic::source(
                coherence_diagnostic.code,
                coherence_diagnostic.message.clone(),
                Some(coherence_diagnostic.span),
            )
            .with_fact("semantic_phase", "trait coherence");
            match coherence_diagnostic.related_span {
                Some(span) => diagnostic
                    .with_related_location(
                        "conflicting implementation",
                        SourceSpan {
                            file: span.file,
                            start: span.start,
                            end: span.end,
                        },
                    )
                    .with_explanation(
                        "coherence",
                        "the two frozen implementation heads can apply to the same trait goal",
                    ),
                None => diagnostic,
            }
        }));
        let mut signatures = ElaboratedInterface::merge(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| {
                    ElaboratedInterface::elaborate_with_index(&node.interface.interface, &index)
                }),
        );
        diagnostics.extend(signatures.diagnostics.iter().map(|diagnostic| {
            CompileDiagnostic::source(diagnostic.code, diagnostic.message.clone(), None)
        }));
        let runtime_manifest = snapshot
            .world()
            .runtime_manifest
            .as_ref()
            .and_then(|input| {
                match input.bind(
                    graphs
                        .values()
                        .flat_map(|graph| graph.modules.values())
                        .map(|node| node.interface.interface.clone()),
                    &signatures,
                ) {
                    Ok(manifest) => Some(manifest),
                    Err(error) => {
                        diagnostics.push(CompileDiagnostic::request(
                            "G7011",
                            format!("trusted runtime manifest is invalid: {error:?}"),
                        ));
                        None
                    }
                }
            });
        if let Some(manifest) = &runtime_manifest {
            // A materialized bootstrap source may carry a seed-only `{ () }`
            // placeholder where its original source declared `host CAP fn`.
            // Only the trusted manifest can reattach that exact declaration
            // identity to the frozen host ABI boundary.
            signatures
                .host_imports
                .extend(manifest.host_imports.clone());
        }
        // An evaluated top-level `let` has no declared result annotation.
        // Freeze its inferred Core result before ordinary bodies are read, so
        // all later value paths have a deterministic, interface-owned type.
        // Path-only `let target = callable;` declarations are intentionally
        // excluded: those retain the forwarding-alias contract frozen above.
        // Keep the parsed form until the ordinary all-body pass consumes it.
        // The preliminary elaboration cannot be reused: each successful
        // initializer freezes a result type that can affect later bodies.
        // Its body syntax, however, is immutable source-local input and must
        // not be reparsed merely because it crosses this two-phase boundary.
        let mut frozen_value_initializer_syntax = BTreeMap::new();
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            let Some(source) = snapshot
                .world()
                .sources
                .iter()
                .find(|source| source.key == node.file)
            else {
                continue;
            };
            let text =
                std::str::from_utf8(&source.bytes).expect("normalized world only contains UTF-8");
            let lexed = crate::LexedFile::lex(source.key, text);
            let fixities = FixityTable::for_module(&node.interface.interface);
            for declaration in node
                .interface
                .interface
                .definitions
                .iter()
                .filter(|definition| {
                    matches!(
                        definition.syntax.header,
                        ParsedHeader::ValueInitializer { .. }
                    )
                })
            {
                let Some(body_range) = declaration.body else {
                    continue;
                };
                let body = BodySyntax::parse_expression(&lexed, text, body_range);
                frozen_value_initializer_syntax.insert(declaration.key, body.clone());
                if !body.diagnostics.is_empty() || body.recovered {
                    continue;
                }
                let core = TypedBody::elaborate_value_initializer(
                    declaration,
                    &body,
                    &index,
                    &signatures,
                    &fixities,
                );
                if core.diagnostics.is_empty() && !core.recovered {
                    let (generic_kinds, ty) = core.value_initializer_type();
                    signatures.freeze_value_initializer(declaration.key, generic_kinds, ty);
                }
            }
        }
        // Host declarations are source-visible only when their exact frozen
        // capability is present in this request world.  This check happens
        // before bodies/Core are produced, so an unauthorized import can
        // never enter an artifact or be recovered as an ordinary function.
        for (definition, import) in &signatures.host_imports {
            if !snapshot
                .world()
                .capability_manifest
                .iter()
                .any(|grant| grant == &import.capability)
            {
                let span = graphs
                    .values()
                    .flat_map(|graph| graph.modules.values())
                    .flat_map(|node| node.interface.interface.definitions.iter())
                    .find(|candidate| candidate.key == *definition)
                    .map(|candidate| candidate.span);
                diagnostics.push(CompileDiagnostic::source(
                    "G7032",
                    format!(
                        "host import `{}` requires undeclared capability `{}`",
                        import.symbol, import.capability
                    ),
                    span,
                )
                .with_fact("host_symbol", import.symbol.clone())
                .with_fact("required_capability", import.capability.clone())
                .with_explanation(
                    "capability-boundary",
                    "a host import is admitted only when its frozen capability is declared by the request",
                ));
            }
        }
        // The reverse table is the only authority passed to MIR lowering.
        // Source names and package paths intentionally disappear here: a
        // primitive leaf is selected exclusively by the frozen declaration
        // identity produced by manifest binding.
        let runtime_primitives = runtime_manifest.as_ref().map(|manifest| {
            manifest
                .primitives
                .iter()
                .map(|(role, definition)| (*definition, *role))
                .collect::<BTreeMap<_, _>>()
        });
        let Some(entry) = root
            .interface
            .interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("main"))
        else {
            diagnostics.push(CompileDiagnostic::source(
                "G7001",
                "root module has no `main` definition",
                None,
            ));
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        };
        // The VM invokes `main` without arguments and without an ambient
        // source-level effect environment.  Validate that dynamic boundary
        // while the frozen callable signature and the declaration span are
        // both available; otherwise a generic or open-row entry could reach
        // code generation merely because its body happens not to use the
        // unresolved binder.
        match signatures.definitions.get(&entry.key) {
            Some(ElaboratedHeader::Callable(signature)) => {
                if signature.generics != 0 {
                    diagnostics.push(
                        CompileDiagnostic::source(
                            "G7028",
                            "executable entry `main` cannot declare generic binders",
                            Some(entry.span),
                        )
                        .with_fact("entry_rule", "monomorphic")
                        .with_fact("observed_generic_binders", signature.generics.to_string())
                        .with_explanation(
                            "vm-entry-boundary",
                            "the VM invokes `main` without a generic argument environment",
                        ),
                    );
                }
                if !signature.parameters.is_empty() {
                    diagnostics.push(
                        CompileDiagnostic::source(
                            "G7028",
                            "executable entry `main` must not declare parameters",
                            Some(entry.span),
                        )
                        .with_fact("entry_rule", "zero parameters")
                        .with_fact(
                            "observed_parameters",
                            signature.parameters.len().to_string(),
                        )
                        .with_explanation(
                            "vm-entry-boundary",
                            "the VM invokes `main` without call arguments",
                        ),
                    );
                }
                if !signature.effects.effects.is_empty()
                    || !signature.effects.projections.is_empty()
                    || signature.effects.tail.is_some()
                {
                    diagnostics.push(
                        CompileDiagnostic::source(
                            "G7028",
                            "executable entry `main` must have a closed empty outward effect row",
                            Some(entry.span),
                        )
                        .with_fact("entry_rule", "closed empty outward effect row")
                        .with_fact("observed_effects", format!("{:?}", signature.effects))
                        .with_explanation(
                            "vm-entry-boundary",
                            "the VM entrypoint has no ambient source-level effect handler",
                        ),
                    );
                }
            }
            Some(_) => diagnostics.push(CompileDiagnostic::source(
                "G7028",
                "executable entry `main` must be a callable declaration",
                Some(entry.span),
            )),
            None => diagnostics.push(CompileDiagnostic::invariant(
                "G7028",
                "root entry declaration lost its frozen signature",
            )),
        }
        if !diagnostics.is_empty() {
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        }
        let entry = entry.key;
        let mut functions = BTreeMap::new();
        let mut constants = BTreeSet::new();
        // Bodies are elaborated before any MIR lowering. This keeps every
        // lowering request rooted in one immutable package world and gives
        // static handler specialization read-only access to direct callee
        // Core products without reopening source or consulting host state.
        let mut body_products = Vec::<(DefKey, bool, bool, TypedBody, PlaceFlow)>::new();
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            session.checkpoint(1)?;
            let Some(source) = snapshot
                .world()
                .sources
                .iter()
                .find(|source| source.key == node.file)
            else {
                diagnostics.push(CompileDiagnostic::input_corruption(
                    "G7003",
                    format!(
                        "module `{}` source is absent from request world",
                        node.key.path
                    ),
                ));
                continue;
            };
            let text =
                std::str::from_utf8(&source.bytes).expect("normalized world only contains UTF-8");
            let lexed = crate::LexedFile::lex(source.key, text);
            let fixities = FixityTable::for_module(&node.interface.interface);
            dependencies.record(
                DependencyNode::Fixity(node.key.clone()),
                fixities.fingerprint(),
                vec![DependencyNode::Interface(node.key.clone())],
            );
            for declaration in node
                .interface
                .interface
                .definitions
                .iter()
                .filter(|definition| {
                    (definition.callable_header().is_some()
                        && definition.kind != crate::DeclarationKind::HostImport)
                        || definition.kind == crate::DeclarationKind::Constant
                        || matches!(
                            definition.syntax.header,
                            ParsedHeader::ValueInitializer { .. }
                        )
                })
            {
                session.checkpoint(1)?;
                if runtime_manifest.as_ref().is_some_and(|manifest| {
                    manifest.host_imports.contains_key(&declaration.key)
                        || [
                            crate::PrimitiveRole::Abort,
                            crate::PrimitiveRole::TextByteLen,
                            crate::PrimitiveRole::TextConcat,
                            crate::PrimitiveRole::TextEq,
                            crate::PrimitiveRole::TextFromUtf8Checked,
                            crate::PrimitiveRole::TextAsBytes,
                            crate::PrimitiveRole::CharFromU32Checked,
                            crate::PrimitiveRole::CharToU32,
                            crate::PrimitiveRole::BytesLen,
                            crate::PrimitiveRole::BytesConcat,
                            crate::PrimitiveRole::BytesGet,
                            crate::PrimitiveRole::BytesSlice,
                            crate::PrimitiveRole::BytesFromArrayMove,
                            crate::PrimitiveRole::BytesToArray,
                            crate::PrimitiveRole::BytesUtf8ValidUpTo,
                            crate::PrimitiveRole::ArrayNew,
                            crate::PrimitiveRole::ArrayLen,
                            crate::PrimitiveRole::ArrayGetCopy,
                            crate::PrimitiveRole::ArrayGetMove,
                            crate::PrimitiveRole::ArrayGetBorrowShared,
                            crate::PrimitiveRole::ArrayGetBorrowUnique,
                            crate::PrimitiveRole::ArraySetMove,
                            crate::PrimitiveRole::ArrayEmpty,
                            crate::PrimitiveRole::ArrayPushMove,
                            crate::PrimitiveRole::ArrayPopMove,
                            crate::PrimitiveRole::ArrayCapacity,
                            crate::PrimitiveRole::ArrayReserve,
                            crate::PrimitiveRole::ArrayFinishDrained,
                            crate::PrimitiveRole::U32CheckedAdd,
                            crate::PrimitiveRole::U32CheckedSub,
                            crate::PrimitiveRole::U32CheckedMul,
                            crate::PrimitiveRole::U32CheckedDiv,
                            crate::PrimitiveRole::U32CheckedRem,
                            crate::PrimitiveRole::U32WrappingAdd,
                            crate::PrimitiveRole::U32WrappingSub,
                            crate::PrimitiveRole::U32WrappingMul,
                            crate::PrimitiveRole::U32WrappingShl,
                            crate::PrimitiveRole::U32WrappingShr,
                            crate::PrimitiveRole::U32CheckedShl,
                            crate::PrimitiveRole::U32CheckedShr,
                            crate::PrimitiveRole::U32Eq,
                            crate::PrimitiveRole::U32Lt,
                            crate::PrimitiveRole::U32Le,
                            crate::PrimitiveRole::U32ToUsize,
                            crate::PrimitiveRole::UsizeToU32Checked,
                            crate::PrimitiveRole::IntCheckedAdd,
                            crate::PrimitiveRole::IntWrappingAdd,
                            crate::PrimitiveRole::IntConvertCheckedToI64,
                            crate::PrimitiveRole::IntConvertWrappingToI64,
                            crate::PrimitiveRole::IntConvertCheckedToU32,
                            crate::PrimitiveRole::IntConvertCheckedToUsize,
                            crate::PrimitiveRole::IntConvertCheckedToU8,
                            crate::PrimitiveRole::IntConvertCheckedToU16,
                            crate::PrimitiveRole::IntConvertCheckedToI16,
                            crate::PrimitiveRole::IntConvertCheckedToI32,
                            crate::PrimitiveRole::IntConvertWrappingToI32,
                            crate::PrimitiveRole::IntConvertCheckedToI8,
                            crate::PrimitiveRole::IntConvertWrappingToI8,
                            crate::PrimitiveRole::IntConvertCheckedToU64,
                            crate::PrimitiveRole::IntConvertWrappingToU64,
                            crate::PrimitiveRole::IntConvertCheckedToIsize,
                            crate::PrimitiveRole::IntConvertWrappingToIsize,
                            crate::PrimitiveRole::IntConvertCheckedToU128,
                            crate::PrimitiveRole::IntConvertWrappingToU128,
                            crate::PrimitiveRole::IntConvertCheckedToI128,
                            crate::PrimitiveRole::IntConvertWrappingToI128,
                            crate::PrimitiveRole::IntWrappingSub,
                            crate::PrimitiveRole::IntWrappingMul,
                            crate::PrimitiveRole::IntWrappingNeg,
                            crate::PrimitiveRole::IntEqual,
                            crate::PrimitiveRole::IntLess,
                            crate::PrimitiveRole::IntGreater,
                            crate::PrimitiveRole::IntBitAnd,
                            crate::PrimitiveRole::IntBitOr,
                            crate::PrimitiveRole::IntBitXor,
                            crate::PrimitiveRole::IntBitNot,
                            crate::PrimitiveRole::IntConvertWrappingToU32,
                            crate::PrimitiveRole::IntConvertWrappingToUsize,
                            crate::PrimitiveRole::IntConvertWrappingToU8,
                            crate::PrimitiveRole::IntConvertWrappingToU16,
                            crate::PrimitiveRole::IntConvertWrappingToI16,
                            crate::PrimitiveRole::IntShr,
                            crate::PrimitiveRole::IntShl,
                        ]
                        .iter()
                        .any(|role| manifest.primitives.get(role) == Some(&declaration.key))
                        || manifest.primitives.iter().any(|(role, definition)| {
                            role.is_float() && definition == &declaration.key
                        })
                }) {
                    // This exact manifest-bound runtime leaf has an opaque
                    // source body. Do not parse or elaborate it as `Unit`:
                    // only a bound identity may bypass ordinary source-body
                    // semantics, and calls lower to the sealed VM opcode.
                    continue;
                }
                let Some(body_range) = declaration.body else {
                    diagnostics.push(CompileDiagnostic::source(
                        "G7002",
                        format!(
                            "value `{}` has no body",
                            declaration.name.as_deref().unwrap_or("<anonymous>")
                        ),
                        Some(declaration.span),
                    ));
                    continue;
                };
                let is_constant = declaration.kind == crate::DeclarationKind::Constant
                    || matches!(
                        declaration.syntax.header,
                        ParsedHeader::ValueInitializer { .. }
                    );
                let body = if matches!(
                    declaration.syntax.header,
                    ParsedHeader::ValueInitializer { .. }
                ) {
                    frozen_value_initializer_syntax
                        .remove(&declaration.key)
                        .unwrap_or_else(|| BodySyntax::parse_expression(&lexed, text, body_range))
                } else if is_constant {
                    BodySyntax::parse_expression(&lexed, text, body_range)
                } else {
                    BodySyntax::parse(&lexed, text, body_range)
                };
                dependencies.record(
                    DependencyNode::Body(declaration.key),
                    body_fingerprint(&body),
                    vec![DependencyNode::Input(node.file)],
                );
                diagnostics.extend(body.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message,
                        Some(diagnostic.span),
                    )
                }));
                if body.recovered {
                    diagnostics.push(CompileDiagnostic::source(
                        "G7006",
                        format!(
                            "value `{}` has recovered body syntax and cannot enter a release artifact",
                            declaration.name.as_deref().unwrap_or("<anonymous>")
                        ),
                        Some(declaration.span),
                    ));
                }
                let core = if declaration.kind == crate::DeclarationKind::Constant {
                    TypedBody::elaborate_constant(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                    )
                } else if matches!(
                    declaration.syntax.header,
                    ParsedHeader::ValueInitializer { .. }
                ) {
                    TypedBody::elaborate_value_initializer(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                    )
                } else {
                    TypedBody::elaborate_with_fixities(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                    )
                };
                diagnostics.extend(core.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message.clone(),
                        Some(diagnostic.span),
                    )
                }));
                if core.recovered {
                    diagnostics.push(CompileDiagnostic::source(
                        "G7007",
                        format!(
                            "value `{}` has recovered Typed Core and cannot enter a release artifact",
                            declaration.name.as_deref().unwrap_or("<anonymous>")
                        ),
                        Some(declaration.span),
                    ));
                }
                let mut core_validation = core.validate();
                let ambient_projection_bounds = signatures
                    .definitions
                    .get(&declaration.key)
                    .and_then(|header| match header {
                        ElaboratedHeader::Callable(signature) => {
                            Some(signature.where_bounds.clone())
                        }
                        _ => None,
                    })
                    .unwrap_or_default();
                core_validation.extend(
                    core.validate_projection_obligations(&signatures, &ambient_projection_bounds),
                );
                diagnostics.extend(core_validation.iter().map(|diagnostic| {
                    CompileDiagnostic::invariant(diagnostic.code, diagnostic.message.clone())
                }));
                let flow = PlaceFlow::analyze(&core);
                diagnostics.extend(flow.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message.clone(),
                        Some(diagnostic.span),
                    )
                }));
                let escapes = EscapeFlow::analyze(&core, &flow);
                diagnostics.extend(escapes.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message.clone(),
                        Some(diagnostic.span),
                    )
                }));
                let uses = UseFlow::analyze_with_interface(&core, &flow, &signatures);
                diagnostics.extend(uses.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message.clone(),
                        Some(diagnostic.span),
                    )
                }));
                let valid = flow.diagnostics.is_empty()
                    && escapes.diagnostics.is_empty()
                    && uses.diagnostics.is_empty()
                    && core_validation.is_empty()
                    && core.diagnostics.is_empty()
                    && body.diagnostics.is_empty();
                let mut core_dependencies = graphs
                    .values()
                    .flat_map(|graph| graph.modules.values())
                    .map(|module| DependencyNode::Interface(module.key.clone()))
                    .collect::<Vec<_>>();
                core_dependencies.push(DependencyNode::Body(declaration.key));
                core_dependencies.push(DependencyNode::Fixity(node.key.clone()));
                dependencies.record(
                    DependencyNode::Core(declaration.key),
                    core.semantic_fingerprint(),
                    core_dependencies,
                );
                body_products.push((declaration.key, is_constant, valid, core, flow));
            }
            for implementation in node
                .interface
                .interface
                .definitions
                .iter()
                .filter(|definition| definition.kind == crate::DeclarationKind::Implementation)
            {
                let ParsedHeader::Implementation(implementation_header) =
                    &implementation.syntax.header
                else {
                    continue;
                };
                let Some(ElaboratedHeader::Implementation(implementation_signature)) =
                    signatures.definitions.get(&implementation.key)
                else {
                    diagnostics.push(CompileDiagnostic::invariant(
                        "G7012",
                        "implementation lost its frozen signature before body elaboration",
                    ));
                    continue;
                };
                for method in &implementation_header.methods {
                    let Some(body_range) = method.body else {
                        diagnostics.push(CompileDiagnostic::source(
                            "G7002",
                            format!("implementation method `{}` has no body", method.name),
                            Some(method.span),
                        ));
                        continue;
                    };
                    let Some(method_signature) = implementation_signature.methods.get(&method.name)
                    else {
                        // Header/signature validation has already issued the
                        // source diagnostic for an unknown method. Do not
                        // invent a body contract during recovery.
                        continue;
                    };
                    let body = BodySyntax::parse(&lexed, text, body_range);
                    let method_key = implementation_method_key(implementation.key, &method.name);
                    dependencies.record(
                        DependencyNode::Body(method_key),
                        body_fingerprint(&body),
                        vec![DependencyNode::Input(node.file)],
                    );
                    diagnostics.extend(body.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message,
                            Some(diagnostic.span),
                        )
                    }));
                    if body.recovered {
                        diagnostics.push(CompileDiagnostic::source(
                            "G7006",
                            format!(
                                "implementation method `{}` has recovered body syntax and cannot enter a release artifact",
                                method.name
                            ),
                            Some(method.span),
                        ));
                    }
                    let core = TypedBody::elaborate_implementation_method(
                        implementation,
                        crate::core::ImplementationMethodContext {
                            implementation_header,
                            method,
                            signature: method_signature,
                        },
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                    );
                    diagnostics.extend(core.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    if core.recovered {
                        diagnostics.push(CompileDiagnostic::source(
                            "G7007",
                            format!(
                                "implementation method `{}` has recovered Typed Core and cannot enter a release artifact",
                                method.name
                            ),
                            Some(method.span),
                        ));
                    }
                    let mut core_validation = core.validate();
                    let mut ambient_projection_bounds =
                        implementation_signature.where_bounds.clone();
                    ambient_projection_bounds.push((
                        implementation_signature.self_ty.clone(),
                        implementation_signature.relation.clone(),
                    ));
                    ambient_projection_bounds.extend(method_signature.where_bounds.clone());
                    core_validation.extend(
                        core.validate_projection_obligations(
                            &signatures,
                            &ambient_projection_bounds,
                        ),
                    );
                    diagnostics.extend(core_validation.iter().map(|diagnostic| {
                        CompileDiagnostic::invariant(diagnostic.code, diagnostic.message.clone())
                    }));
                    let flow = PlaceFlow::analyze(&core);
                    diagnostics.extend(flow.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    let escapes = EscapeFlow::analyze(&core, &flow);
                    diagnostics.extend(escapes.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    let uses = UseFlow::analyze_with_interface(&core, &flow, &signatures);
                    diagnostics.extend(uses.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    let valid = flow.diagnostics.is_empty()
                        && escapes.diagnostics.is_empty()
                        && uses.diagnostics.is_empty()
                        && core_validation.is_empty()
                        && core.diagnostics.is_empty()
                        && body.diagnostics.is_empty();
                    let mut core_dependencies = graphs
                        .values()
                        .flat_map(|graph| graph.modules.values())
                        .map(|module| DependencyNode::Interface(module.key.clone()))
                        .collect::<Vec<_>>();
                    core_dependencies.push(DependencyNode::Body(method_key));
                    core_dependencies.push(DependencyNode::Fixity(node.key.clone()));
                    dependencies.record(
                        DependencyNode::Core(method_key),
                        core.semantic_fingerprint(),
                        core_dependencies,
                    );
                    body_products.push((method_key, false, valid, core, flow));
                }
            }
        }
        let typed_bodies = body_products
            .iter()
            .map(|(definition, _, _, core, _)| (*definition, core.clone()))
            .collect::<BTreeMap<_, _>>();
        // Demand-discover the executable spine before lowering.  This is not
        // monomorphization: it records only concrete callable identities and
        // direct callable dependencies, leaving generic substitutions for the
        // later instance materializer.
        let mut instance_graph = InstanceGraph::default();
        let limits = self.instance_limits;
        let entry_kinds = match signatures.definitions.get(&entry) {
            Some(ElaboratedHeader::Callable(signature)) => signature.generic_kinds.clone(),
            _ => Vec::new(),
        };
        let entry_instance = InstanceKey::new(entry, &entry_kinds, vec![]).map_err(|error| {
            failed(
                input_fingerprint,
                vec![CompileDiagnostic::invariant(
                    "G7030",
                    format!("entry instance is not concrete: {error:?}"),
                )],
                &source_lengths,
            )
        })?;
        instance_graph
            .discover_root(
                InstanceRoot {
                    key: entry_instance,
                    reason: "executable entry".into(),
                },
                limits,
            )
            .map_err(|error| {
                failed(
                    input_fingerprint,
                    vec![CompileDiagnostic::resource(
                        "G7031",
                        format!("instance discovery limit: {error:?}"),
                    )],
                    &source_lengths,
                )
            })?;
        while let Some(caller) = instance_graph.pop_pending() {
            let Some(body) = typed_bodies.get(&caller.callable) else {
                continue;
            };
            // A direct call owns its callable child in Core. Process that
            // child through the call below, rather than once as a first-class
            // function value and again as the call's callee. Retaining
            // standalone callable values here is still essential: a value
            // can flow through a closure or aggregate before invocation.
            let direct_callees = body
                .expressions
                .iter()
                .filter_map(|expression| match &expression.kind {
                    crate::core::CoreKind::Call { callee, .. } => Some(*callee),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            for (index, expression) in body.expressions.iter().enumerate() {
                let function = match &expression.kind {
                    crate::core::CoreKind::Function { .. }
                    | crate::core::CoreKind::TraitMethod { .. }
                    | crate::core::CoreKind::Constant { .. }
                        if !direct_callees.contains(&crate::CoreId(index as u32)) =>
                    {
                        Some(&expression.kind)
                    }
                    crate::core::CoreKind::Call { callee, .. } => {
                        Some(&body.expression(*callee).kind)
                    }
                    _ => None,
                };
                let key = match function {
                    Some(crate::core::CoreKind::Function {
                        definition: callee,
                        arguments,
                        ..
                    }) => {
                        let Some(ElaboratedHeader::Callable(signature)) =
                            signatures.definitions.get(callee)
                        else {
                            continue;
                        };
                        InstanceKey::new(
                            *callee,
                            &signature.generic_kinds,
                            arguments
                                .iter()
                                .map(|argument| {
                                    specialize_generic_argument(argument, caller.arguments())
                                })
                                .collect(),
                        )
                    }
                    Some(crate::core::CoreKind::Constant {
                        definition: callee,
                        arguments,
                    }) => {
                        let Some(ElaboratedHeader::ValueInitializer { generic_kinds, .. }) =
                            signatures.definitions.get(callee)
                        else {
                            continue;
                        };
                        InstanceKey::new(
                            *callee,
                            generic_kinds,
                            arguments
                                .iter()
                                .map(|argument| {
                                    specialize_generic_argument(argument, caller.arguments())
                                })
                                .collect(),
                        )
                    }
                    Some(crate::core::CoreKind::TraitMethod {
                        evidence,
                        method,
                        trait_arguments,
                        method_arguments,
                    }) => {
                        let trait_arguments = trait_arguments
                            .iter()
                            .map(|argument| {
                                specialize_generic_argument(argument, caller.arguments())
                            })
                            .collect::<Vec<_>>();
                        let method_arguments = method_arguments
                            .iter()
                            .map(|argument| {
                                specialize_generic_argument(argument, caller.arguments())
                            })
                            .collect::<Vec<_>>();
                        trait_method_instance_key(
                            *evidence,
                            *method,
                            &trait_arguments,
                            &method_arguments,
                        )
                    }
                    _ => continue,
                };
                let key = match key {
                    Ok(key) => key,
                    Err(
                        crate::InstanceKeyError::NonConcreteType { .. }
                        | crate::InstanceKeyError::UnresolvedType { .. }
                        | crate::InstanceKeyError::OpenEffectRow { .. }
                        | crate::InstanceKeyError::NonConcreteLifetime { .. }
                        | crate::InstanceKeyError::NonConcreteConst { .. },
                    ) => continue,
                    Err(error) => {
                        return Err(failed(
                            input_fingerprint,
                            vec![CompileDiagnostic::invariant(
                                "G7030",
                                format!("callable instance is not concrete: {error:?}"),
                            )],
                            &source_lengths,
                        ));
                    }
                };
                instance_graph
                    .discover_callee(&caller, key, limits)
                    .map_err(|error| {
                        failed(
                            input_fingerprint,
                            vec![CompileDiagnostic::resource(
                                "G7031",
                                format!("instance discovery limit: {error:?}"),
                            )],
                            &source_lengths,
                        )
                    })?;
            }
        }
        for instance in instance_graph.ordered() {
            session.checkpoint(1)?;
            let mut instance_dependencies = vec![
                DependencyNode::Core(instance.callable),
                DependencyNode::Body(instance.callable),
            ];
            if let Some(callees) = instance_graph.callees(&instance) {
                instance_dependencies.extend(callees.iter().cloned().map(DependencyNode::Instance));
            }
            dependencies.record(
                DependencyNode::Instance(instance.clone()),
                instance.fingerprint(),
                instance_dependencies,
            );
        }
        for (definition, is_constant, valid, core, flow) in body_products {
            session.checkpoint(1)?;
            if !valid {
                continue;
            }
            let lowered = MirLowering::lower_with_bodies_signatures_and_primitives(
                definition,
                &core,
                &flow,
                &typed_bodies,
                Some(&signatures),
                runtime_primitives.as_ref(),
            );
            diagnostics.extend(lowered.diagnostics.into_iter().map(|diagnostic| {
                CompileDiagnostic::invariant(diagnostic.code, diagnostic.message)
            }));
            if let Some(mir) = lowered.function {
                let mir = match crate::mir::optimize(mir) {
                    Ok((mir, _)) => mir,
                    Err(message) => {
                        diagnostics.push(CompileDiagnostic::invariant(
                            "G7010",
                            format!("MIR optimization rejected function: {message}"),
                        ));
                        continue;
                    }
                };
                if is_constant {
                    constants.insert(definition);
                }
                dependencies.record(
                    DependencyNode::Mir(definition),
                    mir_fingerprint(&mir),
                    vec![DependencyNode::Core(definition)],
                );
                functions.insert(definition, mir);
                for (lifted_definition, lifted) in lowered.lifted {
                    let lifted = match crate::mir::optimize(lifted) {
                        Ok((mir, _)) => mir,
                        Err(message) => {
                            diagnostics.push(CompileDiagnostic::invariant(
                                "G7010",
                                format!("MIR optimization rejected lifted callable: {message}"),
                            ));
                            continue;
                        }
                    };
                    if functions.insert(lifted_definition, lifted).is_some() {
                        diagnostics.push(CompileDiagnostic::invariant(
                            "G7009",
                            "lifted callable identity collided with another function",
                        ));
                    } else {
                        let lifted = functions
                            .get(&lifted_definition)
                            .expect("lifted function was inserted");
                        dependencies.record(
                            DependencyNode::Mir(lifted_definition),
                            mir_fingerprint(lifted),
                            vec![DependencyNode::Core(definition)],
                        );
                    }
                }
            }
        }
        let instances = match materialize_concrete_instances(
            &mut functions,
            &instance_graph,
            &signatures,
            runtime_primitives.as_ref(),
        ) {
            Ok(instances) => instances,
            Err(message) => {
                diagnostics.push(CompileDiagnostic::invariant("G7032", message));
                BTreeMap::new()
            }
        };
        if !diagnostics.is_empty() {
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        }
        if let Some(cycle) = constant_cycle(&functions, &constants) {
            return Err(failed(
                input_fingerprint,
                vec![CompileDiagnostic::source(
                    "G7008",
                    format!("constant initializer cycle: {cycle:?}"),
                    None,
                )],
                &source_lengths,
            ));
        }
        // A mode changes the requested product, never the source semantics.
        // Check/inspection/IDE requests may consume exactly the same frontend
        // and MIR facts as a build, but must not accidentally publish an
        // executable artifact merely because a caller asked a shallower root.
        let demands_artifact = matches!(
            snapshot.world().mode,
            CompilationMode::Build | CompilationMode::Test | CompilationMode::Bootstrap(_)
        );
        if !demands_artifact {
            session.checkpoint(1)?;
            return Ok(CompilationOutcome {
                diagnostics,
                artifact: None,
                runtime_manifest,
                bootstrap_manifest: None,
                instance_graph: Some(instance_graph),
            });
        }
        let linked_functions = reachable_functions(&functions, entry);
        let linked_instances = instances
            .into_iter()
            .filter(|(executable, _)| linked_functions.contains_key(executable))
            .collect();
        let program = MirProgram {
            entry,
            functions: linked_functions,
            instances: linked_instances,
        };
        session.checkpoint(
            u64::try_from(program.functions.len())
                .expect("reachable function count fits in request work budget")
                .saturating_add(1),
        )?;
        let mut candidate = emit_vm_program(&program).map_err(|error| {
            failed(
                input_fingerprint,
                vec![CompileDiagnostic::invariant(
                    "G7004",
                    format!("VM emission rejected MIR: {error:?}"),
                )],
                &source_lengths,
            )
        })?;
        // Emission derives the declaration list from actual HostCall edges,
        // not the request's broader grant set.  Recheck the subset at the
        // artifact boundary so a future MIR producer cannot smuggle a host
        // instruction past the source authorization pass above.
        if let Some(capability) = candidate.host_capabilities.iter().find(|capability| {
            !snapshot
                .world()
                .capability_manifest
                .iter()
                .any(|grant| grant == *capability)
        }) {
            return Err(failed(
                input_fingerprint,
                vec![CompileDiagnostic::verification(
                    "G7033",
                    format!(
                        "emitted host capability `{capability}` is not granted by the request manifest"
                    ),
                )],
                &source_lengths,
            ));
        }
        if let Some(manifest) = &runtime_manifest {
            candidate.runtime_manifest = Some(manifest.digest);
            candidate.fingerprint = candidate.computed_fingerprint();
        }
        let artifact = verify_vm_program(candidate).map_err(|error| {
            failed(
                input_fingerprint,
                vec![CompileDiagnostic::verification(
                    "G7005",
                    format!("VM verification rejected emitted artifact: {error:?}"),
                )],
                &source_lengths,
            )
        })?;
        dependencies.record(
            DependencyNode::Artifact(snapshot.world().root_package.clone()),
            artifact.fingerprint(),
            program
                .functions
                .keys()
                .copied()
                .map(DependencyNode::Mir)
                .collect(),
        );
        session.checkpoint(1)?;
        let bootstrap_manifest = match &snapshot.world().mode {
            CompilationMode::Bootstrap(stage) => {
                if let Some(expected) = stage.expected_artifact
                    && expected != artifact.fingerprint()
                {
                    return Err(failed(
                        input_fingerprint,
                        vec![CompileDiagnostic::request(
                            "G7012",
                            format!(
                                "bootstrap stage {} did not converge: expected artifact {expected}, got {}",
                                stage.ordinal,
                                artifact.fingerprint(),
                            ),
                        )],
                        &source_lengths,
                    ));
                }
                Some(BootstrapManifest::from_verified_program(
                    snapshot.world(),
                    stage.clone(),
                    &artifact,
                ))
            }
            _ => None,
        };
        Ok(CompilationOutcome {
            diagnostics,
            artifact: Some(artifact),
            runtime_manifest,
            bootstrap_manifest,
            instance_graph: Some(instance_graph),
        })
    }
}

/// Materialize concrete direct-call instances into their own MIR products.
/// The executable key is derived from the canonical `InstanceKey` digest, so
/// `identity<i64>` and `identity<Text>` cannot alias merely because they
/// share one source declaration key.
fn materialize_concrete_instances(
    functions: &mut BTreeMap<DefKey, MirFunction>,
    graph: &InstanceGraph,
    signatures: &ElaboratedInterface,
    runtime_primitives: Option<&BTreeMap<DefKey, crate::PrimitiveRole>>,
) -> Result<BTreeMap<DefKey, MirInstance>, String> {
    let mut instances = BTreeMap::new();
    let mut targets = BTreeMap::new();
    for key in graph.ordered().into_iter().filter(|key| {
        !key.arguments().is_empty()
                // Generic runtime leaves lower directly from frozen call
                // sites. Their source bodies are opaque and must never be
                // requested as ordinary materialized callable instances.
                && !runtime_primitives
                    .is_some_and(|primitives| primitives.contains_key(&key.callable))
                // A manifest-bound host declaration has no source body to
                // specialize. Direct calls lower through its frozen Host ABI
                // identity instead.
                && !signatures.host_imports.contains_key(&key.callable)
    }) {
        let executable = DefKey(key.fingerprint());
        if functions.contains_key(&executable) {
            return Err(
                "specialized instance identity collided with an existing MIR function".into(),
            );
        }
        let base = functions
            .get(&key.callable)
            .cloned()
            .ok_or_else(|| format!("instance body is unavailable for {:?}", key.callable))?;
        let mut specialized = base;
        specialized.definition = executable;
        specialize_mir_local_types(&mut specialized, key.arguments());
        materialize_deferred_scalar_operations(&mut specialized)?;
        register_specialized_nominal_copy_descriptors(&mut specialized, signatures);
        targets.insert(key.clone(), executable);
        instances.insert(executable, MirInstance { key, executable });
        functions.insert(executable, specialized);
    }
    for function in functions.values_mut() {
        for block in &mut function.blocks {
            for instruction in &mut block.instructions {
                let (callee, generic_arguments, trait_instance) = match instruction {
                    crate::MirInstruction::Call {
                        callee,
                        generic_arguments,
                        trait_instance,
                        ..
                    }
                    | crate::MirInstruction::MakeCallable {
                        callee,
                        generic_arguments,
                        trait_instance,
                        ..
                    } => (callee, generic_arguments, trait_instance),
                    _ => continue,
                };
                if trait_instance.is_some() {
                    let key = {
                        let trait_instance = trait_instance
                            .as_ref()
                            .expect("trait method identity was checked");
                        trait_method_instance_key(
                            trait_instance.evidence,
                            *callee,
                            &trait_instance.trait_arguments,
                            &trait_instance.method_arguments,
                        )
                    };
                    let key = match key {
                        Ok(key) => key,
                        Err(
                            crate::InstanceKeyError::NonConcreteType { .. }
                            | crate::InstanceKeyError::UnresolvedType { .. }
                            | crate::InstanceKeyError::OpenEffectRow { .. }
                            | crate::InstanceKeyError::NonConcreteLifetime { .. }
                            | crate::InstanceKeyError::NonConcreteConst { .. },
                        ) => {
                            // Source generic templates are retained for
                            // diagnostics and only their concrete clones are
                            // executable. Their solver-selected callee is
                            // still valid, but no executable instance exists
                            // until an outer materialization closes the
                            // binders.
                            *trait_instance = None;
                            continue;
                        }
                        Err(error) => {
                            return Err(format!(
                                "trait method instance is not executable: {error:?}"
                            ));
                        }
                    };
                    *callee = *targets.get(&key).ok_or_else(|| {
                        format!("selected trait-method instance was not materialized: {key:?}")
                    })?;
                    generic_arguments.clear();
                    *trait_instance = None;
                    continue;
                }
                if generic_arguments.is_empty() {
                    continue;
                }
                let generic_kinds = match signatures.definitions.get(callee) {
                    Some(ElaboratedHeader::Callable(signature)) => &signature.generic_kinds,
                    Some(ElaboratedHeader::ValueInitializer { generic_kinds, .. }) => generic_kinds,
                    _ => {
                        return Err(format!(
                            "generic direct call has no callable signature for {callee:?}"
                        ));
                    }
                };
                let key = match InstanceKey::new(*callee, generic_kinds, generic_arguments.clone())
                {
                    Ok(key) => key,
                    Err(
                        crate::InstanceKeyError::NonConcreteType { .. }
                        | crate::InstanceKeyError::UnresolvedType { .. }
                        | crate::InstanceKeyError::OpenEffectRow { .. }
                        | crate::InstanceKeyError::NonConcreteLifetime { .. }
                        | crate::InstanceKeyError::NonConcreteConst { .. },
                    ) => {
                        // Generic templates keep the existing VM-generic
                        // call path until an outer concrete instance fixes
                        // their binders. This increment materializes only
                        // closed direct-call substitutions.
                        generic_arguments.clear();
                        continue;
                    }
                    Err(error) => {
                        return Err(format!("direct-call instance is not executable: {error:?}"));
                    }
                };
                let Some(target) = targets.get(&key) else {
                    // This instruction belongs to an otherwise unreachable
                    // source body. Instance discovery deliberately starts at
                    // the executable entry, so no specialized target exists
                    // (and none may enter the linked program). Erase the
                    // template substitution; if the body becomes reachable,
                    // discovery will materialize the same key first.
                    generic_arguments.clear();
                    continue;
                };
                *callee = *target;
                generic_arguments.clear();
            }
        }
    }
    Ok(instances)
}

/// Rewrite scalar operations whose source templates deliberately retain a
/// generic type parameter until instance materialization.  Runtime primitive
/// declarations are sealed and cannot themselves be materialized; ordinary
/// source wrappers therefore carry this deferred operation through Typed Core
/// and MIR until their enclosing instance fixes the local register types.
fn materialize_deferred_scalar_operations(function: &mut MirFunction) -> Result<(), String> {
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            let MirInstruction::BitAndGeneric { dst, left, right } = instruction else {
                continue;
            };
            let scalar = function
                .locals
                .get(dst.0 as usize)
                .map(|local| local.ty.clone())
                .ok_or_else(|| "deferred bitwise-and destination is not a MIR local".to_owned())?;
            *instruction = match scalar {
                Type::Scalar(crate::ScalarType::I64) => MirInstruction::BitAndI64 {
                    dst: *dst,
                    left: *left,
                    right: *right,
                },
                Type::Scalar(crate::ScalarType::U32) => MirInstruction::BitAndU32 {
                    dst: *dst,
                    left: *left,
                    right: *right,
                },
                Type::Scalar(crate::ScalarType::U64) => MirInstruction::BitAndU64 {
                    dst: *dst,
                    left: *left,
                    right: *right,
                },
                other => {
                    return Err(format!(
                        "generic int bitwise-and instance has unsupported scalar result {other:?}"
                    ));
                }
            };
        }
    }
    Ok(())
}

/// Canonicalize a solver-selected trait method into the shared instance-key
/// vocabulary. Trait and method arguments remain ordered type slots; the
/// evidence digest is appended as eight const slots so distinct coherent
/// implementations can never share an executable body.
fn trait_method_instance_key(
    evidence: DefKey,
    method: DefKey,
    trait_arguments: &[GenericArgument],
    method_arguments: &[GenericArgument],
) -> Result<InstanceKey, crate::InstanceKeyError> {
    let mut arguments = trait_arguments.to_vec();
    arguments.extend_from_slice(method_arguments);
    let mut kinds = arguments
        .iter()
        .map(instance_argument_kind)
        .collect::<Vec<_>>();
    for bytes in evidence.0.as_bytes().chunks_exact(4) {
        arguments.push(GenericArgument::ConstU32(u32::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3],
        ])));
        kinds.push(crate::GenericKind::Const(crate::ConstKind::U32));
    }
    InstanceKey::new(method, &kinds, arguments)
}

fn instance_argument_kind(argument: &GenericArgument) -> crate::GenericKind {
    match argument {
        GenericArgument::Type(_) => crate::GenericKind::Type,
        GenericArgument::EffectRow(_) => crate::GenericKind::EffectRow,
        GenericArgument::Lifetime(_) => crate::GenericKind::Lifetime,
        GenericArgument::ConstU32(_) => crate::GenericKind::Const(crate::ConstKind::U32),
        GenericArgument::ConstU32Expr(_) => crate::GenericKind::Const(crate::ConstKind::U32),
        GenericArgument::ConstQuantity(_) => crate::GenericKind::Const(crate::ConstKind::Quantity),
        GenericArgument::ConstGeneric { kind, .. } => crate::GenericKind::Const(*kind),
        GenericArgument::ConstInfer { kind, .. } => crate::GenericKind::Const(*kind),
        GenericArgument::ConstProjection { kind, .. } => crate::GenericKind::Const(*kind),
    }
}

/// Stage 0's first materializer specializes every local signature.  The
/// general instruction-type substitution follows in the same product
/// boundary; direct scalar calls already obtain fully concrete VM registers.
fn specialize_mir_local_types(function: &mut MirFunction, arguments: &[GenericArgument]) {
    for local in &mut function.locals {
        local.ty = specialize_type(&local.ty, arguments);
    }
    function.result = specialize_type(&function.result, arguments);
    for descriptor in &mut function.nominal_copy_descriptors {
        descriptor.arguments = descriptor
            .arguments
            .iter()
            .map(|argument| specialize_generic_argument(argument, arguments))
            .collect();
        for variant in &mut descriptor.variants {
            *variant = variant
                .iter()
                .map(|field| specialize_type(field, arguments))
                .collect();
        }
    }
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            match instruction {
                crate::MirInstruction::MakeArray { element_type, .. }
                | crate::MirInstruction::ProjectArray { element_type, .. } => {
                    *element_type = specialize_type(element_type, arguments);
                }
                crate::MirInstruction::MakeRecord { field_types, .. }
                | crate::MirInstruction::MakeEnum { field_types, .. } => {
                    *field_types = field_types
                        .iter()
                        .map(|field| specialize_type(field, arguments))
                        .collect();
                }
                crate::MirInstruction::ProjectRecord { field_type, .. }
                | crate::MirInstruction::ProjectTuple { field_type, .. }
                | crate::MirInstruction::UpdateRecord { field_type, .. } => {
                    *field_type = specialize_type(field_type, arguments);
                }
                crate::MirInstruction::PatternTest { pattern, .. } => {
                    specialize_mir_pattern(pattern, arguments);
                }
                crate::MirInstruction::Perform {
                    effect_arguments, ..
                } => {
                    *effect_arguments = effect_arguments
                        .iter()
                        .map(|argument| specialize_generic_argument(argument, arguments))
                        .collect();
                }
                crate::MirInstruction::InstallHandler {
                    effect_arguments,
                    resume_type,
                    ..
                } => {
                    *effect_arguments = effect_arguments
                        .iter()
                        .map(|argument| specialize_generic_argument(argument, arguments))
                        .collect();
                    *resume_type = specialize_type(resume_type, arguments);
                }
                crate::MirInstruction::HostCall {
                    parameters, result, ..
                } => {
                    *parameters = parameters
                        .iter()
                        .map(|parameter| specialize_type(parameter, arguments))
                        .collect();
                    *result = specialize_type(result, arguments);
                }
                crate::MirInstruction::MakeCallable {
                    environment: Some(environment),
                    ..
                } => {
                    for capture in &mut environment.captures {
                        capture.ty = specialize_type(&capture.ty, arguments);
                    }
                }
                _ => {}
            }
            let (generic_arguments, trait_instance) = match instruction {
                crate::MirInstruction::Call {
                    generic_arguments,
                    trait_instance,
                    ..
                }
                | crate::MirInstruction::MakeCallable {
                    generic_arguments,
                    trait_instance,
                    ..
                } => (generic_arguments, trait_instance),
                _ => continue,
            };
            *generic_arguments = generic_arguments
                .iter()
                .map(|argument| specialize_generic_argument(argument, arguments))
                .collect();
            if let Some(instance) = trait_instance {
                instance.trait_arguments = instance
                    .trait_arguments
                    .iter()
                    .map(|argument| specialize_generic_argument(argument, arguments))
                    .collect();
                instance.method_arguments = instance
                    .method_arguments
                    .iter()
                    .map(|argument| specialize_generic_argument(argument, arguments))
                    .collect();
            }
        }
    }
}

/// A template can contain a `T` local whose concrete nominal layout becomes
/// knowable only while materializing an instance. Re-freeze that layout before
/// the specialized MIR reaches VM emission.
fn register_specialized_nominal_copy_descriptors(
    function: &mut MirFunction,
    signatures: &ElaboratedInterface,
) {
    let roots = function
        .locals
        .iter()
        .map(|local| local.ty.clone())
        .chain(std::iter::once(function.result.clone()))
        .collect::<Vec<_>>();
    let mut building = vec![];
    for root in roots {
        register_specialized_nominal_copy_type(&root, function, signatures, &mut building);
    }
}

fn register_specialized_nominal_copy_type(
    value: &Type,
    function: &mut MirFunction,
    signatures: &ElaboratedInterface,
    building: &mut Vec<(DefKey, Vec<GenericArgument>)>,
) {
    match value {
        Type::Tuple(fields) => {
            for field in fields {
                register_specialized_nominal_copy_type(field, function, signatures, building);
            }
        }
        Type::Array(element) => {
            register_specialized_nominal_copy_type(element, function, signatures, building)
        }
        Type::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                register_specialized_nominal_copy_type(parameter, function, signatures, building);
            }
            register_specialized_nominal_copy_type(result, function, signatures, building);
        }
        Type::Nominal {
            definition,
            arguments,
        } => {
            let key = (*definition, arguments.clone());
            if function.nominal_copy_descriptors.iter().any(|descriptor| {
                descriptor.definition == *definition && descriptor.arguments == *arguments
            }) || building.contains(&key)
            {
                return;
            }
            let variants = match signatures.definitions.get(definition) {
                Some(ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Struct(_),
                    ..
                }) => signatures
                    .instantiate_struct_fields_generic(*definition, arguments)
                    .ok()
                    .map(|fields| vec![fields.into_iter().map(|field| field.ty).collect()]),
                Some(ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                    ..
                }) => variants
                    .iter()
                    .enumerate()
                    .map(|(index, _)| {
                        signatures
                            .instantiate_enum_fields_generic(*definition, arguments, index as u32)
                            .ok()
                            .map(|fields| {
                                fields.into_iter().map(|field| field.ty).collect::<Vec<_>>()
                            })
                    })
                    .collect::<Option<Vec<_>>>(),
                _ => None,
            };
            let Some(variants) = variants else {
                return;
            };
            building.push(key);
            for variant in &variants {
                for field in variant {
                    register_specialized_nominal_copy_type(field, function, signatures, building);
                }
            }
            building.pop();
            function
                .nominal_copy_descriptors
                .push(crate::MirNominalCopyDescriptor {
                    definition: *definition,
                    arguments: arguments.clone(),
                    variants,
                });
        }
        Type::Reference { .. }
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Projection { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => {}
    }
}

/// Every type witness embedded in MIR crosses the frozen VM boundary
/// independently of a local register declaration.  A concrete instance must
/// specialize those witnesses too: otherwise a generic record layout or
/// pattern can survive even when the value registers were made concrete.
fn specialize_mir_pattern(pattern: &mut crate::MirPattern, arguments: &[GenericArgument]) {
    match pattern {
        crate::MirPattern::Any | crate::MirPattern::Literal(_) => {}
        crate::MirPattern::Tuple(elements) => {
            for element in elements {
                specialize_mir_pattern(element, arguments);
            }
        }
        crate::MirPattern::Array { element, elements } => {
            *element = specialize_type(element, arguments);
            for element in elements {
                specialize_mir_pattern(element, arguments);
            }
        }
        crate::MirPattern::Record {
            field_types,
            fields,
            ..
        }
        | crate::MirPattern::Enum {
            field_types,
            fields,
            ..
        } => {
            *field_types = field_types
                .iter()
                .map(|field| specialize_type(field, arguments))
                .collect();
            for field in fields {
                field.ty = specialize_type(&field.ty, arguments);
                specialize_mir_pattern(&mut field.pattern, arguments);
            }
        }
    }
}

fn specialize_type(value: &Type, arguments: &[GenericArgument]) -> Type {
    match value {
        Type::Generic(slot) => arguments
            .get(*slot as usize)
            .and_then(|argument| match argument {
                GenericArgument::Type(value) => Some(value.clone()),
                _ => None,
            })
            .unwrap_or_else(|| value.clone()),
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| specialize_type(field, arguments))
                .collect(),
        ),
        Type::Array(element) => Type::Array(Box::new(specialize_type(element, arguments))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: specialize_lifetime(*lifetime, arguments),
            referent: Box::new(specialize_type(referent, arguments)),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(specialize_type(subject, arguments)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| specialize_generic_argument(argument, arguments))
                .collect(),
            name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| specialize_generic_argument(argument, arguments))
                .collect(),
        },
        Type::Nominal {
            definition,
            arguments: fields,
        } => Type::Nominal {
            definition: *definition,
            arguments: fields
                .iter()
                .map(|field| specialize_generic_argument(field, arguments))
                .collect(),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders: *lifetime_binders,
            parameters: parameters
                .iter()
                .map(|parameter| specialize_type(parameter, arguments))
                .collect(),
            result: Box::new(specialize_type(result, arguments)),
            effects: specialize_effect_row(effects, arguments),
            invocation: *invocation,
        },
        Type::ConstGeneric { index, kind } => arguments
            .get(*index as usize)
            .and_then(|argument| match (argument, kind) {
                (GenericArgument::ConstU32(value), crate::ConstKind::U32) => {
                    Some(Type::ConstU32(*value))
                }
                (GenericArgument::ConstQuantity(value), crate::ConstKind::Quantity) => {
                    Some(Type::ConstQuantity(*value))
                }
                (GenericArgument::ConstGeneric { kind: found, .. }, expected)
                    if found == expected =>
                {
                    Some(match argument {
                        GenericArgument::ConstGeneric { index, kind } => Type::ConstGeneric {
                            index: *index,
                            kind: *kind,
                        },
                        _ => unreachable!("const generic arm only admits const generic arguments"),
                    })
                }
                _ => None,
            })
            .unwrap_or_else(|| value.clone()),
        value => value.clone(),
    }
}

fn specialize_lifetime(
    lifetime: crate::Lifetime,
    arguments: &[GenericArgument],
) -> crate::Lifetime {
    match lifetime {
        crate::Lifetime::Generic(index) => arguments
            .get(index as usize)
            .and_then(|argument| match argument {
                GenericArgument::Lifetime(value) => Some(*value),
                _ => None,
            })
            .unwrap_or(lifetime),
        lifetime => lifetime,
    }
}

fn specialize_effect_row(
    value: &crate::EffectRow,
    arguments: &[GenericArgument],
) -> crate::EffectRow {
    let mut row = crate::EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| crate::EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| specialize_generic_argument(argument, arguments))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .iter()
            .map(|projection| crate::EffectRowProjection {
                subject: Box::new(specialize_type(&projection.subject, arguments)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .iter()
                    .map(|argument| specialize_generic_argument(argument, arguments))
                    .collect(),
                name: projection.name.clone(),
                item_generic_kinds: projection.item_generic_kinds.clone(),
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|argument| specialize_generic_argument(argument, arguments))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    };
    if let Some(crate::EffectTail::Generic(index)) = row.tail
        && let Some(GenericArgument::EffectRow(argument)) = arguments.get(index as usize)
    {
        let argument = specialize_effect_row(argument, arguments);
        row.effects.extend(argument.effects);
        row.projections.extend(argument.projections);
        row.tail = argument.tail;
    }
    row.canonicalized()
}

fn specialize_generic_argument(
    value: &GenericArgument,
    arguments: &[GenericArgument],
) -> GenericArgument {
    match value {
        GenericArgument::Type(value) => GenericArgument::Type(specialize_type(value, arguments)),
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(specialize_effect_row(value, arguments))
        }
        GenericArgument::Lifetime(value) => {
            GenericArgument::Lifetime(specialize_lifetime(*value, arguments))
        }
        GenericArgument::ConstGeneric { index, kind } => arguments
            .get(*index as usize)
            .filter(|argument| match (argument, kind) {
                (GenericArgument::ConstU32(_), crate::ConstKind::U32)
                | (GenericArgument::ConstQuantity(_), crate::ConstKind::Quantity) => true,
                (GenericArgument::ConstGeneric { kind: found, .. }, expected) => found == expected,
                _ => false,
            })
            .cloned()
            .unwrap_or_else(|| value.clone()),
        GenericArgument::ConstU32Expr(value) => match value.substitute(arguments) {
            crate::StructuralU32Expr::Literal(value) => GenericArgument::ConstU32(value),
            value => GenericArgument::ConstU32Expr(value),
        },
        value => value.clone(),
    }
}

/// Link only statically reachable functions into the executable program. A
/// body is still parsed, typed, and checked before this point, but a helper
/// eliminated by a verified static handler specialization must not force the
/// VM emitter to manufacture a normal runtime value for its terminal path.
/// `MakeCallable` is an edge because an indirect call may invoke that code
/// later; all iteration is ordered for byte-identical linking.
fn reachable_functions(
    functions: &BTreeMap<DefKey, MirFunction>,
    entry: DefKey,
) -> BTreeMap<DefKey, MirFunction> {
    let mut pending = BTreeSet::from([entry]);
    let mut reachable = BTreeSet::new();
    while let Some(definition) = pending.pop_first() {
        if !reachable.insert(definition) {
            continue;
        }
        let Some(function) = functions.get(&definition) else {
            continue;
        };
        for block in &function.blocks {
            for instruction in &block.instructions {
                if let crate::MirInstruction::Call { callee, .. }
                | crate::MirInstruction::MakeCallable { callee, .. } = instruction
                {
                    pending.insert(*callee);
                }
            }
        }
    }
    reachable
        .into_iter()
        .filter_map(|definition| {
            functions
                .get(&definition)
                .cloned()
                .map(|body| (definition, body))
        })
        .collect()
}

/// MIR contains no source spans; its deterministic structural debug form is
/// sufficient as a stage-zero product identity until the MIR serialization
/// boundary becomes the canonical persisted representation.  Keeping this
/// helper at the service boundary makes that future replacement local.
fn mir_fingerprint(function: &MirFunction) -> Digest {
    Digest::of_parts([
        b"grandiose-stage0-mir-v1".as_slice(),
        format!("{function:?}").as_bytes(),
    ])
}

/// Body syntax is a request-local frontend product. It includes recovery and
/// spans, because a source edit must cause that exact parsed body to be
/// checked again; downstream Core receives a span-free semantic fingerprint
/// and can still go green when the elaborated meaning is unchanged.
fn body_fingerprint(body: &BodySyntax) -> Digest {
    Digest::of_parts([
        b"grandiose-stage0-body-syntax-v1".as_slice(),
        format!("{body:?}").as_bytes(),
    ])
}

/// Attach the revision identity only at the service boundary, after every
/// phase has produced its deterministic local facts.  This keeps phase-local
/// diagnostics independent of request-session plumbing while ensuring no
/// published failure can be mistaken for a result from another source world.
fn failed(
    input_fingerprint: Digest,
    diagnostics: Vec<CompileDiagnostic>,
    source_lengths: &BTreeMap<crate::FileKey, u32>,
) -> ServiceError {
    let mut diagnostics = CompileDiagnostic::validate_primary_spans(diagnostics, source_lengths);
    for diagnostic in &mut diagnostics {
        enrich_semantic_provenance(diagnostic);
        diagnostic.input_fingerprint = Some(input_fingerprint);
    }
    let mut diagnostics =
        CompileDiagnostic::limit_errors(diagnostics, CompileDiagnostic::DEFAULT_ERROR_LIMIT);
    // The resource fact is synthesized after provenance is attached to the
    // phase-local batch, so give it the same immutable request identity.
    for diagnostic in &mut diagnostics {
        diagnostic.input_fingerprint = Some(input_fingerprint);
    }
    ServiceError::Failed(diagnostics)
}

/// Attach the immutable semantic boundary that produced diagnostics whose
/// phase-local representation predates the structured reporting API.  The
/// facts are deliberately code-driven rather than message-driven: wording
/// can improve without changing a machine consumer's contract.
fn enrich_semantic_provenance(diagnostic: &mut CompileDiagnostic) {
    type FactSet = &'static [(&'static str, &'static str)];
    type Explanation = Option<(&'static str, &'static str)>;
    let (facts, explanation): (FactSet, Explanation) = match diagnostic.code {
        "G4104" => (
            &[
                ("expected", "a declaration visible from the lexical scope"),
                ("observed", "an unresolved name"),
                ("semantic_phase", "name resolution"),
            ],
            Some((
                "name-resolution",
                "lexical lookup completed before type checking the expression",
            )),
        ),
        "G5013" | "G5014" | "G5015" | "G5017" | "G5019" => (
            &[("semantic_phase", "place and ownership flow")],
            Some((
                "ownership",
                "the frozen Core place graph was checked across every control-flow exit",
            )),
        ),
        "G5022" => (
            &[("semantic_phase", "escape analysis")],
            Some((
                "escape-boundary",
                "body-local borrows cannot outlive the body through an outward value or effect payload",
            )),
        ),
        "G6005" => (
            &[("semantic_phase", "handler resumption lowering")],
            Some((
                "handler-lifetime",
                "a resumed continuation cannot retain an uninstalled inner handler payload",
            )),
        ),
        _ => (&[], None),
    };
    for (name, value) in facts {
        if !diagnostic.facts.iter().any(|fact| fact.name == *name) {
            diagnostic.facts.push(DiagnosticFact {
                name: (*name).into(),
                value: (*value).into(),
            });
        }
    }
    if let Some((kind, message)) = explanation
        && !diagnostic
            .explanation
            .iter()
            .any(|frame| frame.kind == kind && frame.message == message)
    {
        diagnostic.explanation.push(DiagnosticExplanationFrame {
            kind: kind.into(),
            message: message.into(),
        });
    }
    diagnostic.canonicalize_provenance();
}

fn constant_cycle(
    functions: &BTreeMap<crate::DefKey, MirFunction>,
    constants: &BTreeSet<crate::DefKey>,
) -> Option<Vec<crate::DefKey>> {
    fn visit(
        definition: crate::DefKey,
        functions: &BTreeMap<crate::DefKey, MirFunction>,
        constants: &BTreeSet<crate::DefKey>,
        visiting: &mut BTreeSet<crate::DefKey>,
        visited: &mut BTreeSet<crate::DefKey>,
        path: &mut Vec<crate::DefKey>,
    ) -> Option<Vec<crate::DefKey>> {
        if !visiting.insert(definition) {
            let start = path.iter().position(|key| *key == definition).unwrap_or(0);
            let mut cycle = path[start..].to_vec();
            cycle.push(definition);
            return Some(cycle);
        }
        path.push(definition);
        let function = functions.get(&definition)?;
        for callee in function
            .blocks
            .iter()
            .flat_map(|block| block.instructions.iter())
            .filter_map(|instruction| match instruction {
                crate::MirInstruction::Call { callee, .. } if constants.contains(callee) => {
                    Some(*callee)
                }
                _ => None,
            })
        {
            if !visited.contains(&callee)
                && let Some(cycle) = visit(callee, functions, constants, visiting, visited, path)
            {
                return Some(cycle);
            }
            if visiting.contains(&callee) {
                let start = path.iter().position(|key| *key == callee).unwrap_or(0);
                let mut cycle = path[start..].to_vec();
                cycle.push(callee);
                return Some(cycle);
            }
        }
        path.pop();
        visiting.remove(&definition);
        visited.insert(definition);
        None
    }

    let mut visiting = BTreeSet::new();
    let mut visited = BTreeSet::new();
    let mut path = vec![];
    for definition in constants {
        if !visited.contains(definition)
            && let Some(cycle) = visit(
                *definition,
                functions,
                constants,
                &mut visiting,
                &mut visited,
                &mut path,
            )
        {
            return Some(cycle);
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::{specialize_mir_local_types, specialize_type};
    use crate::{
        CallableId, CaptureMode, CoreId, DefKey, Digest, EffectInstance, EffectRow,
        EffectRowProjection, EffectTail, EnvironmentBrand, GenericArgument, Lifetime, MirBlock,
        MirBlockId, MirCapture, MirCaptureEnvironment, MirFunction, MirInstruction, MirLocal,
        MirLocalDecl, MirPattern, MirPatternField, MirTerminator, Mutability, Quantity, ScalarType,
        Type,
    };

    fn key(name: &str) -> DefKey {
        DefKey(Digest::of_bytes(name.as_bytes()))
    }

    #[test]
    fn instance_specialization_rewrites_nested_generic_identity() {
        let outer_effect = key("outer-effect");
        let supplied_effect = key("supplied-effect");
        let trait_key = key("trait");
        let generic_effect = EffectInstance {
            definition: outer_effect,
            arguments: vec![
                GenericArgument::Type(Type::Generic(0)),
                GenericArgument::Lifetime(Lifetime::Generic(1)),
                GenericArgument::ConstGeneric {
                    index: 2,
                    kind: crate::ConstKind::U32,
                },
            ],
        };
        let supplied_row = EffectRow {
            effects: BTreeSet::from([EffectInstance {
                definition: supplied_effect,
                arguments: vec![GenericArgument::Type(Type::Generic(0))],
            }]),
            projections: vec![],
            tail: None,
        };
        let original = Type::Callable {
            lifetime_binders: 0,
            parameters: vec![Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Generic(1),
                referent: Box::new(Type::Generic(0)),
            }],
            result: Box::new(Type::ConstGeneric {
                index: 2,
                kind: crate::ConstKind::U32,
            }),
            effects: EffectRow {
                effects: BTreeSet::from([generic_effect]),
                projections: vec![EffectRowProjection {
                    subject: Box::new(Type::Generic(0)),
                    trait_definition: trait_key,
                    trait_arguments: vec![GenericArgument::Type(Type::Generic(0))],
                    name: "Effects".into(),
                    item_generic_kinds: vec![crate::GenericKind::Const(crate::ConstKind::U32)],
                    item_arguments: vec![GenericArgument::ConstGeneric {
                        index: 2,
                        kind: crate::ConstKind::U32,
                    }],
                }],
                tail: Some(EffectTail::Generic(3)),
            },
            invocation: Quantity::ONCE,
        };

        let specialized = specialize_type(
            &original,
            &[
                GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::ConstU32(17),
                GenericArgument::EffectRow(supplied_row),
            ],
        );

        let Type::Callable {
            parameters,
            result,
            effects,
            ..
        } = specialized
        else {
            panic!("expected specialized callable");
        };
        assert!(matches!(
            parameters.as_slice(),
            [Type::Reference {
                lifetime: Lifetime::Static,
                referent,
                ..
            }] if **referent == Type::Scalar(ScalarType::Text)
        ));
        assert_eq!(*result, Type::ConstU32(17));
        assert_eq!(effects.tail, None);
        assert!(effects.effects.contains(&EffectInstance {
            definition: outer_effect,
            arguments: vec![
                GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::ConstU32(17),
            ],
        }));
        assert!(effects.effects.contains(&EffectInstance {
            definition: supplied_effect,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
        }));
        assert!(matches!(
            effects.projections.as_slice(),
            [EffectRowProjection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            }] if **subject == Type::Scalar(ScalarType::Text)
                && trait_arguments == &vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))]
                && item_arguments == &vec![GenericArgument::ConstU32(17)]
        ));
    }

    #[test]
    fn materialization_specializes_every_frozen_mir_type_witness() {
        let generic = Type::Generic(0);
        let callable = Type::Callable {
            lifetime_binders: 0,
            parameters: vec![generic.clone()],
            result: Box::new(generic.clone()),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
        };
        let mut function = MirFunction {
            nominal_copy_descriptors: vec![],
            definition: key("specialize-frozen-mir-witnesses"),
            captures: 0,
            parameters: vec![],
            locals: vec![
                MirLocalDecl {
                    ty: generic.clone(),
                    source: CoreId(u32::MAX),
                },
                MirLocalDecl {
                    ty: Type::Scalar(ScalarType::Bool),
                    source: CoreId(u32::MAX),
                },
                MirLocalDecl {
                    ty: callable.clone(),
                    source: CoreId(u32::MAX),
                },
            ],
            result: generic.clone(),
            entry: MirBlockId(0),
            blocks: vec![MirBlock {
                parameters: vec![],
                instructions: vec![
                    MirInstruction::MakeRecord {
                        dst: MirLocal(0),
                        definition: key("generic-record"),
                        fields: vec![],
                        field_types: vec![generic.clone()],
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(1),
                        subject: MirLocal(0),
                        pattern: MirPattern::Record {
                            definition: key("generic-record"),
                            field_types: vec![generic.clone()],
                            field_count: 1,
                            fields: vec![MirPatternField {
                                index: 0,
                                ty: generic.clone(),
                                pattern: MirPattern::Array {
                                    element: generic.clone(),
                                    elements: vec![],
                                },
                            }],
                        },
                    },
                    MirInstruction::InstallHandler {
                        effect: key("generic-handler"),
                        effect_arguments: vec![GenericArgument::Type(generic.clone())],
                        operation: 0,
                        payload_destinations: vec![],
                        resume_type: generic.clone(),
                        continuation: crate::MirContinuationPolicy::Consume,
                        target: MirBlockId(0),
                    },
                    MirInstruction::HostCall {
                        dst: MirLocal(0),
                        capability: "test".into(),
                        symbol: "specialized".into(),
                        parameters: vec![generic.clone()],
                        result: generic.clone(),
                        arguments: vec![],
                    },
                    MirInstruction::MakeCallable {
                        dst: MirLocal(2),
                        callee: key("generic-callable"),
                        captures: vec![],
                        generic_arguments: vec![],
                        trait_instance: None,
                        environment: Some(MirCaptureEnvironment {
                            brand: EnvironmentBrand {
                                owner: key("generic-owner"),
                                callable: CallableId(0),
                            },
                            captures: vec![MirCapture {
                                mode: CaptureMode::Move,
                                ty: callable,
                            }],
                        }),
                    },
                ],
                terminator: MirTerminator::Unreachable,
            }],
        };
        specialize_mir_local_types(
            &mut function,
            &[GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        );
        assert!(
            !format!("{function:?}").contains("Generic(0)"),
            "a concrete instance retained a generic frozen witness: {function:#?}"
        );
    }
}
