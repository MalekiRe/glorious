//! End-to-end semantic service over immutable compilation requests.
//!
//! The command adapter may read files, but this service receives only a
//! `CompilationRequest`; every compiler product derives from its pinned
//! revision snapshot.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    BodySyntax, BootstrapManifest, CoherenceSet, CompilationMode, CompilationRequest,
    CompilerDatabase, DefKey, DefinitionIndex, DiagnosticClass, Digest, ElaboratedHeader,
    ElaboratedInterface, FixityTable, MirFunction, MirLowering, MirProgram, ModuleGraph,
    ParsedHeader, PlaceFlow, RevisionError, RevisionId, Severity, SourceSpan, Span,
    TrustedRuntimeManifest, TypedBody, VerifiedVmProgram, emit_vm_program,
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
}
impl CompileDiagnostic {
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
        }
    }

    /// Canonicalize a diagnostic batch at the service boundary.  Individual
    /// compiler phases deliberately retain local recovery behavior, so more
    /// than one phase can independently report the same source fact.  The
    /// published result must neither depend on phase traversal order nor make
    /// clients render that fact repeatedly.
    pub fn canonicalize(mut diagnostics: Vec<Self>) -> Vec<Self> {
        diagnostics.sort_by(|left, right| left.stable_key().cmp(&right.stable_key()));
        diagnostics.dedup_by(|left, right| left.stable_key() == right.stable_key());
        diagnostics
    }

    fn stable_key(
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
}
#[derive(Debug)]
pub struct CompilationOutcome {
    pub diagnostics: Vec<CompileDiagnostic>,
    pub artifact: Option<VerifiedVmProgram>,
    pub runtime_manifest: Option<TrustedRuntimeManifest>,
    /// Present only for `CompilationMode::Bootstrap`; this is the canonical
    /// evidence a host bootstrap driver persists and compares.
    pub bootstrap_manifest: Option<BootstrapManifest>,
}
#[derive(Debug)]
pub enum ServiceError {
    Revision(RevisionError),
    Failed(Vec<CompileDiagnostic>),
}
impl From<RevisionError> for ServiceError {
    fn from(value: RevisionError) -> Self {
        Self::Revision(value)
    }
}

#[derive(Debug, Default)]
pub struct StageZeroCompiler {
    database: CompilerDatabase,
}
impl StageZeroCompiler {
    pub fn new() -> Self {
        Self::default()
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
        let snapshot = self.database.open(revision)?;
        let input_fingerprint = snapshot.world().fingerprint;
        let graph = ModuleGraph::build(snapshot.world(), &snapshot.world().root_package);
        let mut diagnostics = graph
            .diagnostics
            .into_iter()
            .map(|diagnostic| {
                CompileDiagnostic::source(diagnostic.code, diagnostic.message, diagnostic.span)
            })
            .collect::<Vec<_>>();
        let Some(root) = graph.modules.get(&graph.root) else {
            return Err(failed(input_fingerprint, diagnostics));
        };
        for node in graph.modules.values() {
            diagnostics.extend(node.interface.diagnostics.iter().map(|diagnostic| {
                CompileDiagnostic::source(
                    diagnostic.code,
                    diagnostic.message.clone(),
                    Some(diagnostic.span),
                )
            }));
        }
        let index = DefinitionIndex::from_interfaces(
            graph.modules.values().map(|node| &node.interface.interface),
        );
        let coherence = CoherenceSet::collect(
            graph.modules.values().map(|node| &node.interface.interface),
            &index,
        );
        diagnostics.extend(coherence.diagnostics.iter().map(|diagnostic| {
            CompileDiagnostic::source(
                diagnostic.code,
                diagnostic.message.clone(),
                Some(diagnostic.span),
            )
        }));
        let signatures = ElaboratedInterface::merge(graph.modules.values().map(|node| {
            ElaboratedInterface::elaborate_with_index(&node.interface.interface, &index)
        }));
        diagnostics.extend(signatures.diagnostics.iter().map(|diagnostic| {
            CompileDiagnostic::source(diagnostic.code, diagnostic.message.clone(), None)
        }));
        let runtime_manifest = snapshot
            .world()
            .runtime_manifest
            .as_ref()
            .and_then(|input| {
                match input.bind(
                    graph
                        .modules
                        .values()
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
            return Err(failed(input_fingerprint, diagnostics));
        };
        let entry = entry.key;
        let mut functions = BTreeMap::new();
        let mut constants = BTreeSet::new();
        // Bodies are elaborated before any MIR lowering. This keeps every
        // lowering request rooted in one immutable package world and gives
        // static handler specialization read-only access to direct callee
        // Core products without reopening source or consulting host state.
        let mut body_products = Vec::<(DefKey, bool, bool, TypedBody, PlaceFlow)>::new();
        for node in graph.modules.values() {
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
            for declaration in node
                .interface
                .interface
                .definitions
                .iter()
                .filter(|definition| {
                    definition.callable_header().is_some()
                        || definition.kind == crate::DeclarationKind::Constant
                })
            {
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
                let is_constant = declaration.kind == crate::DeclarationKind::Constant;
                let body = if is_constant {
                    BodySyntax::parse_expression(&lexed, text, body_range)
                } else {
                    BodySyntax::parse(&lexed, text, body_range)
                };
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
                let core = if is_constant {
                    TypedBody::elaborate_constant(
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
                let flow = PlaceFlow::analyze(&core);
                diagnostics.extend(flow.diagnostics.iter().map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message.clone(),
                        Some(diagnostic.span),
                    )
                }));
                let valid = flow.diagnostics.is_empty()
                    && core.diagnostics.is_empty()
                    && body.diagnostics.is_empty();
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
                    let flow = PlaceFlow::analyze(&core);
                    diagnostics.extend(flow.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    let valid = flow.diagnostics.is_empty()
                        && core.diagnostics.is_empty()
                        && body.diagnostics.is_empty();
                    body_products.push((
                        implementation_method_key(implementation.key, &method.name),
                        false,
                        valid,
                        core,
                        flow,
                    ));
                }
            }
        }
        let typed_bodies = body_products
            .iter()
            .map(|(definition, _, _, core, _)| (*definition, core.clone()))
            .collect::<BTreeMap<_, _>>();
        for (definition, is_constant, valid, core, flow) in body_products {
            if !valid {
                continue;
            }
            let lowered = MirLowering::lower_with_bodies(definition, &core, &flow, &typed_bodies);
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
                    }
                }
            }
        }
        if !diagnostics.is_empty() {
            return Err(failed(input_fingerprint, diagnostics));
        }
        if let Some(cycle) = constant_cycle(&functions, &constants) {
            return Err(failed(
                input_fingerprint,
                vec![CompileDiagnostic::source(
                    "G7008",
                    format!("constant initializer cycle: {cycle:?}"),
                    None,
                )],
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
            return Ok(CompilationOutcome {
                diagnostics,
                artifact: None,
                runtime_manifest,
                bootstrap_manifest: None,
            });
        }
        let program = MirProgram {
            entry,
            functions: reachable_functions(&functions, entry),
        };
        let mut candidate = emit_vm_program(&program).map_err(|error| {
            failed(
                input_fingerprint,
                vec![CompileDiagnostic::invariant(
                    "G7004",
                    format!("VM emission rejected MIR: {error:?}"),
                )],
            )
        })?;
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
            )
        })?;
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
        })
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

/// Attach the revision identity only at the service boundary, after every
/// phase has produced its deterministic local facts.  This keeps phase-local
/// diagnostics independent of request-session plumbing while ensuring no
/// published failure can be mistaken for a result from another source world.
fn failed(input_fingerprint: Digest, mut diagnostics: Vec<CompileDiagnostic>) -> ServiceError {
    for diagnostic in &mut diagnostics {
        diagnostic.input_fingerprint = Some(input_fingerprint);
    }
    ServiceError::Failed(CompileDiagnostic::canonicalize(diagnostics))
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
