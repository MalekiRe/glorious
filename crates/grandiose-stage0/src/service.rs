//! End-to-end semantic service over immutable compilation requests.
//!
//! The command adapter may read files, but this service receives only a
//! `CompilationRequest`; every compiler product derives from its pinned
//! revision snapshot.

use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};

use crate::revision::{
    BodyScratchLease, PackageSessionError, PackageSessionLease, RequestControlError,
};
use crate::{
    BodySyntax, BootstrapManifest, Budget, BudgetError, CancellationToken, CoherenceSet,
    CompilationMode, CompilationRequest, CompilerDatabase, DatabaseSnapshot, DefKey,
    DefinitionIndex, DependencyNode, DependencyTrace, Digest, ElaboratedHeader,
    ElaboratedInterface, EscapeFlow, FixityTable, GenericArgument, InstanceGraph,
    InstanceKey, InstanceLimits,
    LogicalPath, ModuleGraph, PackageKey, ParsedHeader, PlaceFlow,
    PrimitiveRole, PrimitiveSelector,
    PublicationGuard, RequestSession, RetentionReport, RevisionError, RevisionId,
    RuntimeManifestInput, SourceInput, SourceSpan, TraitConstProjectionAnswer, TraitGoal,
    TraitSolver, TrustedRuntimeManifest,
    PersistentArtifactCache, Type, TypedBody, UseFlow, VerifiedVmProgram, implementation_method_key,
    verify_vm_program,
};

#[cfg(test)]
use crate::{MirFunction, MirInstance, MirInstruction};

mod diagnostics;
mod interface_dependencies;
pub use diagnostics::{
    CompileDiagnostic, DiagnosticExplanationFrame, DiagnosticFact, RelatedDiagnosticLocation,
};

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

/// The immutable product of one successfully elaborated body.  This is kept
/// private deliberately: consumers below this boundary receive only a body
/// that has crossed the body session's publication gate, never the mutable
/// parser/elaboration scratch that created it.
#[derive(Debug)]
struct PublishedBody {
    definition: DefKey,
    is_constant: bool,
    valid: bool,
    core: TypedBody,
    flow: PlaceFlow,
    /// The body remains the parent of its MIR lowering work even after its
    /// syntax/core scratch has been frozen into this request-local product.
    budget: Arc<Budget>,
}

/// Frozen typing product, before any inter-body ownership/control analysis.
/// Keeping this phase separate makes the complete demanded Core arena
/// available regardless of declaration or package traversal order. It is
/// request-local staging, never an externally published executable product.
struct StagedTypedBody {
    definition: DefKey,
    is_constant: bool,
    valid: bool,
    core: TypedBody,
    lexical_bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
    lexical_effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
    solver: TraitSolver,
    budget: Arc<Budget>,
}

impl std::fmt::Debug for StagedTypedBody {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.debug_struct("StagedTypedBody")
            .field("definition", &self.definition)
            .field("is_constant", &self.is_constant)
            .field("valid", &self.valid)
            .field("core", &self.core)
            .finish_non_exhaustive()
    }
}

impl StagedTypedBody {
    fn check_resources(
        &self,
        signatures: &ElaboratedInterface,
        abort_primitive: Option<DefKey>,
        continuations: Arc<crate::core_continuations::CoreContinuations>,
        diagnostics: &mut Vec<CompileDiagnostic>,
    ) -> (PlaceFlow, EscapeFlow, bool) {
        let Self { core, lexical_bounds, lexical_effect_bindings, solver, .. } = self;
        let flow = PlaceFlow::analyze_with_frozen_solver(
            core, signatures, lexical_bounds, lexical_effect_bindings, solver, abort_primitive,
            continuations,
        );
        diagnostics.extend(flow.diagnostics.iter().map(|diagnostic| CompileDiagnostic::source(
            diagnostic.code, diagnostic.message.clone(), Some(diagnostic.span),
        )));
        let escapes = EscapeFlow::analyze_with_interface(core, &flow, signatures);
        diagnostics.extend(escapes.diagnostics.iter().map(|diagnostic| CompileDiagnostic::source(
            diagnostic.code, diagnostic.message.clone(), Some(diagnostic.span),
        )));
        let uses = UseFlow::analyze_with_interface(core, &flow, signatures);
        diagnostics.extend(uses.diagnostics.iter().map(|diagnostic| CompileDiagnostic::source(
            diagnostic.code, diagnostic.message.clone(), Some(diagnostic.span),
        )));
        let valid = self.valid && flow.diagnostics.is_empty() && escapes.diagnostics.is_empty()
            && uses.diagnostics.is_empty();
        (flow, escapes, valid)
    }

    fn analyze(
        self,
        signatures: &ElaboratedInterface,
        abort_primitive: Option<DefKey>,
        continuations: Arc<crate::core_continuations::CoreContinuations>,
        diagnostics: &mut Vec<CompileDiagnostic>,
    ) -> PublishedBody {
        let (flow, _, valid) = self.check_resources(signatures, abort_primitive, continuations, diagnostics);
        let Self { definition, is_constant, core, budget, .. } = self;
        PublishedBody { definition, is_constant, valid, core, flow, budget }
    }
}

/// Request-local owner for one package's demanded body work.
///
/// A package session borrows the request's immutable snapshot and controls,
/// but owns only package-local mutable staging.  It intentionally does not
/// own source bytes, interfaces, or an interner: those remain immutable
/// database products.  Dropping an unfinished package session discards all
/// staged bodies, so no partial package product can escape a failed request.
#[derive(Debug)]
struct PackageSession<'request> {
    request: &'request RequestSession,
    lease: PackageSessionLease<'request>,
    budget: Arc<Budget>,
    package: PackageKey,
    demanded_bodies: BTreeSet<DefKey>,
    staged_bodies: Vec<StagedTypedBody>,
}

impl<'request> PackageSession<'request> {
    fn new(
        request: &'request RequestSession,
        package: PackageKey,
    ) -> Result<Self, PackageSessionError> {
        let lease = request.open_package_session(package.clone())?;
        Ok(Self {
            request,
            lease,
            budget: request.package_budget(),
            package,
            demanded_bodies: BTreeSet::new(),
            staged_bodies: Vec::new(),
        })
    }

    /// Open the sole mutable owner for a body.  The `&mut self` borrow makes
    /// it impossible to open two active sessions for the same package through
    /// this API, and `demanded_bodies` makes accidental duplicate admission an
    /// explicit compiler invariant rather than silent duplicate publication.
    fn open_body(
        &mut self,
        definition: DefKey,
        is_constant: bool,
        syntax: BodySyntax,
    ) -> Result<BodySession<'_, 'request>, PackageSessionError> {
        let inserted = self.demanded_bodies.insert(definition);
        assert!(
            inserted,
            "body `{definition:?}` was admitted twice by package `{}`",
            self.package.0,
        );
        let budget = self.budget.child("body", self.budget.ceiling());
        let scratch = self.request.open_body_scratch(self.package.clone())?;
        Ok(BodySession {
            package: self,
            definition,
            is_constant,
            syntax,
            budget,
            scratch,
        })
    }

    fn checkpoint(&self, cost: u64) -> Result<(), RequestControlError> {
        self.request.checkpoint_in(&self.budget, cost)
    }

    fn finish(mut self) -> Result<Vec<StagedTypedBody>, PackageSessionError> {
        // The worklist is a deterministic set.  Sort the staged result too,
        // so later instance discovery never acquires source traversal order
        // as an accidental semantic input.
        self.staged_bodies.sort_by_key(|body| body.definition);
        // This consumes the affine request-owned lease.  If staging failed,
        // normal destruction rolls back this package before any mutable
        // product can escape the request transaction.
        self.lease.stage()?;
        Ok(self.staged_bodies)
    }
}

/// Affine mutable owner for one body elaboration.
///
/// It owns transient syntax and freezes Typed Core at staging. Consuming
/// `self` in [`Self::stage_typed`] is the only path that transfers this typing
/// product to its package session; normal Rust destruction
/// rolls back an incomplete body by dropping its scratch instead.
#[must_use = "a body session must stage its typed body or be dropped to roll back scratch"]
struct BodySession<'package, 'request> {
    package: &'package mut PackageSession<'request>,
    definition: DefKey,
    is_constant: bool,
    syntax: BodySyntax,
    budget: Arc<Budget>,
    scratch: BodyScratchLease<'request>,
}

impl BodySession<'_, '_> {
    fn syntax(&self) -> &BodySyntax {
        &self.syntax
    }

    fn checkpoint(&self, cost: u64) -> Result<(), RequestControlError> {
        self.package.request.checkpoint_in(&self.budget, cost)
    }

    /// Stage a complete immutable typing product. The checkpoint happens
    /// before mutation of package staging, so cancellation/resource failure
    /// cannot publish this body even to request-local staging.  The enclosing
    /// request transaction remains the sole external publication boundary.
    fn stage_typed(self, valid: bool, core: TypedBody,
        lexical_bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
        lexical_effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
        solver: TraitSolver,
    ) -> Result<(), ServiceError> {
        let Self {
            package,
            definition,
            is_constant,
            budget,
            scratch,
            ..
        } = self;
        scratch.publish()?;
        package.staged_bodies.push(StagedTypedBody {
            definition,
            is_constant,
            valid,
            core,
            lexical_bounds,
            lexical_effect_bindings,
            solver,
            budget,
        });
        Ok(())
    }
}


#[derive(Debug)]
enum EmissionFailure {
    Emit(String),
    UnauthorizedCapability(String),
    Verify(String),
}

/// Affine owner for the final VM-artifact construction boundary.
///
/// This session owns the selected reachable program and the mutable candidate
/// artifact until verification succeeds.  Its only success path consumes the
/// session and returns a frozen VM image; all failure paths drop the candidate
/// without publication.
#[derive(Debug)]
struct EmissionSession {
    program: crate::vm_lir::VmLirProgram,
    runtime_manifest: Option<TrustedRuntimeManifest>,
    budget: Arc<Budget>,
}

impl EmissionSession {
    fn new(
        program: crate::vm_lir::VmLirProgram,
        runtime_manifest: Option<TrustedRuntimeManifest>,
        budget: Arc<Budget>,
    ) -> Self {
        Self {
            program,
            runtime_manifest,
            budget,
        }
    }

    fn checkpoint(&self, session: &RequestSession, cost: u64) -> Result<(), RequestControlError> {
        session.checkpoint_in(&self.budget, cost)
    }

    fn mir_dependencies(&self) -> Vec<DependencyNode> {
        self.program
            .functions()
            .keys()
            .copied()
            .map(DependencyNode::Mir)
            .collect()
    }

    fn emit(
        self,
        capability_granted: impl Fn(&str) -> bool,
    ) -> Result<VerifiedVmProgram, EmissionFailure> {
        let mut candidate = self.program.emit()
            .map_err(|error| EmissionFailure::Emit(format!("{error:?}")))?;
        if let Some(capability) = candidate
            .host_capabilities
            .iter()
            .find(|capability| !capability_granted(capability))
        {
            return Err(EmissionFailure::UnauthorizedCapability(capability.clone()));
        }
        if let Some(manifest) = &self.runtime_manifest {
            candidate.runtime_manifest = Some(manifest.digest);
            candidate.fingerprint = candidate.computed_fingerprint();
        }
        verify_vm_program(candidate).map_err(|error| EmissionFailure::Verify(format!("{error:?}")))
    }
}
#[derive(Debug)]
pub enum ServiceError {
    Revision(RevisionError),
    PackageSession(PackageSessionError),
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
            Self::PackageSession(error) => vec![CompileDiagnostic::invariant(
                "G7035",
                format!("request package-session lifecycle violation: {error:?}"),
            )],
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

impl From<RevisionError> for ServiceError {
    fn from(value: RevisionError) -> Self {
        Self::Revision(value)
    }
}

/// Compilation contains host arithmetic too: literal decoding, pattern
/// validation and optimization must not inherit an embedding thread's
/// rounding, subnormal, exception-mask or sticky-status state. Keep the guard
/// at request entry, not around individual literals or optimization rules.
fn with_float_profile<T>(
    body: impl FnOnce() -> Result<T, ServiceError>,
) -> Result<T, ServiceError> {
    let failure = |error| ServiceError::Failed(vec![CompileDiagnostic::invariant(
        "G7043",
        format!("compiler floating-point environment failed: {error:?}"),
    )]);
    let environment = crate::vm_backend::float_env::FloatEnvironment::enter().map_err(failure)?;
    let result = body();
    environment.restore().map_err(failure)?;
    result
}

impl From<RequestControlError> for ServiceError {
    fn from(value: RequestControlError) -> Self {
        match value {
            RequestControlError::Cancelled => Self::Cancelled,
            RequestControlError::Resource(error) => Self::Resource(error),
        }
    }
}

impl From<PackageSessionError> for ServiceError {
    fn from(value: PackageSessionError) -> Self {
        Self::PackageSession(value)
    }
}

#[derive(Debug, Default)]
pub struct StageZeroCompiler {
    database: CompilerDatabase,
    instance_limits: InstanceLimits,
}

const BUNDLED_STANDARD_LIBRARY: &str = "std@0.1.0";
#[path = "../../../stdlib/sources.rs"]
mod standard_library_sources;
pub use standard_library_sources::{STANDARD_LIBRARY_SOURCE, STANDARD_LIBRARY_FRAGMENTS};
const STANDARD_LIBRARY_BASE_SOURCE: &[u8] = include_bytes!("../../../stdlib/src/lib.glorious");
const BUNDLED_STANDARD_SOURCE: &[u8] = STANDARD_LIBRARY_BASE_SOURCE;

fn request_root_attributes(request: &CompilationRequest) -> Option<crate::scanner::ModuleAttributes> {
    let mut roots = request.sources.iter().filter(|source| {
        source.package == request.root_package
            && matches!(source.logical_path.as_str(), "src/main.glorious" | "src/lib.glorious")
    });
    let source = roots.next()?;
    // Invalid multi-root requests must not select a library profile by source
    // enumeration order. Ordinary request/graph validation reports the error.
    if roots.next().is_some() {
        return None;
    }
    let text = std::str::from_utf8(&source.bytes).ok()?;
    let lexed = crate::LexedFile::lex(source.key, text);
    Some(crate::DeclarationScan::scan(&lexed, text).module_attributes)
}

/// Attach the compiler-distributed source package unless a host already
/// supplied that exact package. The latter remains useful for bootstrap and
/// conformance worlds; ordinary CLI and API requests receive the canonical
/// library automatically. Its source-owned prelude is selected after module
/// collection; source bytes and source spans are never rewritten with imports.
fn bundled_standard_library(mut request: CompilationRequest) -> CompilationRequest {
    let standard_library = PackageKey(BUNDLED_STANDARD_LIBRARY.into());
    // An explicit runtime manifest is a closed authority contract. Do not
    // silently add a second standard package whose private leaves that
    // manifest did not bind; callers using such a manifest may still supply
    // `std@0.1.0` explicitly when they want this distributed source package.
    let injected = request.runtime_manifest.is_none()
        && request_root_attributes(&request).is_some_and(|attributes| !attributes.no_std)
        && request.root_package != standard_library
        && !request
            .sources
            .iter()
            .any(|source| crate::identity::package_module_alias(&source.package).as_deref() == Some("std"));
    if injected {
        request.sources.push(SourceInput::new(
            standard_library.clone(),
            LogicalPath::parse("src/lib.glorious").expect("static standard path is valid"),
            BUNDLED_STANDARD_SOURCE,
        ));
    }
    let has_bundled_source = request.sources.iter().any(|source| {
        source.package == standard_library
            && standard_library_sources::is_standard_library_composition(source.bytes.as_ref())
    });
    if has_bundled_source && request.runtime_manifest.is_none() {
        let float_bit_views = request.sources.iter().any(|source| {
            source.package == standard_library
                && standard_library_sources::composition_contains(source.bytes.as_ref(), "src/float.glorious")
        });
        request.runtime_manifest = Some(RuntimeManifestInput {
            standard_library,
            selectors: [
                PrimitiveRole::BytesFromArrayMove,
                PrimitiveRole::BytesToArray,
                PrimitiveRole::Blake3,
                PrimitiveRole::ArrayGetBorrowShared,
                PrimitiveRole::ArrayEmpty,
                PrimitiveRole::ArrayPushMove,
                PrimitiveRole::StaticLen,
                PrimitiveRole::CharFromU32Checked,
                PrimitiveRole::CharToU32,
                PrimitiveRole::IntConvertWrappingToU32,
                PrimitiveRole::IntConvertWrappingToUsize,
                PrimitiveRole::IntConvertWrappingToI64,
                PrimitiveRole::IntConvertWrappingToU8,
                PrimitiveRole::IntConvertWrappingToU16,
                PrimitiveRole::IntConvertWrappingToI8,
                PrimitiveRole::IntConvertWrappingToI16,
                PrimitiveRole::IntConvertWrappingToI32,
                PrimitiveRole::IntConvertWrappingToU64,
                PrimitiveRole::IntConvertWrappingToIsize,
                PrimitiveRole::IntConvertWrappingToU128,
                PrimitiveRole::IntConvertWrappingToI128,
                PrimitiveRole::IntConvertCheckedToU8,
                PrimitiveRole::IntConvertCheckedToU16,
                PrimitiveRole::IntConvertCheckedToU32,
                PrimitiveRole::IntConvertCheckedToU64,
                PrimitiveRole::IntConvertCheckedToUsize,
                PrimitiveRole::IntConvertCheckedToI8,
                PrimitiveRole::IntConvertCheckedToI16,
                PrimitiveRole::IntConvertCheckedToI32,
                PrimitiveRole::IntConvertCheckedToIsize,
                PrimitiveRole::IntConvertCheckedToU128,
                PrimitiveRole::IntConvertCheckedToI128,
                PrimitiveRole::IntWrappingAdd,
                PrimitiveRole::IntCheckedAdd,
                PrimitiveRole::IntCheckedDiv,
                PrimitiveRole::IntEqual,
                PrimitiveRole::IntLess,
                PrimitiveRole::IntGreater,
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Neg {
                    width: crate::runtime_manifest::FloatWidth::F32,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Neg {
                    width: crate::runtime_manifest::FloatWidth::F64,
                }),
                PrimitiveRole::IntWrappingSub,
                PrimitiveRole::IntWrappingMul,
                PrimitiveRole::IntBitAnd,
                PrimitiveRole::IntBitOr,
                PrimitiveRole::IntBitXor,
                PrimitiveRole::IntBitNot,
                PrimitiveRole::IntShl,
                PrimitiveRole::IntShr,
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatBinaryOp::Add,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatBinaryOp::Sub,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatBinaryOp::Mul,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatBinaryOp::Div,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatBinaryOp::Rem,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Eq,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Ne,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Lt,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Le,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Gt,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F32,
                    operation: crate::runtime_manifest::FloatCompareOp::Ge,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::FromBits {
                    width: crate::runtime_manifest::FloatWidth::F32,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Convert {
                    from: crate::ScalarType::I64,
                    to: crate::ScalarType::F32,
                    checked: false,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Convert {
                    from: crate::ScalarType::F32,
                    to: crate::ScalarType::I64,
                    checked: true,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatBinaryOp::Add,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatBinaryOp::Sub,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatBinaryOp::Mul,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatBinaryOp::Div,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Binary {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatBinaryOp::Rem,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Eq,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Ne,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Lt,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Le,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Gt,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Compare {
                    width: crate::runtime_manifest::FloatWidth::F64,
                    operation: crate::runtime_manifest::FloatCompareOp::Ge,
                }),
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Convert {
                    from: crate::ScalarType::F64,
                    to: crate::ScalarType::I64,
                    checked: true,
                }),
            ]
            .into_iter()
            // Complete the library's numeric conversion matrix using only
            // existing, signature-checked VM roles. The public As trait and
            // saturation policy are ordinary source, not manifest bindings.
            .chain([
                (crate::ScalarType::U8, crate::ScalarType::F32, false),
                (crate::ScalarType::U8, crate::ScalarType::F64, false),
                (crate::ScalarType::U16, crate::ScalarType::F32, false),
                (crate::ScalarType::U16, crate::ScalarType::F64, false),
                (crate::ScalarType::U32, crate::ScalarType::F32, false),
                (crate::ScalarType::U32, crate::ScalarType::F64, false),
                (crate::ScalarType::U64, crate::ScalarType::F32, false),
                (crate::ScalarType::U64, crate::ScalarType::F64, false),
                (crate::ScalarType::U128, crate::ScalarType::F32, false),
                (crate::ScalarType::U128, crate::ScalarType::F64, false),
                (crate::ScalarType::Usize, crate::ScalarType::F32, false),
                (crate::ScalarType::Usize, crate::ScalarType::F64, false),
                (crate::ScalarType::I8, crate::ScalarType::F32, false),
                (crate::ScalarType::I8, crate::ScalarType::F64, false),
                (crate::ScalarType::I16, crate::ScalarType::F32, false),
                (crate::ScalarType::I16, crate::ScalarType::F64, false),
                (crate::ScalarType::I32, crate::ScalarType::F32, false),
                (crate::ScalarType::I32, crate::ScalarType::F64, false),
                (crate::ScalarType::I64, crate::ScalarType::F64, false),
                (crate::ScalarType::I128, crate::ScalarType::F32, false),
                (crate::ScalarType::I128, crate::ScalarType::F64, false),
                (crate::ScalarType::Isize, crate::ScalarType::F32, false),
                (crate::ScalarType::Isize, crate::ScalarType::F64, false),
                (crate::ScalarType::F32, crate::ScalarType::F64, false),
                (crate::ScalarType::F64, crate::ScalarType::F32, false),
                (crate::ScalarType::F64, crate::ScalarType::U8, true),
                (crate::ScalarType::F64, crate::ScalarType::U16, true),
                (crate::ScalarType::F64, crate::ScalarType::U32, true),
                (crate::ScalarType::F64, crate::ScalarType::U64, true),
                (crate::ScalarType::F64, crate::ScalarType::U128, true),
                (crate::ScalarType::F64, crate::ScalarType::Usize, true),
                (crate::ScalarType::F64, crate::ScalarType::I8, true),
                (crate::ScalarType::F64, crate::ScalarType::I16, true),
                (crate::ScalarType::F64, crate::ScalarType::I32, true),
                (crate::ScalarType::F64, crate::ScalarType::I128, true),
                (crate::ScalarType::F64, crate::ScalarType::Isize, true),
            ].into_iter().map(|(from, to, checked)| {
                PrimitiveRole::Float(crate::runtime_manifest::FloatPrimitive::Convert {
                    from, to, checked,
                })
            }))
            .chain(crate::MemoryPrimitive::ALL.into_iter().map(PrimitiveRole::Memory))
            .chain([
                crate::runtime_manifest::FloatPrimitive::ToBits { width: crate::runtime_manifest::FloatWidth::F32 },
                crate::runtime_manifest::FloatPrimitive::ToBits { width: crate::runtime_manifest::FloatWidth::F64 },
                crate::runtime_manifest::FloatPrimitive::FromBits { width: crate::runtime_manifest::FloatWidth::F64 },
            ].into_iter().filter(|_| float_bit_views).map(PrimitiveRole::Float))
            .chain([PrimitiveRole::Abort])
            .map(|role| PrimitiveSelector {
                role,
                module_path: "crate".into(),
                name: format!("__g1_{}", role.selector_name().replace('-', "_")),
            })
            .collect(),
            host_imports: vec![],
        });
    }
    request
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

    /// Produce an executable program through a host-supplied persistent cache.
    ///
    /// This artifact-only convenience path is intentionally separate from
    /// [`Self::compile`]: a cache hit has already crossed the decoder and VM
    /// verifier boundary, but does not reconstruct body diagnostics, instance
    /// discovery evidence, bootstrap manifests, or revision traces. Hosts
    /// requiring those inspection products must use the ordinary service path.
    /// Cache I/O failures are optimization misses, never source-compilation
    /// failures; a freshly verified program still reaches the caller.
    pub fn compile_artifact_with_cache(
        &self,
        request: CompilationRequest,
        cache: &PersistentArtifactCache,
    ) -> Result<Option<VerifiedVmProgram>, ServiceError> {
        with_float_profile(|| self.compile_artifact_with_cache_in_profile(request, cache))
    }

    fn compile_artifact_with_cache_in_profile(
        &self,
        request: CompilationRequest,
        cache: &PersistentArtifactCache,
    ) -> Result<Option<VerifiedVmProgram>, ServiceError> {
        let request = bundled_standard_library(request);
        let world = request
            .clone()
            .normalize()
            .map_err(RevisionError::Input)?;
        if let Some(program) = cache.load(&world) {
            return Ok(Some(program));
        }
        let outcome = self.compile(request)?;
        if let Some(program) = outcome.artifact {
            // A persistent cache is untrusted and optional by design. Do not
            // convert a successfully verified fresh program into a failed
            // user build merely because the host cache is unavailable.
            let _ = cache.store(&world, &program);
            Ok(Some(program))
        } else {
            Ok(None)
        }
    }

    /// Import one immutable request world into this compiler's database. The
    /// caller may explicitly link it to the revision it supersedes; this is
    /// the only way incremental clients establish a parent/child relation.
    pub fn import_revision(
        &self,
        request: CompilationRequest,
        parent: Option<RevisionId>,
    ) -> Result<RevisionId, ServiceError> {
        Ok(self.database.import(bundled_standard_library(request), parent)?)
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
        with_float_profile(|| self.compile_session_in_profile(session))
    }

    fn compile_session_in_profile(
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
        let outcome = match self.compile_snapshot(
            session.snapshot(),
            session,
            &mut interfaces,
            &mut dependencies,
        ) {
            Ok(outcome) => outcome,
            Err(error) => {
                // Package staging is deliberately request-owned.  A body,
                // elaboration, or lowering failure abandons every package
                // product before the interface/dependency transactions drop.
                session.rollback_package_sessions();
                return Err(error);
            }
        };
        // One final cancellation check linearizes request publication. Before
        // it succeeds, dropping the outcome and transaction publishes neither
        // an artifact nor newly collected frozen interfaces.
        let outcome = match PublicationGuard::stage(outcome).commit(session.cancellation()) {
            Ok(outcome) => outcome,
            Err(_) => {
                session.rollback_package_sessions();
                return Err(ServiceError::Cancelled);
            }
        };
        // All package sessions must have reached staging before any
        // request-visible cache transaction becomes durable.  `commit_all`
        // validates first and then changes every package atomically.
        if let Err(error) = session.commit_package_sessions() {
            session.rollback_package_sessions();
            return Err(error.into());
        }
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
        let prelude = graphs.keys()
            .find(|package| crate::identity::package_module_alias(package).as_deref() == Some("std"))
            .map(|package| crate::ModuleKey { package: package.clone(), path: "crate::prelude".into() })
            .filter(|module| graphs.get(&module.package).is_some_and(|graph| graph.modules.contains_key(module)));
        let index = DefinitionIndex::from_interfaces_with_prelude(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| &node.interface.interface),
            prelude,
        );
        let declared_fixities = graphs
            .values()
            .flat_map(|graph| graph.modules.values())
            .flat_map(|node| node.interface.interface.definitions.iter())
            .filter_map(|definition| match &definition.syntax.header {
                ParsedHeader::Fixity(fixity) => Some((definition.key, fixity.clone())),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
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
        let interface_inputs = graphs
            .values()
            .flat_map(|graph| graph.modules.values())
            .map(|node| {
                (
                    node.key.clone(),
                    (node.file, index.sealed_public_dependencies(&node.interface.interface)),
                )
            })
            .collect::<BTreeMap<_, _>>();
        let interface_dependencies =
            interface_dependencies::publication_dependencies(&interface_inputs);
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            dependencies.record(
                DependencyNode::Interface(node.key.clone()),
                node.interface.interface.public_fingerprint,
                interface_dependencies[&node.key].clone(),
            );
        }
        diagnostics.extend(index.validate_imports().into_iter().map(|diagnostic| {
            CompileDiagnostic::source(diagnostic.code, diagnostic.message, Some(diagnostic.span))
        }));
        diagnostics.extend(
            index
                .validate_package_import_cycles()
                .into_iter()
                .map(|diagnostic| {
                    CompileDiagnostic::source(
                        diagnostic.code,
                        diagnostic.message,
                        Some(diagnostic.span),
                    )
                }),
        );
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
        // Coherence and body typing consume the same immutable signatures.
        // Elaborating them inside coherence and again below duplicated every
        // signature validation and all of its frozen solver construction.
        let mut signatures = ElaboratedInterface::merge(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| {
                    ElaboratedInterface::elaborate_with_index(&node.interface.interface, &index)
                }),
        );
        let coherence = CoherenceSet::collect_with_signatures(
            graphs
                .values()
                .flat_map(|graph| graph.modules.values())
                .map(|node| &node.interface.interface),
            &index,
            &signatures,
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
            let fixities = visible_fixities_for_module(&node.key, &index, &declared_fixities);
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
                let body = BodySyntax::parse_expression_with_fixities(&lexed, text, body_range, &fixities);
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
                signatures.freeze_typed_value_initializer(declaration.key, &core);
            }
        }
        // `Use` is not ordinary implementation selection: the frozen
        // interface owns one structural principal interval per type, and a
        // manual implementation may only restrict it.  Run this after the
        // initializer prepass so memoized globals are checked against their
        // actual frozen result types rather than a body-local inference term.
        // An explicit position binding is a declaration contract, not a
        // request to search for an alternative operator when it is used.
        // Validate even unused bindings, after named aliases have frozen.
        for definition in graphs.values().flat_map(|graph| graph.modules.values())
            .flat_map(|node| &node.interface.interface.definitions) {
            let ParsedHeader::Fixity(fixity) = &definition.syntax.header else { continue; };
            let Some(path) = &fixity.target else { continue; };
            let state = index.resolve_path(crate::DefinitionNamespace::Value, &definition.module, path);
            let valid = match state {
                crate::ResolutionState::Resolved(target) => {
                    let target = signatures.value_alias_target(target).unwrap_or(target);
                    match signatures.definitions.get(&target) {
                        Some(ElaboratedHeader::Callable(signature) | ElaboratedHeader::ValueAlias { signature, .. }) =>
                            signature.parameters.len() == if fixity.form.is_prefix() { 1 } else { 2 },
                        _ => false,
                    }
                }
                _ => false,
            };
            if !valid {
                diagnostics.push(CompileDiagnostic::source("G3214",
                    format!("explicit operator target `{}` must resolve to an accessible ordinary callable with {} parameter(s)",
                        path.join("::"), if fixity.form.is_prefix() { 1 } else { 2 }), Some(definition.span)));
            }
        }
        diagnostics.extend(signatures.validate_principal_use_rules().into_iter().map(
            |diagnostic| CompileDiagnostic::source(diagnostic.code, diagnostic.message, None),
        ));
        for header in signatures.definitions.values() {
            let ElaboratedHeader::ValueInitializer { ty: Some(ty), .. } = header else {
                continue;
            };
            // A generalized initializer can retain an abstract principal
            // interval until a concrete instantiation supplies its generic
            // arguments. Reject known restricted globals here; an unknown
            // symbolic interval is not evidence of a restricted runtime
            // allocation and must remain generalizable.
            if signatures
                .principal_use_interval(ty)
                .is_some_and(|quantity| quantity != crate::Quantity::UNRESTRICTED)
            {
                diagnostics.push(CompileDiagnostic::source(
                    "G4196",
                    "memoized top-level global has a restricted or unproven principal `Use` quantity",
                    None,
                ));
            }
        }
        // `Drop` is an opaque zero-use destruction hook, not another way to
        // satisfy ownership. Its interface must therefore be available at
        // zero use and its hook cannot expose effects before a body is ever
        // lowered into cleanup machinery.
        for implementation in signatures
            .definitions
            .values()
            .filter_map(|header| match header {
                ElaboratedHeader::Implementation(implementation)
                    if implementation.relation.definition
                        == crate::resolution::language_drop_trait_definition() =>
                {
                    Some(implementation)
                }
                _ => None,
            })
        {
            if !signatures
                .principal_use_interval_with_bounds(&implementation.self_ty, &implementation.where_bounds)
                .is_some_and(|quantity| quantity.contains(crate::Quantity::AFFINE))
            {
                diagnostics.push(CompileDiagnostic::source(
                    "G4197",
                    "custom `Drop` requires affine `Use<[0,1]>` erasure permission; an exact-linear value cannot be destroyed",
                    None,
                ));
            }
            if implementation.methods.get("drop").is_some_and(|method| {
                !method.effects.effects.is_empty()
                    || !method.effects.projections.is_empty()
                    || !method.effects.tails.is_empty()
            }) {
                diagnostics.push(CompileDiagnostic::source(
                    "G4197",
                    "custom `Drop` destructor must be pure and cannot expose effects or suspension",
                    None,
                ));
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
                    || !signature.effects.tails.is_empty()
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
        let mut lowering = BTreeMap::new();
        // Value-initializer types and runtime contracts are now frozen. Share
        // their immutable rule/layout snapshot across bodies, while every
        // body retains fresh tables and its original independent work limit.
        let body_trait_solver = TraitSolver::new(&signatures);
        // Bodies are elaborated before any MIR lowering. This keeps every
        // lowering request rooted in one immutable package world and gives
        // static handler specialization read-only access to direct callee
        // Core products without reopening source or consulting host state.
        // One request may demand bodies from several packages.  Keep their
        // mutable staging separate even though this Stage0 implementation
        // still consumes the resulting immutable products in one later
        // instance-discovery pass.
        let mut package_sessions = graphs
            .keys()
            .cloned()
            .map(|package| {
                let package_session = PackageSession::new(session, package.clone())?;
                Ok((package, package_session))
            })
            .collect::<Result<BTreeMap<_, _>, PackageSessionError>>()?;
        for node in graphs.values().flat_map(|graph| graph.modules.values()) {
            package_sessions
                .get(&node.key.package)
                .expect("every module graph has a request-local package session")
                .checkpoint(1)?;
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
            let fixities = visible_fixities_for_module(&node.key, &index, &declared_fixities);
            dependencies.record(
                DependencyNode::Fixity(node.key.clone()),
                fixities.fingerprint(),
                fixities.dependency_modules(&index, &node.key).into_iter()
                    .map(DependencyNode::Interface).collect(),
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
                            crate::PrimitiveRole::Blake3,
                            crate::PrimitiveRole::ArrayGetBorrowShared,
                            crate::PrimitiveRole::ArrayEmpty,
                            crate::PrimitiveRole::ArrayPushMove,
                            crate::PrimitiveRole::StaticLen,
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
                            crate::PrimitiveRole::IntCheckedDiv,
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
                            (role.is_float() || matches!(role, PrimitiveRole::Memory(_)))
                                && definition == &declaration.key
                        })
                }) {
                    package_sessions
                        .get(&node.key.package)
                        .expect("every module graph has a request-local package session")
                        .checkpoint(1)?;
                    // This exact manifest-bound declaration is implemented by
                    // the runtime. Canonical source has no body. Historical
                    // seed placeholders remain compatible, but are not parsed
                    // as Glorious implementations. An unbound declaration
                    // reaches the missing-body diagnostic below.
                    continue;
                }
                let Some(body_range) = declaration.body else {
                    package_sessions
                        .get(&node.key.package)
                        .expect("every module graph has a request-local package session")
                        .checkpoint(1)?;
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
                        .unwrap_or_else(|| BodySyntax::parse_expression_with_fixities(&lexed, text, body_range, &fixities))
                } else if is_constant {
                    BodySyntax::parse_expression_with_fixities(&lexed, text, body_range, &fixities)
                } else {
                    BodySyntax::parse_with_fixities(&lexed, text, body_range, &fixities)
                };
                let body_session = package_sessions
                    .get_mut(&node.key.package)
                    .expect("every module graph has a request-local package session")
                    .open_body(declaration.key, is_constant, body)?;
                body_session.checkpoint(1)?;
                let body = body_session.syntax();
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
                    TypedBody::elaborate_constant_with_trait_solver(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                        body_trait_solver.fresh_query(),
                    )
                } else if matches!(
                    declaration.syntax.header,
                    ParsedHeader::ValueInitializer { .. }
                ) {
                    TypedBody::elaborate_value_initializer_with_trait_solver(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                        body_trait_solver.fresh_query(),
                    )
                } else {
                    TypedBody::elaborate_control_input(
                        declaration,
                        &body,
                        &index,
                        &signatures,
                        &fixities,
                        body_trait_solver.fresh_query(),
                        true,
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
                let mut core_validation = core.validate_for_control_fusion();
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
                let mut validation_solver = body_trait_solver.fresh_query();
                if let Some(ElaboratedHeader::Callable(signature)) = signatures.definitions.get(&declaration.key) {
                    validation_solver.assume_callable_contract(signature);
                    validation_solver.set_associated_bindings(signature.where_associated_type_bindings.clone(), signature.where_associated_effect_bindings.clone());
                }
                core_validation.extend(
                    core.validate_projection_obligations_in_environment(&signatures, &ambient_projection_bounds,
                        &signatures.definitions.get(&declaration.key).and_then(|header| match header {
                            ElaboratedHeader::Callable(signature) => Some(signature.where_outlives.clone()),
                            _ => None,
                        }).unwrap_or_default(), validation_solver.fresh_query()),
                );
                diagnostics.extend(core_validation.iter().map(|diagnostic| {
                    if diagnostic.code.starts_with("G440") {
                        CompileDiagnostic::source(diagnostic.code, diagnostic.message.clone(), Some(diagnostic.span))
                    } else { CompileDiagnostic::invariant(diagnostic.code, diagnostic.message.clone()) }
                }));
                let ambient_effect_bindings = signatures.definitions.get(&declaration.key)
                    .and_then(|header| match header {
                        ElaboratedHeader::Callable(signature) => Some(signature.where_associated_effect_bindings.as_slice()),
                        _ => None,
                    }).unwrap_or_default();
                let valid = core_validation.is_empty()
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
                body_session.stage_typed(valid, core, ambient_projection_bounds,
                    ambient_effect_bindings.to_vec(), validation_solver)?;
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
                    let method_key = implementation_method_key(implementation.key, &method.name);
                    let body = BodySyntax::parse_with_fixities(&lexed, text, body_range, &fixities);
                    let body_session = package_sessions
                        .get_mut(&node.key.package)
                        .expect("every module graph has a request-local package session")
                        .open_body(method_key, false, body)?;
                    body_session.checkpoint(1)?;
                    let body = body_session.syntax();
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
                        body_trait_solver.fresh_query(),
                        true,
                    );
                    diagnostics.extend(core.diagnostics.iter().map(|diagnostic| {
                        CompileDiagnostic::source(
                            diagnostic.code,
                            diagnostic.message.clone(),
                            Some(diagnostic.span),
                        )
                    }));
                    if implementation_signature.relation.definition
                        == crate::resolution::language_drop_trait_definition()
                        && core.expressions.iter().any(|expression| {
                            matches!(expression.kind, crate::CoreKind::Transfer { .. })
                        })
                    {
                        diagnostics.push(CompileDiagnostic::source(
                            "G4197",
                            "custom `Drop` destructor cannot perform a label transfer or otherwise expose control",
                            Some(method.span),
                        ));
                    }
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
                    let mut core_validation = core.validate_for_control_fusion();
                    let mut ambient_projection_bounds =
                        implementation_signature.where_bounds.clone();
                    ambient_projection_bounds.push((
                        implementation_signature.self_ty.clone(),
                        implementation_signature.relation.clone(),
                    ));
                    ambient_projection_bounds.extend(method_signature.where_bounds.clone());
                    let mut validation_solver = body_trait_solver.fresh_query();
                    validation_solver.set_lexical_assumptions(ambient_projection_bounds.iter().map(|(subject, relation)| crate::TraitGoal {
                        subject: subject.clone(), relation: relation.clone() }).collect());
                    validation_solver.set_outlives_assumptions(implementation_signature.where_outlives.iter().chain(&method_signature.where_outlives).cloned().collect());
                    validation_solver.set_universal_assumptions(implementation_signature.universal_bounds.iter()
                        .chain(&method_signature.universal_bounds).cloned().collect());
                    validation_solver.set_associated_bindings(
                        implementation_signature.where_associated_type_bindings.iter().chain(&method_signature.where_associated_type_bindings).cloned().collect(),
                        implementation_signature.where_associated_effect_bindings.iter().chain(&method_signature.where_associated_effect_bindings).cloned().collect());
                    core_validation.extend(
                        core.validate_projection_obligations_in_environment(
                            &signatures,
                            &ambient_projection_bounds,
                            &implementation_signature.where_outlives.iter().chain(&method_signature.where_outlives).cloned().collect::<Vec<_>>(),
                            validation_solver.fresh_query(),
                        ),
                    );
                    diagnostics.extend(core_validation.iter().map(|diagnostic| {
                        if diagnostic.code.starts_with("G440") {
                            CompileDiagnostic::source(diagnostic.code, diagnostic.message.clone(), Some(diagnostic.span))
                        } else { CompileDiagnostic::invariant(diagnostic.code, diagnostic.message.clone()) }
                    }));
                    let mut ambient_effect_bindings = implementation_signature.where_associated_effect_bindings.clone();
                    ambient_effect_bindings.extend(method_signature.where_associated_effect_bindings.clone());
                    let valid = core_validation.is_empty()
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
                    body_session.stage_typed(valid, core, ambient_projection_bounds,
                        ambient_effect_bindings, validation_solver)?;
                }
            }
        }
        let mut staged_bodies = package_sessions
            .into_values()
            .map(PackageSession::finish)
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        // Every demanded body has crossed typing before any ownership check
        // or MIR lowering begins. Inter-body contracts can now be derived
        // from this complete immutable batch without source-order guessing.
        let abort_primitive = runtime_manifest.as_ref()
            .and_then(|manifest| manifest.primitives.get(&PrimitiveRole::Abort)).copied();
        let control_signatures = staged_bodies.iter().filter_map(|staged|
            crate::callable_declarations::body_signature(&signatures, staged.definition)
                .map(|signature| (staged.definition, signature))).collect::<BTreeMap<_, _>>();
        // Resolve and discharge lexical control obligations before deriving
        // the ownership representation. Source contracts are checked on the
        // original program; no representation rewrite may repair invalid use
        // or escape. The transformed program then receives fresh analyses.
        let mut original_resources = BTreeMap::new();
        let unchanged_control = {
            let control_bodies = staged_bodies.iter().filter_map(|staged|
                control_signatures.get(&staged.definition).map(|signature| (staged.definition,
                    crate::callable_control::ControlBody { body: &staged.core, signature, interface: &signatures })))
                .collect::<BTreeMap<_, _>>();
            let budgets = staged_bodies.iter().map(|staged| (staged.definition, staged.budget.clone())).collect::<BTreeMap<_, _>>();
            let summaries = crate::callable_control::derive_fusion_summaries_with_check(
                &control_bodies, Default::default(), &mut |definition, cost|
                    session.checkpoint_in(&budgets[&definition], cost))?;
            let bound = summaries.bind(&control_bodies).map_err(|reason| ServiceError::Failed(vec![
                CompileDiagnostic::invariant("G4180", format!("staged control batch failed validation: {reason:?}"))]))?;
            let mut control_captures = crate::escape::ControlCaptures::default();
            for staged in &staged_bodies {
                if !staged.valid || !control_bodies.contains_key(&staged.definition) { continue; }
                session.checkpoint_in(&staged.budget, 0)?;
                let facts = crate::core_continuations::CoreContinuations::derive_with_invocations(
                    &staged.core, bound.body(staged.definition))
                    .map_err(|error| ServiceError::Failed(vec![CompileDiagnostic::invariant(error.code, error.message)]))?;
                let (flow, escapes, valid) = staged.check_resources(&signatures, abort_primitive, Arc::new(facts), &mut diagnostics);
                if valid {
                    control_captures.include(staged.definition, &staged.core, &escapes).map_err(|error|
                        ServiceError::Failed(vec![CompileDiagnostic::invariant("G4180", error)]))?;
                }
                original_resources.insert(staged.definition, (flow, valid));
            }
            let mut transformed = BTreeMap::new();
            for staged in &staged_bodies {
                if !staged.valid || !control_bodies.contains_key(&staged.definition) { continue; }
                if !original_resources.get(&staged.definition).is_some_and(|(_, valid)| *valid) { continue; }
                session.checkpoint_in(&staged.budget, 0)?;
                match crate::core::control_fusion::transform(staged.definition, &bound, &control_captures) {
                    Ok(Some(core)) => {
                        session.checkpoint_in(&staged.budget, core.expressions.len() as u64 + 1)?;
                        transformed.insert(staged.definition, core);
                    }
                    Ok(_) => {}
                    Err(error) => diagnostics.push(CompileDiagnostic::source(error.code, error.message, Some(error.span))),
                }
            }
            let unchanged = transformed.is_empty();
            for staged in &mut staged_bodies {
                if let Some(core) = transformed.remove(&staged.definition) {
                    staged.core = core;
                }
                // Recovered/invalid staged inputs have already published
                // their diagnostics and cannot enter ownership publication.
                // The strict receiving-phase check is for admitted inputs,
                // not a second report of their earlier validation failure.
                if !staged.valid { continue; }
                let errors = staged.core.validate();
                staged.valid &= errors.is_empty();
                diagnostics.extend(errors.into_iter().map(|error| CompileDiagnostic::source(error.code, error.message, Some(error.span))));
            }
            if !unchanged { original_resources.clear(); }
            unchanged.then_some(summaries)
        };
        let control_bodies = staged_bodies.iter().filter_map(|staged|
            control_signatures.get(&staged.definition).map(|signature| (staged.definition,
                crate::callable_control::ControlBody { body: &staged.core, signature, interface: &signatures })))
            .collect::<BTreeMap<_, _>>();
        let control_budgets = staged_bodies.iter().map(|staged| (staged.definition, staged.budget.clone()))
            .collect::<BTreeMap<_, _>>();
        let control_summaries = if let Some(summaries) = unchanged_control { summaries } else {
            crate::callable_control::derive_control_summaries_with_check(
            &control_bodies, Default::default(), &mut |definition, cost|
                session.checkpoint_in(&control_budgets[&definition], cost),
        )? };
        let bound_control = control_summaries.bind(&control_bodies)
            .map_err(|reason| ServiceError::Failed(vec![CompileDiagnostic::invariant("G4180",
                format!("callable control batch failed dependency validation: {reason:?}"))]))?;
        for obligation in bound_control.label_address_obligations() {
            diagnostics.push(CompileDiagnostic::source("G4179",
                "generative labels are proof-only and cannot be addressed through callable inputs", Some(obligation.span))
                .with_fact("label_target", format!("{:?}", obligation.target))
                .with_fact("invocation_site", format!("{:?}", obligation.site)));
        }
        let continuations = staged_bodies.iter()
            .filter(|staged| !original_resources.contains_key(&staged.definition)).map(|staged| {
            crate::core_continuations::CoreContinuations::derive_with_invocations(
                &staged.core, bound_control.body(staged.definition),
            ).map(|facts| (staged.definition, Arc::new(facts)))
        }).collect::<Result<BTreeMap<_, _>, _>>()
            .map_err(|error| ServiceError::Failed(vec![CompileDiagnostic::invariant(error.code, error.message)]))?;
        let mut body_products = Vec::with_capacity(staged_bodies.len());
        for staged in staged_bodies {
            // Observe cancellation at the new phase boundary without
            // changing the existing semantic work charges or body budget.
            session.checkpoint_in(&staged.budget, 0)?;
            if let Some((flow, valid)) = original_resources.remove(&staged.definition) {
                let valid = valid && staged.valid;
                let StagedTypedBody { definition, is_constant, core, budget, .. } = staged;
                body_products.push(PublishedBody { definition, is_constant, valid, core, flow, budget });
            } else {
                let facts = continuations[&staged.definition].clone();
                body_products.push(staged.analyze(&signatures, abort_primitive, facts, &mut diagnostics));
            }
        }
        for PublishedBody {
            definition,
            is_constant,
            valid,
            core,
            flow,
            budget,
        } in body_products
        {
            // Lowering remains owned by the completed body rather than by an
            // ambient request counter.  The child propagates every charge
            // through body and package to the request cap.
            let lowering_budget = budget.child("lowering", budget.ceiling());
            session.checkpoint_in(&lowering_budget, 1)?;
            if !valid {
                continue;
            }
            match crate::ownership_mir::OwnershipMir::from_typed_with_frozen_solver(definition, &core, &flow, Some(&signatures), Some(&body_trait_solver)) {
                Ok((ownership, result)) => {
                    lowering.insert(definition, crate::specialized_mir::SpecializationInput { ownership, result, is_constant });
                }
                Err(error) => diagnostics.push(CompileDiagnostic::invariant("G6001", error.0)),
            }
        }
        if !diagnostics.is_empty() {
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        }
        // Every concrete source instance crosses this distinct phase. No
        // downstream representation failure retries source-shape lowering.
        let mut destruction = crate::destruction::Planner::new(&signatures);
        let (specialized, instance_graph) = crate::specialized_mir::SpecializedProgram::discover(entry, &lowering, &signatures, runtime_primitives.as_ref(), self.instance_limits, &mut destruction)
            .map_err(|error| {
                let diagnostic = match error {
                    crate::specialized_mir::SpecializedDiscoveryError::Invalid(error) => CompileDiagnostic::invariant("G7032", error.0),
                    crate::specialized_mir::SpecializedDiscoveryError::Limit(error) => CompileDiagnostic::resource("G7031", format!("instance discovery limit: {error:?}")),
                    crate::specialized_mir::SpecializedDiscoveryError::NonAddressableLabel { definition, ty } => CompileDiagnostic::source(
                        "G4179", "generative labels are proof-only and cannot be addressed", None)
                        .with_fact("specialized_body", format!("{definition:?}"))
                        .with_fact("label_type", format!("{ty:?}")),
                };
                failed(input_fingerprint, vec![diagnostic], &source_lengths)
            })?;
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
        let cleanup = crate::cleanup_mir::CleanupProgram::lower(&specialized, &instance_graph, &signatures, &destruction)
            .map_err(|error| failed(input_fingerprint, vec![CompileDiagnostic::invariant("G7040", error.0)], &source_lengths))?;
        drop(lowering);
        drop(specialized);
        let runtime = crate::runtime_mir::RuntimeProgram::lower(&cleanup, &signatures, runtime_primitives.as_ref())
            .map_err(|error| failed(input_fingerprint, vec![CompileDiagnostic::invariant("G7041", error.0)], &source_lengths))?;
        drop(cleanup);
        if !diagnostics.is_empty() {
            return Err(failed(input_fingerprint, diagnostics, &source_lengths));
        }
        if let Some(cycle) = runtime.constant_cycle() {
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
        // Charge the backend stage before register lowering and verification,
        // not after that work has already completed. Retain one budget owner
        // through final emission and publication.
        let emission_budget = session.emission_budget();
        let backend_cost = u64::try_from(runtime.reachable_function_keys().len())
            .expect("reachable function count fits in request work budget")
            .saturating_add(1);
        session.checkpoint_in(&emission_budget, backend_cost)?;
        let program = crate::vm_lir::VmLirProgram::lower(&runtime).map_err(|error| {
            let mut diagnostic = CompileDiagnostic::invariant("G7042", format!("VM LIR lowering rejected Runtime MIR: {error:?}"));
            if let crate::VmArtifactError::UnprovenTailCarrier { function, pc, register, .. } = &error {
                let definition = runtime.instances().values().find(|instance| instance.executable == *function)
                    .map_or(*function, |instance| instance.key.callable);
                diagnostic = diagnostic.with_fact("vm-function", function.0.to_string())
                    .with_fact("vm-pc", pc.to_string()).with_fact("vm-register", register.to_string());
                if let Some(declaration) = graphs.values().flat_map(|graph| graph.modules.values())
                    .flat_map(|node| &node.interface.interface.definitions).find(|declaration| declaration.key == definition) {
                    let name = declaration.name.as_deref().unwrap_or("<anonymous>");
                    diagnostic.message.push_str(&format!(" in `{name}`"));
                    diagnostic = diagnostic.with_related_location("source callable", SourceSpan {
                        file: declaration.span.file, start: declaration.span.start, end: declaration.span.end,
                    });
                }
            }
            failed(input_fingerprint, vec![diagnostic], &source_lengths)
        })?;
        drop(runtime);
        for (definition, function) in program.functions() {
            dependencies.record(DependencyNode::Mir(*definition), function.fingerprint(), vec![DependencyNode::Core(function.definition())]);
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
        let emission =
            EmissionSession::new(program, runtime_manifest.clone(), emission_budget);
        emission.checkpoint(session, 0)?;
        let artifact_dependencies = emission.mir_dependencies();
        let artifact = emission
            .emit(|capability| {
                snapshot
                    .world()
                    .capability_manifest
                    .iter()
                    .any(|grant| grant == capability)
            })
            .map_err(|error| {
                let diagnostic = match error {
                    EmissionFailure::Emit(error) => CompileDiagnostic::invariant(
                        "G7004",
                        format!("VM emission rejected LIR: {error}"),
                    ),
                    EmissionFailure::UnauthorizedCapability(capability) => {
                        CompileDiagnostic::verification(
                            "G7033",
                            format!(
                                "emitted host capability `{capability}` is not granted by the request manifest"
                            ),
                        )
                    }
                    EmissionFailure::Verify(error) => CompileDiagnostic::verification(
                        "G7005",
                        format!("VM verification rejected emitted artifact: {error}"),
                    ),
                };
                failed(input_fingerprint, vec![diagnostic], &source_lengths)
            })?;
        dependencies.record(
            DependencyNode::Artifact(snapshot.world().root_package.clone()),
            artifact.fingerprint(),
            artifact_dependencies,
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
#[cfg(test)]
fn materialize_concrete_instances(
    functions: &mut BTreeMap<DefKey, MirFunction>,
    graph: &InstanceGraph,
    signatures: &ElaboratedInterface,
    runtime_primitives: Option<&BTreeMap<DefKey, crate::PrimitiveRole>>,
    destruction: &mut crate::destruction::Planner<'_>,
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
        if crate::destruction::is_glue(&key) {
            functions.insert(executable, destruction.materialize(&key)?);
            targets.insert(key.clone(), executable);
            instances.insert(executable, MirInstance { key, executable });
            continue;
        }
        let base = functions
            .get(&key.callable)
            .cloned()
            .ok_or_else(|| format!("instance body is unavailable for {:?}", key.callable))?;
        let mut specialized = base;
        specialized.definition = executable;
        let body_arguments = materialization_body_arguments(&key, signatures)?;
        specialize_mir_local_types(&mut specialized, &body_arguments);
        normalize_materialized_associated_projections(&mut specialized, signatures)?;
        materialize_deferred_scalar_operations(&mut specialized)?;
        register_specialized_nominal_copy_descriptors(&mut specialized, signatures)?;
        targets.insert(key.clone(), executable);
        functions.insert(executable, specialized);
        materialize_lifted_callable_instances(
            functions,
            &key,
            executable,
            &body_arguments,
            signatures,
        )?;
        instances.insert(executable, MirInstance { key, executable });
    }
    finalize_materialized_instances(functions, graph, signatures, destruction, instances, targets)
}


#[cfg(test)]
fn finalize_materialized_instances(
    functions: &mut BTreeMap<DefKey, MirFunction>, graph: &InstanceGraph,
    signatures: &ElaboratedInterface, destruction: &mut crate::destruction::Planner<'_>,
    instances: BTreeMap<DefKey, MirInstance>, targets: BTreeMap<InstanceKey, DefKey>,
) -> Result<BTreeMap<DefKey, MirInstance>, String> {
    let mut glue_definitions = instances.iter().filter_map(|(definition, instance)|
        crate::destruction::is_glue(&instance.key).then_some(*definition)).collect::<BTreeSet<_>>();
    glue_definitions.extend(destruction.seal_callable_environments(functions)?);
    for function in functions.values_mut() {
        if !glue_definitions.contains(&function.definition) {
            destruction.elaborate(function)?;
            destruction.seal_native_operations(function)?;
        }
    }
    let mut unmaterialized_trait_calls = BTreeMap::new();
    for function in functions.values_mut() {
        for block in &mut function.blocks {
            for instruction in &mut block.instructions {
                let receiver = match &*instruction {
                    crate::MirInstruction::Call { arguments, dst, .. } => arguments
                        .first()
                        .and_then(|local| function.locals.get(local.0 as usize))
                        .map(|local| local.ty.clone())
                        .or_else(|| {
                            function
                                .locals
                                .get(dst.0 as usize)
                                .map(|local| local.ty.clone())
                        }),
                    crate::MirInstruction::MakeCallable { dst, .. } => function
                        .locals
                        .get(dst.0 as usize)
                        .and_then(|local| match &local.ty {
                            Type::Callable {
                                parameters, result, ..
                            } => Some(parameters.first().unwrap_or(result).clone()),
                            _ => None,
                        }),
                    _ => None,
                };
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
                if let Some(deferred) = trait_instance
                    .as_ref()
                    .and_then(|instance| instance.deferred.clone())
                {
                    let mut solver = TraitSolver::new(signatures);
                    match solver.select_method(
                        TraitGoal {
                            relation: deferred.relation,
                            subject: deferred.subject,
                        },
                        &deferred.name,
                        &trait_instance
                            .as_ref()
                            .expect("deferred trait method has an instance")
                            .method_arguments,
                    ) {
                        crate::TraitMethodAnswer::Selected {
                            evidence, method, ..
                        } => {
                            let instance = trait_instance
                                .as_mut()
                                .expect("deferred trait method has an instance");
                            instance.evidence = evidence;
                            instance.deferred = None;
                            *callee = method;
                        }
                        // An unmaterialized generic source template cannot
                        // select an implementation yet. It is retained only
                        // as a diagnostic template and never reaches the VM.
                        crate::TraitMethodAnswer::NoSolution
                        | crate::TraitMethodAnswer::Ambiguous
                        | crate::TraitMethodAnswer::Overflow
                        | crate::TraitMethodAnswer::Refuted { .. }
                        | crate::TraitMethodAnswer::MissingMethod { .. }
                        | crate::TraitMethodAnswer::MethodArity { .. } => {
                            *trait_instance = None;
                            continue;
                        }
                    }
                }
                if trait_instance.is_some() {
                    let (evidence, trait_arguments, method_arguments) = {
                        let instance = trait_instance
                            .as_ref()
                            .expect("trait method identity was checked");
                        (
                            instance.evidence,
                            instance.trait_arguments.clone(),
                            instance.method_arguments.clone(),
                        )
                    };
                    let key = trait_method_instance_key(
                        evidence,
                        *callee,
                        &trait_arguments,
                        &method_arguments,
                        trait_method_executable_receiver(
                            evidence,
                            *callee,
                            receiver.as_ref(),
                            signatures,
                        )?
                        .as_ref(),
                    );
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
                    let Some(target) = targets.get(&key) else {
                        // All source bodies are checked/lowered, but the
                        // instance graph starts only at demanded roots. An
                        // unused body may therefore contain a concrete trait
                        // call with no executable specialization. Defer this
                        // error until all call edges have been rewritten;
                        // never admit it if its owner reaches the program.
                        unmaterialized_trait_calls
                            .entry(function.definition)
                            .or_insert(key);
                        generic_arguments.clear();
                        *trait_instance = None;
                        continue;
                    };
                    *callee = *target;
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
    if !unmaterialized_trait_calls.is_empty() {
        let roots = graph
            .roots()
            .keys()
            .map(|key| targets.get(key).copied().unwrap_or(key.callable));
        for definition in reachable_function_keys(functions, roots) {
            if let Some(key) = unmaterialized_trait_calls.get(&definition) {
                return Err(format!(
                    "selected trait-method instance was not materialized: {key:?}"
                ));
            }
        }
    }
    Ok(instances)
}

/// Give every closure lifted from a concrete generic callable instance its
/// own executable MIR body. A lifted closure is a separate function, but its
/// capture ABI and body retain the enclosing callable's generic placeholders.
/// Reusing the source template's lifted definition would therefore leave the
/// VM with a callable whose types disagree with its materialized environment.
///
/// The closure identity includes the enclosing instance and its source lifted
/// definition. Nested closures are processed transitively because they inherit
/// the same enclosing substitutions.
#[cfg(test)]
fn materialize_lifted_callable_instances(
    functions: &mut BTreeMap<DefKey, MirFunction>,
    instance: &InstanceKey,
    executable: DefKey,
    body_arguments: &[GenericArgument],
    signatures: &ElaboratedInterface,
) -> Result<(), String> {
    let mut targets = BTreeMap::<DefKey, DefKey>::new();
    let mut pending = vec![executable];

    while let Some(definition) = pending.pop() {
        let discovered = {
            let function = functions.get_mut(&definition).ok_or_else(|| {
                format!(
                    "materialized callable body disappeared before lifted closures were specialized: {definition:?}"
                )
            })?;
            let mut discovered = Vec::new();
            for block in &mut function.blocks {
                for instruction in &mut block.instructions {
                    let MirInstruction::MakeCallable {
                        callee,
                        environment: Some(_),
                        ..
                    } = instruction
                    else {
                        continue;
                    };
                    let source = *callee;
                    let (target, is_new) = match targets.get(&source).copied() {
                        Some(target) => (target, false),
                        None => {
                            let target = crate::mir::materialized_lifted_callable_definition(
                                instance, source,
                            );
                            targets.insert(source, target);
                            (target, true)
                        }
                    };
                    *callee = target;
                    if is_new {
                        discovered.push((source, target));
                    }
                }
            }
            discovered
        };

        for (source, target) in discovered {
            if functions.contains_key(&target) {
                return Err(format!(
                    "specialized lifted callable identity collided with an existing MIR function: {target:?}"
                ));
            }
            let mut specialized = functions.get(&source).cloned().ok_or_else(|| {
                format!("lifted callable body is unavailable for specialization: {source:?}")
            })?;
            specialized.definition = target;
            specialize_mir_local_types(&mut specialized, body_arguments);
            normalize_materialized_associated_projections(&mut specialized, signatures)?;
            materialize_deferred_scalar_operations(&mut specialized)?;
            register_specialized_nominal_copy_descriptors(&mut specialized, signatures)?;
            functions.insert(target, specialized);
            pending.push(target);
        }
    }
    Ok(())
}

/// Translate the executable instance identity for a selected trait method
/// back into that implementation body's binder order.  A method instance key
/// intentionally includes the trait relation arguments and an evidence digest
/// so distinct dictionaries cannot alias.  Neither belongs to the method
/// body's generic substitution: its slots are implementation binders followed
/// by method binders.  Treating the executable key itself as that substitution
/// therefore shifted every method argument by the trait arity.
pub(crate) fn materialization_body_arguments(
    key: &InstanceKey,
    signatures: &ElaboratedInterface,
) -> Result<Vec<GenericArgument>, String> {
    for (implementation_definition, header) in &signatures.definitions {
        let ElaboratedHeader::Implementation(implementation) = header else {
            continue;
        };
        for (name, method) in &implementation.methods {
            if implementation_method_key(*implementation_definition, name) != key.callable {
                continue;
            }
            let relation_arguments = implementation.relation.arguments.len();
            let method_arguments = method.generic_kinds.len();
            const EVIDENCE_ARGUMENTS: usize = 8;
            let without_receiver = relation_arguments
                .checked_add(method_arguments)
                .and_then(|count| count.checked_add(EVIDENCE_ARGUMENTS))
                .ok_or_else(|| "trait method instance argument count overflowed".to_owned())?;
            let with_receiver = without_receiver
                .checked_add(1)
                .ok_or_else(|| "trait method instance argument count overflowed".to_owned())?;
            let receiver = if key.arguments().len() == with_receiver {
                match &key.arguments()[relation_arguments + method_arguments] {
                    GenericArgument::Type(receiver) => Some(receiver),
                    _ => return Err("trait method executable key has a non-type receiver".into()),
                }
            } else if key.arguments().len() == without_receiver {
                None
            } else {
                return Err("selected trait method instance has an invalid executable key".into());
            };
            let relation_values = &key.arguments()[..relation_arguments];
            return crate::callable_declarations::implementation_arguments(signatures, implementation,
                relation_values, &key.arguments()[relation_arguments..relation_arguments + method_arguments], receiver);
        }
    }
    Ok(key.arguments().to_vec())
}

/// Rewrite scalar operations whose source templates deliberately retain a
/// generic type parameter until instance materialization.  Runtime primitive
/// declarations are sealed and cannot themselves be materialized; ordinary
/// source wrappers therefore carry this deferred operation through Typed Core
/// and MIR until their enclosing instance fixes the local register types.
#[cfg(test)]
fn materialize_deferred_scalar_operations(function: &mut MirFunction) -> Result<(), String> {
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            match instruction {
                MirInstruction::DeferredLiteral { dst, text } => {
                    let scalar = function
                        .locals
                        .get(dst.0 as usize)
                        .map(|local| local.ty.clone())
                        .ok_or_else(|| {
                            "deferred literal destination is not a MIR local".to_owned()
                        })?;
                    let Type::Scalar(scalar) = scalar else {
                        return Err(
                            "generic numeric literal did not specialize to a scalar type".into(),
                        );
                    };
                    *instruction =
                        crate::mir::materialize_numeric_literal(*dst, text, scalar)?;
                }
                MirInstruction::BitAndGeneric { dst, left, right } => {
                    let scalar = function
                        .locals
                        .get(dst.0 as usize)
                        .map(|local| local.ty.clone())
                        .ok_or_else(|| {
                            "deferred bitwise-and destination is not a MIR local".to_owned()
                        })?;
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
                        Type::Scalar(scalar) => MirInstruction::IntIntrinsic {
                            dst: *dst,
                            primitive: PrimitiveRole::IntBitAnd,
                            scalar,
                            arguments: vec![*left, *right],
                        },
                        other => {
                            return Err(format!(
                                "generic int bitwise-and instance has unsupported scalar result {other:?}"
                            ));
                        }
                    };
                }
                MirInstruction::IntGenericIntrinsic {
                    dst,
                    primitive,
                    arguments,
                } => {
                    let source = *arguments.first().ok_or_else(|| {
                        "deferred integer primitive has no source argument".to_owned()
                    })?;
                    let Type::Scalar(scalar) = function
                        .locals
                        .get(source.0 as usize)
                        .map(|local| local.ty.clone())
                        .ok_or_else(|| {
                            "deferred integer primitive source is not a MIR local".to_owned()
                        })?
                    else {
                        return Err("generic integer primitive source is not a scalar".into());
                    };
                    *instruction = MirInstruction::IntIntrinsic {
                        dst: *dst,
                        primitive: *primitive,
                        scalar,
                        arguments: arguments.clone(),
                    };
                }
                _ => {}
            }
        }
    }
    Ok(())
}

pub(crate) use crate::callable_declarations::trait_method_executable_receiver;

/// Canonicalize a solver-selected trait method into the shared instance-key
/// vocabulary. Trait and method arguments remain ordered type slots; the
/// evidence digest is appended as eight const slots so distinct coherent
/// implementations can never share an executable body.
pub(crate) fn trait_method_instance_key(
    evidence: DefKey,
    method: DefKey,
    trait_arguments: &[GenericArgument],
    method_arguments: &[GenericArgument],
    receiver: Option<&Type>,
) -> Result<InstanceKey, crate::InstanceKeyError> {
    let mut arguments = trait_arguments.to_vec();
    arguments.extend_from_slice(method_arguments);
    if let Some(receiver) = receiver {
        arguments.push(GenericArgument::Type(receiver.clone()));
    }
    let mut kinds = arguments
        .iter()
        .map(instance_argument_kind)
        .collect::<Vec<_>>();
    for bytes in evidence.0.as_bytes().chunks_exact(4) {
        arguments.push(GenericArgument::ConstInteger(u32::from_le_bytes([
            bytes[0], bytes[1], bytes[2], bytes[3],
        ]).into()));
        kinds.push(crate::GenericKind::Const(crate::ConstKind::U32));
    }
    InstanceKey::new(method, &kinds, arguments)
}

use crate::callable_declarations::instance_argument_kind;

/// Stage 0's first materializer specializes every local signature.  The
/// general instruction-type substitution follows in the same product
/// boundary; direct scalar calls already obtain fully concrete VM registers.
#[cfg(test)]
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
                crate::MirInstruction::MemoryIntrinsic { types, .. } => {
                    *types = types.iter().map(|ty| specialize_type(ty, arguments)).collect();
                }
                crate::MirInstruction::MakeArray { element_type, .. }
                | crate::MirInstruction::ProjectArray { element_type, .. }
                | crate::MirInstruction::ArrayGetBorrowShared { element_type, .. }
                | crate::MirInstruction::ArrayEmpty { element_type, .. }
                | crate::MirInstruction::ArrayPushMove { element_type, .. } => {
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
                if let Some(deferred) = &mut instance.deferred {
                    deferred.relation.arguments = deferred
                        .relation
                        .arguments
                        .iter()
                        .map(|argument| specialize_generic_argument(argument, arguments))
                        .collect();
                    deferred.subject = specialize_type(&deferred.subject, arguments);
                }
            }
        }
    }
    // Control-site tables are frozen MIR metadata, not an advisory cache.
    // Keep their type witnesses in lockstep with the executable instruction
    // stream when a generic template becomes a concrete instance.
    for handler in &mut function.control.handlers {
        handler.effect_arguments = handler
            .effect_arguments
            .iter()
            .map(|argument| specialize_generic_argument(argument, arguments))
            .collect();
        handler.resume_type = specialize_type(&handler.resume_type, arguments);
    }
    for perform in &mut function.control.performs {
        perform.effect_arguments = perform
            .effect_arguments
            .iter()
            .map(|argument| specialize_generic_argument(argument, arguments))
            .collect();
    }
}

/// A template can contain a `T` local whose concrete nominal layout becomes
/// knowable only while materializing an instance. Re-freeze that layout before
/// the specialized MIR reaches VM emission.
#[cfg(test)]
pub(crate) fn register_specialized_nominal_copy_descriptors(
    function: &mut MirFunction,
    signatures: &ElaboratedInterface,
) -> Result<(), String> {
    let mut roots = function
        .locals
        .iter()
        .map(|local| local.ty.clone())
        .chain(std::iter::once(function.result.clone()))
        .chain(function.blocks.iter().flat_map(|block| &block.instructions).flat_map(|instruction| {
            match instruction { MirInstruction::MemoryIntrinsic { types, .. } => types.as_slice(), _ => &[] }
        }).cloned())
        .collect::<Vec<_>>();
    let native_roots = function.blocks.iter().flat_map(|block| &block.instructions)
        .filter_map(|instruction| match instruction {
            MirInstruction::HostCall { parameters, result, .. } => Some((parameters, result)),
            _ => None,
        })
        .flat_map(|(parameters, result)| parameters.iter().chain(std::iter::once(result)))
        .cloned().collect::<Vec<_>>();
    roots.extend(crate::mir::native_contract_nominals(&native_roots, signatures)?);
    let mut building = vec![];
    for root in roots {
        register_specialized_nominal_copy_type(&root, function, signatures, &mut building);
    }
    // Several pre-specialization descriptors may collapse to one concrete
    // layout when their generic witnesses are substituted. Keep one exact
    // copy of that layout; retain conflicting duplicates for the structural
    // validator to reject rather than masking malformed metadata.
    let mut canonical = Vec::with_capacity(function.nominal_copy_descriptors.len());
    for descriptor in std::mem::take(&mut function.nominal_copy_descriptors) {
        match canonical.iter().find(|existing: &&crate::MirNominalCopyDescriptor| {
            existing.definition == descriptor.definition && existing.arguments == descriptor.arguments
        }) {
            Some(existing) if *existing == descriptor => {}
            _ => canonical.push(descriptor),
        }
    }
    function.nominal_copy_descriptors = canonical;
    Ok(())
}

#[cfg(test)]
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
        Type::Array(element) | Type::FixedArray { element, .. } | Type::StaticData { element, .. } => {
            register_specialized_nominal_copy_type(element, function, signatures, building)
        }
        Type::Callable {
            parameters, result, ..
        } => {
            for parameter in parameters {
                register_specialized_nominal_copy_type(&crate::core::open_hrtb_callable_body_type(parameter.clone(), 0), function, signatures, building);
            }
            register_specialized_nominal_copy_type(&crate::core::open_hrtb_callable_body_type((**result).clone(), 0), function, signatures, building);
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
                    layout: crate::signature::ElaboratedNominalLayout::Struct(_) | crate::signature::ElaboratedNominalLayout::TupleStruct(_),
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
            let Some(source_contract) = signatures.definitions.get(definition)
                .and_then(|header| crate::signature::nominal_contract_fingerprint(*definition, header)) else {
                return;
            };
            building.push(key);
            for variant in &variants {
                for field in variant {
                    register_specialized_nominal_copy_type(field, function, signatures, building);
                }
            }
            building.pop();
            // A nested field traversal can register this same concrete
            // layout before its outer root completes (for example two
            // library collection wrappers sharing `Vec<T>`). Re-check at the
            // mutation point so specialization remains idempotent while the
            // MIR validator can continue rejecting genuinely malformed
            // duplicate metadata.
            if function.nominal_copy_descriptors.iter().any(|descriptor| {
                descriptor.definition == *definition && descriptor.arguments == *arguments
            }) {
                return;
            }
            function
                .nominal_copy_descriptors
                .push(crate::MirNominalCopyDescriptor {
                    definition: *definition,
                    source_contract,
                    is_enum: matches!(signatures.definitions.get(definition),
                        Some(ElaboratedHeader::Nominal { layout: crate::signature::ElaboratedNominalLayout::Enum(_), .. })),
                    arguments: arguments.clone(),
                    variants,
                });
        }
        Type::Reference { .. }
        | Type::RawPointer { .. }
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
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
#[cfg(test)]
fn specialize_mir_pattern(pattern: &mut crate::MirPattern, arguments: &[GenericArgument]) {
    match pattern {
        crate::MirPattern::Any | crate::MirPattern::Literal(_) => {}
        crate::MirPattern::Tuple(elements) => {
            for element in elements {
                specialize_mir_pattern(element, arguments);
            }
        }
        crate::MirPattern::Array { element, elements, .. } => {
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

pub(crate) fn specialize_type(value: &Type, arguments: &[GenericArgument]) -> Type {
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
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(specialize_type(element, arguments)),
            length: Box::new(specialize_generic_argument(length, arguments)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(specialize_type(pointee, arguments)),
        },
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
        Type::Callable { contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable { contract: Box::new(contract.instantiate(arguments)),
            safety: *safety,
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
                (GenericArgument::ConstInteger(value), expected) if value.kind() == *expected => {
                    Some(Type::ConstInteger(*value))
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

pub(crate) fn specialize_effect_row(
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
        tails: value.tails.clone(),
    };
    row.substitute_tails(|tail| match tail {
        crate::EffectTail::Generic(index) => match arguments.get(index as usize) {
            // Instance arguments share the closed specialization environment;
            // nested type/const identities still need materialization here.
            Some(GenericArgument::EffectRow(row)) => Some(specialize_effect_row(row, arguments)), _ => None,
        }, _ => None,
    });
    row.canonicalized()
}

pub(crate) fn specialize_generic_argument(
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
                (GenericArgument::ConstInteger(value), expected) => value.kind() == *expected,
                (GenericArgument::ConstQuantity(_), crate::ConstKind::Quantity) => true,
                (GenericArgument::ConstGeneric { kind: found, .. }, expected) => found == expected,
                _ => false,
            })
            .cloned()
            .unwrap_or_else(|| value.clone()),
        GenericArgument::ConstIntegerExpr(value) => crate::types::integer_const_argument(value.substitute_arguments(arguments)),
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(specialize_type(subject, arguments)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| specialize_generic_argument(argument, arguments))
                .collect(),
            name: name.clone(),
            kind: *kind,
        },
        value => value.clone(),
    }
}

/// A generic source body can legitimately retain an associated projection
/// until its direct-call instance fixes the implementation subject. Resolve
/// delayed const and effect-row projections after ordinary binder substitution
/// and before the clone becomes executable MIR. This is deliberately a
/// separate pass from source elaboration: using the original template
/// arguments here would select the wrong implementation for a concrete
/// instance.
#[cfg(test)]
fn normalize_materialized_associated_projections(
    function: &mut MirFunction,
    signatures: &ElaboratedInterface,
) -> Result<(), String> {
    let mut solver = TraitSolver::new(signatures);
    function.result = normalize_materialized_type(&function.result, &mut solver)?;
    for local in &mut function.locals {
        local.ty = normalize_materialized_type(&local.ty, &mut solver)?;
    }
    for descriptor in &mut function.nominal_copy_descriptors {
        descriptor.arguments = descriptor
            .arguments
            .iter()
            .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
            .collect::<Result<_, _>>()?;
        for variant in &mut descriptor.variants {
            *variant = variant
                .iter()
                .map(|field| normalize_materialized_type(field, &mut solver))
                .collect::<Result<_, _>>()?;
        }
    }
    for block in &mut function.blocks {
        for instruction in &mut block.instructions {
            match instruction {
                MirInstruction::MakeArray { element_type, .. }
                | MirInstruction::ProjectArray { element_type, .. } => {
                    *element_type = normalize_materialized_type(element_type, &mut solver)?;
                }
                MirInstruction::MakeRecord { field_types, .. }
                | MirInstruction::MakeEnum { field_types, .. } => {
                    *field_types = field_types
                        .iter()
                        .map(|field| normalize_materialized_type(field, &mut solver))
                        .collect::<Result<_, _>>()?;
                }
                MirInstruction::ProjectRecord { field_type, .. }
                | MirInstruction::ProjectTuple { field_type, .. }
                | MirInstruction::UpdateRecord { field_type, .. } => {
                    *field_type = normalize_materialized_type(field_type, &mut solver)?;
                }
                MirInstruction::PatternTest { pattern, .. } => {
                    normalize_materialized_pattern(pattern, &mut solver)?;
                }
                MirInstruction::Perform {
                    effect_arguments, ..
                } => {
                    *effect_arguments = effect_arguments
                        .iter()
                        .map(|argument| {
                            normalize_materialized_generic_argument(argument, &mut solver)
                        })
                        .collect::<Result<_, _>>()?;
                }
                MirInstruction::InstallHandler {
                    effect_arguments,
                    resume_type,
                    ..
                } => {
                    *effect_arguments = effect_arguments
                        .iter()
                        .map(|argument| {
                            normalize_materialized_generic_argument(argument, &mut solver)
                        })
                        .collect::<Result<_, _>>()?;
                    *resume_type = normalize_materialized_type(resume_type, &mut solver)?;
                }
                MirInstruction::HostCall {
                    parameters, result, ..
                } => {
                    *parameters = parameters
                        .iter()
                        .map(|parameter| normalize_materialized_type(parameter, &mut solver))
                        .collect::<Result<_, _>>()?;
                    *result = normalize_materialized_type(result, &mut solver)?;
                }
                MirInstruction::MakeCallable {
                    environment: Some(environment),
                    ..
                } => {
                    for capture in &mut environment.captures {
                        capture.ty = normalize_materialized_type(&capture.ty, &mut solver)?;
                    }
                }
                _ => {}
            }
            let (generic_arguments, trait_instance) = match instruction {
                MirInstruction::Call {
                    generic_arguments,
                    trait_instance,
                    ..
                }
                | MirInstruction::MakeCallable {
                    generic_arguments,
                    trait_instance,
                    ..
                } => (generic_arguments, trait_instance),
                _ => continue,
            };
            *generic_arguments = generic_arguments
                .iter()
                .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
                .collect::<Result<_, _>>()?;
            if let Some(instance) = trait_instance {
                instance.trait_arguments = instance
                    .trait_arguments
                    .iter()
                    .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
                    .collect::<Result<_, _>>()?;
                instance.method_arguments = instance
                    .method_arguments
                    .iter()
                    .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
                    .collect::<Result<_, _>>()?;
            }
        }
    }
    // Associated-const normalization has the same frozen-control boundary as
    // generic specialization above.  Normalize the duplicated witnesses too,
    // so MIR validation can prove table and instruction agreement.
    for handler in &mut function.control.handlers {
        handler.effect_arguments = handler
            .effect_arguments
            .iter()
            .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
            .collect::<Result<_, _>>()?;
        handler.resume_type = normalize_materialized_type(&handler.resume_type, &mut solver)?;
    }
    for perform in &mut function.control.performs {
        perform.effect_arguments = perform
            .effect_arguments
            .iter()
            .map(|argument| normalize_materialized_generic_argument(argument, &mut solver))
            .collect::<Result<_, _>>()?;
    }
    Ok(())
}

pub(crate) fn normalize_materialized_type(value: &Type, solver: &mut TraitSolver) -> Result<Type, String> {
    Ok(match value {
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(normalize_materialized_type(element, solver)?),
            length: Box::new(normalize_materialized_generic_argument(length, solver)?),
        },
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| normalize_materialized_type(field, solver))
                .collect::<Result<_, _>>()?,
        ),
        Type::Array(element) => {
            Type::Array(Box::new(normalize_materialized_type(element, solver)?))
        }
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(normalize_materialized_type(pointee, solver)?),
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: *lifetime,
            referent: Box::new(normalize_materialized_type(referent, solver)?),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(normalize_materialized_type(subject, solver)?),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| normalize_materialized_generic_argument(argument, solver))
                .collect::<Result<_, _>>()?,
            name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|argument| normalize_materialized_generic_argument(argument, solver))
                .collect::<Result<_, _>>()?,
        },
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|argument| normalize_materialized_generic_argument(argument, solver))
                .collect::<Result<_, _>>()?,
        },
        Type::Callable { contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable { contract: Box::new(contract.try_map_terms(|value, _| normalize_materialized_generic_argument(&value, solver))?),
            safety: *safety,
            lifetime_binders: *lifetime_binders,
            parameters: parameters
                .iter()
                .map(|parameter| normalize_materialized_type(parameter, solver))
                .collect::<Result<_, _>>()?,
            result: Box::new(normalize_materialized_type(result, solver)?),
            // A materialized callable is an executable signature, rather
            // than a declaration-owned symbolic contract.  In particular a
            // GAT effect row selected for a `for<'a>` callback must be
            // reduced while that callback's binder is live; otherwise the
            // VM sees the projection in the function header but the selected
            // row in its MakeCallable witness.
            effects: normalize_materialized_effect_row(effects, solver, *lifetime_binders)?,
            invocation: *invocation,
        },
        value => value.clone(),
    })
}

pub(crate) fn normalize_materialized_effect_row(
    value: &crate::EffectRow,
    solver: &mut TraitSolver,
    lifetime_binders: u32,
) -> Result<crate::EffectRow, String> {
    let row = crate::EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| {
                Ok(crate::EffectInstance {
                    definition: effect.definition,
                    arguments: effect
                        .arguments
                        .iter()
                        .map(|argument| normalize_materialized_generic_argument(argument, solver))
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, String>>()?,
        projections: value
            .projections
            .iter()
            .map(|projection| {
                Ok(crate::EffectRowProjection {
                    subject: Box::new(normalize_materialized_type(&projection.subject, solver)?),
                    trait_definition: projection.trait_definition,
                    trait_arguments: projection
                        .trait_arguments
                        .iter()
                        .map(|argument| normalize_materialized_generic_argument(argument, solver))
                        .collect::<Result<_, _>>()?,
                    name: projection.name.clone(),
                    item_generic_kinds: projection.item_generic_kinds.clone(),
                    item_arguments: projection
                        .item_arguments
                        .iter()
                        .map(|argument| normalize_materialized_generic_argument(argument, solver))
                        .collect::<Result<_, _>>()?,
                })
            })
            .collect::<Result<_, String>>()?,
        tails: value.tails.clone(),
    }
    .canonicalized();
    // Keep an unresolved row symbolic so the source checker remains the
    // authority for diagnostics. Materialized concrete selections, however,
    // must agree with their lowered callable witnesses.
    Ok(if lifetime_binders == 0 {
        solver.normalize_effect_row(row.clone()).unwrap_or(row)
    } else {
        solver
            .normalize_effect_row_in_hrtb(row.clone(), lifetime_binders)
            .unwrap_or(row)
    })
}

pub(crate) fn normalize_materialized_generic_argument(
    value: &GenericArgument,
    solver: &mut TraitSolver,
) -> Result<GenericArgument, String> {
    match value {
        GenericArgument::Type(value) => Ok(GenericArgument::Type(normalize_materialized_type(
            value, solver,
        )?)),
        GenericArgument::EffectRow(value) => Ok(GenericArgument::EffectRow(
            normalize_materialized_effect_row(value, solver, 0)?,
        )),
        GenericArgument::ConstProjection { .. } => {
            normalize_materialized_const_projection(value.clone(), solver)
        }
        value => Ok(value.clone()),
    }
}

/// Follow an implementation's associated-const value through another
/// concrete projection (for example `First::Value = Second::Value`) while
/// preserving a finite, deterministic failure boundary for malformed cycles.
fn normalize_materialized_const_projection(
    mut value: GenericArgument,
    solver: &mut TraitSolver,
) -> Result<GenericArgument, String> {
    const MAX_PROJECTION_CHAIN: u32 = 128;
    for _ in 0..MAX_PROJECTION_CHAIN {
        let GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } = value
        else {
            return normalize_materialized_generic_argument(&value, solver);
        };
        let subject = normalize_materialized_type(&subject, solver)?;
        let trait_arguments = trait_arguments
            .iter()
            .map(|argument| normalize_materialized_generic_argument(argument, solver))
            .collect::<Result<Vec<_>, _>>()?;
        let goal = TraitGoal {
            relation: crate::ElaboratedTraitReference {
                definition: trait_definition,
                arguments: trait_arguments,
            },
            subject,
        };
        value = match solver.normalize_associated_const(goal, &name, kind) {
            TraitConstProjectionAnswer::Normalized { value, .. } => value,
            answer => {
                return Err(format!(
                    "materialized associated const `{name}` could not be normalized: {answer:?}"
                ));
            }
        };
    }
    Err("materialized associated-const projection chain exceeded its limit".into())
}

#[cfg(test)]
fn normalize_materialized_pattern(
    pattern: &mut crate::MirPattern,
    solver: &mut TraitSolver,
) -> Result<(), String> {
    match pattern {
        crate::MirPattern::Any | crate::MirPattern::Literal(_) => Ok(()),
        crate::MirPattern::Tuple(elements) => elements
            .iter_mut()
            .try_for_each(|element| normalize_materialized_pattern(element, solver)),
        crate::MirPattern::Array { element, elements, .. } => {
            *element = normalize_materialized_type(element, solver)?;
            elements
                .iter_mut()
                .try_for_each(|element| normalize_materialized_pattern(element, solver))
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
                .map(|field| normalize_materialized_type(field, solver))
                .collect::<Result<_, _>>()?;
            for field in fields {
                field.ty = normalize_materialized_type(&field.ty, solver)?;
                normalize_materialized_pattern(&mut field.pattern, solver)?;
            }
            Ok(())
        }
    }
}

/// Link only statically reachable functions into the executable program. A
/// body is still parsed, typed, and checked before this point, but a helper
/// eliminated by a verified static handler specialization must not force the
/// VM emitter to manufacture a normal runtime value for its terminal path.
/// `MakeCallable` is an edge because an indirect call may invoke that code
/// later; all iteration is ordered for byte-identical linking.
#[cfg(test)]
fn reachable_function_keys(
    functions: &BTreeMap<DefKey, MirFunction>,
    roots: impl IntoIterator<Item = DefKey>,
) -> BTreeSet<DefKey> {
    let mut pending = roots.into_iter().collect::<BTreeSet<_>>();
    let mut reachable = BTreeSet::new();
    while let Some(definition) = pending.pop_first() {
        if !reachable.insert(definition) {
            continue;
        }
        let Some(function) = functions.get(&definition) else {
            continue;
        };
        pending.extend(function.control.frame_cleanup.iter().map(|action| action.destructor));
        for block in &function.blocks {
            for instruction in &block.instructions {
                if let crate::MirInstruction::CallOwned { callee, .. }
                | crate::MirInstruction::Call { callee, .. }
                | crate::MirInstruction::MakeCallable { callee, .. } = instruction
                {
                    pending.insert(*callee);
                }
                if let crate::MirInstruction::HostCall { resident_operations, .. } | crate::MirInstruction::HostCallOwned { resident_operations, .. } = instruction {
                    pending.extend(resident_operations.iter().filter_map(|(_, destructor)| *destructor));
                }
                if let crate::MirInstruction::MakeCallable { environment: Some(environment), .. } = instruction {
                    pending.extend(environment.destructor);
                }
            }
        }
    }
    reachable
}

/// Build the body-grouping table from every operator declaration visible in
/// this lexical module. Interface collection owns declarations, while the
/// resolution index owns imports, aliases, globs, privacy, and re-exports;
/// joining them here prevents a body parser from treating an imported operator
/// as if it had no declared associativity.
fn visible_fixities_for_module(
    module: &crate::ModuleKey,
    index: &DefinitionIndex,
    declarations: &BTreeMap<DefKey, crate::FixityHeader>,
) -> FixityTable {
    FixityTable::visible_in_module(module, index, declarations)
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
    fn frozen_solver_construction_does_not_scale_with_bodies_or_lifted_closures() {
        fn compile_many(bodies: usize) -> usize {
            let mut source = String::from("pub fn main() -> i64 { 42 }");
            for index in 0..bodies {
                source.push_str(&format!("\nfn work_{index}(value: i64) -> i64 {{ let callback = (input: i64) -> i64 {{ input }}; callback(value) }}"));
            }
            let package = crate::PackageKey("solver-scaling@0.1.0".into());
            let request = crate::CompilationRequest {
                build: crate::CompilerBuildIdentity::stage0(Digest::of_bytes(b"solver-scaling")),
                mode: crate::CompilationMode::Build,
                root_package: package.clone(),
                sources: vec![crate::SourceInput::new(package,
                    crate::LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
                target: "stage0-vm".into(),
                semantic_options: Default::default(), codegen_options: Default::default(),
                capability_manifest: vec![], runtime_manifest: None,
            };
            let before = crate::trait_solver::snapshot_builds();
            let outcome = super::StageZeroCompiler::new().compile(request)
                .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics()));
            let built = crate::trait_solver::snapshot_builds() - before;
            let artifact = outcome.artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(crate::decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            built
        }
        let small = compile_many(2);
        let large = compile_many(64);
        assert_eq!(large, small, "immutable snapshot construction must not grow with body/closure count: {small} -> {large}");
        assert!(large < 64, "a single small request rebuilt {large} immutable snapshots");
    }

    #[test]
    fn unmaterialized_trait_calls_remain_errors_on_reachable_call_and_callable_edges() {
        fn body(definition: DefKey, instructions: Vec<MirInstruction>) -> MirFunction {
            MirFunction {
                safety: crate::Safety::Safe,
                unsafe_execution: false,
                nominal_copy_descriptors: vec![],
                definition,
                captures: 0,
                parameters: vec![],
                locals: vec![MirLocalDecl {
                    ty: Type::Unit,
                    source: CoreId(u32::MAX),
                }],
                result: Type::Unit,
                control: crate::MirControlTables::default(),
                entry: MirBlockId(0),
                blocks: vec![MirBlock {
                    scope: crate::MirScopeId::ROOT,
                    parameters: vec![],
                    instructions,
                    terminator: MirTerminator::Unreachable,
                }],
            }
        }
        let entry = key("missing-instance-entry");
        let helper = key("missing-instance-helper");
        let missing = MirInstruction::MakeCallable {
            dst: MirLocal(0),
            callee: key("undiscovered-trait-method"),
            captures: vec![],
            generic_arguments: vec![],
            environment: None,
            trait_instance: Some(crate::mir::MirTraitMethodInstance {
                evidence: key("selected-evidence"),
                trait_arguments: vec![],
                method_arguments: vec![],
                deferred: None,
            }),
        };
        let mut graph = crate::InstanceGraph::default();
        graph
            .discover_root(
                crate::InstanceRoot {
                    key: crate::InstanceKey::new(entry, &[], vec![]).unwrap(),
                    reason: "test".into(),
                },
                crate::InstanceLimits::default(),
            )
            .unwrap();
        let signatures = crate::ElaboratedInterface::default();
        let mut unused = std::collections::BTreeMap::from([
            (entry, body(entry, vec![])),
            (helper, body(helper, vec![missing.clone()])),
        ]);
        assert!(
            super::materialize_concrete_instances(&mut unused, &graph, &signatures, None,
                &mut crate::destruction::Planner::new(&signatures)).is_ok()
        );
        for edge in [
            MirInstruction::Call {
                dst: MirLocal(0),
                callee: helper,
                arguments: vec![],
                generic_arguments: vec![],
                trait_instance: None,
            },
            MirInstruction::MakeCallable {
                dst: MirLocal(0),
                callee: helper,
                captures: vec![],
                generic_arguments: vec![],
                trait_instance: None,
                environment: None,
            },
        ] {
            let mut functions = std::collections::BTreeMap::from([
                (entry, body(entry, vec![edge])),
                (helper, body(helper, vec![missing.clone()])),
            ]);
            let error =
                super::materialize_concrete_instances(&mut functions, &graph, &signatures, None,
                    &mut crate::destruction::Planner::new(&signatures))
                    .expect_err("a reachable owner must not hide an undiscovered method instance");
            assert!(
                error.contains("selected trait-method instance was not materialized"),
                "{error}"
            );
        }
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
            tails: Default::default(),
        };
        let original = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
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
                tails: [EffectTail::Generic(3)].into_iter().collect(),
            },
            invocation: Quantity::ONCE,
        };

        let specialized = specialize_type(
            &original,
            &[
                GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::ConstInteger(17u32.into()),
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
        assert_eq!(*result, Type::ConstInteger(17u32.into()));
        assert!(effects.tails.is_empty());
        assert!(effects.effects.contains(&EffectInstance {
            definition: outer_effect,
            arguments: vec![
                GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::ConstInteger(17u32.into()),
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
                && item_arguments == &vec![GenericArgument::ConstInteger(17u32.into())]
        ));
    }

    #[test]
    fn materialization_specializes_every_frozen_mir_type_witness() {
        let generic = Type::Generic(0);
        let callable = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![generic.clone()],
            result: Box::new(generic.clone()),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
        };
        let mut function = MirFunction {
            safety: crate::Safety::Safe,
            unsafe_execution: false,
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
            control: crate::MirControlTables::default(),
            entry: MirBlockId(0),
            blocks: vec![MirBlock {
                scope: crate::MirScopeId::ROOT,
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
                                    rest: None,
                                    element: generic.clone(),
                                    elements: vec![],
                                },
                            }],
                        },
                    },
                    MirInstruction::InstallHandler {
                        site: crate::MirHandlerSiteId::UNASSIGNED,
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
                        source_contract: Digest::of_bytes(b"specialized-host-contract"),
                        resident_operations: vec![],
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
                            destructor: None,
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
