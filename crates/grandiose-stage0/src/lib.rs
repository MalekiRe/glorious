//! Independent Rust stage-zero compiler.
//!
//! The module boundaries mirror the self-hosted compiler specification.  The
//! current implementation deliberately starts at the system spine: all later
//! parsing, semantic, MIR, and VM-emission work receives an immutable revision
//! snapshot and has no ambient filesystem, environment, network, or clock
//! authority.

pub mod body;
pub mod bootstrap;
pub mod coherence;
pub mod core;
pub mod dependency;
pub mod diagnostic;
pub mod escape;
pub mod fixity;
pub mod header;
pub mod identity;
pub mod instance;
pub mod interface;
pub mod mir;
pub mod module_graph;
pub mod operation;
pub mod pattern;
pub mod placeflow;
pub mod quantity;
pub mod query;
pub mod request;
pub mod resolution;
pub mod revision;
pub mod runtime_manifest;
pub mod scanner;
pub mod service;
pub mod signature;
pub mod source;
pub mod trait_solver;
pub mod types;
pub mod useflow;
pub mod vm_backend;

pub use body::{
    BodyDiagnostic, BodySyntax, ClosureParameter, Expr, ExprId, ExprKind, HandlerClause, Pattern,
    PatternId, PatternKind,
};
pub use bootstrap::{
    BOOTSTRAP_MANIFEST_MAGIC, BOOTSTRAP_MANIFEST_SCHEMA, BootstrapConvergenceError,
    BootstrapManifest, BootstrapManifestError,
};
pub use coherence::{CoherenceDiagnostic, CoherenceSet, ImplHead};
pub use core::{
    CallReferenceOrigin, CallReferencePath, CallReferenceShape, CallableBrand, CallableId,
    CaptureEnvironment, CaptureMode, CapturePostState, ClosureCapture, CoreDiagnostic, CoreExpr,
    CoreHandlerClause, CoreHandlerContinuationContract, CoreHandlerResumption, CoreId, CoreKind,
    CorePattern, CorePatternField, CorePlace, EnvironmentBrand, LabelBrand, RefinementBrand,
    RefinementEnvironment, TypedBody,
};
pub use dependency::{DependencyLedger, DependencyNode, DependencyStatus, DependencyTrace};
pub use diagnostic::{Diagnostic, DiagnosticClass, DiagnosticCode, Severity, SourceSpan};
pub use escape::{EscapeDiagnostic, EscapeFlow};
pub use fixity::{Fixity, FixityPosition, FixityTable};
pub use header::{
    AssociatedTypeDefinitionHeader, AssociatedTypeHeader, CallableHeader, EffectHeader,
    EffectOperationHeader, EffectRowHeader, EnumVariantHeader, EnumVariantPayloadHeader,
    FixityForm, FixityHeader, GenericParameters, HeaderDiagnostic, HeaderGenericArgument,
    HeaderParameter, HeaderParse, HeaderStructuralConst, HeaderStructuralU32Expr, HeaderType,
    ImplementationHeader, ImplementationMethodHeader, ImportBindingHeader, ImportHeader,
    NominalFieldHeader, NominalLayoutHeader, ParsedHeader, TraitHeader, TraitMethodHeader,
    TraitRefHeader, WhereBoundHeader,
};
pub use identity::{
    DefKey, Digest, FileKey, ModuleKey, PackageKey, RevisionId, implementation_method_key,
};
pub use instance::{
    CallSummary, InstanceArgument, InstanceGraph, InstanceGraphError, InstanceKey,
    InstanceKeyError, InstanceLimits, InstanceRoot, SummaryError, SummaryLimits,
    solve_call_summaries,
};
pub use interface::{
    Definition, DefinitionNamespace, InterfaceCache, InterfaceCacheStats, InterfaceDiagnostic,
    InterfaceSet, PackageInterface,
};
pub use mir::{
    MirBlock, MirBlockId, MirCapture, MirCaptureEnvironment, MirCleanupPlan, MirContinuationPolicy,
    MirDiagnostic, MirEditor, MirFunction, MirInstance, MirInstruction, MirLocal, MirLocalDecl,
    MirLowering, MirOptimizationReport, MirPattern, MirPatternField, MirProgram, MirTerminator,
    MirTraitMethodInstance, optimize as optimize_mir,
};
pub use module_graph::{ModuleDiagnostic, ModuleGraph, ModuleNode};
pub use operation::{Budget, BudgetError, CancellationToken, PublicationGuard};
pub use pattern::{
    BinderKey, BindingMode, PatternBinding, PatternDecision, PatternDiagnostic, PatternElaboration,
    PatternGenericScope, PatternPlan, elaborate_pattern, elaborate_pattern_with_scope,
};
pub use placeflow::{
    FlowDiagnostic, FlowEvent, FlowEventKind, LoanFact, LocalState, MoveFact, PlaceFlow,
    RefinementFact,
};
pub use quantity::{Quantity, QuantityError};
pub use request::{
    BootstrapLimits, BootstrapStage, CompilationMode, CompilationRequest, CompilerBuildIdentity,
    InputError, LogicalPath, NormalizedInputWorld, STAGE0_BYTECODE_GENERATION,
    STAGE0_CACHE_GENERATION, STAGE0_INTERFACE_GENERATION, STAGE0_LANGUAGE_GENERATION,
    STAGE0_QUERY_GENERATION, STAGE0_VERIFIER_GENERATION, SourceInput,
};
pub use resolution::{
    DefinitionIndex, ImportBinding, Occurrence, OccurrenceRole, ReferenceIndex,
    ResolutionDiagnostic, ResolutionState, ScopeMap,
};
pub use revision::{
    CompilerDatabase, DatabaseSnapshot, RequestSession, RetentionReport, RevisionCache,
    RevisionError, RevisionMetadata,
};
pub use runtime_manifest::{
    ManifestError, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput, TrustedRuntimeManifest,
};
pub use scanner::{DeclarationKind, DeclarationScan, DeclarationShell, ScanDiagnostic, TokenRange};
pub use service::{
    CompilationOutcome, CompileDiagnostic, DiagnosticExplanationFrame, DiagnosticFact,
    RelatedDiagnosticLocation, ServiceError, StageZeroCompiler,
};
pub use signature::{
    CallableSignature, ElaboratedAssociatedConst, ElaboratedAssociatedConstDefinition,
    ElaboratedAssociatedEffectRowDefinition, ElaboratedAssociatedType,
    ElaboratedAssociatedTypeDefinition, ElaboratedEffect, ElaboratedEffectOperation,
    ElaboratedEnumVariant, ElaboratedEnumVariantPayload, ElaboratedHeader,
    ElaboratedImplementation, ElaboratedInterface, ElaboratedNominalLayout, ElaboratedTrait,
    ElaboratedTraitReference, InstantiationError, NominalField, SignatureDiagnostic,
};
pub use source::{LexedFile, LexerDiagnostic, LineIndex, SourcePosition, Span, Token, TokenKind};
pub use trait_solver::{
    DEFAULT_MAX_TRAIT_DEPTH, DEFAULT_MAX_TRAIT_STEPS, TraitAnswer, TraitCandidateExplanation,
    TraitCandidateRejection, TraitConstProjectionAnswer, TraitCyclePolicy,
    TraitEffectRowProjectionAnswer, TraitExplanationTerminal, TraitGoal, TraitGoalQuery,
    TraitMethodAnswer, TraitProjectionAnswer, TraitSelectionExplanation, TraitSolver,
    TraitSolverLimits, TraitWhereBoundExplanation,
};
pub use types::{
    ConstInferVar, ConstKind, EffectInstance, EffectRow, EffectRowProjection, EffectTail,
    EffectVar, GenericArgument, GenericKind, InferContext, InferVar, Lifetime, Mutability,
    ScalarType, StructuralConstError, StructuralU32Expr, Type, TypeError,
};
pub use useflow::{
    CallableEscapeBoundary, CallableEscapeFact, CallableUseFact, UseDiagnostic, UseFlow,
    ValueUseDisposition, ValueUseFact,
};
pub use vm_backend::{
    CandidateVmArtifact, CandidateVmProgram, STAGE0_MAX_DECODE_FUNCTIONS,
    STAGE0_MAX_DECODE_INSTRUCTIONS, STAGE0_MAX_DECODE_REGISTERS, STAGE0_MAX_DECODE_TEXT_BYTES,
    STAGE0_VM_SCHEMA, VerifiedVmArtifact, VerifiedVmProgram, VmArtifactError, VmCapture,
    VmCaptureEnvironment, VmCaptureMode, VmCleanupLoan, VmCleanupPlace, VmCleanupProof, VmCompare,
    VmContinuationPolicy, VmEffectInstance, VmEffectRow, VmEffectRowProjection, VmExecutionLimits,
    VmFunction, VmGenericArgument, VmInstruction, VmPattern, VmPatternField, VmType,
    decode_and_verify_artifact, decode_and_verify_program, decode_artifact, decode_program,
    emit as emit_vm, emit_program as emit_vm_program, encode_artifact, encode_program,
    verify as verify_vm, verify_program as verify_vm_program,
};
