//! Typed Core, the semantic boundary before ownership facts and MIR.

use crate::{
    body::{BodySyntax, ClosureParameter, ExprId, ExprKind, HandlerClause},
    fixity::FixityTable,
    header::FixityForm,
    identity::{DefKey, Digest, ModuleKey, PackageKey},
    interface::{Definition, DefinitionNamespace},
    pattern::{PatternDecision, PatternGenericScope, elaborate_pattern_with_scope},
    resolution::{DefinitionIndex, ResolutionState, ScopeMap},
    signature::{
        CallableSignature, ElaboratedEffect, ElaboratedHeader, ElaboratedInterface,
        ElaboratedNominalLayout, ElaboratedTraitReference, HostImport,
    },
    source::Span,
    trait_solver::{
        TraitAnswer, TraitConstProjectionAnswer, TraitEffectRowProjectionAnswer, TraitGoal,
        TraitMethodAnswer, TraitProjectionAnswer, TraitSolver,
    },
    types::{
        EffectInstance, EffectRow, GenericArgument, InferContext, Lifetime, Mutability, ScalarType,
        Type, canonical_generic_arguments_encoding, canonical_type_encoding,
        is_canonical_effect_row_identity, is_canonical_generic_argument_identity,
        is_canonical_type_identity,
    },
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CoreId(pub u32);
/// Fresh body-local identity for an anonymous callable. It is deliberately
/// separate from a source offset so nested closure allocation has no effect on
/// named declaration identities or interface fingerprints.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CallableId(pub u32);
/// Stable body-local identity of a suspended handler continuation.  This is
/// deliberately independent from its source binder: aliases may carry the
/// same snapshot capability, while lexical shadowing must never manufacture a
/// new continuation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ResumptionId(pub u32);
/// A generative owner-local identity for a closure environment.  Unlike a
/// capture spelling, this is proof that a particular callable body owns the
/// layout; it cannot be reconstructed from a source name in another body.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EnvironmentBrand {
    pub owner: DefKey,
    pub callable: CallableId,
}
/// A fresh, owner-scoped proof namespace introduced by a structural pattern
/// decision.  It is distinct from a label or callable environment: a fact in
/// this namespace is valid only while the decision that produced it remains
/// on the active control path.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RefinementBrand {
    pub owner: DefKey,
    pub refinement: u32,
}
/// A binder belongs to one generative refinement environment. Equal source
/// spellings in different tests never identify interchangeable evidence.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct RefinementBindingKey {
    pub environment: RefinementBrand,
    pub binder: u32,
}
/// A generative lexical destination identity. A source spelling is resolved
/// only while its label scope is active; transfers carry this brand rather
/// than a name so shadowing cannot retarget nonlocal control.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LabelBrand {
    pub owner: DefKey,
    pub label: u32,
}
/// The nominal identity of an executable body.  Named declarations already
/// have a stable `DefKey`; anonymous and handler-generated bodies mint a
/// fresh owner-local brand instead of borrowing a user-visible name.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum CallableBrand {
    Named(DefKey),
    Closure(EnvironmentBrand),
    HandlerClause { owner: DefKey, clause: u32 },
    Continuation { owner: DefKey, clause: u32 },
}
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum CaptureMode {
    SharedBorrow,
    UniqueBorrow,
    /// An owned closure environment slot initialized by copying a
    /// `[0, infinity]` value.  It is distinct from a borrow: the closure may
    /// outlive the source binding without retaining a loan.
    Copy,
    Move,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureCapture {
    pub name: String,
    pub mode: CaptureMode,
    pub ty: Type,
}
/// The mode-derived ownership state of one outer place immediately after its
/// environment has been captured. Keeping this separate from the capture
/// layout makes the callable's `RunsIn` post-state a frozen Core fact rather
/// than an inference-only convention.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CapturePostState {
    pub name: String,
    pub mode: CaptureMode,
}
/// Compiler-created proof that one callable may run against exactly one
/// sealed capture environment. Source code cannot spell its environment
/// brand, so a trait merely named `RunsIn` never grants this authority.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RunsInEvidence {
    pub environment: EnvironmentBrand,
    pub callable: CallableId,
    pub effects: EffectRow,
    pub post_states: Vec<CapturePostState>,
    pub sealed: bool,
}
/// A closure's complete, post-inference environment.  Capture mode selection
/// remains the responsibility of PlaceFlow; this record seals that selected
/// layout together with the callable that is allowed to consume it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaptureEnvironment {
    pub brand: EnvironmentBrand,
    pub captures: Vec<ClosureCapture>,
    pub post_states: Vec<CapturePostState>,
    pub runs_in: RunsInEvidence,
    pub sealed: bool,
}

/// The three ordinary source ownership forms admitted as the `Access`
/// argument of compiler-generated `RunsIn` evidence.  This is deliberately
/// an elaborator-local classification, not a second receiver-mode type in
/// Core: the retained evidence is always the ordinary `E`, `&E`, or `&mut E`
/// source type.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RunsInAccess {
    Owned,
    Shared,
    Unique,
}

/// An opaque, deterministic nominal identity for one sealed environment
/// state.  `after` distinguishes an owned call's normal successor ledger
/// from its incoming ledger without exposing either as a source declaration.
fn generated_environment_type(brand: EnvironmentBrand, after: bool) -> Type {
    let callable = brand.callable.0.to_le_bytes();
    let phase = if after {
        b"after".as_slice()
    } else {
        b"before".as_slice()
    };
    Type::Nominal {
        definition: DefKey(Digest::of_parts([
            b"grandiose-stage0-generated-environment-type-v1".as_slice(),
            brand.owner.0.as_bytes().as_slice(),
            callable.as_slice(),
            phase,
        ])),
        arguments: vec![],
    }
}

/// Decode the two type-valued arguments of an intrinsic RunsIn relation.
/// Header elaboration enforces the outer shape; retaining this check here
/// keeps forged or partially recovered signatures from gaining evidence.
fn intrinsic_runs_in_arguments(relation: &crate::ElaboratedTraitReference) -> Option<(Type, Type)> {
    let [GenericArgument::Type(access), GenericArgument::Type(inputs)] =
        relation.arguments.as_slice()
    else {
        return None;
    };
    Some((access.clone(), inputs.clone()))
}
/// Positive evidence produced by `is`. Bindings remain facts rather than
/// ordinary locals until a branching consumer opens their lexical scope; this
/// prevents a test expression from silently leaking a pattern binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefinementEnvironment {
    pub brand: RefinementBrand,
    pub subject: Option<String>,
    pub bindings: Vec<String>,
    pub binding_keys: Vec<RefinementBindingKey>,
    /// The source-level types behind `bindings`.  Names alone are retained
    /// for inspection, while completion dispatch needs the frozen types to
    /// open the positive branch as an ordinary lexical scope.
    pub binding_types: Vec<(String, Type)>,
    pub sealed: bool,
}
impl CaptureEnvironment {
    fn seal(
        owner: DefKey,
        callable: CallableId,
        captures: Vec<ClosureCapture>,
        effects: EffectRow,
    ) -> Self {
        let brand = EnvironmentBrand { owner, callable };
        let post_states: Vec<CapturePostState> = captures
            .iter()
            .map(|capture| CapturePostState {
                name: capture.name.clone(),
                mode: capture.mode,
            })
            .collect();
        Self {
            brand,
            runs_in: RunsInEvidence {
                environment: brand,
                callable,
                effects,
                post_states: post_states.clone(),
                sealed: true,
            },
            post_states,
            captures,
            sealed: true,
        }
    }
}
/// Fully typed, source-free pattern decision. Field types are carried through
/// Core so MIR and the independently decoded VM artifact can validate every
/// structural projection without retaining an interface table at runtime.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorePattern {
    Any,
    /// A pattern binder is semantically irrefutable but retains its local
    /// identity until MIR has projected the selected payload field.
    Bind {
        name: String,
    },
    Literal(String),
    Tuple(Vec<CorePattern>),
    Array {
        element: Type,
        elements: Vec<CorePattern>,
    },
    Record {
        definition: DefKey,
        /// Complete ordered instantiated layout.  Keeping this separately
        /// from the selected fields freezes the identity and type of every
        /// declaration slot, including omitted fields.
        field_types: Vec<Type>,
        field_count: u32,
        fields: Vec<CorePatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        /// Complete ordered instantiated payload layout for `variant`.
        field_types: Vec<Type>,
        field_count: u32,
        fields: Vec<CorePatternField>,
    },
    Error,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorePatternField {
    pub index: u32,
    pub ty: Type,
    pub pattern: CorePattern,
}
/// One fully resolved handler arm.  Source spellings and payload binder names
/// never reach MIR as dispatch identities: the protocol instance and stable
/// declaration-order operation index are the runtime key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreHandlerClause {
    pub brand: CallableBrand,
    pub effect: EffectInstance,
    pub operation: u32,
    /// Exact operation payload signature retained after body elaboration.
    /// MIR needs it when materializing a lexical frame for a sibling operation
    /// that is not the immediately visible `Perform` site.
    pub payload_types: Vec<Type>,
    pub patterns: Vec<CorePattern>,
    pub bindings: Vec<(String, Type)>,
    pub resumption: CoreHandlerResumption,
    /// The frozen continuation interface for this arm.  It is retained even
    /// for a discarded continuation: ownership and MIR need the same source
    /// contract to distinguish cancellation from a terminal operation.
    pub continuation: Option<CoreHandlerContinuationContract>,
    pub body: CoreId,
    pub terminal: bool,
    pub span: Span,
}
/// The source-independent boundary between handler checking and continuation
/// lowering.  A resumption accepts the operation result, returns the handler
/// result, and can only perform the residual outward row after all enclosing
/// deep handlers have subtracted the effects they intercept.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreHandlerContinuationContract {
    pub brand: CallableBrand,
    pub parameter: Type,
    pub result: Type,
    pub effects: EffectRow,
    pub invocation: crate::quantity::Quantity,
    /// Direct syntactic invocation sites observed while elaborating this arm.
    /// This is deliberately a lower-bound check only: later control-flow and
    /// ownership passes refine path-sensitive use counts.
    pub direct_uses: u64,
}
/// One normal-completion arm after resolution has established that its source
/// head was not an operation of the handled effect row.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreCompletionClause {
    pub pattern: CorePattern,
    pub bindings: Vec<(String, Type)>,
    /// A positive `is` environment opened only when this completion pattern
    /// proves the test result is `true`.  It deliberately references the
    /// once-evaluated structural subject rather than reconstructing it from
    /// source spelling during MIR lowering.
    pub refinement: Option<CoreRefinementBranch>,
    pub body: CoreId,
    pub span: Span,
}
/// Frozen provenance for a direct-reference result at a callable boundary.
/// A reference-valued call must name every argument whose region it may
/// forward, prove that it is external/static, or be explicitly opaque. The
/// latter is rejected by ownership consumers rather than silently shortening
/// a caller loan based on a callee implementation detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CallReferenceOrigin {
    /// The result has no direct reference component.
    None,
    /// Every caller-derived reference leaf maps to its possible input leaves.
    /// Several relations may share a result path; all such input loans remain
    /// live. Vectors use frozen structural field indices, never spellings.
    Paths(Vec<CallReferencePath>),
    /// The result is an external/static reference with no caller loan.
    External,
    /// Reference validity/lifetimes (including nested/generic residents) are
    /// unsafe callable preconditions, not checked input-loan derivations.
    Unsafe,
    /// Core could not prove the possible source regions for a reference result.
    Opaque,
}
/// The sealed reference-bearing shape of a callable result.  This is kept
/// alongside its provenance because an opaque nominal, enum, array, or
/// projection has no Core projection path even though it may carry a
/// body-local loan.  Later phases must not mistake that lack of a path for a
/// proof that the value is scalar.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallReferenceShape {
    /// The realized result is proven not to contain a reference.
    None,
    /// Every reference component is static/external.
    External,
    /// Validity comes from a checked unsafe call contract, not a static claim.
    Unsafe,
    /// At least one component forwards a caller path (possibly alongside
    /// static components).
    CallerPaths,
    /// The realized result may contain a non-static reference, but Core has
    /// no sound structural path through its representation.
    OpaquePotentiallyReference,
}

/// Classify the *realized* result rather than the declaration contract alone.
/// A generic contract is necessarily opaque before instantiation, but a VM
/// specialization such as `identity<i64>` is conclusively non-reference and
/// must not inherit that conservative declaration opacity.
fn call_reference_shape(
    signatures: &ElaboratedInterface,
    result: &Type,
    origin: &CallReferenceOrigin,
) -> CallReferenceShape {
    // Unsafe reconstruction also covers references nested in records/enums or
    // an abstract T returned by raw read. Validity of every such resident is
    // the unsafe caller's obligation, not a fabricated checked input loan.
    if matches!(origin, CallReferenceOrigin::Unsafe) {
        return CallReferenceShape::Unsafe;
    }
    let mut leaves = vec![];
    match reference_leaf_paths(signatures, result, &mut vec![], &mut leaves) {
        Ok(()) if leaves.is_empty() => CallReferenceShape::None,
        // A frozen generic contract still forwards its argument path when
        // that particular argument is static. Preserve the path contract
        // rather than pairing Paths provenance with an External-only shape.
        // Static arguments carry no local loan; retaining the path does not
        // manufacture one or weaken the validator's exact shape check.
        Ok(()) if matches!(origin, CallReferenceOrigin::Paths(_)) => {
            CallReferenceShape::CallerPaths
        }
        Ok(())
            if leaves.iter().all(|(_, leaf)| {
                matches!(
                    leaf,
                    Type::Reference {
                        lifetime: Lifetime::Static,
                        ..
                    }
                )
            }) =>
        {
            CallReferenceShape::External
        }
        // A visible non-static reference whose relation is ambiguous is just
        // as unsafe as a representation that cannot be opened at all.
        Ok(()) | Err(()) => CallReferenceShape::OpaquePotentiallyReference,
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallReferencePath {
    pub result_fields: Vec<u32>,
    pub argument: u32,
    pub argument_fields: Vec<u32>,
}
/// One branch-local view of a source `is` test.  The boolean result selects
/// the completion arm; this record supplies the corresponding structural
/// subject and frozen projection plan only to a proven-positive arm.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreRefinementBranch {
    pub environment: RefinementEnvironment,
    pub subject: CoreId,
    pub pattern: CorePattern,
}
/// A payload-only resumptive arm tail-resumes with its body value.  An explicit
/// continuation name is a normal callable in the clause scope; its quantity is
/// preserved for the ownership/resumption analysis that follows Typed Core.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoreHandlerResumption {
    Tail {
        quantity: crate::quantity::Quantity,
    },
    Explicit {
        name: String,
        quantity: crate::quantity::Quantity,
    },
    /// Full-control `_` discards the continuation. This is distinct from a
    /// payload-only tail arm, whose body implicitly resumes exactly once.
    Discard {
        quantity: crate::quantity::Quantity,
    },
    Terminal,
}

/// The lexical identity of a generated handler continuation.  A spelling is
/// insufficient here: an ordinary local is allowed to shadow a continuation
/// in a nested scope.  `binding_generation` comes from the journaled local
/// environment and identifies the exact currently visible binding.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ActiveResumption {
    id: ResumptionId,
    name: String,
    binding_generation: u64,
}
#[derive(Clone, Debug, Eq, PartialEq)]
struct ResumptionUseTracker {
    identity: ActiveResumption,
    direct_uses: u64,
}
#[derive(Clone)]
struct ActiveLabel {
    name: String,
    brand: LabelBrand,
    result: Type,
}

enum GroupedOperator {
    Operand(ExprId),
    Apply { name: String, operands: Vec<GroupedOperator> },
}

/// A single callable invocation opens two distinct lifetime namespaces. Source
/// declaration lifetimes are instantiated by the caller, while `for<'a>`
/// lifetimes are rigid until the invocation opens their outermost binder.
/// Keeping these maps separate prevents a de Bruijn bound region from ever
/// being mistaken for a declaration generic with the same numeric slot.
#[derive(Default)]
struct CallLifetimeSubstitution {
    generics: std::collections::BTreeMap<u32, Lifetime>,
    bounds: std::collections::BTreeMap<u32, Lifetime>,
}

#[derive(Clone, Copy)]
enum LifetimeMode {
    /// A declared body contract is rigid: assigning or returning a shorter
    /// body loan through `&'a` cannot manufacture an outlives proof.
    Rigid,
    /// A callee's own generic/bound lifetime is opened at the call site and
    /// may be instantiated from a caller argument.
    Instantiate,
}

#[derive(Clone, Copy)]
enum LifetimeError {
    UnsatisfiedOutlives,
    UnresolvedGeneric,
    EscapingBound,
}
/// A write destination frozen by Typed Core.  A place denotes stable storage,
/// unlike an ordinary value expression which may be copied or moved.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CorePlace {
    Local {
        name: String,
        ty: Type,
    },
    Field {
        base: Box<CorePlace>,
        index: u32,
        field_count: u32,
        ty: Type,
    },
    /// A dereferenced unique reference place.  The reference expression is
    /// retained as Typed Core rather than reconstructed from a spelling so
    /// every later ownership phase sees the same referent contract.
    Deref {
        reference: CoreId,
        ty: Type,
        unique: bool,
    },
    Error,
}
impl CorePlace {
    pub(crate) fn ty(&self) -> Type {
        match self {
            Self::Local { ty, .. } => ty.clone(),
            Self::Field { ty, .. } => ty.clone(),
            Self::Deref { ty, .. } => ty.clone(),
            Self::Error => Type::Error,
        }
    }
    pub(crate) fn root_local(&self) -> Option<(&str, &Type)> {
        match self {
            Self::Local { name, ty } => Some((name, ty)),
            Self::Field { base, .. } => base.root_local(),
            Self::Deref { .. } => None,
            Self::Error => None,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoreKind {
    Literal(String),
    Local(String),
    /// A first-class reference to one active handler snapshot.  It retains
    /// the lexical spelling solely so capture/diagnostic products can name
    /// the binding; `id` is the semantic identity consumed by UseFlow and
    /// continuation lowering.
    Resumption {
        id: ResumptionId,
        name: String,
    },
    /// A direct callable reference plus the caller-owned substitution used to
    /// instantiate its frozen declaration contract. Keeping this on Core is
    /// essential: a later instance/MIR query must never recreate inference
    /// variables or infer specialization identity from a rendered type.
    Function {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
        /// A declaration must explicitly carry this frozen boundary to be
        /// lowered as a host call. Absent means an ordinary VM function.
        host_import: Option<HostImport>,
    },
    /// A direct function value selected from a trait implementation. Retain
    /// proof evidence alongside the callable key until MIR consumes this
    /// source-free selection, rather than reconstructing lookup from a name.
    TraitMethod {
        evidence: DefKey,
        method: DefKey,
        trait_arguments: Vec<GenericArgument>,
        method_arguments: Vec<GenericArgument>,
        /// A lexical trait proof establishes the declaration contract, but
        /// has no concrete implementation identity until this generic body
        /// is instantiated.  The placeholder keys above keep ordinary Core
        /// identity operations total; MIR replaces them before execution.
        deferred: Option<DeferredTraitMethod>,
    },
    /// An evaluated top-level value is lowered as a zero-argument function.
    /// Its outward type may be generalized, so retain the use-site
    /// substitution exactly as we do for ordinary callable references.
    Constant {
        definition: DefKey,
        arguments: Vec<GenericArgument>,
    },
    Tuple(Vec<CoreId>),
    Array(Vec<CoreId>),
    Record {
        definition: DefKey,
        fields: Vec<CoreId>,
    },
    Field {
        base: CoreId,
        index: u32,
        field_count: u32,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        fields: Vec<CoreId>,
    },
    /// A source-free structural decision operation. The syntax-level `is` is
    /// erased at this boundary; refinement binding environments are layered
    /// on this once-evaluated test in the following analysis pass.
    PatternTest {
        subject: CoreId,
        pattern: CorePattern,
        refinement: RefinementEnvironment,
    },
    Closure {
        callable: CallableId,
        parameters: Vec<(String, Type)>,
        environment: CaptureEnvironment,
        body: CoreId,
    },
    Let {
        name: String,
        value: CoreId,
    },
    Label {
        brand: LabelBrand,
        body: CoreId,
    },
    /// The compiler-minted, first-class capability for one live lexical
    /// label.  Its callable shape is `(payload) -> !`; the nominal brand is
    /// retained instead of a source spelling so generic forwarding cannot
    /// retarget a shadowed destination.
    LabelValue {
        brand: LabelBrand,
    },
    Transfer {
        brand: LabelBrand,
        value: CoreId,
    },
    /// A statement-shaped write; the source parser admits it only in a block.
    Assign {
        place: CorePlace,
        value: CoreId,
    },
    Call {
        callee: CoreId,
        arguments: Vec<CoreId>,
        /// The declaration-level relation observed before generic/HRTB
        /// lifetimes are opened into caller-local regions.  This independently
        /// seals interface-aware nominal paths for Core validation.
        reference_contract: CallReferenceOrigin,
        reference_origin: CallReferenceOrigin,
        /// Frozen classification of the realized result.  It prevents an
        /// opaque representation from being treated as a non-reference by
        /// ownership or lowering consumers that cannot reopen interfaces.
        reference_shape: CallReferenceShape,
    },
    /// Canonical effect performance selected by the effect namespace, never a
    /// value function merely named like an operation.
    Perform {
        effect: EffectInstance,
        operation: u32,
        /// The fully instantiated operation payload contract selected during
        /// body elaboration.  Keeping it beside the actual argument nodes
        /// makes effect performance an independently checkable callable
        /// boundary for ownership/quantity consumers; they must not infer a
        /// receiver contract from the sender's realized expression type.
        payload_types: Vec<Type>,
        arguments: Vec<CoreId>,
        terminal: bool,
        /// The operation declaration's caller-region relation before body
        /// inference can collapse distinct lifetime arguments.  Operations
        /// are callable boundaries just like ordinary functions, so this
        /// contract independently seals the selected payload path.
        reference_contract: CallReferenceOrigin,
        /// Frozen caller-region provenance for the operation result.  Effect
        /// operations are callable boundaries too: the handler/resumption
        /// machinery must never infer a shorter region from an implementation
        /// detail after Core has been sealed.
        reference_origin: CallReferenceOrigin,
        /// See [`CoreKind::Call::reference_shape`].
        reference_shape: CallReferenceShape,
    },
    /// Deep handler scope.  Its operations are already namespace-resolved,
    /// structurally typed, and coverage-checked before this Core boundary.
    Handle {
        computation: CoreId,
        clauses: Vec<CoreHandlerClause>,
    },
    Completion {
        computation: CoreId,
        clauses: Vec<CoreCompletionClause>,
        /// Checked compiler-owned pack construction on this immediate
        /// structural decision. The executable nodes remain ordinary records
        /// and enum constructors; this metadata grants no source constructor.
        refinement_test: Option<RefinementEnvironment>,
        /// This dispatch belongs to the directly wrapped operation handler,
        /// whose full-control clauses bypass normal-completion dispatch.
        /// A distinct outer completion must observe the inner handler result.
        handles_operations: bool,
    },
    /// A call to a compiler-owned primitive implementation.  Surface
    /// operators either elaborate to a source-selected trait method or this
    /// uniform intrinsic-call form; Typed Core deliberately has no distinct
    /// arithmetic or prefix-expression node family.
    IntrinsicCall {
        operator: String,
        arguments: Vec<CoreId>,
    },
    Block(Vec<CoreId>),
    Borrow {
        unique: bool,
        value: CoreId,
    },
    /// Read through a shared or unique reference without consuming the loan.
    Deref(CoreId),
    Move(CoreId),
    Error,
}

/// A trait method call justified by an enclosing `where` bound.  This is not
/// runtime dictionary data: it is a frozen selection request resolved once
/// the surrounding callable's instance arguments are concrete.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeferredTraitMethod {
    pub relation: ElaboratedTraitReference,
    pub subject: Type,
    pub name: String,
}
impl CoreKind {
    /// Return the explicit nominal callable identity carried by executable
    /// values. Handler clauses and continuations retain their identities in
    /// their enclosing handler metadata rather than pretending to be ordinary
    /// named functions.
    pub fn callable_brand(&self) -> Option<CallableBrand> {
        match self {
            Self::Function { definition, .. } => Some(CallableBrand::Named(*definition)),
            Self::TraitMethod { method, .. } => Some(CallableBrand::Named(*method)),
            Self::Closure { environment, .. } => Some(CallableBrand::Closure(environment.brand)),
            _ => None,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreExpr {
    pub kind: CoreKind,
    pub ty: Type,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CoreDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}
#[derive(Clone, Debug)]
pub struct TypedBody {
    pub safety: crate::Safety,
    /// Explicit unsafe lexical block identities. Scope membership is derived
    /// from the structured graph, not from a call-site permission bit.
    /// Closure and handler bodies do not inherit an enclosing scope.
    pub unsafe_scopes: std::collections::BTreeSet<CoreId>,
    /// Conservatively retain unsafe implementations available in this source
    /// world. Their promises may influence static evidence without emitting a
    /// raw-memory operation. These identities are requirements, not host trust
    /// certificates, and never grant lexical unsafe permission.
    pub unsafe_implementations: std::collections::BTreeSet<DefKey>,
    pub parameters: Vec<(String, Type)>,
    pub expressions: Vec<CoreExpr>,
    pub root: CoreId,
    pub diagnostics: Vec<CoreDiagnostic>,
    pub recovered: bool,
}

impl TypedBody {
    /// A deterministic body-semantic identity for cache and differential
    /// comparison consumers. Source spans and body-arena allocation order do
    /// not participate; reachable nodes receive IDs in structural traversal
    /// order from the root instead. This is deliberately a fingerprint of
    /// frozen Core, not of recovery diagnostics or presentation metadata.
    pub fn semantic_fingerprint(&self) -> Digest {
        let mut encoder = CoreFingerprintEncoder {
            body: self,
            numbers: std::collections::BTreeMap::new(),
            bytes: Vec::new(),
        };
        encoder.bytes(b"grandiose-stage0-typed-core-v1");
        if self.safety == crate::Safety::Unsafe {
            encoder.bytes(b"unsafe-callable-contract");
        }
        if !self.unsafe_implementations.is_empty() {
            encoder.bytes(b"unsafe-implementation-requirements");
            encoder.debug(&self.unsafe_implementations);
        }
        encoder.id(self.root);
        Digest::of_bytes(&encoder.bytes)
    }

    /// Independently validate the frozen Core graph before any ownership or
    /// lowering pass consumes it.  Elaboration normally constructs these
    /// facts directly, but this boundary is also where a future persisted or
    /// imported Core product must fail closed rather than relying on that
    /// producer's implementation details.
    pub fn validate(&self) -> Vec<CoreDiagnostic> {
        let mut diagnostics = Vec::new();
        let mut needs_unsafe_validation = !self.unsafe_scopes.is_empty();
        if !self.contains(self.root) {
            diagnostics.push(CoreDiagnostic {
                code: "G4180",
                span: Span {
                    file: crate::FileKey(crate::Digest::of_bytes(b"invalid-typed-core-root")),
                    start: 0,
                    end: 0,
                },
                message: "Typed Core root refers to an expression outside its body arena".into(),
            });
        }
        let parameter_span = self
            .expressions
            .get(self.root.0 as usize)
            .map(|expression| expression.span);
        for (_, parameter) in &self.parameters {
            if !is_canonical_type_identity(parameter) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4186",
                    span: parameter_span.unwrap_or_else(invalid_typed_core_span),
                    message: "Typed Core parameter has a non-canonical semantic type identity"
                        .into(),
                });
            }
            if type_contains_out_of_scope_bound_lifetime(parameter) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4184",
                    span: parameter_span.unwrap_or_else(invalid_typed_core_span),
                    message: "Typed Core parameter contains a higher-ranked lifetime outside its callable binder".into(),
                });
            }
        }
        let mut authorized_binding_packs = std::collections::BTreeSet::new();
        for (index, expression) in self.expressions.iter().enumerate() {
            if matches!(expression.kind, CoreKind::Completion { refinement_test: Some(_), .. }) {
                match refinement_test_construction(self, CoreId(index as u32)) {
                    Ok(packs) => authorized_binding_packs.extend(packs),
                    Err(message) => diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span, message }),
                }
            }
        }
        let mut refinement_producers = std::collections::BTreeMap::new();
        for (index, expression) in self.expressions.iter().enumerate() {
            if let CoreKind::PatternTest { refinement, .. } | CoreKind::Completion { refinement_test: Some(refinement), .. } = &expression.kind
                && refinement_producers.insert(refinement.brand, index).is_some() {
                diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span,
                    message: "Typed Core reuses one refinement environment brand for distinct test producers".into() });
            }
            needs_unsafe_validation |= matches!(expression.ty, Type::Callable { safety: crate::Safety::Unsafe, .. });
            let owner = CoreId(index as u32);
            if matches!(&expression.kind, CoreKind::Record { definition, .. } if *definition == crate::refinement::bindings_definition())
                && !authorized_binding_packs.contains(&owner) {
                diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span,
                    message: "binding-pack construction lacks an immediate checked pattern decision".into() });
            }
            let mut check = |child: CoreId| {
                if !self.contains(child) {
                    diagnostics.push(CoreDiagnostic {
                        code: "G4180",
                        span: expression.span,
                        message: format!(
                            "Typed Core expression {} refers to missing expression {}",
                            owner.0, child.0
                        ),
                    });
                }
            };
            for child in core_children(&expression.kind) {
                check(child);
            }
            if let CoreKind::Completion { computation, handles_operations: true, .. } = &expression.kind
                && !self.expressions.get(computation.0 as usize)
                    .is_some_and(|expression| matches!(expression.kind, CoreKind::Handle { .. }))
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4183", span: expression.span,
                    message: "Typed Core completion is not attached to its direct operation handler".into(),
                });
            }
            if type_contains_inference(&expression.ty)
                || core_metadata_contains_inference(&expression.kind)
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4181",
                    span: expression.span,
                    message: "Typed Core expression or embedded metadata retains an unresolved inference variable".into(),
                });
            }
            if !is_canonical_type_identity(&expression.ty)
                || core_metadata_contains_noncanonical_type_identity(&expression.kind)
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4186",
                    span: expression.span,
                    message: "Typed Core expression or embedded metadata has a non-canonical semantic type identity".into(),
                });
            }
            if type_contains_out_of_scope_bound_lifetime(&expression.ty)
                || core_metadata_contains_out_of_scope_bound_lifetime(&expression.kind)
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4184",
                    span: expression.span,
                    message: "Typed Core expression or embedded metadata contains a higher-ranked lifetime outside its callable binder".into(),
                });
            }
            if core_kind_is_recovered(&expression.kind) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4182",
                    span: expression.span,
                    message: "Typed Core contains a recovered structural form".into(),
                });
            }
            if let Some(message) = core_structural_error(&expression.kind, &expression.ty) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4183",
                    span: expression.span,
                    message,
                });
            }
            if let Some(message) = completion_refinement_error(self, &expression.kind) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4183",
                    span: expression.span,
                    message,
                });
            }
            if let Some(message) = pattern_refinement_error(self, &expression.kind) {
                diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span, message });
            }
            if let Some(message) = perform_payload_contract_error(self, &expression.kind) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4183",
                    span: expression.span,
                    message,
                });
            }
            if let Some(message) =
                call_reference_origin_error(self, &expression.kind, &expression.ty)
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4187",
                    span: expression.span,
                    message,
                });
            }
        }
        if needs_unsafe_validation {
            self.validate_unsafe_scopes(&mut diagnostics);
        }
        self.validate_binding_pack_accesses(&mut diagnostics);
        diagnostics
    }

    fn validate_binding_pack_accesses(&self, diagnostics: &mut Vec<CoreDiagnostic>) {
        fn is_pack(ty: &Type) -> bool {
            match ty {
                Type::Nominal { definition, .. } => *definition == crate::refinement::bindings_definition(),
                Type::Reference { referent, .. } => is_pack(referent),
                _ => false,
            }
        }
        if !self.expressions.iter().any(|expression| is_pack(&expression.ty)) { return; }
        // Layout facts apply to the entire frozen arena, including unused
        // expressions. Lexical declaration checks below follow scoped paths.
        for expression in &self.expressions {
            let invalid = match &expression.kind {
                CoreKind::Field { base, index, field_count } => self.expressions.get(base.0 as usize)
                    .filter(|base| is_pack(&base.ty)).is_some_and(|base|
                        !crate::refinement::binding_pack_fields(&base.ty).is_some_and(|fields|
                            fields.len() == *field_count as usize && fields.get(*index as usize) == Some(&expression.ty))),
                CoreKind::Deref(reference) => self.expressions.get(reference.0 as usize)
                    .filter(|reference| is_pack(&reference.ty) || is_pack(&expression.ty)).is_some_and(|reference|
                        !matches!(&reference.ty, Type::Reference { referent, .. } if referent.as_ref() == &expression.ty)),
                _ => false,
            };
            if invalid {
                diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span,
                    message: "binding-pack access does not match its sealed field or referent layout".into() });
            }
        }
        type Locals = std::collections::BTreeMap<String, Type>;
        type CheckedScopes = std::collections::BTreeMap<CoreId, Vec<(Locals, Locals)>>;
        fn visit(body: &TypedBody, id: CoreId, locals: &mut Locals,
            active: &mut std::collections::BTreeSet<CoreId>, checked: &mut CheckedScopes,
            diagnostics: &mut Vec<CoreDiagnostic>) {
            let Some(expression) = body.expressions.get(id.0 as usize) else { return; };
            if let Some((_, output)) = checked.get(&id).into_iter().flatten().find(|(input, _)| input == locals) {
                *locals = output.clone();
                return;
            }
            if !active.insert(id) {
                diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span,
                    message: "binding-pack access has a cyclic lexical Core path".into() });
                return;
            }
            let input = locals.clone();
            let mut error = |message: &str| diagnostics.push(CoreDiagnostic {
                code: "G4183", span: expression.span, message: message.into(),
            });
            match &expression.kind {
                CoreKind::Local(name) if is_pack(&expression.ty) || locals.get(name).is_some_and(is_pack) => {
                    if locals.get(name) != Some(&expression.ty) {
                        error("binding-pack local does not match its lexical declaration");
                    }
                }
                _ => {},
            }
            match &expression.kind {
                CoreKind::Block(values) => {
                    let mut scoped = locals.clone();
                    for value in values { visit(body, *value, &mut scoped, active, checked, diagnostics); }
                }
                CoreKind::Let { name, value } => {
                    visit(body, *value, locals, active, checked, diagnostics);
                    if let Some(value) = body.expressions.get(value.0 as usize) {
                        locals.insert(name.clone(), value.ty.clone());
                    }
                }
                CoreKind::Closure { parameters, environment, body: closure_body, .. } => {
                    if parameters.iter().any(|(_, ty)| is_pack(ty))
                        || matches!(&expression.ty, Type::Callable { parameters, .. } if parameters.iter().any(is_pack)) {
                        let matches = match &expression.ty {
                            Type::Callable { parameters: expected, .. } => expected.len() == parameters.len()
                                && parameters.iter().zip(expected).all(|((_, actual), expected)|
                                    !is_pack(actual) && !is_pack(expected)
                                        || *actual == open_hrtb_callable_body_type(expected.clone(), 0)),
                            _ => false,
                        };
                        if !matches {
                            diagnostics.push(CoreDiagnostic { code: "G4183", span: expression.span,
                                message: "binding-pack body parameter differs from its callable contract".into() });
                        }
                    }
                    let mut scoped = environment.captures.iter().map(|capture| (capture.name.clone(), capture.ty.clone()))
                        .chain(parameters.iter().cloned()).collect();
                    visit(body, *closure_body, &mut scoped, active, checked, diagnostics);
                }
                CoreKind::Completion { computation, clauses, .. } => {
                    visit(body, *computation, locals, active, checked, diagnostics);
                    for clause in clauses {
                        let mut scoped = locals.clone();
                        scoped.extend(clause.bindings.iter().cloned());
                        visit(body, clause.body, &mut scoped, active, checked, diagnostics);
                    }
                }
                CoreKind::Handle { computation, clauses } => {
                    visit(body, *computation, locals, active, checked, diagnostics);
                    for clause in clauses {
                        let mut scoped = locals.clone();
                        scoped.extend(clause.bindings.iter().cloned());
                        visit(body, clause.body, &mut scoped, active, checked, diagnostics);
                    }
                }
                _ => for child in core_children(&expression.kind) { visit(body, child, locals, active, checked, diagnostics); },
            }
            active.remove(&id);
            checked.entry(id).or_default().push((input, locals.clone()));
        }
        visit(self, self.root, &mut self.parameters.iter().cloned().collect(),
            &mut std::collections::BTreeSet::new(), &mut CheckedScopes::new(), diagnostics);
    }

    fn validate_unsafe_scopes(&self, diagnostics: &mut Vec<CoreDiagnostic>) {
        for scope in &self.unsafe_scopes {
            if !self
                .expressions
                .get(scope.0 as usize)
                .is_some_and(|expression| matches!(expression.kind, CoreKind::Block(_)))
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4202",
                    span: self
                        .expressions
                        .get(scope.0 as usize)
                        .map_or_else(invalid_typed_core_span, |expression| expression.span),
                    message: "Typed Core unsafe scope must name an existing lexical block".into(),
                });
            }
        }
        // Scope is a property of each structural path, not of an arena node.
        // A shared expression reached both inside and outside unsafe must be
        // checked twice. The finite pair set also makes hostile cyclic graphs
        // total without authorizing a scope through a recursive edge.
        let mut visited = std::collections::BTreeSet::new();
        let mut pending = vec![(self.root, false)];
        while let Some((id, inherited)) = pending.pop() {
            if !visited.insert((id, inherited)) {
                continue;
            }
            let Some(expression) = self.expressions.get(id.0 as usize) else {
                continue;
            };
            let allowed = inherited
                || (self.unsafe_scopes.contains(&id)
                    && matches!(expression.kind, CoreKind::Block(_)));
            if let CoreKind::Call { callee, .. } = &expression.kind
                && !allowed
                && self
                    .expressions
                    .get(callee.0 as usize)
                    .is_some_and(|callee| {
                        matches!(
                            callee.ty,
                            Type::Callable {
                                safety: crate::Safety::Unsafe,
                                ..
                            }
                        )
                    })
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4202",
                    span: expression.span,
                    message:
                        "Typed Core unsafe invocation is outside an explicit lexical unsafe scope"
                            .into(),
                });
            }
            match &expression.kind {
                CoreKind::Closure { body, .. } => pending.push((*body, false)),
                CoreKind::Handle {
                    computation,
                    clauses,
                } => {
                    pending.push((*computation, allowed));
                    pending.extend(clauses.iter().map(|clause| (clause.body, false)));
                }
                CoreKind::Completion {
                    computation,
                    clauses,
                    ..
                } => {
                    pending.push((*computation, allowed));
                    pending.extend(clauses.iter().map(|clause| (clause.body, false)));
                }
                CoreKind::Assign { place, value } => {
                    pending.push((*value, allowed));
                    let mut place = place;
                    while let CorePlace::Field { base, .. } = place {
                        place = base;
                    }
                    if let CorePlace::Deref { reference, .. } = place {
                        pending.push((*reference, allowed));
                    }
                }
                kind => pending.extend(
                    core_children(kind)
                        .into_iter()
                        .map(|child| (child, allowed)),
                ),
            }
        }
    }

    /// Recheck projection evidence at the frozen Core boundary.  Source
    /// declaration validation establishes the public contract first, while
    /// this entry point makes imported or forged Core fail closed under the
    /// same lexical `where` evidence before ownership and MIR consumers run.
    pub fn validate_projection_obligations(
        &self,
        signatures: &ElaboratedInterface,
        ambient: &[(Type, crate::ElaboratedTraitReference)],
    ) -> Vec<CoreDiagnostic> {
        let mut terms = FrozenProjectionTerms::default();
        for (_, ty) in &self.parameters {
            terms.types.push(ty);
        }
        for expression in &self.expressions {
            terms.types.push(&expression.ty);
            collect_core_projection_terms(&expression.kind, &mut terms);
        }
        let span = self
            .expressions
            .get(self.root.0 as usize)
            .map(|expression| expression.span)
            .unwrap_or_else(invalid_typed_core_span);
        signatures
            .projection_obligation_diagnostics_for_frozen_terms(
                terms.types,
                terms.arguments,
                terms.effect_rows,
                ambient,
            )
            .into_iter()
            .map(|diagnostic| CoreDiagnostic {
                code: diagnostic.code,
                span,
                message: format!(
                    "Typed Core contains a projection without valid frozen evidence: {}",
                    diagnostic.message
                ),
            })
            .collect()
    }

    fn contains(&self, id: CoreId) -> bool {
        (id.0 as usize) < self.expressions.len()
    }
}

/// Borrowed type-kind carriers discovered in a frozen Core product.  Keeping
/// this separate from structural validation ensures projection evidence is
/// rechecked in every metadata position without treating rows or substitutions
/// as fabricated value types.
#[derive(Default)]
struct FrozenProjectionTerms<'a> {
    types: Vec<&'a Type>,
    arguments: Vec<&'a GenericArgument>,
    effect_rows: Vec<&'a EffectRow>,
}

fn collect_core_projection_terms<'a>(kind: &'a CoreKind, terms: &mut FrozenProjectionTerms<'a>) {
    match kind {
        CoreKind::Closure {
            parameters,
            environment,
            ..
        } => {
            terms.types.extend(parameters.iter().map(|(_, ty)| ty));
            terms
                .types
                .extend(environment.captures.iter().map(|capture| &capture.ty));
        }
        CoreKind::Assign { place, .. } => collect_place_projection_terms(place, terms),
        CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => {
            terms.arguments.extend(arguments)
        }
        CoreKind::TraitMethod {
            trait_arguments,
            method_arguments,
            ..
        } => terms
            .arguments
            .extend(trait_arguments.iter().chain(method_arguments)),
        CoreKind::Perform {
            effect,
            payload_types,
            ..
        } => {
            terms.arguments.extend(&effect.arguments);
            terms.types.extend(payload_types);
        }
        CoreKind::PatternTest {
            pattern,
            refinement,
            ..
        } => {
            collect_pattern_projection_terms(pattern, terms);
            terms
                .types
                .extend(refinement.binding_types.iter().map(|(_, ty)| ty));
        }
        CoreKind::Handle { clauses, .. } => {
            for clause in clauses {
                terms.arguments.extend(&clause.effect.arguments);
                terms.types.extend(&clause.payload_types);
                for pattern in &clause.patterns {
                    collect_pattern_projection_terms(pattern, terms);
                }
                terms.types.extend(clause.bindings.iter().map(|(_, ty)| ty));
                if let Some(continuation) = &clause.continuation {
                    terms.types.push(&continuation.parameter);
                    terms.types.push(&continuation.result);
                    terms.effect_rows.push(&continuation.effects);
                }
            }
        }
        CoreKind::Completion { clauses, .. } => {
            for clause in clauses {
                collect_pattern_projection_terms(&clause.pattern, terms);
                terms.types.extend(clause.bindings.iter().map(|(_, ty)| ty));
                if let Some(refinement) = &clause.refinement {
                    collect_pattern_projection_terms(&refinement.pattern, terms);
                    terms.types.extend(
                        refinement
                            .environment
                            .binding_types
                            .iter()
                            .map(|(_, ty)| ty),
                    );
                }
            }
        }
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Tuple(_)
        | CoreKind::Array(_)
        | CoreKind::Record { .. }
        | CoreKind::Field { .. }
        | CoreKind::Enum { .. }
        | CoreKind::Let { .. }
        | CoreKind::Label { .. }
        | CoreKind::Transfer { .. }
        | CoreKind::Call { .. }
        | CoreKind::IntrinsicCall { .. }
        | CoreKind::Block(_)
        | CoreKind::Borrow { .. }
        | CoreKind::Deref(_)
        | CoreKind::Move(_)
        | CoreKind::Error => {}
    }
}

fn collect_place_projection_terms<'a>(place: &'a CorePlace, terms: &mut FrozenProjectionTerms<'a>) {
    match place {
        CorePlace::Local { ty, .. } | CorePlace::Deref { ty, .. } => terms.types.push(ty),
        CorePlace::Field { base, ty, .. } => {
            collect_place_projection_terms(base, terms);
            terms.types.push(ty);
        }
        CorePlace::Error => {}
    }
}

fn collect_pattern_projection_terms<'a>(
    pattern: &'a CorePattern,
    terms: &mut FrozenProjectionTerms<'a>,
) {
    match pattern {
        CorePattern::Tuple(values) => {
            for value in values {
                collect_pattern_projection_terms(value, terms);
            }
        }
        CorePattern::Array { element, elements } => {
            terms.types.push(element);
            for element in elements {
                collect_pattern_projection_terms(element, terms);
            }
        }
        CorePattern::Record {
            field_types,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_types,
            fields,
            ..
        } => {
            terms.types.extend(field_types);
            for field in fields {
                terms.types.push(&field.ty);
                collect_pattern_projection_terms(&field.pattern, terms);
            }
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => {}
    }
}

struct CoreFingerprintEncoder<'a> {
    body: &'a TypedBody,
    numbers: std::collections::BTreeMap<CoreId, u32>,
    bytes: Vec<u8>,
}

impl CoreFingerprintEncoder<'_> {
    fn bytes(&mut self, value: &[u8]) {
        self.bytes
            .extend_from_slice(&(value.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(value);
    }

    fn debug(&mut self, value: impl std::fmt::Debug) {
        self.bytes(format!("{value:?}").as_bytes());
    }

    fn ty(&mut self, value: &Type) {
        self.bytes(&canonical_type_encoding(value));
    }

    fn types(&mut self, values: &[Type]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.ty(value);
        }
    }

    fn generic_arguments(&mut self, values: &[GenericArgument]) {
        self.bytes(&canonical_generic_arguments_encoding(values));
    }

    fn effect(&mut self, value: &EffectInstance) {
        self.debug(value.definition);
        self.generic_arguments(&value.arguments);
    }

    fn effect_row(&mut self, value: &EffectRow) {
        // Effect rows are already canonical frozen identities at this
        // boundary, including delayed projections and their tail.
        self.debug(value);
    }

    fn pattern(&mut self, value: &CorePattern) {
        match value {
            CorePattern::Any => self.bytes(b"any"),
            CorePattern::Bind { name } => {
                self.bytes(b"bind");
                self.bytes(name.as_bytes());
            }
            CorePattern::Literal(value) => {
                self.bytes(b"literal");
                self.bytes(value.as_bytes());
            }
            CorePattern::Tuple(values) => {
                self.bytes(b"tuple");
                self.bytes(&(values.len() as u64).to_le_bytes());
                for value in values {
                    self.pattern(value);
                }
            }
            CorePattern::Array { element, elements } => {
                self.bytes(b"array");
                self.ty(element);
                self.bytes(&(elements.len() as u64).to_le_bytes());
                for element in elements {
                    self.pattern(element);
                }
            }
            CorePattern::Record {
                definition,
                field_types,
                field_count,
                fields,
            }
            | CorePattern::Enum {
                definition,
                field_types,
                field_count,
                fields,
                ..
            } => {
                self.bytes(if matches!(value, CorePattern::Record { .. }) {
                    b"record"
                } else {
                    b"enum"
                });
                self.debug(definition);
                if let CorePattern::Enum { variant, .. } = value {
                    self.bytes(&variant.to_le_bytes());
                }
                self.bytes(&field_count.to_le_bytes());
                self.bytes(&(field_types.len() as u64).to_le_bytes());
                for field_type in field_types {
                    self.ty(field_type);
                }
                self.bytes(&(fields.len() as u64).to_le_bytes());
                for field in fields {
                    self.bytes(&field.index.to_le_bytes());
                    self.ty(&field.ty);
                    self.pattern(&field.pattern);
                }
            }
            CorePattern::Error => self.bytes(b"error"),
        }
    }

    fn bindings(&mut self, values: &[(String, Type)]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for (name, ty) in values {
            self.bytes(name.as_bytes());
            self.ty(ty);
        }
    }

    fn refinement(&mut self, value: &RefinementEnvironment) {
        self.debug(value.brand);
        self.debug(&value.subject);
        self.bytes(&(value.bindings.len() as u64).to_le_bytes());
        for binding in &value.bindings {
            self.bytes(binding.as_bytes());
        }
        self.bindings(&value.binding_types);
        self.debug(&value.binding_keys);
        self.bytes(&[value.sealed as u8]);
    }

    fn capture_environment(&mut self, value: &CaptureEnvironment) {
        self.debug(value.brand);
        self.bytes(&(value.captures.len() as u64).to_le_bytes());
        for capture in &value.captures {
            self.bytes(capture.name.as_bytes());
            self.debug(capture.mode);
            self.ty(&capture.ty);
        }
        self.debug(&value.post_states);
        self.debug(value.runs_in.environment);
        self.debug(value.runs_in.callable);
        self.effect_row(&value.runs_in.effects);
        self.debug(&value.runs_in.post_states);
        self.bytes(&[value.runs_in.sealed as u8]);
        self.bytes(&[value.sealed as u8]);
    }

    fn place(&mut self, value: &CorePlace) {
        match value {
            CorePlace::Local { name, ty } => {
                self.bytes(b"local");
                self.bytes(name.as_bytes());
                self.ty(ty);
            }
            CorePlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                self.bytes(b"field");
                self.place(base);
                self.bytes(&index.to_le_bytes());
                self.bytes(&field_count.to_le_bytes());
                self.ty(ty);
            }
            CorePlace::Deref {
                reference,
                ty,
                unique,
            } => {
                self.bytes(b"deref");
                self.id(*reference);
                self.ty(ty);
                self.bytes(&[*unique as u8]);
            }
            CorePlace::Error => self.bytes(b"error"),
        }
    }

    fn id(&mut self, id: CoreId) {
        if let Some(number) = self.numbers.get(&id).copied() {
            self.bytes(b"ref");
            self.bytes(&number.to_le_bytes());
            return;
        }
        let number = self.numbers.len() as u32;
        self.numbers.insert(id, number);
        self.bytes(b"node");
        self.bytes(&number.to_le_bytes());
        let Some(expression) = self.body.expressions.get(id.0 as usize) else {
            // Invalid Core never becomes a release product, but representing
            // this state deterministically keeps inspection tools total.
            self.bytes(b"missing");
            self.bytes(&id.0.to_le_bytes());
            return;
        };
        self.ty(&expression.ty);
        if self.body.unsafe_scopes.contains(&id) {
            self.bytes(b"explicit-unsafe-scope");
        }
        self.kind(&expression.kind);
    }

    fn ids(&mut self, values: &[CoreId]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.id(*value);
        }
    }

    fn kind(&mut self, kind: &CoreKind) {
        match kind {
            CoreKind::Literal(value) => {
                self.bytes(b"literal");
                self.bytes(value.as_bytes());
            }
            CoreKind::Local(name) => {
                self.bytes(b"local");
                self.bytes(name.as_bytes());
            }
            CoreKind::Resumption { id, name } => {
                self.bytes(b"resumption");
                self.debug(id);
                self.bytes(name.as_bytes());
            }
            CoreKind::LabelValue { brand } => {
                self.bytes(b"label-value");
                self.debug(brand);
            }
            CoreKind::Function {
                definition,
                arguments,
                host_import,
            } => {
                self.bytes(b"function");
                self.debug(definition);
                self.generic_arguments(arguments);
                match host_import {
                    Some(import) => {
                        self.bytes(b"host-import");
                        self.bytes(import.capability.as_bytes());
                        self.bytes(import.symbol.as_bytes());
                    }
                    None => self.bytes(b"ordinary-function"),
                }
            }
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred,
            } => {
                self.bytes(b"trait-method");
                self.debug(evidence);
                self.debug(method);
                self.generic_arguments(trait_arguments);
                self.generic_arguments(method_arguments);
                if let Some(deferred) = deferred {
                    self.bytes(b"deferred-trait-method");
                    self.debug(&deferred.relation.definition);
                    self.generic_arguments(&deferred.relation.arguments);
                    self.ty(&deferred.subject);
                    self.bytes(deferred.name.as_bytes());
                }
            }
            CoreKind::Constant {
                definition,
                arguments,
            } => {
                self.bytes(b"constant");
                self.debug(definition);
                self.generic_arguments(arguments);
            }
            CoreKind::Tuple(values) => {
                self.bytes(b"tuple");
                self.ids(values);
            }
            CoreKind::Array(values) => {
                self.bytes(b"array");
                self.ids(values);
            }
            CoreKind::Record { definition, fields } => {
                self.bytes(b"record");
                self.debug(definition);
                self.ids(fields);
            }
            CoreKind::Field {
                base,
                index,
                field_count,
            } => {
                self.bytes(b"field");
                self.bytes(&index.to_le_bytes());
                self.bytes(&field_count.to_le_bytes());
                self.id(*base);
            }
            CoreKind::Enum {
                definition,
                variant,
                fields,
            } => {
                self.bytes(b"enum");
                self.debug(definition);
                self.bytes(&variant.to_le_bytes());
                self.ids(fields);
            }
            CoreKind::PatternTest {
                subject,
                pattern,
                refinement,
            } => {
                self.bytes(b"pattern-test");
                self.pattern(pattern);
                self.refinement(refinement);
                self.id(*subject);
            }
            CoreKind::Closure {
                callable,
                parameters,
                environment,
                body,
            } => {
                self.bytes(b"closure");
                self.debug(callable);
                self.bindings(parameters);
                self.capture_environment(environment);
                self.id(*body);
            }
            CoreKind::Let { name, value } => {
                self.bytes(b"let");
                self.bytes(name.as_bytes());
                self.id(*value);
            }
            CoreKind::Label { brand, body } => {
                self.bytes(b"label");
                self.debug(brand);
                self.id(*body);
            }
            CoreKind::Transfer { brand, value } => {
                self.bytes(b"transfer");
                self.debug(brand);
                self.id(*value);
            }
            CoreKind::Assign { place, value } => {
                self.bytes(b"assign");
                self.place(place);
                self.id(*value);
            }
            CoreKind::Call {
                callee,
                arguments,
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                self.bytes(b"call");
                self.id(*callee);
                self.ids(arguments);
                self.debug(reference_contract);
                self.debug(reference_origin);
                self.debug(reference_shape);
            }
            CoreKind::Perform {
                effect,
                operation,
                payload_types,
                arguments,
                terminal,
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                self.bytes(b"perform");
                self.effect(effect);
                self.bytes(&operation.to_le_bytes());
                self.bytes(&[*terminal as u8]);
                self.types(payload_types);
                self.ids(arguments);
                self.debug(reference_contract);
                self.debug(reference_origin);
                self.debug(reference_shape);
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.bytes(b"handle");
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.debug(clause.brand);
                    self.effect(&clause.effect);
                    self.bytes(&clause.operation.to_le_bytes());
                    self.types(&clause.payload_types);
                    self.bytes(&(clause.patterns.len() as u64).to_le_bytes());
                    for pattern in &clause.patterns {
                        self.pattern(pattern);
                    }
                    self.bindings(&clause.bindings);
                    self.debug(&clause.resumption);
                    match &clause.continuation {
                        Some(continuation) => {
                            self.bytes(b"continuation");
                            self.debug(continuation.brand);
                            self.ty(&continuation.parameter);
                            self.ty(&continuation.result);
                            self.ty(&Type::Callable {
                                safety: crate::Safety::Safe,
                                lifetime_binders: 0,
                                parameters: vec![],
                                result: Box::new(Type::Unit),
                                effects: continuation.effects.clone(),
                                invocation: continuation.invocation,
                            });
                            self.bytes(&continuation.direct_uses.to_le_bytes());
                        }
                        None => self.bytes(b"no-continuation"),
                    }
                    self.bytes(&[clause.terminal as u8]);
                    self.id(clause.body);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
                handles_operations,
                refinement_test,
            } => {
                self.bytes(b"completion");
                if let Some(environment) = refinement_test { self.bytes(b"binding-pack-producer"); self.refinement(environment); }
                self.bytes(&[*handles_operations as u8]);
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.pattern(&clause.pattern);
                    self.bindings(&clause.bindings);
                    match &clause.refinement {
                        Some(refinement) => {
                            self.bytes(b"refinement");
                            self.refinement(&refinement.environment);
                            self.id(refinement.subject);
                            self.pattern(&refinement.pattern);
                        }
                        None => self.bytes(b"no-refinement"),
                    }
                    self.id(clause.body);
                }
            }
            CoreKind::IntrinsicCall {
                operator,
                arguments,
            } => {
                self.bytes(b"intrinsic-call");
                self.bytes(operator.as_bytes());
                self.bytes(&(arguments.len() as u64).to_le_bytes());
                for argument in arguments {
                    self.id(*argument);
                }
            }
            CoreKind::Block(values) => {
                self.bytes(b"block");
                self.ids(values);
            }
            CoreKind::Borrow { unique, value } => {
                self.bytes(b"borrow");
                self.bytes(&[*unique as u8]);
                self.id(*value);
            }
            CoreKind::Deref(value) => {
                self.bytes(b"deref");
                self.id(*value);
            }
            CoreKind::Move(value) => {
                self.bytes(b"move");
                self.id(*value);
            }
            CoreKind::Error => self.bytes(b"error"),
        }
    }
}

fn core_children(kind: &CoreKind) -> Vec<CoreId> {
    match kind {
        CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
            values.clone()
        }
        CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => fields.clone(),
        CoreKind::Field { base, .. }
        | CoreKind::PatternTest { subject: base, .. }
        | CoreKind::Borrow { value: base, .. }
        | CoreKind::Deref(base)
        | CoreKind::Move(base) => vec![*base],
        CoreKind::Closure { body, .. }
        | CoreKind::Let { value: body, .. }
        | CoreKind::Label { body, .. }
        | CoreKind::Transfer { value: body, .. } => vec![*body],
        CoreKind::Assign { place, value } => {
            let mut children = vec![*value];
            if let CorePlace::Deref { reference, .. } = place {
                children.push(*reference);
            }
            children
        }
        CoreKind::Call {
            callee, arguments, ..
        } => std::iter::once(*callee)
            .chain(arguments.iter().copied())
            .collect(),
        CoreKind::Perform { arguments, .. } => arguments.clone(),
        CoreKind::Handle {
            computation,
            clauses,
        } => std::iter::once(*computation)
            .chain(clauses.iter().map(|clause| clause.body))
            .collect(),
        CoreKind::Completion {
            computation,
            clauses,
            ..
        } => std::iter::once(*computation)
            .chain(clauses.iter().map(|clause| clause.body))
            .collect(),
        CoreKind::IntrinsicCall { arguments, .. } => arguments.clone(),
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Function { .. }
        | CoreKind::TraitMethod { .. }
        | CoreKind::Constant { .. }
        | CoreKind::Error => vec![],
    }
}

fn core_kind_is_recovered(kind: &CoreKind) -> bool {
    match kind {
        CoreKind::Error => true,
        CoreKind::Assign {
            place: CorePlace::Error,
            ..
        } => true,
        CoreKind::PatternTest { pattern, .. } => pattern_is_recovered(pattern),
        CoreKind::Handle { clauses, .. } => clauses.iter().any(|clause| {
            clause.patterns.iter().any(pattern_is_recovered)
                || matches!(clause.resumption, CoreHandlerResumption::Terminal)
                    && clause.continuation.is_some()
        }),
        CoreKind::Completion { clauses, .. } => clauses
            .iter()
            .any(|clause| pattern_is_recovered(&clause.pattern)),
        _ => false,
    }
}

fn core_structural_error(kind: &CoreKind, ty: &Type) -> Option<String> {
    match kind {
        CoreKind::Closure {
            callable,
            environment,
            ..
        } => capture_environment_error(*callable, environment, ty),
        CoreKind::Field {
            index, field_count, ..
        } if index >= field_count => Some(format!(
            "Typed Core field projection index {index} is outside structural arity {field_count}"
        )),
        CoreKind::Assign { place, .. } => place_structural_error(place),
        CoreKind::PatternTest {
            pattern,
            refinement,
            ..
        } => pattern_structural_error(pattern).or_else(|| refinement_environment_error(refinement)),
        CoreKind::Handle { clauses, .. } => handler_clause_error(clauses).or_else(|| {
            clauses
                .iter()
                .flat_map(|clause| clause.patterns.iter())
                .find_map(pattern_structural_error)
        }),
        CoreKind::Completion { clauses, .. } => clauses.iter().find_map(|clause| {
            pattern_structural_error(&clause.pattern).or_else(|| {
                clause.refinement.as_ref().and_then(|refinement| {
                    refinement_environment_error(&refinement.environment)
                        .or_else(|| pattern_structural_error(&refinement.pattern))
                })
            })
        }),
        _ => None,
    }
}

/// Validate the proof edge between an `is` decision and the completion arm
/// which opens its positive binders.  A refinement environment is not merely
/// a convenient projection recipe: it is branded evidence that one exact
/// `PatternTest` evaluated true.  In particular, a persisted or otherwise
/// forged Core graph must not be able to attach a copied environment to an
/// unrelated completion arm and thereby introduce its binders into PlaceFlow
/// or MIR without the deciding boolean edge.
fn refinement_test_construction(body: &TypedBody, producer: CoreId) -> Result<Vec<CoreId>, String> {
    let invalid = || "Typed Core binding-pack producer does not preserve its immediate pattern decision".to_string();
    let expression = body.expressions.get(producer.0 as usize).ok_or_else(invalid)?;
    let CoreKind::Completion { computation, clauses, refinement_test: Some(environment), handles_operations: false } = &expression.kind else { return Err(invalid()); };
    if let Some(error) = refinement_environment_error(environment) { return Err(error); }
    let [yes, no] = clauses.as_slice() else { return Err(invalid()); };
    if !matches!(no.pattern, CorePattern::Any) || !no.bindings.is_empty() || yes.refinement.is_some() || no.refinement.is_some() { return Err(invalid()); }
    let subject = body.expressions.get(computation.0 as usize).ok_or_else(invalid)?;
    let mut bindings = vec![];
    collect_pattern_binding_types(&yes.pattern, &subject.ty, &mut bindings).ok_or_else(invalid)?;
    for (_, ty) in &mut bindings { *ty = refinement_binding_type(ty.clone()); }
    if bindings != environment.binding_types || yes.bindings != bindings { return Err(invalid()); }
    let name = match &subject.kind { CoreKind::Local(name) => Some(name), _ => None };
    if name != environment.subject.as_ref() { return Err(invalid()); }
    let Type::Nominal { definition: test, arguments } = &expression.ty else { return Err(invalid()); };
    let parents = |value: CoreId| body.expressions.iter().enumerate().flat_map(|(index, expression)| {
        core_children(&expression.kind).into_iter().filter(move |child| *child == value).map(move |_| CoreId(index as u32))
    }).collect::<Vec<_>>();
    let mut packs = vec![];
    let mut variants = vec![];
    for (index, clause) in clauses.iter().enumerate() {
        let positive = index == 0;
        let expected = environment.binding_pack_type(positive, Lifetime::Elided)?;
        if arguments.get(index) != Some(&GenericArgument::Type(expected.clone())) || arguments.len() != 2 { return Err(invalid()); }
        let constructor = body.expressions.get(clause.body.0 as usize).ok_or_else(invalid)?;
        let CoreKind::Enum { definition, variant, fields } = &constructor.kind else { return Err(invalid()); };
        if definition != test || constructor.ty != expression.ty || fields.len() != 1 || parents(clause.body) != [producer] { return Err(invalid()); }
        variants.push(*variant);
        let pack = fields[0];
        let record = body.expressions.get(pack.0 as usize).ok_or_else(invalid)?;
        let CoreKind::Record { definition, fields } = &record.kind else { return Err(invalid()); };
        if *definition != crate::refinement::bindings_definition() || record.ty != expected || parents(pack) != [clause.body]
            || fields.len() != clause.bindings.len() { return Err(invalid()); }
        for (field, (name, ty)) in fields.iter().zip(&clause.bindings) {
            let field = body.expressions.get(field.0 as usize).ok_or_else(invalid)?;
            if !matches!(&field.kind, CoreKind::Local(actual) if actual == name) || &field.ty != ty { return Err(invalid()); }
        }
        packs.push(pack);
    }
    if variants[0] == variants[1] { return Err(invalid()); }
    Ok(packs)
}

fn pattern_refinement_error(body: &TypedBody, kind: &CoreKind) -> Option<String> {
    let CoreKind::PatternTest { subject, pattern, refinement } = kind else { return None; };
    let subject = body.expressions.get(subject.0 as usize)?;
    let mut bindings = Vec::new();
    if collect_pattern_binding_types(pattern, &subject.ty, &mut bindings).is_none() {
        return Some("Typed Core refinement cannot derive bindings from its subject's structural pattern".into());
    }
    for (_, ty) in &mut bindings { *ty = refinement_binding_type(ty.clone()); }
    if bindings != refinement.binding_types {
        return Some("Typed Core refinement binding types do not match the originating structural pattern".into());
    }
    let name = match &subject.kind { CoreKind::Local(name) => Some(name), _ => None };
    if refinement.subject.as_ref() != name {
        return Some("Typed Core refinement subject does not match its once-evaluated producer".into());
    }
    None
}

fn completion_refinement_error(body: &TypedBody, kind: &CoreKind) -> Option<String> {
    let CoreKind::Completion {
        computation,
        clauses,
        ..
    } = kind
    else {
        return None;
    };
    if !clauses.iter().any(|clause| clause.refinement.is_some()) {
        return None;
    }
    let Some(computation) = body.expressions.get(computation.0 as usize) else {
        // The ordinary child-edge check reports the missing expression with
        // its exact owner.  Do not manufacture a second, less precise error.
        return None;
    };
    let CoreKind::PatternTest {
        subject,
        pattern,
        refinement: environment,
    } = &computation.kind
    else {
        return Some(
            "Typed Core completion refinement is not produced by its completion computation's pattern test"
                .into(),
        );
    };
    let subject_expression = body.expressions.get(subject.0 as usize)?;
    let mut expected_bindings = Vec::new();
    if collect_pattern_binding_types(pattern, &subject_expression.ty, &mut expected_bindings)
        .is_none()
    {
        return Some(
            "Typed Core completion refinement cannot derive binders from the originating pattern-test layout"
                .into(),
        );
    }
    for (_, ty) in &mut expected_bindings {
        *ty = refinement_binding_type(ty.clone());
    }
    for clause in clauses {
        let Some(branch) = &clause.refinement else {
            continue;
        };
        if !core_pattern_is_true(&clause.pattern) {
            return Some(
                "Typed Core completion refinement is attached to an arm that does not prove the test result true"
                    .into(),
            );
        }
        if branch.subject != *subject
            || branch.pattern != *pattern
            || branch.environment != *environment
        {
            return Some(
                "Typed Core completion refinement does not preserve the exact originating pattern-test evidence"
                    .into(),
            );
        }
        if branch.environment.binding_types != expected_bindings {
            return Some(
                "Typed Core completion refinement binding types do not match the originating structural pattern"
                    .into(),
            );
        }
    }
    None
}

/// Recover the exact type of every structural binder from the frozen pattern
/// layout.  This duplicates no source lookup: `CorePattern` already owns the
/// instantiated tuple, array, and nominal field types that MIR will project.
/// Returning `None` delegates malformed layout reporting to the existing
/// structural validator, keeping diagnostics deterministic.
pub(crate) fn collect_pattern_binding_types(
    pattern: &CorePattern,
    subject: &Type,
    bindings: &mut Vec<(String, Type)>,
) -> Option<()> {
    match pattern {
        CorePattern::Any | CorePattern::Literal(_) => Some(()),
        CorePattern::Bind { name } => {
            bindings.push((name.clone(), subject.clone()));
            Some(())
        }
        CorePattern::Tuple(patterns) => {
            let Type::Tuple(types) = subject else {
                return None;
            };
            if patterns.len() != types.len() {
                return None;
            }
            for (pattern, ty) in patterns.iter().zip(types) {
                collect_pattern_binding_types(pattern, ty, bindings)?;
            }
            Some(())
        }
        CorePattern::Array { element, elements } => {
            let Type::Array(subject_element) = subject else {
                return None;
            };
            if **subject_element != *element {
                return None;
            }
            for pattern in elements {
                collect_pattern_binding_types(pattern, element, bindings)?;
            }
            Some(())
        }
        CorePattern::Record {
            definition,
            field_types,
            field_count,
            fields,
        }
        | CorePattern::Enum {
            definition,
            field_types,
            field_count,
            fields,
            ..
        } => {
            let Type::Nominal {
                definition: subject_definition,
                ..
            } = subject
            else {
                return None;
            };
            if subject_definition != definition || *field_count != field_types.len() as u32 {
                return None;
            }
            for field in fields {
                let field_ty = field_types.get(field.index as usize)?;
                if &field.ty != field_ty {
                    return None;
                }
                collect_pattern_binding_types(&field.pattern, field_ty, bindings)?;
            }
            Some(())
        }
        CorePattern::Error => None,
    }
}

/// Refinements observe their subject. The representation-independent scalar
/// cases may copy; all other bindings retain a shared view of the selected
/// place. In particular an affine aggregate or unique reference is never
/// transferred merely because its structural test succeeded.
pub(crate) fn refinement_binding_type(ty: Type) -> Type {
    match ty {
        Type::Unit | Type::Never | Type::Scalar(_) | Type::RawPointer { .. }
        | Type::Reference { mutability: Mutability::Shared, .. } => ty,
        _ => Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Elided,
            referent: Box::new(ty),
        },
    }
}

/// `Perform` is an operation-call boundary with no callee expression from
/// which later passes can recover a parameter contract.  Freeze and validate
/// the selected ABI directly in Core so UseFlow, PlaceFlow, and a future
/// persisted-Core reader agree on which payload capability receives a
/// transfer.
fn perform_payload_contract_error(body: &TypedBody, kind: &CoreKind) -> Option<String> {
    let CoreKind::Perform {
        arguments,
        payload_types,
        ..
    } = kind
    else {
        return None;
    };
    if arguments.len() != payload_types.len() {
        return Some(format!(
            "effect operation has {} payload arguments but {} frozen payload contract entries",
            arguments.len(),
            payload_types.len()
        ));
    }
    for (index, (argument, payload_type)) in arguments.iter().zip(payload_types).enumerate() {
        let Some(actual) = body
            .expressions
            .get(argument.0 as usize)
            .map(|value| &value.ty)
        else {
            // Missing child IDs are independently diagnosed by the general
            // Core graph validator above.
            continue;
        };
        // A transfer in a strict payload position abandons evaluation before
        // the operation is performed. It therefore has no runtime payload to
        // validate against this selected ABI; `Never` is the ordinary typed
        // representation of that terminal edge, not a mismatched argument.
        if actual != payload_type && !matches!(actual, Type::Never) {
            return Some(format!(
                "effect operation payload {index} does not match its frozen selected parameter contract"
            ));
        }
    }
    None
}

fn call_reference_origin_error(body: &TypedBody, kind: &CoreKind, result: &Type) -> Option<String> {
    let (arguments, reference_origin, reference_shape, boundary, callable_contract) = match kind {
        CoreKind::Call {
            arguments,
            reference_contract,
            reference_origin,
            reference_shape,
            ..
        } => (
            arguments,
            reference_origin,
            reference_shape,
            "call",
            // The callee expression may have already opened its lifetime
            // binders. The separately frozen contract retains the
            // interface-aware nominal relation from before that opening.
            Some(reference_contract.clone()),
        ),
        CoreKind::Perform {
            arguments,
            reference_contract,
            reference_origin,
            reference_shape,
            ..
        } => (
            arguments,
            reference_origin,
            reference_shape,
            "effect operation",
            Some(reference_contract.clone()),
        ),
        _ => return None,
    };
    // A declaration-generic contract may remain `Opaque` even after its
    // realized result specializes to a scalar or static reference.  The
    // shape is intentionally more precise in those cases; all other origin
    // forms have one exact compatible shape.
    let shape_matches_origin = match reference_origin {
        CallReferenceOrigin::None => matches!(reference_shape, CallReferenceShape::None),
        CallReferenceOrigin::External => {
            matches!(reference_shape, CallReferenceShape::External)
        }
        CallReferenceOrigin::Unsafe => matches!(reference_shape, CallReferenceShape::Unsafe),
        CallReferenceOrigin::Paths(_) => {
            matches!(reference_shape, CallReferenceShape::CallerPaths)
        }
        CallReferenceOrigin::Opaque => matches!(
            reference_shape,
            CallReferenceShape::None
                | CallReferenceShape::External
                | CallReferenceShape::OpaquePotentiallyReference
        ),
    };
    if !shape_matches_origin {
        return Some(format!(
            "reference-valued {boundary} does not match its frozen result shape"
        ));
    }
    if matches!(reference_origin, CallReferenceOrigin::Unsafe) {
        let CoreKind::Call { callee, .. } = kind else {
            return Some("only an unsafe callable can establish raw-reference provenance".into());
        };
        if !body.contains(*callee) { return None; }
        if !matches!(body.expression(*callee).ty, Type::Callable { safety: crate::Safety::Unsafe, .. }) {
            return Some("raw-reference provenance requires an unsafe callable".into());
        }
    }
    if let Some(contract) = callable_contract
        && !matches!(contract, CallReferenceOrigin::Opaque)
        && reference_origin != &contract
    {
        return Some(format!(
            "reference-valued {boundary} does not match its frozen callable lifetime contract"
        ));
    }
    let is_reference = known_reference_bearing_type(result);
    match reference_origin {
        CallReferenceOrigin::None if is_reference => Some(format!(
            "reference-valued {boundary} omitted its frozen caller-region provenance"
        )),
        CallReferenceOrigin::Paths(paths) => {
            if !known_reference_bearing_type(result) && !matches!(result, Type::Nominal { .. }) {
                return Some(format!(
                    "{boundary}-reference paths require a reference-bearing result"
                ));
            }
            let mut result_paths = std::collections::BTreeSet::new();
            for path in paths {
                if !result_paths.insert((path.result_fields.clone(), path.argument, path.argument_fields.clone())) {
                    return Some(format!(
                        "{boundary}-reference provenance repeats an argument/result projection relation"
                    ));
                }
                let Some(argument) = arguments.get(path.argument as usize) else {
                    return Some(format!(
                        "{boundary}-reference provenance indexes a missing argument"
                    ));
                };
                if !body.contains(*argument) {
                    return None;
                }
            }
            None
        }
        // `reference_shape` was sealed from a structural traversal of the
        // realized result.  An `External` shape therefore proves that every
        // reference leaf is static, including leaves nested in a source
        // record such as `Slice<'static, u8>`.  Restricting this to a
        // top-level `&'static T` made sound library wrappers impossible and
        // incorrectly rejected their frozen external provenance.
        CallReferenceOrigin::External | CallReferenceOrigin::Unsafe => None,
        // An unconstrained generic result may later instantiate to a scalar
        // or a reference. Its call-site Core has no direct path to validate;
        // ownership consumers reject it only when the frozen concrete use is
        // reference-bearing.
        CallReferenceOrigin::Opaque => None,
        CallReferenceOrigin::None => None,
    }
}

fn known_reference_bearing_type(value: &Type) -> bool {
    matches!(value, Type::Reference { .. })
        || matches!(value, Type::Tuple(values) if values.iter().any(known_reference_bearing_type))
}

pub(crate) fn refinement_environment_error(environment: &RefinementEnvironment) -> Option<String> {
    if !environment.sealed {
        return Some("Typed Core pattern test has an unsealed refinement environment".into());
    }
    if environment.binding_keys.len() != environment.bindings.len()
        || environment.binding_keys.iter().enumerate().any(|(index, key)| {
            key.environment != environment.brand || key.binder as usize != index
        }) {
        return Some("Typed Core refinement environment has noncanonical branded binding keys".into());
    }
    let mut bindings = std::collections::BTreeSet::new();
    for binding in &environment.bindings {
        if !bindings.insert(binding) {
            return Some(format!(
                "Typed Core refinement environment repeats binding `{binding}`"
            ));
        }
    }
    if environment.bindings.len() != environment.binding_types.len()
        || environment
            .bindings
            .iter()
            .zip(&environment.binding_types)
            .any(|(name, (typed_name, _))| name != typed_name)
    {
        return Some("Typed Core refinement environment has inconsistent binding types".into());
    }
    None
}

fn handler_clause_error(clauses: &[CoreHandlerClause]) -> Option<String> {
    for (index, clause) in clauses.iter().enumerate() {
        let CallableBrand::HandlerClause {
            owner,
            clause: branded,
        } = clause.brand
        else {
            return Some("Typed Core handler arm lacks a handler-clause callable brand".into());
        };
        if branded != index as u32 {
            return Some("Typed Core handler clause brand has a noncanonical clause index".into());
        }
        if let Some(continuation) = &clause.continuation
            && continuation.brand
                != (CallableBrand::Continuation {
                    owner,
                    clause: branded,
                })
        {
            return Some("Typed Core continuation brand does not belong to its handler arm".into());
        }
    }
    None
}

pub(crate) fn capture_environment_error(
    callable: CallableId,
    environment: &CaptureEnvironment,
    callable_ty: &Type,
) -> Option<String> {
    if !environment.sealed {
        return Some("Typed Core closure has an unsealed capture environment".into());
    }
    if environment.brand.callable != callable {
        return Some("Typed Core closure environment brand belongs to another callable".into());
    }
    let Type::Callable {
        lifetime_binders,
        effects,
        ..
    } = callable_ty
    else {
        return Some("Typed Core closure lacks a callable type for its RunsIn evidence".into());
    };
    if !environment.runs_in.sealed
        || environment.runs_in.environment != environment.brand
        || environment.runs_in.callable != callable
        || environment.runs_in.post_states != environment.post_states
    {
        return Some(
            "Typed Core closure has forged or incomplete RunsIn environment evidence".into(),
        );
    }
    let body_effects = if *lifetime_binders == 0 {
        effects.clone()
    } else {
        open_hrtb_callable_body_effect_row(effects.clone(), 0)
    };
    if environment.runs_in.effects != body_effects {
        return Some(
            "Typed Core RunsIn evidence does not match the closure effect contract".into(),
        );
    }
    let mut names = std::collections::BTreeSet::new();
    for capture in &environment.captures {
        if !names.insert(&capture.name) {
            return Some(format!(
                "Typed Core closure environment repeats capture `{}`",
                capture.name
            ));
        }
    }
    if environment.post_states.len() != environment.captures.len()
        || environment
            .captures
            .iter()
            .zip(&environment.post_states)
            .any(|(capture, state)| capture.name != state.name || capture.mode != state.mode)
    {
        return Some("Typed Core closure environment has inconsistent capture post-states".into());
    }
    None
}

fn place_structural_error(place: &CorePlace) -> Option<String> {
    match place {
        CorePlace::Field {
            base,
            index,
            field_count,
            ..
        } if index >= field_count => Some(format!(
            "Typed Core assignment field index {index} is outside structural arity {field_count}"
        )),
        CorePlace::Field { base, .. } => place_structural_error(base),
        CorePlace::Deref { .. } => None,
        CorePlace::Local { .. } | CorePlace::Error => None,
    }
}

/// Compare only stable source-place shape. Refinement facts are scoped to a
/// syntactic storage path, not a particular Core allocation ordinal: the
/// handler test and a later `value.0` each elaborate their own `Local` and
/// `Deref` nodes while referring to the same place.
fn same_core_place_shape(expressions: &[CoreExpr], left: CoreId, right: CoreId) -> bool {
    match (
        &expressions[left.0 as usize].kind,
        &expressions[right.0 as usize].kind,
    ) {
        (CoreKind::Local(left), CoreKind::Local(right)) => left == right,
        (CoreKind::Deref(left), CoreKind::Deref(right)) => {
            same_core_place_shape(expressions, *left, *right)
        }
        (
            CoreKind::Field {
                base: left,
                index: left_index,
                ..
            },
            CoreKind::Field {
                base: right,
                index: right_index,
                ..
            },
        ) => left_index == right_index && same_core_place_shape(expressions, *left, *right),
        _ => false,
    }
}

fn pattern_structural_error(pattern: &CorePattern) -> Option<String> {
    match pattern {
        CorePattern::Tuple(values) => values.iter().find_map(pattern_structural_error),
        CorePattern::Array { elements, .. } => elements.iter().find_map(pattern_structural_error),
        CorePattern::Record {
            field_types,
            field_count,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_types,
            field_count,
            fields,
            ..
        } => {
            if *field_count != field_types.len() as u32 {
                return Some(format!(
                    "Typed Core pattern layout has {} fields but frozen arity is {field_count}",
                    field_types.len()
                ));
            }
            let mut seen = std::collections::BTreeSet::new();
            for field in fields {
                if field.index >= *field_count {
                    return Some(format!(
                        "Typed Core pattern field index {} is outside structural arity {field_count}",
                        field.index
                    ));
                }
                if !seen.insert(field.index) {
                    return Some(format!(
                        "Typed Core pattern repeats structural field index {}",
                        field.index
                    ));
                }
                if field.ty != field_types[field.index as usize] {
                    return Some(format!(
                        "Typed Core pattern field {} does not match its frozen layout type",
                        field.index
                    ));
                }
                if let Some(error) = pattern_structural_error(&field.pattern) {
                    return Some(error);
                }
            }
            None
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => None,
    }
}

fn pattern_is_recovered(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Error => true,
        CorePattern::Tuple(values) => values.iter().any(pattern_is_recovered),
        CorePattern::Array { elements, .. } => elements.iter().any(pattern_is_recovered),
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => fields
            .iter()
            .any(|field| pattern_is_recovered(&field.pattern)),
        CorePattern::Any | CorePattern::Bind { .. } | CorePattern::Literal(_) => false,
    }
}

/// Whether a semantic type tree still contains body-local uncertainty.  Core
/// uses this before freezing a body, and MIR repeats the same check because a
/// persisted or forged Core product must not get a weaker route to execution.
pub(crate) fn type_contains_inference(ty: &Type) -> bool {
    match ty {
        Type::Infer(_) => true,
        Type::Nominal { arguments, .. } => {
            arguments.iter().any(generic_argument_contains_inference)
        }
        Type::Tuple(arguments) => arguments.iter().any(type_contains_inference),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_contains_inference(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_inference)
                || item_arguments
                    .iter()
                    .any(generic_argument_contains_inference)
        }
        Type::Array(element)
        | Type::RawPointer { pointee: element, .. }
        | Type::StaticData { element, .. } => type_contains_inference(element),
        Type::Reference { lifetime, referent, .. } => {
            matches!(lifetime, Lifetime::Infer(_)) || type_contains_inference(referent)
        }
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters.iter().any(type_contains_inference)
                || type_contains_inference(result)
                || effects.effects.iter().any(|effect| {
                    effect
                        .arguments
                        .iter()
                        .any(generic_argument_contains_inference)
                })
                || matches!(effects.tail, Some(crate::types::EffectTail::Infer(_)))
                || effects.projections.iter().any(|projection| {
                    type_contains_inference(&projection.subject)
                        || projection
                            .trait_arguments
                            .iter()
                            .any(generic_argument_contains_inference)
                        || projection
                            .item_arguments
                            .iter()
                            .any(generic_argument_contains_inference)
                })
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Error => false,
    }
}

/// A bound lifetime is meaningful only beneath the callable type that
/// introduces it.  Source elaboration maintains that invariant while opening
/// higher-ranked calls, but frozen Core is also an import boundary: persisted
/// or forged products must not be able to smuggle a rigid placeholder into a
/// local, capture, effect argument, or MIR type after its binder has gone
/// away.
pub(crate) fn type_contains_out_of_scope_bound_lifetime(ty: &Type) -> bool {
    type_contains_out_of_scope_bound_lifetime_in(ty, &[])
}

fn type_contains_out_of_scope_bound_lifetime_in(ty: &Type, binders: &[u32]) -> bool {
    match ty {
        Type::Nominal { arguments, .. } => arguments.iter().any(|argument| {
            generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
        }),
        Type::Tuple(arguments) => arguments
            .iter()
            .any(|argument| type_contains_out_of_scope_bound_lifetime_in(argument, binders)),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_contains_out_of_scope_bound_lifetime_in(subject, binders)
                || trait_arguments.iter().any(|argument| {
                    generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
                })
                || item_arguments.iter().any(|argument| {
                    generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
                })
        }
        Type::Array(element) | Type::StaticData { element, .. }
        | Type::RawPointer { pointee: element, .. } => {
            type_contains_out_of_scope_bound_lifetime_in(element, binders)
        }
        Type::Reference {
            lifetime, referent, ..
        } => {
            lifetime_is_out_of_scope_bound(*lifetime, binders)
                || type_contains_out_of_scope_bound_lifetime_in(referent, binders)
        }
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            ..
        } => {
            let mut nested_binders = Vec::with_capacity(binders.len() + 1);
            nested_binders.push(*lifetime_binders);
            nested_binders.extend_from_slice(binders);
            parameters.iter().any(|parameter| {
                type_contains_out_of_scope_bound_lifetime_in(parameter, &nested_binders)
            }) || type_contains_out_of_scope_bound_lifetime_in(result, &nested_binders)
                || effect_row_contains_out_of_scope_bound_lifetime(effects, &nested_binders)
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => false,
    }
}

fn lifetime_is_out_of_scope_bound(lifetime: Lifetime, binders: &[u32]) -> bool {
    match lifetime {
        Lifetime::Infer(_) => true,
        Lifetime::Bound { depth, index } => binders
            .get(depth as usize)
            .is_none_or(|binder_count| index >= *binder_count),
        Lifetime::Static | Lifetime::Generic(_) | Lifetime::Elided => false,
    }
}

fn generic_argument_contains_out_of_scope_bound_lifetime(
    argument: &GenericArgument,
    binders: &[u32],
) -> bool {
    match argument {
        GenericArgument::Type(value) => {
            type_contains_out_of_scope_bound_lifetime_in(value, binders)
        }
        GenericArgument::EffectRow(value) => {
            effect_row_contains_out_of_scope_bound_lifetime(value, binders)
        }
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            type_contains_out_of_scope_bound_lifetime_in(subject, binders)
                || trait_arguments.iter().any(|argument| {
                    generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
                })
        }
        GenericArgument::Lifetime(value) => lifetime_is_out_of_scope_bound(*value, binders),
        GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn effect_row_contains_out_of_scope_bound_lifetime(row: &EffectRow, binders: &[u32]) -> bool {
    row.effects.iter().any(|effect| {
        effect.arguments.iter().any(|argument| {
            generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
        })
    }) || row.projections.iter().any(|projection| {
        type_contains_out_of_scope_bound_lifetime_in(&projection.subject, binders)
            || projection.trait_arguments.iter().any(|argument| {
                generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
            })
            || projection.item_arguments.iter().any(|argument| {
                generic_argument_contains_out_of_scope_bound_lifetime(argument, binders)
            })
    })
}

fn generic_argument_contains_inference(argument: &GenericArgument) -> bool {
    match argument {
        GenericArgument::Type(value) => type_contains_inference(value),
        GenericArgument::EffectRow(value) => effect_row_contains_inference(value),
        GenericArgument::ConstInfer { .. } => true,
        GenericArgument::Lifetime(Lifetime::Infer(_)) => true,
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            type_contains_inference(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_inference)
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => false,
    }
}

fn core_metadata_contains_inference(kind: &CoreKind) -> bool {
    match kind {
        CoreKind::Closure {
            parameters,
            environment,
            ..
        } => {
            parameters.iter().any(|(_, ty)| type_contains_inference(ty))
                || environment
                    .captures
                    .iter()
                    .any(|capture| type_contains_inference(&capture.ty))
                || effect_row_contains_inference(&environment.runs_in.effects)
        }
        CoreKind::Assign { place, .. } => place_contains_inference(place),
        CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => {
            arguments.iter().any(generic_argument_contains_inference)
        }
        CoreKind::TraitMethod {
            trait_arguments,
            method_arguments,
            ..
        } => trait_arguments
            .iter()
            .chain(method_arguments)
            .any(generic_argument_contains_inference),
        CoreKind::Perform {
            effect,
            payload_types,
            ..
        } => {
            effect
                .arguments
                .iter()
                .any(generic_argument_contains_inference)
                || payload_types.iter().any(type_contains_inference)
        }
        CoreKind::PatternTest { pattern, .. } => pattern_contains_inference(pattern),
        CoreKind::Handle { clauses, .. } => clauses.iter().any(|clause| {
            clause
                .effect
                .arguments
                .iter()
                .any(generic_argument_contains_inference)
                || clause.payload_types.iter().any(type_contains_inference)
                || clause.patterns.iter().any(pattern_contains_inference)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| type_contains_inference(ty))
                || clause.continuation.as_ref().is_some_and(|continuation| {
                    type_contains_inference(&continuation.parameter)
                        || type_contains_inference(&continuation.result)
                        || effect_row_contains_inference(&continuation.effects)
                })
        }),
        CoreKind::Completion { clauses, .. } => clauses.iter().any(|clause| {
            pattern_contains_inference(&clause.pattern)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| type_contains_inference(ty))
                || clause.refinement.as_ref().is_some_and(|refinement| {
                    pattern_contains_inference(&refinement.pattern)
                        || refinement
                            .environment
                            .binding_types
                            .iter()
                            .any(|(_, ty)| type_contains_inference(ty))
                })
        }),
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Tuple(_)
        | CoreKind::Array(_)
        | CoreKind::Record { .. }
        | CoreKind::Field { .. }
        | CoreKind::Enum { .. }
        | CoreKind::Let { .. }
        | CoreKind::Label { .. }
        | CoreKind::Transfer { .. }
        | CoreKind::Call { .. }
        | CoreKind::IntrinsicCall { .. }
        | CoreKind::Block(_)
        | CoreKind::Borrow { .. }
        | CoreKind::Deref(_)
        | CoreKind::Move(_)
        | CoreKind::Error => false,
    }
}

/// A frozen Core product must not retain a merely representational variant of
/// a semantic type (for example, duplicate or out-of-order associated effect
/// row projections).  Elaboration normally canonicalizes these, but imported
/// and forged Core have to be checked independently before MIR, instance
/// caches, or fingerprints consume them.
fn core_metadata_contains_noncanonical_type_identity(kind: &CoreKind) -> bool {
    match kind {
        CoreKind::Closure {
            parameters,
            environment,
            ..
        } => {
            parameters
                .iter()
                .any(|(_, ty)| !is_canonical_type_identity(ty))
                || environment
                    .captures
                    .iter()
                    .any(|capture| !is_canonical_type_identity(&capture.ty))
                || !is_canonical_effect_row_identity(&environment.runs_in.effects)
        }
        CoreKind::Assign { place, .. } => place_contains_noncanonical_type_identity(place),
        CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => arguments
            .iter()
            .any(|argument| !is_canonical_generic_argument_identity(argument)),
        CoreKind::TraitMethod {
            trait_arguments,
            method_arguments,
            ..
        } => trait_arguments
            .iter()
            .chain(method_arguments)
            .any(|argument| !is_canonical_generic_argument_identity(argument)),
        CoreKind::Perform {
            effect,
            payload_types,
            ..
        } => {
            effect
                .arguments
                .iter()
                .any(|argument| !is_canonical_generic_argument_identity(argument))
                || payload_types
                    .iter()
                    .any(|ty| !is_canonical_type_identity(ty))
        }
        CoreKind::PatternTest {
            pattern,
            refinement,
            ..
        } => {
            pattern_contains_noncanonical_type_identity(pattern)
                || refinement
                    .binding_types
                    .iter()
                    .any(|(_, ty)| !is_canonical_type_identity(ty))
        }
        CoreKind::Handle { clauses, .. } => clauses.iter().any(|clause| {
            clause
                .effect
                .arguments
                .iter()
                .any(|argument| !is_canonical_generic_argument_identity(argument))
                || clause
                    .payload_types
                    .iter()
                    .any(|ty| !is_canonical_type_identity(ty))
                || clause
                    .patterns
                    .iter()
                    .any(pattern_contains_noncanonical_type_identity)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| !is_canonical_type_identity(ty))
                || clause.continuation.as_ref().is_some_and(|continuation| {
                    !is_canonical_type_identity(&continuation.parameter)
                        || !is_canonical_type_identity(&continuation.result)
                        || !is_canonical_effect_row_identity(&continuation.effects)
                })
        }),
        CoreKind::Completion { clauses, .. } => clauses.iter().any(|clause| {
            pattern_contains_noncanonical_type_identity(&clause.pattern)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| !is_canonical_type_identity(ty))
                || clause.refinement.as_ref().is_some_and(|refinement| {
                    pattern_contains_noncanonical_type_identity(&refinement.pattern)
                        || refinement
                            .environment
                            .binding_types
                            .iter()
                            .any(|(_, ty)| !is_canonical_type_identity(ty))
                })
        }),
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Tuple(_)
        | CoreKind::Array(_)
        | CoreKind::Record { .. }
        | CoreKind::Field { .. }
        | CoreKind::Enum { .. }
        | CoreKind::Let { .. }
        | CoreKind::Label { .. }
        | CoreKind::Transfer { .. }
        | CoreKind::Call { .. }
        | CoreKind::IntrinsicCall { .. }
        | CoreKind::Block(_)
        | CoreKind::Borrow { .. }
        | CoreKind::Deref(_)
        | CoreKind::Move(_)
        | CoreKind::Error => false,
    }
}

fn place_contains_noncanonical_type_identity(place: &CorePlace) -> bool {
    match place {
        CorePlace::Local { ty, .. } | CorePlace::Deref { ty, .. } => {
            !is_canonical_type_identity(ty)
        }
        CorePlace::Field { base, ty, .. } => {
            place_contains_noncanonical_type_identity(base) || !is_canonical_type_identity(ty)
        }
        CorePlace::Error => false,
    }
}

fn pattern_contains_noncanonical_type_identity(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Tuple(values) => values
            .iter()
            .any(pattern_contains_noncanonical_type_identity),
        CorePattern::Array { element, elements } => {
            !is_canonical_type_identity(element)
                || elements
                    .iter()
                    .any(pattern_contains_noncanonical_type_identity)
        }
        CorePattern::Record {
            field_types,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_types,
            fields,
            ..
        } => {
            field_types.iter().any(|ty| !is_canonical_type_identity(ty))
                || fields.iter().any(|field| {
                    !is_canonical_type_identity(&field.ty)
                        || pattern_contains_noncanonical_type_identity(&field.pattern)
                })
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => false,
    }
}

fn core_metadata_contains_out_of_scope_bound_lifetime(kind: &CoreKind) -> bool {
    match kind {
        CoreKind::Closure {
            parameters,
            environment,
            ..
        } => {
            parameters
                .iter()
                .any(|(_, ty)| type_contains_out_of_scope_bound_lifetime(ty))
                || environment
                    .captures
                    .iter()
                    .any(|capture| type_contains_out_of_scope_bound_lifetime(&capture.ty))
                || effect_row_contains_out_of_scope_bound_lifetime(
                    &environment.runs_in.effects,
                    &[],
                )
        }
        CoreKind::Assign { place, .. } => place_contains_out_of_scope_bound_lifetime(place),
        CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => arguments
            .iter()
            .any(|argument| generic_argument_contains_out_of_scope_bound_lifetime(argument, &[])),
        CoreKind::TraitMethod {
            trait_arguments,
            method_arguments,
            ..
        } => trait_arguments
            .iter()
            .chain(method_arguments)
            .any(|argument| generic_argument_contains_out_of_scope_bound_lifetime(argument, &[])),
        CoreKind::Perform {
            effect,
            payload_types,
            ..
        } => {
            effect.arguments.iter().any(|argument| {
                generic_argument_contains_out_of_scope_bound_lifetime(argument, &[])
            }) || payload_types
                .iter()
                .any(type_contains_out_of_scope_bound_lifetime)
        }
        CoreKind::PatternTest { pattern, .. } => {
            pattern_contains_out_of_scope_bound_lifetime(pattern)
        }
        CoreKind::Handle { clauses, .. } => clauses.iter().any(|clause| {
            clause.effect.arguments.iter().any(|argument| {
                generic_argument_contains_out_of_scope_bound_lifetime(argument, &[])
            }) || clause
                .payload_types
                .iter()
                .any(type_contains_out_of_scope_bound_lifetime)
                || clause
                    .patterns
                    .iter()
                    .any(pattern_contains_out_of_scope_bound_lifetime)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| type_contains_out_of_scope_bound_lifetime(ty))
                || clause.continuation.as_ref().is_some_and(|continuation| {
                    type_contains_out_of_scope_bound_lifetime(&continuation.parameter)
                        || type_contains_out_of_scope_bound_lifetime(&continuation.result)
                        || effect_row_contains_out_of_scope_bound_lifetime(
                            &continuation.effects,
                            &[],
                        )
                })
        }),
        CoreKind::Completion { clauses, .. } => clauses.iter().any(|clause| {
            pattern_contains_out_of_scope_bound_lifetime(&clause.pattern)
                || clause
                    .bindings
                    .iter()
                    .any(|(_, ty)| type_contains_out_of_scope_bound_lifetime(ty))
                || clause.refinement.as_ref().is_some_and(|refinement| {
                    pattern_contains_out_of_scope_bound_lifetime(&refinement.pattern)
                        || refinement
                            .environment
                            .binding_types
                            .iter()
                            .any(|(_, ty)| type_contains_out_of_scope_bound_lifetime(ty))
                })
        }),
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::LabelValue { .. }
        | CoreKind::Tuple(_)
        | CoreKind::Array(_)
        | CoreKind::Record { .. }
        | CoreKind::Field { .. }
        | CoreKind::Enum { .. }
        | CoreKind::Let { .. }
        | CoreKind::Label { .. }
        | CoreKind::Transfer { .. }
        | CoreKind::Call { .. }
        | CoreKind::IntrinsicCall { .. }
        | CoreKind::Block(_)
        | CoreKind::Borrow { .. }
        | CoreKind::Deref(_)
        | CoreKind::Move(_)
        | CoreKind::Error => false,
    }
}

/// Effect-row selection may reveal an associated type whose own GAT argument
/// is the row currently being selected.  Descending through that argument
/// would turn a finite cyclic-row diagnostic into elaborator recursion.  We
/// may still normalize ordinary associated type arguments embedded in a
/// selected row, provided their type tree has no row argument to re-enter.
fn generic_argument_contains_effect_row(argument: &GenericArgument) -> bool {
    match argument {
        GenericArgument::Type(value) => type_contains_effect_row_argument(value),
        GenericArgument::EffectRow(_) => true,
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            type_contains_effect_row_argument(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_effect_row)
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn type_contains_effect_row_argument(value: &Type) -> bool {
    match value {
        Type::Nominal { arguments, .. } => arguments.iter().any(generic_argument_contains_effect_row),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_contains_effect_row_argument(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_effect_row)
                || item_arguments
                    .iter()
                    .any(generic_argument_contains_effect_row)
        }
        Type::Tuple(values) => values.iter().any(type_contains_effect_row_argument),
        Type::Array(value)
        | Type::RawPointer { pointee: value, .. }
        | Type::StaticData { element: value, .. }
        | Type::Reference {
            referent: value, ..
        } => type_contains_effect_row_argument(value),
        Type::Callable { .. } => true,
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => false,
    }
}

fn effect_row_contains_inference(row: &EffectRow) -> bool {
    row.effects.iter().any(|effect| {
        effect
            .arguments
            .iter()
            .any(generic_argument_contains_inference)
    }) || matches!(row.tail, Some(crate::types::EffectTail::Infer(_)))
        || row.projections.iter().any(|projection| {
            type_contains_inference(&projection.subject)
                || projection
                    .trait_arguments
                    .iter()
                    .any(generic_argument_contains_inference)
                || projection
                    .item_arguments
                    .iter()
                    .any(generic_argument_contains_inference)
        })
}

fn place_contains_inference(place: &CorePlace) -> bool {
    match place {
        CorePlace::Local { ty, .. } => type_contains_inference(ty),
        CorePlace::Field { base, ty, .. } => {
            type_contains_inference(ty) || place_contains_inference(base)
        }
        CorePlace::Deref { ty, .. } => type_contains_inference(ty),
        CorePlace::Error => false,
    }
}

fn place_contains_out_of_scope_bound_lifetime(place: &CorePlace) -> bool {
    match place {
        CorePlace::Local { ty, .. } => type_contains_out_of_scope_bound_lifetime(ty),
        CorePlace::Field { base, ty, .. } => {
            type_contains_out_of_scope_bound_lifetime(ty)
                || place_contains_out_of_scope_bound_lifetime(base)
        }
        CorePlace::Deref { ty, .. } => type_contains_out_of_scope_bound_lifetime(ty),
        CorePlace::Error => false,
    }
}

fn pattern_contains_inference(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Tuple(values) => values.iter().any(pattern_contains_inference),
        CorePattern::Array { element, elements } => {
            type_contains_inference(element) || elements.iter().any(pattern_contains_inference)
        }
        CorePattern::Record {
            field_types,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_types,
            fields,
            ..
        } => {
            field_types.iter().any(type_contains_inference)
                || fields.iter().any(|field| {
                    type_contains_inference(&field.ty) || pattern_contains_inference(&field.pattern)
                })
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => false,
    }
}

fn pattern_contains_out_of_scope_bound_lifetime(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Tuple(values) => values
            .iter()
            .any(pattern_contains_out_of_scope_bound_lifetime),
        CorePattern::Array { element, elements } => {
            type_contains_out_of_scope_bound_lifetime(element)
                || elements
                    .iter()
                    .any(pattern_contains_out_of_scope_bound_lifetime)
        }
        CorePattern::Record {
            field_types,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_types,
            fields,
            ..
        } => {
            field_types
                .iter()
                .any(type_contains_out_of_scope_bound_lifetime)
                || fields.iter().any(|field| {
                    type_contains_out_of_scope_bound_lifetime(&field.ty)
                        || pattern_contains_out_of_scope_bound_lifetime(&field.pattern)
                })
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => false,
    }
}

fn invalid_typed_core_span() -> Span {
    Span {
        file: crate::FileKey(crate::Digest::of_bytes(
            b"invalid-typed-core-bound-lifetime",
        )),
        start: 0,
        end: 0,
    }
}

/// Frozen method facts that must travel together while one implementation
/// body is elaborated.
pub(crate) struct ImplementationMethodContext<'a> {
    pub implementation_header: &'a crate::header::ImplementationHeader,
    pub method: &'a crate::header::ImplementationMethodHeader,
    pub signature: &'a crate::signature::CallableSignature,
}

impl TypedBody {
    pub fn elaborate(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
    ) -> Self {
        let fixities = FixityTable::with_prelude();
        Self::elaborate_with_fixities(definition, body, index, signatures, &fixities)
    }

    /// Elaborate a body after its module's source-defined fixity environment
    /// has been collected.  The syntax parser retains a flat chain; this is
    /// the single semantic point at which that chain becomes a binary tree.
    pub fn elaborate_with_fixities(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
    ) -> Self {
        Self::elaborate_with_trait_solver(
            definition, body, index, signatures, fixities, TraitSolver::new(signatures),
        )
    }

    pub(crate) fn elaborate_with_trait_solver(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
        trait_solver: TraitSolver,
    ) -> Self {
        let scoped_body = index
            .inherent_method(definition.key)
            .map(|method| bind_inherent_self_paths(body, &method.self_ty));
        let body = scoped_body.as_ref().unwrap_or(body);
        let generic_parameters = definition
            .callable_header()
            .map(|header| {
                header
                    .generics
                    .iter()
                    .enumerate()
                    .filter(|(_, name)| {
                        !header.generics.is_effect_row(name)
                            && !header.generics.is_lifetime(name)
                            && header.generics.const_kind(name).is_none()
                    })
                    .map(|(index, name)| (name.clone(), index as u32))
                    .collect()
            })
            .unwrap_or_default();
        let mut elaborator = Elaborator {
            unsafe_context: false,
            unsafe_scopes: Default::default(),
            body,
            index,
            signatures,
            trait_solver,
            fixities,
            definition: definition.key,
            module: &definition.module,
            inference: InferContext::for_body(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
            active_refinement_bindings: std::collections::BTreeSet::new(),
            active_refinement_patterns: vec![],
            generic_parameters,
            effect_row_parameters: definition
                .callable_header()
                .map(|header| {
                    header
                        .generics
                        .iter()
                        .enumerate()
                        .filter(|(_, name)| header.generics.is_effect_row(name))
                        .map(|(index, name)| (name.clone(), index as u32))
                        .collect()
                })
                .unwrap_or_default(),
            lifetime_parameters: definition
                .callable_header()
                .map(|header| {
                    header
                        .generics
                        .iter()
                        .enumerate()
                        .filter(|(_, name)| header.generics.is_lifetime(name))
                        .map(|(index, name)| (name.clone(), index as u32))
                        .collect()
                })
                .unwrap_or_default(),
            bound_lifetime_scopes: vec![],
            const_parameters: definition
                .callable_header()
                .map(|header| {
                    header
                        .generics
                        .iter()
                        .enumerate()
                        .filter_map(|(index, name)| {
                            header
                                .generics
                                .const_kind(name)
                                .map(|kind| (name.clone(), (index as u32, kind)))
                        })
                        .collect()
                })
                .unwrap_or_default(),
            declared_effects: signatures
                .definitions
                .get(&definition.key)
                .and_then(callable)
                .map(|signature| signature.effects.clone())
                .unwrap_or_else(EffectRow::empty),
            ambient_where_bounds: signatures
                .definitions
                .get(&definition.key)
                .and_then(callable)
                .map(|signature| signature.where_bounds.clone())
                .unwrap_or_default(),
            ambient_callable_type_bindings: signatures
                .definitions
                .get(&definition.key)
                .and_then(callable)
                .map(|signature| signature.where_associated_type_bindings.clone())
                .unwrap_or_default(),
            ambient_callable_effect_bindings: signatures
                .definitions
                .get(&definition.key)
                .and_then(callable)
                .map(|signature| signature.where_associated_effect_bindings.clone())
                .unwrap_or_default(),
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_trackers: vec![],
            generated_environment_types: std::collections::BTreeSet::new(),
            pending_callable_bounds: vec![],
            allow_rigid_trait_arguments: false,
        };
        let expected_result = signatures
            .definitions
            .get(&definition.key)
            .and_then(callable)
            .map(|signature| signature.result.clone());
        elaborator.declared_effects =
            elaborator.normalize_selectable_effect_row(elaborator.declared_effects.clone());
        // Ordinary callable interfaces are public contracts. Their generic
        // trait arguments remain opaque in the body unless a local where
        // clause supplies explicit evidence; only implementation bodies own
        // selected implementation evidence for rigid trait arguments.
        let expected_result = expected_result
            .map(|result| elaborator.normalize_selectable_type_projections(result));
        let mut parameters = vec![];
        if let Some(signature) = signatures
            .definitions
            .get(&definition.key)
            .and_then(callable)
        {
            if let Some(header) = definition.callable_header() {
                for (parameter, ty) in header.parameters.iter().zip(signature.parameters.iter()) {
                    // A callable parameter can itself be an HRTB alias whose
                    // selected GAT result carries the invocation-region
                    // relation.  Keep that relation concrete in the body so
                    // calls through the parameter freeze the caller loan
                    // before escape analysis and VM lowering.
                    let ty = elaborator.normalize_selectable_type_projections(ty.clone());
                    elaborator.locals.define(parameter.name.clone(), ty.clone());
                    parameters.push((parameter.name.clone(), ty));
                }
            }
        } else {
            elaborator.error(
                definition.span,
                "G4100",
                "body belongs to a non-callable declaration",
            );
        }
        // The declared result is useful while elaborating, not merely as a
        // post-hoc assertion.  In particular, a result such as
        // `(i64 -> i64, Array<i64>)` supplies the parameter type of a compact
        // closure and the element type of an empty array nested in the body.
        // Every named callable introduces an implicit lexical label bearing
        // its own name.  The label brand is static proof identity owned by
        // the definition; each invocation still gets its own runtime leave
        // target during MIR lowering.  Install it before elaborating the
        // body so `@function_name(value)` resolves exactly like a compact
        // lexical label, while nested closures remain unable to capture it.
        let implicit_label = definition
            .name
            .clone()
            .filter(|name| {
                body.expressions.iter().any(|expression| {
                    matches!(
                        &expression.kind,
                        ExprKind::Transfer { name: target, .. }
                            | ExprKind::LabelValue { name: target }
                            if target == name
                    )
                })
            })
            .map(|name| {
                let result = expected_result
                    .clone()
                    .unwrap_or_else(|| elaborator.inference.fresh());
                let brand = LabelBrand {
                    owner: definition.key,
                    label: elaborator.next_label,
                };
                elaborator.next_label += 1;
                elaborator.active_labels.push(ActiveLabel {
                    name,
                    brand,
                    result: result.clone(),
                });
                (brand, result)
            });
        let body_root = elaborator.expression_expected(body.root, expected_result.clone());
        let root = if let Some((brand, result)) = implicit_label {
            let _active = elaborator
                .active_labels
                .pop()
                .expect("implicit callable label must outlive its body");
            let body_type = elaborator.expressions[body_root.0 as usize].ty.clone();
            let mut transfers = Vec::new();
            collect_transfer_brands(&elaborator.expressions, body_root, &mut transfers);
            let rejoined_by_own_transfer = transfers.into_iter().any(|target| target == brand);
            let rejoined_by_own_value =
                contains_label_value_brand(&elaborator.expressions, body_root, brand);
            let label_type = if matches!(body_type, Type::Never)
                && !rejoined_by_own_transfer
                && !rejoined_by_own_value
            {
                Type::Never
            } else {
                result
            };
            elaborator.alloc(
                CoreKind::Label {
                    brand,
                    body: body_root,
                },
                label_type,
                definition.span,
            )
        } else {
            body_root
        };
        if let Some(expected) = expected_result {
            let actual = elaborator.expressions[root.0 as usize].ty.clone();
            if elaborator
                .unify_rigid_lifetimes(expected, actual, definition.span)
                .is_err()
            {
                elaborator.error(
                    definition.span,
                    "G4110",
                    "function body does not match declared result type",
                );
                elaborator.recovered = true;
            }
        }
        elaborator.seal_types();
        elaborator
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            safety: signatures.definitions.get(&definition.key).and_then(callable)
                .map_or(crate::Safety::Safe, |signature| signature.safety),
            unsafe_scopes: elaborator.unsafe_scopes,
            unsafe_implementations: unsafe_implementation_definitions(signatures),
            parameters,
            expressions: elaborator.expressions,
            root,
            diagnostics: elaborator.diagnostics,
            recovered: elaborator.recovered,
        }
    }
    pub fn expression(&self, id: CoreId) -> &CoreExpr {
        &self.expressions[id.0 as usize]
    }

    /// Elaborate one implementation method as an independently checked body.
    /// Its stable callable identity is owned by the implementation contract,
    /// while its generic environment combines implementation and method
    /// binders in the same slot order frozen by signature elaboration.
    pub(crate) fn elaborate_implementation_method(
        implementation: &Definition,
        context: ImplementationMethodContext<'_>,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
        trait_solver: TraitSolver,
    ) -> Self {
        let mut generic_parameters = std::collections::BTreeMap::new();
        for (index, name) in context.implementation_header.generics.iter().enumerate() {
            if !context.implementation_header.generics.is_effect_row(name)
                && !context.implementation_header.generics.is_lifetime(name)
                && context
                    .implementation_header
                    .generics
                    .const_kind(name)
                    .is_none()
            {
                generic_parameters.insert(name.clone(), index as u32);
            }
        }
        let method_base = context.implementation_header.generics.len() as u32;
        for (offset, name) in context.method.signature.generics.iter().enumerate() {
            if !context.method.signature.generics.is_effect_row(name)
                && !context.method.signature.generics.is_lifetime(name)
                && context.method.signature.generics.const_kind(name).is_none()
            {
                generic_parameters.insert(name.clone(), method_base + offset as u32);
            }
        }
        let mut elaborator = Elaborator {
            unsafe_context: false,
            unsafe_scopes: Default::default(),
            body,
            index,
            signatures,
            trait_solver,
            fixities,
            definition: DefKey(Digest::of_parts([
                b"grandiose-stage0-implementation-method".as_slice(),
                implementation.key.0.as_bytes().as_slice(),
                context.method.name.as_bytes(),
            ])),
            module: &implementation.module,
            inference: InferContext::for_body(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
            active_refinement_bindings: std::collections::BTreeSet::new(),
            active_refinement_patterns: vec![],
            generic_parameters,
            effect_row_parameters: {
                let mut parameters = std::collections::BTreeMap::new();
                for (index, name) in context.implementation_header.generics.iter().enumerate() {
                    if context.implementation_header.generics.is_effect_row(name) {
                        parameters.insert(name.clone(), index as u32);
                    }
                }
                let method_base = context.implementation_header.generics.len() as u32;
                for (offset, name) in context.method.signature.generics.iter().enumerate() {
                    if context.method.signature.generics.is_effect_row(name) {
                        parameters.insert(name.clone(), method_base + offset as u32);
                    }
                }
                parameters
            },
            lifetime_parameters: {
                let mut parameters = std::collections::BTreeMap::new();
                for (index, name) in context.implementation_header.generics.iter().enumerate() {
                    if context.implementation_header.generics.is_lifetime(name) {
                        parameters.insert(name.clone(), index as u32);
                    }
                }
                let method_base = context.implementation_header.generics.len() as u32;
                for (offset, name) in context.method.signature.generics.iter().enumerate() {
                    if context.method.signature.generics.is_lifetime(name) {
                        parameters.insert(name.clone(), method_base + offset as u32);
                    }
                }
                parameters
            },
            bound_lifetime_scopes: vec![],
            const_parameters: {
                let mut parameters = std::collections::BTreeMap::new();
                for (index, name) in context.implementation_header.generics.iter().enumerate() {
                    if let Some(kind) = context.implementation_header.generics.const_kind(name) {
                        parameters.insert(name.clone(), (index as u32, kind));
                    }
                }
                let method_base = context.implementation_header.generics.len() as u32;
                for (offset, name) in context.method.signature.generics.iter().enumerate() {
                    if let Some(kind) = context.method.signature.generics.const_kind(name) {
                        parameters.insert(name.clone(), (method_base + offset as u32, kind));
                    }
                }
                parameters
            },
            declared_effects: context.signature.effects.clone(),
            ambient_where_bounds: signatures
                .definitions
                .get(&implementation.key)
                .and_then(|header| match header {
                    ElaboratedHeader::Implementation(implementation) => {
                        Some(implementation.where_bounds.clone())
                    }
                    _ => None,
                })
                .into_iter()
                .flatten()
                .chain(context.signature.where_bounds.clone())
                .collect(),
            ambient_callable_type_bindings: context
                .signature
                .where_associated_type_bindings
                .clone(),
            ambient_callable_effect_bindings: context
                .signature
                .where_associated_effect_bindings
                .clone(),
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_trackers: vec![],
            generated_environment_types: std::collections::BTreeSet::new(),
            pending_callable_bounds: vec![],
            allow_rigid_trait_arguments: true,
        };
        elaborator.declared_effects =
            elaborator.normalize_selectable_effect_row(elaborator.declared_effects.clone());
        let mut parameters = vec![];
        for (parameter, ty) in context
            .method
            .signature
            .parameters
            .iter()
            .zip(context.signature.parameters.iter())
        {
            let ty = elaborator.normalize_concrete_type_projections(ty.clone());
            elaborator.locals.define(parameter.name.clone(), ty.clone());
            parameters.push((parameter.name.clone(), ty));
        }
        // The implementation header supplies concrete trait evidence even
        // when a method keeps rigid declaration generics.  Open projections
        // selected by that evidence before the body receives its contextual
        // result type: otherwise `Item<'a, U>` is compared as an opaque
        // projection with an `i64` body merely because `U` is universally
        // quantified by the method.
        let expected_result =
            elaborator.normalize_selectable_type_projections(context.signature.result.clone());
        let root = elaborator.expression_expected(body.root, Some(expected_result.clone()));
        let actual = elaborator.expressions[root.0 as usize].ty.clone();
        if elaborator
            .unify_rigid_lifetimes(
                expected_result,
                actual,
                context.method.span,
            )
            .is_err()
        {
            elaborator.error(
                context.method.span,
                "G4110",
                "implementation method body does not match declared result type",
            );
            elaborator.recovered = true;
        }
        elaborator.seal_types();
        elaborator
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            safety: context.signature.safety,
            unsafe_scopes: elaborator.unsafe_scopes,
            unsafe_implementations: unsafe_implementation_definitions(signatures),
            parameters,
            expressions: elaborator.expressions,
            root,
            diagnostics: elaborator.diagnostics,
            recovered: elaborator.recovered,
        }
    }

    /// Constants are body-local expressions with an interface-declared result
    /// type and no parameter scope. Their initializer is still demand parsed,
    /// resolved, and frozen through the ordinary Core boundary.
    pub fn elaborate_constant(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
    ) -> Self {
        Self::elaborate_constant_with_trait_solver(
            definition, body, index, signatures, fixities, TraitSolver::new(signatures),
        )
    }

    pub(crate) fn elaborate_constant_with_trait_solver(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
        trait_solver: TraitSolver,
    ) -> Self {
        let mut elaborator = Elaborator {
            unsafe_context: false,
            unsafe_scopes: Default::default(),
            body,
            index,
            signatures,
            trait_solver,
            fixities,
            definition: definition.key,
            module: &definition.module,
            inference: InferContext::for_body(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
            active_refinement_bindings: std::collections::BTreeSet::new(),
            active_refinement_patterns: vec![],
            generic_parameters: std::collections::BTreeMap::new(),
            effect_row_parameters: std::collections::BTreeMap::new(),
            lifetime_parameters: std::collections::BTreeMap::new(),
            bound_lifetime_scopes: vec![],
            const_parameters: std::collections::BTreeMap::new(),
            declared_effects: EffectRow::empty(),
            ambient_where_bounds: vec![],
            ambient_callable_type_bindings: vec![],
            ambient_callable_effect_bindings: vec![],
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_trackers: vec![],
            generated_environment_types: std::collections::BTreeSet::new(),
            pending_callable_bounds: vec![],
            allow_rigid_trait_arguments: false,
        };
        let expected = match signatures.definitions.get(&definition.key) {
            Some(ElaboratedHeader::Constant(Some(ty))) => Some(ty.clone()),
            Some(ElaboratedHeader::Constant(None)) => {
                elaborator.error(
                    definition.span,
                    "G4100",
                    "constant declarations require an explicit type in stage zero",
                );
                elaborator.recovered = true;
                None
            }
            _ => {
                elaborator.error(
                    definition.span,
                    "G4100",
                    "body belongs to a non-constant declaration",
                );
                elaborator.recovered = true;
                None
            }
        };
        let root = elaborator.expression_expected(body.root, expected.clone());
        if let Some(expected) = expected {
            let actual = elaborator.expressions[root.0 as usize].ty.clone();
            if elaborator
                .unify_rigid_lifetimes(expected, actual, definition.span)
                .is_err()
            {
                elaborator.error(
                    definition.span,
                    "G4110",
                    "constant initializer does not match declared type",
                );
                elaborator.recovered = true;
            }
        }
        elaborator.seal_types();
        elaborator
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            safety: crate::Safety::Safe,
            unsafe_scopes: elaborator.unsafe_scopes,
            unsafe_implementations: unsafe_implementation_definitions(signatures),
            parameters: vec![],
            expressions: elaborator.expressions,
            root,
            diagnostics: elaborator.diagnostics,
            recovered: elaborator.recovered,
        }
    }

    /// Elaborate the expression owned by an evaluated top-level `let`.
    /// These declarations deliberately share the constant lowering model:
    /// they have no parameter scope and their outward effect row is closed.
    /// The inferred result type is returned in Typed Core and is frozen by
    /// the service before any ordinary body can consume the value.
    pub fn elaborate_value_initializer(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
    ) -> Self {
        Self::elaborate_value_initializer_with_trait_solver(
            definition, body, index, signatures, fixities, TraitSolver::new(signatures),
        )
    }

    pub(crate) fn elaborate_value_initializer_with_trait_solver(
        definition: &Definition,
        body: &BodySyntax,
        index: &DefinitionIndex,
        signatures: &ElaboratedInterface,
        fixities: &FixityTable,
        trait_solver: TraitSolver,
    ) -> Self {
        let mut elaborator = Elaborator {
            unsafe_context: false,
            unsafe_scopes: Default::default(),
            body,
            index,
            signatures,
            trait_solver,
            fixities,
            definition: definition.key,
            module: &definition.module,
            inference: InferContext::for_body(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
            active_refinement_bindings: std::collections::BTreeSet::new(),
            active_refinement_patterns: vec![],
            generic_parameters: std::collections::BTreeMap::new(),
            effect_row_parameters: std::collections::BTreeMap::new(),
            lifetime_parameters: std::collections::BTreeMap::new(),
            bound_lifetime_scopes: vec![],
            const_parameters: std::collections::BTreeMap::new(),
            declared_effects: EffectRow::empty(),
            ambient_where_bounds: vec![],
            ambient_callable_type_bindings: vec![],
            ambient_callable_effect_bindings: vec![],
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_trackers: vec![],
            generated_environment_types: std::collections::BTreeSet::new(),
            pending_callable_bounds: vec![],
            allow_rigid_trait_arguments: false,
        };
        let root = elaborator.expression_expected(body.root, None);
        let initializer_type = match elaborator
            .inference
            .generalize_result_type(elaborator.expressions[root.0 as usize].ty.clone())
        {
            Ok((initializer_type, _)) => initializer_type,
            Err(_) => {
                elaborator.error(
                    definition.span,
                    "G4116",
                    "cannot infer a complete closure type",
                );
                elaborator.recovered = true;
                Type::Error
            }
        };
        elaborator.expressions[root.0 as usize].ty = initializer_type;
        elaborator.seal_types();
        elaborator
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            safety: crate::Safety::Safe,
            unsafe_scopes: elaborator.unsafe_scopes,
            unsafe_implementations: unsafe_implementation_definitions(signatures),
            parameters: vec![],
            expressions: elaborator.expressions,
            root,
            diagnostics: elaborator.diagnostics,
            recovered: elaborator.recovered,
        }
    }

    pub fn value_initializer_type(&self) -> (Vec<crate::GenericKind>, Type) {
        let root = self.expression(self.root);
        let generic_kinds = vec![crate::GenericKind::Type; type_generic_arity(&root.ty) as usize];
        (generic_kinds, root.ty.clone())
    }
}

/// Resolve the lexical `Self` constructor namespace using the impl head.
/// This changes only the body-local syntax product, never source text or
/// definition identity; original expression and pattern spans are preserved.
fn bind_inherent_self_paths(body: &BodySyntax, self_ty: &crate::header::HeaderType) -> BodySyntax {
    use crate::header::{HeaderGenericArgument, HeaderType};
    let (owner, owner_arguments) = match self_ty {
        HeaderType::Path(path) => (path, &[][..]),
        HeaderType::Application(base, arguments) => match base.as_ref() {
            HeaderType::Path(path) => (path, arguments.as_slice()),
            _ => return body.clone(),
        },
        _ => return body.clone(),
    };
    let bind = |path: &mut Vec<String>, arguments: &mut Vec<HeaderGenericArgument>| {
        if path.first().is_some_and(|name| name == "Self") && arguments.is_empty() {
            let mut expanded = owner.clone();
            expanded.extend_from_slice(&path[1..]);
            *path = expanded;
            *arguments = owner_arguments.to_vec();
        }
    };
    let mut body = body.clone();
    for expression in &mut body.expressions {
        match &mut expression.kind {
            ExprKind::Path(path) if path.first().is_some_and(|name| name == "Self") => {
                let mut arguments = vec![];
                bind(path, &mut arguments);
                if !arguments.is_empty() {
                    expression.kind = ExprKind::GenericPath {
                        path: path.clone(),
                        effect_arguments: arguments,
                        operation_arguments: vec![],
                    };
                }
            }
            ExprKind::GenericPath {
                path,
                effect_arguments,
                ..
            } => bind(path, effect_arguments),
            ExprKind::Record {
                path, arguments, ..
            } => bind(path, arguments),
            ExprKind::Handle { clauses, .. } => {
                for clause in clauses {
                    bind(&mut clause.path, &mut clause.effect_arguments);
                }
            }
            _ => {}
        }
    }
    for pattern in &mut body.patterns {
        match &mut pattern.kind {
            crate::body::PatternKind::Enum {
                path, arguments, ..
            }
            | crate::body::PatternKind::Record {
                path, arguments, ..
            } => bind(path, arguments),
            _ => {}
        }
    }
    body
}

fn callable(header: &ElaboratedHeader) -> Option<&crate::signature::CallableSignature> {
    match header {
        ElaboratedHeader::Callable(value)
        | ElaboratedHeader::ValueAlias {
            signature: value, ..
        } => Some(value),
        _ => None,
    }
}

/// Recover `Self` from the declaration's receiver shape, not from whichever
/// implementation happens to accept the entire source argument first. A
/// `&Self` parameter borrows the subject; a `Self` parameter can itself be a
/// reference. Unrelated first parameters do not establish this correspondence.
pub(crate) fn declared_receiver_subject(parameter: &Type, argument: &Type) -> Option<Type> {
    match (parameter, argument) {
        (Type::Generic(crate::signature::TRAIT_SELF_GENERIC), argument) => Some(argument.clone()),
        (
            Type::Reference {
                referent: parameter,
                ..
            },
            Type::Reference {
                referent: argument, ..
            },
        ) => declared_receiver_subject(parameter, argument),
        _ => None,
    }
}

fn unsafe_implementation_definitions(
    signatures: &ElaboratedInterface,
) -> std::collections::BTreeSet<DefKey> {
    signatures.definitions.iter().filter_map(|(definition, header)| {
        matches!(header, ElaboratedHeader::Implementation(implementation) if implementation.safety == crate::Safety::Unsafe).then_some(*definition)
    }).collect()
}

/// Check the one directional relation needed when a callable value is passed
/// as an argument. Callable parameters are contravariant: a function that
/// accepts an elided shared borrow can be used where the caller will supply
/// only a `'static` shared borrow, but not conversely. The general inference
/// unifier remains equality-oriented; it is intentionally not made a global
/// subtyping engine by this narrow call-boundary rule.
fn callable_argument_accepts(required: &Type, provided: &Type) -> bool {
    let (
        Type::Callable {
            safety: required_safety,
            lifetime_binders: required_binders,
            parameters: required_parameters,
            result: required_result,
            effects: required_effects,
            invocation: required_invocation,
        },
        Type::Callable {
            safety: provided_safety,
            lifetime_binders: provided_binders,
            parameters: provided_parameters,
            result: provided_result,
            effects: provided_effects,
            invocation: provided_invocation,
        },
    ) = (required, provided)
    else {
        return false;
    };
    required_safety == provided_safety && required_binders == provided_binders
        && provided_invocation.contains(*required_invocation)
        && required_effects == provided_effects
        && required_result == provided_result
        && required_parameters.len() == provided_parameters.len()
        && required_parameters
            .iter()
            .zip(provided_parameters)
            .all(|(required, provided)| callable_parameter_accepts(provided, required))
}

fn callable_parameter_accepts(provided: &Type, required: &Type) -> bool {
    match (provided, required) {
        (
            Type::Reference {
                mutability: Mutability::Shared,
                lifetime: provided_lifetime,
                referent: provided_referent,
            },
            Type::Reference {
                mutability: Mutability::Shared,
                lifetime: required_lifetime,
                referent: required_referent,
            },
        ) if provided_referent == required_referent => {
            *provided_lifetime == Lifetime::Elided || provided_lifetime == required_lifetime
        }
        _ => provided == required,
    }
}

#[derive(Clone)]
struct ResolvedHandlerClause {
    source: HandlerClause,
    effect: EffectInstance,
    operation_index: u32,
    operation: crate::signature::ElaboratedEffectOperation,
    patterns: Vec<crate::pattern::PatternElaboration>,
    failed: bool,
}
impl ResolvedHandlerClause {
    fn error(source: HandlerClause) -> Self {
        Self {
            source,
            effect: EffectInstance {
                definition: DefKey(Digest::of_bytes(b"grandiose-stage0 handler error")),
                arguments: vec![],
            },
            operation_index: 0,
            operation: crate::signature::ElaboratedEffectOperation {
                name: "<error>".into(),
                generics: 0,
                generic_kinds: vec![],
                parameters: vec![],
                result: Type::Error,
                terminal: false,
                resumption: crate::quantity::Quantity::ONCE,
            },
            patterns: vec![],
            failed: true,
        }
    }
}

struct PendingCallableBound {
    subject: Type,
    relation: crate::ElaboratedTraitReference,
    type_bindings: Vec<crate::ElaboratedAssociatedTypeBinding>,
    effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
    span: Span,
}

struct Elaborator<'a> {
    unsafe_context: bool,
    unsafe_scopes: std::collections::BTreeSet<CoreId>,
    body: &'a BodySyntax,
    index: &'a DefinitionIndex,
    signatures: &'a ElaboratedInterface,
    /// A body-local query engine over an immutable frozen solver world.
    /// Individual uses reset their tables and step counter, matching the
    /// former fresh-solver behavior without repeatedly cloning interfaces.
    trait_solver: TraitSolver,
    fixities: &'a FixityTable,
    definition: DefKey,
    module: &'a ModuleKey,
    inference: InferContext,
    locals: ScopeMap<String, Type>,
    expressions: Vec<CoreExpr>,
    diagnostics: Vec<CoreDiagnostic>,
    recovered: bool,
    next_callable: u32,
    next_resumption: u32,
    next_refinement: u32,
    next_label: u32,
    /// Names whose evidence is valid only in the currently elaborated
    /// positive refinement branch. A nested closure must not capture one: it
    /// could outlive the structural test and thereby forge a refinement fact.
    active_refinement_bindings: std::collections::BTreeSet<String>,
    /// Structural facts currently proven by the positive arm of a completion
    /// handler.  Unlike the exposed pattern binders, this retains the exact
    /// tested place so `value.0` can select an enum payload only where the
    /// corresponding variant has been proven.
    active_refinement_patterns: Vec<(CorePlace, CorePattern)>,
    /// Callable-declaration generic binders are lexically visible in its
    /// body, including effect applications such as `State<T>::get()`. They
    /// remain stable `Type::Generic` slots; inference variables are reserved
    /// for instantiations at a call site.
    generic_parameters: std::collections::BTreeMap<String, u32>,
    /// Lexically visible row-kind binders. These intentionally remain
    /// separate from `generic_parameters`: an effect row can be a callable
    /// tail but can never be elaborated as a value type.
    effect_row_parameters: std::collections::BTreeMap<String, u32>,
    /// Lifetime binders have their own namespace and slot identity. They are
    /// valid only as the qualifier of a reference, never as a value type.
    lifetime_parameters: std::collections::BTreeMap<String, u32>,
    /// Stack of lexical higher-ranked lifetime binders while elaborating a
    /// header type. Bound regions cannot be confused with callable-declaration
    /// lifetimes or escape through normal body inference.
    bound_lifetime_scopes: Vec<std::collections::BTreeMap<String, u32>>,
    /// Structural const binders share source-slot numbering with the other
    /// generic kinds, but are only valid while elaborating an explicit const
    /// argument of a kinded nominal application.
    const_parameters: std::collections::BTreeMap<String, (u32, crate::ConstKind)>,
    declared_effects: EffectRow,
    /// Trait facts supplied by the callable contract currently being
    /// elaborated. These are assumptions, not global solver rules: callers
    /// must still prove the contract before crossing this callable boundary.
    /// Keeping them in Typed Core prevents a generic implementation from
    /// rejecting a call which is valid precisely because its own `where`
    /// clause established the required evidence.
    ambient_where_bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
    /// Associated equalities belonging to the lexical callable evidence.
    /// These give a generic `F: Fn<..., Output = R, Effects = E>` its actual
    /// indirect-call contract without manufacturing a nominal function type.
    ambient_callable_type_bindings: Vec<crate::ElaboratedAssociatedTypeBinding>,
    ambient_callable_effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
    /// Protocol instances exhaustively intercepted by lexically active deep
    /// handlers.  A partial handler never enters this set, so forwarding still
    /// requires the enclosing callable's outward effect declaration.
    handled_effects: std::collections::BTreeSet<EffectInstance>,
    /// Individually exhaustive operation clauses of a partial active handler.
    /// An effect row names a whole protocol, so this fact can discharge a
    /// direct `perform` but never a callable boundary that may invoke any
    /// operation of the protocol.
    handled_operations: std::collections::BTreeSet<(EffectInstance, u32)>,
    /// Lexically live generated continuations. A resumption is an identity
    /// tied to one suspended handler frame, not an ordinary closure value.
    active_resumptions: Vec<ActiveResumption>,
    /// Every lexical alias of an active snapshot points to its original
    /// generated identity. Scope generations are never reused, so stale
    /// entries cannot make a shadowing local resumptive.
    resumption_bindings: std::collections::BTreeMap<(String, u64), ActiveResumption>,
    active_labels: Vec<ActiveLabel>,
    /// One tracker for each lexically active explicit handler arm. Nested
    /// arms keep enclosing trackers live: an outer continuation may be
    /// resumed from a nested handler body, while an identically spelled inner
    /// continuation remains a distinct branded value.
    resumption_use_trackers: Vec<ResumptionUseTracker>,
    /// Opaque nominal identities minted for this body's sealed callable
    /// environments and their normal post-states.  They are intentionally
    /// tracked separately from source nominal definitions: a source path can
    /// never resolve to one of these identities.
    generated_environment_types: std::collections::BTreeSet<DefKey>,
    /// Obligations whose subject has no shape yet remain live until the
    /// enclosing inference island is closed. Zonk alone proves no Fn bound.
    pending_callable_bounds: Vec<PendingCallableBound>,
    /// Only an implementation body may use its selected implementation
    /// evidence to reduce projections carrying rigid trait arguments.
    allow_rigid_trait_arguments: bool,
}
impl Elaborator<'_> {
    fn pattern_generic_scope(&self) -> PatternGenericScope {
        PatternGenericScope {
            types: self.generic_parameters.clone(),
            effect_rows: self.effect_row_parameters.clone(),
            lifetimes: self.lifetime_parameters.clone(),
            consts: self.const_parameters.clone(),
        }
    }

    fn expression(&mut self, id: ExprId) -> CoreId {
        let expression = self.body.expression(id).clone();
        if let ExprKind::GenericPath {
            path,
            effect_arguments,
            operation_arguments,
        } = &expression.kind
            && let Some(value) =
                self.inherent_path(path, effect_arguments, operation_arguments, expression.span)
        {
            return value;
        }
        match expression.kind {
            ExprKind::Literal(text) => self.alloc(
                CoreKind::Literal(text.clone()),
                literal_type(&text),
                expression.span,
            ),
            ExprKind::Path(path) => self
                .enum_constructor(path.clone(), vec![], vec![], None, expression.span)
                .unwrap_or_else(|| self.path(path, expression.span)),
            ExprKind::GenericPath {
                path,
                effect_arguments,
                operation_arguments,
            } if operation_arguments.is_empty() => {
                if let Some(value) = self.enum_constructor(
                    path.clone(),
                    effect_arguments.clone(),
                    vec![],
                    None,
                    expression.span,
                ) {
                    return value;
                }
                self.generic_path(path, effect_arguments, expression.span)
            }
            ExprKind::GenericPath {
                path,
                effect_arguments,
                operation_arguments,
            } if effect_arguments.is_empty() => {
                self.generic_path(path, operation_arguments, expression.span)
            }
            ExprKind::GenericPath { .. } => self.fail(
                expression.span,
                "G4184",
                "a qualified generic operation must be followed by a call",
            ),
            ExprKind::Let { name, value } => {
                let value = self.expression(value);
                let ty = self.expressions[value.0 as usize].ty.clone();
                self.locals.define(name.clone(), ty.clone());
                if let Some(identity) = self.resumption_identity(value)
                    && let Some(generation) = self.locals.binding_generation(&name)
                {
                    self.resumption_bindings
                        .insert((name.clone(), generation), identity);
                }
                // A binding has the unit value only after its initializer has
                // completed.  Preserve bottom here so an enclosing strict
                // block does not try to evaluate statements after a terminal
                // operation hidden in a `let` initializer.
                let statement_type = if matches!(ty, Type::Never) {
                    Type::Never
                } else {
                    Type::Unit
                };
                self.alloc(
                    CoreKind::Let { name, value },
                    statement_type,
                    expression.span,
                )
            }
            ExprKind::Label { name, result, body } => {
                let brand = LabelBrand {
                    owner: self.definition,
                    label: self.next_label,
                };
                self.next_label += 1;
                // A compact source label annotation constrains the exact
                // result variable shared with its body and all transfers. Do
                // not defer this to a discarded parser-side hint: doing so
                // would allow `@done: i64 { @done(true) }` to infer Bool.
                let result = result
                    .as_ref()
                    .map(|annotation| self.header_type(annotation))
                    .unwrap_or_else(|| self.inference.fresh());
                self.active_labels.push(ActiveLabel {
                    name,
                    brand,
                    result: result.clone(),
                });
                let body = self.expression(body);
                let _active = self
                    .active_labels
                    .pop()
                    .expect("label scope must outlive its body");
                let body_type = self.expressions[body.0 as usize].ty.clone();
                let mut transfers = Vec::new();
                collect_transfer_brands(&self.expressions, body, &mut transfers);
                let rejoined_by_own_transfer = transfers.into_iter().any(|target| target == brand);
                let rejoined_by_own_value =
                    contains_label_value_brand(&self.expressions, body, brand);
                // A transfer does not produce the label result at its source
                // location: it abandons that continuation.  Its payload was
                // unified with `result` while elaborating the transfer, so a
                // terminal body must not subsequently constrain the result
                // with `Never`.  This also keeps dead suffixes after a
                // transfer out of the label's result contract.
                if !matches!(body_type, Type::Never)
                    && self
                        .inference
                        .unify(result.clone(), body_type.clone())
                        .is_err()
                {
                    self.error(
                        expression.span,
                        "G4178",
                        "label body and transfers have incompatible result types",
                    );
                    self.recovered = true;
                }
                // A label re-establishes a normal value only when a transfer
                // reaches *its own* destination.  An inner label whose body
                // exits through an enclosing brand remains terminal; leaving
                // its fresh result variable in the frozen Core would turn a
                // valid nested transfer into an inference-hole diagnostic.
                let label_type = if matches!(body_type, Type::Never)
                    && !rejoined_by_own_transfer
                    && !rejoined_by_own_value
                {
                    Type::Never
                } else {
                    result
                };
                self.alloc(CoreKind::Label { brand, body }, label_type, expression.span)
            }
            ExprKind::LabelValue { name } => {
                let Some(label) = self
                    .active_labels
                    .iter()
                    .rev()
                    .find(|label| label.name == name)
                    .cloned()
                else {
                    return self.fail(
                        expression.span,
                        "G4177",
                        "label value is outside its lexical scope",
                    );
                };
                self.alloc(
                    CoreKind::LabelValue { brand: label.brand },
                    Type::Callable {
                        safety: crate::Safety::Safe,
                        lifetime_binders: 0,
                        parameters: vec![label.result],
                        result: Box::new(Type::Never),
                        effects: EffectRow::empty(),
                        invocation: crate::Quantity::ONCE,
                    },
                    expression.span,
                )
            }
            ExprKind::Transfer { name, value } => {
                let value = self.expression(value);
                let Some(label) = self
                    .active_labels
                    .iter()
                    .rev()
                    .find(|label| label.name == name)
                    .cloned()
                else {
                    return self.fail(
                        expression.span,
                        "G4177",
                        "transfer targets a label outside its lexical scope",
                    );
                };
                let value_type = self.expressions[value.0 as usize].ty.clone();
                if self
                    .inference
                    .unify(label.result.clone(), value_type)
                    .is_err()
                {
                    self.error(
                        expression.span,
                        "G4178",
                        "transfer value does not match its label result type",
                    );
                    self.recovered = true;
                }
                self.alloc(
                    CoreKind::Transfer {
                        brand: label.brand,
                        value,
                    },
                    // A label transfer is a nonlocal edge, not an expression
                    // that returns the destination's payload locally.  The
                    // payload type remains attached to the branded target;
                    // `Never` prevents strict enclosing forms and dead
                    // suffixes from being typed as reachable work.
                    Type::Never,
                    expression.span,
                )
            }
            ExprKind::Assign { place, value } => {
                // The RHS is elaborated before the destination, as specified
                // for assignment and mirrored by MIR's Store order.
                let value = self.expression(value);
                let value_ty = self.expressions[value.0 as usize].ty.clone();
                let place = self.assignment_place(place, expression.span);
                if !matches!(&place, CorePlace::Error)
                    && self
                        .unify_rigid_lifetimes(place.ty(), value_ty, expression.span)
                        .is_err()
                {
                    self.error(
                        expression.span,
                        "G4136",
                        "assignment value does not match destination type",
                    );
                    self.recovered = true;
                }
                let assignment = self.alloc(
                    CoreKind::Assign { place, value },
                    self.strict_result(&[value], Type::Unit),
                    expression.span,
                );
                self.record_assigned_enum_refinement(assignment);
                assignment
            }
            ExprKind::Block(values) | ExprKind::ContextualBlock(values) => {
                self.block_expected(values, None, expression.span)
            }
            ExprKind::UnsafeBlock(values) => self.unsafe_block(values, None, expression.span),
            ExprKind::Tuple(values) => self.tuple_expected(values, None, expression.span),
            ExprKind::Array(values) => self.array_expected(values, None, expression.span),
            ExprKind::Record {
                path,
                arguments,
                fields,
            } => self.record(path, arguments, fields, None, expression.span),
            ExprKind::Field { base, name } => self.field(base, name, expression.span),
            ExprKind::Is { subject, pattern } => {
                let subject = self.expression(subject);
                let subject_type = self.zonk_type(
                    self.expressions[subject.0 as usize].ty.clone(),
                    expression.span,
                );
                let scope = self.pattern_generic_scope();
                let elaboration = elaborate_pattern_with_scope(
                    self.body,
                    pattern,
                    subject_type.clone(),
                    self.index,
                    self.signatures,
                    self.module,
                    &scope,
                );
                for diagnostic in elaboration.diagnostics {
                    self.error(diagnostic.span, diagnostic.code, &diagnostic.message);
                }
                self.recovered |= elaboration.recovered;
                let names = elaboration
                    .plan
                    .bindings
                    .iter()
                    .map(|binding| (binding.key, binding.name.clone()))
                    .collect::<std::collections::BTreeMap<_, _>>();
                let pattern = self.core_pattern(
                    elaboration.plan.decision,
                    subject_type,
                    expression.span,
                    Some(&names),
                );
                let binding_types = elaboration
                    .plan
                    .bindings
                    .iter()
                    .map(|binding| (binding.name.clone(), binding.ty.clone()))
                    .collect();
                let refinement = self.refinement_environment(subject, &pattern, binding_types);
                self.refinement_test_value(subject, pattern, refinement, expression.span)
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => self.handle(computation, clauses, None, expression.span),
            ExprKind::Call { callee, arguments } => {
                if matches!(self.body.expression(callee).kind, ExprKind::Path(ref path) if path.len() == 1 && path[0] == "available_to_unit")
                {
                    return self.available_to_unit(arguments, expression.span);
                }
                // `resume(k, value)` is migration syntax for the ordinary
                // generated-resumption callable form `k(value)`. Normalize it
                // before general call elaboration so both spellings receive
                // identical quantity/effect contracts.
                if matches!(self.body.expression(callee).kind, ExprKind::Path(ref path) if path.len() == 1 && path[0] == "resume")
                    && let [resumption, value] = arguments.as_slice()
                {
                    let callee = self.expression(*resumption);
                    self.record_resumption_call(callee);
                    let expected = match self.expressions[callee.0 as usize].ty.clone() {
                        Type::Callable { parameters, .. } => parameters.first().cloned(),
                        _ => None,
                    };
                    let value = self.expression_expected(*value, expected);
                    return self.call(callee, vec![value], expression.span);
                }
                if let ExprKind::Path(path) = &self.body.expression(callee).kind
                    && let Some(value) = self.enum_constructor(
                        path.clone(),
                        vec![],
                        arguments.clone(),
                        None,
                        expression.span,
                    )
                {
                    return value;
                }
                if let ExprKind::GenericPath {
                    path,
                    effect_arguments,
                    operation_arguments,
                } = &self.body.expression(callee).kind
                    && operation_arguments.is_empty()
                    && let Some(value) = self.enum_constructor(
                        path.clone(),
                        effect_arguments.clone(),
                        arguments.clone(),
                        None,
                        expression.span,
                    )
                {
                    return value;
                }
                match &self.body.expression(callee).kind {
                    ExprKind::Path(path) => {
                        if let Some(value) = self.trait_method_call(
                            path.clone(),
                            vec![],
                            vec![],
                            arguments.clone(),
                            None,
                            expression.span,
                        ) {
                            return value;
                        }
                        if let Some(value) = self.perform(
                            path.clone(),
                            vec![],
                            vec![],
                            arguments.clone(),
                            expression.span,
                        ) {
                            return value;
                        }
                    }
                    ExprKind::GenericPath {
                        path,
                        effect_arguments,
                        operation_arguments,
                    } => {
                        if let Some(value) = self.trait_method_call(
                            path.clone(),
                            effect_arguments.clone(),
                            operation_arguments.clone(),
                            arguments.clone(),
                            None,
                            expression.span,
                        ) {
                            return value;
                        }
                        if let Some(value) = self.perform(
                            path.clone(),
                            effect_arguments.clone(),
                            operation_arguments.clone(),
                            arguments.clone(),
                            expression.span,
                        ) {
                            return value;
                        }
                    }
                    _ => {}
                }
                // `{}` is syntactically a contextual block so a normal
                // callable can still receive it.  A zero-field struct uses
                // the same token shape; resolve that ambiguity only through
                // the frozen type namespace, never through its spelling.
                if let ExprKind::Path(path) = &self.body.expression(callee).kind
                    && matches!(arguments.as_slice(), [argument]
                        if matches!(self.body.expression(*argument).kind, ExprKind::ContextualBlock(ref values) if values.is_empty()))
                    && let Some(value) =
                        self.empty_braced_nominal(path.clone(), vec![], expression.span)
                {
                    return value;
                }
                if let ExprKind::GenericPath {
                    path,
                    effect_arguments,
                    operation_arguments,
                } = &self.body.expression(callee).kind
                    && operation_arguments.is_empty()
                    && matches!(arguments.as_slice(), [argument]
                        if matches!(self.body.expression(*argument).kind, ExprKind::ContextualBlock(ref values) if values.is_empty()))
                    && let Some(value) = self.empty_braced_nominal(
                        path.clone(),
                        effect_arguments.clone(),
                        expression.span,
                    )
                {
                    return value;
                }
                let callee = self.expression(callee);
                self.record_resumption_call(callee);
                let parameters = match self.expressions[callee.0 as usize].ty.clone() {
                    Type::Callable { parameters, .. } => parameters,
                    _ => vec![],
                };
                let arguments = self.call_arguments_with_context(callee, &parameters, arguments);
                self.call(callee, arguments, expression.span)
            }
            ExprKind::OperatorChain {
                operands,
                operators,
            } => self.operators(operands, operators, expression.span),
            ExprKind::Borrow { unique, value } => {
                let value = self.expression(value);
                if unique && self.place_uses_shared_reference(value) {
                    return self.fail(expression.span, "G4141",
                        "a unique borrow cannot be derived through a shared reference");
                }
                let ty = self.expressions[value.0 as usize].ty.clone();
                if matches!(&ty, Type::Never) {
                    return self.alloc(
                        CoreKind::Borrow { unique, value },
                        Type::Never,
                        expression.span,
                    );
                }
                // A borrow of a projected dereference is a reborrow of the
                // incoming loan, not a fresh body-local loan.  Preserve its
                // lifetime in Core so `&value.0` can satisfy an outward
                // `&'a T` contract and PlaceFlow/MIR retain the same owner.
                let lifetime = self
                    .projected_reborrow_lifetime(value)
                    .unwrap_or(Lifetime::Elided);
                self.alloc(
                    CoreKind::Borrow { unique, value },
                    Type::Reference {
                        mutability: if unique {
                            Mutability::Unique
                        } else {
                            Mutability::Shared
                        },
                        lifetime,
                        referent: Box::new(ty),
                    },
                    expression.span,
                )
            }
            ExprKind::Deref(value) => {
                let value = self.expression(value);
                if matches!(&self.expressions[value.0 as usize].ty, Type::Never) {
                    return self.alloc(CoreKind::Deref(value), Type::Never, expression.span);
                }
                let Type::Reference {
                    referent,
                    mutability: _,
                    lifetime: _,
                } = self.expressions[value.0 as usize].ty.clone()
                else {
                    return self.fail(
                        expression.span,
                        "G4140",
                        "dereference requires a shared or unique reference",
                    );
                };
                self.alloc(CoreKind::Deref(value), *referent, expression.span)
            }
            ExprKind::Move(value) => {
                let value = self.expression(value);
                let projected_base_ty = match self.expressions[value.0 as usize].kind {
                    CoreKind::Field { base, .. } => {
                        Some(self.expressions[base.0 as usize].ty.clone())
                    }
                    _ => None,
                };
                if projected_base_ty
                    .as_ref()
                    .is_some_and(|ty| self.type_has_custom_drop(ty))
                {
                    self.error(
                        expression.span,
                        "G4188",
                        "a custom-Drop aggregate cannot be partially moved; transfer the whole value or destroy it through its destructor",
                    );
                    self.recovered = true;
                }
                let ty = self.expressions[value.0 as usize].ty.clone();
                self.alloc(CoreKind::Move(value), ty, expression.span)
            }
            ExprKind::Prefix { operator, value } => self.prefix(operator, value, expression.span),
            ExprKind::Closure { parameters, body } => self.closure(
                parameters
                    .into_iter()
                    .map(|name| ClosureParameter {
                        name,
                        ty: None,
                        span: expression.span,
                    })
                    .collect(),
                None,
                crate::header::EffectRowHeader::default(),
                body,
                None,
                None,
                expression.span,
            ),
            ExprKind::MoveClosure { captures, body } => self.closure(
                vec![],
                None,
                crate::header::EffectRowHeader::default(),
                body,
                None,
                Some(captures),
                expression.span,
            ),
            ExprKind::TypedClosure {
                parameters,
                result,
                effects,
                body,
            } => self.closure(parameters, result, effects, body, None, None, expression.span),
            // Recovery is a first-class parser outcome, rather than an
            // unsupported source construct. Preserve it as the Core error
            // sentinel so every downstream semantic pass can remain total
            // without turning editor syntax damage into a spurious feature
            // diagnostic.
            ExprKind::Recovered => {
                self.recovered = true;
                self.alloc(CoreKind::Error, Type::Error, expression.span)
            }
        }
    }
    fn projected_reborrow_lifetime(&self, value: CoreId) -> Option<Lifetime> {
        match &self.expressions[value.0 as usize].kind {
            CoreKind::Field { base, .. } => self.projected_reborrow_lifetime(*base),
            CoreKind::Deref(reference) => match &self.expressions[reference.0 as usize].ty {
                Type::Reference { lifetime, .. } => Some(*lifetime),
                _ => None,
            },
            _ => None,
        }
    }

    fn place_uses_shared_reference(&self, value: CoreId) -> bool {
        match self.expressions[value.0 as usize].kind {
            CoreKind::Deref(reference) => matches!(self.expressions[reference.0 as usize].ty,
                Type::Reference { mutability: Mutability::Shared, .. })
                || self.place_uses_shared_reference(reference),
            CoreKind::Field { base, .. } => self.place_uses_shared_reference(base),
            _ => false,
        }
    }
    fn expression_expected(&mut self, id: ExprId, expected: Option<Type>) -> CoreId {
        self.expression_expected_with_open_lifetimes(id, expected, false)
    }

    fn freshen_call_context_lifetimes(&mut self, expected: Type) -> Type {
        let mut substitution = CallLifetimeSubstitution::default();
        if align_lifetime_types(&expected, &expected, &mut substitution, LifetimeMode::Instantiate, 0).is_err() {
            return expected;
        }
        for lifetime in substitution.generics.values_mut().chain(substitution.bounds.values_mut()) {
            *lifetime = self.inference.fresh_lifetime();
        }
        substitute_call_lifetimes(expected.clone(), &substitution, 0).unwrap_or(expected)
    }

    fn expression_expected_with_open_lifetimes(&mut self, id: ExprId, expected: Option<Type>, open_call_lifetimes: bool) -> CoreId {
        // Context may already have solved a nominal's type parameter. Expose
        // that contract before selecting literal/callable elaboration rules.
        let expected = expected.map(|ty| {
            let ty = self.inference.zonk(ty.clone()).unwrap_or(ty);
            // A callback's output may still be inferred from its body even
            // after earlier operands have solved its argument types. Preserve
            // those independently known shapes (including hidden Bindings)
            // instead of requiring the whole callable to be frozen first.
            match ty {
                Type::Callable { safety, lifetime_binders, parameters, result, effects, invocation } => Type::Callable {
                    safety, lifetime_binders,
                    parameters: parameters.into_iter().map(|parameter|
                        self.inference.zonk(parameter.clone()).unwrap_or(parameter)).collect(),
                    result: Box::new(self.inference.zonk((*result).clone()).unwrap_or(*result)),
                    effects, invocation,
                },
                ty => ty,
            }
        });
        // A callee's region binders are not rigid names in this body. Supply
        // fresh contextual holes while elaborating an argument (including
        // nested aggregate literals); the eventual call jointly checks the
        // realized argument lifetimes against its declaration contract.
        let expected = if open_call_lifetimes {
            expected.map(|expected| self.freshen_call_context_lifetimes(expected))
        } else { expected };
        let expression = self.body.expression(id).clone();
        match expression.kind {
            ExprKind::Literal(text) => self.literal_expected(text, expected, expression.span),
            ExprKind::Record { path, arguments, fields } => self.record(path, arguments, fields, expected, expression.span),
            ExprKind::Block(values) => self.block_expected(values, expected, expression.span),
            ExprKind::UnsafeBlock(values) => self.unsafe_block(values, expected, expression.span),
            ExprKind::Tuple(values) => self.tuple_expected(values, expected, expression.span),
            ExprKind::Array(values) => self.array_expected(values, expected, expression.span),
            ExprKind::Prefix { operator, value } => {
                if self.fixities.prefix(&operator).is_none() {
                    return self.fail(expression.span, "G4111", "operator has no unambiguous visible prefix fixity declaration");
                }
                self.grouped_operator(GroupedOperator::Apply { name: operator, operands: vec![GroupedOperator::Operand(value)] }, expected, expression.span)
            }
            // A direct call can carry result evidence backwards into a
            // generic callback argument.  This is essential for canonical
            // `if(condition) { body } else { fallback }`: the outer declared
            // result constrains `else`, which constrains the `if` result, and
            // finally gives both contextual blocks their `Fn::Output` type.
            // The ordinary expression path deliberately remains responsible
            // for enum constructors, trait methods, and effects; this narrow
            // path only handles a frozen direct function once its exact
            // callable result is available.
            ExprKind::Call { callee, arguments } if expected.is_some() => {
                let path = match &self.body.expression(callee).kind {
                    ExprKind::Path(path) => path,
                    ExprKind::GenericPath { path, .. }
                        if matches!(
                            self.index.resolve_path(DefinitionNamespace::Value, self.module, path),
                            ResolutionState::Resolved(definition)
                                if matches!(self.signatures.definitions.get(&definition), Some(ElaboratedHeader::Callable(_)))
                        ) => path,
                    _ => return self.expression(id),
                };
                // Lexical bindings shadow declaration paths. Looking up the
                // global header first can mistake a local non-callable for
                // the function it shadows and panic below. The ordinary call
                // path handles both local Fn bounds and the G4105 diagnostic.
                if path.len() == 1 && self.locals.lookup(&path[0]).is_some() {
                    return self.expression(id);
                }
                if let Some(value) = self.trait_method_call(
                    path.clone(),
                    vec![],
                    vec![],
                    arguments.clone(),
                    expected.clone(),
                    expression.span,
                ) {
                    return value;
                }
                if let Some(value) = self.enum_constructor(
                    path.clone(),
                    vec![],
                    arguments.clone(),
                    expected.clone(),
                    expression.span,
                ) {
                    return value;
                }
                let ResolutionState::Resolved(definition) =
                    self.index
                        .resolve_path(DefinitionNamespace::Value, self.module, path)
                else {
                    return self.expression(id);
                };
                if !matches!(
                    self.signatures.definitions.get(&definition),
                    Some(ElaboratedHeader::Callable(_))
                ) {
                    return self.expression(id);
                }
                let callee = self.expression(callee);
                let Type::Callable {
                    parameters, result, ..
                } = self.expressions[callee.0 as usize].ty.clone()
                else {
                    // Explicit argument validation may already have rejected
                    // this function application. Preserve that diagnostic;
                    // a resolved declaration is not proof of a valid callee.
                    return callee;
                };
                // Feed result evidence into generic type inference before
                // elaborating contextual arguments, but defer a mismatch
                // diagnostic until `call` has opened the declaration-owned
                // lifetime relation against its actual arguments.  A result
                // such as `&'a T` cannot unify with contextual `&T` while
                // `'a` is still rigid; the call boundary is the only place
                // that can soundly turn it into the caller-local region.
                let expected = expected.expect("guarded above");
                let result_context = self.freshen_call_context_lifetimes(*result);
                let _ = self.inference.unify(result_context, expected.clone());
                let arguments = self.call_arguments_with_context(callee, &parameters, arguments);
                let call = self.call_with_expected(callee, arguments, expression.span,
                    if open_call_lifetimes { None } else { Some(&expected) });
                let actual = self.expressions[call.0 as usize].ty.clone();
                // An outer call's parameter regions are not rigid regions of
                // this body. A nested call may supply the region that opens
                // them; the outer invocation still jointly checks every
                // argument and retains its frozen provenance relation.
                let compatible = if open_call_lifetimes {
                    let mut substitution = CallLifetimeSubstitution::default();
                    align_lifetime_types(&expected, &actual, &mut substitution, LifetimeMode::Instantiate, 0)
                        .map_err(|_| ())
                        .and_then(|aligned| self.inference.unify(aligned, actual).map(|_| ()).map_err(|_| ()))
                } else { self.unify_rigid_lifetimes(expected, actual, expression.span) };
                if compatible.is_err() {
                    self.error(
                        expression.span,
                        "G4107",
                        "call result does not match the contextual expected type",
                    );
                    self.recovered = true;
                }
                call
            }
            ExprKind::OperatorChain {
                operands,
                operators,
            } if expected.is_some() => {
                self.operators_expected(operands, operators, expression.span, expected)
            }
            ExprKind::Closure { parameters, body } => self.closure(
                parameters
                    .into_iter()
                    .map(|name| ClosureParameter {
                        name,
                        ty: None,
                        span: expression.span,
                    })
                    .collect(),
                None,
                crate::header::EffectRowHeader::default(),
                body,
                expected,
                None,
                expression.span,
            ),
            ExprKind::MoveClosure { captures, body } => self.closure(
                vec![],
                None,
                crate::header::EffectRowHeader::default(),
                body,
                expected,
                Some(captures),
                expression.span,
            ),
            // An explicitly typed closure still needs the surrounding
            // callable's invocation contract. In particular, a library
            // callback parameter may require `F: Use<[0,*]>`; dropping the
            // expectation here silently rebuilt this closure as one-shot and
            // made a duplicable capturing predicate fail its `Fn` contract.
            ExprKind::TypedClosure {
                parameters,
                result,
                effects,
                body,
            } => self.closure(
                parameters,
                result,
                effects,
                body,
                expected,
                None,
                expression.span,
            ),
            // A qualified trait method is a genuine callable value, not only
            // special syntax for an immediately-applied call.  Its receiver
            // type comes from the contextual callable contract, which is the
            // same source of information an ordinary generic function value
            // uses to close its substitution.
            ExprKind::Path(path) => {
                if let Some(value) = self.trait_method_value(
                    path.clone(),
                    vec![],
                    vec![],
                    expected.clone(),
                    expression.span,
                )
                {
                    return value;
                }
                if let Some(value) =
                    self.named_hrtb_function_value(path.clone(), expected.clone(), expression.span)
                {
                    return value;
                }
                let value = self.expression(id);
                // A polymorphic initializer is instantiated at this use site.
                // Apply its expected type now, even when a preceding terminal
                // expression makes the enclosing block's result Never. Waiting
                // for the block join loses constraints on this checked value.
                if matches!(self.expressions[value.0 as usize].kind, CoreKind::Constant { .. })
                    && let Some(expected) = expected.clone()
                {
                    let actual = self.expressions[value.0 as usize].ty.clone();
                    if self.unify_rigid_lifetimes(expected, actual, expression.span).is_err() {
                        self.error(expression.span, "G4107", "constant value does not match the contextual expected type");
                        self.recovered = true;
                    }
                }
                self.weaken_callable_invocation_for_expected(value, expected)
            }
            ExprKind::GenericPath {
                path,
                effect_arguments,
                operation_arguments,
            } if operation_arguments.is_empty() => {
                if let Some(value) = self.trait_method_value(
                    path,
                    effect_arguments,
                    operation_arguments,
                    expected,
                    expression.span,
                ) {
                    return value;
                }
                self.expression(id)
            }
            ExprKind::ContextualBlock(values) => match expected {
                Some(Type::Callable {
                    safety,
                    parameters,
                    result,
                    effects,
                    invocation,
                    lifetime_binders,
                }) if parameters.is_empty() => self.contextual_callable_block(
                    values,
                    safety,
                    *result,
                    effects,
                    invocation,
                    lifetime_binders,
                    None,
                    expression.span,
                ),
                Some(Type::Callable { safety, parameters, result, effects, invocation, lifetime_binders }) => {
                    let context = parameters.first().filter(|_| parameters.len() == 1)
                        .and_then(|parameter| self.refinement_context_bindings(parameter)
                            .map(|bindings| (parameter.clone(), bindings)));
                    let Some(context) = context else {
                        return self.fail(expression.span, "G4118",
                            "contextual block requires explicit parameters unless its expected argument is a known binding pack");
                    };
                    self.contextual_callable_block(values, safety, *result, effects, invocation, lifetime_binders, Some(context), expression.span)
                },
                Some(expected) => self.block_expected(values, Some(expected), expression.span),
                None => self.block_expected(values, None, expression.span),
            },
            ExprKind::Handle {
                computation,
                clauses,
            } => self.handle(computation, clauses, expected, expression.span),
            _ => self.expression(id),
        }
    }

    /// A named function value has no captured environment and can therefore
    /// be used more often than its declaration body is itself invoked.  At a
    /// contextual callable boundary we may view that reusable value through a
    /// weaker invocation contract (for example, store it in a `Use<[1,1]>`
    /// field).  Keep the rest of the inferred callable type untouched: the
    /// ordinary field/call unifier still proves parameters, result, and
    /// effects.
    fn weaken_callable_invocation_for_expected(
        &mut self,
        value: CoreId,
        expected: Option<Type>,
    ) -> CoreId {
        let Some(Type::Callable {
            invocation: required,
            ..
        }) = expected
        else {
            return value;
        };
        let actual = self.expressions[value.0 as usize].ty.clone();
        let Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation: provided,
        } = actual
        else {
            return value;
        };
        if provided.contains(required) {
            self.expressions[value.0 as usize].ty = Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation: required,
            };
        }
        value
    }

    /// Apply the same one-way callable view through a nominal type argument.
    /// This matters for `Box<(T) -> U>`-style source records: inference may
    /// first construct the record with a reusable named function, then later
    /// pass it to a parameter whose instantiated field is one-shot.
    fn weaken_nested_callable_invocations(required: &Type, provided: Type) -> Type {
        match (required, provided) {
            (
                Type::Callable {
                    invocation: required,
                    ..
                },
                Type::Callable {
                    safety,
                    lifetime_binders,
                    parameters,
                    result,
                    effects,
                    invocation: provided,
                },
            ) if provided.contains(*required) => Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation: *required,
            },
            (
                Type::Nominal {
                    definition: required_definition,
                    arguments: required_arguments,
                },
                Type::Nominal {
                    definition: provided_definition,
                    arguments: provided_arguments,
                },
            ) if required_definition == &provided_definition
                && required_arguments.len() == provided_arguments.len() => Type::Nominal {
                definition: provided_definition,
                arguments: required_arguments
                    .iter()
                    .zip(provided_arguments)
                    .map(|(required, provided)| match (required, provided) {
                        (GenericArgument::Type(required), GenericArgument::Type(provided)) => {
                            GenericArgument::Type(Self::weaken_nested_callable_invocations(
                                required, provided,
                            ))
                        }
                        (_, provided) => provided,
                    })
                    .collect(),
            },
            (_, provided) => provided,
        }
    }

    /// Source literals are contextual. The distributed standard library keeps
    /// `Bool` as `Result<(), ()>`, so its ordinary `true` and `false`
    /// spellings must build that nominal carrier when a Bool is expected.
    fn literal_expected(&mut self, text: String, expected: Option<Type>, span: Span) -> CoreId {
        // A string literal is compiler-emitted immutable data, but `Str` is
        // intentionally an ordinary source-defined view rather than another
        // compiler scalar. When the expected type is the distributed
        // `Str` (including a callable's not-yet-opened lifetime binder),
        // construct the sealed data literal first and invoke
        // std's manifest-bound wrapper. Keeping the final wrapping step as a
        // normal Core call lets `Str` evolve its private source layout without
        // teaching bytecode about a public string-slice representation.
        if text.starts_with('"')
            && expected
                .as_ref()
                .is_some_and(|expected| self.is_standard_str(expected))
        {
            let raw = self.alloc(
                CoreKind::Literal(text),
                Type::StaticData {
                    element: Box::new(Type::Scalar(ScalarType::U8)),
                    tag: crate::STATIC_UTF8_DATA_TAG,
                    alignment: 1,
                },
                span,
            );
            let callee = self.standard_static_str_wrapper(span);
            return self.call(callee, vec![raw], span);
        }
        if text.starts_with("b\"")
            && expected
                .as_ref()
                .is_some_and(|expected| self.is_standard_static_u8_slice(expected))
        {
            let raw = self.alloc(
                CoreKind::Literal(text),
                Type::StaticData {
                    element: Box::new(Type::Scalar(ScalarType::U8)),
                    tag: crate::STATIC_RAW_U8_DATA_TAG,
                    alignment: 1,
                },
                span,
            );
            let callee = self.standard_static_slice_wrapper(span);
            return self.call(callee, vec![raw], span);
        }
        let ty = match (expected, text.as_str()) {
            // The standard library's `Str<'a>` is a public alias for the
            // sealed static UTF-8 backing type.  A quoted literal acquires
            // that representation only in this explicit expected context;
            // uncontextualized literals retain the ordinary dynamic Text
            // type used by legacy compiler leaves.
            (Some(ref static_data @ Type::StaticData { ref element, tag, .. }), literal)
                if matches!(element.as_ref(), Type::Scalar(crate::types::ScalarType::U8))
                    && ((literal.starts_with('"') && tag == crate::STATIC_UTF8_DATA_TAG)
                        || (literal.starts_with("b\"") && tag == crate::STATIC_RAW_U8_DATA_TAG)) =>
            {
                static_data.clone()
            }
            (Some(Type::Scalar(scalar)), literal)
                if literal_is_numeric(literal) && scalar_is_numeric(scalar) =>
            {
                Type::Scalar(scalar)
            }
            // A generic callable may promise a numeric operator contract
            // through an ambient trait bound before the caller fixes `T`.
            // Keep the literal at that declaration-owned type rather than
            // prematurely defaulting it to `i64`; instance materialization
            // later specializes the literal's MIR local together with the
            // rest of the generic body.
            (Some(Type::Generic(slot)), literal) if literal_is_numeric(literal) => {
                Type::Generic(slot)
            }
            _ => literal_type(&text),
        };
        self.alloc(CoreKind::Literal(text), ty, span)
    }

    fn is_standard_str(&self, expected: &Type) -> bool {
        let ResolutionState::Resolved(definition) = self.index.resolve_path(
            DefinitionNamespace::Type,
            self.module,
            &["std".into(), "Str".into()],
        ) else {
            return false;
        };
        matches!(
            expected,
            Type::Nominal { definition: actual, arguments }
                if actual == &definition
                    && matches!(
                        arguments.as_slice(),
                        [GenericArgument::Lifetime(_)]
                    )
        )
    }

    fn is_standard_static_u8_slice(&self, expected: &Type) -> bool {
        let ResolutionState::Resolved(definition) = self.index.resolve_path(
            DefinitionNamespace::Type,
            self.module,
            &["std".into(), "Slice".into()],
        ) else {
            return false;
        };
        matches!(
            expected,
            Type::Nominal { definition: actual, arguments }
                if actual == &definition
                    && matches!(
                        arguments.as_slice(),
                        [
                            GenericArgument::Lifetime(_),
                            GenericArgument::Type(Type::Scalar(ScalarType::U8)),
                        ]
                    )
        )
    }

    /// Resolve the compiler-selected literal wrapper from the standard
    /// package's own root. This deliberately bypasses application-package
    /// visibility: it is compiler elaboration of a literal, not a source
    /// spelling that should make the helper part of the public API.
    fn standard_static_str_wrapper(&mut self, span: Span) -> CoreId {
        let standard_module = ModuleKey {
            package: PackageKey("std@0.1.0".into()),
            path: "crate".into(),
        };
        let ResolutionState::Resolved(definition) = self.index.resolve_path(
            DefinitionNamespace::Value,
            &standard_module,
            &["__g1_wrap_static_str".into()],
        ) else {
            return self.fail(
                span,
                "G4188",
                "the distributed standard library is missing its static Str literal wrapper",
            );
        };
        let Some(signature) = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)
            .cloned()
        else {
            return self.fail(
                span,
                "G4188",
                "the distributed static Str literal wrapper has no callable contract",
            );
        };
        if !signature.generic_kinds.is_empty() {
            return self.fail(
                span,
                "G4188",
                "the distributed static Str literal wrapper must not be generic",
            );
        }
        self.alloc(
            CoreKind::Function {
                definition,
                arguments: vec![],
                host_import: self.signatures.host_imports.get(&definition).cloned(),
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters: signature.parameters,
                result: Box::new(signature.result),
                effects: signature.effects,
                invocation: signature.invocation,
            },
            span,
        )
    }

    fn standard_static_slice_wrapper(&mut self, span: Span) -> CoreId {
        let standard_module = ModuleKey {
            package: PackageKey("std@0.1.0".into()),
            path: "crate".into(),
        };
        let ResolutionState::Resolved(definition) = self.index.resolve_path(
            DefinitionNamespace::Value,
            &standard_module,
            &["__g1_wrap_static_slice".into()],
        ) else {
            return self.fail(
                span,
                "G4188",
                "the distributed standard library is missing its static Slice literal wrapper",
            );
        };
        let Some(signature) = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)
            .cloned()
        else {
            return self.fail(
                span,
                "G4188",
                "the distributed static Slice literal wrapper has no callable contract",
            );
        };
        if !signature.generic_kinds.is_empty() {
            return self.fail(
                span,
                "G4188",
                "the distributed static Slice literal wrapper must not be generic",
            );
        }
        self.alloc(
            CoreKind::Function {
                definition,
                arguments: vec![],
                host_import: self.signatures.host_imports.get(&definition).cloned(),
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters: signature.parameters,
                result: Box::new(signature.result),
                effects: signature.effects,
                invocation: signature.invocation,
            },
            span,
        )
    }

    /// Materialize the documented `&String -> Str` view coercion through the
    /// standard library's own ordinary `String::as_str` function. This is not
    /// a second string representation or an application-callable compiler
    /// leaf: it merely inserts the same source-level view call a programmer
    /// could spell explicitly when an elided `Str` parameter is expected.
    fn coerce_standard_string_borrow_to_str(
        &mut self,
        expected: &Type,
        argument: CoreId,
        span: Span,
    ) -> Option<CoreId> {
        if !self.is_standard_str(expected) {
            return None;
        }
        let Type::Reference {
            mutability: Mutability::Shared,
            referent,
            ..
        } = &self.expressions[argument.0 as usize].ty
        else {
            return None;
        };
        let standard_module = ModuleKey {
            package: PackageKey("std@0.1.0".into()),
            path: "crate".into(),
        };
        let ResolutionState::Resolved(string_definition) = self.index.resolve_path(
            DefinitionNamespace::Type,
            &standard_module,
            &["String".into()],
        ) else {
            return None;
        };
        if !matches!(
            referent.as_ref(),
            Type::Nominal { definition, arguments } if *definition == string_definition && arguments.is_empty()
        ) {
            return None;
        }
        let ResolutionState::Resolved(definition) = self.index.resolve_path(
            DefinitionNamespace::Value,
            &standard_module,
            &["String".into(), "as_str".into()],
        ) else {
            return None;
        };
        let signature = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)
            .cloned()?;
        if signature.parameters.len() != 1
            || !matches!(signature.generic_kinds.as_slice(), [] | [crate::GenericKind::Lifetime])
        {
            return None;
        }
        // The source accessor now explicitly preserves its owner's lifetime.
        // Open that declaration binder through `call`, just like an ordinary
        // named generic function; do not erase it to Elided or manufacture a
        // static view. Retain support for the older elided library signature.
        let arguments = signature.generic_kinds.iter().enumerate()
            .map(|(index, _)| GenericArgument::Lifetime(Lifetime::Generic(index as u32)))
            .collect::<Vec<_>>();
        let signature = self.signatures.instantiate_callable_generic(definition, &arguments).ok()?;
        let Type::Nominal { definition: expected_str, .. } = expected else { return None; };
        if !matches!(&signature.result, Type::Nominal { definition, arguments }
            if definition == expected_str && matches!(arguments.as_slice(), [GenericArgument::Lifetime(_)]))
        {
            return None;
        }
        let callee = self.alloc(
            CoreKind::Function {
                definition,
                arguments,
                host_import: self.signatures.host_imports.get(&definition).cloned(),
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters: signature.parameters,
                result: Box::new(signature.result),
                effects: signature.effects,
                invocation: signature.invocation,
            },
            span,
        );
        Some(self.call(callee, vec![argument], span))
    }

    /// Strict expression forms evaluate their children from left to right. If
    /// any child cannot return normally, the enclosing construction cannot
    /// manufacture its nominal, tuple, array, call, or statement result.
    /// `Never` is therefore propagated through strict forms; it is coerced to
    /// an expected type only at a value boundary that is actually reached
    /// (return, assignment contract, handler arm, or callable result).
    fn strict_result(&self, values: &[CoreId], normal: Type) -> Type {
        if values
            .iter()
            .any(|value| matches!(&self.expressions[value.0 as usize].ty, Type::Never))
        {
            Type::Never
        } else {
            normal
        }
    }

    /// Elaborate a lexical block with the result expectation available only
    /// to its tail expression.  Earlier statements execute for their effects
    /// and must not inherit a value contract intended for the block result.
    fn unsafe_block(&mut self, values: Vec<ExprId>, expected: Option<Type>, span: Span) -> CoreId {
        let previous = std::mem::replace(&mut self.unsafe_context, true);
        let block = self.block_expected(values, expected, span);
        self.unsafe_context = previous;
        self.unsafe_scopes.insert(block);
        block
    }

    fn block_expected(
        &mut self,
        values: Vec<ExprId>,
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        self.locals.enter();
        let value_count = values.len();
        let values = values
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                if index + 1 == value_count {
                    self.expression_expected(value, expected.clone())
                } else {
                    self.expression(value)
                }
            })
            .collect::<Vec<_>>();
        let ty = values
            .last()
            .map(|value| self.expressions[value.0 as usize].ty.clone())
            .unwrap_or(Type::Unit);
        let ty = self.strict_result(&values, ty);
        self.locals.leave();
        self.alloc(CoreKind::Block(values), ty, span)
    }

    /// Elaborate tuple elements against their corresponding structural
    /// expectation.  This is deliberately exact: a tuple does not gain an
    /// implicit conversion merely because one of its elements happens to
    /// type-check under a different shape.
    fn tuple_expected(
        &mut self,
        values: Vec<ExprId>,
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        let expected_elements = match expected {
            Some(Type::Tuple(elements)) if elements.len() == values.len() => Some(elements),
            Some(Type::Unit) if values.is_empty() => Some(vec![]),
            _ => None,
        };
        let values = values
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                self.expression_expected(
                    value,
                    expected_elements
                        .as_ref()
                        .and_then(|elements| elements.get(index))
                        .cloned(),
                )
            })
            .collect::<Vec<_>>();
        let ty = if values.is_empty() {
            Type::Unit
        } else {
            Type::Tuple(
                values
                    .iter()
                    .map(|value| self.expressions[value.0 as usize].ty.clone())
                    .collect(),
            )
        };
        let ty = self.strict_result(&values, ty);
        self.alloc(CoreKind::Tuple(values), ty, span)
    }

    /// Elaborate every array element under the single expected element type;
    /// this is what gives an empty array a stable body-local type before the
    /// surrounding expression is frozen.
    fn array_expected(
        &mut self,
        values: Vec<ExprId>,
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        let expected_element = match expected {
            Some(Type::Array(element)) => Some(*element),
            _ => None,
        };
        let element = expected_element
            .clone()
            .unwrap_or_else(|| self.inference.fresh());
        let values = values
            .into_iter()
            .map(|value| {
                let value = self.expression_expected(value, expected_element.clone());
                let actual = self.expressions[value.0 as usize].ty.clone();
                if self.inference.unify(element.clone(), actual).is_err() {
                    self.error(span, "G4119", "array elements have incompatible types");
                    self.recovered = true;
                }
                value
            })
            .collect::<Vec<_>>();
        let ty = self.strict_result(&values, Type::Array(Box::new(element)));
        self.alloc(CoreKind::Array(values), ty, span)
    }
    fn refinement_context_bindings(&self, parameter: &Type) -> Option<Vec<(String, Type)>> {
        let parameter = match parameter {
            Type::Reference { mutability: Mutability::Shared, referent, .. } => referent.as_ref(),
            parameter => parameter,
        };
        let (brand, positive) = crate::refinement::binding_pack_brand(parameter)?;
        let fields = crate::refinement::binding_pack_fields(parameter)?;
        let environment = self.expressions.iter().find_map(|expression| match &expression.kind {
            CoreKind::Completion { refinement_test: Some(environment), .. } if environment.brand == brand => Some(environment),
            _ => None,
        })?;
        if !positive { return Some(vec![]); }
        if fields.len() != environment.bindings.len() { return None; }
        Some(environment.bindings.iter().cloned().zip(fields.iter().cloned()).collect())
    }

    fn activate_refinement_context(&mut self, pack_type: Type, bindings: Vec<(String, Type)>, span: Span)
        -> ((String, Type), Vec<CoreId>) {
        let parameter = format!("<bindings-{}>", self.next_callable);
        self.locals.define(parameter.clone(), pack_type.clone());
        let mut pack = self.alloc(CoreKind::Local(parameter.clone()), pack_type.clone(), span);
        if let Type::Reference { referent, .. } = &pack_type {
            pack = self.alloc(CoreKind::Deref(pack), (**referent).clone(), span);
        }
        let field_count = bindings.len() as u32;
        let mut prefix = vec![];
        for (index, (name, ty)) in bindings.into_iter().enumerate() {
            if self.locals.lookup(&name).is_some() {
                self.error(span, "G4170", "refinement binder cannot shadow an incoming local in a contextual body");
                self.recovered = true;
            }
            let value = self.alloc(CoreKind::Field { base: pack, index: index as u32, field_count }, ty.clone(), span);
            prefix.push(self.alloc(CoreKind::Let { name: name.clone(), value }, Type::Unit, span));
            self.locals.define(name, ty);
        }
        ((parameter, pack_type), prefix)
    }

    fn contextual_callable_block(
        &mut self,
        values: Vec<ExprId>,
        safety: crate::Safety,
        result: Type,
        effects: crate::types::EffectRow,
        invocation: crate::quantity::Quantity,
        lifetime_binders: u32,
        refinement_context: Option<(Type, Vec<(String, Type)>)>,
        span: Span,
    ) -> CoreId {
        let contract = Type::Callable {
            safety, lifetime_binders,
            parameters: refinement_context.as_ref().map(|(ty, _)| vec![ty.clone()]).unwrap_or_default(),
            result: Box::new(result.clone()), effects: effects.clone(), invocation,
        };
        let result = open_hrtb_callable_body_type(result, 0);
        let effects = if lifetime_binders == 0 { effects } else { open_hrtb_callable_body_effect_row(effects, 0) };
        self.locals.enter();
        let mut parameters = vec![];
        let mut prefix = vec![];
        if let Some((pack_type, bindings)) = refinement_context {
            let pack_type = open_hrtb_callable_body_type(pack_type, 0);
            let bindings = bindings.into_iter().map(|(name, ty)| (name, open_hrtb_callable_body_type(ty, 0))).collect();
            let (parameter, bindings) = self.activate_refinement_context(pack_type, bindings, span);
            parameters.push(parameter);
            prefix = bindings;
        }
        let previous_unsafe = std::mem::replace(&mut self.unsafe_context, false);
        // A contextual block is a callable body, not an eager continuation
        // of its enclosing expression. Its expected callable row therefore
        // governs any operations in the block, and enclosing handlers cannot
        // be captured as though they would still be active when it runs.
        let previous_effects = std::mem::replace(&mut self.declared_effects, effects.clone());
        let previous_handled = std::mem::take(&mut self.handled_effects);
        let previous_handled_operations = std::mem::take(&mut self.handled_operations);
        let value_count = values.len();
        let values = values
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                if index + 1 == value_count {
                    self.expression_expected(value, Some(result.clone()))
                } else {
                    self.expression(value)
                }
            })
            .collect::<Vec<_>>();
        self.declared_effects = previous_effects;
        self.unsafe_context = previous_unsafe;
        self.handled_effects = previous_handled;
        self.handled_operations = previous_handled_operations;
        let body_ty = values
            .last()
            .map(|value| self.expressions[value.0 as usize].ty.clone())
            .unwrap_or(Type::Unit);
        prefix.extend(values);
        let body = self.alloc(CoreKind::Block(prefix), body_ty.clone(), span);
        self.locals.leave();
        if self
            .unify_rigid_lifetimes(result.clone(), body_ty, span)
            .is_err()
        {
            self.error(
                span,
                "G4113",
                "contextual callable block does not match its expected result",
            );
            self.recovered = true;
        }
        let captures = self.closure_captures(body, &parameters);
        self.check_label_transfer_escape(body, span);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters: parameters.clone(),
                environment: CaptureEnvironment::seal(
                    self.definition,
                    callable,
                    captures,
                    effects.clone(),
                ),
                body,
            },
            contract,
            span,
        )
    }
    fn closure(
        &mut self,
        parameters: Vec<ClosureParameter>,
        declared_result: Option<crate::header::HeaderType>,
        effects: crate::header::EffectRowHeader,
        body: ExprId,
        expected: Option<Type>,
        forced_move_captures: Option<Vec<String>>,
        span: Span,
    ) -> CoreId {
        // Compact closures deliberately omit a source signature.  A callable
        // expectation provides that signature without creating a general
        // implicit conversion: user arity must match after the one permitted
        // hidden binding-pack argument. Annotations still constrain the
        // ordinary user parameters and result.
        let parameter_count = parameters.len();
        let refinement_context = expected.as_ref().and_then(|expected| {
            let Type::Callable { parameters, .. } = expected else { return None; };
            parameters.first().filter(|_| parameters.len() == parameter_count + 1)
                .and_then(|parameter| self.refinement_context_bindings(parameter)
                    .map(|bindings| (parameter.clone(), bindings)))
        });
        let hidden_parameters = usize::from(refinement_context.is_some());
        let expected_callable = expected.as_ref().and_then(|expected| {
            let Type::Callable {
                safety: _,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } = expected
            else {
                return None;
            };
            if parameters.len() != parameter_count + hidden_parameters {
                return None;
            }
            // A closure body executes only after its own `for<'a>` contract
            // has been opened for one call.  Keep the universal contract on
            // the closure value, while its body-local parameter/result types
            // use caller-local regions.  This mirrors `call`'s HRTB opening
            // and, crucially, prevents a bound placeholder from leaking into
            // the flat Core expression arena or the lifted VM body.
            let body_parameters = parameters
                .iter()
                .cloned()
                .map(|parameter| open_hrtb_callable_body_type(parameter, 0))
                .collect::<Vec<_>>();
            let body_result = open_hrtb_callable_body_type((**result).clone(), 0);
            let body_effects = if *lifetime_binders == 0 {
                effects.clone()
            } else {
                open_hrtb_callable_body_effect_row(effects.clone(), 0)
            };
            Some((
                expected.clone(),
                body_parameters,
                body_result,
                body_effects,
                *invocation,
            ))
        });
        let expected_parameters = expected_callable
            .as_ref()
            .map(|(_, parameters, _, _, _)| &parameters[hidden_parameters..]);
        let mut parameters = parameters
            .into_iter()
            .enumerate()
            .map(|(index, parameter)| {
                let ty = parameter
                    .ty
                    .as_ref()
                    .map(|ty| self.header_type(ty))
                    .or_else(|| {
                        expected_parameters
                            .and_then(|parameters| parameters.get(index))
                            .cloned()
                    })
                    .unwrap_or_else(|| self.inference.fresh());
                (parameter.name, ty)
            })
            .collect::<Vec<_>>();
        let effects = expected_callable
            .as_ref()
            .map(|(_, _, _, effects, _)| effects.clone())
            .unwrap_or_else(|| self.closure_effects(&effects, span));
        self.locals.enter();
        for (name, ty) in &parameters {
            self.locals.define(name.clone(), ty.clone());
        }
        let mut prefix = vec![];
        if let Some((pack_type, bindings)) = refinement_context {
            let pack_type = open_hrtb_callable_body_type(pack_type, 0);
            let bindings = bindings.into_iter().map(|(name, ty)| (name, open_hrtb_callable_body_type(ty, 0))).collect();
            let (parameter, bindings) = self.activate_refinement_context(pack_type, bindings, span);
            parameters.insert(0, parameter);
            prefix = bindings;
        }
        // A typed closure freezes an independent callable contract. Check
        // its body against that contract and do not let an enclosing handler
        // discharge effects that may escape with the closure value.
        let previous_effects = std::mem::replace(&mut self.declared_effects, effects.clone());
        let previous_handled = std::mem::take(&mut self.handled_effects);
        let previous_handled_operations = std::mem::take(&mut self.handled_operations);
        let declared_result = declared_result
            .as_ref()
            .map(|ty| self.header_type(ty));
        let contextual_result = expected_callable
            .as_ref()
            .map(|(_, _, result, _, _)| result.clone());
        // The direct callback contract is the executable ABI of the closure
        // value. A written result annotation is a constraint on that ABI,
        // not permission to build a closure with a different result and then
        // label it as the contextual type. This matters for `Bool`, whose
        // source alias and VM predicate carrier can otherwise be normalized
        // at different points in the elaboration pipeline.
        if let (Some(declared), Some(contextual)) =
            (declared_result.clone(), contextual_result.clone())
            && self.inference.unify(declared, contextual).is_err()
        {
            self.error(
                span,
                "G4113",
                "closure result annotation does not match its contextual callable result",
            );
            self.recovered = true;
        }
        let expected_result = contextual_result.or(declared_result);
        let previous_unsafe = std::mem::replace(&mut self.unsafe_context, false);
        let body = self.expression_expected(body, expected_result.clone());
        let body = if prefix.is_empty() { body } else {
            prefix.push(body);
            self.alloc(CoreKind::Block(prefix), self.expressions[body.0 as usize].ty.clone(), span)
        };
        self.unsafe_context = previous_unsafe;
        self.declared_effects = previous_effects;
        self.handled_effects = previous_handled;
        self.handled_operations = previous_handled_operations;
        self.locals.leave();
        let actual_result = self.expressions[body.0 as usize].ty.clone();
        let result = expected_result.unwrap_or_else(|| actual_result.clone());
        if self
            .unify_rigid_lifetimes(result.clone(), actual_result, span)
            .is_err()
        {
            self.error(
                span,
                "G4113",
                "closure body does not match its declared result",
            );
            self.recovered = true;
        }
        let captures = self.closure_captures(body, &parameters);
        let captures = self.force_move_captures(captures, forced_move_captures, span);
        self.check_label_transfer_escape(body, span);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        let callable_type = expected_callable
            .as_ref()
            .map(|(contract, _, _, _, _)| contract.clone())
            .unwrap_or_else(|| Type::Callable {
                safety: crate::Safety::Safe,
                lifetime_binders: 0,
                parameters: parameters.iter().map(|(_, ty)| ty.clone()).collect(),
                result: Box::new(result.clone()),
                effects: effects.clone(),
                invocation: crate::quantity::Quantity::ONCE,
            });
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters: parameters.clone(),
                environment: CaptureEnvironment::seal(
                    self.definition,
                    callable,
                    captures,
                    effects.clone(),
                ),
                body,
            },
            callable_type,
            span,
        )
    }
    fn header_type(&mut self, value: &crate::header::HeaderType) -> Type {
        use crate::header::HeaderType;
        match value {
            HeaderType::Never => Type::Never,
            HeaderType::Recovered => Type::Error,
            HeaderType::Tuple(values) if values.is_empty() => Type::Unit,
            HeaderType::Tuple(values) => {
                Type::Tuple(values.iter().map(|value| self.header_type(value)).collect())
            }
            HeaderType::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
            } => {
                let mut scope = std::collections::BTreeMap::new();
                for (index, name) in lifetime_binders.iter().enumerate() {
                    if scope.insert(name.clone(), index as u32).is_some() {
                        self.error(
                            self.body.expression(self.body.root).span,
                            "G4174",
                            "duplicate higher-ranked lifetime binder",
                        );
                        self.recovered = true;
                    }
                }
                self.bound_lifetime_scopes.push(scope);
                let parameters = parameters
                    .iter()
                    .map(|value| self.header_type(value))
                    .collect();
                let result = Box::new(self.header_type(result));
                let effects =
                    self.closure_effects(effects, self.body.expression(self.body.root).span);
                self.bound_lifetime_scopes.pop();
                Type::Callable {
                    safety: *safety,
                    lifetime_binders: lifetime_binders.len() as u32,
                    parameters,
                    result,
                    effects,
                    invocation: crate::quantity::Quantity::ONCE,
                }
            }
            HeaderType::Reference {
                unique,
                lifetime,
                referent,
            } => Type::Reference {
                mutability: if *unique {
                    Mutability::Unique
                } else {
                    Mutability::Shared
                },
                lifetime: self.header_lifetime(lifetime.as_deref()),
                referent: Box::new(self.header_type(referent)),
            },
            HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            } => self.header_projection(subject, trait_path, trait_arguments, name, item_arguments),
            HeaderType::RawPointer { mutability, pointee } => Type::RawPointer {
                mutability: *mutability,
                pointee: Box::new(self.header_type(pointee)),
            },
            HeaderType::Path(path) => self.header_path(path, &[]),
            HeaderType::Application(base, arguments) => match base.as_ref() {
                HeaderType::Path(path) => self.header_path(path, arguments),
                _ => Type::Error,
            },
        }
    }
    fn header_lifetime(&mut self, spelling: Option<&str>) -> Lifetime {
        match spelling {
            None | Some("'_") => Lifetime::Elided,
            Some("'static") => Lifetime::Static,
            Some(name) => match self
                .bound_lifetime_scopes
                .iter()
                .rev()
                .enumerate()
                .find_map(|(depth, scope)| scope.get(name).map(|index| (depth, index)))
            {
                Some((depth, index)) => Lifetime::Bound {
                    depth: depth as u32,
                    index: *index,
                },
                None => match self.lifetime_parameters.get(name) {
                    Some(index) => Lifetime::Generic(*index),
                    None => {
                        self.error(
                            self.body.expression(self.body.root).span,
                            "G4170",
                            &format!("unbound lifetime `{name}` in closure annotation"),
                        );
                        self.recovered = true;
                        Lifetime::Elided
                    }
                },
            },
        }
    }
    /// Callable signatures retain symbolic projections so generic interfaces
    /// do not guess evidence. At a concrete body boundary, however, every
    /// selected associated definition must reduce recursively before ordinary
    /// type unification compares the declared result with the body value.
    fn normalize_concrete_type_projections(&mut self, value: Type) -> Type {
        let value = match self.trait_query().normalize_type(value) {
            Ok(value) => value,
            Err(answer) => self.projection_normalization_error(*answer),
        };
        self.normalize_nested_callable_effect_rows(value)
    }

    /// A method implementation owns its generic binders.  A projection whose
    /// trait head is concrete may therefore be selected with those binders as
    /// rigid arguments: the selected implementation proves its result for
    /// every possible instantiation, rather than asking this body to guess
    /// caller evidence.  This is intentionally narrower than general
    /// normalization; projections with an abstract subject remain symbolic.
    fn normalize_selectable_type_projections(&mut self, value: Type) -> Type {
        let value = self.normalize_concrete_type_projections(value);
        self.normalize_selectable_type_projections_inner(
            value,
            &mut std::collections::BTreeSet::new(),
            &[],
        )
    }

    fn normalize_selectable_type_projections_inner(
        &mut self,
        value: Type,
        active: &mut std::collections::BTreeSet<Digest>,
        hrtb_binders: &[u32],
    ) -> Type {
        match value {
            Type::Nominal {
                definition,
                arguments,
            } => Type::Nominal {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.normalize_selectable_type_argument(argument, active, hrtb_binders))
                    .collect(),
            },
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_generic_kinds,
                item_arguments,
            } => {
                let subject = self.normalize_selectable_type_projections_inner(*subject, active, hrtb_binders);
                let trait_arguments = trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_selectable_type_argument(argument, active, hrtb_binders))
                    .collect::<Vec<_>>();
                let item_arguments = item_arguments
                    .into_iter()
                    .map(|argument| self.normalize_selectable_type_argument(argument, active, hrtb_binders))
                    .collect::<Vec<_>>();
                let projection = Type::Projection {
                    subject: Box::new(subject),
                    trait_definition,
                    trait_arguments,
                    name,
                    item_generic_kinds,
                    item_arguments,
                };
                if !projection_is_selectable_type_projection(
                    &projection,
                    hrtb_binders,
                    self.allow_rigid_trait_arguments,
                ) {
                    return projection;
                }
                let Type::Projection {
                    subject,
                    trait_definition,
                    trait_arguments,
                    name,
                    item_arguments,
                    ..
                } = &projection
                else {
                    unreachable!("projection was just constructed")
                };
                let trait_arguments_encoding =
                    canonical_generic_arguments_encoding(trait_arguments);
                let subject_encoding = canonical_type_encoding(subject);
                let item_arguments_encoding = canonical_generic_arguments_encoding(item_arguments);
                let key = Digest::of_parts([
                    b"grandiose-stage0-selectable-type-projection-v1".as_slice(),
                    trait_definition.0.as_bytes().as_slice(),
                    trait_arguments_encoding.as_slice(),
                    subject_encoding.as_slice(),
                    name.as_bytes(),
                    item_arguments_encoding.as_slice(),
                ]);
                if !active.insert(key) {
                    return projection;
                }
                let answer = self
                    .trait_query()
                    .normalize_associated_type_application_in_hrtb(
                    TraitGoal {
                        relation: crate::ElaboratedTraitReference {
                            definition: *trait_definition,
                            arguments: trait_arguments.clone(),
                        },
                        subject: *subject.clone(),
                    },
                    name,
                    item_arguments,
                    hrtb_binders,
                );
                let result = match answer {
                    TraitProjectionAnswer::Normalized { ty, .. } => {
                        self.normalize_selectable_type_projections_inner(ty, active, hrtb_binders)
                    }
                    _ => projection,
                };
                active.remove(&key);
                result
            }
            Type::Tuple(values) => Type::Tuple(
                values
                    .into_iter()
                    .map(|value| self.normalize_selectable_type_projections_inner(value, active, hrtb_binders))
                    .collect(),
            ),
            Type::Array(value) => Type::Array(Box::new(
                self.normalize_selectable_type_projections_inner(*value, active, hrtb_binders),
            )),
            Type::RawPointer { mutability, pointee } => Type::RawPointer {
                mutability,
                pointee: Box::new(self.normalize_selectable_type_projections_inner(*pointee, active, hrtb_binders)),
            },
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => Type::Reference {
                mutability,
                lifetime,
                referent: Box::new(
                    self.normalize_selectable_type_projections_inner(*referent, active, hrtb_binders),
                ),
            },
            Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } => {
                let mut nested_binders = Vec::with_capacity(hrtb_binders.len() + 1);
                nested_binders.push(lifetime_binders);
                nested_binders.extend_from_slice(hrtb_binders);
                Type::Callable {
                    safety,
                    lifetime_binders,
                    parameters: parameters
                        .into_iter()
                        .map(|parameter| {
                            self.normalize_selectable_type_projections_inner(
                                parameter,
                                active,
                                &nested_binders,
                            )
                        })
                        .collect(),
                    result: Box::new(self.normalize_selectable_type_projections_inner(
                        *result,
                        active,
                        &nested_binders,
                    )),
                    effects: self.normalize_selectable_effect_row(effects),
                    invocation,
                }
            }
            value => value,
        }
    }

    fn normalize_selectable_type_argument(
        &mut self,
        argument: GenericArgument,
        active: &mut std::collections::BTreeSet<Digest>,
        hrtb_binders: &[u32],
    ) -> GenericArgument {
        match argument {
            GenericArgument::Type(value) => GenericArgument::Type(
                self.normalize_selectable_type_projections_inner(value, active, hrtb_binders),
            ),
            GenericArgument::EffectRow(value) => {
                GenericArgument::EffectRow(self.normalize_selectable_effect_row(value))
            }
            GenericArgument::ConstProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                kind,
            } => GenericArgument::ConstProjection {
                subject: Box::new(
                    self.normalize_selectable_type_projections_inner(*subject, active, hrtb_binders),
                ),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_selectable_type_argument(argument, active, hrtb_binders))
                    .collect(),
                name,
                kind,
            },
            argument => argument,
        }
    }

    /// Type projection normalization deliberately leaves effect rows opaque
    /// because they have their own solver entry point. A callable parameter
    /// is still an executable contract, though: normalize its nested row
    /// before it becomes a direct-call expectation. This is especially
    /// important for an imported `for<'a>` callback whose selected effect GAT
    /// otherwise reaches argument checking as an opaque projection.
    fn normalize_nested_callable_effect_rows(&mut self, value: Type) -> Type {
        match value {
            Type::Nominal {
                definition,
                arguments,
            } => Type::Nominal {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.normalize_nested_callable_effect_argument(argument))
                    .collect(),
            },
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_generic_kinds,
                item_arguments,
            } => Type::Projection {
                subject: Box::new(self.normalize_nested_callable_effect_rows(*subject)),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_nested_callable_effect_argument(argument))
                    .collect(),
                name,
                item_generic_kinds,
                item_arguments: item_arguments
                    .into_iter()
                    .map(|argument| self.normalize_nested_callable_effect_argument(argument))
                    .collect(),
            },
            Type::Tuple(values) => Type::Tuple(
                values
                    .into_iter()
                    .map(|value| self.normalize_nested_callable_effect_rows(value))
                    .collect(),
            ),
            Type::Array(value) => {
                Type::Array(Box::new(self.normalize_nested_callable_effect_rows(*value)))
            }
            Type::RawPointer { mutability, pointee } => Type::RawPointer {
                mutability,
                pointee: Box::new(self.normalize_nested_callable_effect_rows(*pointee)),
            },
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => Type::Reference {
                mutability,
                lifetime,
                referent: Box::new(self.normalize_nested_callable_effect_rows(*referent)),
            },
            Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } => Type::Callable {
                safety,
                lifetime_binders,
                parameters: parameters
                    .into_iter()
                    .map(|parameter| self.normalize_nested_callable_effect_rows(parameter))
                    .collect(),
                result: Box::new(self.normalize_nested_callable_effect_rows(*result)),
                effects: if lifetime_binders == 0 {
                    self.normalize_concrete_effect_row(effects)
                } else {
                    self.normalize_concrete_hrtb_effect_row(effects, lifetime_binders)
                },
                invocation,
            },
            value => value,
        }
    }

    fn normalize_nested_callable_effect_argument(
        &mut self,
        argument: GenericArgument,
    ) -> GenericArgument {
        match argument {
            GenericArgument::Type(value) => {
                GenericArgument::Type(self.normalize_nested_callable_effect_rows(value))
            }
            GenericArgument::EffectRow(value) => {
                GenericArgument::EffectRow(self.normalize_concrete_effect_row(value))
            }
            GenericArgument::ConstProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                kind,
            } => GenericArgument::ConstProjection {
                subject: Box::new(self.normalize_nested_callable_effect_rows(*subject)),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_nested_callable_effect_argument(argument))
                    .collect(),
                name,
                kind,
            },
            argument => argument,
        }
    }

    /// Effect rows follow the same boundary as type projections: concrete
    /// selected rows are executable identities, while rows under declaration
    /// binders remain symbolic for lexical forwarding.  Keep a failed
    /// normalization intact so the ordinary effect checker can issue its
    /// source diagnostic rather than silently dropping a forged projection.
    fn normalize_concrete_effect_row(&mut self, value: EffectRow) -> EffectRow {
        self.trait_query()
            .normalize_effect_row(value.clone())
            .unwrap_or(value)
    }

    /// The HRTB counterpart retains the callable's binder while opening a
    /// selected associated effect GAT. A plain normalization query correctly
    /// rejects a raw `Bound` lifetime as escaped; a named higher-ranked
    /// function value has already established the owning callable scope.
    fn normalize_concrete_hrtb_effect_row(
        &mut self,
        value: EffectRow,
        lifetime_binders: u32,
    ) -> EffectRow {
        self.trait_query()
            .normalize_effect_row_in_hrtb(value.clone(), lifetime_binders)
            .unwrap_or(value)
    }

    /// Reduce effect-row projections whose only symbolic terms are this
    /// declaration's rigid lifetime parameters.  They are safe to select:
    /// an impl generic over `'a` proves the row for every caller-supplied
    /// lifetime, rather than guessing an inference variable.  Keep all other
    /// symbolic rows intact so ordinary lexical forwarding stays symbolic.
    fn normalize_selectable_effect_row(&mut self, value: EffectRow) -> EffectRow {
        let mut result = self.normalize_concrete_effect_row(value);
        let mut projections = std::mem::take(&mut result.projections);
        let mut unresolved = vec![];
        let mut expanded = std::collections::BTreeSet::new();
        while let Some(projection) = projections.pop() {
            if !projection_is_concrete(&projection.subject)
                || !projection
                    .trait_arguments
                    .iter()
                    .all(generic_argument_is_selectable_effect_projection)
                || !projection
                    .item_arguments
                    .iter()
                    .all(generic_argument_is_selectable_effect_projection)
            {
                unresolved.push(projection);
                continue;
            }
            let trait_arguments = canonical_generic_arguments_encoding(&projection.trait_arguments);
            let subject = canonical_type_encoding(&projection.subject);
            let item_arguments = canonical_generic_arguments_encoding(&projection.item_arguments);
            let key = Digest::of_parts([
                b"grandiose-stage0-selectable-effect-projection-v1".as_slice(),
                projection.trait_definition.0.as_bytes().as_slice(),
                trait_arguments.as_slice(),
                subject.as_slice(),
                projection.name.as_bytes(),
                item_arguments.as_slice(),
            ]);
            if !expanded.insert(key) {
                // A selectable row may expand through another associated row.
                // Retain a repeated projection as unresolved rather than
                // re-opening a fresh solver query forever; ordinary effect
                // validation then reports the recursive contract without
                // manufacturing an empty executable row.
                unresolved.push(projection);
                continue;
            }
            match self
                .trait_query()
                .normalize_associated_effect_row_application(
                    TraitGoal {
                        relation: crate::ElaboratedTraitReference {
                            definition: projection.trait_definition,
                            arguments: projection.trait_arguments.clone(),
                        },
                        subject: (*projection.subject).clone(),
                    },
                    &projection.name,
                    &projection.item_arguments,
                ) {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    let tails_compatible = match (&result.tail, &row.tail) {
                        (None, _) | (_, None) => true,
                        (Some(left), Some(right)) => left == right,
                    };
                    if !tails_compatible {
                        unresolved.push(projection);
                        continue;
                    }
                    result.effects.extend(row.effects);
                    projections.extend(row.projections);
                    if result.tail.is_none() {
                        result.tail = row.tail;
                    }
                }
                answer => {
                    // Concrete selected rows are no longer lexical
                    // forwarding. Preserve why normalization failed so an
                    // inherited ambiguity cannot be reported as the same
                    // generic missing-row error as an unresolved facade.
                    self.effect_projection_normalization_error(&answer);
                    unresolved.push(projection);
                }
            }
        }
        result.projections = unresolved;
        // A selected associated row can itself contain selected associated
        // types.  Normalize those arguments before the row is retained as an
        // executable callable contract; `Perform` normalizes its instance at
        // the same boundary, so both sides retain the same closed protocol
        // identity through MIR and VM lowering.
        result.effects = result
            .effects
            .into_iter()
            .map(|effect| {
                EffectInstance {
                    definition: effect.definition,
                    arguments: effect
                        .arguments
                        .into_iter()
                        .map(|argument| match argument {
                            GenericArgument::Type(value)
                                if !type_contains_effect_row_argument(&value) =>
                            {
                                GenericArgument::Type(
                                    self.normalize_selectable_type_projections(value),
                                )
                            }
                            argument => argument,
                        })
                        .collect(),
                }
            })
            .collect();
        result
    }

    /// Every former `TraitSolver::new` call represented a fresh resource
    /// budget and table namespace. Retain that per-query isolation while
    /// reusing this elaborator's immutable frozen rule snapshot.
    fn trait_query(&mut self) -> &mut TraitSolver {
        self.trait_solver.reset_query();
        &mut self.trait_solver
    }
    fn projection_normalization_error(&mut self, answer: TraitProjectionAnswer) -> Type {
        match answer {
            TraitProjectionAnswer::Refuted { .. } => {
                self.projection_error(
                    "G4151",
                    "associated type projection is refuted by a negative implementation",
                );
                Type::Error
            }
            TraitProjectionAnswer::NoSolution => {
                self.projection_error(
                    "G4152",
                    "no implementation can normalize this associated type projection",
                );
                Type::Error
            }
            TraitProjectionAnswer::Ambiguous => {
                self.projection_error("G4153", "associated type projection is ambiguous");
                Type::Error
            }
            TraitProjectionAnswer::Overflow => {
                self.projection_error(
                    "G4154",
                    "associated type projection exceeded the trait solver limit",
                );
                Type::Error
            }
            TraitProjectionAnswer::MissingAssociatedType { .. } => {
                self.projection_error(
                    "G4155",
                    "selected implementation does not define this associated type",
                );
                Type::Error
            }
            TraitProjectionAnswer::AssociatedTypeArity { .. } => {
                self.projection_error("G4156", "associated type projection has the wrong arity");
                Type::Error
            }
            TraitProjectionAnswer::RecursiveProjection => {
                self.projection_error(
                    "G4157",
                    "associated type projection has no finite normal form",
                );
                Type::Error
            }
            TraitProjectionAnswer::Normalized { .. } => {
                unreachable!("normalized projections are returned through Ok")
            }
        }
    }

    fn effect_projection_normalization_error(&mut self, answer: &TraitEffectRowProjectionAnswer) {
        let (code, message) = match answer {
            TraitEffectRowProjectionAnswer::Refuted { .. } => (
                "G4151",
                "associated effect-row projection is refuted by a negative implementation",
            ),
            TraitEffectRowProjectionAnswer::NoSolution => (
                "G4152",
                "no implementation can normalize this associated effect-row projection",
            ),
            TraitEffectRowProjectionAnswer::Ambiguous => {
                ("G4153", "associated effect-row projection is ambiguous")
            }
            TraitEffectRowProjectionAnswer::Overflow => (
                "G4154",
                "associated effect-row projection exceeded the trait solver limit",
            ),
            TraitEffectRowProjectionAnswer::MissingAssociatedEffectRow { .. }
            | TraitEffectRowProjectionAnswer::AssociatedEffectRowArity { .. } => (
                "G4155",
                "selected implementation does not define this associated effect row",
            ),
            TraitEffectRowProjectionAnswer::NestedTypeProjection { .. }
            | TraitEffectRowProjectionAnswer::RecursiveProjection
            | TraitEffectRowProjectionAnswer::ConflictingRowTails => (
                "G4157",
                "associated effect-row projection has no finite normal form",
            ),
            TraitEffectRowProjectionAnswer::Normalized { .. } => {
                unreachable!("normalized effect projections are returned through the success arm")
            }
        };
        self.projection_error(code, message);
    }
    fn header_projection(
        &mut self,
        subject: &crate::header::HeaderType,
        trait_path: &[String],
        trait_arguments: &[crate::header::HeaderGenericArgument],
        name: &str,
        item_arguments: &[crate::header::HeaderGenericArgument],
    ) -> Type {
        let subject = self.header_type(subject);
        let trait_definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Trait, self.module, trait_path)
            {
                ResolutionState::Resolved(definition) => definition,
                ResolutionState::Ambiguous(_) => {
                    self.projection_error(
                        "G4146",
                        "associated type projection has an ambiguous trait",
                    );
                    return Type::Error;
                }
                ResolutionState::Inaccessible(_)
                | ResolutionState::Unresolved
                | ResolutionState::Recovered => {
                    self.projection_error(
                        "G4147",
                        "associated type projection has an unresolved trait",
                    );
                    return Type::Error;
                }
            };
        let trait_kinds = self
            .index
            .trait_generic_kinds(trait_definition)
            .unwrap_or(&[]);
        let Some(trait_identity_arguments) =
            self.header_generic_arguments(trait_arguments, trait_kinds)
        else {
            return Type::Error;
        };
        let Some(ElaboratedHeader::Trait(trait_header)) =
            self.signatures.definitions.get(&trait_definition)
        else {
            self.projection_error("G4148", "associated type projection target is not a trait");
            return Type::Error;
        };
        let item = match trait_header.associated_types.get(name) {
            Some(item) if item.effect_row => {
                self.projection_error(
                    "G4149",
                    "associated effect rows require the pending effect-row projection syntax",
                );
                return Type::Error;
            }
            Some(item) if item.generics == item_arguments.len() as u32 => item,
            Some(_) => {
                self.projection_error(
                    "G4149",
                    "associated type projection has the wrong number of item arguments",
                );
                return Type::Error;
            }
            None => {
                self.projection_error("G4150", "trait does not declare this associated type");
                return Type::Error;
            }
        };
        let Some(item_arguments) =
            self.header_generic_arguments(item_arguments, &item.generic_kinds)
        else {
            return Type::Error;
        };
        let projection = Type::Projection {
            subject: Box::new(subject),
            trait_definition,
            trait_arguments: trait_identity_arguments.clone(),
            name: name.to_owned(),
            item_generic_kinds: item.generic_kinds.clone(),
            item_arguments,
        };
        if !projection_is_concrete(&projection) {
            return projection;
        }
        let Type::Projection {
            subject,
            trait_arguments: _,
            name,
            item_arguments,
            ..
        } = &projection
        else {
            unreachable!("projection was just constructed")
        };
        let answer = self.trait_query().normalize_associated_type_application(
            TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: trait_definition,
                    arguments: trait_identity_arguments,
                },
                subject: *subject.clone(),
            },
            name,
            item_arguments,
        );
        match answer {
            TraitProjectionAnswer::Normalized { ty, .. } => ty,
            answer => self.projection_normalization_error(answer),
        }
    }

    /// Elaborate source generic arguments only after the declaration's
    /// source-slot kinds are known.  This keeps const terms out of ordinary
    /// type slots in body-local closure annotations as well as signatures.
    fn header_generic_arguments(
        &mut self,
        arguments: &[crate::header::HeaderGenericArgument],
        kinds: &[crate::GenericKind],
    ) -> Option<Vec<GenericArgument>> {
        if arguments.len() != kinds.len() {
            self.projection_error(
                "G4158",
                "generic application has the wrong number of arguments",
            );
            return None;
        }
        Some(
            arguments
                .iter()
                .zip(kinds)
                .map(|(argument, kind)| match (argument, kind) {
                    (
                        crate::header::HeaderGenericArgument::Type(
                            crate::header::HeaderType::Projection {
                                subject,
                                trait_path,
                                trait_arguments,
                                name,
                                item_arguments,
                            },
                        ),
                        crate::GenericKind::Const(expected),
                    ) => self.associated_const_argument(
                        (subject, trait_path, trait_arguments, name, item_arguments),
                        *expected,
                        (self.body.expression(self.body.root).span, "G4158"),
                    ),
                    (
                        crate::header::HeaderGenericArgument::Type(value),
                        crate::GenericKind::Type,
                    ) => GenericArgument::Type(self.header_type(value)),
                    (
                        crate::header::HeaderGenericArgument::U32(value),
                        crate::GenericKind::Const(crate::ConstKind::U32),
                    ) => GenericArgument::ConstU32(*value),
                    (
                        crate::header::HeaderGenericArgument::Quantity(value),
                        crate::GenericKind::Const(crate::ConstKind::Quantity),
                    ) => GenericArgument::ConstQuantity(*value),
                    (
                        crate::header::HeaderGenericArgument::Type(
                            crate::header::HeaderType::Path(path),
                        ),
                        crate::GenericKind::Const(kind),
                    ) if path.len() == 1 => match self.const_parameters.get(&path[0]).copied() {
                        Some((index, found)) if found == *kind => {
                            GenericArgument::ConstGeneric { index, kind: *kind }
                        }
                        _ => {
                            self.projection_error(
                                "G4158",
                                "const generic argument has the wrong kind",
                            );
                            GenericArgument::Type(Type::Error)
                        }
                    },
                    (
                        crate::header::HeaderGenericArgument::Lifetime(value),
                        crate::GenericKind::Lifetime,
                    ) => GenericArgument::Lifetime(self.header_lifetime(Some(value))),
                    (
                        crate::header::HeaderGenericArgument::EffectRow(value),
                        crate::GenericKind::EffectRow,
                    ) => GenericArgument::EffectRow(
                        self.closure_effects(value, self.body.expression(self.body.root).span),
                    ),
                    _ => {
                        self.projection_error("G4158", "generic argument has the wrong kind");
                        GenericArgument::Type(Type::Error)
                    }
                })
                .collect(),
        )
    }

    /// Elaborate body-local explicit generic arguments only after resolving
    /// the callee declaration's slot kinds.  Unlike the legacy header helper
    /// above, this retains a row, lifetime, or structural value as its own
    /// `GenericArgument` all the way to the instantiation contract boundary.
    fn body_generic_arguments(
        &mut self,
        arguments: &[crate::header::HeaderGenericArgument],
        kinds: &[crate::GenericKind],
        span: Span,
        code: &'static str,
        arity_message: &'static str,
    ) -> Option<Vec<GenericArgument>> {
        if arguments.len() != kinds.len() {
            self.error(span, code, arity_message);
            self.recovered = true;
            return None;
        }
        let mut elaborated = Vec::with_capacity(arguments.len());
        for (argument, kind) in arguments.iter().zip(kinds) {
            let value = match (argument, kind) {
                (
                    crate::header::HeaderGenericArgument::Type(
                        crate::header::HeaderType::Projection {
                            subject,
                            trait_path,
                            trait_arguments,
                            name,
                            item_arguments,
                        },
                    ),
                    crate::GenericKind::Const(expected),
                ) => self.associated_const_argument(
                    (subject, trait_path, trait_arguments, name, item_arguments),
                    *expected,
                    (span, code),
                ),
                (
                    crate::header::HeaderGenericArgument::Type(crate::header::HeaderType::Path(
                        path,
                    )),
                    crate::GenericKind::EffectRow,
                ) if path.len() == 1 => match self.effect_row_parameters.get(&path[0]).copied() {
                    Some(index) => GenericArgument::EffectRow(EffectRow {
                        effects: Default::default(),
                        projections: vec![],
                        tail: Some(crate::EffectTail::Generic(index)),
                    }),
                    None => GenericArgument::Type(
                        self.header_type(&crate::header::HeaderType::Path(path.clone())),
                    ),
                },
                (
                    crate::header::HeaderGenericArgument::Type(crate::header::HeaderType::Path(
                        path,
                    )),
                    crate::GenericKind::Const(expected),
                ) if path.len() == 1 => {
                    let parameter = self
                        .const_parameters
                        .get(&path[0])
                        .copied()
                        .filter(|(_, found)| found == expected);
                    match parameter {
                        Some((index, kind)) => GenericArgument::ConstGeneric { index, kind },
                        None => GenericArgument::Type(
                            self.header_type(&crate::header::HeaderType::Path(path.clone())),
                        ),
                    }
                }
                (crate::header::HeaderGenericArgument::Type(value), _) => {
                    GenericArgument::Type(self.header_type(value))
                }
                (crate::header::HeaderGenericArgument::Lifetime(value), _) => {
                    GenericArgument::Lifetime(self.header_lifetime(Some(value)))
                }
                (crate::header::HeaderGenericArgument::EffectRow(value), _) => {
                    GenericArgument::EffectRow(self.closure_effects(value, span))
                }
                (crate::header::HeaderGenericArgument::U32(value), _) => {
                    GenericArgument::ConstU32(*value)
                }
                (
                    crate::header::HeaderGenericArgument::StructuralConst(value),
                    crate::GenericKind::Const(crate::ConstKind::U32),
                ) => self.body_structural_u32(value, span, code),
                (crate::header::HeaderGenericArgument::StructuralConst(_), _) => {
                    self.error(
                        span,
                        code,
                        "structural u32 expression supplied to a non-u32 generic slot",
                    );
                    GenericArgument::ConstU32(0)
                }
                (crate::header::HeaderGenericArgument::Quantity(value), _) => {
                    GenericArgument::ConstQuantity(*value)
                }
                (
                    crate::header::HeaderGenericArgument::AssociatedTypeBinding { .. }
                    | crate::header::HeaderGenericArgument::AssociatedEffectBinding { .. },
                    _,
                ) => {
                    self.error(
                        span,
                        code,
                        "associated type equality is only valid on a callable where-bound",
                    );
                    GenericArgument::Type(Type::Error)
                }
            };
            elaborated.push(value);
        }
        Some(elaborated)
    }

    fn body_structural_u32(
        &mut self,
        value: &crate::header::HeaderStructuralConst,
        span: Span,
        code: &'static str,
    ) -> GenericArgument {
        fn elaborate(
            elaborator: &mut Elaborator<'_>,
            value: &crate::header::HeaderStructuralU32Expr,
            span: Span,
            code: &'static str,
        ) -> Option<crate::StructuralU32Expr> {
            use crate::StructuralU32Expr as Expr;
            use crate::header::HeaderStructuralU32Expr as Source;
            Some(match value {
                Source::Literal(value) => Expr::Literal(*value),
                Source::Param(name) => match elaborator.const_parameters.get(name).copied() {
                    Some((index, crate::ConstKind::U32)) => Expr::Param(index),
                    _ => {
                        elaborator.error(span, code, &format!("structural u32 expression refers to undeclared or wrong-kind binder `{name}`"));
                        return None;
                    }
                },
                Source::Add(left, right) => Expr::Add(
                    Box::new(elaborate(elaborator, left, span, code)?),
                    Box::new(elaborate(elaborator, right, span, code)?),
                ),
                Source::Sub(left, right) => Expr::Sub(
                    Box::new(elaborate(elaborator, left, span, code)?),
                    Box::new(elaborate(elaborator, right, span, code)?),
                ),
                Source::Mul(left, right) => Expr::Mul(
                    Box::new(elaborate(elaborator, left, span, code)?),
                    Box::new(elaborate(elaborator, right, span, code)?),
                ),
                Source::Div(left, right) => Expr::Div(
                    Box::new(elaborate(elaborator, left, span, code)?),
                    Box::new(elaborate(elaborator, right, span, code)?),
                ),
                Source::Rem(left, right) => Expr::Rem(
                    Box::new(elaborate(elaborator, left, span, code)?),
                    Box::new(elaborate(elaborator, right, span, code)?),
                ),
            })
        }
        let value = match value {
            crate::header::HeaderStructuralConst::U32(value) => {
                crate::StructuralU32Expr::Literal(*value)
            }
            crate::header::HeaderStructuralConst::U32Expression(value) => {
                match elaborate(self, value, span, code) {
                    Some(value) => value,
                    None => return GenericArgument::ConstU32(0),
                }
            }
            _ => {
                self.error(span, code, "structural u32 expression has the wrong kind");
                return GenericArgument::ConstU32(0);
            }
        };
        match value.normalized() {
            Ok(crate::StructuralU32Expr::Literal(value)) => GenericArgument::ConstU32(value),
            Ok(value) => GenericArgument::ConstU32Expr(value),
            Err(_) => {
                self.error(span, code, "structural u32 arithmetic overflowed, divided by zero, or exceeded its resource limit");
                GenericArgument::ConstU32(0)
            }
        }
    }

    /// Elaborate `<S as Trait<Args>>::CONST` only in a structural const slot.
    /// This is intentionally a Core boundary: headers preserve the source
    /// spelling, while only an executable use is allowed to select concrete
    /// implementation evidence and insert the normalized structural term.
    fn associated_const_argument(
        &mut self,
        projection: (
            &crate::header::HeaderType,
            &[String],
            &[crate::header::HeaderGenericArgument],
            &str,
            &[crate::header::HeaderGenericArgument],
        ),
        expected: crate::ConstKind,
        context: (Span, &'static str),
    ) -> GenericArgument {
        let (subject, trait_path, source_arguments, name, item_arguments) = projection;
        let (span, code) = context;
        if !item_arguments.is_empty() {
            self.error(
                span,
                code,
                "associated constants do not accept item arguments",
            );
            self.recovered = true;
            return structural_const_error(expected);
        }
        let ResolutionState::Resolved(trait_definition) =
            self.index
                .resolve_path(DefinitionNamespace::Trait, self.module, trait_path)
        else {
            self.error(
                span,
                code,
                "associated constant projection has an unresolved trait",
            );
            self.recovered = true;
            return structural_const_error(expected);
        };
        let Some(ElaboratedHeader::Trait(trait_header)) =
            self.signatures.definitions.get(&trait_definition)
        else {
            self.error(
                span,
                code,
                "associated constant projection target is not a trait",
            );
            self.recovered = true;
            return structural_const_error(expected);
        };
        // The named trait need not own the constant directly: an inherited
        // associated item is selected through the same instantiated
        // supertrait edge as methods, types, and effect rows. The trait
        // solver performs that lookup (and verifies the resulting kind), so
        // rejecting a missing direct header entry here would make a valid
        // `<S as Child>::CONST` projection unreachable before selection.
        let Some(arguments) = self.body_generic_arguments(
            source_arguments,
            &trait_header.generic_kinds,
            span,
            code,
            "associated constant trait arguments do not match its declaration",
        ) else {
            return structural_const_error(expected);
        };
        let subject = self.header_type(subject);
        match self.trait_query().normalize_associated_const(
            TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: trait_definition,
                    arguments,
                },
                subject,
            },
            name,
            expected,
        ) {
            TraitConstProjectionAnswer::Normalized { value, .. }
                if generic_argument_matches_kind(&value, crate::GenericKind::Const(expected)) =>
            {
                value
            }
            TraitConstProjectionAnswer::Refuted { .. } => {
                self.error(
                    span,
                    code,
                    "associated constant projection is refuted by a negative implementation",
                );
                self.recovered = true;
                structural_const_error(expected)
            }
            TraitConstProjectionAnswer::NoSolution => {
                self.error(
                    span,
                    code,
                    "no implementation can normalize this associated constant",
                );
                self.recovered = true;
                structural_const_error(expected)
            }
            TraitConstProjectionAnswer::Ambiguous => {
                self.error(span, code, "associated constant projection is ambiguous");
                self.recovered = true;
                structural_const_error(expected)
            }
            TraitConstProjectionAnswer::Overflow => {
                self.error(
                    span,
                    code,
                    "associated constant projection exceeded the trait solver limit",
                );
                self.recovered = true;
                structural_const_error(expected)
            }
            TraitConstProjectionAnswer::MissingAssociatedConst { .. }
            | TraitConstProjectionAnswer::AssociatedConstKind { .. }
            | TraitConstProjectionAnswer::Normalized { .. } => {
                self.error(
                    span,
                    code,
                    "associated constant projection did not produce the required structural value",
                );
                self.recovered = true;
                structural_const_error(expected)
            }
        }
    }

    /// Create omitted method arguments in their own semantic domains. Trait
    /// selection consumes these same values, so a row or const never has to
    /// masquerade as a value type just to reach substitution.
    fn inferred_method_generic_arguments(
        &mut self,
        kinds: &[crate::GenericKind],
    ) -> Vec<GenericArgument> {
        kinds
            .iter()
            .enumerate()
            .map(|(index, kind)| match kind {
                crate::GenericKind::Type => GenericArgument::Type(self.inference.fresh()),
                crate::GenericKind::EffectRow => {
                    GenericArgument::EffectRow(self.inference.fresh_effects())
                }
                // Preserve declaration-region identity until call lifetime
                // opening relates it to the actual receiver or value.
                crate::GenericKind::Lifetime => {
                    GenericArgument::Lifetime(Lifetime::Generic(index as u32))
                }
                crate::GenericKind::Const(kind) => self.inference.fresh_const(*kind),
            })
            .collect()
    }
    fn header_path(
        &mut self,
        path: &[String],
        arguments: &[crate::header::HeaderGenericArgument],
    ) -> Type {
        let Some(name) = path.last() else {
            return Type::Error;
        };
        if path.len() == 1 {
            if name == "Self"
                && arguments.is_empty()
                && let Some(self_ty) = self.signatures.inherent_self_types.get(&self.definition)
            {
                return self.signatures.normalize_type_aliases(self_ty.clone());
            }
            if let Some(index) = self.generic_parameters.get(name) {
                return if arguments.is_empty() {
                    Type::Generic(*index)
                } else {
                    Type::Error
                };
            }
            if self.effect_row_parameters.contains_key(name) {
                self.error(
                    self.body.expression(self.body.root).span,
                    "G4171",
                    &format!("effect-row generic `{name}` cannot be used as a closure type"),
                );
                self.recovered = true;
                return Type::Error;
            }
            if self.lifetime_parameters.contains_key(name) {
                self.error(
                    self.body.expression(self.body.root).span,
                    "G4172",
                    &format!("lifetime generic `{name}` cannot be used as a closure type"),
                );
                self.recovered = true;
                return Type::Error;
            }
            if self.const_parameters.contains_key(name) {
                self.error(
                    self.body.expression(self.body.root).span,
                    "G4173",
                    &format!("const generic `{name}` cannot be used as a closure type"),
                );
                self.recovered = true;
                return Type::Error;
            }
            if let Some(scalar) = closure_scalar(name) {
                return if arguments.is_empty() {
                    Type::Scalar(scalar)
                } else {
                    Type::Error
                };
            }
            if name == "Array" {
                return match arguments {
                    [crate::header::HeaderGenericArgument::Type(element)] => {
                        Type::Array(Box::new(self.header_type(element)))
                    }
                    _ => Type::Error,
                };
            }
            // Match signature elaboration exactly: this compiler-owned type
            // spelling is admitted only while checking the bundled standard
            // library, where it can be hidden behind public aliases. It is
            // not a source-level capability for application packages.
            if name == "__StaticData" && self.module.package.0 == "std@0.1.0" {
                return match arguments {
                    [crate::header::HeaderGenericArgument::Type(element)] => {
                        let tag = match element {
                            crate::header::HeaderType::Path(path)
                                if path.as_slice() == ["Utf8Bytes"] =>
                            {
                                crate::STATIC_UTF8_DATA_TAG
                            }
                            crate::header::HeaderType::Path(path) if path.as_slice() == ["u8"] => {
                                crate::STATIC_RAW_U8_DATA_TAG
                            }
                            _ => return Type::Error,
                        };
                        Type::StaticData {
                            element: Box::new(Type::Scalar(crate::ScalarType::U8)),
                            tag,
                            alignment: 1,
                        }
                    }
                    _ => Type::Error,
                };
            }
        }
        match self
            .index
            .resolve_path(DefinitionNamespace::Type, self.module, path)
        {
            ResolutionState::Resolved(definition) => {
                let span = self.body.expression(self.body.root).span;
                let Some(arguments) = self.header_nominal_arguments(definition, arguments, span)
                else {
                    return Type::Error;
                };
                self.signatures.normalize_type_aliases(Type::Nominal {
                    definition,
                    arguments,
                })
            }
            ResolutionState::Ambiguous(_) => Type::Error,
            ResolutionState::Inaccessible(_)
            | ResolutionState::Unresolved
            | ResolutionState::Recovered => Type::Error,
        }
    }

    /// Source type annotations are semantic nominal applications, even when
    /// they occur inside a typed closure rather than a declaration header.
    /// Validate every supplied slot before constructing its identity; doing
    /// so prevents a row, region, or const from degrading into `Type::Error`.
    fn header_nominal_arguments(
        &mut self,
        definition: DefKey,
        source: &[crate::header::HeaderGenericArgument],
        span: Span,
    ) -> Option<Vec<GenericArgument>> {
        let kinds = self.index.type_generic_kinds(definition)?.to_vec();
        let arguments = self.complete_nominal_generic_arguments(
            definition,
            source,
            &kinds,
            span,
            "G4158",
            "nominal type annotation has the wrong number of generic arguments",
        )?;
        if arguments
            .iter()
            .zip(&kinds)
            .all(|(argument, kind)| generic_argument_matches_kind(argument, *kind))
        {
            return Some(arguments);
        }
        self.error(
            span,
            "G4158",
            "nominal type annotation has a generic argument of the wrong kind",
        );
        self.recovered = true;
        None
    }

    /// Complete an explicitly written nominal application with its declaration
    /// owned trailing structural defaults.  The default is substituted only
    /// after earlier source arguments are elaborated, so its canonical const
    /// identity is identical to spelling that value at every call site.
    fn complete_nominal_generic_arguments(
        &mut self,
        definition: DefKey,
        source: &[crate::header::HeaderGenericArgument],
        kinds: &[crate::GenericKind],
        span: Span,
        code: &'static str,
        arity_message: &'static str,
    ) -> Option<Vec<GenericArgument>> {
        let defaults = self.index.type_generic_defaults(definition).unwrap_or(&[]);
        if source.len() > kinds.len()
            || (source.len()..kinds.len())
                .any(|index| defaults.get(index).is_none_or(Option::is_none))
        {
            self.error(span, code, arity_message);
            self.recovered = true;
            return None;
        }
        let mut arguments = self.body_generic_arguments(
            source,
            &kinds[..source.len()],
            span,
            code,
            arity_message,
        )?;
        for index in source.len()..kinds.len() {
            let default = defaults
                .get(index)
                .and_then(Option::as_ref)
                .expect("missing nominal default was rejected above");
            arguments.push(instantiate_nominal_default(default, &arguments));
        }
        Some(arguments)
    }
    fn projection_error(&mut self, code: &'static str, message: &str) {
        let span = self.body.expression(self.body.root).span;
        self.error(span, code, message);
        self.recovered = true;
    }
    fn closure_effects(
        &mut self,
        effects: &crate::header::EffectRowHeader,
        span: Span,
    ) -> crate::types::EffectRow {
        let mut resolved = crate::types::EffectRow::empty();
        for effect in &effects.effects {
            match effect {
                crate::header::HeaderType::Path(path) => {
                    match self
                        .index
                        .resolve_path(DefinitionNamespace::Effect, self.module, path)
                    {
                        ResolutionState::Resolved(definition) => {
                            resolved.effects.insert(EffectInstance {
                                definition,
                                arguments: vec![],
                            });
                        }
                        _ => {
                            self.error(span, "G4115", "closure effect is unresolved");
                            self.recovered = true;
                        }
                    }
                }
                crate::header::HeaderType::Application(base, arguments) => {
                    let crate::header::HeaderType::Path(path) = base.as_ref() else {
                        self.error(
                            span,
                            "G4115",
                            "closure effect application is not a named effect",
                        );
                        self.recovered = true;
                        continue;
                    };
                    let ResolutionState::Resolved(definition) =
                        self.index
                            .resolve_path(DefinitionNamespace::Effect, self.module, path)
                    else {
                        self.error(span, "G4115", "closure effect is unresolved");
                        self.recovered = true;
                        continue;
                    };
                    let Some(ElaboratedHeader::Effect(declaration)) =
                        self.signatures.definitions.get(&definition)
                    else {
                        self.error(
                            span,
                            "G4115",
                            "closure effect target is not an effect declaration",
                        );
                        self.recovered = true;
                        continue;
                    };
                    let kinds = declaration.generic_kinds.clone();
                    if kinds.len() != arguments.len() {
                        self.error(
                            span,
                            "G4115",
                            "closure effect application has the wrong number of arguments",
                        );
                        self.recovered = true;
                        continue;
                    }
                    let Some(arguments) = self.body_generic_arguments(
                        arguments,
                        &kinds,
                        span,
                        "G4115",
                        "closure effect application has the wrong number of arguments",
                    ) else {
                        continue;
                    };
                    if !arguments
                        .iter()
                        .zip(&kinds)
                        .all(|(argument, kind)| generic_argument_matches_kind(argument, *kind))
                    {
                        self.error(
                            span,
                            "G4115",
                            "closure effect application has a generic argument of the wrong kind",
                        );
                        self.recovered = true;
                        continue;
                    }
                    resolved.effects.insert(EffectInstance {
                        definition,
                        arguments,
                    });
                }
                crate::header::HeaderType::Projection {
                    subject,
                    trait_path,
                    trait_arguments,
                    name,
                    item_arguments,
                } => {
                    let subject = self.header_type(subject);
                    let ResolutionState::Resolved(trait_definition) = self.index.resolve_path(
                        DefinitionNamespace::Trait,
                        self.module,
                        trait_path,
                    ) else {
                        self.error(
                            span,
                            "G4115",
                            "closure associated effect row has an unresolved trait",
                        );
                        self.recovered = true;
                        continue;
                    };
                    let trait_kinds = self
                        .index
                        .trait_generic_kinds(trait_definition)
                        .unwrap_or(&[]);
                    let Some(trait_arguments) =
                        self.header_generic_arguments(trait_arguments, trait_kinds)
                    else {
                        continue;
                    };
                    let Some(ElaboratedHeader::Trait(trait_header)) =
                        self.signatures.definitions.get(&trait_definition)
                    else {
                        self.error(
                            span,
                            "G4115",
                            "closure associated effect row target is not a trait",
                        );
                        self.recovered = true;
                        continue;
                    };
                    let Some(item) = trait_header.associated_types.get(name) else {
                        self.error(
                            span,
                            "G4115",
                            "trait does not declare this associated effect row",
                        );
                        self.recovered = true;
                        continue;
                    };
                    if !item.effect_row || item.generics != item_arguments.len() as u32 {
                        self.error(
                            span,
                            "G4115",
                            "closure associated effect-row projection has an invalid item kind or arity",
                        );
                        self.recovered = true;
                        continue;
                    }
                    let item_kinds = item.generic_kinds.clone();
                    let Some(item_arguments) =
                        self.header_generic_arguments(item_arguments, &item_kinds)
                    else {
                        continue;
                    };
                    if !projection_is_concrete(&subject)
                        || !trait_arguments.iter().all(generic_argument_is_concrete)
                        || !item_arguments.iter().all(generic_argument_is_concrete)
                    {
                        self.error(
                            span,
                            "G4115",
                            "closure associated effect-row projection must be concrete",
                        );
                        self.recovered = true;
                        continue;
                    }
                    match self
                        .trait_query()
                        .normalize_associated_effect_row_application(
                            TraitGoal {
                                relation: crate::ElaboratedTraitReference {
                                    definition: trait_definition,
                                    arguments: trait_arguments,
                                },
                                subject,
                            },
                            name,
                            &item_arguments,
                        ) {
                        TraitEffectRowProjectionAnswer::Normalized { row, .. }
                            if row.tail.is_none() && row.projections.is_empty() =>
                        {
                            resolved.effects.extend(row.effects);
                        }
                        _ => {
                            self.error(
                                span,
                                "G4115",
                                "closure associated effect-row projection cannot be normalized",
                            );
                            self.recovered = true;
                        }
                    }
                }
                _ => {
                    self.error(span, "G4115", "closure effect is not a named effect");
                    self.recovered = true;
                }
            }
        }
        if let Some(tail) = &effects.tail {
            match self.effect_row_parameters.get(tail).copied() {
                Some(index) => resolved.tail = Some(crate::EffectTail::Generic(index)),
                None => {
                    self.error(
                        span,
                        "G4115",
                        "typed closure effect-row tail requires an enclosing `EffectRow` binder",
                    );
                    self.recovered = true;
                }
            }
        }
        resolved
    }
    fn refinement_test_value(&mut self, subject: CoreId, pattern: CorePattern, environment: RefinementEnvironment, span: Span) -> CoreId {
        let ResolutionState::Resolved(definition) = self.index.resolve_path(DefinitionNamespace::Type, self.module, &["Test".into()]) else {
            return self.fail(span, "G4183", "`is` requires the ordinary `Test<Y, N>` enum in type scope");
        };
        let Some(ElaboratedHeader::Nominal { generic_kinds, layout: ElaboratedNominalLayout::Enum(variants), .. }) = self.signatures.definitions.get(&definition) else {
            return self.fail(span, "G4183", "`Test` must be an ordinary two-parameter enum");
        };
        if generic_kinds != &[crate::GenericKind::Type, crate::GenericKind::Type] || variants.len() != 2 {
            return self.fail(span, "G4183", "`Test` must have two type parameters and two variants");
        }
        let Some(yes) = variants.iter().position(|variant| variant.name == "Yes") else { return self.fail(span, "G4183", "`Test` lacks its `Yes` constructor"); };
        let Some(no) = variants.iter().position(|variant| variant.name == "No") else { return self.fail(span, "G4183", "`Test` lacks its `No` constructor"); };
        let Ok(yes_type) = environment.binding_pack_type(true, Lifetime::Elided) else { return self.fail(span, "G4183", "invalid positive binding environment"); };
        let Ok(no_type) = environment.binding_pack_type(false, Lifetime::Elided) else { return self.fail(span, "G4183", "invalid negative binding environment"); };
        let arguments = vec![GenericArgument::Type(yes_type.clone()), GenericArgument::Type(no_type.clone())];
        for (variant, expected) in [(yes, &yes_type), (no, &no_type)] {
            let Ok(fields) = self.signatures.instantiate_enum_fields_generic(definition, &arguments, variant as u32) else {
                return self.fail(span, "G4183", "`Test` constructor has an invalid payload contract");
            };
            if fields.len() != 1 || &fields[0].ty != expected {
                return self.fail(span, "G4183", "`Test::Yes` and `Test::No` must carry their respective context parameters");
            }
        }
        let result = Type::Nominal { definition, arguments };
        let mut clauses = vec![];
        for (positive, variant, pack_type) in [(true, yes, yes_type), (false, no, no_type)] {
            let bindings = if positive { environment.binding_types.clone() } else { vec![] };
            let fields = bindings.iter().map(|(name, ty)| self.alloc(CoreKind::Local(name.clone()), ty.clone(), span)).collect();
            let pack = self.alloc(CoreKind::Record { definition: crate::refinement::bindings_definition(), fields }, pack_type, span);
            let body = self.alloc(CoreKind::Enum { definition, variant: variant as u32, fields: vec![pack] }, result.clone(), span);
            clauses.push(CoreCompletionClause { pattern: if positive { pattern.clone() } else { CorePattern::Any }, bindings,
                refinement: None, body, span });
        }
        self.alloc(CoreKind::Completion { computation: subject, clauses, refinement_test: Some(environment), handles_operations: false }, result, span)
    }

    fn refinement_environment(
        &mut self,
        subject: CoreId,
        pattern: &CorePattern,
        binding_types: Vec<(String, Type)>,
    ) -> RefinementEnvironment {
        let brand = RefinementBrand {
            owner: self.definition,
            refinement: self.next_refinement,
        };
        self.next_refinement += 1;
        let subject = match &self.expressions[subject.0 as usize].kind {
            CoreKind::Local(name) => Some(name.clone()),
            _ => None,
        };
        let mut bindings = Vec::new();
        collect_pattern_bindings(pattern, &mut bindings);
        RefinementEnvironment {
            brand,
            subject,
            binding_keys: (0..bindings.len()).map(|binder| RefinementBindingKey { environment: brand, binder: binder as u32 }).collect(),
            bindings,
            binding_types: binding_types.into_iter()
                .map(|(name, ty)| (name, refinement_binding_type(ty))).collect(),
            sealed: true,
        }
    }
    fn closure_captures(&self, body: CoreId, parameters: &[(String, Type)]) -> Vec<ClosureCapture> {
        let mut parameter_names = parameters
            .iter()
            .map(|(name, _)| name.clone())
            .collect::<std::collections::BTreeSet<_>>();
        let mut captures = std::collections::BTreeMap::<String, (CaptureMode, Type)>::new();
        self.collect_captures(body, &mut parameter_names, &mut captures);
        captures
            .into_iter()
            .map(|(name, (mode, ty))| ClosureCapture { name, mode, ty })
            .collect()
    }

    fn owned_capture_mode(&self, ty: &Type) -> CaptureMode {
        if self
            .signatures
            .principal_use_interval_with_solver(ty, &self.trait_solver)
            .is_some_and(|quantity| quantity == crate::quantity::Quantity::UNRESTRICTED)
        {
            CaptureMode::Copy
        } else {
            CaptureMode::Move
        }
    }

    fn inferred_capture_mode(&self, ty: &Type) -> CaptureMode {
        // Callable and reference capabilities retain their established
        // invocation/loan authorities when inferred. An explicit `move (...)`
        // remains available when a closure must own such a value; ordinary
        // data captures use the default copy-or-move rule below.
        if matches!(
            ty,
            Type::Callable { .. }
                | Type::Reference { .. }
                | Type::Generic(_)
                | Type::Projection { .. }
                | Type::Infer(_)
        ) {
            CaptureMode::SharedBorrow
        } else {
            self.owned_capture_mode(ty)
        }
    }

    /// Apply the optional `move (name, ...) { ... }` capture list after
    /// ordinary body-driven capture inference. The list can retain a value
    /// whose body only borrows it, which is what permits an escaping closure
    /// to own its environment without forcing a body-level `move name`.
    fn force_move_captures(
        &mut self,
        captures: Vec<ClosureCapture>,
        forced: Option<Vec<String>>,
        span: Span,
    ) -> Vec<ClosureCapture> {
        let Some(forced) = forced else {
            return captures;
        };
        let mut captures = captures
            .into_iter()
            .map(|capture| (capture.name, (capture.mode, capture.ty)))
            .collect::<std::collections::BTreeMap<_, _>>();
        for name in forced {
            let Some(ty) = self.locals.lookup(&name).cloned() else {
                self.error(
                    span,
                    "G4120",
                    &format!("closure move capture `{name}` does not name an outer local"),
                );
                self.recovered = true;
                continue;
            };
            let mode = self.owned_capture_mode(&ty);
            captures.insert(name, (mode, ty));
        }
        captures
            .into_iter()
            .map(|(name, (mode, ty))| ClosureCapture { name, mode, ty })
            .collect()
    }
    /// A continuation snapshot is valid only while its handler frame is
    /// active.  A closure may capture it when the complete enclosing clause
    /// proves that the closure is immediately invoked; returning, storing, or
    /// passing that closure would let the snapshot outlive the frame and is
    /// therefore rejected.  This mirrors refinement-capture checking but
    /// retains the stronger handler-frame diagnostic and provenance.
    fn check_resumption_capture_escapes(
        &mut self,
        branch: CoreId,
        resumptions: &std::collections::BTreeSet<String>,
    ) {
        if resumptions.is_empty() {
            return;
        }
        // Capture names are not continuation identities: a nested operation
        // payload may deliberately shadow an outer `with k`.  Freeze the
        // currently visible resumption type while the arm remains active so
        // the later structural scan only diagnoses the actual snapshot, not
        // an ordinary same-spelled payload local.
        let resumption_types = resumptions
            .iter()
            .filter_map(|name| {
                self.active_resumption(name)
                    .and_then(|_| self.locals.lookup(name).cloned())
                    .map(|ty| (name.clone(), ty))
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let mut closures = Vec::new();
        self.collect_refinement_capturing_closures(branch, &resumption_types, &mut closures);
        for (closure, resumption) in closures {
            if self.refinement_closure_is_immediately_invoked(branch, closure) {
                continue;
            }
            self.error(
                self.expressions[closure.0 as usize].span,
                "G4174",
                &format!(
                    "nested closure cannot let handler resumption `{resumption}` escape its active frame",
                ),
            );
            self.recovered = true;
        }
    }
    /// A refinement binder is a branch-local proof-backed projection.  A
    /// closure may use such a projection only while the branch proves the
    /// refinement.  Direct invocation is therefore sound, including the
    /// common `let callback = { ... }; callback()` spelling, whereas
    /// returning, storing, passing, or otherwise retaining the closure is
    /// an escape.  We check this after elaborating the complete branch so the
    /// decision is based on frozen Core control structure rather than on the
    /// order in which an initializer happened to be elaborated.
    fn check_refinement_capture_escapes(
        &mut self,
        branch: CoreId,
        refinement_bindings: &std::collections::BTreeSet<String>,
    ) {
        if refinement_bindings.is_empty() {
            return;
        }
        let refinement_types = refinement_bindings
            .iter()
            .filter_map(|name| {
                self.locals
                    .lookup(name)
                    .cloned()
                    .map(|ty| (name.clone(), ty))
            })
            .collect::<std::collections::BTreeMap<_, _>>();
        let mut closures = Vec::new();
        self.collect_refinement_capturing_closures(branch, &refinement_types, &mut closures);
        for (closure, binding) in closures {
            if self.refinement_closure_is_immediately_invoked(branch, closure) {
                continue;
            }
            let span = self.expressions[closure.0 as usize].span;
            self.error(
                span,
                "G4171",
                &format!(
                    "nested closure cannot capture refinement binder `{binding}` outside its proven branch"
                ),
            );
            self.recovered = true;
        }
    }

    fn collect_refinement_capturing_closures(
        &self,
        expression: CoreId,
        refinement_bindings: &std::collections::BTreeMap<String, Type>,
        closures: &mut Vec<(CoreId, String)>,
    ) {
        let node = &self.expressions[expression.0 as usize];
        if let CoreKind::Closure {
            environment, body, ..
        } = &node.kind
        {
            if let Some(binding) = environment.captures.iter().find(|capture| {
                refinement_bindings
                    .get(&capture.name)
                    .is_some_and(|ty| ty == &capture.ty)
            }) {
                closures.push((expression, binding.name.clone()));
            }
            // A closure body is checked in the lexical branch in which that
            // closure is created.  Inspect nested closures as well: a child
            // that retains a refinement capture is independently required to
            // be directly invoked before its enclosing scope ends.
            self.collect_refinement_capturing_closures(*body, refinement_bindings, closures);
            return;
        }
        for child in core_children(&node.kind) {
            self.collect_refinement_capturing_closures(child, refinement_bindings, closures);
        }
    }

    fn refinement_closure_is_immediately_invoked(&self, branch: CoreId, closure: CoreId) -> bool {
        let node = &self.expressions[branch.0 as usize].kind;
        match node {
            CoreKind::Call { callee, .. } if *callee == closure => true,
            CoreKind::Block(values) => {
                values.windows(2).enumerate().any(|(index, window)| {
                    let [CoreId(let_index), CoreId(call_index)] = *window else {
                        return false;
                    };
                    let CoreKind::Let { name, value } = &self.expressions[let_index as usize].kind
                    else {
                        return false;
                    };
                    let CoreKind::Call {
                        callee, arguments, ..
                    } = &self.expressions[call_index as usize].kind
                    else {
                        return false;
                    };
                    if !matches!(
                        &self.expressions[callee.0 as usize].kind,
                        CoreKind::Local(callee_name) if *value == closure && callee_name == name
                    ) {
                        return false;
                    }
                    // The immediate call is the only permitted use of its
                    // temporary local.  In particular, a closure cannot be
                    // handed to another abstraction and then called locally
                    // as a way to launder its branch dependency.
                    if arguments
                        .iter()
                        .any(|argument| self.core_contains_local(*argument, name))
                    {
                        return false;
                    }
                    !values[index + 2..]
                        .iter()
                        .any(|following| self.core_contains_local(*following, name))
                }) || values
                    .iter()
                    .any(|value| self.refinement_closure_is_immediately_invoked(*value, closure))
            }
            CoreKind::Closure { .. } => false,
            _ => core_children(node)
                .into_iter()
                .any(|child| self.refinement_closure_is_immediately_invoked(child, closure)),
        }
    }

    fn core_contains_local(&self, expression: CoreId, name: &str) -> bool {
        match &self.expressions[expression.0 as usize].kind {
            CoreKind::Local(candidate) => candidate == name,
            kind => core_children(kind)
                .into_iter()
                .any(|child| self.core_contains_local(child, name)),
        }
    }
    /// A closure executes after its surrounding label scope may have exited.
    /// Keep transfers to an outer label out of its environment rather than
    /// deferring an invalid nonlocal edge to MIR. Labels declared inside the
    /// closure have fresh brands and are not in `active_labels` here.
    fn check_label_transfer_escape(&mut self, body: CoreId, span: Span) {
        let active = self
            .active_labels
            .iter()
            .map(|label| label.brand)
            .collect::<std::collections::BTreeSet<_>>();
        if active.is_empty() {
            return;
        }
        let mut transfers = Vec::new();
        collect_transfer_brands(&self.expressions, body, &mut transfers);
        if transfers.into_iter().any(|brand| active.contains(&brand)) {
            self.error(
                span,
                "G4179",
                "closure cannot capture a transfer target from an enclosing label scope",
            );
            self.recovered = true;
        }
    }
    /// Handler clauses retain the exact enclosing label brand in Core.  MIR
    /// now has a cleanup-carrying `Leave` terminator and the VM preserves it
    /// across a suspended handler frame, so a lexically valid transfer is not
    /// discarded merely because its source lies in a clause.  Closure escape
    /// remains separately rejected above; unsupported handler CFG shapes fail
    /// closed during MIR lowering rather than losing this proof here.
    fn check_handler_label_transfer_escape(&mut self, body: CoreId, span: Span) {
        let active = self
            .active_labels
            .iter()
            .map(|label| label.brand)
            .collect::<std::collections::BTreeSet<_>>();
        if active.is_empty() {
            return;
        }
        let mut transfers = Vec::new();
        collect_transfer_brands(&self.expressions, body, &mut transfers);
        if transfers.into_iter().any(|brand| active.contains(&brand)) {
            // The active-set membership is the owner/brand proof consumed by
            // `MirTerminator::Leave`; do not turn it into a recovered Core
            // error now that the target survives handler lowering.
            let _ = span;
        }
    }
    fn collect_captures(
        &self,
        id: CoreId,
        locals: &mut std::collections::BTreeSet<String>,
        captures: &mut std::collections::BTreeMap<String, (CaptureMode, Type)>,
    ) {
        let expression = &self.expressions[id.0 as usize];
        match &expression.kind {
            CoreKind::Local(name) if !locals.contains(name) => {
                record_capture(
                    captures,
                    name,
                    self.inferred_capture_mode(&expression.ty),
                    expression.ty.clone(),
                );
            }
            CoreKind::Resumption { name, .. } if !locals.contains(name) => {
                record_capture(
                    captures,
                    name,
                    self.inferred_capture_mode(&expression.ty),
                    expression.ty.clone(),
                );
            }
            CoreKind::Move(value) => {
                if let Some((name, ty)) = self.capture_root_local(*value) {
                    let mode = self.owned_capture_mode(&ty);
                    record_capture(captures, &name, mode, ty);
                } else {
                    self.collect_captures(*value, locals, captures);
                }
            }
            CoreKind::Deref(value) => self.collect_captures(*value, locals, captures),
            CoreKind::Borrow { unique, value } => {
                if let CoreKind::Local(name) = &self.expressions[value.0 as usize].kind {
                    record_capture(
                        captures,
                        name,
                        if *unique {
                            CaptureMode::UniqueBorrow
                        } else {
                            CaptureMode::SharedBorrow
                        },
                        self.expressions[value.0 as usize].ty.clone(),
                    );
                } else {
                    self.collect_captures(*value, locals, captures);
                }
            }
            CoreKind::Let { name, value } => {
                self.collect_captures(*value, locals, captures);
                locals.insert(name.clone());
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.collect_captures(*body, locals, captures)
            }
            CoreKind::Assign { place, value } => {
                self.collect_captures(*value, locals, captures);
                if let Some((name, ty)) = place.root_local()
                    && !locals.contains(name)
                {
                    record_capture(captures, name, CaptureMode::UniqueBorrow, ty.clone());
                }
            }
            CoreKind::Call {
                callee, arguments, ..
            } => {
                self.collect_captures(*callee, locals, captures);
                for argument in arguments {
                    self.collect_captures(*argument, locals, captures);
                }
            }
            CoreKind::Perform { arguments, .. } => {
                for argument in arguments {
                    self.collect_captures(*argument, locals, captures);
                }
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.collect_captures(*computation, locals, captures);
                for clause in clauses {
                    let mut scoped = locals.clone();
                    for (name, _) in &clause.bindings {
                        scoped.insert(name.clone());
                    }
                    if let CoreHandlerResumption::Explicit { name, .. } = &clause.resumption {
                        scoped.insert(name.clone());
                    }
                    self.collect_captures(clause.body, &mut scoped, captures);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
                ..
            } => {
                self.collect_captures(*computation, locals, captures);
                for clause in clauses {
                    let mut scoped = locals.clone();
                    for (name, _) in &clause.bindings {
                        scoped.insert(name.clone());
                    }
                    self.collect_captures(clause.body, &mut scoped, captures);
                }
            }
            CoreKind::Tuple(values) => {
                for value in values {
                    self.collect_captures(*value, locals, captures);
                }
            }
            CoreKind::Array(values) => {
                for value in values {
                    self.collect_captures(*value, locals, captures);
                }
            }
            CoreKind::Record { fields, .. } => {
                for field in fields {
                    self.collect_captures(*field, locals, captures);
                }
            }
            CoreKind::Enum { fields, .. } => {
                for field in fields {
                    self.collect_captures(*field, locals, captures);
                }
            }
            CoreKind::Field { base, .. } => self.collect_captures(*base, locals, captures),
            CoreKind::PatternTest { subject, .. } => {
                self.collect_captures(*subject, locals, captures)
            }
            CoreKind::IntrinsicCall { arguments, .. } => {
                for argument in arguments {
                    self.collect_captures(*argument, locals, captures);
                }
            }
            CoreKind::Block(values) => {
                let mut scoped = locals.clone();
                for value in values {
                    self.collect_captures(*value, &mut scoped, captures);
                }
            }
            // A nested closure is itself a runtime environment-construction
            // site.  Its free captures which are not locals of this closure
            // must therefore be forwarded through the enclosing environment:
            // the lifted outer body cannot materialize the child from a
            // grandparent register it does not own.  Captures of an enclosing
            // parameter/local are already available to the outer lifted body
            // and deliberately do not widen its layout.  Preserve the child
            // mode here so a move or unique borrow cannot be weakened while
            // it crosses more than one callable boundary.
            CoreKind::Closure { environment, .. } => {
                for capture in &environment.captures {
                    if !locals.contains(&capture.name) {
                        record_capture(captures, &capture.name, capture.mode, capture.ty.clone());
                    }
                }
            }
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error => {}
            CoreKind::Local(_) => {}
        }
    }

    /// A closure environment currently carries local roots, not projected
    /// field slots.  Moving `pair.callback` inside a closure therefore
    /// transfers the owning `pair` into that environment; retaining a shared
    /// capture would incorrectly leave the outer aggregate usable while a
    /// later closure invocation can consume one of its fields.
    fn capture_root_local(&self, id: CoreId) -> Option<(String, Type)> {
        match &self.expressions[id.0 as usize].kind {
            CoreKind::Local(name) => {
                Some((name.clone(), self.expressions[id.0 as usize].ty.clone()))
            }
            CoreKind::Field { base, .. } => self.capture_root_local(*base),
            _ => None,
        }
    }
    /// Typed Core is a frozen semantic boundary: body-local inference holes
    /// can help elaboration but cannot escape to PlaceFlow, MIR, or caches.
    fn seal_types(&mut self) {
        self.inference.finish_body_lifetimes();
        let mut pending = std::mem::take(&mut self.pending_callable_bounds);
        while !pending.is_empty() {
            let previous = pending.len();
            for bound in pending {
                self.check_intrinsic_callable_bindings(
                    vec![(bound.subject, bound.relation)],
                    bound.type_bindings,
                    bound.effect_bindings,
                    bound.span,
                    true,
                );
            }
            pending = std::mem::take(&mut self.pending_callable_bounds);
            // A solved Output/input equality can expose the shape needed by
            // an earlier obligation. Retry while at least one was discharged;
            // no-progress subjects are ambiguous, never guessed callables.
            if pending.len() == previous {
                for bound in pending {
                    self.check_intrinsic_callable_bindings(
                        vec![(bound.subject, bound.relation)],
                        bound.type_bindings,
                        bound.effect_bindings,
                        bound.span,
                        false,
                    );
                }
                break;
            }
        }
        for index in 0..self.expressions.len() {
            let span = self.expressions[index].span;
            let ty = self.expressions[index].ty.clone();
            self.expressions[index].ty = self.zonk_type(ty, span);
            let kind = self.expressions[index].kind.clone();
            let result = self.expressions[index].ty.clone();
            self.expressions[index].kind = self.zonk_core_metadata(kind, span, &result);
        }
    }

    fn zonk_core_metadata(&mut self, mut kind: CoreKind, span: Span, result: &Type) -> CoreKind {
        match &mut kind {
            CoreKind::Closure {
                parameters,
                environment,
                ..
            } => {
                for (_, ty) in parameters {
                    *ty = self.zonk_type(ty.clone(), span);
                }
                for capture in &mut environment.captures {
                    capture.ty = self.zonk_type(capture.ty.clone(), span);
                }
                // RunsIn repeats the callable's effect contract as sealed
                // evidence.  It is allocated while a contextual closure may
                // still carry an effect-row inference variable, so freeze it
                // alongside the closure type and capture layout.
                environment.runs_in.effects =
                    self.zonk_effect_row(environment.runs_in.effects.clone(), span);
            }
            CoreKind::Assign { place, .. } => self.zonk_place(place, span),
            CoreKind::Label { .. } | CoreKind::LabelValue { .. } | CoreKind::Transfer { .. } => {}
            CoreKind::Function { arguments, .. } | CoreKind::Constant { arguments, .. } => {
                *arguments = arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
            }
            CoreKind::TraitMethod {
                trait_arguments,
                method_arguments,
                deferred,
                ..
            } => {
                *trait_arguments = trait_arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
                *method_arguments = method_arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
                if let Some(deferred) = deferred {
                    deferred.relation.arguments = deferred
                        .relation
                        .arguments
                        .iter()
                        .cloned()
                        .map(|argument| self.zonk_generic_argument(argument, span))
                        .collect();
                    deferred.subject = self.zonk_type(deferred.subject.clone(), span);
                }
            }
            CoreKind::Perform {
                effect,
                arguments,
                payload_types,
                reference_contract,
                reference_origin,
                reference_shape,
                ..
            } => {
                effect.arguments = effect
                    .arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
                for payload_type in payload_types {
                    *payload_type = self.zonk_type(payload_type.clone(), span);
                }
                // The declared operation relation is determined before
                // zonking can collapse distinct generic lifetimes into the
                // same caller-local representation.  Fall back to the
                // realized expression types only for a genuinely opaque
                // declaration contract, as ordinary calls do.
                if matches!(reference_contract, CallReferenceOrigin::Opaque) {
                    *reference_origin = call_reference_origin(
                        self.signatures,
                        &self.expressions,
                        arguments,
                        result,
                    );
                } else {
                    *reference_origin = reference_contract.clone();
                }
                *reference_shape = call_reference_shape(self.signatures, result, reference_origin);
            }
            CoreKind::Call {
                arguments,
                reference_origin,
                reference_shape,
                ..
            } => {
                // Generic/HRTB callable signatures preserve a more precise
                // relationship than the caller's erased local regions.  Once
                // that contract names a unique source argument, keep it
                // frozen instead of recomputing an ambiguous `Elided` match.
                if matches!(reference_origin, CallReferenceOrigin::Opaque) {
                    *reference_origin = call_reference_origin(
                        self.signatures,
                        &self.expressions,
                        arguments,
                        result,
                    );
                }
                *reference_shape = call_reference_shape(self.signatures, result, reference_origin);
            }
            CoreKind::PatternTest {
                pattern,
                refinement,
                ..
            } => {
                self.zonk_pattern(pattern, span);
                for (_, ty) in &mut refinement.binding_types {
                    *ty = self.zonk_type(ty.clone(), span);
                }
            }
            CoreKind::Handle { clauses, .. } => {
                for clause in clauses {
                    clause.effect.arguments = clause
                        .effect
                        .arguments
                        .iter()
                        .cloned()
                        .map(|argument| self.zonk_generic_argument(argument, span))
                        .collect();
                    clause.payload_types = clause
                        .payload_types
                        .iter()
                        .cloned()
                        .map(|ty| self.zonk_type(ty, span))
                        .collect();
                    for pattern in &mut clause.patterns {
                        self.zonk_pattern(pattern, span);
                    }
                    for (_, ty) in &mut clause.bindings {
                        *ty = self.zonk_type(ty.clone(), span);
                    }
                    if let Some(continuation) = &mut clause.continuation {
                        continuation.parameter =
                            self.zonk_type(continuation.parameter.clone(), span);
                        continuation.result = self.zonk_type(continuation.result.clone(), span);
                        continuation.effects =
                            self.zonk_effect_row(continuation.effects.clone(), span);
                    }
                }
            }
            CoreKind::Completion { clauses, refinement_test, .. } => {
                if let Some(environment) = refinement_test {
                    for (_, ty) in &mut environment.binding_types { *ty = self.zonk_type(ty.clone(), span); }
                }
                for clause in clauses {
                    self.zonk_pattern(&mut clause.pattern, span);
                    for (_, ty) in &mut clause.bindings {
                        *ty = self.zonk_type(ty.clone(), span);
                    }
                    if let Some(refinement) = &mut clause.refinement {
                        self.zonk_pattern(&mut refinement.pattern, span);
                        for (_, ty) in &mut refinement.environment.binding_types {
                            *ty = self.zonk_type(ty.clone(), span);
                        }
                    }
                }
            }
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Tuple(_)
            | CoreKind::Array(_)
            | CoreKind::Record { .. }
            | CoreKind::Field { .. }
            | CoreKind::Enum { .. }
            | CoreKind::Let { .. }
            | CoreKind::IntrinsicCall { .. }
            | CoreKind::Block(_)
            | CoreKind::Borrow { .. }
            | CoreKind::Deref(_)
            | CoreKind::Move(_)
            | CoreKind::Error => {}
        }
        kind
    }

    fn zonk_place(&mut self, place: &mut CorePlace, span: Span) {
        match place {
            CorePlace::Local { ty, .. } => *ty = self.zonk_type(ty.clone(), span),
            CorePlace::Field { base, ty, .. } => {
                self.zonk_place(base, span);
                *ty = self.zonk_type(ty.clone(), span);
            }
            CorePlace::Deref { ty, .. } => *ty = self.zonk_type(ty.clone(), span),
            CorePlace::Error => {}
        }
    }

    fn zonk_pattern(&mut self, pattern: &mut CorePattern, span: Span) {
        match pattern {
            CorePattern::Tuple(values) => {
                for value in values {
                    self.zonk_pattern(value, span);
                }
            }
            CorePattern::Array { element, elements } => {
                *element = self.zonk_type(element.clone(), span);
                for value in elements {
                    self.zonk_pattern(value, span);
                }
            }
            CorePattern::Record {
                field_types,
                fields,
                ..
            }
            | CorePattern::Enum {
                field_types,
                fields,
                ..
            } => {
                for field_type in field_types {
                    *field_type = self.zonk_type(field_type.clone(), span);
                }
                for field in fields {
                    field.ty = self.zonk_type(field.ty.clone(), span);
                    self.zonk_pattern(&mut field.pattern, span);
                }
            }
            CorePattern::Any
            | CorePattern::Bind { .. }
            | CorePattern::Literal(_)
            | CorePattern::Error => {}
        }
    }

    fn zonk_effect_row(&mut self, effects: EffectRow, span: Span) -> EffectRow {
        match self.inference.zonk_effects_allowing_generic_tail(effects) {
            Ok(effects) => effects,
            Err(_) => {
                self.error(
                    span,
                    "G4116",
                    "cannot infer a complete Typed Core effect row",
                );
                self.recovered = true;
                EffectRow::empty()
            }
        }
    }
    fn zonk_type(&mut self, ty: Type, span: Span) -> Type {
        match self.inference.zonk(ty) {
            Ok(ty) => ty,
            Err(_) => {
                self.error(span, "G4116", "cannot infer a complete closure type");
                self.recovered = true;
                Type::Error
            }
        }
    }

    fn zonk_generic_argument(&mut self, argument: GenericArgument, span: Span) -> GenericArgument {
        let fallback = argument.clone();
        match self.inference.zonk_generic_argument(argument) {
            Ok(argument) => argument,
            Err(_) => {
                self.error(
                    span,
                    "G4116",
                    "cannot infer a complete Typed Core generic argument",
                );
                self.recovered = true;
                // Keep the original body-local term so the independent Core
                // and MIR validators also reject a forged/recovered product;
                // replacing it with `Type::Error` would turn this into an
                // unrelated generic-kind failure during instance discovery.
                fallback
            }
        }
    }

    /// Unify a body contract without allowing its declared regions to be
    /// solved from a shorter local loan. This is used at returns, assignments,
    /// and aggregate field construction; call sites use the opening variant
    /// below instead.
    fn unify_rigid_lifetimes(
        &mut self,
        expected: Type,
        actual: Type,
        span: Span,
    ) -> Result<(), ()> {
        // Equality inference may solve constructor-owned holes, but never a
        // declared region. The directional lifetime proof below still owns
        // all outlives/coercion checks when rigid lifetimes differ.
        let _ = self.inference.unify(expected.clone(), actual.clone());
        let expected = self.inference.zonk(expected.clone()).unwrap_or(expected);
        let actual = self.inference.zonk(actual.clone()).unwrap_or(actual);
        let mut substitution = CallLifetimeSubstitution::default();
        let aligned = match align_lifetime_types(
            &expected,
            &actual,
            &mut substitution,
            LifetimeMode::Rigid,
            0,
        ) {
            Ok(value) => value,
            Err(error) => {
                self.lifetime_error(span, error);
                return Err(());
            }
        };
        if self.inference.unify(aligned, actual).is_err() {
            Err(())
        } else {
            Ok(())
        }
    }

    /// Open one callable's lifetime binders, prove each reference argument
    /// against the parameter it enters, then substitute the resulting region
    /// evidence into its result/effect contract. This is the sole point where
    /// declaration generic lifetimes and HRTB depth-zero binders become caller
    /// lifetimes.
    fn instantiate_call_lifetimes(
        &mut self,
        parameters: Vec<Type>,
        result: Type,
        effects: crate::types::EffectRow,
        arguments: &[CoreId],
        span: Span,
        unsafe_reference_result: Option<Lifetime>,
    ) -> Result<(
        Vec<Type>,
        Type,
        crate::types::EffectRow,
        CallLifetimeSubstitution,
    ), ()> {
        let mut substitution = CallLifetimeSubstitution::default();
        let mut aligned_parameters = Vec::with_capacity(parameters.len());
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let raw_actual = self.expressions[argument.0 as usize].ty.clone();
            // A local can retain a solved inference variable in an otherwise
            // structural nominal application until Typed Core is sealed. The
            // lifetime relation must inspect that solved shape before it
            // opens a callee's region binders; otherwise `Box<&'a T>` looks
            // opaque and leaves `'a` uninstantiated in the result. Keep the
            // raw value when unrelated inference remains open so ordinary
            // call unification still owns that diagnostic.
            let actual = self
                .inference
                .zonk(raw_actual.clone())
                .unwrap_or(raw_actual);
            let aligned = match align_lifetime_types(
                parameter,
                &actual,
                &mut substitution,
                LifetimeMode::Instantiate,
                0,
            ) {
                Ok(value) => value,
                Err(error) => {
                    self.lifetime_error(span, error);
                    return Err(());
                }
            };
            aligned_parameters.push(aligned);
        }
        // Only an explicitly unsafe direct-reference result may choose a
        // region independently of its arguments. Existing argument-derived
        // bindings always win; this does not lengthen an ordinary caller loan.
        if let (Some(selected), Type::Reference { lifetime, .. }) = (unsafe_reference_result, &result) {
            match lifetime {
                Lifetime::Generic(index) => { substitution.generics.entry(*index).or_insert(selected); }
                Lifetime::Bound { depth: 0, index } => { substitution.bounds.entry(*index).or_insert(selected); }
                _ => {}
            }
        }
        let result = match substitute_call_lifetimes(result, &substitution, 0) {
            Ok(value) => value,
            Err(error) => {
                self.lifetime_error(span, error);
                return Err(());
            }
        };
        let effects = match substitute_call_effects(effects, &substitution, 0) {
            Ok(value) => value,
            Err(error) => {
                self.lifetime_error(span, error);
                return Err(());
            }
        };
        Ok((aligned_parameters, result, effects, substitution))
    }

    fn lifetime_error(&mut self, span: Span, error: LifetimeError) {
        let (code, message) = match error {
            LifetimeError::UnsatisfiedOutlives => (
                "G5017",
                "reference lifetime does not satisfy the required outlives constraint",
            ),
            LifetimeError::UnresolvedGeneric => (
                "G5018",
                "call result retains an unsatisfied lifetime substitution",
            ),
            LifetimeError::EscapingBound => (
                "G5019",
                "higher-ranked bound lifetime escapes its callable invocation",
            ),
        };
        self.error(span, code, message);
        self.recovered = true;
    }
    fn core_pattern(
        &mut self,
        decision: PatternDecision,
        subject: Type,
        span: Span,
        bindings: Option<&std::collections::BTreeMap<crate::pattern::BinderKey, String>>,
    ) -> CorePattern {
        match decision {
            PatternDecision::Any => CorePattern::Any,
            PatternDecision::Bind(key) => bindings
                .and_then(|bindings| bindings.get(&key))
                .cloned()
                .map(|name| CorePattern::Bind { name })
                // `is` and handler dispatch both preserve binder identity in
                // Core.  A test's binders remain inside its refinement
                // environment until a branch opens their lexical scope.
                .unwrap_or(CorePattern::Any),
            PatternDecision::Literal(value) => CorePattern::Literal(value),
            PatternDecision::Tuple(values) => {
                let Type::Tuple(types) = subject else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision lost its tuple subject type",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                if values.len() != types.len() {
                    self.error(span, "G4146", "pattern decision has an invalid tuple arity");
                    self.recovered = true;
                    return CorePattern::Error;
                }
                CorePattern::Tuple(
                    values
                        .into_iter()
                        .zip(types)
                        .map(|(value, ty)| self.core_pattern(value, ty, span, bindings))
                        .collect(),
                )
            }
            PatternDecision::Array(values) => {
                let Type::Array(element) = subject else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision lost its array subject type",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                CorePattern::Array {
                    element: (*element).clone(),
                    elements: values
                        .into_iter()
                        .map(|value| self.core_pattern(value, (*element).clone(), span, bindings))
                        .collect(),
                }
            }
            PatternDecision::Record { definition, fields } => {
                let Some((actual, arguments)) = nominal_parts(&subject) else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision lost its nominal subject type",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                let Some(layout) = self
                    .signatures
                    .instantiate_struct_fields_generic(actual, &arguments)
                    .ok()
                else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision names an invalid record layout",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                if actual != definition {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision record identity does not match its subject",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                }
                let mut fields = fields
                    .into_iter()
                    .map(|(index, pattern)| {
                        let Some(field) = layout.get(index as usize) else {
                            self.error(
                                span,
                                "G4146",
                                "pattern decision selects an invalid record field",
                            );
                            self.recovered = true;
                            return CorePatternField {
                                index,
                                ty: Type::Error,
                                pattern: CorePattern::Error,
                            };
                        };
                        CorePatternField {
                            index,
                            ty: field.ty.clone(),
                            pattern: self.core_pattern(pattern, field.ty.clone(), span, bindings),
                        }
                    })
                    .collect::<Vec<_>>();
                fields.sort_by_key(|field| field.index);
                CorePattern::Record {
                    definition,
                    field_types: layout.iter().map(|field| field.ty.clone()).collect(),
                    field_count: layout.len() as u32,
                    fields,
                }
            }
            PatternDecision::Enum {
                definition,
                variant,
                fields,
            } => {
                let Some((actual, arguments)) = nominal_parts(&subject) else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision lost its nominal subject type",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                let Some(layout) = self
                    .signatures
                    .instantiate_enum_fields_generic(actual, &arguments, variant)
                    .ok()
                else {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision names an invalid enum layout",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                };
                if actual != definition {
                    self.error(
                        span,
                        "G4146",
                        "pattern decision enum identity does not match its subject",
                    );
                    self.recovered = true;
                    return CorePattern::Error;
                }
                let mut fields = fields
                    .into_iter()
                    .map(|(index, pattern)| {
                        let Some(field) = layout.get(index as usize) else {
                            self.error(
                                span,
                                "G4146",
                                "pattern decision selects an invalid enum field",
                            );
                            self.recovered = true;
                            return CorePatternField {
                                index,
                                ty: Type::Error,
                                pattern: CorePattern::Error,
                            };
                        };
                        CorePatternField {
                            index,
                            ty: field.ty.clone(),
                            pattern: self.core_pattern(pattern, field.ty.clone(), span, bindings),
                        }
                    })
                    .collect::<Vec<_>>();
                fields.sort_by_key(|field| field.index);
                CorePattern::Enum {
                    definition,
                    variant,
                    field_types: layout.iter().map(|field| field.ty.clone()).collect(),
                    field_count: layout.len() as u32,
                    fields,
                }
            }
            PatternDecision::Error => CorePattern::Error,
        }
    }
    fn path(&mut self, path: Vec<String>, span: Span) -> CoreId {
        if path.len() == 1
            && let Some(ty) = self.locals.lookup(&path[0]).cloned()
        {
            if let Some(active) = self.active_resumption(&path[0]) {
                return self.alloc(
                    CoreKind::Resumption {
                        id: active.id,
                        name: path[0].clone(),
                    },
                    ty,
                    span,
                );
            }
            return self.alloc(CoreKind::Local(path[0].clone()), ty, span);
        }
        match self
            .index
            .resolve_path(DefinitionNamespace::Value, self.module, &path)
        {
            ResolutionState::Resolved(definition) => {
                let definition = self
                    .signatures
                    .value_alias_target(definition)
                    .unwrap_or(definition);
                match self
                    .signatures
                    .definitions
                    .get(&definition)
                    .and_then(callable)
                {
                    Some(signature) => {
                        let generic_kinds = signature.generic_kinds.clone();
                        // Every omitted generic receives a value in its native
                        // semantic domain.  In particular, an `EffectRow` slot
                        // gets a fresh row variable rather than `{}`: a nominal
                        // parameter such as `Token<e>` can then constrain it to
                        // the row carried by the call argument.  The old
                        // type-only instantiator silently fixed those slots to
                        // empty, rejecting valid implicit calls and losing the
                        // caller-owned row identity in Core.
                        let arguments = generic_kinds
                            .iter()
                            .enumerate()
                            .map(|kind| match kind {
                                (_, crate::GenericKind::Type) => {
                                    GenericArgument::Type(self.inference.fresh())
                                }
                                (_, crate::GenericKind::EffectRow) => {
                                    GenericArgument::EffectRow(self.inference.fresh_effects())
                                }
                                // Preserve declaration-region identity in the
                                // unopened callable contract. `call` opens it
                                // against the actual arguments after freezing
                                // reference provenance; replacing it with
                                // `Elided` here would make two distinct generic
                                // lifetimes indistinguishable before that proof.
                                (index, crate::GenericKind::Lifetime) => {
                                    GenericArgument::Lifetime(Lifetime::Generic(index as u32))
                                }
                                (_, crate::GenericKind::Const(kind)) => {
                                    self.inference.fresh_const(*kind)
                                }
                            })
                            .collect::<Vec<_>>();
                        let signature = self
                            .signatures
                            .instantiate_callable_generic(definition, &arguments)
                            .expect("fresh arguments match the callable generic contract");
                        let parameters = signature
                            .parameters
                            .into_iter()
                            .map(|parameter| self.normalize_concrete_type_projections(parameter))
                            .collect();
                        let result = self.normalize_concrete_type_projections(signature.result);
                        // A concrete associated effect-row projection is a
                        // selected callable contract, not deferred metadata.
                        // Retain symbolic projections under declaration
                        // binders, but normalize concrete rows before the
                        // function value reaches `call` and MIR. Otherwise
                        // source checking accepts a handler while VM-frame
                        // lowering cannot see the operation identity it must
                        // install.
                        let effects = self.normalize_concrete_effect_row(signature.effects);
                        self.alloc(
                            CoreKind::Function {
                                definition,
                                arguments,
                                host_import: self.signatures.host_imports.get(&definition).cloned(),
                            },
                            Type::Callable {
                                safety: signature.safety,
                                lifetime_binders: 0,
                                parameters,
                                result: Box::new(result),
                                effects,
                                // A named function value owns no lexical
                                // capture environment. Its callable body may
                                // run once per application, but the value
                                // itself is a reusable function reference;
                                // in particular it can satisfy an explicit
                                // `F: Use<[0,*]>` callback requirement.
                                invocation: crate::Quantity::UNRESTRICTED,
                            },
                            span,
                        )
                    }
                    None => match self.signatures.definitions.get(&definition) {
                        Some(ElaboratedHeader::Constant(Some(ty))) => self.alloc(
                            CoreKind::Constant {
                                definition,
                                arguments: vec![],
                            },
                            ty.clone(),
                            span,
                        ),
                        Some(ElaboratedHeader::Constant(None)) => {
                            self.fail(span, "G4102", "constant value has no frozen type")
                        }
                        Some(ElaboratedHeader::ValueInitializer {
                            generic_kinds,
                            ty: Some(_),
                        }) => {
                            let arguments = generic_kinds
                                .iter()
                                .enumerate()
                                .map(|(index, kind)| match kind {
                                    crate::GenericKind::Type => {
                                        GenericArgument::Type(self.inference.fresh())
                                    }
                                    crate::GenericKind::EffectRow => {
                                        GenericArgument::EffectRow(self.inference.fresh_effects())
                                    }
                                    crate::GenericKind::Lifetime => {
                                        GenericArgument::Lifetime(Lifetime::Generic(index as u32))
                                    }
                                    crate::GenericKind::Const(kind) => {
                                        self.inference.fresh_const(*kind)
                                    }
                                })
                                .collect::<Vec<_>>();
                            let ty = self
                                .signatures
                                .instantiate_value_initializer_generic(definition, &arguments)
                                .expect("fresh arguments match the frozen initializer contract");
                            self.alloc(
                                CoreKind::Constant {
                                    definition,
                                    arguments,
                                },
                                ty,
                                span,
                            )
                        }
                        Some(ElaboratedHeader::ValueInitializer { ty: None, .. }) => self.fail(
                            span,
                            "G4102",
                            "top-level value initializer has no frozen type",
                        ),
                        _ => self.fail(span, "G4102", "value does not have a callable signature"),
                    },
                }
            }
            ResolutionState::Ambiguous(_) => self.fail(span, "G4103", "ambiguous value reference"),
            ResolutionState::Inaccessible(_) => self.fail(
                span,
                "G4104",
                "value reference is private to another module",
            ),
            _ => self.fail(span, "G4104", "unresolved value reference"),
        }
    }

    /// Materialize a declaration-level lifetime-polymorphic named function as
    /// a first-class higher-ranked callable.  A function declaration owns
    /// generic lifetime slots, whereas a callable annotation owns lexical
    /// `for<'a>` binders.  They are the same universal contract only after we
    /// prove the declaration under fresh bound placeholders.  The executable
    /// instance itself uses `'static`: VM references erase regions, and this
    /// concrete instance is justified by the checked universal source
    /// contract rather than by treating `'static` as an HRTB coercion.
    fn named_hrtb_function_value(
        &mut self,
        path: Vec<String>,
        expected: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        let Type::Callable {
            safety,
            lifetime_binders,
            parameters: expected_parameters,
            result: expected_result,
            effects: expected_effects,
            invocation: expected_invocation,
        } = expected?
        else {
            return None;
        };
        if lifetime_binders == 0 {
            return None;
        }
        let ResolutionState::Resolved(definition) =
            self.index
                .resolve_path(DefinitionNamespace::Value, self.module, &path)
        else {
            return None;
        };
        let definition = self
            .signatures
            .value_alias_target(definition)
            .unwrap_or(definition);
        let Some(signature) = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)
        else {
            return None;
        };
        if signature.generic_kinds.len() != lifetime_binders as usize
            || !signature
                .generic_kinds
                .iter()
                .all(|kind| matches!(kind, crate::GenericKind::Lifetime))
        {
            return None;
        }

        let bound_arguments = (0..lifetime_binders)
            .map(|index| GenericArgument::Lifetime(Lifetime::Bound { depth: 0, index }))
            .collect::<Vec<_>>();
        let bound_signature = self
            .signatures
            .instantiate_callable_generic(definition, &bound_arguments)
            .ok()?;
        let bound_effects =
            self.normalize_concrete_hrtb_effect_row(bound_signature.effects, lifetime_binders);
        let expected_effects =
            self.normalize_concrete_hrtb_effect_row(expected_effects, lifetime_binders);
        let bound_callable = self.normalize_selectable_type_projections(Type::Callable {
            safety: bound_signature.safety,
            lifetime_binders,
            parameters: bound_signature.parameters,
            result: Box::new(bound_signature.result),
            effects: bound_effects,
            invocation: bound_signature.invocation,
        });
        let expected = self.normalize_selectable_type_projections(Type::Callable {
            safety,
            lifetime_binders,
            parameters: expected_parameters,
            result: expected_result,
            effects: expected_effects,
            invocation: expected_invocation,
        });
        if self.inference.unify(bound_callable, expected.clone()).is_err() {
            return None;
        }

        let arguments = (0..lifetime_binders)
            .map(|_| GenericArgument::Lifetime(Lifetime::Static))
            .collect::<Vec<_>>();
        Some(self.alloc(
            CoreKind::Function {
                definition,
                arguments,
                host_import: self.signatures.host_imports.get(&definition).cloned(),
            },
            expected,
            span,
        ))
    }

    /// Inherent applications keep owner arguments separate from method
    /// arguments. Unifying the actual owner with the declared impl head also
    /// enforces specialized heads, even for static functions with no receiver.
    fn inherent_path(
        &mut self,
        path: &[String],
        owner_arguments: &[crate::header::HeaderGenericArgument],
        method_arguments: &[crate::header::HeaderGenericArgument],
        span: Span,
    ) -> Option<CoreId> {
        let ResolutionState::Resolved(definition) =
            self.index
                .resolve_path(DefinitionNamespace::Value, self.module, path)
        else {
            return None;
        };
        let header = self.index.inherent_method(definition)?;
        let base = header.impl_generics as usize;
        let kinds = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)?
            .generic_kinds
            .clone();
        if method_arguments.len() > kinds.len() - base {
            return Some(self.fail(
                span,
                "G4184",
                "inherent function generic arguments do not match its method binders",
            ));
        }
        let mut arguments = self.inferred_method_generic_arguments(&kinds);
        let Some(explicit) = self.body_generic_arguments(
            method_arguments,
            &kinds[base..base + method_arguments.len()],
            span,
            "G4184",
            "inherent function generic arguments have the wrong kind",
        ) else {
            return Some(self.fail(span, "G4184", "invalid inherent function generic arguments"));
        };
        arguments[base..base + explicit.len()].clone_from_slice(&explicit);
        if !owner_arguments.is_empty() {
            let declared = self
                .signatures
                .instantiate_inherent_self_type(definition, &arguments)?;
            let Type::Nominal {
                definition: owner, ..
            } = &declared
            else {
                return Some(self.fail(span, "G4184", "inherent function has no nominal owner"));
            };
            let Some(provided) = self.nominal_arguments(*owner, owner_arguments, span) else {
                return Some(self.fail(
                    span,
                    "G4184",
                    "inherent owner generic arguments do not match its declaration",
                ));
            };
            let provided = Type::Nominal {
                definition: *owner,
                arguments: provided,
            };
            let declared = self.signatures.normalize_type_aliases(declared);
            let provided = self.signatures.normalize_type_aliases(provided);
            let mut lifetimes = CallLifetimeSubstitution::default();
            let declared = match align_lifetime_types(
                &declared,
                &provided,
                &mut lifetimes,
                LifetimeMode::Instantiate,
                0,
            ) {
                Ok(declared) => declared,
                Err(_) => {
                    return Some(self.fail(
                        span,
                        "G4184",
                        "owner lifetimes do not match the inherent impl head",
                    ));
                }
            };
            // Bind only the impl's region slots. Method lifetime arguments
            // already name caller regions and must not be reinterpreted as
            // impl-local binders merely because their numeric slots coincide.
            for (index, argument) in arguments[..base].iter_mut().enumerate() {
                if kinds[index] == crate::GenericKind::Lifetime
                    && let Some(lifetime) = lifetimes.generics.get(&(index as u32))
                {
                    *argument = GenericArgument::Lifetime(*lifetime);
                }
            }
            if self.inference.unify(declared, provided).is_err() {
                return Some(self.fail(
                    span,
                    "G4184",
                    "type arguments do not match the inherent impl head",
                ));
            }
        }
        let signature = match self
            .signatures
            .instantiate_callable_generic(definition, &arguments)
        {
            Ok(signature) => signature,
            Err(_) => {
                return Some(self.fail(span, "G4184", "invalid inherent callable substitution"));
            }
        };
        let parameters = signature
            .parameters
            .into_iter()
            .map(|ty| self.normalize_concrete_type_projections(ty))
            .collect();
        let result = self.normalize_concrete_type_projections(signature.result);
        let effects = self.normalize_concrete_effect_row(signature.effects);
        Some(self.alloc(
            CoreKind::Function {
                definition,
                arguments,
                host_import: None,
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters,
                result: Box::new(result),
                effects,
                invocation: signature.invocation,
            },
            span,
        ))
    }

    /// Resolve an explicitly applied direct callable.  Body syntax keeps the
    /// arguments source-kinded until this value lookup establishes the frozen
    /// callable contract; the resulting Core function retains precisely that
    /// caller-owned substitution for instance discovery and later lowering.
    fn generic_path(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        span: Span,
    ) -> CoreId {
        if matches!(path.as_slice(), [name] if name == "Available") {
            return self.fail(
                span,
                "G4188",
                "compiler-generated intrinsic `Available` evidence cannot be constructed by source code",
            );
        }
        if matches!(path.as_slice(), [name] if name == "Bindings") {
            return self.fail(
                span,
                "G4188",
                "compiler-generated intrinsic `Bindings` evidence cannot be constructed by source code",
            );
        }
        if path.len() == 1 && self.locals.lookup(&path[0]).is_some() {
            return self.fail(
                span,
                "G4184",
                "a local value cannot be explicitly generic-applied",
            );
        }
        let ResolutionState::Resolved(definition) =
            self.index
                .resolve_path(DefinitionNamespace::Value, self.module, &path)
        else {
            return self.fail(
                span,
                "G4184",
                "generic callable path is unresolved in the value namespace",
            );
        };
        let definition = self
            .signatures
            .value_alias_target(definition)
            .unwrap_or(definition);
        let Some(signature) = self
            .signatures
            .definitions
            .get(&definition)
            .and_then(callable)
        else {
            return self.fail(
                span,
                "G4184",
                "explicit generic arguments require a callable value",
            );
        };
        // Direct functions may specify a prefix of their type arguments and
        // infer the remaining types from arguments/result context. This is
        // declaration-driven, not special treatment of a library spelling.
        // Omitted lifetime/row/const slots still require explicit arguments.
        let kinds = signature.generic_kinds.clone();
        if source_arguments.len() > kinds.len()
            || kinds[source_arguments.len()..]
                .iter()
                .any(|kind| *kind != crate::GenericKind::Type)
        {
            return self.fail(
                span,
                "G4184",
                "callable generic arguments do not match its declaration",
            );
        }
        let Some(mut arguments) = self.body_generic_arguments(
            &source_arguments,
            &kinds[..source_arguments.len()],
            span,
            "G4184",
            "callable generic arguments do not match its declaration",
        ) else {
            return self.fail(
                span,
                "G4184",
                "callable generic arguments do not match its declaration",
            );
        };
        arguments.extend(
            kinds[source_arguments.len()..]
                .iter()
                .map(|_| GenericArgument::Type(self.inference.fresh())),
        );
        let signature = match self
            .signatures
            .instantiate_callable_generic(definition, &arguments)
        {
            Ok(signature) => signature,
            Err(_) => {
                return self.fail(
                    span,
                    "G4184",
                    "callable generic arguments do not satisfy its declaration contract",
                );
            }
        };
        let parameters = signature
            .parameters
            .into_iter()
            .map(|parameter| self.normalize_concrete_type_projections(parameter))
            .collect();
        let result = self.normalize_concrete_type_projections(signature.result);
        let effects = self.normalize_concrete_effect_row(signature.effects);
        self.alloc(
            CoreKind::Function {
                definition,
                arguments,
                host_import: self.signatures.host_imports.get(&definition).cloned(),
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters,
                result: Box::new(result),
                effects,
                invocation: signature.invocation,
            },
            span,
        )
    }
    fn active_resumption(&self, name: &str) -> Option<ActiveResumption> {
        let generation = self.locals.binding_generation(&name.to_owned())?;
        self.resumption_bindings
            .get(&(name.to_owned(), generation))
            .cloned()
    }
    fn resumption_identity(&self, id: CoreId) -> Option<ActiveResumption> {
        match &self.expressions[id.0 as usize].kind {
            CoreKind::Resumption { id, .. } => self
                .active_resumptions
                .iter()
                .rev()
                .find(|resumption| resumption.id == *id)
                .cloned(),
            CoreKind::Local(name) => self.active_resumption(name),
            _ => None,
        }
    }
    fn record_resumption_call(&mut self, id: CoreId) {
        let Some(identity) = self.resumption_identity(id) else {
            return;
        };
        for tracker in &mut self.resumption_use_trackers {
            if tracker.identity.id == identity.id {
                tracker.direct_uses = tracker.direct_uses.saturating_add(1);
            }
        }
    }
    /// Find a unique-reference use in the residual source region of the
    /// exact operation a handler is about to replay. Core is scope-resolved
    /// here, so this observes the real loan capability rather than a source
    /// spelling that happens to resemble a borrow.
    fn replay_residual_captures_unique_borrow(
        &self,
        root: CoreId,
        effect: &EffectInstance,
        operation: u32,
    ) -> bool {
        let mut pending = vec![root];
        let mut visited = std::collections::BTreeSet::new();
        let mut performances = vec![];
        let mut reachable = vec![];
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let expression = &self.expressions[id.0 as usize];
            if matches!(
                &expression.kind,
                CoreKind::Perform {
                    effect: performed_effect,
                    operation: performed_operation,
                    ..
                } if performed_effect == effect && *performed_operation == operation
            ) {
                performances.push(expression.span);
            }
            pending.extend(core_children(&expression.kind));
            reachable.push(id);
        }
        reachable.into_iter().any(|id| {
            let expression = &self.expressions[id.0 as usize];
            matches!(
                expression.ty,
                Type::Reference {
                    mutability: Mutability::Unique,
                    ..
                }
            ) && performances
                .iter()
                .any(|performance| expression.span.start >= performance.end)
        })
    }
    fn assignment_place(&mut self, id: ExprId, span: Span) -> CorePlace {
        let expression = self.body.expression(id);
        match &expression.kind {
            ExprKind::Path(path) => {
                let [name] = path.as_slice() else {
                    self.error(
                        span,
                        "G4137",
                        "top-level and qualified values are not assignable places",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                };
                let Some(ty) = self.locals.lookup(name).cloned() else {
                    self.error(
                        span,
                        "G4137",
                        "assignment destination is not a local binding",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                };
                CorePlace::Local {
                    name: name.clone(),
                    ty,
                }
            }
            ExprKind::Field { base, name } => {
                let base = self.assignment_place(*base, expression.span);
                let Type::Nominal {
                    definition,
                    arguments,
                } = base.ty()
                else {
                    self.error(span, "G4138", "assignment field requires a struct place");
                    self.recovered = true;
                    return CorePlace::Error;
                };
                let Some(fields) = self
                    .signatures
                    .instantiate_struct_fields_generic(definition, &arguments)
                    .ok()
                else {
                    self.error(
                        span,
                        "G4138",
                        "assignment field requires a visible struct place",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                };
                let field_count = fields.len() as u32;
                let Some((index, field)) = fields
                    .into_iter()
                    .enumerate()
                    .find(|(_, field)| field.name == *name)
                else {
                    self.error(span, "G4139", "struct does not declare the assigned field");
                    self.recovered = true;
                    return CorePlace::Error;
                };
                if !self.field_is_accessible(&field, span) {
                    self.error(
                        span,
                        "G4140",
                        "assignment accesses a private field outside its declaring source entry",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                }
                CorePlace::Field {
                    base: Box::new(base),
                    index: index as u32,
                    field_count,
                    ty: field.ty,
                }
            }
            ExprKind::Deref(reference) => {
                let reference = self.expression(*reference);
                let Type::Reference {
                    mutability,
                    referent,
                    ..
                } = self.expressions[reference.0 as usize].ty.clone()
                else {
                    self.error(
                        span,
                        "G4140",
                        "assignment through dereference requires a reference",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                };
                if !matches!(mutability, Mutability::Unique) || self.place_uses_shared_reference(reference) {
                    self.error(
                        span,
                        "G4141",
                        "assignment through a shared reference is not permitted",
                    );
                    self.recovered = true;
                    return CorePlace::Error;
                }
                CorePlace::Deref {
                    reference,
                    ty: *referent,
                    unique: true,
                }
            }
            _ => {
                self.error(
                    span,
                    "G4137",
                    "assignment destination is not an addressable local place",
                );
                self.recovered = true;
                CorePlace::Error
            }
        }
    }
    /// Resolve a nominal application's source arguments in declaration-slot
    /// order. Omitted arguments use inference only for type slots; the other
    /// kinds retain their own semantic form so a runtime-layout consumer can
    /// reject them explicitly instead of silently erasing identity.
    fn nominal_arguments(
        &mut self,
        definition: DefKey,
        source_arguments: &[crate::header::HeaderGenericArgument],
        span: Span,
    ) -> Option<Vec<GenericArgument>> {
        let kinds = self.index.type_generic_kinds(definition)?.to_vec();
        if !source_arguments.is_empty() {
            let arguments = self.complete_nominal_generic_arguments(
                definition,
                source_arguments,
                &kinds,
                span,
                "G4185",
                "nominal generic arguments do not match its declaration",
            )?;
            if arguments
                .iter()
                .zip(&kinds)
                .all(|(argument, kind)| generic_argument_matches_kind(argument, *kind))
            {
                return Some(arguments);
            }
            self.error(
                span,
                "G4185",
                "nominal generic argument has the wrong declared kind",
            );
            self.recovered = true;
            return None;
        }
        let defaults = self.index.type_generic_defaults(definition).unwrap_or(&[]);
        let mut arguments = Vec::with_capacity(kinds.len());
        for (index, kind) in kinds.into_iter().enumerate() {
            if let Some(default) = defaults.get(index).and_then(Option::as_ref) {
                arguments.push(instantiate_nominal_default(default, &arguments));
                continue;
            }
            arguments.push(match kind {
                crate::GenericKind::Type => GenericArgument::Type(self.inference.fresh()),
                crate::GenericKind::EffectRow => GenericArgument::EffectRow(EffectRow::empty()),
                crate::GenericKind::Lifetime => GenericArgument::Lifetime(self.inference.fresh_lifetime()),
                crate::GenericKind::Const(kind) => GenericArgument::ConstGeneric {
                    index: index as u32,
                    kind,
                },
            });
        }
        Some(arguments)
    }
    /// A replayed continuation may use an enclosing label in its clause
    /// *after* all resumed activations have returned. What is unsound is a
    /// transfer in the residual region itself: replaying that continuation
    /// would duplicate the lexical Leave edge. Distinguish the two by
    /// locating transfers after the selected performance, just as the unique
    /// borrow check locates duplicated loan uses.
    fn replay_residual_captures_label_transfer(
        &self,
        root: CoreId,
        effect: &EffectInstance,
        operation: u32,
    ) -> bool {
        let mut pending = vec![root];
        let mut visited = std::collections::BTreeSet::new();
        let mut performances = vec![];
        let mut reachable = vec![];
        while let Some(id) = pending.pop() {
            if !visited.insert(id) {
                continue;
            }
            let expression = &self.expressions[id.0 as usize];
            if matches!(
                &expression.kind,
                CoreKind::Perform {
                    effect: performed_effect,
                    operation: performed_operation,
                    ..
                } if performed_effect == effect && *performed_operation == operation
            ) {
                performances.push(expression.span);
            }
            pending.extend(core_children(&expression.kind));
            reachable.push(id);
        }
        reachable.into_iter().any(|id| {
            let expression = &self.expressions[id.0 as usize];
            matches!(expression.kind, CoreKind::Transfer { .. })
                && performances
                    .iter()
                    .any(|performance| expression.span.start >= performance.end)
        })
    }

    fn record(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        fields: Vec<(String, ExprId)>,
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        if let Some(value) = self.enum_record_constructor(
            path.clone(),
            source_arguments.clone(),
            fields.clone(),
            expected.clone(),
            span,
        ) {
            return value;
        }
        let definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Type, self.module, &path)
            {
                ResolutionState::Resolved(definition) => definition,
                ResolutionState::Ambiguous(_) => {
                    return self.fail(span, "G4120", "ambiguous record constructor type");
                }
                ResolutionState::Inaccessible(_) => {
                    return self.fail(span, "G4121", "record constructor type is private");
                }
                ResolutionState::Unresolved | ResolutionState::Recovered => {
                    return self.fail(span, "G4122", "unresolved record constructor type");
                }
            };
        let Some(arguments) = self.nominal_arguments(definition, &source_arguments, span) else {
            return self.fail(
                span,
                "G4123",
                "record generic arguments do not match its declaration",
            );
        };
        if let Some(expected) = expected
            && self.unify_rigid_lifetimes(expected, Type::Nominal { definition, arguments: arguments.clone() }, span).is_err() {
            return self.fail(span, "G4126", "record constructor does not match its contextual expected type");
        }
        let Some(layout) = self
            .signatures
            .instantiate_struct_fields_generic(definition, &arguments)
            .ok()
        else {
            return self.fail(
                span,
                "G4123",
                "record constructor requires type-valued generic arguments for its runtime layout",
            );
        };
        let mut supplied = std::collections::BTreeMap::new();
        for (name, value) in fields {
            if supplied.insert(name.clone(), value).is_some() {
                self.error(span, "G4124", "record field is supplied more than once");
                self.recovered = true;
            }
        }
        let mut values = Vec::with_capacity(layout.len());
        for field in layout {
            let Some(value) = supplied.remove(&field.name) else {
                self.error(span, "G4125", "record construction omits a required field");
                self.recovered = true;
                continue;
            };
            if !self.field_is_accessible(&field, span) {
                self.error(
                    span,
                    "G4140",
                    "record construction names a private field outside its declaring source entry",
                );
                self.recovered = true;
                continue;
            }
            // A generic nominal layout is instantiated at this constructor
            // boundary.  Its field may contain a now-concrete associated
            // projection, so normalize it before handing the expectation to
            // body inference or freezing it into Core/MIR.
            let field_ty = self.normalize_concrete_type_projections(field.ty);
            let value = self.expression_expected(value, Some(field_ty.clone()));
            let actual = self.expressions[value.0 as usize].ty.clone();
            if self.unify_rigid_lifetimes(field_ty, actual, span).is_err() {
                self.error(
                    span,
                    "G4126",
                    "record field does not match its declared type",
                );
                self.recovered = true;
            }
            values.push(value);
        }
        if !supplied.is_empty() {
            self.error(span, "G4127", "record construction names an unknown field");
            self.recovered = true;
        }
        let ty = Type::Nominal {
            definition,
            arguments,
        };
        let ty = self.strict_result(&values, ty);
        self.alloc(
            CoreKind::Record {
                definition,
                fields: values,
            },
            ty,
            span,
        )
    }
    fn empty_braced_nominal(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        span: Span,
    ) -> Option<CoreId> {
        if self.empty_enum_record_constructor(&path) {
            return self.enum_record_constructor(path, source_arguments, vec![], None, span);
        }
        self.empty_record_constructor(path, source_arguments, span)
    }
    fn empty_record_constructor(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        span: Span,
    ) -> Option<CoreId> {
        let ResolutionState::Resolved(definition) =
            self.index
                .resolve_path(DefinitionNamespace::Type, self.module, &path)
        else {
            return None;
        };
        let Some(ElaboratedHeader::Nominal {
            layout: crate::signature::ElaboratedNominalLayout::Struct(fields),
            ..
        }) = self.signatures.definitions.get(&definition)
        else {
            return None;
        };
        fields
            .is_empty()
            .then(|| self.record(path, source_arguments, vec![], None, span))
    }
    fn empty_enum_record_constructor(&self, path: &[String]) -> bool {
        let Some((variant, enum_path)) = path.split_last() else {
            return false;
        };
        let ResolutionState::Resolved(definition) =
            self.index
                .resolve_path(DefinitionNamespace::Type, self.module, enum_path)
        else {
            return false;
        };
        matches!(
            self.signatures.definitions.get(&definition),
            Some(ElaboratedHeader::Nominal {
                layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                ..
            }) if variants.iter().any(|candidate| {
                candidate.name == *variant
                    && matches!(
                        candidate.payload,
                        crate::signature::ElaboratedEnumVariantPayload::Struct(ref fields)
                            if fields.is_empty()
                    )
            })
        )
    }
    fn enum_record_constructor(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        supplied_fields: Vec<(String, ExprId)>,
        expected: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        let (variant_name, enum_path) = path.split_last()?;
        if enum_path.is_empty() {
            return None;
        }
        let definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Type, self.module, enum_path)
            {
                ResolutionState::Resolved(definition) => definition,
                _ => return None,
            };
        let arguments = self.nominal_arguments(definition, &source_arguments, span)?;
        if let Some(expected) = expected
            && self.unify_rigid_lifetimes(expected, Type::Nominal { definition, arguments: arguments.clone() }, span).is_err() {
            return Some(self.fail(span, "G4134", "enum record constructor does not match its contextual expected type"));
        }
        let (variant, layout) = self
            .signatures
            .instantiate_enum_record_variant_generic(definition, &arguments, variant_name)
            .ok()?;
        let mut supplied = std::collections::BTreeMap::new();
        for (name, value) in supplied_fields {
            if supplied.insert(name, value).is_some() {
                return Some(self.fail(
                    span,
                    "G4132",
                    "enum record field is supplied more than once",
                ));
            }
        }
        let mut fields = Vec::with_capacity(layout.len());
        for field in layout {
            let Some(value) = supplied.remove(&field.name) else {
                return Some(self.fail(
                    span,
                    "G4133",
                    "enum record construction omits a required field",
                ));
            };
            if !self.field_is_accessible(&field, span) {
                return Some(self.fail(
                    span,
                    "G4140",
                    "enum record construction names a private field outside its declaring source entry",
                ));
            }
            let value = self.expression_expected(value, Some(field.ty.clone()));
            let actual = self.expressions[value.0 as usize].ty.clone();
            if self.unify_rigid_lifetimes(field.ty, actual, span).is_err() {
                return Some(self.fail(
                    span,
                    "G4134",
                    "enum record field does not match its declared type",
                ));
            }
            fields.push(value);
        }
        if !supplied.is_empty() {
            return Some(self.fail(
                span,
                "G4135",
                "enum record construction names an unknown field",
            ));
        }
        let ty = self.strict_result(
            &fields,
            Type::Nominal {
                definition,
                arguments,
            },
        );
        Some(self.alloc(
            CoreKind::Enum {
                definition,
                variant,
                fields,
            },
            ty,
            span,
        ))
    }
    fn field(&mut self, base: ExprId, name: String, span: Span) -> CoreId {
        let base = self.expression(base);
        // Field syntax automatically projects through a reference, but keep
        // the explicit Core dereference so MIR can reborrow the selected
        // payload rather than materializing or moving the whole enum.
        let base = match self.expressions[base.0 as usize].ty.clone() {
            Type::Reference { referent, .. } => self.alloc(CoreKind::Deref(base), *referent, span),
            _ => base,
        };
        let base_ty = self.expressions[base.0 as usize].ty.clone();
        let Type::Nominal {
            definition,
            arguments,
        } = base_ty
        else {
            return self.fail(span, "G4128", "field projection requires a struct value");
        };
        let fields = self
            .signatures
            .instantiate_struct_fields_generic(definition, &arguments)
            .ok()
            .or_else(|| self.refined_enum_projection_fields(base, definition));
        let Some(fields) = fields else {
            return self.fail(
                span,
                "G4128",
                "field projection requires a struct value or a proven enum variant",
            );
        };
        let field_count = fields.len() as u32;
        let field = if let Ok(index) = name.parse::<usize>() {
            fields.get(index).cloned().map(|field| (index, field))
        } else {
            fields
                .into_iter()
                .enumerate()
                .find(|(_, field)| field.name == name)
        };
        let Some((index, field)) = field else {
            return self.fail(
                span,
                "G4129",
                "aggregate does not declare the requested field or payload index",
            );
        };
        if !self.field_is_accessible(&field, span) {
            return self.fail(
                span,
                "G4140",
                "field projection accesses a private field outside its declaring source entry",
            );
        }
        // Layout instantiation can turn an interface-owned projection into a
        // concrete goal. Normalize at the same field boundary as record
        // construction so Core and MIR never retain a projection whose
        // selected implementation is already known.
        let field_ty = self.normalize_concrete_type_projections(field.ty);
        self.alloc(
            CoreKind::Field {
                base,
                index: index as u32,
                field_count,
            },
            field_ty,
            span,
        )
    }

    /// `Drop` observes the complete initialized aggregate.  The hook cannot
    /// run after a field has been moved out, so safe source may only transfer
    /// such a value as a whole (or use a legal zero-use destruction path).
    fn type_has_custom_drop(&mut self, ty: &Type) -> bool {
        // A destructor is not a nominal declaration property: an impl with a
        // `where` clause applies only to the instantiations for which trait
        // selection proves that clause.  Match cleanup lowering's selected
        // evidence so an inapplicable generic `Drop` impl does not make an
        // otherwise ordinary aggregate spuriously opaque to partial moves.
        // Keep unknown selection conservative: moving a field would make a
        // subsequently selected destructor observe an incomplete aggregate.
        let assumptions = self.ambient_trait_solver_assumptions();
        !matches!(
            self.trait_query().solve_with_assumptions(
                TraitGoal {
                    relation: crate::ElaboratedTraitReference {
                        definition: crate::resolution::language_drop_trait_definition(),
                        arguments: Vec::new(),
                    },
                    subject: ty.clone(),
                },
                &assumptions,
            ),
            TraitAnswer::NoSolution | TraitAnswer::Refuted { .. }
        )
    }
    /// Return the payload layout of a selected enum variant only while the
    /// enclosing positive refinement proves that this exact Core place has
    /// that variant.  Generic enum alternatives can have incompatible field
    /// types, so a bare enum projection is never guessed from field ordinal.
    fn refined_enum_projection_fields(
        &self,
        base: CoreId,
        definition: DefKey,
    ) -> Option<Vec<crate::signature::NominalField>> {
        let base_place = self.expression_place(base)?;
        self.active_refinement_patterns
            .iter()
            .rev()
            .find_map(|(subject, pattern)| {
                if !self.same_core_place_shape(subject, &base_place) {
                    return None;
                }
                let CorePattern::Enum {
                    definition: selected,
                    variant,
                    field_types,
                    ..
                } = pattern
                else {
                    return None;
                };
                if *selected != definition {
                    return None;
                }
                let Some(ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                    ..
                }) = self.signatures.definitions.get(&definition)
                else {
                    return None;
                };
                let payload = &variants.get(*variant as usize)?.payload;
                Some(
                    field_types
                        .iter()
                        .enumerate()
                        .map(|(index, ty)| {
                            let declared = match payload {
                                crate::signature::ElaboratedEnumVariantPayload::Struct(fields) => {
                                    fields.get(index)
                                }
                                _ => None,
                            };
                            crate::signature::NominalField {
                                name: declared
                                    .map(|field| field.name.clone())
                                    .unwrap_or_else(|| index.to_string()),
                                ty: ty.clone(),
                                private_authority: declared
                                    .and_then(|field| field.private_authority),
                            }
                        })
                        .collect(),
                )
            })
    }

    /// Convert a stable value projection into its assignable place form. This
    /// is used only for lexical refinement facts; temporaries deliberately do
    /// not acquire a mutable post-state identity.
    fn expression_place(&self, id: CoreId) -> Option<CorePlace> {
        let expression = self.expressions.get(id.0 as usize)?;
        match &expression.kind {
            CoreKind::Local(name) => Some(CorePlace::Local {
                name: name.clone(),
                ty: expression.ty.clone(),
            }),
            CoreKind::Deref(reference) => {
                let Type::Reference { mutability, .. } =
                    &self.expressions.get(reference.0 as usize)?.ty
                else {
                    return None;
                };
                Some(CorePlace::Deref {
                    reference: *reference,
                    ty: expression.ty.clone(),
                    unique: matches!(mutability, Mutability::Unique),
                })
            }
            CoreKind::Field {
                base,
                index,
                field_count,
            } => Some(CorePlace::Field {
                base: Box::new(self.expression_place(*base)?),
                index: *index,
                field_count: *field_count,
                ty: expression.ty.clone(),
            }),
            _ => None,
        }
    }

    fn same_core_place_shape(&self, left: &CorePlace, right: &CorePlace) -> bool {
        match (left, right) {
            (CorePlace::Local { name: left, .. }, CorePlace::Local { name: right, .. }) => {
                left == right
            }
            (
                CorePlace::Deref {
                    reference: left, ..
                },
                CorePlace::Deref {
                    reference: right, ..
                },
            ) => same_core_place_shape(&self.expressions, *left, *right),
            (
                CorePlace::Field {
                    base: left_base,
                    index: left_index,
                    ..
                },
                CorePlace::Field {
                    base: right_base,
                    index: right_index,
                    ..
                },
            ) => left_index == right_index && self.same_core_place_shape(left_base, right_base),
            _ => false,
        }
    }

    /// A direct enum constructor assignment establishes a stronger fact than
    /// any preceding `is` test for the same place. Keeping that replacement
    /// local to the active lexical refinement scope lets safe library code
    /// initialize an empty `Option` and immediately borrow its new payload.
    fn record_assigned_enum_refinement(&mut self, assignment: CoreId) {
        let CoreKind::Assign { place, value } = self.expressions[assignment.0 as usize].kind.clone() else {
            return;
        };
        let previous = std::mem::take(&mut self.active_refinement_patterns);
        self.active_refinement_patterns = previous
            .into_iter()
            .filter(|(subject, _)| !self.same_core_place_shape(subject, &place))
            .collect();
        let CoreKind::Enum {
            definition,
            variant,
            fields,
        } = self.expressions[value.0 as usize].kind.clone()
        else {
            return;
        };
        let field_types = fields
            .iter()
            .map(|field| self.expressions[field.0 as usize].ty.clone())
            .collect::<Vec<_>>();
        let pattern = CorePattern::Enum {
            definition,
            variant,
            field_count: field_types.len() as u32,
            fields: field_types
                .iter()
                .enumerate()
                .map(|(index, ty)| CorePatternField {
                    index: index as u32,
                    ty: ty.clone(),
                    pattern: CorePattern::Any,
                })
                .collect(),
            field_types,
        };
        self.active_refinement_patterns.push((place, pattern));
    }
    /// A negated enum test proves a payload layout only when exactly one
    /// alternate variant remains.  This is the source-level dual of a
    /// positive refinement; it is intentionally unavailable for larger
    /// enums, where a negative test leaves multiple incompatible layouts.
    fn complementary_enum_refinement(
        &self,
        subject: CoreId,
        selected: &CorePattern,
    ) -> Option<CorePattern> {
        let CorePattern::Enum {
            definition,
            variant,
            ..
        } = selected
        else {
            return None;
        };
        let Type::Nominal {
            definition: subject_definition,
            arguments,
        } = &self.expressions[subject.0 as usize].ty
        else {
            return None;
        };
        if subject_definition != definition {
            return None;
        }
        let ElaboratedHeader::Nominal {
            layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
            ..
        } = self.signatures.definitions.get(definition)?
        else {
            return None;
        };
        if variants.len() != 2 {
            return None;
        }
        let (other_index, _) = variants
            .iter()
            .enumerate()
            .find(|(index, _)| *index as u32 != *variant)?;
        // A complement can be a record variant too. The constructor-specific
        // tuple API rejects that layout before its field authority can be
        // checked by ordinary projection elaboration.
        let field_types = self
            .signatures
            .instantiate_enum_fields_generic(*definition, arguments, other_index as u32)
            .ok()?
            .into_iter()
            .map(|field| field.ty)
            .collect::<Vec<_>>();
        Some(CorePattern::Enum {
            definition: *definition,
            variant: other_index as u32,
            field_count: field_types.len() as u32,
            fields: field_types
                .iter()
                .enumerate()
                .map(|(index, ty)| CorePatternField {
                    index: index as u32,
                    ty: ty.clone(),
                    pattern: CorePattern::Any,
                })
                .collect(),
            field_types,
        })
    }
    fn enum_constructor(
        &mut self,
        path: Vec<String>,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        supplied: Vec<ExprId>,
        expected: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        if let ResolutionState::Resolved(alias) = self
            .index
            .resolve_path(DefinitionNamespace::Value, self.module, &path)
            && let Some((definition, variant_name)) =
                self.signatures.value_alias_enum_constructor(alias)
        {
            return self.enum_constructor_variant(
                definition,
                variant_name.to_owned(),
                source_arguments,
                supplied,
                expected,
                span,
            );
        }
        let (variant_name, enum_path) = path.split_last()?;
        if enum_path.is_empty() {
            return None;
        }
        let definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Type, self.module, enum_path)
            {
                ResolutionState::Resolved(definition) => definition,
                _ => return None,
            };
        // A qualified value such as `Slice::len` shares the surface syntax
        // with an enum constructor.  Only an actual enum may take the
        // constructor path; otherwise preserve the ordinary value lookup so
        // source-defined associated library bindings remain callable in a
        // contextual-result position.
        if !matches!(
            self.signatures.definitions.get(&definition),
            Some(ElaboratedHeader::Nominal {
                layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                ..
            }) if variants.iter().any(|variant| variant.name == *variant_name)
        ) {
            return None;
        }
        self.enum_constructor_variant(
            definition,
            variant_name.clone(),
            source_arguments,
            supplied,
            expected,
            span,
        )
    }

    fn enum_constructor_variant(
        &mut self,
        definition: DefKey,
        variant_name: String,
        source_arguments: Vec<crate::header::HeaderGenericArgument>,
        supplied: Vec<ExprId>,
        expected: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        let arguments = self.nominal_arguments(definition, &source_arguments, span)?;
        let nominal = Type::Nominal {
            definition,
            arguments: arguments.clone(),
        };
        if let Some(expected) = expected
            && self.inference.unify(nominal.clone(), expected).is_err()
        {
            return Some(self.fail(
                span,
                "G4131",
                "enum constructor result does not match its contextual expected type",
            ));
        }
        // Contextual result evidence may have solved an omitted nominal type
        // argument (for example `Option::Some(7)` under `Option<u8>`).
        // Reify that substitution before elaborating payloads, otherwise the
        // literal only sees the stale inference variable and falls back to
        // the default integer type.
        let nominal = self.inference.zonk(nominal.clone()).unwrap_or(nominal);
        let Type::Nominal { arguments, .. } = &nominal else {
            return Some(self.fail(
                span,
                "G4131",
                "enum constructor lost its nominal result type",
            ));
        };
        let (variant, fields) = self
            .signatures
            .instantiate_enum_variant_generic(definition, arguments, &variant_name)
            .ok()?;
        if fields.len() != supplied.len() {
            return Some(self.fail(
                span,
                "G4130",
                "enum constructor argument count does not match its variant payload",
            ));
        }
        let values = supplied
            .into_iter()
            .zip(fields)
            .map(|(value, expected)| {
                let value = self.expression_expected(value, Some(expected.clone()));
                let actual = self.expressions[value.0 as usize].ty.clone();
                if self.unify_rigid_lifetimes(expected, actual, span).is_err() {
                    self.error(
                        span,
                        "G4131",
                        "enum payload does not match its declared type",
                    );
                    self.recovered = true;
                }
                value
            })
            .collect::<Vec<_>>();
        let ty = self.strict_result(&values, nominal);
        Some(self.alloc(
            CoreKind::Enum {
                definition,
                variant,
                fields: values,
            },
            ty,
            span,
        ))
    }
    fn prefix(&mut self, operator: String, value: ExprId, span: Span) -> CoreId {
        if self.fixities.prefix(&operator).is_none() {
            return self.fail(span, "G4111", "operator has no unambiguous visible prefix fixity declaration");
        }
        self.grouped_operator(GroupedOperator::Apply { name: operator, operands: vec![GroupedOperator::Operand(value)] }, None, span)
    }

    /// Lower a source-declared operator through the same identity-carrying
    /// trait-method representation as an explicitly-qualified trait call.
    /// Every spelling, including scalar arithmetic, is selected from traits
    /// actually in lexical scope and carries implementation identity to MIR.
    fn operator_trait_call(&mut self, operator: String, values: Vec<CoreId>, span: Span) -> CoreId {
        let Some(receiver) = values.first().copied() else {
            return self.fail(span, "G4117", "operator has no receiver operand");
        };
        let subject = self.zonk_type(self.expressions[receiver.0 as usize].ty.clone(), span);
        let mut selected = Vec::new();
        let mut solver_ambiguous = false;
        let mut solver_overflow = false;
        let mut refuted = false;
        for definition in self
            .index
            .visible_definitions(DefinitionNamespace::Trait, self.module)
        {
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.signatures.definitions.get(&definition)
            else {
                continue;
            };
            if !trait_header.methods.contains_key(&operator) {
                continue;
            }
            // An operator has no source slot for `Trait<T, Effects, 'a>`
            // arguments. Derive them from receiver patterns in the frozen
            // impl set, then keep the normal solver as the single selector of
            // implementation evidence.
            for relation in self
                .trait_query()
                .relations_for_subject(definition, &subject)
            {
                let Some(method_generic_kinds) = self
                    .trait_query()
                    .method_generic_kinds(&relation, &operator)
                else {
                    continue;
                };
                let method_arguments =
                    self.inferred_method_generic_arguments(&method_generic_kinds);
                let trait_arguments = relation.arguments.clone();
                match self.trait_query().select_method(
                    TraitGoal {
                        relation,
                        subject: subject.clone(),
                    },
                    &operator,
                    &method_arguments,
                ) {
                    TraitMethodAnswer::Selected {
                        evidence,
                        method,
                        signature,
                    } if signature.parameters.len() == values.len() => selected.push((
                        evidence,
                        method,
                        trait_arguments,
                        method_arguments,
                        signature,
                    )),
                    TraitMethodAnswer::Ambiguous => solver_ambiguous = true,
                    TraitMethodAnswer::Overflow => solver_overflow = true,
                    TraitMethodAnswer::Refuted { .. } => refuted = true,
                    TraitMethodAnswer::NoSolution
                    | TraitMethodAnswer::Selected { .. }
                    | TraitMethodAnswer::MissingMethod { .. }
                    | TraitMethodAnswer::MethodArity { .. } => {}
                }
            }
        }
        // A generic declaration may promise the operator through an ambient
        // where-bound (`T: Less`) before any concrete implementation can be
        // selected.  Its method contract is still a declaration fact, so
        // type-check against that now and retain a deferred selection request
        // for instance materialization.  Concrete candidates above always
        // win: lexical evidence must not displace an already-selected impl.
        if selected.is_empty() {
            let visible_traits = self
                .index
                .visible_definitions(DefinitionNamespace::Trait, self.module)
                .into_iter()
                .collect::<std::collections::BTreeSet<_>>();
            let mut deferred = Vec::new();
            for goal in self.ambient_trait_solver_assumptions() {
                if goal.subject != subject || !visible_traits.contains(&goal.relation.definition) {
                    continue;
                }
                let Some(method_generic_kinds) = self
                    .trait_query()
                    .method_generic_kinds(&goal.relation, &operator)
                else {
                    continue;
                };
                let method_arguments =
                    self.inferred_method_generic_arguments(&method_generic_kinds);
                let Some(signature) = self.trait_query().declared_method_signature(
                    goal.clone(),
                    &operator,
                    &method_arguments,
                ) else {
                    continue;
                };
                if signature.parameters.len() != values.len() { continue; }
                deferred.push((
                    DeferredTraitMethod {
                        relation: goal.relation.clone(),
                        subject: goal.subject.clone(),
                        name: operator.clone(),
                    },
                    goal.relation.arguments,
                    method_arguments,
                    signature,
                ));
            }
            match deferred.len() {
                1 => {
                    let (deferred, trait_arguments, method_arguments, signature) =
                        deferred.pop().expect("one deferred operator method");
                    let placeholder = Self::deferred_trait_method_placeholder(&deferred);
                    let callee = self.alloc(
                        CoreKind::TraitMethod {
                            evidence: placeholder,
                            method: placeholder,
                            trait_arguments,
                            method_arguments,
                            deferred: Some(deferred),
                        },
                        Type::Callable {
                            safety: signature.safety,
                            lifetime_binders: 0,
                            parameters: signature.parameters.clone(),
                            result: Box::new(signature.result.clone()),
                            effects: signature.effects.clone(),
                            invocation: signature.invocation,
                        },
                        span,
                    );
                    let call = self.call(callee, values, span);
                    self.check_callable_contract_bounds(signature, None, span);
                    return call;
                }
                2.. => {
                    return self.fail(
                        span,
                        "G4117",
                        "operator trait implementation is ambiguous",
                    );
                }
                0 => {}
            }
        }
        let (evidence, method, trait_arguments, method_arguments, signature) = match selected.len()
        {
            1 => selected.pop().expect("one selected operator method"),
            0 if solver_overflow => {
                return self.fail(
                    span,
                    "G4117",
                    "operator trait selection exceeded the solver limit",
                );
            }
            0 if solver_ambiguous => {
                return self.fail(span, "G4117", "operator trait implementation is ambiguous");
            }
            0 if refuted => {
                return self.fail(
                    span,
                    "G4117",
                    "operator trait implementation is refuted by a negative implementation",
                );
            }
            0 => return self.fail(span, "G4117", "operator has incompatible operand type"),
            _ => return self.fail(span, "G4117", "operator trait implementation is ambiguous"),
        };
        let callee = self.alloc(
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred: None,
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters: signature.parameters.clone(),
                result: Box::new(signature.result.clone()),
                effects: signature.effects.clone(),
                invocation: signature.invocation,
            },
            span,
        );
        let call = self.call(callee, values, span);
        self.check_callable_contract_bounds(*signature, None, span);
        call
    }

    fn deferred_trait_method_placeholder(deferred: &DeferredTraitMethod) -> DefKey {
        let arguments = canonical_generic_arguments_encoding(&deferred.relation.arguments);
        let subject = canonical_type_encoding(&deferred.subject);
        DefKey(Digest::of_parts([
            b"grandiose-stage0-deferred-trait-method-v1".as_slice(),
            deferred.relation.definition.0.as_bytes().as_slice(),
            arguments.as_slice(),
            subject.as_slice(),
            deferred.name.as_bytes(),
        ]))
    }
    /// Recover the concrete callable shape promised by an intrinsic `Fn`
    /// bound on one parameter of a direct generic call.  The ordinary
    /// parameter list only carries the fresh variable chosen for `F`; that
    /// is insufficient to elaborate a contextual `{ ... }` argument, whose
    /// body needs its zero-argument callable result contract before it can be
    /// typed.  The declaration's already-instantiated bound and associated
    /// `Output`/`Effects` equalities are the authoritative contract.
    fn direct_bound_callable_contract(&self, callee: CoreId, parameter: &Type) -> Option<Type> {
        let CoreKind::Function {
            definition,
            arguments,
            ..
        } = &self.expressions[callee.0 as usize].kind
        else {
            return None;
        };
        let signature = self
            .signatures
            .instantiate_callable_generic(*definition, arguments)
            .ok()?;
        let relation = signature
            .where_bounds
            .iter()
            .find_map(|(subject, relation)| {
                (subject == parameter && crate::is_intrinsic_callable_trait(relation))
                    .then_some(relation)
            })?;
        let parameters = match relation.arguments.as_slice() {
            [GenericArgument::Type(Type::Tuple(parameters))] => parameters.clone(),
            [GenericArgument::Type(Type::Unit)] => vec![],
            _ => return None,
        };
        let result = signature
            .where_associated_type_bindings
            .iter()
            .find_map(|binding| {
                (binding.subject == *parameter
                    && binding.relation == *relation
                    && binding.name == "Output"
                    && binding.item_arguments.is_empty())
                .then(|| binding.value.clone())
            })?;
        let effects = signature
            .where_associated_effect_bindings
            .iter()
            .find_map(|binding| {
                (binding.subject == *parameter
                    && binding.relation == *relation
                    && binding.name == "Effects"
                    && binding.item_arguments.is_empty())
                .then(|| binding.value.clone())
            })
            .unwrap_or_else(EffectRow::empty);
        // A contextual callback is a concrete value for the declaration's
        // `F`.  Preserve any explicit `F: Use<Q>` contract on that value so
        // a closure captured for a zero-use forwarding callback carries the
        // same quantitative proof rather than the parser's default `once`.
        let invocation = signature
            .where_bounds
            .iter()
            .find_map(|(subject, relation)| {
                (subject == parameter
                    && relation.definition == crate::resolution::language_use_trait_definition())
                .then(|| match relation.arguments.as_slice() {
                    [GenericArgument::ConstQuantity(quantity)] => Some(*quantity),
                    _ => None,
                })
                .flatten()
            })
            .unwrap_or(crate::Quantity::ONCE);
        Some(Type::Callable {
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters,
            result: Box::new(result),
            effects,
            invocation,
        })
    }

    fn call(&mut self, callee: CoreId, arguments: Vec<CoreId>, span: Span) -> CoreId {
        self.call_with_expected(callee, arguments, span, None)
    }

    fn call_with_expected(&mut self, callee: CoreId, arguments: Vec<CoreId>, span: Span, expected: Option<&Type>) -> CoreId {
        let callable = self.expressions[callee.0 as usize].ty.clone();
        let callable = match callable {
            callable @ Type::Callable { .. } => callable,
            value => match self.callable_contract_from_ambient_fn_bound(&value) {
                Some(callable) => callable,
                None => return self.fail(span, "G4105", "called expression is not callable"),
            },
        };
        let Type::Callable {
            safety,
            parameters,
            result,
            effects,
            ..
        } = callable
        else {
            return self.fail(span, "G4105", "called expression is not callable");
        };
        if safety == crate::Safety::Unsafe && !self.unsafe_context {
            return self.fail(
                span,
                "G4201",
                "unsafe callable invocation requires an explicit `unsafe` block",
            );
        }
        if parameters.len() != arguments.len() {
            return self.fail(
                span,
                "G4106",
                "call argument count does not match callable signature",
            );
        }
        // Preserve the declaration-owned lifetime relation before opening the
        // callable into caller-local (usually elided) regions.  Two distinct
        // generic or higher-ranked regions can legitimately both become
        // `Elided` at this boundary; deriving provenance afterwards would
        // make a precise result look ambiguous or, worse, pick a wrong loan.
        let mut reference_contract =
            callable_reference_origin_from_contract(self.signatures, &parameters, &result);
        let unsafe_reference_result = if safety == crate::Safety::Unsafe
            && matches!(reference_contract, CallReferenceOrigin::Opaque)
        {
            reference_contract = CallReferenceOrigin::Unsafe;
            if matches!(result.as_ref(), Type::Reference { .. }) {
                Some(match expected { Some(Type::Reference { lifetime, .. }) => *lifetime, _ => Lifetime::Elided })
            } else { None }
        } else { None };
        let Ok((parameters, result, effects, lifetime_substitution)) =
            self.instantiate_call_lifetimes(parameters, *result, effects, &arguments, span, unsafe_reference_result)
        else {
            return self.fail(
                span,
                "G5017",
                "call cannot satisfy its reference lifetime contract",
            );
        };
        // A named callee lifetime is part of the callee's frozen generic
        // application as well as its parameter/result contract.  Preserve
        // the region inferred from the actual argument in that application;
        // otherwise an ordinary call such as `HashMap::get(&map, &key)`
        // retains a synthetic `Lifetime::Generic(0)` after its result has
        // already become `&'elided V`. Instance discovery then sees a false
        // non-concrete substitution and links the generic template instead
        // of its executable specialization.
        // A selected trait method carries its own method application too.
        // Leaving that application in declaration-region coordinates has
        // the same failure: its body and nested generic calls cannot be
        // materialized even though the invocation's borrow contract passed.
        // Trait relation arguments remain the solver-selected identity;
        // only the invoked method's arguments are opened here.
        let callee_arguments = match &mut self.expressions[callee.0 as usize].kind {
            CoreKind::Function { arguments, .. } => Some(arguments),
            CoreKind::TraitMethod { method_arguments, .. } => Some(method_arguments),
            _ => None,
        };
        if let Some(arguments) = callee_arguments {
            for argument in arguments {
                match substitute_call_generic_argument(
                    argument.clone(),
                    &lifetime_substitution,
                    0,
                ) {
                    Ok(substituted) => *argument = substituted,
                    Err(error) => {
                        self.lifetime_error(span, error);
                        return self.fail(
                            span,
                            "G5017",
                            "call cannot satisfy its reference lifetime contract",
                        );
                    }
                }
            }
        }
        for (parameter, argument) in parameters.into_iter().zip(&arguments) {
            let raw_actual = self.expressions[argument.0 as usize].ty.clone();
            let actual = Self::weaken_nested_callable_invocations(
                &parameter,
                self.inference.zonk(raw_actual.clone()).unwrap_or(raw_actual),
            );
            self.expressions[argument.0 as usize].ty = actual.clone();
            // A capture-free named function is duplicable, but it can still
            // be supplied to an ordinary one-shot callable parameter: the
            // parameter promises at most/at least the uses performed by this
            // call site, while the function reference permits a superset.
            // Keep the parameter's invocation contract for the structural
            // unification below so callable argument/result variance and
            // lifetime checking retain their existing direction.
            let actual = match (&parameter, actual) {
                (
                    Type::Callable { invocation: required, .. },
                    Type::Callable {
                        safety,
                        lifetime_binders,
                        parameters,
                        result,
                        effects,
                        invocation: provided,
                    },
                ) if provided.contains(*required) => Type::Callable {
                    safety,
                    lifetime_binders,
                    parameters,
                    result,
                    effects,
                    invocation: *required,
                },
                (_, actual) => actual,
            };
            // Do not bypass unification while either side still carries an
            // inference variable.  In particular, generic record fields can
            // contain callable contracts whose concrete argument/result types
            // are solved by this call.  The compatibility relation below is
            // a check for already-realized callable values, not a substitute
            // for constraint propagation.
            if !type_contains_inference(&parameter)
                && !type_contains_inference(&actual)
                && callable_argument_accepts(&parameter, &actual)
            {
                continue;
            }
            if self.inference.unify(parameter.clone(), actual.clone()).is_err() {
                let callable_lifetime_mismatch = matches!(
                    (&parameter, &actual),
                    (Type::Callable { .. }, Type::Callable { .. })
                );
                self.error(
                    span,
                    if callable_lifetime_mismatch { "G5017" } else { "G4107" },
                    if callable_lifetime_mismatch {
                        "callable argument does not satisfy its reference lifetime contract"
                    } else {
                        "call argument type does not match parameter"
                    },
                );
                self.recovered = true;
            }
        }
        // Value arguments do not necessarily determine every declaration
        // generic.  A recursive generic function can carry (for example) a
        // label payload `B` and callback row `e` solely in its where-clause:
        // `L: Label<B>, F: Fn<..., Effects = e>`.  When the same lexical
        // evidence is in scope, its associated contracts are the precise
        // source of those substitutions.  Leaving the fresh slots unresolved
        // would reject a well-typed recursive forwarding call at sealing.
        self.infer_direct_call_contract_from_ambient_bounds(callee, &arguments);
        // Arguments may have just fixed a generic return type. Publish that
        // concrete result to the enclosing expression now: otherwise a
        // subsequent scalar operator observes a stale inference variable and
        // incorrectly falls through to trait selection.
        let result = self.inference.zonk(result.clone()).unwrap_or(result);
        let strict_operands = std::iter::once(callee)
            .chain(arguments.iter().copied())
            .collect::<Vec<_>>();
        // A nonreturning callee is still entered and must satisfy its full
        // effect/evidence contract. Only divergence while evaluating the
        // callee or an argument makes the invocation itself unreachable.
        let reaches_call = strict_operands.iter()
            .all(|value| self.expressions[value.0 as usize].ty != Type::Never);
        let result = self.strict_result(&strict_operands, result);
        if reaches_call {
            self.check_effects(&effects, span);
            self.check_call_where_bounds(callee, &arguments, span);
        }
        let reference_shape = call_reference_shape(self.signatures, &result, &reference_contract);
        self.alloc(
            CoreKind::Call {
                callee,
                arguments,
                reference_contract: reference_contract.clone(),
                reference_origin: reference_contract,
                reference_shape,
            },
            result,
            span,
        )
    }

    /// Consume the compiler-issued witness for an unselected owned execution
    /// environment.  This is intentionally an elaborator intrinsic rather
    /// than a source function: `Available` has no runtime representation and
    /// releasing it is legal only when the environment is publicly affine:
    /// the concrete unselected path still contributes zero owned uses to the
    /// internal flow ledger.
    fn available_to_unit(&mut self, arguments: Vec<ExprId>, span: Span) -> CoreId {
        let [argument] = arguments.as_slice() else {
            return self.fail(
                span,
                "G4188",
                "intrinsic `available_to_unit` requires exactly one `Available` witness",
            );
        };
        let argument = self.expression(*argument);
        let witness = self.expressions[argument.0 as usize].ty.clone();
        let Type::Nominal {
            definition,
            arguments,
        } = witness
        else {
            return self.fail(
                span,
                "G4188",
                "intrinsic `available_to_unit` requires compiler-generated `Available` evidence",
            );
        };
        let Some(GenericArgument::Type(environment)) = arguments.get(1) else {
            return self.fail(
                span,
                "G4188",
                "intrinsic `available_to_unit` requires compiler-generated `Available` evidence",
            );
        };
        let has_affine_erasure_proof = definition == crate::intrinsic_available_type_definition()
            && self.ambient_where_bounds.iter().any(|(subject, relation)| {
                self.inference.zonk(subject.clone()).is_ok_and(|subject| {
                    subject == *environment
                        && relation.definition == crate::resolution::language_use_trait_definition()
                        && relation.arguments
                            == [GenericArgument::ConstQuantity(crate::Quantity::AFFINE)]
                })
            });
        if !has_affine_erasure_proof {
            return self.fail(
                span,
                "G4188",
                "releasing `Available<E>` requires an affine `E: Use<[0,1]>` proof",
            );
        }
        let unit = self.alloc(CoreKind::Tuple(vec![]), Type::Unit, span);
        self.alloc(CoreKind::Block(vec![argument, unit]), Type::Unit, span)
    }

    /// Elaborate direct-call operands left-to-right while carrying each
    /// successful unification into the next operand's contextual type. A
    /// generic scalar callable such as `bit_and<T>(T, T)` learns `T = u64`
    /// from `f64_to_bits(value)`; the following unsuffixed mask literal must
    /// then be a `u64`, rather than prematurely defaulting to `i64`.
    ///
    /// Keep the user-facing mismatch diagnostic in `call`. This provisional
    /// unification is only evidence for contextual elaboration, so it cannot
    /// conceal a genuine incompatible argument.
    fn call_arguments_with_context(
        &mut self,
        callee: CoreId,
        parameters: &[Type],
        arguments: Vec<ExprId>,
    ) -> Vec<CoreId> {
        // Contextual type unification must use caller-local holes, never the
        // callee's declaration region names. Open the whole parameter pack
        // together so repeated regions constrain the same hole across operands.
        // The callee expression retains its original contract for the final
        // joint lifetime/provenance check in `call_with_expected`.
        let Type::Tuple(contextual_parameters) = self.freshen_call_context_lifetimes(Type::Tuple(parameters.to_vec())) else {
            unreachable!("freshening preserves the parameter pack shape");
        };
        arguments
            .into_iter()
            .enumerate()
            .map(|(index, value)| {
                let parameter = contextual_parameters.get(index).cloned();
                let expected = parameter.as_ref().map(|parameter| {
                    self.direct_bound_callable_contract(callee, &parameters[index])
                        .unwrap_or_else(|| parameter.clone())
                });
                // Generic parameters begin as inference variables. Expose a
                // scalar shape fixed by an earlier operand to literals, while
                // retaining the unresolved parameter for contextual closures.
                let expected = expected
                    .map(|expected| self.inference.zonk(expected.clone()).unwrap_or(expected));
                let argument = self.expression_expected_with_open_lifetimes(value, expected.clone(), true);
                let argument = expected
                    .as_ref()
                    .and_then(|expected| {
                        self.coerce_standard_string_borrow_to_str(expected, argument, self.body.expression(value).span)
                    })
                    .unwrap_or(argument);
                if let Some(parameter) = parameter {
                    let actual = self.expressions[argument.0 as usize].ty.clone();
                    let _ = self.inference.unify(parameter, actual);
                }
                argument
            })
            .collect()
    }

    /// Open the compiler-owned `Fn` evidence attached to the declaration
    /// currently being elaborated.  This is lexical contract use, not an
    /// inference fallback: a same-spelled user trait has a different frozen
    /// identity and therefore cannot make an arbitrary value callable.
    fn callable_contract_from_ambient_fn_bound(&self, value: &Type) -> Option<Type> {
        for (subject, relation) in &self.ambient_where_bounds {
            if subject != value {
                continue;
            }
            if crate::is_intrinsic_label_trait(relation) {
                let [crate::GenericArgument::Type(payload)] = relation.arguments.as_slice() else {
                    continue;
                };
                return Some(Type::Callable {
                    safety: crate::Safety::Safe,
                    lifetime_binders: 0,
                    parameters: vec![payload.clone()],
                    result: Box::new(Type::Never),
                    effects: EffectRow::empty(),
                    invocation: crate::Quantity::ONCE,
                });
            }
            if !crate::is_intrinsic_callable_trait(relation) {
                continue;
            }
            let parameters = match relation.arguments.as_slice() {
                [crate::GenericArgument::Type(Type::Tuple(parameters))] => parameters.clone(),
                [crate::GenericArgument::Type(Type::Unit)] => vec![],
                _ => continue,
            };
            let outputs = self
                .ambient_callable_type_bindings
                .iter()
                .filter(|binding| {
                    binding.subject == *subject
                        && binding.relation == *relation
                        && binding.name == "Output"
                        && binding.item_arguments.is_empty()
                })
                .collect::<Vec<_>>();
            let effects = self
                .ambient_callable_effect_bindings
                .iter()
                .filter(|binding| {
                    binding.subject == *subject
                        && binding.relation == *relation
                        && binding.name == "Effects"
                        && binding.item_arguments.is_empty()
                })
                .collect::<Vec<_>>();
            let [output] = outputs.as_slice() else {
                continue;
            };
            let effects = match effects.as_slice() {
                [] => EffectRow::empty(),
                [effects] => effects.value.clone(),
                _ => continue,
            };
            return Some(Type::Callable {
                safety: crate::Safety::Safe,
                lifetime_binders: 0,
                parameters,
                result: Box::new(output.value.clone()),
                effects,
                invocation: crate::Quantity::ONCE,
            });
        }
        None
    }
    /// Resolve a qualified trait method used as a first-class callable.  A
    /// trait selection needs a concrete subject. Receiver methods obtain it
    /// from the expected callable's first parameter. Static methods do not
    /// have that parameter, so a contextually typed value may instead select
    /// the one concrete implementation of the qualified trait relation. This
    /// keeps `Trait::method` principled: an unconstrained bare path remains an
    /// error rather than guessing among implementations.
    fn trait_method_value(
        &mut self,
        path: Vec<String>,
        trait_arguments: Vec<crate::header::HeaderGenericArgument>,
        operation_arguments: Vec<crate::header::HeaderGenericArgument>,
        expected: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        let (name, trait_path) = path.split_last()?;
        if trait_path.is_empty() {
            return None;
        }
        let trait_definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Trait, self.module, trait_path)
            {
                ResolutionState::Resolved(definition) => definition,
                _ => return None,
            };
        let Some(ElaboratedHeader::Trait(trait_header)) =
            self.signatures.definitions.get(&trait_definition)
        else {
            return Some(self.fail(
                span,
                "G4168",
                "qualified method path does not name a frozen trait",
            ));
        };
        let Type::Callable {
            lifetime_binders: expected_lifetime_binders,
            parameters: expected_parameters,
            ..
        } = expected.clone().unwrap_or(Type::Error)
        else {
            return Some(self.fail(
                span,
                "G4168",
                "qualified trait method values require a contextual callable type",
            ));
        };
        let Some(subject) = expected_parameters.first().cloned() else {
            return Some(self.fail(
                span,
                "G4168",
                "qualified trait method values require a receiver parameter",
            ));
        };
        let trait_arguments = self.body_generic_arguments(
            &trait_arguments,
            &trait_header.generic_kinds,
            span,
            "G4168",
            "trait method qualification generic arguments do not match its declaration",
        )?;
        let Some(method_generic_kinds) = self.trait_query().method_generic_kinds(
            &crate::ElaboratedTraitReference {
                definition: trait_definition,
                arguments: trait_arguments.clone(),
            },
            name,
        ) else {
            return Some(self.fail(span, "G4168", "trait does not declare the requested method"));
        };
        let method_arguments = if operation_arguments.is_empty() {
            self.inferred_method_generic_arguments(&method_generic_kinds)
        } else {
            if operation_arguments.len() != method_generic_kinds.len() {
                return Some(self.fail(
                    span,
                    "G4168",
                    "trait method operation arguments do not match its declaration",
                ));
            }
            self.body_generic_arguments(
                &operation_arguments,
                &method_generic_kinds,
                span,
                "G4168",
                "trait method operation arguments do not match its declaration",
            )?
        };
        // A declaration-level lifetime method generic and an annotation-level
        // `for<'a>` binder express the same universal callable contract. Open
        // the former with fresh bound lifetimes while proving the value, then
        // retain a concrete `'static` instance for VM lowering just as named
        // HRTB function values do.
        let hrtb_lifetime_slots = method_generic_kinds
            .iter()
            .enumerate()
            .filter_map(|(slot, kind)| {
                matches!(kind, crate::GenericKind::Lifetime).then_some(slot)
            })
            .collect::<Vec<_>>();
        let hrtb_method_value = operation_arguments.is_empty()
            && expected_lifetime_binders > 0
            && hrtb_lifetime_slots.len() == expected_lifetime_binders as usize;
        let selection_method_arguments = if hrtb_method_value {
            method_arguments
                .iter()
                .cloned()
                .enumerate()
                .map(|(slot, argument)| {
                    hrtb_lifetime_slots
                        .iter()
                        .position(|lifetime_slot| *lifetime_slot == slot)
                        .map(|index| {
                            GenericArgument::Lifetime(Lifetime::Bound {
                                depth: 0,
                                index: index as u32,
                            })
                        })
                        .unwrap_or(argument)
                })
                .collect()
        } else {
            method_arguments.clone()
        };
        let runtime_method_arguments = if hrtb_method_value {
            method_arguments
                .iter()
                .cloned()
                .enumerate()
                .map(|(slot, argument)| {
                    hrtb_lifetime_slots.contains(&slot).then_some(
                        GenericArgument::Lifetime(Lifetime::Static),
                    ).unwrap_or(argument)
                })
                .collect()
        } else {
            method_arguments.clone()
        };
        let assumptions = self.ambient_trait_solver_assumptions();
        let relation = crate::ElaboratedTraitReference {
            definition: trait_definition,
            arguments: trait_arguments.clone(),
        };
        let mut subject = self.zonk_type(subject, span);
        if let Some(declaration) = self.trait_query().declared_method_signature(
            TraitGoal {
                relation: relation.clone(),
                subject: Type::Generic(crate::signature::TRAIT_SELF_GENERIC),
            },
            name,
            &selection_method_arguments,
        ) && let Some(parameter) = declaration.parameters.first()
            && let Some(inferred) = declared_receiver_subject(parameter, &subject)
        {
            subject = inferred;
        }
        let mut answer = self.trait_query().select_method_with_assumptions(
            TraitGoal {
                relation: relation.clone(),
                subject: subject.clone(),
            },
            name,
            &selection_method_arguments,
            &assumptions,
        );
        // A static trait method has no `Self` receiver to recover from the
        // contextual callable. If receiver-shaped selection did not find a
        // solution, recover the subject only when the fully-qualified
        // relation has exactly one monomorphic positive implementation. The
        // eventual callable unification still proves that this was genuinely
        // a static-compatible value; multiple or generic candidates remain
        // deliberately unconstrained rather than guessed.
        if matches!(&answer, TraitMethodAnswer::NoSolution) {
            let candidates = self
                .signatures
                .definitions
                .values()
                .filter_map(|header| match header {
                    ElaboratedHeader::Implementation(implementation)
                        if !implementation.negative
                            && implementation.generics == 0
                            && implementation.relation == relation =>
                    {
                        Some(implementation.self_ty.clone())
                    }
                    _ => None,
                })
                .fold(Vec::new(), |mut candidates, candidate| {
                    if !candidates.contains(&candidate) {
                        candidates.push(candidate);
                    }
                    candidates
                });
            if let [candidate] = candidates.as_slice() {
                subject = candidate.clone();
                answer = self.trait_query().select_method_with_assumptions(
                    TraitGoal {
                        relation: relation.clone(),
                        subject: subject.clone(),
                    },
                    name,
                    &selection_method_arguments,
                    &assumptions,
                );
            }
        }
        let (evidence, method, signature) = match answer {
            TraitMethodAnswer::Selected {
                evidence,
                method,
                signature,
            } => (evidence, method, signature),
            TraitMethodAnswer::Refuted { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method is refuted by a negative implementation",
                ));
            }
            TraitMethodAnswer::NoSolution => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "no implementation provides the qualified trait method",
                ));
            }
            TraitMethodAnswer::Ambiguous => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method implementation is ambiguous",
                ));
            }
            TraitMethodAnswer::Overflow => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method selection exceeded the solver limit",
                ));
            }
            TraitMethodAnswer::MissingMethod { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "selected implementation omits the qualified trait method",
                ));
            }
            TraitMethodAnswer::MethodArity { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method generic arguments could not be inferred",
                ));
            }
        };
        let effects = if hrtb_method_value {
            self.normalize_concrete_hrtb_effect_row(
                signature.effects.clone(),
                expected_lifetime_binders,
            )
        } else {
            self.normalize_concrete_effect_row(signature.effects.clone())
        };
        let callable = self.normalize_selectable_type_projections(Type::Callable {
            safety: signature.safety,
            lifetime_binders: if hrtb_method_value {
                expected_lifetime_binders
            } else {
                0
            },
            parameters: signature.parameters.clone(),
            result: Box::new(signature.result.clone()),
            effects,
            invocation: signature.invocation,
        });
        let Some(expected) = expected else {
            unreachable!("the contextual callable was checked above");
        };
        let expected = if hrtb_method_value {
            let Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } = expected
            else {
                unreachable!("the contextual callable was checked above");
            };
            Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects: self.normalize_concrete_hrtb_effect_row(effects, lifetime_binders),
                invocation,
            }
        } else {
            expected
        };
        let expected = self.normalize_selectable_type_projections(expected);
        if self.inference.unify(expected, callable.clone()).is_err() {
            return Some(self.fail(
                span,
                "G4168",
                "qualified trait method value does not match its contextual callable type",
            ));
        }
        // The bound-lifetime signature above proves the HRTB callable itself.
        // Contract obligations, however, are checked at the concrete VM
        // instance boundary. Re-selecting with `'static` prevents a bound
        // region inside an associated effect-row equality from being sent to
        // ordinary projection normalization, which only has executable
        // concrete evidence.
        let contract_signature = if hrtb_method_value {
            match self.trait_query().select_method_with_assumptions(
                TraitGoal {
                    relation,
                    subject,
                },
                name,
                &runtime_method_arguments,
                &assumptions,
            ) {
                TraitMethodAnswer::Selected { signature, .. } => *signature,
                _ => *signature.clone(),
            }
        } else {
            *signature.clone()
        };
        self.check_callable_contract_bounds(contract_signature, None, span);
        Some(self.alloc(
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments: runtime_method_arguments,
                deferred: None,
            },
            callable,
            span,
        ))
    }

    /// Resolve an explicitly-qualified trait method call. The method's first
    /// declared parameter is the receiver; qualification keeps this initial
    /// surface free of accidental field-vs-method ambiguity while preserving
    /// the solver evidence and selected implementation identity for MIR.
    fn trait_method_call(
        &mut self,
        path: Vec<String>,
        trait_arguments: Vec<crate::header::HeaderGenericArgument>,
        operation_arguments: Vec<crate::header::HeaderGenericArgument>,
        supplied: Vec<ExprId>,
        expected_result: Option<Type>,
        span: Span,
    ) -> Option<CoreId> {
        let (name, trait_path) = path.split_last()?;
        if trait_path.is_empty() {
            return None;
        }
        let trait_definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Trait, self.module, trait_path)
            {
                ResolutionState::Resolved(definition) => definition,
                _ => return None,
            };
        let Some(ElaboratedHeader::Trait(trait_header)) =
            self.signatures.definitions.get(&trait_definition)
        else {
            return Some(self.fail(
                span,
                "G4168",
                "qualified method path does not name a frozen trait",
            ));
        };
        let trait_arguments = self.body_generic_arguments(
            &trait_arguments,
            &trait_header.generic_kinds,
            span,
            "G4168",
            "trait method qualification generic arguments do not match its declaration",
        )?;
        let Some(method_generic_kinds) = self.trait_query().method_generic_kinds(
            &crate::ElaboratedTraitReference {
                definition: trait_definition,
                arguments: trait_arguments.clone(),
            },
            name,
        ) else {
            return Some(self.fail(span, "G4168", "trait does not declare the requested method"));
        };
        let (receiver, subject, mut peeled_subject, remaining_arguments) = match supplied
            .split_first()
        {
            Some((receiver_source, remaining_arguments)) => {
                let receiver = self.expression(*receiver_source);
                let receiver_type =
                    self.zonk_type(self.expressions[receiver.0 as usize].ty.clone(), span);
                // Retain the legacy first-argument fallback for declarations
                // whose first parameter does not mention Self. For Self and
                // borrowed Self, the declaration determines the subject below.
                let peeled_subject = match &receiver_type {
                    Type::Reference { referent, .. } => Some((**referent).clone()),
                    _ => None,
                };
                (Some(receiver), receiver_type, peeled_subject, remaining_arguments)
            }
            None => {
                let Some(expected_result) = expected_result else {
                    return Some(self.fail(
                        span,
                        "G4168",
                        "receiver-less qualified trait method calls require an expected result type",
                    ));
                };
                (None, self.zonk_type(expected_result, span), None, &[] as &[ExprId])
            }
        };
        let method_arguments = if operation_arguments.is_empty() {
            self.inferred_method_generic_arguments(&method_generic_kinds)
        } else {
            if operation_arguments.len() != method_generic_kinds.len() {
                return Some(self.fail(
                    span,
                    "G4168",
                    "trait method operation arguments do not match its declaration",
                ));
            }
            self.body_generic_arguments(
                &operation_arguments,
                &method_generic_kinds,
                span,
                "G4168",
                "trait method operation arguments do not match its declaration",
            )?
        };
        let assumptions = self.ambient_trait_solver_assumptions();
        let relation = crate::ElaboratedTraitReference {
            definition: trait_definition,
            arguments: trait_arguments.clone(),
        };
        let mut selected_subject = subject.clone();
        if receiver.is_some()
            && let Some(declaration) = self.trait_query().declared_method_signature(
                TraitGoal {
                    relation: relation.clone(),
                    subject: Type::Generic(crate::signature::TRAIT_SELF_GENERIC),
                },
                name,
                &method_arguments,
            )
            && let Some(parameter) = declaration.parameters.first()
            && let Some(inferred) = declared_receiver_subject(parameter, &subject)
        {
            selected_subject = inferred;
            peeled_subject = None;
        }
        let mut answer = self.trait_query().select_method_with_assumptions(
            TraitGoal {
                relation: relation.clone(),
                subject: selected_subject.clone(),
            },
            name,
            &method_arguments,
            &assumptions,
        );
        if matches!(answer, TraitMethodAnswer::NoSolution)
            && let Some(peeled_subject) = peeled_subject
            && peeled_subject != selected_subject
        {
            selected_subject = peeled_subject;
            answer = self.trait_query().select_method_with_assumptions(
                TraitGoal {
                    relation: relation.clone(),
                    subject: selected_subject.clone(),
                },
                name,
                &method_arguments,
                &assumptions,
            );
        }
        // A receiver-less trait method inside a generic declaration is
        // selected from the declaration's own ambient bound rather than from
        // a concrete implementation.  Keep that request deferred exactly as
        // generic operator dispatch does; instance materialization supplies
        // the eventual implementation evidence.
        if matches!(answer, TraitMethodAnswer::NoSolution) {
            let goal = TraitGoal {
                relation: relation.clone(),
                subject: selected_subject.clone(),
            };
            if assumptions.contains(&goal)
                && let Some(signature) = self.trait_query().declared_method_signature(
                    goal.clone(),
                    name,
                    &method_arguments,
                )
            {
                if receiver.is_none() && !signature.parameters.is_empty() {
                    return Some(self.fail(
                        span,
                        "G4168",
                        "qualified trait method requires a receiver argument",
                    ));
                }
                let deferred = DeferredTraitMethod {
                    relation: goal.relation,
                    subject: goal.subject,
                    name: name.clone(),
                };
                let placeholder = Self::deferred_trait_method_placeholder(&deferred);
                let callee = self.alloc(
                    CoreKind::TraitMethod {
                        evidence: placeholder,
                        method: placeholder,
                        trait_arguments,
                        method_arguments,
                        deferred: Some(deferred),
                    },
                    Type::Callable {
                        safety: signature.safety,
                        lifetime_binders: 0,
                        parameters: signature.parameters.clone(),
                        result: Box::new(signature.result.clone()),
                        effects: signature.effects.clone(),
                        invocation: signature.invocation,
                    },
                    span,
                );
                let parameters = signature
                    .parameters
                    .iter()
                    .cloned()
                    .map(|parameter| self.normalize_concrete_type_projections(parameter))
                    .collect::<Vec<_>>();
                let receiver_offset = usize::from(receiver.is_some());
                let mut values = receiver.into_iter().collect::<Vec<_>>();
                for (index, argument) in remaining_arguments.iter().enumerate() {
                    let parameter_index = index + receiver_offset;
                    let value = match parameters.get(parameter_index) {
                        Some(parameter) => {
                            let value = self.expression_expected(*argument, Some(parameter.clone()));
                            let actual = self.expressions[value.0 as usize].ty.clone();
                            let _ = self.inference.unify(parameter.clone(), actual);
                            value
                        }
                        None => self.expression(*argument),
                    };
                    values.push(value);
                }
                let call = self.call(callee, values, span);
                self.check_callable_contract_bounds(signature, None, span);
                return Some(call);
            }
        }
        let (evidence, method, signature) = match answer {
            TraitMethodAnswer::Selected {
                evidence,
                method,
                signature,
            } => (evidence, method, signature),
            TraitMethodAnswer::Refuted { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method is refuted by a negative implementation",
                ));
            }
            TraitMethodAnswer::NoSolution => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "no implementation provides the qualified trait method",
                ));
            }
            TraitMethodAnswer::Ambiguous => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method implementation is ambiguous",
                ));
            }
            TraitMethodAnswer::Overflow => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method selection exceeded the solver limit",
                ));
            }
            TraitMethodAnswer::MissingMethod { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "selected implementation omits the qualified trait method",
                ));
            }
            TraitMethodAnswer::MethodArity { .. } => {
                return Some(self.fail(
                    span,
                    "G4169",
                    "qualified trait method generic arguments could not be inferred",
                ));
            }
        };
        let parameters = signature
            .parameters
            .iter()
            .cloned()
            .map(|parameter| self.normalize_concrete_type_projections(parameter))
            .collect::<Vec<_>>();
        if receiver.is_none() && !parameters.is_empty() {
            return Some(self.fail(
                span,
                "G4168",
                "qualified trait method requires a receiver argument",
            ));
        }
        let effects = self.normalize_concrete_effect_row(signature.effects.clone());
        let callee = self.alloc(
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred: None,
            },
            Type::Callable {
                safety: signature.safety,
                lifetime_binders: 0,
                parameters: parameters.clone(),
                result: Box::new(signature.result.clone()),
                effects,
                invocation: signature.invocation,
            },
            span,
        );
        let receiver_offset = usize::from(receiver.is_some());
        let mut values = receiver.into_iter().collect::<Vec<_>>();
        for (index, argument) in remaining_arguments.iter().enumerate() {
            let parameter_index = index + receiver_offset;
            let value = match parameters.get(parameter_index) {
                Some(parameter) => {
                    let value = self.expression_expected(*argument, Some(parameter.clone()));
                    let actual = self.expressions[value.0 as usize].ty.clone();
                    let _ = self.inference.unify(parameter.clone(), actual);
                    value
                }
                None => self.expression(*argument),
            };
            values.push(value);
        }
        let call = self.call(callee, values, span);
        self.check_callable_contract_bounds(*signature.clone(), None, span);
        Some(call)
    }
    fn perform(
        &mut self,
        path: Vec<String>,
        effect_arguments: Vec<crate::header::HeaderGenericArgument>,
        operation_arguments: Vec<crate::header::HeaderGenericArgument>,
        arguments: Vec<ExprId>,
        span: Span,
    ) -> Option<CoreId> {
        let (operation_name, effect_path) = path.split_last()?;
        if effect_path.is_empty() {
            return None;
        }
        let effect_definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Effect, self.module, effect_path)
            {
                ResolutionState::Resolved(definition) => definition,
                // This remains an ordinary value call unless the prefix resolves
                // unambiguously in the dedicated effect namespace.
                _ => return None,
            };
        let Some(ElaboratedHeader::Effect(effect)) =
            self.signatures.definitions.get(&effect_definition)
        else {
            return Some(self.fail(
                span,
                "G4150",
                "resolved effect has no frozen operation table",
            ));
        };
        let effect_arguments = match self.body_generic_arguments(
            &effect_arguments,
            &effect.generic_kinds,
            span,
            "G4151",
            "effect operation protocol arguments do not match its declaration",
        ) {
            Some(arguments) => arguments,
            None => {
                return Some(self.fail(
                    span,
                    "G4151",
                    "effect operation protocol arguments do not match its declaration",
                ));
            }
        };
        let operation_arguments = match self.operation_generic_arguments(
            effect,
            operation_name,
            &operation_arguments,
            span,
        ) {
            Some(arguments) => arguments,
            None => {
                return Some(self.fail(
                    span,
                    "G4152",
                    "effect does not declare the requested operation",
                ));
            }
        };
        let Ok((operation_index, operation)) =
            self.signatures.instantiate_effect_operation_generic(
                effect_definition,
                &effect_arguments,
                &operation_arguments,
                operation_name,
            )
        else {
            return Some(self.fail(
                span,
                "G4152",
                "effect operation generic arguments do not satisfy its declaration contract",
            ));
        };
        if operation.parameters.len() != arguments.len() {
            return Some(self.fail(
                span,
                "G4153",
                "effect operation argument count does not match its declaration",
            ));
        }
        // Effect operation signatures cross package facades just like callable
        // signatures.  Normalize concrete associated items before using the
        // payload contract as an expression expectation; otherwise a payload
        // constructed as `Packet<i64>` cannot satisfy the equivalent frozen
        // `Packet<<i64 as FacadedTrait>::Item>` operation parameter.
        let parameters = operation
            .parameters
            .iter()
            .cloned()
            .map(|parameter| self.normalize_selectable_type_projections(parameter))
            .collect::<Vec<_>>();
        let result = self.normalize_selectable_type_projections(operation.result.clone());
        let values = arguments
            .into_iter()
            .zip(&parameters)
            .map(|(argument, expected)| {
                let argument = self.expression_expected(argument, Some(expected.clone()));
                let actual = self.expressions[argument.0 as usize].ty.clone();
                if self
                    .unify_rigid_lifetimes(expected.clone(), actual, span)
                    .is_err()
                {
                    self.error(
                        span,
                        "G4154",
                        "effect operation argument does not match its declaration",
                    );
                    self.recovered = true;
                }
                argument
            })
            .collect::<Vec<_>>();
        // The selected operation payload/result contracts above are already
        // normalized before unification. Its protocol identity must cross the
        // same boundary: retaining a selectable associated type only in the
        // effect argument would leave Core apparently clean while making the
        // corresponding MIR `Perform` impossible for the VM to encode.
        let mut effect_projection_stack = std::collections::BTreeSet::new();
        let effect_arguments = effect_arguments
            .into_iter()
            .map(|argument| {
                self.normalize_selectable_type_argument(
                    argument,
                    &mut effect_projection_stack,
                    &[],
                )
            })
            .collect();
        let instance = EffectInstance {
            definition: effect_definition,
            arguments: effect_arguments,
        };
        self.check_effect_instance(&instance, Some(operation_index), span);
        let reference_contract = callable_reference_origin_from_contract(
            self.signatures,
            &parameters,
            &result,
        );
        let reference_shape =
            call_reference_shape(self.signatures, &result, &reference_contract);
        Some(self.alloc(
            CoreKind::Perform {
                effect: instance,
                operation: operation_index,
                payload_types: parameters,
                arguments: values,
                terminal: operation.terminal,
                reference_origin: reference_contract.clone(),
                reference_contract,
                reference_shape,
            },
            result,
            span,
        ))
    }
    /// Supply operation-generic arguments independently from the enclosing
    /// effect instance.  Operation binders retain their native semantic kind:
    /// an effect row or structural constant must not be coerced into a type
    /// hole before the operation contract is instantiated.
    fn operation_generic_arguments(
        &mut self,
        effect: &ElaboratedEffect,
        name: &str,
        supplied: &[crate::header::HeaderGenericArgument],
        span: Span,
    ) -> Option<Vec<GenericArgument>> {
        let operation = effect
            .operations
            .iter()
            .find(|operation| operation.name == name)?;
        let kinds = operation.generic_kinds.get(effect.generics as usize..)?;
        if supplied.is_empty() && !kinds.is_empty() {
            return Some(
                kinds
                    .iter()
                    .enumerate()
                    .map(|(offset, kind)| match kind {
                        crate::GenericKind::Type => GenericArgument::Type(self.inference.fresh()),
                        crate::GenericKind::EffectRow => {
                            GenericArgument::EffectRow(self.inference.fresh_effects())
                        }
                        // The declaration-owned operation slot remains rigid
                        // until the selected operation contract opens it at
                        // the perform/handler boundary.
                        crate::GenericKind::Lifetime => GenericArgument::Lifetime(
                            Lifetime::Generic(effect.generics + offset as u32),
                        ),
                        crate::GenericKind::Const(kind) => self.inference.fresh_const(*kind),
                    })
                    .collect(),
            );
        }
        self.body_generic_arguments(
            supplied,
            kinds,
            span,
            "G4152",
            "effect operation arguments do not match its declaration",
        )
    }
    fn handle(
        &mut self,
        computation: ExprId,
        clauses: Vec<HandlerClause>,
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        // With no operation or completion arm, the standard completion arm is
        // the identity `value => value`.  Avoid materializing a vacuous
        // handler node so normal computations retain their ordinary Core/MIR
        // execution path.
        if clauses.is_empty() {
            return self.expression(computation);
        }
        let mut completion_clauses = Vec::new();
        let mut operation_clauses = Vec::new();
        for clause in clauses {
            if clause.operation_candidate && self.is_handler_operation_candidate(&clause) {
                operation_clauses.push(clause);
            } else {
                completion_clauses.push(clause);
            }
        }
        if operation_clauses.is_empty() {
            return self.completion_handle(computation, &completion_clauses, expected, span);
        }
        let mut resolved = Vec::with_capacity(operation_clauses.len());
        for clause in operation_clauses {
            resolved.push(self.resolve_handler_clause(clause));
        }
        // Handler operations use the same ordered finite-domain proof as
        // completion dispatch.  Previously this proof was only consulted for
        // effect discharge, which meant a duplicate or post-fallback handler
        // row could reach MIR even though it could never be selected.
        for index in self.unreachable_handler_operation_rows(&resolved) {
            self.error(
                resolved[index].source.span,
                "G4175",
                "handler arm is unreachable because earlier arms cover every payload it can match",
            );
            self.recovered = true;
        }
        // An effect leaves the outward row only when every operation has an
        // irrefutable arm.  This deliberately conservative rule preserves the
        // required forwarding behaviour of partial handlers until the shared
        // pattern-matrix pass proves more precise coverage.
        let covered_operations = self.exhaustively_handled_operations(&resolved);
        let covered = self.exhaustively_handled_effects(&covered_operations);
        let mut active = self.handled_effects.clone();
        active.extend(covered);
        let previous = std::mem::replace(&mut self.handled_effects, active);
        let mut active_operations = self.handled_operations.clone();
        active_operations.extend(covered_operations);
        let previous_operations =
            std::mem::replace(&mut self.handled_operations, active_operations);
        // A handler is an expression boundary just like a block or a direct
        // call.  Its declared result must therefore constrain operation-arm
        // bodies before they are elaborated.  This matters for the canonical
        // `Bool` carrier (`Result<(), ()>`): a terminal arm written as
        // `true`/`false` otherwise falls back to the legacy scalar literal
        // and only fails at the outer function boundary.
        let result = expected.clone().unwrap_or_else(|| self.inference.fresh());
        let computation = self.expression(computation);
        let computation_ty = self.expressions[computation.0 as usize].ty.clone();
        if !matches!(computation_ty, Type::Never)
            && self
                .inference
                .unify(result.clone(), computation_ty)
                .is_err()
        {
            self.error(
                span,
                "G4164",
                "handler computation has an incompatible result",
            );
            self.recovered = true;
        }

        let mut core_clauses = Vec::with_capacity(resolved.len());
        for (clause_index, clause) in resolved.into_iter().enumerate() {
            let mut patterns = Vec::with_capacity(clause.patterns.len());
            let mut bindings = Vec::new();
            self.locals.enter();
            for pattern in &clause.patterns {
                let names = pattern
                    .plan
                    .bindings
                    .iter()
                    .map(|binding| (binding.key, binding.name.clone()))
                    .collect::<std::collections::BTreeMap<_, _>>();
                for binding in &pattern.plan.bindings {
                    self.locals.define(binding.name.clone(), binding.ty.clone());
                    bindings.push((binding.name.clone(), binding.ty.clone()));
                }
                patterns.push(self.core_pattern(
                    pattern.plan.decision.clone(),
                    pattern.plan.subject.clone(),
                    clause.source.span,
                    Some(&names),
                ));
            }
            // Freeze the same residual row that will be installed when the
            // continuation resumes.  At this point `handled_effects` already
            // contains every enclosing total deep handler plus this handler's
            // own total coverage, while partial coverage remains available
            // only for direct operations.  This is the semantic subtraction
            // point: a declined partial arm forwards outward instead of
            // silently erasing a whole protocol from a callable boundary.
            let continuation_effects = self.residual_effects();
            // Handler clauses consume the same frozen operation ABI as a
            // `Perform`. Normalize concrete selected associated items through
            // package facades before creating continuation binders or checking
            // tail-arm results, so the clause cannot observe a less concrete
            // contract than its dispatcher.
            let operation_parameters = clause
                .operation
                .parameters
                .iter()
                .cloned()
                .map(|parameter| self.normalize_selectable_type_projections(parameter))
                .collect::<Vec<_>>();
            let operation_result =
                self.normalize_selectable_type_projections(clause.operation.result.clone());
            let resumption = if clause.operation.terminal {
                if let Some(name) = &clause.source.resumption {
                    self.error(
                        clause.source.span,
                        "G4160",
                        "terminal handler operation cannot bind a resumption",
                    );
                    self.recovered = true;
                    // Retain a terminal Core marker after reporting so later
                    // lowering never mistakes the arm for a callable one.
                    let _ = name;
                }
                if clause.source.discard_resumption {
                    self.error(
                        clause.source.span,
                        "G4160",
                        "terminal handler operation cannot carry a continuation pattern",
                    );
                    self.recovered = true;
                }
                CoreHandlerResumption::Terminal
            } else if clause.source.discard_resumption {
                if clause.operation.resumption.requires_positive_use() {
                    self.error(
                        clause.source.span,
                        "G4160",
                        "handler discards a continuation whose quantity requires a resume",
                    );
                    self.recovered = true;
                }
                CoreHandlerResumption::Discard {
                    quantity: clause.operation.resumption,
                }
            } else if let Some(name) = &clause.source.resumption {
                self.locals.define(
                    name.clone(),
                    Type::Callable {
                        safety: crate::Safety::Safe,
                        lifetime_binders: 0,
                        parameters: vec![operation_result.clone()],
                        result: Box::new(result.clone()),
                        // A deep resumption reinstalls this handler, so its
                        // callable contract exposes only the residual outward
                        // row rather than the protocol being intercepted.
                        effects: continuation_effects.clone(),
                        invocation: clause.operation.resumption,
                    },
                );
                CoreHandlerResumption::Explicit {
                    name: name.clone(),
                    quantity: clause.operation.resumption,
                }
            } else {
                CoreHandlerResumption::Tail {
                    quantity: clause.operation.resumption,
                }
            };
            let active_resumption = match &resumption {
                CoreHandlerResumption::Explicit { name, .. } => Some(name.clone()),
                CoreHandlerResumption::Tail { .. }
                | CoreHandlerResumption::Discard { .. }
                | CoreHandlerResumption::Terminal => None,
            };
            let mut active_identity = None;
            if let Some(name) = &active_resumption {
                match self.locals.binding_generation(name) {
                    Some(binding_generation) => {
                        let identity = ActiveResumption {
                            id: ResumptionId(self.next_resumption),
                            name: name.clone(),
                            binding_generation,
                        };
                        self.next_resumption = self.next_resumption.saturating_add(1);
                        self.resumption_bindings
                            .insert((name.clone(), binding_generation), identity.clone());
                        self.active_resumptions.push(identity.clone());
                        active_identity = Some(identity);
                    }
                    None => {
                        self.error(
                            clause.source.span,
                            "G4160",
                            "handler continuation binder lost its lexical identity",
                        );
                        self.recovered = true;
                    }
                }
            }
            if let Some(identity) = active_identity.as_ref() {
                self.resumption_use_trackers.push(ResumptionUseTracker {
                    identity: identity.clone(),
                    direct_uses: 0,
                });
            }
            // A deep handler is reinstated only around a resumed protected
            // continuation.  While its clause itself runs the selected frame
            // is suspended, so a fresh operation of this protocol must flow
            // to an enclosing handler (or the callable's outward row), never
            // be discharged by this same frame.  Retain the enclosing handler
            // facts, but temporarily remove this handler's total/partial
            // coverage while elaborating the clause body.
            let clause_effects = std::mem::replace(&mut self.handled_effects, previous.clone());
            let clause_operations =
                std::mem::replace(&mut self.handled_operations, previous_operations.clone());
            let body_expected = match &resumption {
                CoreHandlerResumption::Tail { .. } => Some(operation_result.clone()),
                CoreHandlerResumption::Explicit { .. }
                | CoreHandlerResumption::Discard { .. }
                | CoreHandlerResumption::Terminal => Some(result.clone()),
            };
            let previous_unsafe = std::mem::replace(&mut self.unsafe_context, false);
            let body = self.expression_expected(clause.source.body, body_expected);
            self.unsafe_context = previous_unsafe;
            if let Some(name) = active_resumption.as_ref() {
                self.check_resumption_capture_escapes(
                    body,
                    &std::collections::BTreeSet::from([name.clone()]),
                );
            }
            self.handled_effects = clause_effects;
            self.handled_operations = clause_operations;
            let direct_uses = if active_identity.is_some() {
                self.resumption_use_trackers
                    .pop()
                    .expect("active handler resumption must retain its use tracker")
                    .direct_uses
            } else {
                0
            };
            if active_identity.is_some() {
                self.active_resumptions
                    .pop()
                    .expect("active handler resumption must outlive its clause body");
            }
            // A replayed continuation reinstates its protected residual once
            // per direct invocation. That residual must not carry a unique
            // loan or a live lexical leave target: either capability would be
            // duplicated by the second activation.
            if direct_uses >= 2 {
                if self.replay_residual_captures_label_transfer(
                    computation,
                    &clause.effect,
                    clause.operation_index,
                ) {
                    self.error(
                        clause.source.span,
                        "G4188",
                        "multi-shot resumption cannot capture an active label",
                    );
                    self.recovered = true;
                }
                if self.replay_residual_captures_unique_borrow(
                    computation,
                    &clause.effect,
                    clause.operation_index,
                ) {
                    self.error(
                        clause.source.span,
                        "G4188",
                        "multi-shot resumption cannot capture a unique borrow",
                    );
                    self.recovered = true;
                }
            }
            self.locals.leave();
            let body_ty = self.expressions[body.0 as usize].ty.clone();
            let expected = match resumption {
                CoreHandlerResumption::Tail { .. } => operation_result.clone(),
                CoreHandlerResumption::Explicit { .. }
                | CoreHandlerResumption::Discard { .. }
                | CoreHandlerResumption::Terminal => result.clone(),
            };
            if self.unify_rigid_lifetimes(expected, body_ty, span).is_err() {
                self.error(
                    clause.source.span,
                    "G4161",
                    "handler clause body does not match its continuation contract",
                );
                self.recovered = true;
            }
            let continuation =
                (!clause.operation.terminal).then(|| CoreHandlerContinuationContract {
                    brand: CallableBrand::Continuation {
                        owner: self.definition,
                        clause: clause_index as u32,
                    },
                    parameter: operation_result.clone(),
                    result: result.clone(),
                    effects: continuation_effects.clone(),
                    invocation: clause.operation.resumption,
                    direct_uses: match &resumption {
                        CoreHandlerResumption::Tail { .. } => 1,
                        CoreHandlerResumption::Explicit { .. } => direct_uses,
                        CoreHandlerResumption::Discard { .. } | CoreHandlerResumption::Terminal => {
                            0
                        }
                    },
                });
            self.validate_handler_continuation_contract(
                &resumption,
                continuation.as_ref(),
                &operation_result,
                &result,
                &continuation_effects,
                clause.source.span,
            );
            core_clauses.push(CoreHandlerClause {
                brand: CallableBrand::HandlerClause {
                    owner: self.definition,
                    clause: clause_index as u32,
                },
                effect: clause.effect,
                operation: clause.operation_index,
                payload_types: operation_parameters,
                patterns,
                bindings,
                resumption,
                continuation,
                body,
                terminal: clause.operation.terminal,
                span: clause.source.span,
            });
        }
        self.handled_effects = previous;
        self.handled_operations = previous_operations;
        let handler = self.alloc(
            CoreKind::Handle {
                computation,
                clauses: core_clauses,
            },
            result,
            span,
        );
        self.check_handler_label_transfer_escape(handler, span);
        if completion_clauses.is_empty() {
            handler
        } else {
            self.completion_handle_core(handler, &completion_clauses, expected, span, true)
        }
    }
    /// Normal-completion dispatch is a distinct Core node.  Keeping its
    /// structural patterns intact lets the MIR boundary compile an ordered
    /// decision chain, rather than conflating completion with effect operation
    /// dispatch or desugaring binders into an insufficiently expressive `let`.
    fn completion_handle(
        &mut self,
        computation: ExprId,
        clauses: &[HandlerClause],
        expected: Option<Type>,
        span: Span,
    ) -> CoreId {
        let subject = self.expression(computation);
        self.completion_handle_core(subject, clauses, expected, span, false)
    }

    fn completion_handle_core(
        &mut self,
        subject: CoreId,
        clauses: &[HandlerClause],
        expected: Option<Type>,
        span: Span,
        handles_operations: bool,
    ) -> CoreId {
        // Structural value patterns contribute ordinary type constraints.
        // A polymorphic initializer may leave an uninhabited variant's type
        // parameter open; another value pattern can close it without any
        // compiler knowledge of Boolean spellings or constructor names.
        let subject_context = self.expressions[subject.0 as usize].ty.clone();
        for pattern in clauses.iter().filter_map(|clause| clause.completion) {
            self.constrain_constant_pattern_type(pattern, &subject_context);
        }
        // Operation-arm inference has already established the handler result
        // by the time normal-completion dispatch is built.  Resolve that
        // result before elaborating literal or structural patterns: the
        // pattern elaborator deliberately compares concrete subjects and
        // would otherwise reject a valid refutable arm against an unresolved
        // inference variable.
        let subject_ty = self.zonk_type(self.expressions[subject.0 as usize].ty.clone(), span);
        let refinement = match self.expressions[subject.0 as usize].kind.clone() {
            CoreKind::PatternTest {
                subject,
                pattern,
                refinement,
            } => Some((subject, pattern, refinement)),
            _ => None,
        };
        let result = expected.unwrap_or_else(|| self.inference.fresh());
        let mut core_clauses = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let Some(pattern) = clause.completion else {
                return self.fail(
                    clause.span,
                    "G4166",
                    "mixed completion and operation handler arms",
                );
            };
            let scope = self.pattern_generic_scope();
            let elaboration = elaborate_pattern_with_scope(
                self.body,
                pattern,
                subject_ty.clone(),
                self.index,
                self.signatures,
                self.module,
                &scope,
            );
            for diagnostic in &elaboration.diagnostics {
                self.error(diagnostic.span, diagnostic.code, &diagnostic.message);
            }
            if elaboration.recovered {
                self.recovered = true;
            }
            let names = elaboration
                .plan
                .bindings
                .iter()
                .map(|binding| (binding.key, binding.name.clone()))
                .collect::<std::collections::BTreeMap<_, _>>();
            let mut bindings = elaboration
                .plan
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding.ty.clone()))
                .collect::<Vec<_>>();
            let core_pattern = self.core_pattern(
                elaboration.plan.decision,
                elaboration.plan.subject,
                clause.span,
                Some(&names),
            );
            if self.type_has_custom_drop(&subject_ty)
                && matches!(
                    core_pattern,
                    CorePattern::Record { .. } | CorePattern::Enum { .. }
                )
            {
                self.error(
                    clause.span,
                    "G4188",
                    "a custom-Drop aggregate cannot be ownership-deconstructed by a pattern",
                );
                self.recovered = true;
            }
            let refinement = refinement
                .as_ref()
                .and_then(|(subject, pattern, environment)| {
                    if core_pattern_is_true(&core_pattern) {
                        return Some(CoreRefinementBranch {
                            environment: environment.clone(),
                            subject: *subject,
                            pattern: pattern.clone(),
                        });
                    }
                    // A negative `is Variant(..)` arm is equally precise for
                    // a closed two-variant enum. Preserve the complementary
                    // payload layout, but do not leak positive-pattern
                    // binders into that opposite arm.
                    core_pattern_is_false(&core_pattern).then(|| {
                        self.complementary_enum_refinement(*subject, pattern)
                            .map(|pattern| {
                                let mut environment = environment.clone();
                                environment.subject = None;
                                environment.bindings.clear();
                                environment.binding_types.clear();
                                CoreRefinementBranch {
                                    environment,
                                    subject: *subject,
                                    pattern,
                                }
                            })
                    })?
                });
            // Persist only the positive refinement evidence.  The negative
            // counterpart is an elaboration-scoped projection fact with no
            // binders; it has already shaped the frozen Field node and does
            // not need to be replayed by later Core consumers.
            let persisted_refinement = core_pattern_is_true(&core_pattern)
                .then(|| refinement.clone())
                .flatten();
            if let Some(refinement) = &refinement {
                for (name, ty) in &refinement.environment.binding_types {
                    if bindings.iter().any(|(existing, _)| existing == name) {
                        self.error(
                            clause.span,
                            "G4169",
                            "refinement binder conflicts with a completion-pattern binder",
                        );
                        self.recovered = true;
                    } else if self.locals.lookup(name).is_some() {
                        // Core local references retain a compact spelling in
                        // this stage. Allowing a branch-only refinement to
                        // shadow an incoming spelling would make PlaceFlow's
                        // post-state join conflate two owners. Reject it
                        // until Core locals carry their lexical generation.
                        self.error(
                            clause.span,
                            "G4170",
                            "refinement binder cannot shadow an incoming local across a branch join",
                        );
                        self.recovered = true;
                    } else {
                        bindings.push((name.clone(), ty.clone()));
                    }
                }
            }
            self.locals.enter();
            for (name, ty) in &bindings {
                self.locals.define(name.clone(), ty.clone());
            }
            let previous_refinement_bindings = self.active_refinement_bindings.clone();
            let previous_refinement_patterns = self.active_refinement_patterns.clone();
            // A non-binding enum arm proves its subject's variant just as a
            // successful `is Variant(_)` test does. This permits borrowing
            // payload fields without first binding (and moving) their owners.
            if matches!(&core_pattern, CorePattern::Enum { fields, .. }
                if fields.iter().all(|field| matches!(field.pattern, CorePattern::Any)))
                && let Some(place) = self.expression_place(subject)
            {
                self.active_refinement_patterns
                    .push((place, core_pattern.clone()));
            }
            if let Some(refinement) = &refinement {
                self.active_refinement_bindings.extend(
                    refinement
                        .environment
                        .binding_types
                        .iter()
                        .map(|(name, _)| name.clone()),
                );
                if let Some(subject) = self.expression_place(refinement.subject) {
                    self.active_refinement_patterns
                        .push((subject, refinement.pattern.clone()));
                }
            }
            let previous_unsafe = std::mem::replace(&mut self.unsafe_context, false);
            let body = self.expression_expected(clause.body, Some(result.clone()));
            self.unsafe_context = previous_unsafe;
            self.check_refinement_capture_escapes(body, &self.active_refinement_bindings.clone());
            self.active_refinement_bindings = previous_refinement_bindings;
            self.active_refinement_patterns = previous_refinement_patterns;
            self.locals.leave();
            let body_ty = self.expressions[body.0 as usize].ty.clone();
            if self
                .unify_rigid_lifetimes(result.clone(), body_ty, span)
                .is_err()
            {
                self.error(
                    clause.span,
                    "G4167",
                    "completion arm body does not match the handler result type",
                );
                self.recovered = true;
            }
            core_clauses.push(CoreCompletionClause {
                pattern: core_pattern,
                bindings,
                refinement: persisted_refinement,
                body,
                span: clause.span,
            });
        }
        let patterns = core_clauses
            .iter()
            .map(|clause| clause.pattern.clone())
            .collect::<Vec<_>>();
        let coverage = self.analyze_core_pattern_matrix(&patterns, &subject_ty);
        for index in coverage.unreachable {
            self.error(
                core_clauses[index].span,
                "G4168",
                "completion arm is unreachable because earlier arms cover every value it can match",
            );
            self.recovered = true;
        }
        if !coverage.exhaustive {
            return self.fail(
                span,
                "G4166",
                "completion arms do not cover every value; add a fallback or cover every finite constructor",
            );
        }
        let operation_can_finish = handles_operations && matches!(
            &self.expressions[subject.0 as usize].kind,
            CoreKind::Handle { clauses, .. } if clauses.iter().any(|clause|
                !matches!(clause.resumption, CoreHandlerResumption::Tail { .. })
                    && self.expressions[clause.body.0 as usize].ty != Type::Never)
        );
        let result = if !operation_can_finish && core_clauses.iter().all(|clause|
            matches!(self.expressions[clause.body.0 as usize].ty, Type::Never)) {
            Type::Never
        } else { result };
        self.alloc(
            CoreKind::Completion {
                computation: subject,
                clauses: core_clauses,
                refinement_test: None,
                handles_operations,
            },
            result,
            span,
        )
    }

    fn constrain_constant_pattern_type(&mut self, pattern: crate::PatternId, subject: &Type) {
        let path = match &self.body.pattern(pattern).kind {
            crate::PatternKind::Binding(name) => vec![name.clone()],
            crate::PatternKind::Enum { path, arguments, fields } if arguments.is_empty() && fields.is_empty() => path.clone(),
            crate::PatternKind::Tuple(patterns) => {
                if let Type::Tuple(types) = subject {
                    for (pattern, ty) in patterns.clone().into_iter().zip(types) { self.constrain_constant_pattern_type(pattern, ty); }
                }
                return;
            }
            _ => return,
        };
        let ResolutionState::Resolved(definition) = self.index.resolve_path(DefinitionNamespace::Value, self.module, &path) else { return; };
        let Some((ty, _)) = self.signatures.pattern_values.get(&definition) else { return; };
        let ty = ty.clone();
        let arguments = match self.signatures.definitions.get(&definition) {
            Some(ElaboratedHeader::ValueInitializer { generic_kinds, .. }) => generic_kinds.iter().map(|kind| match kind {
                crate::GenericKind::Type => GenericArgument::Type(self.inference.fresh()),
                crate::GenericKind::Lifetime => GenericArgument::Lifetime(self.inference.fresh_lifetime()),
                crate::GenericKind::EffectRow => GenericArgument::EffectRow(self.inference.fresh_effects()),
                crate::GenericKind::Const(kind) => self.inference.fresh_const(*kind),
            }).collect::<Vec<_>>(),
            _ => vec![],
        };
        let ty = self.signatures.instantiate_value_initializer_generic(definition, &arguments).unwrap_or(ty);
        let _ = self.inference.unify(subject.clone(), ty);
    }
    /// Check an ordered pattern matrix against the finite structural domains
    /// available to Stage 0.  Unlike the former constructor-only check, this
    /// follows nested tuple, record, and enum payload decisions. Open leaves
    /// represent every possible resident, not an invented concrete value:
    /// partial matches may be useful but cannot prove those leaves covered.
    fn analyze_core_pattern_matrix(
        &self,
        patterns: &[CorePattern],
        subject: &Type,
    ) -> CorePatternMatrixAnalysis {
        let mut analysis = CorePatternMatrixAnalysis {
            exhaustive: false,
            unreachable: vec![],
        };
        let mut covered_by_catch_all = false;
        for (index, pattern) in patterns.iter().enumerate() {
            if covered_by_catch_all {
                analysis.unreachable.push(index);
            }
            if core_pattern_irrefutable(pattern) {
                covered_by_catch_all = true;
            }
        }
        analysis.exhaustive = covered_by_catch_all;

        // This structural subsumption check also handles unbounded literal
        // domains.  Finite enumeration below proves broader combinations,
        // while an identical `41` row after an earlier `41` must be rejected
        // even though `i64` is not enumerable.
        for (index, pattern) in patterns.iter().enumerate() {
            if patterns[..index]
                .iter()
                .any(|earlier| core_pattern_subsumes(earlier, pattern))
            {
                analysis.unreachable.push(index);
            }
        }

        // An enum's constructor set is finite even when one or more payload
        // domains are not.  Do not require us to enumerate every `i64` or
        // `Text` merely to prove that `Ok(_)` and `Err(_)` cover their two
        // complete variants.  This proof is intentionally narrower than the
        // structural matrix below: one source row must cover every payload
        // slot of its constructor. Preserve this proof if a large matrix
        // exceeds its bounds, but still inspect bounded matrices for rows
        // covered collectively by several predecessors.
        analysis.exhaustive |= self.enum_constructor_patterns_exhaustive(patterns, subject);
        analysis.unreachable.sort_unstable();
        analysis.unreachable.dedup();

        let mut fuel = 131_072;
        let Some(values) = self.finite_pattern_values(subject, 0, &mut fuel) else {
            return analysis;
        };
        for (index, pattern) in patterns.iter().enumerate() {
            let useful = values.iter().any(|value| {
                core_pattern_matches_value(pattern, value) != Some(false)
                    && !patterns[..index]
                        .iter()
                        .any(|earlier| core_pattern_matches_value(earlier, value) == Some(true))
            });
            if !useful {
                analysis.unreachable.push(index);
            }
        }
        analysis.exhaustive |= values.iter().all(|value| {
            patterns
                .iter()
                .any(|pattern| core_pattern_matches_value(pattern, value) == Some(true))
        });
        analysis.unreachable.sort_unstable();
        analysis.unreachable.dedup();
        analysis
    }

    /// Prove a nominal enum exhaustive by complete constructor rows without
    /// descending into unbounded payload types.  Runtime dispatch always
    /// selects a declaration-order variant before projecting payload fields,
    /// so this mirrors the Core/MIR/VM decision boundary precisely.
    fn enum_constructor_patterns_exhaustive(
        &self,
        patterns: &[CorePattern],
        subject: &Type,
    ) -> bool {
        let Type::Nominal { definition, .. } = subject else {
            return false;
        };
        let Some(ElaboratedHeader::Nominal {
            layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
            ..
        }) = self.signatures.definitions.get(definition)
        else {
            return false;
        };
        variants.iter().enumerate().all(|(variant, _)| {
            patterns.iter().any(|pattern| {
                core_pattern_covers_enum_constructor(pattern, *definition, variant as u32)
            })
        })
    }

    /// Enumerate a finite structural over-approximation. An open payload does
    /// not erase its surrounding constructors: `Err(_)` covers all integers
    /// in that branch while the matrix can still partition `Ok(Event)`.
    /// Bound both row count and aggregate intermediate storage. Exhausting
    /// the proof budget means unknown coverage, never an accepted omission.
    fn finite_pattern_values(
        &self,
        subject: &Type,
        depth: u8,
        fuel: &mut usize,
    ) -> Option<Vec<FinitePatternValue>> {
        const MAX_VALUES: usize = 4096;
        const MAX_DEPTH: u8 = 16;
        if *fuel == 0 {
            return None;
        }
        *fuel -= 1;
        if depth >= MAX_DEPTH {
            return Some(vec![FinitePatternValue::Unknown]);
        }
        let values = match subject {
            Type::Unit => Some(vec![FinitePatternValue::Unit]),
            Type::Scalar(ScalarType::Bool) => Some(vec![
                FinitePatternValue::Bool(false),
                FinitePatternValue::Bool(true),
            ]),
            Type::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.finite_pattern_values(field, depth + 1, fuel))
                    .collect::<Option<Vec<_>>>()?;
                finite_pattern_products(fields, MAX_VALUES)
                    .map(|values| values.into_iter().map(FinitePatternValue::Tuple).collect())
            }
            Type::Nominal {
                definition,
                arguments,
            } => match self.signatures.definitions.get(definition)? {
                ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Struct(_),
                    ..
                } => {
                    let fields = self
                        .signatures
                        .instantiate_struct_fields_generic(*definition, arguments)
                        .ok()?;
                    let values = fields
                        .iter()
                        .map(|field| self.finite_pattern_values(&field.ty, depth + 1, fuel))
                        .collect::<Option<Vec<_>>>()?;
                    finite_pattern_products(values, MAX_VALUES).map(|values| {
                        values
                            .into_iter()
                            .map(|fields| FinitePatternValue::Record {
                                definition: *definition,
                                fields,
                            })
                            .collect()
                    })
                }
                ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                    ..
                } => {
                    let mut values = vec![];
                    let mut nodes = 0usize;
                    for (variant, _) in variants.iter().enumerate() {
                        let fields = self
                            .signatures
                            .instantiate_enum_fields_generic(*definition, arguments, variant as u32)
                            .ok()?;
                        let fields = fields
                            .iter()
                            .map(|field| self.finite_pattern_values(&field.ty, depth + 1, fuel))
                            .collect::<Option<Vec<_>>>()?;
                        let products = finite_pattern_products(fields, MAX_VALUES)?;
                        if values.len().checked_add(products.len())? > MAX_VALUES {
                            return None;
                        }
                        nodes = nodes.checked_add(products.len())?
                            .checked_add(products.iter().flatten().map(finite_pattern_weight).sum())?;
                        if nodes > 65_536 {
                            return None;
                        }
                        values.extend(products.into_iter().map(|fields| {
                            FinitePatternValue::Enum {
                                definition: *definition,
                                variant: variant as u32,
                                fields,
                            }
                        }));
                    }
                    Some(values)
                }
                ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Opaque,
                    ..
                } => Some(vec![FinitePatternValue::Unknown]),
                _ => None,
            },
            _ => Some(vec![FinitePatternValue::Unknown]),
        }?;
        *fuel = fuel.checked_sub(values.iter().map(finite_pattern_weight).sum())?;
        Some(values)
    }
    fn residual_effects(&self) -> EffectRow {
        let mut effects = self.declared_effects.clone();
        effects.effects.retain(|effect| {
            !self.handled_effects.contains(effect)
                && !self.effect_is_covered_by_active_operations(effect)
        });
        effects
    }
    /// A nested collection of partial deep handlers can collectively remove a
    /// protocol from the outward row.  The innermost frame receives the first
    /// chance to match; a declined operation forwards to the next frame, so
    /// it is sound to compose exhaustive operation coverage by exact effect
    /// instance.  This is intentionally stronger than treating every partial
    /// handler as opaque, while still refusing to discharge a callable whose
    /// stack lacks an arm for any declared operation.
    fn effect_is_covered_by_active_operations(&self, effect: &EffectInstance) -> bool {
        let Some(ElaboratedHeader::Effect(declaration)) =
            self.signatures.definitions.get(&effect.definition)
        else {
            return false;
        };
        declaration
            .operations
            .iter()
            .enumerate()
            .all(|(operation, _)| {
                self.handled_operations
                    .contains(&(effect.clone(), operation as u32))
            })
    }
    /// Validate the continuation interface before ownership facts and MIR are
    /// allowed to consume the handler.  MIR still validates artifacts, but it
    /// must not be the first phase to discover that a source-level handler
    /// promised an impossible resume/cancellation contract.
    fn validate_handler_continuation_contract(
        &mut self,
        resumption: &CoreHandlerResumption,
        continuation: Option<&CoreHandlerContinuationContract>,
        operation_result: &Type,
        handler_result: &Type,
        residual_effects: &EffectRow,
        span: Span,
    ) {
        let Some(continuation) = continuation else {
            return;
        };
        if self
            .inference
            .unify(continuation.parameter.clone(), operation_result.clone())
            .is_err()
            || self
                .inference
                .unify(continuation.result.clone(), handler_result.clone())
                .is_err()
            || continuation.effects != *residual_effects
        {
            self.error(
                span,
                "G4176",
                "handler continuation contract disagrees with its operation, result, or outward effects",
            );
            self.recovered = true;
        }
        match resumption {
            CoreHandlerResumption::Tail { quantity } => {
                if !quantity.contains(crate::quantity::Quantity::ONCE) {
                    self.error(
                        span,
                        "G6005",
                        "implicit tail resumption is not permitted by the operation's quantity",
                    );
                    self.recovered = true;
                }
            }
            CoreHandlerResumption::Explicit { quantity, .. } => {
                let actual = crate::quantity::Quantity::new(
                    continuation.direct_uses,
                    Some(continuation.direct_uses),
                )
                .expect("a direct resumption use count always forms an interval");
                if continuation.direct_uses > 0 && !quantity.contains(actual) {
                    self.error(
                        span,
                        "G6005",
                        "direct handler resumptions do not satisfy the operation's quantity",
                    );
                    self.recovered = true;
                }
                if continuation.direct_uses == 0 && quantity.requires_positive_use() {
                    self.error(
                        span,
                        "G4178",
                        "handler continuation requires a resume but this arm never invokes it",
                    );
                    self.recovered = true;
                }
            }
            CoreHandlerResumption::Discard { quantity } => {
                if quantity.requires_positive_use() {
                    self.error(
                        span,
                        "G4178",
                        "handler cancellation violates the continuation's required-use quantity",
                    );
                    self.recovered = true;
                }
            }
            CoreHandlerResumption::Terminal => {}
        }
    }
    /// Parser shape never decides whether `Path::name(...)` is an effect arm:
    /// the same spelling may be a nominal enum completion pattern. Probe the
    /// frozen effect namespace without issuing diagnostics; if it is not an
    /// exact declared operation, the caller elaborates the preserved pattern
    /// as a normal completion arm instead.
    fn is_handler_operation_candidate(&self, source: &HandlerClause) -> bool {
        let Some((operation_name, effect_path)) = source.path.split_last() else {
            return false;
        };
        let ResolutionState::Resolved(effect) =
            self.index
                .resolve_path(DefinitionNamespace::Effect, self.module, effect_path)
        else {
            return false;
        };
        let Some(ElaboratedHeader::Effect(declaration)) = self.signatures.definitions.get(&effect)
        else {
            return false;
        };
        // Classify by the namespace and operation name only.  Arity belongs
        // to `resolve_handler_clause`, where an effect-shaped arm can receive
        // the precise protocol- or operation-application diagnostic.  Making
        // classification depend on supplied protocol arguments would instead
        // reinterpret (for example) `State<A, B>::get()` as a completion
        // pattern, which both changes handler semantics and hides the actual
        // source error.
        declaration
            .operations
            .iter()
            .any(|operation| operation.name == *operation_name)
    }
    fn resolve_handler_clause(&mut self, mut source: HandlerClause) -> ResolvedHandlerClause {
        let Some((operation_name, effect_path)) = source.path.split_last() else {
            self.error(source.span, "G4162", "handler clause has no operation path");
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        };
        if effect_path.is_empty() {
            self.error(
                source.span,
                "G4162",
                "handler clause must name an effect-qualified operation",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        }
        let effect =
            match self
                .index
                .resolve_path(DefinitionNamespace::Effect, self.module, effect_path)
            {
                ResolutionState::Resolved(effect) => effect,
                _ => {
                    self.error(
                        source.span,
                        "G4162",
                        "handler clause names an unresolved effect",
                    );
                    self.recovered = true;
                    return ResolvedHandlerClause::error(source);
                }
            };
        let Some(ElaboratedHeader::Effect(declaration)) = self.signatures.definitions.get(&effect)
        else {
            self.error(
                source.span,
                "G4162",
                "handler effect has no frozen operation table",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        };
        let Some(effect_arguments) = self.body_generic_arguments(
            &source.effect_arguments,
            &declaration.generic_kinds,
            source.span,
            "G4163",
            "handler effect arguments do not match its declaration",
        ) else {
            return ResolvedHandlerClause::error(source);
        };
        let Some(operation_arguments) = self.operation_generic_arguments(
            declaration,
            operation_name,
            &source.operation_arguments,
            source.span,
        ) else {
            self.error(
                source.span,
                "G4162",
                "handler operation arguments do not match its declaration",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        };
        let Ok((operation_index, operation)) =
            self.signatures.instantiate_effect_operation_generic(
                effect,
                &effect_arguments,
                &operation_arguments,
                operation_name,
            )
        else {
            self.error(
                source.span,
                "G4162",
                "effect does not declare this handler operation",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        };
        // The current surface has one arm grammar.  A final binding pattern
        // beyond the operation payload is the full-control continuation slot;
        // normalize it into the migration-era field so the typed Core below
        // has one canonical representation regardless of source spelling.
        if source.resumption.is_none() && source.patterns.len() == operation.parameters.len() + 1 {
            let continuation = source.patterns.pop().expect("length established above");
            match &self.body.pattern(continuation).kind {
                crate::body::PatternKind::Binding(name) => {
                    source.resumption = Some(name.clone());
                }
                crate::body::PatternKind::Wildcard => {
                    source.discard_resumption = true;
                }
                _ => {
                    self.error(
                        source.span,
                        "G4160",
                        "the final full-control handler pattern must be a continuation binder",
                    );
                    self.recovered = true;
                }
            }
        }
        if operation.parameters.len() != source.patterns.len() {
            self.error(
                source.span,
                "G4165",
                "handler payload pattern count does not match the operation declaration",
            );
            self.recovered = true;
        }
        let patterns = source
            .patterns
            .iter()
            .copied()
            .zip(operation.parameters.iter().cloned())
            .map(|(pattern, subject)| {
                let scope = self.pattern_generic_scope();
                let elaboration = elaborate_pattern_with_scope(
                    self.body,
                    pattern,
                    subject,
                    self.index,
                    self.signatures,
                    self.module,
                    &scope,
                );
                for diagnostic in &elaboration.diagnostics {
                    self.error(diagnostic.span, diagnostic.code, &diagnostic.message);
                }
                self.recovered |= elaboration.recovered;
                elaboration
            })
            .collect::<Vec<_>>();
        // `BodySyntax` normally rejects this while parsing, but Typed Core is
        // also an API boundary used by recovered and tooling syntax.  Keep
        // the handler environment sound even when a caller supplies a body
        // directly: an explicit generated continuation must not overwrite a
        // payload binder in the same clause scope.
        if let Some(resumption) = &source.resumption
            && patterns
                .iter()
                .flat_map(|pattern| &pattern.plan.bindings)
                .any(|binding| binding.name == *resumption)
        {
            self.error(
                source.span,
                "G4160",
                "handler continuation binder conflicts with a payload binder",
            );
            self.recovered = true;
        }
        ResolvedHandlerClause {
            source,
            effect: EffectInstance {
                definition: effect,
                arguments: effect_arguments,
            },
            operation_index,
            operation,
            patterns,
            failed: false,
        }
    }
    fn exhaustively_handled_operations(
        &self,
        clauses: &[ResolvedHandlerClause],
    ) -> std::collections::BTreeSet<(EffectInstance, u32)> {
        let mut operation_rows =
            std::collections::BTreeMap::<(EffectInstance, u32), Vec<&ResolvedHandlerClause>>::new();
        for clause in clauses {
            if !clause.failed {
                operation_rows
                    .entry((clause.effect.clone(), clause.operation_index))
                    .or_default()
                    .push(clause);
            }
        }
        let mut handled = std::collections::BTreeSet::new();
        for ((effect, operation), rows) in operation_rows {
            if self.handler_operation_is_exhaustive(&rows) {
                handled.insert((effect, operation));
            }
        }
        handled
    }
    fn exhaustively_handled_effects(
        &self,
        handled_operations: &std::collections::BTreeSet<(EffectInstance, u32)>,
    ) -> std::collections::BTreeSet<EffectInstance> {
        handled_operations
            .iter()
            .map(|(effect, _)| effect.clone())
            .collect::<std::collections::BTreeSet<_>>()
            .into_iter()
            .filter(|effect| {
                let Some(ElaboratedHeader::Effect(declaration)) =
                    self.signatures.definitions.get(&effect.definition)
                else {
                    return false;
                };
                declaration
                    .operations
                    .iter()
                    .enumerate()
                    .all(|(operation, _)| {
                        handled_operations.contains(&(effect.clone(), operation as u32))
                    })
            })
            .collect()
    }
    /// A bounded structural matrix proof for operation payloads.  This uses
    /// the same finite abstract domain as normal-completion coverage, so a
    /// handler can discharge an operation through nested enum/record/tuple
    /// patterns without falsely treating a partially refined payload as total.
    /// Uncovered open leaves and over-large domains remain conservatively
    /// outward-facing; irrefutable payloads need no concrete enumeration.
    fn handler_operation_is_exhaustive(&self, rows: &[&ResolvedHandlerClause]) -> bool {
        self.analyze_handler_operation_patterns(rows).exhaustive
    }

    /// Return source indices of handler rows which cannot be selected after
    /// their earlier siblings for the same `(effect instance, operation)`.
    /// Grouping by the resolved protocol identity is important: syntactically
    /// identical operation names from distinct instantiated effects are not
    /// competing dispatch rows.
    fn unreachable_handler_operation_rows(&self, clauses: &[ResolvedHandlerClause]) -> Vec<usize> {
        let mut groups = std::collections::BTreeMap::<
            (EffectInstance, u32),
            Vec<(usize, &ResolvedHandlerClause)>,
        >::new();
        for (index, clause) in clauses
            .iter()
            .enumerate()
            .filter(|(_, clause)| !clause.failed)
        {
            groups
                .entry((clause.effect.clone(), clause.operation_index))
                .or_default()
                .push((index, clause));
        }
        let mut unreachable = vec![];
        for rows in groups.into_values() {
            let clauses = rows.iter().map(|(_, clause)| *clause).collect::<Vec<_>>();
            let analysis = self.analyze_handler_operation_patterns(&clauses);
            unreachable.extend(analysis.unreachable.into_iter().map(|row| rows[row].0));
        }
        unreachable.sort_unstable();
        unreachable
    }

    /// Bounded matrix analysis for one operation's payload tuple.  This is
    /// deliberately shared by both reachability diagnostics and outward
    /// effect coverage: a decision is never considered exhaustive by one
    /// consumer while another consumer still treats an earlier row as live.
    fn analyze_handler_operation_patterns(
        &self,
        rows: &[&ResolvedHandlerClause],
    ) -> CorePatternMatrixAnalysis {
        let mut analysis = CorePatternMatrixAnalysis {
            exhaustive: false,
            unreachable: vec![],
        };
        let Some(first) = rows.first() else {
            return analysis;
        };
        if rows
            .iter()
            .any(|row| row.patterns.len() != first.patterns.len())
        {
            return analysis;
        }
        let mut covered_by_catch_all = false;
        for (index, row) in rows.iter().enumerate() {
            if covered_by_catch_all {
                analysis.unreachable.push(index);
            }
            if row.patterns.iter().all(|pattern| !pattern.plan.refutable) {
                covered_by_catch_all = true;
            }
        }
        analysis.exhaustive = covered_by_catch_all;
        for (index, row) in rows.iter().enumerate() {
            if rows[..index]
                .iter()
                .any(|earlier| handler_patterns_subsume(&earlier.patterns, &row.patterns))
            {
                analysis.unreachable.push(index);
            }
        }
        analysis.exhaustive |= self.handler_enum_constructor_patterns_exhaustive(rows);
        analysis.unreachable.sort_unstable();
        analysis.unreachable.dedup();
        let mut fuel = 131_072;
        let domains = first
            .patterns
            .iter()
            .map(|pattern| self.finite_pattern_values(&pattern.plan.subject, 0, &mut fuel))
            .collect::<Option<Vec<_>>>();
        let Some(domains) = domains else {
            return analysis;
        };
        let Some(assignments) = finite_pattern_products(domains, 4096) else {
            return analysis;
        };
        for (index, row) in rows.iter().enumerate() {
            let useful = assignments.iter().any(|assignment| {
                row.patterns.iter().zip(assignment).all(|(pattern, value)| {
                    pattern_decision_matches_value(&pattern.plan.decision, value) != Some(false)
                }) && !rows[..index].iter().any(|earlier| {
                    earlier
                        .patterns
                        .iter()
                        .zip(assignment)
                        .all(|(pattern, value)| {
                            pattern_decision_matches_value(&pattern.plan.decision, value) == Some(true)
                        })
                })
            });
            if !useful {
                analysis.unreachable.push(index);
            }
        }
        analysis.exhaustive |= assignments.iter().all(|assignment| {
            rows.iter().any(|row| {
                row.patterns.iter().zip(assignment).all(|(pattern, value)| {
                    pattern_decision_matches_value(&pattern.plan.decision, value) == Some(true)
                })
            })
        });
        analysis.unreachable.sort_unstable();
        analysis.unreachable.dedup();
        analysis
    }

    /// The operation analogue of enum constructor coverage.  A payload tuple
    /// is total when one enum column is partitioned by complete constructor
    /// rows and every other payload column is irrefutable in every row.  This
    /// is safe for unbounded sibling payloads without pretending to solve the
    /// general unbounded pattern-matrix problem.
    fn handler_enum_constructor_patterns_exhaustive(
        &self,
        rows: &[&ResolvedHandlerClause],
    ) -> bool {
        let Some(first) = rows.first() else {
            return false;
        };
        for column in 0..first.patterns.len() {
            if !rows.iter().all(|row| {
                row.patterns
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| *index != column)
                    .all(|(_, pattern)| !pattern.plan.refutable)
            }) {
                continue;
            }
            let patterns = rows
                .iter()
                .map(|row| &row.patterns[column].plan.decision)
                .collect::<Vec<_>>();
            if self.enum_constructor_decisions_exhaustive(
                &patterns,
                &first.patterns[column].plan.subject,
            ) {
                return true;
            }
        }
        false
    }

    fn enum_constructor_decisions_exhaustive(
        &self,
        patterns: &[&crate::pattern::PatternDecision],
        subject: &Type,
    ) -> bool {
        let Type::Nominal { definition, .. } = subject else {
            return false;
        };
        let Some(ElaboratedHeader::Nominal {
            layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
            ..
        }) = self.signatures.definitions.get(definition)
        else {
            return false;
        };
        variants.iter().enumerate().all(|(variant, _)| {
            patterns.iter().any(|pattern| {
                pattern_decision_covers_enum_constructor(pattern, *definition, variant as u32)
            })
        })
    }

    fn check_effects(&mut self, effects: &EffectRow, span: Span) {
        let effects = match self
            .inference
            .zonk_effects_allowing_generic_tail(effects.clone())
        {
            Ok(effects) => effects,
            Err(_) => {
                // An implicit row argument is inferred from the caller's
                // outward contract. Solve it before reporting an unresolved
                // row: this is the row analogue of using an expected type to
                // finish an otherwise unconstrained type variable.
                if self
                    .inference
                    .constrain_effect_subset(effects.clone(), self.declared_effects.clone())
                    .is_ok()
                {
                    match self
                        .inference
                        .zonk_effects_allowing_generic_tail(effects.clone())
                    {
                        Ok(effects) => effects,
                        Err(_) => {
                            self.error(span, "G4155", "call has an unresolved outward effect row");
                            self.recovered = true;
                            return;
                        }
                    }
                } else {
                    self.error(span, "G4155", "call has an unresolved outward effect row");
                    self.recovered = true;
                    return;
                }
            }
        };
        let mut effects = effects;
        // A callable's row binder is instantiated at this call site.  This
        // compact frontend has no explicit row argument syntax, so the
        // caller's declared residual is the contextual argument; a closed
        // caller selects the empty residual.  This also keeps binder slot
        // numbers local to their declarations rather than accidentally
        // requiring a callee's `e` to share the caller's numeric index.
        if matches!(effects.tail, Some(crate::EffectTail::Generic(_))) {
            effects.tail = self.declared_effects.tail;
        }
        if let Some(tail) = effects.tail
            && self
                .inference
                .zonk_effects_allowing_generic_tail(self.declared_effects.clone())
                .ok()
                .and_then(|declared| declared.tail)
                != Some(tail)
        {
            self.error(
                span,
                "G4155",
                "call has an outward effect-row tail not admitted by this callable",
            );
            self.recovered = true;
            return;
        }
        // Preserve a symbolic associated row when the caller has supplied
        // the *same lexical evidence*.  A generic forwarding function such
        // as
        //
        //   relay<T>() / { <T as Capability>::Effects }
        //       where T: Capability
        //
        // may call another callable with that exact contract without choosing
        // an implementation for `T`.  Requiring concrete normalization here
        // would reject valid effect polymorphism (and tempt a later phase to
        // guess an impl).  `constrain_effect_subset` compares named members,
        // delayed associated projections, and the one permitted tail with the
        // same inference discipline as ordinary generic arguments.  A
        // concrete projection which is only compatible after selection simply
        // falls through to the normalization path below; executable instance
        // construction still requires that selection to close the row.
        if self
            .inference
            .constrain_effect_subset(effects.clone(), self.declared_effects.clone())
            .is_ok()
        {
            return;
        }
        let mut projections = std::mem::take(&mut effects.projections);
        while let Some(projection) = projections.pop() {
            if !projection_is_concrete(&projection.subject)
                || !projection
                    .trait_arguments
                    .iter()
                    .all(generic_argument_is_concrete)
                || !projection
                    .item_arguments
                    .iter()
                    .all(generic_argument_is_selectable_effect_projection)
            {
                self.error(
                    span,
                    "G4155",
                    "call has an unresolved associated effect-row projection",
                );
                self.recovered = true;
                return;
            }
            match self
                .trait_query()
                .normalize_associated_effect_row_application(
                    TraitGoal {
                        relation: crate::ElaboratedTraitReference {
                            definition: projection.trait_definition,
                            arguments: projection.trait_arguments.clone(),
                        },
                        subject: *projection.subject,
                    },
                    &projection.name,
                    &projection.item_arguments,
                ) {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    effects.effects.extend(row.effects);
                    projections.extend(row.projections);
                    match (effects.tail, row.tail) {
                        (None, tail) => effects.tail = tail,
                        (Some(left), Some(right)) if left == right => {}
                        (Some(_), None) => {}
                        (Some(_), Some(_)) => {
                            self.error(
                                span,
                                "G4155",
                                "normalized effect row has a conflicting outward tail",
                            );
                            self.recovered = true;
                            return;
                        }
                    }
                    if let Some(tail) = effects.tail
                        && self
                            .inference
                            .zonk_effects_allowing_generic_tail(self.declared_effects.clone())
                            .ok()
                            .and_then(|declared| declared.tail)
                            != Some(tail)
                    {
                        self.error(span, "G4155", "normalized effect row remains open");
                        self.recovered = true;
                        return;
                    }
                }
                _ => {
                    self.error(
                        span,
                        "G4155",
                        "associated effect-row projection cannot be normalized",
                    );
                    self.recovered = true;
                    return;
                }
            }
        }
        for effect in &effects.effects {
            self.check_effect_instance(effect, None, span);
        }
    }
    fn check_effect_instance(
        &mut self,
        effect: &EffectInstance,
        operation: Option<u32>,
        span: Span,
    ) {
        let handled_operation = operation.is_some_and(|operation| {
            self.handled_operations
                .contains(&(effect.clone(), operation))
        });
        if !self.declared_effects.effects.contains(effect)
            && !self.handled_effects.contains(effect)
            && !self.effect_is_covered_by_active_operations(effect)
            && !handled_operation
        {
            self.error(
                span,
                "G4155",
                "performed effect is absent from this callable's declared outward row",
            );
            self.recovered = true;
        }
    }
    /// Direct calls retain their caller-owned substitution on the function
    /// Core value. This is the narrowest point at which ordinary callable
    /// bounds can be checked: argument unification has constrained the
    /// variables, while no unresolved inference state has crossed into a
    /// persistence boundary.
    fn check_call_where_bounds(&mut self, callee: CoreId, arguments: &[CoreId], span: Span) {
        let actual_arguments = arguments.to_vec();
        let (definition, generic_arguments) = match &self.expressions[callee.0 as usize].kind {
            CoreKind::Function {
                definition,
                arguments,
                ..
            } => (*definition, arguments.clone()),
            _ => return,
        };
        let Ok(signature) = self
            .signatures
            .instantiate_callable_generic(definition, &generic_arguments)
        else {
            self.error(
                span,
                "G4140",
                "direct call lost its frozen callable signature",
            );
            self.recovered = true;
            return;
        };
        self.check_callable_contract_bounds(signature, Some(&actual_arguments), span);
    }

    /// Infer direct-call generics that appear only in frozen where-clause
    /// evidence from an exactly matching lexical bound.  Ordinary parameter
    /// inference deliberately cannot discover `B` in `L: Label<B>` or the
    /// row binder in a callable `Effects` equality because neither inhabits
    /// the runtime value representation of `L` or `F`.
    fn infer_direct_call_contract_from_ambient_bounds(
        &mut self,
        callee: CoreId,
        call_arguments: &[CoreId],
    ) {
        let (definition, arguments) = match &self.expressions[callee.0 as usize].kind {
            CoreKind::Function {
                definition,
                arguments,
                ..
            } => (*definition, arguments.clone()),
            _ => return,
        };
        let Ok(signature) = self
            .signatures
            .instantiate_callable_generic(definition, &arguments)
        else {
            return;
        };
        let ambient_bounds = self.ambient_where_bounds.clone();
        let ambient_type_bindings = self.ambient_callable_type_bindings.clone();
        let ambient_effect_bindings = self.ambient_callable_effect_bindings.clone();
        for (subject, relation) in &signature.where_bounds {
            let subject = self.inference.zonk(subject.clone()).unwrap_or_else(|_| subject.clone());
            // A concrete label value is represented at the call boundary by
            // its escaping callable shape.  Unlike an ambient generic label
            // bound, this direct argument contains the payload type that can
            // solve a generic used only in `L: Label<B>` (the `S` in
            // `try<T, E, S, L>` is the canonical case).  Recover that
            // evidence before generic sealing rather than forcing std to
            // artificially tie the propagated function's Ok type to `T`.
            if crate::is_intrinsic_label_trait(relation)
                && let [GenericArgument::Type(expected_payload)] = relation.arguments.as_slice()
            {
                // A generic `L` has been unified from its value parameter by
                // this point, but retain the actual Core operand as the
                // authoritative direct-evidence source. It also avoids
                // depending on whether the generic inference table exposes
                // the callable's structural shape before where-bound
                // checking starts.
                let actual_label = signature
                    .parameters
                    .iter()
                    .zip(call_arguments)
                    .find_map(|(parameter, argument)| {
                        self.inference
                            .zonk(parameter.clone())
                            .is_ok_and(|parameter| parameter == subject)
                            .then(|| self.expressions[argument.0 as usize].ty.clone())
                    })
                    .or_else(|| {
                        // A direct label function normally has one matching
                        // value parameter above. During recovery or when an
                        // alias has delayed that relation, use the unique
                        // terminal callable argument as the same evidence;
                        // do not guess when a call contains several labels.
                        let mut candidates = call_arguments
                            .iter()
                            .filter_map(|argument| {
                                let ty = self.expressions[argument.0 as usize].ty.clone();
                                matches!(&ty, Type::Callable { result, .. } if matches!(result.as_ref(), Type::Never))
                                    .then_some(ty)
                            });
                        let candidate = candidates.next();
                        candidates.next().is_none().then_some(candidate).flatten()
                    });
                if let Some(Type::Callable {
                    parameters: actual_parameters,
                    result: actual_result,
                    ..
                }) = actual_label
                    && let [actual_payload] = actual_parameters.as_slice()
                    && matches!(actual_result.as_ref(), Type::Never)
                {
                    let _ = self
                        .inference
                        .unify(expected_payload.clone(), actual_payload.clone());
                }
            }
            let matches = ambient_bounds
                .iter()
                .filter(|(ambient_subject, ambient_relation)| {
                    ambient_relation.definition == relation.definition
                        && ambient_relation.arguments.len() == relation.arguments.len()
                        && self
                            .inference
                            .zonk(ambient_subject.clone())
                            .is_ok_and(|ambient_subject| ambient_subject == subject)
                })
                .collect::<Vec<_>>();
            let [(matched_subject, matched_relation)] = matches.as_slice() else {
                continue;
            };
            let matched_subject = (*matched_subject).clone();
            let matched_relation = (*matched_relation).clone();
            let _ = self.inference.unify_generic_arguments(
                relation.arguments.clone(),
                matched_relation.arguments.clone(),
            );
            for binding in signature.where_associated_type_bindings.clone() {
                if binding.relation.definition != relation.definition
                    || !self
                        .inference
                        .zonk(binding.subject.clone())
                        .is_ok_and(|binding_subject| binding_subject == subject)
                {
                    continue;
                }
                let mut candidate = None;
                for ambient in &ambient_type_bindings {
                    if ambient.name != binding.name
                        || ambient.item_generic_kinds != binding.item_generic_kinds
                        || ambient.relation != matched_relation
                        || !self
                            .inference
                            .zonk(ambient.subject.clone())
                            .is_ok_and(|ambient_subject| ambient_subject == matched_subject)
                    {
                        continue;
                    }
                    if candidate.replace(ambient).is_some() {
                        candidate = None;
                        break;
                    }
                }
                if let Some(ambient) = candidate {
                    let _ = self.inference.unify(binding.value, ambient.value.clone());
                }
            }
            for binding in signature.where_associated_effect_bindings.clone() {
                if binding.relation.definition != relation.definition
                    || !self
                        .inference
                        .zonk(binding.subject.clone())
                        .is_ok_and(|binding_subject| binding_subject == subject)
                {
                    continue;
                }
                let mut candidate = None;
                for ambient in &ambient_effect_bindings {
                    if ambient.name != binding.name
                        || ambient.item_generic_kinds != binding.item_generic_kinds
                        || ambient.relation != matched_relation
                        || !self
                            .inference
                            .zonk(ambient.subject.clone())
                            .is_ok_and(|ambient_subject| ambient_subject == matched_subject)
                    {
                        continue;
                    }
                    if candidate.replace(ambient).is_some() {
                        candidate = None;
                        break;
                    }
                }
                if let Some(ambient) = candidate {
                    let _ = self
                        .inference
                        .constrain_effect_subset(binding.value, ambient.value.clone());
                }
            }
        }
    }

    /// Verify the whole frozen callable contract after argument inference has
    /// constrained it.  A trait predicate is only one part of that contract:
    /// associated type and effect-row equalities are obligations too.
    fn check_callable_contract_bounds(
        &mut self,
        signature: CallableSignature,
        arguments: Option<&[CoreId]>,
        span: Span,
    ) {
        // RunsIn is not an ordinary globally-selectable trait.  Its concrete
        // environment type is minted by the closure elaborator, so bind that
        // evidence before attempting to zonk the rest of this call contract.
        // In particular, this lets an `E` which appears only in a RunsIn
        // relation become the unnameable environment of the actual closure.
        self.check_intrinsic_runs_in_bindings(&signature, arguments, span);
        self.check_intrinsic_environment_bounds(signature.where_bounds.clone(), span);
        self.check_where_bounds(signature.where_bounds.clone(), span);
        self.check_intrinsic_callable_bindings(
            signature.where_bounds.clone(),
            signature.where_associated_type_bindings.clone(),
            signature.where_associated_effect_bindings.clone(),
            span,
            true,
        );
        self.check_nonintrinsic_associated_bindings(
            signature.where_associated_type_bindings,
            signature.where_associated_effect_bindings,
            span,
        );
    }

    fn check_nonintrinsic_associated_bindings(
        &mut self,
        type_bindings: Vec<crate::ElaboratedAssociatedTypeBinding>,
        effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
        span: Span,
    ) {
        for binding in type_bindings {
            if crate::is_intrinsic_callable_trait(&binding.relation)
                || crate::is_intrinsic_runs_in_trait(&binding.relation)
            {
                continue;
            }
            let Some((subject, relation, item_arguments, value)) =
                self.zonk_associated_type_binding(&binding)
            else {
                self.error(
                    span,
                    "G4141",
                    "cannot prove a callable associated type equality with unresolved arguments",
                );
                self.recovered = true;
                continue;
            };
            if self.ambient_associated_type_binding_proves(
                &binding,
                &subject,
                &relation,
                &item_arguments,
                &value,
            ) {
                continue;
            }
            let answer = self.trait_query().normalize_associated_type_application(
                TraitGoal { relation, subject },
                &binding.name,
                &item_arguments,
            );
            if !matches!(answer, TraitProjectionAnswer::Normalized { ty, .. } if ty == value) {
                self.error(
                    span,
                    "G4143",
                    "no implementation satisfies a required callable associated type equality",
                );
                self.recovered = true;
            }
        }
        for binding in effect_bindings {
            if crate::is_intrinsic_callable_trait(&binding.relation)
                || crate::is_intrinsic_runs_in_trait(&binding.relation)
            {
                continue;
            }
            let Some((subject, relation, item_arguments, value)) =
                self.zonk_associated_effect_binding(&binding)
            else {
                self.error(
                    span,
                    "G4141",
                    "cannot prove a callable associated effect-row equality with unresolved arguments",
                );
                self.recovered = true;
                continue;
            };
            if self.ambient_associated_effect_binding_proves(
                &binding,
                &subject,
                &relation,
                &item_arguments,
                &value,
            ) {
                continue;
            }
            let answer = self
                .trait_query()
                .normalize_associated_effect_row_application(
                    TraitGoal { relation, subject },
                    &binding.name,
                    &item_arguments,
                );
            let proves_binding = match answer {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    // A selected outer GAT can itself expose another selected
                    // effect-row projection.  Its concrete subject may carry
                    // the caller's open row binder, which is safe to retain
                    // but not concrete enough for the raw solver result to
                    // close. Follow only the selectable projection boundary
                    // used by callable signatures before comparing the
                    // equality witness.
                    self.normalize_selectable_effect_row(row)
                        == self.normalize_selectable_effect_row(value)
                }
                _ => false,
            };
            if !proves_binding {
                self.error(
                    span,
                    "G4143",
                    "no implementation satisfies a required callable associated effect-row equality",
                );
                self.recovered = true;
            }
        }
    }

    fn zonk_associated_type_binding(
        &mut self,
        binding: &crate::ElaboratedAssociatedTypeBinding,
    ) -> Option<(
        Type,
        crate::ElaboratedTraitReference,
        Vec<GenericArgument>,
        Type,
    )> {
        Some((
            self.inference.zonk(binding.subject.clone()).ok()?,
            self.zonk_trait_reference(binding.relation.clone())?,
            self.zonk_generic_arguments(binding.item_arguments.clone())?,
            self.inference.zonk(binding.value.clone()).ok()?,
        ))
    }

    fn zonk_associated_effect_binding(
        &mut self,
        binding: &crate::ElaboratedAssociatedEffectBinding,
    ) -> Option<(
        Type,
        crate::ElaboratedTraitReference,
        Vec<GenericArgument>,
        EffectRow,
    )> {
        Some((
            self.inference.zonk(binding.subject.clone()).ok()?,
            self.zonk_trait_reference(binding.relation.clone())?,
            self.zonk_generic_arguments(binding.item_arguments.clone())?,
            self.inference
                .zonk_effects_allowing_generic_tail(binding.value.clone())
                .ok()?,
        ))
    }

    fn zonk_trait_reference(
        &mut self,
        relation: crate::ElaboratedTraitReference,
    ) -> Option<crate::ElaboratedTraitReference> {
        Some(crate::ElaboratedTraitReference {
            definition: relation.definition,
            arguments: self.zonk_generic_arguments(relation.arguments)?,
        })
    }

    fn zonk_generic_arguments(
        &mut self,
        arguments: Vec<GenericArgument>,
    ) -> Option<Vec<GenericArgument>> {
        arguments
            .into_iter()
            .map(|argument| self.inference.zonk_generic_argument(argument).ok())
            .collect()
    }

    fn ambient_associated_type_binding_proves(
        &mut self,
        binding: &crate::ElaboratedAssociatedTypeBinding,
        subject: &Type,
        relation: &crate::ElaboratedTraitReference,
        item_arguments: &[GenericArgument],
        value: &Type,
    ) -> bool {
        self.ambient_callable_type_bindings
            .clone()
            .iter()
            .any(|ambient| {
                ambient.name == binding.name
                    && ambient.item_generic_kinds == binding.item_generic_kinds
                    && self.zonk_associated_type_binding(ambient).is_some_and(
                        |(ambient_subject, ambient_relation, ambient_arguments, ambient_value)| {
                            ambient_subject == *subject
                                && ambient_relation == *relation
                                && ambient_arguments == item_arguments
                                && ambient_value == *value
                        },
                    )
            })
    }

    fn ambient_associated_effect_binding_proves(
        &mut self,
        binding: &crate::ElaboratedAssociatedEffectBinding,
        subject: &Type,
        relation: &crate::ElaboratedTraitReference,
        item_arguments: &[GenericArgument],
        value: &EffectRow,
    ) -> bool {
        self.ambient_callable_effect_bindings
            .clone()
            .iter()
            .any(|ambient| {
                ambient.name == binding.name
                    && ambient.item_generic_kinds == binding.item_generic_kinds
                    && self.zonk_associated_effect_binding(ambient).is_some_and(
                        |(ambient_subject, ambient_relation, ambient_arguments, ambient_value)| {
                            ambient_subject == *subject
                                && ambient_relation == *relation
                                && ambient_arguments == item_arguments
                                && ambient_value == *value
                        },
                    )
            })
    }
    fn check_where_bounds(
        &mut self,
        bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
        span: Span,
    ) {
        let assumptions = self.ambient_trait_solver_assumptions();
        let mut failed = false;
        for (subject, relation) in bounds {
            // `RunsIn` is compiler-generated evidence carried by a concrete
            // closure environment, rather than a globally selectable trait
            // implementation. Direct-call checking below validates that
            // evidence against the actual callable argument.
            if crate::is_intrinsic_runs_in_trait(&relation)
                || crate::is_intrinsic_environment_trait(&relation)
            {
                continue;
            }
            // `Fn` is a compiler-owned structural contract, not an ordinary
            // implementation lookup. Its parameter, result, and effect
            // equalities are checked below from the concrete callable value;
            // asking the implementation solver for a synthetic `Fn` impl
            // rejects valid contextual blocks such as canonical `if` arms.
            if crate::is_intrinsic_callable_trait(&relation) {
                continue;
            }
            let subject = match self.inference.zonk(subject) {
                Ok(subject) => subject,
                Err(_) => {
                    self.error(
                        span,
                        "G4141",
                        "cannot prove a callable trait bound with unresolved type arguments",
                    );
                    self.recovered = true;
                    failed = true;
                    continue;
                }
            };
            let arguments = relation
                .arguments
                .into_iter()
                .map(|argument| match argument {
                    crate::GenericArgument::Type(argument) => self
                        .inference
                        .zonk(argument)
                        .map(crate::GenericArgument::Type),
                    argument => Ok(argument),
                })
                .collect::<Result<Vec<_>, _>>();
            let Ok(arguments) = arguments else {
                self.error(
                    span,
                    "G4141",
                    "cannot prove a callable trait bound with unresolved type arguments",
                );
                self.recovered = true;
                failed = true;
                continue;
            };
            let goal = TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: relation.definition,
                    arguments,
                },
                subject,
            };
            // `Use<Q>` is likewise structural for closed values.  The
            // frozen interface owns its sole principal interval, including
            // scalars and `()`, so this proof must not depend on a fictional
            // source implementation being selected by the general solver.
            if goal.relation.definition == crate::resolution::language_use_trait_definition()
                && let [GenericArgument::ConstQuantity(required)] = goal.relation.arguments.as_slice()
                && self
                    .signatures
                    .principal_use_interval_with_solver(&goal.subject, &self.trait_solver)
                    .is_some_and(|principal| principal.contains(*required))
            {
                continue;
            }
            match self
                .trait_query()
                .solve_with_assumptions(goal, &assumptions)
            {
                TraitAnswer::Proven { .. } => {}
                TraitAnswer::Refuted { .. } => {
                    self.error(
                        span,
                        "G4142",
                        "callable trait bound is explicitly refuted by a negative implementation",
                    );
                    failed = true;
                }
                TraitAnswer::NoSolution => {
                    self.error(
                        span,
                        "G4143",
                        "no implementation proves a required callable trait bound",
                    );
                    failed = true;
                }
                TraitAnswer::Ambiguous => {
                    self.error(span, "G4144", "required callable trait bound is ambiguous");
                    failed = true;
                }
                TraitAnswer::Overflow => {
                    self.error(
                        span,
                        "G4145",
                        "required callable trait bound exceeded the solver limit",
                    );
                    failed = true;
                }
            }
        }
        if failed {
            self.recovered = true;
        }
    }

    fn check_intrinsic_callable_bindings(
        &mut self,
        bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
        type_bindings: Vec<crate::ElaboratedAssociatedTypeBinding>,
        effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
        span: Span,
        defer_unresolved: bool,
    ) {
        for (subject, relation) in bounds {
            if !crate::is_intrinsic_callable_trait(&relation) {
                continue;
            }
            let resolved = self.inference.resolve(subject.clone());
            if matches!(resolved, Type::Infer(_)) {
                if defer_unresolved {
                    self.pending_callable_bounds.push(PendingCallableBound {
                        subject,
                        relation,
                        type_bindings: type_bindings.clone(),
                        effect_bindings: effect_bindings.clone(),
                        span,
                    });
                } else {
                    self.error(span, "G4141", "cannot prove `Fn` evidence for an unresolved argument type");
                    self.recovered = true;
                }
                continue;
            }
            let Type::Callable {
                safety,
                parameters,
                result,
                effects,
                ..
            } = resolved
            else {
                // A terminal/recovered argument never supplies a runtime value.
                // Every other non-structural callable needs exact lexical
                // evidence; skipping it admits scalars as generic callbacks.
                if !matches!(resolved, Type::Error | Type::Never)
                    && !self.ambient_intrinsic_callable_bound_proves(
                        &resolved, &relation, &type_bindings, &effect_bindings,
                    )
                {
                    self.error(span, "G4105", "argument does not supply the required `Fn` evidence");
                    self.recovered = true;
                }
                continue;
            };
            if safety != crate::Safety::Safe {
                self.error(span, "G4200", "unsafe callable cannot supply safe `Fn` evidence");
                self.recovered = true;
                continue;
            }
            let inputs = match relation.arguments.as_slice() {
                [crate::GenericArgument::Type(Type::Tuple(inputs))] => inputs.clone(),
                [crate::GenericArgument::Type(Type::Unit)] => vec![],
                _ => {
                    self.error(
                        span,
                        "G4164",
                        "intrinsic `Fn` requires a tuple input argument",
                    );
                    self.recovered = true;
                    continue;
                }
            };
            if self.inference.unify(Type::Tuple(inputs), Type::Tuple(parameters)).is_err() {
                self.error(
                    span,
                    "G4166",
                    "intrinsic `Fn` input tuple does not match callable parameters",
                );
                self.recovered = true;
            }
            let outputs = type_bindings
                .iter()
                .filter(|binding| {
                    binding.subject == subject
                        && binding.relation == relation
                        && binding.name == "Output"
                        && binding.item_arguments.is_empty()
                })
                .collect::<Vec<_>>();
            if let [binding] = outputs.as_slice()
                && self
                    .inference
                    .unify(binding.value.clone(), *result.clone())
                    .is_err()
            {
                self.error(
                    span,
                    "G4167",
                    "intrinsic `Fn` Output equality does not match callable result",
                );
                self.recovered = true;
            }
            let rows = effect_bindings
                .iter()
                .filter(|binding| {
                    binding.subject == subject
                        && binding.relation == relation
                        && binding.name == "Effects"
                        && binding.item_arguments.is_empty()
                })
                .collect::<Vec<_>>();
            if let [binding] = rows.as_slice()
                && (self
                    .inference
                    .constrain_effect_subset(binding.value.clone(), effects.clone())
                    .is_err()
                    || self
                        .inference
                        .constrain_effect_subset(effects.clone(), binding.value.clone())
                        .is_err())
            {
                self.error(
                    span,
                    "G4168",
                    "intrinsic `Fn` Effects equality does not match callable effects",
                );
                self.recovered = true;
            }
        }
    }

    fn ambient_intrinsic_callable_bound_proves(
        &mut self,
        subject: &Type,
        relation: &crate::ElaboratedTraitReference,
        type_bindings: &[crate::ElaboratedAssociatedTypeBinding],
        effect_bindings: &[crate::ElaboratedAssociatedEffectBinding],
    ) -> bool {
        let Ok(arguments) = relation.arguments.iter().cloned()
            .map(|argument| self.inference.zonk_generic_argument(argument))
            .collect::<Result<Vec<_>, _>>() else { return false; };
        let required = crate::ElaboratedTraitReference {
            definition: relation.definition,
            arguments,
        };
        if !self.ambient_trait_solver_assumptions().iter()
            .any(|goal| goal.subject == *subject && goal.relation == required)
        {
            return false;
        }
        for binding in type_bindings.iter().filter(|binding| binding.relation == *relation) {
            let binding_subject = self.inference.resolve(binding.subject.clone());
            if binding_subject != *subject { continue; }
            let Some((subject, relation, arguments, value)) = self.zonk_associated_type_binding(binding) else { return false; };
            if !self.ambient_associated_type_binding_proves(binding, &subject, &relation, &arguments, &value) {
                return false;
            }
        }
        for binding in effect_bindings.iter().filter(|binding| binding.relation == *relation) {
            let binding_subject = self.inference.resolve(binding.subject.clone());
            if binding_subject != *subject { continue; }
            let Some((subject, relation, arguments, value)) = self.zonk_associated_effect_binding(binding) else { return false; };
            if !self.ambient_associated_effect_binding_proves(binding, &subject, &relation, &arguments, &value) {
                return false;
            }
        }
        true
    }
    fn check_intrinsic_runs_in_bindings(
        &mut self,
        signature: &CallableSignature,
        arguments: Option<&[CoreId]>,
        span: Span,
    ) {
        let Some(arguments) = arguments else {
            return;
        };
        for (subject, relation) in &signature.where_bounds {
            if !crate::is_intrinsic_runs_in_trait(relation) {
                continue;
            }
            let Ok(subject) = self.inference.zonk(subject.clone()) else {
                continue;
            };
            let argument =
                signature
                    .parameters
                    .iter()
                    .enumerate()
                    .find_map(|(index, parameter)| {
                        self.inference
                            .zonk(parameter.clone())
                            .ok()
                            .filter(|parameter| *parameter == subject)
                            .and_then(|_| arguments.get(index).copied())
                    });
            let Some(argument) = argument else {
                continue;
            };
            let environment = match &self.expressions[argument.0 as usize].kind {
                CoreKind::Closure { environment, .. } => Some(environment.clone()),
                // A named function item is a compiler-created callable with
                // the canonical empty physical environment. It therefore
                // carries the same unit RunsIn relation as a noncapturing
                // closure, even though its nominal callable identity lives in
                // the frozen declaration table rather than a Core closure.
                CoreKind::Function { .. } => None,
                _ => {
                    self.error(
                        span,
                        "G4188",
                        "intrinsic `RunsIn` requires compiler-generated callable environment evidence",
                    );
                    self.recovered = true;
                    continue;
                }
            };
            let callable = self.expressions[argument.0 as usize].ty.clone();
            let Ok(Type::Callable {
                parameters, result, ..
            }) = self.inference.zonk(callable)
            else {
                self.error(
                    span,
                    "G4188",
                    "compiler-generated `RunsIn` evidence is attached to a non-callable value",
                );
                self.recovered = true;
                continue;
            };
            let Some((access, inputs)) = intrinsic_runs_in_arguments(relation) else {
                self.error(
                    span,
                    "G4188",
                    "intrinsic `RunsIn` requires an environment access and tuple input argument",
                );
                self.recovered = true;
                continue;
            };
            // The unit type is the sole public spelling for the canonical
            // empty environment. Every nonempty layout receives an opaque
            // nominal input and post-state identity.
            let is_empty_environment = environment
                .as_ref()
                .is_none_or(|value| value.captures.is_empty());
            let environment_type = if is_empty_environment {
                Type::Unit
            } else {
                generated_environment_type(
                    environment
                        .as_ref()
                        .expect("nonempty closure must retain its environment")
                        .brand,
                    false,
                )
            };
            let after_type = if is_empty_environment {
                Type::Unit
            } else {
                generated_environment_type(
                    environment
                        .as_ref()
                        .expect("nonempty closure must retain its environment")
                        .brand,
                    true,
                )
            };
            self.remember_generated_environment_type(&environment_type);
            self.remember_generated_environment_type(&after_type);
            let access = self.match_runs_in_access(access, &environment_type, span);
            let inputs_match = self.match_runs_in_inputs(inputs, &parameters);
            let output_bindings = signature
                .where_associated_type_bindings
                .iter()
                .filter(|binding| {
                    binding.relation == *relation
                        && binding.name == "Output"
                        && binding.item_arguments.is_empty()
                })
                .cloned()
                .collect::<Vec<_>>();
            let mut output_matches = true;
            for binding in output_bindings {
                if self
                    .inference
                    .zonk(binding.subject)
                    .is_ok_and(|value| value == subject)
                {
                    output_matches &= self.inference.unify(binding.value, *result.clone()).is_ok();
                }
            }
            let expected_after = match access {
                Some(RunsInAccess::Owned) => after_type,
                Some(RunsInAccess::Shared | RunsInAccess::Unique) => environment_type,
                None => Type::Error,
            };
            let access_matches_captures = match (access, environment.as_ref()) {
                (Some(RunsInAccess::Owned), _) | (_, None) => true,
                (Some(RunsInAccess::Shared), Some(environment)) => environment
                    .captures
                    .iter()
                    .all(|capture| {
                        matches!(
                            capture.mode,
                            CaptureMode::SharedBorrow | CaptureMode::Copy
                        )
                    }),
                (Some(RunsInAccess::Unique), Some(environment)) => environment
                    .captures
                    .iter()
                    .all(|capture| capture.mode != CaptureMode::Move),
                (None, _) => false,
            };
            let after_bindings = signature
                .where_associated_type_bindings
                .iter()
                .filter(|binding| {
                    binding.relation == *relation
                        && binding.name == "After"
                        && binding.item_arguments.is_empty()
                })
                .cloned()
                .collect::<Vec<_>>();
            let mut after_matches = true;
            for binding in after_bindings {
                if self
                    .inference
                    .zonk(binding.subject)
                    .is_ok_and(|value| value == subject)
                {
                    after_matches &= self
                        .inference
                        .unify(binding.value, expected_after.clone())
                        .is_ok();
                }
            }
            if access.is_none()
                || !access_matches_captures
                || !inputs_match
                || !output_matches
                || !after_matches
            {
                self.error(
                    span,
                    "G4188",
                    "intrinsic `RunsIn` evidence does not match the callable's sealed environment",
                );
                self.recovered = true;
            }
        }
    }

    /// Validate intrinsic `Environment` declarations after RunsIn has bound
    /// their otherwise-unnameable type variables to the sealed closure
    /// environment.  These facts have no source implementation and therefore
    /// must never be delegated to ordinary trait selection.
    fn check_intrinsic_environment_bounds(
        &mut self,
        bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
        span: Span,
    ) {
        for (subject, relation) in bounds {
            if !crate::is_intrinsic_environment_trait(&relation) {
                continue;
            }
            let Ok(subject) = self.inference.zonk(subject) else {
                // A generic environment not used by this direct call remains
                // a declaration-level promise; its caller is responsible for
                // supplying concrete RunsIn evidence.
                continue;
            };
            if !self.is_compiler_environment_type(&subject) {
                self.error(
                    span,
                    "G4188",
                    "intrinsic `Environment` evidence is only created for sealed compiler environments",
                );
                self.recovered = true;
            }
        }
    }

    fn match_runs_in_access(
        &mut self,
        access: Type,
        environment: &Type,
        _span: Span,
    ) -> Option<RunsInAccess> {
        match access {
            Type::Reference {
                mutability,
                referent,
                ..
            } => self
                .inference
                .unify(*referent, environment.clone())
                .ok()
                .map(|_| match mutability {
                    Mutability::Shared => RunsInAccess::Shared,
                    Mutability::Unique => RunsInAccess::Unique,
                }),
            access => self
                .inference
                .unify(access, environment.clone())
                .ok()
                .map(|_| RunsInAccess::Owned),
        }
    }

    fn match_runs_in_inputs(&mut self, inputs: Type, parameters: &[Type]) -> bool {
        match inputs {
            Type::Unit => parameters.is_empty(),
            Type::Tuple(inputs) if inputs.len() == parameters.len() => inputs
                .into_iter()
                .zip(parameters.iter().cloned())
                .all(|(input, parameter)| self.inference.unify(input, parameter).is_ok()),
            _ => false,
        }
    }

    fn remember_generated_environment_type(&mut self, ty: &Type) {
        if let Type::Nominal { definition, .. } = ty {
            self.generated_environment_types.insert(*definition);
        }
    }

    fn is_compiler_environment_type(&self, ty: &Type) -> bool {
        matches!(ty, Type::Unit)
            || matches!(ty, Type::Nominal { definition, arguments } if arguments.is_empty()
                && self.generated_environment_types.contains(definition))
    }
    /// Freeze the declaration-owned trait contracts into scoped solver
    /// assumptions.  The solver expands their supertrait closure, while this
    /// elaborator keeps them local to the body that declared the bounds.
    fn ambient_trait_solver_assumptions(&mut self) -> Vec<TraitGoal> {
        self.ambient_where_bounds
            .clone()
            .into_iter()
            .filter_map(|(subject, relation)| {
                let subject = self.inference.zonk(subject).ok()?;
                let arguments = relation
                    .arguments
                    .into_iter()
                    .map(|argument| match argument {
                        GenericArgument::Type(argument) => {
                            self.inference.zonk(argument).map(GenericArgument::Type)
                        }
                        argument => Ok(argument),
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .ok()?;
                Some(TraitGoal {
                    relation: crate::ElaboratedTraitReference {
                        definition: relation.definition,
                        arguments,
                    },
                    subject,
                })
            })
            .collect()
    }
    fn operators(&mut self, operands: Vec<ExprId>, operators: Vec<String>, span: Span) -> CoreId {
        self.operators_expected(operands, operators, span, None)
    }

    fn operators_expected(&mut self, operands: Vec<ExprId>, operators: Vec<String>, span: Span, expected: Option<Type>) -> CoreId {
        let Some(tree) = self.group_operators(operands, operators, span) else {
            return self.fail(span, "G4108", "malformed or unresolved operator chain");
        };
        self.grouped_operator(tree, expected, span)
    }

    fn group_operators(&mut self, operands: Vec<ExprId>, operators: Vec<String>, span: Span) -> Option<GroupedOperator> {
        if operands.len() != operators.len().checked_add(1)? { return None; }
        fn reduce(values: &mut Vec<GroupedOperator>, operators: &mut Vec<String>) -> Option<()> {
            let name = operators.pop()?;
            let right = values.pop()?;
            let left = values.pop()?;
            values.push(GroupedOperator::Apply { name, operands: vec![left, right] });
            Some(())
        }
        let mut source = operands.into_iter();
        let mut values = vec![GroupedOperator::Operand(source.next()?)];
        let mut pending = Vec::<String>::new();
        for (operator, operand) in operators.into_iter().zip(source) {
            let Some(fixity) = self.fixities.infix(&operator).cloned() else {
                self.error(span, "G4111", "operator has no unambiguous visible infix fixity declaration");
                return None;
            };
            while let Some(top) = pending.last() {
                let previous = self.fixities.infix(top)?;
                if previous.precedence == fixity.precedence && (previous.form == FixityForm::InfixNonAssociative || fixity.form == FixityForm::InfixNonAssociative) {
                    self.error(span, "G4112", "non-associative operators of equal precedence require parentheses");
                    return None;
                }
                if previous.precedence < fixity.precedence || (previous.precedence == fixity.precedence && fixity.form == FixityForm::InfixRight) { break; }
                reduce(&mut values, &mut pending)?;
            }
            pending.push(operator);
            values.push(GroupedOperator::Operand(operand));
        }
        while !pending.is_empty() { reduce(&mut values, &mut pending)?; }
        values.pop()
    }

    fn grouped_operator(&mut self, tree: GroupedOperator, expected: Option<Type>, span: Span) -> CoreId {
        let GroupedOperator::Apply { name, operands } = tree else {
            let GroupedOperator::Operand(id) = tree else { unreachable!() };
            return self.expression_expected(id, expected);
        };
        if let ResolutionState::Resolved(definition) = self.index.resolve_path(DefinitionNamespace::Value, self.module, &[name.clone()]) {
            let definition = self.signatures.value_alias_target(definition).unwrap_or(definition);
            if self.signatures.definitions.get(&definition).and_then(callable)
                .is_some_and(|signature| signature.parameters.len() == operands.len()) {
                let callee = self.path(vec![name], span);
                let Type::Callable { parameters, result, .. } = self.expressions[callee.0 as usize].ty.clone() else {
                    return self.fail(span, "G4117", "operator binding is not callable");
                };
                if let Some(expected) = expected {
                    let result_context = self.freshen_call_context_lifetimes(*result);
                    let _ = self.inference.unify(result_context, expected);
                }
                let mut arguments = vec![];
                for (operand, parameter) in operands.into_iter().zip(parameters) {
                    let expected = self.direct_bound_callable_contract(callee, &parameter).unwrap_or_else(|| parameter.clone());
                    let expected = self.inference.zonk(expected.clone()).unwrap_or(expected);
                    let argument = self.grouped_operator(operand, Some(expected), span);
                    let actual = self.expressions[argument.0 as usize].ty.clone();
                    let _ = self.inference.unify(parameter, actual);
                    arguments.push(argument);
                }
                return self.call(callee, arguments, span);
            }
        }
        let contextual_receiver = matches!(operands.first(), Some(GroupedOperator::Operand(id))
            if matches!(&self.body.expression(*id).kind, ExprKind::Literal(text) if literal_is_numeric(text)))
            && !expected.as_ref().is_some_and(|ty| matches!(ty, Type::Scalar(scalar) if scalar_is_numeric(*scalar)));
        let mut arguments = vec![];
        for operand in operands {
            // A source numeric literal is contextual, independent of which
            // operator name selected this ordinary receiver-based call.
            let context = match (&operand, arguments.first().copied()) {
                (GroupedOperator::Operand(id), None) if matches!(&self.body.expression(*id).kind,
                    ExprKind::Literal(text) if literal_is_numeric(text)) => expected.clone().filter(|ty| matches!(ty, Type::Scalar(scalar) if scalar_is_numeric(*scalar))),
                (GroupedOperator::Operand(id), Some(receiver)) if matches!(&self.body.expression(*id).kind,
                    ExprKind::Literal(text) if literal_is_numeric(text)) => Some(self.expressions[receiver as usize].ty.clone()),
                _ => None,
            };
            let argument = self.grouped_operator(operand, context, span);
            arguments.push(argument.0);
        }
        // Solve an otherwise uncontextualized numeric literal from the other
        // operand's concrete type before selecting a receiver implementation.
        // This updates only literal typing: emitted operand order is unchanged.
        if contextual_receiver && let [left, right] = arguments.as_slice() {
            let ty = self.expressions[*right as usize].ty.clone();
            if matches!(&ty, Type::Scalar(scalar) if scalar_is_numeric(*scalar)) {
                self.expressions[*left as usize].ty = ty;
            }
        }
        self.operator_trait_call(name, arguments.into_iter().map(CoreId).collect(), span)
    }

    fn alloc(&mut self, kind: CoreKind, ty: Type, span: Span) -> CoreId {
        let id = CoreId(self.expressions.len() as u32);
        self.expressions.push(CoreExpr { kind, ty, span });
        id
    }
    fn fail(&mut self, span: Span, code: &'static str, message: &'static str) -> CoreId {
        self.error(span, code, message);
        self.recovered = true;
        self.alloc(CoreKind::Error, Type::Error, span)
    }
    fn field_is_accessible(&self, field: &crate::signature::NominalField, span: Span) -> bool {
        field
            .private_authority
            .is_none_or(|authority| authority == span.file)
    }
    fn error(&mut self, span: Span, code: &'static str, message: &str) {
        self.diagnostics.push(CoreDiagnostic {
            code,
            span,
            message: message.into(),
        });
    }
}

fn type_generic_arity(value: &Type) -> u32 {
    fn argument_arity(value: &GenericArgument) -> u32 {
        match value {
            GenericArgument::Type(value) => type_generic_arity(value),
            GenericArgument::EffectRow(row) => row
                .effects
                .iter()
                .flat_map(|effect| effect.arguments.iter())
                .map(argument_arity)
                .chain(row.projections.iter().flat_map(|projection| {
                    std::iter::once(type_generic_arity(&projection.subject))
                        .chain(projection.trait_arguments.iter().map(argument_arity))
                        .chain(projection.item_arguments.iter().map(argument_arity))
                }))
                .max()
                .unwrap_or(0),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => std::iter::once(type_generic_arity(subject))
                .chain(trait_arguments.iter().map(argument_arity))
                .max()
                .unwrap_or(0),
            _ => 0,
        }
    }

    match value {
        Type::Generic(index) => index + 1,
        Type::Nominal { arguments, .. } => arguments.iter().map(argument_arity).max().unwrap_or(0),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => std::iter::once(type_generic_arity(subject))
            .chain(trait_arguments.iter().map(argument_arity))
            .chain(item_arguments.iter().map(argument_arity))
            .max()
            .unwrap_or(0),
        Type::Tuple(values) => values.iter().map(type_generic_arity).max().unwrap_or(0),
        Type::Array(value) => type_generic_arity(value),
        Type::Reference { referent, .. }
        | Type::RawPointer { pointee: referent, .. } => type_generic_arity(referent),
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => parameters
            .iter()
            .map(type_generic_arity)
            .chain(std::iter::once(type_generic_arity(result)))
            .chain(std::iter::once(argument_arity(
                &GenericArgument::EffectRow(effects.clone()),
            )))
            .max()
            .unwrap_or(0),
        _ => 0,
    }
}

fn collect_pattern_bindings(pattern: &CorePattern, bindings: &mut Vec<String>) {
    match pattern {
        CorePattern::Bind { name } => bindings.push(name.clone()),
        CorePattern::Tuple(values) => {
            for value in values {
                collect_pattern_bindings(value, bindings);
            }
        }
        CorePattern::Array { elements, .. } => {
            for element in elements {
                collect_pattern_bindings(element, bindings);
            }
        }
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            for field in fields {
                collect_pattern_bindings(&field.pattern, bindings);
            }
        }
        CorePattern::Any | CorePattern::Literal(_) | CorePattern::Error => {}
    }
}

fn collect_transfer_brands(expressions: &[CoreExpr], id: CoreId, brands: &mut Vec<LabelBrand>) {
    let Some(expression) = expressions.get(id.0 as usize) else {
        return;
    };
    if let CoreKind::Transfer { brand, .. } = expression.kind {
        brands.push(brand);
    }
    for child in core_children(&expression.kind) {
        collect_transfer_brands(expressions, child, brands);
    }
}

/// A first-class label capability may transfer only after crossing an
/// ordinary generic call.  Its Core body is therefore `Never` at the source
/// site even though the owning label regains its declared result at the
/// dynamic rejoin.  Preserve that result contract just as direct branded
/// transfers do, without treating a same-spelled label in another scope as
/// evidence.
fn contains_label_value_brand(expressions: &[CoreExpr], id: CoreId, target: LabelBrand) -> bool {
    let Some(expression) = expressions.get(id.0 as usize) else {
        return false;
    };
    matches!(expression.kind, CoreKind::LabelValue { brand } if brand == target)
        || core_children(&expression.kind)
            .into_iter()
            .any(|child| contains_label_value_brand(expressions, child, target))
}

/// Align the lifetime leaves of two structurally corresponding types while
/// leaving ordinary type inference to [`InferContext`]. `depth` counts nested
/// callable binders below the callable being invoked: a bound region at that
/// exact depth belongs to the opened callable; shallower bounds are rigid
/// inner HRTBs and deeper bounds name an outer binder that cannot escape this
/// instantiation.
fn align_lifetime_types(
    expected: &Type,
    actual: &Type,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<Type, LifetimeError> {
    match (expected, actual) {
        (
            Type::Reference {
                mutability: expected_mutability,
                lifetime: expected_lifetime,
                referent: expected_referent,
            },
            Type::Reference {
                mutability: actual_mutability,
                lifetime: actual_lifetime,
                referent: actual_referent,
            },
        ) if expected_mutability == actual_mutability => {
            bind_lifetime(
                *expected_lifetime,
                *actual_lifetime,
                substitution,
                mode,
                depth,
            )?;
            let referent = align_lifetime_types(
                expected_referent,
                actual_referent,
                substitution,
                mode,
                depth,
            )?;
            // `&mut` is covariant in its loan region but invariant in the
            // stored referent: accepting a shorter nested reference here
            // could permit a later write through the unique outer loan to
            // violate the promised longer inner lifetime.
            if *expected_mutability == Mutability::Unique {
                check_invariant_lifetimes(expected_referent, actual_referent, substitution, mode, depth)?;
            }
            Ok(Type::Reference {
                mutability: *expected_mutability,
                // The actual lifetime is intentionally retained here. A
                // longer `'static` argument may satisfy an elided parameter;
                // ordinary type unification must not turn that safe coercion
                // back into an equality failure.
                lifetime: aligned_lifetime(*expected_lifetime, *actual_lifetime, mode, depth),
                referent: Box::new(referent),
            })
        }
        (Type::Tuple(expected), Type::Tuple(actual)) if expected.len() == actual.len() => {
            Ok(Type::Tuple(
                expected
                    .iter()
                    .zip(actual)
                    .map(|(expected, actual)| {
                        align_lifetime_types(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
            ))
        }
        (Type::Array(expected), Type::Array(actual)) => Ok(Type::Array(Box::new(
            align_lifetime_types(expected, actual, substitution, mode, depth)?,
        ))),
        (
            Type::RawPointer { mutability: expected_mutability, pointee: expected_pointee },
            Type::RawPointer { mutability: actual_mutability, pointee: actual_pointee },
        ) if expected_mutability == actual_mutability => {
            let pointee = align_lifetime_types(expected_pointee, actual_pointee, substitution, mode, depth)?;
            // A writable pointer is invariant in stored values: shortening
            // an embedded reference could otherwise enable an invalid write.
            // Const pointers allow the ordinary covariant lifetime relation.
            if *expected_mutability == crate::PointerMutability::Mut {
                check_invariant_lifetimes(expected_pointee, actual_pointee, substitution, mode, depth)?;
            }
            Ok(Type::RawPointer { mutability: *expected_mutability, pointee: Box::new(pointee) })
        }
        (
            Type::Nominal {
                definition: expected_definition,
                arguments: expected_arguments,
            },
            Type::Nominal {
                definition: actual_definition,
                arguments: actual_arguments,
            },
        ) if expected_definition == actual_definition
            && expected_arguments.len() == actual_arguments.len() =>
        {
            Ok(Type::Nominal {
                definition: *expected_definition,
                arguments: expected_arguments
                    .iter()
                    .zip(actual_arguments)
                    .map(|(expected, actual)| {
                        align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
            })
        }
        (
            Type::Projection {
                subject: expected_subject,
                trait_definition: expected_trait,
                trait_arguments: expected_trait_arguments,
                name: expected_name,
                item_generic_kinds: expected_item_kinds,
                item_arguments: expected_item_arguments,
            },
            Type::Projection {
                subject: actual_subject,
                trait_definition: actual_trait,
                trait_arguments: actual_trait_arguments,
                name: actual_name,
                item_generic_kinds: actual_item_kinds,
                item_arguments: actual_item_arguments,
            },
        ) if expected_trait == actual_trait
            && expected_name == actual_name
            && expected_item_kinds == actual_item_kinds
            && expected_trait_arguments.len() == actual_trait_arguments.len()
            && expected_item_arguments.len() == actual_item_arguments.len() =>
        {
            Ok(Type::Projection {
                subject: Box::new(align_lifetime_types(
                    expected_subject,
                    actual_subject,
                    substitution,
                    mode,
                    depth,
                )?),
                trait_definition: *expected_trait,
                trait_arguments: expected_trait_arguments
                    .iter()
                    .zip(actual_trait_arguments)
                    .map(|(expected, actual)| {
                        align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
                name: expected_name.clone(),
                item_generic_kinds: expected_item_kinds.clone(),
                item_arguments: expected_item_arguments
                    .iter()
                    .zip(actual_item_arguments)
                    .map(|(expected, actual)| {
                        align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
            })
        }
        (
            Type::Callable {
                safety: expected_safety,
                lifetime_binders: expected_binders,
                parameters: expected_parameters,
                result: expected_result,
                effects: expected_effects,
                invocation: expected_invocation,
            },
            Type::Callable {
                safety: actual_safety,
                lifetime_binders: actual_binders,
                parameters: actual_parameters,
                result: actual_result,
                effects: actual_effects,
                invocation: actual_invocation,
            },
        ) if expected_safety == actual_safety && expected_binders == actual_binders
            && expected_parameters.len() == actual_parameters.len()
            && expected_invocation == actual_invocation =>
        {
            // Callable inputs are contravariant: a callback that accepts a
            // shorter/elided reference can safely stand in for one that will
            // only ever receive a `'static` reference.  Results and effect
            // payloads remain covariant below.  Keep the actual parameter
            // spelling in the returned type so the ordinary equality-based
            // inference pass sees the already-proven coercion rather than
            // trying to rediscover it as an equality.
            for (expected, actual) in expected_parameters.iter().zip(actual_parameters) {
                align_lifetime_types(actual, expected, substitution, mode, depth + 1)?;
            }
            Ok(Type::Callable {
                safety: *expected_safety,
                lifetime_binders: *expected_binders,
                parameters: actual_parameters.clone(),
                result: Box::new(align_lifetime_types(
                    expected_result,
                    actual_result,
                    substitution,
                    mode,
                    depth + 1,
                )?),
                effects: align_lifetime_effect_row(
                    expected_effects,
                    actual_effects,
                    substitution,
                    mode,
                    depth + 1,
                )?,
                invocation: *expected_invocation,
            })
        }
        // Let ordinary type inference diagnose any non-reference structural
        // mismatch. Returning `expected` here keeps generic type variables
        // inferable at the same locations as before this lifetime pass.
        _ => Ok(expected.clone()),
    }
}

fn check_invariant_lifetimes(
    expected: &Type,
    actual: &Type,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<(), LifetimeError> {
    // The forward pass has opened callee regions into caller coordinates.
    // Reverse variance must compare that instantiated contract rigidly: a
    // callee `'a` already bound to `'static` is not a caller-local short loan,
    // and caller Generic indices must never become new callee substitutions.
    // Use the original contract, not the aligned type (which already contains
    // coercions), so fixed nested regions still enforce real invariance.
    let expected = match mode {
        LifetimeMode::Instantiate => substitute_call_lifetimes(expected.clone(), substitution, depth)?,
        LifetimeMode::Rigid => expected.clone(),
    };
    align_lifetime_types(actual, &expected, substitution, LifetimeMode::Rigid, depth).map(|_| ())
}

/// Open the selected binder of a higher-ranked callable for elaborating its
/// own body. The callable value retains the original universally quantified
/// type; only body-local Core terms use `Elided` regions, which are erased
/// after ordinary lifetime/escape checking during VM lowering.
fn open_hrtb_callable_body_type(value: Type, binder_depth: u32) -> Type {
    match value {
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime: match lifetime {
                Lifetime::Bound { depth, .. } if depth == binder_depth => Lifetime::Elided,
                Lifetime::Bound { depth, index } if depth > binder_depth => Lifetime::Bound {
                    depth: depth - 1,
                    index,
                },
                lifetime => lifetime,
            },
            referent: Box::new(open_hrtb_callable_body_type(*referent, binder_depth)),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| open_hrtb_callable_body_type(value, binder_depth))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(open_hrtb_callable_body_type(
            *value,
            binder_depth,
        ))),
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability,
            pointee: Box::new(open_hrtb_callable_body_type(*pointee, binder_depth)),
        },
        Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            safety,
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|parameter| open_hrtb_callable_body_type(parameter, binder_depth + 1))
                .collect(),
            result: Box::new(open_hrtb_callable_body_type(*result, binder_depth + 1)),
            effects,
            invocation,
        },
        value => value,
    }
}

/// The effect counterpart of [`open_hrtb_callable_body_type`]. Associated
/// effect-row projections retain lifetime arguments in their identity, so
/// opening only references would leave a bound universe in `RunsIn` metadata
/// even though the closure body itself has caller-local regions.
pub(crate) fn open_hrtb_callable_body_effect_row(
    value: EffectRow,
    binder_depth: u32,
) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| open_hrtb_callable_body_generic_argument(argument, binder_depth))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| crate::types::EffectRowProjection {
                subject: Box::new(open_hrtb_callable_body_type(
                    *projection.subject,
                    binder_depth,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|argument| {
                        open_hrtb_callable_body_generic_argument(argument, binder_depth)
                    })
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|argument| {
                        open_hrtb_callable_body_generic_argument(argument, binder_depth)
                    })
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

fn open_hrtb_callable_body_generic_argument(
    value: GenericArgument,
    binder_depth: u32,
) -> GenericArgument {
    match value {
        GenericArgument::Type(value) => {
            GenericArgument::Type(open_hrtb_callable_body_type(value, binder_depth))
        }
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(open_hrtb_callable_body_effect_row(value, binder_depth))
        }
        GenericArgument::Lifetime(Lifetime::Bound { depth, .. }) if depth == binder_depth => {
            GenericArgument::Lifetime(Lifetime::Elided)
        }
        GenericArgument::Lifetime(Lifetime::Bound { depth, index }) if depth > binder_depth => {
            GenericArgument::Lifetime(Lifetime::Bound {
                depth: depth - 1,
                index,
            })
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(open_hrtb_callable_body_type(*subject, binder_depth)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| open_hrtb_callable_body_generic_argument(argument, binder_depth))
                .collect(),
            name,
            kind,
        },
        value => value,
    }
}

fn align_lifetime_generic_argument(
    expected: &GenericArgument,
    actual: &GenericArgument,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<GenericArgument, LifetimeError> {
    match (expected, actual) {
        (GenericArgument::Type(expected), GenericArgument::Type(actual)) => {
            align_lifetime_types(expected, actual, substitution, mode, depth)
                .map(GenericArgument::Type)
        }
        (GenericArgument::Lifetime(expected), GenericArgument::Lifetime(actual)) => {
            bind_lifetime(*expected, *actual, substitution, mode, depth)?;
            Ok(GenericArgument::Lifetime(aligned_lifetime(*expected, *actual, mode, depth)))
        }
        (GenericArgument::EffectRow(expected), GenericArgument::EffectRow(actual)) => {
            align_lifetime_effect_row(expected, actual, substitution, mode, depth)
                .map(GenericArgument::EffectRow)
        }
        // Structural constants carry no lifetime leaves, but their values can
        // be body-local inference terms.  Preserve an omitted native-domain
        // hole for the ordinary generic unifier below; treating a different
        // concrete value as a lifetime failure prevented `Tag<n>` from
        // learning `n = 7` at a direct call.
        (
            GenericArgument::ConstInfer {
                kind: expected_kind,
                ..
            },
            actual,
        ) if generic_argument_matches_const_kind(actual, *expected_kind) => Ok(expected.clone()),
        (expected, actual) if expected == actual => Ok(expected.clone()),
        _ => Err(LifetimeError::UnsatisfiedOutlives),
    }
}

fn generic_argument_matches_const_kind(argument: &GenericArgument, kind: crate::ConstKind) -> bool {
    matches!(
        (argument, kind),
        (GenericArgument::ConstU32(_), crate::ConstKind::U32)
            | (GenericArgument::ConstU32Expr(_), crate::ConstKind::U32)
            | (
                GenericArgument::ConstQuantity(_),
                crate::ConstKind::Quantity
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::ConstKind::U32
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::ConstKind::Quantity
            )
            | (
                GenericArgument::ConstProjection {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::ConstKind::U32
            )
            | (
                GenericArgument::ConstProjection {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::ConstKind::Quantity
            )
            | (
                GenericArgument::ConstInfer {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::ConstKind::U32
            )
            | (
                GenericArgument::ConstInfer {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::ConstKind::Quantity
            )
    )
}

fn align_lifetime_effect_row(
    expected: &EffectRow,
    actual: &EffectRow,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<EffectRow, LifetimeError> {
    // An open body-local tail is a genuine inference term, not a malformed
    // lifetime relation.  There is no corresponding effect instance whose
    // nested reference lifetimes we could inspect until the ordinary row
    // solver has bound it.  Preserve the expected row here and let
    // `InferContext::unify_effect_rows` solve (or reject) the structural
    // difference afterwards.  Treating this as an outlives failure made an
    // implicit `fn id<e: EffectRow>(Token<e>)` call reject before `e` could
    // learn the row carried by its argument.
    if expected.tail != actual.tail || expected.effects.len() != actual.effects.len() {
        return Ok(expected.clone());
    }
    let mut unmatched = actual.effects.iter().cloned().collect::<Vec<_>>();
    let mut effects = std::collections::BTreeSet::new();
    for expected_effect in &expected.effects {
        let Some(index) = unmatched.iter().position(|actual_effect| {
            actual_effect.definition == expected_effect.definition
                && actual_effect.arguments.len() == expected_effect.arguments.len()
        }) else {
            return Ok(expected.clone());
        };
        let actual_effect = unmatched.remove(index);
        effects.insert(EffectInstance {
            definition: expected_effect.definition,
            arguments: expected_effect
                .arguments
                .iter()
                .zip(&actual_effect.arguments)
                .map(|(expected, actual)| {
                    align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                })
                .collect::<Result<_, _>>()?,
        });
    }
    if expected.projections.len() != actual.projections.len() {
        return Ok(expected.clone());
    }
    let mut unmatched = actual.projections.clone();
    let mut projections = Vec::with_capacity(expected.projections.len());
    for expected_projection in &expected.projections {
        let Some(index) = unmatched.iter().position(|actual_projection| {
            actual_projection.trait_definition == expected_projection.trait_definition
                && actual_projection.name == expected_projection.name
                && actual_projection.trait_arguments.len()
                    == expected_projection.trait_arguments.len()
                && actual_projection.item_arguments.len()
                    == expected_projection.item_arguments.len()
                && actual_projection.item_generic_kinds == expected_projection.item_generic_kinds
        }) else {
            return Ok(expected.clone());
        };
        let actual_projection = unmatched.remove(index);
        projections.push(crate::EffectRowProjection {
            subject: Box::new(align_lifetime_types(
                &expected_projection.subject,
                &actual_projection.subject,
                substitution,
                mode,
                depth,
            )?),
            trait_definition: expected_projection.trait_definition,
            trait_arguments: expected_projection
                .trait_arguments
                .iter()
                .zip(&actual_projection.trait_arguments)
                .map(|(expected, actual)| {
                    align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                })
                .collect::<Result<_, _>>()?,
            name: expected_projection.name.clone(),
            item_generic_kinds: expected_projection.item_generic_kinds.clone(),
            item_arguments: expected_projection
                .item_arguments
                .iter()
                .zip(&actual_projection.item_arguments)
                .map(|(expected, actual)| {
                    align_lifetime_generic_argument(expected, actual, substitution, mode, depth)
                })
                .collect::<Result<_, _>>()?,
        });
    }
    Ok(EffectRow {
        effects,
        projections,
        tail: expected.tail,
    }
    .canonicalized())
}

fn opens_call_lifetime(value: Lifetime, mode: LifetimeMode, depth: u32) -> bool {
    matches!(mode, LifetimeMode::Instantiate)
        && (matches!(value, Lifetime::Generic(_))
            || matches!(value, Lifetime::Bound { depth: binder, .. } if binder == depth))
}

fn aligned_lifetime(expected: Lifetime, actual: Lifetime, mode: LifetimeMode, depth: u32) -> Lifetime {
    if matches!(expected, Lifetime::Infer(_))
        || (matches!(actual, Lifetime::Infer(_)) && !opens_call_lifetime(expected, mode, depth)) {
        expected
    } else { actual }
}

fn bind_lifetime(
    expected: Lifetime,
    actual: Lifetime,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<(), LifetimeError> {
    // An unsolved caller hole can still open a callee binder. Retain that
    // hole in the application until body inference seals it; feeding the
    // declaration's Generic/Bound name back into unification would instead
    // capture the hole and poison earlier generic instances sharing it.
    if matches!(actual, Lifetime::Infer(_)) && !opens_call_lifetime(expected, mode, depth) {
        return Ok(());
    }
    match expected {
        Lifetime::Infer(_) => Ok(()),
        Lifetime::Static => (actual == Lifetime::Static)
            .then_some(())
            .ok_or(LifetimeError::UnsatisfiedOutlives),
        Lifetime::Elided if matches!(mode, LifetimeMode::Instantiate) => Ok(()),
        Lifetime::Elided => matches!(actual, Lifetime::Elided | Lifetime::Static)
            .then_some(())
            .ok_or(LifetimeError::UnsatisfiedOutlives),
        Lifetime::Generic(index) => match mode {
            LifetimeMode::Rigid => (actual == expected || actual == Lifetime::Static)
                .then_some(())
                .ok_or(LifetimeError::UnsatisfiedOutlives),
            LifetimeMode::Instantiate => match substitution.generics.get(&index) {
                Some(previous) if *previous != actual => Err(LifetimeError::UnsatisfiedOutlives),
                Some(_) => Ok(()),
                None => {
                    substitution.generics.insert(index, actual);
                    Ok(())
                }
            },
        },
        Lifetime::Bound {
            depth: bound_depth,
            index,
        } if matches!(mode, LifetimeMode::Instantiate) && bound_depth == depth => {
            match substitution.bounds.get(&index) {
                Some(previous) if *previous != actual => Err(LifetimeError::UnsatisfiedOutlives),
                Some(_) => Ok(()),
                None => {
                    substitution.bounds.insert(index, actual);
                    Ok(())
                }
            }
        }
        Lifetime::Bound { .. } => (actual == expected)
            .then_some(())
            .ok_or(LifetimeError::UnsatisfiedOutlives),
    }
}

fn substitute_call_lifetimes(
    value: Type,
    substitution: &CallLifetimeSubstitution,
    depth: u32,
) -> Result<Type, LifetimeError> {
    match value {
        Type::Nominal {
            definition,
            arguments,
        } => Ok(Type::Nominal {
            definition,
            arguments: arguments
                .into_iter()
                .map(|value| substitute_call_generic_argument(value, substitution, depth))
                .collect::<Result<_, _>>()?,
        }),
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Ok(Type::Projection {
            subject: Box::new(substitute_call_lifetimes(*subject, substitution, depth)?),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_call_generic_argument(value, substitution, depth))
                .collect::<Result<_, _>>()?,
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_call_generic_argument(value, substitution, depth))
                .collect::<Result<_, _>>()?,
        }),
        Type::Tuple(values) => Ok(Type::Tuple(
            values
                .into_iter()
                .map(|value| substitute_call_lifetimes(value, substitution, depth))
                .collect::<Result<_, _>>()?,
        )),
        Type::Array(value) => Ok(Type::Array(Box::new(substitute_call_lifetimes(
            *value,
            substitution,
            depth,
        )?))),
        Type::RawPointer { mutability, pointee } => Ok(Type::RawPointer {
            mutability,
            pointee: Box::new(substitute_call_lifetimes(*pointee, substitution, depth)?),
        }),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Ok(Type::Reference {
            mutability,
            lifetime: substitute_call_lifetime(lifetime, substitution, depth)?,
            referent: Box::new(substitute_call_lifetimes(*referent, substitution, depth)?),
        }),
        Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Ok(Type::Callable {
            safety,
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| substitute_call_lifetimes(value, substitution, depth + 1))
                .collect::<Result<_, _>>()?,
            result: Box::new(substitute_call_lifetimes(*result, substitution, depth + 1)?),
            effects: substitute_call_effects(effects, substitution, depth + 1)?,
            invocation,
        }),
        value => Ok(value),
    }
}

fn substitute_call_lifetime(
    lifetime: Lifetime,
    substitution: &CallLifetimeSubstitution,
    depth: u32,
) -> Result<Lifetime, LifetimeError> {
    match lifetime {
        Lifetime::Generic(index) => substitution
            .generics
            .get(&index)
            .copied()
            .ok_or(LifetimeError::UnresolvedGeneric),
        Lifetime::Bound {
            depth: bound_depth,
            index,
        } if bound_depth == depth => substitution
            .bounds
            .get(&index)
            .copied()
            .ok_or(LifetimeError::EscapingBound),
        Lifetime::Bound {
            depth: bound_depth,
            index,
        } if bound_depth > depth => Ok(Lifetime::Bound {
            depth: bound_depth - 1,
            index,
        }),
        lifetime => Ok(lifetime),
    }
}

fn substitute_call_effects(
    effects: crate::types::EffectRow,
    substitution: &CallLifetimeSubstitution,
    depth: u32,
) -> Result<crate::types::EffectRow, LifetimeError> {
    let crate::types::EffectRow {
        effects,
        projections,
        tail,
    } = effects;
    let effects = effects
        .into_iter()
        .map(|effect| {
            Ok(crate::types::EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|value| substitute_call_generic_argument(value, substitution, depth))
                    .collect::<Result<_, _>>()?,
            })
        })
        .collect::<Result<_, _>>()?;
    let projections = projections
        .into_iter()
        .map(|projection| {
            Ok(crate::types::EffectRowProjection {
                subject: Box::new(substitute_call_lifetimes(
                    *projection.subject,
                    substitution,
                    depth,
                )?),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|value| substitute_call_generic_argument(value, substitution, depth))
                    .collect::<Result<_, _>>()?,
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_call_generic_argument(value, substitution, depth))
                    .collect::<Result<_, _>>()?,
            })
        })
        .collect::<Result<_, _>>()?;
    Ok(crate::types::EffectRow {
        effects,
        projections,
        tail,
    })
}

fn substitute_call_generic_argument(
    value: GenericArgument,
    substitution: &CallLifetimeSubstitution,
    depth: u32,
) -> Result<GenericArgument, LifetimeError> {
    match value {
        GenericArgument::Type(value) => {
            substitute_call_lifetimes(value, substitution, depth).map(GenericArgument::Type)
        }
        GenericArgument::EffectRow(value) => {
            substitute_call_effects(value, substitution, depth).map(GenericArgument::EffectRow)
        }
        GenericArgument::Lifetime(value) => {
            substitute_call_lifetime(value, substitution, depth).map(GenericArgument::Lifetime)
        }
        value => Ok(value),
    }
}

fn projection_is_concrete(value: &Type) -> bool {
    match value {
        Type::Generic(_) | Type::Infer(_) => false,
        Type::Nominal { arguments, .. } => arguments.iter().all(generic_argument_is_concrete),
        Type::Tuple(arguments) => arguments.iter().all(projection_is_concrete),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            projection_is_concrete(subject)
                && trait_arguments.iter().all(generic_argument_is_concrete)
                && item_arguments.iter().all(generic_argument_is_concrete)
        }
        Type::Array(element)
        | Type::RawPointer { pointee: element, .. }
        | Type::StaticData { element, .. }
        | Type::Reference {
            referent: element, ..
        } => projection_is_concrete(element),
        Type::Callable {
            parameters, result, ..
        } => parameters.iter().all(projection_is_concrete) && projection_is_concrete(result),
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Error => true,
    }
}

fn generic_argument_is_concrete(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => projection_is_concrete(value),
        GenericArgument::EffectRow(value) => {
            value.tail.is_none()
                && value
                    .effects
                    .iter()
                    .all(|effect| effect.arguments.iter().all(generic_argument_is_concrete))
                && value.projections.is_empty()
        }
        GenericArgument::Lifetime(Lifetime::Static | Lifetime::Elided)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::Lifetime(Lifetime::Generic(_) | Lifetime::Bound { .. } | Lifetime::Infer(_))
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

/// Whether an associated effect-row application may be selected while
/// checking a body.  A callable's own lifetime parameter is a rigid,
/// declaration-owned term: it is not an inference variable and selecting an
/// implementation generic over that lifetime does not choose a lifetime for
/// the caller.  Treat it as selectable here so signatures such as
/// `<&'a T as Capability>::Effects<'a>` can normalize their concrete effect
/// implementation.  Other symbolic arguments remain deliberately rejected.
fn generic_argument_is_selectable_effect_projection(value: &GenericArgument) -> bool {
    generic_argument_is_concrete(value)
        || matches!(value, GenericArgument::Lifetime(Lifetime::Generic(_)))
        // The selected trait head is still required to be concrete. A type
        // item argument owned by this declaration therefore cannot choose an
        // implementation; it is merely substituted into the already selected
        // associated row (for example `<i64 as Gate>::Effects<'a, T>`).
        || matches!(value, GenericArgument::Type(Type::Generic(_)))
        || matches!(
            value,
            GenericArgument::EffectRow(EffectRow {
                effects,
                projections,
                tail: Some(crate::EffectTail::Generic(_)),
            }) if projections.is_empty()
                && effects.iter().all(|effect| {
                    effect
                        .arguments
                        .iter()
                        .all(generic_argument_is_selectable_effect_projection)
                })
        )
}

/// A selected associated type may carry a declaration-owned generic item
/// argument.  The trait head still has to be concrete, so this does not let a
/// body select an implementation for an abstract `Self`; it only lets the
/// selected implementation substitute a rigid parameter into its item value.
///
/// Keep unresolved associated projections and inference variables out of this
/// set.  Treating either as rigid would allow a concrete head to choose an
/// implementation based on evidence that belongs to a caller or has not been
/// inferred yet.
fn projection_is_selectable_type_projection(
    value: &Type,
    hrtb_binders: &[u32],
    allow_rigid_trait_arguments: bool,
) -> bool {
    let Type::Projection {
        subject,
        trait_arguments,
        item_arguments,
        ..
    } = value
    else {
        return false;
    };
    projection_is_concrete(subject)
        // An implementation body owns its declaration generics. Once the
        // subject is concrete, those rigid trait arguments select the same
        // generic impl evidence for every instantiation; requiring them to
        // be fully concrete leaves `<i64 as Parent<T>>::Item<'a>` opaque in
        // precisely the body that establishes `Parent<T> for i64`.
        && trait_arguments.iter().all(|argument| {
            allow_rigid_trait_arguments
                && generic_argument_is_selectable_type_projection(argument, hrtb_binders)
                || generic_argument_is_concrete(argument)
        })
        && item_arguments
            .iter()
            .all(|argument| {
                generic_argument_is_selectable_type_projection(argument, hrtb_binders)
            })
}

fn generic_argument_is_selectable_type_projection(
    value: &GenericArgument,
    hrtb_binders: &[u32],
) -> bool {
    match value {
        GenericArgument::Type(value) => {
            type_is_selectable_type_projection_argument(value, hrtb_binders)
        }
        GenericArgument::EffectRow(value) => {
            value.projections.is_empty()
                && value.effects.iter().all(|effect| {
                    effect
                        .arguments
                        .iter()
                        .all(|argument| {
                            generic_argument_is_selectable_type_projection(argument, hrtb_binders)
                        })
                })
                && matches!(value.tail, None | Some(crate::EffectTail::Generic(_)))
        }
        GenericArgument::Lifetime(Lifetime::Static | Lifetime::Elided | Lifetime::Generic(_))
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => true,
        GenericArgument::Lifetime(Lifetime::Bound { depth, index }) => hrtb_binders
            .get(*depth as usize)
            .is_some_and(|count| *index < *count),
        GenericArgument::Lifetime(Lifetime::Infer(_))
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn type_is_selectable_type_projection_argument(value: &Type, hrtb_binders: &[u32]) -> bool {
    match value {
        Type::Generic(_) | Type::ConstGeneric { .. } => true,
        Type::Infer(_) | Type::Error => false,
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .all(|argument| generic_argument_is_selectable_type_projection(argument, hrtb_binders)),
        Type::Tuple(values) => values
            .iter()
            .all(|value| type_is_selectable_type_projection_argument(value, hrtb_binders)),
        // A nested projection is selectable only once it has been selected
        // to a concrete type by the recursive normalizer above.
        Type::Projection { .. } => projection_is_concrete(value),
        Type::Array(value) | Type::StaticData { element: value, .. }
        | Type::RawPointer { pointee: value, .. } => {
            type_is_selectable_type_projection_argument(value, hrtb_binders)
        }
        Type::Reference {
            lifetime, referent, ..
        } => {
            (matches!(lifetime, Lifetime::Static | Lifetime::Elided | Lifetime::Generic(_))
                || matches!(lifetime, Lifetime::Bound { depth, index }
                    if hrtb_binders.get(*depth as usize).is_some_and(|count| *index < *count)))
                && type_is_selectable_type_projection_argument(referent, hrtb_binders)
        }
        Type::Callable {
            parameters, result, ..
        } => {
            parameters
                .iter()
                .all(|value| type_is_selectable_type_projection_argument(value, hrtb_binders))
                && type_is_selectable_type_projection_argument(result, hrtb_binders)
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_) => true,
    }
}

fn literal_type(text: &str) -> Type {
    if matches!(text, "true" | "false") {
        Type::Scalar(ScalarType::Bool)
    } else if text.starts_with('"') {
        Type::Scalar(ScalarType::Text)
    } else if text.starts_with("b\"") {
        Type::Scalar(ScalarType::Bytes)
    } else if text.starts_with('\'') {
        Type::Scalar(ScalarType::Char)
    } else if text.contains('.') || text.contains('e') || text.contains('E') {
        Type::Scalar(ScalarType::F64)
    } else {
        Type::Scalar(ScalarType::I64)
    }
}

pub(crate) fn literal_is_numeric(text: &str) -> bool {
    !matches!(text, "true" | "false")
        && !text.starts_with('"')
        && !text.starts_with("b\"")
        && !text.starts_with('\'')
}

fn scalar_is_numeric(scalar: ScalarType) -> bool {
    matches!(
        scalar,
        ScalarType::U8
            | ScalarType::U16
            | ScalarType::U32
            | ScalarType::U64
            | ScalarType::U128
            | ScalarType::Usize
            | ScalarType::I8
            | ScalarType::I16
            | ScalarType::I32
            | ScalarType::I64
            | ScalarType::I128
            | ScalarType::Isize
            | ScalarType::F32
            | ScalarType::F64
    )
}

/// A refinement pack is available only to a completion arm whose own pattern
/// establishes the positive test result.  Wildcards and later ordered arms
/// intentionally do not inherit the proof: that would let a negative path
/// manufacture a positive binder.
fn core_pattern_is_true(pattern: &CorePattern) -> bool {
    matches!(pattern, CorePattern::Literal(value) if value == "true")
}

fn core_pattern_is_false(pattern: &CorePattern) -> bool {
    matches!(pattern, CorePattern::Literal(value) if value == "false")
}

fn core_pattern_irrefutable(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => true,
        CorePattern::Tuple(values) => values.iter().all(core_pattern_irrefutable),
        CorePattern::Array { .. } => false,
        CorePattern::Record { fields, .. } => fields
            .iter()
            .all(|field| core_pattern_irrefutable(&field.pattern)),
        CorePattern::Literal(_) | CorePattern::Enum { .. } | CorePattern::Error => false,
    }
}

/// A row covers a whole enum constructor only when every explicitly selected
/// payload field is itself irrefutable. Omitted named fields are wildcards by
/// construction, so they need no synthetic Core node here.
fn core_pattern_covers_enum_constructor(
    pattern: &CorePattern,
    definition: DefKey,
    variant: u32,
) -> bool {
    matches!(
        pattern,
        CorePattern::Enum {
            definition: actual_definition,
            variant: actual_variant,
            fields,
            ..
        } if *actual_definition == definition
            && *actual_variant == variant
            && fields.iter().all(|field| core_pattern_irrefutable(&field.pattern))
    )
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CorePatternMatrixAnalysis {
    exhaustive: bool,
    unreachable: Vec<usize>,
}

/// A cell in a bounded structural over-approximation. `Unknown` contains all
/// residents of an open leaf (such as i64), not one representative integer.
/// This is proof-only data: neither MIR nor the VM receives an invented value.
#[derive(Clone, Debug, Eq, PartialEq)]
enum FinitePatternValue {
    Unknown,
    Unit,
    Bool(bool),
    Tuple(Vec<FinitePatternValue>),
    Record {
        definition: DefKey,
        fields: Vec<FinitePatternValue>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        fields: Vec<FinitePatternValue>,
    },
}

fn finite_pattern_weight(value: &FinitePatternValue) -> usize {
    1 + match value {
        FinitePatternValue::Tuple(fields)
        | FinitePatternValue::Record { fields, .. }
        | FinitePatternValue::Enum { fields, .. } => fields.iter().map(finite_pattern_weight).sum(),
        _ => 0,
    }
}

fn finite_pattern_products(
    columns: Vec<Vec<FinitePatternValue>>,
    limit: usize,
) -> Option<Vec<Vec<FinitePatternValue>>> {
    if columns.len() > limit {
        return None;
    }
    let mut products = vec![vec![]];
    for column in columns {
        let count = products.len().checked_mul(column.len())?;
        if count > limit {
            return None;
        }
        let prefix_weight: usize = products.iter().flatten().map(finite_pattern_weight).sum();
        let column_weight: usize = column.iter().map(finite_pattern_weight).sum();
        if prefix_weight
            .checked_mul(column.len())?
            .checked_add(column_weight.checked_mul(products.len())?)?
            > 65_536
        {
            return None;
        }
        let mut next = Vec::with_capacity(count);
        for prefix in products {
            for value in &column {
                let mut product = prefix.clone();
                product.push(value.clone());
                next.push(product);
            }
        }
        products = next;
    }
    Some(products)
}

/// Conjunction in a three-valued coverage proof. A known mismatch dominates
/// an open sibling, while a possible match never becomes a total match.
fn pattern_matches_all(results: impl Iterator<Item = Option<bool>>) -> Option<bool> {
    let mut unknown = false;
    for result in results {
        match result {
            Some(false) => return Some(false),
            None => unknown = true,
            Some(true) => {}
        }
    }
    if unknown { None } else { Some(true) }
}

fn core_pattern_matches_value(pattern: &CorePattern, value: &FinitePatternValue) -> Option<bool> {
    match (pattern, value) {
        (CorePattern::Any | CorePattern::Bind { .. }, _) => Some(true),
        (_, FinitePatternValue::Unknown) => None,
        (CorePattern::Literal(literal), FinitePatternValue::Bool(value)) => {
            Some(matches!((literal.as_str(), value), ("true", true) | ("false", false)))
        }
        (CorePattern::Tuple(patterns), FinitePatternValue::Unit) => Some(patterns.is_empty()),
        (CorePattern::Tuple(patterns), FinitePatternValue::Tuple(values)) => {
            if patterns.len() != values.len() {
                return Some(false);
            }
            pattern_matches_all(patterns.iter().zip(values)
                .map(|(pattern, value)| core_pattern_matches_value(pattern, value)))
        }
        (
            CorePattern::Record {
                definition, fields, ..
            },
            FinitePatternValue::Record {
                definition: actual,
                fields: values,
            },
        ) => {
            if definition != actual {
                return Some(false);
            }
            pattern_matches_all(fields.iter().map(|field| {
                values.get(field.index as usize)
                    .and_then(|value| core_pattern_matches_value(&field.pattern, value))
            }))
        }
        (
            CorePattern::Enum {
                definition,
                variant,
                fields,
                ..
            },
            FinitePatternValue::Enum {
                definition: actual_definition,
                variant: actual_variant,
                fields: values,
            },
        ) => {
            if definition != actual_definition || variant != actual_variant {
                return Some(false);
            }
            pattern_matches_all(fields.iter().map(|field| {
                values.get(field.index as usize)
                    .and_then(|value| core_pattern_matches_value(&field.pattern, value))
            }))
        }
        _ => Some(false),
    }
}

/// Whether every value matched by `right` is also matched by `left`.  This is
/// a structural, source-order proof rather than a finite-domain enumeration,
/// so it can identify duplicate literal and nested nominal rows even when the
/// surrounding scalar domain is unbounded.
fn core_pattern_subsumes(left: &CorePattern, right: &CorePattern) -> bool {
    match (left, right) {
        (CorePattern::Any | CorePattern::Bind { .. }, _) => true,
        (CorePattern::Literal(left), CorePattern::Literal(right)) => left == right,
        (CorePattern::Tuple(left), CorePattern::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| core_pattern_subsumes(left, right))
        }
        // Arrays are dynamic-length and therefore do not belong to the
        // finite-domain exhaustiveness proof below.  They nevertheless have
        // exact structural matching semantics, so ordered reachability must
        // still recognize that an earlier `[p0, .., pn]` covers an identical
        // or more-specific later array row.  Without this branch duplicate
        // array arms escaped the common decision-DAG proof merely because
        // their element domain was unbounded.
        (
            CorePattern::Array { elements: left, .. },
            CorePattern::Array {
                elements: right, ..
            },
        ) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| core_pattern_subsumes(left, right))
        }
        (
            CorePattern::Record {
                definition: left_definition,
                fields: left_fields,
                ..
            },
            CorePattern::Record {
                definition: right_definition,
                fields: right_fields,
                ..
            },
        ) => {
            left_definition == right_definition
                && left_fields.iter().all(|left| {
                    right_fields
                        .iter()
                        .find(|right| right.index == left.index)
                        .is_some_and(|right| core_pattern_subsumes(&left.pattern, &right.pattern))
                })
        }
        (
            CorePattern::Enum {
                definition: left_definition,
                variant: left_variant,
                fields: left_fields,
                ..
            },
            CorePattern::Enum {
                definition: right_definition,
                variant: right_variant,
                fields: right_fields,
                ..
            },
        ) => {
            left_definition == right_definition
                && left_variant == right_variant
                && left_fields.iter().all(|left| {
                    right_fields
                        .iter()
                        .find(|right| right.index == left.index)
                        .is_some_and(|right| core_pattern_subsumes(&left.pattern, &right.pattern))
                })
        }
        _ => false,
    }
}

fn handler_patterns_subsume(
    left: &[crate::pattern::PatternElaboration],
    right: &[crate::pattern::PatternElaboration],
) -> bool {
    left.len() == right.len()
        && left.iter().zip(right).all(|(left, right)| {
            pattern_decision_subsumes(&left.plan.decision, &right.plan.decision)
        })
}

fn pattern_decision_subsumes(
    left: &crate::pattern::PatternDecision,
    right: &crate::pattern::PatternDecision,
) -> bool {
    use crate::pattern::PatternDecision;
    match (left, right) {
        (PatternDecision::Any | PatternDecision::Bind(_), _) => true,
        (PatternDecision::Literal(left), PatternDecision::Literal(right)) => left == right,
        (PatternDecision::Tuple(left), PatternDecision::Tuple(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| pattern_decision_subsumes(left, right))
        }
        // Handler payload rows share the same exact array decision semantics
        // as normal completion arms.  Keep their source-free proof in lock
        // step with `core_pattern_subsumes` so an unreachable array handler
        // arm cannot remain live merely because its payload type is open.
        (PatternDecision::Array(left), PatternDecision::Array(right)) => {
            left.len() == right.len()
                && left
                    .iter()
                    .zip(right)
                    .all(|(left, right)| pattern_decision_subsumes(left, right))
        }
        (
            PatternDecision::Record {
                definition: left_definition,
                fields: left_fields,
            },
            PatternDecision::Record {
                definition: right_definition,
                fields: right_fields,
            },
        ) => {
            left_definition == right_definition
                && left_fields.iter().all(|(index, left)| {
                    right_fields
                        .iter()
                        .find(|(right, _)| right == index)
                        .is_some_and(|(_, right)| pattern_decision_subsumes(left, right))
                })
        }
        (
            PatternDecision::Enum {
                definition: left_definition,
                variant: left_variant,
                fields: left_fields,
            },
            PatternDecision::Enum {
                definition: right_definition,
                variant: right_variant,
                fields: right_fields,
            },
        ) => {
            left_definition == right_definition
                && left_variant == right_variant
                && left_fields.iter().all(|(index, left)| {
                    right_fields
                        .iter()
                        .find(|(right, _)| right == index)
                        .is_some_and(|(_, right)| pattern_decision_subsumes(left, right))
                })
        }
        _ => false,
    }
}

fn pattern_decision_irrefutable(decision: &crate::pattern::PatternDecision) -> bool {
    use crate::pattern::PatternDecision;
    match decision {
        PatternDecision::Any | PatternDecision::Bind(_) => true,
        PatternDecision::Tuple(values) => values.iter().all(pattern_decision_irrefutable),
        PatternDecision::Record { fields, .. } => fields
            .iter()
            .all(|(_, pattern)| pattern_decision_irrefutable(pattern)),
        PatternDecision::Literal(_)
        | PatternDecision::Array(_)
        | PatternDecision::Enum { .. }
        | PatternDecision::Error => false,
    }
}

fn pattern_decision_covers_enum_constructor(
    decision: &crate::pattern::PatternDecision,
    definition: DefKey,
    variant: u32,
) -> bool {
    matches!(
        decision,
        crate::pattern::PatternDecision::Enum {
            definition: actual_definition,
            variant: actual_variant,
            fields,
        } if *actual_definition == definition
            && *actual_variant == variant
            && fields
                .iter()
                .all(|(_, pattern)| pattern_decision_irrefutable(pattern))
    )
}

fn pattern_decision_matches_value(
    decision: &crate::pattern::PatternDecision,
    value: &FinitePatternValue,
) -> Option<bool> {
    match (decision, value) {
        (crate::pattern::PatternDecision::Any | crate::pattern::PatternDecision::Bind(_), _) => {
            Some(true)
        }
        (_, FinitePatternValue::Unknown) => None,
        (crate::pattern::PatternDecision::Literal(literal), FinitePatternValue::Bool(value)) => {
            Some(matches!((literal.as_str(), value), ("true", true) | ("false", false)))
        }
        (crate::pattern::PatternDecision::Tuple(patterns), FinitePatternValue::Unit) => Some(patterns.is_empty()),
        (crate::pattern::PatternDecision::Tuple(patterns), FinitePatternValue::Tuple(values)) => {
            if patterns.len() != values.len() {
                return Some(false);
            }
            pattern_matches_all(patterns.iter().zip(values)
                .map(|(pattern, value)| pattern_decision_matches_value(pattern, value)))
        }
        (
            crate::pattern::PatternDecision::Record { definition, fields },
            FinitePatternValue::Record {
                definition: actual,
                fields: values,
            },
        ) => {
            if definition != actual {
                return Some(false);
            }
            pattern_matches_all(fields.iter().map(|(index, pattern)| {
                values.get(*index as usize)
                    .and_then(|value| pattern_decision_matches_value(pattern, value))
            }))
        }
        (
            crate::pattern::PatternDecision::Enum {
                definition,
                variant,
                fields,
            },
            FinitePatternValue::Enum {
                definition: actual_definition,
                variant: actual_variant,
                fields: values,
            },
        ) => {
            if definition != actual_definition || variant != actual_variant {
                return Some(false);
            }
            pattern_matches_all(fields.iter().map(|(index, pattern)| {
                values.get(*index as usize)
                    .and_then(|value| pattern_decision_matches_value(pattern, value))
            }))
        }
        _ => Some(false),
    }
}

fn nominal_parts(subject: &Type) -> Option<(DefKey, Vec<GenericArgument>)> {
    match subject {
        Type::Nominal {
            definition,
            arguments,
        } => Some((*definition, arguments.clone())),
        _ => None,
    }
}

fn generic_argument_matches_kind(argument: &GenericArgument, kind: crate::GenericKind) -> bool {
    matches!(
        (argument, kind),
        (GenericArgument::Type(_), crate::GenericKind::Type)
            | (GenericArgument::EffectRow(_), crate::GenericKind::EffectRow)
            | (GenericArgument::Lifetime(_), crate::GenericKind::Lifetime)
            | (
                GenericArgument::ConstU32(_),
                crate::GenericKind::Const(crate::ConstKind::U32)
            )
            | (
                GenericArgument::ConstQuantity(_),
                crate::GenericKind::Const(crate::ConstKind::Quantity)
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::GenericKind::Const(crate::ConstKind::U32)
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::GenericKind::Const(crate::ConstKind::Quantity)
            )
    )
}

fn call_reference_origin(
    signatures: &ElaboratedInterface,
    expressions: &[CoreExpr],
    arguments: &[CoreId],
    result: &Type,
) -> CallReferenceOrigin {
    let mut result_leaves = vec![];
    if reference_leaf_paths(signatures, result, &mut vec![], &mut result_leaves).is_err() {
        return CallReferenceOrigin::Opaque;
    }
    if result_leaves.is_empty() {
        return CallReferenceOrigin::None;
    }
    if result_leaves.iter().all(|(_, ty)| {
        matches!(
            ty,
            Type::Reference {
                lifetime: Lifetime::Static,
                ..
            }
        )
    }) {
        return CallReferenceOrigin::External;
    }
    let mut argument_leaves = vec![];
    for (argument, id) in arguments.iter().enumerate() {
        let Some(expression) = expressions.get(id.0 as usize) else {
            return CallReferenceOrigin::Opaque;
        };
        let mut leaves = vec![];
        if reference_leaf_paths(signatures, &expression.ty, &mut vec![], &mut leaves).is_err() {
            return CallReferenceOrigin::Opaque;
        }
        argument_leaves.extend(
            leaves
                .into_iter()
                .map(|(fields, ty)| (argument as u32, fields, ty)),
        );
    }
    let mut paths = vec![];
    for (result_fields, result_ty) in result_leaves {
        let Type::Reference {
            lifetime: result_lifetime,
            ..
        } = result_ty
        else {
            unreachable!("reference leaf traversal only yields references");
        };
        if matches!(result_lifetime, Lifetime::Static) {
            // `Paths` records only caller-region leaves.  A result that is
            // entirely static used `External` above; in a mixed aggregate the
            // static leaf has no loan to preserve and can be omitted while
            // its caller-derived siblings retain their exact paths.
            continue;
        }
        let candidates = argument_leaves
            .iter()
            // Caller-region provenance follows the reference lifetime and
            // structural path, not referent equality.  A well-typed callee
            // may project `&'a Tri` to `&'a i64`; requiring `Tri == i64`
            // would incorrectly turn that unique, frozen loan relation into
            // opaque provenance. With several inputs in the same region,
            // retain their union: referent equality cannot rule out a
            // projection from a differently shaped input aggregate.
            .filter(|(_, _, candidate)| {
                matches!(candidate, Type::Reference { lifetime, .. } if lifetime == &result_lifetime)
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return CallReferenceOrigin::Opaque;
        }
        for (argument, argument_fields, _) in candidates {
            paths.push(CallReferencePath {
                result_fields: result_fields.clone(),
                argument: *argument,
                argument_fields: argument_fields.clone(),
            });
        }
    }
    CallReferenceOrigin::Paths(paths)
}


/// Recover the reference-result relation directly from the interface-aware
/// callable contract, before call instantiation turns distinct declaration or
/// higher-ranked regions into caller-local `Elided` lifetimes.
pub(crate) fn callable_reference_origin_from_contract(
    signatures: &ElaboratedInterface,
    parameters: &[Type],
    result: &Type,
) -> CallReferenceOrigin {
    let mut result_leaves = vec![];
    if reference_leaf_paths(signatures, result, &mut vec![], &mut result_leaves).is_err() {
        return CallReferenceOrigin::Opaque;
    }
    if result_leaves.is_empty() {
        return CallReferenceOrigin::None;
    }
    if result_leaves.iter().all(|(_, ty)| {
        matches!(
            ty,
            Type::Reference {
                lifetime: Lifetime::Static,
                ..
            }
        )
    }) {
        return CallReferenceOrigin::External;
    }
    let mut argument_leaves = vec![];
    for (argument, parameter) in parameters.iter().enumerate() {
        let mut leaves = vec![];
        if reference_leaf_paths(signatures, parameter, &mut vec![], &mut leaves).is_err() {
            return CallReferenceOrigin::Opaque;
        }
        argument_leaves.extend(
            leaves
                .into_iter()
                .map(|(fields, ty)| (argument as u32, fields, ty)),
        );
    }
    let mut paths = vec![];
    for (result_fields, result_ty) in result_leaves {
        if matches!(
            result_ty,
            Type::Reference {
                lifetime: Lifetime::Static,
                ..
            }
        ) {
            // Static leaves carry no caller-region provenance.  The whole
            // result is `External` only when every leaf is static; otherwise
            // preserve just the caller-derived paths in this mixed result.
            continue;
        }
        let Type::Reference {
            lifetime: result_lifetime,
            ..
        } = result_ty
        else {
            unreachable!("reference leaf traversal only yields references");
        };
        // See `call_reference_origin`: a declaration contract records the
        // caller region it forwards.  It intentionally permits a structural
        // projection whose referent differs from the source aggregate.
        let candidates = argument_leaves
            .iter()
            .filter(|(_, _, candidate)| {
                matches!(candidate, Type::Reference { lifetime, .. } if lifetime == &result_lifetime)
            })
            .collect::<Vec<_>>();
        if candidates.is_empty() {
            return CallReferenceOrigin::Opaque;
        }
        for (argument, argument_fields, _) in candidates {
            paths.push(CallReferencePath {
                result_fields: result_fields.clone(),
                argument: *argument,
                argument_fields: argument_fields.clone(),
            });
        }
    }
    CallReferenceOrigin::Paths(paths)
}

/// Discover direct reference leaves through the sealed structural shapes that
/// Typed Core can project. Nominal layouts are read from the frozen interface
/// and instantiated with their canonical application arguments; an enum or
/// opaque projection with a reference-bearing payload remains deliberately
/// opaque because a path would depend on a runtime variant.
pub(crate) fn reference_leaf_paths(
    signatures: &ElaboratedInterface,
    ty: &Type,
    path: &mut Vec<u32>,
    leaves: &mut Vec<(Vec<u32>, Type)>,
) -> Result<(), ()> {
    if let Some(fields) = crate::refinement::binding_pack_fields(ty) {
        for (index, field) in fields.iter().enumerate() {
            path.push(index as u32);
            reference_leaf_paths(signatures, field, path, leaves)?;
            path.pop();
        }
        return Ok(());
    }
    match ty {
        Type::Reference { .. } => leaves.push((path.clone(), ty.clone())),
        Type::Tuple(fields) => {
            for (index, field) in fields.iter().enumerate() {
                path.push(index as u32);
                reference_leaf_paths(signatures, field, path, leaves)?;
                path.pop();
            }
        }
        Type::Nominal {
            definition,
            arguments,
        } => match signatures.definitions.get(definition) {
            Some(ElaboratedHeader::Nominal {
                layout: ElaboratedNominalLayout::Struct(fields),
                ..
            }) => {
                for (index, field) in fields.iter().enumerate() {
                    path.push(index as u32);
                    let field = instantiate_nominal_field_type(&field.ty, arguments)?;
                    reference_leaf_paths(signatures, &field, path, leaves)?;
                    path.pop();
                }
            }
            Some(ElaboratedHeader::Nominal {
                layout: ElaboratedNominalLayout::Enum(variants),
                ..
            }) => {
                // An enum's active variant is not known at the call boundary,
                // but a payload position can still have stable caller-region
                // provenance when every variant that exposes that position
                // gives it the same lifetime.  `Result<&'a A, &'a E>` is the
                // canonical example: either variant may be returned, yet a
                // later refinement can soundly reborrow field zero from the
                // one `&'a Result<A, E>` input.  Preserve such field paths;
                // fail closed if a single position would name different
                // regions in different variants.
                let mut variant_leaves = std::collections::BTreeMap::new();
                for variant in variants {
                    let fields = match &variant.payload {
                        crate::signature::ElaboratedEnumVariantPayload::Unit => continue,
                        crate::signature::ElaboratedEnumVariantPayload::Tuple(fields) => {
                            fields.iter().collect::<Vec<_>>()
                        }
                        crate::signature::ElaboratedEnumVariantPayload::Struct(fields) => {
                            fields.iter().map(|field| &field.ty).collect::<Vec<_>>()
                        }
                    };
                    for (index, field) in fields.into_iter().enumerate() {
                        let field = instantiate_nominal_field_type(field, arguments)?;
                        path.push(index as u32);
                        let mut field_leaves = vec![];
                        let traversed =
                            reference_leaf_paths(signatures, &field, path, &mut field_leaves);
                        path.pop();
                        traversed?;
                        for (field_path, leaf) in field_leaves {
                            let Some(existing) = variant_leaves.get(&field_path) else {
                                variant_leaves.insert(field_path, leaf);
                                continue;
                            };
                            if !matches!(
                                (existing, &leaf),
                                (
                                    Type::Reference { lifetime: left, .. },
                                    Type::Reference { lifetime: right, .. },
                                ) if left == right
                            ) {
                                return Err(());
                            }
                        }
                    }
                }
                leaves.extend(variant_leaves);
            }
            Some(ElaboratedHeader::Nominal {
                layout: ElaboratedNominalLayout::Opaque,
                ..
            })
            | None => return Err(()),
            _ => return Err(()),
        },
        Type::Array(element) | Type::StaticData { element, .. } => {
            if type_may_contain_reference(signatures, element) {
                return Err(());
            }
        }
        Type::Projection { .. } | Type::Generic(_) | Type::Infer(_) => return Err(()),
        // The pointer is a value, but its pointee is not a resident reference
        // leaf. Dereferencing/converting it must establish fresh unsafe
        // obligations rather than inherit a fictitious checked loan here.
        Type::RawPointer { .. } => {},
        Type::Callable { .. }
        | Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Error => {}
    }
    Ok(())
}

fn type_may_contain_reference(signatures: &ElaboratedInterface, ty: &Type) -> bool {
    // Array elements are not projection paths, but the array branch still
    // needs to reject a potentially reference-bearing element. Do that with
    // a cycle-aware structural walk instead of re-entering the path walker:
    // `enum Chain { Node(Array<Chain>) }` is heap-indirected and finite at
    // runtime, whereas recursively opening its element layout here used to
    // overflow the compiler stack.
    fn visit(
        signatures: &ElaboratedInterface,
        ty: &Type,
        active: &mut std::collections::BTreeSet<crate::DefKey>,
    ) -> bool {
        match ty {
            Type::Reference { .. } => true,
            Type::Tuple(fields) => fields.iter().any(|field| visit(signatures, field, active)),
            Type::Array(element) | Type::StaticData { element, .. } => {
                visit(signatures, element, active)
            }
            Type::Nominal {
                definition,
                arguments,
            } => {
                // A repeated nominal lies behind at least one array on this
                // walk. Do not expand it again: every direct field of this
                // application is visited during its first occurrence, while
                // array elements never contribute a stable caller projection.
                if !active.insert(*definition) {
                    return false;
                }
                let result = match signatures.definitions.get(definition) {
                    Some(ElaboratedHeader::Nominal {
                        layout: ElaboratedNominalLayout::Struct(fields),
                        ..
                    }) => fields.iter().any(|field| {
                        instantiate_nominal_field_type(&field.ty, arguments)
                            .map_or(true, |field| visit(signatures, &field, active))
                    }),
                    Some(ElaboratedHeader::Nominal {
                        layout: ElaboratedNominalLayout::Enum(variants),
                        ..
                    }) => variants.iter().any(|variant| match &variant.payload {
                        crate::signature::ElaboratedEnumVariantPayload::Unit => false,
                        crate::signature::ElaboratedEnumVariantPayload::Tuple(fields) => {
                            fields.iter().any(|field| {
                                instantiate_nominal_field_type(field, arguments).map_or(true, |field| {
                                    visit(signatures, &field, active)
                                })
                            })
                        }
                        crate::signature::ElaboratedEnumVariantPayload::Struct(fields) => {
                            fields.iter().any(|field| {
                                instantiate_nominal_field_type(&field.ty, arguments).map_or(true, |field| {
                                    visit(signatures, &field, active)
                                })
                            })
                        }
                    }),
                    Some(ElaboratedHeader::Nominal {
                        layout: ElaboratedNominalLayout::Opaque,
                        ..
                    })
                    | None => true,
                    _ => true,
                };
                active.remove(definition);
                result
            }
            Type::Projection { .. } | Type::Generic(_) | Type::Infer(_) => true,
            Type::RawPointer { .. } => false,
            Type::Callable { .. }
            | Type::Unit
            | Type::Never
            | Type::Scalar(_)
            | Type::ConstU32(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. }
            | Type::Error => false,
        }
    }

    visit(signatures, ty, &mut std::collections::BTreeSet::new())
}

pub(crate) fn instantiate_nominal_field_type(
    ty: &Type,
    arguments: &[GenericArgument],
) -> Result<Type, ()> {
    match ty {
        Type::Generic(index) => match arguments.get(*index as usize) {
            Some(GenericArgument::Type(ty)) => Ok(ty.clone()),
            _ => Err(()),
        },
        Type::Tuple(fields) => fields
            .iter()
            .map(|field| instantiate_nominal_field_type(field, arguments))
            .collect::<Result<Vec<_>, _>>()
            .map(Type::Tuple),
        Type::Array(element) => Ok(Type::Array(Box::new(instantiate_nominal_field_type(
            element, arguments,
        )?))),
        Type::RawPointer { mutability, pointee } => Ok(Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(instantiate_nominal_field_type(pointee, arguments)?),
        }),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Ok(Type::Reference {
            mutability: *mutability,
            lifetime: instantiate_nominal_field_lifetime(*lifetime, arguments)?,
            referent: Box::new(instantiate_nominal_field_type(referent, arguments)?),
        }),
        Type::Nominal {
            definition,
            arguments: nested,
        } => Ok(Type::Nominal {
            definition: *definition,
            arguments: nested
                .iter()
                .map(|argument| instantiate_nominal_generic_argument(argument, arguments))
                .collect::<Result<_, _>>()?,
        }),
        value => Ok(value.clone()),
    }
}

fn instantiate_nominal_field_lifetime(
    lifetime: Lifetime,
    arguments: &[GenericArgument],
) -> Result<Lifetime, ()> {
    match lifetime {
        Lifetime::Generic(index) => match arguments.get(index as usize) {
            Some(GenericArgument::Lifetime(lifetime)) => Ok(*lifetime),
            _ => Err(()),
        },
        lifetime => Ok(lifetime),
    }
}

fn instantiate_nominal_generic_argument(
    argument: &GenericArgument,
    arguments: &[GenericArgument],
) -> Result<GenericArgument, ()> {
    match argument {
        GenericArgument::Type(ty) => {
            instantiate_nominal_field_type(ty, arguments).map(GenericArgument::Type)
        }
        // A lifetime nested in a nominal application is just as much part of
        // that field's instantiated type as a nested type argument. Leaving
        // `Slice<'a, T>` as `Slice<'generic-0, T>` while opening an enclosing
        // `Str<'static>` hid its static reference leaf from callable
        // provenance analysis and made sound source wrappers appear opaque.
        GenericArgument::Lifetime(lifetime) => {
            instantiate_nominal_field_lifetime(*lifetime, arguments).map(GenericArgument::Lifetime)
        }
        value => Ok(value.clone()),
    }
}

fn instantiate_nominal_default(
    default: &GenericArgument,
    arguments: &[GenericArgument],
) -> GenericArgument {
    match default {
        GenericArgument::ConstGeneric { index, .. } => arguments
            .get(*index as usize)
            .cloned()
            .unwrap_or_else(|| default.clone()),
        GenericArgument::ConstU32Expr(value) => match value.substitute(arguments) {
            crate::StructuralU32Expr::Literal(value) => GenericArgument::ConstU32(value),
            value => GenericArgument::ConstU32Expr(value),
        },
        value => value.clone(),
    }
}

fn structural_const_error(kind: crate::ConstKind) -> GenericArgument {
    match kind {
        crate::ConstKind::U32 => GenericArgument::ConstU32(0),
        crate::ConstKind::Quantity => {
            GenericArgument::ConstQuantity(crate::quantity::Quantity::ONCE)
        }
    }
}

fn record_capture(
    captures: &mut std::collections::BTreeMap<String, (CaptureMode, Type)>,
    name: &str,
    mode: CaptureMode,
    ty: Type,
) {
    let rank = |mode| match mode {
        CaptureMode::SharedBorrow => 0,
        CaptureMode::Copy => 1,
        // Reading a copyable value must not turn an earlier write to the
        // enclosing place into mutation of a private copied environment.
        CaptureMode::UniqueBorrow => 2,
        CaptureMode::Move => 3,
    };
    match captures.get_mut(name) {
        Some((existing, _)) if rank(*existing) >= rank(mode) => {}
        Some(value) => *value = (mode, ty),
        None => {
            captures.insert(name.to_owned(), (mode, ty));
        }
    }
}

fn closure_scalar(name: &str) -> Option<ScalarType> {
    use ScalarType::*;
    Some(match name {
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "u128" => U128,
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "i128" => I128,
        "usize" => Usize,
        "isize" => Isize,
        "f32" => F32,
        "f64" => F64,
        "char" => Char,
        "Text" => Text,
        "Bytes" => Bytes,
        _ => return None,
    })
}

#[cfg(test)]
mod invariant_call_lifetime_tests {
    use super::*;

    fn inner(lifetime: Lifetime) -> Type {
        Type::Reference { mutability: Mutability::Shared, lifetime, referent: Box::new(Type::Scalar(ScalarType::I64)) }
    }

    fn storage(lifetime: Lifetime, pointer: bool) -> Type {
        if pointer {
            Type::RawPointer { mutability: crate::PointerMutability::Mut, pointee: Box::new(inner(lifetime)) }
        } else {
            Type::Reference { mutability: Mutability::Unique, lifetime: Lifetime::Elided, referent: Box::new(inner(lifetime)) }
        }
    }

    #[test]
    fn reverse_invariance_uses_the_opened_callee_contract() {
        for pointer in [false, true] {
            for expected in [Lifetime::Generic(0), Lifetime::Bound { depth: 0, index: 0 }] {
                for actual in [Lifetime::Static, Lifetime::Generic(7)] {
                    let mut substitution = CallLifetimeSubstitution::default();
                    // An unrelated callee binder shares an index with the
                    // caller's rigid name. Reverse checking must not open it.
                    substitution.generics.insert(7, Lifetime::Elided);
                    let found = align_lifetime_types(&storage(expected, pointer), &storage(actual, pointer),
                        &mut substitution, LifetimeMode::Instantiate, 0);
                    assert!(found.is_ok(), "{expected:?}, {actual:?}, pointer={pointer}");
                    assert_eq!(substitution.generics[&7], Lifetime::Elided);
                }
            }
        }
    }

    #[test]
    fn reverse_invariance_does_not_erase_fixed_or_rigid_region_requirements() {
        for pointer in [false, true] {
            for (expected, actual, mode) in [
                (Lifetime::Static, Lifetime::Elided, LifetimeMode::Instantiate),
                (Lifetime::Elided, Lifetime::Static, LifetimeMode::Instantiate),
                (Lifetime::Generic(0), Lifetime::Generic(1), LifetimeMode::Rigid),
            ] {
                let result = align_lifetime_types(&storage(expected, pointer), &storage(actual, pointer),
                    &mut CallLifetimeSubstitution::default(), mode, 0);
                assert!(matches!(result, Err(LifetimeError::UnsatisfiedOutlives)), "{expected:?}, {actual:?}, pointer={pointer}");
            }
        }
    }
}
