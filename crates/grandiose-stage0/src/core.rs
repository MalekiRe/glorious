//! Typed Core, the semantic boundary before ownership facts and MIR.

use crate::{
    body::{BodySyntax, ClosureParameter, ExprId, ExprKind, HandlerClause},
    fixity::FixityTable,
    header::FixityForm,
    identity::{DefKey, Digest, ModuleKey},
    interface::{Definition, DefinitionNamespace},
    pattern::{PatternDecision, elaborate_pattern},
    resolution::{DefinitionIndex, ResolutionState, ScopeMap},
    signature::{ElaboratedEffect, ElaboratedHeader, ElaboratedInterface},
    source::Span,
    trait_solver::{
        TraitAnswer, TraitEffectRowProjectionAnswer, TraitGoal, TraitMethodAnswer,
        TraitProjectionAnswer, TraitSolver,
    },
    types::{
        EffectInstance, EffectRow, GenericArgument, InferContext, Lifetime, Mutability, ScalarType,
        Type,
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
    Move,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureCapture {
    pub name: String,
    pub mode: CaptureMode,
    pub ty: Type,
}
/// A closure's complete, post-inference environment.  Capture mode selection
/// remains the responsibility of PlaceFlow; this record seals that selected
/// layout together with the callable that is allowed to consume it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CaptureEnvironment {
    pub brand: EnvironmentBrand,
    pub captures: Vec<ClosureCapture>,
    pub sealed: bool,
}
/// Positive evidence produced by `is`. Bindings remain facts rather than
/// ordinary locals until a branching consumer opens their lexical scope; this
/// prevents a test expression from silently leaking a pattern binder.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RefinementEnvironment {
    pub brand: RefinementBrand,
    pub subject: Option<String>,
    pub bindings: Vec<String>,
    pub sealed: bool,
}
impl CaptureEnvironment {
    fn seal(owner: DefKey, callable: CallableId, captures: Vec<ClosureCapture>) -> Self {
        Self {
            brand: EnvironmentBrand { owner, callable },
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
    Record {
        definition: DefKey,
        field_count: u32,
        fields: Vec<CorePatternField>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
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
    pub body: CoreId,
    pub span: Span,
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
    },
    /// A direct function value selected from a trait implementation. Retain
    /// proof evidence alongside the callable key until MIR consumes this
    /// source-free selection, rather than reconstructing lookup from a name.
    TraitMethod {
        evidence: DefKey,
        method: DefKey,
        trait_arguments: Vec<GenericArgument>,
        method_arguments: Vec<GenericArgument>,
    },
    Constant(DefKey),
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
    },
    /// Canonical effect performance selected by the effect namespace, never a
    /// value function merely named like an operation.
    Perform {
        effect: EffectInstance,
        operation: u32,
        arguments: Vec<CoreId>,
        terminal: bool,
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
    },
    Binary {
        operator: String,
        left: CoreId,
        right: CoreId,
    },
    Block(Vec<CoreId>),
    Borrow {
        unique: bool,
        value: CoreId,
    },
    /// Read through a shared or unique reference without consuming the loan.
    Deref(CoreId),
    Move(CoreId),
    Unary {
        operator: String,
        value: CoreId,
    },
    Error,
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
        for (index, expression) in self.expressions.iter().enumerate() {
            let owner = CoreId(index as u32);
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
            if type_contains_inference(&expression.ty)
                || core_metadata_contains_inference(&expression.kind)
            {
                diagnostics.push(CoreDiagnostic {
                    code: "G4181",
                    span: expression.span,
                    message: "Typed Core expression or embedded metadata retains an unresolved inference variable".into(),
                });
            }
            if core_kind_is_recovered(&expression.kind) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4182",
                    span: expression.span,
                    message: "Typed Core contains a recovered structural form".into(),
                });
            }
            if let Some(message) = core_structural_error(&expression.kind) {
                diagnostics.push(CoreDiagnostic {
                    code: "G4183",
                    span: expression.span,
                    message,
                });
            }
        }
        diagnostics
    }

    fn contains(&self, id: CoreId) -> bool {
        (id.0 as usize) < self.expressions.len()
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
        self.debug(&expression.ty);
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
            CoreKind::Function {
                definition,
                arguments,
            } => {
                self.bytes(b"function");
                self.debug(definition);
                self.debug(arguments);
            }
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
            } => {
                self.bytes(b"trait-method");
                self.debug(evidence);
                self.debug(method);
                self.debug(trait_arguments);
                self.debug(method_arguments);
            }
            CoreKind::Constant(definition) => {
                self.bytes(b"constant");
                self.debug(definition);
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
                self.debug(pattern);
                self.debug(refinement);
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
                self.debug(parameters);
                self.debug(environment);
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
                self.debug(place);
                self.id(*value);
            }
            CoreKind::Call { callee, arguments } => {
                self.bytes(b"call");
                self.id(*callee);
                self.ids(arguments);
            }
            CoreKind::Perform {
                effect,
                operation,
                arguments,
                terminal,
            } => {
                self.bytes(b"perform");
                self.debug(effect);
                self.bytes(&operation.to_le_bytes());
                self.bytes(&[*terminal as u8]);
                self.ids(arguments);
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.bytes(b"handle");
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.debug(&clause.effect);
                    self.bytes(&clause.operation.to_le_bytes());
                    self.debug(&clause.payload_types);
                    self.debug(&clause.patterns);
                    self.debug(&clause.bindings);
                    self.debug(&clause.resumption);
                    self.debug(&clause.continuation);
                    self.bytes(&[clause.terminal as u8]);
                    self.id(clause.body);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                self.bytes(b"completion");
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.debug(&clause.pattern);
                    self.debug(&clause.bindings);
                    self.id(clause.body);
                }
            }
            CoreKind::Binary {
                operator,
                left,
                right,
            } => {
                self.bytes(b"binary");
                self.bytes(operator.as_bytes());
                self.id(*left);
                self.id(*right);
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
            CoreKind::Unary { operator, value } => {
                self.bytes(b"unary");
                self.bytes(operator.as_bytes());
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
        | CoreKind::Unary { value: base, .. }
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
        CoreKind::Call { callee, arguments } => std::iter::once(*callee)
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
        } => std::iter::once(*computation)
            .chain(clauses.iter().map(|clause| clause.body))
            .collect(),
        CoreKind::Binary { left, right, .. } => vec![*left, *right],
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::Function { .. }
        | CoreKind::TraitMethod { .. }
        | CoreKind::Constant(_)
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

fn core_structural_error(kind: &CoreKind) -> Option<String> {
    match kind {
        CoreKind::Closure {
            callable,
            environment,
            ..
        } => capture_environment_error(*callable, environment),
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
        CoreKind::Completion { clauses, .. } => clauses
            .iter()
            .find_map(|clause| pattern_structural_error(&clause.pattern)),
        _ => None,
    }
}

fn refinement_environment_error(environment: &RefinementEnvironment) -> Option<String> {
    if !environment.sealed {
        return Some("Typed Core pattern test has an unsealed refinement environment".into());
    }
    let mut bindings = std::collections::BTreeSet::new();
    for binding in &environment.bindings {
        if !bindings.insert(binding) {
            return Some(format!(
                "Typed Core refinement environment repeats binding `{binding}`"
            ));
        }
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

fn capture_environment_error(
    callable: CallableId,
    environment: &CaptureEnvironment,
) -> Option<String> {
    if !environment.sealed {
        return Some("Typed Core closure has an unsealed capture environment".into());
    }
    if environment.brand.callable != callable {
        return Some("Typed Core closure environment brand belongs to another callable".into());
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

fn pattern_structural_error(pattern: &CorePattern) -> Option<String> {
    match pattern {
        CorePattern::Tuple(values) => values.iter().find_map(pattern_structural_error),
        CorePattern::Record {
            field_count,
            fields,
            ..
        }
        | CorePattern::Enum {
            field_count,
            fields,
            ..
        } => {
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
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => fields
            .iter()
            .any(|field| pattern_is_recovered(&field.pattern)),
        CorePattern::Any | CorePattern::Bind { .. } | CorePattern::Literal(_) => false,
    }
}

fn type_contains_inference(ty: &Type) -> bool {
    match ty {
        Type::Infer(_) => true,
        Type::Nominal { arguments, .. } | Type::Tuple(arguments) => {
            arguments.iter().any(type_contains_inference)
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_contains_inference(subject)
                || trait_arguments.iter().any(type_contains_inference)
                || item_arguments.iter().any(type_contains_inference)
        }
        Type::Array(element)
        | Type::Reference {
            referent: element, ..
        } => type_contains_inference(element),
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
                            .any(type_contains_inference)
                        || projection
                            .item_arguments
                            .iter()
                            .any(type_contains_inference)
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

fn generic_argument_contains_inference(argument: &GenericArgument) -> bool {
    match argument {
        GenericArgument::Type(value) => type_contains_inference(value),
        GenericArgument::EffectRow(value) => effect_row_contains_inference(value),
        _ => false,
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
        }
        CoreKind::Assign { place, .. } => place_contains_inference(place),
        CoreKind::Function { arguments, .. } => {
            arguments.iter().any(generic_argument_contains_inference)
        }
        CoreKind::Perform { effect, .. } => effect
            .arguments
            .iter()
            .any(generic_argument_contains_inference),
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
        }),
        CoreKind::Literal(_)
        | CoreKind::Local(_)
        | CoreKind::Resumption { .. }
        | CoreKind::TraitMethod { .. }
        | CoreKind::Constant(_)
        | CoreKind::Tuple(_)
        | CoreKind::Array(_)
        | CoreKind::Record { .. }
        | CoreKind::Field { .. }
        | CoreKind::Enum { .. }
        | CoreKind::Let { .. }
        | CoreKind::Label { .. }
        | CoreKind::Transfer { .. }
        | CoreKind::Call { .. }
        | CoreKind::Binary { .. }
        | CoreKind::Block(_)
        | CoreKind::Borrow { .. }
        | CoreKind::Deref(_)
        | CoreKind::Move(_)
        | CoreKind::Unary { .. }
        | CoreKind::Error => false,
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
                    .any(type_contains_inference)
                || projection
                    .item_arguments
                    .iter()
                    .any(type_contains_inference)
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

fn pattern_contains_inference(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Tuple(values) => values.iter().any(pattern_contains_inference),
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            fields.iter().any(|field| {
                type_contains_inference(&field.ty) || pattern_contains_inference(&field.pattern)
            })
        }
        CorePattern::Any
        | CorePattern::Bind { .. }
        | CorePattern::Literal(_)
        | CorePattern::Error => false,
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
            body,
            index,
            signatures,
            fixities,
            definition: definition.key,
            module: &definition.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
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
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_tracker: None,
        };
        let expected_result = signatures
            .definitions
            .get(&definition.key)
            .and_then(callable)
            .map(|signature| signature.result.clone());
        let expected_result =
            expected_result.map(|result| elaborator.normalize_concrete_type_projections(result));
        let mut parameters = vec![];
        if let Some(signature) = signatures
            .definitions
            .get(&definition.key)
            .and_then(callable)
        {
            if let Some(header) = definition.callable_header() {
                for (parameter, ty) in header.parameters.iter().zip(signature.parameters.iter()) {
                    elaborator.locals.define(parameter.name.clone(), ty.clone());
                    parameters.push((parameter.name.clone(), ty.clone()));
                }
            }
        } else {
            elaborator.error(
                definition.span,
                "G4100",
                "body belongs to a non-callable declaration",
            );
        }
        let root = elaborator.expression(body.root);
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
            body,
            index,
            signatures,
            fixities,
            definition: DefKey(Digest::of_parts([
                b"grandiose-stage0-implementation-method".as_slice(),
                implementation.key.0.as_bytes().as_slice(),
                context.method.name.as_bytes(),
            ])),
            module: &implementation.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
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
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_tracker: None,
        };
        let mut parameters = vec![];
        for (parameter, ty) in context
            .method
            .signature
            .parameters
            .iter()
            .zip(context.signature.parameters.iter())
        {
            elaborator.locals.define(parameter.name.clone(), ty.clone());
            parameters.push((parameter.name.clone(), ty.clone()));
        }
        let root = elaborator.expression(body.root);
        let actual = elaborator.expressions[root.0 as usize].ty.clone();
        if elaborator
            .unify_rigid_lifetimes(
                context.signature.result.clone(),
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
        let mut elaborator = Elaborator {
            body,
            index,
            signatures,
            fixities,
            definition: definition.key,
            module: &definition.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            next_resumption: 0,
            next_refinement: 0,
            next_label: 0,
            generic_parameters: std::collections::BTreeMap::new(),
            effect_row_parameters: std::collections::BTreeMap::new(),
            lifetime_parameters: std::collections::BTreeMap::new(),
            bound_lifetime_scopes: vec![],
            const_parameters: std::collections::BTreeMap::new(),
            declared_effects: EffectRow::empty(),
            ambient_where_bounds: vec![],
            handled_effects: std::collections::BTreeSet::new(),
            handled_operations: std::collections::BTreeSet::new(),
            active_resumptions: vec![],
            resumption_bindings: std::collections::BTreeMap::new(),
            active_labels: vec![],
            resumption_use_tracker: None,
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
        let root = elaborator.expression(body.root);
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
            parameters: vec![],
            expressions: elaborator.expressions,
            root,
            diagnostics: elaborator.diagnostics,
            recovered: elaborator.recovered,
        }
    }
}

fn callable(header: &ElaboratedHeader) -> Option<&crate::signature::CallableSignature> {
    match header {
        ElaboratedHeader::Callable(value) => Some(value),
        _ => None,
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

struct Elaborator<'a> {
    body: &'a BodySyntax,
    index: &'a DefinitionIndex,
    signatures: &'a ElaboratedInterface,
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
    /// Installed only while one explicit handler arm is elaborated. Nested
    /// handler arms replace and restore it, preserving lexical continuation
    /// identity rather than counting an accidentally shadowed spelling.
    resumption_use_tracker: Option<ResumptionUseTracker>,
}
impl Elaborator<'_> {
    fn expression(&mut self, id: ExprId) -> CoreId {
        let expression = self.body.expression(id).clone();
        match expression.kind {
            ExprKind::Literal(text) => self.alloc(
                CoreKind::Literal(text.clone()),
                literal_type(&text),
                expression.span,
            ),
            ExprKind::Path(path) => self
                .enum_constructor(path.clone(), vec![], expression.span)
                .unwrap_or_else(|| self.path(path, expression.span)),
            ExprKind::GenericPath { .. } => self.fail(
                expression.span,
                "G4151",
                "a generic effect instance must be followed by an operation call",
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
                self.alloc(CoreKind::Let { name, value }, Type::Unit, expression.span)
            }
            ExprKind::Label { name, body } => {
                let brand = LabelBrand {
                    owner: self.definition,
                    label: self.next_label,
                };
                self.next_label += 1;
                let result = self.inference.fresh();
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
                if self.inference.unify(result.clone(), body_type).is_err() {
                    self.error(
                        expression.span,
                        "G4178",
                        "label body and transfers have incompatible result types",
                    );
                    self.recovered = true;
                }
                self.alloc(CoreKind::Label { brand, body }, result, expression.span)
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
                    label.result,
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
                self.alloc(
                    CoreKind::Assign { place, value },
                    Type::Unit,
                    expression.span,
                )
            }
            ExprKind::Block(values) | ExprKind::ContextualBlock(values) => {
                self.locals.enter();
                let values = values
                    .into_iter()
                    .map(|value| self.expression(value))
                    .collect::<Vec<_>>();
                let ty = values
                    .last()
                    .map(|value| self.expressions[value.0 as usize].ty.clone())
                    .unwrap_or(Type::Unit);
                self.locals.leave();
                self.alloc(CoreKind::Block(values), ty, expression.span)
            }
            ExprKind::Tuple(values) => {
                let values = values
                    .into_iter()
                    .map(|value| self.expression(value))
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
                self.alloc(CoreKind::Tuple(values), ty, expression.span)
            }
            ExprKind::Array(values) => {
                let element = self.inference.fresh();
                let values = values
                    .into_iter()
                    .map(|value| {
                        let value = self.expression(value);
                        let actual = self.expressions[value.0 as usize].ty.clone();
                        if self.inference.unify(element.clone(), actual).is_err() {
                            self.error(
                                expression.span,
                                "G4119",
                                "array elements have incompatible types",
                            );
                            self.recovered = true;
                        }
                        value
                    })
                    .collect();
                self.alloc(
                    CoreKind::Array(values),
                    Type::Array(Box::new(element)),
                    expression.span,
                )
            }
            ExprKind::Record { path, fields } => self.record(path, fields, expression.span),
            ExprKind::Field { base, name } => self.field(base, name, expression.span),
            ExprKind::Is { subject, pattern } => {
                let subject = self.expression(subject);
                let subject_type = self.zonk_type(
                    self.expressions[subject.0 as usize].ty.clone(),
                    expression.span,
                );
                let elaboration = elaborate_pattern(
                    self.body,
                    pattern,
                    subject_type.clone(),
                    self.index,
                    self.signatures,
                    self.module,
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
                let refinement = self.refinement_environment(subject, &pattern);
                self.alloc(
                    CoreKind::PatternTest {
                        subject,
                        pattern,
                        refinement,
                    },
                    Type::Scalar(ScalarType::Bool),
                    expression.span,
                )
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => self.handle(computation, clauses, expression.span),
            ExprKind::Call { callee, arguments } => {
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
                    && let Some(value) =
                        self.enum_constructor(path.clone(), arguments.clone(), expression.span)
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
                        let effect_arguments = effect_arguments
                            .iter()
                            .map(|argument| self.header_type(argument))
                            .collect::<Vec<_>>();
                        let operation_arguments = operation_arguments
                            .iter()
                            .map(|argument| self.header_type(argument))
                            .collect::<Vec<_>>();
                        if let Some(value) = self.trait_method_call(
                            path.clone(),
                            effect_arguments.clone(),
                            operation_arguments.clone(),
                            arguments.clone(),
                            expression.span,
                        ) {
                            return value;
                        }
                        if let Some(value) = self.perform(
                            path.clone(),
                            effect_arguments,
                            operation_arguments,
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
                    && let Some(value) = self.empty_braced_nominal(path.clone(), expression.span)
                {
                    return value;
                }
                let callee = self.expression(callee);
                self.record_resumption_call(callee);
                let expected = match self.expressions[callee.0 as usize].ty.clone() {
                    Type::Callable { parameters, .. } => Some(parameters),
                    _ => None,
                };
                let arguments = arguments
                    .into_iter()
                    .enumerate()
                    .map(|(index, value)| {
                        self.expression_expected(
                            value,
                            expected
                                .as_ref()
                                .and_then(|parameters| parameters.get(index))
                                .cloned(),
                        )
                    })
                    .collect();
                self.call(callee, arguments, expression.span)
            }
            ExprKind::OperatorChain {
                operands,
                operators,
            } => self.operators(operands, operators, expression.span),
            ExprKind::Borrow { unique, value } => {
                let value = self.expression(value);
                let ty = self.expressions[value.0 as usize].ty.clone();
                self.alloc(
                    CoreKind::Borrow { unique, value },
                    Type::Reference {
                        mutability: if unique {
                            Mutability::Unique
                        } else {
                            Mutability::Shared
                        },
                        lifetime: Lifetime::Elided,
                        referent: Box::new(ty),
                    },
                    expression.span,
                )
            }
            ExprKind::Deref(value) => {
                let value = self.expression(value);
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
                expression.span,
            ),
            ExprKind::TypedClosure {
                parameters,
                result,
                effects,
                body,
            } => self.closure(parameters, result, effects, body, expression.span),
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
    fn expression_expected(&mut self, id: ExprId, expected: Option<Type>) -> CoreId {
        let expression = self.body.expression(id).clone();
        let ExprKind::ContextualBlock(values) = expression.kind else {
            return self.expression(id);
        };
        match expected {
            Some(Type::Callable {
                parameters,
                result,
                effects,
                invocation,
                ..
            }) if parameters.is_empty() => self.contextual_zero_arg_closure(
                values,
                *result,
                effects,
                invocation,
                expression.span,
            ),
            Some(Type::Callable { .. }) => self.fail(
                expression.span,
                "G4118",
                "contextual block requires explicit parameters for a nonzero-argument callable",
            ),
            Some(_) => self.expression(id),
            None => self.fail(
                expression.span,
                "G4118",
                "contextual block has no resolved expected type",
            ),
        }
    }
    fn contextual_zero_arg_closure(
        &mut self,
        values: Vec<ExprId>,
        result: Type,
        effects: crate::types::EffectRow,
        invocation: crate::quantity::Quantity,
        span: Span,
    ) -> CoreId {
        self.locals.enter();
        // A contextual block is a callable body, not an eager continuation
        // of its enclosing expression. Its expected callable row therefore
        // governs any operations in the block, and enclosing handlers cannot
        // be captured as though they would still be active when it runs.
        let previous_effects = std::mem::replace(&mut self.declared_effects, effects.clone());
        let previous_handled = std::mem::take(&mut self.handled_effects);
        let previous_handled_operations = std::mem::take(&mut self.handled_operations);
        let values = values
            .into_iter()
            .map(|value| self.expression(value))
            .collect::<Vec<_>>();
        self.declared_effects = previous_effects;
        self.handled_effects = previous_handled;
        self.handled_operations = previous_handled_operations;
        let body_ty = values
            .last()
            .map(|value| self.expressions[value.0 as usize].ty.clone())
            .unwrap_or(Type::Unit);
        let body = self.alloc(CoreKind::Block(values), body_ty.clone(), span);
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
        let parameters = vec![];
        let captures = self.closure_captures(body, &parameters);
        self.check_resumption_captures(&captures, span);
        self.check_label_transfer_escape(body, span);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters,
                environment: CaptureEnvironment::seal(self.definition, callable, captures),
                body,
            },
            Type::Callable {
                lifetime_binders: 0,
                parameters: vec![],
                result: Box::new(result),
                effects,
                invocation,
            },
            span,
        )
    }
    fn closure(
        &mut self,
        parameters: Vec<ClosureParameter>,
        declared_result: Option<crate::header::HeaderType>,
        effects: crate::header::EffectRowHeader,
        body: ExprId,
        span: Span,
    ) -> CoreId {
        let parameters = parameters
            .into_iter()
            .map(|parameter| {
                let ty = parameter
                    .ty
                    .as_ref()
                    .map(|ty| self.header_type(ty))
                    .unwrap_or_else(|| self.inference.fresh());
                (parameter.name, ty)
            })
            .collect::<Vec<_>>();
        let effects = self.closure_effects(&effects, span);
        self.locals.enter();
        for (name, ty) in &parameters {
            self.locals.define(name.clone(), ty.clone());
        }
        // A typed closure freezes an independent callable contract. Check
        // its body against that contract and do not let an enclosing handler
        // discharge effects that may escape with the closure value.
        let previous_effects = std::mem::replace(&mut self.declared_effects, effects.clone());
        let previous_handled = std::mem::take(&mut self.handled_effects);
        let previous_handled_operations = std::mem::take(&mut self.handled_operations);
        let body = self.expression(body);
        self.declared_effects = previous_effects;
        self.handled_effects = previous_handled;
        self.handled_operations = previous_handled_operations;
        self.locals.leave();
        let actual_result = self.expressions[body.0 as usize].ty.clone();
        let result = declared_result
            .as_ref()
            .map(|ty| self.header_type(ty))
            .unwrap_or_else(|| actual_result.clone());
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
        self.check_resumption_captures(&captures, span);
        self.check_label_transfer_escape(body, span);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters: parameters.clone(),
                environment: CaptureEnvironment::seal(self.definition, callable, captures),
                body,
            },
            Type::Callable {
                lifetime_binders: 0,
                parameters: parameters.into_iter().map(|(_, ty)| ty).collect(),
                result: Box::new(result),
                effects,
                invocation: crate::quantity::Quantity::ONCE,
            },
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
                lifetime_binders,
                parameters,
                result,
            } => {
                let scope = lifetime_binders
                    .iter()
                    .enumerate()
                    .map(|(index, name)| (name.clone(), index as u32))
                    .collect();
                self.bound_lifetime_scopes.push(scope);
                let parameters = parameters
                    .iter()
                    .map(|value| self.header_type(value))
                    .collect();
                let result = Box::new(self.header_type(result));
                self.bound_lifetime_scopes.pop();
                Type::Callable {
                    lifetime_binders: lifetime_binders.len() as u32,
                    parameters,
                    result,
                    effects: crate::types::EffectRow::empty(),
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
        match TraitSolver::new(self.signatures).normalize_type(value) {
            Ok(value) => value,
            Err(answer) => self.projection_normalization_error(*answer),
        }
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
        let Some(trait_arguments) = self.header_generic_arguments(trait_arguments, trait_kinds)
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
            trait_arguments,
            name: name.to_owned(),
            item_arguments,
        };
        if !projection_is_concrete(&projection) {
            return projection;
        }
        let Type::Projection {
            subject,
            trait_arguments,
            name,
            item_arguments,
            ..
        } = &projection
        else {
            unreachable!("projection was just constructed")
        };
        let answer = TraitSolver::new(self.signatures).normalize_associated_type_application(
            TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: trait_definition,
                    arguments: trait_arguments
                        .clone()
                        .into_iter()
                        .map(crate::GenericArgument::Type)
                        .collect(),
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
    ) -> Option<Vec<Type>> {
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
                        crate::header::HeaderGenericArgument::Type(value),
                        crate::GenericKind::Type,
                    ) => self.header_type(value),
                    (
                        crate::header::HeaderGenericArgument::U32(value),
                        crate::GenericKind::Const(crate::ConstKind::U32),
                    ) => Type::ConstU32(*value),
                    (
                        crate::header::HeaderGenericArgument::Quantity(value),
                        crate::GenericKind::Const(crate::ConstKind::Quantity),
                    ) => Type::ConstQuantity(*value),
                    (
                        crate::header::HeaderGenericArgument::Type(
                            crate::header::HeaderType::Path(path),
                        ),
                        crate::GenericKind::Const(kind),
                    ) if path.len() == 1 => match self.const_parameters.get(&path[0]).copied() {
                        Some((index, found)) if found == *kind => {
                            Type::ConstGeneric { index, kind: *kind }
                        }
                        _ => {
                            self.projection_error(
                                "G4158",
                                "const generic argument has the wrong kind",
                            );
                            Type::Error
                        }
                    },
                    _ => {
                        self.projection_error("G4158", "generic argument has the wrong kind");
                        Type::Error
                    }
                })
                .collect(),
        )
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
        }
        match self
            .index
            .resolve_path(DefinitionNamespace::Type, self.module, path)
        {
            ResolutionState::Resolved(definition) => {
                let kinds = self.index.type_generic_kinds(definition).unwrap_or(&[]);
                if kinds.len() != arguments.len() {
                    return Type::Error;
                }
                Type::Nominal {
                    definition,
                    arguments: arguments
                        .iter()
                        .zip(kinds)
                        .map(|(argument, kind)| match (argument, kind) {
                            (
                                crate::header::HeaderGenericArgument::Type(value),
                                crate::GenericKind::Type,
                            ) => self.header_type(value),
                            (
                                crate::header::HeaderGenericArgument::U32(value),
                                crate::GenericKind::Const(crate::ConstKind::U32),
                            ) => Type::ConstU32(*value),
                            (
                                crate::header::HeaderGenericArgument::Quantity(value),
                                crate::GenericKind::Const(crate::ConstKind::Quantity),
                            ) => Type::ConstQuantity(*value),
                            (
                                crate::header::HeaderGenericArgument::Type(
                                    crate::header::HeaderType::Path(path),
                                ),
                                crate::GenericKind::Const(kind),
                            ) if path.len() == 1 => self
                                .const_parameters
                                .get(&path[0])
                                .filter(|(_, found)| found == kind)
                                .map_or(Type::Error, |(index, kind)| Type::ConstGeneric {
                                    index: *index,
                                    kind: *kind,
                                }),
                            _ => Type::Error,
                        })
                        .collect(),
                }
            }
            ResolutionState::Ambiguous(_) => Type::Error,
            ResolutionState::Inaccessible(_)
            | ResolutionState::Unresolved
            | ResolutionState::Recovered => Type::Error,
        }
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
                    if declaration.generics != arguments.len() as u32 {
                        self.error(
                            span,
                            "G4115",
                            "closure effect application has the wrong number of arguments",
                        );
                        self.recovered = true;
                        continue;
                    }
                    resolved.effects.insert(EffectInstance {
                        definition,
                        arguments: arguments
                            .iter()
                            .map(|argument| {
                                GenericArgument::Type(match argument {
                                    crate::header::HeaderGenericArgument::Type(argument) => {
                                        self.header_type(argument)
                                    }
                                    crate::header::HeaderGenericArgument::U32(_) => Type::Error,
                                    crate::header::HeaderGenericArgument::Quantity(_) => {
                                        Type::Error
                                    }
                                    crate::header::HeaderGenericArgument::Lifetime(_) => {
                                        Type::Error
                                    }
                                    crate::header::HeaderGenericArgument::EffectRow(_) => {
                                        Type::Error
                                    }
                                })
                            })
                            .collect(),
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
                        || !trait_arguments.iter().all(projection_is_concrete)
                        || !item_arguments.iter().all(projection_is_concrete)
                    {
                        self.error(
                            span,
                            "G4115",
                            "closure associated effect-row projection must be concrete",
                        );
                        self.recovered = true;
                        continue;
                    }
                    match TraitSolver::new(self.signatures)
                        .normalize_associated_effect_row_application(
                            TraitGoal {
                                relation: crate::ElaboratedTraitReference {
                                    definition: trait_definition,
                                    arguments: trait_arguments
                                        .into_iter()
                                        .map(crate::GenericArgument::Type)
                                        .collect(),
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
    fn refinement_environment(
        &mut self,
        subject: CoreId,
        pattern: &CorePattern,
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
            bindings,
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
    /// Continuations are frame-bound identities. Capturing one by a nested
    /// closure would let it survive the handler frame that owns it, which the
    /// current continuation lowering deliberately has no representation for.
    /// Direct invocation remains valid; this is only the closure-capture
    /// product boundary.
    fn check_resumption_captures(&mut self, captures: &[ClosureCapture], span: Span) {
        if let Some(capture) = captures
            .iter()
            .find(|capture| self.active_resumption(&capture.name).is_some())
        {
            self.error(
                span,
                "G4174",
                &format!(
                    "nested closure cannot capture handler resumption `{}` before continuations have an escaping representation",
                    capture.name
                ),
            );
            self.recovered = true;
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
                    CaptureMode::SharedBorrow,
                    expression.ty.clone(),
                );
            }
            CoreKind::Resumption { name, .. } if !locals.contains(name) => {
                record_capture(
                    captures,
                    name,
                    CaptureMode::SharedBorrow,
                    expression.ty.clone(),
                );
            }
            CoreKind::Move(value) => {
                if let CoreKind::Local(name) = &self.expressions[value.0 as usize].kind {
                    record_capture(
                        captures,
                        name,
                        CaptureMode::Move,
                        self.expressions[value.0 as usize].ty.clone(),
                    );
                } else {
                    self.collect_captures(*value, locals, captures);
                }
            }
            CoreKind::Unary { value, .. } | CoreKind::Deref(value) => {
                self.collect_captures(*value, locals, captures)
            }
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
            CoreKind::Call { callee, arguments } => {
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
            CoreKind::Binary { left, right, .. } => {
                self.collect_captures(*left, locals, captures);
                self.collect_captures(*right, locals, captures);
            }
            CoreKind::Block(values) => {
                let mut scoped = locals.clone();
                for value in values {
                    self.collect_captures(*value, &mut scoped, captures);
                }
            }
            CoreKind::Closure { .. }
            | CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
            CoreKind::Local(_) => {}
        }
    }
    /// Typed Core is a frozen semantic boundary: body-local inference holes
    /// can help elaboration but cannot escape to PlaceFlow, MIR, or caches.
    fn seal_types(&mut self) {
        for index in 0..self.expressions.len() {
            let span = self.expressions[index].span;
            let ty = self.expressions[index].ty.clone();
            self.expressions[index].ty = self.zonk_type(ty, span);
            let kind = self.expressions[index].kind.clone();
            self.expressions[index].kind = self.zonk_core_metadata(kind, span);
        }
    }

    fn zonk_core_metadata(&mut self, mut kind: CoreKind, span: Span) -> CoreKind {
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
            }
            CoreKind::Assign { place, .. } => self.zonk_place(place, span),
            CoreKind::Label { .. } | CoreKind::Transfer { .. } => {}
            CoreKind::Function { arguments, .. } => {
                *arguments = arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
            }
            CoreKind::Perform { effect, .. } => {
                effect.arguments = effect
                    .arguments
                    .iter()
                    .cloned()
                    .map(|argument| self.zonk_generic_argument(argument, span))
                    .collect();
            }
            CoreKind::PatternTest { pattern, .. } => self.zonk_pattern(pattern, span),
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
            CoreKind::Completion { clauses, .. } => {
                for clause in clauses {
                    self.zonk_pattern(&mut clause.pattern, span);
                    for (_, ty) in &mut clause.bindings {
                        *ty = self.zonk_type(ty.clone(), span);
                    }
                }
            }
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Tuple(_)
            | CoreKind::Array(_)
            | CoreKind::Record { .. }
            | CoreKind::Field { .. }
            | CoreKind::Enum { .. }
            | CoreKind::Let { .. }
            | CoreKind::Call { .. }
            | CoreKind::Binary { .. }
            | CoreKind::Block(_)
            | CoreKind::Borrow { .. }
            | CoreKind::Deref(_)
            | CoreKind::Move(_)
            | CoreKind::Unary { .. }
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
            CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
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
        match argument {
            GenericArgument::Type(value) => GenericArgument::Type(self.zonk_type(value, span)),
            GenericArgument::EffectRow(value) => {
                GenericArgument::EffectRow(self.zonk_effect_row(value, span))
            }
            argument => argument,
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
    ) -> Result<(Vec<Type>, Type, crate::types::EffectRow), ()> {
        let mut substitution = CallLifetimeSubstitution::default();
        let mut aligned_parameters = Vec::with_capacity(parameters.len());
        for (parameter, argument) in parameters.iter().zip(arguments) {
            let actual = self.expressions[argument.0 as usize].ty.clone();
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
        Ok((aligned_parameters, result, effects))
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
                    .instantiate_struct_fields(actual, &arguments)
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
                    .instantiate_enum_fields(actual, &arguments, variant)
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
            ResolutionState::Resolved(definition) => match self
                .signatures
                .definitions
                .get(&definition)
                .and_then(callable)
            {
                Some(signature) => {
                    let generic_kinds = signature.generic_kinds.clone();
                    // Callable signatures still substitute value types
                    // through their legacy type-only representation. Reserve
                    // every source slot there, but mint inference variables
                    // only for slots that are actually type-kinded. The
                    // canonical Core identity below retains the real kind so
                    // a row, region, or const never becomes a bogus type
                    // inference variable merely to satisfy this compatibility
                    // boundary.
                    let type_arguments = generic_kinds
                        .iter()
                        .map(|kind| match kind {
                            crate::GenericKind::Type => self.inference.fresh(),
                            crate::GenericKind::EffectRow
                            | crate::GenericKind::Lifetime
                            | crate::GenericKind::Const(_) => Type::Error,
                        })
                        .collect::<Vec<_>>();
                    let signature = self
                        .signatures
                        .instantiate_callable(definition, &type_arguments)
                        .expect("fresh arguments match the callable generic arity");
                    let arguments = generic_kinds
                        .iter()
                        .enumerate()
                        .map(|(index, kind)| match kind {
                            crate::GenericKind::Type => {
                                GenericArgument::Type(type_arguments[index].clone())
                            }
                            crate::GenericKind::EffectRow => {
                                GenericArgument::EffectRow(EffectRow::empty())
                            }
                            crate::GenericKind::Lifetime => {
                                GenericArgument::Lifetime(Lifetime::Elided)
                            }
                            crate::GenericKind::Const(kind) => GenericArgument::ConstGeneric {
                                index: index as u32,
                                kind: *kind,
                            },
                        })
                        .collect();
                    self.alloc(
                        CoreKind::Function {
                            definition,
                            arguments,
                        },
                        Type::Callable {
                            lifetime_binders: 0,
                            parameters: signature.parameters,
                            result: Box::new(signature.result),
                            effects: signature.effects,
                            invocation: signature.invocation,
                        },
                        span,
                    )
                }
                None => match self.signatures.definitions.get(&definition) {
                    Some(ElaboratedHeader::Constant(Some(ty))) => {
                        self.alloc(CoreKind::Constant(definition), ty.clone(), span)
                    }
                    Some(ElaboratedHeader::Constant(None)) => {
                        self.fail(span, "G4102", "constant value has no frozen type")
                    }
                    _ => self.fail(span, "G4102", "value does not have a callable signature"),
                },
            },
            ResolutionState::Ambiguous(_) => self.fail(span, "G4103", "ambiguous value reference"),
            ResolutionState::Inaccessible(_) => self.fail(
                span,
                "G4104",
                "value reference is private to another module",
            ),
            _ => self.fail(span, "G4104", "unresolved value reference"),
        }
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
        if let Some(tracker) = &mut self.resumption_use_tracker
            && tracker.identity.id == identity.id
        {
            tracker.direct_uses = tracker.direct_uses.saturating_add(1);
        }
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
                    .instantiate_struct_fields(definition, &arguments)
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
                if !matches!(mutability, Mutability::Unique) {
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
    fn record(&mut self, path: Vec<String>, fields: Vec<(String, ExprId)>, span: Span) -> CoreId {
        if let Some(value) = self.enum_record_constructor(path.clone(), fields.clone(), span) {
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
        let generic_count = match self.signatures.definitions.get(&definition) {
            Some(ElaboratedHeader::Nominal { generics, .. }) => *generics as usize,
            _ => return self.fail(span, "G4123", "record constructor is not a struct type"),
        };
        let arguments = (0..generic_count)
            .map(|_| self.inference.fresh())
            .collect::<Vec<_>>();
        let Some(layout) = self
            .signatures
            .instantiate_struct_fields(definition, &arguments)
        else {
            return self.fail(span, "G4123", "record constructor is not a struct type");
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
            let value = self.expression_expected(value, Some(field.ty.clone()));
            let actual = self.expressions[value.0 as usize].ty.clone();
            if self.unify_rigid_lifetimes(field.ty, actual, span).is_err() {
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
        self.alloc(
            CoreKind::Record {
                definition,
                fields: values,
            },
            ty,
            span,
        )
    }
    fn empty_braced_nominal(&mut self, path: Vec<String>, span: Span) -> Option<CoreId> {
        if self.empty_enum_record_constructor(&path) {
            return self.enum_record_constructor(path, vec![], span);
        }
        self.empty_record_constructor(path, span)
    }
    fn empty_record_constructor(&mut self, path: Vec<String>, span: Span) -> Option<CoreId> {
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
        fields.is_empty().then(|| self.record(path, vec![], span))
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
        supplied_fields: Vec<(String, ExprId)>,
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
        let generic_count = match self.signatures.definitions.get(&definition) {
            Some(ElaboratedHeader::Nominal { generics, .. }) => *generics as usize,
            _ => return None,
        };
        let arguments = (0..generic_count)
            .map(|_| self.inference.fresh())
            .collect::<Vec<_>>();
        let (variant, layout) = self.signatures.instantiate_enum_record_variant(
            definition,
            &arguments,
            variant_name,
        )?;
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
        Some(self.alloc(
            CoreKind::Enum {
                definition,
                variant,
                fields,
            },
            Type::Nominal {
                definition,
                arguments,
            },
            span,
        ))
    }
    fn field(&mut self, base: ExprId, name: String, span: Span) -> CoreId {
        let base = self.expression(base);
        let base_ty = self.expressions[base.0 as usize].ty.clone();
        let Type::Nominal {
            definition,
            arguments,
        } = base_ty
        else {
            return self.fail(span, "G4128", "field projection requires a struct value");
        };
        let Some(fields) = self
            .signatures
            .instantiate_struct_fields(definition, &arguments)
        else {
            return self.fail(span, "G4128", "field projection requires a struct value");
        };
        let field_count = fields.len() as u32;
        let Some((index, field)) = fields
            .into_iter()
            .enumerate()
            .find(|(_, field)| field.name == name)
        else {
            return self.fail(span, "G4129", "struct does not declare the requested field");
        };
        self.alloc(
            CoreKind::Field {
                base,
                index: index as u32,
                field_count,
            },
            field.ty,
            span,
        )
    }
    fn enum_constructor(
        &mut self,
        path: Vec<String>,
        supplied: Vec<ExprId>,
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
        let generic_count = match self.signatures.definitions.get(&definition) {
            Some(ElaboratedHeader::Nominal { generics, .. }) => *generics as usize,
            _ => return None,
        };
        let arguments = (0..generic_count)
            .map(|_| self.inference.fresh())
            .collect::<Vec<_>>();
        let (variant, fields) =
            self.signatures
                .instantiate_enum_variant(definition, &arguments, variant_name)?;
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
            .collect();
        Some(self.alloc(
            CoreKind::Enum {
                definition,
                variant,
                fields: values,
            },
            Type::Nominal {
                definition,
                arguments,
            },
            span,
        ))
    }
    fn prefix(&mut self, operator: String, value: ExprId, span: Span) -> CoreId {
        if self.fixities.prefix(&operator).is_none() {
            return self.fail(
                span,
                "G4111",
                "operator has no visible prefix fixity declaration",
            );
        }
        let value = self.expression(value);
        let value_ty = self.expressions[value.0 as usize].ty.clone();
        let result = match (operator.as_str(), &value_ty) {
            ("+" | "-", Type::Scalar(ScalarType::I64 | ScalarType::F64)) => value_ty.clone(),
            ("!", Type::Scalar(ScalarType::Bool)) => Type::Scalar(ScalarType::Bool),
            _ => {
                return self.fail(
                    span,
                    "G4117",
                    "prefix operator has incompatible operand type",
                );
            }
        };
        self.alloc(CoreKind::Unary { operator, value }, result, span)
    }
    fn call(&mut self, callee: CoreId, arguments: Vec<CoreId>, span: Span) -> CoreId {
        let callable = self.expressions[callee.0 as usize].ty.clone();
        let Type::Callable {
            parameters,
            result,
            effects,
            ..
        } = callable
        else {
            return self.fail(span, "G4105", "called expression is not callable");
        };
        if parameters.len() != arguments.len() {
            return self.fail(
                span,
                "G4106",
                "call argument count does not match callable signature",
            );
        }
        let Ok((parameters, result, effects)) =
            self.instantiate_call_lifetimes(parameters, *result, effects, &arguments, span)
        else {
            return self.fail(
                span,
                "G5017",
                "call cannot satisfy its reference lifetime contract",
            );
        };
        for (parameter, argument) in parameters.into_iter().zip(&arguments) {
            let actual = self.expressions[argument.0 as usize].ty.clone();
            if self.inference.unify(parameter, actual).is_err() {
                self.error(span, "G4107", "call argument type does not match parameter");
                self.recovered = true;
            }
        }
        self.check_effects(&effects, span);
        self.check_call_where_bounds(callee, span);
        self.alloc(CoreKind::Call { callee, arguments }, result, span)
    }
    /// Resolve an explicitly-qualified trait method call. The method's first
    /// declared parameter is the receiver; qualification keeps this initial
    /// surface free of accidental field-vs-method ambiguity while preserving
    /// the solver evidence and selected implementation identity for MIR.
    fn trait_method_call(
        &mut self,
        path: Vec<String>,
        trait_arguments: Vec<Type>,
        operation_arguments: Vec<Type>,
        supplied: Vec<ExprId>,
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
        if trait_arguments.len() != trait_header.generics as usize {
            return Some(self.fail(
                span,
                "G4168",
                "trait method qualification has the wrong number of trait arguments",
            ));
        }
        let Some(method_header) = trait_header.methods.get(name) else {
            return Some(self.fail(span, "G4168", "trait does not declare the requested method"));
        };
        let values = supplied
            .into_iter()
            .map(|value| self.expression(value))
            .collect::<Vec<_>>();
        let Some(receiver) = values.first().copied() else {
            return Some(self.fail(
                span,
                "G4168",
                "qualified trait method call requires a receiver argument",
            ));
        };
        let subject = self.zonk_type(self.expressions[receiver.0 as usize].ty.clone(), span);
        let method_arguments = if operation_arguments.is_empty() {
            (0..method_header.generics)
                .map(|_| self.inference.fresh())
                .collect::<Vec<_>>()
        } else {
            if operation_arguments.len() != method_header.generics as usize {
                return Some(self.fail(
                    span,
                    "G4168",
                    "trait method operation arguments do not match its declaration",
                ));
            }
            operation_arguments
        };
        let trait_arguments = trait_arguments
            .into_iter()
            .map(crate::GenericArgument::Type)
            .collect::<Vec<_>>();
        let method_arguments = method_arguments
            .into_iter()
            .map(crate::GenericArgument::Type)
            .collect::<Vec<_>>();
        let answer = TraitSolver::new(self.signatures).select_method(
            TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: trait_definition,
                    arguments: trait_arguments.clone(),
                },
                subject,
            },
            name,
            &method_arguments
                .iter()
                .filter_map(|argument| match argument {
                    crate::GenericArgument::Type(ty) => Some(ty.clone()),
                    _ => None,
                })
                .collect::<Vec<_>>(),
        );
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
        let callee = self.alloc(
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
            },
            Type::Callable {
                lifetime_binders: 0,
                parameters: signature.parameters.clone(),
                result: Box::new(signature.result.clone()),
                effects: signature.effects.clone(),
                invocation: signature.invocation,
            },
            span,
        );
        let call = self.call(callee, values, span);
        self.check_where_bounds(signature.where_bounds.clone(), span);
        Some(call)
    }
    fn perform(
        &mut self,
        path: Vec<String>,
        effect_arguments: Vec<Type>,
        operation_arguments: Vec<Type>,
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
        if effect.generics as usize != effect_arguments.len() {
            return Some(self.fail(
                span,
                "G4151",
                "effect operation protocol arguments do not match its declaration",
            ));
        }
        let operation_arguments =
            match self.operation_generic_arguments(effect, operation_name, operation_arguments) {
                Some(arguments) => arguments,
                None => {
                    return Some(self.fail(
                        span,
                        "G4152",
                        "effect does not declare the requested operation",
                    ));
                }
            };
        let Some((operation_index, operation)) = self.signatures.instantiate_effect_operation(
            effect_definition,
            &effect_arguments,
            &operation_arguments,
            operation_name,
        ) else {
            return Some(self.fail(
                span,
                "G4152",
                "effect operation arguments do not match its declaration",
            ));
        };
        if operation.parameters.len() != arguments.len() {
            return Some(self.fail(
                span,
                "G4153",
                "effect operation argument count does not match its declaration",
            ));
        }
        let values = arguments
            .into_iter()
            .zip(&operation.parameters)
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
        let instance = EffectInstance {
            definition: effect_definition,
            arguments: effect_arguments
                .into_iter()
                .map(GenericArgument::Type)
                .collect(),
        };
        self.check_effect_instance(&instance, Some(operation_index), span);
        Some(self.alloc(
            CoreKind::Perform {
                effect: instance,
                operation: operation_index,
                arguments: values,
                terminal: operation.terminal,
            },
            operation.result.clone(),
            span,
        ))
    }
    /// Supply operation-generic arguments independently from the enclosing
    /// effect instance. Omitted arguments become caller-owned inference
    /// variables; explicit applications must have the exact operation arity.
    fn operation_generic_arguments(
        &mut self,
        effect: &ElaboratedEffect,
        name: &str,
        supplied: Vec<Type>,
    ) -> Option<Vec<Type>> {
        let operation = effect
            .operations
            .iter()
            .find(|operation| operation.name == name)?;
        let count = operation.generics.checked_sub(effect.generics)? as usize;
        if supplied.is_empty() && count != 0 {
            return Some((0..count).map(|_| self.inference.fresh()).collect());
        }
        (supplied.len() == count).then_some(supplied)
    }
    fn handle(&mut self, computation: ExprId, clauses: Vec<HandlerClause>, span: Span) -> CoreId {
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
            return self.completion_handle(computation, &completion_clauses, span);
        }
        let mut resolved = Vec::with_capacity(operation_clauses.len());
        for clause in operation_clauses {
            resolved.push(self.resolve_handler_clause(clause));
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
        let result = self.inference.fresh();
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
                        lifetime_binders: 0,
                        parameters: vec![clause.operation.result.clone()],
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
            let previous_tracker = active_identity.as_ref().map(|identity| {
                self.resumption_use_tracker.replace(ResumptionUseTracker {
                    identity: identity.clone(),
                    direct_uses: 0,
                })
            });
            let body = self.expression(clause.source.body);
            let direct_uses = if active_identity.is_some() {
                self.resumption_use_tracker
                    .take()
                    .map(|tracker| tracker.direct_uses)
                    .unwrap_or(0)
            } else {
                0
            };
            if let Some(previous) = previous_tracker {
                self.resumption_use_tracker = previous;
            }
            if active_identity.is_some() {
                self.active_resumptions
                    .pop()
                    .expect("active handler resumption must outlive its clause body");
            }
            self.locals.leave();
            let body_ty = self.expressions[body.0 as usize].ty.clone();
            let expected = match resumption {
                CoreHandlerResumption::Tail { .. } => clause.operation.result.clone(),
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
                    parameter: clause.operation.result.clone(),
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
                &clause.operation.result,
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
                payload_types: clause.operation.parameters.clone(),
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
            self.completion_handle_core(handler, &completion_clauses, span)
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
        span: Span,
    ) -> CoreId {
        let subject = self.expression(computation);
        self.completion_handle_core(subject, clauses, span)
    }
    fn completion_handle_core(
        &mut self,
        subject: CoreId,
        clauses: &[HandlerClause],
        span: Span,
    ) -> CoreId {
        // Operation-arm inference has already established the handler result
        // by the time normal-completion dispatch is built.  Resolve that
        // result before elaborating literal or structural patterns: the
        // pattern elaborator deliberately compares concrete subjects and
        // would otherwise reject a valid refutable arm against an unresolved
        // inference variable.
        let subject_ty = self.zonk_type(self.expressions[subject.0 as usize].ty.clone(), span);
        let result = self.inference.fresh();
        let mut core_clauses = Vec::with_capacity(clauses.len());
        for clause in clauses {
            let Some(pattern) = clause.completion else {
                return self.fail(
                    clause.span,
                    "G4166",
                    "mixed completion and operation handler arms",
                );
            };
            let elaboration = elaborate_pattern(
                self.body,
                pattern,
                subject_ty.clone(),
                self.index,
                self.signatures,
                self.module,
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
            let bindings = elaboration
                .plan
                .bindings
                .iter()
                .map(|binding| (binding.name.clone(), binding.ty.clone()))
                .collect::<Vec<_>>();
            self.locals.enter();
            for (name, ty) in &bindings {
                self.locals.define(name.clone(), ty.clone());
            }
            let body = self.expression(clause.body);
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
                pattern: self.core_pattern(
                    elaboration.plan.decision,
                    elaboration.plan.subject,
                    clause.span,
                    Some(&names),
                ),
                bindings,
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
        self.alloc(
            CoreKind::Completion {
                computation: subject,
                clauses: core_clauses,
            },
            result,
            span,
        )
    }
    /// Check an ordered pattern matrix against the finite structural domains
    /// available to Stage 0.  Unlike the former constructor-only check, this
    /// follows nested tuple, record, and enum payload decisions.  It is a
    /// proof procedure, not a heuristic: unknown/infinite/recursive domains
    /// are left open and still require an irrefutable arm.
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
        if covered_by_catch_all {
            analysis.exhaustive = true;
            return analysis;
        }

        let Some(values) = self.finite_pattern_values(subject, 0) else {
            return analysis;
        };
        for (index, pattern) in patterns.iter().enumerate() {
            let useful = values.iter().any(|value| {
                core_pattern_matches_value(pattern, value)
                    && !patterns[..index]
                        .iter()
                        .any(|earlier| core_pattern_matches_value(earlier, value))
            });
            if !useful {
                analysis.unreachable.push(index);
            }
        }
        analysis.exhaustive = values.iter().all(|value| {
            patterns
                .iter()
                .any(|pattern| core_pattern_matches_value(pattern, value))
        });
        analysis
    }

    /// Enumerate a closed structural domain with a deliberately modest cap.
    /// The cap preserves predictable compilation while keeping the proof
    /// complete for all domains it accepts; exceeding it means "unknown",
    /// never a false claim of coverage.
    fn finite_pattern_values(&self, subject: &Type, depth: u8) -> Option<Vec<FinitePatternValue>> {
        const MAX_VALUES: usize = 4096;
        const MAX_DEPTH: u8 = 16;
        if depth >= MAX_DEPTH {
            return None;
        }
        match subject {
            Type::Unit => Some(vec![FinitePatternValue::Unit]),
            Type::Scalar(ScalarType::Bool) => Some(vec![
                FinitePatternValue::Bool(false),
                FinitePatternValue::Bool(true),
            ]),
            Type::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.finite_pattern_values(field, depth + 1))
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
                        .instantiate_struct_fields(*definition, arguments)?;
                    let values = fields
                        .iter()
                        .map(|field| self.finite_pattern_values(&field.ty, depth + 1))
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
                    for (variant, _) in variants.iter().enumerate() {
                        let fields = self.signatures.instantiate_enum_fields(
                            *definition,
                            arguments,
                            variant as u32,
                        )?;
                        let fields = fields
                            .iter()
                            .map(|field| self.finite_pattern_values(&field.ty, depth + 1))
                            .collect::<Option<Vec<_>>>()?;
                        let products = finite_pattern_products(fields, MAX_VALUES)?;
                        if values.len().checked_add(products.len())? > MAX_VALUES {
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
                } => None,
                _ => None,
            },
            _ => None,
        }
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
        let effect_arguments = source
            .effect_arguments
            .iter()
            .map(|argument| self.header_type(argument))
            .collect::<Vec<_>>();
        let operation_arguments = source
            .operation_arguments
            .iter()
            .map(|argument| self.header_type(argument))
            .collect::<Vec<_>>();
        if declaration.generics as usize != effect_arguments.len() {
            self.error(
                source.span,
                "G4163",
                "handler effect arguments do not match its declaration",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        }
        let Some(operation_arguments) =
            self.operation_generic_arguments(declaration, operation_name, operation_arguments)
        else {
            self.error(
                source.span,
                "G4162",
                "handler operation arguments do not match its declaration",
            );
            self.recovered = true;
            return ResolvedHandlerClause::error(source);
        };
        let Some((operation_index, operation)) = self.signatures.instantiate_effect_operation(
            effect,
            &effect_arguments,
            &operation_arguments,
            operation_name,
        ) else {
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
                let elaboration = elaborate_pattern(
                    self.body,
                    pattern,
                    subject,
                    self.index,
                    self.signatures,
                    self.module,
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
                arguments: effect_arguments
                    .into_iter()
                    .map(GenericArgument::Type)
                    .collect(),
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
    /// the same finite inhabitant domain as normal-completion coverage, so a
    /// handler can discharge an operation through nested enum/record/tuple
    /// patterns without falsely treating a partially refined payload as total.
    /// Unknown, recursive, or over-large domains remain conservatively
    /// outward-facing.
    fn handler_operation_is_exhaustive(&self, rows: &[&ResolvedHandlerClause]) -> bool {
        if rows
            .iter()
            .any(|row| row.patterns.iter().all(|pattern| !pattern.plan.refutable))
        {
            return true;
        }
        let Some(first) = rows.first() else {
            return false;
        };
        if rows
            .iter()
            .any(|row| row.patterns.len() != first.patterns.len())
        {
            return false;
        }
        let domains = first
            .patterns
            .iter()
            .map(|pattern| self.finite_pattern_values(&pattern.plan.subject, 0))
            .collect::<Option<Vec<_>>>();
        let Some(domains) = domains else {
            return false;
        };
        let Some(assignments) = finite_pattern_products(domains, 4096) else {
            return false;
        };
        assignments.iter().all(|assignment| {
            rows.iter().any(|row| {
                row.patterns.iter().zip(assignment).all(|(pattern, value)| {
                    pattern_decision_matches_value(&pattern.plan.decision, value)
                })
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
                self.error(span, "G4155", "call has an unresolved outward effect row");
                self.recovered = true;
                return;
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
            && self.declared_effects.tail != Some(tail)
        {
            self.error(
                span,
                "G4155",
                "call has an outward effect-row tail not admitted by this callable",
            );
            self.recovered = true;
            return;
        }
        let mut projections = std::mem::take(&mut effects.projections);
        while let Some(projection) = projections.pop() {
            if !projection_is_concrete(&projection.subject)
                || !projection
                    .trait_arguments
                    .iter()
                    .all(projection_is_concrete)
                || !projection.item_arguments.iter().all(projection_is_concrete)
            {
                self.error(
                    span,
                    "G4155",
                    "call has an unresolved associated effect-row projection",
                );
                self.recovered = true;
                return;
            }
            match TraitSolver::new(self.signatures).normalize_associated_effect_row_application(
                TraitGoal {
                    relation: crate::ElaboratedTraitReference {
                        definition: projection.trait_definition,
                        arguments: projection
                            .trait_arguments
                            .into_iter()
                            .map(crate::GenericArgument::Type)
                            .collect(),
                    },
                    subject: *projection.subject,
                },
                &projection.name,
                &projection.item_arguments,
            ) {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    effects.effects.extend(row.effects);
                    projections.extend(row.projections);
                    if row.tail.is_some() {
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
    fn check_call_where_bounds(&mut self, callee: CoreId, span: Span) {
        let (definition, arguments) = match &self.expressions[callee.0 as usize].kind {
            CoreKind::Function {
                definition,
                arguments,
            } => (*definition, arguments.clone()),
            _ => return,
        };
        // The legacy callable-substitution API still accepts a type vector.
        // Preserve its source-slot alignment with placeholders for non-type
        // arguments; those cannot occur in a value-type where-bound subject,
        // and their canonical identities remain on `CoreKind::Function`.
        let arguments = arguments
            .into_iter()
            .map(|argument| match argument {
                GenericArgument::Type(argument) => argument,
                GenericArgument::EffectRow(_)
                | GenericArgument::Lifetime(_)
                | GenericArgument::ConstU32(_)
                | GenericArgument::ConstQuantity(_)
                | GenericArgument::ConstGeneric { .. } => Type::Error,
            })
            .collect::<Vec<_>>();
        let Some(signature) = self.signatures.instantiate_callable(definition, &arguments) else {
            self.error(
                span,
                "G4140",
                "direct call lost its frozen callable signature",
            );
            self.recovered = true;
            return;
        };
        self.check_where_bounds(signature.where_bounds, span);
    }
    fn check_where_bounds(
        &mut self,
        bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
        span: Span,
    ) {
        let mut solver = TraitSolver::new(self.signatures);
        let mut failed = false;
        for (subject, relation) in bounds {
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
            if self.ambient_where_bound_proves(&goal) {
                continue;
            }
            match solver.solve(goal) {
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
    /// Discharge an obligation directly from the declaration contract in
    /// scope.  This intentionally uses structural equality after zonking
    /// rather than extending the global trait solver: a caller's assumptions
    /// must never become implementation evidence for another callable.
    fn ambient_where_bound_proves(&mut self, goal: &TraitGoal) -> bool {
        self.ambient_where_bounds.iter().any(|(subject, relation)| {
            self.inference
                .zonk(subject.clone())
                .ok()
                .is_some_and(|subject| subject == goal.subject && relation == &goal.relation)
        })
    }
    fn operators(&mut self, operands: Vec<ExprId>, operators: Vec<String>, span: Span) -> CoreId {
        if operands.len() != operators.len().saturating_add(1) {
            return self.fail(span, "G4108", "malformed operator chain");
        }
        let values = operands
            .into_iter()
            .map(|value| self.expression(value))
            .collect::<Vec<_>>();
        let Some(first) = values.first().copied() else {
            return self.fail(span, "G4108", "operator chain has no operands");
        };
        let mut output = vec![first];
        let mut stack = Vec::<String>::new();
        for (operator, right) in operators.into_iter().zip(values.into_iter().skip(1)) {
            let Some(fixity) = self.fixities.infix(&operator).cloned() else {
                return self.fail(
                    span,
                    "G4111",
                    "operator has no visible infix fixity declaration",
                );
            };
            if fixity.form == FixityForm::Prefix {
                return self.fail(span, "G4111", "operator is only declared as prefix");
            }
            while let Some(top) = stack.last() {
                let top_fixity = self
                    .fixities
                    .infix(top)
                    .expect("operator stack contains only resolved fixities");
                if top_fixity.precedence == fixity.precedence
                    && (top_fixity.form == FixityForm::InfixNonAssociative
                        || fixity.form == FixityForm::InfixNonAssociative)
                {
                    return self.fail(
                        span,
                        "G4112",
                        "non-associative operators of equal precedence require parentheses",
                    );
                }
                let reduce = top_fixity.precedence > fixity.precedence
                    || (top_fixity.precedence == fixity.precedence
                        && fixity.form != FixityForm::InfixRight);
                if !reduce {
                    break;
                }
                if !self.reduce_operator(&mut output, &mut stack, span) {
                    return self.fail(span, "G4108", "malformed operator chain");
                }
            }
            stack.push(operator);
            output.push(right);
        }
        while !stack.is_empty() {
            if !self.reduce_operator(&mut output, &mut stack, span) {
                return self.fail(span, "G4108", "malformed operator chain");
            }
        }
        output
            .pop()
            .expect("valid operator chain retains one result")
    }
    fn reduce_operator(
        &mut self,
        values: &mut Vec<CoreId>,
        operators: &mut Vec<String>,
        span: Span,
    ) -> bool {
        let Some(operator) = operators.pop() else {
            return false;
        };
        let (Some(right), Some(left)) = (values.pop(), values.pop()) else {
            return false;
        };
        let left_ty = self.expressions[left.0 as usize].ty.clone();
        let right_ty = self.expressions[right.0 as usize].ty.clone();
        let operand_ty = match self.inference.unify(left_ty.clone(), right_ty) {
            Ok(ty) => ty,
            Err(_) => {
                self.fail(span, "G4109", "operator operands have incompatible types");
                return false;
            }
        };
        let numeric = matches!(operand_ty, Type::Scalar(ScalarType::I64 | ScalarType::F64));
        let text = matches!(operand_ty, Type::Scalar(ScalarType::Text));
        let ordered = numeric || matches!(operand_ty, Type::Scalar(ScalarType::Char));
        let equality = ordered
            || matches!(
                operand_ty,
                Type::Scalar(ScalarType::Bool | ScalarType::Text)
            );
        let result = match operator.as_str() {
            "and" | "or" if matches!(operand_ty, Type::Scalar(ScalarType::Bool)) => {
                Type::Scalar(ScalarType::Bool)
            }
            "+" if text => operand_ty,
            "+" | "-" | "*" | "/" | "%" if numeric => operand_ty,
            "==" | "!=" if equality => Type::Scalar(ScalarType::Bool),
            "<" | "<=" | ">" | ">=" if ordered => Type::Scalar(ScalarType::Bool),
            _ => {
                self.fail(span, "G4117", "operator has incompatible operand type");
                return false;
            }
        };
        values.push(self.alloc(
            CoreKind::Binary {
                operator,
                left,
                right,
            },
            result,
            span,
        ));
        true
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
    fn error(&mut self, span: Span, code: &'static str, message: &str) {
        self.diagnostics.push(CoreDiagnostic {
            code,
            span,
            message: message.into(),
        });
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
            Ok(Type::Reference {
                mutability: *expected_mutability,
                // The actual lifetime is intentionally retained here. A
                // longer `'static` argument may satisfy an elided parameter;
                // ordinary type unification must not turn that safe coercion
                // back into an equality failure.
                lifetime: *actual_lifetime,
                referent: Box::new(align_lifetime_types(
                    expected_referent,
                    actual_referent,
                    substitution,
                    mode,
                    depth,
                )?),
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
                        align_lifetime_types(expected, actual, substitution, mode, depth)
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
                item_arguments: expected_item_arguments,
            },
            Type::Projection {
                subject: actual_subject,
                trait_definition: actual_trait,
                trait_arguments: actual_trait_arguments,
                name: actual_name,
                item_arguments: actual_item_arguments,
            },
        ) if expected_trait == actual_trait
            && expected_name == actual_name
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
                        align_lifetime_types(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
                name: expected_name.clone(),
                item_arguments: expected_item_arguments
                    .iter()
                    .zip(actual_item_arguments)
                    .map(|(expected, actual)| {
                        align_lifetime_types(expected, actual, substitution, mode, depth)
                    })
                    .collect::<Result<_, _>>()?,
            })
        }
        (
            Type::Callable {
                lifetime_binders: expected_binders,
                parameters: expected_parameters,
                result: expected_result,
                effects: expected_effects,
                invocation: expected_invocation,
            },
            Type::Callable {
                lifetime_binders: actual_binders,
                parameters: actual_parameters,
                result: actual_result,
                effects: actual_effects,
                invocation: actual_invocation,
            },
        ) if expected_binders == actual_binders
            && expected_parameters.len() == actual_parameters.len()
            && expected_effects == actual_effects
            && expected_invocation == actual_invocation =>
        {
            Ok(Type::Callable {
                lifetime_binders: *expected_binders,
                parameters: expected_parameters
                    .iter()
                    .zip(actual_parameters)
                    .map(|(expected, actual)| {
                        align_lifetime_types(expected, actual, substitution, mode, depth + 1)
                    })
                    .collect::<Result<_, _>>()?,
                result: Box::new(align_lifetime_types(
                    expected_result,
                    actual_result,
                    substitution,
                    mode,
                    depth + 1,
                )?),
                effects: expected_effects.clone(),
                invocation: *expected_invocation,
            })
        }
        // Let ordinary type inference diagnose any non-reference structural
        // mismatch. Returning `expected` here keeps generic type variables
        // inferable at the same locations as before this lifetime pass.
        _ => Ok(expected.clone()),
    }
}

fn bind_lifetime(
    expected: Lifetime,
    actual: Lifetime,
    substitution: &mut CallLifetimeSubstitution,
    mode: LifetimeMode,
    depth: u32,
) -> Result<(), LifetimeError> {
    match expected {
        Lifetime::Static => (actual == Lifetime::Static)
            .then_some(())
            .ok_or(LifetimeError::UnsatisfiedOutlives),
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
                .map(|value| substitute_call_lifetimes(value, substitution, depth))
                .collect::<Result<_, _>>()?,
        }),
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Ok(Type::Projection {
            subject: Box::new(substitute_call_lifetimes(*subject, substitution, depth)?),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_call_lifetimes(value, substitution, depth))
                .collect::<Result<_, _>>()?,
            name,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_call_lifetimes(value, substitution, depth))
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
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Ok(Type::Callable {
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
                    .map(|value| substitute_call_lifetimes(value, substitution, depth))
                    .collect::<Result<_, _>>()?,
                name: projection.name,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_call_lifetimes(value, substitution, depth))
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
        Type::Nominal { arguments, .. } | Type::Tuple(arguments) => {
            arguments.iter().all(projection_is_concrete)
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            projection_is_concrete(subject)
                && trait_arguments.iter().all(projection_is_concrete)
                && item_arguments.iter().all(projection_is_concrete)
        }
        Type::Array(element)
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

fn literal_type(text: &str) -> Type {
    if matches!(text, "true" | "false") {
        Type::Scalar(ScalarType::Bool)
    } else if text.starts_with('"') {
        Type::Scalar(ScalarType::Text)
    } else if text.starts_with('\'') {
        Type::Scalar(ScalarType::Char)
    } else if text.contains('.') || text.contains('e') || text.contains('E') {
        Type::Scalar(ScalarType::F64)
    } else {
        Type::Scalar(ScalarType::I64)
    }
}

fn core_pattern_irrefutable(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => true,
        CorePattern::Tuple(values) => values.iter().all(core_pattern_irrefutable),
        CorePattern::Record { fields, .. } => fields
            .iter()
            .all(|field| core_pattern_irrefutable(&field.pattern)),
        CorePattern::Literal(_) | CorePattern::Enum { .. } | CorePattern::Error => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CorePatternMatrixAnalysis {
    exhaustive: bool,
    unreachable: Vec<usize>,
}

/// A concrete inhabitant of a small, closed structural type.  This exists
/// only during Core validation: neither MIR nor the VM receives an invented
/// value, only the already typed pattern decision that this proof validates.
#[derive(Clone, Debug, Eq, PartialEq)]
enum FinitePatternValue {
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

fn finite_pattern_products(
    columns: Vec<Vec<FinitePatternValue>>,
    limit: usize,
) -> Option<Vec<Vec<FinitePatternValue>>> {
    let mut products = vec![vec![]];
    for column in columns {
        let count = products.len().checked_mul(column.len())?;
        if count > limit {
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

fn core_pattern_matches_value(pattern: &CorePattern, value: &FinitePatternValue) -> bool {
    match (pattern, value) {
        (CorePattern::Any | CorePattern::Bind { .. }, _) => true,
        (CorePattern::Literal(literal), FinitePatternValue::Bool(value)) => {
            matches!((literal.as_str(), value), ("true", true) | ("false", false))
        }
        (CorePattern::Tuple(patterns), FinitePatternValue::Tuple(values)) => {
            patterns.len() == values.len()
                && patterns
                    .iter()
                    .zip(values)
                    .all(|(pattern, value)| core_pattern_matches_value(pattern, value))
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
            definition == actual
                && fields.iter().all(|field| {
                    values
                        .get(field.index as usize)
                        .is_some_and(|value| core_pattern_matches_value(&field.pattern, value))
                })
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
            definition == actual_definition
                && variant == actual_variant
                && fields.iter().all(|field| {
                    values
                        .get(field.index as usize)
                        .is_some_and(|value| core_pattern_matches_value(&field.pattern, value))
                })
        }
        _ => false,
    }
}

fn pattern_decision_matches_value(
    decision: &crate::pattern::PatternDecision,
    value: &FinitePatternValue,
) -> bool {
    match (decision, value) {
        (crate::pattern::PatternDecision::Any | crate::pattern::PatternDecision::Bind(_), _) => {
            true
        }
        (crate::pattern::PatternDecision::Literal(literal), FinitePatternValue::Bool(value)) => {
            matches!((literal.as_str(), value), ("true", true) | ("false", false))
        }
        (crate::pattern::PatternDecision::Tuple(patterns), FinitePatternValue::Tuple(values)) => {
            patterns.len() == values.len()
                && patterns
                    .iter()
                    .zip(values)
                    .all(|(pattern, value)| pattern_decision_matches_value(pattern, value))
        }
        (
            crate::pattern::PatternDecision::Record { definition, fields },
            FinitePatternValue::Record {
                definition: actual,
                fields: values,
            },
        ) => {
            definition == actual
                && fields.iter().all(|(index, pattern)| {
                    values
                        .get(*index as usize)
                        .is_some_and(|value| pattern_decision_matches_value(pattern, value))
                })
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
            definition == actual_definition
                && variant == actual_variant
                && fields.iter().all(|(index, pattern)| {
                    values
                        .get(*index as usize)
                        .is_some_and(|value| pattern_decision_matches_value(pattern, value))
                })
        }
        _ => false,
    }
}

fn nominal_parts(subject: &Type) -> Option<(DefKey, Vec<Type>)> {
    match subject {
        Type::Nominal {
            definition,
            arguments,
        } => Some((*definition, arguments.clone())),
        _ => None,
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
        CaptureMode::UniqueBorrow => 1,
        CaptureMode::Move => 2,
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
        "Bool" => Bool,
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
