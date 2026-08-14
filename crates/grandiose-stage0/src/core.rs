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
    types::{EffectInstance, EffectRow, InferContext, Lifetime, Mutability, ScalarType, Type},
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CoreId(pub u32);
/// Fresh body-local identity for an anonymous callable. It is deliberately
/// separate from a source offset so nested closure allocation has no effect on
/// named declaration identities or interface fingerprints.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct CallableId(pub u32);
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
    pub effect: EffectInstance,
    pub operation: u32,
    /// Exact operation payload signature retained after body elaboration.
    /// MIR needs it when materializing a lexical frame for a sibling operation
    /// that is not the immediately visible `Perform` site.
    pub payload_types: Vec<Type>,
    pub patterns: Vec<CorePattern>,
    pub bindings: Vec<(String, Type)>,
    pub resumption: CoreHandlerResumption,
    pub body: CoreId,
    pub terminal: bool,
    pub span: Span,
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
    Error,
}
impl CorePlace {
    pub(crate) fn ty(&self) -> Type {
        match self {
            Self::Local { ty, .. } => ty.clone(),
            Self::Field { ty, .. } => ty.clone(),
            Self::Error => Type::Error,
        }
    }
    pub(crate) fn root_local(&self) -> Option<(&str, &Type)> {
        match self {
            Self::Local { name, ty } => Some((name, ty)),
            Self::Field { base, .. } => base.root_local(),
            Self::Error => None,
        }
    }
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CoreKind {
    Literal(String),
    Local(String),
    Function(DefKey),
    /// A direct function value selected from a trait implementation. Retain
    /// proof evidence alongside the callable key until MIR consumes this
    /// source-free selection, rather than reconstructing lookup from a name.
    TraitMethod {
        evidence: DefKey,
        method: DefKey,
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
    },
    Closure {
        callable: CallableId,
        parameters: Vec<(String, Type)>,
        captures: Vec<ClosureCapture>,
        body: CoreId,
    },
    Let {
        name: String,
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
    Move(CoreId),
    Unary {
        operator: String,
        value: CoreId,
    },
    Error,
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
                    .filter(|(_, name)| !header.generics.is_effect_row(name))
                    .map(|(index, name)| (name.clone(), index as u32))
                    .collect()
            })
            .unwrap_or_default();
        let mut elaborator = Elaborator {
            body,
            index,
            signatures,
            fixities,
            module: &definition.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            function_arguments: std::collections::BTreeMap::new(),
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
            declared_effects: signatures
                .definitions
                .get(&definition.key)
                .and_then(callable)
                .map(|signature| signature.effects.clone())
                .unwrap_or_else(EffectRow::empty),
            handled_effects: std::collections::BTreeSet::new(),
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
            if elaborator.inference.unify(expected, actual).is_err() {
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
            if !context.implementation_header.generics.is_effect_row(name) {
                generic_parameters.insert(name.clone(), index as u32);
            }
        }
        let method_base = context.implementation_header.generics.len() as u32;
        for (offset, name) in context.method.signature.generics.iter().enumerate() {
            if !context.method.signature.generics.is_effect_row(name) {
                generic_parameters.insert(name.clone(), method_base + offset as u32);
            }
        }
        let mut elaborator = Elaborator {
            body,
            index,
            signatures,
            fixities,
            module: &implementation.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            function_arguments: std::collections::BTreeMap::new(),
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
            declared_effects: context.signature.effects.clone(),
            handled_effects: std::collections::BTreeSet::new(),
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
            .inference
            .unify(context.signature.result.clone(), actual)
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
            module: &definition.module,
            inference: InferContext::default(),
            locals: ScopeMap::default(),
            expressions: vec![],
            diagnostics: vec![],
            recovered: body.recovered,
            next_callable: 0,
            function_arguments: std::collections::BTreeMap::new(),
            generic_parameters: std::collections::BTreeMap::new(),
            effect_row_parameters: std::collections::BTreeMap::new(),
            declared_effects: EffectRow::empty(),
            handled_effects: std::collections::BTreeSet::new(),
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
            if elaborator.inference.unify(expected, actual).is_err() {
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
    module: &'a ModuleKey,
    inference: InferContext,
    locals: ScopeMap<String, Type>,
    expressions: Vec<CoreExpr>,
    diagnostics: Vec<CoreDiagnostic>,
    recovered: bool,
    next_callable: u32,
    function_arguments: std::collections::BTreeMap<CoreId, Vec<Type>>,
    /// Callable-declaration generic binders are lexically visible in its
    /// body, including effect applications such as `State<T>::get()`. They
    /// remain stable `Type::Generic` slots; inference variables are reserved
    /// for instantiations at a call site.
    generic_parameters: std::collections::BTreeMap<String, u32>,
    /// Lexically visible row-kind binders. These intentionally remain
    /// separate from `generic_parameters`: an effect row can be a callable
    /// tail but can never be elaborated as a value type.
    effect_row_parameters: std::collections::BTreeMap<String, u32>,
    declared_effects: EffectRow,
    /// Protocol instances exhaustively intercepted by lexically active deep
    /// handlers.  A partial handler never enters this set, so forwarding still
    /// requires the enclosing callable's outward effect declaration.
    handled_effects: std::collections::BTreeSet<EffectInstance>,
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
                self.alloc(CoreKind::Let { name, value }, Type::Unit, expression.span)
            }
            ExprKind::Assign { place, value } => {
                // The RHS is elaborated before the destination, as specified
                // for assignment and mirrored by MIR's Store order.
                let value = self.expression(value);
                let value_ty = self.expressions[value.0 as usize].ty.clone();
                let place = self.assignment_place(place, expression.span);
                if !matches!(&place, CorePlace::Error)
                    && self.inference.unify(place.ty(), value_ty).is_err()
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
                let pattern = self.core_pattern(
                    elaboration.plan.decision,
                    subject_type,
                    expression.span,
                    None,
                );
                self.alloc(
                    CoreKind::PatternTest { subject, pattern },
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
            _ => self.fail(
                expression.span,
                "G4101",
                "syntax form is not yet elaborated into Typed Core",
            ),
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
        let values = values
            .into_iter()
            .map(|value| self.expression(value))
            .collect::<Vec<_>>();
        self.declared_effects = previous_effects;
        self.handled_effects = previous_handled;
        let body_ty = values
            .last()
            .map(|value| self.expressions[value.0 as usize].ty.clone())
            .unwrap_or(Type::Unit);
        let body = self.alloc(CoreKind::Block(values), body_ty.clone(), span);
        self.locals.leave();
        if self.inference.unify(result.clone(), body_ty).is_err() {
            self.error(
                span,
                "G4113",
                "contextual callable block does not match its expected result",
            );
            self.recovered = true;
        }
        let parameters = vec![];
        let captures = self.closure_captures(body, &parameters);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters,
                captures,
                body,
            },
            Type::Callable {
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
        let body = self.expression(body);
        self.declared_effects = previous_effects;
        self.handled_effects = previous_handled;
        self.locals.leave();
        let actual_result = self.expressions[body.0 as usize].ty.clone();
        let result = declared_result
            .as_ref()
            .map(|ty| self.header_type(ty))
            .unwrap_or_else(|| actual_result.clone());
        if self.inference.unify(result.clone(), actual_result).is_err() {
            self.error(
                span,
                "G4113",
                "closure body does not match its declared result",
            );
            self.recovered = true;
        }
        let captures = self.closure_captures(body, &parameters);
        let callable = CallableId(self.next_callable);
        self.next_callable += 1;
        self.alloc(
            CoreKind::Closure {
                callable,
                parameters: parameters.clone(),
                captures,
                body,
            },
            Type::Callable {
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
            HeaderType::Callable { parameters, result } => Type::Callable {
                parameters: parameters
                    .iter()
                    .map(|value| self.header_type(value))
                    .collect(),
                result: Box::new(self.header_type(result)),
                effects: crate::types::EffectRow::empty(),
                invocation: crate::quantity::Quantity::ONCE,
            },
            HeaderType::Reference {
                unique,
                lifetime: _,
                referent,
            } => Type::Reference {
                mutability: if *unique {
                    Mutability::Unique
                } else {
                    Mutability::Shared
                },
                lifetime: Lifetime::Elided,
                referent: Box::new(self.header_type(referent)),
            },
            HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            } => self.header_projection(subject, trait_path, trait_arguments, name, item_arguments),
            HeaderType::Path(path) => self.header_path(path, vec![]),
            HeaderType::Application(base, arguments) => {
                let arguments = arguments
                    .iter()
                    .map(|argument| self.header_type(argument))
                    .collect::<Vec<_>>();
                match base.as_ref() {
                    HeaderType::Path(path) => self.header_path(path, arguments),
                    _ => Type::Error,
                }
            }
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
        trait_arguments: &[crate::header::HeaderType],
        name: &str,
        item_arguments: &[crate::header::HeaderType],
    ) -> Type {
        let subject = self.header_type(subject);
        let trait_arguments = trait_arguments
            .iter()
            .map(|argument| self.header_type(argument))
            .collect::<Vec<_>>();
        let item_arguments = item_arguments
            .iter()
            .map(|argument| self.header_type(argument))
            .collect::<Vec<_>>();
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
        let Some(ElaboratedHeader::Trait(trait_header)) =
            self.signatures.definitions.get(&trait_definition)
        else {
            self.projection_error("G4148", "associated type projection target is not a trait");
            return Type::Error;
        };
        match trait_header.associated_types.get(name) {
            Some(item) if item.effect_row => {
                self.projection_error(
                    "G4149",
                    "associated effect rows require the pending effect-row projection syntax",
                );
                return Type::Error;
            }
            Some(item) if item.generics == item_arguments.len() as u32 => {}
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
        }
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
                    arguments: trait_arguments.clone(),
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
    fn header_path(&mut self, path: &[String], arguments: Vec<Type>) -> Type {
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
            if let Some(scalar) = closure_scalar(name) {
                return if arguments.is_empty() {
                    Type::Scalar(scalar)
                } else {
                    Type::Error
                };
            }
            if name == "Array" {
                return match arguments.as_slice() {
                    [element] => Type::Array(Box::new(element.clone())),
                    _ => Type::Error,
                };
            }
        }
        match self
            .index
            .resolve_path(DefinitionNamespace::Type, self.module, path)
        {
            ResolutionState::Resolved(definition) => Type::Nominal {
                definition,
                arguments,
            },
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
                            .map(|argument| self.header_type(argument))
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
                    let trait_arguments = trait_arguments
                        .iter()
                        .map(|argument| self.header_type(argument))
                        .collect::<Vec<_>>();
                    let item_arguments = item_arguments
                        .iter()
                        .map(|argument| self.header_type(argument))
                        .collect::<Vec<_>>();
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
            CoreKind::Unary { value, .. } => self.collect_captures(*value, locals, captures),
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
            | CoreKind::Function(_)
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
            let closure_data = match &self.expressions[index].kind {
                CoreKind::Closure {
                    parameters,
                    captures,
                    ..
                } => Some((parameters.clone(), captures.clone())),
                _ => None,
            };
            let Some((parameters, captures)) = closure_data else {
                continue;
            };
            let parameters = parameters
                .into_iter()
                .map(|(name, ty)| (name, self.zonk_type(ty, span)))
                .collect();
            let captures = captures
                .into_iter()
                .map(|mut capture| {
                    capture.ty = self.zonk_type(capture.ty, span);
                    capture
                })
                .collect();
            if let CoreKind::Closure {
                parameters: target_parameters,
                captures: target_captures,
                ..
            } = &mut self.expressions[index].kind
            {
                *target_parameters = parameters;
                *target_captures = captures;
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
                // `is` has no refinement environment, so its bind pattern is
                // exactly an ordinary wildcard at Typed Core's test boundary.
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
                    let arguments = (0..signature.generics)
                        .map(|_| self.inference.fresh())
                        .collect::<Vec<_>>();
                    let signature = self
                        .signatures
                        .instantiate_callable(definition, &arguments)
                        .expect("fresh arguments match the callable generic arity");
                    let value = self.alloc(
                        CoreKind::Function(definition),
                        Type::Callable {
                            parameters: signature.parameters,
                            result: Box::new(signature.result),
                            effects: signature.effects,
                            invocation: signature.invocation,
                        },
                        span,
                    );
                    self.function_arguments.insert(value, arguments);
                    value
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
            if self.inference.unify(field.ty, actual).is_err() {
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
            if self.inference.unify(field.ty, actual).is_err() {
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
                if self.inference.unify(expected, actual).is_err() {
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
            parameters, result, ..
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
        for (parameter, argument) in parameters.into_iter().zip(&arguments) {
            let actual = self.expressions[argument.0 as usize].ty.clone();
            if self.inference.unify(parameter, actual).is_err() {
                self.error(span, "G4107", "call argument type does not match parameter");
                self.recovered = true;
            }
        }
        if let Type::Callable { effects, .. } = &self.expressions[callee.0 as usize].ty {
            self.check_effects(&effects.clone(), span);
        }
        self.check_call_where_bounds(callee, span);
        self.alloc(CoreKind::Call { callee, arguments }, *result, span)
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
        let answer = TraitSolver::new(self.signatures).select_method(
            TraitGoal {
                relation: crate::ElaboratedTraitReference {
                    definition: trait_definition,
                    arguments: trait_arguments,
                },
                subject,
            },
            name,
            &method_arguments,
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
            CoreKind::TraitMethod { evidence, method },
            Type::Callable {
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
                if self.inference.unify(expected.clone(), actual).is_err() {
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
            arguments: effect_arguments,
        };
        self.check_effect_instance(&instance, span);
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
        let covered = self.exhaustively_handled_effects(&resolved);
        let mut active = self.handled_effects.clone();
        active.extend(covered);
        let previous = std::mem::replace(&mut self.handled_effects, active);
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
        for clause in resolved {
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
                        parameters: vec![clause.operation.result.clone()],
                        result: Box::new(result.clone()),
                        // A deep resumption reinstalls this handler, so its
                        // callable contract exposes only the residual outward
                        // row rather than the protocol being intercepted.
                        effects: self.residual_effects(),
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
            let body = self.expression(clause.source.body);
            self.locals.leave();
            let body_ty = self.expressions[body.0 as usize].ty.clone();
            let expected = match resumption {
                CoreHandlerResumption::Tail { .. } => clause.operation.result.clone(),
                CoreHandlerResumption::Explicit { .. }
                | CoreHandlerResumption::Discard { .. }
                | CoreHandlerResumption::Terminal => result.clone(),
            };
            if self.inference.unify(expected, body_ty).is_err() {
                self.error(
                    clause.source.span,
                    "G4161",
                    "handler clause body does not match its continuation contract",
                );
                self.recovered = true;
            }
            core_clauses.push(CoreHandlerClause {
                effect: clause.effect,
                operation: clause.operation_index,
                payload_types: clause.operation.parameters.clone(),
                patterns,
                bindings,
                resumption,
                body,
                terminal: clause.operation.terminal,
                span: clause.source.span,
            });
        }
        self.handled_effects = previous;
        let handler = self.alloc(
            CoreKind::Handle {
                computation,
                clauses: core_clauses,
            },
            result,
            span,
        );
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
        let subject_ty = self.expressions[subject.0 as usize].ty.clone();
        let result = self.inference.fresh();
        let mut core_clauses = Vec::with_capacity(clauses.len());
        let mut has_fallback = false;
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
            has_fallback |= !elaboration.plan.refutable;
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
            if self.inference.unify(result.clone(), body_ty).is_err() {
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
        if !has_fallback
            && !self.core_patterns_exhaustive(
                &core_clauses
                    .iter()
                    .map(|clause| clause.pattern.clone())
                    .collect::<Vec<_>>(),
                &subject_ty,
            )
        {
            return self.fail(
                span,
                "G4166",
                "completion arms need an irrefutable fallback",
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
    /// Finite normal-completion coverage mirrors the operation-row proof:
    /// it permits a closed enum or Bool matrix, while leaving all infinite or
    /// partially refined subjects subject to the ordinary fallback rule.
    fn core_patterns_exhaustive(&self, patterns: &[CorePattern], subject: &Type) -> bool {
        if patterns.iter().any(core_pattern_irrefutable) {
            return true;
        }
        match subject {
            Type::Nominal { definition, .. } => {
                let Some(ElaboratedHeader::Nominal {
                    layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                    ..
                }) = self.signatures.definitions.get(definition)
                else {
                    return false;
                };
                let covered = patterns
                    .iter()
                    .filter_map(|pattern| match pattern {
                        CorePattern::Enum {
                            definition: actual,
                            variant,
                            fields,
                            ..
                        } if actual == definition
                            && fields
                                .iter()
                                .all(|field| core_pattern_irrefutable(&field.pattern)) =>
                        {
                            Some(*variant)
                        }
                        _ => None,
                    })
                    .collect::<std::collections::BTreeSet<_>>();
                covered.len() == variants.len()
                    && covered
                        .iter()
                        .all(|variant| (*variant as usize) < variants.len())
            }
            Type::Scalar(ScalarType::Bool) => {
                patterns
                    .iter()
                    .filter_map(|pattern| match pattern {
                        CorePattern::Literal(value) if value == "true" || value == "false" => {
                            Some(value.as_str())
                        }
                        _ => None,
                    })
                    .collect::<std::collections::BTreeSet<_>>()
                    .len()
                    == 2
            }
            _ => false,
        }
    }
    fn residual_effects(&self) -> EffectRow {
        let mut effects = self.declared_effects.clone();
        effects
            .effects
            .retain(|effect| !self.handled_effects.contains(effect));
        effects
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
        declaration.generics as usize == source.effect_arguments.len()
            && declaration
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
            .collect();
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
    fn exhaustively_handled_effects(
        &self,
        clauses: &[ResolvedHandlerClause],
    ) -> std::collections::BTreeSet<EffectInstance> {
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
        let mut irrefutable =
            std::collections::BTreeMap::<EffectInstance, std::collections::BTreeSet<u32>>::new();
        for ((effect, operation), rows) in operation_rows {
            if self.handler_operation_is_exhaustive(&rows) {
                irrefutable.entry(effect).or_default().insert(operation);
            }
        }
        irrefutable
            .into_iter()
            .filter_map(|(effect, handled)| {
                let Some(ElaboratedHeader::Effect(declaration)) =
                    self.signatures.definitions.get(&effect.definition)
                else {
                    return None;
                };
                (handled.len() == declaration.operations.len()).then_some(effect)
            })
            .collect()
    }
    /// A compact, source-order matrix proof for the finite cases available in
    /// stage0.  The shared pattern DAG remains responsible for dispatch; this
    /// proof only decides whether an operation may leave the outward effect
    /// row.  It deliberately accepts a row only when every constructor arm
    /// covers its payload irrefutably, so it never mistakes a partial nested
    /// pattern for total coverage.
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
        let mut domains = Vec::with_capacity(first.patterns.len());
        let mut combinations = 1usize;
        for pattern in &first.patterns {
            let domain = match &pattern.plan.subject {
                Type::Scalar(ScalarType::Bool) => {
                    vec![
                        FiniteConstructor::Bool(false),
                        FiniteConstructor::Bool(true),
                    ]
                }
                Type::Nominal { definition, .. } => {
                    let Some(ElaboratedHeader::Nominal {
                        layout: crate::signature::ElaboratedNominalLayout::Enum(variants),
                        ..
                    }) = self.signatures.definitions.get(definition)
                    else {
                        return false;
                    };
                    (0..variants.len() as u32)
                        .map(|variant| FiniteConstructor::Enum {
                            definition: *definition,
                            variant,
                        })
                        .collect()
                }
                _ => return false,
            };
            combinations = match combinations.checked_mul(domain.len()) {
                Some(count) if count <= 4096 => count,
                _ => return false,
            };
            domains.push(domain);
        }
        (0..combinations).all(|ordinal| {
            let mut cursor = ordinal;
            let assignment = domains
                .iter()
                .map(|domain| {
                    let constructor = domain[cursor % domain.len()];
                    cursor /= domain.len();
                    constructor
                })
                .collect::<Vec<_>>();
            rows.iter().any(|row| {
                row.patterns
                    .iter()
                    .zip(&assignment)
                    .all(|(pattern, constructor)| {
                        pattern_decision_matches_constructor(&pattern.plan.decision, *constructor)
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
                        arguments: projection.trait_arguments,
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
            self.check_effect_instance(effect, span);
        }
    }
    fn check_effect_instance(&mut self, effect: &EffectInstance, span: Span) {
        if !self.declared_effects.effects.contains(effect) && !self.handled_effects.contains(effect)
        {
            self.error(
                span,
                "G4155",
                "performed effect is absent from this callable's declared outward row",
            );
            self.recovered = true;
        }
    }
    /// Direct calls carry a body-local map from their function Core value to
    /// the fresh type arguments used to instantiate its frozen signature.
    /// This is the narrowest point at which ordinary callable bounds can be
    /// checked: argument unification has constrained the variables, while no
    /// unresolved inference state has crossed into a persistence boundary.
    fn check_call_where_bounds(&mut self, callee: CoreId, span: Span) {
        let definition = match &self.expressions[callee.0 as usize].kind {
            CoreKind::Function(definition) => *definition,
            _ => return,
        };
        let Some(arguments) = self.function_arguments.get(&callee).cloned() else {
            return;
        };
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
                .map(|argument| self.inference.zonk(argument))
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
        Type::Unit | Type::Never | Type::Scalar(_) | Type::Error => true,
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

/// Whether a decision is total once an enclosing finite constructor has
/// already selected its variant. This is intentionally narrower than general
/// matrix exhaustiveness: it is the local payload proof used by the handler
/// coverage check above.
fn pattern_decision_irrefutable(decision: &crate::pattern::PatternDecision) -> bool {
    match decision {
        crate::pattern::PatternDecision::Any | crate::pattern::PatternDecision::Bind(_) => true,
        crate::pattern::PatternDecision::Tuple(values) => {
            values.iter().all(pattern_decision_irrefutable)
        }
        crate::pattern::PatternDecision::Record { fields, .. } => fields
            .iter()
            .all(|(_, field)| pattern_decision_irrefutable(field)),
        crate::pattern::PatternDecision::Literal(_)
        | crate::pattern::PatternDecision::Enum { .. }
        | crate::pattern::PatternDecision::Error => false,
    }
}

#[derive(Clone, Copy)]
enum FiniteConstructor {
    Bool(bool),
    Enum { definition: DefKey, variant: u32 },
}

fn pattern_decision_matches_constructor(
    decision: &crate::pattern::PatternDecision,
    constructor: FiniteConstructor,
) -> bool {
    match (decision, constructor) {
        (crate::pattern::PatternDecision::Any | crate::pattern::PatternDecision::Bind(_), _) => {
            true
        }
        (crate::pattern::PatternDecision::Literal(value), FiniteConstructor::Bool(actual)) => {
            matches!((value.as_str(), actual), ("true", true) | ("false", false))
        }
        (
            crate::pattern::PatternDecision::Enum {
                definition,
                variant,
                fields,
            },
            FiniteConstructor::Enum {
                definition: actual_definition,
                variant: actual_variant,
            },
        ) => {
            definition == &actual_definition
                && *variant == actual_variant
                && fields
                    .iter()
                    .all(|(_, field)| pattern_decision_irrefutable(field))
        }
        _ => false,
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
