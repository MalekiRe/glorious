//! Quantitative callable-use facts derived from Typed Core.
//!
//! `PlaceFlow` answers whether an evaluation is ownership-safe.  This pass
//! answers a distinct question once that ownership shape is known: how many
//! times can each *local callable capability* be invoked?  The representation
//! deliberately uses the same [`Quantity`] algebra as effect resumptions, so
//! ordinary calls, closure captures, and dynamically selected handler arms
//! compose at one semantic boundary before MIR.

use crate::{
    core::{
        CoreHandlerClause, CoreHandlerResumption, CoreId, CoreKind, CorePattern,
        CorePlace, TypedBody, instantiate_nominal_field_type,
    },
    placeflow::{FlowEventKind, MoveFact, PlaceFlow},
    quantity::{Quantity, QuantityError},
    signature::{ElaboratedHeader, ElaboratedInterface, ElaboratedNominalLayout},
    source::Span,
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};
mod invocations;
pub(crate) use invocations::{UseBodies, UseBody};

/// One structured failure from quantitative Core analysis.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct UseDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

/// A checked local callable contract and its path-sensitive use interval.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableUseFact {
    pub name: String,
    pub declared: Quantity,
    pub actual: Quantity,
    pub span: Span,
    /// `true` when this fact is the generated continuation of a handler arm.
    pub resumption: bool,
}

/// A principal callable-use obligation attached to a canonical PlaceFlow
/// projection.  This is the bridge from callable capabilities to aggregate
/// ownership: the place identity is frozen by PlaceFlow, never rebuilt from a
/// field expression by UseFlow.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValueUseFact {
    pub place: MoveFact,
    pub declared: Quantity,
    pub actual: Quantity,
    pub span: Span,
    pub disposition: ValueUseDisposition,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ValueUseDisposition {
    Live,
    Transferred,
    Overwritten,
    Borrowed,
}

/// One explicit transfer of a callable-use obligation to another semantic
/// boundary.  Keeping this as data prevents escape from becoming an implicit
/// exception to lower-bound checking.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableEscapeFact {
    pub name: String,
    pub declared: Quantity,
    /// The callable contract carried by the receiver. `None` means the
    /// boundary is opaque and cannot prove that it preserves the capability.
    pub required: Option<Quantity>,
    /// How often this boundary receives the capability.  A replayed handler
    /// continuation can execute an otherwise ordinary call more than once,
    /// so this is deliberately distinct from the receiver's per-call
    /// `required` contract.
    pub actual: Quantity,
    pub span: Span,
    pub boundary: CallableEscapeBoundary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CallableEscapeBoundary {
    Result,
    Argument,
    Assignment,
    Closure,
}

/// The result of quantitative-use analysis.  Facts are retained for tooling
/// and later ownership refinements even when a diagnostic prevents lowering.
#[derive(Clone, Debug, Default)]
pub struct UseFlow {
    pub(crate) resumption_transfers: Option<std::sync::Arc<ResumptionTransfers>>,
    pub callable_uses: Vec<CallableUseFact>,
    pub callable_escapes: Vec<CallableEscapeFact>,
    pub value_obligations: Vec<ValueUseFact>,
    pub diagnostics: Vec<UseDiagnostic>,
}

/// Published by the checked quantity execution, not inferred from callable
/// types. Each recorded occurrence denotes only replay-resumption handles on
/// every observed alternative in this exact source body. It grants carrier
/// transport, never source Copy or an additional invocation budget.
#[derive(Clone, Debug)]
pub(crate) struct ResumptionTransfers {
    input: crate::Digest,
    values: BTreeSet<CoreId>,
}

impl ResumptionTransfers {
    pub(crate) fn matches(&self, input: crate::Digest) -> bool { self.input == input }
    pub(crate) fn retains(&self, value: CoreId) -> bool { self.values.contains(&value) }
}

impl UseFlow {
    /// Analyze only ownership-valid Core.  Keeping `PlaceFlow` in the input
    /// makes the ordering explicit: a moved or conflicting-borrow path is not
    /// a valid witness for a quantitative callable contract, and reporting a
    /// second use error for it would be misleading.
    pub fn analyze(body: &TypedBody, ownership: &PlaceFlow) -> Self {
        Self::analyze_with_optional_interface(body, ownership, None, None)
    }

    /// Analyze a source body with the frozen nominal layouts that define its
    /// aggregate ownership.  The layout is an explicit semantic input: a
    /// callable field in a struct parameter is an owned capability even when
    /// its body never happens to project that field.
    pub fn analyze_with_interface(
        body: &TypedBody,
        ownership: &PlaceFlow,
        signatures: &ElaboratedInterface,
    ) -> Self {
        Self::analyze_with_optional_interface(body, ownership, Some(signatures), None)
    }

    pub(crate) fn analyze_with_bodies(body: &TypedBody, ownership: &PlaceFlow,
        signatures: &ElaboratedInterface, bodies: &UseBodies<'_>) -> Self {
        Self::analyze_with_optional_interface(body, ownership, Some(signatures), Some(bodies))
    }

    fn analyze_with_optional_interface(
        body: &TypedBody,
        ownership: &PlaceFlow,
        signatures: Option<&ElaboratedInterface>,
        bodies: Option<&UseBodies<'_>>,
    ) -> Self {
        if !ownership.diagnostics.is_empty() {
            return Self::default();
        }
        let continuations = match ownership.continuations_for(body) {
            Ok(facts) => facts,
            Err(error) => return Self { diagnostics: vec![UseDiagnostic {
                code: error.code, span: error.span, message: error.message,
            }], ..Self::default() },
        };
        let mut analyzer = Analyzer {
            body,
            continuations,
            ownership,
            body_flow: ownership,
            bodies,
            active_frames: vec![],
            frame_steps: 0,
            signatures,
            next_key: 0,
            contracts: BTreeMap::new(),
            facts: BTreeMap::new(),
            projected_contracts: BTreeMap::new(),
            closure_values: BTreeMap::new(),
            result_values: BTreeMap::new(),
            resumption_transfers: BTreeMap::new(),
            escapes: EscapeSummary::default(),
            value_obligations: vec![],
            diagnostics: vec![],
        };
        let mut environment = Environment::default();
        for (name, ty) in &body.parameters {
            let binding = analyzer.binding_for_type(name, ty, body.expression(body.root).span);
            if !matches!(binding, Binding::Other) {
                environment.bindings.insert(name.clone(), binding);
            }
        }
        let summary = analyzer.expression(body.root, &mut environment);
        analyzer.record(summary);
        let result_type = body.expression(body.root).ty.clone();
        let result_uses = analyzer.escape_value_as(
            body.root,
            &environment,
            &result_type,
            CallableEscapeBoundary::Result,
        );
        analyzer.record(result_uses);
        analyzer.finish()
    }
}

#[derive(Clone, Debug, Default)]
struct Summary {
    uses: BTreeMap<ContractKey, Quantity>,
}

impl Summary {
    fn one(key: ContractKey) -> Self {
        let mut uses = BTreeMap::new();
        uses.insert(key, Quantity::ONCE);
        Self { uses }
    }

    fn sequence(mut self, other: Self) -> Result<Self, QuantityError> {
        for (key, quantity) in other.uses {
            let next = self
                .uses
                .remove(&key)
                .unwrap_or(Quantity::ZERO)
                .sequence(quantity)?;
            self.uses.insert(key, next);
        }
        Ok(self)
    }

    fn branch_hull(mut self, other: Self) -> Self {
        let keys = self
            .uses
            .keys()
            .chain(other.uses.keys())
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        for key in keys {
            let left = self.uses.remove(&key).unwrap_or(Quantity::ZERO);
            let right = other.uses.get(&key).copied().unwrap_or(Quantity::ZERO);
            self.uses.insert(key, left.branch_hull(right));
        }
        self
    }

    fn multiply(mut self, repetitions: Quantity) -> Result<Self, QuantityError> {
        for quantity in self.uses.values_mut() {
            *quantity = quantity.multiply(repetitions)?;
        }
        Ok(self)
    }
}

/// A direct perform may end the handled computation only when every matching
/// operation clause is a full-control discard with an irrefutable payload
/// pattern. Pattern-sensitive and resumptive dispatch remain on the ordinary
/// conservative path: this predicate is a proof of suffix abandonment, never
/// a heuristic about likely runtime values.
fn handler_definitely_discards(
    clauses: &[CoreHandlerClause],
    effect: &crate::EffectInstance,
    operation: u32,
) -> bool {
    let matching = clauses
        .iter()
        .filter(|clause| clause.effect == *effect && clause.operation == operation)
        .collect::<Vec<_>>();
    !matching.is_empty()
        && matching.iter().all(|clause| {
            matches!(clause.resumption, CoreHandlerResumption::Discard { .. })
                && clause.patterns.iter().all(core_pattern_is_irrefutable)
        })
}

fn core_pattern_is_irrefutable(pattern: &CorePattern) -> bool {
    match pattern {
        CorePattern::Any | CorePattern::Bind { .. } => true,
        CorePattern::Tuple(values) => values.iter().all(core_pattern_is_irrefutable),
        CorePattern::Array { .. } => false,
        CorePattern::Record { fields, .. } => fields
            .iter()
            .all(|field| core_pattern_is_irrefutable(&field.pattern)),
        CorePattern::Literal(_) | CorePattern::Enum { .. } | CorePattern::Error => false,
    }
}

/// A normally completing straight-line computation must pass through one of
/// these direct performances. An effectful callable contract alone does not
/// establish this fact: its callee may return without performing anything.
fn computation_must_dispatch(body: &TypedBody, id: CoreId, clauses: &[CoreHandlerClause], signatures: Option<&ElaboratedInterface>) -> bool {
    match &body.expression(id).kind {
        CoreKind::Perform { effect, operation, arguments, .. } => {
            let rows = clauses.iter().filter(|clause| clause.effect == *effect && clause.operation == *operation)
                .map(|clause| clause.patterns.as_slice()).collect::<Vec<_>>();
            rows.iter().any(|row| row.len() == arguments.len() && row.iter().all(core_pattern_is_irrefutable))
                || signatures.is_some_and(|signatures| crate::core::core_pattern_rows_exhaustive(
                    signatures,
                    &arguments.iter().map(|argument| body.expression(*argument).ty.clone()).collect::<Vec<_>>(),
                    &rows,
                ))
        }
        CoreKind::Let { value, .. } => computation_must_dispatch(body, *value, clauses, signatures),
        CoreKind::Block(values) => values.iter().any(|value| computation_must_dispatch(body, *value, clauses, signatures)),
        _ => false,
    }
}

fn direct_replay_split(
    body: &TypedBody,
    computation: CoreId,
    clauses: &[CoreHandlerClause],
) -> Option<DirectReplaySplit> {
    let CoreKind::Block(values) = &body.expression(computation).kind else {
        return None;
    };
    for (index, value) in values.iter().copied().enumerate() {
        let (effect, operation, arguments, result_binding) = match &body.expression(value).kind {
            CoreKind::Perform {
                effect,
                operation,
                arguments,
                ..
            } => (effect, *operation, arguments.clone(), None),
            CoreKind::Let { name, value, .. } => {
                let CoreKind::Perform {
                    effect,
                    operation,
                    arguments,
                    ..
                } = &body.expression(*value).kind
                else {
                    continue;
                };
                (effect, *operation, arguments.clone(), Some(name.clone()))
            }
            _ => continue,
        };
        if handler_definitely_replays(clauses, effect, operation) {
            return Some(DirectReplaySplit {
                prefix: values[..index].to_vec(),
                operation_arguments: arguments,
                residual: values[index + 1..].to_vec(),
                result_binding,
            });
        }
    }
    None
}

/// Prove that the direct operation dispatch always re-enters its residual.
/// All matching clauses must be resumptive and irrefutable; a terminal,
/// discard, or payload-sensitive arm leaves ordinary conservative handling in
/// place rather than inventing a replay multiplier.
fn handler_definitely_replays(
    clauses: &[CoreHandlerClause],
    effect: &crate::EffectInstance,
    operation: u32,
) -> bool {
    let matching = clauses
        .iter()
        .filter(|clause| clause.effect == *effect && clause.operation == operation)
        .collect::<Vec<_>>();
    !matching.is_empty()
        && matching.iter().all(|clause| {
            matches!(
                clause.resumption,
                CoreHandlerResumption::Tail { .. } | CoreHandlerResumption::Explicit { .. }
            ) && clause.patterns.iter().all(core_pattern_is_irrefutable)
        })
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ContractKey(u32);

#[derive(Clone, Debug)]
struct Contract {
    name: String,
    declared: Quantity,
    span: Span,
    resumption: bool,
}

#[derive(Clone, Debug)]
struct ClosureValue {
    environment: crate::core::EnvironmentBrand,
    body: CoreId,
    captures: BTreeMap<String, Binding>,
    parameters: Vec<(String, Type)>,
    invocation: Quantity,
    resident_types: Vec<(String, Type)>,
}

/// One outgoing capability transfer observed while evaluating Core.  The
/// receiver contract is per invocation; `actual` records the enclosing
/// control-flow multiplicity (notably handler replay and closure invocation).
#[derive(Clone, Debug)]
struct Escape {
    required: Option<Quantity>,
    span: Span,
    boundary: CallableEscapeBoundary,
    actual: Quantity,
}

/// Quantitative transfers produced by one control-flow fragment. `demand`
/// is the semantic path summary used for contract checking; `facts` retains
/// every concrete boundary for diagnostics and tooling. Keeping them separate
/// is essential: two facts from alternative arms are both observable facts,
/// but their demands must join rather than execute sequentially.
#[derive(Clone, Debug, Default)]
struct EscapeSummary {
    facts: BTreeMap<ContractKey, Vec<Escape>>,
    demand: BTreeMap<ContractKey, Quantity>,
}

impl EscapeSummary {
    fn sequence(mut self, other: Self) -> Result<Self, QuantityError> {
        for (key, facts) in other.facts {
            self.facts.entry(key).or_default().extend(facts);
        }
        for (key, demand) in other.demand {
            let total = self
                .demand
                .remove(&key)
                .unwrap_or(Quantity::ZERO)
                .sequence(demand)?;
            self.demand.insert(key, total);
        }
        Ok(self)
    }

    fn branch_hull(mut self, other: Self) -> Self {
        for (key, facts) in other.facts {
            self.facts.entry(key).or_default().extend(facts);
        }
        let keys = self
            .demand
            .keys()
            .chain(other.demand.keys())
            .copied()
            .collect::<BTreeSet<_>>();
        for key in keys {
            let left = self.demand.remove(&key).unwrap_or(Quantity::ZERO);
            let right = other.demand.get(&key).copied().unwrap_or(Quantity::ZERO);
            self.demand.insert(key, left.branch_hull(right));
        }
        self
    }

    fn multiply(mut self, repetitions: Quantity) -> Result<Self, QuantityError> {
        for facts in self.facts.values_mut() {
            for escape in facts {
                escape.actual = escape.actual.multiply(repetitions)?;
            }
        }
        for demand in self.demand.values_mut() {
            *demand = demand.multiply(repetitions)?;
        }
        Ok(self)
    }
}

/// A straight-line handled computation with one directly intercepted
/// operation. The prefix executes once before dispatch; each resumption
/// replays the residual. Keeping this shape explicit avoids claiming CFG
/// precision for nested control that Core has not yet made first-class.
#[derive(Clone, Debug)]
struct DirectReplaySplit {
    prefix: Vec<CoreId>,
    operation_arguments: Vec<CoreId>,
    residual: Vec<CoreId>,
    result_binding: Option<String>,
}

#[derive(Clone, Debug)]
enum Binding {
    Contract(ContractKey),
    Closure(ClosureValue),
    /// Aggregate ownership is structurally decomposed only for callable
    /// leaves.  `PlaceFlow` remains authoritative for whether the enclosing
    /// projection is live/moved/borrowed; this map only preserves the
    /// callable-use obligation while the aggregate is live.
    Aggregate(BTreeMap<u32, Binding>),
    Choice(Vec<Binding>),
    /// A callable created by a named declaration is globally reusable. Its
    /// invocation field describes the invocation itself, not a consumable
    /// body-local capability, so no local quantity fact is created here.
    GlobalCallable,
    Other,
}

#[derive(Clone, Debug, Default)]
struct Environment {
    bindings: BTreeMap<String, Binding>,
}

/// The value selected by one completed strict operand. Later operands may
/// replace its source storage, but cannot change this invocation input.
struct EvaluatedValue {
    expression: CoreId,
    binding: Binding,
}

struct Analyzer<'a> {
    continuations: &'a crate::core_continuations::CoreContinuations,
    body: &'a TypedBody,
    ownership: &'a PlaceFlow,
    body_flow: &'a PlaceFlow,
    bodies: Option<&'a UseBodies<'a>>,
    active_frames: Vec<crate::CallableBrand>,
    frame_steps: usize,
    signatures: Option<&'a ElaboratedInterface>,
    next_key: u32,
    contracts: BTreeMap<ContractKey, Contract>,
    facts: BTreeMap<ContractKey, Quantity>,
    /// Callable leaves reached through a parameter/opaque aggregate are
    /// discovered from PlaceFlow's canonical projection rather than inferred
    /// from the aggregate's source spelling.  One place owns one contract
    /// across direct calls, moves, branches, and closure bodies.
    projected_contracts: BTreeMap<MoveFact, ContractKey>,
    /// Frozen pre-transfer environments for closure values. A move capture
    /// removes its outer binding while the closure is evaluated, but the
    /// resulting closure remains the owner of that capability.
    closure_values: BTreeMap<CoreId, ClosureValue>,
    result_values: BTreeMap<CoreId, Binding>,
    resumption_transfers: BTreeMap<CoreId, bool>,
    escapes: EscapeSummary,
    value_obligations: Vec<ValueUseFact>,
    diagnostics: Vec<UseDiagnostic>,
}

impl Analyzer<'_> {
    fn record(&mut self, summary: Summary) {
        for (key, actual) in summary.uses {
            let previous = self.facts.remove(&key).unwrap_or(Quantity::ZERO);
            match previous.sequence(actual) {
                Ok(actual) => {
                    self.facts.insert(key, actual);
                }
                Err(QuantityError::Overflow) => {
                    self.error(
                        self.body.expression(self.body.root).span,
                        "G5010",
                        "quantitative callable-use count overflowed",
                    );
                }
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity summaries are never empty")
                }
            }
        }
    }

    fn contract(
        &mut self,
        name: &str,
        declared: Quantity,
        span: Span,
        resumption: bool,
    ) -> ContractKey {
        let key = ContractKey(self.next_key);
        self.next_key += 1;
        self.contracts.insert(
            key,
            Contract {
                name: name.into(),
                declared,
                span,
                resumption,
            },
        );
        key
    }

    fn error(&mut self, span: Span, code: &'static str, message: impl Into<String>) {
        self.diagnostics.push(UseDiagnostic {
            code,
            span,
            message: message.into(),
        });
    }

    fn compose(&mut self, span: Span, left: Summary, right: Summary) -> Summary {
        match left.sequence(right) {
            Ok(summary) => summary,
            Err(QuantityError::Overflow) => {
                self.error(span, "G5010", "quantitative callable-use count overflowed");
                Summary::default()
            }
            Err(QuantityError::EmptyInterval) => {
                self.error(
                    span,
                    "G5010",
                    "quantitative callable-use interval became empty",
                );
                Summary::default()
            }
        }
    }

    fn repeat(&mut self, span: Span, summary: Summary, quantity: Quantity) -> Summary {
        match summary.multiply(quantity) {
            Ok(summary) => summary,
            Err(QuantityError::Overflow) => {
                self.error(
                    span,
                    "G5010",
                    "quantitative closure-capture use count overflowed",
                );
                Summary::default()
            }
            Err(QuantityError::EmptyInterval) => {
                self.error(
                    span,
                    "G5010",
                    "quantitative closure-capture interval became empty",
                );
                Summary::default()
            }
        }
    }

    fn expression(&mut self, id: CoreId, environment: &mut Environment) -> Summary {
        let expression = self.body.expression(id).clone();
        match expression.kind {
            CoreKind::ConstValue(_) => Summary::default(),
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error => Summary::default(),
            CoreKind::Closure {
                callable: _,
                parameters,
                environment: capture_environment,
                body,
            } => {
                // Capture post-states are applied below. Preserve the
                // capability environment first, otherwise `move function`
                // would erase the function from the closure's own body.
                self.closure_values
                    .insert(id, ClosureValue {
                        environment: capture_environment.brand,
                        resident_types: capture_environment.captures.iter().map(|capture|
                            (capture.name.clone(), crate::capture_formation::CaptureFormation::new(capture).resident_type())).collect(),
                        body,
                        captures: capture_environment
                            .captures
                            .iter()
                            .map(|capture| {
                                (
                                    capture.name.clone(),
                                    environment
                                        .bindings
                                        .get(&capture.name)
                                        .cloned()
                                        .unwrap_or(Binding::Other),
                                )
                            })
                            .collect(),
                        parameters,
                        invocation: callable_invocation(&expression.ty).unwrap_or(Quantity::ONCE),
                    });
                // PlaceFlow supplies the canonical captured root.  The
                // environment supplies only the obligation carried by that
                // root, so this records capture transfer without rebuilding
                // a source projection in UseFlow.
                for capture in capture_environment.captures {
                    use crate::capture_formation::{CaptureFormation, CaptureSource};
                    let source = CaptureFormation::new(&capture).source();
                    let binding = environment
                        .bindings
                        .get(&capture.name)
                        .cloned()
                        .unwrap_or(Binding::Other);
                    if let Some(place) = self.closure_place_fact(
                        expression.span,
                        &capture.name,
                        source,
                    ) {
                        match source {
                            CaptureSource::Move => {
                                self.record_transfer(&binding, place, expression.span);
                                environment.bindings.insert(capture.name, Binding::Other);
                            }
                            CaptureSource::Borrow(_) => {
                                self.record_borrow(&binding, place, expression.span);
                            }
                            CaptureSource::Copy => {
                                // A copy is an owned environment entry but
                                // leaves its unrestricted source binding
                                // available for later ordinary uses.
                                self.record_borrow(&binding, place, expression.span);
                            }
                        }
                    }
                }
                Summary::default()
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.expression(body, environment)
            }
            CoreKind::Let { name, value, .. } => {
                let summary = self.expression(value, environment);
                if self.continuations.is_abrupt(value) {
                    return summary;
                }
                let binding = self.binding_for_value(value, environment);
                if matches!(self.body.expression(value).kind, CoreKind::Move(_)) {
                    if let Some(place) = self.move_place_fact(self.body.expression(value).span) {
                        self.record_transfer(&binding, place, expression.span);
                    }
                    self.take_moved_binding(value, environment);
                }
                environment.bindings.insert(name, binding);
                summary
            }
            CoreKind::Assign { place, value } => {
                let summary = self.expression(value, environment);
                if self.continuations.is_abrupt(value) {
                    return summary;
                }
                let replacement = self.binding_for_value(value, environment);
                let (destination, returns) = self.assignment_destination(&place, environment);
                let summary = self.compose(expression.span, summary, destination);
                if !returns { return summary; }
                if self.ownership.assignment_boundary(id) == crate::placeflow::AssignmentBoundary::OutsideFrame {
                    let transferred = self.escape_evaluated_as(value, &replacement, &place.ty(), CallableEscapeBoundary::Assignment);
                    return self.compose(expression.span, summary, transferred);
                }
                if let Some(place_fact) = self.assignment_place_fact(expression.span) {
                    let previous =
                        self.binding_at_place(&place, &place_fact, expression.span, environment);
                    self.record_overwrite(&previous, place_fact, expression.span);
                }
                if !self.assign_binding(&place, replacement.clone(), environment) && replacement.has_capability() {
                    self.error(expression.span, "G5013",
                        "callable assignment destination is not represented in the quantity storage state");
                }
                summary
            }
            CoreKind::Borrow { unique, value } => {
                let summary = self.expression(value, environment);
                if let Some(place) = self.borrow_place_fact(expression.span, unique) {
                    let binding = self.binding_for_value(value, environment);
                    self.record_borrow(&binding, place, expression.span);
                }
                summary
            }
            CoreKind::Deref(value) => self.expression(value, environment),
            CoreKind::Move(value)
            | CoreKind::ReleaseAvailable(value)
            | CoreKind::Field { base: value, .. }
            | CoreKind::PatternTest { subject: value, .. } => self.expression(value, environment),
            CoreKind::Block(values) => {
                let last = values.last().copied();
                let summary = self.sequence(values, environment, expression.span);
                let binding = last.filter(|_| !self.continuations.is_abrupt(id))
                    .map(|last| self.binding_for_value(last, environment)).unwrap_or(Binding::Other);
                self.result_values.insert(id, binding);
                summary
            }
            CoreKind::Tuple(values) | CoreKind::Array(values)
            | CoreKind::Record { fields: values, .. } | CoreKind::Enum { fields: values, .. } => {
                let (summary, values) = self.evaluated_values(values, environment, expression.span);
                let binding = values.map(|values| Binding::Aggregate(values.into_iter().enumerate()
                    .map(|(index, value)| (index as u32, value.binding)).collect())).unwrap_or(Binding::Other);
                self.result_values.insert(id, binding);
                summary
            }
            CoreKind::IntrinsicCall { arguments, .. } => {
                self.sequence(arguments, environment, expression.span)
            }
            CoreKind::Perform {
                arguments,
                payload_types,
                ..
            } => {
                let (summary, arguments) = self.evaluated_values(arguments, environment, expression.span);
                let Some(arguments) = arguments else { return summary; };
                // Performing an operation is a typed ownership boundary just
                // like an ordinary call.  In particular, a callable payload
                // cannot disappear merely because its consumer is selected
                // by a handler rather than named by a function value.  Core
                // has already checked each argument against the frozen
                // operation signature, so the realized argument type is the
                // receiver's per-performance callable requirement here.
                //
                // Do this after evaluating the payloads: a payload can build
                // a closure or move an aggregate field while it is evaluated,
                // and the transfer must observe that exact resulting binding.
                let transfers = self.escape_perform_arguments(
                    &arguments,
                    &payload_types,
                    expression.span,
                );
                self.compose(expression.span, summary, transfers)
            }
            CoreKind::Call {
                callee, arguments, ..
            } => self.call(id, callee, arguments, environment, expression.span),
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                let normal_completion_possible = !computation_must_dispatch(self.body, computation, &clauses, self.signatures);
                // A full-control `_` arm abandons the suspended suffix. The
                // ordinary expression walker is intentionally sequencing
                // oriented, so using its whole computation summary here
                // would incorrectly count a callback *after* a discarded
                // operation as though it ran before the arm. For a direct,
                // statically total discard dispatch, retain exactly the
                // evaluated prefix and then branch into the arm summaries.
                // Resumptive or pattern-uncertain handlers keep the existing
                // conservative summary path until their residual CFG is
                // represented explicitly in Core.
                let before_computation = environment.clone();
                let mut replay_residual = None;
                let mut replay_escapes = None;
                let (computation, incoming) =
                    if let Some(split) = direct_replay_split(self.body, computation, &clauses) {
                        let prefix = self.sequence(split.prefix, environment, expression.span);
                        let arguments =
                            self.sequence(split.operation_arguments, environment, expression.span);
                        let prefix = self.compose(expression.span, prefix, arguments);
                        let mut residual_environment = environment.clone();
                        if let Some(name) = split.result_binding {
                            residual_environment.bindings.insert(name, Binding::Other);
                        }
                        let prefix_escapes = self.take_escapes();
                        replay_residual = Some(self.sequence(
                            split.residual,
                            &mut residual_environment,
                            expression.span,
                        ));
                        replay_escapes = Some(self.take_escapes());
                        self.escapes = prefix_escapes;
                        (prefix, before_computation)
                    } else {
                        match self.discarded_prefix(computation, &clauses, environment) {
                            Some(prefix) => (prefix, before_computation),
                            None => (
                                self.expression(computation, environment),
                                environment.clone(),
                            ),
                        }
                    };
                // Every arm is a mutually exclusive dynamic path. Detach the
                // transfers accumulated by the computation, then join each
                // arm's own transfer summary with `branch_hull` below. This
                // is deliberately conservative for unknown dispatch: an arm
                // may happen, but two sibling arms never happen in sequence.
                let computation_escapes = self.take_escapes();
                // Unless direct dispatch is proved, normal completion skips
                // every operation clause. Include that zero-use path for
                // capabilities owned outside this handler.
                let mut arms = normal_completion_possible.then(Summary::default);
                let mut arm_escapes = normal_completion_possible.then(EscapeSummary::default);
                for clause in clauses {
                    let mut arm_environment = incoming.clone();
                    // Payload binders own fresh capabilities for the one
                    // dynamically selected arm.  They are not aliases of
                    // the performed argument: the outgoing operation
                    // boundary discharges the sender, while this arm must
                    // independently consume or transfer its received owner.
                    // Keep their facts branch-local below, otherwise an arm
                    // that is not selected would spuriously contribute zero
                    // use to a different arm's local capability.
                    let payload_contracts = self.bind_conditional_bindings(
                        &clause.bindings,
                        &mut arm_environment,
                        clause.span,
                    );
                    let continuation_key = match &clause.resumption {
                        CoreHandlerResumption::Explicit { name, quantity, .. } => {
                            let key = self.contract(name, *quantity, clause.span, true);
                            // A generated continuation may intentionally
                            // shadow an ordinary callable parameter. The
                            // outer capability is still owned by the
                            // enclosing callable boundary; do not mistake
                            // lexical shadowing for an implicit zero-use
                            // destruction of that boundary capability.
                            if let Some(Binding::Contract(outer)) =
                                arm_environment.bindings.get(name).cloned()
                                && let Some(contract) = self.contracts.get(&outer)
                            {
                                self.escape_contract(
                                    outer,
                                    Some(contract.declared),
                                    clause.span,
                                    CallableEscapeBoundary::Closure,
                                );
                            }
                            arm_environment
                                .bindings
                                .insert(name.clone(), Binding::Contract(key));
                            Some(key)
                        }
                        // Tail and cancellation are continuation actions too,
                        // not special exemptions from the quantity engine.
                        // Materialize declarative zero/one-use obligations so
                        // the same checker explains ordinary calls, replay,
                        // implicit resumption, and cancellation.
                        CoreHandlerResumption::Tail { quantity } => {
                            Some(self.contract("<tail-resumption>", *quantity, clause.span, true))
                        }
                        CoreHandlerResumption::Discard { quantity } => Some(self.contract(
                            "<cancelled-resumption>",
                            *quantity,
                            clause.span,
                            true,
                        )),
                        CoreHandlerResumption::Terminal => None,
                    };
                    let mut arm = self.expression(clause.body, &mut arm_environment);
                    let replay_actual = if let Some(key) = continuation_key {
                        let actual = match clause.resumption {
                            CoreHandlerResumption::Tail { .. } => Quantity::ONCE,
                            CoreHandlerResumption::Discard { .. } => Quantity::ZERO,
                            CoreHandlerResumption::Explicit { .. }
                            | CoreHandlerResumption::Terminal => {
                                arm.uses.get(&key).copied().unwrap_or(Quantity::ZERO)
                            }
                        };
                        self.facts.insert(key, actual);
                        self.check_contract(key, actual);
                        // The generated continuation is checked above as its
                        // own contract. Its call count is instead the replay
                        // multiplier for residual callable obligations, so it
                        // must not leak into the enclosing branch summary.
                        arm.uses.remove(&key);
                        if let Some(residual) = replay_residual.clone() {
                            let replayed = self.repeat(clause.span, residual, actual);
                            arm = self.compose(clause.span, arm, replayed);
                        }
                        actual
                    } else {
                        Quantity::ZERO
                    };
                    self.check_conditional_contracts(&mut arm, &payload_contracts);
                    let mut escapes = self.take_escapes();
                    if let Some(replay_escapes) = &replay_escapes {
                        let replayed =
                            self.scale_escapes(clause.span, replay_escapes.clone(), replay_actual);
                        self.escapes = escapes;
                        self.sequence_escapes(clause.span, replayed);
                        escapes = self.take_escapes();
                    }
                    arm_escapes = Some(match arm_escapes {
                        Some(previous) => previous.branch_hull(escapes),
                        None => escapes,
                    });
                    arms = Some(match arms {
                        Some(previous) => previous.branch_hull(arm),
                        None => arm,
                    });
                }
                self.escapes = computation_escapes;
                self.sequence_escapes(expression.span, arm_escapes.unwrap_or_default());
                self.compose(expression.span, computation, arms.unwrap_or_default())
            }
            CoreKind::Completion {
                computation,
                clauses,
                ..
            } => {
                let computation_id = computation;
                let computation = self.expression(computation_id, environment);
                let incoming = environment.clone();
                // A completion pattern can deconstruct an already-owned
                // aggregate.  Its binders must retain the canonical callable
                // contract of the selected field rather than manufacture a
                // second, independent owner.  Otherwise
                //
                //   handle pair { Pair { function, .. } =>
                //       function(..) + pair.function(..) }
                //
                // appears to invoke two distinct exact callables even though
                // both spellings name the same affine field.  Fresh
                // computation results still receive fresh contracts below;
                // only a structurally known source carries identities into
                // its pattern binders.
                let completion_source = self.binding_for_value(computation_id, &incoming);
                let computation_escapes = self.take_escapes();
                let mut arms = None::<Summary>;
                let mut arm_escapes = None::<EscapeSummary>;
                let mut results = vec![];
                for clause in clauses {
                    let mut arm_environment = incoming.clone();
                    // Completion patterns have the same conditional-owner
                    // shape as operation payload patterns.  A callable result
                    // is owned only after this completion arm is selected;
                    // checking it after the arm preserves exact lower bounds
                    // without contaminating sibling branch hulls.
                    let completion_contracts = self.bind_completion_bindings(
                        &clause.pattern,
                        &completion_source,
                        &clause.bindings,
                        &mut arm_environment,
                        clause.span,
                    );
                    let arm = self.expression(clause.body, &mut arm_environment);
                    if !self.continuations.is_abrupt(clause.body) {
                        results.push(self.binding_for_value(clause.body, &arm_environment));
                    }
                    let mut arm = arm;
                    self.check_conditional_contracts(&mut arm, &completion_contracts);
                    let escapes = self.take_escapes();
                    arm_escapes = Some(match arm_escapes {
                        Some(previous) => previous.branch_hull(escapes),
                        None => escapes,
                    });
                    arms = Some(match arms {
                        Some(previous) => previous.branch_hull(arm),
                        None => arm,
                    });
                }
                self.escapes = computation_escapes;
                self.sequence_escapes(expression.span, arm_escapes.unwrap_or_default());
                self.result_values.insert(id, Binding::choice(results));
                self.compose(expression.span, computation, arms.unwrap_or_default())
            }
        }
    }

    fn sequence<I>(&mut self, values: I, environment: &mut Environment, span: Span) -> Summary
    where
        I: IntoIterator<Item = CoreId>,
    {
        let mut summary = Summary::default();
        for value in values {
            let next = self.expression(value, environment);
            summary = self.compose(span, summary, next);
            if self.continuations.is_abrupt(value) {
                break;
            }
        }
        summary
    }

    fn evaluated_values(&mut self, values: Vec<CoreId>, environment: &mut Environment, span: Span)
        -> (Summary, Option<Vec<EvaluatedValue>>) {
        let mut summary = Summary::default();
        let mut evaluated = Vec::with_capacity(values.len());
        for expression in values {
            let next = self.expression(expression, environment);
            summary = self.compose(span, summary, next);
            if self.continuations.is_abrupt(expression) { return (summary, None); }
            let binding = self.binding_for_value(expression, environment);
            evaluated.push(EvaluatedValue { expression, binding });
        }
        (summary, Some(evaluated))
    }

    /// Evaluate the prefix of a straight-line Core fragment through its first
    /// definitely intercepted discarded operation. `None` means the fragment
    /// has no such total direct operation, so callers must use ordinary
    /// summary evaluation. This deliberately does not guess through nested
    /// handler/closure/control constructs: retaining the old conservative
    /// behavior there is safer than treating an uncertain suffix as dead.
    fn discarded_prefix(
        &mut self,
        id: CoreId,
        clauses: &[CoreHandlerClause],
        environment: &mut Environment,
    ) -> Option<Summary> {
        let expression = self.body.expression(id).clone();
        match expression.kind {
            CoreKind::Perform {
                effect,
                operation,
                arguments,
                ..
            } if handler_definitely_discards(clauses, &effect, operation) => {
                Some(self.sequence(arguments, environment, expression.span))
            }
            CoreKind::Call { callee, arguments, .. }
                if self.call_may_enter_discarded_handler(callee, clauses) =>
            {
                // An effectful call is not an eager invocation of its
                // callable arguments.  A handler can intercept an operation
                // performed by that callee before it reaches a callback, so
                // evaluation of the callee and its arguments, plus the
                // callee's own invocation, belongs to the live prefix.
                // In particular, do not use
                // `self.call` here: its ordinary outgoing-boundary rule is
                // correct on a normal return, but would incorrectly
                // discharge a captured callable's lower-use obligation on
                // this cancellation path.
                //
                // This is intentionally based on the frozen callable effect
                // row and resolved handler operations rather than package or
                // facade names.  An opaque/imported forwarding function has
                // exactly the same potential cancellation boundary as a
                // local function with the same callable interface.
                let prefix = self.expression(callee, environment);
                if self.continuations.is_abrupt(callee) { return Some(prefix); }
                let receiver = self.binding_for_value(callee, environment);
                let arguments_summary = self.sequence(arguments.clone(), environment, expression.span);
                let prefix = self.compose(expression.span, prefix, arguments_summary);
                if arguments.iter().any(|argument| self.continuations.is_abrupt(*argument)) { return Some(prefix); }
                // The operation can only be intercepted after entering the
                // callee. This does not imply that any callable argument was
                // invoked before cancellation.
                Some(match receiver {
                    Binding::Contract(key) => self.compose(expression.span, prefix, Summary::one(key)),
                    _ => prefix,
                })
            }
            CoreKind::Block(values) => {
                let mut prefix = Summary::default();
                for value in values {
                    if let Some(through_discard) =
                        self.discarded_prefix(value, clauses, environment)
                    {
                        return Some(self.compose(expression.span, prefix, through_discard));
                    }
                    let next = self.expression(value, environment);
                    prefix = self.compose(expression.span, prefix, next);
                }
                None
            }
            // `let value = perform()` does not initialize `value` when the
            // intercepted operation selects a discard arm, so only its RHS
            // prefix may contribute. A normal `let` remains on the ordinary
            // walker path above.
            CoreKind::Let { value, .. } => self.discarded_prefix(value, clauses, environment),
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.discarded_prefix(body, clauses, environment)
            }
            _ => None,
        }
    }

    /// Whether one callable invocation may perform an operation that this
    /// handler definitely cancels.  Effect rows deliberately summarize
    /// *possible* control exits: when such an exit exists, an exact callable
    /// argument cannot be counted as used solely because it crossed the call
    /// boundary.  Its normal-return transfer is still accounted by `call`;
    /// this helper is used only while constructing the cancelled path.
    fn call_may_enter_discarded_handler(
        &self,
        callee: CoreId,
        clauses: &[CoreHandlerClause],
    ) -> bool {
        let Type::Callable { effects, .. } = &self.body.expression(callee).ty else {
            return false;
        };
        // An open or projected row has no complete operation inventory at
        // this boundary.  Preserve the existing conservative walker until
        // its row evidence is normalized into resolved effect instances.
        if !effects.projections.is_empty() || !effects.tails.is_empty() {
            return false;
        }
        effects.effects.iter().any(|effect| {
            self.signatures
                .and_then(|signatures| signatures.definitions.get(&effect.definition))
                .and_then(|header| match header {
                    ElaboratedHeader::Effect(definition) => Some(definition),
                    _ => None,
                })
                .is_some_and(|definition| {
                    definition.operations.iter().enumerate().any(|(operation, _)| {
                        handler_definitely_discards(clauses, effect, operation as u32)
                    })
                })
        })
    }

    fn call(
        &mut self,
        id: CoreId,
        callee: CoreId,
        arguments: Vec<CoreId>,
        environment: &mut Environment,
        span: Span,
    ) -> Summary {
        // Evaluating a callee value does not execute its closure body. Its
        // captures execute only below after direct invocation is known.
        let mut summary = self.expression(callee, environment);
        if self.continuations.is_abrupt(callee) {
            return summary;
        }
        let binding = self.binding_for_value(callee, environment);
        let (evaluated_arguments, inputs) = self.evaluated_values(arguments, environment, span);
        summary = self.compose(span, summary, evaluated_arguments);
        let Some(inputs) = inputs else { return summary; };
        let bindings = inputs.iter().map(|input| input.binding.clone()).collect::<Vec<_>>();
        if !matches!(binding, Binding::Closure(_) | Binding::Choice(_))
            && let Some((body, result)) = self.checked_body_call(id, &binding, &bindings, span) {
            self.result_values.insert(id, result);
            return self.compose(span, summary, body);
        }
        let body = self.invoke_binding(&binding, &inputs, callee, span);
        self.result_values.insert(id, body.1);
        self.compose(span, summary, body.0)
    }

    fn invoke_binding(&mut self, binding: &Binding, inputs: &[EvaluatedValue], callee: CoreId,
        span: Span) -> (Summary, Binding) {
        match binding {
            Binding::Contract(key) => {
                let arguments = self.escape_arguments(callee, inputs, span);
                (self.compose(span, arguments, Summary::one(*key)), Binding::Other)
            }
            Binding::Closure(closure) => self.run_closure(closure.clone(),
                &inputs.iter().map(|input| input.binding.clone()).collect::<Vec<_>>(), span),
            Binding::Choice(choices) => {
                let mut results = vec![];
                let summary = self.branch_bindings(choices, span, |this, binding| {
                    let (summary, result) = this.invoke_binding(binding, inputs, callee, span);
                    results.push(result);
                    summary
                });
                (summary, Binding::choice(results))
            }
            Binding::Aggregate(_) | Binding::GlobalCallable | Binding::Other => {
                (self.escape_arguments(callee, inputs, span), Binding::Other)
            }
        }
    }

    fn binding_for_value(&mut self, id: CoreId, environment: &Environment) -> Binding {
        self.binding_for_value_at_place(id, environment, None)
    }

    fn binding_for_value_at_place(
        &mut self, id: CoreId, environment: &Environment, supplied_place: Option<MoveFact>,
    ) -> Binding {
        let binding = self.binding_for_value_inner(id, environment, supplied_place);
        // A helper inspected under one caller's hypothetical inputs cannot
        // publish universal transport permission for that helper's code.
        if self.active_frames.is_empty() {
            fn replay(binding: &Binding, contracts: &BTreeMap<ContractKey, Contract>) -> bool {
                match binding {
                    Binding::Contract(key) => contracts.get(key).is_some_and(|contract|
                        contract.resumption && contract.declared.lower >= 2
                            && contract.declared.upper == Some(contract.declared.lower)),
                    Binding::Choice(choices) => !choices.is_empty() && choices.iter().all(|value| replay(value, contracts)),
                    _ => false,
                }
            }
            let retained = matches!(self.body.expression(id).ty, Type::Callable { .. })
                && replay(&binding, &self.contracts);
            self.resumption_transfers.entry(id).and_modify(|prior| *prior &= retained).or_insert(retained);
        }
        binding
    }

    fn binding_for_value_inner(
        &mut self,
        id: CoreId,
        environment: &Environment,
        supplied_place: Option<MoveFact>,
    ) -> Binding {
        let expression = self.body.expression(id);
        match &expression.kind {
            CoreKind::Local(name) => environment
                .bindings
                .get(name)
                .cloned()
                .unwrap_or(Binding::Other),
            CoreKind::Resumption { name, .. } => environment
                .bindings
                .get(name)
                .cloned()
                .unwrap_or(Binding::Other),
            CoreKind::Function { .. } | CoreKind::TraitMethod { .. } => Binding::GlobalCallable,
            CoreKind::Field { base, index, .. } => {
                match self.binding_for_value(*base, environment) {
                    Binding::Aggregate(fields) => {
                        fields.get(index).cloned().unwrap_or(Binding::Other)
                    }
                    Binding::Other => self
                        .projected_binding(
                            supplied_place.or_else(|| self.read_place_fact(expression.span)),
                            &expression.ty,
                            expression.span,
                        )
                        .unwrap_or(Binding::Other),
                    Binding::Choice(choices) => Binding::choice(choices.into_iter().map(|binding| match binding {
                        Binding::Aggregate(fields) => fields.get(index).cloned().unwrap_or(Binding::Other),
                        _ => Binding::Other,
                    }).collect()),
                    _ => Binding::Other,
                }
            }
            CoreKind::Tuple(values)
            | CoreKind::Array(values)
            | CoreKind::Record { fields: values, .. }
            | CoreKind::Enum { fields: values, .. } => self.result_values.get(&id).cloned().unwrap_or_else(|| Binding::Aggregate(
                values
                    .iter()
                    .enumerate()
                    .map(|(index, value)| {
                        (index as u32, self.binding_for_value(*value, environment))
                    })
                    .collect(),
            )),
            CoreKind::Move(value) => self.binding_for_value_at_place(
                *value,
                environment,
                self.move_place_fact(expression.span),
            ),
            CoreKind::Closure {
                callable: _,
                parameters,
                environment: closure_environment,
                body,
            } => {
                if let Some(closure) = self.closure_values.get(&id).cloned() {
                    return Binding::Closure(closure);
                }
                // This path is for a consumer that asks for a closure before
                // the normal walker evaluates its captures. Normal closure
                // evaluation installs the pre-transfer snapshot above.
                let captures = closure_environment
                    .captures
                    .iter()
                    .map(|capture| {
                        (
                            capture.name.clone(),
                            environment
                                .bindings
                                .get(&capture.name)
                                .cloned()
                                .unwrap_or(Binding::Other),
                        )
                    })
                    .collect();
                Binding::Closure(ClosureValue {
                    environment: closure_environment.brand,
                    resident_types: closure_environment.captures.iter().map(|capture|
                        (capture.name.clone(), crate::capture_formation::CaptureFormation::new(capture).resident_type())).collect(),
                    body: *body,
                    captures,
                    parameters: parameters.clone(),
                    invocation: callable_invocation(&expression.ty).unwrap_or(Quantity::ONCE),
                })
            }
            CoreKind::Borrow { value, .. } | CoreKind::Deref(value) => self.binding_for_value(*value, environment),
            CoreKind::Call { .. } | CoreKind::Block(_) | CoreKind::Completion { .. } | CoreKind::Handle { .. }
                => self.result_values.get(&id).cloned().unwrap_or(Binding::Other),
            _ => Binding::Other,
        }
    }

    fn binding_for_type(&mut self, name: &str, ty: &Type, span: Span) -> Binding {
        match ty {
            Type::Callable { invocation, .. } => {
                Binding::Contract(self.contract(name, *invocation, span, false))
            }
            Type::Tuple(fields) => Binding::Aggregate(
                fields
                    .iter()
                    .enumerate()
                    .map(|(index, field)| {
                        (
                            index as u32,
                            self.binding_for_type(&format!("{name}.{index}"), field, span),
                        )
                    })
                    .collect(),
            ),
            Type::Nominal {
                definition,
                arguments,
            } => self.nominal_struct_binding(name, *definition, arguments, span),
            _ => Binding::Other,
        }
    }

    /// Struct fields are stable owned projections, unlike enum payloads whose
    /// active variant is not known at a parameter boundary.  Decompose only
    /// the former here; enum and opaque nominal capability ownership remains
    /// conservatively opaque until it gains a variant-sensitive owner model.
    fn nominal_struct_binding(
        &mut self,
        name: &str,
        definition: crate::DefKey,
        arguments: &[crate::GenericArgument],
        span: Span,
    ) -> Binding {
        let Some(ElaboratedHeader::Nominal {
            layout: ElaboratedNominalLayout::Struct(fields) | ElaboratedNominalLayout::TupleStruct(fields),
            ..
        }) = self
            .signatures
            .and_then(|signatures| signatures.definitions.get(&definition))
        else {
            return Binding::Other;
        };
        let mut bindings = BTreeMap::new();
        for (index, field) in fields.iter().enumerate() {
            let Ok(field_type) = instantiate_nominal_field_type(&field.ty, arguments) else {
                // Frozen signature validation normally makes this impossible.
                // Do not invent a partially decomposed owner for malformed
                // imported Core; its structural validator remains the
                // authoritative fail-closed boundary.
                return Binding::Other;
            };
            bindings.insert(
                index as u32,
                self.binding_for_type(&format!("{name}.{index}"), &field_type, span),
            );
        }
        Binding::Aggregate(bindings)
    }

    /// Install the bindings introduced by one conditionally selected arm and
    /// return every fresh callable contract they own.  Those contracts are
    /// deliberately checked at the arm boundary, rather than being carried
    /// through the enclosing branch hull: a payload/result owner does not
    /// exist on sibling exits where its pattern did not match.
    fn bind_conditional_bindings(
        &mut self,
        bindings: &[(String, Type)],
        environment: &mut Environment,
        span: Span,
    ) -> Vec<ContractKey> {
        let mut contracts = vec![];
        for (name, ty) in bindings {
            let binding = self.binding_for_type(name, ty, span);
            Self::binding_contract_keys(&binding, &mut contracts);
            environment.bindings.insert(name.clone(), binding);
        }
        contracts
    }

    /// Install normal-completion pattern binders.  Unlike effect payload
    /// binders, a completion pattern may select a field of an aggregate that
    /// remains lexically named outside the pattern.  Preserve that field's
    /// contract key so all aliases contribute to the one owner obligation.
    ///
    /// If the computation is an opaque or newly produced value there is no
    /// pre-existing binding to preserve, so the fallback intentionally keeps
    /// the conditional fresh-owner behavior used by the former implementation.
    fn bind_completion_bindings(
        &mut self,
        pattern: &CorePattern,
        source: &Binding,
        bindings: &[(String, Type)],
        environment: &mut Environment,
        span: Span,
    ) -> Vec<ContractKey> {
        let mut projected = BTreeMap::new();
        Self::pattern_bindings(pattern, source, &mut projected);
        let mut contracts = vec![];
        for (name, ty) in bindings {
            let binding = projected
                .remove(name)
                .unwrap_or_else(|| self.binding_for_type(name, ty, span));
            Self::binding_contract_keys(&binding, &mut contracts);
            environment.bindings.insert(name.clone(), binding);
        }
        contracts
    }

    /// Recover each binder's ownership identity from a structural Core
    /// pattern.  A missing/opaque field deliberately yields no entry: its
    /// caller allocates the fresh conditional owner appropriate for a value
    /// received from a callable/effect boundary.
    fn pattern_bindings(
        pattern: &CorePattern,
        source: &Binding,
        bindings: &mut BTreeMap<String, Binding>,
    ) {
        match pattern {
            CorePattern::Bind { name } => {
                // `Other` carries no ownership identity.  Do not install it
                // as though it were an alias: the caller must allocate the
                // fresh conditional contract dictated by the binder type
                // (for example, a callable field of a newly returned
                // nominal value).
                if !matches!(source, Binding::Other) {
                    bindings.insert(name.clone(), source.clone());
                }
            }
            CorePattern::Tuple(values) => {
                for (index, pattern) in values.iter().enumerate() {
                    let field = match source {
                        Binding::Aggregate(fields) => fields
                            .get(&(index as u32))
                            .cloned()
                            .unwrap_or(Binding::Other),
                        _ => Binding::Other,
                    };
                    Self::pattern_bindings(pattern, &field, bindings);
                }
            }
            CorePattern::Array { elements, rest, .. } => {
                for (index, pattern) in elements.iter().enumerate() {
                    let index = crate::pattern::ArrayPatternRest::index(*rest, index);
                    let field = match source {
                        Binding::Aggregate(fields) => fields
                            .get(&(index as u32))
                            .cloned()
                            .unwrap_or(Binding::Other),
                        _ => Binding::Other,
                    };
                    Self::pattern_bindings(pattern, &field, bindings);
                }
            }
            CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
                for field_pattern in fields {
                    let field = match source {
                        Binding::Aggregate(fields) => fields
                            .get(&field_pattern.index)
                            .cloned()
                            .unwrap_or(Binding::Other),
                        _ => Binding::Other,
                    };
                    Self::pattern_bindings(&field_pattern.pattern, &field, bindings);
                }
            }
            CorePattern::Any | CorePattern::Literal(_) | CorePattern::Error => {}
        }
    }

    fn binding_contract_keys(binding: &Binding, contracts: &mut Vec<ContractKey>) {
        match binding {
            Binding::Choice(choices) => {
                for binding in choices { Self::binding_contract_keys(binding, contracts); }
            }
            Binding::Contract(key) => contracts.push(*key),
            Binding::Aggregate(fields) => {
                for binding in fields.values() {
                    Self::binding_contract_keys(binding, contracts);
                }
            }
            Binding::Closure(_) | Binding::GlobalCallable | Binding::Other => {}
        }
    }

    /// Check conditional arm owners before joining the arm summaries.  We
    /// retain their observed fact for diagnostics/tooling, but remove it from
    /// the outer summary: the key is fresh for this arm and therefore cannot
    /// be interpreted as a zero-use owner on an unselected sibling arm.
    fn check_conditional_contracts(&mut self, arm: &mut Summary, contracts: &[ContractKey]) {
        for key in contracts {
            let actual = arm.uses.remove(key).unwrap_or(Quantity::ZERO);
            self.facts.insert(*key, actual);
            self.check_contract(*key, actual);
        }
    }

    fn callable_parameter_types(&self, callee: CoreId) -> Vec<Type> {
        match &self.body.expression(callee).ty {
            Type::Callable { parameters, .. } => parameters.clone(),
            _ => vec![],
        }
    }

    fn escape_perform_arguments(
        &mut self,
        arguments: &[EvaluatedValue],
        payload_types: &[Type],
        span: Span,
    ) -> Summary {
        // `TypedBody::validate` independently proves this arity relation.
        // Keep the zip explicit nevertheless: malformed imported Core must
        // fail validation before UseFlow is requested, never manufacture a
        // payload capability from an unmatched sender expression.
        let mut summary = Summary::default();
        for (argument, payload_type) in arguments.iter().zip(payload_types) {
            // The selected operation declaration, not the sender expression,
            // owns this contract.  A generic argument may have been inferred
            // or coerced into the parameter; `payload_types` is the zonked,
            // instantiated receiver ABI frozen in Core.
            let next = self.escape_evaluated_as(
                argument.expression,
                &argument.binding,
                payload_type,
                CallableEscapeBoundary::Argument,
            );
            summary = self.compose(span, summary, next);
        }
        summary
    }

    fn assignment_place_fact(&self, span: Span) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            matches!(event.kind, FlowEventKind::Assign(_))
                .then_some(())
                .filter(|_| event.span == span)
                .and(event.place.clone())
        })
    }

    fn move_place_fact(&self, span: Span) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            matches!(event.kind, FlowEventKind::Move(_))
                .then_some(())
                .filter(|_| event.span == span)
                .and(event.place.clone())
        })
    }

    fn read_place_fact(&self, span: Span) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            matches!(event.kind, FlowEventKind::Read(_))
                .then_some(())
                .filter(|_| event.span == span)
                .and(event.place.clone())
        })
    }

    fn projected_binding(
        &mut self,
        place: Option<MoveFact>,
        ty: &Type,
        span: Span,
    ) -> Option<Binding> {
        let place = place?;
        let invocation = callable_invocation(ty)?;
        let key = match self.projected_contracts.get(&place).copied() {
            Some(key) => key,
            None => {
                let name = display_place(&place);
                let key = self.contract(&name, invocation, span, false);
                self.projected_contracts.insert(place, key);
                key
            }
        };
        Some(Binding::Contract(key))
    }

    fn borrow_place_fact(&self, span: Span, unique: bool) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            let matches_kind = matches!(
                (&event.kind, unique),
                (FlowEventKind::BorrowUnique(_), true) | (FlowEventKind::BorrowShared(_), false)
            );
            matches_kind
                .then_some(())
                .filter(|_| event.span == span)
                .and(event.place.clone())
        })
    }

    fn closure_place_fact(
        &self,
        span: Span,
        root: &str,
        source: crate::capture_formation::CaptureSource,
    ) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            use crate::capture_formation::CaptureSource;
            let matches_kind = match (&event.kind, source) {
                (FlowEventKind::Move(name), CaptureSource::Move)
                | (FlowEventKind::BorrowShared(name), CaptureSource::Borrow(crate::Mutability::Shared))
                | (FlowEventKind::BorrowUnique(name), CaptureSource::Borrow(crate::Mutability::Unique))
                | (FlowEventKind::Read(name), CaptureSource::Copy) => name == root,
                _ => false,
            };
            matches_kind
                .then_some(())
                .filter(|_| event.span == span)
                .and(event.place.clone())
        })
    }

    fn binding_at_place(
        &mut self,
        place: &CorePlace,
        place_fact: &MoveFact,
        span: Span,
        environment: &Environment,
    ) -> Binding {
        let binding = self.existing_binding_at_place(place, environment);
        if matches!(binding, Binding::Other) {
            self.projected_binding(Some(place_fact.clone()), &place.ty(), span)
                .unwrap_or(Binding::Other)
        } else {
            binding
        }
    }

    fn existing_binding_at_place(&self, place: &CorePlace, environment: &Environment) -> Binding {
        match place {
            CorePlace::Local { name, .. } => environment
                .bindings
                .get(name)
                .cloned()
                .unwrap_or(Binding::Other),
            CorePlace::Field { base, index, .. } => {
                match self.existing_binding_at_place(base, environment) {
                    Binding::Aggregate(fields) => {
                        fields.get(index).cloned().unwrap_or(Binding::Other)
                    }
                    _ => Binding::Other,
                }
            }
            CorePlace::Deref { .. } => Binding::Other,
            CorePlace::Error => Binding::Other,
        }
    }

    fn assignment_destination(&mut self, place: &CorePlace, environment: &mut Environment) -> (Summary, bool) {
        match place {
            CorePlace::Field { base, .. } => self.assignment_destination(base, environment),
            CorePlace::Deref { reference, .. } => {
                let summary = self.expression(*reference, environment);
                (summary, !self.continuations.is_abrupt(*reference))
            }
            CorePlace::Local { .. } | CorePlace::Error => (Summary::default(), true),
        }
    }

    fn assign_binding(
        &mut self,
        place: &CorePlace,
        replacement: Binding,
        environment: &mut Environment,
    ) -> bool {
        match place {
            CorePlace::Local { name, .. } => {
                environment.bindings.insert(name.clone(), replacement);
                true
            }
            CorePlace::Field { base, index, .. } => {
                let mut aggregate = self.existing_binding_at_place(base, environment);
                if let Binding::Aggregate(fields) = &mut aggregate {
                    fields.insert(*index, replacement);
                    self.assign_binding(base, aggregate, environment)
                } else { false }
            }
            CorePlace::Deref { .. } | CorePlace::Error => false,
        }
    }

    fn take_moved_binding(&mut self, id: CoreId, environment: &mut Environment) {
        match &self.body.expression(id).kind {
            CoreKind::Move(value) => self.take_moved_binding(*value, environment),
            CoreKind::Local(name) => {
                environment.bindings.insert(name.clone(), Binding::Other);
            }
            CoreKind::Field { base, index, .. } => {
                let mut aggregate = self.binding_for_value(*base, environment);
                if let Binding::Aggregate(fields) = &mut aggregate {
                    fields.insert(*index, Binding::Other);
                    self.replace_expression_binding(*base, aggregate, environment);
                }
            }
            _ => {}
        }
    }

    fn replace_expression_binding(
        &mut self,
        id: CoreId,
        replacement: Binding,
        environment: &mut Environment,
    ) {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => {
                environment.bindings.insert(name.clone(), replacement);
            }
            CoreKind::Field { base, index, .. } => {
                let mut aggregate = self.binding_for_value(*base, environment);
                if let Binding::Aggregate(fields) = &mut aggregate {
                    fields.insert(*index, replacement);
                    self.replace_expression_binding(*base, aggregate, environment);
                }
            }
            _ => {}
        }
    }

    fn record_overwrite(&mut self, binding: &Binding, place: MoveFact, span: Span) {
        match binding {
            Binding::Choice(choices) => {
                for binding in choices { self.record_overwrite(binding, place.clone(), span); }
            }
            Binding::Contract(key) => {
                let Some(contract) = self.contracts.get(key) else {
                    return;
                };
                self.value_obligations.push(ValueUseFact {
                    place: place.clone(),
                    declared: contract.declared,
                    actual: Quantity::ZERO,
                    span,
                    disposition: ValueUseDisposition::Overwritten,
                });
                if contract.declared.requires_positive_use() {
                    self.error(
                        span,
                        "G5014",
                        format!(
                            "assignment overwrites `{}` and abandons its required callable-use obligation [{}, {}]",
                            display_place(&place),
                            contract.declared.lower,
                            display_upper(contract.declared.upper),
                        ),
                    );
                }
            }
            Binding::Aggregate(fields) => {
                for (field, binding) in fields {
                    let mut child = place.clone();
                    child.fields.push(*field);
                    self.record_overwrite(binding, child, span);
                }
            }
            Binding::Closure(_) | Binding::GlobalCallable | Binding::Other => {}
        }
    }

    fn record_transfer(&mut self, binding: &Binding, place: MoveFact, span: Span) {
        match binding {
            Binding::Choice(choices) => {
                for binding in choices { self.record_transfer(binding, place.clone(), span); }
            }
            Binding::Contract(key) => {
                if let Some(contract) = self.contracts.get(key) {
                    self.value_obligations.push(ValueUseFact {
                        place,
                        declared: contract.declared,
                        actual: Quantity::ZERO,
                        span,
                        disposition: ValueUseDisposition::Transferred,
                    });
                }
            }
            Binding::Aggregate(fields) => {
                for (field, binding) in fields {
                    let mut child = place.clone();
                    child.fields.push(*field);
                    self.record_transfer(binding, child, span);
                }
            }
            Binding::Closure(_) | Binding::GlobalCallable | Binding::Other => {}
        }
    }

    fn record_borrow(&mut self, binding: &Binding, place: MoveFact, span: Span) {
        match binding {
            Binding::Choice(choices) => {
                for binding in choices { self.record_borrow(binding, place.clone(), span); }
            }
            Binding::Contract(key) => {
                if let Some(contract) = self.contracts.get(key) {
                    self.value_obligations.push(ValueUseFact {
                        place,
                        declared: contract.declared,
                        actual: Quantity::ZERO,
                        span,
                        disposition: ValueUseDisposition::Borrowed,
                    });
                }
            }
            Binding::Aggregate(fields) => {
                for (field, binding) in fields {
                    let mut child = place.clone();
                    child.fields.push(*field);
                    self.record_borrow(binding, child, span);
                }
            }
            Binding::Closure(_) | Binding::GlobalCallable | Binding::Other => {}
        }
    }

    fn escape_arguments(
        &mut self,
        callee: CoreId,
        arguments: &[EvaluatedValue],
        span: Span,
    ) -> Summary {
        let parameter_types = self.callable_parameter_types(callee);
        let mut summary = Summary::default();
        for (index, argument) in arguments.iter().enumerate() {
            let next = if let Some(parameter_type) = parameter_types.get(index) {
                self.escape_evaluated_as(
                    argument.expression,
                    &argument.binding,
                    parameter_type,
                    CallableEscapeBoundary::Argument,
                )
            } else {
                // Typed Core validates call arity before this analysis. Keep
                // malformed frozen input fail-closed rather than assuming an
                // arbitrary capability for an unmatched argument.
                self.escape_binding(
                    &argument.binding,
                    None,
                    self.body.expression(argument.expression).span,
                    CallableEscapeBoundary::Argument,
                )
            };
            summary = self.compose(span, summary, next);
        }
        summary
    }

    fn escape_contract(
        &mut self,
        key: ContractKey,
        required: Option<Quantity>,
        span: Span,
        boundary: CallableEscapeBoundary,
    ) {
        let escape = Escape {
            required,
            span,
            boundary,
            actual: Quantity::ONCE,
        };
        self.record_escape(key, escape);
    }

    fn record_escape(&mut self, key: ContractKey, escape: Escape) {
        if let Some(required) = escape.required {
            let demanded = match required.multiply(escape.actual) {
                Ok(demanded) => demanded,
                Err(QuantityError::Overflow) => {
                    self.error(
                        escape.span,
                        "G5010",
                        "quantitative callable escape demand overflowed",
                    );
                    self.escapes.facts.entry(key).or_default().push(escape);
                    return;
                }
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity products are never empty")
                }
            };
            let total = self
                .escapes
                .demand
                .get(&key)
                .copied()
                .unwrap_or(Quantity::ZERO)
                .sequence(demanded);
            match total {
                Ok(total) => {
                    self.escapes.demand.insert(key, total);
                }
                Err(QuantityError::Overflow) => self.error(
                    escape.span,
                    "G5010",
                    "quantitative callable escape demand overflowed",
                ),
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity summaries are never empty")
                }
            }
        }
        self.escapes.facts.entry(key).or_default().push(escape);
    }

    /// Detach transfers from the current evaluation fragment. Branches and
    /// closure bodies use this to establish their own path summary before it
    /// is sequenced back into the surrounding path.
    fn take_escapes(&mut self) -> EscapeSummary {
        std::mem::take(&mut self.escapes)
    }

    fn sequence_escapes(&mut self, span: Span, escapes: EscapeSummary) {
        let current = self.take_escapes();
        self.escapes = match current.clone().sequence(escapes) {
            Ok(escapes) => escapes,
            Err(QuantityError::Overflow) => {
                self.error(
                    span,
                    "G5010",
                    "quantitative callable escape demand overflowed",
                );
                current
            }
            Err(QuantityError::EmptyInterval) => {
                unreachable!("quantity summaries are never empty")
            }
        };
    }

    fn scale_escapes(
        &mut self,
        span: Span,
        escapes: EscapeSummary,
        multiplier: Quantity,
    ) -> EscapeSummary {
        match escapes.multiply(multiplier) {
            Ok(escapes) => escapes,
            Err(QuantityError::Overflow) => {
                self.error(
                    span,
                    "G5010",
                    "quantitative callable escape count overflowed",
                );
                EscapeSummary::default()
            }
            Err(QuantityError::EmptyInterval) => {
                unreachable!("quantity summaries are never empty")
            }
        }
    }

    fn escape_closure(&mut self, closure: ClosureValue, span: Span) -> Summary {
        // A closure environment is a first-class owner, not a memoized
        // summary.  Every outgoing call boundary that receives this closure
        // may activate its captures, even if the receiver is an imported
        // declaration and the closure's generated callable identity is the
        // same.  Suppressing a later transfer by `CallableId` made
        // `invoke(callback) + invoke(callback)` look like one activation of
        // a move-captured exact callable.
        //
        // Closure capture graphs are lexical snapshots: a closure can refer
        // to an enclosing closure but cannot capture its own not-yet-bound
        // local name.  Re-evaluating this snapshot therefore terminates and
        // accurately charges each independent transfer.
        self.run_closure(closure, &[], span).0
    }

    /// Transfer a value into a receiver whose complete structural callable
    /// contract is known.  Callable capability is recursive: a `Pair<F>` is
    /// not an untyped shell when `F` is an exactly-once callable.  The old
    /// top-level-only check lost that receiver proof and rejected ordinary
    /// forwarding of a parameter-owned record with `G5013`.
    fn escape_value_as(
        &mut self,
        id: CoreId,
        environment: &Environment,
        expected: &Type,
        boundary: CallableEscapeBoundary,
    ) -> Summary {
        let binding = self.binding_for_value(id, environment);
        self.escape_evaluated_as(id, &binding, expected, boundary)
    }

    fn escape_evaluated_as(
        &mut self, id: CoreId, binding: &Binding, expected: &Type, boundary: CallableEscapeBoundary,
    ) -> Summary {
        if let CoreKind::Block(values) = &self.body.expression(id).kind {
            // Only the tail value crosses this boundary. Prefix expressions
            // were checked during evaluation; neither discard their use
            // counts nor reclassify them as outgoing capabilities.
            return values.last().map_or_else(Summary::default, |value|
                self.escape_evaluated_as(*value, binding, expected, boundary));
        }
        // An enum constructor carries its active variant at this expression,
        // unlike an enum parameter whose variant is genuinely dynamic. Use
        // that proof to preserve payload capabilities across a call or effect
        // boundary, including generic substitutions in the selected layout.
        if let CoreKind::Enum {
            definition,
            variant,
            fields,
        } = &self.body.expression(id).kind
            && let Some(field_types) =
                self.enum_variant_field_types(expected, *definition, *variant)
            && field_types.len() == fields.len()
            && let Binding::Aggregate(bindings) = binding
            && bindings.len() == fields.len()
        {
            let mut summary = Summary::default();
            for (index, (field, field_type)) in fields.iter().zip(field_types.iter()).enumerate() {
                let Some(field_binding) = bindings.get(&(index as u32)) else {
                    return self.escape_binding(binding, None, self.body.expression(id).span, boundary);
                };
                let next = self.escape_evaluated_as(*field, field_binding, field_type, boundary);
                summary = self.compose(self.body.expression(id).span, summary, next);
            }
            return summary;
        }
        self.escape_binding_as(binding, expected, self.body.expression(id).span, boundary)
    }

    fn escape_binding_as(
        &mut self,
        binding: &Binding,
        expected: &Type,
        span: Span,
        boundary: CallableEscapeBoundary,
    ) -> Summary {
        match binding {
            Binding::Contract(key) => {
                self.escape_contract(*key, callable_invocation(expected), span, boundary);
                Summary::default()
            }
            Binding::Closure(closure) => self.escape_closure(closure.clone(), span),
            Binding::Choice(choices) => self.branch_bindings(choices, span,
                |this, binding| this.escape_binding_as(binding, expected, span, boundary)),
            Binding::Aggregate(fields) => {
                let mut summary = Summary::default();
                for (index, binding) in fields {
                    let next =
                        if let Some(field_type) = self.structural_field_type(expected, *index) {
                            self.escape_binding_as(binding, &field_type, span, boundary)
                        } else {
                            // For an aggregate whose active layout cannot be
                            // proven here (notably a dynamic enum parameter),
                            // retain the existing conservative diagnostic rather
                            // than silently treating an affine payload as copied.
                            self.escape_binding(binding, None, span, boundary)
                        };
                    summary = self.compose(span, summary, next);
                }
                summary
            }
            Binding::GlobalCallable | Binding::Other => Summary::default(),
        }
    }

    fn structural_field_type(&self, expected: &Type, index: u32) -> Option<Type> {
        match expected {
            Type::Tuple(fields) => fields.get(index as usize).cloned(),
            Type::Array(element) => Some((**element).clone()),
            Type::FixedArray { element, .. } if expected.fixed_array_length().is_some_and(|n| u64::from(index) < n) => Some((**element).clone()),
            Type::Nominal {
                definition,
                arguments,
            } => self
                .signatures?
                .instantiate_struct_fields_generic(*definition, arguments)
                .ok()?
                .get(index as usize)
                .map(|field| field.ty.clone()),
            _ => None,
        }
    }

    fn enum_variant_field_types(
        &self,
        expected: &Type,
        definition: crate::DefKey,
        variant: u32,
    ) -> Option<Vec<Type>> {
        let Type::Nominal {
            definition: actual,
            arguments,
        } = expected
        else {
            return None;
        };
        (*actual == definition).then(|| {
            self.signatures?
                .instantiate_enum_fields_generic(definition, arguments, variant)
                .ok()
                .map(|fields| fields.into_iter().map(|field| field.ty).collect())
        })?
    }

    fn escape_binding(
        &mut self,
        binding: &Binding,
        required: Option<Quantity>,
        span: Span,
        boundary: CallableEscapeBoundary,
    ) -> Summary {
        match binding {
            Binding::Contract(key) => {
                self.escape_contract(*key, required, span, boundary);
                Summary::default()
            }
            Binding::Closure(closure) => self.escape_closure(closure.clone(), span),
            Binding::Choice(choices) => self.branch_bindings(choices, span,
                |this, binding| this.escape_binding(binding, required, span, boundary)),
            Binding::Aggregate(fields) => {
                let mut summary = Summary::default();
                for binding in fields.values() {
                    let next = self.escape_binding(binding, required, span, boundary);
                    summary = self.compose(span, summary, next);
                }
                summary
            }
            Binding::GlobalCallable | Binding::Other => Summary::default(),
        }
    }

    fn check_contract(&mut self, key: ContractKey, actual: Quantity) {
        let Some(contract) = self.contracts.get(&key).cloned() else {
            return;
        };
        if contract.resumption {
            if contract.declared.contains(actual) {
                return;
            }
            self.contract_error(&contract, actual, "G5012");
            return;
        }

        let escapes = self.escapes.facts.get(&key).cloned().unwrap_or_default();
        if escapes.is_empty() {
            if contract.declared.contains(actual) {
                return;
            }
            self.contract_error(&contract, actual, "G5011");
            return;
        }

        // Direct invocations and outgoing callable capabilities consume the
        // same source budget. A transfer may discharge a lower bound through
        // its receiver, but it cannot make a preceding local invocation free.
        let mut escaped_at = None;
        for escape in escapes {
            if escape.required.is_none() {
                self.error(
                    escape.span,
                    "G5013",
                    format!(
                        "callable `{}` escapes through {} without a compatible callable-use capability; declared [{}, {}]",
                        contract.name,
                        display_boundary(escape.boundary),
                        contract.declared.lower,
                        display_upper(contract.declared.upper),
                    ),
                );
                continue;
            }
            escaped_at.get_or_insert((escape.span, escape.boundary));
        }
        if let Some((span, boundary)) = escaped_at {
            let escaped_demand = self
                .escapes
                .demand
                .get(&key)
                .copied()
                .unwrap_or(Quantity::ZERO);
            let total_demand = match actual.sequence(escaped_demand) {
                Ok(total) => total,
                Err(QuantityError::Overflow) => {
                    self.error(
                        span,
                        "G5010",
                        "quantitative callable use and escape demand overflowed",
                    );
                    return;
                }
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity summaries are never empty")
                }
            };
            if !contract.declared.contains(total_demand) {
                self.error(
                    span,
                    "G5013",
                    format!(
                        "callable `{}` has direct use [{}, {}] and escapes through {} with combined demand [{}, {}], exceeding its declared capability [{}, {}]",
                        contract.name,
                        actual.lower,
                        display_upper(actual.upper),
                        display_boundary(boundary),
                        total_demand.lower,
                        display_upper(total_demand.upper),
                        contract.declared.lower,
                        display_upper(contract.declared.upper),
                    ),
                );
            }
        } else if !upper_within(actual.upper, contract.declared.upper) {
            // An unresolved receiver already has its own G5013 diagnostic.
            // Preserve the local upper-bound check without treating its
            // missing lower capability as a second contract violation.
            self.contract_error(&contract, actual, "G5011");
        }
    }

    fn contract_error(&mut self, contract: &Contract, actual: Quantity, code: &'static str) {
        let subject = if contract.resumption {
            "handler continuation"
        } else {
            "callable"
        };
        self.error(
            contract.span,
            code,
            format!(
                "{subject} `{}` is invoked [{}, {}] but its declared quantity is [{}, {}]",
                contract.name,
                actual.lower,
                display_upper(actual.upper),
                contract.declared.lower,
                display_upper(contract.declared.upper),
            ),
        );
    }

    fn finish(mut self) -> UseFlow {
        // Parameters and aliases live across the whole root control-flow tree.
        // Handler continuations are checked per arm above, because their
        // quantity is conditional on operation selection rather than on the
        // outer handler expression being evaluated.
        for (key, contract) in self.contracts.clone() {
            if contract.resumption {
                continue;
            }
            let actual = self.facts.get(&key).copied().unwrap_or(Quantity::ZERO);
            self.check_contract(key, actual);
        }
        let mut callable_uses = self
            .contracts
            .iter()
            .map(|(key, contract)| CallableUseFact {
                name: contract.name.clone(),
                declared: contract.declared,
                actual: self.facts.get(key).copied().unwrap_or(Quantity::ZERO),
                span: contract.span,
                resumption: contract.resumption,
            })
            .collect::<Vec<_>>();
        callable_uses.sort_by(|left, right| {
            left.span
                .start
                .cmp(&right.span.start)
                .then(left.name.cmp(&right.name))
        });
        let mut callable_escapes = self
            .escapes
            .facts
            .iter()
            .flat_map(|(key, escapes)| {
                let contract = &self.contracts[key];
                escapes.iter().map(move |escape| CallableEscapeFact {
                    name: contract.name.clone(),
                    declared: contract.declared,
                    required: escape.required,
                    actual: escape.actual,
                    span: escape.span,
                    boundary: escape.boundary,
                })
            })
            .collect::<Vec<_>>();
        callable_escapes.sort_by(|left, right| {
            left.span
                .start
                .cmp(&right.span.start)
                .then(left.name.cmp(&right.name))
        });
        self.value_obligations.sort_by(|left, right| {
            left.span
                .start
                .cmp(&right.span.start)
                .then(left.place.root.cmp(&right.place.root))
                .then(left.place.fields.cmp(&right.place.fields))
        });
        self.diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        UseFlow {
            resumption_transfers: self.diagnostics.is_empty().then(|| std::sync::Arc::new(ResumptionTransfers {
                input: self.body.semantic_fingerprint(),
                values: self.resumption_transfers.into_iter().filter_map(|(value, retained)| retained.then_some(value)).collect(),
            })),
            callable_uses,
            callable_escapes,
            value_obligations: self.value_obligations,
            diagnostics: self.diagnostics,
        }
    }
}

fn callable_invocation(ty: &Type) -> Option<Quantity> {
    match ty {
        Type::Callable { invocation, .. } => Some(*invocation),
        _ => None,
    }
}

fn display_upper(value: Option<u64>) -> String {
    value.map_or_else(|| "*".into(), |value| value.to_string())
}

fn upper_within(actual: Option<u64>, declared: Option<u64>) -> bool {
    match (actual, declared) {
        (_, None) => true,
        (Some(actual), Some(declared)) => actual <= declared,
        (None, Some(_)) => false,
    }
}

fn display_boundary(boundary: CallableEscapeBoundary) -> &'static str {
    match boundary {
        CallableEscapeBoundary::Result => "the result boundary",
        CallableEscapeBoundary::Argument => "a callable argument",
        CallableEscapeBoundary::Assignment => "an assigned place",
        CallableEscapeBoundary::Closure => "a closure environment",
    }
}

fn display_place(place: &MoveFact) -> String {
    place
        .fields
        .iter()
        .fold(place.root.clone(), |mut value, field| {
            value.push('.');
            value.push_str(&field.to_string());
            value
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CallableId;
    use crate::{
        core::{CaptureMode, ClosureCapture, CoreCompletionClause, CoreExpr},
        identity::{FileKey, PackageKey},
        types::EffectRow,
    };

    fn span() -> Span {
        Span {
            file: FileKey::new(&PackageKey("useflow-test@0".into()), "main.glorious"),
            start: 0,
            end: 1,
        }
    }

    fn callable(invocation: Quantity) -> Type {
        Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![Type::Scalar(crate::types::ScalarType::I64)],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation,
        }
    }

    fn receiver_replacement_body() -> TypedBody {
        let callback = callable(Quantity::AFFINE);
        let integer = Type::Scalar(crate::ScalarType::I64);
        let expression = |kind, ty| CoreExpr { kind, ty, span: span() };
        let invoke = |callee, argument| CoreKind::Call {
            mandatory_tail: false, callee, arguments: vec![argument],
            invocation: crate::core::CoreCallContract { declaration: callback.clone(), effects: EffectRow::empty() },
            reference_contract: crate::core::CallReferenceOrigin::None,
            reference_origin: crate::core::CallReferenceOrigin::None,
            reference_shape: crate::core::CallReferenceShape::None,
        };
        TypedBody {
            safety: crate::Safety::Safe, unsafe_scopes: Default::default(), unsafe_implementations: Default::default(),
            body_regions: Default::default(), parameters: vec![("first".into(), callback.clone()), ("second".into(), callback.clone())],
            expressions: vec![
                expression(CoreKind::Local("first".into()), callback.clone()),
                expression(CoreKind::Let { name:"current".into(), value:CoreId(0), stored_type: callback.clone() }, Type::Unit),
                expression(CoreKind::Local("current".into()), callback.clone()),
                expression(CoreKind::Local("second".into()), callback.clone()),
                expression(CoreKind::Assign { place: CorePlace::Local { name:"current".into(), ty:callback.clone() }, value:CoreId(3) }, Type::Unit),
                expression(CoreKind::Literal("0".into()), integer.clone()),
                expression(CoreKind::Block(vec![CoreId(4), CoreId(5)]), integer.clone()),
                expression(invoke(CoreId(2), CoreId(6)), integer.clone()),
                expression(invoke(CoreId(0), CoreId(5)), integer.clone()),
                expression(CoreKind::Block(vec![CoreId(1), CoreId(7), CoreId(8)]), integer),
            ], root:CoreId(9), diagnostics:vec![], recovered:false,
        }
    }

    fn checked_uses(body: &TypedBody) -> UseFlow {
        assert!(body.validate().is_empty(), "{:?}", body.validate());
        let ownership = PlaceFlow::analyze(body);
        assert!(ownership.diagnostics.is_empty(), "{:?}", ownership.diagnostics);
        UseFlow::analyze(body, &ownership)
    }

    #[test]
    fn argument_replacement_cannot_change_the_already_evaluated_receiver() {
        let body = receiver_replacement_body();
        let uses = checked_uses(&body);
        let first = uses.callable_uses.iter().find(|fact| fact.name == "first").unwrap();
        assert_eq!(first.actual, Quantity::new(2, Some(2)).unwrap(), "{uses:#?}");
        assert!(!uses.diagnostics.is_empty(), "the original affine receiver was invoked twice");
        let mut once = body;
        once.expressions[9].kind = CoreKind::Block(vec![CoreId(1), CoreId(7)]);
        let uses = checked_uses(&once);
        assert!(uses.diagnostics.is_empty(), "{uses:#?}");
        assert_eq!(uses.callable_uses.iter().find(|fact| fact.name == "first").unwrap().actual, Quantity::ONCE);
        assert_eq!(uses.callable_uses.iter().find(|fact| fact.name == "second").unwrap().actual, Quantity::ZERO);
    }

    #[test]
    fn later_operands_cannot_replace_prior_argument_or_aggregate_field_capabilities() {
        for aggregate in [false, true] {
            let mut body = receiver_replacement_body();
            let mut arguments = vec![CoreId(2), CoreId(6)];
            let mut parameters = vec![callable(Quantity::AFFINE), Type::Scalar(crate::ScalarType::I64)];
            if aggregate {
                let ty = Type::Tuple(parameters);
                parameters = vec![ty.clone()];
                let tuple = CoreId(body.expressions.len() as u32);
                body.expressions.push(CoreExpr { kind:CoreKind::Tuple(arguments), ty, span:span() });
                arguments = vec![tuple];
            }
            let target = Type::Callable { contract:Default::default(), safety:crate::Safety::Safe,
                lifetime_binders:0, parameters, result:Box::new(Type::Scalar(crate::ScalarType::I64)),
                effects:EffectRow::empty(), invocation:Quantity::UNRESTRICTED };
            let callee = CoreId(body.expressions.len() as u32);
            body.expressions.push(CoreExpr { kind:CoreKind::Function {
                definition:crate::DefKey(crate::Digest::of_bytes(b"snapshot-argument-consumer")), arguments:vec![], host_import:None,
            }, ty:target.clone(), span:span() });
            body.expressions[7].kind = CoreKind::Call { mandatory_tail:false, callee, arguments,
                invocation:crate::core::CoreCallContract { declaration:target, effects:EffectRow::empty() },
                reference_contract:crate::core::CallReferenceOrigin::None, reference_origin:crate::core::CallReferenceOrigin::None,
                reference_shape:crate::core::CallReferenceShape::None };
            let uses = checked_uses(&body);
            assert!(uses.callable_escapes.iter().any(|fact| fact.name == "first" && fact.boundary == CallableEscapeBoundary::Argument), "{uses:#?}");
            assert!(!uses.callable_escapes.iter().any(|fact| fact.name == "second"), "{uses:#?}");
            assert!(uses.diagnostics.iter().any(|diagnostic| diagnostic.code == "G5013"), "{uses:#?}");
        }
    }

    #[test]
    fn later_operation_payloads_cannot_replace_an_evaluated_capability() {
        let mut body = receiver_replacement_body();
        body.expressions[7].kind = CoreKind::Perform {
            effect:crate::EffectInstance { definition:crate::DefKey(crate::Digest::of_bytes(b"snapshot-effect")), arguments:vec![] },
            operation:0, operation_arguments:vec![], payload_types:vec![callable(Quantity::AFFINE), Type::Scalar(crate::ScalarType::I64)],
            arguments:vec![CoreId(2), CoreId(6)], terminal:false,
            reference_contract:crate::core::CallReferenceOrigin::None, reference_origin:crate::core::CallReferenceOrigin::None,
            reference_shape:crate::core::CallReferenceShape::None,
        };
        let uses = checked_uses(&body);
        assert!(uses.callable_escapes.iter().any(|fact| fact.name == "first"), "{uses:#?}");
        assert!(!uses.callable_escapes.iter().any(|fact| fact.name == "second"), "{uses:#?}");
        assert!(uses.diagnostics.iter().any(|diagnostic| diagnostic.code == "G5013"), "{uses:#?}");
    }

    #[test]
    fn resumption_transport_is_not_callable_type_evidence_and_binds_its_body() {
        let ty = callable(Quantity::UNRESTRICTED);
        let mut body = TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(), unsafe_implementations: Default::default(),
            body_regions: Default::default(),
            parameters: vec![("task".into(), ty.clone())],
            expressions: vec![CoreExpr { kind: CoreKind::Local("task".into()), ty, span: span() }],
            root: CoreId(0), diagnostics: vec![], recovered: false,
        };
        let mut flow = PlaceFlow::analyze(&body);
        let uses = UseFlow::analyze(&body, &flow);
        assert!(uses.diagnostics.is_empty(), "{uses:?}");
        let product = uses.resumption_transfers.unwrap();
        assert!(!product.retains(CoreId(0)));
        flow.install_resumption_transfers(product.clone()).unwrap();
        body.parameters[0].0 = "changed".into();
        body.expressions[0].kind = CoreKind::Local("changed".into());
        let mut changed = PlaceFlow::analyze(&body);
        assert!(changed.install_resumption_transfers(product).is_err());
    }

    #[test]
    fn forged_move_capture_retains_its_obligation_through_unrestricted_replay() {
        let function = callable(Quantity::ONCE);
        let closure = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation: Quantity::UNRESTRICTED,
        };
        let body = TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            body_regions: Default::default(),
            parameters: vec![("function".into(), function.clone())],
            expressions: vec![
                CoreExpr {
                    kind: CoreKind::Local("function".into()),
                    ty: function.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("41".into()),
                    ty: Type::Scalar(crate::types::ScalarType::I64),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Call {
                        mandatory_tail: false,
                        callee: CoreId(0),
                        arguments: vec![CoreId(1)],
                        invocation: crate::core::CoreCallContract { declaration: function.clone(), effects: EffectRow::empty() },
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
                        reference_shape: crate::core::CallReferenceShape::None,
                    },
                    ty: Type::Scalar(crate::types::ScalarType::I64),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Closure {
                        callable: CallableId(0),
                        parameters: vec![],
                        environment: crate::core::CaptureEnvironment {
                            brand: crate::core::EnvironmentBrand {
                                owner: crate::DefKey(crate::Digest::of_bytes(b"useflow-test")),
                                callable: CallableId(0),
                            },
                            captures: vec![ClosureCapture {
                                name: "function".into(),
                                mode: CaptureMode::Move,
                                ty: function.clone(),
                            }],
                            post_states: vec![crate::core::CapturePostState {
                                name: "function".into(),
                                mode: CaptureMode::Move,
                            }],
                            runs_in: crate::core::RunsInEvidence {
                                environment: crate::core::EnvironmentBrand {
                                    owner: crate::DefKey(crate::Digest::of_bytes(b"useflow-test")),
                                    callable: CallableId(0),
                                },
                                callable: CallableId(0),
                                effects: EffectRow::empty(),
                                post_states: vec![crate::core::CapturePostState {
                                    name: "function".into(),
                                    mode: CaptureMode::Move,
                                }],
                                sealed: true,
                            },
                            sealed: true,
                        },
                        body: CoreId(2),
                    },
                    ty: closure.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Call {
                        mandatory_tail: false,
                        callee: CoreId(3),
                        arguments: vec![],
                        invocation: crate::core::CoreCallContract { declaration: closure.clone(), effects: EffectRow::empty() },
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
                        reference_shape: crate::core::CallReferenceShape::None,
                    },
                    ty: Type::Scalar(crate::types::ScalarType::I64),
                    span: span(),
                },
            ],
            root: CoreId(4),
            diagnostics: vec![],
            recovered: false,
        };
        let ownership = PlaceFlow::analyze(&body);
        assert!(ownership.diagnostics.is_empty(), "{ownership:#?}");
        let uses = UseFlow::analyze(&body, &ownership);
        assert!(
            uses.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5011"),
            "unrestricted replay lost a forged move-captured exact callable: {uses:#?}"
        );
        assert_eq!(uses.callable_uses[0].actual.upper, None);
    }

    #[test]
    fn frozen_core_cannot_split_one_exact_callable_obligation_across_two_escapes() {
        let callback = callable(Quantity::ONCE);
        let apply = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![
                callback.clone(),
                Type::Scalar(crate::types::ScalarType::I64),
            ],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation: Quantity::UNRESTRICTED,
        };
        let i64 = Type::Scalar(crate::types::ScalarType::I64);
        let call = |callee, callback, value| CoreExpr {
            kind: CoreKind::Call {
                mandatory_tail: false,
                callee,
                arguments: vec![callback, value],
                invocation: crate::core::CoreCallContract { declaration: apply.clone(), effects: EffectRow::empty() },
                reference_contract: crate::core::CallReferenceOrigin::None,
                reference_origin: crate::core::CallReferenceOrigin::None,
                reference_shape: crate::core::CallReferenceShape::None,
            },
            ty: i64.clone(),
            span: span(),
        };
        // This is deliberately constructed Core rather than parsed source:
        // it exercises the frozen Core → PlaceFlow → UseFlow boundary that a
        // cache or embedding host could otherwise try to bypass.
        let body = TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            body_regions: Default::default(),
            parameters: vec![("callback".into(), callback.clone())],
            expressions: vec![
                CoreExpr {
                    kind: CoreKind::Function {
                        definition: crate::DefKey(crate::Digest::of_bytes(b"apply")),
                        arguments: vec![],
                        host_import: None,
                    },
                    ty: apply.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("20".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                call(CoreId(0), CoreId(1), CoreId(2)),
                CoreExpr {
                    kind: CoreKind::Function {
                        definition: crate::DefKey(crate::Digest::of_bytes(b"apply")),
                        arguments: vec![],
                        host_import: None,
                    },
                    ty: apply.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback,
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("21".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                call(CoreId(4), CoreId(5), CoreId(6)),
                CoreExpr {
                    kind: CoreKind::IntrinsicCall {
                        operator: "+".into(),
                        arguments: vec![CoreId(3), CoreId(7)],
                    },
                    ty: i64,
                    span: span(),
                },
            ],
            root: CoreId(8),
            diagnostics: vec![],
            recovered: false,
        };
        assert!(
            body.validate().is_empty(),
            "forged Core must still be valid"
        );
        let ownership = PlaceFlow::analyze(&body);
        assert!(ownership.diagnostics.is_empty(), "{ownership:#?}");
        let uses = UseFlow::analyze(&body, &ownership);
        assert!(
            uses.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5013"),
            "two outgoing transfers must consume one combined owner budget: {uses:#?}"
        );
    }

    #[test]
    fn frozen_core_joins_alternative_callable_transfers_without_sequencing_them() {
        let callback = callable(Quantity::ONCE);
        let apply = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![
                callback.clone(),
                Type::Scalar(crate::types::ScalarType::I64),
            ],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation: Quantity::UNRESTRICTED,
        };
        let i64 = Type::Scalar(crate::types::ScalarType::I64);
        let bool = Type::Scalar(crate::types::ScalarType::Bool);
        let call = |callee, callback, value| CoreExpr {
            kind: CoreKind::Call {
                mandatory_tail: false,
                callee,
                arguments: vec![callback, value],
                invocation: crate::core::CoreCallContract { declaration: apply.clone(), effects: EffectRow::empty() },
                reference_contract: crate::core::CallReferenceOrigin::None,
                reference_origin: crate::core::CallReferenceOrigin::None,
                reference_shape: crate::core::CallReferenceShape::None,
            },
            ty: i64.clone(),
            span: span(),
        };
        // This valid frozen Core bypasses source elaboration. Its two call
        // transfers are selected by distinct completion arms, so an exact
        // callback must retain the one-use interval rather than become [2,2].
        let body = TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            body_regions: Default::default(),
            parameters: vec![("callback".into(), callback.clone())],
            expressions: vec![
                CoreExpr {
                    kind: CoreKind::Function {
                        definition: crate::DefKey(crate::Digest::of_bytes(b"apply-left")),
                        arguments: vec![],
                        host_import: None,
                    },
                    ty: apply.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("20".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                call(CoreId(0), CoreId(1), CoreId(2)),
                CoreExpr {
                    kind: CoreKind::Function {
                        definition: crate::DefKey(crate::Digest::of_bytes(b"apply-right")),
                        arguments: vec![],
                        host_import: None,
                    },
                    ty: apply.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback,
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("21".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                call(CoreId(4), CoreId(5), CoreId(6)),
                CoreExpr {
                    kind: CoreKind::Literal("true".into()),
                    ty: bool,
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Completion {
                        refinement_test: None,
                        computation: CoreId(8),
                        handles_operations: false,
                        clauses: vec![
                            CoreCompletionClause {
                                pattern: CorePattern::Literal("true".into()),
                                bindings: vec![],
                                refinement: None,
                                body: CoreId(3),
                                span: span(),
                            },
                            CoreCompletionClause {
                                pattern: CorePattern::Literal("false".into()),
                                bindings: vec![],
                                refinement: None,
                                body: CoreId(7),
                                span: span(),
                            },
                        ],
                    },
                    ty: i64,
                    span: span(),
                },
            ],
            root: CoreId(9),
            diagnostics: vec![],
            recovered: false,
        };
        assert!(
            body.validate().is_empty(),
            "forged Core must still be valid"
        );
        let ownership = PlaceFlow::analyze(&body);
        assert!(ownership.diagnostics.is_empty(), "{ownership:#?}");
        let uses = UseFlow::analyze(&body, &ownership);
        assert!(
            uses.diagnostics.is_empty(),
            "alternative callable transfers must join as one use: {uses:#?}"
        );
    }

    #[test]
    fn frozen_core_cannot_add_direct_use_to_an_outgoing_callable_transfer() {
        let callback = callable(Quantity::ONCE);
        let apply = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![
                callback.clone(),
                Type::Scalar(crate::types::ScalarType::I64),
            ],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation: Quantity::UNRESTRICTED,
        };
        let i64 = Type::Scalar(crate::types::ScalarType::I64);
        let body = TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            body_regions: Default::default(),
            parameters: vec![("callback".into(), callback.clone())],
            expressions: vec![
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("20".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Call {
                        mandatory_tail: false,
                        callee: CoreId(0),
                        arguments: vec![CoreId(1)],
                        invocation: crate::core::CoreCallContract { declaration: callback.clone(), effects: EffectRow::empty() },
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
                        reference_shape: crate::core::CallReferenceShape::None,
                    },
                    ty: i64.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Function {
                        definition: crate::DefKey(crate::Digest::of_bytes(b"apply")),
                        arguments: vec![],
                        host_import: None,
                    },
                    ty: apply.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Local("callback".into()),
                    ty: callback,
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Literal("21".into()),
                    ty: i64.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Call {
                        mandatory_tail: false,
                        callee: CoreId(3),
                        arguments: vec![CoreId(4), CoreId(5)],
                        invocation: crate::core::CoreCallContract { declaration: apply.clone(), effects: EffectRow::empty() },
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
                        reference_shape: crate::core::CallReferenceShape::None,
                    },
                    ty: i64.clone(),
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::IntrinsicCall {
                        operator: "+".into(),
                        arguments: vec![CoreId(2), CoreId(6)],
                    },
                    ty: i64,
                    span: span(),
                },
            ],
            root: CoreId(7),
            diagnostics: vec![],
            recovered: false,
        };
        assert!(
            body.validate().is_empty(),
            "forged Core must still be valid"
        );
        let ownership = PlaceFlow::analyze(&body);
        assert!(ownership.diagnostics.is_empty(), "{ownership:#?}");
        let uses = UseFlow::analyze(&body, &ownership);
        assert!(
            uses.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5013"),
            "direct invocation and outgoing transfer must consume one owner budget: {uses:#?}"
        );
    }
}
