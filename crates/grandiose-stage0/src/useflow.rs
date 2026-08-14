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
        CallableId, CoreHandlerClause, CoreHandlerResumption, CoreId, CoreKind, CorePattern,
        CorePlace, TypedBody,
    },
    placeflow::{FlowEventKind, MoveFact, PlaceFlow},
    quantity::{Quantity, QuantityError},
    source::Span,
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

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
    pub callable_uses: Vec<CallableUseFact>,
    pub callable_escapes: Vec<CallableEscapeFact>,
    pub value_obligations: Vec<ValueUseFact>,
    pub diagnostics: Vec<UseDiagnostic>,
}

impl UseFlow {
    /// Analyze only ownership-valid Core.  Keeping `PlaceFlow` in the input
    /// makes the ordering explicit: a moved or conflicting-borrow path is not
    /// a valid witness for a quantitative callable contract, and reporting a
    /// second use error for it would be misleading.
    pub fn analyze(body: &TypedBody, ownership: &PlaceFlow) -> Self {
        if !ownership.diagnostics.is_empty() {
            return Self::default();
        }
        let mut analyzer = Analyzer {
            body,
            ownership,
            next_key: 0,
            contracts: BTreeMap::new(),
            facts: BTreeMap::new(),
            projected_contracts: BTreeMap::new(),
            escapes: BTreeMap::new(),
            escaped_closures: BTreeSet::new(),
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
        let required = callable_invocation(&body.expression(body.root).ty);
        analyzer.escape_value(
            body.root,
            &environment,
            required,
            CallableEscapeBoundary::Result,
        );
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
        CorePattern::Record { fields, .. } => fields
            .iter()
            .all(|field| core_pattern_is_irrefutable(&field.pattern)),
        CorePattern::Literal(_) | CorePattern::Enum { .. } | CorePattern::Error => false,
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
            CoreKind::Let { name, value } => {
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
    callable: CallableId,
    body: CoreId,
    captures: BTreeMap<String, Binding>,
    parameters: Vec<(String, Type)>,
    invocation: Quantity,
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

struct Analyzer<'a> {
    body: &'a TypedBody,
    ownership: &'a PlaceFlow,
    next_key: u32,
    contracts: BTreeMap<ContractKey, Contract>,
    facts: BTreeMap<ContractKey, Quantity>,
    /// Callable leaves reached through a parameter/opaque aggregate are
    /// discovered from PlaceFlow's canonical projection rather than inferred
    /// from the aggregate's source spelling.  One place owns one contract
    /// across direct calls, moves, branches, and closure bodies.
    projected_contracts: BTreeMap<MoveFact, ContractKey>,
    escapes: BTreeMap<ContractKey, Vec<Escape>>,
    escaped_closures: BTreeSet<CallableId>,
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
            CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => Summary::default(),
            CoreKind::Closure {
                environment: capture_environment,
                ..
            } => {
                // PlaceFlow supplies the canonical captured root.  The
                // environment supplies only the obligation carried by that
                // root, so this records capture transfer without rebuilding
                // a source projection in UseFlow.
                for capture in capture_environment.captures {
                    let binding = environment
                        .bindings
                        .get(&capture.name)
                        .cloned()
                        .unwrap_or(Binding::Other);
                    if let Some(place) = self.closure_place_fact(
                        expression.span,
                        &capture.name,
                        matches!(capture.mode, crate::core::CaptureMode::Move),
                    ) {
                        match capture.mode {
                            crate::core::CaptureMode::Move => {
                                self.record_transfer(&binding, place, expression.span);
                                environment.bindings.insert(capture.name, Binding::Other);
                            }
                            crate::core::CaptureMode::SharedBorrow
                            | crate::core::CaptureMode::UniqueBorrow => {
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
            CoreKind::Let { name, value } => {
                let summary = self.expression(value, environment);
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
                // Assignment stores a capability beyond this expression's
                // direct invocation site. Until place summaries model the
                // destination's exact callable contract, treat it as an
                // opaque transfer rather than silently dropping a must-use
                // obligation.
                let replacement = self.binding_for_value(value, environment);
                if let Some(place_fact) = self.assignment_place_fact(expression.span) {
                    let previous =
                        self.binding_at_place(&place, &place_fact, expression.span, environment);
                    self.record_overwrite(&previous, place_fact, expression.span);
                }
                self.assign_binding(&place, replacement, environment);
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
            | CoreKind::Unary { value, .. }
            | CoreKind::Field { base: value, .. }
            | CoreKind::PatternTest { subject: value, .. } => self.expression(value, environment),
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
                self.sequence(values, environment, expression.span)
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                self.sequence(fields, environment, expression.span)
            }
            CoreKind::Binary { left, right, .. } => {
                self.sequence(vec![left, right], environment, expression.span)
            }
            CoreKind::Perform { arguments, .. } => {
                self.sequence(arguments, environment, expression.span)
            }
            CoreKind::Call {
                callee, arguments, ..
            } => self.call(callee, arguments, environment, expression.span),
            CoreKind::Handle {
                computation,
                clauses,
            } => {
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
                let mut replay_escape_checkpoint = None;
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
                        replay_escape_checkpoint = Some(self.escape_checkpoint());
                        replay_residual = Some(self.sequence(
                            split.residual,
                            &mut residual_environment,
                            expression.span,
                        ));
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
                // The residual is walked once to derive its local use
                // summary, but outgoing callback transfers belong to each
                // selected resumption.  Detach those transfers now and add
                // them back with the arm's replay multiplicity below.
                let replay_escapes = replay_escape_checkpoint
                    .as_ref()
                    .map(|checkpoint| self.take_escapes_since(checkpoint));
                let mut arms = None::<Summary>;
                for clause in clauses {
                    let mut arm_environment = incoming.clone();
                    for (name, _) in &clause.bindings {
                        arm_environment
                            .bindings
                            .insert(name.clone(), Binding::Other);
                    }
                    let continuation_key = match &clause.resumption {
                        CoreHandlerResumption::Explicit { name, quantity } => {
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
                    if let Some(key) = continuation_key {
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
                            if let Some(escapes) = &replay_escapes {
                                self.record_scaled_escapes(escapes, actual);
                            }
                        }
                    }
                    arms = Some(match arms {
                        Some(previous) => previous.branch_hull(arm),
                        None => arm,
                    });
                }
                self.compose(expression.span, computation, arms.unwrap_or_default())
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                let computation = self.expression(computation, environment);
                let incoming = environment.clone();
                let mut arms = None::<Summary>;
                for clause in clauses {
                    let mut arm_environment = incoming.clone();
                    for (name, _) in &clause.bindings {
                        arm_environment
                            .bindings
                            .insert(name.clone(), Binding::Other);
                    }
                    let arm = self.expression(clause.body, &mut arm_environment);
                    arms = Some(match arms {
                        Some(previous) => previous.branch_hull(arm),
                        None => arm,
                    });
                }
                self.compose(expression.span, computation, arms.unwrap_or_default())
            }
        }
    }

    fn sequence<I>(&mut self, values: I, environment: &mut Environment, span: Span) -> Summary
    where
        I: IntoIterator<Item = CoreId>,
    {
        values
            .into_iter()
            .fold(Summary::default(), |summary, value| {
                let next = self.expression(value, environment);
                self.compose(span, summary, next)
            })
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

    fn call(
        &mut self,
        callee: CoreId,
        arguments: Vec<CoreId>,
        environment: &mut Environment,
        span: Span,
    ) -> Summary {
        // Evaluating a callee value does not execute its closure body. Its
        // captures execute only below after direct invocation is known.
        let mut summary = self.expression(callee, environment);
        let evaluated_arguments = self.sequence(arguments.clone(), environment, span);
        summary = self.compose(span, summary, evaluated_arguments);
        match self.binding_for_value(callee, environment) {
            Binding::Contract(key) => {
                self.escape_arguments(callee, &arguments, environment);
                self.compose(span, summary, Summary::one(key))
            }
            Binding::Closure(closure) => {
                let escapes_before = self.escape_checkpoint();
                let mut closure_environment = Environment {
                    bindings: closure.captures.clone(),
                };
                for (index, (name, ty)) in closure.parameters.iter().enumerate() {
                    // Preserve the caller's contract identity when a local
                    // capability is passed through a closure. Creating a
                    // fresh parameter contract here would lose the caller's
                    // lower-bound obligation and undercount captures.
                    let binding = arguments
                        .get(index)
                        .map(|argument| self.binding_for_value(*argument, environment))
                        .filter(|binding| {
                            matches!(binding, Binding::Contract(_) | Binding::Closure(_))
                        })
                        .unwrap_or_else(|| {
                            callable_invocation(ty)
                                .map(|quantity| {
                                    Binding::Contract(self.contract(
                                        &format!("{name}@closure{}", closure.callable.0),
                                        quantity,
                                        span,
                                        false,
                                    ))
                                })
                                .unwrap_or(Binding::Other)
                        });
                    closure_environment.bindings.insert(name.clone(), binding);
                }
                let body = self.expression(closure.body, &mut closure_environment);
                let escapes = self.take_escapes_since(&escapes_before);
                self.record_scaled_escapes(&escapes, closure.invocation);
                // A contextual closure can carry a finite, optional, or
                // widened invocation interval from its expected callable
                // type.  Replaying it multiplies every captured obligation.
                let body = self.repeat(span, body, closure.invocation);
                self.compose(span, summary, body)
            }
            Binding::Aggregate(_) | Binding::GlobalCallable | Binding::Other => {
                self.escape_arguments(callee, &arguments, environment);
                summary
            }
        }
    }

    fn binding_for_value(&mut self, id: CoreId, environment: &Environment) -> Binding {
        self.binding_for_value_at_place(id, environment, None)
    }

    fn binding_for_value_at_place(
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
                    _ => Binding::Other,
                }
            }
            CoreKind::Tuple(values)
            | CoreKind::Array(values)
            | CoreKind::Record { fields: values, .. }
            | CoreKind::Enum { fields: values, .. } => Binding::Aggregate(
                values
                    .iter()
                    .enumerate()
                    .map(|(index, value)| {
                        (index as u32, self.binding_for_value(*value, environment))
                    })
                    .collect(),
            ),
            CoreKind::Move(value) => self.binding_for_value_at_place(
                *value,
                environment,
                self.move_place_fact(expression.span),
            ),
            CoreKind::Closure {
                callable,
                parameters,
                environment: closure_environment,
                body,
            } => {
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
                    callable: *callable,
                    body: *body,
                    captures,
                    parameters: parameters.clone(),
                    invocation: callable_invocation(&expression.ty).unwrap_or(Quantity::ONCE),
                })
            }
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
            _ => Binding::Other,
        }
    }

    fn callable_parameters(&self, callee: CoreId) -> Vec<Option<Quantity>> {
        match &self.body.expression(callee).ty {
            Type::Callable { parameters, .. } => {
                parameters.iter().map(callable_invocation).collect()
            }
            _ => vec![],
        }
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

    fn closure_place_fact(&self, span: Span, root: &str, moved: bool) -> Option<MoveFact> {
        self.ownership.events.iter().find_map(|event| {
            let matches_kind = matches!(
                (&event.kind, moved),
                (FlowEventKind::Move(name), true)
                    | (FlowEventKind::BorrowShared(name), false)
                    | (FlowEventKind::BorrowUnique(name), false)
                    if name == root
            );
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

    fn assign_binding(
        &mut self,
        place: &CorePlace,
        replacement: Binding,
        environment: &mut Environment,
    ) {
        match place {
            CorePlace::Local { name, .. } => {
                environment.bindings.insert(name.clone(), replacement);
            }
            CorePlace::Field { base, index, .. } => {
                let mut aggregate = self.existing_binding_at_place(base, environment);
                if let Binding::Aggregate(fields) = &mut aggregate {
                    fields.insert(*index, replacement);
                    self.assign_binding(base, aggregate, environment);
                }
            }
            CorePlace::Deref { .. } => {}
            CorePlace::Error => {}
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
        arguments: &[CoreId],
        environment: &Environment,
    ) {
        let parameter_capabilities = self.callable_parameters(callee);
        for (index, argument) in arguments.iter().enumerate() {
            self.escape_value(
                *argument,
                environment,
                parameter_capabilities.get(index).copied().flatten(),
                CallableEscapeBoundary::Argument,
            );
        }
    }

    fn escape_contract(
        &mut self,
        key: ContractKey,
        required: Option<Quantity>,
        span: Span,
        boundary: CallableEscapeBoundary,
    ) {
        self.escapes.entry(key).or_default().push(Escape {
            required,
            span,
            boundary,
            actual: Quantity::ONCE,
        });
    }

    fn escape_checkpoint(&self) -> BTreeMap<ContractKey, usize> {
        self.escapes
            .iter()
            .map(|(key, escapes)| (*key, escapes.len()))
            .collect()
    }

    /// Extract transfers produced while evaluating one structural fragment.
    /// The caller can then replay them with the same quantity algebra as the
    /// fragment's local callable-use summary.
    fn take_escapes_since(
        &mut self,
        checkpoint: &BTreeMap<ContractKey, usize>,
    ) -> Vec<(ContractKey, Escape)> {
        let keys = self.escapes.keys().copied().collect::<Vec<_>>();
        let mut extracted = Vec::new();
        for key in keys {
            let start = checkpoint.get(&key).copied().unwrap_or(0);
            let Some(escapes) = self.escapes.get_mut(&key) else {
                continue;
            };
            if start < escapes.len() {
                extracted.extend(escapes.drain(start..).map(|escape| (key, escape)));
            }
        }
        self.escapes.retain(|_, escapes| !escapes.is_empty());
        extracted
    }

    fn record_scaled_escapes(&mut self, escapes: &[(ContractKey, Escape)], multiplier: Quantity) {
        for (key, escape) in escapes {
            let actual = match escape.actual.multiply(multiplier) {
                Ok(actual) => actual,
                Err(QuantityError::Overflow) => {
                    self.error(
                        escape.span,
                        "G5010",
                        "quantitative callable escape count overflowed",
                    );
                    continue;
                }
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity products are never empty")
                }
            };
            self.escapes.entry(*key).or_default().push(Escape {
                required: escape.required,
                span: escape.span,
                boundary: escape.boundary,
                actual,
            });
        }
    }

    fn escape_closure(&mut self, closure: ClosureValue, span: Span) {
        if !self.escaped_closures.insert(closure.callable) {
            return;
        }
        let mut environment = Environment {
            bindings: closure.captures,
        };
        // Arguments belong to the receiver of the escaped closure. They are
        // not body-local obligations of the enclosing declaration.
        for (name, _) in closure.parameters {
            environment.bindings.insert(name, Binding::Other);
        }
        let escapes_before = self.escape_checkpoint();
        let summary = self.expression(closure.body, &mut environment);
        let escapes = self.take_escapes_since(&escapes_before);
        self.record_scaled_escapes(&escapes, closure.invocation);
        let summary = self.repeat(span, summary, closure.invocation);
        self.record(summary);
    }

    fn escape_value(
        &mut self,
        id: CoreId,
        environment: &Environment,
        required: Option<Quantity>,
        boundary: CallableEscapeBoundary,
    ) {
        match self.binding_for_value(id, environment) {
            Binding::Contract(key) => {
                self.escape_contract(key, required, self.body.expression(id).span, boundary)
            }
            Binding::Closure(closure) => {
                self.escape_closure(closure, self.body.expression(id).span)
            }
            Binding::Aggregate(fields) => {
                for binding in fields.values() {
                    self.escape_binding(binding, required, self.body.expression(id).span, boundary);
                }
            }
            Binding::GlobalCallable | Binding::Other => match &self.body.expression(id).kind {
                CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
                    for value in values {
                        self.escape_value(*value, environment, None, boundary);
                    }
                }
                CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                    for value in fields {
                        self.escape_value(*value, environment, None, boundary);
                    }
                }
                _ => {}
            },
        }
    }

    fn escape_binding(
        &mut self,
        binding: &Binding,
        required: Option<Quantity>,
        span: Span,
        boundary: CallableEscapeBoundary,
    ) {
        match binding {
            Binding::Contract(key) => self.escape_contract(*key, required, span, boundary),
            Binding::Closure(closure) => self.escape_closure(closure.clone(), span),
            Binding::Aggregate(fields) => {
                for binding in fields.values() {
                    self.escape_binding(binding, required, span, boundary);
                }
            }
            Binding::GlobalCallable | Binding::Other => {}
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

        let escapes = self.escapes.get(&key).cloned().unwrap_or_default();
        if escapes.is_empty() {
            if contract.declared.contains(actual) {
                return;
            }
            self.contract_error(&contract, actual, "G5011");
            return;
        }

        // A local use interval and each outgoing callable capability are
        // separate declarative obligations. The receiver's callable type
        // must be admitted by the source contract, and the local prefix may
        // not already exceed the source upper bound. Lower bounds are then
        // discharged by the typed receiver rather than silently forgotten.
        if !upper_within(actual.upper, contract.declared.upper) {
            self.contract_error(&contract, actual, "G5011");
        }
        for escape in escapes {
            let Some(required) = escape.required else {
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
            };
            let demanded = match required.multiply(escape.actual) {
                Ok(demanded) => demanded,
                Err(QuantityError::Overflow) => {
                    self.error(
                        escape.span,
                        "G5010",
                        "quantitative callable escape demand overflowed",
                    );
                    continue;
                }
                Err(QuantityError::EmptyInterval) => {
                    unreachable!("quantity products are never empty")
                }
            };
            if contract.declared.contains(demanded) {
                continue;
            }
            self.error(
                escape.span,
                "G5013",
                format!(
                    "callable `{}` escapes through {} [{}, {}] times with per-call requirement [{}, {}], exceeding its declared capability [{}, {}]",
                    contract.name,
                    display_boundary(escape.boundary),
                    escape.actual.lower,
                    display_upper(escape.actual.upper),
                    required.lower,
                    display_upper(required.upper),
                    contract.declared.lower,
                    display_upper(contract.declared.upper),
                ),
            );
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
    use crate::{
        core::{CaptureMode, ClosureCapture, CoreExpr},
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
        Type::Callable {
            lifetime_binders: 0,
            parameters: vec![Type::Scalar(crate::types::ScalarType::I64)],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation,
        }
    }

    #[test]
    fn widens_captured_uses_for_an_unrestricted_closure_invocation() {
        let function = callable(Quantity::ONCE);
        let closure = Type::Callable {
            lifetime_binders: 0,
            parameters: vec![],
            result: Box::new(Type::Scalar(crate::types::ScalarType::I64)),
            effects: EffectRow::empty(),
            invocation: Quantity::UNRESTRICTED,
        };
        let body = TypedBody {
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
                        callee: CoreId(0),
                        arguments: vec![CoreId(1)],
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
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
                                mode: CaptureMode::SharedBorrow,
                                ty: function.clone(),
                            }],
                            post_states: vec![crate::core::CapturePostState {
                                name: "function".into(),
                                mode: CaptureMode::SharedBorrow,
                            }],
                            sealed: true,
                        },
                        body: CoreId(2),
                    },
                    ty: closure,
                    span: span(),
                },
                CoreExpr {
                    kind: CoreKind::Call {
                        callee: CoreId(3),
                        arguments: vec![],
                        reference_contract: crate::core::CallReferenceOrigin::None,
                        reference_origin: crate::core::CallReferenceOrigin::None,
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
            "unrestricted closure replay did not widen its captured exact callable: {uses:#?}"
        );
        assert_eq!(uses.callable_uses[0].actual.upper, None);
    }
}
