//! Quantitative callable-use facts derived from Typed Core.
//!
//! `PlaceFlow` answers whether an evaluation is ownership-safe.  This pass
//! answers a distinct question once that ownership shape is known: how many
//! times can each *local callable capability* be invoked?  The representation
//! deliberately uses the same [`Quantity`] algebra as effect resumptions, so
//! ordinary calls, closure captures, and dynamically selected handler arms
//! compose at one semantic boundary before MIR.

use crate::{
    core::{CallableId, CoreHandlerResumption, CoreId, CoreKind, TypedBody},
    placeflow::PlaceFlow,
    quantity::{Quantity, QuantityError},
    source::Span,
    types::Type,
};
use std::collections::BTreeMap;

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

/// The result of quantitative-use analysis.  Facts are retained for tooling
/// and later ownership refinements even when a diagnostic prevents lowering.
#[derive(Clone, Debug, Default)]
pub struct UseFlow {
    pub callable_uses: Vec<CallableUseFact>,
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
            next_key: 0,
            contracts: BTreeMap::new(),
            facts: BTreeMap::new(),
            diagnostics: vec![],
        };
        let mut environment = Environment::default();
        for (name, ty) in &body.parameters {
            if let Some(invocation) = callable_invocation(ty) {
                let key =
                    analyzer.contract(name, invocation, body.expression(body.root).span, false);
                environment
                    .bindings
                    .insert(name.clone(), Binding::Contract(key));
            }
        }
        let summary = analyzer.expression(body.root, &mut environment);
        analyzer.record(summary);
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
}

#[derive(Clone, Debug)]
enum Binding {
    Contract(ContractKey),
    Closure(ClosureValue),
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
    next_key: u32,
    contracts: BTreeMap<ContractKey, Contract>,
    facts: BTreeMap<ContractKey, Quantity>,
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
            | CoreKind::Function(_)
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => Summary::default(),
            CoreKind::Closure { .. } => Summary::default(),
            CoreKind::Let { name, value } => {
                let summary = self.expression(value, environment);
                let binding = self.binding_for_value(value, environment);
                environment.bindings.insert(name, binding);
                summary
            }
            CoreKind::Assign { value, .. }
            | CoreKind::Borrow { value, .. }
            | CoreKind::Move(value)
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
            CoreKind::Call { callee, arguments } => {
                self.call(callee, arguments, environment, expression.span)
            }
            CoreKind::Handle {
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
                    let continuation_key = match &clause.resumption {
                        CoreHandlerResumption::Explicit { name, quantity } => {
                            let key = self.contract(name, *quantity, clause.span, true);
                            arm_environment
                                .bindings
                                .insert(name.clone(), Binding::Contract(key));
                            Some(key)
                        }
                        _ => None,
                    };
                    let arm = self.expression(clause.body, &mut arm_environment);
                    if let Some(key) = continuation_key {
                        let actual = arm.uses.get(&key).copied().unwrap_or(Quantity::ZERO);
                        self.check_contract(key, actual);
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
        let arguments = self.sequence(arguments, environment, span);
        summary = self.compose(span, summary, arguments);
        match self.binding_for_value(callee, environment) {
            Binding::Contract(key) => self.compose(span, summary, Summary::one(key)),
            Binding::Closure(closure) => {
                let mut closure_environment = Environment {
                    bindings: closure.captures.clone(),
                };
                for (name, ty) in &closure.parameters {
                    let binding = callable_invocation(ty)
                        .map(|quantity| {
                            Binding::Contract(self.contract(
                                &format!("{name}@closure{}", closure.callable.0),
                                quantity,
                                span,
                                false,
                            ))
                        })
                        .unwrap_or(Binding::Other);
                    closure_environment.bindings.insert(name.clone(), binding);
                }
                let body = self.expression(closure.body, &mut closure_environment);
                // Every direct call executes the closure body exactly once.
                let body = self.repeat(span, body, Quantity::ONCE);
                self.compose(span, summary, body)
            }
            Binding::GlobalCallable | Binding::Other => summary,
        }
    }

    fn binding_for_value(&mut self, id: CoreId, environment: &Environment) -> Binding {
        let expression = self.body.expression(id);
        match &expression.kind {
            CoreKind::Local(name) => environment
                .bindings
                .get(name)
                .cloned()
                .unwrap_or(Binding::Other),
            CoreKind::Function(_) | CoreKind::TraitMethod { .. } => Binding::GlobalCallable,
            CoreKind::Closure {
                callable,
                parameters,
                captures,
                body,
            } => {
                let captures = captures
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
                })
            }
            _ => Binding::Other,
        }
    }

    fn check_contract(&mut self, key: ContractKey, actual: Quantity) {
        let Some(contract) = self.contracts.get(&key).cloned() else {
            return;
        };
        // A callable parameter may be returned, stored in a closure, or
        // otherwise transferred to a later caller.  This intrabody pass has
        // no escape summary yet, so it can soundly reject only an excessive
        // upper bound for ordinary capabilities. A generated continuation is
        // frame-local and cannot escape Core, hence its full lower-and-upper
        // contract is enforceable here.
        if (contract.resumption && contract.declared.contains(actual))
            || (!contract.resumption && upper_within(actual.upper, contract.declared.upper))
        {
            return;
        }
        let subject = if contract.resumption {
            "handler continuation"
        } else {
            "callable"
        };
        self.error(
            contract.span,
            if contract.resumption {
                "G5012"
            } else {
                "G5011"
            },
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
        self.diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        UseFlow {
            callable_uses,
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
