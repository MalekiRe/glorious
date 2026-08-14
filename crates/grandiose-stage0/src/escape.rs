//! Lifetime escape and outlives validation over frozen Typed Core.
//!
//! [`crate::placeflow::PlaceFlow`] establishes when a loan is live inside a
//! body.  This pass answers the complementary boundary question: may a value
//! that still contains that loan leave the body (or cross a suspension
//! boundary)?  It deliberately works on Typed Core rather than source syntax,
//! so aliases, aggregates, closure environments, handler exits, and
//! completion exits all use the same provenance model.

use crate::{
    core::{CaptureMode, CoreId, CoreKind, CorePlace, TypedBody},
    placeflow::PlaceFlow,
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EscapeDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

/// Frozen diagnostics from the body-outlives boundary.
#[derive(Clone, Debug, Default)]
pub struct EscapeFlow {
    pub diagnostics: Vec<EscapeDiagnostic>,
}

impl EscapeFlow {
    /// Check returned values and suspension payloads. `flow` is intentionally
    /// an input to this phase: its NLL/reborrow facts establish that this is a
    /// post-loan boundary, rather than a second lexical borrow checker.
    pub fn analyze(body: &TypedBody, flow: &PlaceFlow) -> Self {
        let mut analyzer = Analyzer {
            body,
            // A direct borrow must already have entered the ownership flow.
            // Retaining these roots lets us fail closed if Core ever grows a
            // reference-producing operation without teaching PlaceFlow about
            // it first.
            loan_roots: flow
                .events
                .iter()
                .filter_map(|event| match &event.kind {
                    crate::placeflow::FlowEventKind::BorrowShared(root)
                    | crate::placeflow::FlowEventKind::BorrowUnique(root)
                    | crate::placeflow::FlowEventKind::Reborrow(root) => Some(root.clone()),
                    _ => None,
                })
                .collect(),
            values: BTreeMap::new(),
            diagnostics: vec![],
        };
        let root = analyzer.value(body.root);
        analyzer.report_return_escape(&root, body.expression(body.root).span);
        analyzer
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        analyzer.diagnostics.dedup_by(|left, right| {
            left.code == right.code && left.span == right.span && left.message == right.message
        });
        Self {
            diagnostics: analyzer.diagnostics,
        }
    }
}

/// Provenance that matters at an outlives boundary.  Scalars and normal
/// nominal values are omitted; only borrowed storage and closures that carry
/// one of those borrows can make a body-local region escape.
#[derive(Clone, Debug, Eq, PartialEq)]
enum Value {
    None,
    Borrowed { root: String },
    Aggregate(Vec<Value>),
    Closure(Vec<Capture>),
    Joined(Vec<Value>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum Capture {
    /// A reference value whose backing place is body-local.
    Borrowed { root: String },
}

struct Analyzer<'a> {
    body: &'a TypedBody,
    loan_roots: BTreeSet<String>,
    values: BTreeMap<String, Value>,
    diagnostics: Vec<EscapeDiagnostic>,
}

impl Analyzer<'_> {
    fn value(&mut self, id: CoreId) -> Value {
        let expression = self.body.expression(id).clone();
        match expression.kind {
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function(_)
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error
            | CoreKind::PatternTest { .. }
            | CoreKind::Unary { .. }
            | CoreKind::Binary { .. } => Value::None,
            CoreKind::Local(name) => self.values.get(&name).cloned().unwrap_or(Value::None),
            CoreKind::Borrow { value, .. } => self.borrowed_value(value),
            CoreKind::Move(value) => self.value(value),
            CoreKind::Tuple(values) | CoreKind::Array(values) => {
                Value::Aggregate(values.into_iter().map(|value| self.value(value)).collect())
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                Value::Aggregate(fields.into_iter().map(|value| self.value(value)).collect())
            }
            CoreKind::Field { base, index, .. } => match self.value(base) {
                Value::Aggregate(fields) => {
                    fields.get(index as usize).cloned().unwrap_or(Value::None)
                }
                Value::Joined(values) => Value::Joined(
                    values
                        .into_iter()
                        .map(|value| match value {
                            Value::Aggregate(fields) => {
                                fields.get(index as usize).cloned().unwrap_or(Value::None)
                            }
                            _ => Value::None,
                        })
                        .collect(),
                ),
                _ => Value::None,
            },
            CoreKind::Let { name, value } => {
                let value = self.value(value);
                self.values.insert(name, value);
                Value::None
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.value(body)
            }
            CoreKind::Assign { place, value } => {
                let value = self.value(value);
                self.assign(place, value);
                Value::None
            }
            CoreKind::Block(values) => {
                let mut result = Value::None;
                for value in values {
                    result = self.value(value);
                }
                result
            }
            CoreKind::Closure { environment, .. } => Value::Closure(
                environment
                    .captures
                    .into_iter()
                    .flat_map(|capture| match capture.mode {
                        CaptureMode::Move => Vec::new(),
                        CaptureMode::SharedBorrow | CaptureMode::UniqueBorrow => {
                            let value = self
                                .values
                                .get(&capture.name)
                                .cloned()
                                .unwrap_or(Value::None);
                            // Capturing a reference reborrows its backing
                            // place. Keep every exact root, not the local
                            // reference slot, for diagnostics.
                            borrowed_roots(&value)
                                .into_iter()
                                .map(|root| Capture::Borrowed { root })
                                .collect()
                        }
                    })
                    .collect(),
            ),
            CoreKind::Call { callee, arguments } => {
                // Calls are not escape boundaries by themselves: their
                // callable contract owns the outlives relationship. Still
                // visit all operands so nested `let` expressions retain their
                // value provenance for the surrounding body.
                self.value(callee);
                for argument in arguments {
                    self.value(argument);
                }
                Value::None
            }
            CoreKind::Perform { arguments, .. } => {
                for argument in arguments {
                    let value = self.value(argument);
                    self.report_suspension_escape(&value, expression.span);
                }
                Value::None
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                let computation = self.value(computation);
                let incoming = self.values.clone();
                // A handler may complete normally without selecting an
                // operation arm, so the computation is one of its dynamic
                // exits alongside every matching clause.
                let mut exits = vec![computation];
                for clause in clauses {
                    self.values = incoming.clone();
                    for (name, _) in clause.bindings {
                        self.values.remove(&name);
                    }
                    if let crate::core::CoreHandlerResumption::Explicit { name, .. } =
                        clause.resumption
                    {
                        self.values.remove(&name);
                    }
                    exits.push(self.value(clause.body));
                }
                self.values = incoming;
                join(exits)
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                let computation = self.value(computation);
                let incoming = self.values.clone();
                let mut exits = vec![computation];
                for clause in clauses {
                    self.values = incoming.clone();
                    for (name, _) in clause.bindings {
                        self.values.remove(&name);
                    }
                    exits.push(self.value(clause.body));
                }
                self.values = incoming;
                join(exits)
            }
        }
    }

    fn borrowed_value(&mut self, id: CoreId) -> Value {
        let Some(root) = self.place_root(id) else {
            self.error(
                self.body.expression(id).span,
                "G5013",
                "reference to a temporary cannot outlive the body that created it",
            );
            return Value::None;
        };
        // Every Core borrow of a stable place should have a matching
        // PlaceFlow event. Keep this fail-closed until a future region source
        // explicitly teaches both passes about a new kind of loan.
        if !self.loan_roots.contains(&root) {
            self.error(
                self.body.expression(id).span,
                "G5016",
                format!("reference to `{root}` has no frozen NLL loan fact"),
            );
        }
        Value::Borrowed { root }
    }

    fn place_root(&self, id: CoreId) -> Option<String> {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => Some(name.clone()),
            CoreKind::Field { base, .. } => self.place_root(*base),
            _ => None,
        }
    }

    fn assign(&mut self, place: CorePlace, value: Value) {
        match place {
            CorePlace::Local { name, .. } => {
                self.values.insert(name, value);
            }
            CorePlace::Field { base, index, .. } => {
                if let Some(name) = base.root_local().map(|(name, _)| name.to_owned())
                    && let Some(Value::Aggregate(fields)) = self.values.get_mut(&name)
                    && let Some(field) = fields.get_mut(index as usize)
                {
                    *field = value;
                }
            }
            CorePlace::Error => {}
        }
    }

    fn report_return_escape(&mut self, value: &Value, span: Span) {
        let mut emitted = BTreeSet::new();
        for root in borrowed_roots(value) {
            if emitted.insert(("reference", root.clone())) {
                self.error(
                    span,
                    "G5013",
                    format!(
                        "reference backed by body-local place `{root}` escapes the function result"
                    ),
                );
            }
        }
        for capture in closure_captures(value) {
            let (code, message) = match capture {
                Capture::Borrowed { root } => (
                    "G5014",
                    format!(
                        "escaping closure captures a reference backed by body-local place `{root}`"
                    ),
                ),
            };
            if emitted.insert(("closure", message.clone())) {
                self.error(span, code, message);
            }
        }
    }

    fn report_suspension_escape(&mut self, value: &Value, span: Span) {
        for root in borrowed_roots(value) {
            self.error(
                span,
                "G5015",
                format!("effect payload carries reference to body-local place `{root}` across a suspension boundary"),
            );
        }
        for Capture::Borrowed { root } in closure_captures(value) {
            self.error(
                span,
                "G5015",
                format!("effect payload carries closure borrowing body-local place `{root}` across a suspension boundary"),
            );
        }
    }

    fn error(&mut self, span: Span, code: &'static str, message: impl Into<String>) {
        self.diagnostics.push(EscapeDiagnostic {
            code,
            span,
            message: message.into(),
        });
    }
}

fn join(mut values: Vec<Value>) -> Value {
    match values.len() {
        0 => Value::None,
        1 => values.pop().expect("one value"),
        _ => Value::Joined(values),
    }
}

fn borrowed_roots(value: &Value) -> BTreeSet<String> {
    let mut roots = BTreeSet::new();
    collect_borrowed_roots(value, &mut roots);
    roots
}

fn collect_borrowed_roots(value: &Value, roots: &mut BTreeSet<String>) {
    match value {
        Value::Borrowed { root } => {
            roots.insert(root.clone());
        }
        Value::Aggregate(values) | Value::Joined(values) => {
            for value in values {
                collect_borrowed_roots(value, roots);
            }
        }
        Value::Closure(_) => {}
        Value::None => {}
    }
}

fn closure_captures(value: &Value) -> Vec<Capture> {
    let mut captures = vec![];
    collect_closure_captures(value, &mut captures);
    captures.sort_by_key(|capture| format!("{capture:?}"));
    captures.dedup();
    captures
}

fn collect_closure_captures(value: &Value, captures: &mut Vec<Capture>) {
    match value {
        Value::Closure(values) => captures.extend(values.clone()),
        Value::Aggregate(values) | Value::Joined(values) => {
            for value in values {
                collect_closure_captures(value, captures);
            }
        }
        Value::None | Value::Borrowed { .. } => {}
    }
}
