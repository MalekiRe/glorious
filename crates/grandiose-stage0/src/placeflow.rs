//! Ownership facts derived solely from Typed Core before MIR lowering.

use crate::{
    core::{CaptureMode, CoreId, CoreKind, TypedBody},
    source::Span,
};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LocalState {
    Initialized,
    Moved,
    SharedBorrowed(u32),
    UniquelyBorrowed,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum FlowEventKind {
    Initialize(String),
    Read(String),
    Move(String),
    BorrowShared(String),
    BorrowUnique(String),
    Assign(String),
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowEvent {
    pub kind: FlowEventKind,
    pub span: Span,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FlowDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}
#[derive(Clone, Debug, Default)]
pub struct PlaceFlow {
    pub final_states: BTreeMap<String, LocalState>,
    pub events: Vec<FlowEvent>,
    pub diagnostics: Vec<FlowDiagnostic>,
}
impl PlaceFlow {
    pub fn analyze(body: &TypedBody) -> Self {
        let mut a = Analyzer {
            body,
            states: BTreeMap::new(),
            events: vec![],
            diagnostics: vec![],
        };
        for (name, _) in &body.parameters {
            a.states.insert(name.clone(), LocalState::Initialized);
        }
        a.visit(body.root);
        a.diagnostics.sort_by_key(|d| d.span.start);
        Self {
            final_states: a.states,
            events: a.events,
            diagnostics: a.diagnostics,
        }
    }
}
struct Analyzer<'a> {
    body: &'a TypedBody,
    states: BTreeMap<String, LocalState>,
    events: Vec<FlowEvent>,
    diagnostics: Vec<FlowDiagnostic>,
}
impl Analyzer<'_> {
    fn visit(&mut self, id: CoreId) {
        let e = self.body.expression(id).clone();
        match e.kind {
            CoreKind::Literal(_)
            | CoreKind::Function(_)
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
            CoreKind::Closure { captures, .. } => {
                for capture in captures {
                    match capture.mode {
                        CaptureMode::SharedBorrow => self.borrow(&capture.name, false, e.span),
                        CaptureMode::UniqueBorrow => self.borrow(&capture.name, true, e.span),
                        CaptureMode::Move => self.move_(&capture.name, e.span),
                    }
                }
            }
            CoreKind::Local(n) => self.read(&n, e.span),
            CoreKind::Let { name, value } => {
                self.visit(value);
                self.states.insert(name.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(name), e.span)
            }
            CoreKind::Assign { place, value } => {
                self.visit(value);
                if let Some((name, _)) = place.root_local() {
                    self.assign(name, e.span);
                }
            }
            CoreKind::Move(v) => {
                self.visit(v);
                if let CoreKind::Local(n) = &self.body.expression(v).kind {
                    self.move_(n, e.span)
                }
            }
            CoreKind::Unary { value, .. } => self.visit(value),
            CoreKind::Borrow { unique, value } => {
                self.visit(value);
                if let CoreKind::Local(n) = &self.body.expression(value).kind {
                    self.borrow(n, unique, e.span)
                }
            }
            CoreKind::Call { callee, arguments } => {
                self.visit(callee);
                for v in arguments {
                    self.visit(v)
                }
            }
            CoreKind::Perform { arguments, .. } => {
                for value in arguments {
                    self.visit(value)
                }
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.visit(computation);
                let incoming = self.states.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    if let crate::core::CoreHandlerResumption::Explicit { name, .. } =
                        clause.resumption
                    {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit(clause.body);
                    exits.push(self.states.clone());
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(&exits);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                self.visit(computation);
                let incoming = self.states.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit(clause.body);
                    exits.push(self.states.clone());
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(&exits);
                }
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) => {
                for value in values {
                    self.visit(value)
                }
            }
            CoreKind::Record { fields, .. } => {
                for field in fields {
                    self.visit(field)
                }
            }
            CoreKind::Enum { fields, .. } => {
                for field in fields {
                    self.visit(field)
                }
            }
            CoreKind::Field { base, .. } => self.visit(base),
            CoreKind::PatternTest { subject, .. } => self.visit(subject),
            CoreKind::Binary { left, right, .. } => {
                self.visit(left);
                self.visit(right)
            }
            CoreKind::Block(v) => {
                for x in v {
                    self.visit(x)
                }
            }
        }
    }
    fn read(&mut self, n: &str, s: Span) {
        match self.states.get(n) {
            Some(LocalState::Moved) => self.error(s, "G5001", format!("use of moved local `{n}`")),
            Some(_) => self.event(FlowEventKind::Read(n.into()), s),
            None => self.error(s, "G5002", format!("unknown local `{n}` in PlaceFlow")),
        }
    }
    fn move_(&mut self, n: &str, s: Span) {
        match self.states.get(n) {
            Some(LocalState::Initialized) => {
                self.states.insert(n.into(), LocalState::Moved);
                self.event(FlowEventKind::Move(n.into()), s)
            }
            Some(LocalState::Moved) => {
                self.error(s, "G5003", format!("local `{n}` is moved more than once"))
            }
            Some(_) => self.error(s, "G5004", format!("cannot move borrowed local `{n}`")),
            None => self.error(s, "G5002", format!("unknown local `{n}` in PlaceFlow")),
        }
    }
    fn borrow(&mut self, n: &str, u: bool, s: Span) {
        match (self.states.get(n).copied(), u) {
            (Some(LocalState::Initialized), true) => {
                self.states.insert(n.into(), LocalState::UniquelyBorrowed);
                self.event(FlowEventKind::BorrowUnique(n.into()), s)
            }
            (Some(LocalState::Initialized), false) => {
                self.states.insert(n.into(), LocalState::SharedBorrowed(1));
                self.event(FlowEventKind::BorrowShared(n.into()), s)
            }
            (Some(LocalState::SharedBorrowed(c)), false) => {
                self.states
                    .insert(n.into(), LocalState::SharedBorrowed(c + 1));
                self.event(FlowEventKind::BorrowShared(n.into()), s)
            }
            (Some(LocalState::Moved), _) => {
                self.error(s, "G5005", format!("cannot borrow moved local `{n}`"))
            }
            (Some(_), _) => self.error(s, "G5006", format!("conflicting borrow of local `{n}`")),
            (None, _) => self.error(s, "G5002", format!("unknown local `{n}` in PlaceFlow")),
        }
    }
    fn assign(&mut self, n: &str, s: Span) {
        match self.states.get(n).copied() {
            Some(LocalState::Initialized) | Some(LocalState::Moved) => {
                self.states.insert(n.into(), LocalState::Initialized);
                self.event(FlowEventKind::Assign(n.into()), s)
            }
            Some(LocalState::SharedBorrowed(_)) | Some(LocalState::UniquelyBorrowed) => {
                self.error(s, "G5007", format!("cannot assign to borrowed local `{n}`"))
            }
            None => self.error(s, "G5002", format!("unknown local `{n}` in PlaceFlow")),
        }
    }
    fn event(&mut self, kind: FlowEventKind, span: Span) {
        self.events.push(FlowEvent { kind, span })
    }
    fn error(&mut self, span: Span, code: &'static str, message: String) {
        self.diagnostics.push(FlowDiagnostic {
            code,
            span,
            message,
        })
    }
}

/// A handler arm is dynamically selected.  Until the full quantity analysis
/// records a path predicate, the post-handler state must be safe for every
/// arm: a value moved or uniquely borrowed on any exit cannot be treated as
/// freely available by code after the handler.
fn join_handler_exits(exits: &[BTreeMap<String, LocalState>]) -> BTreeMap<String, LocalState> {
    let mut names = BTreeMap::<String, Vec<LocalState>>::new();
    for exit in exits {
        for (name, state) in exit {
            names.entry(name.clone()).or_default().push(*state);
        }
    }
    names
        .into_iter()
        .filter_map(|(name, states)| {
            (states.len() == exits.len()).then(|| {
                let state = if states.contains(&LocalState::Moved) {
                    LocalState::Moved
                } else if states.contains(&LocalState::UniquelyBorrowed) {
                    LocalState::UniquelyBorrowed
                } else {
                    let shared = states
                        .iter()
                        .filter_map(|state| match state {
                            LocalState::SharedBorrowed(count) => Some(*count),
                            _ => None,
                        })
                        .max()
                        .unwrap_or(0);
                    if shared == 0 {
                        LocalState::Initialized
                    } else {
                        LocalState::SharedBorrowed(shared)
                    }
                };
                (name, state)
            })
        })
        .collect()
}
