//! Ownership facts derived solely from Typed Core before MIR lowering.

use crate::{
    core::{CaptureMode, CoreId, CoreKind, CorePlace, TypedBody},
    source::Span,
};
use std::collections::BTreeMap;

/// A statically-selected subplace of one local.  PlaceFlow deliberately keeps
/// dereferences out of this representation: their aliasing is not yet proven
/// precisely enough to make them disjoint.  Struct-field paths, on the other
/// hand, have stable Core indices and can safely participate in overlap tests.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Projection {
    root: String,
    fields: Vec<u32>,
}

impl Projection {
    fn overlaps(&self, other: &Self) -> bool {
        self.root == other.root
            && (self.fields.starts_with(&other.fields) || other.fields.starts_with(&self.fields))
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProjectionLoan {
    place: Projection,
    unique: bool,
}

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
            projection_loans: vec![],
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
    /// Loans of proper field projections.  Whole-local loans continue to use
    /// `LocalState`, preserving the compact public final-state summary.
    projection_loans: Vec<ProjectionLoan>,
    events: Vec<FlowEvent>,
    diagnostics: Vec<FlowDiagnostic>,
}
impl Analyzer<'_> {
    fn visit(&mut self, id: CoreId) {
        let e = self.body.expression(id).clone();
        match e.kind {
            CoreKind::Literal(_)
            | CoreKind::Function(_)
            | CoreKind::TraitMethod { .. }
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
            CoreKind::Local(_) => self.read_place(id, e.span),
            CoreKind::Let { name, value } => {
                self.visit(value);
                self.states.insert(name.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(name), e.span)
            }
            CoreKind::Assign { place, value } => {
                self.visit(value);
                self.assign_place(&place, e.span);
            }
            CoreKind::Move(v) => {
                self.visit(v);
                // A field is a place projection into its root local.  The
                // current flow domain does not retain per-field move paths,
                // so consuming a projection must conservatively consume the
                // owner too.  That preserves the essential ownership
                // invariant until partial-move states are represented.
                self.move_place(v, e.span)
            }
            CoreKind::Unary { value, .. } => self.visit(value),
            CoreKind::Borrow { unique, value } => {
                self.visit(value);
                // A field projection is still a borrow of storage owned by
                // its root local.  Until PlaceFlow has projection-disjoint
                // loans, retain a loan on that root rather than silently
                // treating `&record.field` as a borrow of a temporary value.
                // This is conservative, but prevents moving or overwriting
                // the enclosing record while a reference into it is live.
                self.borrow_place(value, unique, e.span)
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
                let incoming_loans = self.projection_loans.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    self.projection_loans = incoming_loans.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    if let crate::core::CoreHandlerResumption::Explicit { name, .. } =
                        clause.resumption
                    {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit(clause.body);
                    exits.push((self.states.clone(), self.projection_loans.clone()));
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(
                        &exits
                            .iter()
                            .map(|(states, _)| states.clone())
                            .collect::<Vec<_>>(),
                    );
                    self.projection_loans = join_handler_projection_loans(&exits, &incoming);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                self.visit(computation);
                let incoming = self.states.clone();
                let incoming_loans = self.projection_loans.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    self.projection_loans = incoming_loans.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit(clause.body);
                    exits.push((self.states.clone(), self.projection_loans.clone()));
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(
                        &exits
                            .iter()
                            .map(|(states, _)| states.clone())
                            .collect::<Vec<_>>(),
                    );
                    self.projection_loans = join_handler_projection_loans(&exits, &incoming);
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
            CoreKind::Field { .. } => self.read_place(id, e.span),
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
            Some(LocalState::UniquelyBorrowed) => self.error(
                s,
                "G5008",
                format!("cannot read uniquely borrowed local `{n}`"),
            ),
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

    fn projection(&self, id: CoreId) -> Option<Projection> {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => Some(Projection {
                root: name.clone(),
                fields: vec![],
            }),
            CoreKind::Field { base, index, .. } => {
                let mut projection = self.projection(*base)?;
                projection.fields.push(*index);
                Some(projection)
            }
            _ => None,
        }
    }

    fn place_projection(place: &CorePlace) -> Option<Projection> {
        match place {
            CorePlace::Local { name, .. } => Some(Projection {
                root: name.clone(),
                fields: vec![],
            }),
            CorePlace::Field { base, index, .. } => {
                let mut projection = Self::place_projection(base)?;
                projection.fields.push(*index);
                Some(projection)
            }
            CorePlace::Error => None,
        }
    }

    fn read_place(&mut self, id: CoreId, span: Span) {
        let Some(place) = self.projection(id) else {
            return;
        };
        self.read(&place.root, span);
        if self
            .projection_loans
            .iter()
            .any(|loan| loan.unique && loan.place.overlaps(&place))
        {
            self.error(
                span,
                "G5008",
                format!("cannot read uniquely borrowed place `{}`", place.root),
            );
        }
    }

    fn move_place(&mut self, id: CoreId, span: Span) {
        let Some(place) = self.projection(id) else {
            return;
        };
        if self
            .projection_loans
            .iter()
            .any(|loan| loan.place.overlaps(&place))
        {
            self.error(
                span,
                "G5004",
                format!("cannot move borrowed place `{}`", place.root),
            );
            return;
        }
        self.move_(&place.root, span);
    }

    fn borrow_place(&mut self, id: CoreId, unique: bool, span: Span) {
        let Some(place) = self.projection(id) else {
            return;
        };
        if self
            .projection_loans
            .iter()
            .any(|loan| loan.place.overlaps(&place) && (unique || loan.unique))
        {
            self.error(
                span,
                "G5006",
                format!("conflicting borrow of place `{}`", place.root),
            );
            return;
        }
        if place.fields.is_empty() {
            self.borrow(&place.root, unique, span);
            return;
        }
        match self.states.get(&place.root) {
            Some(LocalState::Initialized) | Some(LocalState::SharedBorrowed(_)) => {}
            Some(LocalState::Moved) => {
                self.error(
                    span,
                    "G5005",
                    format!("cannot borrow moved local `{}`", place.root),
                );
                return;
            }
            Some(LocalState::UniquelyBorrowed) => {
                self.error(
                    span,
                    "G5006",
                    format!("conflicting borrow of local `{}`", place.root),
                );
                return;
            }
            None => {
                self.error(
                    span,
                    "G5002",
                    format!("unknown local `{}` in PlaceFlow", place.root),
                );
                return;
            }
        }
        self.projection_loans.push(ProjectionLoan { place, unique });
        self.event(
            if unique {
                FlowEventKind::BorrowUnique(self.root_name(id))
            } else {
                FlowEventKind::BorrowShared(self.root_name(id))
            },
            span,
        );
    }

    fn assign_place(&mut self, place: &CorePlace, span: Span) {
        let Some(projection) = Self::place_projection(place) else {
            return;
        };
        if self
            .projection_loans
            .iter()
            .any(|loan| loan.place.overlaps(&projection))
        {
            self.error(
                span,
                "G5007",
                format!("cannot assign to borrowed place `{}`", projection.root),
            );
            return;
        }
        self.assign(&projection.root, span);
    }

    fn root_name(&self, id: CoreId) -> String {
        self.projection(id)
            .map(|place| place.root)
            .unwrap_or_default()
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

/// A handler arm is dynamically selected, so any projection loan established
/// on an outer local by one possible exit remains live after the handler.  We
/// retain only roots that existed before entering the handler: clause-local
/// references cannot escape their lexical arm merely because another arm uses
/// the same spelling.
fn join_handler_projection_loans(
    exits: &[(BTreeMap<String, LocalState>, Vec<ProjectionLoan>)],
    incoming: &BTreeMap<String, LocalState>,
) -> Vec<ProjectionLoan> {
    let mut loans = exits
        .iter()
        .flat_map(|(_, loans)| loans)
        .filter(|loan| incoming.contains_key(&loan.place.root))
        .cloned()
        .collect::<Vec<_>>();
    loans.sort();
    loans.dedup();
    loans
}
