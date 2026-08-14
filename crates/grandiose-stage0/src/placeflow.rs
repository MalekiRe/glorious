//! Ownership facts derived solely from Typed Core before MIR lowering.

use crate::{
    core::{CaptureMode, CoreId, CoreKind, CorePlace, TypedBody},
    source::Span,
};
use std::collections::{BTreeMap, BTreeSet};

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
    /// The lexical reference binding that keeps this loan live. `None` is a
    /// conservative temporary/capture loan whose lifetime has not yet been
    /// made explicit in Typed Core.
    owner: Option<String>,
}

/// A frozen ownership fact for a loan that is still live at the body exit.
/// Unlike the compact [`LocalState`] summary this retains the exact projected
/// place and, when available, the reference local that owns its region.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LoanFact {
    pub owner: Option<String>,
    pub root: String,
    pub fields: Vec<u32>,
    pub unique: bool,
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
    /// A closure captured a reference local whose backing place is already
    /// loaned.  The capture must retain that backing loan for the callable
    /// environment; otherwise NLL would end the loan at the reference
    /// local's last syntactic use and permit the referent to be mutated or
    /// moved while the closure can still observe it.
    Reborrow(String),
    EndBorrow(String),
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
    pub active_loans: Vec<LoanFact>,
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
        a.visit_with_live_after(body.root, &BTreeSet::new());
        a.diagnostics.sort_by_key(|d| d.span.start);
        let active_loans = a
            .projection_loans
            .iter()
            .map(|loan| LoanFact {
                owner: loan.owner.clone(),
                root: loan.place.root.clone(),
                fields: loan.place.fields.clone(),
                unique: loan.unique,
            })
            .collect();
        Self {
            final_states: a.states,
            active_loans,
            events: a.events,
            diagnostics: a.diagnostics,
        }
    }
}
struct Analyzer<'a> {
    body: &'a TypedBody,
    states: BTreeMap<String, LocalState>,
    /// Every precise source loan, including a whole-local loan.  Whole-local
    /// entries are mirrored in `states` for the legacy compact summary.
    projection_loans: Vec<ProjectionLoan>,
    events: Vec<FlowEvent>,
    diagnostics: Vec<FlowDiagnostic>,
}
impl Analyzer<'_> {
    /// Visit an expression while retaining only loans whose owner may be used
    /// by the continuation.  This is the first NLL region domain: a `let r =
    /// &place` loan lasts to the last value use of `r`, rather than to body
    /// exit.  Dynamic handler exits receive the same continuation set and are
    /// joined conservatively below.
    fn visit_with_live_after(&mut self, id: CoreId, live_after: &BTreeSet<String>) {
        let e = self.body.expression(id).clone();
        match e.kind {
            CoreKind::Literal(_)
            | CoreKind::Function(_)
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
            CoreKind::Closure { captures, .. } => {
                for capture in captures {
                    self.capture_reference_loan(&capture.name, e.span);
                    match capture.mode {
                        CaptureMode::SharedBorrow => self.borrow(&capture.name, false, e.span),
                        CaptureMode::UniqueBorrow => self.borrow(&capture.name, true, e.span),
                        CaptureMode::Move => self.move_(&capture.name, e.span),
                    }
                }
            }
            CoreKind::Local(_) => self.read_place(id, e.span),
            CoreKind::Let { name, value } => {
                if let CoreKind::Borrow { unique, value } = self.body.expression(value).kind.clone()
                {
                    // `name` owns the region instead of creating a forever
                    // live temporary loan. Evaluate the borrowed place first;
                    // its read remains subject to all pre-existing loans.
                    self.visit_with_live_after(value, live_after);
                    self.borrow_place(value, unique, e.span, Some(name.clone()));
                } else {
                    self.visit_with_live_after(value, live_after);
                }
                self.states.insert(name.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(name), e.span)
            }
            CoreKind::Assign { place, value } => {
                self.visit_with_live_after(value, live_after);
                self.assign_place(&place, e.span);
            }
            CoreKind::Move(v) => {
                self.visit_with_live_after(v, live_after);
                // A field is a place projection into its root local.  The
                // current flow domain does not retain per-field move paths,
                // so consuming a projection must conservatively consume the
                // owner too.  That preserves the essential ownership
                // invariant until partial-move states are represented.
                self.move_place(v, e.span)
            }
            CoreKind::Unary { value, .. } => self.visit_with_live_after(value, live_after),
            CoreKind::Borrow { unique, value } => {
                self.visit_with_live_after(value, live_after);
                // A field projection is still a borrow of storage owned by
                // its root local.  Until PlaceFlow has projection-disjoint
                // loans, retain a loan on that root rather than silently
                // treating `&record.field` as a borrow of a temporary value.
                // This is conservative, but prevents moving or overwriting
                // the enclosing record while a reference into it is live.
                self.borrow_place(value, unique, e.span, None)
            }
            CoreKind::Call { callee, arguments } => {
                let mut values = vec![callee];
                values.extend(arguments);
                self.visit_sequence(&values, live_after);
            }
            CoreKind::Perform { arguments, .. } => {
                self.visit_sequence(&arguments, live_after);
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                let mut inside_handler = live_after.clone();
                for clause in &clauses {
                    self.collect_local_uses(clause.body, &mut inside_handler);
                }
                self.visit_with_live_after(computation, &inside_handler);
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
                    self.visit_with_live_after(clause.body, live_after);
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
                let mut inside_completion = live_after.clone();
                for clause in &clauses {
                    self.collect_local_uses(clause.body, &mut inside_completion);
                }
                self.visit_with_live_after(computation, &inside_completion);
                let incoming = self.states.clone();
                let incoming_loans = self.projection_loans.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    self.projection_loans = incoming_loans.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit_with_live_after(clause.body, live_after);
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
                self.visit_sequence(&values, live_after);
            }
            CoreKind::Record { fields, .. } => {
                self.visit_sequence(&fields, live_after);
            }
            CoreKind::Enum { fields, .. } => {
                self.visit_sequence(&fields, live_after);
            }
            CoreKind::Field { .. } => self.read_place(id, e.span),
            CoreKind::PatternTest { subject, .. } => {
                self.visit_with_live_after(subject, live_after)
            }
            CoreKind::Binary { left, right, .. } => {
                self.visit_sequence(&[left, right], live_after);
            }
            CoreKind::Block(values) => self.visit_sequence(&values, live_after),
        }
        self.release_dead_loans(live_after, e.span);
    }

    fn visit_sequence(&mut self, values: &[CoreId], live_after: &BTreeSet<String>) {
        let mut suffixes = vec![live_after.clone(); values.len()];
        let mut future = live_after.clone();
        for (index, value) in values.iter().enumerate().rev() {
            suffixes[index] = future.clone();
            self.collect_local_uses(*value, &mut future);
        }
        for (value, future) in values.iter().zip(suffixes) {
            self.visit_with_live_after(*value, &future);
        }
    }

    /// Source-free local-use collection over Typed Core. Names are deliberately
    /// collected conservatively across shadowing: retaining a loan too long is
    /// safe, whereas releasing it before a shadow-sensitive use would not be.
    fn collect_local_uses(&self, id: CoreId, uses: &mut BTreeSet<String>) {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => {
                uses.insert(name.clone());
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
                for value in values {
                    self.collect_local_uses(*value, uses);
                }
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                for field in fields {
                    self.collect_local_uses(*field, uses);
                }
            }
            CoreKind::Field { base, .. }
            | CoreKind::Borrow { value: base, .. }
            | CoreKind::Move(base)
            | CoreKind::Unary { value: base, .. }
            | CoreKind::PatternTest { subject: base, .. } => self.collect_local_uses(*base, uses),
            CoreKind::Let { value, .. } => self.collect_local_uses(*value, uses),
            CoreKind::Assign { value, .. } => self.collect_local_uses(*value, uses),
            CoreKind::Call { callee, arguments } => {
                self.collect_local_uses(*callee, uses);
                for argument in arguments {
                    self.collect_local_uses(*argument, uses);
                }
            }
            CoreKind::Perform { arguments, .. } => {
                for argument in arguments {
                    self.collect_local_uses(*argument, uses);
                }
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.collect_local_uses(*computation, uses);
                for clause in clauses {
                    self.collect_local_uses(clause.body, uses);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
            } => {
                self.collect_local_uses(*computation, uses);
                for clause in clauses {
                    self.collect_local_uses(clause.body, uses);
                }
            }
            CoreKind::Binary { left, right, .. } => {
                self.collect_local_uses(*left, uses);
                self.collect_local_uses(*right, uses);
            }
            CoreKind::Closure { captures, .. } => {
                // Captures are reads at callable construction time.  More
                // importantly, a captured reference keeps its owning local
                // live until this closure boundary can reborrow its backing
                // place in `visit_with_live_after`.
                for capture in captures {
                    uses.insert(capture.name.clone());
                }
            }
            CoreKind::Literal(_)
            | CoreKind::Function(_)
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
        }
    }

    fn release_dead_loans(&mut self, live_after: &BTreeSet<String>, span: Span) {
        let dead = self
            .projection_loans
            .iter()
            .filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| !live_after.contains(*owner))
            .cloned()
            .collect::<BTreeSet<_>>();
        for owner in dead {
            self.release_owner_loans(&owner, span);
        }
    }

    /// Transfer the backing region of a named reference into a closure
    /// environment.  `let r = &place; let f = || r` is not merely a borrow of
    /// the stack slot for `r`: `f` can later read the reference value and
    /// therefore keeps `place` borrowed.  The closure environment has no
    /// source-local spelling in Typed Core, so `owner: None` is the explicit
    /// conservative representation of an escaping/unknown owner.  It is
    /// retained through handler joins and to the end of the enclosing body.
    ///
    /// This is also the first reborrow operation in the flow domain.  We copy
    /// the exact projected source loan, preserving mutability, rather than
    /// widening `&pair.left` to an imprecise whole-record loan.
    fn capture_reference_loan(&mut self, name: &str, span: Span) {
        let reborrows = self
            .projection_loans
            .iter()
            .filter(|loan| loan.owner.as_deref() == Some(name))
            .cloned()
            .map(|mut loan| {
                loan.owner = None;
                loan
            })
            .collect::<Vec<_>>();
        if reborrows.is_empty() {
            return;
        }
        for loan in reborrows {
            if !self.projection_loans.contains(&loan) {
                self.event(FlowEventKind::Reborrow(loan.place.root.clone()), span);
                self.projection_loans.push(loan);
            }
        }
    }

    fn release_owner_loans(&mut self, owner: &str, span: Span) {
        let removed = self
            .projection_loans
            .iter()
            .filter(|loan| loan.owner.as_deref() == Some(owner))
            .cloned()
            .collect::<Vec<_>>();
        if removed.is_empty() {
            return;
        }
        self.projection_loans
            .retain(|loan| loan.owner.as_deref() != Some(owner));
        for loan in removed.iter().filter(|loan| loan.place.fields.is_empty()) {
            let remaining_shared = self
                .projection_loans
                .iter()
                .filter(|other| other.place == loan.place && !other.unique)
                .count() as u32;
            let remaining_unique = self
                .projection_loans
                .iter()
                .any(|other| other.place == loan.place && other.unique);
            let state = self.states.get(&loan.place.root).copied();
            match (state, loan.unique, remaining_unique) {
                (Some(LocalState::UniquelyBorrowed), true, false) => {
                    self.states
                        .insert(loan.place.root.clone(), LocalState::Initialized);
                }
                (Some(LocalState::SharedBorrowed(count)), false, false) => {
                    let retained_untracked = count.saturating_sub(1 + remaining_shared);
                    let total = retained_untracked + remaining_shared;
                    self.states.insert(
                        loan.place.root.clone(),
                        if total == 0 {
                            LocalState::Initialized
                        } else {
                            LocalState::SharedBorrowed(total)
                        },
                    );
                }
                _ => {}
            }
        }
        self.event(FlowEventKind::EndBorrow(owner.into()), span);
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

    fn borrow_place(&mut self, id: CoreId, unique: bool, span: Span, owner: Option<String>) {
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
            // Keep a precise whole-place fact only for a lexical reference
            // loan. Legacy temporary/capture loans remain represented solely
            // by LocalState until their Core lifetime is explicit.
            if owner.is_some() {
                self.projection_loans.push(ProjectionLoan {
                    place,
                    unique,
                    owner,
                });
            }
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
        self.projection_loans.push(ProjectionLoan {
            place,
            unique,
            owner,
        });
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
