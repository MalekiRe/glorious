//! Ownership facts derived solely from Typed Core before MIR lowering.

use crate::{
    core::{CaptureMode, CoreId, CoreKind, CorePlace, RefinementBrand, TypedBody},
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

    fn is_strict_ancestor_of(&self, other: &Self) -> bool {
        self.root == other.root
            && self.fields.len() < other.fields.len()
            && other.fields.starts_with(&self.fields)
    }

    fn display(&self) -> String {
        self.fields
            .iter()
            .fold(self.root.clone(), |mut text, field| {
                text.push('.');
                text.push_str(&field.to_string());
                text
            })
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

/// A frozen move path that remains uninitialized at the body exit. A path
/// with no fields denotes a whole local; otherwise it denotes one statically
/// selected aggregate field. Facts are canonical: no fact is a strict
/// descendant of another fact, which makes them directly usable by future
/// drop elaboration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct MoveFact {
    pub root: String,
    pub fields: Vec<u32>,
}
/// A lexical positive refinement observed while interpreting Core. It is an
/// inspection fact, not a persistent binding: joins and callable boundaries
/// intentionally do not retain it unless a later branch lowering proves the
/// same brand on every predecessor.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct RefinementFact {
    pub brand: RefinementBrand,
    pub subject: Option<String>,
    pub bindings: Vec<String>,
    pub span: Span,
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
    /// Exact canonical place identity when this event operates on a static
    /// projection. Consumers such as UseFlow must use this fact rather than
    /// reconstructing projection paths from syntax.
    pub place: Option<MoveFact>,
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
    /// Projection-granular uninitialized paths. `final_states` remains the
    /// compact whole-local summary for existing consumers; this retains the
    /// information needed for partial moves and aggregate cleanup.
    pub moved_places: Vec<MoveFact>,
    pub active_loans: Vec<LoanFact>,
    pub refinements: Vec<RefinementFact>,
    pub events: Vec<FlowEvent>,
    pub diagnostics: Vec<FlowDiagnostic>,
}
impl PlaceFlow {
    pub fn analyze(body: &TypedBody) -> Self {
        let mut a = Analyzer {
            body,
            states: BTreeMap::new(),
            projection_loans: vec![],
            reborrow_parents: BTreeMap::new(),
            reference_origins: BTreeMap::new(),
            moved_places: BTreeSet::new(),
            events: vec![],
            refinements: vec![],
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
        let moved_places = a
            .moved_places
            .iter()
            .map(|place| MoveFact {
                root: place.root.clone(),
                fields: place.fields.clone(),
            })
            .collect();
        Self {
            final_states: a.states,
            moved_places,
            active_loans,
            refinements: a.refinements,
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
    /// Child reference binding -> suspended parent binding.  This is kept
    /// separate from the loan identity because a child may end nonlexically
    /// while the parent loan remains available again.
    reborrow_parents: BTreeMap<String, String>,
    /// Provenance outlives one compact active-loan entry.  It is consulted
    /// only when a live descendant proves the parent region remains open.
    reference_origins: BTreeMap<String, ProjectionLoan>,
    /// Canonical paths that have been moved and have not since been
    /// reinitialized. Whole-local moves are mirrored in `states`; field moves
    /// deliberately are not, because their siblings remain usable.
    moved_places: BTreeSet<Projection>,
    events: Vec<FlowEvent>,
    refinements: Vec<RefinementFact>,
    diagnostics: Vec<FlowDiagnostic>,
}

/// State observed at one dynamically selected handler/completion exit.
type HandlerExit = (
    BTreeMap<String, LocalState>,
    Vec<ProjectionLoan>,
    BTreeSet<Projection>,
    BTreeMap<String, String>,
    BTreeMap<String, ProjectionLoan>,
);

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
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
            CoreKind::Closure { environment, .. } => {
                if environment.post_states.len() != environment.captures.len()
                    || environment
                        .captures
                        .iter()
                        .zip(&environment.post_states)
                        .any(|(capture, state)| {
                            capture.name != state.name || capture.mode != state.mode
                        })
                {
                    self.error(
                        e.span,
                        "G5020",
                        "closure environment capture post-state disagrees with its sealed layout"
                            .into(),
                    );
                    return;
                }
                for (capture, post_state) in
                    environment.captures.iter().zip(&environment.post_states)
                {
                    self.capture_reference_loan(&capture.name, e.span);
                    let place = Projection {
                        root: capture.name.clone(),
                        fields: vec![],
                    };
                    match post_state.mode {
                        CaptureMode::SharedBorrow => {
                            self.borrow(&capture.name, false, e.span);
                            self.place_event(
                                FlowEventKind::BorrowShared(capture.name.clone()),
                                place,
                                e.span,
                            );
                        }
                        CaptureMode::UniqueBorrow => {
                            self.borrow(&capture.name, true, e.span);
                            self.place_event(
                                FlowEventKind::BorrowUnique(capture.name.clone()),
                                place,
                                e.span,
                            );
                        }
                        CaptureMode::Move => {
                            self.move_(&capture.name, e.span);
                            self.place_event(
                                FlowEventKind::Move(capture.name.clone()),
                                place,
                                e.span,
                            );
                        }
                    }
                }
            }
            CoreKind::Local(_) => self.read_place(id, e.span),
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.visit_with_live_after(body, live_after)
            }
            CoreKind::Let { name, value } => {
                if let CoreKind::Borrow { unique, value } = self.body.expression(value).kind.clone()
                {
                    // `name` owns the region instead of creating a forever
                    // live temporary loan. Evaluate the borrowed place first;
                    // its read remains subject to all pre-existing loans.
                    // The referent is evaluated before the lexical child is
                    // installed.  Include its handles in the NLL frontier so
                    // `let child = &*parent` cannot release `parent` merely
                    // because only `child` is used after a handler boundary.
                    let mut borrow_live = live_after.clone();
                    self.collect_local_uses(value, &mut borrow_live);
                    if let CoreKind::Deref(reference) = self.body.expression(value).kind {
                        self.visit_with_live_after(reference, &borrow_live);
                    } else {
                        self.visit_with_live_after(value, &borrow_live);
                    }
                    if !self.reborrow_place(value, unique, e.span, name.clone()) {
                        self.borrow_place(value, unique, e.span, Some(name.clone()));
                    }
                } else {
                    self.visit_with_live_after(value, live_after);
                }
                self.states.insert(name.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(name), e.span)
            }
            CoreKind::Assign { place, value } => {
                // The destination is evaluated after the RHS, but its local
                // references must keep their loans alive while the RHS is
                // evaluated.  Otherwise `*parent = rhs` could prematurely
                // end the parent region before the destination conflict is
                // checked against a live reborrow.
                let mut rhs_live = live_after.clone();
                self.collect_place_uses(&place, &mut rhs_live);
                self.visit_with_live_after(value, &rhs_live);
                if let CorePlace::Deref { reference, .. } = &place {
                    self.use_deref_reference(*reference, e.span, true);
                }
                self.assign_place(&place, e.span);
            }
            CoreKind::Move(v) => {
                // A move of a static place is validated directly. Visiting a
                // field first would turn a second move into an unrelated
                // read-after-move diagnostic and obscure the precise path
                // being consumed.
                if self.projection(v).is_none() {
                    self.visit_with_live_after(v, live_after);
                }
                self.move_place(v, e.span)
            }
            CoreKind::Unary { value, .. } => self.visit_with_live_after(value, live_after),
            CoreKind::Borrow { unique, value } => {
                if self.projection(value).is_none() {
                    self.visit_with_live_after(value, live_after);
                }
                if let CoreKind::Deref(reference) = self.body.expression(value).kind
                    && !matches!(self.body.expression(reference).kind, CoreKind::Local(_))
                {
                    self.error(
                        e.span,
                        "G5006",
                        "reborrow through an aggregate-held reference requires an explicit local loan binding".into(),
                    );
                    return;
                }
                self.borrow_place(value, unique, e.span, None)
            }
            CoreKind::Deref(value) => {
                self.visit_with_live_after(value, live_after);
                self.use_deref_reference(value, e.span, false);
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
                let incoming_moves = self.moved_places.clone();
                let incoming_parents = self.reborrow_parents.clone();
                let incoming_origins = self.reference_origins.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    self.projection_loans = incoming_loans.clone();
                    self.moved_places = incoming_moves.clone();
                    self.reborrow_parents = incoming_parents.clone();
                    self.reference_origins = incoming_origins.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    if let crate::core::CoreHandlerResumption::Explicit { name, .. } =
                        clause.resumption
                    {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit_with_live_after(clause.body, live_after);
                    exits.push((
                        self.states.clone(),
                        self.projection_loans.clone(),
                        self.moved_places.clone(),
                        self.reborrow_parents.clone(),
                        self.reference_origins.clone(),
                    ));
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(
                        &exits
                            .iter()
                            .map(|(states, _, _, _, _)| states.clone())
                            .collect::<Vec<_>>(),
                    );
                    self.projection_loans = join_handler_projection_loans(&exits, &incoming);
                    self.moved_places = join_handler_moves(&exits, &incoming);
                    self.join_reborrow_facts(&exits, &incoming);
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
                let incoming_moves = self.moved_places.clone();
                let incoming_parents = self.reborrow_parents.clone();
                let incoming_origins = self.reference_origins.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for clause in clauses {
                    self.states = incoming.clone();
                    self.projection_loans = incoming_loans.clone();
                    self.moved_places = incoming_moves.clone();
                    self.reborrow_parents = incoming_parents.clone();
                    self.reference_origins = incoming_origins.clone();
                    for (name, _) in clause.bindings {
                        self.states.insert(name, LocalState::Initialized);
                    }
                    self.visit_with_live_after(clause.body, live_after);
                    exits.push((
                        self.states.clone(),
                        self.projection_loans.clone(),
                        self.moved_places.clone(),
                        self.reborrow_parents.clone(),
                        self.reference_origins.clone(),
                    ));
                }
                if !exits.is_empty() {
                    self.states = join_handler_exits(
                        &exits
                            .iter()
                            .map(|(states, _, _, _, _)| states.clone())
                            .collect::<Vec<_>>(),
                    );
                    self.projection_loans = join_handler_projection_loans(&exits, &incoming);
                    self.moved_places = join_handler_moves(&exits, &incoming);
                    self.join_reborrow_facts(&exits, &incoming);
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
            CoreKind::PatternTest {
                subject,
                refinement,
                ..
            } => {
                self.visit_with_live_after(subject, live_after);
                // `is` produces a scoped positive proof. The expression
                // itself cannot introduce ordinary locals, so retaining this
                // only as a branded observation makes escape and join errors
                // visible without granting it authority past the test.
                self.refinements.push(RefinementFact {
                    brand: refinement.brand,
                    subject: refinement.subject,
                    bindings: refinement.bindings,
                    span: e.span,
                });
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
            | CoreKind::Deref(base)
            | CoreKind::Move(base)
            | CoreKind::Unary { value: base, .. }
            | CoreKind::PatternTest { subject: base, .. } => self.collect_local_uses(*base, uses),
            CoreKind::Let { value, .. } => self.collect_local_uses(*value, uses),
            CoreKind::Assign { place, value } => {
                self.collect_local_uses(*value, uses);
                self.collect_place_uses(place, uses);
            }
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
            CoreKind::Closure { environment, .. } => {
                // Captures are reads at callable construction time.  More
                // importantly, a captured reference keeps its owning local
                // live until this closure boundary can reborrow its backing
                // place in `visit_with_live_after`.
                for capture in &environment.captures {
                    uses.insert(capture.name.clone());
                }
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } => {
                self.collect_local_uses(*body, uses)
            }
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant(_)
            | CoreKind::Error => {}
        }
    }

    fn collect_place_uses(&self, place: &CorePlace, uses: &mut BTreeSet<String>) {
        match place {
            CorePlace::Local { name, .. } => {
                uses.insert(name.clone());
            }
            CorePlace::Field { base, .. } => self.collect_place_uses(base, uses),
            CorePlace::Deref { reference, .. } => self.collect_local_uses(*reference, uses),
            CorePlace::Error => {}
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
    fn move_(&mut self, n: &str, s: Span) {
        let place = Projection {
            root: n.into(),
            fields: vec![],
        };
        if let Some(moved) = self.moved_place_overlapping(&place) {
            self.error(
                s,
                "G5003",
                format!(
                    "cannot move `{n}` because `{}` is already moved",
                    moved.display()
                ),
            );
            return;
        }
        match self.states.get(n) {
            Some(LocalState::Initialized) => {
                self.states.insert(n.into(), LocalState::Moved);
                self.record_move(place);
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
    fn event(&mut self, kind: FlowEventKind, span: Span) {
        self.events.push(FlowEvent {
            kind,
            span,
            place: None,
        })
    }

    fn place_event(&mut self, kind: FlowEventKind, place: Projection, span: Span) {
        self.events.push(FlowEvent {
            kind,
            span,
            place: Some(MoveFact {
                root: place.root,
                fields: place.fields,
            }),
        })
    }

    fn moved_place_overlapping(&self, place: &Projection) -> Option<Projection> {
        self.moved_places
            .iter()
            .find(|moved| moved.overlaps(place))
            .cloned()
    }

    /// Returns a moved *proper prefix* of `place`. Writing the exact moved
    /// field is a reinitialization, but writing through an already-moved
    /// parent would require accessing uninitialized storage and is rejected.
    fn moved_ancestor_of(&self, place: &Projection) -> Option<Projection> {
        self.moved_places
            .iter()
            .find(|moved| moved.is_strict_ancestor_of(place))
            .cloned()
    }

    fn record_move(&mut self, place: Projection) {
        // A whole/parent move subsumes any child facts. Conversely, a child
        // fact under an already moved parent cannot add information.
        if self
            .moved_places
            .iter()
            .any(|moved| place.fields.starts_with(&moved.fields) && moved.root == place.root)
        {
            return;
        }
        self.moved_places
            .retain(|moved| !place.is_strict_ancestor_of(moved));
        self.moved_places.insert(place);
    }

    fn reinitialize_place(&mut self, place: &Projection) {
        // Replacing an aggregate initializes all of its descendants. Replacing
        // one field initializes that field and any previously moved subfields,
        // while intentionally leaving sibling move facts alone.
        self.moved_places
            .retain(|moved| !moved.fields.starts_with(&place.fields) || moved.root != place.root);
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
            // Dynamic aliasing through a reference is represented by the
            // reference loan, not conflated with a statically disjoint field
            // projection.  The loan checker remains conservative here.
            CorePlace::Deref { .. } => None,
            CorePlace::Error => None,
        }
    }

    fn read_place(&mut self, id: CoreId, span: Span) {
        let Some(place) = self.projection(id) else {
            return;
        };
        if let Some(moved) = self.moved_place_overlapping(&place) {
            self.error(
                span,
                "G5001",
                format!("use of moved place `{}`", moved.display()),
            );
            return;
        }
        // Preserve the complete static projection in the event stream. Later
        // consumers (notably quantitative-use) must not reconstruct a field
        // path from source spelling or collapse `pair.left` into `pair`.
        match self.states.get(&place.root) {
            Some(LocalState::Moved) => self.error(
                span,
                "G5001",
                format!("use of moved local `{}`", place.root),
            ),
            Some(LocalState::UniquelyBorrowed) => self.error(
                span,
                "G5008",
                format!("cannot read uniquely borrowed local `{}`", place.root),
            ),
            Some(_) => {
                self.place_event(FlowEventKind::Read(place.root.clone()), place.clone(), span)
            }
            None => self.error(
                span,
                "G5002",
                format!("unknown local `{}` in PlaceFlow", place.root),
            ),
        }
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
        if let Some(moved) = self.moved_place_overlapping(&place) {
            self.error(
                span,
                "G5003",
                format!(
                    "cannot move `{}` because `{}` is already moved",
                    place.display(),
                    moved.display()
                ),
            );
            return;
        }
        match self.states.get(&place.root).copied() {
            Some(LocalState::Initialized) => {
                if place.fields.is_empty() {
                    self.states.insert(place.root.clone(), LocalState::Moved);
                }
                self.record_move(place.clone());
                self.place_event(FlowEventKind::Move(place.root.clone()), place, span);
            }
            Some(LocalState::Moved) => self.error(
                span,
                "G5003",
                format!("local `{}` is moved more than once", place.root),
            ),
            Some(_) => self.error(
                span,
                "G5004",
                format!("cannot move borrowed local `{}`", place.root),
            ),
            None => self.error(
                span,
                "G5002",
                format!("unknown local `{}` in PlaceFlow", place.root),
            ),
        }
    }

    fn borrow_place(&mut self, id: CoreId, unique: bool, span: Span, owner: Option<String>) {
        let Some(place) = self.projection(id) else {
            return;
        };
        if let Some(moved) = self.moved_place_overlapping(&place) {
            self.error(
                span,
                "G5005",
                format!("cannot borrow moved place `{}`", moved.display()),
            );
            return;
        }
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
            self.place_event(
                if unique {
                    FlowEventKind::BorrowUnique(place.root.clone())
                } else {
                    FlowEventKind::BorrowShared(place.root.clone())
                },
                place.clone(),
                span,
            );
            // Keep a precise whole-place fact only for a lexical reference
            // loan. Legacy temporary/capture loans remain represented solely
            // by LocalState until their Core lifetime is explicit.
            if owner.is_some() {
                let loan = ProjectionLoan {
                    place,
                    unique,
                    owner,
                };
                if let Some(owner) = &loan.owner {
                    self.reference_origins.insert(owner.clone(), loan.clone());
                }
                self.projection_loans.push(loan);
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
        let loan = ProjectionLoan {
            place: place.clone(),
            unique,
            owner,
        };
        if let Some(owner) = &loan.owner {
            self.reference_origins.insert(owner.clone(), loan.clone());
        }
        self.projection_loans.push(loan);
        self.place_event(
            if unique {
                FlowEventKind::BorrowUnique(self.root_name(id))
            } else {
                FlowEventKind::BorrowShared(self.root_name(id))
            },
            place,
            span,
        );
    }

    /// A borrow of `*reference` is a reborrow of the reference's frozen loan,
    /// not a borrow of a temporary dereference result.  The child owns a
    /// distinct NLL region and therefore keeps the parent suspended while it
    /// remains live.
    fn reborrow_place(&mut self, id: CoreId, unique: bool, span: Span, owner: String) -> bool {
        let CoreKind::Deref(reference) = self.body.expression(id).kind else {
            return false;
        };
        let CoreKind::Local(parent) = &self.body.expression(reference).kind else {
            return false;
        };
        let parent_loan = self
            .projection_loans
            .iter()
            .find(|loan| loan.owner.as_deref() == Some(parent.as_str()))
            .cloned()
            .or_else(|| {
                self.projection_loans
                    .iter()
                    .any(|loan| {
                        let mut owner = loan.owner.as_deref();
                        while let Some(current) = owner {
                            if current == parent {
                                return true;
                            }
                            owner = self.reborrow_parents.get(current).map(String::as_str);
                        }
                        false
                    })
                    .then(|| self.reference_origins.get(parent).cloned())
                    .flatten()
            });
        let Some(parent_loan) = parent_loan else {
            self.error(span, "G5006", "reborrow has no live parent loan".into());
            return true;
        };
        if unique && !parent_loan.unique {
            self.error(
                span,
                "G5006",
                "unique reborrow requires a unique parent loan".into(),
            );
            return true;
        }
        self.place_event(
            FlowEventKind::Reborrow(parent_loan.place.root.clone()),
            parent_loan.place.clone(),
            span,
        );
        let loan = ProjectionLoan {
            place: parent_loan.place,
            unique,
            owner: Some(owner.clone()),
        };
        self.reference_origins.insert(owner.clone(), loan.clone());
        self.projection_loans.push(loan);
        self.reborrow_parents.insert(owner, parent.clone());
        true
    }

    fn use_deref_reference(&mut self, id: CoreId, span: Span, mutation: bool) {
        let CoreKind::Local(name) = &self.body.expression(id).kind else {
            return;
        };
        let Some(parent) = self
            .projection_loans
            .iter()
            .find(|loan| loan.owner.as_deref() == Some(name.as_str()))
            .cloned()
        else {
            return;
        };
        let conflicts = self.projection_loans.iter().any(|loan| {
            loan.owner.as_deref() != Some(name.as_str())
                && self
                    .reborrow_parents
                    .get(name)
                    .is_none_or(|parent| loan.owner.as_deref() != Some(parent.as_str()))
                && loan.place.overlaps(&parent.place)
                && (mutation || parent.unique || loan.unique)
        });
        if conflicts {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot access reborrowed place `{}` through its suspended parent",
                    parent.place.root
                ),
            );
        }
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
        if let Some(moved) = self.moved_ancestor_of(&projection) {
            self.error(
                span,
                "G5009",
                format!(
                    "cannot assign through moved place `{}`; reinitialize `{}` first",
                    moved.display(),
                    moved.display()
                ),
            );
            return;
        }
        if projection.fields.is_empty() {
            match self.states.get(&projection.root).copied() {
                Some(LocalState::Initialized) | Some(LocalState::Moved) => {
                    self.states
                        .insert(projection.root.clone(), LocalState::Initialized);
                    self.reinitialize_place(&projection);
                    self.place_event(
                        FlowEventKind::Assign(projection.root.clone()),
                        projection,
                        span,
                    );
                }
                Some(LocalState::SharedBorrowed(_)) | Some(LocalState::UniquelyBorrowed) => self
                    .error(
                        span,
                        "G5007",
                        format!("cannot assign to borrowed local `{}`", projection.root),
                    ),
                None => self.error(
                    span,
                    "G5002",
                    format!("unknown local `{}` in PlaceFlow", projection.root),
                ),
            }
            return;
        }
        match self.states.get(&projection.root).copied() {
            Some(LocalState::Initialized) => {
                self.reinitialize_place(&projection);
                self.place_event(
                    FlowEventKind::Assign(projection.root.clone()),
                    projection,
                    span,
                );
            }
            Some(LocalState::Moved) => self.error(
                span,
                "G5009",
                format!(
                    "cannot assign through moved local `{}`; reinitialize the local first",
                    projection.root
                ),
            ),
            Some(LocalState::SharedBorrowed(_)) | Some(LocalState::UniquelyBorrowed) => self.error(
                span,
                "G5007",
                format!("cannot assign to borrowed local `{}`", projection.root),
            ),
            None => self.error(
                span,
                "G5002",
                format!("unknown local `{}` in PlaceFlow", projection.root),
            ),
        }
    }

    fn root_name(&self, id: CoreId) -> String {
        self.projection(id)
            .map(|place| place.root)
            .unwrap_or_default()
    }

    fn join_reborrow_facts(
        &mut self,
        exits: &[HandlerExit],
        incoming: &BTreeMap<String, LocalState>,
    ) {
        self.reborrow_parents = exits
            .iter()
            .flat_map(|(_, _, _, parents, _)| parents)
            .filter(|(child, _)| incoming.contains_key(*child))
            .map(|(child, parent)| (child.clone(), parent.clone()))
            .collect();
        self.reference_origins = exits
            .iter()
            .flat_map(|(_, _, _, _, origins)| origins)
            .filter(|(_, loan)| incoming.contains_key(&loan.place.root))
            .map(|(name, loan)| (name.clone(), loan.clone()))
            .collect();
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
    exits: &[HandlerExit],
    incoming: &BTreeMap<String, LocalState>,
) -> Vec<ProjectionLoan> {
    let mut loans = exits
        .iter()
        .flat_map(|(_, loans, _, _, _)| loans)
        .filter(|loan| incoming.contains_key(&loan.place.root))
        .cloned()
        .collect::<Vec<_>>();
    loans.sort();
    loans.dedup();
    loans
}

/// Dynamic handler/completion selection may take any arm, so a field moved
/// on one exit is unavailable after the join even if a sibling arm leaves it
/// initialized. This is the aggregate analogue of the conservative whole
/// local `Moved` join above. Clause-local roots are excluded because they
/// cannot escape their arm.
fn join_handler_moves(
    exits: &[HandlerExit],
    incoming: &BTreeMap<String, LocalState>,
) -> BTreeSet<Projection> {
    let mut moves = exits
        .iter()
        .flat_map(|(_, _, moves, _, _)| moves)
        .filter(|place| incoming.contains_key(&place.root))
        .cloned()
        .collect::<Vec<_>>();
    moves.sort();
    moves.dedup();
    let mut canonical = BTreeSet::new();
    for place in moves {
        if canonical.iter().any(|known: &Projection| {
            known.root == place.root && place.fields.starts_with(&known.fields)
        }) {
            continue;
        }
        canonical.retain(|known| !place.is_strict_ancestor_of(known));
        canonical.insert(place);
    }
    canonical
}
