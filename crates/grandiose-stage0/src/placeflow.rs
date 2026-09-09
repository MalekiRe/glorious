//! Ownership facts derived solely from Typed Core before MIR lowering.

use crate::{
    LabelBrand,
    core::{
        CallReferenceOrigin, CallReferenceShape, CaptureMode, CoreId, CoreKind, CorePattern,
        CorePlace, RefinementBrand, TypedBody,
    },
    quantity::Quantity,
    signature::ElaboratedInterface,
    source::Span,
    types::Type,
};
use std::collections::{BTreeMap, BTreeSet};

mod minimum;
mod drop;
use minimum::{MinimumBinding, MinimumDisposition, MinimumHandler};

/// A statically-selected subplace of one local.  PlaceFlow deliberately keeps
/// dereferences out of this representation: their aliasing is not yet proven
/// precisely enough to make them disjoint.  Struct-field paths, on the other
/// hand, have stable Core indices and can safely participate in overlap tests.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Projection {
    root: String,
    fields: Vec<u32>,
}

/// A strict child which never reaches the next source-ordered operand.  A
/// label transfer is kept distinct from `Never`: a label consumes transfers to
/// its own brand and turns them back into an ordinary result for the enclosing
/// continuation, whereas a transfer targeting an outer label skips all
/// siblings still inside the current label body.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum AbruptExit {
    Never,
    Transfer(LabelBrand),
}

impl Projection {
    fn overlaps(&self, other: &Self) -> bool {
        self.root == other.root
            && (crate::core::reference_path_is_prefix(&self.fields, &other.fields)
                || crate::core::reference_path_is_prefix(&other.fields, &self.fields))
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

fn projection_key(root: &str, fields: &[u32]) -> String {
    fields.iter().fold(root.to_owned(), |mut key, field| {
        key.push('.');
        key.push_str(&field.to_string());
        key
    })
}

fn belongs_to_scope(locals: &BTreeSet<String>, key: &str) -> bool {
    locals.iter().any(|local| {
        key == local
            || key
                .strip_prefix(local)
                .is_some_and(|suffix| suffix.starts_with('.'))
    })
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct ProjectionLoan {
    place: Projection,
    unique: bool,
    /// The lexical reference binding that keeps this loan live. `None` is a
    /// conservative temporary/capture loan whose lifetime has not yet been
    /// made explicit in Typed Core.
    owner: Option<String>,
    /// Distinct reference leaves returned by one checked call coexist in the
    /// same value. Whenever either leaf is unique, they must be disjoint.
    /// Retain this structural partition through forwarding and reborrowing,
    /// separately from the caller region which keeps the backing owner live.
    partitions: BTreeMap<CoreId, Vec<u32>>,
    /// Incoming reference leaves name caller storage, not the local slot
    /// containing the reference handle. Reborrowing a parameter's field must
    /// not make merely reading that handle look like reading the whole data.
    indirect: bool,
    /// A frozen External/Unsafe call establishes this referent, not a local
    /// or parameter binding. Its descendants still obey ordinary loan rules.
    external: bool,
}

impl ProjectionLoan {
    fn disjoint_from(&self, other: &Self) -> bool {
        self.partitions.iter().any(|(call, fields)| other.partitions.get(call)
            .is_some_and(|other| !crate::core::reference_path_is_prefix(fields, other)
                && !crate::core::reference_path_is_prefix(other, fields)))
    }
}

/// Snapshot the source before generative arm names shadow its spelling.
/// Installation happens only in the selected arm, after its locals exist.
struct PatternBindingTransfer {
    name: String,
    value: CoreId,
    moved: Option<Projection>,
    borrowed_move: bool,
    aliases: Vec<(Vec<u32>, BTreeSet<ProjectionLoan>)>,
    regions: Vec<(Vec<u32>, BTreeSet<regions::Region>)>,
}

/// A frozen ownership fact for a loan that is still live at the body exit.
/// Unlike the compact [`LocalState`] summary this retains the exact projected
/// place and, when available, the reference local that owns its region.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct LoanFact {
    pub owner: Option<String>,
    /// Opaque lexical storage identity for this loan's root. Text remains
    /// available for diagnostics, but cleanup and VM verification compare it.
    pub binding: PlaceBindingId,
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

/// Body-local identity for one statically distinguishable owned move path.
/// Identities are dense and append-only for the duration of one PlaceFlow
/// analysis; they are never inferred from a source spelling or a final-fact
/// position.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct MovePathId(pub u32);

/// Opaque identity for one lexical storage binding in a Typed Core body.
///
/// A source spelling is intentionally not an identity: a nested `let value`
/// must never share a move-path root with an outer `value`.  The id is dense
/// and append-only during one PlaceFlow analysis.  It is published alongside
/// the original spelling so diagnostics and the legacy compact facts can stay
/// readable while later MIR import stops reconstructing ownership from names.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct PlaceBindingId(pub u32);

pub(crate) fn borrowed_temporary_root(expression: CoreId) -> String {
    format!("<borrowed-temporary-{}>", expression.0)
}

pub(crate) fn borrowed_place_base(body: &TypedBody, mut expression: CoreId) -> CoreId {
    while let CoreKind::Field { base, .. } = body.expression(expression).kind {
        expression = base;
    }
    expression
}

/// Typed lexical storage-scope identity published with one [`PlaceFlow`]
/// product.  This is deliberately independent from parser/source scopes: it
/// records exactly the scopes which own addressable bindings and therefore
/// determine `StorageLive`/`StorageDead` and cleanup boundaries in MIR.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SourceStorageScopeId(pub u32);

impl SourceStorageScopeId {
    pub const ROOT: Self = Self(0);
}

/// One immutable lexical storage scope. Bindings are retained in their
/// initialization order; cleanup must consume that order in reverse and may
/// not infer it from a presentation spelling.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceStorageScope {
    pub id: SourceStorageScopeId,
    pub parent: Option<SourceStorageScopeId>,
    pub bindings: Vec<PlaceBindingId>,
}

/// Stable Typed-Core provenance for a lexical storage binding.
///
/// The presentation spelling is deliberately insufficient: an inner `value`
/// must not alias an outer `value`.  The origin records the Core construction
/// which introduced the storage, including a deterministic arm/binder slot
/// for pattern and handler binders.  It is preserved into MIR so later local
/// allocation can join identities without name resolution.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PlaceBindingOrigin {
    Parameter {
        index: u32,
    },
    Let {
        expression: CoreId,
    },
    /// Addressable storage introduced by explicitly borrowing an rvalue.
    Temporary {
        expression: CoreId,
    },
    HandlerBinder {
        handle: CoreId,
        clause: u32,
        binder: u32,
    },
    HandlerResumption {
        handle: CoreId,
        clause: u32,
    },
    CompletionBinder {
        completion: CoreId,
        clause: u32,
        binder: u32,
    },
}

/// Presentation metadata for a [`PlaceBindingId`].  `spelling` is never a
/// lookup key for ownership; it exists solely for diagnostics and tools.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct PlaceBinding {
    pub id: PlaceBindingId,
    pub origin: PlaceBindingOrigin,
    pub spelling: String,
}

/// One node in the canonical move-path tree published by PlaceFlow.
///
/// The root node of a source storage place has no `parent` or `field`; every
/// projected child names the immediately preceding path and the selected
/// field.  Keeping this tree alongside the compact `MoveFact` exit summary
/// lets later MIR cleanup/lowering use stable identities without retaining
/// mutable analyzer state.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MovePathData {
    pub parent: Option<MovePathId>,
    /// The opaque lexical storage root.  This, rather than `root`, is the
    /// ownership identity consumed by later lowering.
    pub binding: PlaceBindingId,
    /// Human-readable source spelling of `binding`.
    pub root: String,
    pub field: Option<u32>,
}

/// Append-only construction arena for canonical owned projection paths.
///
/// It stores each prefix exactly once, so a nested partial move has stable
/// parent identities even when only the leaf remains moved at the body exit.
#[derive(Clone, Debug, Default)]
struct MovePathArena {
    entries: Vec<MovePathData>,
    ids: BTreeMap<Projection, MovePathId>,
}

impl MovePathArena {
    fn intern(&mut self, path: &Projection, binding: PlaceBindingId, root: &str) -> MovePathId {
        if let Some(id) = self.ids.get(path) {
            return *id;
        }

        let (parent, field) = match path.fields.split_last() {
            Some((field, prefix)) => {
                let parent = self.intern(
                    &Projection {
                        root: path.root.clone(),
                        fields: prefix.to_vec(),
                    },
                    binding,
                    root,
                );
                (Some(parent), Some(*field))
            }
            None => (None, None),
        };
        let id = MovePathId(
            u32::try_from(self.entries.len())
                .expect("PlaceFlow move-path arena exceeded the representable identity space"),
        );
        self.entries.push(MovePathData {
            parent,
            binding,
            root: root.to_owned(),
            field,
        });
        self.ids.insert(path.clone(), id);
        id
    }

    fn into_entries(self) -> Vec<MovePathData> {
        self.entries
    }

    fn id(&self, path: &Projection) -> MovePathId {
        *self
            .ids
            .get(path)
            .expect("every final move fact has a recorded move path")
    }
}

/// The analyzer's private name-resolution key is deliberately separate from
/// the frozen identity published to consumers.  Existing transfer/loan maps
/// still use the key while they are incrementally migrated; no frozen fact
/// may expose it.
#[derive(Clone, Debug, Default)]
struct PlaceBindingArena {
    ids: BTreeMap<String, PlaceBindingId>,
    entries: Vec<PlaceBinding>,
}

impl PlaceBindingArena {
    fn intern(
        &mut self,
        identity: &str,
        spelling: &str,
        origin: PlaceBindingOrigin,
    ) -> PlaceBindingId {
        if let Some(id) = self.ids.get(identity) {
            return *id;
        }
        let id = PlaceBindingId(
            u32::try_from(self.entries.len())
                .expect("PlaceFlow binding arena exceeded the representable identity space"),
        );
        self.ids.insert(identity.to_owned(), id);
        self.entries.push(PlaceBinding {
            id,
            origin,
            spelling: spelling.to_owned(),
        });
        id
    }

    fn get(&self, identity: &str) -> Option<PlaceBindingId> {
        self.ids.get(identity).copied()
    }

    fn id(&self, identity: &str) -> PlaceBindingId {
        self.get(identity)
            .expect("every PlaceFlow projection root has a binding identity")
    }

    fn spelling(&self, id: PlaceBindingId) -> &str {
        &self.entries[id.0 as usize].spelling
    }

    fn into_entries(self) -> Vec<PlaceBinding> {
        self.entries
    }
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
    pub binding_keys: Vec<crate::RefinementBindingKey>,
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
    /// Exact manifest-bound abort declaration. This machine leaf has no
    /// cleanup continuation; arbitrary `!` functions do not gain that proof.
    pub(crate) abort_primitive: Option<crate::DefKey>,
    /// Lexical trait assumptions checked with this body, inherited by lifted
    /// callables even when their executable identity differs from the owner.
    pub lexical_bounds: Vec<(Type, crate::ElaboratedTraitReference)>,
    /// Associated rows are part of a generic Fn's checked lexical contract,
    /// not recoverable from its uninstantiated Core callee type alone.
    pub(crate) lexical_effect_bindings: Vec<crate::ElaboratedAssociatedEffectBinding>,
    pub(crate) lexical_universal_bounds: Vec<crate::QuantifiedWhereBound>,
    /// Frozen lexical storage identities referenced by `move_paths`.
    pub bindings: Vec<PlaceBinding>,
    /// Persistent lexical source-storage arena. `binding_scopes` is dense in
    /// `bindings` order and names the exact scope which owns each binding.
    pub storage_scopes: Vec<SourceStorageScope>,
    pub binding_scopes: Vec<SourceStorageScopeId>,
    /// Exact lexical source-storage boundary crossed by each static label
    /// transfer. The key is the branded Core label identity; the pair is
    /// `(source, target)` in source-storage scope space. MIR consumes this
    /// directly while elaborating a `Leave`, rather than attempting to
    /// reconstruct lexical ownership from CFG blocks or local spellings.
    pub label_storage_exits: BTreeMap<crate::LabelBrand, (SourceStorageScopeId, SourceStorageScopeId)>,
    pub final_states: BTreeMap<String, LocalState>,
    /// Projection-granular uninitialized paths. `final_states` remains the
    /// compact whole-local summary for existing consumers; this retains the
    /// information needed for partial moves and aggregate cleanup.
    pub moved_places: Vec<MoveFact>,
    /// The append-only, prefix-closed identity tree for every owned path that
    /// became moved during this body analysis. It is distinct from
    /// `moved_places`, which intentionally retains only final uninitialized
    /// leaves for cleanup.
    pub move_paths: Vec<MovePathData>,
    /// Exact identities for `moved_places` in the same canonical order.  The
    /// legacy facts retain text for diagnostics and VM wire compatibility;
    /// consumers that need ownership identity must use this companion list.
    pub final_move_paths: Vec<MovePathId>,
    pub active_loans: Vec<LoanFact>,
    pub refinements: Vec<RefinementFact>,
    pub events: Vec<FlowEvent>,
    pub diagnostics: Vec<FlowDiagnostic>,
}
impl PlaceFlow {
    pub fn analyze(body: &TypedBody) -> Self {
        Self::analyze_root(body, body.root, &body.parameters, None, &[], &[], None, None)
    }

    /// Analyze against the sealed interface that determined each type's
    /// principal `Use` interval.  A bare value occurrence copies only when
    /// that interval is `[0, infinity]`; every other owned occurrence moves.
    pub fn analyze_with_interface(body: &TypedBody, signatures: &ElaboratedInterface) -> Self {
        Self::analyze_with_interface_and_bounds(body, signatures, &[])
    }

    pub fn analyze_with_interface_and_bounds(
        body: &TypedBody,
        signatures: &ElaboratedInterface,
        bounds: &[(Type, crate::ElaboratedTraitReference)],
    ) -> Self {
        Self::analyze_root(body, body.root, &body.parameters, Some(signatures), bounds, &[], None, None)
    }

    /// Reuse only the immutable rule/layout snapshot from this exact sealed
    /// interface. Each analysis still owns separate proof tables and budgets.
    pub(crate) fn analyze_with_frozen_solver(
        body: &TypedBody,
        signatures: &ElaboratedInterface,
        bounds: &[(Type, crate::ElaboratedTraitReference)],
        effect_bindings: &[crate::ElaboratedAssociatedEffectBinding],
        solver: &crate::TraitSolver,
        abort_primitive: Option<crate::DefKey>,
    ) -> Self {
        Self::analyze_root(body, body.root, &body.parameters, Some(signatures), bounds, effect_bindings, Some(solver), abort_primitive)
    }

    /// Analyze one lifted callable body as an independent storage owner.
    ///
    /// A closure shares the immutable Typed Core arena with its parent, but
    /// its captures and invocation parameters are a new executable ABI. The
    /// resulting dense binding IDs must therefore begin at zero for the child
    /// and may not import parent flow identities.
    pub fn analyze_lifted(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
    ) -> Self {
        Self::analyze_root(body, root, parameters, None, &[], &[], None, None)
    }

    pub fn analyze_lifted_with_interface(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
        signatures: &ElaboratedInterface,
    ) -> Self {
        Self::analyze_lifted_with_interface_and_bounds(body, root, parameters, signatures, &[])
    }

    pub fn analyze_lifted_with_interface_and_bounds(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
        signatures: &ElaboratedInterface,
        bounds: &[(Type, crate::ElaboratedTraitReference)],
    ) -> Self {
        Self::analyze_root(body, root, parameters, Some(signatures), bounds, &[], None, None)
    }

    fn analyze_root(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
        signatures: Option<&ElaboratedInterface>,
        bounds: &[(Type, crate::ElaboratedTraitReference)],
        effect_bindings: &[crate::ElaboratedAssociatedEffectBinding],
        frozen_solver: Option<&crate::TraitSolver>,
        abort_primitive: Option<crate::DefKey>,
    ) -> Self {
        Self::analyze_root_with_captures(body, root, parameters, &[], signatures, bounds,
            effect_bindings, frozen_solver, abort_primitive)
    }

    /// A borrowed capture names its caller-owned referent in Core. Its source
    /// type is not a newly transferred owner and must not acquire a second
    /// destructor or positive-use obligation in the lifted body.
    pub(crate) fn analyze_closure(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
        environment: &crate::core::CaptureEnvironment,
        signatures: Option<&ElaboratedInterface>,
        parent: &PlaceFlow,
        solver: Option<&crate::TraitSolver>,
    ) -> Self {
        let abi = environment.captures.iter()
            .map(|capture| (capture.name.clone(), capture.ty.clone()))
            .chain(parameters.iter().cloned()).collect::<Vec<_>>();
        let modes = environment.captures.iter().map(|capture| capture.mode).collect::<Vec<_>>();
        Self::analyze_root_with_captures(body, root, &abi, &modes, signatures,
            &parent.lexical_bounds, &parent.lexical_effect_bindings, solver, parent.abort_primitive)
    }

    fn analyze_root_with_captures(
        body: &TypedBody,
        root: CoreId,
        parameters: &[(String, Type)],
        capture_modes: &[CaptureMode],
        signatures: Option<&ElaboratedInterface>,
        bounds: &[(Type, crate::ElaboratedTraitReference)],
        effect_bindings: &[crate::ElaboratedAssociatedEffectBinding],
        frozen_solver: Option<&crate::TraitSolver>,
        abort_primitive: Option<crate::DefKey>,
    ) -> Self {
        let mut a = Analyzer {
            body,
            signatures,
            lexical_bounds: bounds,
            lexical_effect_bindings: effect_bindings,
            frozen_solver,
            abort_primitive,
            states: BTreeMap::new(),
            destructor_paths: BTreeSet::new(),
            drop_solver: None,
            ownership_solver: std::cell::OnceCell::new(),
            has_drop_implementations: signatures.is_some_and(|signatures|
                signatures.definitions.values().any(|header| matches!(header,
                    crate::ElaboratedHeader::Implementation(implementation)
                        if !implementation.negative && implementation.relation.definition
                            == crate::resolution::language_drop_trait_definition()))),
            projection_loans: vec![],
            reborrow_parents: BTreeMap::new(),
            reference_origins: BTreeMap::new(),
            logical: LogicalFlow::default(),
            open_referent_holes: BTreeMap::new(),
            moved_places: BTreeSet::new(),
            minimum_bindings: BTreeMap::new(),
            minimum_states: vec![MinimumDisposition::default()],
            minimum_handlers: vec![],
            normal_continuation: true,
            label_continuations: vec![],
            move_paths: MovePathArena::default(),
            bindings: PlaceBindingArena::default(),
            scopes: vec![BTreeMap::new()],
            storage_scopes: vec![SourceStorageScope {
                id: SourceStorageScopeId::ROOT,
                parent: None,
                bindings: vec![],
            }],
            active_storage_scopes: vec![SourceStorageScopeId::ROOT],
            binding_scopes: vec![],
            label_storage_exits: BTreeMap::new(),
            scope_refinement_starts: vec![0],
            ephemeral_borrow_owner: None,
            nonretaining_call_owner: None,
            pending_results: BTreeSet::new(),
            next_shadow: 0,
            events: vec![],
            refinements: vec![],
            diagnostics: vec![],
        };
        for (index, (name, ty)) in parameters.iter().enumerate() {
            let binding = a.bindings.intern(
                name,
                name,
                PlaceBindingOrigin::Parameter {
                    index: u32::try_from(index)
                        .expect("parameter index exceeded PlaceFlow identity space"),
                },
            );
            a.record_storage_binding(binding);
            a.states.insert(name.clone(), LocalState::Initialized);
            a.scopes[0].insert(name.clone(), name.clone());
            if !matches!(capture_modes.get(index), Some(CaptureMode::SharedBorrow | CaptureMode::UniqueBorrow)) {
                a.record_destructor_paths(name, ty);
                a.record_minimum_binding(name, ty, body.expression(root).span);
            }
        }
        // Parameters are caller-owned values, but reference-typed parameter
        // projections still name a stable external loan.  Seed those frozen
        // identities before visiting the body so a call or operation may
        // forward one into its result, and a child reborrow can suspend it,
        // without inventing a body-local backing place.
        a.record_parameter_reference_origins(parameters);
        a.visit_with_live_after(root, &BTreeSet::new());
        a.check_minimum_scope(&a.minimum_bindings.keys().cloned().collect(), body.expression(root).span);
        a.reject_open_referent_holes(
            body.expression(root).span,
            "cannot complete a body while a unique-reference referent is moved out",
        );
        a.diagnostics.sort_by_key(|d| d.span.start);
        let active_loans = a
            .projection_loans
            .iter()
            .filter_map(|loan| {
                // A flow product may retain a conservative temporary/capture
                // provenance entry after the lexical owner that introduced it
                // has gone out of scope.  Such an entry has no source-storage
                // identity, so it cannot become a frozen MIR loan or a VM
                // cleanup obligation.  Keep only live, addressable roots;
                // `end_scope` remains responsible for releasing owned loans.
                a.bindings.get(&loan.place.root).map(|binding| LoanFact {
                    owner: loan.owner.clone(),
                    binding,
                    root: loan.place.root.clone(),
                    fields: loan.place.fields.clone(),
                    unique: loan.unique,
                })
            })
            .collect();
        let final_move_paths = a
            .moved_places
            .iter()
            .map(|place| a.move_paths.id(place))
            .collect::<Vec<_>>();
        let moved_places = a
            .moved_places
            .iter()
            .map(|place| MoveFact {
                root: a.bindings.spelling(a.bindings.id(&place.root)).to_owned(),
                fields: place.fields.clone(),
            })
            .collect();
        Self {
            abort_primitive,
            lexical_bounds: bounds.to_vec(),
            lexical_effect_bindings: effect_bindings.to_vec(),
            lexical_universal_bounds: frozen_solver.map_or_else(Vec::new, |solver| solver.universal_assumptions().to_vec()),
            bindings: a.bindings.into_entries(),
            storage_scopes: a.storage_scopes,
            binding_scopes: a.binding_scopes,
            label_storage_exits: a.label_storage_exits,
            final_states: a.states,
            moved_places,
            move_paths: a.move_paths.into_entries(),
            final_move_paths,
            active_loans,
            refinements: a.refinements,
            events: a.events,
            diagnostics: a.diagnostics,
        }
    }
}
pub(crate) mod regions;
mod control;

#[derive(Clone, Default)]
struct LogicalFlow {
    origins: BTreeMap<String, BTreeSet<regions::Region>>,
    regions: regions::RegionGraph<BTreeSet<ProjectionLoan>>,
}

struct Analyzer<'a> {
    normal_continuation: bool,
    label_continuations: Vec<control::LabelBoundary>,
    body: &'a TypedBody,
    signatures: Option<&'a ElaboratedInterface>,
    lexical_bounds: &'a [(Type, crate::ElaboratedTraitReference)],
    lexical_effect_bindings: &'a [crate::ElaboratedAssociatedEffectBinding],
    frozen_solver: Option<&'a crate::TraitSolver>,
    abort_primitive: Option<crate::DefKey>,
    states: BTreeMap<String, LocalState>,
    /// Places whose eventual source Drop hook can still observe their owned
    /// reference leaves. They add implicit uses at lexical destruction;
    /// moved-out subplaces no longer retain those loans.
    destructor_paths: BTreeSet<Projection>,
    drop_solver: Option<crate::TraitSolver>,
    ownership_solver: std::cell::OnceCell<crate::TraitSolver>,
    has_drop_implementations: bool,
    /// Every precise source loan, including a whole-local loan.  Whole-local
    /// entries are mirrored in `states` for the legacy compact summary.
    projection_loans: Vec<ProjectionLoan>,
    /// Child reference binding -> suspended parent binding.  This is kept
    /// separate from the loan identity because a child may end nonlexically
    /// while the parent loan remains available again.
    reborrow_parents: BTreeMap<String, BTreeSet<String>>,
    /// Provenance outlives one compact active-loan entry.  It is consulted
    /// only when a live descendant proves the parent region remains open.
    reference_origins: BTreeMap<String, BTreeSet<ProjectionLoan>>,
    logical: LogicalFlow,
    /// A direct `move *reference` leaves its unique referent uninitialized
    /// while retaining the reference handle.  The key is the exact lexical
    /// reference binding, never the referent root: a parameter reference may
    /// name caller storage which the local move-path arena cannot represent.
    /// Only `*reference = value` may close this hole.
    open_referent_holes: BTreeMap<String, Span>,
    /// A direct borrow used as an intrinsic operand has no lexical binding,
    /// but it is still live while the intrinsic evaluates.  Keep a synthetic
    /// owner for that short region so the ordinary loan-release path restores
    /// the local immediately after an intrinsic whose result cannot retain a
    /// Grandiose reference.
    ephemeral_borrow_owner: Option<String>,
    /// Anonymous callable operands of a call with a closed, reference-free
    /// result cannot retain their capture loans after that call completes.
    /// This is separate from a let initializer, whose result may escape.
    nonretaining_call_owner: Option<String>,
    /// Computed values remain owned while their enclosing strict expression
    /// evaluates. Their reference leaves must survive arm/block scope exit
    /// and later operands, until the enclosing expression transfers or drops
    /// them. These are analysis temporaries, not lexical source bindings.
    pending_results: BTreeSet<CoreId>,
    /// Canonical paths that have been moved and have not since been
    /// reinitialized. Whole-local moves are mirrored in `states`; field moves
    /// deliberately are not, because their siblings remain usable.
    moved_places: BTreeSet<Projection>,
    minimum_bindings: BTreeMap<String, MinimumBinding>,
    minimum_states: Vec<MinimumDisposition>,
    minimum_handlers: Vec<MinimumHandler>,
    move_paths: MovePathArena,
    bindings: PlaceBindingArena,
    /// Source spellings remain useful in frozen Core diagnostics, while
    /// ownership facts need lexical identities so an inner `let value` does
    /// not alias an outer loan of the same spelling.
    scopes: Vec<BTreeMap<String, String>>,
    /// Persistent counterpart to `scopes`. The mutable name map is still the
    /// analyzer's resolver, while this arena is the artifact-facing lifetime
    /// graph imported by MIR.
    storage_scopes: Vec<SourceStorageScope>,
    active_storage_scopes: Vec<SourceStorageScopeId>,
    binding_scopes: Vec<SourceStorageScopeId>,
    label_storage_exits: BTreeMap<crate::LabelBrand, (SourceStorageScopeId, SourceStorageScopeId)>,
    /// The refinement journal position at each lexical boundary.  Positive
    /// pattern evidence is branch-local evidence, so it must not survive an
    /// arm/block exit merely because it shares a source spelling with an
    /// outer local.
    scope_refinement_starts: Vec<usize>,
    next_shadow: u32,
    events: Vec<FlowEvent>,
    refinements: Vec<RefinementFact>,
    diagnostics: Vec<FlowDiagnostic>,
}

/// Ownership state attached to one control continuation. May-move facts and
/// minimum-use alternatives travel together: neither is a substitute for the
/// other when a branch leaves a scope or rejoins a labelled destination.
#[derive(Clone)]
struct ContinuationState {
    states: BTreeMap<String, LocalState>,
    loans: Vec<ProjectionLoan>,
    moves: BTreeSet<Projection>,
    parents: BTreeMap<String, BTreeSet<String>>,
    origins: BTreeMap<String, BTreeSet<ProjectionLoan>>,
    holes: BTreeMap<String, Span>,
    logical: LogicalFlow,
    minimum: Vec<MinimumDisposition>,
}

impl Analyzer<'_> {
    fn capture_continuation(&self) -> ContinuationState {
        ContinuationState {
            states: self.states.clone(),
            loans: self.projection_loans.clone(),
            moves: self.moved_places.clone(),
            parents: self.reborrow_parents.clone(),
            origins: self.reference_origins.clone(),
            holes: self.open_referent_holes.clone(),
            logical: self.logical.clone(),
            minimum: self.minimum_states.clone(),
        }
    }

    fn restore_continuation(&mut self, state: &ContinuationState) {
        self.normal_continuation = true;
        self.states = state.states.clone();
        self.projection_loans = state.loans.clone();
        self.moved_places = state.moves.clone();
        self.reborrow_parents = state.parents.clone();
        self.reference_origins = state.origins.clone();
        self.open_referent_holes = state.holes.clone();
        self.logical = state.logical.clone();
        self.minimum_states = state.minimum.clone();
    }

    fn record_destructor_paths(&mut self, owner: &str, ty: &Type) {
        let paths = self.drop_observation_paths(ty, &mut BTreeSet::new());
        self.destructor_paths.extend(paths.into_iter().map(|fields| Projection {
            root: owner.to_owned(), fields,
        }));
    }

    fn drop_observation_paths(&mut self, ty: &Type, active: &mut BTreeSet<crate::DefKey>) -> Vec<Vec<u32>> {
        if !self.has_drop_implementations { return vec![]; }
        let Some(signatures) = self.signatures else { return vec![]; };
        let layouts = match ty {
            Type::Reference { .. } | Type::RawPointer { .. } | Type::Callable { .. } => return vec![],
            Type::Generic(_) | Type::Projection { .. } => return vec![vec![]],
            Type::Nominal { definition, arguments } => {
                if !active.insert(*definition) { return vec![vec![]]; }
                if self.custom_drop_may_apply(ty) {
                    active.remove(definition);
                    return vec![vec![]];
                }
                let layouts = match signatures.definitions.get(definition) {
                    Some(crate::ElaboratedHeader::Nominal { layout, .. }) =>
                        crate::mir::instantiate_nominal_copy_layout(layout, arguments).unwrap_or_default(),
                    _ => vec![],
                };
                layouts
            }
            Type::Tuple(fields) => vec![fields.clone()],
            Type::Array(element) | Type::FixedArray { element, .. } => return if self.drop_observation_paths(element, active).is_empty() {
                vec![]
            } else { vec![vec![]] },
            _ => return vec![],
        };
        let mut paths = BTreeSet::new();
        for fields in layouts {
            for (index, ty) in fields.iter().enumerate() {
                for mut path in self.drop_observation_paths(ty, active) {
                    path.insert(0, index as u32);
                    paths.insert(path);
                }
            }
        }
        if let Type::Nominal { definition, .. } = ty { active.remove(definition); }
        paths.into_iter().collect()
    }

    fn loan_is_used_by_destruction(&self, owner: &str) -> bool {
        self.destructor_paths.iter().any(|place| {
            let key = projection_key(&place.root, &place.fields);
            self.states.contains_key(&place.root)
                && (owner == key || owner.starts_with(&(key + ".")))
                && !self.origin_has_been_moved(owner)
        })
    }

    /// A successful pattern selects a concrete variant. Its residual cleanup
    /// must not observe fields belonging only to another variant, even when
    /// those unrelated fields reuse the same numeric payload indices.
    fn selected_drop_observation_paths(&mut self, ty: &Type, pattern: &CorePattern) -> Vec<Vec<u32>> {
        let all = self.drop_observation_paths(ty, &mut BTreeSet::new());
        if all.is_empty() || all.iter().any(Vec::is_empty) { return all; }
        let fields = match (ty, pattern) {
            (Type::Tuple(fields), CorePattern::Tuple(_)) => fields.clone(),
            (Type::Nominal { definition, arguments }, CorePattern::Enum { definition: selected, variant, .. })
                if definition == selected => {
                let Some(crate::ElaboratedHeader::Nominal { layout, .. }) = self.signatures
                    .and_then(|signatures| signatures.definitions.get(definition)) else { return all; };
                let Some(layouts) = crate::mir::instantiate_nominal_copy_layout(layout, arguments) else { return all; };
                let Some(fields) = layouts.get(*variant as usize) else { return all; };
                fields.clone()
            }
            (Type::Nominal { definition, arguments }, CorePattern::Record { definition: selected, .. })
                if definition == selected => {
                let Some(crate::ElaboratedHeader::Nominal { layout, .. }) = self.signatures
                    .and_then(|signatures| signatures.definitions.get(definition)) else { return all; };
                let Some(layouts) = crate::mir::instantiate_nominal_copy_layout(layout, arguments) else { return all; };
                let Some(fields) = layouts.first() else { return all; };
                fields.clone()
            }
            _ => return all,
        };
        let mut paths = vec![];
        for (index, ty) in fields.iter().enumerate() {
            let nested = match pattern {
                CorePattern::Tuple(patterns) => patterns.get(index),
                CorePattern::Enum { fields, .. } | CorePattern::Record { fields, .. } =>
                    fields.iter().find(|field| field.index as usize == index).map(|field| &field.pattern),
                _ => None,
            };
            let observed = match nested {
                Some(pattern) => self.selected_drop_observation_paths(ty, pattern),
                None => self.drop_observation_paths(ty, &mut BTreeSet::new()),
            };
            for mut path in observed {
                path.insert(0, index as u32);
                paths.push(path);
            }
        }
        paths
    }

    fn origin_has_been_moved(&self, owner: &str) -> bool {
        self.moved_places.iter().any(|moved| {
            let moved = projection_key(&moved.root, &moved.fields);
            owner == moved || owner.starts_with(&(moved + "."))
        })
    }

    fn origin_loans(&self, owner: &str) -> BTreeSet<ProjectionLoan> {
        let active = self.projection_loans.iter()
            .filter(|loan| loan.owner.as_deref() == Some(owner)).cloned().collect::<BTreeSet<_>>();
        if !active.is_empty() { return active; }
        let mut origins = self.reference_origins.get(owner).cloned().unwrap_or_default();
        let Some((root, _)) = owner.split_once('.') else { return origins; };
        let prefix = format!("{root}.");
        let selected = owner.split('.').collect::<Vec<_>>();
        let wildcard = crate::core::REFERENCE_PATH_ARRAY_ELEMENT.to_string();
        for (key, loans) in self.reference_origins.range(prefix.clone()..)
            .take_while(|(key, _)| key.starts_with(&prefix)) {
            if key == owner { continue; }
            let pattern = key.split('.').collect::<Vec<_>>();
            if pattern.len() != selected.len() { continue; }
            if !pattern.iter().zip(&selected).all(|(left, right)|
                left == right || left.parse::<u32>().ok().zip(right.parse::<u32>().ok())
                    .is_some_and(|(left, right)| crate::core::reference_path_matches(&[left], &[right]))) {
                continue;
            }
            let selected_indices = pattern.iter().zip(&selected)
                .filter_map(|(left, right)| (*left == wildcard && *right != wildcard)
                    .then(|| right.parse::<u32>().ok()).flatten()).collect::<Vec<_>>();
            for mut loan in loans.iter().cloned() {
                // A selected unique result element is a distinct leaf of the
                // already checked result, even though its frozen contract
                // represented all elements with one symbolic component.
                for fields in loan.partitions.values_mut() {
                    let mut indices = selected_indices.iter();
                    for field in fields {
                        if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT
                            && let Some(index) = indices.next() { *field = *index; }
                    }
                }
                if loan.indirect && pattern.first().is_some_and(|root| *root == loan.place.root) {
                    let fields = selected.iter().skip(1).map(|field| field.parse::<u32>()).collect::<Result<Vec<_>, _>>();
                    if let Ok(fields) = fields
                        && crate::core::reference_path_matches(&loan.place.fields, &fields) {
                        loan.place.fields = fields;
                    }
                }
                origins.insert(loan);
            }
        }
        origins
    }

    fn captured_origin_loans(&self, owner: &str) -> BTreeSet<ProjectionLoan> {
        let prefix = format!("{owner}.");
        self.reference_origins.iter().filter(|(key, _)| key.as_str() == owner || key.starts_with(&prefix))
            .flat_map(|(_, loans)| loans.iter().cloned())
            .chain(self.projection_loans.iter().filter(|loan| loan.owner.as_ref()
                .is_some_and(|key| key == owner || key.starts_with(&prefix))).cloned()).collect()
    }

    fn reference_ancestors(&self, owner: &str) -> BTreeSet<String> {
        let mut pending = vec![owner.to_owned()];
        let mut seen = BTreeSet::new();
        while let Some(owner) = pending.pop() {
            if !seen.insert(owner.clone()) { continue; }
            if let Some(parents) = self.reborrow_parents.get(&owner) {
                pending.extend(parents.iter().cloned());
            }
        }
        seen
    }

    fn record_parameter_reference_origins(&mut self, abi: &[(String, Type)]) {
        // A wrapper may forward a hidden reference field without projecting
        // that field in this body at all (Slice::get_unchecked is one such
        // wrapper). Seed the ABI's structurally proven leaves, using the same
        // frozen layout traversal that establishes call reference contracts.
        // Do not infer a loan merely because a call claims an argument path.
        // Opaque/ambiguous layouts remain closed, including the no-interface
        // analysis entry points; their explicit reference projections below
        // continue to work as before.
        let empty = ElaboratedInterface::default();
        let signatures = self.signatures.unwrap_or(&empty);
        for (name, ty) in abi {
            let mut leaves = vec![];
            if crate::core::reference_leaf_paths(signatures, ty, &mut vec![], &mut leaves).is_err() && leaves.is_empty() {
                continue;
            }
            for (fields, ty) in leaves {
                let Type::Reference { mutability, .. } = ty else {
                    unreachable!("reference layout traversal only yields references");
                };
                let key = projection_key(name, &fields);
                let loans = self.reference_origins.entry(key.clone()).or_insert_with(|| BTreeSet::from([ProjectionLoan {
                    place: Projection { root: name.clone(), fields: fields.clone() },
                    unique: matches!(mutability, crate::types::Mutability::Unique),
                    owner: None,
                    partitions: BTreeMap::new(),
                    indirect: true,
                    external: false,
                }])).clone();
                if crate::core::reference_path_is_logical(&fields) {
                    let region = regions::Region { site: name.clone(), path: fields };
                    self.logical.origins.insert(key, BTreeSet::from([region.clone()]));
                    self.logical.regions.insert(region, loans, |loans, incoming| loans.extend(incoming));
                }
            }
        }
        let parameters = abi
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<BTreeSet<_>>();
        for index in 0..self.body.expressions.len() {
            let id = CoreId(index as u32);
            let Some(place) = self.projection(id) else {
                continue;
            };
            if !parameters.contains(place.root.as_str()) {
                continue;
            }
            let Type::Reference { mutability, .. } = &self.body.expression(id).ty else {
                continue;
            };
            let key = projection_key(&place.root, &place.fields);
            self.reference_origins
                .entry(key)
                .or_insert_with(|| BTreeSet::from([ProjectionLoan {
                    place,
                    unique: matches!(mutability, crate::types::Mutability::Unique),
                    owner: None,
                    partitions: BTreeMap::new(),
                    indirect: true,
                    external: false,
                }]));
        }
    }

    fn resolve_name(&self, name: &str) -> String {
        self.scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name))
            .cloned()
            .unwrap_or_else(|| name.to_owned())
    }

    fn reserve_binding(&mut self, name: &str) -> String {
        if self
            .scopes
            .iter()
            .rev()
            .any(|scope| scope.contains_key(name))
        {
            let identity = format!("{name}#{}", self.next_shadow);
            self.next_shadow = self.next_shadow.saturating_add(1);
            identity
        } else {
            name.to_owned()
        }
    }

    fn activate_binding(&mut self, spelling: &str, identity: String, origin: PlaceBindingOrigin) {
        let binding = self.bindings.intern(&identity, spelling, origin);
        self.record_storage_binding(binding);
        self.scopes
            .last_mut()
            .expect("PlaceFlow always has a root lexical scope")
            .insert(spelling.to_owned(), identity);
    }

    fn record_storage_binding(&mut self, binding: PlaceBindingId) {
        let scope = *self
            .active_storage_scopes
            .last()
            .expect("PlaceFlow always has a root source-storage scope");
        let index = binding.0 as usize;
        if self.binding_scopes.len() == index {
            self.binding_scopes.push(scope);
        } else {
            // PlaceFlow may revisit the same lexical Core construction while
            // summarizing alternative handler/branch paths.  The binding is
            // still one source-storage owner: retain the scope assigned on
            // its first construction rather than treating the later
            // analysis-only branch scope as a second owner.
            return;
        }
        self.storage_scopes[scope.0 as usize].bindings.push(binding);
    }

    fn fresh_binding(&mut self, name: &str) -> String {
        let identity = format!("{name}#{}", self.next_shadow);
        self.next_shadow = self.next_shadow.saturating_add(1);
        identity
    }

    fn begin_scope(&mut self) {
        self.scopes.push(BTreeMap::new());
        self.scope_refinement_starts.push(self.refinements.len());
        let parent = *self
            .active_storage_scopes
            .last()
            .expect("PlaceFlow always has a root source-storage scope");
        let id = SourceStorageScopeId(
            u32::try_from(self.storage_scopes.len())
                .expect("PlaceFlow source-storage arena exceeded identity space"),
        );
        self.storage_scopes.push(SourceStorageScope {
            id,
            parent: Some(parent),
            bindings: vec![],
        });
        self.active_storage_scopes.push(id);
    }

    fn end_scope(&mut self, span: Span) {
        let storage_scope = self.active_storage_scopes
            .pop()
            .expect("nested PlaceFlow source-storage scope");
        self.scopes.pop().expect("nested PlaceFlow scope");
        let refinement_start = self
            .scope_refinement_starts
            .pop()
            .expect("refinement journal follows PlaceFlow scopes");
        self.refinements.truncate(refinement_start);
        // The spelling map keeps only the newest shadow. Cleanup must end
        // every binding in this scope, including hidden earlier owners.
        let locals = self.bindings.ids.iter().filter(|(_, binding)|
            self.binding_scopes[binding.0 as usize] == storage_scope)
            .map(|(identity, _)| identity.clone()).collect::<BTreeSet<_>>();
        self.end_minimum_scope(storage_scope, span);
        let escaping = self.projection_loans.iter().any(|loan|
            !loan.indirect && locals.contains(&loan.place.root) && loan.owner.as_ref().is_some_and(|owner|
                !belongs_to_scope(&locals, owner) || self.pending_results.iter().any(|id| {
                    let result = Self::result_owner(*id);
                    owner == &result || owner.starts_with(&(result + "."))
                })));
        if escaping {
            self.error(span, "G5013", "computed value retains a borrow of storage destroyed at this scope exit".into());
        }
        let holes = self
            .open_referent_holes
            .keys()
            .filter(|reference| belongs_to_scope(&locals, reference))
            .cloned()
            .collect::<Vec<_>>();
        for reference in holes {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot leave the scope of unique reference `{reference}` while its referent is uninitialized"
                ),
            );
            self.open_referent_holes.remove(&reference);
        }
        let owners = self
            .projection_loans
            .iter()
            .filter_map(|loan| loan.owner.as_deref())
            .filter(|owner| belongs_to_scope(&locals, owner))
            .map(str::to_owned)
            .collect::<BTreeSet<_>>();
        for owner in owners {
            self.release_owner_loans(&owner, span);
        }
        self.states.retain(|name, _| !locals.contains(name));
        self.destructor_paths.retain(|place| !locals.contains(&place.root));
        self.projection_loans.retain(|loan| {
            !locals.contains(&loan.place.root)
                && !loan
                    .owner
                    .as_ref()
                    .is_some_and(|owner| belongs_to_scope(&locals, owner))
        });
        self.moved_places
            .retain(|place| !locals.contains(&place.root));
        self.reborrow_parents.retain(|child, parents| {
            parents.retain(|parent| !belongs_to_scope(&locals, parent));
            !belongs_to_scope(&locals, child) && !parents.is_empty()
        });
        self.reference_origins.retain(|name, loans| {
            loans.retain(|loan| !locals.contains(&loan.place.root) && !loan
                    .owner
                    .as_ref()
                    .is_some_and(|owner| belongs_to_scope(&locals, owner)));
            !belongs_to_scope(&locals, name) && !loans.is_empty()
        });
        self.logical.origins.retain(|name, _| !belongs_to_scope(&locals, name));
    }

    fn activate_branch_bindings<'b>(
        &mut self,
        bindings: impl IntoIterator<Item = &'b (String, crate::types::Type)>,
        resumption: Option<&str>,
        mut origin: impl FnMut(u32) -> PlaceBindingOrigin,
        resumption_origin: Option<PlaceBindingOrigin>,
    ) {
        for (index, (name, ty)) in bindings.into_iter().enumerate() {
            let identity = self.fresh_binding(name);
            self.activate_binding(
                name,
                identity.clone(),
                origin(u32::try_from(index).expect("branch binder index exceeded identity space")),
            );
            self.record_destructor_paths(&identity, ty);
            self.record_minimum_binding(&identity, ty, self.body.expression(self.body.root).span);
            self.states.insert(identity, LocalState::Initialized);
        }
        if let Some(name) = resumption {
            let identity = self.fresh_binding(name);
            self.activate_binding(
                name,
                identity.clone(),
                resumption_origin.expect("resumption binding must have typed-core provenance"),
            );
            self.states.insert(identity, LocalState::Initialized);
        }
    }

    fn visit_scoped_sequence(&mut self, id: CoreId, values: &[CoreId], live_after: &BTreeSet<String>) {
        self.begin_scope();
        self.visit_sequence_with_discarded_prefix(values, live_after, true);
        if let Some(tail) = values.last() {
            self.preserve_expression_result(id, *tail);
        }
        self.end_scope(self.body.expression(self.body.root).span);
    }

    fn result_owner(id: CoreId) -> String { format!("<expression-result-{}>", id.0) }

    fn preserve_expression_result(&mut self, id: CoreId, source: CoreId) {
        let owner = Self::result_owner(id);
        self.record_aggregate_reference_origins(&owner, source);
        if self.reference_origins.keys().chain(self.logical.origins.keys())
            .any(|key| key == &owner || key.starts_with(&(owner.clone() + "."))) {
            self.pending_results.insert(id);
        }
    }

    fn release_expression_results(&mut self, incoming: &BTreeSet<CoreId>, keep: Option<CoreId>, span: Span) {
        let consumed = self.pending_results.iter().filter(|id| !incoming.contains(id) && Some(**id) != keep)
            .copied().collect::<Vec<_>>();
        for id in consumed {
            self.release_result_loans(id, span);
            self.pending_results.remove(&id);
        }
    }

    fn release_result_loans(&mut self, id: CoreId, span: Span) {
        let root = Self::result_owner(id);
        let owners = self.projection_loans.iter().filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| **owner == root || owner.starts_with(&(root.clone() + ".")))
            .cloned().collect::<BTreeSet<_>>();
        for owner in owners { self.release_owner_loans(&owner, span); }
        self.logical.origins.retain(|owner, _| *owner != root && !owner.starts_with(&(root.clone() + ".")));
    }

    fn release_unobserved_result_loans(&mut self, id: CoreId, observed: &[Vec<u32>], span: Span) {
        let root = Self::result_owner(id);
        let observed = observed.iter().map(|fields| projection_key(&root, fields)).collect::<Vec<_>>();
        let owners = self.projection_loans.iter().filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| **owner == root || owner.starts_with(&(root.clone() + ".")))
            .filter(|owner| !observed.iter().any(|path| *owner == path
                || owner.starts_with(&(path.clone() + "."))
                || path.starts_with(&((*owner).clone() + "."))))
            .cloned().collect::<BTreeSet<_>>();
        for owner in owners { self.release_owner_loans(&owner, span); }
    }

    /// Visit an expression while retaining only loans whose owner may be used
    /// by the continuation.  This is the first NLL region domain: a `let r =
    /// &place` loan lasts to the last value use of `r`, rather than to body
    /// exit.  Dynamic handler exits receive the same continuation set and are
    /// joined conservatively below.
    fn visit_with_live_after(&mut self, id: CoreId, live_after: &BTreeSet<String>) {
        let incoming_results = self.pending_results.clone();
        self.visit_expression(id, live_after);
        if self.pending_results != incoming_results && !self.pending_results.contains(&id) {
            self.preserve_expression_result(id, id);
        }
        self.release_expression_results(&incoming_results, Some(id), self.body.expression(id).span);
        self.release_dead_loans(live_after, self.body.expression(id).span);
    }

    fn visit_expression(&mut self, id: CoreId, live_after: &BTreeSet<String>) {
        let e = self.body.expression(id).clone();
        match e.kind {
            CoreKind::ConstValue(_) => {},
            CoreKind::Literal(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error => {}
            CoreKind::Closure { environment, .. } => {
                let owner = self.nonretaining_call_owner.clone();
                self.visit_closure_environment(&environment, e.span, owner.as_deref());
            }
            // Ordinary value occurrences are owned by default.  The sealed
            // principal `Use` interval is the authority for whether that
            // ownership transfer is a copy or a move; `[0, 0]` only permits
            // discarding and must not accidentally make a value duplicable.
            CoreKind::Local(_) => {
                if let Type::Reference { mutability, .. } = &e.ty {
                    self.use_deref_reference(id, e.span, matches!(mutability, crate::Mutability::Unique));
                }
                if self.is_duplicable(&e.ty) {
                    self.read_place(id, e.span);
                } else if self.ordinary_value_moves_place(&e.ty) {
                    self.move_place(id, e.span);
                } else {
                    // Standalone PlaceFlow unit tests construct Core without
                    // an interface. Preserve their observation-only legacy
                    // mode; executable compilation always supplies one.
                    self.read_place(id, e.span);
                }
            }
            CoreKind::Label { brand, body } => {
                self.enter_label_continuation(brand);
                // Labels are control boundaries, but their body is also a
                // lexical storage region. Capture that region at analysis
                // time while Core still tells us exactly which branded label
                // owns it. Later MIR cleanup can therefore cross the real
                // `source -> target` storage boundary without guessing from
                // a block number or local spelling.
                let target = *self
                    .active_storage_scopes
                    .last()
                    .expect("PlaceFlow always has a root source-storage scope");
                let next_scope = SourceStorageScopeId(
                    u32::try_from(self.storage_scopes.len())
                        .expect("PlaceFlow source-storage arena exceeded the representable identity space"),
                );
                let body_opens_scope = matches!(
                    self.body.expression(body).kind,
                    CoreKind::Block(_)
                ) && body != self.body.root;
                self.visit_with_live_after(body, live_after);
                let source = (body_opens_scope
                    && self
                        .storage_scopes
                        .get(next_scope.0 as usize)
                        .is_some_and(|scope| scope.parent == Some(target)))
                    .then_some(next_scope)
                    .unwrap_or(target);
                self.label_storage_exits.insert(brand, (source, target));
                self.finish_label_continuation(brand, e.span);
            }
            CoreKind::Transfer { brand, value } => {
                self.visit_with_live_after(value, live_after);
                if self.normal_continuation { self.record_label_continuation(brand, e.span); }
            }
            CoreKind::Let { name, value } => {
                // A strict initializer which transfers out or evaluates to
                // `Never` never creates the lexical owner. In particular,
                // reserving the binding before the initializer would let a
                // forged post-transfer suffix retarget later PlaceFlow facts
                // through a local that cannot exist at runtime.
                if Self::abrupt_exit(self.body, value).is_some() {
                    self.visit_with_live_after(value, live_after);
                    return;
                }
                let binding = self.reserve_binding(&name);
                let initializer_owner = format!("<let-initializer-{}>", id.0);
                let previous_ephemeral = self.ephemeral_borrow_owner.replace(initializer_owner.clone());
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
                    if let Some(reference) = self.reborrow_reference(value) {
                        self.visit_reference_handle(reference, &borrow_live);
                    } else if self.projection(value).is_some() {
                        self.read_place(value, self.body.expression(value).span);
                    } else {
                        self.visit_with_live_after(borrowed_place_base(self.body, value), &borrow_live);
                    }
                    if !self.reborrow_place(value, unique, e.span, binding.clone()) {
                        self.borrow_place(value, unique, e.span, Some(binding.clone()));
                    }
                } else if let CoreKind::Closure { environment, .. } =
                    self.body.expression(value).kind.clone()
                {
                    // A closure bound to a local has a concrete region owner.
                    // Keep both its direct capture loans and any reborrowed
                    // backing loans only until that callable's last use,
                    // including when the binding was created in a handler
                    // arm. Bare closure expressions still use `None` below:
                    // they may be returned, passed, or otherwise escape.
                    self.visit_closure_environment(&environment, e.span, Some(binding.as_str()));
                } else {
                    self.visit_with_live_after(value, live_after);
                }
                // Resolve initializer origins in the old lexical environment:
                // `let value = value` must refer to the hidden previous owner.
                self.record_aggregate_reference_origins(&binding, value);
                // A moved reference-bearing initializer has transferred its
                // loans to the new binding. Vacant source fields must not
                // survive as competing children of the same backing loan.
                self.release_vacated_reference_loans(e.span);
                self.release_owner_loans(&initializer_owner, e.span);
                self.ephemeral_borrow_owner = previous_ephemeral;
                self.activate_binding(
                    &name,
                    binding.clone(),
                    PlaceBindingOrigin::Let { expression: id },
                );
                self.record_destructor_paths(&binding, &self.body.expression(value).ty.clone());
                self.record_minimum_binding(&binding, &self.body.expression(value).ty.clone(), e.span);
                self.states.insert(binding.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(binding), e.span)
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
                // The destination is evaluated only after a normally
                // completed RHS. A terminal RHS or escaping label transfer
                // must not reinitialize a moved place, consume a destination
                // loan, or record reference provenance on an unreachable
                // store edge.
                if Self::abrupt_exit(self.body, value).is_some() {
                    return;
                }
                if let CorePlace::Deref { reference, .. } = &place {
                    self.restore_whole_referent_hole(&place, e.span);
                    // The capability may itself be computed (a call, block,
                    // or completion). Evaluate it without moving a static
                    // reference carrier, and retain its result loan through
                    // the store just as for an ordinary dereference.
                    self.visit_reference_handle(*reference, live_after);
                    if Self::abrupt_exit(self.body, *reference).is_some() {
                        return;
                    }
                    self.use_deref_reference(*reference, e.span, true);
                } else {
                    let mut destination = &place;
                    let mut fields = vec![];
                    while let CorePlace::Field { base, index, .. } = destination {
                        fields.push(*index);
                        destination = base;
                    }
                    if let CorePlace::Deref { reference, .. } = destination {
                        fields.reverse();
                        self.visit_reference_handle(*reference, live_after);
                        if Self::abrupt_exit(self.body, *reference).is_some() {
                            return;
                        }
                        self.use_projected_deref_reference(*reference, &fields, e.span, true);
                    }
                }
                self.assign_place(&place, e.span);
                self.record_assigned_reference_origin(&place, value);
            }
            CoreKind::Move(v) => {
                if !self.open_whole_referent_hole(v, e.span) {
                    // A move of a static place is validated directly. Visiting a
                    // field first would turn a second move into an unrelated
                    // read-after-move diagnostic and obscure the precise path
                    // being consumed.
                    if self.projection(v).is_none() {
                        self.visit_with_live_after(v, live_after);
                    }
                    self.move_place(v, e.span)
                }
            }
            CoreKind::ReleaseAvailable(value) => {
                if e.ty != Type::Unit || !crate::core::available_release_is_authorized(
                    &self.body.expression(value).ty, self.lexical_bounds,
                ) {
                    self.error(e.span, "G4188", "available release lacks its exact Environment and affine erasure contracts".into());
                }
                self.visit_with_live_after(value, live_after);
            }
            CoreKind::IntrinsicCall { arguments, .. } => {
                // Runtime intrinsics are manifest leaves: their values are
                // scalar/aggregate Grandiose values, never a reference whose
                // region could escape into later Core.  A direct `&mut local`
                // operand therefore has precisely this call's lifetime.
                // Model it as an ordinary owned loan, rather than leaving the
                // compact LocalState permanently uniquely borrowed.
                let owner = format!("<temporary-intrinsic-{}>", id.0);
                let previous = self.ephemeral_borrow_owner.replace(owner.clone());
                self.visit_sequence(&arguments, live_after);
                self.release_owner_loans(&owner, e.span);
                self.ephemeral_borrow_owner = previous;
            }
            CoreKind::Borrow { unique, value } => {
                if let Some(reference) = self.reborrow_reference(value) {
                    self.visit_reference_handle(reference, live_after);
                } else if self.projection(value).is_none() {
                    self.visit_with_live_after(borrowed_place_base(self.body, value), live_after);
                }
                if Self::abrupt_exit(self.body, value).is_some() {
                    return;
                }
                let owner = Self::result_owner(id);
                if !self.reborrow_place(value, unique, e.span, owner.clone()) {
                    self.borrow_place(value, unique, e.span, Some(owner.clone()));
                }
                if self.reference_origins.contains_key(&owner) { self.pending_results.insert(id); }
            }
            CoreKind::Deref(value) => {
                // Dereferencing uses a reference capability; it does not
                // transfer ownership of that reference. In particular an
                // `&mut T` remains usable for later reborrows.
                self.visit_reference_handle(value, live_after);
                self.use_deref_reference(value, e.span, false);
                if self.signatures.is_some() && !self.is_duplicable(&e.ty) {
                    self.error(e.span, "G5004", "an owned value use cannot copy a non-Copy referent; borrow it or explicitly move and restore it".into());
                }
            }
            CoreKind::Call {
                callee,
                arguments,
                reference_shape,
                ..
            } => {
                let logical_arguments = arguments.clone();
                let operands_complete = Self::abrupt_exit(self.body, callee).is_none()
                    && arguments.iter().all(|argument| Self::abrupt_exit(self.body, *argument).is_none());
                self.reject_opaque_reference_result(reference_shape, &e.ty, e.span, "call");
                if let CoreKind::Closure { environment, .. } =
                    self.body.expression(callee).kind.clone()
                {
                    // An immediately-invoked closure has no outward value
                    // owner. Give its environment a transient NLL owner that
                    // remains live across argument evaluation and the call,
                    // then release it before the following expression.
                    let owner = format!("<temporary-closure-{}>", callee.0);
                    let mut during_call = live_after.clone();
                    during_call.insert(owner.clone());
                    self.visit_closure_environment(&environment, e.span, Some(owner.as_str()));
                    self.visit_sequence(&arguments, &during_call);
                    if operands_complete && self.normal_continuation { self.record_captured_call_stores(callee, Some(&owner), id); }
                    self.release_owner_loans(&owner, e.span);
                } else {
                    if matches!(reference_shape, CallReferenceShape::None) {
                        // The sealed call result proves it cannot retain an
                        // operand reference.  This covers manifest-bound
                        // runtime leaves, which elaborate as ordinary Core
                        // calls rather than CoreKind::IntrinsicCall.
                        let owner = format!("<temporary-call-{}>", id.0);
                        let previous = self.ephemeral_borrow_owner.replace(owner.clone());
                        let previous_capture = self.nonretaining_call_owner.clone();
                        if self.result_has_no_capture_carriers(&e.ty, &mut BTreeSet::new()) {
                            self.nonretaining_call_owner = Some(owner.clone());
                        }
                        let mut during_call = live_after.clone();
                        during_call.insert(owner.clone());
                        self.visit_call_operands(callee, &arguments, &during_call);
                        self.release_owner_loans(&owner, e.span);
                        self.ephemeral_borrow_owner = previous;
                        self.nonretaining_call_owner = previous_capture;
                    } else {
                        self.visit_call_operands(callee, &arguments, live_after);
                    }
                }
                if operands_complete && self.normal_continuation {
                    self.record_logical_call_stores(callee, &logical_arguments, id);
                    self.record_captured_call_stores(callee, None, id);
                    if self.minimum_definitely_aborts(id) { self.minimum_states.clear(); }
                    else { self.check_minimum_call_suspensions(callee, &arguments, e.span); }
                }
            }
            CoreKind::Perform {
                arguments,
                reference_shape,
                effect,
                operation,
                ..
            } => {
                self.reject_open_referent_holes(
                    e.span,
                    "cannot perform an effect while a unique-reference referent is moved out",
                );
                self.reject_opaque_reference_result(
                    reference_shape,
                    &e.ty,
                    e.span,
                    "effect operation",
                );
                self.visit_sequence(&arguments, live_after);
                if arguments.iter().all(|argument| Self::abrupt_exit(self.body, *argument).is_none()) {
                    self.check_minimum_suspension(&effect, operation, e.span);
                }
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.reject_open_referent_holes(
                    e.span,
                    "cannot enter a handler while a unique-reference referent is moved out",
                );
                let mut inside_handler = live_after.clone();
                for clause in &clauses {
                    self.collect_local_uses(clause.body, &mut inside_handler);
                }
                // A matching payload binder may reborrow a reference carried
                // by this suspension.  Retain its caller loan through the
                // dynamic handler boundary even though the source argument's
                // spelling is not visible inside the arm.
                self.collect_local_uses(computation, &mut inside_handler);
                self.enter_minimum_handler(&clauses);
                self.visit_pattern_subject(computation, &inside_handler, e.span);
                let minimum_handler = self.minimum_handlers.pop().expect("active minimum-use handler");
                if !self.normal_continuation { return; }
                let incoming_state = self.capture_continuation();
                let incoming = incoming_state.states.clone();
                let incoming_refinements = self.refinements.clone();
                let incoming_minimum = self.minimum_states.clone();
                let mut exits = if self.minimum_handler_completes_normally(computation, &clauses) {
                    vec![incoming_state.clone()]
                } else { vec![] };
                for (clause_index, clause) in clauses.into_iter().enumerate() {
                    self.restore_continuation(&incoming_state);
                    self.refinements = incoming_refinements.clone();
                    self.minimum_states = self.minimum_clause_inputs(&minimum_handler, &clause, &incoming_minimum);
                    let transfers = self.handler_payload_transfers(computation, &clause);
                    self.begin_scope();
                    let resumption = match &clause.resumption {
                        crate::core::CoreHandlerResumption::Explicit { name, .. } => {
                            Some(name.as_str())
                        }
                        _ => None,
                    };
                    let clause_index = u32::try_from(clause_index)
                        .expect("handler clause index exceeded PlaceFlow identity space");
                    self.activate_branch_bindings(
                        &clause.bindings,
                        resumption,
                        |binder| PlaceBindingOrigin::HandlerBinder {
                            handle: id,
                            clause: clause_index,
                            binder,
                        },
                        resumption.map(|_| PlaceBindingOrigin::HandlerResumption {
                            handle: id,
                            clause: clause_index,
                        }),
                    );
                    self.install_pattern_transfers(transfers);
                    self.check_custom_drop_payload_patterns(&clause);
                    self.open_minimum_payload_patterns(&clause);
                    let arm_results = self.pending_results.clone();
                    self.visit_with_live_after(clause.body, live_after);
                    self.preserve_expression_result(id, clause.body);
                    self.release_expression_results(&arm_results, Some(id), clause.span);
                    // A dynamically selected arm may update outer places,
                    // but neither its payload nor continuation identity may
                    // become an outer post-state fact.
                    self.end_scope(clause.span);
                    if self.normal_continuation { exits.push(self.capture_continuation()); }
                }
                self.normal_continuation = !exits.is_empty();
                if self.normal_continuation {
                    self.join_continuation_states(&exits, &incoming, e.span);
                    self.refinements = incoming_refinements;
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
                refinement_test,
                ..
            } => {
                if let Some(environment) = &refinement_test {
                    self.refinements.push(RefinementFact { brand: environment.brand, subject: environment.subject.clone(),
                        bindings: environment.bindings.clone(), binding_keys: environment.binding_keys.clone(), span: e.span });
                }
                let mut inside_completion = live_after.clone();
                for clause in &clauses {
                    self.collect_local_uses(clause.body, &mut inside_completion);
                }
                // Completion binders can project a reference returned by a
                // performed operation or call. Keep its source argument live
                // while the result is structurally bound into the arm.
                self.collect_local_uses(computation, &mut inside_completion);
                let subject_owner = format!("<completion-subject-{}>", id.0);
                inside_completion.insert(subject_owner.clone());
                let previous_ephemeral = self.ephemeral_borrow_owner.replace(subject_owner.clone());
                self.visit_pattern_subject(computation, &inside_completion, e.span);
                self.ephemeral_borrow_owner = previous_ephemeral;
                if !self.normal_continuation { return; }
                let incoming_state = self.capture_continuation();
                let incoming = incoming_state.states.clone();
                let incoming_refinements = self.refinements.clone();
                let incoming_minimum = self.minimum_states.clone();
                let mut exits = Vec::with_capacity(clauses.len());
                for (clause_index, clause) in clauses.into_iter().enumerate() {
                    self.restore_continuation(&incoming_state);
                    self.refinements = incoming_refinements.clone();
                    self.minimum_states = incoming_minimum.clone();
                    let transfers = self.pattern_binding_transfers(
                        computation, &clause.pattern, &clause.bindings, true,
                    );
                    let minimum_place = self.projection(computation);
                    self.begin_scope();
                    // `bindings` includes the positive refinement
                    // environment when this completion arm opens one.  Give
                    // those names the same generative treatment as ordinary
                    // completion-pattern binders: forged Core cannot use a
                    // matching spelling to retarget an outer loan.
                    let clause_index = u32::try_from(clause_index)
                        .expect("completion clause index exceeded PlaceFlow identity space");
                    self.activate_branch_bindings(
                        &clause.bindings,
                        None,
                        |binder| PlaceBindingOrigin::CompletionBinder {
                            completion: id,
                            clause: clause_index,
                            binder,
                        },
                        None,
                    );
                    self.install_pattern_transfers(transfers);
                    self.check_custom_drop_pattern(computation, &clause.pattern, clause.span);
                    if !self.minimum_definitely_aborts(clause.body) {
                        self.open_minimum_pattern(computation, minimum_place, &clause.pattern, clause.span);
                    }
                    if clause_index == 0 && let Some(environment) = &refinement_test {
                        // Producer binders are observational projections, not
                        // reference fields already resident in the subject.
                        self.install_refinement_bindings(&crate::core::CoreRefinementBranch {
                            subject: computation,
                            pattern: clause.pattern.clone(),
                            environment: environment.clone(),
                        });
                    }
                    if let Some(refinement) = &clause.refinement {
                        self.install_refinement_bindings(refinement);
                    }
                    // The selected pattern has transferred the temporary's
                    // reference leaves into branch bindings. Their last uses
                    // now determine the loans' lifetime; the consumed result
                    // must not keep an iterator borrowed for the whole arm.
                    // A remaining destructor can still observe its leaves,
                    // so keep that subject's loans through arm cleanup.
                    let observed = self.selected_drop_observation_paths(
                        &self.body.expression(computation).ty, &clause.pattern,
                    );
                    self.release_unobserved_result_loans(computation, &observed, clause.span);
                    let arm_results = self.pending_results.clone();
                    self.visit_with_live_after(clause.body, live_after);
                    self.preserve_expression_result(id, clause.body);
                    self.release_expression_results(&arm_results, Some(id), clause.span);
                    self.end_scope(clause.span);
                    self.release_owner_loans(&subject_owner, clause.span);
                    if self.normal_continuation { exits.push(self.capture_continuation()); }
                }
                self.normal_continuation = !exits.is_empty();
                if self.normal_continuation {
                    self.join_continuation_states(&exits, &incoming, e.span);
                    self.refinements = incoming_refinements;
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
            CoreKind::Field { .. } => {
                if self.reborrow_reference(id).is_some() {
                    self.visit_pattern_subject(id, live_after, e.span);
                }
                if let Type::Reference { mutability, .. } = &e.ty {
                    let unique = matches!(mutability, crate::Mutability::Unique);
                    if unique && self.place_uses_shared_reference(id) {
                        self.error(e.span, "G5004", "cannot extract a unique reference through a shared view".into());
                    }
                    self.use_deref_reference(id, e.span, unique);
                } else if self.signatures.is_some() && !self.is_duplicable(&e.ty)
                    && self.reborrow_reference(id).is_some() {
                    self.error(e.span, "G5004", "cannot implicitly move a non-Copy field through a borrow".into());
                }
                if self.is_duplicable(&e.ty) {
                    self.read_place(id, e.span);
                } else if self.ordinary_value_moves_place(&e.ty) {
                    self.move_place(id, e.span);
                } else {
                    self.read_place(id, e.span);
                }
            }
            CoreKind::PatternTest {
                subject,
                refinement,
                ..
            } => {
                // A selector test observes its subject. Its branch arms may
                // subsequently each own the value under RunsIn correlation,
                // but the test itself is not a move.
                self.visit_pattern_subject(subject, live_after, e.span);
                // `is` produces a scoped positive proof. The expression
                // itself cannot introduce ordinary locals, so retaining this
                // only as a branded observation makes escape and join errors
                // visible without granting it authority past the test.
                self.refinements.push(RefinementFact {
                    brand: refinement.brand,
                    subject: refinement.subject,
                    bindings: refinement.bindings,
                    binding_keys: refinement.binding_keys,
                    span: e.span,
                });
            }
            CoreKind::Block(values) if id == self.body.root => {
                self.visit_sequence_with_discarded_prefix(&values, live_after, true)
            }
            CoreKind::Block(values) => self.visit_scoped_sequence(id, &values, live_after),
        }
        self.release_dead_loans(live_after, e.span);
    }

    fn visit_call_operands(&mut self, callee: CoreId, arguments: &[CoreId], live_after: &BTreeSet<String>) {
        if matches!(self.body.expression(callee).ty, Type::Reference { .. }) {
            let mut during_arguments = live_after.clone();
            for argument in arguments { self.collect_local_uses(*argument, &mut during_arguments); }
            self.visit_reference_handle(callee, &during_arguments);
            let mut receiver_live = live_after.clone();
            self.collect_local_uses(callee, &mut receiver_live);
            self.visit_sequence(arguments, &receiver_live);
            // A strict argument can transfer to an enclosing label. The
            // receiver is not invoked on that edge, even though its handle
            // was evaluated before the argument.
            if !self.normal_continuation { return; }
            self.use_deref_reference(callee, self.body.expression(callee).span,
                matches!(self.body.expression(callee).ty, Type::Reference { mutability: crate::Mutability::Unique, .. }));
        } else {
            let values = std::iter::once(callee).chain(arguments.iter().copied()).collect::<Vec<_>>();
            self.visit_sequence(&values, live_after);
        }
    }

    fn visit_sequence(&mut self, values: &[CoreId], live_after: &BTreeSet<String>) {
        self.visit_sequence_with_discarded_prefix(values, live_after, false);
    }

    fn visit_sequence_with_discarded_prefix(&mut self, values: &[CoreId], live_after: &BTreeSet<String>, discard_prefix: bool) {
        // A strict child which cannot normally complete leaves the current
        // lexical continuation. Core retains the syntactic suffix for
        // diagnostics and IDE tools, but ownership must not treat that dead
        // suffix as a use of a loan, a move, or a cleanup transition. This is
        // broader than a top-level `Transfer`: `Never` and an outer-label
        // transfer can be nested in a let, assignment, aggregate, or call.
        // Conversely, a transfer consumed by its own `Label` is an ordinary
        // value again, so `abrupt_exit` deliberately does not classify that
        // enclosing label expression as terminal.
        let reachable = values
            .iter()
            .copied()
            .scan(false, |terminated, value| {
                if *terminated {
                    return None;
                }
                if Self::abrupt_exit(self.body, value).is_some() {
                    *terminated = true;
                }
                Some(value)
            })
            .collect::<Vec<_>>();
        let mut suffixes = vec![live_after.clone(); reachable.len()];
        let mut future = live_after.clone();
        for (index, value) in reachable.iter().enumerate().rev() {
            suffixes[index] = future.clone();
            self.collect_local_uses(*value, &mut future);
        }
        let mut operand_owners = BTreeSet::new();
        for (index, (value, mut future)) in reachable.iter().zip(suffixes).enumerate() {
            if !self.normal_continuation { break; }
            // Strict operands remain owned by their parent operation. Only
            // a non-tail block expression discards its result at this point;
            // give that temporary an exact statement-long loan owner. Unit
            // lets/assignments introduce or update other owners, not one
            // whose initializer loans may be retired with their Unit result.
            if discard_prefix && index + 1 < values.len()
                && !matches!(self.body.expression(*value).ty, Type::Unit | Type::Never) {
                self.check_minimum_discard(&self.body.expression(*value).ty.clone(), self.body.expression(*value).span);
                let owner = format!("<temporary-statement-{}>", value.0);
                let previous = self.ephemeral_borrow_owner.replace(owner.clone());
                future.insert(owner.clone());
                let incoming_results = self.pending_results.clone();
                self.visit_with_live_after(*value, &future);
                self.release_expression_results(&incoming_results, None, self.body.expression(*value).span);
                self.release_owner_loans(&owner, self.body.expression(*value).span);
                self.ephemeral_borrow_owner = previous;
            } else {
                self.visit_with_live_after(*value, &future);
            }
            if !discard_prefix && index + 1 < values.len() && Self::abrupt_exit(self.body, *value).is_none() {
                // Once evaluated, an operand is no longer in its source
                // place, but its owner remains resident until the enclosing
                // operation runs. A later transfer/cancellation must prove
                // that abandoning this operand is authorized too.
                operand_owners.insert(self.retain_minimum_operand(*value));
            }
        }
        if reachable.last().is_none_or(|value| Self::abrupt_exit(self.body, *value).is_none()) {
            self.release_minimum_owners(&operand_owners);
        }
    }

    /// Determine whether evaluating `id` can reach the following strict
    /// operand. The calculation is structural and source ordered; it does
    /// not infer effects or reinterpret handler control. A completed label
    /// consumes only its own brand, preserving its regular continuation while
    /// allowing an inner label to propagate a transfer to an enclosing label.
    fn abrupt_exit(body: &TypedBody, id: CoreId) -> Option<AbruptExit> {
        let expression = body.expression(id);
        let structural_exit = match &expression.kind {
            CoreKind::ConstValue(_) => None,
            CoreKind::Transfer { brand, .. } => Some(AbruptExit::Transfer(*brand)),
            CoreKind::Label { brand, body: child } => match Self::abrupt_exit(body, *child) {
                Some(AbruptExit::Transfer(target)) if target == *brand => None,
                // Bottom in the body says that it cannot return to its own
                // continuation. It does not say that it bypasses this label:
                // completion arms and indirect calls can leave to this very
                // destination. Only a known different brand propagates here;
                // otherwise the label's frozen result type decides below.
                Some(AbruptExit::Never) => None,
                exit => exit,
            },
            CoreKind::Let { value, .. }
            | CoreKind::Borrow { value, .. }
            | CoreKind::Deref(value)
            | CoreKind::Move(value)
            | CoreKind::ReleaseAvailable(value)
            | CoreKind::PatternTest { subject: value, .. }
            | CoreKind::Field { base: value, .. } => Self::abrupt_exit(body, *value),
            CoreKind::Assign { value, place } => Self::abrupt_exit(body, *value).or_else(|| {
                let mut destination = place;
                while let CorePlace::Field { base, .. } = destination {
                    destination = base;
                }
                match destination {
                    CorePlace::Deref { reference, .. } => Self::abrupt_exit(body, *reference),
                    _ => None,
                }
            }),
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
                Self::first_abrupt_exit(body, values)
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                Self::first_abrupt_exit(body, fields)
            }
            CoreKind::IntrinsicCall { arguments, .. } => Self::first_abrupt_exit(body, arguments),
            CoreKind::Call {
                callee, arguments, ..
            } => Self::abrupt_exit(body, *callee)
                .or_else(|| Self::first_abrupt_exit(body, arguments)),
            CoreKind::Perform { arguments, .. } => Self::first_abrupt_exit(body, arguments),
            // A handler can turn a terminal performance into an ordinary arm
            // result. Its frozen result type, rather than the computation
            // child, is authoritative at this boundary.
            CoreKind::Handle { .. }
            | CoreKind::Completion { .. }
            | CoreKind::Closure { .. }
            | CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
            | CoreKind::Error => None,
        };
        // Inspect structural children before trusting the frozen bottom type.
        // In particular, a block containing `transfer done value` is `Never`
        // at the source site, but the enclosing `label done` consumes that
        // exact branded edge and continues with the transferred value.
        structural_exit
            .or_else(|| matches!(expression.ty, Type::Never).then_some(AbruptExit::Never))
    }

    fn first_abrupt_exit(body: &TypedBody, values: &[CoreId]) -> Option<AbruptExit> {
        values
            .iter()
            .find_map(|value| Self::abrupt_exit(body, *value))
    }

    /// Source-free local-use collection over Typed Core. Names are deliberately
    /// collected conservatively across shadowing: retaining a loan too long is
    /// safe, whereas releasing it before a shadow-sensitive use would not be.
    fn collect_local_uses(&self, id: CoreId, uses: &mut BTreeSet<String>) {
        match &self.body.expression(id).kind {
            CoreKind::ConstValue(_) => {},
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
            | CoreKind::ReleaseAvailable(base)
            | CoreKind::PatternTest { subject: base, .. } => self.collect_local_uses(*base, uses),
            CoreKind::Let { value, .. } => self.collect_local_uses(*value, uses),
            CoreKind::Assign { place, value } => {
                self.collect_local_uses(*value, uses);
                self.collect_place_uses(place, uses);
            }
            CoreKind::Call {
                callee, arguments, ..
            } => {
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
                ..
            } => {
                self.collect_local_uses(*computation, uses);
                for clause in clauses {
                    self.collect_local_uses(clause.body, uses);
                }
            }
            CoreKind::IntrinsicCall { arguments, .. } => {
                for argument in arguments {
                    self.collect_local_uses(*argument, uses);
                }
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
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Constant { .. }
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
            .filter(|owner| {
                // `live_after` originates from frozen Core spellings, while
                // loan owners are generative lexical identities. Preserve an
                // outer owner if its spelling is live beyond an arm, and
                // preserve the active branch identity when a branch-local
                // spelling is used later in the same arm. The arm scope
                // itself releases the latter before the dynamic join.
                !self.loan_is_used_by_destruction(owner)
                    && !self.pending_results.iter().any(|id| {
                        let root = Self::result_owner(*id);
                        **owner == root || owner.starts_with(&(root + "."))
                    })
                    && !live_after.iter().any(|name| {
                        let resolved = self.resolve_name(name);
                        **owner == *name || owner.starts_with(&(name.clone() + "."))
                            || **owner == resolved || owner.starts_with(&(resolved + "."))
                    })
            })
            .cloned()
            .collect::<BTreeSet<_>>();
        for owner in dead {
            self.release_owner_loans(&owner, span);
        }
    }

    /// A callable's hidden environment is not a structural reference leaf.
    /// Even a `CallReferenceShape::None` result therefore needs this separate
    /// check before retiring anonymous callback capture loans. Unknown or
    /// recursive layouts conservatively retain them.
    fn result_has_no_capture_carriers(&self, ty: &Type, active: &mut BTreeSet<crate::DefKey>) -> bool {
        match ty {
            Type::Callable { .. } | Type::Generic(_) | Type::Projection { .. }
                | Type::Infer(_) | Type::Error => false,
            Type::Tuple(fields) => fields.iter().all(|ty| self.result_has_no_capture_carriers(ty, active)),
            Type::Array(element) | Type::FixedArray { element, .. } | Type::StaticData { element, .. } => self.result_has_no_capture_carriers(element, active),
            Type::Nominal { definition, arguments } => {
                if !active.insert(*definition) { return false; }
                let no_captures = match self.signatures.and_then(|signatures| signatures.definitions.get(definition)) {
                    Some(crate::ElaboratedHeader::Nominal { layout: crate::ElaboratedNominalLayout::Struct(fields) | crate::ElaboratedNominalLayout::TupleStruct(fields), .. }) =>
                        fields.iter().all(|field| crate::core::instantiate_nominal_field_type(&field.ty, arguments)
                            .is_ok_and(|ty| self.result_has_no_capture_carriers(&ty, active))),
                    Some(crate::ElaboratedHeader::Nominal { layout: crate::ElaboratedNominalLayout::Enum(variants), .. }) =>
                        variants.iter().all(|variant| match &variant.payload {
                            crate::signature::ElaboratedEnumVariantPayload::Unit => true,
                            crate::signature::ElaboratedEnumVariantPayload::Tuple(fields) => fields.iter().all(|field|
                                crate::core::instantiate_nominal_field_type(field, arguments).is_ok_and(|ty| self.result_has_no_capture_carriers(&ty, active))),
                            crate::signature::ElaboratedEnumVariantPayload::Struct(fields) => fields.iter().all(|field|
                                crate::core::instantiate_nominal_field_type(&field.ty, arguments).is_ok_and(|ty| self.result_has_no_capture_carriers(&ty, active))),
                        }),
                    _ => false,
                };
                active.remove(definition);
                no_captures
            }
            Type::Reference { .. } => false,
            _ => true,
        }
    }

    fn is_duplicable(&self, ty: &Type) -> bool {
        self.signatures
            .and_then(|signatures| {
                let solver = self.ownership_solver.get_or_init(|| self.frozen_solver
                    .map_or_else(|| crate::TraitSolver::new(signatures), crate::TraitSolver::fresh_query));
                signatures.principal_use_interval_with_solver(ty, solver).or_else(|| {
                    signatures.principal_use_interval_with_bounds_and_solver(ty, self.lexical_bounds, solver)
                })
            })
            .is_some_and(|quantity| quantity == Quantity::UNRESTRICTED)
    }

    fn visit_pattern_subject(
        &mut self,
        subject: CoreId,
        live_after: &BTreeSet<String>,
        span: Span,
    ) {
        let incoming_results = self.pending_results.clone();
        self.visit_pattern_subject_inner(subject, live_after, span);
        let mut leaves = vec![];
        let empty = ElaboratedInterface::default();
        if crate::core::reference_leaf_paths(
            self.signatures.unwrap_or(&empty), &self.body.expression(subject).ty,
            &mut vec![], &mut leaves,
        ).is_ok() && leaves.is_empty()
            && regions::callable_paths(self.signatures.unwrap_or(&empty), &self.body.expression(subject).ty, false).is_empty() {
            // Reading a scalar through a computed reference consumes that
            // intermediate handle. It is not a payload of the scalar's
            // completion and cannot suspend its parent across either arm.
            self.release_expression_results(&incoming_results, None, span);
        }
    }

    fn visit_pattern_subject_inner(
        &mut self, subject: CoreId, live_after: &BTreeSet<String>, span: Span,
    ) {
        if self.projection(subject).is_some() {
            self.read_place(subject, span);
        } else if let Some((reference, fields)) = self.projected_dereference(subject) {
            self.visit_reference_handle(reference, live_after);
            self.use_projected_deref_reference(reference, &fields, span, false);
        } else if let CoreKind::Field { base, .. } = self.body.expression(subject).kind {
            self.visit_pattern_subject(base, live_after, span);
        } else {
            self.visit_with_live_after(subject, live_after);
        }
    }

    /// Reading a handle for a dereference/reborrow does not itself transfer
    /// the referenced value. In particular a shared view of an `&mut T`
    /// permits observing `T`, but cannot copy the unique handle into a tuple.
    fn visit_reference_handle(&mut self, id: CoreId, live_after: &BTreeSet<String>) {
        if self.projection(id).is_some() {
            self.read_place(id, self.body.expression(id).span);
        } else if let CoreKind::Deref(reference) = self.body.expression(id).kind {
            self.visit_reference_handle(reference, live_after);
            self.use_deref_reference(reference, self.body.expression(id).span, false);
        } else if let CoreKind::Field { .. } = self.body.expression(id).kind {
            self.visit_pattern_subject(id, live_after, self.body.expression(id).span);
        } else {
            self.visit_with_live_after(id, live_after);
        }
    }

    fn ordinary_value_moves_place(&self, ty: &Type) -> bool {
        // Callable invocation has a separate quantitative-use analysis.
        // A unique reference used as an owned value, however, is transferred:
        // later projections must not read its vacated carrier. Explicit
        // dereference/reborrow contexts use visit_reference_handle instead.
        self.signatures.is_some()
            && !self.minimum_owned_by_callable_lane(ty)
            && matches!(ty, Type::Nominal { .. } | Type::Tuple(_) | Type::Array(_) | Type::FixedArray { .. }
                | Type::Generic(_) | Type::Projection { .. }
                | Type::Reference { mutability: crate::Mutability::Unique, .. })
    }

    fn visit_closure_environment(
        &mut self,
        environment: &crate::core::CaptureEnvironment,
        span: Span,
        owner: Option<&str>,
    ) {
        if !environment.runs_in.sealed
            || environment.runs_in.environment != environment.brand
            || environment.runs_in.callable != environment.brand.callable
            || environment.runs_in.post_states != environment.post_states
        {
            self.error(
                span,
                "G5020",
                "closure RunsIn evidence does not match its sealed environment".into(),
            );
            return;
        }
        if environment.post_states.len() != environment.captures.len()
            || environment
                .captures
                .iter()
                .zip(&environment.post_states)
                .any(|(capture, state)| capture.name != state.name || capture.mode != state.mode)
        {
            self.error(
                span,
                "G5020",
                "closure environment capture post-state disagrees with its sealed layout".into(),
            );
            return;
        }
        for (capture, post_state) in environment.captures.iter().zip(&environment.post_states) {
            if let Some(owner) = owner { self.record_capture_origins(capture, owner); }
            self.capture_reference_loan(&capture.name, span, owner);
            match post_state.mode {
                CaptureMode::SharedBorrow => {
                    self.capture_place_loan(&capture.name, false, span, owner);
                }
                CaptureMode::UniqueBorrow => {
                    self.capture_place_loan(&capture.name, true, span, owner);
                }
                CaptureMode::Copy => {
                    // An owned copy is a value transfer into the environment,
                    // not a loan on the source binding.
                    self.read_place_by_name(&capture.name, span);
                }
                CaptureMode::Move => {
                    self.move_projection(Projection {
                        root: self.resolve_name(&capture.name), fields: vec![],
                    }, span);
                }
            }
        }
    }

    /// Capture contracts join sets of types, not physical environment indices.
    /// Index snapshots by the opened capture type so two joined environments
    /// with different capture orders cannot exchange their store operands.
    /// These lexical analysis keys never become Core projection authority.
    fn capture_origin_key(owner: &str, ty: &Type) -> String {
        format!("{owner}.<capture-{:?}>", crate::Digest::of_bytes(&crate::types::canonical_type_encoding(ty)))
    }

    fn record_capture_origins(&mut self, capture: &crate::core::ClosureCapture, owner: &str) {
        let source = self.resolve_name(&capture.name);
        let borrowed = matches!(capture.mode, CaptureMode::SharedBorrow | CaptureMode::UniqueBorrow);
        let ty = if borrowed { Type::Reference {
            lifetime: crate::Lifetime::Elided,
            mutability: if matches!(capture.mode, CaptureMode::UniqueBorrow) { crate::Mutability::Unique } else { crate::Mutability::Shared },
            referent: Box::new(capture.ty.clone()),
        } } else { capture.ty.clone() };
        let root = Self::capture_origin_key(owner, &ty);
        let resident = if borrowed { projection_key(&root, &[crate::core::REFERENCE_PATH_DEREF]) } else { root.clone() };
        let prefix = format!("{source}.");
        let references = self.reference_origins.iter().filter(|(key, _)| **key == source || key.starts_with(&prefix))
            .map(|(key, loans)| (format!("{resident}{}", &key[source.len()..]), loans.clone())).collect::<Vec<_>>();
        let logical = self.logical.origins.iter().filter(|(key, _)| **key == source || key.starts_with(&prefix))
            .map(|(key, regions)| (format!("{resident}{}", &key[source.len()..]), regions.clone())).collect::<Vec<_>>();
        for (key, loans) in references { self.reference_origins.entry(key).or_default().extend(loans); }
        for (key, regions) in logical { self.logical.origins.entry(key).or_default().extend(regions); }
        if borrowed {
            self.reference_origins.entry(root).or_default().insert(ProjectionLoan {
                place: Projection { root: source, fields: vec![] }, unique: matches!(capture.mode, CaptureMode::UniqueBorrow),
                owner: None, partitions: BTreeMap::new(), indirect: false, external: false,
            });
        }
    }

    /// Record a closure capture of a direct local as an ordinary, owned loan
    /// rather than a permanent borrow-state bit. A named environment owner
    /// makes the capture eligible for NLL release; an anonymous closure keeps
    /// the conservative escaping representation.
    fn capture_place_loan(&mut self, name: &str, unique: bool, span: Span, owner: Option<&str>) {
        let place = Projection {
            root: self.resolve_name(name),
            fields: vec![],
        };
        if self
            .projection_loans
            .iter()
            .any(|loan| !loan.indirect && loan.place.overlaps(&place) && (unique || loan.unique))
        {
            self.error(
                span,
                "G5006",
                format!("conflicting closure capture of place `{name}`"),
            );
            return;
        }
        self.borrow(name, unique, span);
        self.place_event(
            if unique {
                FlowEventKind::BorrowUnique(place.root.clone())
            } else {
                FlowEventKind::BorrowShared(place.root.clone())
            },
            place.clone(),
            span,
        );
        self.projection_loans.push(ProjectionLoan {
            place,
            unique,
            owner: owner.map(str::to_owned),
            partitions: BTreeMap::new(),
            indirect: false,
            external: false,
        });
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
    fn capture_reference_loan(&mut self, name: &str, span: Span, owner: Option<&str>) {
        let name = self.resolve_name(name);
        let regions = self.logical.origins.iter()
            .filter(|(key, _)| **key == name || key.starts_with(&(name.clone() + ".")))
            .flat_map(|(_, regions)| regions.iter().cloned()).collect::<BTreeSet<_>>();
        if !regions.is_empty() {
            let owner = owner.map(str::to_owned).unwrap_or_else(|| format!("<anonymous-logical-capture-{}>", span.start));
            self.logical.origins.entry(owner).or_default().extend(regions);
        }
        if self.open_referent_holes.contains_key(&name) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot capture unique reference `{name}` while its referent is uninitialized"
                ),
            );
            return;
        }
        let reborrows = self
            .projection_loans
            .iter()
            .filter(|loan| loan.owner.as_ref().is_some_and(|owner| *owner == name || owner.starts_with(&(name.clone() + "."))))
            .cloned()
            .map(|mut loan| {
                loan.owner = owner.map(str::to_owned);
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
        for loan in removed.iter().filter(|loan| !loan.indirect && loan.place.fields.is_empty()) {
            let remaining_shared = self
                .projection_loans
                .iter()
                .filter(|other| !other.indirect && other.place == loan.place && !other.unique)
                .count() as u32;
            let remaining_unique = self
                .projection_loans
                .iter()
                .any(|other| !other.indirect && other.place == loan.place && other.unique);
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
    fn read_place_by_name(&mut self, name: &str, span: Span) {
        let name = self.resolve_name(name);
        let place = Projection {
            root: name.clone(),
            fields: vec![],
        };
        if self.projection_loans.iter().any(|loan|
            !loan.indirect && loan.unique && loan.place.overlaps(&place)) {
            self.error(span, "G5008", format!("cannot copy a capture of uniquely borrowed place `{name}`"));
            return;
        }
        if let Some(moved) = self.moved_place_overlapping(&place) {
            self.error(span, "G5001", format!("use of moved place `{}`", moved.display()));
            return;
        }
        match self.states.get(&name) {
            Some(LocalState::Initialized) | Some(LocalState::SharedBorrowed(_)) => {
                self.place_event(FlowEventKind::Read(name), place, span)
            }
            Some(LocalState::Moved) => {
                self.error(span, "G5001", format!("use of moved local `{name}`"))
            }
            Some(LocalState::UniquelyBorrowed) => self.error(
                span,
                "G5008",
                format!("cannot read uniquely borrowed local `{name}`"),
            ),
            None => self.error(
                span,
                "G5002",
                format!("unknown local `{name}` in PlaceFlow"),
            ),
        }
    }
    fn borrow(&mut self, n: &str, u: bool, s: Span) {
        let n = self.resolve_name(n);
        match (self.states.get(&n).copied(), u) {
            (Some(LocalState::Initialized), true) => {
                self.states.insert(n.clone(), LocalState::UniquelyBorrowed);
                self.event(FlowEventKind::BorrowUnique(n.clone()), s)
            }
            (Some(LocalState::Initialized), false) => {
                self.states.insert(n.clone(), LocalState::SharedBorrowed(1));
                self.event(FlowEventKind::BorrowShared(n.clone()), s)
            }
            (Some(LocalState::SharedBorrowed(c)), false) => {
                self.states
                    .insert(n.clone(), LocalState::SharedBorrowed(c + 1));
                self.event(FlowEventKind::BorrowShared(n.clone()), s)
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
        self.minimum_transfer(&place);
        let binding = self.bindings.id(&place.root);
        let spelling = self.bindings.spelling(binding).to_owned();
        self.move_paths.intern(&place, binding, &spelling);
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
        let projection = match &self.body.expression(id).kind {
            CoreKind::Local(name) => Some(Projection {
                root: self.resolve_name(name),
                fields: vec![],
            }),
            CoreKind::Field { base, index, .. } => {
                self.projection(*base).map(|mut projection| {
                    projection.fields.push(*index);
                    projection
                })
            }
            _ => None,
        };
        projection.or_else(|| {
            let root = borrowed_temporary_root(id);
            self.bindings.ids.contains_key(&root).then_some(Projection { root, fields: vec![] })
        })
    }

    fn place_projection(&self, place: &CorePlace) -> Option<Projection> {
        match place {
            CorePlace::Local { name, .. } => Some(Projection {
                root: self.resolve_name(name),
                fields: vec![],
            }),
            CorePlace::Field { base, index, .. } => {
                let mut projection = self.place_projection(base)?;
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
        if !self.minimum_shell_available(&place, span) { return; }
        if self.open_referent_holes.contains_key(&place.root) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot use unique reference `{}` while its referent is uninitialized",
                    place.root
                ),
            );
            return;
        }
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
            .any(|loan| !loan.indirect && loan.unique && loan.place.overlaps(&place))
        {
            self.error(
                span,
                "G5008",
                format!("cannot read uniquely borrowed place `{}`", place.root),
            );
        }
    }

    fn move_place(&mut self, id: CoreId, span: Span) {
        if !self.check_custom_drop_projection(id, span) { return; }
        let Some(place) = self.projection(id) else {
            return;
        };
        self.move_projection(place, span);
    }

    fn move_projection(&mut self, place: Projection, span: Span) {
        if !self.minimum_shell_available(&place, span) { return; }
        if self
            .projection_loans
            .iter()
            .any(|loan| !loan.indirect && loan.place.overlaps(&place))
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
        let place = match self.projection(id) {
            Some(place) => place,
            None => {
                // Evaluation MIR already materializes this rvalue exactly
                // once. Give that same storage a frozen identity and retain
                // its borrowed fields and Drop observations until cleanup.
                let base = borrowed_place_base(self.body, id);
                let root = borrowed_temporary_root(base);
                self.activate_binding(&root, root.clone(), PlaceBindingOrigin::Temporary { expression: base });
                self.states.insert(root.clone(), LocalState::Initialized);
                self.event(FlowEventKind::Initialize(root.clone()), self.body.expression(base).span);
                self.record_aggregate_reference_origins(&root, base);
                self.record_destructor_paths(&root, &self.body.expression(base).ty.clone());
                self.record_minimum_binding(&root, &self.body.expression(base).ty.clone(), self.body.expression(base).span);
                self.projection(id).expect("the temporary's field path has an initialized root")
            }
        };
        self.borrow_projection(place, unique, span, owner);
    }

    fn borrow_projection(&mut self, place: Projection, unique: bool, span: Span, owner: Option<String>) {
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
            .any(|loan| !loan.indirect && loan.place.overlaps(&place) && (unique || loan.unique))
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
                    partitions: BTreeMap::new(),
                    indirect: false,
                    external: false,
                };
                if let Some(owner) = &loan.owner {
                    self.reference_origins.insert(owner.clone(), BTreeSet::from([loan.clone()]));
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
            partitions: BTreeMap::new(),
            indirect: false,
            external: false,
        };
        if let Some(owner) = &loan.owner {
            self.reference_origins.insert(owner.clone(), BTreeSet::from([loan.clone()]));
        }
        self.projection_loans.push(loan);
        self.place_event(
            if unique {
                FlowEventKind::BorrowUnique(place.root.clone())
            } else {
                FlowEventKind::BorrowShared(place.root.clone())
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
        let Some(reference) = self.reborrow_reference(id) else {
            return false;
        };
        let parents = self.reference_loans_from_value(reference);
        if parents.is_empty() {
            self.error(span, "G5006", "reborrow has no live parent loan".into());
            return true;
        }
        if unique && (self.place_uses_shared_reference(id) || parents.iter().any(|parent| !parent.unique)) {
            self.error(
                span,
                "G5006",
                "unique reborrow requires a unique parent loan".into(),
            );
            return true;
        }
        let mut fields = vec![];
        let mut place = id;
        while let CoreKind::Field { base, index, .. } = self.body.expression(place).kind {
            fields.push(index);
            place = base;
        }
        fields.reverse();
        let mut allowed = BTreeSet::new();
        if let Some(parent) = self.reference_origin_key(reference) {
            allowed.extend(self.reference_ancestors(&parent));
        }
        for parent in &parents {
            if let Some(owner) = &parent.owner { allowed.extend(self.reference_ancestors(owner)); }
        }
        let projected = parents.iter().cloned().map(|mut parent| {
            parent.place.fields.extend_from_slice(&fields);
            parent
        }).collect::<Vec<_>>();
        if self.projection_loans.iter().any(|loan|
            !loan.owner.as_ref().is_some_and(|owner| allowed.contains(owner))
                && projected.iter().any(|parent| loan.indirect == parent.indirect && loan.place.overlaps(&parent.place)
                    && !loan.disjoint_from(parent) && (unique || loan.unique))) {
            self.error(span, "G5006", "reborrow conflicts with a live child loan".into());
            return true;
        }
        let mut aliases = BTreeSet::new();
        let mut parent_owners = BTreeSet::new();
        if let Some(parent) = self.reference_origin_key(reference) { parent_owners.insert(parent); }
        for parent_loan in projected {
            if let Some(parent) = &parent_loan.owner { parent_owners.insert(parent.clone()); }
            self.place_event(FlowEventKind::Reborrow(parent_loan.place.root.clone()),
                parent_loan.place.clone(), span);
            let loan = ProjectionLoan { unique, owner: Some(owner.clone()), ..parent_loan };
            aliases.insert(loan.clone());
            self.projection_loans.push(loan);
        }
        self.reference_origins.insert(owner.clone(), aliases);
        self.reborrow_parents.insert(owner, parent_owners);
        true
    }

    /// A projected field retains the reference carrier introduced by its
    /// autoderef: `&parent.0` is a reborrow of `parent`, not a new temporary
    /// loan detached from the caller-owned place.
    fn reborrow_reference(&self, id: CoreId) -> Option<CoreId> {
        match self.body.expression(id).kind {
            CoreKind::Deref(reference) => Some(reference),
            CoreKind::Field { base, .. } => self.reborrow_reference(base),
            _ => None,
        }
    }

    fn place_uses_shared_reference(&self, id: CoreId) -> bool {
        match self.body.expression(id).kind {
            CoreKind::Deref(reference) => matches!(self.body.expression(reference).ty,
                Type::Reference { mutability: crate::Mutability::Shared, .. })
                || self.place_uses_shared_reference(reference),
            CoreKind::Field { base, .. } => self.place_uses_shared_reference(base),
            _ => false,
        }
    }

    fn reference_origin_key(&self, id: CoreId) -> Option<String> {
        match &self.body.expression(id).kind {
            CoreKind::Local(name) => Some(self.resolve_name(name)),
            CoreKind::Field { base, index, .. } => {
                let mut key = self.reference_origin_key(*base)?;
                key.push('.');
                key.push_str(&index.to_string());
                Some(key)
            }
            _ => None,
        }
    }

    fn logical_origin_regions(&self, owner: &str) -> BTreeSet<regions::Region> {
        let selected = owner.split('.').collect::<Vec<_>>();
        let root = selected[0];
        self.logical.origins.range(root.to_owned()..)
            .take_while(|(key, _)| *key == root || key.starts_with(&(root.to_owned() + ".")))
            .filter(|(key, _)| {
                let candidate = key.split('.').collect::<Vec<_>>();
                candidate.len() == selected.len() && candidate.iter().zip(&selected).all(|(left, right)|
                    left == right || left.parse::<u32>().ok().zip(right.parse::<u32>().ok())
                        .is_some_and(|(left, right)| crate::core::reference_path_matches(&[left], &[right])))
            }).flat_map(|(_, regions)| regions.iter().cloned()).collect()
    }

    fn logical_regions_from_value_path(&self, id: CoreId, fields: &[u32]) -> BTreeSet<regions::Region> {
        let logical = crate::core::reference_path_is_logical(fields);
        if let Some(deref) = fields.iter().position(|field| *field == crate::core::REFERENCE_PATH_DEREF) {
            let parents = self.reference_loans_from_value_path(id, &fields[..deref]);
            return parents.into_iter().flat_map(|parent| {
                let mut path = parent.place.fields;
                path.extend_from_slice(&fields[deref + 1..]);
                let known = self.logical_origin_regions(&projection_key(&parent.place.root, &path));
                if known.is_empty() && logical {
                    BTreeSet::from([regions::Region { site: parent.place.root, path }])
                } else { known }
            }).collect();
        }
        if self.pending_results.contains(&id) {
            return self.logical_origin_regions(&projection_key(&Self::result_owner(id), fields));
        }
        if let Some(key) = self.reference_origin_key(id) {
            let known = self.logical_origin_regions(&projection_key(&key, fields));
            if !known.is_empty() || !logical { return known; }
            return BTreeSet::from([regions::Region { site: key, path: fields.to_vec() }]);
        }
        match &self.body.expression(id).kind {
            CoreKind::Move(value) | CoreKind::Label { body: value, .. } | CoreKind::Transfer { value, .. } =>
                return self.logical_regions_from_value_path(*value, fields),
            CoreKind::Block(values) => return values.last().map(|value|
                self.logical_regions_from_value_path(*value, fields)).unwrap_or_default(),
            CoreKind::Deref(reference) => {
                return self.reference_loans_from_value(*reference).into_iter().flat_map(|parent| {
                    let mut path = parent.place.fields;
                    path.extend_from_slice(fields);
                    let known = self.logical_origin_regions(&projection_key(&parent.place.root, &path));
                    if known.is_empty() && logical { BTreeSet::from([regions::Region { site: parent.place.root, path }]) }
                    else { known }
                }).collect();
            }
            CoreKind::Call { arguments, .. }
            | CoreKind::Perform { arguments, reference_origin: CallReferenceOrigin::Paths(_), .. } => {
                let mut known = BTreeSet::new();
                for path in self.resident_call_paths(id) {
                    if !crate::core::reference_path_is_prefix(&path.result_fields, fields) { continue; }
                    let Some(argument) = arguments.get(path.argument as usize) else { continue; };
                    let mut source = path.argument_fields.clone();
                    source.extend_from_slice(&fields[path.result_fields.len()..]);
                    known.extend(self.logical_regions_from_value_path(*argument, &source));
                }
                if !known.is_empty() || !logical { return known; }
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Record { fields: values, .. }
            | CoreKind::Enum { fields: values, .. } => {
                if let Some((field, tail)) = fields.split_first() {
                    if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
                        return values.iter().flat_map(|value| self.logical_regions_from_value_path(*value, tail)).collect();
                    }
                    if let Some(value) = values.get(*field as usize) { return self.logical_regions_from_value_path(*value, tail); }
                }
            }
            _ => {}
        }
        if logical { BTreeSet::from([regions::Region { site: Self::result_owner(id), path: fields.to_vec() }]) }
        else { BTreeSet::new() }
    }

    fn record_logical_value_origins(&mut self, name: &str, id: CoreId) {
        let mut changed = false;
        let source = if self.pending_results.contains(&id) { Some(Self::result_owner(id)) }
            else { self.reference_origin_key(id) };
        if let Some(source) = source {
            let aliases = self.logical.origins.iter()
                .filter(|(key, _)| **key == source || key.starts_with(&(source.clone() + ".")))
                .map(|(key, regions)| (format!("{name}{}", &key[source.len()..]), regions.clone())).collect::<Vec<_>>();
            for (key, regions) in aliases { self.logical.origins.entry(key).or_default().extend(regions); changed = true; }
        }
        let empty = ElaboratedInterface::default();
        let mut leaves = vec![];
        let _ = crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty), &self.body.expression(id).ty, &mut vec![], &mut leaves);
        leaves.extend(regions::callable_paths(self.signatures.unwrap_or(&empty), &self.body.expression(id).ty, false));
        for (path, _) in leaves {
            let regions = self.logical_regions_from_value_path(id, &path);
            let Some(first) = regions.first().cloned() else { continue; };
            let parents = self.reference_loans_from_value_path(id, &path).into_iter()
                .map(|loan| ProjectionLoan { owner: None, ..loan }).collect::<BTreeSet<_>>();
            self.logical.regions.connect(&regions);
            self.logical.regions.insert(first, parents, |loans, incoming| loans.extend(incoming));
            self.logical.origins.entry(projection_key(name, &path)).or_default().extend(regions);
            changed = true;
        }
        if changed { self.refresh_logical_loans(id); }
    }

    fn record_logical_call_stores(&mut self, callee: CoreId, arguments: &[CoreId], call: CoreId) {
        let Some(signatures) = self.signatures else { return; };
        let mut changed = false;
        for transfer in regions::call_transfers(signatures, self.body, callee) {
            let (Some(destination), Some(source)) = (arguments.get(transfer.destination), arguments.get(transfer.source)) else { continue; };
            let mut region_ids = self.logical_regions_from_value_path(*destination, &transfer.destination_path);
            let Some(first) = region_ids.first().cloned() else { continue; };
            region_ids.extend(self.logical_regions_from_value_path(*source, &transfer.source_path));
            let loans = self.reference_loans_from_value_path(*source, &transfer.source_path).into_iter()
                .map(|loan| ProjectionLoan { owner: None, ..loan }).collect::<BTreeSet<_>>();
            self.logical.regions.connect(&region_ids);
            self.logical.regions.insert(first, loans, |loans, incoming| loans.extend(incoming));
            changed = true;
        }
        if changed { self.refresh_logical_loans(call); }
    }

    /// Captures are implicit invocation inputs. Their contract describes the
    /// same possible resident stores as explicit inputs, while the value's
    /// live origins retain the actual capture roots after contextual erasure.
    /// Capture unions need not have a common physical order; typed snapshots
    /// preserve each operand without inventing environment projections.
    fn record_captured_call_stores(&mut self, callee: CoreId, owner: Option<&str>, call: CoreId) {
        let Some(signatures) = self.signatures else { return; };
        let Type::Callable { contract, .. } = &self.body.expression(callee).ty else { return; };
        if contract.captures.is_empty() && contract.environment.is_some() { return; }
        let captures = contract.open(|_| None).map(|contract| contract.captures).unwrap_or_else(|| contract.captures.clone());
        if !(captures.is_empty() && contract.environment.is_none())
            && regions::parameter_transfers(signatures, &captures).is_empty() { return; }
        let owned = owner.map(str::to_owned).or_else(|| self.reference_origin_key(callee));
        if let Some(owner) = &owned {
            let mut known = false;
            for transfer in regions::parameter_transfers(signatures, &captures) {
                let destination = projection_key(&Self::capture_origin_key(owner, &captures[transfer.destination]), &transfer.destination_path);
                let source = projection_key(&Self::capture_origin_key(owner, &captures[transfer.source]), &transfer.source_path);
                let mut regions = self.logical_origin_regions(&destination);
                let Some(first) = regions.first().cloned() else { continue; };
                regions.extend(self.logical_origin_regions(&source));
                let loans = self.origin_loans(&source).into_iter().map(|loan| ProjectionLoan { owner: None, ..loan }).collect();
                self.logical.regions.connect(&regions);
                self.logical.regions.insert(first, loans, |loans, incoming| loans.extend(incoming));
                known = true;
            }
            if known { self.refresh_logical_loans(call); return; }
        }
        let region_ids = if let Some(owner) = &owned {
            self.logical.origins.iter().filter(|(key, _)| *key == owner || key.starts_with(&(owner.clone() + ".")))
                .flat_map(|(_, regions)| regions.iter().cloned()).collect::<BTreeSet<_>>()
        } else { self.logical_regions_from_value_path(callee, &[]) };
        let Some(first) = region_ids.first().cloned() else { return; };
        let loans = if let Some(owner) = &owned {
            self.captured_origin_loans(owner)
        } else { self.reference_loans_from_value(callee) };
        self.logical.regions.connect(&region_ids);
        self.logical.regions.insert(first, loans.into_iter().map(|loan| ProjectionLoan { owner: None, ..loan }).collect(),
            |loans, incoming| loans.extend(incoming));
        self.refresh_logical_loans(call);
    }

    fn resident_call_paths(&self, id: CoreId) -> Vec<crate::core::CallReferencePath> {
        let mut paths = match &self.body.expression(id).kind {
            CoreKind::Call { reference_origin: CallReferenceOrigin::Paths(paths), .. }
            | CoreKind::Perform { reference_origin: CallReferenceOrigin::Paths(paths), .. } => paths.clone(),
            _ => vec![],
        };
        if let (Some(signatures), CoreKind::Call { callee, .. }) = (self.signatures, &self.body.expression(id).kind) {
            paths.extend(regions::callable_result_paths(signatures, self.body.expression(*callee)));
        }
        paths
    }

    fn refresh_logical_loans(&mut self, source: CoreId) {
        let aliases = self.logical.origins.iter().filter(|(owner, _)| !self.origin_has_been_moved(owner))
            .flat_map(|(owner, regions)| self.logical.regions.contents(regions).into_iter().flatten()
                .map(|loan| (owner.clone(), loan))).collect::<Vec<_>>();
        for (owner, loan) in aliases {
            if !self.projection_loans.contains(&ProjectionLoan { owner: Some(owner.clone()), ..loan.clone() }) {
                self.install_reference_alias(&owner, loan, source);
            }
        }
    }

    fn record_aggregate_reference_origins(&mut self, name: &str, id: CoreId) {
        self.record_logical_value_origins(name, id);
        if self.pending_results.contains(&id) {
            let source = Self::result_owner(id);
            let aliases = self.reference_origins.keys()
                .filter(|key| **key == source || key.starts_with(&(source.clone() + ".")))
                .map(|key| (format!("{name}{}", &key[source.len()..]), self.origin_loans(key)))
                .collect::<Vec<_>>();
            for (destination, parents) in aliases {
                for parent in parents { self.install_reference_alias(&destination, parent, id); }
            }
            return;
        }
        match self.body.expression(id).kind.clone() {
            CoreKind::Move(value) => self.record_aggregate_reference_origins(name, value),
            CoreKind::Block(values) => {
                if let Some(tail) = values.last() { self.record_aggregate_reference_origins(name, *tail); }
            }
            CoreKind::Label { body, .. } | CoreKind::Transfer { value: body, .. } =>
                self.record_aggregate_reference_origins(name, body),
            CoreKind::Local(_) | CoreKind::Field { .. } => {
                if let Some(source) = self.reference_origin_key(id) {
                    let prefix = source.clone() + ".";
                    let aliases = self.reference_origins.iter()
                        .filter(|(key, _)| **key == source || key.starts_with(&prefix))
                        .map(|(key, _)| (format!("{name}{}", &key[source.len()..]), self.origin_loans(key)))
                        .collect::<Vec<_>>();
                    for (destination, parents) in aliases {
                        for parent in parents { self.install_reference_alias(&destination, parent, id); }
                    }
                } else {
                    let empty = ElaboratedInterface::default();
                    let mut leaves = vec![];
                    let _ = crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty),
                        &self.body.expression(id).ty, &mut vec![], &mut leaves);
                    for (fields, _) in leaves {
                        for parent in self.reference_loans_through_deref(id, &fields) {
                            self.install_reference_alias(&projection_key(name, &fields), parent, id);
                        }
                    }
                }
            }
            // A reference stored inside an aggregate is owned by that
            // aggregate's lexical storage just as `let r = &mut value` is
            // owned by `r`.  The initial borrow was necessarily visited
            // before the aggregate binding existed, so it has no direct NLL
            // owner yet. Reify the sealed projected loan under the aggregate
            // field identity now; scope exit can then release the unique
            // borrow instead of pinning the referent to the enclosing body.
            CoreKind::Borrow { .. } | CoreKind::Closure { .. } => {
                for parent in self.reference_loans_from_value(id) {
                    self.install_reference_alias(name, parent, id);
                }
            }
            // Every aggregate constructor carries its children in frozen Core
            // order.  Keeping this deliberately independent of source field
            // syntax means that enum payload binders and array elements get
            // the exact same backing-loan identity as tuple and record
            // fields.  In particular, a reference may be created before an
            // effect boundary and only extracted by a later refinement arm.
            CoreKind::Record { fields, .. }
            | CoreKind::Enum { fields, .. }
            | CoreKind::Tuple(fields)
            | CoreKind::Array(fields) => {
                for (index, field) in fields.into_iter().enumerate() {
                    let key = format!("{name}.{index}");
                    // Do not special-case a syntactic `&place`: the
                    // aggregate can equally receive a caller reference,
                    // reborrow, or frozen call result.  All of those have a
                    // sealed projection loan by this point.  Copy the loan
                    // identity into the aggregate slot while leaving the
                    // aggregate itself as ordinary storage; a later
                    // `&*slot` creates the child reborrow that owns an NLL
                    // region.
                    let parents = self.reference_loans_from_value(field);
                    if !parents.is_empty() {
                        self.reference_origins.insert(key.clone(), parents.into_iter().map(|parent|
                            ProjectionLoan { owner: None, ..parent }).collect());
                    }
                    self.record_aggregate_reference_origins(&key, field);
                }
            }
            CoreKind::Call {
                arguments,
                reference_origin,
                ..
            }
            | CoreKind::Perform {
                arguments,
                reference_origin,
                ..
            } => self.record_call_reference_origin(name, id, &arguments, reference_origin),
            _ => {}
        }
    }

    /// Reify every frozen caller-region path a call result is permitted to
    /// forward. Each path is an owned alias, keeping its backing loan live
    /// through the matching result projection while suspending a unique
    /// caller reference during that projection's use.
    fn record_call_reference_origin(
        &mut self,
        result: &str,
        call: CoreId,
        arguments: &[CoreId],
        origin: CallReferenceOrigin,
    ) {
        if let (Some(signatures), CoreKind::Call { callee, .. }) = (self.signatures, &self.body.expression(call).kind) {
            for path in regions::callable_result_paths(signatures, self.body.expression(*callee)) {
                if let Some(argument) = arguments.get(path.argument as usize) {
                    for parent in self.reference_loans_from_value_path(*argument, &path.argument_fields) {
                        self.install_reference_alias(&projection_key(result, &path.result_fields), parent, call);
                    }
                }
            }
        }
        if matches!(origin, CallReferenceOrigin::External | CallReferenceOrigin::Unsafe) {
            let empty = ElaboratedInterface::default();
            let mut leaves = vec![];
            let _ = crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty),
                &self.body.expression(call).ty, &mut vec![], &mut leaves);
            for (fields, _) in leaves {
                for parent in self.external_reference_loans(call, &fields) {
                    self.install_reference_alias(&projection_key(result, &fields), parent, call);
                }
            }
            return;
        }
        let CallReferenceOrigin::Paths(paths) = origin else {
            return;
        };
        for path in paths {
            let Some(argument) = arguments.get(path.argument as usize).copied() else {
                self.error(
                    self.body.expression(self.body.root).span,
                    "G5023",
                    "reference-valued call names an argument outside its frozen arity".into(),
                );
                continue;
            };
            let parents = self.reference_loans_from_value_path(argument, &path.argument_fields);
            if parents.is_empty() {
                // A logical generic resident may be empty. Forwarding that
                // empty set creates no checked reference authority; unlike
                // a missing physical reference it is not a malformed call.
                if crate::core::reference_path_is_logical(&path.argument_fields) { continue; }
                // A call classified as `External` has proved that all of its
                // reference leaves are static/external.  Forwarding one of
                // those leaves needs no caller loan to keep alive; in
                // particular this lets ordinary std wrappers project the
                // backing reference of a static `Str` into a `Slice`.
                if self.external_reference_path(argument) {
                    continue;
                }
                self.error(
                    self.body.expression(argument).span,
                    "G5023",
                    "reference-valued call forwards an argument without a live reference provenance"
                        .into(),
                );
                continue;
            }
            let result = projection_key(result, &path.result_fields);
            for parent in parents {
                let parent = self.partition_call_result(call, &path.result_fields, parent);
                self.install_reference_alias(&result, parent, argument);
            }
        }
    }

    fn reject_opaque_reference_result(
        &mut self,
        shape: CallReferenceShape,
        result: &crate::types::Type,
        span: Span,
        boundary: &str,
    ) {
        if matches!(shape, CallReferenceShape::OpaquePotentiallyReference)
            && !contains_open_type_parameter(result)
        {
            self.error(
                span,
                "G5023",
                format!("reference-valued {boundary} has no frozen caller-region provenance"),
            );
        }
    }

    fn reference_loans_from_value(&self, id: CoreId) -> BTreeSet<ProjectionLoan> {
        if self.pending_results.contains(&id) {
            return self.origin_loans(&Self::result_owner(id));
        }
        match &self.body.expression(id).kind {
            CoreKind::Closure { environment, .. } => environment.captures.iter().flat_map(|capture| {
                let name = self.resolve_name(&capture.name);
                let mut loans = self.captured_origin_loans(&name);
                if matches!(capture.mode, CaptureMode::SharedBorrow | CaptureMode::UniqueBorrow) {
                    loans.insert(ProjectionLoan { place: Projection { root: name, fields: vec![] },
                        unique: matches!(capture.mode, CaptureMode::UniqueBorrow), owner: None,
                        partitions: BTreeMap::new(), indirect: false, external: false });
                }
                loans
            }).collect(),
            CoreKind::Deref(_) => self.reference_loans_through_deref(id, &[]),
            CoreKind::Borrow { unique, value } => {
                if let Some(place) = self.projection(*value) {
                    let loans = self.projection_loans.iter()
                        .filter(|loan| loan.place == place && loan.unique == *unique)
                        .cloned().collect::<BTreeSet<_>>();
                    if loans.is_empty() {
                        BTreeSet::from([ProjectionLoan { place, unique: *unique, owner: None, partitions: BTreeMap::new(), indirect: false, external: false }])
                    } else { loans }
                } else if let Some((reference, fields)) = self.projected_dereference(*value) {
                    // A projected reborrow retains every possible backing
                    // region of its incoming reference, not a selected one.
                    self.reference_loans_from_value(reference).into_iter().map(|mut parent| {
                        parent.place.fields.extend_from_slice(&fields);
                        parent.unique = *unique;
                        parent
                    }).collect()
                } else { BTreeSet::new() }
            }
            CoreKind::Local(_) | CoreKind::Field { .. } => {
                self.reference_origin_key(id).map(|key| self.origin_loans(&key))
                    .unwrap_or_else(|| self.reference_loans_through_deref(id, &[]))
            }
            CoreKind::Call { reference_origin: CallReferenceOrigin::External | CallReferenceOrigin::Unsafe, .. }
            | CoreKind::Perform { reference_origin: CallReferenceOrigin::External, .. } =>
                self.external_reference_loans(id, &[]),
            CoreKind::Call {
                arguments,
                ..
            }
            | CoreKind::Perform {
                arguments,
                reference_origin: CallReferenceOrigin::Paths(_),
                ..
            } => self.resident_call_paths(id)
                .into_iter()
                .filter(|path| path.result_fields.is_empty())
                .flat_map(|path| arguments.get(path.argument as usize).map(|argument|
                    self.reference_loans_from_value_path(*argument, &path.argument_fields).into_iter()
                        .map(|loan| self.partition_call_result(id, &path.result_fields, loan)).collect::<BTreeSet<_>>()).unwrap_or_default())
                .collect(),
            CoreKind::Move(value) => self.reference_loans_from_value(*value),
            _ => BTreeSet::new(),
        }
    }

    fn reference_loans_from_value_path(&self, id: CoreId, fields: &[u32]) -> BTreeSet<ProjectionLoan> {
        if let Some(deref) = fields.iter().position(|field| *field == crate::core::REFERENCE_PATH_DEREF) {
            let parents = self.reference_loans_from_value_path(id, &fields[..deref]);
            let empty = ElaboratedInterface::default();
            let mut leaves = vec![];
            let _ = crate::core::input_reference_leaf_paths(self.signatures.unwrap_or(&empty),
                &self.body.expression(id).ty, &mut leaves);
            leaves.extend(regions::callable_paths(self.signatures.unwrap_or(&empty), &self.body.expression(id).ty, true));
            let Some((_, ty)) = leaves.into_iter().find(|(path, _)| crate::core::reference_path_matches(path, fields)) else {
                return BTreeSet::new();
            };
            return self.reference_resident_loans(parents, &fields[deref + 1..],
                matches!(ty, Type::Reference { mutability: crate::Mutability::Unique, .. }));
        }
        if self.pending_results.contains(&id) {
            return self.origin_loans(&projection_key(&Self::result_owner(id), fields));
        }
        if fields.is_empty() {
            return self.reference_loans_from_value(id);
        }
        // A call can return a nominal aggregate which carries a reference in
        // one of its fields (for example `Vec::as_mut_slice` and then
        // `SliceMut::iter`). The frozen caller-path relation already proves
        // that field aliases an argument field; follow it before treating the
        // call expression as an anonymous aggregate. This makes provenance
        // compose through wrappers that have not been let-bound.
        match &self.body.expression(id).kind {
            CoreKind::Call { reference_origin: CallReferenceOrigin::External | CallReferenceOrigin::Unsafe, .. }
            | CoreKind::Perform { reference_origin: CallReferenceOrigin::External, .. } =>
                return self.external_reference_loans(id, fields),
            CoreKind::Call {
                arguments,
                ..
            }
            | CoreKind::Perform {
                arguments,
                reference_origin: CallReferenceOrigin::Paths(_),
                ..
            } => {
                let mut loans = BTreeSet::new();
                for path in self.resident_call_paths(id) {
                    if !crate::core::reference_path_is_prefix(&path.result_fields, fields) {
                        continue;
                    }
                    let Some(argument) = arguments.get(path.argument as usize).copied() else { continue; };
                    let mut argument_fields = path.argument_fields.clone();
                    argument_fields.extend_from_slice(&fields[path.result_fields.len()..]);
                    loans.extend(self.reference_loans_from_value_path(argument, &argument_fields).into_iter()
                        .map(|loan| self.partition_call_result(id, &fields[..path.result_fields.len()], loan)));
                }
                return loans;
            }
            CoreKind::Move(value) => return self.reference_loans_from_value_path(*value, fields),
            _ => {}
        }
        let mut value = id;
        let mut remaining = fields;
        while let Some((field, tail)) = remaining.split_first() {
            let fields = match &self.body.expression(value).kind {
                CoreKind::Tuple(fields)
                | CoreKind::Array(fields)
                | CoreKind::Record { fields, .. }
                | CoreKind::Enum { fields, .. } => fields,
                _ => {
                    // A local/field expression stands for an already-built
                    // aggregate, so all remaining projections belong to its
                    // single lexical origin. Looking up only the first
                    // projection loses nested reference carriers such as
                    // `Str { bytes: Slice { storage: &Array<_>, .. } }`.
                    let Some(key) = self.reference_origin_key(value) else {
                        return self.reference_loans_through_deref(value, remaining);
                    };
                    return self.origin_loans(&projection_key(&key, remaining));
                }
            };
            if *field == crate::core::REFERENCE_PATH_ARRAY_ELEMENT {
                return fields.iter().flat_map(|value|
                    self.reference_loans_from_value_path(*value, tail)).collect();
            }
            let Some(next) = fields.get(*field as usize).copied() else { return BTreeSet::new(); };
            value = next;
            remaining = tail;
        }
        self.reference_loans_from_value(value)
    }

    fn reference_resident_loans(&self, parents: BTreeSet<ProjectionLoan>, fields: &[u32], unique: bool) -> BTreeSet<ProjectionLoan> {
        let next = fields.iter().position(|field| *field == crate::core::REFERENCE_PATH_DEREF);
        let projection = &fields[..next.unwrap_or(fields.len())];
        let mut residents = BTreeSet::new();
        for parent in parents {
            let mut place = parent.place.clone();
            place.fields.extend_from_slice(projection);
            let known = self.origin_loans(&projection_key(&place.root, &place.fields));
            if !known.is_empty() && (!parent.indirect || !projection.is_empty()) {
                residents.extend(known.into_iter().map(|mut resident| {
                    // Copying a shared stored handle preserves its backing
                    // loan but does not borrow the replaceable handle slot.
                    // A unique resident still needs that slot's authority.
                    if !resident.unique { resident.owner = None; }
                    resident
                }));
            } else if parent.external || self.bindings.get(&parent.place.root).is_some_and(|binding|
                matches!(self.bindings.entries[binding.0 as usize].origin, PlaceBindingOrigin::Parameter { .. })) {
                // The reference stored in caller storage has a distinct
                // region from the outer handle. Do not retain the outer
                // reborrow owner merely because it was used to read it.
                residents.insert(ProjectionLoan { place, unique, owner: None, ..parent });
            }
        }
        match next {
            Some(next) => self.reference_resident_loans(residents, &fields[next + 1..], unique),
            None => residents,
        }
    }

    /// A reference leaf projected through a borrowed aggregate either names
    /// a known local resident or comes from a caller-owned referent. Never
    /// invent external provenance for an unknown local's reference field.
    fn reference_loans_through_deref(&self, mut id: CoreId, fields: &[u32]) -> BTreeSet<ProjectionLoan> {
        let empty = ElaboratedInterface::default();
        let mut leaves = vec![];
        let _ = crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty),
            &self.body.expression(id).ty, &mut vec![], &mut leaves);
        let Some((_, Type::Reference { mutability, .. })) = leaves.into_iter().find(|(path, _)| crate::core::reference_path_matches(path, fields)) else {
            return BTreeSet::new();
        };
        let mut path = vec![];
        while let CoreKind::Field { base, index, .. } = self.body.expression(id).kind {
            path.push(index);
            id = base;
        }
        path.reverse();
        path.extend_from_slice(fields);
        let CoreKind::Deref(reference) = self.body.expression(id).kind else { return BTreeSet::new(); };
        let mut loans = BTreeSet::new();
        for parent in self.reference_loans_from_value(reference) {
            let mut projected = parent.place.clone();
            projected.fields.extend_from_slice(&path);
            let residents = self.origin_loans(&projection_key(&projected.root, &projected.fields));
            if !residents.is_empty() {
                loans.extend(residents);
            } else if parent.external || self.bindings.get(&parent.place.root).is_some_and(|binding|
                matches!(self.bindings.entries[binding.0 as usize].origin, PlaceBindingOrigin::Parameter { .. })) {
                loans.insert(ProjectionLoan { place: projected,
                    unique: matches!(mutability, crate::Mutability::Unique), ..parent });
            }
        }
        loans
    }

    fn partition_call_result(&self, call: CoreId, fields: &[u32], mut loan: ProjectionLoan) -> ProjectionLoan {
        let empty = ElaboratedInterface::default();
        let mut leaves = vec![];
        if crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty),
            &self.body.expression(call).ty, &mut vec![], &mut leaves).is_ok()
            && let Some((path, Type::Reference { mutability, .. })) = leaves.iter().find(|(path, _)| crate::core::reference_path_matches(path, fields)) {
            loan.unique = matches!(mutability, crate::Mutability::Unique);
            if leaves.len() > 1 || path.contains(&crate::core::REFERENCE_PATH_ARRAY_ELEMENT) {
                loan.partitions.insert(call, fields.to_vec());
            }
        }
        loan
    }

    /// Establish a distinct referent only from an already checked external or
    /// unsafe construction contract. Raw pointer bits and unknown locals never
    /// reach this path. Forwarding that reference preserves this root rather
    /// than dropping its provenance as if it could not be reborrowed.
    fn external_reference_loans(&self, call: CoreId, fields: &[u32]) -> BTreeSet<ProjectionLoan> {
        let empty = ElaboratedInterface::default();
        let mut leaves = vec![];
        let _ = crate::core::reference_leaf_paths(self.signatures.unwrap_or(&empty),
            &self.body.expression(call).ty, &mut vec![], &mut leaves);
        let Some((_, Type::Reference { mutability, .. })) = leaves.into_iter().find(|(path, _)| crate::core::reference_path_matches(path, fields)) else {
            return BTreeSet::new();
        };
        BTreeSet::from([ProjectionLoan {
            place: Projection { root: format!("<external-reference-result-{}>", call.0), fields: fields.to_vec() },
            unique: matches!(mutability, crate::Mutability::Unique), owner: None,
            partitions: BTreeMap::new(), indirect: true, external: true,
        }])
    }

    fn external_reference_path(&self, id: CoreId) -> bool {
        match &self.body.expression(id).kind {
            CoreKind::Call {
                reference_origin: CallReferenceOrigin::External | CallReferenceOrigin::Unsafe,
                ..
            }
            | CoreKind::Perform {
                reference_origin: CallReferenceOrigin::External,
                ..
            } => true,
            CoreKind::Field { base, .. } => self.external_reference_path(*base),
            _ => false,
        }
    }

    /// Handler payload binders are ordinary branch locals, but their backing
    /// loan comes from the suspended operation's frozen caller-region path.
    /// Install that alias before analysing the arm so reborrows, forwarding,
    /// cancellation, and scope exit all see the same loan identity.
    fn handler_payload_transfers(
        &self,
        computation: CoreId,
        clause: &crate::core::CoreHandlerClause,
    ) -> Vec<PatternBindingTransfer> {
        let CoreKind::Perform {
            effect,
            operation,
            arguments,
            ..
        } = self.body.expression(computation).kind.clone()
        else {
            return self.call_handler_payload_transfers(computation, clause);
        };
        if effect != clause.effect || operation != clause.operation {
            return vec![];
        }
        clause.patterns.iter().zip(arguments).flat_map(|(pattern, argument)| {
            // Perform already transferred the caller's arguments. The
            // handler owns the payload, not a second move from that caller.
            self.pattern_binding_transfers(argument, pattern, &clause.bindings, false)
        }).collect()
    }

    /// An indirect callee's sealed effect row carries the same declaration
    /// regions as its parameters, including higher-ranked binders. Relate the
    /// operation payload to those parameters before consulting actual loans;
    /// never infer its backing storage from the handler binder's spelling or
    /// the caller's erased local lifetimes.
    fn call_handler_payload_transfers(
        &self, computation: CoreId, clause: &crate::core::CoreHandlerClause,
    ) -> Vec<PatternBindingTransfer> {
        let Some(signatures) = self.signatures else { return vec![]; };
        let CoreKind::Call { callee, arguments, .. } = &self.body.expression(computation).kind else {
            return vec![];
        };
        let Type::Callable { parameters, effects, .. } = &self.body.expression(*callee).ty else {
            return vec![];
        };
        if !effects.tails.is_empty() || !effects.projections.is_empty() {
            return vec![];
        }
        let Some(crate::ElaboratedHeader::Effect(declaration)) =
            signatures.definitions.get(&clause.effect.definition) else { return vec![]; };
        let Some(operation) = declaration.operations.get(clause.operation as usize) else { return vec![]; };
        let mut paths = vec![];
        for effect in effects.effects.iter().filter(|effect| effect.definition == clause.effect.definition) {
            let Ok((_, operation)) = signatures.instantiate_effect_operation_generic(
                effect.definition, &effect.arguments, &[], &operation.name,
            ) else { return vec![]; };
            let origin = crate::core::callable_reference_origin_from_contract(
                signatures, parameters, &Type::Tuple(operation.parameters),
            );
            match origin {
                CallReferenceOrigin::Paths(incoming) => paths.extend(incoming),
                CallReferenceOrigin::None | CallReferenceOrigin::External => {},
                // A callee-local or otherwise unproven payload cannot be
                // promoted to one of the known caller regions.
                CallReferenceOrigin::Opaque | CallReferenceOrigin::Unsafe => return vec![],
            }
        }
        let mut transfers = vec![];
        for (payload, pattern) in clause.patterns.iter().enumerate() {
            let mut binders = vec![];
            collect_pattern_binders(pattern, &mut vec![payload as u32], &mut binders);
            for (name, fields) in binders {
                let Some((_, ty)) = clause.bindings.iter().find(|(binding, _)| binding == &name) else { continue; };
                let mut leaves = vec![];
                if crate::core::reference_leaf_paths(signatures, ty, &mut vec![], &mut leaves).is_err() {
                    continue;
                }
                let regions = leaves.iter().map(|(leaf, _)| {
                    let mut source = fields.clone();
                    source.extend_from_slice(leaf);
                    let regions = paths.iter().filter(|path| crate::core::reference_path_matches(&path.result_fields, &source))
                        .flat_map(|path| arguments.get(path.argument as usize).into_iter().flat_map(|argument|
                            self.logical_regions_from_value_path(*argument, &path.argument_fields))).collect();
                    (leaf.clone(), regions)
                }).collect();
                let aliases = leaves.into_iter().map(|(leaf, ty)| {
                    let mut source = fields.clone();
                    source.extend_from_slice(&leaf);
                    let loans = paths.iter().filter(|path| crate::core::reference_path_matches(&path.result_fields, &source))
                        .flat_map(|path| arguments.get(path.argument as usize).into_iter().flat_map(|argument|
                            self.reference_loans_from_value_path(*argument, &path.argument_fields)))
                        .map(|mut loan| {
                            loan.unique = matches!(ty, Type::Reference { mutability: crate::Mutability::Unique, .. });
                            loan
                        }).collect();
                    (leaf, loans)
                }).collect();
                transfers.push(PatternBindingTransfer {
                    name, value: computation, moved: None, borrowed_move: false, aliases, regions,
                });
            }
        }
        transfers
    }

    fn pattern_binding_transfers(
        &self, value: CoreId, pattern: &CorePattern,
        types: &[(String, Type)], move_source: bool,
    ) -> Vec<PatternBindingTransfer> {
        let mut bindings = vec![];
        collect_pattern_binders(pattern, &mut vec![], &mut bindings);
        let empty = ElaboratedInterface::default();
        let signatures = self.signatures.unwrap_or(&empty);
        bindings.into_iter().filter_map(|(name, fields)| {
            let (_, ty) = types.iter().find(|(binding, _)| binding == &name)?;
            let moving = move_source && self.signatures.is_some() && !self.is_duplicable(ty);
            let moved = if moving { self.projection(value).map(|mut place| {
                place.fields.extend_from_slice(&fields);
                place
            }) } else { None };
            let mut root = value;
            while let CoreKind::Field { base, .. } = self.body.expression(root).kind { root = base; }
            let borrowed_move = moving && matches!(self.body.expression(root).kind, CoreKind::Deref(_));
            let mut leaves = vec![];
            let _ = crate::core::reference_leaf_paths(signatures, ty, &mut vec![], &mut leaves);
            leaves.extend(regions::callable_paths(signatures, ty, false));
            let regions = leaves.iter().map(|(leaf, _)| {
                let mut source = fields.clone();
                source.extend_from_slice(leaf);
                (leaf.clone(), self.logical_regions_from_value_path(value, &source))
            }).collect();
            let aliases = leaves.into_iter().map(|(leaf, _)| {
                let mut source = fields.clone();
                source.extend_from_slice(&leaf);
                let loans = self.reference_loans_from_value_path(value, &source);
                (leaf, loans)
            }).collect();
            Some(PatternBindingTransfer { name, value, moved, borrowed_move, aliases, regions })
        }).collect()
    }

    fn install_refinement_bindings(&mut self, refinement: &crate::core::CoreRefinementBranch) {
        let mut binders = vec![];
        collect_pattern_binders(&refinement.pattern, &mut vec![], &mut binders);
        let mut types = vec![];
        let _ = crate::core::collect_pattern_binding_types(&refinement.pattern,
            &self.body.expression(refinement.subject).ty, &mut types);
        for (name, fields) in binders {
            let Some((_, ty)) = types.iter().find(|(spelling, _)| spelling == &name) else { continue; };
            let owner = self.resolve_name(&name);
            if crate::core::refinement_binding_type(ty.clone()) == *ty {
                for parent in self.reference_loans_from_value_path(refinement.subject, &fields) {
                    self.install_reference_alias(&owner, parent, refinement.subject);
                }
            } else if let Some(mut place) = self.projection(refinement.subject) {
                place.fields.extend_from_slice(&fields);
                self.borrow_projection(place, false, self.body.expression(refinement.subject).span, Some(owner));
            } else {
                let mut subject = refinement.subject;
                let mut projection = vec![];
                while let CoreKind::Field { base, index, .. } = self.body.expression(subject).kind {
                    projection.push(index);
                    subject = base;
                }
                projection.reverse();
                projection.extend_from_slice(&fields);
                if let CoreKind::Deref(reference) = self.body.expression(subject).kind {
                    self.use_deref_reference(reference, self.body.expression(subject).span, false);
                    for mut parent in self.reference_loans_from_value(reference) {
                        parent.place.fields.extend_from_slice(&projection);
                        parent.unique = false;
                        self.install_reference_alias(&owner, parent, refinement.subject);
                    }
                } else {
                    self.error(self.body.expression(refinement.subject).span, "G5023",
                        "borrowed refinement requires a tracked subject place".into());
                }
            }
        }
    }

    fn install_pattern_transfers(&mut self, transfers: Vec<PatternBindingTransfer>) {
        // Invalidate all selected source slots before transferring their
        // nested loans. A moved owner must not remain a reborrow parent.
        for transfer in &transfers {
            let span = self.body.expression(transfer.value).span;
            if transfer.borrowed_move {
                self.error(span, "G5004", "an owning pattern cannot move a non-Copy field through a borrow".into());
            } else if let Some(place) = &transfer.moved {
                self.move_projection(place.clone(), span);
            }
        }
        for transfer in transfers {
            let name = self.resolve_name(&transfer.name);
            for (leaf, regions) in transfer.regions {
                if !regions.is_empty() { self.logical.origins.entry(projection_key(&name, &leaf)).or_default().extend(regions); }
            }
            for (leaf, parents) in transfer.aliases {
                let destination = projection_key(&name, &leaf);
                for parent in parents {
                    self.install_reference_alias(&destination, parent, transfer.value);
                }
            }
        }
        self.release_vacated_reference_loans(self.body.expression(self.body.root).span);
    }

    fn release_vacated_reference_loans(&mut self, span: Span) {
        let vacated = self.projection_loans.iter().filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| self.origin_has_been_moved(owner)).cloned().collect::<BTreeSet<_>>();
        for owner in vacated {
            self.release_owner_loans(&owner, span);
        }
    }

    fn install_reference_alias(&mut self, result: &str, parent: ProjectionLoan, source: CoreId) {
        let alias = ProjectionLoan {
            place: parent.place.clone(),
            unique: parent.unique,
            owner: Some(result.to_owned()),
            partitions: parent.partitions.clone(),
            indirect: parent.indirect,
            external: parent.external,
        };
        self.reference_origins
            .entry(result.to_owned()).or_default().insert(alias.clone());
        if !self.projection_loans.contains(&alias) {
            self.projection_loans.push(alias);
        }
        if let Some(owner) = parent.owner.filter(|owner| owner != result) {
            if self.origin_has_been_moved(&owner) {
                // Moving a reference-bearing owner transfers its backing
                // loans; it must not suspend the now-vacant source slot.
                // Retain any external ancestor that was already suspended.
                let parents = self.reference_ancestors(&owner).into_iter()
                    .filter(|parent| !self.origin_has_been_moved(parent)).collect::<BTreeSet<_>>();
                self.reborrow_parents.entry(result.to_owned()).or_default().extend(parents);
            } else {
                self.reborrow_parents.entry(result.to_owned()).or_default().insert(owner);
            }
        }
        self.event(
            FlowEventKind::Reborrow(parent.place.root),
            self.body.expression(source).span,
        );
    }

    fn record_assigned_reference_origin(&mut self, place: &CorePlace, value: CoreId) {
        let Some(key) = self.place_origin_key(place) else {
            return;
        };
        // Evaluate provenance before ending the old resident: self-assignment
        // and projected moves can read precisely the origin being replaced.
        // This transient namespace snapshots the RHS's ordinary frozen facts;
        // it is removed before publishing the new destination's aliases.
        let temporary = format!("<assignment-value-{}>", value.0);
        self.record_aggregate_reference_origins(&temporary, value);
        let under = |candidate: &str, root: &str| candidate == root
            || candidate.strip_prefix(root).is_some_and(|suffix| suffix.starts_with('.'));
        let replacement = self.reference_origins.iter()
            .filter(|(origin, _)| under(origin, &temporary))
            .map(|(origin, _)| (
                format!("{key}{}", &origin[temporary.len()..]),
                self.origin_loans(origin),
                self.reborrow_parents.get(origin).cloned().unwrap_or_default(),
            )).collect::<Vec<_>>();
        let logical_replacement = self.logical.origins.iter()
            .filter(|(origin, _)| under(origin, &temporary))
            .map(|(origin, regions)| (format!("{key}{}", &origin[temporary.len()..]), regions.clone()))
            .collect::<Vec<_>>();
        let old_owners = self.projection_loans.iter().filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| under(owner, &key)).cloned().collect::<BTreeSet<_>>();
        for owner in old_owners { self.release_owner_loans(&owner, self.body.expression(value).span); }
        self.reference_origins.retain(|origin, _| !under(origin, &key));
        self.reborrow_parents.retain(|origin, _| !under(origin, &key));
        self.logical.origins.retain(|origin, _| !under(origin, &key));
        for (destination, regions) in logical_replacement { self.logical.origins.insert(destination, regions); }
        for (destination, loans, parents) in replacement {
            for mut loan in loans {
                loan.owner = Some(destination.clone());
                self.reference_origins.entry(destination.clone()).or_default().insert(loan.clone());
                if !self.projection_loans.contains(&loan) { self.projection_loans.push(loan); }
            }
            // A transferred old resident is not a reborrow of its new self.
            let parents = parents.into_iter().filter(|parent| !under(parent, &key)).collect::<BTreeSet<_>>();
            if !parents.is_empty() { self.reborrow_parents.insert(destination, parents); }
        }
        let temporary_owners = self.projection_loans.iter().filter_map(|loan| loan.owner.as_ref())
            .filter(|owner| under(owner, &temporary)).cloned().collect::<BTreeSet<_>>();
        for owner in temporary_owners { self.release_owner_loans(&owner, self.body.expression(value).span); }
        self.reference_origins.retain(|origin, _| !under(origin, &temporary));
        self.reborrow_parents.retain(|origin, _| !under(origin, &temporary));
        self.logical.origins.retain(|origin, _| !under(origin, &temporary));
    }

    fn place_origin_key(&self, place: &CorePlace) -> Option<String> {
        match place {
            CorePlace::Local { name, .. } => Some(self.resolve_name(name)),
            CorePlace::Field { base, index, .. } => {
                let mut key = self.place_origin_key(base)?;
                key.push('.');
                key.push_str(&index.to_string());
                Some(key)
            }
            CorePlace::Deref { reference, .. } => {
                // A unique handle with one known local referent writes that
                // resident's reference fields. Caller-owned or dynamically
                // selected referents are not a single lexical assignment.
                let loans = self.reference_loans_from_value(*reference);
                if loans.iter().any(|loan| loan.indirect || loan.external) { return None; }
                let places = loans.into_iter().map(|loan| loan.place).collect::<BTreeSet<_>>();
                if places.len() != 1 { return None; }
                let place = places.into_iter().next()?;
                Some(projection_key(&place.root, &place.fields))
            }
            CorePlace::Error => None,
        }
    }

    /// Detect the intentionally narrow source form `move *reference`.
    /// `reference` must be one lexical unique-reference local; moving through
    /// an aggregate field, temporary, or arbitrary dereference expression is
    /// not a whole-referent move and remains subject to the ordinary move
    /// rules.
    fn direct_unique_reference_key(&self, id: CoreId) -> Option<String> {
        let CoreKind::Local(name) = &self.body.expression(id).kind else {
            return None;
        };
        matches!(
            self.body.expression(id).ty,
            crate::types::Type::Reference {
                mutability: crate::types::Mutability::Unique,
                ..
            }
        )
        .then(|| self.resolve_name(name))
    }

    /// Open the temporary uninitialized-referent state produced by
    /// `move *reference`.  The reference handle itself remains initialized,
    /// but no ordinary use, alias, call argument, effect boundary, or scope
    /// exit may observe it until the exact dereference place is restored.
    /// Returns `true` when `value` was this dedicated source form, including
    /// a malformed use which has already received its focused diagnostic.
    fn open_whole_referent_hole(&mut self, value: CoreId, span: Span) -> bool {
        let CoreKind::Deref(reference) = self.body.expression(value).kind else {
            return false;
        };
        let Some(reference) = self.direct_unique_reference_key(reference) else {
            self.error(
                span,
                "G5004",
                "move through a dereference requires one direct live unique-reference local"
                    .into(),
            );
            return true;
        };
        if self.open_referent_holes.contains_key(&reference) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot move through unique reference `{reference}` while its referent is uninitialized"
                ),
            );
            return true;
        }
        if !matches!(self.states.get(&reference), Some(LocalState::Initialized)) {
            self.error(
                span,
                "G5004",
                format!("cannot move through unavailable unique reference `{reference}`"),
            );
            return true;
        }
        if self.live_child_reborrow_descends_from(&reference) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot move through unique reference `{reference}` while a child reborrow is live"
                ),
            );
            return true;
        }
        self.open_referent_holes.insert(reference, span);
        true
    }

    /// The only operation which closes a whole-referent hole is assignment to
    /// the exact direct `*reference` place.  A field projection below that
    /// dereference remains an ordinary partial write and cannot make the
    /// uninitialized whole referent usable again.
    fn restore_whole_referent_hole(&mut self, place: &CorePlace, span: Span) {
        let CorePlace::Deref { reference, unique, .. } = place else {
            return;
        };
        if !unique {
            return;
        }
        let Some(reference) = self.direct_unique_reference_key(*reference) else {
            return;
        };
        if !self.open_referent_holes.contains_key(&reference) {
            return;
        }
        if self.live_child_reborrow_descends_from(&reference) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot restore unique reference `{reference}` while a child reborrow is live"
                ),
            );
            return;
        }
        self.open_referent_holes.remove(&reference);
    }

    fn reject_open_referent_holes(&mut self, span: Span, message: &str) {
        let references = self
            .open_referent_holes
            .keys()
            .cloned()
            .collect::<Vec<_>>();
        for reference in references {
            self.error(span, "G5004", format!("{message}: `{reference}`"));
        }
    }

    fn use_deref_reference(&mut self, id: CoreId, span: Span, mutation: bool) {
        self.use_projected_deref_reference(id, &[], span, mutation);
    }

    fn projected_dereference(&self, mut id: CoreId) -> Option<(CoreId, Vec<u32>)> {
        let mut fields = vec![];
        while let CoreKind::Field { base, index, .. } = self.body.expression(id).kind {
            fields.push(index);
            id = base;
        }
        let CoreKind::Deref(reference) = self.body.expression(id).kind else { return None; };
        fields.reverse();
        Some((reference, fields))
    }

    fn use_projected_deref_reference(&mut self, id: CoreId, fields: &[u32], span: Span, mutation: bool) {
        let key = self.reference_origin_key(id);
        let name = key.clone().unwrap_or_else(|| format!("<reference-value-{}>", id.0));
        // A shared view of an affine reference borrows the carrier itself,
        // not its referent. Its loan therefore cannot overlap the referent
        // loans checked below. Using the unique capability while that view
        // is live would bypass the suspension established by `&reference`.
        if matches!(self.body.expression(id).ty, Type::Reference { mutability: crate::Mutability::Unique, .. })
            && self.projection(id).is_some_and(|carrier|
                self.projection_loans.iter().any(|loan| !loan.indirect && loan.place.overlaps(&carrier)
                    && (mutation || loan.unique))) {
            self.error(span, "G5004", format!("cannot access unique reference `{name}` while its carrier is borrowed"));
            return;
        }
        if self.open_referent_holes.contains_key(&name) {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot access through unique reference `{name}` while its referent is uninitialized"
                ),
            );
            return;
        }
        let parents = self.reference_loans_from_value(id);
        if parents.is_empty() {
            return;
        }
        // A dereference may name a reference stored in an aggregate rather
        // than a standalone local (`*holder.0`).  Follow the reborrow chain
        // by identity and admit the exact frozen backing loan for each
        // ancestor.  This permits a child reborrow to use its own suspended
        // parent while still rejecting access through that parent while the
        // child is live.
        let mut allowed_owners = self.reference_ancestors(&name);
        if key.is_none() {
            for parent in &parents {
                if let Some(owner) = &parent.owner { allowed_owners.extend(self.reference_ancestors(owner)); }
            }
        }
        let allowed_origin_loans = allowed_owners
            .iter()
            .flat_map(|owner| self.reference_origins.get(owner).into_iter().flatten())
            .cloned()
            .collect::<BTreeSet<_>>();
        let parents = parents.into_iter().map(|mut parent| {
            parent.place.fields.extend_from_slice(fields);
            parent
        }).collect::<Vec<_>>();
        let conflicts = self.projection_loans.iter().any(|loan| {
            !loan
                .owner
                .as_ref()
                .is_some_and(|owner| allowed_owners.contains(owner))
                && !allowed_origin_loans.contains(loan)
                && parents.iter().any(|parent| loan.indirect == parent.indirect && loan.place.overlaps(&parent.place)
                    && !loan.disjoint_from(parent)
                    && (mutation || parent.unique || loan.unique))
        });
        if conflicts {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot access reborrowed place `{}` through its suspended parent",
                    name
                ),
            );
        }
    }

    fn assign_place(&mut self, place: &CorePlace, span: Span) {
        // A reborrow suspends the *reference carrier* as well as access to
        // the backing referent.  It is not enough to reject `*parent = ...`:
        // replacing `holder.loan` (or the aggregate containing it) while
        // `child = &mut *holder.loan` remains live would discard the parent
        // capability from which the child was derived.  The VM happens to
        // retain the copied target today, but that implementation detail must
        // not weaken the source ownership contract.
        //
        // Reference origins are canonical static paths, so this catches both
        // the exact slot and any enclosing aggregate replacement while
        // preserving disjoint sibling updates.  Only a live projection loan
        // may trigger the error: NLL release of the child before this store
        // deliberately reopens the carrier for a new reference.
        if let Some(carrier) = self.place_origin_key(place)
            && self.live_reborrow_descends_from(&carrier)
        {
            self.error(
                span,
                "G5004",
                format!(
                    "cannot replace reference carrier `{carrier}` while a child reborrow is live"
                ),
            );
            return;
        }
        let Some(projection) = self.place_projection(place) else {
            return;
        };
        self.check_minimum_assignment(&projection, &place.ty(), span);
        if self
            .projection_loans
            .iter()
            .any(|loan| !loan.indirect && loan.place.overlaps(&projection))
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

    /// Whether a currently-live child loan is descended from a reference
    /// carried by `carrier`. `reborrow_parents` intentionally retains the
    /// stable ancestry graph beyond NLL release for joins and diagnostics;
    /// therefore the projection-loan owner is the liveness authority here.
    fn live_reborrow_descends_from(&self, carrier: &str) -> bool {
        self.projection_loans.iter().any(|loan| {
            let Some(owner) = &loan.owner else {
                return false;
            };
            // The carrier owns these loans and its replacement destroys
            // them together. Only an independently live descendant can
            // suspend replacement; the carrier is not its own reborrow.
            if owner == carrier || owner.strip_prefix(carrier)
                .is_some_and(|suffix| suffix.starts_with('.'))
            {
                return false;
            }
            self.reference_ancestors(owner).iter().any(|ancestor| ancestor == carrier
                    || ancestor
                        .strip_prefix(carrier)
                        .is_some_and(|suffix| suffix.starts_with('.')))
        })
    }

    /// Unlike replacing a reference carrier, moving or restoring its
    /// *referent* is compatible with the carrier's own loan.  Only a distinct
    /// live child reborrow suspends that operation.
    fn live_child_reborrow_descends_from(&self, carrier: &str) -> bool {
        self.projection_loans.iter().any(|loan| {
            let Some(owner) = &loan.owner else {
                return false;
            };
            owner != carrier && self.reference_ancestors(owner).contains(carrier)
        })
    }

    fn join_reborrow_facts(
        &mut self,
        exits: &[ContinuationState],
        incoming: &BTreeMap<String, LocalState>,
    ) {
        self.reborrow_parents.clear();
        self.reference_origins.clear();
        self.logical = LogicalFlow::default();
        for exit in exits {
            let ContinuationState { parents, origins, logical, .. } = exit;
            self.logical.regions.merge_from(&logical.regions, |loans, incoming| loans.extend(incoming));
            for (owner, regions) in &logical.origins {
                self.logical.origins.entry(owner.clone()).or_default().extend(regions.iter().cloned());
            }
            for (child, parents) in parents {
                if incoming.contains_key(child) || self.pending_results.iter().any(|id| {
                    let root = Self::result_owner(*id);
                    *child == root || child.starts_with(&(root + "."))
                }) {
                    self.reborrow_parents.entry(child.clone()).or_default().extend(parents.iter().cloned());
                }
            }
            for (name, loans) in origins {
                self.reference_origins.entry(name.clone()).or_default().extend(loans.iter()
                    .filter(|loan| loan.external || incoming.contains_key(&loan.place.root)).cloned());
            }
        }
    }

    fn error(&mut self, span: Span, code: &'static str, message: String) {
        self.diagnostics.push(FlowDiagnostic {
            code,
            span,
            message,
        })
    }
}

/// Shared source-order control fact for ownership consumers which traverse
/// Typed Core after PlaceFlow. A `true` result means evaluation of this strict
/// expression cannot reach its following sibling; EscapeFlow and UseFlow must
/// therefore not publish borrow, move, escape, or quantitative facts for that
/// syntactic suffix.
pub(crate) fn strict_expression_abrupt(body: &TypedBody, id: CoreId) -> bool {
    Analyzer::abrupt_exit(body, id).is_some()
}

/// A generic body is checked once, before every VM instance materializes its
/// type argument. An open `T` cannot itself name a body-local reference: a
/// concrete use is checked at its call boundary after instantiation. Do not
/// turn that deferred proof obligation into a false-positive in the generic
/// declaration, while keeping opaque projections and concrete aggregates
/// fail-closed.
fn contains_open_type_parameter(value: &crate::types::Type) -> bool {
    match value {
        crate::types::Type::FixedArray { element, length } => contains_open_type_parameter(element)
            || generic_argument_contains_open_type_parameter(length),
        crate::types::Type::Generic(_) => true,
        crate::types::Type::Tuple(values) => values.iter().any(contains_open_type_parameter),
        crate::types::Type::Array(value)
        | crate::types::Type::StaticData { element: value, .. }
        | crate::types::Type::Reference {
            referent: value, ..
        } => contains_open_type_parameter(value),
        crate::types::Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(generic_argument_contains_open_type_parameter),
        crate::types::Type::Callable {
            parameters, result, ..
        } => {
            parameters.iter().any(contains_open_type_parameter)
                || contains_open_type_parameter(result)
        }
        crate::types::Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            contains_open_type_parameter(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
                || item_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
        }
        crate::types::Type::Infer(_)
        | crate::types::Type::Unit
        | crate::types::Type::RawPointer { .. }
        | crate::types::Type::Never
        | crate::types::Type::Scalar(_)
        | crate::types::Type::ConstInteger(_)
        | crate::types::Type::ConstQuantity(_)
        | crate::types::Type::ConstGeneric { .. }
        | crate::types::Type::Error => false,
    }
}

fn generic_argument_contains_open_type_parameter(value: &crate::types::GenericArgument) -> bool {
    match value {
        crate::types::GenericArgument::Type(value) => contains_open_type_parameter(value),
        crate::types::GenericArgument::EffectRow(row) => {
            effect_row_contains_open_type_parameter(row)
        }
        crate::types::GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            contains_open_type_parameter(subject)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_open_type_parameter)
        }
        crate::types::GenericArgument::Lifetime(_)
        | crate::types::GenericArgument::ConstInteger(_)
        | crate::types::GenericArgument::ConstQuantity(_)
        | crate::types::GenericArgument::ConstGeneric { .. }
        | crate::types::GenericArgument::ConstIntegerExpr(_) => false,
        crate::types::GenericArgument::ConstInfer { .. } => true,
    }
}

fn effect_row_contains_open_type_parameter(row: &crate::types::EffectRow) -> bool {
    row.effects.iter().any(|effect| {
        effect
            .arguments
            .iter()
            .any(generic_argument_contains_open_type_parameter)
    }) || row.projections.iter().any(|projection| {
        contains_open_type_parameter(&projection.subject)
            || projection
                .trait_arguments
                .iter()
                .any(generic_argument_contains_open_type_parameter)
            || projection
                .item_arguments
                .iter()
                .any(generic_argument_contains_open_type_parameter)
    })
}

/// Flatten a frozen pattern to the structural paths owned by each binder.
/// Core patterns retain declaration indices, so this is independent of source
/// spellings and stays valid for generic effect payload/result identities.
fn collect_pattern_binders(
    pattern: &CorePattern,
    prefix: &mut Vec<u32>,
    output: &mut Vec<(String, Vec<u32>)>,
) {
    match pattern {
        CorePattern::Bind { name } => output.push((name.clone(), prefix.clone())),
        CorePattern::Tuple(patterns) => {
            for (index, pattern) in patterns.iter().enumerate() {
                prefix.push(index as u32);
                collect_pattern_binders(pattern, prefix, output);
                prefix.pop();
            }
        }
        CorePattern::Array { elements, rest, .. } => {
            for (index, pattern) in elements.iter().enumerate() {
                let index = crate::pattern::ArrayPatternRest::index(*rest, index);
                prefix.push(index as u32);
                collect_pattern_binders(pattern, prefix, output);
                prefix.pop();
            }
        }
        CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
            for field in fields {
                prefix.push(field.index);
                collect_pattern_binders(&field.pattern, prefix, output);
                prefix.pop();
            }
        }
        CorePattern::Any | CorePattern::Literal(_) | CorePattern::Error => {}
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
    exits: &[ContinuationState],
    incoming: &BTreeMap<String, LocalState>,
) -> Vec<ProjectionLoan> {
    let mut loans = exits
        .iter()
        .flat_map(|exit| &exit.loans)
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
    exits: &[ContinuationState],
    incoming: &BTreeMap<String, LocalState>,
) -> BTreeSet<Projection> {
    let mut moves = exits
        .iter()
        .flat_map(|exit| &exit.moves)
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

/// A dynamically selected handler/completion arm can leave a direct unique
/// reference's referent moved out.  Retain that hole after the join whenever
/// any reachable arm leaves an incoming reference open; a sibling restoration
/// is not proof that the next ordinary expression may use the handle.
fn join_handler_referent_holes(
    exits: &[ContinuationState],
    incoming: &BTreeMap<String, LocalState>,
) -> BTreeMap<String, Span> {
    exits
        .iter()
        .flat_map(|exit| &exit.holes)
        .filter(|(reference, _)| incoming.contains_key(*reference))
        .map(|(reference, span)| (reference.clone(), *span))
        .collect()
}
