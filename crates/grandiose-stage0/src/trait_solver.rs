//! Deterministic tabled solving for ordinary, coherent source traits.
//!
//! This is intentionally a compact kernel: it operates only on frozen
//! interfaces, returns declaration-key evidence, and never walks source or
//! body arenas.  Associated projections, HRTBs, and inference variables build
//! on the same goal/table boundary later.

use std::{collections::{BTreeMap, BTreeSet}, sync::Arc};

use crate::{
    CallableSignature, DefKey, Digest, EffectInstance, EffectRow, ElaboratedEnumVariantPayload,
    ElaboratedHeader, ElaboratedImplementation, ElaboratedInterface, ElaboratedNominalLayout,
    ElaboratedTrait, ElaboratedTraitReference, GenericArgument, Lifetime, Type, implementation_method_key,
    signature::{
        TRAIT_SELF_GENERIC, is_intrinsic_callable_trait, is_intrinsic_label_trait,
        is_intrinsic_runs_in_trait,
    },
    types::{canonical_generic_arguments_encoding, canonical_type_encoding},
};

pub const DEFAULT_MAX_TRAIT_DEPTH: u32 = 128;
pub const DEFAULT_MAX_TRAIT_STEPS: u32 = 1_000_000;
mod contracts;
mod callable;
pub(crate) mod variance;

// Structural performance regression accounting, not wall-clock assertions.
// Thread-local state keeps concurrently running compiler tests independent.
#[cfg(test)]
std::thread_local! {
    static SNAPSHOT_BUILDS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn snapshot_builds() -> usize {
    SNAPSHOT_BUILDS.with(std::cell::Cell::get)
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitGoal {
    pub relation: ElaboratedTraitReference,
    pub subject: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitGoalQuery {
    pub fingerprint: Digest,
    pub trait_definition: DefKey,
    pub candidate_implementations: Vec<DefKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitAnswer {
    Proven { evidence: DefKey },
    Refuted { evidence: DefKey },
    NoSolution,
    Ambiguous,
    Overflow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitCandidateExplanation {
    Applicable {
        implementation: DefKey,
        negative: bool,
        where_bounds: Vec<TraitWhereBoundExplanation>,
    },
    Rejected {
        implementation: DefKey,
        reason: TraitCandidateRejection,
    },
    /// Implicit field traversal for a source-declared auto trait. The
    /// evidence is synthesized from the canonical goal and therefore is as
    /// stable and cacheable as ordinary implementation evidence.
    Structural {
        evidence: DefKey,
        obligations: Vec<TraitWhereBoundExplanation>,
    },
}

/// One implementation where-bound after the candidate's head substitution.
/// The nested goal and its canonical solver outcome are retained together so
/// callers can explain a rejected candidate without reconstructing a second
/// substitution environment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitWhereBoundExplanation {
    pub goal: TraitGoal,
    pub outcome: TraitAnswer,
    /// Recursive evidence for this obligation.  This keeps a cycle or limit
    /// cause attached to the exact where-bound that produced it rather than
    /// requiring a caller to reconstruct solver traversal from a flat list.
    pub explanation: Box<TraitSelectionExplanation>,
}

/// Why a trait implementation was not an applicable candidate for one goal.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitCandidateRejection {
    HeadMismatch,
    WhereBound {
        outcomes: Vec<TraitWhereBoundExplanation>,
    },
    AssociatedBinding { outcome: TraitAnswer },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitSelectionExplanation {
    pub goal: TraitGoal,
    pub answer: TraitAnswer,
    pub candidates: Vec<TraitCandidateExplanation>,
    /// A terminal cause is present only when this tree leaf stopped before
    /// candidate selection could complete normally.
    pub terminal: Option<TraitExplanationTerminal>,
}

/// Cycle semantics available to the current source-trait kernel.  Ordinary
/// traits are inductive: re-entering an active goal is ambiguous. Source
/// `auto trait` declarations add a separate structural coinductive policy.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TraitCyclePolicy {
    Inductive,
    CoinductiveAuto,
}

/// A finite explanation-tree leaf produced by recursive goal evaluation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitExplanationTerminal {
    OrdinaryCycle {
        reentered: TraitGoal,
        policy: TraitCyclePolicy,
    },
    DepthLimit {
        limit: u32,
    },
    StepLimit {
        limit: u32,
    },
}

/// The result of normalizing a zero-arity associated type through selected
/// trait evidence.  This deliberately mirrors [`TraitAnswer`] rather than
/// hiding failed selection behind an error type: callers need to distinguish a
/// negative implementation, ambiguity, and a missing associated item when
/// explaining a projection constraint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitProjectionAnswer {
    Normalized {
        evidence: DefKey,
        ty: Type,
    },
    Refuted {
        evidence: DefKey,
    },
    NoSolution,
    Ambiguous,
    Overflow,
    MissingAssociatedType {
        evidence: DefKey,
    },
    AssociatedTypeArity {
        evidence: DefKey,
        expected: u32,
        found: u32,
    },
    /// Normalizing an associated type led back to a projection already being
    /// normalized.  Recursive projection values have no finite normal form,
    /// so callers must report an error rather than preserving a misleading
    /// symbolic type in an executable interface.
    RecursiveProjection,
    /// A row inside a callable or a kinded argument failed normalization.
    NestedEffectRowProjection {
        answer: Box<TraitEffectRowProjectionAnswer>,
    },
}

/// The row-kinded counterpart of [`TraitProjectionAnswer`]. Keeping it
/// separate makes it impossible for an associated effect row to cross a
/// value-type normalization boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitEffectRowProjectionAnswer {
    Normalized {
        evidence: DefKey,
        row: EffectRow,
    },
    Refuted {
        evidence: DefKey,
    },
    NoSolution,
    Ambiguous,
    Overflow,
    MissingAssociatedEffectRow {
        evidence: DefKey,
    },
    AssociatedEffectRowArity {
        evidence: DefKey,
        expected: u32,
        found: u32,
    },
    /// A type projection nested in an associated effect-row head could not
    /// be normalized.  A row answer cannot silently retain that failure:
    /// doing so would make the row's effect identity depend on which caller
    /// happened to inspect it first.
    NestedTypeProjection {
        answer: Box<TraitProjectionAnswer>,
    },
    /// An associated effect row reduced back to a projection already on the
    /// active normalization stack.  As with associated value types, there is
    /// no finite normal form to expose to a callable contract.
    RecursiveProjection,
}

/// The structural-constant counterpart of associated type normalization.
/// Keeping this separate from [`TraitProjectionAnswer`] prevents a selected
/// `u32` or quantity from being treated as a value type by Core or the VM.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitConstProjectionAnswer {
    Normalized {
        evidence: DefKey,
        value: GenericArgument,
    },
    Refuted {
        evidence: DefKey,
    },
    NoSolution,
    Ambiguous,
    Overflow,
    MissingAssociatedConst {
        evidence: DefKey,
    },
    AssociatedConstKind {
        evidence: DefKey,
        expected: crate::ConstKind,
        found: crate::ConstKind,
    },
}

/// Selected implementation method evidence with all implementation and method
/// generic slots substituted for one concrete call site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitMethodAnswer {
    Selected {
        /// Stable identity of the selected implementation method. This is
        /// separate from its implementation evidence because later body/MIR
        /// products are callable functions, not implementation declarations.
        method: DefKey,
        evidence: DefKey,
        signature: Box<CallableSignature>,
    },
    Refuted {
        evidence: DefKey,
    },
    NoSolution,
    Ambiguous,
    Overflow,
    MissingMethod {
        evidence: DefKey,
    },
    MethodArity {
        evidence: DefKey,
        expected: u32,
        found: u32,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitSolverLimits {
    pub max_depth: u32,
    pub max_steps: u32,
}

impl Default for TraitSolverLimits {
    fn default() -> Self {
        Self {
            max_depth: DEFAULT_MAX_TRAIT_DEPTH,
            max_steps: DEFAULT_MAX_TRAIT_STEPS,
        }
    }
}

#[derive(Clone)]
struct Rule {
    definition: DefKey,
    implementation: ElaboratedImplementation,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TableState {
    Evaluating,
    Complete(TraitAnswerIndex),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum TraitAnswerIndex {
    Proven(DefKey),
    Refuted(DefKey),
    NoSolution,
    Ambiguous,
    Overflow,
}

impl From<TraitAnswerIndex> for TraitAnswer {
    fn from(value: TraitAnswerIndex) -> Self {
        match value {
            TraitAnswerIndex::Proven(evidence) => Self::Proven { evidence },
            TraitAnswerIndex::Refuted(evidence) => Self::Refuted { evidence },
            TraitAnswerIndex::NoSolution => Self::NoSolution,
            TraitAnswerIndex::Ambiguous => Self::Ambiguous,
            TraitAnswerIndex::Overflow => Self::Overflow,
        }
    }
}

/// Select from coherent candidates without letting an ordinary inductive
/// cycle hide a hard resource exhaustion. A proven/refuted candidate remains
/// sufficient evidence even when another candidate could not be explored.
fn select_answer(
    positives: &[DefKey],
    negatives: &[DefKey],
    saw_cycle: bool,
    saw_overflow: bool,
) -> TraitAnswerIndex {
    match (positives, negatives) {
        // A coherent interface has at most one applicable answer across both
        // polarities. Treat contradictory input as ambiguity so an unchecked
        // coherence failure cannot make selection order matter.
        ([..], [..]) if !positives.is_empty() && !negatives.is_empty() => {
            TraitAnswerIndex::Ambiguous
        }
        ([], []) if saw_overflow => TraitAnswerIndex::Overflow,
        ([], []) if saw_cycle => TraitAnswerIndex::Ambiguous,
        ([], []) => TraitAnswerIndex::NoSolution,
        ([definition], []) => TraitAnswerIndex::Proven(*definition),
        ([], [definition]) => TraitAnswerIndex::Refuted(*definition),
        _ => TraitAnswerIndex::Ambiguous,
    }
}

/// A per-body solver cache.  It can be discarded with the caller's body
/// scratch; every entry is keyed by a span-free canonical goal digest.
#[derive(Clone)]
pub struct TraitSolver {
    rules: Arc<Vec<Rule>>,
    /// Manual Use rules are nominal-headed. Index those heads once in the
    /// same immutable snapshot as the rules, rather than rescanning every
    /// source declaration for each structural ownership query.
    manual_use_nominals: Arc<BTreeSet<DefKey>>,
    /// Trait declarations carry associated-item defaults.  The solver owns a
    /// frozen copy alongside implementation rules so projection selection
    /// remains self-contained and deterministic.
    traits: Arc<BTreeMap<DefKey, ElaboratedTrait>>,
    /// Frozen layouts are needed for source-declared auto traits to turn a
    /// nominal application into its field obligations. Keeping them in the
    /// solver preserves the same body-local, interface-only boundary as impl
    /// rule selection.
    definitions: Arc<BTreeMap<DefKey, ElaboratedHeader>>,
    nominal_variances: Arc<std::sync::OnceLock<Arc<variance::NominalVariances>>>,
    tables: BTreeMap<Digest, TableState>,
    /// Principal ownership queries share the trait query's budget and lexical
    /// environment. This stack also cuts mixed `Use`/ordinary-trait cycles.
    principal_active: Vec<Type>,
    limits: TraitSolverLimits,
    steps: u32,
    assumed_type_bindings: Arc<Vec<crate::ElaboratedAssociatedTypeBinding>>,
    assumed_effect_bindings: Arc<Vec<crate::ElaboratedAssociatedEffectBinding>>,
    /// Immutable lexical facts for implementation-contract normalization only.
    /// Changing this environment invalidates all goal-only table entries.
    lexical_assumptions: Arc<Vec<TraitGoal>>,
    lexical_outlives: Arc<Vec<crate::OutlivesPredicate>>,
    lexical_universal: Arc<Vec<crate::QuantifiedWhereBound>>,
    quantified_inference: crate::InferContext,
    quantified_depth: u32,
    active_domains: Vec<Digest>,
    /// Compiler-issued environments reachable from this query's callable
    /// values. These are query-local witnesses, never source impl rules.
    callable_environments: Vec<Type>,
}

/// Declared Use is permission at an opaque source boundary. A closed resident
/// can additionally carry a sealed physical capture layout. The same nominal
/// restriction and structural rules apply to both; resident refinements cannot
/// prove a source trait prerequisite while selecting a manual Use declaration.
#[derive(Clone, Copy)]
enum UseEvidence { Declared, Resident }

/// A parametric query abstracts only caller-owned lifetime inference cells.
/// Other unsolved kinds remain unsolved; existing region binders shift without
/// capture. A successful result is opened back into the very same cells.
#[derive(Default)]
struct ParametricRegions {
    inputs: Vec<Lifetime>,
    indices: BTreeMap<Lifetime, u32>,
}

impl ParametricRegions {
    fn abstract_argument(&mut self, value: GenericArgument, outer_depth: u32) -> Option<GenericArgument> {
        crate::types::regions::map_argument_regions(value, &mut |region, depth| {
            let cutoff = depth.checked_add(outer_depth)?;
            Some(match region {
                Lifetime::Infer(_) => {
                    let index = if let Some(index) = self.indices.get(&region) { *index } else {
                        let index = u32::try_from(self.inputs.len()).ok()?;
                        self.inputs.push(region);
                        self.indices.insert(region, index);
                        index
                    };
                    Lifetime::Bound { depth: cutoff, index }
                }
                Lifetime::Bound { depth, index } if depth >= cutoff =>
                    Lifetime::Bound { depth: depth.checked_add(1)?, index },
                region => region,
            })
        })
    }

    fn open(&self, value: GenericArgument) -> Option<GenericArgument> {
        crate::types::regions::open_argument(value, |index| self.inputs.get(index as usize).copied())
    }
}

#[derive(Clone, Copy)]
pub(crate) enum AssociatedItemKind {
    Type,
    EffectRow,
    Const,
}

enum SupertraitLookup<T> {
    Found(T),
    Missing,
    Ambiguous,
}

/// True only when the shared kinded normalizer cannot select a projection.
/// This is a no-evidence fast path, not an alternative normalization rule.
pub(crate) fn type_projection_normalization_is_identity(value: &Type) -> bool {
    match value {
        Type::Projection { .. } => false,
        Type::FixedArray { element, length } => type_projection_normalization_is_identity(element)
            && argument_projection_normalization_is_identity(length),
        Type::Nominal { arguments, .. } => arguments.iter().all(argument_projection_normalization_is_identity),
        Type::Tuple(values) => values.iter().all(type_projection_normalization_is_identity),
        Type::Array(value) | Type::Reference { referent: value, .. }
        | Type::RawPointer { pointee: value, .. } | Type::StaticData { element: value, .. } =>
            type_projection_normalization_is_identity(value),
        Type::Callable { contract, parameters, result, effects, .. } =>
            contract.terms().iter().all(|(value, _)| argument_projection_normalization_is_identity(value))
                && parameters.iter().all(type_projection_normalization_is_identity)
                && type_projection_normalization_is_identity(result)
                && row_projection_normalization_is_identity(effects),
        Type::Unit | Type::Never | Type::Scalar(_)
        | Type::ConstInteger(_) | Type::ConstQuantity(_) | Type::ConstGeneric { .. }
        | Type::Generic(_) | Type::Infer(_) | Type::Error => true,
    }
}

fn argument_projection_normalization_is_identity(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => type_projection_normalization_is_identity(value),
        GenericArgument::EffectRow(value) => row_projection_normalization_is_identity(value),
        GenericArgument::ConstProjection { .. } => false,
        _ => true,
    }
}

fn row_projection_normalization_is_identity(value: &EffectRow) -> bool {
    value.projections.is_empty() && value.effects.iter().all(|effect|
        effect.arguments.iter().all(argument_projection_normalization_is_identity))
}

fn trait_declares_associated_item(
    trait_header: &ElaboratedTrait,
    name: &str,
    kind: AssociatedItemKind,
) -> bool {
    match kind {
        AssociatedItemKind::Type => trait_header
            .associated_types
            .get(name)
            .is_some_and(|item| !item.effect_row),
        AssociatedItemKind::EffectRow => trait_header
            .associated_types
            .get(name)
            .is_some_and(|item| item.effect_row),
        AssociatedItemKind::Const => trait_header.associated_consts.contains_key(name),
    }
}

fn merge_supertrait_lookups(
    values: impl IntoIterator<Item = SupertraitLookup<TraitGoal>>,
) -> SupertraitLookup<TraitGoal> {
    let mut found = Vec::new();
    let mut ambiguous = false;
    for value in values {
        match value {
            SupertraitLookup::Found(goal) => {
                if !found.iter().any(|candidate: &TraitGoal| candidate == &goal) {
                    found.push(goal);
                }
            }
            SupertraitLookup::Ambiguous => ambiguous = true,
            SupertraitLookup::Missing => {}
        }
    }
    if ambiguous || found.len() > 1 {
        SupertraitLookup::Ambiguous
    } else if let Some(goal) = found.pop() {
        SupertraitLookup::Found(goal)
    } else {
        SupertraitLookup::Missing
    }
}

impl TraitSolver {
    pub fn new(signatures: &ElaboratedInterface) -> Self {
        Self::with_limits(signatures, TraitSolverLimits::default())
    }

    pub fn with_limits(signatures: &ElaboratedInterface, limits: TraitSolverLimits) -> Self {
        #[cfg(test)]
        SNAPSHOT_BUILDS.with(|count| count.set(count.get() + 1));
        let mut rules = signatures
            .definitions
            .iter()
            .filter_map(|(definition, header)| match header {
                ElaboratedHeader::Implementation(implementation) => Some(Rule {
                    definition: *definition,
                    implementation: implementation.clone(),
                }),
                _ => None,
            })
            .collect::<Vec<_>>();
        rules.sort_by_key(|rule| rule.definition);
        let manual_use_nominals = rules.iter().filter_map(|rule| {
            if rule.implementation.relation.definition != crate::resolution::language_use_trait_definition() {
                return None;
            }
            match &rule.implementation.self_ty {
                Type::Nominal { definition, .. } => Some(*definition),
                _ => None,
            }
        }).collect();
        let traits = signatures
            .definitions
            .iter()
            .filter_map(|(definition, header)| match header {
                ElaboratedHeader::Trait(trait_header) => Some((*definition, trait_header.clone())),
                _ => None,
            })
            .collect();
        Self {
            rules: Arc::new(rules),
            manual_use_nominals: Arc::new(manual_use_nominals),
            traits: Arc::new(traits),
            // Queries need nominal layouts and effect-family domains, not
            // ordinary source callable/value headers. Rules and traits are
            // already frozen above.
            definitions: Arc::new(signatures.definitions.iter().filter_map(|(key, header)| {
                matches!(header, ElaboratedHeader::Nominal { .. } | ElaboratedHeader::Effect(_))
                    .then(|| (*key, header.clone()))
            }).collect()),
            tables: BTreeMap::new(),
            nominal_variances: Arc::new(std::sync::OnceLock::new()),
            principal_active: vec![],
            limits,
            steps: 0,
            assumed_type_bindings: Arc::new(vec![]),
            assumed_effect_bindings: Arc::new(vec![]),
            lexical_assumptions: Arc::new(vec![]),
            lexical_outlives: Arc::new(vec![]),
            lexical_universal: Arc::new(vec![]),
            quantified_inference: crate::InferContext::default(),
            quantified_depth: 0,
            active_domains: vec![],
            callable_environments: vec![],
        }
    }

    /// Start independent body/query scratch over the same immutable interface.
    /// Unlike `Clone`, this never carries answers or spent work into the new
    /// solver. The snapshot must be created after interface mutation ends.
    pub(crate) fn fresh_query(&self) -> Self {
        self.fresh_query_with_limits(self.limits.clone())
    }

    pub(crate) fn fresh_query_with_limits(&self, limits: TraitSolverLimits) -> Self {
        Self {
            rules: Arc::clone(&self.rules),
            manual_use_nominals: Arc::clone(&self.manual_use_nominals),
            traits: Arc::clone(&self.traits),
            definitions: Arc::clone(&self.definitions),
            nominal_variances: Arc::clone(&self.nominal_variances),
            tables: BTreeMap::new(),
            principal_active: vec![],
            limits,
            steps: 0,
            assumed_type_bindings: Arc::clone(&self.assumed_type_bindings),
            assumed_effect_bindings: Arc::clone(&self.assumed_effect_bindings),
            lexical_assumptions: Arc::clone(&self.lexical_assumptions),
            lexical_outlives: Arc::clone(&self.lexical_outlives),
            lexical_universal: Arc::clone(&self.lexical_universal),
            quantified_inference: self.quantified_inference.clone(),
            quantified_depth: self.quantified_depth,
            active_domains: vec![],
            callable_environments: self.callable_environments.clone(),
        }
    }

    /// Install one lexical equality environment and discard answers from the
    /// previous environment. These are caller obligations, never global rules.
    pub(crate) fn set_associated_bindings(
        &mut self,
        types: Vec<crate::ElaboratedAssociatedTypeBinding>,
        effects: Vec<crate::ElaboratedAssociatedEffectBinding>,
    ) {
        self.tables.clear();
        self.assumed_type_bindings = Arc::new(types);
        self.assumed_effect_bindings = Arc::new(effects);
    }

    pub(crate) fn set_lexical_assumptions(&mut self, assumptions: Vec<TraitGoal>) {
        self.reset_query();
        self.lexical_assumptions = Arc::new(assumptions);
    }

    pub fn set_outlives_assumptions(&mut self, assumptions: Vec<crate::OutlivesPredicate>) {
        self.reset_query();
        self.lexical_outlives = Arc::new(assumptions);
    }

    pub(crate) fn set_universal_assumptions(&mut self, assumptions: Vec<crate::QuantifiedWhereBound>) {
        self.reset_query();
        self.lexical_universal = Arc::new(assumptions);
    }

    /// Introduce fresh rigid regions in an isolated solver. Neither tabled
    /// answers nor impl substitutions escape this proof. Nested quantified
    /// obligations inherit the live universe supply and a bounded depth.
    pub(crate) fn proves_universal(&mut self, bound: &crate::QuantifiedWhereBound) -> bool {
        if self.quantified_depth >= self.limits.max_depth || self.steps >= self.limits.max_steps {
            return false;
        }
        let mut scoped = self.fresh_query();
        scoped.quantified_depth += 1;
        scoped.steps = self.steps + 1;
        let proven = (|| {
            let Ok(scope) = scoped.quantified_inference.begin_universal_scope(bound.lifetime_binders) else {
                return false;
            };
            let Some(opened) = bound.open(&scope) else { return false; };
            let goal = TraitGoal { subject: opened.subject, relation: opened.relation };
            if !matches!(scoped.solve_scoped_hrtb(goal.clone()), TraitAnswer::Proven { .. }) {
                return false;
            }
            let lexical = scoped.lexical_universal.iter()
                .filter_map(|bound| bound.for_goal(&goal)).collect::<Vec<_>>();
            for binding in opened.type_bindings {
                if lexical.iter().any(|bound| bound.type_bindings.iter().any(|actual| actual == &binding)) {
                    continue;
                }
                if !matches!(scoped.select_associated_type_application(goal.clone(), &binding.name, &binding.item_arguments, true),
                    TraitProjectionAnswer::Normalized { ty, .. } if ty == binding.value) {
                    return false;
                }
            }
            for binding in opened.effect_bindings {
                if lexical.iter().any(|bound| bound.effect_bindings.iter().any(|actual| actual == &binding)) {
                    continue;
                }
                if !matches!(scoped.select_associated_effect_row_application(goal.clone(), &binding.name, &binding.item_arguments, true),
                    TraitEffectRowProjectionAnswer::Normalized { row, .. } if row == binding.value) {
                    return false;
                }
            }
            scoped.quantified_inference.finish_universal_scope(scope).is_ok()
        })();
        self.steps = scoped.steps;
        proven
    }

    pub(crate) fn assume_callable_contract(&mut self, signature: &CallableSignature) {
        self.set_universal_assumptions(self.lexical_universal.iter().cloned().chain(signature.universal_bounds.clone()).collect());
        self.set_outlives_assumptions(self.lexical_outlives.iter().cloned().chain(signature.outlives_environment())
            .chain(self.implied_outlives(signature.parameters.clone())).collect());
        self.set_lexical_assumptions(self.lexical_assumptions.iter().cloned().chain(signature.where_bounds.iter().map(|(subject, relation)|
            TraitGoal { subject: subject.clone(), relation: relation.clone() })).collect());
    }

    fn solve_projection_implementation(&mut self, goal: TraitGoal, scoped_hrtb: bool) -> TraitAnswer {
        if !scoped_hrtb && trait_goal_contains_escaping_hrtb(&goal) {
            return TraitAnswer::NoSolution;
        }
        let assumptions = Arc::clone(&self.lexical_assumptions);
        // An abstract `T: Trait` fact proves membership, but is not an impl
        // identity from which an associated definition can be read.
        self.solve_at_with_assumptions(goal, 0, false, &assumptions, false).into()
    }

    fn same_associated_owner(&self, left: &TraitGoal, right: &TraitGoal, name: &str, kind: AssociatedItemKind) -> bool {
        matches!((
            self.find_associated_item_goal(left, name, kind, &mut vec![]),
            self.find_associated_item_goal(right, name, kind, &mut vec![]),
        ), (SupertraitLookup::Found(left), SupertraitLookup::Found(right)) if left == right)
    }

    fn assumed_type_value(&self, projection: &Type) -> Result<Option<Type>, TraitProjectionAnswer> {
        if has_free_hrtb_placeholder(projection, 0) { return Ok(None); }
        let Type::Projection { subject, trait_definition, trait_arguments, name, item_generic_kinds, item_arguments } = projection else {
            return Ok(None);
        };
        let goal = TraitGoal { subject: (**subject).clone(), relation: ElaboratedTraitReference {
            definition: *trait_definition, arguments: trait_arguments.clone(),
        } };
        let mut selected = None;
        let universal = self.lexical_universal.iter().filter_map(|bound| bound.for_goal(&goal))
            .flat_map(|bound| bound.type_bindings).collect::<Vec<_>>();
        for binding in self.assumed_type_bindings.iter().chain(&universal) {
            if binding.name != *name || binding.item_generic_kinds != *item_generic_kinds
                || binding.item_arguments != *item_arguments { continue; }
            let bound = TraitGoal { subject: binding.subject.clone(), relation: binding.relation.clone() };
            if !self.same_associated_owner(&goal, &bound, name, AssociatedItemKind::Type) { continue; }
            if selected.as_ref().is_some_and(|value| *value != binding.value) {
                return Err(TraitProjectionAnswer::Ambiguous);
            }
            selected = Some(binding.value.clone());
        }
        Ok(selected)
    }

    fn assumed_effect_value(&self, projection: &crate::EffectRowProjection) -> Result<Option<EffectRow>, TraitEffectRowProjectionAnswer> {
        let row = EffectRow { effects: Default::default(), tails: Default::default(), projections: vec![projection.clone()] };
        if effect_row_contains_free_hrtb_placeholder(&row, 0) { return Ok(None); }
        let goal = TraitGoal { subject: (*projection.subject).clone(), relation: ElaboratedTraitReference {
            definition: projection.trait_definition, arguments: projection.trait_arguments.clone(),
        } };
        let mut selected = None;
        let universal = self.lexical_universal.iter().filter_map(|bound| bound.for_goal(&goal))
            .flat_map(|bound| bound.effect_bindings).collect::<Vec<_>>();
        for binding in self.assumed_effect_bindings.iter().chain(&universal) {
            if binding.name != projection.name || binding.item_generic_kinds != projection.item_generic_kinds
                || binding.item_arguments != projection.item_arguments { continue; }
            let bound = TraitGoal { subject: binding.subject.clone(), relation: binding.relation.clone() };
            if !self.same_associated_owner(&goal, &bound, &projection.name, AssociatedItemKind::EffectRow) { continue; }
            if selected.as_ref().is_some_and(|value| *value != binding.value) {
                return Err(TraitEffectRowProjectionAnswer::Ambiguous);
            }
            selected = Some(binding.value.clone());
        }
        Ok(selected)
    }

    pub(crate) fn has_manual_use_for(&self, definition: DefKey) -> bool {
        self.manual_use_nominals.contains(&definition)
    }

    pub fn solve(&mut self, goal: TraitGoal) -> TraitAnswer {
        // A solver goal has no ambient callable binder.  A raw `Bound`
        // lifetime can only be admitted when it is closed by a nested HRTB
        // in the type tree itself; otherwise tabled evidence would preserve
        // a region that escapes its source binder.
        if trait_goal_contains_escaping_hrtb(&goal) {
            return TraitAnswer::NoSolution;
        }
        self.solve_at(goal, 0, false).into()
    }

    /// Solve a trait goal embedded in a syntactically owned higher-ranked
    /// callable binder.  Unlike [`Self::solve`], bound lifetimes in this goal
    /// are not escaped: the caller has already established that their De
    /// Bruijn scope is part of the containing signature.  The solver table
    /// remains local to this query, so the scoped evidence cannot become a
    /// general source-level proof for the same spelling outside that binder.
    pub fn solve_scoped_hrtb(&mut self, goal: TraitGoal) -> TraitAnswer {
        self.solve_at(goal, 0, false).into()
    }

    /// Begin an independent solver query over the same frozen interface.
    /// Table entries and resource steps are per-query facts: retaining either
    /// would let one body expression consume another expression's limit or
    /// inherit its active-cycle state. The immutable rule/interface snapshot
    /// is reference counted, so creating a fresh query avoids recloning the
    /// full semantic world.
    pub fn reset_query(&mut self) {
        self.tables.clear();
        self.principal_active.clear();
        self.active_domains.clear();
        self.callable_environments.clear();
        self.steps = 0;
    }

    /// The one ownership interval, with implementation binders instantiated
    /// and conditional bounds checked in the same query as ordinary traits.
    pub fn principal_use_with_assumptions(
        &self,
        ty: &Type,
        assumptions: &[TraitGoal],
    ) -> Option<crate::Quantity> {
        self.fresh_query().principal_use_at(ty, 0, assumptions, UseEvidence::Declared)
    }

    pub(crate) fn resident_use(&self, ty: &Type) -> Option<crate::Quantity> {
        self.fresh_query().principal_use_at(ty, 0, &[], UseEvidence::Resident)
    }

    fn principal_use_at(
        &mut self,
        ty: &Type,
        depth: u32,
        assumptions: &[TraitGoal],
        evidence: UseEvidence,
    ) -> Option<crate::Quantity> {
        if depth >= self.limits.max_depth || self.steps >= self.limits.max_steps
            || self.principal_active.contains(ty)
        {
            return None;
        }
        self.steps += 1;
        self.principal_active.push(ty.clone());
        let result = self.principal_use_inner(ty, depth, assumptions, evidence);
        self.principal_active.pop();
        result
    }

    fn principal_use_inner(
        &mut self,
        ty: &Type,
        depth: u32,
        assumptions: &[TraitGoal],
        evidence: UseEvidence,
    ) -> Option<crate::Quantity> {
        use crate::Quantity;
        if crate::types::label::payload(ty).is_some() { return Some(Quantity::UNRESTRICTED); }
        let relation = |quantity| ElaboratedTraitReference {
            definition: crate::resolution::language_use_trait_definition(),
            arguments: vec![GenericArgument::ConstQuantity(quantity)],
        };
        // Assumptions are guaranteed capabilities, not an assertion that the
        // caller's principal interval is exactly the written bound.
        for quantity in [Quantity::UNRESTRICTED, Quantity::AFFINE, Quantity::ONCE] {
            let goal = TraitGoal {
                subject: ty.clone(), relation: relation(quantity),
            };
            if self.assumption_proves(&goal, assumptions) || self.associated_result_proves(&goal, assumptions, depth + 1) {
                return Some(quantity);
            }
        }
        let rules = Arc::clone(&self.rules);
        let mut declared = None;
        let mut unresolved = false;
        for rule in rules.iter().filter(|rule| rule.implementation.relation.definition
            == crate::resolution::language_use_trait_definition())
        {
            let implementation = &rule.implementation;
            let mut head = ImplementationSubstitution::default();
            if match_type(&implementation.self_ty, ty, &mut head).is_none()
                || solve_pending_effect_rows(&mut head).is_none() {
                continue;
            }
            if implementation.negative { return None; }
            let mut selected = None;
            let mut rule_unresolved = false;
            // A forwarded quantity is determined by the widest capability
            // its bounds prove. Fixed intervals still select only themselves.
            for quantity in [Quantity::UNRESTRICTED, Quantity::AFFINE, Quantity::ONCE] {
                let Some(substitution) = self.match_rule_with_callable_bindings(implementation, &TraitGoal {
                    subject: ty.clone(), relation: relation(quantity),
                }) else { continue; };
                let mut viable = true;
                for (subject, bound) in &implementation.where_bounds {
                    let obligation = TraitGoal {
                        subject: substitute_type(subject, &substitution),
                        relation: substitute_relation(bound, &substitution),
                    };
                    match self.solve_at_with_assumptions(
                        obligation.clone(), depth + 1, false, assumptions, true,
                    ) {
                        TraitAnswerIndex::Proven(_) => {},
                        TraitAnswerIndex::Ambiguous | TraitAnswerIndex::Overflow => {
                            rule_unresolved = true;
                            viable = false;
                        },
                        _ => {
                            rule_unresolved |= principal_goal_is_open(&obligation);
                            viable = false;
                        },
                    }
                    if !viable { break; }
                }
                if viable && let Err(answer) = self.check_implementation_bindings(implementation, &substitution) {
                    rule_unresolved |= matches!(answer, TraitAnswerIndex::Ambiguous | TraitAnswerIndex::Overflow);
                    viable = false;
                }
                if viable { selected = Some(quantity); break; }
            }
            if let Some(quantity) = selected {
                if declared.is_some_and(|previous| previous != quantity) {
                    return None;
                }
                declared = Some(quantity);
            } else {
                unresolved |= rule_unresolved;
            }
        }
        if unresolved { return None; }
        let structural = self.structural_principal_use_at(ty, depth + 1, assumptions, evidence);
        match (declared, structural) {
            (Some(manual), Some(structural)) => structural.contains(manual).then_some(manual),
            // Header validation checks generic restrictions against the
            // implementation's own assumptions. Concrete queries recheck the
            // actual field contract above whenever it is known.
            (Some(manual), None) => Some(manual),
            (None, structural) => structural,
        }
    }

    pub(crate) fn structural_principal_use_with_assumptions(
        &self, ty: &Type, assumptions: &[TraitGoal],
    ) -> Option<crate::Quantity> {
        self.fresh_query().structural_principal_use_at(ty, 0, assumptions, UseEvidence::Declared)
    }

    pub(crate) fn principal_use_rule_contracts(
        &self, implementation: &ElaboratedImplementation,
    ) -> Option<Vec<(crate::Quantity, Option<crate::Quantity>)>> {
        use crate::Quantity;
        let candidates = match implementation.relation.arguments.as_slice() {
            [GenericArgument::ConstQuantity(quantity)] => vec![(*quantity, None)],
            [GenericArgument::ConstGeneric { index, kind: crate::ConstKind::Quantity }]
                if implementation.generic_kinds.get(*index as usize)
                    == Some(&crate::GenericKind::Const(crate::ConstKind::Quantity))
                    && implementation.where_bounds.iter().any(|(_, relation)| {
                        relation.definition == crate::resolution::language_use_trait_definition()
                            && relation.arguments == implementation.relation.arguments
                    }) => [Quantity::UNRESTRICTED, Quantity::AFFINE, Quantity::ONCE]
                        .into_iter().map(|quantity| (quantity, Some(*index))).collect(),
            _ => return None,
        };
        Some(candidates.into_iter().map(|(quantity, index)| {
            let mut substitution = ImplementationSubstitution::default();
            if let Some(index) = index {
                substitution.generic_arguments.insert(index, GenericArgument::ConstQuantity(quantity));
            }
            let subject = substitute_type(&implementation.self_ty, &substitution);
            let assumptions = implementation.where_bounds.iter().map(|(subject, relation)| TraitGoal {
                subject: substitute_type(subject, &substitution),
                relation: substitute_relation(relation, &substitution),
            }).collect::<Vec<_>>();
            let mut scoped = self.fresh_query();
            let shifted = substitution_under_region_binder(&substitution).expect("concrete quantity substitution cannot escape a region binder");
            scoped.set_universal_assumptions(implementation.universal_bounds.iter().map(|bound|
                bound.map_terms(|argument| substitute_generic_argument(&argument, &shifted))).collect());
            scoped.set_lexical_assumptions(assumptions.clone());
            scoped.set_outlives_assumptions(implementation.where_outlives.iter().map(|bound|
                bound.map_terms(|argument| substitute_generic_argument(&argument, &substitution)))
                .chain(self.implied_outlives(std::iter::once(subject.clone()))).collect());
            let bindings = crate::AssociatedItemContract { where_bounds: vec![], where_outlives: vec![],
                type_bindings: implementation.where_associated_type_bindings.clone(),
                effect_bindings: implementation.where_associated_effect_bindings.clone(),
            }.map_terms(|argument| substitute_generic_argument(&argument, &substitution));
            scoped.set_associated_bindings(bindings.type_bindings, bindings.effect_bindings);
            (quantity, scoped.structural_principal_use_with_assumptions(&subject, &assumptions))
        }).collect())
    }

    fn structural_principal_use_at(
        &mut self, ty: &Type, depth: u32, assumptions: &[TraitGoal], evidence: UseEvidence,
    ) -> Option<crate::Quantity> {
        use crate::Quantity;
        let fields = match ty {
            Type::Unit | Type::Never | Type::Scalar(_) | Type::StaticData { .. }
            | Type::RawPointer { .. } => return Some(Quantity::UNRESTRICTED),
            Type::Reference { mutability, .. } => return Some(match mutability {
                crate::Mutability::Shared => Quantity::UNRESTRICTED,
                crate::Mutability::Unique => Quantity::AFFINE,
            }),
            Type::Callable { contract, invocation, .. } => return match evidence {
                UseEvidence::Declared => Some(*invocation),
                UseEvidence::Resident => contract.resident_quantity(*invocation,
                    |capture| self.principal_use_at(capture, depth + 1, assumptions, evidence)),
            },
            Type::Tuple(fields) => fields.clone(),
            Type::Array(element) => vec![(**element).clone()],
            Type::FixedArray { element, .. } => if ty.fixed_array_length() == Some(0) {
                vec![]
            } else { vec![(**element).clone()] },
            Type::Nominal { definition, arguments } =>
                self.nominal_structural_fields(*definition, arguments)?,
            _ => return None,
        };
        fields.iter().try_fold(Quantity::UNRESTRICTED, |quantity, field| {
            quantity.intersection(self.principal_use_at(field, depth + 1, assumptions, evidence)?).ok()
        })
    }

    /// Solve a trait goal under declaration-owned assumptions.
    ///
    /// This is deliberately separate from [`Self::solve`]: a callable or
    /// implementation `where` clause is lexical evidence, not a new global
    /// implementation rule.  In particular, caching an answer obtained from
    /// `T: Parent` as an ordinary answer for `T: Parent` would let one
    /// declaration's generic contract leak into an unrelated body.  The
    /// scoped probe owns a fresh table while still using the same frozen
    /// implementation and supertrait rules as ordinary selection.
    ///
    /// An assumption also entails the transitive supertraits declared by its
    /// relation.  This is necessary for the ordinary implementation rule
    /// `impl<T> Child for Box<T> where Box<T>: Parent` to establish
    /// `Child: Parent`, including when the selected parent implementation has
    /// further where-obligations that must be discharged by the same clause.
    pub fn solve_with_assumptions(
        &self,
        goal: TraitGoal,
        assumptions: &[TraitGoal],
    ) -> TraitAnswer {
        if trait_goal_contains_escaping_hrtb(&goal) {
            return TraitAnswer::NoSolution;
        }
        let mut solver = self.clone();
        // A `TraitSolver` cache is intentionally local to one lexical
        // environment. Cloning also resets neither the cache nor the budget,
        // so do both explicitly before entering the scoped fixed point.
        solver.tables.clear();
        solver.steps = 0;
        let assumptions = assumptions
            .iter()
            .cloned()
            .filter_map(|assumption| solver.normalize_goal(assumption).ok())
            .filter(|assumption| !trait_goal_contains_escaping_hrtb(assumption))
            .collect::<Vec<_>>();
        // Normalizing a concrete projection can consult ordinary rules. Those
        // intermediate answers are valid for normalization, but are not
        // entries in this lexical proof environment.
        solver.tables.clear();
        solver.steps = 0;
        solver
            .solve_at_with_assumptions(goal, 0, false, &assumptions, true)
            .into()
    }

    /// Select a rule-backed implementation under lexical assumptions.  Method
    /// bodies need an implementation identity, so an assumption that merely
    /// entails the goal cannot be returned as the final evidence.  The same
    /// assumptions remain available to discharge the selected rule's where
    /// obligations.
    fn solve_implementation_with_assumptions(
        &self,
        goal: TraitGoal,
        assumptions: &[TraitGoal],
    ) -> TraitAnswer {
        if trait_goal_contains_escaping_hrtb(&goal) {
            return TraitAnswer::NoSolution;
        }
        let mut solver = self.clone();
        solver.tables.clear();
        solver.steps = 0;
        let assumptions = assumptions
            .iter()
            .cloned()
            .filter_map(|assumption| solver.normalize_goal(assumption).ok())
            .filter(|assumption| !trait_goal_contains_escaping_hrtb(assumption))
            .collect::<Vec<_>>();
        solver.tables.clear();
        solver.steps = 0;
        solver
            .solve_at_with_assumptions(goal, 0, false, &assumptions, false)
            .into()
    }

    pub fn query(&self, goal: &TraitGoal) -> TraitGoalQuery {
        TraitGoalQuery {
            fingerprint: goal_key(goal),
            trait_definition: goal.relation.definition,
            candidate_implementations: self
                .rules
                .iter()
                .filter(|rule| rule.implementation.relation.definition == goal.relation.definition)
                .map(|rule| rule.definition)
                .collect(),
        }
    }

    /// Method binders are declaration facts.  Looking them up through the
    /// supertrait closure lets Core create operation inference variables
    /// before it has selected the concrete parent implementation.
    pub fn method_generic_kinds(
        &self,
        relation: &ElaboratedTraitReference,
        name: &str,
    ) -> Option<Vec<crate::GenericKind>> {
        let goal = TraitGoal {
            relation: relation.clone(),
            subject: Type::Generic(TRAIT_SELF_GENERIC),
        };
        match self.find_method_goal(&goal, name, &mut Vec::new()) {
            SupertraitLookup::Found(goal) => self
                .traits
                .get(&goal.relation.definition)
                .and_then(|trait_header| trait_header.methods.get(name))
                .map(|method| method.generic_kinds.clone()),
            SupertraitLookup::Missing | SupertraitLookup::Ambiguous => None,
        }
    }

    /// Instantiate the declaration-owned method contract for a trait goal
    /// without selecting an implementation.  Generic bodies may rely on a
    /// lexical `T: Trait` proof before `T` is concrete; their call sites need
    /// this interface contract now and defer implementation selection until
    /// instance materialization closes the binders.
    pub fn declared_method_signature(
        &self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> Option<CallableSignature> {
        let goal = match self.method_goal(goal, name) {
            Ok(goal) => goal,
            Err(_) => return None,
        };
        let trait_header = self.traits.get(&goal.relation.definition)?;
        let method = trait_header.methods.get(name)?;
        if !generic_arguments_match_kinds(arguments, &method.generic_kinds) {
            return None;
        }
        let mut substitution = ImplementationSubstitution::default();
        substitution
            .types
            .insert(TRAIT_SELF_GENERIC, goal.subject.clone());
        for (index, argument) in goal.relation.arguments.into_iter().enumerate() {
            install_item_argument(&mut substitution, index as u32, argument);
        }
        for (offset, argument) in arguments.iter().cloned().enumerate() {
            install_item_argument(
                &mut substitution,
                trait_header.generics + offset as u32,
                argument,
            );
        }
        Some(substitute_callable_signature(method, &substitution))
    }

    fn supertrait_goals(&self, goal: &TraitGoal) -> Vec<TraitGoal> {
        if is_intrinsic_label_trait(&goal.relation)
            && matches!(goal.relation.arguments.as_slice(), [GenericArgument::Type(_)]) {
            return vec![TraitGoal { subject: goal.subject.clone(), relation: ElaboratedTraitReference {
                definition: crate::resolution::language_use_trait_definition(),
                arguments: vec![GenericArgument::ConstQuantity(crate::Quantity::UNRESTRICTED)],
            } }];
        }
        let Some(trait_header) = self.traits.get(&goal.relation.definition) else {
            return vec![];
        };
        let mut substitution = ImplementationSubstitution::default();
        substitution
            .types
            .insert(TRAIT_SELF_GENERIC, goal.subject.clone());
        for (index, argument) in goal.relation.arguments.iter().cloned().enumerate() {
            install_item_argument(&mut substitution, index as u32, argument);
        }
        trait_header
            .supertraits
            .iter()
            .map(|relation| TraitGoal {
                relation: substitute_relation(relation, &substitution),
                subject: goal.subject.clone(),
            })
            .collect()
    }

    fn find_method_goal(
        &self,
        goal: &TraitGoal,
        name: &str,
        active: &mut Vec<Digest>,
    ) -> SupertraitLookup<TraitGoal> {
        let key = goal_key(goal);
        if active.contains(&key) {
            return SupertraitLookup::Ambiguous;
        }
        let Some(trait_header) = self.traits.get(&goal.relation.definition) else {
            return SupertraitLookup::Missing;
        };
        if trait_header.methods.contains_key(name) {
            return SupertraitLookup::Found(goal.clone());
        }
        active.push(key);
        let result = merge_supertrait_lookups(
            self.supertrait_goals(goal)
                .into_iter()
                .map(|parent| self.find_method_goal(&parent, name, active)),
        );
        active.pop();
        result
    }

    pub(crate) fn associated_item_owner_is_ambiguous(
        &self,
        goal: &TraitGoal,
        name: &str,
        kind: AssociatedItemKind,
    ) -> bool {
        matches!(
            self.find_associated_item_goal(goal, name, kind, &mut vec![]),
            SupertraitLookup::Ambiguous
        )
    }

    fn find_associated_item_goal(
        &self,
        goal: &TraitGoal,
        name: &str,
        kind: AssociatedItemKind,
        active: &mut Vec<Digest>,
    ) -> SupertraitLookup<TraitGoal> {
        // Compiler-owned callable traits have no source trait header. Their
        // associated items still have an exact declaration owner, including
        // when the subject is a generic with lexical equality evidence.
        // Looking only in source headers made that evidence disappear at
        // ordinary projection normalization and frozen-contract validation.
        let callable = is_intrinsic_callable_trait(&goal.relation);
        let runs_in = is_intrinsic_runs_in_trait(&goal.relation);
        if callable || runs_in {
            return if matches!((kind, name), (AssociatedItemKind::Type, "Output")
                | (AssociatedItemKind::EffectRow, "Effects"))
                || (runs_in && matches!((kind, name), (AssociatedItemKind::Type, "After"))) {
                SupertraitLookup::Found(goal.clone())
            } else { SupertraitLookup::Missing };
        }
        let key = goal_key(goal);
        if active.contains(&key) {
            return SupertraitLookup::Ambiguous;
        }
        let Some(trait_header) = self.traits.get(&goal.relation.definition) else {
            return SupertraitLookup::Missing;
        };
        if trait_declares_associated_item(trait_header, name, kind) {
            return SupertraitLookup::Found(goal.clone());
        }
        active.push(key);
        let result = merge_supertrait_lookups(
            self.supertrait_goals(goal)
                .into_iter()
                .map(|parent| self.find_associated_item_goal(&parent, name, kind, active)),
        );
        active.pop();
        result
    }

    /// Inspect deterministic candidate shape alongside the ordinary tabled
    /// answer. This is diagnostic evidence only and never influences tables.
    pub fn explain(&mut self, goal: TraitGoal) -> TraitSelectionExplanation {
        // Preserve the normal tabled selection exactly. A fresh structural
        // probe builds a finite obligation tree, so asking for an explanation
        // can neither pre-populate nor perturb this solver's cache or budget.
        let answer = self.solve(goal.clone());
        let mut probe = Self {
            callable_environments: self.callable_environments.clone(),
            rules: self.rules.clone(),
            manual_use_nominals: self.manual_use_nominals.clone(),
            traits: self.traits.clone(),
            definitions: self.definitions.clone(),
            nominal_variances: Arc::clone(&self.nominal_variances),
            tables: BTreeMap::new(),
            principal_active: vec![],
            limits: self.limits.clone(),
            steps: 0,
            assumed_type_bindings: Arc::clone(&self.assumed_type_bindings),
            assumed_effect_bindings: Arc::clone(&self.assumed_effect_bindings),
            lexical_assumptions: Arc::clone(&self.lexical_assumptions),
            lexical_outlives: Arc::clone(&self.lexical_outlives),
            lexical_universal: Arc::clone(&self.lexical_universal),
            quantified_inference: self.quantified_inference.clone(),
            quantified_depth: self.quantified_depth,
            active_domains: vec![],
        };
        let mut active = BTreeMap::new();
        let mut explanation = probe.explain_at(goal, 0, false, &mut active);
        // Table reuse can only make the ordinary solver more precise within a
        // fixed budget. Its answer remains authoritative for callers, while
        // the fresh probe supplies the deterministic causal tree.
        explanation.answer = answer;
        explanation
    }

    fn explain_at(
        &mut self,
        goal: TraitGoal,
        depth: u32,
        coinductive_edge: bool,
        active: &mut BTreeMap<Digest, TraitGoal>,
    ) -> TraitSelectionExplanation {
        if depth >= self.limits.max_depth {
            return TraitSelectionExplanation {
                goal,
                answer: TraitAnswer::Overflow,
                candidates: vec![],
                terminal: Some(TraitExplanationTerminal::DepthLimit {
                    limit: self.limits.max_depth,
                }),
            };
        }
        if self.steps >= self.limits.max_steps {
            return TraitSelectionExplanation {
                goal,
                answer: TraitAnswer::Overflow,
                candidates: vec![],
                terminal: Some(TraitExplanationTerminal::StepLimit {
                    limit: self.limits.max_steps,
                }),
            };
        }
        let goal = match self.normalize_goal(goal.clone()) {
            Ok(goal) => goal,
            Err(answer) => {
                return TraitSelectionExplanation {
                    goal,
                    answer: answer.into(),
                    candidates: vec![],
                    terminal: None,
                };
            }
        };
        if trait_goal_contains_escaping_hrtb(&goal) {
            return TraitSelectionExplanation {
                goal,
                answer: TraitAnswer::NoSolution,
                candidates: vec![],
                terminal: None,
            };
        }
        let key = goal_key(&goal);
        if let Some(reentered) = active.get(&key) {
            let auto = coinductive_edge && self.is_auto_trait(&goal);
            return TraitSelectionExplanation {
                answer: if auto {
                    TraitAnswer::Proven {
                        evidence: self.structural_evidence(&goal),
                    }
                } else {
                    TraitAnswer::Ambiguous
                },
                goal,
                candidates: vec![],
                terminal: Some(TraitExplanationTerminal::OrdinaryCycle {
                    reentered: reentered.clone(),
                    policy: if auto {
                        TraitCyclePolicy::CoinductiveAuto
                    } else {
                        TraitCyclePolicy::Inductive
                    },
                }),
            };
        }
        self.steps += 1;
        active.insert(key, goal.clone());

        let mut positives = vec![];
        let mut negatives = vec![];
        let mut saw_cycle = false;
        let mut saw_overflow = false;
        let rules = self
            .rules
            .iter()
            .filter(|rule| rule.implementation.relation.definition == goal.relation.definition)
            .cloned()
            .collect::<Vec<_>>();
        let mut candidates: Vec<TraitCandidateExplanation> = rules
            .into_iter()
            .map(|rule| {
                let Some(substitution) = self.match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                    return TraitCandidateExplanation::Rejected {
                        implementation: rule.definition,
                        reason: TraitCandidateRejection::HeadMismatch,
                    };
                };
                let mut outcomes = Vec::new();
                for (subject, relation) in &rule.implementation.where_bounds {
                    let obligation = TraitGoal {
                        relation: substitute_relation(relation, &substitution),
                        subject: substitute_type(subject, &substitution),
                    };
                    let explanation = self.explain_at(obligation.clone(), depth + 1, false, active);
                    let outcome = explanation.answer.clone();
                    match outcome {
                        TraitAnswer::Ambiguous => saw_cycle = true,
                        TraitAnswer::Overflow => saw_overflow = true,
                        TraitAnswer::Proven { .. }
                        | TraitAnswer::Refuted { .. }
                        | TraitAnswer::NoSolution => {}
                    }
                    let proven = matches!(outcome, TraitAnswer::Proven { .. });
                    outcomes.push(TraitWhereBoundExplanation {
                        goal: obligation,
                        outcome,
                        explanation: Box::new(explanation),
                    });
                    if !proven {
                        return TraitCandidateExplanation::Rejected {
                            implementation: rule.definition,
                            reason: TraitCandidateRejection::WhereBound { outcomes },
                        };
                    }
                }
                if let Err(answer) = self.check_implementation_bindings(&rule.implementation, &substitution) {
                    saw_cycle |= matches!(answer, TraitAnswerIndex::Ambiguous);
                    saw_overflow |= matches!(answer, TraitAnswerIndex::Overflow);
                    return TraitCandidateExplanation::Rejected {
                        implementation: rule.definition,
                        reason: TraitCandidateRejection::AssociatedBinding { outcome: answer.into() },
                    };
                }
                if rule.implementation.negative {
                    negatives.push(rule.definition);
                } else {
                    positives.push(rule.definition);
                }
                TraitCandidateExplanation::Applicable {
                    implementation: rule.definition,
                    negative: rule.implementation.negative,
                    where_bounds: outcomes,
                }
            })
            .collect();
        let mut answer = select_answer(&positives, &negatives, saw_cycle, saw_overflow).into();
        if matches!(answer, TraitAnswer::NoSolution)
            && self.is_auto_trait(&goal)
            && let Some(obligations) = self.structural_obligations(&goal)
        {
            let mut outcomes = Vec::new();
            let mut structural_answer = TraitAnswer::Proven {
                evidence: self.structural_evidence(&goal),
            };
            for obligation in obligations {
                let explanation = self.explain_at(obligation.clone(), depth + 1, true, active);
                let outcome = explanation.answer.clone();
                if !matches!(outcome, TraitAnswer::Proven { .. }) {
                    structural_answer = outcome.clone();
                }
                outcomes.push(TraitWhereBoundExplanation {
                    goal: obligation,
                    outcome,
                    explanation: Box::new(explanation),
                });
            }
            let evidence = self.structural_evidence(&goal);
            candidates.push(TraitCandidateExplanation::Structural {
                evidence,
                obligations: outcomes,
            });
            answer = structural_answer;
        }
        active.remove(&key);
        TraitSelectionExplanation {
            goal,
            answer,
            candidates,
            terminal: None,
        }
    }

    /// Select an implementation for `goal` and normalize one of its
    /// zero-arity associated types with the selected impl substitution.
    ///
    /// Source projection syntax and frozen interfaces share this solver
    /// boundary, so candidate selection, bounds checking, and canonical
    /// memoization never need a parallel impl lookup.
    pub fn normalize_associated_type(
        &mut self,
        goal: TraitGoal,
        name: &str,
    ) -> TraitProjectionAnswer {
        self.normalize_associated_type_application(goal, name, &[])
    }

    /// Normalize projections throughout a kinded type under this query's
    /// lexical evidence. Structural heads can select generic implementations
    /// with rigid arguments only when every prerequisite is proved. Abstract
    /// subjects and missing generic evidence remain symbolic obligations.
    pub fn normalize_type(&mut self, value: Type) -> Result<Type, Box<TraitProjectionAnswer>> {
        self.normalize_type_projections(value, &mut vec![])
    }

    /// Normalize a term owned by one explicit surrounding region binder.
    /// The caller retains that binder while consuming the result. Ordinary
    /// unscoped entry points continue to reject escaped bound regions.
    pub(crate) fn normalize_type_in_region_binder(&mut self, value: Type, lifetime_binders: u32)
        -> Result<Type, Box<TraitProjectionAnswer>> {
        self.normalize_type_projections_in_hrtb(value, &mut vec![], &[lifetime_binders])
    }

    /// Normalize a kinded argument through the same traversal and resource
    /// budget, including rows nested inside types and types nested in rows.
    pub fn normalize_generic_argument(
        &mut self,
        argument: GenericArgument,
    ) -> Result<GenericArgument, Box<TraitProjectionAnswer>> {
        self.normalize_trait_argument(argument, &mut vec![])
    }

    /// Normalize associated rows using exactly the same lexical selection
    /// rule and kinded traversal as types. Missing generic evidence remains
    /// an obligation, not an empty row or an invented implementation.
    pub fn normalize_effect_row(
        &mut self,
        value: EffectRow,
    ) -> Result<EffectRow, Box<TraitEffectRowProjectionAnswer>> {
        self.normalize_effect_row_projections(value, &mut vec![])
    }

    /// Normalize selected associated effect rows nested directly beneath an
    /// HRTB callable. Bound lifetime item arguments are rigid evidence only
    /// while this caller-owned binder is live; the public unscoped entry point
    /// above continues to reject them as escaping placeholders.
    pub fn normalize_effect_row_in_hrtb(
        &mut self,
        value: EffectRow,
        lifetime_binders: u32,
    ) -> Result<EffectRow, Box<TraitEffectRowProjectionAnswer>> {
        self.normalize_effect_row_projections_in_hrtb(value, &mut vec![], &[lifetime_binders])
    }

    /// Normalize an associated type application through selected trait
    /// evidence. Item arguments occupy generic slots after the implementation
    /// binders, preserving a stable substitution layout for GAT-like items.
    pub fn normalize_associated_type_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> TraitProjectionAnswer {
        let mut active = vec![];
        let subject = match self.normalize_type_projections(goal.subject, &mut active) {
            Ok(subject) => subject,
            Err(answer) => return *answer,
        };
        let trait_arguments = match goal
            .relation
            .arguments
            .into_iter()
            .map(|argument| self.normalize_trait_argument(argument, &mut active))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(answer) => return *answer,
        };
        let arguments = match arguments
            .iter()
            .cloned()
            .map(|argument| self.normalize_trait_argument(argument, &mut active))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(answer) => return *answer,
        };
        let goal = TraitGoal {
            relation: ElaboratedTraitReference {
                definition: goal.relation.definition,
                arguments: trait_arguments,
            },
            subject,
        };
        let root_key = associated_projection_key(&goal, name, &arguments);
        let answer = self.select_associated_type_application(goal, name, &arguments, false);
        let TraitProjectionAnswer::Normalized { evidence, ty } = answer else {
            return answer;
        };
        let mut active = vec![root_key];
        match self.normalize_type_projections(ty, &mut active) {
            Ok(ty) => TraitProjectionAnswer::Normalized { evidence, ty },
            Err(answer) => *answer,
        }
    }

    /// Select an associated type while a callable-owned HRTB binder is live.
    /// Bound lifetimes are rigid evidence in that scope, but remain rejected
    /// by the ordinary public projection entry point.
    pub fn normalize_associated_type_application_in_hrtb(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
        lifetime_binders: &[u32],
    ) -> TraitProjectionAnswer {
        let mut active = vec![];
        let subject = match self.normalize_type_projections_in_hrtb(
            goal.subject,
            &mut active,
            lifetime_binders,
        ) {
            Ok(subject) => subject,
            Err(answer) => return *answer,
        };
        let trait_arguments = match goal.relation.arguments.into_iter().map(|argument| {
            self.normalize_trait_argument_in_hrtb(argument, &mut active, lifetime_binders)
        }).collect::<Result<Vec<_>, _>>() {
            Ok(arguments) => arguments,
            Err(answer) => return *answer,
        };
        let arguments = match arguments.iter().cloned().map(|argument| {
            self.normalize_trait_argument_in_hrtb(argument, &mut active, lifetime_binders)
        }).collect::<Result<Vec<_>, _>>() {
            Ok(arguments) => arguments,
            Err(answer) => return *answer,
        };
        let goal = TraitGoal {
            relation: ElaboratedTraitReference { definition: goal.relation.definition, arguments: trait_arguments },
            subject,
        };
        if !projection_type_is_known(&goal.subject, lifetime_binders, ProjectionPosition::Head)
            || !goal.relation.arguments.iter().all(|argument| projection_argument_is_known(argument, lifetime_binders, ProjectionPosition::Head))
            || !arguments.iter().all(|argument| projection_argument_is_known(argument, lifetime_binders, ProjectionPosition::Item)) {
            return TraitProjectionAnswer::NoSolution;
        }
        let root_key = associated_projection_key(&goal, name, &arguments);
        let answer = self.select_associated_type_application(goal, name, &arguments, true);
        let TraitProjectionAnswer::Normalized { evidence, ty } = answer else { return answer; };
        let mut active = vec![root_key];
        match self.normalize_type_projections_in_hrtb(ty, &mut active, lifetime_binders) {
            Ok(ty) => TraitProjectionAnswer::Normalized { evidence, ty },
            Err(answer) => *answer,
        }
    }

    /// Perform the one-step selection and substitution for an associated type.
    /// Recursive normalization is intentionally kept above this boundary so
    /// every nested projection uses the same candidate selection machinery.
    fn select_associated_type_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
        scoped_hrtb_item_arguments: bool,
    ) -> TraitProjectionAnswer {
        // A public projection request has no enclosing binder, so a bound
        // item argument is an escaped HRTB placeholder. The recursive type
        // normalizer may opt in only after it has verified that the argument
        // is owned by a surrounding callable binder.
        if !scoped_hrtb_item_arguments
            && (trait_goal_contains_escaping_hrtb(&goal)
                || arguments
                    .iter()
                    .any(generic_argument_contains_escaping_hrtb))
        {
            return TraitProjectionAnswer::NoSolution;
        }
        if arguments.is_empty() && (is_intrinsic_callable_trait(&goal.relation) || is_intrinsic_runs_in_trait(&goal.relation)) {
            let Some(value) = self.callable_evidence(&goal) else { return TraitProjectionAnswer::NoSolution; };
            let ty = match name {
                "Output" => value.output,
                "After" => match value.after { Some(after) => after, None => return TraitProjectionAnswer::NoSolution },
                _ => return TraitProjectionAnswer::NoSolution,
            };
            return TraitProjectionAnswer::Normalized { evidence: assumption_evidence(&goal), ty };
        }
        // An inherited item is still being requested through `goal`'s
        // trait.  Require that boundary before following a supertrait edge:
        // otherwise either `impl !Child for T`, or no Child evidence at all,
        // could be bypassed by an unrelated `impl Parent for T` that supplies
        // Child's inherited item.
        let requested = if scoped_hrtb_item_arguments {
            self.solve_scoped_hrtb(goal.clone())
        } else {
            self.solve(goal.clone())
        };
        match requested {
            TraitAnswer::Refuted { evidence } => {
                return TraitProjectionAnswer::Refuted { evidence };
            }
            TraitAnswer::Ambiguous => return TraitProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => return TraitProjectionAnswer::Overflow,
            TraitAnswer::Proven { .. } => {}
            TraitAnswer::NoSolution => return TraitProjectionAnswer::NoSolution,
        }
        if self.associated_contract(&goal, name, arguments).is_some()
            && !self.projection_domain_proven(&goal, name, arguments) { return TraitProjectionAnswer::NoSolution; }
        let goal = match self.find_associated_item_goal(
            &goal,
            name,
            AssociatedItemKind::Type,
            &mut Vec::new(),
        ) {
            SupertraitLookup::Found(goal) => goal,
            SupertraitLookup::Missing => goal,
            SupertraitLookup::Ambiguous => return TraitProjectionAnswer::Ambiguous,
        };
        // The surrounding normalizer has verified that the goal's rigid
        // regions are owned by its live callable binder. Re-entering the
        // public solver would reject that same evidence as escaped.
        let answer = self.solve_projection_implementation(goal.clone(), scoped_hrtb_item_arguments);
        match answer {
            TraitAnswer::Proven { evidence } => {
                let rules = Arc::clone(&self.rules);
                let Some(rule) = rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitProjectionAnswer::NoSolution;
                };
                let Some(substitution) = self.match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                    return TraitProjectionAnswer::NoSolution;
                };
                match rule.implementation.associated_types.get(name) {
                    Some(_)
                        if !associated_type_contract_matches(
                            self.traits.get(&goal.relation.definition),
                            name,
                            false,
                            rule.implementation.associated_types.get(name),
                        ) =>
                    {
                        TraitProjectionAnswer::NoSolution
                    }
                    Some(item) if item.generics != arguments.len() as u32 => {
                        TraitProjectionAnswer::AssociatedTypeArity {
                            evidence,
                            expected: item.generics,
                            found: arguments.len() as u32,
                        }
                    }
                    Some(item)
                        if !generic_arguments_match_kinds(arguments, &item.generic_kinds) =>
                    {
                        TraitProjectionAnswer::NoSolution
                    }
                    Some(item) => {
                        let base = rule.implementation.generics;
                        let mut substitution = substitution;
                        for (offset, argument) in arguments.iter().cloned().enumerate() {
                            install_item_argument(
                                &mut substitution,
                                base + offset as u32,
                                argument,
                            );
                        }
                        TraitProjectionAnswer::Normalized {
                            evidence,
                            ty: substitute_type(&item.value, &substitution),
                        }
                    }
                    None => {
                        let Some(trait_header) = self.traits.get(&goal.relation.definition) else {
                            return TraitProjectionAnswer::NoSolution;
                        };
                        let Some(declaration) = trait_header.associated_types.get(name) else {
                            return TraitProjectionAnswer::MissingAssociatedType { evidence };
                        };
                        if declaration.effect_row {
                            return TraitProjectionAnswer::NoSolution;
                        }
                        if declaration.generics != arguments.len() as u32 {
                            return TraitProjectionAnswer::AssociatedTypeArity {
                                evidence,
                                expected: declaration.generics,
                                found: arguments.len() as u32,
                            };
                        }
                        if !generic_arguments_match_kinds(arguments, &declaration.generic_kinds) {
                            return TraitProjectionAnswer::NoSolution;
                        }
                        let Some(default) = &declaration.default else {
                            return TraitProjectionAnswer::MissingAssociatedType { evidence };
                        };
                        let substitution = default_associated_item_substitution(
                            &goal,
                            trait_header.generics,
                            arguments,
                        );
                        TraitProjectionAnswer::Normalized {
                            evidence,
                            ty: substitute_type(default, &substitution),
                        }
                    }
                }
            }
            TraitAnswer::Refuted { evidence } => TraitProjectionAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => TraitProjectionAnswer::NoSolution,
            TraitAnswer::Ambiguous => TraitProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => TraitProjectionAnswer::Overflow,
        }
    }

    /// Selected definitions recurse through a single active stack across
    /// types, rows and constants. Known structural heads may use rigid lexical
    /// arguments; abstract subjects and unproved generic prerequisites remain
    /// symbolic until actual evidence is available.
    fn normalize_type_projections(
        &mut self,
        value: Type,
        active: &mut Vec<Digest>,
    ) -> Result<Type, Box<TraitProjectionAnswer>> {
        self.normalize_type_projections_in_hrtb(value, active, &[])
    }

    /// A lifetime-dependent head may have a result valid for every choice of
    /// its unresolved regions. Prove that under a fresh owned binder, retaining
    /// the exact lexical predicates, then restore the caller's original cells.
    /// Failure is not refutation of the eventual caller choice: a static-only
    /// implementation, for example, must stay deferred until inference decides.
    /// This never solves a caller type, lifetime, row or constant variable.
    fn normalize_parametric_regions(&mut self, value: GenericArgument, active: &mut Vec<Digest>,
        hrtb_binders: &[u32]) -> Option<GenericArgument> {
        if self.steps >= self.limits.max_steps || self.quantified_depth >= self.limits.max_depth {
            return None;
        }
        let mut regions = ParametricRegions::default();
        let abstracted = regions.abstract_argument(value.clone(), 0)?;
        if regions.inputs.is_empty() { return None; }
        let mut invalid = false;
        let contract = crate::signature::AssociatedItemContract {
            where_bounds: self.lexical_assumptions.iter().map(|goal|
                (goal.subject.clone(), goal.relation.clone())).collect(),
            where_outlives: self.lexical_outlives.as_ref().clone(),
            type_bindings: self.assumed_type_bindings.as_ref().clone(),
            effect_bindings: self.assumed_effect_bindings.as_ref().clone(),
        }.map_terms(|argument| regions.abstract_argument(argument.clone(), 0)
            .unwrap_or_else(|| { invalid = true; argument }));
        let universal = self.lexical_universal.iter().map(|bound| bound.map_terms(|argument|
            regions.abstract_argument(argument.clone(), 1).unwrap_or_else(|| { invalid = true; argument })))
            .collect::<Vec<_>>();
        let environments = self.callable_environments.iter().map(|environment|
            match regions.abstract_argument(GenericArgument::Type(environment.clone()), 0) {
                Some(GenericArgument::Type(value)) => value,
                _ => { invalid = true; environment.clone() },
            }).collect::<Vec<_>>();
        if invalid { return None; }
        let mut binders = vec![u32::try_from(regions.inputs.len()).ok()?];
        binders.extend_from_slice(hrtb_binders);
        let mut scoped = self.fresh_query();
        scoped.lexical_assumptions = Arc::new(contract.where_bounds.into_iter().map(|(subject, relation)|
            TraitGoal { subject, relation }).collect());
        scoped.lexical_outlives = Arc::new(contract.where_outlives);
        scoped.assumed_type_bindings = Arc::new(contract.type_bindings);
        scoped.assumed_effect_bindings = Arc::new(contract.effect_bindings);
        scoped.lexical_universal = Arc::new(universal);
        scoped.callable_environments = environments;
        scoped.quantified_depth += 1;
        scoped.steps = self.steps + 1;
        let normalized = scoped.normalize_trait_argument_in_hrtb(abstracted, active, &binders);
        self.steps = self.steps.max(scoped.steps);
        let result = regions.open(normalized.ok()?)?;
        (result != value).then_some(result)
    }

    /// HRTB-aware form of type projection normalization. `hrtb_binders` is
    /// ordered from the innermost callable outwards and is used solely to
    /// decide whether a bound item argument is rigidly scoped or escaped.
    fn normalize_type_projections_in_hrtb(
        &mut self,
        value: Type,
        active: &mut Vec<Digest>,
        hrtb_binders: &[u32],
    ) -> Result<Type, Box<TraitProjectionAnswer>> {
        if type_projection_normalization_is_identity(&value) { return Ok(value); }
        match value {
            Type::Nominal {
                definition,
                arguments,
            } => Ok(Type::Nominal {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|argument| {
                        self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                    })
                    .collect::<Result<_, _>>()?,
            }),
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_generic_kinds,
                item_arguments,
            } => {
                let subject =
                    self.normalize_type_projections_in_hrtb(*subject, active, hrtb_binders)?;
                let trait_arguments = trait_arguments
                    .into_iter()
                    .map(|argument| {
                        self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let item_arguments = item_arguments
                    .into_iter()
                    .map(|argument| {
                        self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let projection = Type::Projection {
                    subject: Box::new(subject),
                    trait_definition,
                    trait_arguments,
                    name,
                    item_generic_kinds,
                    item_arguments,
                };
                if let Some(value) = self.assumed_type_value(&projection).map_err(Box::new)? {
                    if !self.type_domains_proven(&projection) { return Err(Box::new(TraitProjectionAnswer::NoSolution)); }
                    let key = Digest::of_parts([b"assumed-type-projection".as_slice(), canonical_type_encoding(&projection).as_slice()]);
                    if active.contains(&key) { return Err(Box::new(TraitProjectionAnswer::RecursiveProjection)); }
                    if active.len() >= self.limits.max_depth as usize { return Err(Box::new(TraitProjectionAnswer::Overflow)); }
                    active.push(key);
                    let normalized = self.normalize_type_projections_in_hrtb(value, active, hrtb_binders);
                    active.pop();
                    return normalized;
                }
                let concrete = projection_is_concrete_in_hrtb_scope(&projection, hrtb_binders);
                let Type::Projection { subject, trait_definition, trait_arguments, item_arguments, .. } = &projection else { unreachable!() };
                if !concrete && !projection_application_is_selectable(subject, *trait_definition, trait_arguments, item_arguments, hrtb_binders) {
                    if let Some(GenericArgument::Type(normalized)) = self.normalize_parametric_regions(
                        GenericArgument::Type(projection.clone()), active, hrtb_binders) {
                        return Ok(normalized);
                    }
                    return Ok(projection);
                }
                let residual = projection.clone();
                let Type::Projection {
                    subject,
                    trait_definition,
                    trait_arguments,
                    name,
                    item_generic_kinds,
                    item_arguments,
                } = projection
                else {
                    unreachable!("projection was just constructed")
                };
                let goal = TraitGoal {
                    relation: ElaboratedTraitReference {
                        definition: trait_definition,
                        arguments: trait_arguments,
                    },
                    subject: *subject,
                };
                if !generic_arguments_match_kinds(&item_arguments, &item_generic_kinds) {
                    return Err(Box::new(TraitProjectionAnswer::NoSolution));
                }
                let key = associated_projection_key(&goal, &name, &item_arguments);
                if active.contains(&key) {
                    return Err(Box::new(TraitProjectionAnswer::RecursiveProjection));
                }
                if active.len() >= self.limits.max_depth as usize {
                    return Err(Box::new(TraitProjectionAnswer::Overflow));
                }
                active.push(key);
                let answer = self.select_associated_type_application(
                    goal,
                    &name,
                    &item_arguments,
                    !hrtb_binders.is_empty(),
                );
                let result = match answer {
                    TraitProjectionAnswer::Normalized { ty, .. } => {
                        self.normalize_type_projections_in_hrtb(ty, active, hrtb_binders)
                    }
                    TraitProjectionAnswer::NoSolution if !concrete => Ok(residual),
                    answer => Err(Box::new(answer)),
                };
                active.pop();
                result
            }
            Type::Tuple(values) => Ok(Type::Tuple(
                values
                    .into_iter()
                    .map(|value| {
                        self.normalize_type_projections_in_hrtb(value, active, hrtb_binders)
                    })
                    .collect::<Result<_, _>>()?,
            )),
            Type::FixedArray { element, length } => Ok(Type::FixedArray {
                element: Box::new(self.normalize_type_projections_in_hrtb(*element, active, hrtb_binders)?),
                length: Box::new(self.normalize_trait_argument_in_hrtb(*length, active, hrtb_binders)?),
            }),
            Type::Array(value) => Ok(Type::Array(Box::new(
                self.normalize_type_projections_in_hrtb(*value, active, hrtb_binders)?,
            ))),
            Type::StaticData { element, tag, alignment } => Ok(Type::StaticData {
                element: Box::new(self.normalize_type_projections_in_hrtb(*element, active, hrtb_binders)?),
                tag, alignment,
            }),
            Type::RawPointer { mutability, pointee } => Ok(Type::RawPointer {
                mutability,
                pointee: Box::new(self.normalize_type_projections_in_hrtb(*pointee, active, hrtb_binders)?),
            }),
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => Ok(Type::Reference {
                mutability,
                lifetime,
                referent: Box::new(self.normalize_type_projections_in_hrtb(
                    *referent,
                    active,
                    hrtb_binders,
                )?),
            }),
            Type::Callable { contract,
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } => {
                let mut nested_binders = Vec::with_capacity(hrtb_binders.len() + 1);
                nested_binders.push(lifetime_binders);
                nested_binders.extend_from_slice(hrtb_binders);
                let mut error = None;
                let contract = contract.map_scoped_terms(|value, scopes| {
                    let mut scopes = scopes.to_vec();
                    scopes.extend_from_slice(&nested_binders);
                    match self.normalize_trait_argument_in_hrtb(value.clone(), active, &scopes) {
                        Ok(value) => value,
                        Err(failure) => { error = Some(failure); value },
                    }
                });
                if let Some(error) = error { return Err(error); }
                Ok(Type::Callable { contract: Box::new(contract),
                    safety,
                    lifetime_binders,
                    parameters: parameters
                        .into_iter()
                        .map(|parameter| {
                            self.normalize_type_projections_in_hrtb(
                                parameter,
                                active,
                                &nested_binders,
                            )
                        })
                        .collect::<Result<_, _>>()?,
                    result: Box::new(self.normalize_type_projections_in_hrtb(
                        *result,
                        active,
                        &nested_binders,
                    )?),
                    effects: self.normalize_effect_row_projections_in_hrtb(effects, active, &nested_binders)
                        .map_err(|answer| Box::new(TraitProjectionAnswer::NestedEffectRowProjection { answer }))?,
                    invocation,
                })
            }
            value => Ok(value),
        }
    }

    /// Normalize a structural associated constant through selected trait
    /// evidence.  The full generic trait relation is passed unchanged to the
    /// normal solver table, so `Trait<7>::N` and `Trait<8>::N` cannot alias.
    pub fn normalize_associated_const(
        &mut self,
        goal: TraitGoal,
        name: &str,
        expected: crate::ConstKind,
    ) -> TraitConstProjectionAnswer {
        self.select_associated_const(goal, name, expected, false)
    }

    fn select_associated_const(
        &mut self,
        goal: TraitGoal,
        name: &str,
        expected: crate::ConstKind,
        scoped_hrtb: bool,
    ) -> TraitConstProjectionAnswer {
        // The requested trait must be selected before following the ancestor
        // that declares this inherited constant; Parent evidence alone is not
        // evidence for a Child-named projection.
        match if scoped_hrtb { self.solve_scoped_hrtb(goal.clone()) } else { self.solve(goal.clone()) } {
            TraitAnswer::Refuted { evidence } => {
                return TraitConstProjectionAnswer::Refuted { evidence };
            }
            TraitAnswer::Ambiguous => return TraitConstProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => return TraitConstProjectionAnswer::Overflow,
            TraitAnswer::Proven { .. } => {}
            TraitAnswer::NoSolution => return TraitConstProjectionAnswer::NoSolution,
        }
        let goal = match self.find_associated_item_goal(
            &goal,
            name,
            AssociatedItemKind::Const,
            &mut Vec::new(),
        ) {
            SupertraitLookup::Found(goal) => goal,
            SupertraitLookup::Missing => goal,
            SupertraitLookup::Ambiguous => return TraitConstProjectionAnswer::Ambiguous,
        };
        match self.solve_projection_implementation(goal.clone(), scoped_hrtb) {
            TraitAnswer::Proven { evidence } => {
                let rules = Arc::clone(&self.rules);
                let Some(rule) = rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitConstProjectionAnswer::NoSolution;
                };
                let Some(substitution) = self.match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                    return TraitConstProjectionAnswer::NoSolution;
                };
                let value = rule
                    .implementation
                    .associated_consts
                    .get(name)
                    .map(|item| {
                        (
                            item.kind,
                            substitute_generic_argument(&item.value, &substitution),
                        )
                    })
                    .or_else(|| {
                        self.traits
                            .get(&goal.relation.definition)
                            .and_then(|trait_header| {
                                trait_header.associated_consts.get(name).and_then(|item| {
                                    item.default.as_ref().map(|value| {
                                        let substitution = default_associated_item_substitution(
                                            &goal,
                                            trait_header.generics,
                                            &[],
                                        );
                                        (
                                            item.kind,
                                            substitute_generic_argument(value, &substitution),
                                        )
                                    })
                                })
                            })
                    });
                match value {
                    Some((found, value)) if found == expected => {
                        TraitConstProjectionAnswer::Normalized { evidence, value }
                    }
                    Some((found, _)) => TraitConstProjectionAnswer::AssociatedConstKind {
                        evidence,
                        expected,
                        found,
                    },
                    None => TraitConstProjectionAnswer::MissingAssociatedConst { evidence },
                }
            }
            TraitAnswer::Refuted { evidence } => TraitConstProjectionAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => TraitConstProjectionAnswer::NoSolution,
            TraitAnswer::Ambiguous => TraitConstProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => TraitConstProjectionAnswer::Overflow,
        }
    }

    pub fn normalize_associated_effect_row_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> TraitEffectRowProjectionAnswer {
        let mut type_active = vec![];
        let subject = match self.normalize_type_projections(goal.subject, &mut type_active) {
            Ok(subject) => subject,
            Err(answer) => {
                return TraitEffectRowProjectionAnswer::NestedTypeProjection { answer };
            }
        };
        let trait_arguments = match goal
            .relation
            .arguments
            .into_iter()
            .map(|argument| self.normalize_trait_argument(argument, &mut type_active))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(answer) => {
                return TraitEffectRowProjectionAnswer::NestedTypeProjection { answer };
            }
        };
        let arguments = match arguments
            .iter()
            .cloned()
            .map(|argument| self.normalize_trait_argument(argument, &mut type_active))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(answer) => {
                return TraitEffectRowProjectionAnswer::NestedTypeProjection { answer };
            }
        };
        let goal = TraitGoal {
            relation: ElaboratedTraitReference {
                definition: goal.relation.definition,
                arguments: trait_arguments,
            },
            subject,
        };
        let root_key = associated_effect_row_projection_key(&goal, name, &arguments);
        let answer = self.select_associated_effect_row_application(goal, name, &arguments, false);
        let TraitEffectRowProjectionAnswer::Normalized { evidence, row } = answer else {
            return answer;
        };
        let mut active = vec![root_key];
        match self.normalize_effect_row_projections(row, &mut active) {
            Ok(row) => TraitEffectRowProjectionAnswer::Normalized { evidence, row },
            Err(answer) => *answer,
        }
    }

    /// Perform only selection and substitution for an associated effect row.
    /// The public normalization boundary above owns recursive reduction, so
    /// nested rows share one active stack and cannot evade cycle detection.
    fn select_associated_effect_row_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
        scoped_hrtb_item_arguments: bool,
    ) -> TraitEffectRowProjectionAnswer {
        if !scoped_hrtb_item_arguments
            && (trait_goal_contains_escaping_hrtb(&goal)
                || arguments
                    .iter()
                    .any(generic_argument_contains_escaping_hrtb))
        {
            return TraitEffectRowProjectionAnswer::NoSolution;
        }
        if arguments.is_empty() && (is_intrinsic_callable_trait(&goal.relation) || is_intrinsic_runs_in_trait(&goal.relation)) {
            let Some(value) = self.callable_evidence(&goal) else { return TraitEffectRowProjectionAnswer::NoSolution; };
            return if name == "Effects" {
                TraitEffectRowProjectionAnswer::Normalized { evidence: assumption_evidence(&goal), row: value.effects }
            } else { TraitEffectRowProjectionAnswer::NoSolution };
        }
        // As with associated types, a supertrait declaration neither erases
        // negative evidence nor supplies missing evidence for the trait
        // through which the row was named.
        let requested = if scoped_hrtb_item_arguments {
            self.solve_scoped_hrtb(goal.clone())
        } else {
            self.solve(goal.clone())
        };
        match requested {
            TraitAnswer::Refuted { evidence } => {
                return TraitEffectRowProjectionAnswer::Refuted { evidence };
            }
            TraitAnswer::Ambiguous => return TraitEffectRowProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => return TraitEffectRowProjectionAnswer::Overflow,
            TraitAnswer::Proven { .. } => {}
            TraitAnswer::NoSolution => return TraitEffectRowProjectionAnswer::NoSolution,
        }
        if self.associated_contract(&goal, name, arguments).is_some()
            && !self.projection_domain_proven(&goal, name, arguments) { return TraitEffectRowProjectionAnswer::NoSolution; }
        let goal = match self.find_associated_item_goal(
            &goal,
            name,
            AssociatedItemKind::EffectRow,
            &mut Vec::new(),
        ) {
            SupertraitLookup::Found(goal) => goal,
            SupertraitLookup::Missing => goal,
            SupertraitLookup::Ambiguous => return TraitEffectRowProjectionAnswer::Ambiguous,
        };
        // Effect-row projection selection must use the same HRTB scope as
        // its type projection counterpart above.
        let answer = self.solve_projection_implementation(goal.clone(), scoped_hrtb_item_arguments);
        match answer {
            TraitAnswer::Proven { evidence } => {
                let rules = Arc::clone(&self.rules);
                let Some(rule) = rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitEffectRowProjectionAnswer::NoSolution;
                };
                let Some(mut substitution) = self.match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                    return TraitEffectRowProjectionAnswer::NoSolution;
                };
                match rule.implementation.associated_effect_rows.get(name) {
                    Some(_)
                        if !associated_effect_row_contract_matches(
                            self.traits.get(&goal.relation.definition),
                            name,
                            rule.implementation.associated_effect_rows.get(name),
                        ) =>
                    {
                        TraitEffectRowProjectionAnswer::NoSolution
                    }
                    Some(item) if item.generics != arguments.len() as u32 => {
                        TraitEffectRowProjectionAnswer::AssociatedEffectRowArity {
                            evidence,
                            expected: item.generics,
                            found: arguments.len() as u32,
                        }
                    }
                    Some(item)
                        if !generic_arguments_match_kinds(arguments, &item.generic_kinds) =>
                    {
                        TraitEffectRowProjectionAnswer::NoSolution
                    }
                    Some(item) => {
                        let base = rule.implementation.generics;
                        for (offset, argument) in arguments.iter().cloned().enumerate() {
                            install_item_argument(
                                &mut substitution,
                                base + offset as u32,
                                argument,
                            );
                        }
                        TraitEffectRowProjectionAnswer::Normalized {
                            evidence,
                            row: substitute_effect_row(&item.value, &substitution),
                        }
                    }
                    None => {
                        let Some(trait_header) = self.traits.get(&goal.relation.definition) else {
                            return TraitEffectRowProjectionAnswer::NoSolution;
                        };
                        let Some(declaration) = trait_header.associated_types.get(name) else {
                            return TraitEffectRowProjectionAnswer::MissingAssociatedEffectRow {
                                evidence,
                            };
                        };
                        if !declaration.effect_row {
                            return TraitEffectRowProjectionAnswer::NoSolution;
                        }
                        if declaration.generics != arguments.len() as u32 {
                            return TraitEffectRowProjectionAnswer::AssociatedEffectRowArity {
                                evidence,
                                expected: declaration.generics,
                                found: arguments.len() as u32,
                            };
                        }
                        if !generic_arguments_match_kinds(arguments, &declaration.generic_kinds) {
                            return TraitEffectRowProjectionAnswer::NoSolution;
                        }
                        let Some(default) = &declaration.effect_row_default else {
                            return TraitEffectRowProjectionAnswer::MissingAssociatedEffectRow {
                                evidence,
                            };
                        };
                        let substitution = default_associated_item_substitution(
                            &goal,
                            trait_header.generics,
                            arguments,
                        );
                        TraitEffectRowProjectionAnswer::Normalized {
                            evidence,
                            row: substitute_effect_row(default, &substitution),
                        }
                    }
                }
            }
            TraitAnswer::Refuted { evidence } => {
                TraitEffectRowProjectionAnswer::Refuted { evidence }
            }
            TraitAnswer::NoSolution => TraitEffectRowProjectionAnswer::NoSolution,
            TraitAnswer::Ambiguous => TraitEffectRowProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => TraitEffectRowProjectionAnswer::Overflow,
        }
    }

    /// Row entry into the same kinded normalization query. Recursive calls
    /// retain its active keys even while traversing a type-valued argument.
    fn normalize_effect_row_projections(
        &mut self,
        value: EffectRow,
        active: &mut Vec<Digest>,
    ) -> Result<EffectRow, Box<TraitEffectRowProjectionAnswer>> {
        self.normalize_effect_row_projections_in_hrtb(value, active, &[])
    }

    fn normalize_effect_row_projections_in_hrtb(
        &mut self,
        value: EffectRow,
        active: &mut Vec<Digest>,
        hrtb_binders: &[u32],
    ) -> Result<EffectRow, Box<TraitEffectRowProjectionAnswer>> {
        if row_projection_normalization_is_identity(&value) { return Ok(value); }
        let effects = value
            .effects
            .into_iter()
            .map(|effect| {
                let arguments = effect
                    .arguments
                    .into_iter()
                    .map(|argument| {
                        self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                    })
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|answer| {
                        Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                    })?;
                Ok(EffectInstance {
                    definition: effect.definition,
                    arguments,
                })
            })
            .collect::<Result<_, Box<TraitEffectRowProjectionAnswer>>>()?;
        let mut result = EffectRow {
            effects,
            projections: vec![],
            tails: value.tails.clone(),
        };
        for projection in value.projections {
            let subject = self
                .normalize_type_projections_in_hrtb(*projection.subject, active, hrtb_binders)
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let trait_arguments = projection
                .trait_arguments
                .into_iter()
                .map(|argument| {
                    self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let item_arguments = projection
                .item_arguments
                .into_iter()
                .map(|argument| {
                    self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let projection = crate::EffectRowProjection {
                subject: Box::new(subject),
                trait_definition: projection.trait_definition,
                trait_arguments,
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments,
            };
            if let Some(value) = self.assumed_effect_value(&projection).map_err(Box::new)? {
                if !self.projection_domain_proven(&TraitGoal { subject: (*projection.subject).clone(), relation: ElaboratedTraitReference {
                    definition: projection.trait_definition, arguments: projection.trait_arguments.clone(),
                } }, &projection.name, &projection.item_arguments) { return Err(Box::new(TraitEffectRowProjectionAnswer::NoSolution)); }
                let key = associated_effect_row_projection_key(&TraitGoal {
                    subject: (*projection.subject).clone(), relation: ElaboratedTraitReference {
                        definition: projection.trait_definition, arguments: projection.trait_arguments.clone(),
                    },
                }, &projection.name, &projection.item_arguments);
                if active.contains(&key) { return Err(Box::new(TraitEffectRowProjectionAnswer::RecursiveProjection)); }
                if active.len() >= self.limits.max_depth as usize { return Err(Box::new(TraitEffectRowProjectionAnswer::Overflow)); }
                active.push(key);
                let normalized = self.normalize_effect_row_projections_in_hrtb(value, active, hrtb_binders);
                active.pop();
                let normalized = normalized?;
                result.effects.extend(normalized.effects);
                result.projections.extend(normalized.projections);
                result.tails.extend(normalized.tails);
                continue;
            }
            let concrete = projection_is_concrete_in_hrtb_scope(&projection.subject, hrtb_binders)
                && projection.trait_arguments.iter().all(|argument| generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders))
                && projection.item_arguments.iter().all(|argument| generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders));
            if !concrete && !projection_application_is_selectable(&projection.subject, projection.trait_definition, &projection.trait_arguments, &projection.item_arguments, hrtb_binders) {
                let input = GenericArgument::EffectRow(EffectRow { effects: Default::default(),
                    tails: Default::default(), projections: vec![projection.clone()] });
                if let Some(GenericArgument::EffectRow(normalized)) = self.normalize_parametric_regions(input, active, hrtb_binders) {
                    result.effects.extend(normalized.effects);
                    result.projections.extend(normalized.projections);
                    result.tails.extend(normalized.tails);
                    continue;
                }
                result.projections.push(projection);
                continue;
            }
            let residual = projection.clone();
            let goal = TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: projection.trait_definition,
                    arguments: projection.trait_arguments,
                },
                subject: *projection.subject,
            };
            let item_arguments = projection.item_arguments;
            if !generic_arguments_match_kinds(&item_arguments, &projection.item_generic_kinds) {
                return Err(Box::new(TraitEffectRowProjectionAnswer::NoSolution));
            }
            let key =
                associated_effect_row_projection_key(&goal, &projection.name, &item_arguments);
            if active.contains(&key) {
                return Err(Box::new(
                    TraitEffectRowProjectionAnswer::RecursiveProjection,
                ));
            }
            if active.len() >= self.limits.max_depth as usize {
                return Err(Box::new(TraitEffectRowProjectionAnswer::Overflow));
            }
            active.push(key);
            let nested = self.select_associated_effect_row_application(
                goal,
                &projection.name,
                &item_arguments,
                !hrtb_binders.is_empty(),
            );
            let nested = match nested {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    self.normalize_effect_row_projections_in_hrtb(row, active, hrtb_binders)
                }
                TraitEffectRowProjectionAnswer::NoSolution if !concrete => Ok(EffectRow {
                    effects: Default::default(), projections: vec![residual], tails: Default::default(),
                }),
                answer => Err(Box::new(answer)),
            };
            active.pop();
            let nested = nested?;
            result.effects.extend(nested.effects);
            result.projections.extend(nested.projections);
            result.tails.extend(nested.tails);
        }
        Ok(result.canonicalized())
    }

    /// Select an implementation method and instantiate both the implementation
    /// binders and method-local generic binders. The returned method identity
    /// and implementation evidence let later Core/MIR lowering name the
    /// callable body without repeating source-shaped impl lookup.
    pub fn select_method(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
    ) -> TraitMethodAnswer {
        // Supertrait lookup identifies the declaration that owns `name`, but
        // it must not turn evidence for that parent into evidence for the
        // originally requested child relation.  Establish the requested
        // relation first, then select its inherited declaration.
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { .. } => {}
            TraitAnswer::Refuted { evidence } => return TraitMethodAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => return TraitMethodAnswer::NoSolution,
            TraitAnswer::Ambiguous => return TraitMethodAnswer::Ambiguous,
            TraitAnswer::Overflow => return TraitMethodAnswer::Overflow,
        }
        let goal = match self.method_goal(goal, name) {
            Ok(goal) => goal,
            Err(answer) => return answer,
        };
        let answer = self.solve(goal.clone());
        self.finish_method_selection(goal, name, arguments, answer)
    }

    /// Select a method with lexical trait evidence from the enclosing
    /// declaration.  These assumptions can establish inherited parent traits
    /// without becoming globally cached implementation evidence.
    /// Seed only constraints common to the sole structurally compatible
    /// implementation head. This is not implementation evidence: the caller
    /// must still solve the complete goal, including where clauses and
    /// inherited relations. Multiple compatible heads never pick a winner.
    /// Each trial has isolated inference state, including numeric classes.
    pub(crate) fn constrain_unique_implementation_head(
        &self,
        goal: &TraitGoal,
        inference: &mut crate::InferContext,
    ) {
        let mut selected = None;
        for rule in self.rules.iter().filter(|rule| rule.implementation.relation.definition == goal.relation.definition) {
            let implementation = &rule.implementation;
            let mut trial = inference.clone();
            let mut substitution = ImplementationSubstitution::default();
            for (index, kind) in implementation.generic_kinds.iter().enumerate() {
                let argument = match kind {
                    crate::GenericKind::Type => GenericArgument::Type(trial.fresh()),
                    crate::GenericKind::Lifetime => GenericArgument::Lifetime(trial.fresh_lifetime()),
                    crate::GenericKind::EffectRow => GenericArgument::EffectRow(trial.fresh_effects()),
                    crate::GenericKind::Const(kind) => trial.fresh_const(*kind),
                };
                install_item_argument(&mut substitution, index as u32, argument);
            }
            let mut arguments = implementation.relation.arguments.iter()
                .map(|argument| substitute_generic_argument(argument, &substitution)).collect::<Vec<_>>();
            arguments.push(GenericArgument::Type(substitute_type(&implementation.self_ty, &substitution)));
            let mut actual = goal.relation.arguments.clone();
            actual.push(GenericArgument::Type(goal.subject.clone()));
            if trial.unify(
                Type::Nominal { definition: goal.relation.definition, arguments },
                Type::Nominal { definition: goal.relation.definition, arguments: actual },
            ).is_ok() {
                if selected.is_some() { return; }
                selected = Some((trial, implementation.negative));
            }
        }
        if let Some((trial, false)) = selected { *inference = trial; }
    }

    pub fn select_method_with_assumptions(
        &self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
        assumptions: &[TraitGoal],
    ) -> TraitMethodAnswer {
        // Lexical evidence can establish the requested child relation, but
        // evidence for only an inherited parent cannot.
        match self.solve_with_assumptions(goal.clone(), assumptions) {
            TraitAnswer::Proven { .. } => {}
            TraitAnswer::Refuted { evidence } => return TraitMethodAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => return TraitMethodAnswer::NoSolution,
            TraitAnswer::Ambiguous => return TraitMethodAnswer::Ambiguous,
            TraitAnswer::Overflow => return TraitMethodAnswer::Overflow,
        }
        let goal = match self.method_goal(goal, name) {
            Ok(goal) => goal,
            Err(answer) => return answer,
        };
        let answer = self.solve_implementation_with_assumptions(goal.clone(), assumptions);
        self.finish_method_selection(goal, name, arguments, answer)
    }

    fn method_goal(&self, goal: TraitGoal, name: &str) -> Result<TraitGoal, TraitMethodAnswer> {
        match self.find_method_goal(&goal, name, &mut Vec::new()) {
            SupertraitLookup::Found(goal) => Ok(goal),
            SupertraitLookup::Missing => Err(TraitMethodAnswer::NoSolution),
            SupertraitLookup::Ambiguous => Err(TraitMethodAnswer::Ambiguous),
        }
    }

    fn finish_method_selection(
        &self,
        goal: TraitGoal,
        name: &str,
        arguments: &[GenericArgument],
        answer: TraitAnswer,
    ) -> TraitMethodAnswer {
        match answer {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitMethodAnswer::NoSolution;
                };
                let Some(method) = rule.implementation.methods.get(name) else {
                    return TraitMethodAnswer::MissingMethod { evidence };
                };
                if method.generics != arguments.len() as u32 {
                    return TraitMethodAnswer::MethodArity {
                        evidence,
                        expected: method.generics,
                        found: arguments.len() as u32,
                    };
                }
                if !generic_arguments_match_kinds(arguments, &method.generic_kinds) {
                    return TraitMethodAnswer::NoSolution;
                }
                let Some(mut substitution) = self.fresh_query().match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                    return TraitMethodAnswer::NoSolution;
                };
                for (offset, argument) in arguments.iter().cloned().enumerate() {
                    install_item_argument(
                        &mut substitution,
                        rule.implementation.generics + offset as u32,
                        argument,
                    );
                }
                TraitMethodAnswer::Selected {
                    method: implementation_method_key(evidence, name),
                    evidence,
                    signature: Box::new(substitute_callable_signature(method, &substitution)),
                }
            }
            TraitAnswer::Refuted { evidence } => TraitMethodAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => TraitMethodAnswer::NoSolution,
            TraitAnswer::Ambiguous => TraitMethodAnswer::Ambiguous,
            TraitAnswer::Overflow => TraitMethodAnswer::Overflow,
        }
    }

    /// Recover the concrete relation arguments implied by a receiver before
    /// selecting an implicit trait surface. The normal solver deliberately
    /// refuses caller-owned inference variables in a frozen goal; operator
    /// syntax has no written trait arguments, so its elaborator derives them
    /// from an implementation receiver pattern and then issues an ordinary
    /// canonical `select_method` request.
    ///
    /// This exposes only substituted frozen relation identities. Coherence,
    /// negative implementations, and where-obligations remain the authority
    /// of `select_method`.
    pub fn relations_for_subject(
        &self,
        definition: DefKey,
        subject: &Type,
    ) -> Vec<ElaboratedTraitReference> {
        let mut relations = Vec::new();
        for rule in self
            .rules
            .iter()
            .filter(|rule| rule.implementation.relation.definition == definition)
        {
            let mut substitution = ImplementationSubstitution::default();
            if match_type(&rule.implementation.self_ty, subject, &mut substitution).is_some()
                && solve_pending_effect_rows(&mut substitution).is_some() {
                let relation = substitute_relation(&rule.implementation.relation, &substitution);
                if !relations.contains(&relation) {
                    relations.push(relation);
                }
            }
        }
        relations
    }
    fn solve_at(
        &mut self,
        goal: TraitGoal,
        depth: u32,
        coinductive_edge: bool,
    ) -> TraitAnswerIndex {
        let assumptions = Arc::clone(&self.lexical_assumptions);
        self.solve_at_with_assumptions(goal, depth, coinductive_edge, &assumptions, true)
    }

    /// The tabled kernel for one fixed lexical assumption environment. The
    /// caller either supplies no assumptions (`solve`) or uses a private,
    /// fresh clone (`solve_with_assumptions`), so the existing goal-keyed
    /// table cannot cross an environment boundary.
    fn solve_at_with_assumptions(
        &mut self,
        goal: TraitGoal,
        depth: u32,
        coinductive_edge: bool,
        assumptions: &[TraitGoal],
        accept_direct_assumption: bool,
    ) -> TraitAnswerIndex {
        if depth >= self.limits.max_depth || self.steps >= self.limits.max_steps {
            return TraitAnswerIndex::Overflow;
        }
        self.remember_callable_environments(&goal.subject);
        // A trait relation may itself be headed by a concrete associated
        // projection: `Value: Consume<<Value as Source>::Item>`.  Projection
        // requests already normalize their own heads, but ordinary goals and
        // implementation where-obligations enter through this path.  Keeping
        // normalization at the shared goal boundary prevents those two
        // semantically equivalent routes from selecting different evidence.
        let goal = match self.normalize_goal(goal) {
            Ok(goal) => goal,
            Err(answer) => return answer,
        };
        if matches!(
            goal.subject,
            Type::Callable {
                safety: crate::Safety::Unsafe,
                ..
            }
        ) && (is_intrinsic_callable_trait(&goal.relation)
            || is_intrinsic_label_trait(&goal.relation))
        {
            // Even caller-provided assumptions cannot relabel an explicitly
            // unsafe function value as safe callable/label evidence.
            return TraitAnswerIndex::NoSolution;
        }
        if accept_direct_assumption && self.assumption_proves(&goal, assumptions) {
            return TraitAnswerIndex::Proven(assumption_evidence(&goal));
        }
        if accept_direct_assumption && self.lexical_universal.iter().any(|bound| bound.for_goal(&goal).is_some()) {
            return TraitAnswerIndex::Proven(assumption_evidence(&goal));
        }
        if accept_direct_assumption && self.associated_result_proves(&goal, assumptions, depth + 1) {
            return TraitAnswerIndex::Proven(assumption_evidence(&goal));
        }
        if accept_direct_assumption
            && goal.relation.definition == crate::resolution::language_use_trait_definition()
        {
            let [GenericArgument::ConstQuantity(required)] = goal.relation.arguments.as_slice()
                else { return TraitAnswerIndex::NoSolution; };
            if self.principal_active.contains(&goal.subject) {
                return TraitAnswerIndex::Ambiguous;
            }
            return if self.principal_use_at(&goal.subject, depth + 1, assumptions, UseEvidence::Declared)
                .is_some_and(|principal| principal.contains(*required))
            {
                TraitAnswerIndex::Proven(assumption_evidence(&goal))
            } else {
                TraitAnswerIndex::NoSolution
            };
        }
        if is_intrinsic_callable_trait(&goal.relation) {
            return self.solve_intrinsic_callable_goal(&goal);
        }
        if is_intrinsic_label_trait(&goal.relation) {
            return self.solve_intrinsic_label_goal(&goal);
        }
        // `RunsIn` evidence is emitted only by Core closure sealing, where a
        // brand is checked against the exact capture post-state and callable
        // effects. A general source-trait query has no such environment
        // witness, so it must fail closed rather than treating a spelling or
        // forged interface implementation as authority.
        if is_intrinsic_runs_in_trait(&goal.relation) {
            return if self.callable_evidence(&goal).is_some() {
                TraitAnswerIndex::Proven(assumption_evidence(&goal))
            } else { TraitAnswerIndex::NoSolution };
        }
        if crate::is_intrinsic_environment_trait(&goal.relation) {
            let [GenericArgument::Lifetime(lifetime)] = goal.relation.arguments.as_slice() else { return TraitAnswerIndex::NoSolution; };
            return if (goal.subject == Type::Unit || self.callable_environments.contains(&goal.subject))
                && (*lifetime == crate::Lifetime::Elided || self.outlives_proven(&crate::OutlivesPredicate::Type {
                    subject: goal.subject.clone(), lifetime: *lifetime,
                })) {
                TraitAnswerIndex::Proven(assumption_evidence(&goal))
            } else { TraitAnswerIndex::NoSolution };
        }
        self.steps += 1;
        let key = goal_key(&goal);
        match self.tables.get(&key).copied() {
            Some(TableState::Complete(answer)) => return answer,
            // A recursive success is available only across a structural auto
            // edge. Rule where-bounds always pass `false`, so a mixed cycle
            // containing an ordinary trait remains inductively ambiguous.
            Some(TableState::Evaluating) if coinductive_edge && self.is_auto_trait(&goal) => {
                return TraitAnswerIndex::Proven(self.structural_evidence(&goal));
            }
            Some(TableState::Evaluating) => return TraitAnswerIndex::Ambiguous,
            None => {}
        }
        self.tables.insert(key, TableState::Evaluating);

        let rules = self
            .rules
            .iter()
            .filter(|rule| rule.implementation.relation.definition == goal.relation.definition)
            .cloned()
            .collect::<Vec<_>>();
        let mut positives = vec![];
        let mut negatives = vec![];
        let mut saw_cycle = false;
        let mut saw_overflow = false;
        for rule in rules {
            let Some(substitution) = self.match_rule_with_callable_bindings(&rule.implementation, &goal) else {
                continue;
            };
            let required_safety = if rule.implementation.negative {
                crate::Safety::Safe
            } else {
                self.traits.get(&goal.relation.definition).map_or(crate::Safety::Safe, |header| header.safety)
            };
            if rule.implementation.safety != required_safety {
                return TraitAnswerIndex::NoSolution;
            }
            let mut viable = true;
            for (subject, relation) in &rule.implementation.where_bounds {
                let obligation = TraitGoal {
                    relation: substitute_relation(relation, &substitution),
                    subject: substitute_type(subject, &substitution),
                };
                match self.solve_at_with_assumptions(
                    obligation,
                    depth + 1,
                    false,
                    assumptions,
                    true,
                ) {
                    TraitAnswerIndex::Proven(_) => {}
                    TraitAnswerIndex::Ambiguous => {
                        viable = false;
                        saw_cycle = true;
                        break;
                    }
                    TraitAnswerIndex::Overflow => {
                        viable = false;
                        saw_overflow = true;
                        break;
                    }
                    TraitAnswerIndex::Refuted(_) | TraitAnswerIndex::NoSolution => {
                        viable = false;
                        break;
                    }
                }
            }
            if viable && let Err(answer) = self.check_implementation_bindings(&rule.implementation, &substitution) {
                viable = false;
                saw_cycle |= matches!(answer, TraitAnswerIndex::Ambiguous);
                saw_overflow |= matches!(answer, TraitAnswerIndex::Overflow);
            }
            if viable {
                if rule.implementation.negative {
                    negatives.push(rule.definition);
                } else {
                    positives.push(rule.definition);
                }
            }
        }
        let mut answer = select_answer(&positives, &negatives, saw_cycle, saw_overflow);
        if matches!(answer, TraitAnswerIndex::NoSolution) {
            answer = self.solve_structural_auto_goal_with_assumptions(&goal, depth, assumptions);
        }
        self.tables.insert(key, TableState::Complete(answer));
        answer
    }

    fn check_implementation_bindings(
        &mut self, implementation: &ElaboratedImplementation,
        substitution: &ImplementationSubstitution,
    ) -> Result<(), TraitAnswerIndex> {
        for bound in &implementation.universal_bounds {
            // Inserting impl arguments beneath the quantifier must shift any
            // caller-owned bound regions rather than capturing them.
            let shifted = substitution_under_region_binder(substitution).ok_or(TraitAnswerIndex::NoSolution)?;
            let bound = bound.map_terms(|argument| substitute_generic_argument(&argument, &shifted));
            if !self.proves_universal(&bound) { return Err(TraitAnswerIndex::NoSolution); }
        }
        if implementation.where_outlives.iter().any(|bound| !self.outlives_proven(&bound.map_terms(|argument|
            substitute_generic_argument(&argument, substitution)))) {
            return Err(TraitAnswerIndex::NoSolution);
        }
        fn type_failure(answer: TraitProjectionAnswer) -> TraitAnswerIndex {
            match answer {
                TraitProjectionAnswer::Ambiguous | TraitProjectionAnswer::RecursiveProjection => TraitAnswerIndex::Ambiguous,
                TraitProjectionAnswer::Overflow => TraitAnswerIndex::Overflow,
                TraitProjectionAnswer::NestedEffectRowProjection { answer } => row_failure(*answer),
                _ => TraitAnswerIndex::NoSolution,
            }
        }
        fn row_failure(answer: TraitEffectRowProjectionAnswer) -> TraitAnswerIndex {
            match answer {
                TraitEffectRowProjectionAnswer::Ambiguous | TraitEffectRowProjectionAnswer::RecursiveProjection => TraitAnswerIndex::Ambiguous,
                TraitEffectRowProjectionAnswer::Overflow => TraitAnswerIndex::Overflow,
                TraitEffectRowProjectionAnswer::NestedTypeProjection { answer } => type_failure(*answer),
                _ => TraitAnswerIndex::NoSolution,
            }
        }
        for binding in &implementation.where_associated_type_bindings {
            let projection = Type::Projection {
                subject: Box::new(substitute_type(&binding.subject, substitution)),
                trait_definition: binding.relation.definition,
                trait_arguments: substitute_relation(&binding.relation, substitution).arguments,
                name: binding.name.clone(), item_generic_kinds: binding.item_generic_kinds.clone(),
                item_arguments: binding.item_arguments.iter().map(|argument| substitute_generic_argument(argument, substitution)).collect(),
            };
            let actual = self.normalize_type(projection).map_err(|answer| type_failure(*answer))?;
            let expected = self.normalize_type(substitute_type(&binding.value, substitution)).map_err(|answer| type_failure(*answer))?;
            if actual != expected {
                return Err(if projection_is_concrete_in_hrtb_scope(&actual, &[])
                    && projection_is_concrete_in_hrtb_scope(&expected, &[]) {
                    TraitAnswerIndex::NoSolution
                } else { TraitAnswerIndex::Ambiguous });
            }
        }
        for binding in &implementation.where_associated_effect_bindings {
            let projection = EffectRow { effects: Default::default(), tails: Default::default(),
                projections: vec![crate::EffectRowProjection {
                    subject: Box::new(substitute_type(&binding.subject, substitution)),
                    trait_definition: binding.relation.definition,
                    trait_arguments: substitute_relation(&binding.relation, substitution).arguments,
                    name: binding.name.clone(), item_generic_kinds: binding.item_generic_kinds.clone(),
                    item_arguments: binding.item_arguments.iter().map(|argument| substitute_generic_argument(argument, substitution)).collect(),
                }],
            };
            let actual = self.normalize_effect_row(projection).map_err(|answer| row_failure(*answer))?;
            let expected = self.normalize_effect_row(substitute_effect_row(&binding.value, substitution)).map_err(|answer| row_failure(*answer))?;
            let actual = GenericArgument::EffectRow(actual);
            let expected = GenericArgument::EffectRow(expected);
            if canonical_generic_arguments_encoding(std::slice::from_ref(&actual))
                != canonical_generic_arguments_encoding(std::slice::from_ref(&expected)) {
                return Err(if generic_argument_is_concrete_in_hrtb_scope(&actual, &[])
                    && generic_argument_is_concrete_in_hrtb_scope(&expected, &[]) {
                    TraitAnswerIndex::NoSolution
                } else { TraitAnswerIndex::Ambiguous });
            }
        }
        Ok(())
    }

    fn is_auto_trait(&self, goal: &TraitGoal) -> bool {
        self.traits
            .get(&goal.relation.definition)
            .is_some_and(|trait_header| trait_header.auto_trait)
    }

    /// `Fn` is compiler-owned evidence, not a declaration that source code
    /// can shadow or implement.  Its sole proof rule is the frozen callable
    /// shape: the single positional relation argument is the input tuple.
    fn solve_intrinsic_callable_goal(&mut self, goal: &TraitGoal) -> TraitAnswerIndex {
        if self.callable_evidence(goal).is_none() { return TraitAnswerIndex::NoSolution; }
        let key = goal_key(goal);
        TraitAnswerIndex::Proven(DefKey(Digest::of_parts([
            b"grandiose-stage0-intrinsic-callable-evidence-v1".as_slice(),
            key.as_bytes().as_slice(),
        ])))
    }

    fn solve_intrinsic_label_goal(&self, goal: &TraitGoal) -> TraitAnswerIndex {
        let [GenericArgument::Type(payload)] = goal.relation.arguments.as_slice() else {
            return TraitAnswerIndex::NoSolution;
        };
        if crate::types::label::payload(&goal.subject) != Some(payload) {
            return TraitAnswerIndex::NoSolution;
        }
        let key = goal_key(goal);
        TraitAnswerIndex::Proven(DefKey(Digest::of_parts([
            b"grandiose-stage0-intrinsic-label-evidence-v1".as_slice(),
            key.as_bytes().as_slice(),
        ])))
    }

    /// Produce structural auto-trait evidence only when the source has
    /// explicitly declared the relation `auto`. An explicit positive or
    /// negative implementation is selected before this fallback, so a
    /// negative impl reliably opts a type out of otherwise structural proof.
    fn solve_structural_auto_goal_with_assumptions(
        &mut self,
        goal: &TraitGoal,
        depth: u32,
        assumptions: &[TraitGoal],
    ) -> TraitAnswerIndex {
        if !self.is_auto_trait(goal) {
            return TraitAnswerIndex::NoSolution;
        }
        let Some(obligations) = self.structural_obligations(goal) else {
            return TraitAnswerIndex::NoSolution;
        };
        for obligation in obligations {
            match self.solve_at_with_assumptions(
                obligation,
                depth + 1,
                true,
                assumptions,
                true,
            ) {
                TraitAnswerIndex::Proven(_) => {}
                TraitAnswerIndex::Overflow => return TraitAnswerIndex::Overflow,
                TraitAnswerIndex::Ambiguous => return TraitAnswerIndex::Ambiguous,
                TraitAnswerIndex::Refuted(_) | TraitAnswerIndex::NoSolution => {
                    return TraitAnswerIndex::NoSolution;
                }
            }
        }
        TraitAnswerIndex::Proven(self.structural_evidence(goal))
    }

    /// Return whether a lexical assumption establishes a goal directly or
    /// through the declaration-level supertrait closure. This is exact frozen
    /// goal identity rather than unification: assumptions quantify only the
    /// source binders already present in their owner, and must never become
    /// ambient blanket implementations for arbitrary callers. `Use` is the
    /// one exception to exact quantity identity: a principal interval is
    /// evidence for every interval it contains. In particular,
    /// `Use<[0,*]>` proves the affine-erasure requirement `Use<[0,1]>`.
    pub(crate) fn assumption_proves(&self, goal: &TraitGoal, assumptions: &[TraitGoal]) -> bool {
        let mut pending = assumptions.to_vec();
        let mut seen = Vec::<TraitGoal>::new();
        while let Some(candidate) = pending.pop() {
            if seen.iter().any(|known| known == &candidate) {
                continue;
            }
            if candidate == *goal || use_assumption_contains(&candidate, goal) {
                return true;
            }
            seen.push(candidate.clone());
            pending.extend(self.supertrait_goals(&candidate));
        }
        false
    }

    fn structural_evidence(&self, goal: &TraitGoal) -> DefKey {
        let key = goal_key(goal);
        DefKey(Digest::of_parts([
            b"grandiose-stage0-structural-auto-trait-v1".as_slice(),
            goal.relation.definition.0.as_bytes().as_slice(),
            key.as_bytes().as_slice(),
        ]))
    }

    /// Enumerate the direct field/value obligations of one auto-trait goal.
    /// An enum requires every payload shape to satisfy the trait: its runtime
    /// value may inhabit any declared variant. Scalars and uninhabited/unit
    /// values have no contained type obligation.
    fn structural_obligations(&self, goal: &TraitGoal) -> Option<Vec<TraitGoal>> {
        let subjects = match &goal.subject {
            Type::Unit | Type::Never | Type::Scalar(_) => vec![],
            Type::Tuple(values) => values.clone(),
            Type::Array(value) => vec![(**value).clone()],
            Type::FixedArray { element, .. } => if goal.subject.fixed_array_length() == Some(0) {
                vec![]
            } else { vec![(**element).clone()] },
            // Static data is a sealed VM handle, not an aggregate whose
            // backing bytes participate in user-visible auto-trait proofs.
            Type::StaticData { .. } => vec![],
            Type::Reference { referent, .. } => vec![(**referent).clone()],
            // Neither a pointee's traits nor an empty field list establish
            // arbitrary auto-trait invariants for an unchecked pointer.
            // Explicit implementations must supply such evidence.
            Type::RawPointer { .. } => return None,
            Type::Callable {
                parameters, result, ..
            } => {
                let mut values = parameters.clone();
                values.push((**result).clone());
                values
            }
            Type::Nominal {
                definition,
                arguments,
            } => self.nominal_structural_fields(*definition, arguments)?,
            // A generic, projection, inference variable, const carrier, or
            // error has no known representation from which to derive proof.
            Type::Projection { .. }
            | Type::ConstInteger(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. }
            | Type::Generic(_)
            | Type::Infer(_)
            | Type::Error => return None,
        };
        Some(
            subjects
                .into_iter()
                .map(|subject| TraitGoal {
                    relation: goal.relation.clone(),
                    subject,
                })
                .collect(),
        )
    }

    fn nominal_structural_fields(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
    ) -> Option<Vec<Type>> {
        if definition == crate::refinement::bindings_definition() {
            return crate::refinement::binding_pack_fields(&Type::Nominal { definition, arguments: arguments.to_vec() }).map(<[Type]>::to_vec);
        }
        let ElaboratedHeader::Nominal {
            generics, layout, ..
        } = self.definitions.get(&definition)?
        else {
            return None;
        };
        if *generics as usize != arguments.len() {
            return None;
        }
        let mut substitution = ImplementationSubstitution::default();
        for (index, argument) in arguments.iter().cloned().enumerate() {
            install_item_argument(&mut substitution, index as u32, argument);
        }
        let fields: Vec<Type> = match layout {
            ElaboratedNominalLayout::Struct(fields) | ElaboratedNominalLayout::TupleStruct(fields) => {
                fields.iter().map(|field| field.ty.clone()).collect()
            }
            ElaboratedNominalLayout::Enum(variants) => variants
                .iter()
                .flat_map(|variant| match &variant.payload {
                    ElaboratedEnumVariantPayload::Unit => vec![],
                    ElaboratedEnumVariantPayload::Tuple(fields) => fields.clone(),
                    ElaboratedEnumVariantPayload::Struct(fields) => {
                        fields.iter().map(|field| field.ty.clone()).collect()
                    }
                })
                .collect(),
            ElaboratedNominalLayout::Opaque => return None,
        };
        Some(
            fields
                .into_iter()
                .map(|field| substitute_type(&field, &substitution))
                .collect(),
        )
    }

    /// Normalize a goal before keying or matching it. The normalizer and the
    /// selector consume the same lexical environment, so declaration/body
    /// consumers cannot invent a separate interpretation of generic heads.
    fn normalize_goal(&mut self, goal: TraitGoal) -> Result<TraitGoal, TraitAnswerIndex> {
        let mut active = vec![];
        let subject = self
            .normalize_type_projections(goal.subject, &mut active)
            .map_err(|answer| projection_failure_answer(*answer))?;
        let arguments = goal
            .relation
            .arguments
            .into_iter()
            .map(|argument| self.normalize_trait_argument(argument, &mut active))
            .collect::<Result<Vec<_>, _>>()
            .map_err(|answer| projection_failure_answer(*answer))?;
        Ok(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: goal.relation.definition,
                arguments,
            },
            subject,
        })
    }

    fn normalize_trait_argument(
        &mut self,
        argument: GenericArgument,
        active: &mut Vec<Digest>,
    ) -> Result<GenericArgument, Box<TraitProjectionAnswer>> {
        self.normalize_trait_argument_in_hrtb(argument, active, &[])
    }

    fn normalize_trait_argument_in_hrtb(
        &mut self,
        argument: GenericArgument,
        active: &mut Vec<Digest>,
        hrtb_binders: &[u32],
    ) -> Result<GenericArgument, Box<TraitProjectionAnswer>> {
        if argument_projection_normalization_is_identity(&argument) { return Ok(argument); }
        match argument {
            GenericArgument::Type(value) => self
                .normalize_type_projections_in_hrtb(value, active, hrtb_binders)
                .map(GenericArgument::Type),
            GenericArgument::EffectRow(value) => self
                .normalize_effect_row_projections_in_hrtb(value, active, hrtb_binders)
                .map(GenericArgument::EffectRow)
                .map_err(|answer| Box::new(TraitProjectionAnswer::NestedEffectRowProjection { answer })),
            GenericArgument::ConstProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                kind,
            } => {
                let subject =
                    self.normalize_type_projections_in_hrtb(*subject, active, hrtb_binders)?;
                let trait_arguments = trait_arguments
                    .into_iter()
                    .map(|argument| {
                        self.normalize_trait_argument_in_hrtb(argument, active, hrtb_binders)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let projection = GenericArgument::ConstProjection {
                    subject: Box::new(subject),
                    trait_definition,
                    trait_arguments,
                    name,
                    kind,
                };
                let residual = projection.clone();
                let GenericArgument::ConstProjection {
                    subject,
                    trait_definition,
                    trait_arguments,
                    name,
                    kind,
                } = projection
                else {
                    unreachable!("associated const projection was just constructed")
                };
                let concrete = projection_is_concrete_in_hrtb_scope(&subject, hrtb_binders)
                    && trait_arguments.iter().all(|argument| generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders));
                if !concrete && !projection_application_is_selectable(&subject, trait_definition, &trait_arguments, &[], hrtb_binders) {
                    return Ok(self.normalize_parametric_regions(residual.clone(), active, hrtb_binders).unwrap_or(residual));
                }
                let goal = TraitGoal {
                    relation: ElaboratedTraitReference {
                        definition: trait_definition,
                        arguments: trait_arguments,
                    },
                    subject: *subject,
                };
                let key = associated_const_projection_key(&goal, &name, kind);
                if active.contains(&key) {
                    return Err(Box::new(TraitProjectionAnswer::RecursiveProjection));
                }
                if active.len() >= self.limits.max_depth as usize {
                    return Err(Box::new(TraitProjectionAnswer::Overflow));
                }
                active.push(key);
                let answer = self.select_associated_const(goal, &name, kind, !hrtb_binders.is_empty());
                let result = match answer {
                    // An associated const may itself be specified through a
                    // second associated const. Keep reducing through the same
                    // active stack so a concrete `A::X = B::Y` reaches a VM
                    // structural term, while recursive definitions fail
                    // closed instead of leaking an unresolved projection.
                    TraitConstProjectionAnswer::Normalized { value, .. } => {
                        self.normalize_trait_argument_in_hrtb(value, active, hrtb_binders)
                    }
                    TraitConstProjectionAnswer::NoSolution if !concrete => Ok(residual),
                    TraitConstProjectionAnswer::Ambiguous => {
                        Err(Box::new(TraitProjectionAnswer::Ambiguous))
                    }
                    TraitConstProjectionAnswer::Overflow => {
                        Err(Box::new(TraitProjectionAnswer::Overflow))
                    }
                    TraitConstProjectionAnswer::Refuted { .. }
                    | TraitConstProjectionAnswer::NoSolution
                    | TraitConstProjectionAnswer::MissingAssociatedConst { .. }
                    | TraitConstProjectionAnswer::AssociatedConstKind { .. } => {
                        Err(Box::new(TraitProjectionAnswer::NoSolution))
                    }
                };
                active.pop();
                result
            }
            // Projection-free arguments retain their original kind.
            argument => Ok(argument),
        }
    }
}

fn use_assumption_contains(candidate: &TraitGoal, goal: &TraitGoal) -> bool {
    candidate.subject == goal.subject
        && candidate.relation.definition == crate::resolution::language_use_trait_definition()
        && goal.relation.definition == crate::resolution::language_use_trait_definition()
        && matches!(
            (candidate.relation.arguments.as_slice(), goal.relation.arguments.as_slice()),
            (
                [GenericArgument::ConstQuantity(provided)],
                [GenericArgument::ConstQuantity(required)],
            ) if provided.contains(*required)
        )
}

/// A projection failure cannot become implicit successful trait evidence.
/// A refuted *projection relation* is not a refutation of the outer trait
/// goal, so it is deliberately reported as no candidate rather than leaking
/// unrelated negative evidence into the result.  Recursive normalization is
/// a bounded solver failure; ambiguity remains ambiguity.
fn projection_failure_answer(answer: TraitProjectionAnswer) -> TraitAnswerIndex {
    match answer {
        TraitProjectionAnswer::NestedEffectRowProjection { answer } => match *answer {
            TraitEffectRowProjectionAnswer::NestedTypeProjection { answer } => projection_failure_answer(*answer),
            TraitEffectRowProjectionAnswer::Ambiguous => TraitAnswerIndex::Ambiguous,
            TraitEffectRowProjectionAnswer::Overflow | TraitEffectRowProjectionAnswer::RecursiveProjection => TraitAnswerIndex::Overflow,
            _ => TraitAnswerIndex::NoSolution,
        },
        TraitProjectionAnswer::Ambiguous => TraitAnswerIndex::Ambiguous,
        TraitProjectionAnswer::Overflow | TraitProjectionAnswer::RecursiveProjection => {
            TraitAnswerIndex::Overflow
        }
        TraitProjectionAnswer::Refuted { .. }
        | TraitProjectionAnswer::NoSolution
        | TraitProjectionAnswer::MissingAssociatedType { .. }
        | TraitProjectionAnswer::AssociatedTypeArity { .. } => TraitAnswerIndex::NoSolution,
        TraitProjectionAnswer::Normalized { .. } => {
            unreachable!("projection normalizer only returns normalized types through Ok")
        }
    }
}

/// One implementation match has separate substitution domains for types and
/// regions.  A source binder slot is shared for stable identity, but a
/// lifetime may never leak into the type map as a fabricated `Type::Generic`.
#[derive(Clone, Default)]
struct ImplementationSubstitution {
    types: BTreeMap<u32, Type>,
    lifetimes: BTreeMap<u32, crate::Lifetime>,
    generic_arguments: BTreeMap<u32, GenericArgument>,
    effect_rows: BTreeMap<u32, EffectRow>,
    pending_effect_rows: Vec<(EffectRow, EffectRow, u32)>,
}

/// Move replacement terms beneath a region binder for substitution only.
/// The original solver state and its pending proof obligations stay intact.
fn substitution_under_region_binder(value: &ImplementationSubstitution) -> Option<ImplementationSubstitution> {
    let mut shifted = value.clone();
    let shift = |value| crate::types::regions::shift_argument(value, 1);
    for value in shifted.types.values_mut() {
        *value = crate::types::regions::shift_type_argument(value.clone(), 1)?;
    }
    for value in shifted.lifetimes.values_mut() {
        let GenericArgument::Lifetime(lifetime) = shift(GenericArgument::Lifetime(*value))? else { return None; };
        *value = lifetime;
    }
    for value in shifted.generic_arguments.values_mut() {
        *value = shift(value.clone())?;
    }
    for value in shifted.effect_rows.values_mut() {
        let GenericArgument::EffectRow(row) = shift(GenericArgument::EffectRow(value.clone()))? else { return None; };
        *value = row;
    }
    Some(shifted)
}

fn solve_pending_effect_rows(substitution: &mut ImplementationSubstitution) -> Option<()> {
    while !substitution.pending_effect_rows.is_empty() {
        let before = substitution.effect_rows.clone();
        for (template, actual, depth) in std::mem::take(&mut substitution.pending_effect_rows) {
            match_effect_row_at(&template, &actual, substitution, depth)?;
        }
        if !substitution.pending_effect_rows.is_empty() && before == substitution.effect_rows { return None; }
    }
    Some(())
}

/// Defaults belong to the trait declaration, not the selected implementation:
/// their outer binder slots receive the concrete trait arguments and their
/// synthetic `Self` binder receives the solved subject.  Item binders begin
/// immediately after the trait's declaration binders, just as they did during
/// header elaboration.
fn default_associated_item_substitution(
    goal: &TraitGoal,
    trait_generics: u32,
    item_arguments: &[GenericArgument],
) -> ImplementationSubstitution {
    let mut substitution = ImplementationSubstitution::default();
    substitution
        .types
        .insert(TRAIT_SELF_GENERIC, goal.subject.clone());
    for (index, argument) in goal.relation.arguments.iter().enumerate() {
        let index = index as u32;
        install_item_argument(&mut substitution, index, argument.clone());
    }
    for (offset, argument) in item_arguments.iter().cloned().enumerate() {
        install_item_argument(&mut substitution, trait_generics + offset as u32, argument);
    }
    substitution
}

fn generic_arguments_match_kinds(
    arguments: &[GenericArgument],
    kinds: &[crate::GenericKind],
) -> bool {
    arguments.len() == kinds.len()
        && arguments
            .iter()
            .zip(kinds)
            .all(|(argument, kind)| generic_argument_matches_kind(argument, *kind))
}

/// Frozen interfaces may arrive from a dependency rather than this
/// elaborator.  Do not let an implementation-side associated item redefine
/// the declaration's arity, kind, or value/row category merely because its
/// local shape happens to accept the caller's arguments.
fn associated_type_contract_matches(
    trait_header: Option<&ElaboratedTrait>,
    name: &str,
    effect_row: bool,
    item: Option<&crate::ElaboratedAssociatedTypeDefinition>,
) -> bool {
    let (Some(trait_header), Some(item)) = (trait_header, item) else {
        return false;
    };
    let Some(declaration) = trait_header.associated_types.get(name) else {
        return false;
    };
    declaration.effect_row == effect_row
        && declaration.generics == item.generics
        && declaration.generic_kinds == item.generic_kinds
}

fn associated_effect_row_contract_matches(
    trait_header: Option<&ElaboratedTrait>,
    name: &str,
    item: Option<&crate::ElaboratedAssociatedEffectRowDefinition>,
) -> bool {
    let (Some(trait_header), Some(item)) = (trait_header, item) else {
        return false;
    };
    let Some(declaration) = trait_header.associated_types.get(name) else {
        return false;
    };
    declaration.effect_row
        && declaration.generics == item.generics
        && declaration.generic_kinds == item.generic_kinds
}

fn generic_argument_matches_kind(argument: &GenericArgument, kind: crate::GenericKind) -> bool {
    match kind {
        // These are method/GAT substitution slots, not implementation heads.
        // An inference cell retains its kind and cannot prove a prerequisite.
        crate::GenericKind::Const(kind) => crate::types::generic_argument_matches_const_kind(argument, kind),
        crate::GenericKind::Type => matches!(argument, GenericArgument::Type(_)),
        crate::GenericKind::EffectRow => matches!(argument, GenericArgument::EffectRow(_)),
        crate::GenericKind::Lifetime => matches!(argument, GenericArgument::Lifetime(_)),
    }
}

fn install_item_argument(
    substitution: &mut ImplementationSubstitution,
    index: u32,
    argument: GenericArgument,
) {
    match &argument {
        GenericArgument::Type(value) => {
            substitution.types.insert(index, value.clone());
        }
        GenericArgument::Lifetime(value) => {
            substitution.lifetimes.insert(index, *value);
        }
        GenericArgument::EffectRow(value) => {
            substitution.effect_rows.insert(index, value.clone());
            substitution.generic_arguments.insert(index, argument);
        }
        GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstInfer { .. } => {
            substitution.generic_arguments.insert(index, argument);
        }
    }
}

fn match_rule(
    implementation: &ElaboratedImplementation,
    goal: &TraitGoal,
) -> Option<ImplementationSubstitution> {
    if implementation.relation.arguments.len() != goal.relation.arguments.len() {
        return None;
    }
    let mut substitution = ImplementationSubstitution::default();
    match_type(&implementation.self_ty, &goal.subject, &mut substitution)?;
    for (template, actual) in implementation
        .relation
        .arguments
        .iter()
        .zip(&goal.relation.arguments)
    {
        match_generic_argument(template, actual, &mut substitution)?;
    }
    solve_pending_effect_rows(&mut substitution)?;
    Some(substitution)
}

fn match_generic_argument(
    template: &GenericArgument,
    actual: &GenericArgument,
    substitution: &mut ImplementationSubstitution,
) -> Option<()> {
    match_generic_argument_at(template, actual, substitution, 0)
}

fn match_generic_argument_at(
    template: &GenericArgument,
    actual: &GenericArgument,
    substitution: &mut ImplementationSubstitution,
    binder_depth: u32,
) -> Option<()> {
    match (template, actual) {
        (GenericArgument::Type(template), GenericArgument::Type(actual)) => {
            match_type_at(template, actual, substitution, binder_depth)
        }
        (
            GenericArgument::Lifetime(crate::Lifetime::Generic(index)),
            GenericArgument::Lifetime(actual),
        ) => match_lifetime(*index, *actual, substitution, binder_depth),
        (GenericArgument::EffectRow(template), GenericArgument::EffectRow(actual)) => {
            match_effect_row_at(template, actual, substitution, binder_depth)
        }
        (
            GenericArgument::ConstProjection {
                subject: template_subject,
                trait_definition: template_trait,
                trait_arguments: template_arguments,
                name: template_name,
                kind: template_kind,
            },
            GenericArgument::ConstProjection {
                subject: actual_subject,
                trait_definition: actual_trait,
                trait_arguments: actual_arguments,
                name: actual_name,
                kind: actual_kind,
            },
        ) if template_trait == actual_trait
            && template_name == actual_name
            && template_kind == actual_kind
            && template_arguments.len() == actual_arguments.len() =>
        {
            match_type_at(template_subject, actual_subject, substitution, binder_depth)?;
            template_arguments
                .iter()
                .zip(actual_arguments)
                .try_for_each(|(template, actual)| {
                    match_generic_argument_at(template, actual, substitution, binder_depth)
                })
        }
        (GenericArgument::ConstGeneric { index, kind }, actual)
            if generic_argument_is_const_kind(actual, *kind) =>
        {
            match substitution.generic_arguments.get(index) {
                Some(previous) if previous != actual => None,
                Some(_) => Some(()),
                None => {
                    substitution
                        .generic_arguments
                        .insert(*index, actual.clone());
                    Some(())
                }
            }
        }
        _ => (template == actual).then_some(()),
    }
}

/// Match an effect-row argument just as structurally as a type argument.  A
/// row binder is an open tails: after the implementation's fixed prefix has
/// matched, it receives the caller's residual row. This is what makes
/// `impl<e: EffectRow> Trait<e>` applicable to a concrete row and to a row
/// carrying delayed associated-effect projections.
fn match_effect_row_at(
    template: &EffectRow,
    actual: &EffectRow,
    substitution: &mut ImplementationSubstitution,
    binder_depth: u32,
) -> Option<()> {
    let mut unmatched_effects = actual.effects.iter().cloned().collect::<Vec<_>>();
    for expected in &template.effects {
        let mut matched = false;
        for index in 0..unmatched_effects.len() {
            let found = &unmatched_effects[index];
            if expected.definition != found.definition
                || expected.arguments.len() != found.arguments.len()
            {
                continue;
            }
            let mut candidate = substitution.clone();
            if expected
                .arguments
                .iter()
                .zip(&found.arguments)
                .try_for_each(|(expected, found)| {
                    match_generic_argument_at(expected, found, &mut candidate, binder_depth)
                })
                .is_some()
            {
                *substitution = candidate;
                unmatched_effects.remove(index);
                matched = true;
                break;
            }
        }
        if !matched {
            return None;
        }
    }

    let mut unmatched_projections = actual.projections.clone();
    for expected in &template.projections {
        let mut matched = false;
        for index in 0..unmatched_projections.len() {
            let found = &unmatched_projections[index];
            if expected.trait_definition != found.trait_definition
                || expected.name != found.name
                || expected.item_generic_kinds != found.item_generic_kinds
                || expected.trait_arguments.len() != found.trait_arguments.len()
                || expected.item_arguments.len() != found.item_arguments.len()
            {
                continue;
            }
            let mut candidate = substitution.clone();
            if match_type_at(
                &expected.subject,
                &found.subject,
                &mut candidate,
                binder_depth,
            )
            .and_then(|()| {
                expected
                    .trait_arguments
                    .iter()
                    .zip(&found.trait_arguments)
                    .try_for_each(|(expected, found)| {
                        match_generic_argument_at(expected, found, &mut candidate, binder_depth)
                    })
            })
            .and_then(|()| {
                expected
                    .item_arguments
                    .iter()
                    .zip(&found.item_arguments)
                    .try_for_each(|(expected, found)| {
                        match_generic_argument_at(expected, found, &mut candidate, binder_depth)
                    })
            })
            .is_some()
            {
                *substitution = candidate;
                unmatched_projections.remove(index);
                matched = true;
                break;
            }
        }
        if !matched {
            return None;
        }
    }

    let mut known = EffectRow::empty();
    let mut unknown = vec![];
    for tail in &template.tails {
        let crate::EffectTail::Generic(index) = tail else { return None; };
        if let Some(row) = substitution.effect_rows.get(index) {
            known.extend(row.clone());
        } else { unknown.push(*index); }
    }
    // Already-bound rows belong to the goal's binder space. Compare their
    // members as rigid terms instead of interpreting them as new impl slots.
    if !known.effects.is_subset(&actual.effects) || !known.tails.is_subset(&actual.tails)
        || !known.projections.iter().all(|projection| actual.projections.contains(projection)) {
        return None;
    }
    unmatched_effects.retain(|effect| !known.effects.contains(effect));
    unmatched_projections.retain(|projection| !known.projections.contains(projection));
    let residual = EffectRow {
        effects: unmatched_effects.into_iter().collect(), projections: unmatched_projections,
        tails: actual.tails.difference(&known.tails).copied().collect(),
    }.canonicalized();
    match unknown.as_slice() {
        [] => (residual == EffectRow::empty()).then_some(()),
        [index] => {
            if binder_depth > 0 && effect_row_contains_free_hrtb_placeholder(&residual, 0) { return None; }
            substitution.effect_rows.insert(*index, residual.clone());
            substitution.generic_arguments.insert(*index, GenericArgument::EffectRow(residual));
            Some(())
        }
        _ if *actual == EffectRow::empty() => {
            for index in unknown { install_item_argument(substitution, index, GenericArgument::EffectRow(EffectRow::empty())); }
            Some(())
        }
        _ => {
            let equation = (template.clone(), actual.clone(), binder_depth);
            if !substitution.pending_effect_rows.contains(&equation) { substitution.pending_effect_rows.push(equation); }
            Some(())
        }
    }
}

fn generic_argument_is_const_kind(argument: &GenericArgument, expected: crate::ConstKind) -> bool {
    !matches!(argument, GenericArgument::ConstInfer { .. })
        && crate::types::generic_argument_matches_const_kind(argument, expected)
}

fn match_type(
    template: &Type,
    actual: &Type,
    substitution: &mut ImplementationSubstitution,
) -> Option<()> {
    match_type_at(template, actual, substitution, 0)
}

/// Match frozen implementation heads against a goal while tracking the
/// higher-ranked binder depth. Bound regions are rigid placeholders; a type
/// metavariable may not capture one from inside a callable binder, because
/// that substitution would escape when the implementation's where-bounds or
/// associated items are later instantiated.
fn match_type_at(
    template: &Type,
    actual: &Type,
    substitution: &mut ImplementationSubstitution,
    binder_depth: u32,
) -> Option<()> {
    match template {
        Type::Generic(index) => match substitution.types.get(index) {
            Some(previous) if previous != actual => None,
            Some(_) => Some(()),
            None => {
                if binder_depth > 0 && has_free_hrtb_placeholder(actual, 0) {
                    return None;
                }
                substitution.types.insert(*index, actual.clone());
                Some(())
            }
        },
        // Const binders share the declaration's source-slot namespace with
        // type binders, but they range over a deliberately closed structural
        // value language.  Treating them as rigid terms means an otherwise
        // generic implementation such as `impl<n: u32> Ready for Tag<n>` can
        // never match `Tag<4>`.  Bind them just like type variables while
        // retaining their kind check, so ordinary types cannot enter a const
        // substitution by accident.
        Type::ConstGeneric { index, kind } => {
            if !is_const_argument_of_kind(actual, *kind) {
                return None;
            }
            match substitution.types.get(index) {
                Some(previous) if previous != actual => None,
                Some(_) => Some(()),
                None => {
                    substitution.types.insert(*index, actual.clone());
                    Some(())
                }
            }
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstQuantity(_)
        | Type::Error => (template == actual).then_some(()),
        Type::Nominal {
            definition,
            arguments,
        } => match actual {
            Type::Nominal {
                definition: actual_definition,
                arguments: actual_arguments,
            } if definition == actual_definition && arguments.len() == actual_arguments.len() => {
                arguments
                    .iter()
                    .zip(actual_arguments)
                    .try_for_each(|(template, actual)| {
                        match_generic_argument_at(template, actual, substitution, binder_depth)
                    })
            }
            _ => None,
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => match actual {
            Type::Projection {
                subject: actual_subject,
                trait_definition: actual_trait_definition,
                trait_arguments: actual_trait_arguments,
                name: actual_name,
                item_generic_kinds: actual_item_generic_kinds,
                item_arguments: actual_item_arguments,
            } if trait_definition == actual_trait_definition
                && name == actual_name
                && item_generic_kinds == actual_item_generic_kinds
                && trait_arguments.len() == actual_trait_arguments.len()
                && item_arguments.len() == actual_item_arguments.len() =>
            {
                match_type_at(subject, actual_subject, substitution, binder_depth)?;
                trait_arguments
                    .iter()
                    .zip(actual_trait_arguments)
                    .try_for_each(|(template, actual)| {
                        match_generic_argument_at(template, actual, substitution, binder_depth)
                    })?;
                item_arguments
                    .iter()
                    .zip(actual_item_arguments)
                    .try_for_each(|(template, actual)| {
                        match_generic_argument_at(template, actual, substitution, binder_depth)
                    })
            }
            _ => None,
        },
        Type::Tuple(values) => match actual {
            Type::Tuple(actual_values) if values.len() == actual_values.len() => values
                .iter()
                .zip(actual_values)
                .try_for_each(|(template, actual)| {
                    match_type_at(template, actual, substitution, binder_depth)
                }),
            _ => None,
        },
        Type::FixedArray { element, length } => match actual {
            Type::FixedArray { element: actual_element, length: actual_length } => {
                match_type_at(element, actual_element, substitution, binder_depth)?;
                match_generic_argument_at(length, actual_length, substitution, binder_depth)
            }
            _ => None,
        },
        Type::Array(element) => match actual {
            Type::Array(actual_element) => {
                match_type_at(element, actual_element, substitution, binder_depth)
            }
            _ => None,
        },
        Type::RawPointer { mutability, pointee } => match actual {
            Type::RawPointer { mutability: actual_mutability, pointee: actual_pointee }
                if mutability == actual_mutability => {
                    match_type_at(pointee, actual_pointee, substitution, binder_depth)
                }
            _ => None,
        },
        Type::StaticData {
            element,
            tag,
            alignment,
        } => match actual {
            Type::StaticData {
                element: actual_element,
                tag: actual_tag,
                alignment: actual_alignment,
            } if tag == actual_tag && alignment == actual_alignment => {
                match_type_at(element, actual_element, substitution, binder_depth)
            }
            _ => None,
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => match actual {
            Type::Reference {
                mutability: actual_mutability,
                lifetime: actual_lifetime,
                referent: actual_referent,
            } if mutability == actual_mutability => {
                match lifetime {
                    crate::Lifetime::Generic(index) => {
                        match_lifetime(*index, *actual_lifetime, substitution, binder_depth)?;
                    }
                    expected if expected == actual_lifetime => {}
                    _ => return None,
                }
                match_type_at(referent, actual_referent, substitution, binder_depth)
            }
            _ => None,
        },
        Type::Callable { contract: template_contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => match actual {
            Type::Callable { contract: actual_contract,
                safety: actual_safety,
                lifetime_binders: actual_lifetime_binders,
                parameters: actual_parameters,
                result: actual_result,
                effects: actual_effects,
                invocation: actual_invocation,
            } if safety == actual_safety && lifetime_binders == actual_lifetime_binders
                && parameters.len() == actual_parameters.len()
                && invocation == actual_invocation
                && (template_contract.is_empty() || template_contract == actual_contract) =>
            {
                parameters
                    .iter()
                    .zip(actual_parameters)
                    .try_for_each(|(template, actual)| {
                        match_type_at(template, actual, substitution, binder_depth + 1)
                    })?;
                match_type_at(result, actual_result, substitution, binder_depth + 1)?;
                match_effect_row_at(effects, actual_effects, substitution, binder_depth + 1)
            }
            _ => None,
        },
        // A caller-owned inference variable is intentionally not solved by
        // this frozen-interface kernel.  Body elaboration must choose a type
        // first, then issue a canonical trait goal.
        Type::Infer(_) => None,
    }
}

fn trait_goal_contains_escaping_hrtb(goal: &TraitGoal) -> bool {
    has_free_hrtb_placeholder(&goal.subject, 0)
        || goal
            .relation
            .arguments
            .iter()
            .any(generic_argument_contains_escaping_hrtb)
}

fn generic_argument_contains_escaping_hrtb(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => has_free_hrtb_placeholder(value, 0),
        GenericArgument::EffectRow(row) => effect_row_contains_free_hrtb_placeholder(row, 0),
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            has_free_hrtb_placeholder(subject, 0)
                || trait_arguments
                    .iter()
                    .any(generic_argument_contains_escaping_hrtb)
        }
        GenericArgument::Lifetime(crate::Lifetime::Bound { .. } | crate::Lifetime::Placeholder(_)) => true,
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

/// A `Bound` lifetime is a fresh universe placeholder unless it is closed by
/// a callable nested inside the candidate type. This walk distinguishes a
/// self-contained nested HRTB from a reference to an enclosing binder, and
/// intentionally reaches every generic-argument and effect-row carrier.
fn has_free_hrtb_placeholder(value: &Type, callable_nesting: u32) -> bool {
    match value {
        Type::FixedArray { element, length } => has_free_hrtb_placeholder(element, callable_nesting)
            || generic_argument_contains_free_hrtb_placeholder(length, callable_nesting),
        Type::Reference { lifetime: crate::Lifetime::Placeholder(_), .. } => true,
        Type::Reference {
            lifetime: crate::Lifetime::Bound { depth, .. },
            referent,
            ..
        } => *depth >= callable_nesting || has_free_hrtb_placeholder(referent, callable_nesting),
        Type::Reference { referent, .. } | Type::Array(referent)
        | Type::RawPointer { pointee: referent, .. } => {
            has_free_hrtb_placeholder(referent, callable_nesting)
        }
        Type::Nominal { arguments, .. } => arguments.iter().any(|argument| {
            generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
        }),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            has_free_hrtb_placeholder(subject, callable_nesting)
                || trait_arguments.iter().any(|value| {
                    generic_argument_contains_free_hrtb_placeholder(value, callable_nesting)
                })
                || item_arguments.iter().any(|value| {
                    generic_argument_contains_free_hrtb_placeholder(value, callable_nesting)
                })
        }
        Type::Tuple(values) => values
            .iter()
            .any(|value| has_free_hrtb_placeholder(value, callable_nesting)),
        Type::Callable {
            contract,
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|value| has_free_hrtb_placeholder(value, callable_nesting + 1))
                || has_free_hrtb_placeholder(result, callable_nesting + 1)
                || effect_row_contains_free_hrtb_placeholder(effects, callable_nesting + 1)
                || contract.terms().iter().any(|(value, extra)| generic_argument_contains_free_hrtb_placeholder(value, callable_nesting + 1 + extra))
        }
        _ => false,
    }
}

fn generic_argument_contains_free_hrtb_placeholder(
    value: &GenericArgument,
    callable_nesting: u32,
) -> bool {
    match value {
        GenericArgument::Type(value) => has_free_hrtb_placeholder(value, callable_nesting),
        GenericArgument::EffectRow(row) => {
            effect_row_contains_free_hrtb_placeholder(row, callable_nesting)
        }
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            has_free_hrtb_placeholder(subject, callable_nesting)
                || trait_arguments.iter().any(|argument| {
                    generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
                })
        }
        GenericArgument::Lifetime(crate::Lifetime::Placeholder(_)) => true,
        GenericArgument::Lifetime(crate::Lifetime::Bound { depth, .. }) => {
            *depth >= callable_nesting
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn effect_row_contains_free_hrtb_placeholder(value: &EffectRow, callable_nesting: u32) -> bool {
    value.effects.iter().any(|effect| {
        effect.arguments.iter().any(|argument| {
            generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
        })
    }) || value.projections.iter().any(|projection| {
        has_free_hrtb_placeholder(&projection.subject, callable_nesting)
            || projection.trait_arguments.iter().any(|argument| {
                generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
            })
            || projection.item_arguments.iter().any(|argument| {
                generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
            })
    })
}

fn match_lifetime(
    index: u32,
    actual: crate::Lifetime,
    substitution: &mut ImplementationSubstitution,
    binder_depth: u32,
) -> Option<()> {
    // An implementation lifetime cannot be bound to a placeholder introduced
    // by an inner `for<'a>` callable: the implementation substitution outlives
    // that callable and would otherwise capture its local universe.
    if binder_depth > 0 && matches!(actual, crate::Lifetime::Bound { .. }) {
        return None;
    }
    match substitution.lifetimes.get(&index) {
        Some(previous) if *previous != actual => None,
        Some(_) => Some(()),
        None => {
            substitution.lifetimes.insert(index, actual);
            Some(())
        }
    }
}

/// Check that a solver-side substitution remains in the structural domain of
/// its declared const binder.  Generic consts are valid actual terms because
/// a canonical goal may itself be parameterized; their kind must still agree.
fn is_const_argument_of_kind(value: &Type, expected: crate::ConstKind) -> bool {
    match value {
        Type::ConstInteger(value) => value.kind() == expected,
        Type::ConstQuantity(_) => expected == crate::ConstKind::Quantity,
        Type::ConstGeneric { kind, .. } => *kind == expected,
        _ => false,
    }
}

fn substitute_relation(
    relation: &ElaboratedTraitReference,
    substitution: &ImplementationSubstitution,
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .map(|argument| substitute_generic_argument(argument, substitution))
            .collect(),
    }
}

fn substitute_generic_argument(
    argument: &GenericArgument,
    substitution: &ImplementationSubstitution,
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => GenericArgument::Type(substitute_type(value, substitution)),
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(substitute_effect_row(value, substitution))
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(substitute_type(subject, substitution)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|argument| substitute_generic_argument(argument, substitution))
                .collect(),
            name: name.clone(),
            kind: *kind,
        },
        GenericArgument::ConstGeneric { index, kind } => substitution
            .generic_arguments
            .get(index)
            // Substitution preserves kind, not head-selection rigidity. GAT
            // and method slots can still contain caller-owned const cells.
            .filter(|argument| crate::types::generic_argument_matches_const_kind(argument, *kind))
            .cloned()
            .unwrap_or_else(|| argument.clone()),
        GenericArgument::ConstIntegerExpr(value) => {
            crate::types::integer_const_argument(substitute_structural_integer_expr(value, substitution))
        }
        GenericArgument::Lifetime(crate::Lifetime::Generic(index)) => GenericArgument::Lifetime(
            substitution
                .lifetimes
                .get(index)
                .copied()
                .unwrap_or(crate::Lifetime::Generic(*index)),
        ),
        argument => argument.clone(),
    }
}

fn substitute_structural_integer_expr(
    value: &crate::IntegerConstExpr,
    substitution: &ImplementationSubstitution,
) -> Result<crate::IntegerConstExpr, crate::types::StructuralConstError> {
    value.substitute_with(&|index| substitution.generic_arguments.get(&index)
        .map(crate::IntegerConstExpr::from_argument).transpose(), 64, &mut 1024)
}

fn substitute_type(value: &Type, substitution: &ImplementationSubstitution) -> Type {
    match value {
        Type::Generic(index) => substitution
            .types
            .get(index)
            .cloned()
            .unwrap_or_else(|| value.clone()),
        Type::ConstGeneric { index, kind } => substitution
            .types
            .get(index)
            .cloned()
            .or_else(|| {
                substitution
                    .generic_arguments
                    .get(index)
                    .and_then(|argument| match (argument, kind) {
                        (GenericArgument::ConstInteger(value), expected) if value.kind() == *expected => {
                            Some(Type::ConstInteger(*value))
                        }
                        (GenericArgument::ConstQuantity(value), crate::ConstKind::Quantity) => {
                            Some(Type::ConstQuantity(*value))
                        }
                        (GenericArgument::ConstGeneric { index, kind: found }, expected)
                            if found == expected =>
                        {
                            Some(Type::ConstGeneric {
                                index: *index,
                                kind: *found,
                            })
                        }
                        _ => None,
                    })
            })
            .unwrap_or_else(|| value.clone()),
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|value| substitute_generic_argument(value, substitution))
                .collect(),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(substitute_type(subject, substitution)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|value| substitute_generic_argument(value, substitution))
                .collect(),
            name: name.clone(),
            item_generic_kinds: item_generic_kinds.clone(),
            item_arguments: item_arguments
                .iter()
                .map(|value| substitute_generic_argument(value, substitution))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .iter()
                .map(|value| substitute_type(value, substitution))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(substitute_type(value, substitution))),
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(substitute_type(element, substitution)),
            length: Box::new(substitute_generic_argument(length, substitution)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability: *mutability,
            pointee: Box::new(substitute_type(pointee, substitution)),
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: match lifetime {
                crate::Lifetime::Generic(index) => substitution
                    .lifetimes
                    .get(index)
                    .copied()
                    .unwrap_or(*lifetime),
                lifetime => *lifetime,
            },
            referent: Box::new(substitute_type(referent, substitution)),
        },
        Type::Callable { contract,
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => {
            let Some(substitution) = substitution_under_region_binder(substitution) else { return Type::Error; };
            Type::Callable { contract: Box::new(contract.map_terms(|value, extra| {
                if extra == 0 { return substitute_generic_argument(&value, &substitution); }
                let Some(substitution) = substitution_under_region_binder(&substitution)
                    else { return GenericArgument::Type(Type::Error); };
                substitute_generic_argument(&value, &substitution)
            })),
                safety: *safety,
                lifetime_binders: *lifetime_binders,
                parameters: parameters.iter().map(|value| substitute_type(value, &substitution)).collect(),
                result: Box::new(substitute_type(result, &substitution)),
                effects: substitute_effect_row(effects, &substitution),
                invocation: *invocation,
            }
        },
        _ => value.clone(),
    }
}

fn substitute_effect_row(
    value: &EffectRow,
    substitution: &ImplementationSubstitution,
) -> EffectRow {
    let mut result = EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| substitute_generic_argument(argument, substitution))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .iter()
            .map(|projection| crate::EffectRowProjection {
                subject: Box::new(substitute_type(&projection.subject, substitution)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .iter()
                    .map(|value| substitute_generic_argument(value, substitution))
                    .collect(),
                name: projection.name.clone(),
                item_generic_kinds: projection.item_generic_kinds.clone(),
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|value| substitute_generic_argument(value, substitution))
                    .collect(),
            })
            .collect(),
        tails: value.tails.clone(),
    };
    // A row variable denotes the complete residual row, not only its tail.
    // In particular, substituting `e` in `{ Prefix, | e }` must retain both
    // the caller's fixed effects/projections and its open tail.  The old
    // pure-row fast path left `e` stale whenever it followed a prefix,
    // causing defaulted and specialized associated rows to normalize to a
    // declaration-local generic instead of the selected application.
    result.substitute_tails(|tail| match tail {
        crate::EffectTail::Generic(index) => substitution.effect_rows.get(&index).cloned(),
        _ => None,
    });
    result.canonicalized()
}

fn substitute_callable_signature(
    value: &CallableSignature,
    substitution: &ImplementationSubstitution,
) -> CallableSignature {
    CallableSignature {
        safety: value.safety,
        generics: 0,
        generic_kinds: vec![],
        parameters: value
            .parameters
            .iter()
            .map(|parameter| substitute_type(parameter, substitution))
            .collect(),
        result: substitute_type(&value.result, substitution),
        effects: substitute_effect_row(&value.effects, substitution),
        invocation: value.invocation,
        where_bounds: value
            .where_bounds
            .iter()
            .map(|(subject, relation)| {
                (
                    substitute_type(subject, substitution),
                    substitute_relation(relation, substitution),
                )
            })
            .collect(),
        where_associated_type_bindings: value
            .where_associated_type_bindings
            .iter()
            .cloned()
            .map(|binding| crate::ElaboratedAssociatedTypeBinding {
                subject: substitute_type(&binding.subject, substitution),
                relation: substitute_relation(&binding.relation, substitution),
                name: binding.name,
                item_generic_kinds: binding.item_generic_kinds,
                item_arguments: binding
                    .item_arguments
                    .iter()
                    .map(|argument| substitute_generic_argument(argument, substitution))
                    .collect(),
                value: substitute_type(&binding.value, substitution),
            })
            .collect(),
        where_associated_effect_bindings: value
            .where_associated_effect_bindings
            .iter()
            .cloned()
            .map(|binding| crate::ElaboratedAssociatedEffectBinding {
                subject: substitute_type(&binding.subject, substitution),
                relation: substitute_relation(&binding.relation, substitution),
                name: binding.name,
                item_generic_kinds: binding.item_generic_kinds,
                item_arguments: binding
                    .item_arguments
                    .iter()
                    .map(|argument| substitute_generic_argument(argument, substitution))
                    .collect(),
                value: substitute_effect_row(&binding.value, substitution),
            })
            .collect(),
        where_outlives: value.where_outlives.iter().map(|bound| bound.map_terms(|argument|
            substitute_generic_argument(&argument, substitution))).collect(),
        universal_bounds: value.universal_bounds.iter().map(|bound| {
            // Substitution values are outside the quantified predicate's
            // region scope. Move their free regions before inserting them.
            let Some(shifted) = substitution_under_region_binder(substitution) else {
                return crate::QuantifiedWhereBound { subject: Type::Error, ..bound.clone() };
            };
            bound.map_terms(|argument| substitute_generic_argument(&argument, &shifted))
        }).collect(),
    }
}

fn goal_key(goal: &TraitGoal) -> Digest {
    let relation_arguments = canonical_generic_arguments_encoding(&goal.relation.arguments);
    let subject = canonical_type_encoding(&goal.subject);
    Digest::of_parts([
        b"grandiose-stage0-trait-goal-v2".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        relation_arguments.as_slice(),
        subject.as_slice(),
    ])
}

#[cfg(test)]
mod quantified_substitution_tests {
    use super::*;

    #[test]
    fn quantified_evidence_is_lexical_rigid_kind_preserving_and_budgeted() {
        let reference = |lifetime, referent| Type::Reference {
            mutability: crate::Mutability::Shared, lifetime, referent: Box::new(referent),
        };
        let row = |index| GenericArgument::EffectRow(EffectRow {
            effects: Default::default(), projections: vec![],
            tails: [crate::EffectTail::Generic(index)].into_iter().collect(),
        });
        let bound = crate::QuantifiedWhereBound {
            lifetime_binders: 1,
            subject: reference(crate::Lifetime::Bound { depth: 0, index: 0 }, Type::Generic(0)),
            relation: ElaboratedTraitReference { definition: DefKey(Digest::of_bytes(b"universal-user-trait")), arguments: vec![row(1)] },
            type_bindings: vec![], effect_bindings: vec![],
        };
        let goal = TraitGoal { subject: reference(crate::Lifetime::Static, Type::Generic(0)), relation: bound.relation.clone() };
        let mut solver = TraitSolver::new(&ElaboratedInterface::default());
        solver.set_universal_assumptions(vec![bound.clone()]);
        assert!(solver.proves_universal(&bound));
        assert!(matches!(solver.solve(goal.clone()), TraitAnswer::Proven { .. }));
        let mut different_type = goal.clone();
        different_type.subject = reference(crate::Lifetime::Static, Type::Generic(1));
        assert_eq!(solver.solve(different_type), TraitAnswer::NoSolution);
        let mut different_row = goal.clone();
        different_row.relation.arguments = vec![row(2)];
        assert_eq!(solver.solve(different_row), TraitAnswer::NoSolution);
        let mut inference = crate::InferContext::default();
        let unknown = TraitGoal { subject: inference.fresh(), relation: bound.relation.clone() };
        assert!(bound.for_goal(&unknown).is_none(), "foreign inference cells cannot be bound by lexical elimination");
        solver.set_universal_assumptions(vec![]);
        assert_eq!(solver.solve(goal), TraitAnswer::NoSolution, "a prior query cannot leak universal evidence");
        solver.set_universal_assumptions(vec![bound.clone()]);
        solver.limits.max_steps = 1;
        assert!(!solver.proves_universal(&bound));
        assert_eq!(solver.steps, 1);
        assert!(!solver.proves_universal(&bound));
    }

    #[test]
    fn selected_callable_substitution_preserves_quantified_and_nested_scopes() {
        let reference = |depth| Type::Reference {
            mutability: crate::Mutability::Shared,
            lifetime: crate::Lifetime::Bound { depth, index: 7 },
            referent: Box::new(Type::Unit),
        };
        let nested = Type::Callable { contract: Default::default(),
            safety: crate::Safety::Safe, lifetime_binders: 1,
            parameters: vec![Type::Generic(0)], result: Box::new(Type::Unit),
            effects: EffectRow::empty(), invocation: crate::Quantity::ONCE,
        };
        let signature = CallableSignature {
            safety: crate::Safety::Safe, generics: 1, generic_kinds: vec![crate::GenericKind::Type],
            parameters: vec![], result: Type::Unit, effects: EffectRow::empty(), invocation: crate::Quantity::ONCE,
            where_bounds: vec![], where_outlives: vec![], where_associated_type_bindings: vec![], where_associated_effect_bindings: vec![],
            universal_bounds: vec![crate::QuantifiedWhereBound {
                lifetime_binders: 1, subject: Type::Generic(0),
                relation: ElaboratedTraitReference {
                    definition: crate::intrinsic_callable_trait_definition(),
                    arguments: vec![GenericArgument::Type(Type::Tuple(vec![nested]))],
                },
                type_bindings: vec![], effect_bindings: vec![],
            }],
        };
        let mut substitution = ImplementationSubstitution::default();
        substitution.types.insert(0, reference(0));
        let selected = substitute_callable_signature(&signature, &substitution);
        let bound = &selected.universal_bounds[0];
        assert_eq!(bound.subject, reference(1));
        let GenericArgument::Type(Type::Tuple(inputs)) = &bound.relation.arguments[0] else { panic!("tuple") };
        let Type::Callable { parameters, .. } = &inputs[0] else { panic!("callable") };
        assert_eq!(parameters, &[reference(2)]);
        assert_eq!(substitution.types[&0], reference(0), "checking must not mutate caller substitutions");
    }
}

/// Lexical where-clause evidence has no declaration key of its own. Derive a
/// stable proof identity from the frozen goal instead of borrowing an
/// implementation identity (which would falsely suggest global selection).
fn assumption_evidence(goal: &TraitGoal) -> DefKey {
    let key = goal_key(goal);
    DefKey(Digest::of_parts([
        b"grandiose-stage0-trait-assumption-evidence-v1".as_slice(),
        key.as_bytes().as_slice(),
    ]))
}

fn associated_projection_key(
    goal: &TraitGoal,
    name: &str,
    arguments: &[GenericArgument],
) -> Digest {
    let relation_arguments = canonical_generic_arguments_encoding(&goal.relation.arguments);
    let subject = canonical_type_encoding(&goal.subject);
    let arguments = canonical_generic_arguments_encoding(arguments);
    Digest::of_parts([
        b"grandiose-stage0-associated-projection-v2".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        relation_arguments.as_slice(),
        subject.as_slice(),
        name.as_bytes(),
        arguments.as_slice(),
    ])
}

fn associated_effect_row_projection_key(
    goal: &TraitGoal,
    name: &str,
    arguments: &[GenericArgument],
) -> Digest {
    let relation_arguments = canonical_generic_arguments_encoding(&goal.relation.arguments);
    let subject = canonical_type_encoding(&goal.subject);
    let arguments = canonical_generic_arguments_encoding(arguments);
    Digest::of_parts([
        b"grandiose-stage0-associated-effect-row-projection-v2".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        relation_arguments.as_slice(),
        subject.as_slice(),
        name.as_bytes(),
        arguments.as_slice(),
    ])
}

fn associated_const_projection_key(goal: &TraitGoal, name: &str, kind: crate::ConstKind) -> Digest {
    let relation_arguments = canonical_generic_arguments_encoding(&goal.relation.arguments);
    let subject = canonical_type_encoding(&goal.subject);
    let kind = match kind {
        crate::ConstKind::U32 => b"u32".as_slice(),
        crate::ConstKind::Quantity => b"quantity".as_slice(),
        kind => kind.name().as_bytes(),
    };
    Digest::of_parts([
        b"grandiose-stage0-associated-const-projection-v1".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        relation_arguments.as_slice(),
        subject.as_slice(),
        name.as_bytes(),
        kind,
    ])
}

/// Eligibility is not evidence: this only excludes unknown heads before the
/// ordinary selector proves the implementation and associated-item domain.
/// Bare generic subjects remain lexical abstractions; structural heads may
/// contain rigid declaration parameters, never unresolved inference cells.
/// Item arguments do not select an implementation: their inference cells may
/// be substituted into its result, but never prove its declared domain.
#[derive(Clone, Copy)]
enum ProjectionPosition { Head, Item }

impl ProjectionPosition {
    fn permits_inference(self) -> bool { matches!(self, Self::Item) }
}

fn projection_application_is_selectable(
    subject: &Type,
    trait_definition: DefKey,
    trait_arguments: &[GenericArgument],
    item_arguments: &[GenericArgument],
    binders: &[u32],
) -> bool {
    let relation = ElaboratedTraitReference { definition: trait_definition, arguments: vec![] };
    let value = match subject { Type::Reference { referent, .. } => referent.as_ref(), value => value };
    if (is_intrinsic_callable_trait(&relation) || is_intrinsic_runs_in_trait(&relation))
        && matches!(value, Type::Callable { .. }) {
        // The sealed call relation selects a known callable shape, not an
        // overlapping implementation head. Its Output/Effects can themselves
        // retain lexical projections. Actual receiver and prerequisite proof
        // still belongs to callable_evidence in the ordinary selector.
        return !crate::core::type_contains_inference(subject)
            && trait_arguments.iter().all(|argument| !crate::core::generic_argument_contains_inference(argument))
            && item_arguments.iter().all(|argument| projection_argument_is_known(argument, binders, ProjectionPosition::Item));
    }
    !matches!(subject, Type::Generic(_) | Type::Projection { .. })
        && projection_type_is_known(subject, binders, ProjectionPosition::Head)
        && trait_arguments.iter().all(|argument| projection_argument_is_known(argument, binders, ProjectionPosition::Head))
        && item_arguments.iter().all(|argument|
            projection_argument_is_known(argument, binders, ProjectionPosition::Item))
}

fn projection_argument_is_known(value: &GenericArgument, binders: &[u32], position: ProjectionPosition) -> bool {
    match value {
        GenericArgument::Type(value) => projection_type_is_known(value, binders, position),
        GenericArgument::EffectRow(value) => projection_row_is_known(value, binders, position),
        GenericArgument::Lifetime(Lifetime::Static | Lifetime::Elided | Lifetime::Generic(_) | Lifetime::Inferred(_))
        | GenericArgument::ConstInteger(_) | GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstQuantity(_) | GenericArgument::ConstGeneric { .. } => true,
        GenericArgument::Lifetime(Lifetime::Bound { depth, index }) =>
            binders.get(*depth as usize).is_some_and(|count| *index < *count),
        GenericArgument::Lifetime(Lifetime::Infer(_)) | GenericArgument::ConstInfer { .. } => position.permits_inference(),
        GenericArgument::Lifetime(Lifetime::Placeholder(_)) | GenericArgument::ConstProjection { .. } => false,
    }
}

fn projection_row_is_known(value: &EffectRow, binders: &[u32], position: ProjectionPosition) -> bool {
    value.projections.is_empty()
        && value.tails.iter().all(|tail| matches!(tail, crate::EffectTail::Generic(_)) || position.permits_inference() && matches!(tail, crate::EffectTail::Infer(_)))
        && value.effects.iter().all(|effect| effect.arguments.iter()
            .all(|argument| projection_argument_is_known(argument, binders, position)))
}

fn projection_type_is_known(value: &Type, binders: &[u32], position: ProjectionPosition) -> bool {
    match value {
        Type::Infer(_) => position.permits_inference(),
        Type::Error | Type::Projection { .. } => false,
        Type::Nominal { arguments, .. } => arguments.iter()
            .all(|argument| projection_argument_is_known(argument, binders, position)),
        Type::Tuple(values) => values.iter().all(|value| projection_type_is_known(value, binders, position)),
        Type::FixedArray { element, length } => projection_type_is_known(element, binders, position)
            && projection_argument_is_known(length, binders, position),
        Type::Array(element) | Type::StaticData { element, .. }
        | Type::RawPointer { pointee: element, .. } => projection_type_is_known(element, binders, position),
        Type::Reference { lifetime, referent, .. } =>
            projection_argument_is_known(&GenericArgument::Lifetime(*lifetime), binders, position)
                && projection_type_is_known(referent, binders, position),
        Type::Callable { contract, lifetime_binders, parameters, result, effects, .. } => {
            let mut nested = vec![*lifetime_binders];
            nested.extend_from_slice(binders);
            let mut rigid = true;
            contract.map_scoped_terms(|value, scopes| {
                let mut scopes = scopes.to_vec();
                scopes.extend_from_slice(&nested);
                rigid &= projection_argument_is_known(&value, &scopes, position);
                value
            });
            rigid && parameters.iter().all(|value| projection_type_is_known(value, &nested, position))
                && projection_type_is_known(result, &nested, position)
                && projection_row_is_known(effects, &nested, position)
        }
        Type::Generic(_) | Type::ConstGeneric { .. } | Type::Unit | Type::Never
        | Type::Scalar(_) | Type::ConstInteger(_) | Type::ConstQuantity(_) => true,
    }
}

fn projection_is_concrete(value: &Type) -> bool {
    match value {
        Type::FixedArray { element, length } => projection_is_concrete(element) && generic_argument_is_concrete(length),
        Type::Generic(_) | Type::Infer(_) | Type::Error => false,
        Type::Nominal { arguments, .. } => arguments.iter().all(generic_argument_is_concrete),
        Type::Tuple(arguments) => arguments.iter().all(projection_is_concrete),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            projection_is_concrete(subject)
                && trait_arguments.iter().all(generic_argument_is_concrete)
                && item_arguments.iter().all(generic_argument_is_concrete)
        }
        Type::Array(element) | Type::StaticData { element, .. } => {
            projection_is_concrete(element)
        }
        Type::Reference { referent, .. }
        | Type::RawPointer { pointee: referent, .. } => projection_is_concrete(referent),
        Type::Callable {
            contract, parameters, result, ..
        } => parameters.iter().all(projection_is_concrete) && projection_is_concrete(result)
            && contract.terms().iter().all(|(value, _)| generic_argument_is_concrete(value)),
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. } => true,
    }
}

/// The callable-owned counterpart to `projection_is_concrete`. Bound
/// lifetimes become rigid, selectable item arguments only when their De
/// Bruijn depth names a live callable binder in this traversal.
fn projection_is_concrete_in_hrtb_scope(value: &Type, hrtb_binders: &[u32]) -> bool {
    match value {
        Type::FixedArray { element, length } => projection_is_concrete_in_hrtb_scope(element, hrtb_binders)
            && generic_argument_is_concrete_in_hrtb_scope(length, hrtb_binders),
        Type::Generic(_) | Type::Infer(_) | Type::Error => false,
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .all(|argument| generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders)),
        Type::Tuple(arguments) => arguments
            .iter()
            .all(|argument| projection_is_concrete_in_hrtb_scope(argument, hrtb_binders)),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            projection_is_concrete_in_hrtb_scope(subject, hrtb_binders)
                && trait_arguments.iter().all(|argument| {
                    generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders)
                })
                && item_arguments.iter().all(|argument| {
                    generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders)
                })
        }
        Type::Array(element) | Type::StaticData { element, .. } => {
            projection_is_concrete_in_hrtb_scope(element, hrtb_binders)
        }
        Type::Reference { lifetime, referent, .. } => {
            generic_argument_is_concrete_in_hrtb_scope(&GenericArgument::Lifetime(*lifetime), hrtb_binders)
                && projection_is_concrete_in_hrtb_scope(referent, hrtb_binders)
        }
        Type::RawPointer { pointee: referent, .. } => {
            projection_is_concrete_in_hrtb_scope(referent, hrtb_binders)
        }
        Type::Callable {
            contract,
            lifetime_binders,
            parameters,
            result,
            effects, ..
        } => {
            let mut nested_binders = Vec::with_capacity(hrtb_binders.len() + 1);
            nested_binders.push(*lifetime_binders);
            nested_binders.extend_from_slice(hrtb_binders);
            let mut concrete = true;
            contract.map_scoped_terms(|value, scopes| {
                let mut scopes = scopes.to_vec();
                scopes.extend_from_slice(&nested_binders);
                concrete &= generic_argument_is_concrete_in_hrtb_scope(&value, &scopes);
                value
            });
            concrete && parameters
                .iter()
                .all(|parameter| projection_is_concrete_in_hrtb_scope(parameter, &nested_binders))
                && projection_is_concrete_in_hrtb_scope(result, &nested_binders)
                && effects.tails.is_empty() && effects.projections.is_empty()
                && effects.effects.iter().all(|effect| effect.arguments.iter()
                    .all(|argument| generic_argument_is_concrete_in_hrtb_scope(argument, &nested_binders)))
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. } => true,
    }
}

fn generic_argument_is_concrete(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => projection_is_concrete(value),
        GenericArgument::EffectRow(value) => {
            value.tails.is_empty()
                && value.projections.is_empty()
                && value
                    .effects
                    .iter()
                    .all(|effect| effect.arguments.iter().all(generic_argument_is_concrete))
        }
        GenericArgument::Lifetime(crate::Lifetime::Static | crate::Lifetime::Elided | crate::Lifetime::Inferred(_))
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::ConstIntegerExpr(_) => false,
        GenericArgument::ConstProjection { .. } => false,
        GenericArgument::Lifetime(crate::Lifetime::Generic(_) | crate::Lifetime::Bound { .. } | crate::Lifetime::Infer(_) | crate::Lifetime::Placeholder(_))
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn principal_goal_is_open(goal: &TraitGoal) -> bool {
    !projection_is_concrete(&goal.subject)
        || !goal.relation.arguments.iter().all(generic_argument_is_concrete)
}

fn generic_argument_is_concrete_in_hrtb_scope(
    value: &GenericArgument,
    hrtb_binders: &[u32],
) -> bool {
    match value {
        GenericArgument::Type(value) => projection_is_concrete_in_hrtb_scope(value, hrtb_binders),
        GenericArgument::EffectRow(value) => {
            value.tails.is_empty()
                && value.projections.is_empty()
                && value.effects.iter().all(|effect| {
                    effect.arguments.iter().all(|argument| {
                        generic_argument_is_concrete_in_hrtb_scope(argument, hrtb_binders)
                    })
                })
        }
        GenericArgument::Lifetime(crate::Lifetime::Bound { depth, index }) => hrtb_binders
            .get(*depth as usize)
            .is_some_and(|count| *index < *count),
        GenericArgument::Lifetime(crate::Lifetime::Static | crate::Lifetime::Elided | crate::Lifetime::Inferred(_))
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::ConstIntegerExpr(_)
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::Lifetime(crate::Lifetime::Generic(_) | crate::Lifetime::Infer(_) | crate::Lifetime::Placeholder(_))
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ScalarType;

    #[test]
    fn resident_use_distinguishes_capture_ownership_from_declared_invocation() {
        use crate::{Mutability, Quantity};
        let solver = TraitSolver::new(&ElaboratedInterface::default());
        let callable = |captures: Option<Vec<Type>>, invocation| {
            let mut contract = crate::CallableContract::default();
            if let Some(captures) = captures {
                contract.environment = Some(Box::new(Type::Nominal {
                    definition: DefKey(Digest::of_bytes(b"quantity-test-environment")), arguments: vec![],
                }));
                contract.captures = captures;
            }
            Type::Callable { contract: Box::new(contract), safety: crate::Safety::Safe,
                lifetime_binders: 0, parameters: vec![], result: Box::new(Type::Unit),
                effects: EffectRow::empty(), invocation }
        };
        for (capture, expected) in [
            (Type::Scalar(ScalarType::I64), Some(Quantity::UNRESTRICTED)),
            (Type::Reference { lifetime: Lifetime::Static, mutability: Mutability::Unique, referent: Box::new(Type::Unit) }, Some(Quantity::AFFINE)),
            (Type::Reference { lifetime: Lifetime::Static, mutability: Mutability::Shared, referent: Box::new(Type::Generic(0)) }, Some(Quantity::UNRESTRICTED)),
            (Type::Generic(0), None),
        ] {
            let resident = callable(Some(vec![capture]), Quantity::ONCE);
            assert_eq!(solver.principal_use_with_assumptions(&resident, &[]), Some(Quantity::ONCE));
            assert_eq!(solver.resident_use(&resident), expected);
            let nested = callable(Some(vec![Type::Tuple(vec![resident])]), Quantity::ONCE);
            assert_eq!(solver.resident_use(&nested), expected);
        }
        for quantity in [Quantity::ONCE, Quantity::AFFINE, Quantity::new(3, Some(3)).unwrap()] {
            assert_eq!(solver.resident_use(&callable(None, quantity)), Some(quantity),
                "erased and resumption contracts cannot acquire Copy from an empty capture list");
        }
    }

    #[test]
    fn intrinsic_callable_projections_keep_symbolic_results_and_receiver_prerequisites() {
        let relation = ElaboratedTraitReference { definition: crate::intrinsic_callable_trait_definition(),
            arguments: vec![GenericArgument::Type(Type::Unit)] };
        let projected_type = |subject| Type::Projection { subject: Box::new(subject),
            trait_definition: relation.definition, trait_arguments: relation.arguments.clone(), name: "Output".into(),
            item_generic_kinds: vec![], item_arguments: vec![] };
        let projected_row = |subject| EffectRow { effects: Default::default(), tails: Default::default(),
            projections: vec![crate::EffectRowProjection { subject: Box::new(subject),
                trait_definition: relation.definition, trait_arguments: relation.arguments.clone(), name: "Effects".into(),
                item_generic_kinds: vec![], item_arguments: vec![] }] };
        let mut contract = crate::CallableContract::default();
        contract.residual.where_bounds.push((Type::Generic(1), relation.clone()));
        let callable = Type::Callable { contract: Box::new(contract), safety: crate::Safety::Safe,
            lifetime_binders: 0, parameters: vec![], result: Box::new(projected_type(Type::Generic(0))),
            effects: projected_row(Type::Generic(0)), invocation: crate::Quantity::ONCE };
        let mut solver = TraitSolver::new(&ElaboratedInterface::default());
        solver.set_lexical_assumptions(vec![TraitGoal { subject: Type::Generic(0), relation: relation.clone() }]);
        assert_eq!(solver.normalize_type(projected_type(callable.clone())).unwrap(), projected_type(callable.clone()));
        assert_eq!(solver.normalize_effect_row(projected_row(callable.clone())).unwrap(), projected_row(callable.clone()));
        solver.set_lexical_assumptions(vec![TraitGoal { subject: Type::Generic(0), relation: relation.clone() },
            TraitGoal { subject: Type::Generic(1), relation: relation.clone() }]);
        assert_eq!(solver.normalize_type(projected_type(callable.clone())).unwrap(), projected_type(Type::Generic(0)));
        assert_eq!(solver.normalize_effect_row(projected_row(callable.clone())).unwrap(), projected_row(Type::Generic(0)));
        let borrowed = Type::Reference { lifetime: Lifetime::Elided, mutability: crate::Mutability::Shared,
            referent: Box::new(callable.clone()) };
        assert_eq!(solver.normalize_effect_row(projected_row(borrowed.clone())).unwrap(), projected_row(borrowed));
        let mut unsafe_callable = callable;
        let Type::Callable { safety, .. } = &mut unsafe_callable else { unreachable!() };
        *safety = crate::Safety::Unsafe;
        assert_eq!(solver.normalize_effect_row(projected_row(unsafe_callable.clone())).unwrap(), projected_row(unsafe_callable));
    }

    #[test]
    fn parametric_region_projections_preserve_type_row_and_const_inputs() {
        let source = "trait Family { type Item; type Effects: EffectRow; const Width: u32; }
            struct Plain<'a> {} struct Restricted<'a> {} struct Mixed<T,'a> {}
            impl<'a> Family for Plain<'a> { type Item = &'a mut i64; type Effects = {}; const Width = 7; }
            impl Family for Restricted<'static> { type Item = &'static i64; type Effects = {}; const Width = 9; }
            impl<T,'a> Family for Mixed<T,'a> { type Item = T; type Effects = {}; const Width = 11; }";
        let package = crate::PackageKey("parametric-projection-regions@0.1.0".into());
        let lexed = crate::LexedFile::lex(crate::FileKey::new(&package, "src/lib.glorious"), source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface = crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        let key = |name: &str| interface.definitions.iter().find(|definition| definition.name.as_deref() == Some(name)).unwrap().key;
        let lifetime = Lifetime::Infer(crate::types::LifetimeInferVar(0));
        let subject = |name, region| Type::Nominal { definition: key(name), arguments: vec![GenericArgument::Lifetime(region)] };
        let projected = |subject| Type::Projection { subject: Box::new(subject), trait_definition: key("Family"),
            trait_arguments: vec![], name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![] };
        let row = |subject| EffectRow { effects: Default::default(), tails: Default::default(), projections: vec![crate::EffectRowProjection {
            subject: Box::new(subject), trait_definition: key("Family"), trait_arguments: vec![], name: "Effects".into(),
            item_generic_kinds: vec![], item_arguments: vec![] }] };
        let constant = |subject| GenericArgument::ConstProjection { subject: Box::new(subject), trait_definition: key("Family"),
            trait_arguments: vec![], name: "Width".into(), kind: crate::ConstKind::U32 };
        let mut solver = TraitSolver::new(&signatures);
        assert_eq!(solver.normalize_type(projected(subject("Plain", lifetime))).unwrap(), Type::Reference {
            lifetime, mutability: crate::Mutability::Unique, referent: Box::new(Type::Scalar(ScalarType::I64)),
        });
        assert_eq!(solver.normalize_effect_row(row(subject("Plain", lifetime))).unwrap(), EffectRow::empty());
        assert_eq!(solver.normalize_generic_argument(constant(subject("Plain", lifetime))).unwrap(), GenericArgument::ConstInteger(7u32.into()));
        let restricted = subject("Restricted", lifetime);
        assert_eq!(solver.normalize_type(projected(restricted.clone())).unwrap(), projected(restricted.clone()));
        assert_eq!(solver.normalize_effect_row(row(restricted.clone())).unwrap(), row(restricted.clone()));
        assert_eq!(solver.normalize_generic_argument(constant(restricted.clone())).unwrap(), constant(restricted));
        assert_eq!(solver.normalize_type(projected(subject("Restricted", Lifetime::Static))).unwrap(), Type::Reference {
            lifetime: Lifetime::Static, mutability: crate::Mutability::Shared, referent: Box::new(Type::Scalar(ScalarType::I64)),
        });
        let mixed = Type::Nominal { definition: key("Mixed"), arguments: vec![
            GenericArgument::Type(Type::Infer(crate::types::InferVar(0))), GenericArgument::Lifetime(lifetime)] };
        assert_eq!(solver.normalize_type(projected(mixed.clone())).unwrap(), projected(mixed.clone()));
        assert_eq!(solver.normalize_effect_row(row(mixed.clone())).unwrap(), row(mixed.clone()));
        assert_eq!(solver.normalize_generic_argument(constant(mixed.clone())).unwrap(), constant(mixed));
    }

    #[test]
    fn parametric_region_projection_preserves_lexical_and_outer_binder_relations() {
        let source = "trait Family { type Item; } struct Conditional<'a,'b> {}
            impl<'a,'b> Family for Conditional<'a,'b> where 'a: 'b { type Item = (&'a i64, &'b i64); }";
        let package = crate::PackageKey("parametric-projection-context@0.1.0".into());
        let lexed = crate::LexedFile::lex(crate::FileKey::new(&package, "src/lib.glorious"), source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface = crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        let key = |name: &str| interface.definitions.iter().find(|definition| definition.name.as_deref() == Some(name)).unwrap().key;
        let first = Lifetime::Infer(crate::types::LifetimeInferVar(0));
        let second = Lifetime::Infer(crate::types::LifetimeInferVar(1));
        let projected = |a, b| Type::Projection {
            subject: Box::new(Type::Nominal { definition: key("Conditional"), arguments: vec![
                GenericArgument::Lifetime(a), GenericArgument::Lifetime(b)] }),
            trait_definition: key("Family"), trait_arguments: vec![], name: "Item".into(),
            item_generic_kinds: vec![], item_arguments: vec![],
        };
        let reference = |lifetime| Type::Reference { lifetime, mutability: crate::Mutability::Shared,
            referent: Box::new(Type::Scalar(ScalarType::I64)) };
        let mut solver = TraitSolver::new(&signatures);
        assert_eq!(solver.normalize_type(projected(first, second)).unwrap(), projected(first, second));
        assert_eq!(solver.normalize_type(projected(first, first)).unwrap(), Type::Tuple(vec![reference(first), reference(first)]));
        solver.set_outlives_assumptions(vec![crate::OutlivesPredicate::Region { longer: first, shorter: second }]);
        assert_eq!(solver.normalize_type(projected(first, second)).unwrap(), Type::Tuple(vec![reference(first), reference(second)]));
        solver.set_outlives_assumptions(vec![]);
        assert_eq!(solver.normalize_type(projected(first, second)).unwrap(), projected(first, second));
        let outer = Lifetime::Bound { depth: 0, index: 0 };
        solver.set_outlives_assumptions(vec![crate::OutlivesPredicate::Region { longer: outer, shorter: second }]);
        assert_eq!(solver.normalize_type_in_region_binder(projected(outer, second), 1).unwrap(),
            Type::Tuple(vec![reference(outer), reference(second)]));
        assert_eq!(solver.normalize_type(projected(outer, second)).unwrap(), projected(outer, second),
            "abstracting an inference cell cannot supply a missing outer binder");
    }

    #[test]
    fn explicitly_bound_projection_normalization_retains_scope_and_outlives_evidence() {
        let source = "struct Wrapper<'a,'b> {} trait Family { type Item; }
            impl<'a,'b> Family for Wrapper<'a,'b> where 'a: 'b { type Item = &'a i64; }";
        let package = crate::PackageKey("bound-projection-regions@0.1.0".into());
        let lexed = crate::LexedFile::lex(crate::FileKey::new(&package, "src/lib.glorious"), source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface = crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        let key = |name: &str| interface.definitions.iter().find(|definition| definition.name.as_deref() == Some(name)).unwrap().key;
        let first = Lifetime::Bound { depth: 0, index: 0 };
        let second = Lifetime::Bound { depth: 0, index: 1 };
        let projected = Type::Projection {
            subject: Box::new(Type::Nominal { definition: key("Wrapper"), arguments: vec![
                GenericArgument::Lifetime(first), GenericArgument::Lifetime(second)] }),
            trait_definition: key("Family"), trait_arguments: vec![], name: "Item".into(),
            item_generic_kinds: vec![], item_arguments: vec![],
        };
        let mut solver = TraitSolver::new(&signatures);
        assert_eq!(solver.normalize_type(projected.clone()).unwrap(), projected,
            "a public unscoped query cannot own these bound regions");
        assert!(solver.normalize_type_in_region_binder(projected.clone(), 2).is_err(),
            "ownership of the binder does not supply an outlives predicate");
        solver.set_outlives_assumptions(vec![crate::OutlivesPredicate::Region { longer: first, shorter: second }]);
        assert_eq!(solver.normalize_type_in_region_binder(projected.clone(), 2).unwrap(),
            Type::Reference { lifetime: first, mutability: crate::Mutability::Shared,
                referent: Box::new(Type::Scalar(ScalarType::I64)) });
        assert_eq!(solver.normalize_type_in_region_binder(projected.clone(), 1).unwrap(), projected,
            "an out-of-range bound region cannot enter a smaller scope");
        assert_eq!(solver.normalize_type(projected.clone()).unwrap(), projected,
            "a scoped result cannot authorize a later unscoped query");
        solver.set_outlives_assumptions(vec![]);
        assert!(solver.normalize_type_in_region_binder(projected, 2).is_err(),
            "removing lexical evidence invalidates the previous selected answer");
    }

    #[test]
    fn structural_projection_normalization_uses_only_the_current_lexical_environment() {
        let source = "trait Mark {} struct Wrapper<T> { value: T } trait Family { type Item; type Effects: EffectRow; const Width: u32; } impl<T> Family for Wrapper<T> where T: Mark { type Item = T; type Effects = {}; const Width = 7; }";
        let package = crate::PackageKey("normalization@0.1.0".into());
        let file = crate::FileKey::new(&package, "src/lib.glorious");
        let lexed = crate::LexedFile::lex(file, source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface = crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.is_empty(), "{:#?}", signatures.diagnostics);
        let key = |name: &str| interface.definitions.iter().find(|definition| definition.name.as_deref() == Some(name)).unwrap().key;
        let projection = Type::Projection {
            subject: Box::new(Type::Nominal { definition: key("Wrapper"), arguments: vec![GenericArgument::Type(Type::Generic(0))] }),
            trait_definition: key("Family"), trait_arguments: vec![],
            name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![],
        };
        let mut solver = TraitSolver::new(&signatures);
        let subject = Type::Nominal { definition: key("Wrapper"), arguments: vec![GenericArgument::Type(Type::Generic(0))] };
        let row = EffectRow { effects: Default::default(), tails: Default::default(), projections: vec![crate::EffectRowProjection {
            subject: Box::new(subject.clone()), trait_definition: key("Family"), trait_arguments: vec![],
            name: "Effects".into(), item_generic_kinds: vec![], item_arguments: vec![],
        }] };
        let constant = GenericArgument::ConstProjection { subject: Box::new(subject), trait_definition: key("Family"),
            trait_arguments: vec![], name: "Width".into(), kind: crate::ConstKind::U32 };
        assert_eq!(solver.normalize_type(projection.clone()).unwrap(), projection);
        assert_eq!(solver.normalize_effect_row(row.clone()).unwrap(), row);
        assert_eq!(solver.normalize_generic_argument(constant.clone()).unwrap(), constant);
        solver.set_lexical_assumptions(vec![TraitGoal { subject: Type::Generic(0), relation: ElaboratedTraitReference {
            definition: key("Mark"), arguments: vec![],
        } }]);
        assert_eq!(solver.normalize_type(projection.clone()).unwrap(), Type::Generic(0));
        assert_eq!(solver.normalize_effect_row(row.clone()).unwrap(), EffectRow::empty());
        assert_eq!(solver.normalize_generic_argument(constant.clone()).unwrap(), GenericArgument::ConstInteger(7u32.into()));
        solver.set_lexical_assumptions(vec![]);
        assert_eq!(solver.normalize_type(projection.clone()).unwrap(), projection);
        assert_eq!(solver.normalize_effect_row(row.clone()).unwrap(), row);
        assert_eq!(solver.normalize_generic_argument(constant.clone()).unwrap(), constant);
        solver.set_lexical_assumptions(vec![TraitGoal { subject: Type::Generic(1), relation: ElaboratedTraitReference {
            definition: key("Mark"), arguments: vec![],
        } }]);
        assert_eq!(solver.normalize_type(projection.clone()).unwrap(), projection);
        assert_eq!(solver.normalize_effect_row(row.clone()).unwrap(), row);
        assert_eq!(solver.normalize_generic_argument(constant.clone()).unwrap(), constant);
    }

    #[test]
    fn projection_free_type_fast_path_matches_normalization_under_every_container() {
        let signatures = ElaboratedInterface::default();
        let definition = DefKey(Digest::of_bytes(b"normalization-container"));
        let leaves = [Type::Unit, Type::Never, Type::Scalar(ScalarType::I64), Type::Generic(0),
            Type::Error, Type::Infer(crate::types::InferVar(0)), Type::ConstInteger(7u32.into()), Type::ConstQuantity(crate::Quantity::AFFINE),
            Type::ConstGeneric { index: 1, kind: crate::ConstKind::U32 }];
        let mut solver = TraitSolver::new(&signatures);
        for leaf in leaves {
            let variants = [leaf.clone(), Type::Tuple(vec![leaf.clone()]), Type::Array(Box::new(leaf.clone())),
                Type::Reference { mutability: crate::Mutability::Unique, lifetime: crate::Lifetime::Generic(0), referent: Box::new(leaf.clone()) },
                Type::Callable { contract: Default::default(), safety: crate::Safety::Safe, lifetime_binders: 1, parameters: vec![leaf.clone()], result: Box::new(leaf.clone()), effects: EffectRow::empty(), invocation: crate::Quantity::ONCE },
                Type::StaticData { element: Box::new(leaf.clone()), tag: 7, alignment: 8 },
                Type::Nominal { definition, arguments: vec![GenericArgument::Type(leaf), GenericArgument::Lifetime(crate::Lifetime::Static),
                    GenericArgument::ConstInteger(2u32.into()), GenericArgument::ConstQuantity(crate::Quantity::AFFINE), GenericArgument::EffectRow(EffectRow::empty()),
                    GenericArgument::ConstGeneric { index: 0, kind: crate::ConstKind::U32 },
                    GenericArgument::ConstInfer { variable: crate::types::ConstInferVar(0), kind: crate::ConstKind::U32 },
                    GenericArgument::ConstIntegerExpr(crate::IntegerConstExpr::binary(crate::types::integer_const::IntegerConstOp::Add, Box::new(crate::IntegerConstExpr::Literal(1u32.into())), Box::new(crate::IntegerConstExpr::Literal(2u32.into()))))] }];
            for value in variants {
                assert!(type_projection_normalization_is_identity(&value), "{value:?}");
                assert_eq!(solver.normalize_type(value.clone()).unwrap(), value);
                assert_eq!(solver.steps, 0);
            }
        }
    }

    #[test]
    fn nested_type_and_const_projections_never_take_the_identity_fast_path() {
        let definition = DefKey(Digest::of_bytes(b"missing-projection-evidence"));
        let projection = Type::Projection { subject: Box::new(Type::Scalar(ScalarType::I64)), trait_definition: definition,
            trait_arguments: vec![], name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![] };
        let constant = Type::Nominal { definition, arguments: vec![GenericArgument::ConstProjection {
            subject: Box::new(Type::Scalar(ScalarType::I64)), trait_definition: definition, trait_arguments: vec![], name: "Width".into(), kind: crate::ConstKind::U32,
        }] };
        for nested in [projection.clone(), constant] {
            let variants = [nested.clone(), Type::Tuple(vec![nested.clone()]), Type::Array(Box::new(nested.clone())),
                Type::Reference { mutability: crate::Mutability::Shared, lifetime: crate::Lifetime::Static, referent: Box::new(nested.clone()) },
                Type::Callable { contract: Default::default(), safety: crate::Safety::Safe, lifetime_binders: 0, parameters: vec![nested.clone()], result: Box::new(Type::Unit), effects: EffectRow::empty(), invocation: crate::Quantity::UNRESTRICTED },
                Type::Callable { contract: Default::default(), safety: crate::Safety::Safe, lifetime_binders: 0, parameters: vec![], result: Box::new(nested.clone()), effects: EffectRow::empty(), invocation: crate::Quantity::UNRESTRICTED },
                Type::Nominal { definition, arguments: vec![GenericArgument::Type(nested)] }];
            for value in variants {
                assert!(!type_projection_normalization_is_identity(&value), "{value:?}");
                assert!(TraitSolver::new(&ElaboratedInterface::default()).normalize_type(value).is_err());
            }
        }
        // All kinded carriers now use the same recursive query; the fast
        // path must not conceal rows, callable contracts or static data.
        let row = EffectRow { effects: Default::default(), projections: vec![crate::EffectRowProjection {
            subject: Box::new(projection.clone()), trait_definition: definition, trait_arguments: vec![],
            name: "Effects".into(), item_generic_kinds: vec![], item_arguments: vec![],
        }], tails: Default::default() };
        let nested = [Type::StaticData { element: Box::new(projection), tag: 1, alignment: 1 },
            Type::Callable { contract: Default::default(), safety: crate::Safety::Safe, lifetime_binders: 0, parameters: vec![], result: Box::new(Type::Unit), effects: row.clone(), invocation: crate::Quantity::UNRESTRICTED },
            Type::Nominal { definition, arguments: vec![GenericArgument::EffectRow(row)] }];
        for value in nested {
            assert!(!type_projection_normalization_is_identity(&value));
            assert!(TraitSolver::new(&ElaboratedInterface::default()).normalize_type(value).is_err());
        }
    }

    #[test]
    fn fresh_query_shares_only_immutable_state_and_restores_its_own_budget() {
        let signatures = ElaboratedInterface::default();
        let goal = TraitGoal {
            relation: ElaboratedTraitReference {
                definition: DefKey(Digest::of_bytes(b"missing-trait")),
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        };
        let mut original = TraitSolver::with_limits(
            &signatures,
            TraitSolverLimits { max_depth: DEFAULT_MAX_TRAIT_DEPTH, max_steps: 1 },
        );
        assert_eq!(original.solve(goal.clone()), TraitAnswer::NoSolution);
        assert!(!original.tables.is_empty());
        let mut fresh = original.fresh_query();
        assert!(Arc::ptr_eq(&original.rules, &fresh.rules));
        assert!(Arc::ptr_eq(&original.manual_use_nominals, &fresh.manual_use_nominals));
        assert!(Arc::ptr_eq(&original.traits, &fresh.traits));
        assert!(Arc::ptr_eq(&original.definitions, &fresh.definitions));
        assert_eq!(fresh.limits, original.limits);
        assert!(fresh.tables.is_empty());
        assert_eq!(fresh.steps, 0);
        assert_eq!(fresh.solve(goal.clone()), TraitAnswer::NoSolution);
        assert_eq!(fresh.solve(goal.clone()), TraitAnswer::Overflow);
        assert_eq!(original.solve(goal), TraitAnswer::Overflow);
    }

    fn ownership_snapshot_fixture() -> (ElaboratedInterface, BTreeMap<String, DefKey>) {
        let source = r#"
            trait Mark: Use<[0, 1]> {}
            struct Ticket {}
            impl Use<[1, 1]> for Ticket {}
            struct Marker {}
            impl Mark for Marker {}
            struct Owner<T> { pointer: *mut T }
            impl<T> Use<[0, 1]> for Owner<T> where T: Mark {}
            struct Pair<T> { left: T, right: Ticket }
            fn bounded<T>() where T: Mark {}
        "#;
        let package = crate::PackageKey("ownership-snapshot@0.1.0".into());
        let file = crate::FileKey::new(&package, "src/lib.glorious");
        let lexed = crate::LexedFile::lex(file, source);
        let scan = crate::DeclarationScan::scan(&lexed, source);
        let interface = crate::InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        let names = interface.definitions.iter().filter_map(|definition|
            definition.name.clone().map(|name| (name, definition.key))).collect();
        (signatures, names)
    }

    #[test]
    fn indexed_ownership_queries_match_uncached_queries_without_inheriting_budgets() {
        let (signatures, names) = ownership_snapshot_fixture();
        let solver = TraitSolver::with_limits(&signatures,
            TraitSolverLimits { max_depth: 0, max_steps: 0 });
        let nominal = |name: &str, arguments| Type::Nominal { definition: names[name], arguments };
        let ticket = nominal("Ticket", vec![]);
        let marker = nominal("Marker", vec![]);
        let owner = |value| nominal("Owner", vec![GenericArgument::Type(value)]);
        let types = vec![
            Type::Unit, Type::Scalar(ScalarType::I64), ticket.clone(), marker.clone(),
            owner(marker), owner(Type::Scalar(ScalarType::I64)), owner(Type::Generic(0)),
            nominal("Pair", vec![GenericArgument::Type(ticket.clone())]),
            Type::Array(Box::new(ticket.clone())),
            Type::Tuple(vec![ticket.clone(), Type::Generic(0)]),
        ];
        assert_eq!(solver.principal_use_with_assumptions(&ticket, &[]), None);
        assert_eq!(signatures.principal_use_interval_with_solver(&ticket, &solver), Some(crate::Quantity::ONCE));
        let ElaboratedHeader::Callable(bounded) = &signatures.definitions[&names["bounded"]] else { panic!() };
        for _ in 0..3 {
            for ty in &types {
                assert_eq!(signatures.principal_use_interval_with_solver(ty, &solver),
                    signatures.principal_use_interval(ty), "{ty:?}");
                assert_eq!(signatures.principal_use_interval_with_bounds_and_solver(ty, &bounded.where_bounds, &solver),
                    signatures.principal_use_interval_with_bounds(ty, &bounded.where_bounds), "{ty:?}");
            }
        }
        assert!(solver.tables.is_empty());
        assert!(solver.principal_active.is_empty());
        assert_eq!(solver.steps, 0);
        assert_eq!(solver.limits.max_steps, 0);
    }

    #[test]
    fn manual_ownership_index_is_frozen_with_its_rule_snapshot() {
        let (mut signatures, names) = ownership_snapshot_fixture();
        let frozen = TraitSolver::new(&signatures);
        assert!(frozen.has_manual_use_for(names["Ticket"]));
        assert!(frozen.has_manual_use_for(names["Owner"]));
        assert!(!frozen.has_manual_use_for(names["Pair"]));
        signatures.definitions.retain(|_, header| !matches!(header,
            ElaboratedHeader::Implementation(implementation)
                if implementation.relation.definition == crate::resolution::language_use_trait_definition()));
        let fresh = frozen.fresh_query();
        assert!(Arc::ptr_eq(&frozen.manual_use_nominals, &fresh.manual_use_nominals));
        assert!(fresh.has_manual_use_for(names["Ticket"]));
        assert!(fresh.has_manual_use_for(names["Owner"]));
        let changed = TraitSolver::new(&signatures);
        assert!(!changed.has_manual_use_for(names["Ticket"]));
        assert!(!changed.has_manual_use_for(names["Owner"]));
    }

    #[test]
    fn fresh_query_retains_its_frozen_interface_not_later_mutations() {
        let key = DefKey(Digest::of_bytes(b"frozen-nominal-layout"));
        let layout = |ty| ElaboratedHeader::Nominal {
            generics: 0, generic_kinds: vec![],
            contract: Default::default(), universal_bounds: vec![],
            layout: ElaboratedNominalLayout::Struct(vec![crate::NominalField {
                name: "field".into(), ty, private_authority: None,
            }]),
        };
        let initial = layout(Type::Scalar(ScalarType::I64));
        let changed = layout(Type::Reference {
            lifetime: crate::Lifetime::Elided, mutability: crate::Mutability::Unique,
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        });
        let mut signatures = ElaboratedInterface::default();
        signatures.definitions.insert(key, initial.clone());
        let original = TraitSolver::new(&signatures);
        signatures.definitions.insert(key, changed.clone());
        let fresh = original.fresh_query();
        assert_eq!(fresh.definitions.get(&key), Some(&initial));
        let updated = TraitSolver::new(&signatures);
        assert_eq!(updated.definitions.get(&key), Some(&changed));
        let nominal = Type::Nominal { definition: key, arguments: vec![] };
        assert_eq!(fresh.principal_use_with_assumptions(&nominal, &[]), Some(crate::Quantity::UNRESTRICTED));
        assert_eq!(updated.principal_use_with_assumptions(&nominal, &[]), Some(crate::Quantity::AFFINE));
    }

    #[test]
    fn reset_query_restores_the_independent_step_budget() {
        let signatures = ElaboratedInterface::default();
        let relation = ElaboratedTraitReference {
            definition: DefKey(Digest::of_bytes(b"missing-trait")),
            arguments: vec![],
        };
        let goal = TraitGoal {
            relation,
            subject: Type::Scalar(ScalarType::I64),
        };
        let mut solver = TraitSolver::with_limits(
            &signatures,
            TraitSolverLimits {
                max_depth: DEFAULT_MAX_TRAIT_DEPTH,
                max_steps: 1,
            },
        );

        assert_eq!(solver.solve(goal.clone()), TraitAnswer::NoSolution);
        assert_eq!(solver.solve(goal.clone()), TraitAnswer::Overflow);
        solver.reset_query();
        assert_eq!(solver.solve(goal), TraitAnswer::NoSolution);
    }
}
