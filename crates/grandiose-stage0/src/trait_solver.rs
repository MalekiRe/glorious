//! Deterministic tabled solving for ordinary, coherent source traits.
//!
//! This is intentionally a compact kernel: it operates only on frozen
//! interfaces, returns declaration-key evidence, and never walks source or
//! body arenas.  Associated projections, HRTBs, and inference variables build
//! on the same goal/table boundary later.

use std::collections::BTreeMap;

use crate::{
    CallableSignature, DefKey, Digest, EffectInstance, EffectRow, ElaboratedEnumVariantPayload,
    ElaboratedHeader, ElaboratedImplementation, ElaboratedInterface, ElaboratedNominalLayout,
    ElaboratedTrait, ElaboratedTraitReference, GenericArgument, Type, implementation_method_key,
    signature::TRAIT_SELF_GENERIC,
    types::{canonical_generic_arguments_encoding, canonical_type_encoding},
};

pub const DEFAULT_MAX_TRAIT_DEPTH: u32 = 128;
pub const DEFAULT_MAX_TRAIT_STEPS: u32 = 1_000_000;

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
    /// Substituting a nested row would create two distinct open tails. G1
    /// rows have one canonical tail, so neither tail can be selected.
    ConflictingRowTails,
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
pub struct TraitSolver {
    rules: Vec<Rule>,
    /// Trait declarations carry associated-item defaults.  The solver owns a
    /// frozen copy alongside implementation rules so projection selection
    /// remains self-contained and deterministic.
    traits: BTreeMap<DefKey, ElaboratedTrait>,
    /// Frozen layouts are needed for source-declared auto traits to turn a
    /// nominal application into its field obligations. Keeping them in the
    /// solver preserves the same body-local, interface-only boundary as impl
    /// rule selection.
    definitions: BTreeMap<DefKey, ElaboratedHeader>,
    tables: BTreeMap<Digest, TableState>,
    limits: TraitSolverLimits,
    steps: u32,
}

#[derive(Clone, Copy)]
enum AssociatedItemKind {
    Type,
    EffectRow,
    Const,
}

enum SupertraitLookup<T> {
    Found(T),
    Missing,
    Ambiguous,
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
        let traits = signatures
            .definitions
            .iter()
            .filter_map(|(definition, header)| match header {
                ElaboratedHeader::Trait(trait_header) => Some((*definition, trait_header.clone())),
                _ => None,
            })
            .collect();
        Self {
            rules,
            traits,
            definitions: signatures.definitions.clone(),
            tables: BTreeMap::new(),
            limits,
            steps: 0,
        }
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

    fn supertrait_goals(&self, goal: &TraitGoal) -> Vec<TraitGoal> {
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

    fn find_associated_item_goal(
        &self,
        goal: &TraitGoal,
        name: &str,
        kind: AssociatedItemKind,
        active: &mut Vec<Digest>,
    ) -> SupertraitLookup<TraitGoal> {
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
            rules: self.rules.clone(),
            traits: self.traits.clone(),
            definitions: self.definitions.clone(),
            tables: BTreeMap::new(),
            limits: self.limits.clone(),
            steps: 0,
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
                let Some(substitution) = match_rule(&rule.implementation, &goal) else {
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

    /// Normalize every concrete associated-type projection contained in a
    /// type.  Declaration-owned generic projections remain symbolic, while
    /// a concrete result is reduced to its recursive projection normal form.
    pub fn normalize_type(&mut self, value: Type) -> Result<Type, Box<TraitProjectionAnswer>> {
        self.normalize_type_projections(value, &mut vec![])
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
        let answer = self.select_associated_type_application(goal, name, &arguments);
        let TraitProjectionAnswer::Normalized { evidence, ty } = answer else {
            return answer;
        };
        let mut active = vec![root_key];
        match self.normalize_type_projections(ty, &mut active) {
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
    ) -> TraitProjectionAnswer {
        if trait_goal_contains_escaping_hrtb(&goal)
            || arguments
                .iter()
                .any(generic_argument_contains_escaping_hrtb)
        {
            return TraitProjectionAnswer::NoSolution;
        }
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
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitProjectionAnswer::NoSolution;
                };
                let Some(substitution) = match_rule(&rule.implementation, &goal) else {
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

    /// Normalize concrete projections nested in a selected associated-type
    /// value.  In particular, an implementation may define `Output` as
    /// another associated projection, and that projection must not leak into
    /// a concrete call site merely because it was introduced by substitution.
    ///
    /// Symbolic projections under declaration-owned generic binders are
    /// retained. They are normalized later once instantiation supplies a
    /// concrete trait head; attempting to select an implementation early
    /// would guess evidence that a caller's where-clause may provide instead.
    fn normalize_type_projections(
        &mut self,
        value: Type,
        active: &mut Vec<Digest>,
    ) -> Result<Type, Box<TraitProjectionAnswer>> {
        match value {
            Type::Nominal {
                definition,
                arguments,
            } => Ok(Type::Nominal {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.normalize_trait_argument(argument, active))
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
                let subject = self.normalize_type_projections(*subject, active)?;
                let trait_arguments = trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_type_projections(argument, active))
                    .collect::<Result<Vec<_>, _>>()?;
                let item_arguments = item_arguments
                    .into_iter()
                    .map(|argument| self.normalize_trait_argument(argument, active))
                    .collect::<Result<Vec<_>, _>>()?;
                let projection = Type::Projection {
                    subject: Box::new(subject),
                    trait_definition,
                    trait_arguments,
                    name,
                    item_generic_kinds,
                    item_arguments,
                };
                if !projection_is_concrete(&projection) {
                    return Ok(projection);
                }
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
                        arguments: trait_arguments
                            .into_iter()
                            .map(GenericArgument::Type)
                            .collect(),
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
                let answer = self.select_associated_type_application(goal, &name, &item_arguments);
                let result = match answer {
                    TraitProjectionAnswer::Normalized { ty, .. } => {
                        self.normalize_type_projections(ty, active)
                    }
                    answer => Err(Box::new(answer)),
                };
                active.pop();
                result
            }
            Type::Tuple(values) => Ok(Type::Tuple(
                values
                    .into_iter()
                    .map(|value| self.normalize_type_projections(value, active))
                    .collect::<Result<_, _>>()?,
            )),
            Type::Array(value) => Ok(Type::Array(Box::new(
                self.normalize_type_projections(*value, active)?,
            ))),
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => Ok(Type::Reference {
                mutability,
                lifetime,
                referent: Box::new(self.normalize_type_projections(*referent, active)?),
            }),
            Type::Callable {
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } => Ok(Type::Callable {
                lifetime_binders,
                parameters: parameters
                    .into_iter()
                    .map(|parameter| self.normalize_type_projections(parameter, active))
                    .collect::<Result<_, _>>()?,
                result: Box::new(self.normalize_type_projections(*result, active)?),
                effects,
                invocation,
            }),
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
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitConstProjectionAnswer::NoSolution;
                };
                let Some(substitution) = match_rule(&rule.implementation, &goal) else {
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
        let answer = self.select_associated_effect_row_application(goal, name, &arguments);
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
    ) -> TraitEffectRowProjectionAnswer {
        if trait_goal_contains_escaping_hrtb(&goal)
            || arguments
                .iter()
                .any(generic_argument_contains_escaping_hrtb)
        {
            return TraitEffectRowProjectionAnswer::NoSolution;
        }
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
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitEffectRowProjectionAnswer::NoSolution;
                };
                let Some(mut substitution) = match_rule(&rule.implementation, &goal) else {
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

    /// Normalize concrete associated effect-row projections introduced by an
    /// implementation definition.  Symbolic projections remain intact: they
    /// need lexical caller evidence and must never trigger a global impl
    /// guess.  This mirrors `normalize_type_projections` for the row-kinded
    /// projection family.
    fn normalize_effect_row_projections(
        &mut self,
        value: EffectRow,
        active: &mut Vec<Digest>,
    ) -> Result<EffectRow, Box<TraitEffectRowProjectionAnswer>> {
        let effects = value
            .effects
            .into_iter()
            .map(|effect| {
                let arguments = effect
                    .arguments
                    .into_iter()
                    .map(|argument| self.normalize_trait_argument(argument, &mut vec![]))
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
            tail: value.tail,
        };
        for projection in value.projections {
            let subject = self
                .normalize_type_projections(*projection.subject, &mut vec![])
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let trait_arguments = projection
                .trait_arguments
                .into_iter()
                .map(|argument| self.normalize_type_projections(argument, &mut vec![]))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let item_arguments = projection
                .item_arguments
                .into_iter()
                .map(|argument| self.normalize_trait_argument(argument, &mut vec![]))
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
            if !projection_is_concrete(&projection.subject)
                || !projection
                    .trait_arguments
                    .iter()
                    .all(projection_is_concrete)
                || !projection
                    .item_arguments
                    .iter()
                    .all(generic_argument_is_concrete)
            {
                result.projections.push(projection);
                continue;
            }
            let goal = TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: projection.trait_definition,
                    arguments: projection
                        .trait_arguments
                        .into_iter()
                        .map(GenericArgument::Type)
                        .collect(),
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
            );
            let nested = match nested {
                TraitEffectRowProjectionAnswer::Normalized { row, .. } => {
                    self.normalize_effect_row_projections(row, active)
                }
                answer => Err(Box::new(answer)),
            };
            active.pop();
            let nested = nested?;
            result.effects.extend(nested.effects);
            result.projections.extend(nested.projections);
            match (result.tail, nested.tail) {
                (None, tail) => result.tail = tail,
                (Some(left), Some(right)) if left != right => {
                    return Err(Box::new(
                        TraitEffectRowProjectionAnswer::ConflictingRowTails,
                    ));
                }
                _ => {}
            }
        }
        Ok(result)
    }

    /// Select an implementation method and instantiate both the implementation
    /// binders and method-local generic binders. The returned method identity
    /// and implementation evidence let later Core/MIR lowering name the
    /// callable body without repeating source-shaped impl lookup.
    pub fn select_method(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[Type],
    ) -> TraitMethodAnswer {
        let goal = match self.find_method_goal(&goal, name, &mut Vec::new()) {
            SupertraitLookup::Found(goal) => goal,
            SupertraitLookup::Missing => return TraitMethodAnswer::NoSolution,
            SupertraitLookup::Ambiguous => return TraitMethodAnswer::Ambiguous,
        };
        match self.solve(goal.clone()) {
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
                let Some(mut substitution) = match_rule(&rule.implementation, &goal) else {
                    return TraitMethodAnswer::NoSolution;
                };
                for (offset, argument) in arguments.iter().cloned().enumerate() {
                    substitution
                        .types
                        .insert(rule.implementation.generics + offset as u32, argument);
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
    fn solve_at(
        &mut self,
        goal: TraitGoal,
        depth: u32,
        coinductive_edge: bool,
    ) -> TraitAnswerIndex {
        if depth >= self.limits.max_depth || self.steps >= self.limits.max_steps {
            return TraitAnswerIndex::Overflow;
        }
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
        if trait_goal_contains_escaping_hrtb(&goal) {
            return TraitAnswerIndex::NoSolution;
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
            let Some(substitution) = match_rule(&rule.implementation, &goal) else {
                continue;
            };
            let mut viable = true;
            for (subject, relation) in &rule.implementation.where_bounds {
                let obligation = TraitGoal {
                    relation: substitute_relation(relation, &substitution),
                    subject: substitute_type(subject, &substitution),
                };
                match self.solve_at(obligation, depth + 1, false) {
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
            answer = self.solve_structural_auto_goal(&goal, depth);
        }
        self.tables.insert(key, TableState::Complete(answer));
        answer
    }

    fn is_auto_trait(&self, goal: &TraitGoal) -> bool {
        self.traits
            .get(&goal.relation.definition)
            .is_some_and(|trait_header| trait_header.auto_trait)
    }

    /// Produce structural auto-trait evidence only when the source has
    /// explicitly declared the relation `auto`. An explicit positive or
    /// negative implementation is selected before this fallback, so a
    /// negative impl reliably opts a type out of otherwise structural proof.
    fn solve_structural_auto_goal(&mut self, goal: &TraitGoal, depth: u32) -> TraitAnswerIndex {
        if !self.is_auto_trait(goal) {
            return TraitAnswerIndex::NoSolution;
        }
        let Some(obligations) = self.structural_obligations(goal) else {
            return TraitAnswerIndex::NoSolution;
        };
        for obligation in obligations {
            match self.solve_at(obligation, depth + 1, true) {
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
            Type::Reference { referent, .. } => vec![(**referent).clone()],
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
            | Type::ConstU32(_)
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
            ElaboratedNominalLayout::Struct(fields) => {
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

    /// Reduce concrete associated projections in a trait goal before it is
    /// keyed or matched against implementation heads.  Generic projections
    /// are deliberately retained by `normalize_type_projections`, preserving
    /// the caller's eventual lexical evidence rather than guessing a global
    /// implementation.
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
        match argument {
            GenericArgument::Type(value) => self
                .normalize_type_projections(value, active)
                .map(GenericArgument::Type),
            // The runtime projection carriers are still type-only. Trait
            // selection nevertheless preserves every other kind exactly;
            // there is no type normalizer allowed to reinterpret it here.
            argument => Ok(argument),
        }
    }
}

/// A projection failure cannot become implicit successful trait evidence.
/// A refuted *projection relation* is not a refutation of the outer trait
/// goal, so it is deliberately reported as no candidate rather than leaking
/// unrelated negative evidence into the result.  Recursive normalization is
/// a bounded solver failure; ambiguity remains ambiguity.
fn projection_failure_answer(answer: TraitProjectionAnswer) -> TraitAnswerIndex {
    match answer {
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
    matches!(
        (argument, kind),
        (GenericArgument::Type(_), crate::GenericKind::Type)
            | (GenericArgument::EffectRow(_), crate::GenericKind::EffectRow)
            | (GenericArgument::Lifetime(_), crate::GenericKind::Lifetime)
            | (
                GenericArgument::ConstU32(_),
                crate::GenericKind::Const(crate::ConstKind::U32)
            )
            | (
                GenericArgument::ConstU32Expr(_),
                crate::GenericKind::Const(crate::ConstKind::U32)
            )
            | (
                GenericArgument::ConstQuantity(_),
                crate::GenericKind::Const(crate::ConstKind::Quantity)
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::GenericKind::Const(crate::ConstKind::U32)
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::GenericKind::Const(crate::ConstKind::Quantity)
            )
    )
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
        GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => {
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
/// row binder is an open tail: after the implementation's fixed prefix has
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
                        match_type_at(expected, found, &mut candidate, binder_depth)
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

    match template.tail {
        None if unmatched_effects.is_empty()
            && unmatched_projections.is_empty()
            && actual.tail.is_none() =>
        {
            Some(())
        }
        Some(crate::EffectTail::Generic(index)) => {
            let residual = EffectRow {
                effects: unmatched_effects.into_iter().collect(),
                projections: unmatched_projections,
                tail: actual.tail,
            }
            .canonicalized();
            if binder_depth > 0 && effect_row_contains_free_hrtb_placeholder(&residual, 0) {
                return None;
            }
            match substitution.effect_rows.get(&index) {
                Some(previous) if previous != &residual => None,
                Some(_) => Some(()),
                None => {
                    substitution.effect_rows.insert(index, residual.clone());
                    substitution
                        .generic_arguments
                        .insert(index, GenericArgument::EffectRow(residual));
                    Some(())
                }
            }
        }
        Some(crate::EffectTail::Infer(_)) => None,
        _ => None,
    }
}

fn generic_argument_is_const_kind(argument: &GenericArgument, expected: crate::ConstKind) -> bool {
    matches!(
        (argument, expected),
        (GenericArgument::ConstU32(_), crate::ConstKind::U32)
            | (GenericArgument::ConstU32Expr(_), crate::ConstKind::U32)
            | (
                GenericArgument::ConstQuantity(_),
                crate::ConstKind::Quantity
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::ConstKind::U32
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::ConstKind::Quantity
            )
    )
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
        | Type::ConstU32(_)
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
                        match_type_at(template, actual, substitution, binder_depth)
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
        Type::Array(element) => match actual {
            Type::Array(actual_element) => {
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
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => match actual {
            Type::Callable {
                lifetime_binders: actual_lifetime_binders,
                parameters: actual_parameters,
                result: actual_result,
                effects: actual_effects,
                invocation: actual_invocation,
            } if lifetime_binders == actual_lifetime_binders
                && parameters.len() == actual_parameters.len()
                && invocation == actual_invocation =>
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
        GenericArgument::Lifetime(crate::Lifetime::Bound { .. }) => true,
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => false,
    }
}

/// A `Bound` lifetime is a fresh universe placeholder unless it is closed by
/// a callable nested inside the candidate type. This walk distinguishes a
/// self-contained nested HRTB from a reference to an enclosing binder, and
/// intentionally reaches every generic-argument and effect-row carrier.
fn has_free_hrtb_placeholder(value: &Type, callable_nesting: u32) -> bool {
    match value {
        Type::Reference {
            lifetime: crate::Lifetime::Bound { depth, .. },
            referent,
            ..
        } => *depth >= callable_nesting || has_free_hrtb_placeholder(referent, callable_nesting),
        Type::Reference { referent, .. } | Type::Array(referent) => {
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
                || trait_arguments
                    .iter()
                    .any(|value| has_free_hrtb_placeholder(value, callable_nesting))
                || item_arguments.iter().any(|value| {
                    generic_argument_contains_free_hrtb_placeholder(value, callable_nesting)
                })
        }
        Type::Tuple(values) => values
            .iter()
            .any(|value| has_free_hrtb_placeholder(value, callable_nesting)),
        Type::Callable {
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
        GenericArgument::Lifetime(crate::Lifetime::Bound { depth, .. }) => {
            *depth >= callable_nesting
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstU32Expr(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. } => false,
    }
}

fn effect_row_contains_free_hrtb_placeholder(value: &EffectRow, callable_nesting: u32) -> bool {
    value.effects.iter().any(|effect| {
        effect.arguments.iter().any(|argument| {
            generic_argument_contains_free_hrtb_placeholder(argument, callable_nesting)
        })
    }) || value.projections.iter().any(|projection| {
        has_free_hrtb_placeholder(&projection.subject, callable_nesting)
            || projection
                .trait_arguments
                .iter()
                .any(|argument| has_free_hrtb_placeholder(argument, callable_nesting))
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
    matches!(
        (value, expected),
        (Type::ConstU32(_), crate::ConstKind::U32)
            | (Type::ConstQuantity(_), crate::ConstKind::Quantity)
            | (
                Type::ConstGeneric {
                    kind: crate::ConstKind::U32,
                    ..
                },
                crate::ConstKind::U32,
            )
            | (
                Type::ConstGeneric {
                    kind: crate::ConstKind::Quantity,
                    ..
                },
                crate::ConstKind::Quantity,
            )
    )
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
        GenericArgument::ConstGeneric { index, kind } => substitution
            .generic_arguments
            .get(index)
            .filter(|argument| generic_argument_is_const_kind(argument, *kind))
            .cloned()
            .unwrap_or_else(|| argument.clone()),
        GenericArgument::ConstU32Expr(value) => {
            let value = substitute_structural_u32_expr(value, substitution);
            match value {
                crate::StructuralU32Expr::Literal(value) => GenericArgument::ConstU32(value),
                value => GenericArgument::ConstU32Expr(value),
            }
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

fn substitute_structural_u32_expr(
    value: &crate::StructuralU32Expr,
    substitution: &ImplementationSubstitution,
) -> crate::StructuralU32Expr {
    use crate::StructuralU32Expr;
    let value = match value {
        StructuralU32Expr::Literal(value) => StructuralU32Expr::Literal(*value),
        StructuralU32Expr::Param(index) => match substitution.generic_arguments.get(index) {
            Some(GenericArgument::ConstU32(value)) => StructuralU32Expr::Literal(*value),
            Some(GenericArgument::ConstU32Expr(value)) => value.clone(),
            Some(GenericArgument::ConstGeneric {
                index,
                kind: crate::ConstKind::U32,
            }) => StructuralU32Expr::Param(*index),
            _ => StructuralU32Expr::Param(*index),
        },
        StructuralU32Expr::Add(left, right) => StructuralU32Expr::Add(
            Box::new(substitute_structural_u32_expr(left, substitution)),
            Box::new(substitute_structural_u32_expr(right, substitution)),
        ),
        StructuralU32Expr::Sub(left, right) => StructuralU32Expr::Sub(
            Box::new(substitute_structural_u32_expr(left, substitution)),
            Box::new(substitute_structural_u32_expr(right, substitution)),
        ),
        StructuralU32Expr::Mul(left, right) => StructuralU32Expr::Mul(
            Box::new(substitute_structural_u32_expr(left, substitution)),
            Box::new(substitute_structural_u32_expr(right, substitution)),
        ),
        StructuralU32Expr::Div(left, right) => StructuralU32Expr::Div(
            Box::new(substitute_structural_u32_expr(left, substitution)),
            Box::new(substitute_structural_u32_expr(right, substitution)),
        ),
        StructuralU32Expr::Rem(left, right) => StructuralU32Expr::Rem(
            Box::new(substitute_structural_u32_expr(left, substitution)),
            Box::new(substitute_structural_u32_expr(right, substitution)),
        ),
    };
    value.clone().normalized().unwrap_or(value)
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
                        (GenericArgument::ConstU32(value), crate::ConstKind::U32) => {
                            Some(Type::ConstU32(*value))
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
                .map(|value| substitute_type(value, substitution))
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
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders: *lifetime_binders,
            parameters: parameters
                .iter()
                .map(|value| substitute_type(value, substitution))
                .collect(),
            result: Box::new(substitute_type(result, substitution)),
            effects: substitute_effect_row(effects, substitution),
            invocation: *invocation,
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
                    .map(|value| substitute_type(value, substitution))
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
        tail: value.tail,
    };
    // A row variable denotes the complete residual row, not only its tail.
    // In particular, substituting `e` in `{ Prefix, | e }` must retain both
    // the caller's fixed effects/projections and its open tail.  The old
    // pure-row fast path left `e` stale whenever it followed a prefix,
    // causing defaulted and specialized associated rows to normalize to a
    // declaration-local generic instead of the selected application.
    if let Some(crate::EffectTail::Generic(index)) = value.tail
        && let Some(row) = substitution.effect_rows.get(&index)
    {
        result.effects.extend(row.effects.iter().cloned());
        result.projections.extend(row.projections.iter().cloned());
        result.tail = row.tail;
    }
    result.canonicalized()
}

fn substitute_callable_signature(
    value: &CallableSignature,
    substitution: &ImplementationSubstitution,
) -> CallableSignature {
    CallableSignature {
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

/// A projection may be selected only after every part of its trait head is
/// known. This mirrors the Core boundary: type parameters retain projections
/// for their eventual lexical evidence environment instead of acquiring a
/// global implementation by accident.
fn projection_is_concrete(value: &Type) -> bool {
    match value {
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
                && trait_arguments.iter().all(projection_is_concrete)
                && item_arguments.iter().all(generic_argument_is_concrete)
        }
        Type::Array(element) => projection_is_concrete(element),
        Type::Reference { referent, .. } => projection_is_concrete(referent),
        Type::Callable {
            parameters, result, ..
        } => parameters.iter().all(projection_is_concrete) && projection_is_concrete(result),
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. } => true,
    }
}

fn generic_argument_is_concrete(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => projection_is_concrete(value),
        GenericArgument::EffectRow(value) => {
            value.tail.is_none()
                && value.projections.is_empty()
                && value
                    .effects
                    .iter()
                    .all(|effect| effect.arguments.iter().all(generic_argument_is_concrete))
        }
        GenericArgument::Lifetime(crate::Lifetime::Static | crate::Lifetime::Elided)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::ConstU32Expr(_) => false,
        GenericArgument::Lifetime(crate::Lifetime::Generic(_) | crate::Lifetime::Bound { .. })
        | GenericArgument::ConstGeneric { .. } => false,
    }
}
