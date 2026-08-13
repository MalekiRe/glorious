//! Deterministic tabled solving for ordinary, coherent source traits.
//!
//! This is intentionally a compact kernel: it operates only on frozen
//! interfaces, returns declaration-key evidence, and never walks source or
//! body arenas.  Associated projections, HRTBs, and inference variables build
//! on the same goal/table boundary later.

use std::collections::BTreeMap;

use crate::{
    DefKey, Digest, ElaboratedHeader, ElaboratedImplementation, ElaboratedInterface,
    ElaboratedTraitReference, Type,
};

pub const DEFAULT_MAX_TRAIT_DEPTH: u32 = 128;
pub const DEFAULT_MAX_TRAIT_STEPS: u32 = 1_000_000;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TraitGoal {
    pub relation: ElaboratedTraitReference,
    pub subject: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TraitAnswer {
    Proven { evidence: DefKey },
    Refuted { evidence: DefKey },
    NoSolution,
    Ambiguous,
    Overflow,
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

/// A per-body solver cache.  It can be discarded with the caller's body
/// scratch; every entry is keyed by a span-free canonical goal digest.
pub struct TraitSolver {
    rules: Vec<Rule>,
    tables: BTreeMap<Digest, TableState>,
    limits: TraitSolverLimits,
    steps: u32,
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
        Self {
            rules,
            tables: BTreeMap::new(),
            limits,
            steps: 0,
        }
    }

    pub fn solve(&mut self, goal: TraitGoal) -> TraitAnswer {
        self.solve_at(goal, 0).into()
    }

    /// Select an implementation for `goal` and normalize one of its
    /// zero-arity associated types with the selected impl substitution.
    ///
    /// Associated-type syntax has not yet reached body type expressions, but
    /// the frozen interface already carries the data.  Keeping normalization
    /// at this solver boundary means the later projection syntax can share
    /// candidate selection, bounds checking, and canonical memoization rather
    /// than introduce a parallel impl lookup.
    pub fn normalize_associated_type(
        &mut self,
        goal: TraitGoal,
        name: &str,
    ) -> TraitProjectionAnswer {
        self.normalize_associated_type_application(goal, name, &[])
    }

    /// Normalize an associated type application through selected trait
    /// evidence. Item arguments occupy generic slots after the implementation
    /// binders, preserving a stable substitution layout for GAT-like items.
    pub fn normalize_associated_type_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[Type],
    ) -> TraitProjectionAnswer {
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitProjectionAnswer::NoSolution;
                };
                let Some(substitution) = match_rule(&rule.implementation, &goal) else {
                    return TraitProjectionAnswer::NoSolution;
                };
                match rule.implementation.associated_types.get(name) {
                    Some(item) if item.generics != arguments.len() as u32 => {
                        TraitProjectionAnswer::AssociatedTypeArity {
                            evidence,
                            expected: item.generics,
                            found: arguments.len() as u32,
                        }
                    }
                    Some(item) => {
                        let base = rule.implementation.generics;
                        let mut substitution = substitution;
                        for (offset, argument) in arguments.iter().cloned().enumerate() {
                            substitution.insert(base + offset as u32, argument);
                        }
                        TraitProjectionAnswer::Normalized {
                            evidence,
                            ty: substitute_type(&item.value, &substitution),
                        }
                    }
                    None => TraitProjectionAnswer::MissingAssociatedType { evidence },
                }
            }
            TraitAnswer::Refuted { evidence } => TraitProjectionAnswer::Refuted { evidence },
            TraitAnswer::NoSolution => TraitProjectionAnswer::NoSolution,
            TraitAnswer::Ambiguous => TraitProjectionAnswer::Ambiguous,
            TraitAnswer::Overflow => TraitProjectionAnswer::Overflow,
        }
    }

    fn solve_at(&mut self, goal: TraitGoal, depth: u32) -> TraitAnswerIndex {
        if depth >= self.limits.max_depth || self.steps >= self.limits.max_steps {
            return TraitAnswerIndex::Overflow;
        }
        self.steps += 1;
        let key = goal_key(&goal);
        match self.tables.get(&key).copied() {
            Some(TableState::Complete(answer)) => return answer,
            // Ordinary recursive cycles are ambiguous by design.  Auto traits
            // are not in this kernel yet and therefore get no coinduction.
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
        let mut uncertain = false;
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
                match self.solve_at(obligation, depth + 1) {
                    TraitAnswerIndex::Proven(_) => {}
                    TraitAnswerIndex::Ambiguous | TraitAnswerIndex::Overflow => {
                        viable = false;
                        uncertain = true;
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
        let answer = match (positives.as_slice(), negatives.as_slice()) {
            // A coherent interface has at most one applicable answer across
            // both polarities.  Treat contradictory input as ambiguity so an
            // unchecked coherence failure cannot make selection order matter.
            ([..], [..]) if !positives.is_empty() && !negatives.is_empty() => {
                TraitAnswerIndex::Ambiguous
            }
            ([], []) if uncertain => TraitAnswerIndex::Ambiguous,
            ([], []) => TraitAnswerIndex::NoSolution,
            ([definition], []) => TraitAnswerIndex::Proven(*definition),
            ([], [definition]) => TraitAnswerIndex::Refuted(*definition),
            _ => TraitAnswerIndex::Ambiguous,
        };
        self.tables.insert(key, TableState::Complete(answer));
        answer
    }
}

fn match_rule(
    implementation: &ElaboratedImplementation,
    goal: &TraitGoal,
) -> Option<BTreeMap<u32, Type>> {
    if implementation.relation.arguments.len() != goal.relation.arguments.len() {
        return None;
    }
    let mut substitution = BTreeMap::new();
    match_type(&implementation.self_ty, &goal.subject, &mut substitution)?;
    for (template, actual) in implementation
        .relation
        .arguments
        .iter()
        .zip(&goal.relation.arguments)
    {
        match_type(template, actual, &mut substitution)?;
    }
    Some(substitution)
}

fn match_type(
    template: &Type,
    actual: &Type,
    substitution: &mut BTreeMap<u32, Type>,
) -> Option<()> {
    match template {
        Type::Generic(index) => match substitution.get(index) {
            Some(previous) if previous != actual => None,
            Some(_) => Some(()),
            None => {
                substitution.insert(*index, actual.clone());
                Some(())
            }
        },
        Type::Unit | Type::Never | Type::Scalar(_) | Type::Error => {
            (template == actual).then_some(())
        }
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
                    .try_for_each(|(template, actual)| match_type(template, actual, substitution))
            }
            _ => None,
        },
        Type::Tuple(values) => match actual {
            Type::Tuple(actual_values) if values.len() == actual_values.len() => values
                .iter()
                .zip(actual_values)
                .try_for_each(|(template, actual)| match_type(template, actual, substitution)),
            _ => None,
        },
        Type::Array(element) => match actual {
            Type::Array(actual_element) => match_type(element, actual_element, substitution),
            _ => None,
        },
        Type::Reference {
            mutability,
            referent,
        } => match actual {
            Type::Reference {
                mutability: actual_mutability,
                referent: actual_referent,
            } if mutability == actual_mutability => {
                match_type(referent, actual_referent, substitution)
            }
            _ => None,
        },
        Type::Callable {
            parameters,
            result,
            effects,
            invocation,
        } => {
            match actual {
                Type::Callable {
                    parameters: actual_parameters,
                    result: actual_result,
                    effects: actual_effects,
                    invocation: actual_invocation,
                } if parameters.len() == actual_parameters.len()
                    && effects == actual_effects
                    && invocation == actual_invocation =>
                {
                    parameters.iter().zip(actual_parameters).try_for_each(
                        |(template, actual)| match_type(template, actual, substitution),
                    )?;
                    match_type(result, actual_result, substitution)
                }
                _ => None,
            }
        }
        // A caller-owned inference variable is intentionally not solved by
        // this frozen-interface kernel.  Body elaboration must choose a type
        // first, then issue a canonical trait goal.
        Type::Infer(_) => None,
    }
}

fn substitute_relation(
    relation: &ElaboratedTraitReference,
    substitution: &BTreeMap<u32, Type>,
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .map(|argument| substitute_type(argument, substitution))
            .collect(),
    }
}

fn substitute_type(value: &Type, substitution: &BTreeMap<u32, Type>) -> Type {
    match value {
        Type::Generic(index) => substitution
            .get(index)
            .cloned()
            .unwrap_or_else(|| value.clone()),
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition: *definition,
            arguments: arguments
                .iter()
                .map(|value| substitute_type(value, substitution))
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
            referent,
        } => Type::Reference {
            mutability: *mutability,
            referent: Box::new(substitute_type(referent, substitution)),
        },
        Type::Callable {
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            parameters: parameters
                .iter()
                .map(|value| substitute_type(value, substitution))
                .collect(),
            result: Box::new(substitute_type(result, substitution)),
            effects: effects.clone(),
            invocation: *invocation,
        },
        _ => value.clone(),
    }
}

fn goal_key(goal: &TraitGoal) -> Digest {
    // `Type` and `EffectRow` have deterministic Debug implementations over
    // ordered members.  This temporary kernel uses that closed rendering only
    // for per-body memoization; public fingerprints never depend on it.
    Digest::of_parts([
        b"grandiose-stage0-trait-goal-v1".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        format!("{:?}", goal.relation.arguments).as_bytes(),
        format!("{:?}", goal.subject).as_bytes(),
    ])
}
