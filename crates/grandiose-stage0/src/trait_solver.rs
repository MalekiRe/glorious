//! Deterministic tabled solving for ordinary, coherent source traits.
//!
//! This is intentionally a compact kernel: it operates only on frozen
//! interfaces, returns declaration-key evidence, and never walks source or
//! body arenas.  Associated projections, HRTBs, and inference variables build
//! on the same goal/table boundary later.

use std::collections::BTreeMap;

use crate::{
    CallableSignature, DefKey, Digest, EffectInstance, EffectRow, ElaboratedHeader,
    ElaboratedImplementation, ElaboratedInterface, ElaboratedTraitReference, Type,
    implementation_method_key,
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
        arguments: &[Type],
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
            .map(|argument| self.normalize_type_projections(argument, &mut active))
            .collect::<Result<Vec<_>, _>>()
        {
            Ok(arguments) => arguments,
            Err(answer) => return *answer,
        };
        let arguments = match arguments
            .iter()
            .cloned()
            .map(|argument| self.normalize_type_projections(argument, &mut active))
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
                    .map(|argument| self.normalize_type_projections(argument, active))
                    .collect::<Result<_, _>>()?,
            }),
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
            } => {
                let subject = self.normalize_type_projections(*subject, active)?;
                let trait_arguments = trait_arguments
                    .into_iter()
                    .map(|argument| self.normalize_type_projections(argument, active))
                    .collect::<Result<Vec<_>, _>>()?;
                let item_arguments = item_arguments
                    .into_iter()
                    .map(|argument| self.normalize_type_projections(argument, active))
                    .collect::<Result<Vec<_>, _>>()?;
                let projection = Type::Projection {
                    subject: Box::new(subject),
                    trait_definition,
                    trait_arguments,
                    name,
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
                parameters,
                result,
                effects,
                invocation,
            } => Ok(Type::Callable {
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

    pub fn normalize_associated_effect_row_application(
        &mut self,
        goal: TraitGoal,
        name: &str,
        arguments: &[Type],
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
            .map(|argument| self.normalize_type_projections(argument, &mut type_active))
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
            .map(|argument| self.normalize_type_projections(argument, &mut type_active))
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
        arguments: &[Type],
    ) -> TraitEffectRowProjectionAnswer {
        match self.solve(goal.clone()) {
            TraitAnswer::Proven { evidence } => {
                let Some(rule) = self.rules.iter().find(|rule| rule.definition == evidence) else {
                    return TraitEffectRowProjectionAnswer::NoSolution;
                };
                let Some(mut substitution) = match_rule(&rule.implementation, &goal) else {
                    return TraitEffectRowProjectionAnswer::NoSolution;
                };
                match rule.implementation.associated_effect_rows.get(name) {
                    Some(item) if item.generics != arguments.len() as u32 => {
                        TraitEffectRowProjectionAnswer::AssociatedEffectRowArity {
                            evidence,
                            expected: item.generics,
                            found: arguments.len() as u32,
                        }
                    }
                    Some(item) => {
                        let base = rule.implementation.generics;
                        for (offset, argument) in arguments.iter().cloned().enumerate() {
                            substitution.insert(base + offset as u32, argument);
                        }
                        TraitEffectRowProjectionAnswer::Normalized {
                            evidence,
                            row: substitute_effect_row(&item.value, &substitution),
                        }
                    }
                    None => TraitEffectRowProjectionAnswer::MissingAssociatedEffectRow { evidence },
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
                    .map(|argument| self.normalize_type_projections(argument, &mut vec![]))
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
                .map(|argument| self.normalize_type_projections(argument, &mut vec![]))
                .collect::<Result<Vec<_>, _>>()
                .map_err(|answer| {
                    Box::new(TraitEffectRowProjectionAnswer::NestedTypeProjection { answer })
                })?;
            let projection = crate::EffectRowProjection {
                subject: Box::new(subject),
                trait_definition: projection.trait_definition,
                trait_arguments,
                name: projection.name,
                item_arguments,
            };
            if !projection_is_concrete(&projection.subject)
                || !projection
                    .trait_arguments
                    .iter()
                    .all(projection_is_concrete)
                || !projection.item_arguments.iter().all(projection_is_concrete)
            {
                result.projections.push(projection);
                continue;
            }
            let goal = TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: projection.trait_definition,
                    arguments: projection.trait_arguments,
                },
                subject: *projection.subject,
            };
            let key = associated_effect_row_projection_key(
                &goal,
                &projection.name,
                &projection.item_arguments,
            );
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
                &projection.item_arguments,
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
                    substitution.insert(rule.implementation.generics + offset as u32, argument);
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
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
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
                    .try_for_each(|(template, actual)| match_type(template, actual, substitution))
            }
            _ => None,
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => match actual {
            Type::Projection {
                subject: actual_subject,
                trait_definition: actual_trait_definition,
                trait_arguments: actual_trait_arguments,
                name: actual_name,
                item_arguments: actual_item_arguments,
            } if trait_definition == actual_trait_definition
                && name == actual_name
                && trait_arguments.len() == actual_trait_arguments.len()
                && item_arguments.len() == actual_item_arguments.len() =>
            {
                match_type(subject, actual_subject, substitution)?;
                trait_arguments
                    .iter()
                    .zip(actual_trait_arguments)
                    .chain(item_arguments.iter().zip(actual_item_arguments))
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
            lifetime,
            referent,
        } => match actual {
            Type::Reference {
                mutability: actual_mutability,
                lifetime: actual_lifetime,
                referent: actual_referent,
            } if mutability == actual_mutability && lifetime == actual_lifetime => {
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
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(substitute_type(subject, substitution)),
            trait_definition: *trait_definition,
            trait_arguments: trait_arguments
                .iter()
                .map(|value| substitute_type(value, substitution))
                .collect(),
            name: name.clone(),
            item_arguments: item_arguments
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
            lifetime,
            referent,
        } => Type::Reference {
            mutability: *mutability,
            lifetime: *lifetime,
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
            effects: substitute_effect_row(effects, substitution),
            invocation: *invocation,
        },
        _ => value.clone(),
    }
}

fn substitute_effect_row(value: &EffectRow, substitution: &BTreeMap<u32, Type>) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .iter()
                    .map(|argument| substitute_type(argument, substitution))
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
                item_arguments: projection
                    .item_arguments
                    .iter()
                    .map(|value| substitute_type(value, substitution))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

fn substitute_callable_signature(
    value: &CallableSignature,
    substitution: &BTreeMap<u32, Type>,
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

fn associated_projection_key(goal: &TraitGoal, name: &str, arguments: &[Type]) -> Digest {
    Digest::of_parts([
        b"grandiose-stage0-associated-projection-v1".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        format!("{:?}", goal.relation.arguments).as_bytes(),
        format!("{:?}", goal.subject).as_bytes(),
        name.as_bytes(),
        format!("{:?}", arguments).as_bytes(),
    ])
}

fn associated_effect_row_projection_key(
    goal: &TraitGoal,
    name: &str,
    arguments: &[Type],
) -> Digest {
    Digest::of_parts([
        b"grandiose-stage0-associated-effect-row-projection-v1".as_slice(),
        goal.relation.definition.0.as_bytes().as_slice(),
        format!("{:?}", goal.relation.arguments).as_bytes(),
        format!("{:?}", goal.subject).as_bytes(),
        name.as_bytes(),
        format!("{:?}", arguments).as_bytes(),
    ])
}

/// A projection may be selected only after every part of its trait head is
/// known. This mirrors the Core boundary: type parameters retain projections
/// for their eventual lexical evidence environment instead of acquiring a
/// global implementation by accident.
fn projection_is_concrete(value: &Type) -> bool {
    match value {
        Type::Generic(_) | Type::Infer(_) | Type::Error => false,
        Type::Nominal { arguments, .. } | Type::Tuple(arguments) => {
            arguments.iter().all(projection_is_concrete)
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            projection_is_concrete(subject)
                && trait_arguments.iter().all(projection_is_concrete)
                && item_arguments.iter().all(projection_is_concrete)
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
