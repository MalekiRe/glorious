//! Canonical semantic types and body-local inference.
//!
//! Fully resolved types use stable nominal keys; uncertainty is confined to an
//! `InferContext` owned by one body elaboration. No backend or diagnostic phase
//! creates a parallel type vocabulary.

use std::{cmp::Ordering, collections::BTreeSet};

use crate::{
    identity::{DefKey, Digest},
    quantity::Quantity,
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferVar(pub u32);

/// An inference variable in an effect row. This is deliberately not a
/// `InferVar`: a type hole can never accidentally escape as an effect tail.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EffectVar(pub u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mutability {
    Shared,
    Unique,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ScalarType {
    Bool,
    U8,
    U16,
    U32,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Usize,
    Isize,
    F32,
    F64,
    Char,
    Text,
    Bytes,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectInstance {
    pub definition: DefKey,
    /// Protocol arguments are part of the nominal effect identity.  A row
    /// containing `State<i64>` is therefore distinct from `State<Text>`.
    pub arguments: Vec<Type>,
}

/// A delayed associated effect-row normalization. This is deliberately a row
/// term rather than a [`Type`] so effect declarations cannot be confused with
/// values or accidentally sent to a runtime backend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectRowProjection {
    pub subject: Box<Type>,
    pub trait_definition: DefKey,
    pub trait_arguments: Vec<Type>,
    pub name: String,
    pub item_arguments: Vec<Type>,
}

impl Ord for EffectInstance {
    fn cmp(&self, other: &Self) -> Ordering {
        self.definition
            .cmp(&other.definition)
            .then_with(|| canonical_types(&self.arguments).cmp(&canonical_types(&other.arguments)))
    }
}

impl PartialOrd for EffectInstance {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EffectRow {
    pub effects: BTreeSet<EffectInstance>,
    /// Symbolic associated effect-row terms. They are normalized by the trait
    /// solver before a callable can become executable.
    pub projections: Vec<EffectRowProjection>,
    /// Body-local row variable. It may not cross into a frozen interface or
    /// Typed Core product before elaboration has resolved it.
    pub tail: Option<EffectVar>,
}

impl EffectRow {
    pub fn closed(effects: impl IntoIterator<Item = DefKey>) -> Self {
        Self::closed_instances(effects.into_iter().map(|definition| EffectInstance {
            definition,
            arguments: vec![],
        }))
    }

    pub fn closed_instances(effects: impl IntoIterator<Item = EffectInstance>) -> Self {
        Self {
            effects: effects.into_iter().collect(),
            projections: vec![],
            tail: None,
        }
    }

    pub fn empty() -> Self {
        Self::closed([])
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Unit,
    Never,
    Scalar(ScalarType),
    Nominal {
        definition: DefKey,
        arguments: Vec<Type>,
    },
    /// A delayed associated-type normalization. Generic interfaces retain this
    /// term until a concrete trait goal can select implementation evidence.
    Projection {
        subject: Box<Type>,
        trait_definition: DefKey,
        trait_arguments: Vec<Type>,
        name: String,
        item_arguments: Vec<Type>,
    },
    Tuple(Vec<Type>),
    Array(Box<Type>),
    Reference {
        mutability: Mutability,
        referent: Box<Type>,
    },
    Callable {
        parameters: Vec<Type>,
        result: Box<Type>,
        effects: EffectRow,
        invocation: Quantity,
    },
    Generic(u32),
    Infer(InferVar),
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TypeError {
    Mismatch {
        expected: Box<Type>,
        found: Box<Type>,
    },
    Arity {
        expected: usize,
        found: usize,
    },
    Occurs(InferVar, Box<Type>),
    EffectRow {
        expected: EffectRow,
        found: EffectRow,
    },
    EffectOccurs(EffectVar, EffectRow),
    UnresolvedEffect(EffectVar),
    Unresolved(InferVar),
}

#[derive(Clone, Debug, Default)]
pub struct InferContext {
    bindings: Vec<Option<Type>>,
    effect_bindings: Vec<Option<EffectRow>>,
}

impl InferContext {
    pub fn fresh(&mut self) -> Type {
        let variable = InferVar(
            u32::try_from(self.bindings.len()).expect("inference variable arena exceeds G1 range"),
        );
        self.bindings.push(None);
        Type::Infer(variable)
    }

    /// Create one body-local open effect row. Frozen interfaces and Typed Core
    /// must call `zonk_effects` before they can retain it.
    pub fn fresh_effects(&mut self) -> EffectRow {
        let variable = EffectVar(
            u32::try_from(self.effect_bindings.len())
                .expect("effect inference variable arena exceeds G1 range"),
        );
        self.effect_bindings.push(None);
        EffectRow {
            effects: BTreeSet::new(),
            projections: vec![],
            tail: Some(variable),
        }
    }

    pub fn unify(&mut self, left: Type, right: Type) -> Result<Type, TypeError> {
        let left = self.resolve(left);
        let right = self.resolve(right);
        match (left, right) {
            (Type::Infer(variable), value) | (value, Type::Infer(variable)) => {
                self.bind(variable, value.clone())?;
                Ok(value)
            }
            // A terminal computation has no normal value, so it is valid in
            // every expected result position without forcing that position to
            // become `Never`. This is the bottom-type rule used by terminal
            // effects, handlers, and source-defined nonlocal control.
            (Type::Never, value) | (value, Type::Never) => Ok(value),
            (Type::Unit, Type::Unit) => Ok(Type::Unit),
            (Type::Scalar(left), Type::Scalar(right)) if left == right => Ok(Type::Scalar(left)),
            (Type::Generic(left), Type::Generic(right)) if left == right => Ok(Type::Generic(left)),
            (Type::Error, _) | (_, Type::Error) => Ok(Type::Error),
            (
                Type::Nominal {
                    definition: left,
                    arguments: left_arguments,
                },
                Type::Nominal {
                    definition: right,
                    arguments: right_arguments,
                },
            ) if left == right => Ok(Type::Nominal {
                definition: left,
                arguments: self.unify_many(left_arguments, right_arguments)?,
            }),
            (
                Type::Projection {
                    subject: left_subject,
                    trait_definition: left_trait,
                    trait_arguments: left_arguments,
                    name: left_name,
                    item_arguments: left_item_arguments,
                },
                Type::Projection {
                    subject: right_subject,
                    trait_definition: right_trait,
                    trait_arguments: right_arguments,
                    name: right_name,
                    item_arguments: right_item_arguments,
                },
            ) if left_trait == right_trait && left_name == right_name => Ok(Type::Projection {
                subject: Box::new(self.unify(*left_subject, *right_subject)?),
                trait_definition: left_trait,
                trait_arguments: self.unify_many(left_arguments, right_arguments)?,
                name: left_name,
                item_arguments: self.unify_many(left_item_arguments, right_item_arguments)?,
            }),
            (Type::Tuple(left), Type::Tuple(right)) => {
                Ok(Type::Tuple(self.unify_many(left, right)?))
            }
            (Type::Array(left), Type::Array(right)) => {
                Ok(Type::Array(Box::new(self.unify(*left, *right)?)))
            }
            (
                Type::Reference {
                    mutability: left_mutability,
                    referent: left,
                },
                Type::Reference {
                    mutability: right_mutability,
                    referent: right,
                },
            ) if left_mutability == right_mutability => Ok(Type::Reference {
                mutability: left_mutability,
                referent: Box::new(self.unify(*left, *right)?),
            }),
            (
                Type::Callable {
                    parameters: left_parameters,
                    result: left_result,
                    effects: left_effects,
                    invocation: left_invocation,
                },
                Type::Callable {
                    parameters: right_parameters,
                    result: right_result,
                    effects: right_effects,
                    invocation: right_invocation,
                },
            ) if left_invocation == right_invocation => {
                let effects = self.unify_effect_rows(left_effects, right_effects)?;
                Ok(Type::Callable {
                    parameters: self.unify_many(left_parameters, right_parameters)?,
                    result: Box::new(self.unify(*left_result, *right_result)?),
                    effects,
                    invocation: left_invocation,
                })
            }
            (expected, found) => Err(TypeError::Mismatch {
                expected: Box::new(expected),
                found: Box::new(found),
            }),
        }
    }

    pub fn zonk(&mut self, value: Type) -> Result<Type, TypeError> {
        match self.resolve(value) {
            Type::Infer(variable) => Err(TypeError::Unresolved(variable)),
            Type::Nominal {
                definition,
                arguments,
            } => Ok(Type::Nominal {
                definition,
                arguments: arguments
                    .into_iter()
                    .map(|argument| self.zonk(argument))
                    .collect::<Result<_, _>>()?,
            }),
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
            } => Ok(Type::Projection {
                subject: Box::new(self.zonk(*subject)?),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.zonk(argument))
                    .collect::<Result<_, _>>()?,
                name,
                item_arguments: item_arguments
                    .into_iter()
                    .map(|argument| self.zonk(argument))
                    .collect::<Result<_, _>>()?,
            }),
            Type::Tuple(elements) => Ok(Type::Tuple(
                elements
                    .into_iter()
                    .map(|element| self.zonk(element))
                    .collect::<Result<_, _>>()?,
            )),
            Type::Array(element) => Ok(Type::Array(Box::new(self.zonk(*element)?))),
            Type::Reference {
                mutability,
                referent,
            } => Ok(Type::Reference {
                mutability,
                referent: Box::new(self.zonk(*referent)?),
            }),
            Type::Callable {
                parameters,
                result,
                effects,
                invocation,
            } => Ok(Type::Callable {
                parameters: parameters
                    .into_iter()
                    .map(|parameter| self.zonk(parameter))
                    .collect::<Result<_, _>>()?,
                result: Box::new(self.zonk(*result)?),
                effects: self.zonk_effects(effects)?,
                invocation,
            }),
            value => Ok(value),
        }
    }

    /// Freeze a body type at a persistence boundary. Inference holes and open
    /// effect rows are rejected rather than receiving an allocation-dependent
    /// fingerprint.
    pub fn type_fingerprint(&mut self, value: Type) -> Result<Digest, TypeError> {
        let value = self.zonk(value)?;
        let mut bytes = Vec::new();
        encode_type(&value, &mut bytes);
        Ok(Digest::of_parts([
            b"grandiose-stage0-type-v1".as_slice(),
            &bytes,
        ]))
    }

    pub fn zonk_effects(&mut self, effects: EffectRow) -> Result<EffectRow, TypeError> {
        let effects = self.resolve_effects(effects);
        if let Some(variable) = effects.tail {
            return Err(TypeError::UnresolvedEffect(variable));
        }
        Ok(EffectRow {
            effects: effects
                .effects
                .into_iter()
                .map(|effect| {
                    Ok(EffectInstance {
                        definition: effect.definition,
                        arguments: effect
                            .arguments
                            .into_iter()
                            .map(|argument| self.zonk(argument))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, _>>()?,
            projections: effects.projections,
            tail: None,
        })
    }

    fn unify_many(&mut self, left: Vec<Type>, right: Vec<Type>) -> Result<Vec<Type>, TypeError> {
        if left.len() != right.len() {
            return Err(TypeError::Arity {
                expected: left.len(),
                found: right.len(),
            });
        }
        left.into_iter()
            .zip(right)
            .map(|(left, right)| self.unify(left, right))
            .collect()
    }

    fn unify_effect_rows(
        &mut self,
        left: EffectRow,
        right: EffectRow,
    ) -> Result<EffectRow, TypeError> {
        let left = self.resolve_effects(left);
        let right = self.resolve_effects(right);
        if left == right {
            return Ok(left);
        }
        let (left_only, right_only) =
            self.partition_effect_instances(&left.effects, &right.effects)?;
        if !left.projections.is_empty() || !right.projections.is_empty() {
            return Err(TypeError::EffectRow {
                expected: left,
                found: right,
            });
        }
        match (left.tail, right.tail) {
            (None, None) if left_only.is_empty() && right_only.is_empty() => Ok(EffectRow {
                effects: left.effects.union(&right.effects).cloned().collect(),
                projections: vec![],
                tail: None,
            }),
            (None, None) => Err(TypeError::EffectRow {
                expected: left,
                found: right,
            }),
            (Some(variable), None) if left_only.is_empty() => {
                self.bind_effect(variable, EffectRow::closed_instances(right_only))?;
                Ok(right)
            }
            (None, Some(variable)) if right_only.is_empty() => {
                self.bind_effect(variable, EffectRow::closed_instances(left_only))?;
                Ok(left)
            }
            (Some(variable), Some(other)) if variable == other => Ok(EffectRow {
                effects: left.effects.union(&right.effects).cloned().collect(),
                projections: vec![],
                tail: Some(variable),
            }),
            (Some(variable), Some(other)) => {
                let remainder = self.fresh_effects();
                let tail = remainder.tail.expect("fresh effect row is open");
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: right_only,
                        projections: vec![],
                        tail: Some(tail),
                    },
                )?;
                self.bind_effect(
                    other,
                    EffectRow {
                        effects: left_only,
                        projections: vec![],
                        tail: Some(tail),
                    },
                )?;
                Ok(EffectRow {
                    effects: left.effects.union(&right.effects).cloned().collect(),
                    projections: vec![],
                    tail: Some(tail),
                })
            }
            _ => Err(TypeError::EffectRow {
                expected: left,
                found: right,
            }),
        }
    }

    fn bind(&mut self, variable: InferVar, value: Type) -> Result<(), TypeError> {
        if value == Type::Infer(variable) {
            return Ok(());
        }
        if self.occurs(variable, &value) {
            return Err(TypeError::Occurs(variable, Box::new(value)));
        }
        self.bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    /// Partition two effect-instance sets after unifying the arguments of a
    /// uniquely identifiable common protocol. Set equality alone is too weak
    /// here: `State<α>` and `State<i64>` name the same protocol occurrence
    /// once normal type inference has bound `α`.
    fn partition_effect_instances(
        &mut self,
        left: &BTreeSet<EffectInstance>,
        right: &BTreeSet<EffectInstance>,
    ) -> Result<(BTreeSet<EffectInstance>, BTreeSet<EffectInstance>), TypeError> {
        let right_values = right.iter().collect::<Vec<_>>();
        let mut used_right = vec![false; right_values.len()];
        let mut left_only = BTreeSet::new();
        for effect in left {
            let mut candidates = vec![];
            for (index, other) in right_values.iter().enumerate() {
                if !used_right[index]
                    && effect.definition == other.definition
                    && effect.arguments.len() == other.arguments.len()
                    && effect
                        .arguments
                        .iter()
                        .zip(&other.arguments)
                        .all(|(left, right)| self.types_may_unify(left, right))
                {
                    candidates.push(index);
                }
            }
            // Multiple instances of one protocol in a row need the full row
            // solver's explicit evidence search. Do not guess a pairing.
            if candidates.len() != 1 {
                left_only.insert(effect.clone());
                continue;
            }
            let index = candidates[0];
            self.unify_many(
                effect.arguments.clone(),
                right_values[index].arguments.clone(),
            )?;
            used_right[index] = true;
        }
        let right_only = right_values
            .into_iter()
            .enumerate()
            .filter(|(index, _)| !used_right[*index])
            .map(|(_, effect)| effect.clone())
            .collect();
        Ok((left_only, right_only))
    }

    fn types_may_unify(&mut self, left: &Type, right: &Type) -> bool {
        match (self.resolve(left.clone()), self.resolve(right.clone())) {
            (Type::Infer(_), _) | (_, Type::Infer(_)) | (Type::Error, _) | (_, Type::Error) => true,
            (
                Type::Nominal {
                    definition: left_definition,
                    arguments: left_arguments,
                },
                Type::Nominal {
                    definition: right_definition,
                    arguments: right_arguments,
                },
            ) if left_definition == right_definition
                && left_arguments.len() == right_arguments.len() =>
            {
                left_arguments
                    .iter()
                    .zip(&right_arguments)
                    .all(|(left, right)| self.types_may_unify(left, right))
            }
            (
                Type::Projection {
                    subject: left_subject,
                    trait_definition: left_trait,
                    trait_arguments: left_arguments,
                    name: left_name,
                    item_arguments: left_item_arguments,
                },
                Type::Projection {
                    subject: right_subject,
                    trait_definition: right_trait,
                    trait_arguments: right_arguments,
                    name: right_name,
                    item_arguments: right_item_arguments,
                },
            ) if left_trait == right_trait
                && left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_item_arguments.len() == right_item_arguments.len() =>
            {
                self.types_may_unify(&left_subject, &right_subject)
                    && left_arguments
                        .iter()
                        .zip(&right_arguments)
                        .chain(left_item_arguments.iter().zip(&right_item_arguments))
                        .all(|(left, right)| self.types_may_unify(left, right))
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => left
                .iter()
                .zip(&right)
                .all(|(left, right)| self.types_may_unify(left, right)),
            (Type::Array(left), Type::Array(right)) => self.types_may_unify(&left, &right),
            (
                Type::Reference {
                    mutability: left_mutability,
                    referent: left_referent,
                },
                Type::Reference {
                    mutability: right_mutability,
                    referent: right_referent,
                },
            ) if left_mutability == right_mutability => {
                self.types_may_unify(&left_referent, &right_referent)
            }
            (left, right) => left == right,
        }
    }

    fn resolve(&mut self, value: Type) -> Type {
        let Type::Infer(variable) = value else {
            return value;
        };
        let Some(binding) = self.bindings[variable.0 as usize].clone() else {
            return Type::Infer(variable);
        };
        let resolved = self.resolve(binding);
        self.bindings[variable.0 as usize] = Some(resolved.clone());
        resolved
    }

    fn bind_effect(&mut self, variable: EffectVar, value: EffectRow) -> Result<(), TypeError> {
        if value.tail == Some(variable) && value.effects.is_empty() {
            return Ok(());
        }
        if self.effect_occurs(variable, &value) {
            return Err(TypeError::EffectOccurs(variable, value));
        }
        self.effect_bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    fn resolve_effects(&mut self, effects: EffectRow) -> EffectRow {
        let Some(variable) = effects.tail else {
            return effects;
        };
        let Some(binding) = self.effect_bindings[variable.0 as usize].clone() else {
            return effects;
        };
        let binding = self.resolve_effects(binding);
        self.effect_bindings[variable.0 as usize] = Some(binding.clone());
        EffectRow {
            effects: effects.effects.union(&binding.effects).cloned().collect(),
            projections: effects
                .projections
                .into_iter()
                .chain(binding.projections)
                .collect(),
            tail: binding.tail,
        }
    }

    fn effect_occurs(&mut self, variable: EffectVar, effects: &EffectRow) -> bool {
        let effects = self.resolve_effects(effects.clone());
        effects.tail == Some(variable)
    }

    fn occurs(&mut self, variable: InferVar, value: &Type) -> bool {
        match self.resolve(value.clone()) {
            Type::Infer(found) => found == variable,
            Type::Nominal { arguments, .. } | Type::Tuple(arguments) => arguments
                .iter()
                .any(|argument| self.occurs(variable, argument)),
            Type::Projection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            } => {
                self.occurs(variable, &subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.occurs(variable, argument))
                    || item_arguments
                        .iter()
                        .any(|argument| self.occurs(variable, argument))
            }
            Type::Array(element)
            | Type::Reference {
                referent: element, ..
            } => self.occurs(variable, &element),
            Type::Callable {
                parameters, result, ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| self.occurs(variable, parameter))
                    || self.occurs(variable, &result)
            }
            _ => false,
        }
    }
}

fn encode_type(value: &Type, output: &mut Vec<u8>) {
    match value {
        Type::Unit => output.push(0),
        Type::Never => output.push(1),
        Type::Scalar(scalar) => {
            output.push(2);
            output.push(match scalar {
                ScalarType::Bool => 17,
                ScalarType::U8 => 0,
                ScalarType::U16 => 1,
                ScalarType::U32 => 2,
                ScalarType::U64 => 3,
                ScalarType::U128 => 4,
                ScalarType::I8 => 5,
                ScalarType::I16 => 6,
                ScalarType::I32 => 7,
                ScalarType::I64 => 8,
                ScalarType::I128 => 9,
                ScalarType::Usize => 10,
                ScalarType::Isize => 11,
                ScalarType::F32 => 12,
                ScalarType::F64 => 13,
                ScalarType::Char => 14,
                ScalarType::Text => 15,
                ScalarType::Bytes => 16,
            });
        }
        Type::Nominal {
            definition,
            arguments,
        } => {
            output.push(3);
            output.extend_from_slice(&definition.0.as_bytes());
            encode_types(arguments, output);
        }
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => {
            output.push(11);
            encode_type(subject, output);
            output.extend_from_slice(&trait_definition.0.as_bytes());
            encode_types(trait_arguments, output);
            output.extend_from_slice(&(name.len() as u64).to_le_bytes());
            output.extend_from_slice(name.as_bytes());
            encode_types(item_arguments, output);
        }
        Type::Tuple(elements) => {
            output.push(4);
            encode_types(elements, output);
        }
        Type::Array(element) => {
            output.push(5);
            encode_type(element, output);
        }
        Type::Reference {
            mutability,
            referent,
        } => {
            output.push(6);
            output.push(match mutability {
                Mutability::Shared => 0,
                Mutability::Unique => 1,
            });
            encode_type(referent, output);
        }
        Type::Callable {
            parameters,
            result,
            effects,
            invocation,
        } => {
            output.push(7);
            encode_types(parameters, output);
            encode_type(result, output);
            output.extend_from_slice(&(effects.effects.len() as u64).to_le_bytes());
            for effect in &effects.effects {
                output.extend_from_slice(&effect.definition.0.as_bytes());
                encode_types(&effect.arguments, output);
            }
            match effects.tail {
                Some(variable) => {
                    output.push(0);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                None => output.push(1),
            }
            output.extend_from_slice(&invocation.lower.to_le_bytes());
            match invocation.upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        Type::Generic(index) => {
            output.push(8);
            output.extend_from_slice(&index.to_le_bytes());
        }
        // Effect-instance ordering is also used while elaborating recovered
        // source. These encodings are deterministic body-local order keys;
        // persistence callers still reject unresolved inference through
        // `InferContext::zonk` before accepting a product.
        Type::Infer(variable) => {
            output.push(9);
            output.extend_from_slice(&variable.0.to_le_bytes());
        }
        Type::Error => output.push(10),
    }
}

fn canonical_types(values: &[Type]) -> Vec<u8> {
    let mut bytes = vec![];
    encode_types(values, &mut bytes);
    bytes
}

fn encode_types(values: &[Type], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_type(value, output);
    }
}
