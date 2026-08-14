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

/// The one open tail permitted in a canonical effect row. Inference tails are
/// body-local; generic tails survive frozen signatures but must be instantiated
/// or proven closed before code generation.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum EffectTail {
    Infer(EffectVar),
    Generic(u32),
}

/// A canonical source-level lifetime.  Region inference will later refine
/// elided references into CFG-point sets, but frozen interfaces must already
/// preserve whether a reference used `'static`, a declaration binder, or
/// elision.  In particular, a lifetime may never be represented as a type
/// generic slot.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Lifetime {
    Static,
    Generic(u32),
    /// A rigid region introduced by a `for<'a>` callable binder. The index is
    /// local to the nearest enclosing [`Type::Callable`] binder list, making
    /// alpha-equivalent source spellings canonical while keeping this region
    /// distinct from declaration generics and inference/elision.
    Bound {
        /// Number of intervening higher-ranked callable binders between this
        /// use and its binder (de Bruijn depth).
        depth: u32,
        /// Position within that binder list.
        index: u32,
    },
    Elided,
}

/// The closed structural-constant domains admitted by the G1 frontend.
///
/// A const binder is deliberately not a [`Type::Generic`]: it may participate
/// in nominal identity and specialization, but cannot be used as a field,
/// parameter, or result type.  Value syntax and normalization are introduced
/// separately so this kind information is available at every frozen interface
/// boundary first.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum ConstKind {
    U32,
    Quantity,
}

/// A symbolic, checked `u32` const term.  The language deliberately keeps
/// const evaluation structural: this tree cannot call a function or inspect a
/// runtime value.  Terms are normalized at every interface boundary, so the
/// same arithmetic has one identity whether it was written in an alias,
/// associated item default, or a direct nominal application.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum StructuralU32Expr {
    Literal(u32),
    Param(u32),
    Add(Box<Self>, Box<Self>),
    Sub(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Div(Box<Self>, Box<Self>),
    Rem(Box<Self>, Box<Self>),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum StructuralConstError {
    OverflowOrDivisionByZero,
    ResourceLimit,
}

impl StructuralU32Expr {
    /// Normalize arithmetic deterministically.  Addition and multiplication
    /// are canonicalized in operand order after their checked literal folds;
    /// this keeps `N + 1` and `1 + N` identical without admitting arbitrary
    /// algebraic rewrites that could hide an overflow.
    pub fn normalized(self) -> Result<Self, StructuralConstError> {
        self.normalize_with_budget(&mut 1024)
    }

    fn normalize_with_budget(self, budget: &mut u32) -> Result<Self, StructuralConstError> {
        if *budget == 0 {
            return Err(StructuralConstError::ResourceLimit);
        }
        *budget -= 1;
        let binary = |left: Box<Self>,
                      right: Box<Self>,
                      op: fn(Box<Self>, Box<Self>) -> Self,
                      checked: fn(u32, u32) -> Option<u32>,
                      commutative: bool,
                      budget: &mut u32|
         -> Result<Self, StructuralConstError> {
            let mut left = left.normalize_with_budget(budget)?;
            let mut right = right.normalize_with_budget(budget)?;
            if let (Self::Literal(left), Self::Literal(right)) = (&left, &right) {
                return checked(*left, *right)
                    .map(Self::Literal)
                    .ok_or(StructuralConstError::OverflowOrDivisionByZero);
            }
            if commutative && structural_u32_expr_key(&right) < structural_u32_expr_key(&left) {
                std::mem::swap(&mut left, &mut right);
            }
            Ok(op(Box::new(left), Box::new(right)))
        };
        match self {
            Self::Literal(_) | Self::Param(_) => Ok(self),
            Self::Add(left, right) => {
                binary(left, right, Self::Add, u32::checked_add, true, budget)
            }
            Self::Sub(left, right) => {
                binary(left, right, Self::Sub, u32::checked_sub, false, budget)
            }
            Self::Mul(left, right) => {
                binary(left, right, Self::Mul, u32::checked_mul, true, budget)
            }
            Self::Div(left, right) => {
                binary(left, right, Self::Div, u32::checked_div, false, budget)
            }
            Self::Rem(left, right) => {
                binary(left, right, Self::Rem, u32::checked_rem, false, budget)
            }
        }
    }

    /// Replace declaration-local const binders and fold newly-ground
    /// arithmetic.  An unresolved binder remains symbolic, which is required
    /// for generic aliases and associated defaults.
    pub fn substitute(&self, arguments: &[GenericArgument]) -> Self {
        let term = match self {
            Self::Literal(value) => Self::Literal(*value),
            Self::Param(index) => match arguments.get(*index as usize) {
                Some(GenericArgument::ConstU32(value)) => Self::Literal(*value),
                Some(GenericArgument::ConstU32Expr(value)) => value.clone(),
                Some(GenericArgument::ConstGeneric {
                    index,
                    kind: ConstKind::U32,
                }) => Self::Param(*index),
                _ => Self::Param(*index),
            },
            Self::Add(left, right) => Self::Add(
                Box::new(left.substitute(arguments)),
                Box::new(right.substitute(arguments)),
            ),
            Self::Sub(left, right) => Self::Sub(
                Box::new(left.substitute(arguments)),
                Box::new(right.substitute(arguments)),
            ),
            Self::Mul(left, right) => Self::Mul(
                Box::new(left.substitute(arguments)),
                Box::new(right.substitute(arguments)),
            ),
            Self::Div(left, right) => Self::Div(
                Box::new(left.substitute(arguments)),
                Box::new(right.substitute(arguments)),
            ),
            Self::Rem(left, right) => Self::Rem(
                Box::new(left.substitute(arguments)),
                Box::new(right.substitute(arguments)),
            ),
        };
        // Existing source has already received a diagnostic for invalid
        // arithmetic.  Retaining the pre-normalized term here is preferable
        // to inventing a different fallback identity during substitution.
        term.clone().normalized().unwrap_or(term)
    }
}

fn structural_u32_expr_key(value: &StructuralU32Expr) -> Vec<u8> {
    let mut output = vec![];
    encode_structural_u32_expr(value, &mut output);
    output
}

fn encode_structural_u32_expr(value: &StructuralU32Expr, output: &mut Vec<u8>) {
    match value {
        StructuralU32Expr::Literal(value) => {
            output.push(0);
            output.extend_from_slice(&value.to_le_bytes());
        }
        StructuralU32Expr::Param(value) => {
            output.push(1);
            output.extend_from_slice(&value.to_le_bytes());
        }
        StructuralU32Expr::Add(left, right) => {
            output.push(2);
            encode_structural_u32_expr(left, output);
            encode_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Sub(left, right) => {
            output.push(3);
            encode_structural_u32_expr(left, output);
            encode_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Mul(left, right) => {
            output.push(4);
            encode_structural_u32_expr(left, output);
            encode_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Div(left, right) => {
            output.push(5);
            encode_structural_u32_expr(left, output);
            encode_structural_u32_expr(right, output);
        }
        StructuralU32Expr::Rem(left, right) => {
            output.push(6);
            encode_structural_u32_expr(left, output);
            encode_structural_u32_expr(right, output);
        }
    }
}

/// Kinds of source generic binders retained by callable signatures.  Keeping
/// these in source-slot order prevents a later phase from treating consts,
/// regions, or rows as ordinary type substitutions.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum GenericKind {
    Type,
    EffectRow,
    Lifetime,
    Const(ConstKind),
}

/// A canonical argument supplied to a declaration-level generic slot.
///
/// This is intentionally not `Type`: effect rows and lifetimes participate in
/// nominal/trait identity but may never be smuggled through the type namespace.
/// The existing `Type::Nominal` migration consumes this boundary incrementally.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum GenericArgument {
    Type(Type),
    EffectRow(EffectRow),
    Lifetime(Lifetime),
    ConstU32(u32),
    /// A normalized symbolic `u32` term retained until all const binders have
    /// been supplied.  Closed terms are always folded to `ConstU32`.
    ConstU32Expr(StructuralU32Expr),
    ConstQuantity(Quantity),
    ConstGeneric {
        index: u32,
        kind: ConstKind,
    },
}

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
    pub arguments: Vec<GenericArgument>,
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
        self.definition.cmp(&other.definition).then_with(|| {
            canonical_generic_arguments(&self.arguments)
                .cmp(&canonical_generic_arguments(&other.arguments))
        })
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
    pub tail: Option<EffectTail>,
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

    /// Put delayed associated effect-row projections into their canonical
    /// order. Named effects already live in a [`BTreeSet`], but projections
    /// may contain inference terms and therefore use a structural order key.
    /// Rows are sets of protocol terms, so exact duplicate projections are
    /// removed as well.
    pub fn canonicalize(&mut self) {
        self.projections.sort_by_key(effect_row_projection_key);
        self.projections.dedup();
    }

    pub fn canonicalized(mut self) -> Self {
        self.canonicalize();
        self
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Type {
    Unit,
    Never,
    Scalar(ScalarType),
    Nominal {
        definition: DefKey,
        /// Nominal identity spans every declared generic kind. Keeping rows,
        /// lifetimes, and structural constants here prevents a source slot
        /// from being erased merely because its runtime layout is type-only.
        arguments: Vec<GenericArgument>,
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
        lifetime: Lifetime,
        referent: Box<Type>,
    },
    Callable {
        /// The number of higher-ranked lifetime binders that scope this
        /// callable's parameter/result tree. Bound lifetimes use their
        /// position in this binder list, so their identity is alpha-stable.
        lifetime_binders: u32,
        parameters: Vec<Type>,
        result: Box<Type>,
        effects: EffectRow,
        invocation: Quantity,
    },
    /// A normalized structural `u32` supplied to a const generic slot. This
    /// is an argument term, not a standalone source type; header elaboration
    /// enforces that it only occupies a `ConstKind::U32` slot.
    ConstU32(u32),
    /// A normalized structural quantity interval supplied to a const generic
    /// slot. Like `ConstU32`, it is an identity-only argument term.
    ConstQuantity(Quantity),
    /// A const binder occurrence retained in a nominal identity.  It shares
    /// the owner-local source slot numbering with other generic kinds, while
    /// its explicit kind prevents type substitution from accepting it.
    ConstGeneric {
        index: u32,
        kind: ConstKind,
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
    UnresolvedGenericEffectRow(u32),
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
            tail: Some(EffectTail::Infer(variable)),
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
            (Type::ConstU32(left), Type::ConstU32(right)) if left == right => {
                Ok(Type::ConstU32(left))
            }
            (Type::ConstQuantity(left), Type::ConstQuantity(right)) if left == right => {
                Ok(Type::ConstQuantity(left))
            }
            (
                Type::ConstGeneric {
                    index: left_index,
                    kind: left_kind,
                },
                Type::ConstGeneric {
                    index: right_index,
                    kind: right_kind,
                },
            ) if left_index == right_index && left_kind == right_kind => Ok(Type::ConstGeneric {
                index: left_index,
                kind: left_kind,
            }),
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
                arguments: self.unify_generic_arguments(left_arguments, right_arguments)?,
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
                    lifetime: left_lifetime,
                    referent: left,
                },
                Type::Reference {
                    mutability: right_mutability,
                    lifetime: right_lifetime,
                    referent: right,
                },
            ) if left_mutability == right_mutability && left_lifetime == right_lifetime => {
                Ok(Type::Reference {
                    mutability: left_mutability,
                    lifetime: left_lifetime,
                    referent: Box::new(self.unify(*left, *right)?),
                })
            }
            (
                Type::Callable {
                    lifetime_binders: left_binders,
                    parameters: left_parameters,
                    result: left_result,
                    effects: left_effects,
                    invocation: left_invocation,
                },
                Type::Callable {
                    lifetime_binders: right_binders,
                    parameters: right_parameters,
                    result: right_result,
                    effects: right_effects,
                    invocation: right_invocation,
                },
            ) if left_binders == right_binders && left_invocation == right_invocation => {
                let effects = self.unify_effect_rows(left_effects, right_effects)?;
                Ok(Type::Callable {
                    lifetime_binders: left_binders,
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
                    .map(|argument| self.zonk_generic_argument(argument))
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
                lifetime,
                referent,
            } => Ok(Type::Reference {
                mutability,
                lifetime,
                referent: Box::new(self.zonk(*referent)?),
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
                    .map(|parameter| self.zonk(parameter))
                    .collect::<Result<_, _>>()?,
                result: Box::new(self.zonk(*result)?),
                // A callable type can legitimately retain a declaration-owned
                // row binder while it is nested in a generic body.  The row
                // itself is closed only when that callable is invoked or an
                // executable interface is finalized.
                effects: self.zonk_effects_allowing_generic_tail(effects)?,
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
        let effects = self.zonk_effects_allowing_generic_tail(effects)?;
        if let Some(EffectTail::Generic(index)) = effects.tail {
            return Err(TypeError::UnresolvedGenericEffectRow(index));
        }
        Ok(effects)
    }

    /// Resolve inference-owned pieces of a row without treating a declared
    /// row-polymorphic binder as an unresolved inference hole.  Body checking
    /// uses this before comparing a callee's symbolic outward row with its
    /// caller's declared symbolic row; persistence boundaries still use
    /// [`Self::zonk_effects`] and therefore require a closed row.
    pub fn zonk_effects_allowing_generic_tail(
        &mut self,
        effects: EffectRow,
    ) -> Result<EffectRow, TypeError> {
        let effects = self.resolve_effects(effects);
        if let Some(EffectTail::Infer(variable)) = effects.tail {
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
                            .map(|argument| self.zonk_generic_argument(argument))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, _>>()?,
            projections: effects
                .projections
                .into_iter()
                .map(|projection| {
                    Ok(EffectRowProjection {
                        subject: Box::new(self.zonk(*projection.subject)?),
                        trait_definition: projection.trait_definition,
                        trait_arguments: projection
                            .trait_arguments
                            .into_iter()
                            .map(|argument| self.zonk(argument))
                            .collect::<Result<_, _>>()?,
                        name: projection.name,
                        item_arguments: projection
                            .item_arguments
                            .into_iter()
                            .map(|argument| self.zonk(argument))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, _>>()?,
            tail: effects.tail,
        }
        .canonicalized())
    }

    /// Constrain `required` to be admitted by `allowed`.  Closed rows use
    /// ordinary set inclusion; an inference-owned required tail is solved to
    /// the remaining allowed row, while declaration-owned generic tails stay
    /// rigid.  This gives callers a precise subset relation without silently
    /// erasing projections or mixed-kind effect arguments.
    pub fn constrain_effect_subset(
        &mut self,
        required: EffectRow,
        allowed: EffectRow,
    ) -> Result<EffectRow, TypeError> {
        let required = self.resolve_effects(required).canonicalized();
        let allowed = self.resolve_effects(allowed).canonicalized();
        let (required_only, allowed_only) =
            self.partition_effect_instances(&required.effects, &allowed.effects)?;
        if !required_only.is_empty() {
            return Err(TypeError::EffectRow {
                expected: allowed,
                found: required,
            });
        }
        let Some(projections) = self.constrain_effect_row_projections(
            required.projections.clone(),
            allowed.projections.clone(),
        )?
        else {
            return Err(TypeError::EffectRow {
                expected: allowed,
                found: required,
            });
        };
        match (required.tail, allowed.tail) {
            (None, _) => Ok(EffectRow {
                effects: required.effects,
                projections,
                tail: None,
            }
            .canonicalized()),
            (Some(EffectTail::Generic(left)), Some(EffectTail::Generic(right)))
                if left == right =>
            {
                Ok(EffectRow {
                    effects: required.effects,
                    projections,
                    tail: Some(EffectTail::Generic(left)),
                }
                .canonicalized())
            }
            (Some(EffectTail::Infer(variable)), tail) => {
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: allowed_only,
                        projections: allowed.projections,
                        tail,
                    },
                )?;
                Ok(EffectRow {
                    effects: required.effects,
                    projections,
                    tail: Some(EffectTail::Infer(variable)),
                }
                .canonicalized())
            }
            _ => Err(TypeError::EffectRow {
                expected: allowed,
                found: required,
            }),
        }
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

    fn unify_generic_arguments(
        &mut self,
        left: Vec<GenericArgument>,
        right: Vec<GenericArgument>,
    ) -> Result<Vec<GenericArgument>, TypeError> {
        if left.len() != right.len() {
            return Err(TypeError::Arity {
                expected: left.len(),
                found: right.len(),
            });
        }
        left.into_iter()
            .zip(right)
            .map(|(left, right)| match (left, right) {
                (GenericArgument::Type(left), GenericArgument::Type(right)) => {
                    self.unify(left, right).map(GenericArgument::Type)
                }
                (left, right) if left == right => Ok(left),
                _ => Err(TypeError::Mismatch {
                    expected: Box::new(Type::Error),
                    found: Box::new(Type::Error),
                }),
            })
            .collect()
    }

    fn unify_effect_rows(
        &mut self,
        left: EffectRow,
        right: EffectRow,
    ) -> Result<EffectRow, TypeError> {
        let left = self.resolve_effects(left).canonicalized();
        let right = self.resolve_effects(right).canonicalized();
        if left == right {
            return Ok(left);
        }
        let (left_only, right_only) =
            self.partition_effect_instances(&left.effects, &right.effects)?;
        let Some(projections) =
            self.unify_effect_row_projections(left.projections.clone(), right.projections.clone())?
        else {
            return Err(TypeError::EffectRow {
                expected: left,
                found: right,
            });
        };
        match (left.tail, right.tail) {
            (None, None) if left_only.is_empty() && right_only.is_empty() => Ok(EffectRow {
                effects: left.effects.union(&right.effects).cloned().collect(),
                projections,
                tail: None,
            }
            .canonicalized()),
            (None, None) => Err(TypeError::EffectRow {
                expected: left,
                found: right,
            }),
            (Some(EffectTail::Infer(variable)), None) if left_only.is_empty() => {
                self.bind_effect(variable, EffectRow::closed_instances(right_only))?;
                Ok(right)
            }
            (None, Some(EffectTail::Infer(variable))) if right_only.is_empty() => {
                self.bind_effect(variable, EffectRow::closed_instances(left_only))?;
                Ok(left)
            }
            (Some(EffectTail::Infer(variable)), Some(EffectTail::Infer(other)))
                if variable == other =>
            {
                Ok(EffectRow {
                    effects: left.effects.union(&right.effects).cloned().collect(),
                    projections,
                    tail: Some(EffectTail::Infer(variable)),
                }
                .canonicalized())
            }
            (Some(EffectTail::Infer(variable)), Some(EffectTail::Infer(other))) => {
                let remainder = self.fresh_effects();
                let Some(EffectTail::Infer(tail)) = remainder.tail else {
                    unreachable!("fresh effect row has an inference tail")
                };
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: right_only,
                        projections: vec![],
                        tail: Some(EffectTail::Infer(tail)),
                    },
                )?;
                self.bind_effect(
                    other,
                    EffectRow {
                        effects: left_only,
                        projections: vec![],
                        tail: Some(EffectTail::Infer(tail)),
                    },
                )?;
                Ok(EffectRow {
                    effects: left.effects.union(&right.effects).cloned().collect(),
                    projections,
                    tail: Some(EffectTail::Infer(tail)),
                }
                .canonicalized())
            }
            _ => Err(TypeError::EffectRow {
                expected: left,
                found: right,
            }),
        }
    }

    /// Unify the symbolic terms in two rows just as rigorously as ordinary
    /// effect instances.  Projection identity is determined by its selected
    /// associated item (trait, name, and arities), while its subject and type
    /// arguments remain regular inference terms.  Requiring `Eq` here used to
    /// reject `<T as Capability>::Effects` against the same projection after
    /// `T` had been inferred to a concrete type.
    ///
    /// Returning `None` means the two rows name different projection sets;
    /// the caller turns that into the row-level mismatch diagnostic.  A type
    /// mismatch inside otherwise matching projections is intentionally kept
    /// as its more precise [`TypeError::Mismatch`].
    fn unify_effect_row_projections(
        &mut self,
        left: Vec<EffectRowProjection>,
        right: Vec<EffectRowProjection>,
    ) -> Result<Option<Vec<EffectRowProjection>>, TypeError> {
        if left.len() != right.len() {
            return Ok(None);
        }
        let mut unmatched = right;
        let mut unified = Vec::with_capacity(left.len());
        for left_projection in left {
            let Some(index) = unmatched.iter().position(|right_projection| {
                left_projection.trait_definition == right_projection.trait_definition
                    && left_projection.name == right_projection.name
                    && left_projection.trait_arguments.len()
                        == right_projection.trait_arguments.len()
                    && left_projection.item_arguments.len() == right_projection.item_arguments.len()
            }) else {
                return Ok(None);
            };
            let right_projection = unmatched.remove(index);
            unified.push(EffectRowProjection {
                subject: Box::new(self.unify(*left_projection.subject, *right_projection.subject)?),
                trait_definition: left_projection.trait_definition,
                trait_arguments: self.unify_many(
                    left_projection.trait_arguments,
                    right_projection.trait_arguments,
                )?,
                name: left_projection.name,
                item_arguments: self.unify_many(
                    left_projection.item_arguments,
                    right_projection.item_arguments,
                )?,
            });
        }
        Ok(Some(unified))
    }

    fn constrain_effect_row_projections(
        &mut self,
        required: Vec<EffectRowProjection>,
        allowed: Vec<EffectRowProjection>,
    ) -> Result<Option<Vec<EffectRowProjection>>, TypeError> {
        let mut unmatched = allowed;
        let mut unified = Vec::with_capacity(required.len());
        for required_projection in required {
            let Some(index) = unmatched.iter().position(|candidate| {
                candidate.trait_definition == required_projection.trait_definition
                    && candidate.name == required_projection.name
                    && candidate.trait_arguments.len() == required_projection.trait_arguments.len()
                    && candidate.item_arguments.len() == required_projection.item_arguments.len()
            }) else {
                return Ok(None);
            };
            let allowed_projection = unmatched.remove(index);
            unified.push(EffectRowProjection {
                subject: Box::new(
                    self.unify(*required_projection.subject, *allowed_projection.subject)?,
                ),
                trait_definition: required_projection.trait_definition,
                trait_arguments: self.unify_many(
                    required_projection.trait_arguments,
                    allowed_projection.trait_arguments,
                )?,
                name: required_projection.name,
                item_arguments: self.unify_many(
                    required_projection.item_arguments,
                    allowed_projection.item_arguments,
                )?,
            });
        }
        Ok(Some(unified))
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
                        .all(|(left, right)| self.generic_arguments_may_unify(left, right))
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
            let _ = self.unify_generic_arguments(
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
                    .all(|(left, right)| self.generic_arguments_may_unify(left, right))
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
                    lifetime: left_lifetime,
                    referent: left_referent,
                },
                Type::Reference {
                    mutability: right_mutability,
                    lifetime: right_lifetime,
                    referent: right_referent,
                },
            ) if left_mutability == right_mutability && left_lifetime == right_lifetime => {
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
        if value.tail == Some(EffectTail::Infer(variable)) && value.effects.is_empty() {
            return Ok(());
        }
        if self.effect_occurs(variable, &value) {
            return Err(TypeError::EffectOccurs(variable, value));
        }
        self.effect_bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    fn resolve_effects(&mut self, effects: EffectRow) -> EffectRow {
        let Some(EffectTail::Infer(variable)) = effects.tail else {
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
        effects.tail == Some(EffectTail::Infer(variable))
    }

    fn occurs(&mut self, variable: InferVar, value: &Type) -> bool {
        match self.resolve(value.clone()) {
            Type::Infer(found) => found == variable,
            Type::Nominal { arguments, .. } => arguments
                .iter()
                .any(|argument| self.generic_argument_occurs(variable, argument)),
            Type::Tuple(arguments) => arguments
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

    fn generic_arguments_may_unify(
        &mut self,
        left: &GenericArgument,
        right: &GenericArgument,
    ) -> bool {
        match (left, right) {
            (GenericArgument::Type(left), GenericArgument::Type(right)) => {
                self.types_may_unify(left, right)
            }
            _ => left == right,
        }
    }

    fn zonk_generic_argument(
        &mut self,
        argument: GenericArgument,
    ) -> Result<GenericArgument, TypeError> {
        match argument {
            GenericArgument::Type(value) => self.zonk(value).map(GenericArgument::Type),
            GenericArgument::EffectRow(value) => self
                .zonk_effects_allowing_generic_tail(value)
                .map(GenericArgument::EffectRow),
            argument => Ok(argument),
        }
    }

    fn generic_argument_occurs(&mut self, variable: InferVar, argument: &GenericArgument) -> bool {
        match argument {
            GenericArgument::Type(value) => self.occurs(variable, value),
            GenericArgument::EffectRow(value) => {
                value.effects.iter().any(|effect| {
                    effect
                        .arguments
                        .iter()
                        .any(|argument| self.generic_argument_occurs(variable, argument))
                }) || value.projections.iter().any(|projection| {
                    self.occurs(variable, &projection.subject)
                        || projection
                            .trait_arguments
                            .iter()
                            .any(|argument| self.occurs(variable, argument))
                        || projection
                            .item_arguments
                            .iter()
                            .any(|argument| self.occurs(variable, argument))
                })
            }
            GenericArgument::Lifetime(_)
            | GenericArgument::ConstU32(_)
            | GenericArgument::ConstU32Expr(_)
            | GenericArgument::ConstQuantity(_)
            | GenericArgument::ConstGeneric { .. } => false,
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
            encode_generic_arguments(arguments, output);
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
            lifetime,
            referent,
        } => {
            output.push(6);
            output.push(match mutability {
                Mutability::Shared => 0,
                Mutability::Unique => 1,
            });
            output.push(match lifetime {
                Lifetime::Static => 0,
                Lifetime::Generic(_) => 1,
                Lifetime::Bound { .. } => 2,
                Lifetime::Elided => 3,
            });
            if let Lifetime::Generic(index) = lifetime {
                output.extend_from_slice(&index.to_le_bytes());
            }
            if let Lifetime::Bound { depth, index } = lifetime {
                output.extend_from_slice(&depth.to_le_bytes());
                output.extend_from_slice(&index.to_le_bytes());
            }
            encode_type(referent, output);
        }
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => {
            output.push(7);
            output.extend_from_slice(&lifetime_binders.to_le_bytes());
            encode_types(parameters, output);
            encode_type(result, output);
            output.extend_from_slice(&(effects.effects.len() as u64).to_le_bytes());
            for effect in &effects.effects {
                output.extend_from_slice(&effect.definition.0.as_bytes());
                encode_generic_arguments(&effect.arguments, output);
            }
            output.extend_from_slice(&(effects.projections.len() as u64).to_le_bytes());
            for projection in &effects.projections {
                encode_type(&projection.subject, output);
                output.extend_from_slice(&projection.trait_definition.0.as_bytes());
                encode_types(&projection.trait_arguments, output);
                output.extend_from_slice(&(projection.name.len() as u64).to_le_bytes());
                output.extend_from_slice(projection.name.as_bytes());
                encode_types(&projection.item_arguments, output);
            }
            match effects.tail {
                Some(EffectTail::Infer(variable)) => {
                    output.push(0);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                Some(EffectTail::Generic(index)) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
                None => output.push(2),
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
        Type::ConstU32(value) => {
            output.push(12);
            output.extend_from_slice(&value.to_le_bytes());
        }
        Type::ConstQuantity(value) => {
            output.push(14);
            output.extend_from_slice(&value.lower.to_le_bytes());
            match value.upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        Type::ConstGeneric { index, kind } => {
            output.push(13);
            output.extend_from_slice(&index.to_le_bytes());
            output.push(match kind {
                ConstKind::U32 => 0,
                ConstKind::Quantity => 1,
            });
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

/// Tagged canonical encoding for a type tree.  Internal identity consumers
/// use this instead of `Debug` rendering so nested nominal arguments retain
/// their type/lifetime/effect-row/const/quantity kinds.
pub(crate) fn canonical_type_encoding(value: &Type) -> Vec<u8> {
    let mut bytes = vec![];
    encode_type(value, &mut bytes);
    bytes
}

/// Tagged canonical encoding for declaration argument sequences.
pub(crate) fn canonical_generic_arguments_encoding(values: &[GenericArgument]) -> Vec<u8> {
    let mut bytes = vec![];
    encode_generic_arguments(values, &mut bytes);
    bytes
}

fn canonical_generic_arguments(values: &[GenericArgument]) -> Vec<u8> {
    canonical_generic_arguments_encoding(values)
}

fn effect_row_projection_key(value: &EffectRowProjection) -> Vec<u8> {
    let mut bytes = vec![];
    encode_type(&value.subject, &mut bytes);
    bytes.extend_from_slice(&value.trait_definition.0.as_bytes());
    encode_types(&value.trait_arguments, &mut bytes);
    bytes.extend_from_slice(&(value.name.len() as u64).to_le_bytes());
    bytes.extend_from_slice(value.name.as_bytes());
    encode_types(&value.item_arguments, &mut bytes);
    bytes
}

fn encode_types(values: &[Type], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_type(value, output);
    }
}

fn encode_generic_arguments(values: &[GenericArgument], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_generic_argument(value, output);
    }
}

fn encode_generic_argument(value: &GenericArgument, output: &mut Vec<u8>) {
    match value {
        GenericArgument::Type(value) => {
            output.push(0);
            encode_type(value, output);
        }
        GenericArgument::EffectRow(value) => {
            output.push(1);
            output.extend_from_slice(&(value.effects.len() as u64).to_le_bytes());
            for effect in &value.effects {
                output.extend_from_slice(&effect.definition.0.as_bytes());
                encode_generic_arguments(&effect.arguments, output);
            }
            output.extend_from_slice(&(value.projections.len() as u64).to_le_bytes());
            for projection in &value.projections {
                output.extend_from_slice(&effect_row_projection_key(projection));
            }
            match value.tail {
                Some(EffectTail::Infer(variable)) => {
                    output.push(0);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                Some(EffectTail::Generic(index)) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
                None => output.push(2),
            }
        }
        GenericArgument::Lifetime(value) => {
            output.push(2);
            match value {
                Lifetime::Static => output.push(0),
                Lifetime::Generic(index) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Bound { depth, index } => {
                    output.push(2);
                    output.extend_from_slice(&depth.to_le_bytes());
                    output.extend_from_slice(&index.to_le_bytes());
                }
                Lifetime::Elided => output.push(3),
            }
        }
        GenericArgument::ConstU32(value) => {
            output.push(3);
            output.extend_from_slice(&value.to_le_bytes());
        }
        GenericArgument::ConstU32Expr(value) => {
            output.push(6);
            encode_structural_u32_expr(value, output);
        }
        GenericArgument::ConstQuantity(value) => {
            output.push(4);
            output.extend_from_slice(&value.lower.to_le_bytes());
            match value.upper {
                Some(upper) => {
                    output.push(0);
                    output.extend_from_slice(&upper.to_le_bytes());
                }
                None => output.push(1),
            }
        }
        GenericArgument::ConstGeneric { index, kind } => {
            output.push(5);
            output.extend_from_slice(&index.to_le_bytes());
            output.push(match kind {
                ConstKind::U32 => 0,
                ConstKind::Quantity => 1,
            });
        }
    }
}
