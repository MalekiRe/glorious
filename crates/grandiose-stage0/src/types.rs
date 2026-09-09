//! Canonical semantic types and body-local inference.
//!
//! Fully resolved types use stable nominal keys; uncertainty is confined to an
//! `InferContext` owned by one body elaboration. No backend or diagnostic phase
//! creates a parallel type vocabulary.

use std::{cmp::Ordering, collections::{BTreeMap, BTreeSet}};

use crate::{
    identity::{DefKey, Digest},
    quantity::Quantity,
};

pub mod integer_const;
pub(crate) mod regions;
mod universes;
pub(crate) use universes::UniversalScope;

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct InferVar(pub u32);

#[cfg(test)]
mod numeric_constraint_tests {
    use super::*;

    #[test]
    fn known_numeric_context_wins_before_defaults_in_either_order() {
        for context_first in [false, true] {
            let mut inference = InferContext::default();
            let literal = inference.fresh();
            let usize_type = Type::Scalar(ScalarType::Usize);
            if context_first {
                inference.unify(literal.clone(), usize_type.clone()).unwrap();
            }
            inference.constrain_numeric(literal.clone(), false).unwrap();
            if !context_first {
                assert!(matches!(inference.zonk(literal.clone()), Err(TypeError::Unresolved(_))));
                inference.unify(literal.clone(), usize_type.clone()).unwrap();
            }
            inference.finish_numeric_defaults().unwrap();
            assert_eq!(inference.zonk(literal).unwrap(), usize_type);
        }
    }

    #[test]
    fn merged_literal_classes_default_independently_of_union_direction() {
        for reverse in [false, true] {
            let mut inference = InferContext::default();
            let integer = inference.fresh();
            let floating = inference.fresh();
            inference.constrain_numeric(integer.clone(), false).unwrap();
            inference.constrain_numeric(floating.clone(), true).unwrap();
            let (left, right) = if reverse { (&floating, &integer) } else { (&integer, &floating) };
            inference.unify(left.clone(), right.clone()).unwrap();
            inference.finish_numeric_defaults().unwrap();
            assert_eq!(inference.zonk(integer).unwrap(), Type::Scalar(ScalarType::F64));
            assert_eq!(inference.zonk(floating).unwrap(), Type::Scalar(ScalarType::F64));
        }
    }

    #[test]
    fn numeric_constraints_reject_wrong_domains_without_poisoning_the_hole() {
        let mut inference = InferContext::default();
        let literal = inference.fresh();
        inference.constrain_numeric(literal.clone(), true).unwrap();
        for wrong in [Type::Unit, Type::Scalar(ScalarType::Bool), Type::Scalar(ScalarType::Usize)] {
            assert!(inference.unify(literal.clone(), wrong).is_err());
        }
        inference.unify(literal.clone(), Type::Scalar(ScalarType::F32)).unwrap();
        inference.finish_numeric_defaults().unwrap();
        assert_eq!(inference.zonk(literal).unwrap(), Type::Scalar(ScalarType::F32));
    }

    #[test]
    fn only_numeric_holes_receive_defaults() {
        let mut inference = InferContext::default();
        let integer = inference.fresh();
        let ordinary = inference.fresh();
        inference.constrain_numeric(integer.clone(), false).unwrap();
        inference.finish_numeric_defaults().unwrap();
        inference.finish_numeric_defaults().unwrap();
        assert_eq!(inference.zonk(integer).unwrap(), Type::Scalar(ScalarType::I64));
        assert!(matches!(inference.zonk(ordinary), Err(TypeError::Unresolved(_))));
    }
}

pub use grandiose_compiler_base::Safety;

/// A body-local structural-constant hole.  Const generics have their own
/// finite domains and must not borrow either the type or effect-row variable
/// spaces.  Just like [`InferVar`], this identity is allocation-local and is
/// rejected before a frozen product is accepted.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct ConstInferVar(pub u32);

/// A body-local lifetime hole, distinct from both declaration binders and
/// resolved elision. It must be solved before a semantic product is frozen.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct LifetimeInferVar(pub u32);

/// An inference variable in an effect row. This is deliberately not a
/// `InferVar`: a type hole can never accidentally escape as an effect tail.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct EffectVar(pub u32);

/// One operand of an open effect-row union. Inference tails are
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
    Infer(LifetimeInferVar),
    Static,
    Generic(u32),
    /// A fresh rigid region used only while checking a universal predicate.
    /// This is not a declaration slot or a serializable source region.
    Placeholder(UniversalRegion),
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

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct UniversalRegion {
    pub(crate) universe: u32,
    pub(crate) index: u32,
}

/// The closed structural-constant domains admitted by the G1 frontend.
///
/// A const binder is deliberately not a [`Type::Generic`]: it may participate
/// in nominal identity and specialization, but cannot be used as a field,
/// parameter, or result type.  Value syntax and normalization are introduced
/// separately so this kind information is available at every frozen interface
/// boundary first.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
#[repr(u8)]
pub enum ConstKind {
    U32,
    Quantity,
    U8,
    U16,
    U64,
    U128,
    I8,
    I16,
    I32,
    I64,
    I128,
    Usize,
    Isize,
}

impl ConstKind {
    pub fn name(self) -> &'static str {
        match self {
            Self::U32 => "u32", Self::Quantity => "Quantity",
            Self::U8 => "u8", Self::U16 => "u16", Self::U64 => "u64",
            Self::U128 => "u128", Self::I8 => "i8", Self::I16 => "i16",
            Self::I32 => "i32", Self::I64 => "i64", Self::I128 => "i128",
            Self::Usize => "usize", Self::Isize => "isize",
        }
    }
    pub fn tag(self) -> u8 { self as u8 }

    pub fn from_tag(tag: u8) -> Option<Self> {
        Some(match tag {
            0 => Self::U32, 1 => Self::Quantity, 2 => Self::U8,
            3 => Self::U16, 4 => Self::U64, 5 => Self::U128,
            6 => Self::I8, 7 => Self::I16, 8 => Self::I32,
            9 => Self::I64, 10 => Self::I128, 11 => Self::Usize,
            12 => Self::Isize, _ => return None,
        })
    }

    pub fn integer_scalar(self) -> Option<ScalarType> {
        Some(match self {
            Self::U8 => ScalarType::U8, Self::U16 => ScalarType::U16,
            Self::U32 => ScalarType::U32, Self::U64 => ScalarType::U64,
            Self::U128 => ScalarType::U128, Self::I8 => ScalarType::I8,
            Self::I16 => ScalarType::I16, Self::I32 => ScalarType::I32,
            Self::I64 => ScalarType::I64, Self::I128 => ScalarType::I128,
            Self::Usize => ScalarType::Usize, Self::Isize => ScalarType::Isize,
            Self::Quantity => return None,
        })
    }

    pub fn from_integer_name(name: &str) -> Option<Self> {
        Some(match name {
            "u8" => Self::U8, "u16" => Self::U16, "u32" => Self::U32,
            "u64" => Self::U64, "u128" => Self::U128, "i8" => Self::I8,
            "i16" => Self::I16, "i32" => Self::I32, "i64" => Self::I64,
            "i128" => Self::I128, "usize" => Self::Usize, "isize" => Self::Isize,
            _ => return None,
        })
    }

    pub fn from_integer_scalar(scalar: ScalarType) -> Option<Self> {
        Some(match scalar {
            ScalarType::U8 => Self::U8, ScalarType::U16 => Self::U16,
            ScalarType::U32 => Self::U32, ScalarType::U64 => Self::U64,
            ScalarType::U128 => Self::U128, ScalarType::Usize => Self::Usize,
            ScalarType::I8 => Self::I8, ScalarType::I16 => Self::I16,
            ScalarType::I32 => Self::I32, ScalarType::I64 => Self::I64,
            ScalarType::I128 => Self::I128, ScalarType::Isize => Self::Isize,
            _ => return None,
        })
    }
}

/// Typed structural integer terms share the checked const-normalization kernel.
pub use integer_const::{IntegerConst, IntegerConstError as StructuralConstError, IntegerConstExpr};

fn encode_structural_integer_expr(value: &IntegerConstExpr, output: &mut Vec<u8>) {
    value.encode(output);
}

/// Freeze a normalized integer term into its unique generic-argument form.
/// Invalid substitutions remain errors, never a fabricated zero value.
pub(crate) fn integer_const_argument(value: Result<IntegerConstExpr, StructuralConstError>) -> GenericArgument {
    match value {
        Ok(IntegerConstExpr::Literal(value)) => GenericArgument::ConstInteger(value),
        Ok(IntegerConstExpr::Param { index, scalar }) => match ConstKind::from_integer_scalar(scalar) {
            Some(kind) => GenericArgument::ConstGeneric { index, kind },
            None => GenericArgument::Type(Type::Error),
        },
        Ok(value) => GenericArgument::ConstIntegerExpr(value),
        Err(_) => GenericArgument::Type(Type::Error),
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

impl GenericKind {
    pub fn tag(self) -> u8 {
        match self {
            Self::Type => 0, Self::EffectRow => 1, Self::Lifetime => 2,
            Self::Const(kind) => 3 + kind.tag(),
        }
    }

    pub fn from_tag(tag: u8) -> Option<Self> {
        Some(match tag {
            0 => Self::Type, 1 => Self::EffectRow, 2 => Self::Lifetime,
            _ => Self::Const(ConstKind::from_tag(tag.checked_sub(3)?)?),
        })
    }
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
    ConstInteger(integer_const::IntegerConst),
    /// A normalized, kind-preserving integer term retained until all const
    /// binders have been supplied. Closed terms fold to `ConstInteger`.
    ConstIntegerExpr(IntegerConstExpr),
    ConstQuantity(Quantity),
    ConstGeneric {
        index: u32,
        kind: ConstKind,
    },
    /// An omitted const argument on a generic invocation.  This is only
    /// produced by body elaboration; source binders remain
    /// [`Self::ConstGeneric`] and therefore rigid.  Keeping the declared
    /// kind at the variable itself makes a `u32` hole impossible to bind to a
    /// quantity term even during error recovery.
    ConstInfer {
        variable: ConstInferVar,
        kind: ConstKind,
    },
    /// A delayed associated structural-constant normalization.  This is the
    /// const-kinded counterpart of [`Type::Projection`]: a public generic
    /// contract may require `Array<T, <T as Width>::Value>` before `T` has a
    /// concrete implementation.  Keeping the full mixed-kind trait head
    /// prevents that contract from being erased into a fake type argument.
    ConstProjection {
        subject: Box<Type>,
        trait_definition: DefKey,
        trait_arguments: Vec<GenericArgument>,
        name: String,
        kind: ConstKind,
    },
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Mutability {
    Shared,
    Unique,
}

/// Raw pointer access permission, not a borrowing or ownership guarantee.
/// In particular, `Mut` does not assert uniqueness and copying either pointer
/// does not copy, move, or destroy its pointee.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PointerMutability {
    Const,
    Mut,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
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
    /// The enclosing trait application is an identity-bearing mixed-kind
    /// substitution.  In particular, a delayed row projection must not turn
    /// an effect-row or lifetime argument into a type-shaped placeholder.
    pub trait_arguments: Vec<GenericArgument>,
    pub name: String,
    /// The associated effect-row item's own binders, distinct from the
    /// enclosing trait arguments and preserved with their identity kinds.
    pub item_generic_kinds: Vec<GenericKind>,
    pub item_arguments: Vec<GenericArgument>,
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
    /// Independent row operands, with stable ordering and duplicate removal.
    /// Inference-owned operands must resolve before a persistence boundary.
    pub tails: std::collections::BTreeSet<EffectTail>,
}

impl EffectRow {
    /// Union rows without equating their independent operands.
    pub fn extend(&mut self, row: Self) {
        self.effects.extend(row.effects);
        self.projections.extend(row.projections);
        self.tails.extend(row.tails);
        self.canonicalize();
    }

    /// Substitution is simultaneous: returned rows belong to the caller's
    /// binder space and must not be substituted again using callee indices.
    pub fn substitute_tails(&mut self, mut substitute: impl FnMut(EffectTail) -> Option<Self>) {
        for tail in std::mem::take(&mut self.tails) {
            if let Some(row) = substitute(tail) {
                self.extend(row);
            } else {
                self.tails.insert(tail);
            }
        }
        self.canonicalize();
    }
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
            tails: Default::default(),
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
        /// The enclosing trait application carries every declared argument
        /// kind.  Keeping this distinct from the associated item's own GAT
        /// application makes `<T as Trait<'a, R>>::Item<N>` canonical rather
        /// than silently lossy at the frozen Core boundary.
        trait_arguments: Vec<GenericArgument>,
        name: String,
        /// Declaration-owned kinds for the associated item's binders. The
        /// Every item argument retains its declared identity kind. This is
        /// separate from the trait's own arguments because GAT binders are
        /// introduced by the associated item, not its enclosing trait.
        item_generic_kinds: Vec<GenericKind>,
        item_arguments: Vec<GenericArgument>,
    },
    Tuple(Vec<Type>),
    Array(Box<Type>),
    /// Inline homogeneous product. Length is a usize-kinded structural const,
    /// including inference and projection terms until specialization seals it.
    FixedArray { element: Box<Type>, length: Box<GenericArgument> },
    /// Compiler-created immutable data embedded in the artifact. This type is
    /// deliberately not expressible in source: it is the sealed backing for
    /// literals and trusted standard-library leaves, not a public slice type.
    StaticData {
        element: Box<Type>,
        tag: u128,
        alignment: u32,
    },
    Reference {
        mutability: Mutability,
        lifetime: Lifetime,
        referent: Box<Type>,
    },
    RawPointer {
        mutability: PointerMutability,
        pointee: Box<Type>,
    },
    Callable {
        safety: Safety,
        /// The number of higher-ranked lifetime binders that scope this
        /// callable's parameter/result tree. Bound lifetimes use their
        /// position in this binder list, so their identity is alpha-stable.
        lifetime_binders: u32,
        parameters: Vec<Type>,
        result: Box<Type>,
        effects: EffectRow,
        invocation: Quantity,
    },
    /// A normalized structural integer supplied to a const generic slot. This
    /// is an argument term, not a standalone source type; header elaboration
    /// enforces that its integer kind matches the declared const slot.
    ConstInteger(integer_const::IntegerConst),
    /// A normalized structural quantity interval supplied to a const generic
    /// slot. Like `ConstInteger`, it is an identity-only argument term.
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

impl Type {
    pub(crate) fn fixed_array(element: Type, count: u64) -> Self {
        Self::FixedArray { element: Box::new(element), length: Box::new(GenericArgument::ConstInteger(
            IntegerConst::new(ScalarType::Usize, false, u128::from(count), 64)
                .expect("u64 count is representable by the stage0 usize target"))) }
    }

    pub(crate) fn fixed_array_length(&self) -> Option<u64> {
        let Self::FixedArray { length, .. } = self else { return None; };
        match length.as_ref() {
            GenericArgument::ConstInteger(value) if value.kind() == ConstKind::Usize => value.array_length(64).ok(),
            _ => None,
        }
    }

    pub(crate) fn array_element(&self) -> Option<&Type> {
        match self {
            Self::Array(element) | Self::FixedArray { element, .. } => Some(element),
            _ => None,
        }
    }

    pub(crate) fn array_accepts_pattern(&self, count: usize, rest: Option<crate::pattern::ArrayPatternRest>) -> bool {
        (rest.is_none() || matches!(self, Self::FixedArray { .. }))
            && crate::pattern::ArrayPatternRest::length(rest, count).is_some_and(|count| self.array_accepts_count(count))
    }

    pub(crate) fn array_accepts_count(&self, count: usize) -> bool {
        matches!(self, Self::Array(_)) || self.fixed_array_length() == u64::try_from(count).ok()
    }
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
    AmbiguousEffectUnion { left: EffectRow, right: EffectRow },
    EffectOccurs(EffectVar, EffectRow),
    UnresolvedEffect(EffectVar),
    UnresolvedGenericEffectRow(u32),
    Unresolved(InferVar),
    UnresolvedConst(ConstInferVar),
    UnresolvedLifetime(LifetimeInferVar),
    LifetimeMismatch { expected: Lifetime, found: Lifetime },
    EscapingUniversalRegion(UniversalRegion),
    InvalidUniversalScope,
}

#[derive(Clone, Debug, Default)]
pub struct InferContext {
    bindings: Vec<Option<Type>>,
    /// Numeric evidence is a constraint on a type variable, not an eager
    /// binding to i64/f64. Roots merge this evidence before defaulting.
    numeric_constraints: BTreeMap<InferVar, bool>,
    effect_bindings: Vec<Option<EffectRow>>,
    pending_effect_equalities: Vec<(EffectRow, EffectRow)>,
    solving_effect_equalities: bool,
    const_bindings: Vec<Option<GenericArgument>>,
    lifetime_bindings: Vec<Option<Lifetime>>,
    /// Body elaboration may inspect partially constrained constructor types.
    /// Sealing ends this phase and resolves unconstrained elision holes.
    pending_body_lifetimes: bool,
    next_universe: u32,
    active_universes: Vec<u32>,
    /// A private partial-zonk mode used only by transactional leak checking.
    checking_universe_leaks: Option<u32>,
    freezing_types: bool,
}

impl InferContext {
    pub(crate) fn has_numeric_constraint(&self, mut value: Type) -> bool {
        while let Type::Infer(variable) = value {
            match &self.bindings[variable.0 as usize] {
                Some(binding) => value = binding.clone(),
                None => return self.numeric_constraints.contains_key(&variable),
            }
        }
        false
    }
    /// Constrain a literal's type without choosing its default. Integer
    /// literals admit integer or floating scalar contexts; floating literals
    /// require floating contexts. `floating` describes the source literal,
    /// not a conversion of an already typed value.
    pub fn constrain_numeric(&mut self, value: Type, floating: bool) -> Result<Type, TypeError> {
        let value = self.resolve(value);
        match &value {
            Type::Infer(variable) => {
                self.numeric_constraints.entry(*variable)
                    .and_modify(|required_float| *required_float |= floating)
                    .or_insert(floating);
            }
            Type::Generic(_) | Type::Error => {}
            Type::Scalar(scalar) if matches!(scalar, ScalarType::F32 | ScalarType::F64)
                || (!floating && matches!(scalar,
                    ScalarType::U8 | ScalarType::U16 | ScalarType::U32 | ScalarType::U64
                    | ScalarType::U128 | ScalarType::Usize | ScalarType::I8 | ScalarType::I16
                    | ScalarType::I32 | ScalarType::I64 | ScalarType::I128 | ScalarType::Isize)) => {}
            _ => return Err(TypeError::Mismatch {
                expected: Box::new(Type::Scalar(if floating { ScalarType::F64 } else { ScalarType::I64 })),
                found: Box::new(value),
            }),
        }
        Ok(value)
    }

    /// Finish numeric inference only after the caller has supplied all
    /// non-defaultable constraints. Ordinary unconstrained type variables
    /// remain unresolved; this is not a general inference fallback.
    pub fn finish_numeric_defaults(&mut self) -> Result<(), TypeError> {
        let constraints = self.numeric_constraints.clone();
        // `bind` transfers evidence to the surviving root. Resolve again so
        // bindings supplied since the last literal are checked as well.
        for (variable, floating) in constraints {
            self.constrain_numeric(Type::Infer(variable), floating)?;
        }
        let constraints = self.numeric_constraints.clone();
        for (variable, floating) in constraints {
            if let Type::Infer(root) = self.resolve(Type::Infer(variable)) {
                let floating = floating || self.numeric_constraints.get(&root).copied().unwrap_or(false);
                self.bind(root, Type::Scalar(if floating { ScalarType::F64 } else { ScalarType::I64 }))?;
            }
        }
        Ok(())
    }

    pub(crate) fn for_body() -> Self {
        Self { pending_body_lifetimes: true, ..Self::default() }
    }

    pub fn fresh_lifetime(&mut self) -> Lifetime {
        let variable = LifetimeInferVar(u32::try_from(self.lifetime_bindings.len())
            .expect("lifetime inference variable arena exceeds G1 range"));
        self.lifetime_bindings.push(None);
        Lifetime::Infer(variable)
    }

    pub fn resolve_lifetime(&mut self, lifetime: Lifetime) -> Result<Lifetime, TypeError> {
        let Lifetime::Infer(variable) = lifetime else { return Ok(lifetime); };
        let binding = self.lifetime_bindings.get(variable.0 as usize)
            .copied().ok_or(TypeError::UnresolvedLifetime(variable))?;
        match binding {
            None => Ok(lifetime),
            Some(bound) => {
                let resolved = self.resolve_lifetime(bound)?;
                self.lifetime_bindings[variable.0 as usize] = Some(resolved);
                Ok(resolved)
            }
        }
    }

    pub(crate) fn unify_lifetimes(&mut self, left: Lifetime, right: Lifetime) -> Result<Lifetime, TypeError> {
        let left = self.resolve_lifetime(left)?;
        let right = self.resolve_lifetime(right)?;
        if left == right { return Ok(left); }
        match (left, right) {
            (Lifetime::Infer(variable), value) | (value, Lifetime::Infer(variable)) => {
                self.lifetime_bindings[variable.0 as usize] = Some(value);
                Ok(value)
            }
            _ => Err(TypeError::LifetimeMismatch { expected: left, found: right }),
        }
    }

    fn zonk_lifetime(&mut self, value: Lifetime) -> Result<Lifetime, TypeError> {
        match self.resolve_lifetime(value)? {
            Lifetime::Infer(variable) if !self.pending_body_lifetimes && self.checking_universe_leaks.is_none() => Err(TypeError::UnresolvedLifetime(variable)),
            Lifetime::Placeholder(region) if self.freezing_types
                || !self.active_universes.contains(&region.universe)
                || self.checking_universe_leaks.is_some_and(|universe| region.universe >= universe) =>
                Err(TypeError::EscapingUniversalRegion(region)),
            value => Ok(value),
        }
    }

    /// Only constructor holes lacking any field/context evidence use ordinary
    /// elision. Named declaration regions are never generalized or rebound.
    pub(crate) fn finish_body_lifetimes(&mut self) {
        for binding in &mut self.lifetime_bindings {
            if binding.is_none() { *binding = Some(Lifetime::Elided); }
        }
        self.pending_body_lifetimes = false;
    }

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
            tails: [EffectTail::Infer(variable)].into_iter().collect(),
        }
    }

    /// Create one native-domain structural-constant hole for an omitted
    /// generic callable argument.  It deliberately returns a
    /// [`GenericArgument`] because consts cannot inhabit ordinary type slots.
    pub fn fresh_const(&mut self, kind: ConstKind) -> GenericArgument {
        let variable = ConstInferVar(
            u32::try_from(self.const_bindings.len())
                .expect("const inference variable arena exceeds G1 range"),
        );
        self.const_bindings.push(None);
        GenericArgument::ConstInfer { variable, kind }
    }

    /// Turn the unresolved type variables reachable from a deliberately
    /// polymorphic value boundary into declaration-owned generic binders.
    ///
    /// This is intentionally narrower than ordinary zonking: call sites and
    /// executable function bodies must still reject unconstrained inference.
    /// A top-level value initializer is different: it is evaluated once, and
    /// a type variable that occurs only in its outward result is a parametric
    /// value (for example `Result::Err(()) : Option<T>`), not an ambiguous
    /// executable choice.  Binding the variables in this context also makes
    /// the subsequent Core seal rewrite every occurrence consistently.
    pub fn generalize_result_type(
        &mut self,
        value: Type,
    ) -> Result<(Type, Vec<GenericKind>), TypeError> {
        // Numeric literals are defaultable scalar choices, not parametric
        // values that can be generalized over every possible type.
        self.finish_numeric_defaults()?;
        let mut variables = BTreeSet::new();
        self.collect_unresolved_type_variables(value.clone(), &mut variables)?;
        let variables = variables.into_iter().collect::<Vec<_>>();
        for (index, variable) in variables.iter().enumerate() {
            self.bindings[variable.0 as usize] = Some(Type::Generic(index as u32));
        }
        let value = self.zonk(value)?;
        Ok((value, vec![GenericKind::Type; variables.len()]))
    }

    fn collect_unresolved_type_variables(
        &mut self,
        value: Type,
        variables: &mut BTreeSet<InferVar>,
    ) -> Result<(), TypeError> {
        match self.resolve(value) {
            Type::Infer(variable) => {
                variables.insert(variable);
                Ok(())
            }
            Type::Nominal { arguments, .. } => arguments.into_iter().try_for_each(|argument| {
                self.collect_generic_argument_variables(argument, variables)
            }),
            Type::Projection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            } => {
                self.collect_unresolved_type_variables(*subject, variables)?;
                trait_arguments.into_iter().try_for_each(|argument| {
                    self.collect_generic_argument_variables(argument, variables)
                })?;
                item_arguments.into_iter().try_for_each(|argument| {
                    self.collect_generic_argument_variables(argument, variables)
                })
            }
            Type::Tuple(values) => values
                .into_iter()
                .try_for_each(|value| self.collect_unresolved_type_variables(value, variables)),
            Type::Array(value) => self.collect_unresolved_type_variables(*value, variables),
            Type::FixedArray { element, length } => {
                self.collect_unresolved_type_variables(*element, variables)?;
                self.collect_generic_argument_variables(*length, variables)
            }
            Type::StaticData { element, .. } => {
                self.collect_unresolved_type_variables(*element, variables)
            }
            Type::Reference { referent, .. }
            | Type::RawPointer { pointee: referent, .. } => {
                self.collect_unresolved_type_variables(*referent, variables)
            }
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters.into_iter().try_for_each(|parameter| {
                    self.collect_unresolved_type_variables(parameter, variables)
                })?;
                self.collect_unresolved_type_variables(*result, variables)?;
                self.collect_effect_variables(effects, variables)
            }
            _ => Ok(()),
        }
    }

    fn collect_generic_argument_variables(
        &mut self,
        argument: GenericArgument,
        variables: &mut BTreeSet<InferVar>,
    ) -> Result<(), TypeError> {
        match argument {
            GenericArgument::Type(value) => {
                self.collect_unresolved_type_variables(value, variables)
            }
            GenericArgument::EffectRow(value) => self.collect_effect_variables(value, variables),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.collect_unresolved_type_variables(*subject, variables)?;
                trait_arguments.into_iter().try_for_each(|argument| {
                    self.collect_generic_argument_variables(argument, variables)
                })
            }
            _ => Ok(()),
        }
    }

    fn collect_effect_variables(
        &mut self,
        effects: EffectRow,
        variables: &mut BTreeSet<InferVar>,
    ) -> Result<(), TypeError> {
        if let Some(variable) = effects.tails.iter().find_map(|tail| match tail {
            EffectTail::Infer(variable) => Some(*variable), _ => None,
        }) {
            return Err(TypeError::UnresolvedEffect(variable));
        }
        for effect in effects.effects {
            for argument in effect.arguments {
                self.collect_generic_argument_variables(argument, variables)?;
            }
        }
        for projection in effects.projections {
            self.collect_unresolved_type_variables(*projection.subject, variables)?;
            for argument in projection.trait_arguments {
                self.collect_generic_argument_variables(argument, variables)?;
            }
            for argument in projection.item_arguments {
                self.collect_generic_argument_variables(argument, variables)?;
            }
        }
        Ok(())
    }

    pub fn unify(&mut self, left: Type, right: Type) -> Result<Type, TypeError> {
        let left = self.resolve(left);
        let right = self.resolve(right);
        match (left, right) {
            // A terminal computation has no normal value, so it is valid in
            // every expected result position without forcing that position to
            // become `Never`. This is the bottom-type rule used by terminal
            // effects, handlers, and source-defined nonlocal control.
            (Type::Never, value) | (value, Type::Never) => Ok(value),
            (Type::Infer(variable), value) | (value, Type::Infer(variable)) => {
                self.bind(variable, value.clone())?;
                Ok(value)
            }
            (Type::Unit, Type::Unit) => Ok(Type::Unit),
            (Type::Scalar(left), Type::Scalar(right)) if left == right => Ok(Type::Scalar(left)),
            (Type::ConstInteger(left), Type::ConstInteger(right)) if left == right => {
                Ok(Type::ConstInteger(left))
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
                    item_generic_kinds: left_item_kinds,
                    item_arguments: left_item_arguments,
                },
                Type::Projection {
                    subject: right_subject,
                    trait_definition: right_trait,
                    trait_arguments: right_arguments,
                    name: right_name,
                    item_generic_kinds: right_item_kinds,
                    item_arguments: right_item_arguments,
                },
            ) if left_trait == right_trait
                && left_name == right_name
                && left_item_kinds == right_item_kinds =>
            {
                Ok(Type::Projection {
                    subject: Box::new(self.unify(*left_subject, *right_subject)?),
                    trait_definition: left_trait,
                    trait_arguments: self
                        .unify_generic_arguments(left_arguments, right_arguments)?,
                    name: left_name,
                    item_generic_kinds: left_item_kinds,
                    item_arguments: self
                        .unify_generic_arguments(left_item_arguments, right_item_arguments)?,
                })
            }
            (Type::Tuple(left), Type::Tuple(right)) => {
                Ok(Type::Tuple(self.unify_many(left, right)?))
            }
            (Type::Array(left), Type::Array(right)) => {
                Ok(Type::Array(Box::new(self.unify(*left, *right)?)))
            }
            (Type::FixedArray { element: left, length: ln }, Type::FixedArray { element: right, length: rn }) => {
                Ok(Type::FixedArray { element: Box::new(self.unify(*left, *right)?),
                    length: Box::new(self.unify_generic_arguments(vec![*ln], vec![*rn])?.remove(0)) })
            }
            (
                Type::RawPointer { mutability: left_mutability, pointee: left },
                Type::RawPointer { mutability: right_mutability, pointee: right },
            ) if left_mutability == right_mutability => Ok(Type::RawPointer {
                mutability: left_mutability,
                pointee: Box::new(self.unify(*left, *right)?),
            }),
            (
                Type::StaticData {
                    element: left_element,
                    tag: left_tag,
                    alignment: left_alignment,
                },
                Type::StaticData {
                    element: right_element,
                    tag: right_tag,
                    alignment: right_alignment,
                },
            ) if left_tag == right_tag && left_alignment == right_alignment => Ok(Type::StaticData {
                element: Box::new(self.unify(*left_element, *right_element)?),
                tag: left_tag,
                alignment: left_alignment,
            }),
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
            ) if left_mutability == right_mutability => {
                Ok(Type::Reference {
                    mutability: left_mutability,
                    lifetime: self.unify_lifetimes(left_lifetime, right_lifetime)?,
                    referent: Box::new(self.unify(*left, *right)?),
                })
            }
            (
                Type::Callable {
                    safety: left_safety,
                    lifetime_binders: left_binders,
                    parameters: left_parameters,
                    result: left_result,
                    effects: left_effects,
                    invocation: left_invocation,
                },
                Type::Callable {
                    safety: right_safety,
                    lifetime_binders: right_binders,
                    parameters: right_parameters,
                    result: right_result,
                    effects: right_effects,
                    invocation: right_invocation,
                },
            ) if left_safety == right_safety && left_binders == right_binders && left_invocation == right_invocation => {
                let effects = self.unify_effect_rows(left_effects, right_effects)?;
                Ok(Type::Callable {
                    safety: left_safety,
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
        self.solve_effect_equalities()?;
        match self.resolve(value) {
            Type::Infer(variable) if self.checking_universe_leaks.is_none() => Err(TypeError::Unresolved(variable)),
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
                item_generic_kinds,
                item_arguments,
            } => Ok(Type::Projection {
                subject: Box::new(self.zonk(*subject)?),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.zonk_generic_argument(argument))
                    .collect::<Result<_, _>>()?,
                name,
                item_generic_kinds,
                item_arguments: item_arguments
                    .into_iter()
                    .map(|argument| self.zonk_generic_argument(argument))
                    .collect::<Result<_, _>>()?,
            }),
            Type::Tuple(elements) => Ok(Type::Tuple(
                elements
                    .into_iter()
                    .map(|element| self.zonk(element))
                    .collect::<Result<_, _>>()?,
            )),
            Type::Array(element) => Ok(Type::Array(Box::new(self.zonk(*element)?))),
            Type::FixedArray { element, length } => Ok(Type::FixedArray {
                element: Box::new(self.zonk(*element)?), length: Box::new(self.zonk_generic_argument(*length)?),
            }),
            Type::RawPointer { mutability, pointee } => Ok(Type::RawPointer {
                mutability,
                pointee: Box::new(self.zonk(*pointee)?),
            }),
            Type::StaticData {
                element,
                tag,
                alignment,
            } => Ok(Type::StaticData {
                element: Box::new(self.zonk(*element)?),
                tag,
                alignment,
            }),
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => Ok(Type::Reference {
                mutability,
                lifetime: self.zonk_lifetime(lifetime)?,
                referent: Box::new(self.zonk(*referent)?),
            }),
            Type::Callable {
                safety,
                lifetime_binders,
                parameters,
                result,
                effects,
                invocation,
            } => Ok(Type::Callable {
                safety,
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
        let pending = std::mem::replace(&mut self.pending_body_lifetimes, false);
        let freezing = std::mem::replace(&mut self.freezing_types, true);
        let resolved = self.zonk(value);
        self.freezing_types = freezing;
        self.pending_body_lifetimes = pending;
        let value = resolved?;
        let bytes = canonical_type_encoding(&value);
        Ok(Digest::of_parts([
            b"grandiose-stage0-type-v1".as_slice(),
            &bytes,
        ]))
    }

    pub fn zonk_effects(&mut self, effects: EffectRow) -> Result<EffectRow, TypeError> {
        let effects = self.zonk_effects_allowing_generic_tail(effects)?;
        if let Some(index) = effects.tails.iter().find_map(|tail| match tail {
            EffectTail::Generic(index) => Some(*index), _ => None,
        }) {
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
        self.solve_effect_equalities()?;
        let effects = self.resolve_effects(effects);
        if let Some(variable) = effects.tails.iter().find_map(|tail| match tail {
            EffectTail::Infer(variable) => Some(*variable), _ => None,
        }) && self.checking_universe_leaks.is_none() {
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
                            .map(|argument| self.zonk_generic_argument(argument))
                            .collect::<Result<_, _>>()?,
                        name: projection.name,
                        item_generic_kinds: projection.item_generic_kinds,
                        item_arguments: projection
                            .item_arguments
                            .into_iter()
                            .map(|argument| self.zonk_generic_argument(argument))
                            .collect::<Result<_, _>>()?,
                    })
                })
                .collect::<Result<_, _>>()?,
            tails: effects.tails.clone(),
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
        if required.tails.is_subset(&allowed.tails) {
            return Ok(EffectRow { effects: required.effects, projections, tails: required.tails });
        }
        if required.tails.len() > 1 || allowed.tails.len() > 1 {
            let unknowns: Vec<_> = required.tails.difference(&allowed.tails).copied().collect();
            if let [EffectTail::Infer(variable)] = unknowns.as_slice() {
                self.bind_effect(*variable, EffectRow {
                    effects: allowed_only, projections: allowed.projections.clone(),
                    tails: allowed.tails.difference(&required.tails).copied().collect(),
                })?;
                return Ok(self.resolve_effects(required));
            }
            return Err(TypeError::EffectRow { expected: allowed, found: required });
        }
        match (required.tails.first().copied(), allowed.tails.first().copied()) {
            (None, _) => Ok(EffectRow {
                effects: required.effects,
                projections,
                tails: Default::default(),
            }
            .canonicalized()),
            (Some(EffectTail::Generic(left)), Some(EffectTail::Generic(right)))
                if left == right =>
            {
                Ok(EffectRow {
                    effects: required.effects,
                    projections,
                    tails: [EffectTail::Generic(left)].into_iter().collect(),
                }
                .canonicalized())
            }
            (Some(EffectTail::Infer(variable)), tail) => {
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: allowed_only,
                        projections: allowed.projections,
                        tails: tail.into_iter().collect(),
                    },
                )?;
                Ok(EffectRow {
                    effects: required.effects,
                    projections,
                    tails: [EffectTail::Infer(variable)].into_iter().collect(),
                }
                .canonicalized())
            }
            // A contextual callable row is an inference hole owned by the
            // closure being elaborated.  It may be constrained by an
            // ambient generic callback row without choosing a concrete
            // effect implementation: record the declared tail on the
            // closure-local variable, just as type inference records a
            // `Type::Generic` in an ordinary type hole.
            (Some(EffectTail::Generic(generic)), Some(EffectTail::Infer(variable))) => {
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: allowed_only,
                        projections: allowed.projections,
                        tails: [EffectTail::Generic(generic)].into_iter().collect(),
                    },
                )?;
                Ok(EffectRow {
                    effects: required.effects,
                    projections,
                    tails: [EffectTail::Generic(generic)].into_iter().collect(),
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

    pub(crate) fn unify_generic_arguments(
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
            .map(|(left, right)| {
                let left = self.resolve_generic_argument(left);
                let right = self.resolve_generic_argument(right);
                match (left, right) {
                    (GenericArgument::Lifetime(left), GenericArgument::Lifetime(right)) => {
                        self.unify_lifetimes(left, right).map(GenericArgument::Lifetime)
                    }
                    (GenericArgument::ConstInfer { variable, kind }, value)
                    | (value, GenericArgument::ConstInfer { variable, kind }) => {
                        self.bind_const(variable, kind, value.clone())?;
                        Ok(self.resolve_generic_argument(value))
                    }
                    (GenericArgument::Type(left), GenericArgument::Type(right)) => {
                        self.unify(left, right).map(GenericArgument::Type)
                    }
                    // Effect rows are first-class generic arguments, not opaque
                    // identity bytes.  A body-local row tail in `Box<e>` must be
                    // able to learn from `Box<{Trace}>` just as a type hole in
                    // `Box<T>` learns from `Box<i64>`.  Keeping this at the
                    // mixed-kind argument boundary also covers rows carried by
                    // associated-item applications and effect instances.
                    (GenericArgument::EffectRow(left), GenericArgument::EffectRow(right)) => self
                        .unify_effect_rows(left, right)
                        .map(GenericArgument::EffectRow),
                    (
                        GenericArgument::ConstProjection {
                            subject: left_subject,
                            trait_definition: left_trait,
                            trait_arguments: left_arguments,
                            name: left_name,
                            kind: left_kind,
                        },
                        GenericArgument::ConstProjection {
                            subject: right_subject,
                            trait_definition: right_trait,
                            trait_arguments: right_arguments,
                            name: right_name,
                            kind: right_kind,
                        },
                    ) if left_trait == right_trait
                        && left_name == right_name
                        && left_kind == right_kind =>
                    {
                        Ok(GenericArgument::ConstProjection {
                            subject: Box::new(self.unify(*left_subject, *right_subject)?),
                            trait_definition: left_trait,
                            trait_arguments: self
                                .unify_generic_arguments(left_arguments, right_arguments)?,
                            name: left_name,
                            kind: left_kind,
                        })
                    }
                    (left, right) if left == right => Ok(left),
                    _ => Err(TypeError::Mismatch {
                        expected: Box::new(Type::Error),
                        found: Box::new(Type::Error),
                    }),
                }
            })
            .collect()
    }

    pub(crate) fn unify_effect_rows(
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
        if left.tails.len() > 1 || right.tails.len() > 1 {
            // The empty union has one solution: every operand is empty.
            // Unlike a nonempty known row, it has no nonunique partitions.
            for (open, closed) in [(&left, &right), (&right, &left)] {
                if closed.effects.is_empty() && closed.projections.is_empty() && closed.tails.is_empty()
                    && open.effects.is_empty() && open.projections.is_empty()
                    && open.tails.iter().all(|tail| matches!(tail, EffectTail::Infer(_))) {
                    for tail in &open.tails {
                        let EffectTail::Infer(variable) = tail else { unreachable!(); };
                        self.bind_effect(*variable, EffectRow::empty())?;
                    }
                    return Ok(EffectRow::empty());
                }
            }
            let left_tails: BTreeSet<_> = left.tails.difference(&right.tails).copied().collect();
            let right_tails: BTreeSet<_> = right.tails.difference(&left.tails).copied().collect();
            if left_tails.is_empty() && right_tails.is_empty()
                && left_only.is_empty() && right_only.is_empty() { return Ok(left); }
            if let [EffectTail::Infer(variable)] = left_tails.iter().copied().collect::<Vec<_>>().as_slice()
                && left_only.is_empty() {
                self.bind_effect(*variable, EffectRow {
                    effects: right_only, projections: vec![], tails: right_tails,
                })?;
                return Ok(self.resolve_effects(left));
            }
            if let [EffectTail::Infer(variable)] = right_tails.iter().copied().collect::<Vec<_>>().as_slice()
                && right_only.is_empty() {
                self.bind_effect(*variable, EffectRow {
                    effects: left_only, projections: vec![], tails: left_tails,
                })?;
                return Ok(self.resolve_effects(right));
            }
            // Arguments later in the call may determine these operands.
            // Retain an equation, never an arbitrary partition or equality
            // between the operands. Freezing requires a unique solution.
            if left_tails.iter().chain(&right_tails)
                .any(|tail| matches!(tail, EffectTail::Infer(_))) {
                let equation = (left.clone(), right);
                if !self.pending_effect_equalities.contains(&equation) {
                    self.pending_effect_equalities.push(equation);
                }
                return Ok(left);
            }
            return Err(TypeError::EffectRow { expected: left, found: right });
        }
        match (left.tails.first().copied(), right.tails.first().copied()) {
            (None, None) if left_only.is_empty() && right_only.is_empty() => Ok(EffectRow {
                effects: left.effects.union(&right.effects).cloned().collect(),
                projections,
                tails: Default::default(),
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
            // A method-local effect-row hole may be inferred from an
            // enclosing declaration's open row binder. This is the row-kinded
            // counterpart of binding an ordinary type hole to a generic
            // parameter: the generic tail remains symbolic, while the hole
            // records any concrete effects needed to align the two rows.
            (Some(EffectTail::Infer(variable)), Some(EffectTail::Generic(generic))) => {
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: right_only,
                        projections: vec![],
                        tails: [EffectTail::Generic(generic)].into_iter().collect(),
                    },
                )?;
                Ok(right)
            }
            (Some(EffectTail::Generic(generic)), Some(EffectTail::Infer(variable))) => {
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: left_only,
                        projections: vec![],
                        tails: [EffectTail::Generic(generic)].into_iter().collect(),
                    },
                )?;
                Ok(left)
            }
            (Some(EffectTail::Infer(variable)), Some(EffectTail::Infer(other)))
                if variable == other =>
            {
                Ok(EffectRow {
                    effects: left.effects.union(&right.effects).cloned().collect(),
                    projections,
                    tails: [EffectTail::Infer(variable)].into_iter().collect(),
                }
                .canonicalized())
            }
            (Some(EffectTail::Infer(variable)), Some(EffectTail::Infer(other))) => {
                let remainder = self.fresh_effects();
                let Some(EffectTail::Infer(tail)) = remainder.tails.first().copied() else {
                    unreachable!("fresh effect row has an inference tail")
                };
                self.bind_effect(
                    variable,
                    EffectRow {
                        effects: right_only,
                        projections: vec![],
                        tails: [EffectTail::Infer(tail)].into_iter().collect(),
                    },
                )?;
                self.bind_effect(
                    other,
                    EffectRow {
                        effects: left_only,
                        projections: vec![],
                        tails: [EffectTail::Infer(tail)].into_iter().collect(),
                    },
                )?;
                Ok(EffectRow {
                    effects: left.effects.union(&right.effects).cloned().collect(),
                    projections,
                    tails: [EffectTail::Infer(tail)].into_iter().collect(),
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
                    && left_projection.item_generic_kinds == right_projection.item_generic_kinds
                    && left_projection.item_arguments.len() == right_projection.item_arguments.len()
            }) else {
                return Ok(None);
            };
            let right_projection = unmatched.remove(index);
            unified.push(EffectRowProjection {
                subject: Box::new(self.unify(*left_projection.subject, *right_projection.subject)?),
                trait_definition: left_projection.trait_definition,
                trait_arguments: self.unify_generic_arguments(
                    left_projection.trait_arguments,
                    right_projection.trait_arguments,
                )?,
                name: left_projection.name,
                item_generic_kinds: left_projection.item_generic_kinds,
                item_arguments: self.unify_generic_arguments(
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
        let mut inference = self.clone();
        let mut unmatched = allowed;
        let mut unified = Vec::with_capacity(required.len());
        for required_projection in required {
            // Prefer exact row membership. Equal item names on different
            // subjects are distinct operands, not an instruction to equate
            // those subjects (for example I::Effects | J::Effects).
            if let Some(index) = unmatched.iter().position(|candidate| candidate == &required_projection) {
                unified.push(unmatched.remove(index));
                continue;
            }
            let mut selected = None;
            for (index, candidate) in unmatched.iter().enumerate().filter(|(_, candidate)| {
                candidate.trait_definition == required_projection.trait_definition
                    && candidate.name == required_projection.name
                    && candidate.trait_arguments.len() == required_projection.trait_arguments.len()
                    && candidate.item_generic_kinds == required_projection.item_generic_kinds
                    && candidate.item_arguments.len() == required_projection.item_arguments.len()
            }) {
                let mut trial = inference.clone();
                let value = (|| -> Result<EffectRowProjection, TypeError> {
                    Ok(EffectRowProjection {
                        subject: Box::new(trial.unify(*required_projection.subject.clone(), *candidate.subject.clone())?),
                        trait_definition: required_projection.trait_definition,
                        trait_arguments: trial.unify_generic_arguments(required_projection.trait_arguments.clone(), candidate.trait_arguments.clone())?,
                        name: required_projection.name.clone(),
                        item_generic_kinds: required_projection.item_generic_kinds.clone(),
                        item_arguments: trial.unify_generic_arguments(required_projection.item_arguments.clone(), candidate.item_arguments.clone())?,
                    })
                })();
                if let Ok(value) = value {
                    // An inference hole must not arbitrarily choose between
                    // distinct allowed operands. Nor may a failed candidate
                    // leave partial bindings behind for the next candidate.
                    if selected.is_some() { return Ok(None); }
                    selected = Some((index, trial, value));
                }
            }
            let Some((index, trial, value)) = selected else { return Ok(None); };
            unmatched.remove(index);
            inference = trial;
            unified.push(value);
        }
        *self = inference;
        Ok(Some(unified))
    }

    fn bind(&mut self, variable: InferVar, value: Type) -> Result<(), TypeError> {
        if value == Type::Infer(variable) {
            return Ok(());
        }
        if self.occurs(variable, &value) {
            return Err(TypeError::Occurs(variable, Box::new(value)));
        }
        if let Some(floating) = self.numeric_constraints.get(&variable).copied() {
            self.constrain_numeric(value.clone(), floating)?;
        }
        self.bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    fn resolve_generic_argument(&mut self, value: GenericArgument) -> GenericArgument {
        let GenericArgument::ConstInfer { variable, kind } = value else {
            return value;
        };
        let Some(binding) = self.const_bindings[variable.0 as usize].clone() else {
            return GenericArgument::ConstInfer { variable, kind };
        };
        let resolved = self.resolve_generic_argument(binding);
        self.const_bindings[variable.0 as usize] = Some(resolved.clone());
        resolved
    }

    fn bind_const(
        &mut self,
        variable: ConstInferVar,
        kind: ConstKind,
        value: GenericArgument,
    ) -> Result<(), TypeError> {
        let value = self.resolve_generic_argument(value);
        if value == (GenericArgument::ConstInfer { variable, kind }) {
            return Ok(());
        }
        if !generic_argument_matches_const_kind(&value, kind)
            || self.const_argument_occurs(variable, &value)
        {
            return Err(TypeError::Mismatch {
                expected: Box::new(Type::Error),
                found: Box::new(Type::Error),
            });
        }
        self.const_bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    fn const_argument_occurs(&mut self, variable: ConstInferVar, value: &GenericArgument) -> bool {
        match value {
            GenericArgument::ConstInfer {
                variable: found, ..
            } => *found == variable,
            GenericArgument::Type(value) => self.const_occurs_in_type(variable, value),
            GenericArgument::EffectRow(value) => {
                value.effects.iter().any(|effect| {
                    effect
                        .arguments
                        .iter()
                        .any(|argument| self.const_argument_occurs(variable, argument))
                }) || value.projections.iter().any(|projection| {
                    self.const_occurs_in_type(variable, &projection.subject)
                        || projection
                            .trait_arguments
                            .iter()
                            .any(|argument| self.const_argument_occurs(variable, argument))
                        || projection
                            .item_arguments
                            .iter()
                            .any(|argument| self.const_argument_occurs(variable, argument))
                })
            }
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.const_occurs_in_type(variable, subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.const_argument_occurs(variable, argument))
            }
            GenericArgument::Lifetime(_)
            | GenericArgument::ConstInteger(_)
            | GenericArgument::ConstIntegerExpr(_)
            | GenericArgument::ConstQuantity(_)
            | GenericArgument::ConstGeneric { .. } => false,
        }
    }

    fn const_occurs_in_type(&mut self, variable: ConstInferVar, value: &Type) -> bool {
        match self.resolve(value.clone()) {
            Type::FixedArray { element, length } => self.const_occurs_in_type(variable, &element)
                || self.const_argument_occurs(variable, &length),
            Type::Nominal { arguments, .. } => arguments
                .iter()
                .any(|argument| self.const_argument_occurs(variable, argument)),
            Type::Tuple(values) => values
                .iter()
                .any(|value| self.const_occurs_in_type(variable, value)),
            Type::Projection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            } => {
                self.const_occurs_in_type(variable, &subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.const_argument_occurs(variable, argument))
                    || item_arguments
                        .iter()
                        .any(|argument| self.const_argument_occurs(variable, argument))
            }
            Type::Array(value)
            | Type::RawPointer { pointee: value, .. }
            | Type::StaticData { element: value, .. }
            | Type::Reference {
                referent: value, ..
            } => self.const_occurs_in_type(variable, &value),
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters
                    .iter()
                    .any(|value| self.const_occurs_in_type(variable, value))
                    || self.const_occurs_in_type(variable, &result)
                    || self.const_argument_occurs(variable, &GenericArgument::EffectRow(effects))
            }
            Type::Unit
            | Type::Never
            | Type::Scalar(_)
            | Type::ConstInteger(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. }
            | Type::Generic(_)
            | Type::Infer(_)
            | Type::Error => false,
        }
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
                    item_generic_kinds: left_item_kinds,
                    item_arguments: left_item_arguments,
                },
                Type::Projection {
                    subject: right_subject,
                    trait_definition: right_trait,
                    trait_arguments: right_arguments,
                    name: right_name,
                    item_generic_kinds: right_item_kinds,
                    item_arguments: right_item_arguments,
                },
            ) if left_trait == right_trait
                && left_name == right_name
                && left_item_kinds == right_item_kinds
                && left_arguments.len() == right_arguments.len()
                && left_item_arguments.len() == right_item_arguments.len() =>
            {
                self.types_may_unify(&left_subject, &right_subject)
                    && left_arguments
                        .iter()
                        .zip(&right_arguments)
                        .all(|(left, right)| self.generic_arguments_may_unify(left, right))
                    && left_item_arguments
                        .iter()
                        .zip(&right_item_arguments)
                        .all(|(left, right)| self.generic_arguments_may_unify(left, right))
            }
            (Type::Tuple(left), Type::Tuple(right)) if left.len() == right.len() => left
                .iter()
                .zip(&right)
                .all(|(left, right)| self.types_may_unify(left, right)),
            (Type::Array(left), Type::Array(right)) => self.types_may_unify(&left, &right),
            (Type::FixedArray { element: left, length: ln }, Type::FixedArray { element: right, length: rn }) =>
                self.types_may_unify(&left, &right) && self.generic_arguments_may_unify(&ln, &rn),
            (
                Type::RawPointer { mutability: left_mutability, pointee: left },
                Type::RawPointer { mutability: right_mutability, pointee: right },
            ) if left_mutability == right_mutability => self.types_may_unify(&left, &right),
            (
                Type::StaticData {
                    element: left_element,
                    tag: left_tag,
                    alignment: left_alignment,
                },
                Type::StaticData {
                    element: right_element,
                    tag: right_tag,
                    alignment: right_alignment,
                },
            ) if left_tag == right_tag && left_alignment == right_alignment => {
                self.types_may_unify(&left_element, &right_element)
            }
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

    /// Expose the outer shape during constraint generation without requiring
    /// nested type variables to be solved. Persistence boundaries use `zonk`.
    pub(crate) fn resolve(&mut self, value: Type) -> Type {
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

    /// Expose solved type shapes inside a body contract without defaulting
    /// numeric variables or requiring unrelated fields to be fully inferred.
    /// This is not a persistence operation: `zonk` remains mandatory there.
    pub(crate) fn resolve_type_structure(&self, mut value: Type) -> Type {
        while let Type::Infer(variable) = value {
            let Some(binding) = &self.bindings[variable.0 as usize] else { break; };
            value = binding.clone();
        }
        match value {
            Type::Nominal { definition, arguments } => Type::Nominal {
                definition, arguments: arguments.into_iter().map(|argument| self.resolve_argument_structure(argument)).collect(),
            },
            Type::Projection { subject, trait_definition, trait_arguments, name, item_generic_kinds, item_arguments } => Type::Projection {
                subject: Box::new(self.resolve_type_structure(*subject)), trait_definition,
                trait_arguments: trait_arguments.into_iter().map(|argument| self.resolve_argument_structure(argument)).collect(),
                name, item_generic_kinds,
                item_arguments: item_arguments.into_iter().map(|argument| self.resolve_argument_structure(argument)).collect(),
            },
            Type::Tuple(values) => Type::Tuple(values.into_iter().map(|value| self.resolve_type_structure(value)).collect()),
            Type::Array(value) => Type::Array(Box::new(self.resolve_type_structure(*value))),
            Type::FixedArray { element, length } => Type::FixedArray {
                element: Box::new(self.resolve_type_structure(*element)), length: Box::new(self.resolve_argument_structure(*length)),
            },
            Type::Reference { mutability, lifetime, referent } => Type::Reference {
                mutability, lifetime, referent: Box::new(self.resolve_type_structure(*referent)),
            },
            Type::RawPointer { mutability, pointee } => Type::RawPointer {
                mutability, pointee: Box::new(self.resolve_type_structure(*pointee)),
            },
            Type::StaticData { element, tag, alignment } => Type::StaticData {
                element: Box::new(self.resolve_type_structure(*element)), tag, alignment,
            },
            Type::Callable { safety, lifetime_binders, parameters, result, effects, invocation } => Type::Callable {
                safety, lifetime_binders,
                parameters: parameters.into_iter().map(|value| self.resolve_type_structure(value)).collect(),
                result: Box::new(self.resolve_type_structure(*result)), effects, invocation,
            },
            value => value,
        }
    }

    fn resolve_argument_structure(&self, argument: GenericArgument) -> GenericArgument {
        match argument {
            GenericArgument::Type(value) => GenericArgument::Type(self.resolve_type_structure(value)),
            argument => argument,
        }
    }

    fn solve_effect_equalities(&mut self) -> Result<(), TypeError> {
        if self.solving_effect_equalities || self.pending_effect_equalities.is_empty() { return Ok(()); }
        self.solving_effect_equalities = true;
        let result = (|| {
            loop {
                let before = self.effect_bindings.clone();
                for (left, right) in std::mem::take(&mut self.pending_effect_equalities) {
                    self.unify_effect_rows(left, right)?;
                }
                if self.pending_effect_equalities.is_empty() { return Ok(()); }
                if before == self.effect_bindings {
                    let (left, right) = self.pending_effect_equalities[0].clone();
                    return Err(TypeError::AmbiguousEffectUnion { left, right });
                }
            }
        })();
        self.solving_effect_equalities = false;
        result
    }

    fn bind_effect(&mut self, variable: EffectVar, value: EffectRow) -> Result<(), TypeError> {
        if value.tails == BTreeSet::from([EffectTail::Infer(variable)])
            && value.effects.is_empty() && value.projections.is_empty() {
            return Ok(());
        }
        if self.effect_occurs(variable, &value) {
            return Err(TypeError::EffectOccurs(variable, value));
        }
        self.effect_bindings[variable.0 as usize] = Some(value);
        Ok(())
    }

    fn resolve_effects(&mut self, mut effects: EffectRow) -> EffectRow {
        effects.substitute_tails(|tail| {
            let EffectTail::Infer(variable) = tail else { return None; };
            let binding = self.effect_bindings.get(variable.0 as usize)?.clone()?;
            let binding = self.resolve_effects(binding);
            self.effect_bindings[variable.0 as usize] = Some(binding.clone());
            Some(binding)
        });
        effects
    }

    fn effect_occurs(&mut self, variable: EffectVar, effects: &EffectRow) -> bool {
        self.effect_occurs_in_row(variable, effects)
    }

    /// Effect variables do not live only in a row tails: an effect row can be
    /// carried as a generic argument, and a type argument can itself be a
    /// callable with an open effect row.  Follow every mixed-kind edge before
    /// binding the variable, otherwise later zonking can recurse forever.
    fn effect_occurs_in_row(&mut self, variable: EffectVar, effects: &EffectRow) -> bool {
        let effects = self.resolve_effects(effects.clone());
        effects.tails.contains(&EffectTail::Infer(variable))
            || effects.effects.iter().any(|effect| {
                effect
                    .arguments
                    .iter()
                    .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
            })
            || effects.projections.iter().any(|projection| {
                self.effect_occurs_in_type(variable, &projection.subject)
                    || projection
                        .trait_arguments
                        .iter()
                        .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
                    || projection
                        .item_arguments
                        .iter()
                        .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
            })
    }

    fn effect_occurs_in_generic_argument(
        &mut self,
        variable: EffectVar,
        argument: &GenericArgument,
    ) -> bool {
        match self.resolve_generic_argument(argument.clone()) {
            GenericArgument::Type(value) => self.effect_occurs_in_type(variable, &value),
            GenericArgument::EffectRow(value) => self.effect_occurs_in_row(variable, &value),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.effect_occurs_in_type(variable, &subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
            }
            GenericArgument::Lifetime(_)
            | GenericArgument::ConstInteger(_)
            | GenericArgument::ConstIntegerExpr(_)
            | GenericArgument::ConstQuantity(_)
            | GenericArgument::ConstGeneric { .. }
            | GenericArgument::ConstInfer { .. } => false,
        }
    }

    fn effect_occurs_in_type(&mut self, variable: EffectVar, value: &Type) -> bool {
        match self.resolve(value.clone()) {
            Type::FixedArray { element, length } => self.effect_occurs_in_type(variable, &element)
                || self.effect_occurs_in_generic_argument(variable, &length),
            Type::Nominal { arguments, .. } => arguments
                .iter()
                .any(|argument| self.effect_occurs_in_generic_argument(variable, argument)),
            Type::Tuple(elements) => elements
                .iter()
                .any(|element| self.effect_occurs_in_type(variable, element)),
            Type::Projection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            } => {
                self.effect_occurs_in_type(variable, &subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
                    || item_arguments
                        .iter()
                        .any(|argument| self.effect_occurs_in_generic_argument(variable, argument))
            }
            Type::Array(element)
            | Type::RawPointer { pointee: element, .. }
            | Type::StaticData { element, .. }
            | Type::Reference {
                referent: element, ..
            } => self.effect_occurs_in_type(variable, &element),
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| self.effect_occurs_in_type(variable, parameter))
                    || self.effect_occurs_in_type(variable, &result)
                    || self.effect_occurs_in_row(variable, &effects)
            }
            Type::Unit
            | Type::Never
            | Type::Scalar(_)
            | Type::ConstInteger(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. }
            | Type::Generic(_)
            | Type::Infer(_)
            | Type::Error => false,
        }
    }

    fn occurs(&mut self, variable: InferVar, value: &Type) -> bool {
        match self.resolve(value.clone()) {
            Type::FixedArray { element, length } => self.occurs(variable, &element)
                || self.generic_argument_occurs(variable, &length),
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
                        .any(|argument| self.generic_argument_occurs(variable, argument))
                    || item_arguments
                        .iter()
                        .any(|argument| self.generic_argument_occurs(variable, argument))
            }
            Type::Array(element)
            | Type::RawPointer { pointee: element, .. }
            | Type::StaticData { element, .. }
            | Type::Reference {
                referent: element, ..
            } => self.occurs(variable, &element),
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                parameters
                    .iter()
                    .any(|parameter| self.occurs(variable, parameter))
                    || self.occurs(variable, &result)
                    || self.effect_row_type_occurs(variable, &effects)
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
            (GenericArgument::EffectRow(left), GenericArgument::EffectRow(right)) => {
                self.effect_rows_may_unify(left, right)
            }
            (
                GenericArgument::ConstProjection {
                    subject: left_subject,
                    trait_definition: left_trait,
                    trait_arguments: left_arguments,
                    name: left_name,
                    kind: left_kind,
                },
                GenericArgument::ConstProjection {
                    subject: right_subject,
                    trait_definition: right_trait,
                    trait_arguments: right_arguments,
                    name: right_name,
                    kind: right_kind,
                },
            ) => {
                left_trait == right_trait
                    && left_name == right_name
                    && left_kind == right_kind
                    && self.types_may_unify(left_subject, right_subject)
                    && left_arguments.len() == right_arguments.len()
                    && left_arguments
                        .iter()
                        .zip(right_arguments)
                        .all(|(left, right)| self.generic_arguments_may_unify(left, right))
            }
            _ => left == right,
        }
    }

    /// A side-effect-free compatibility filter used only while matching
    /// effect instances.  The real row solver remains
    /// [`Self::unify_effect_rows`]; this predicate merely avoids treating an
    /// inference-owned row argument as a permanently distinct protocol
    /// instance before that solver can bind it.
    fn effect_rows_may_unify(&mut self, left: &EffectRow, right: &EffectRow) -> bool {
        let left = self.resolve_effects(left.clone()).canonicalized();
        let right = self.resolve_effects(right.clone()).canonicalized();
        if left == right {
            return true;
        }
        if left.tails.iter().any(|tail| matches!(tail, EffectTail::Infer(_)))
            || right.tails.iter().any(|tail| matches!(tail, EffectTail::Infer(_)))
        {
            return true;
        }
        let compatible_tails = left.tails == right.tails;
        compatible_tails
            && left.effects.len() == right.effects.len()
            && left.projections.len() == right.projections.len()
            && left.effects.iter().all(|effect| {
                right.effects.iter().any(|candidate| {
                    effect.definition == candidate.definition
                        && effect.arguments.len() == candidate.arguments.len()
                        && effect
                            .arguments
                            .iter()
                            .zip(&candidate.arguments)
                            .all(|(left, right)| self.generic_arguments_may_unify(left, right))
                })
            })
            && left.projections.iter().all(|projection| {
                right.projections.iter().any(|candidate| {
                    projection.trait_definition == candidate.trait_definition
                        && projection.name == candidate.name
                        && projection.item_generic_kinds == candidate.item_generic_kinds
                        && projection.trait_arguments.len() == candidate.trait_arguments.len()
                        && projection.item_arguments.len() == candidate.item_arguments.len()
                        && self.types_may_unify(&projection.subject, &candidate.subject)
                        && projection
                            .trait_arguments
                            .iter()
                            .zip(&candidate.trait_arguments)
                            .all(|(left, right)| self.generic_arguments_may_unify(left, right))
                        && projection
                            .item_arguments
                            .iter()
                            .zip(&candidate.item_arguments)
                            .all(|(left, right)| self.generic_arguments_may_unify(left, right))
                })
            })
    }

    pub(crate) fn zonk_generic_argument(
        &mut self,
        argument: GenericArgument,
    ) -> Result<GenericArgument, TypeError> {
        match self.resolve_generic_argument(argument) {
            GenericArgument::Lifetime(value) => self.zonk_lifetime(value).map(GenericArgument::Lifetime),
            GenericArgument::Type(value) => self.zonk(value).map(GenericArgument::Type),
            GenericArgument::EffectRow(value) => self
                .zonk_effects_allowing_generic_tail(value)
                .map(GenericArgument::EffectRow),
            GenericArgument::ConstProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                kind,
            } => Ok(GenericArgument::ConstProjection {
                subject: Box::new(self.zonk(*subject)?),
                trait_definition,
                trait_arguments: trait_arguments
                    .into_iter()
                    .map(|argument| self.zonk_generic_argument(argument))
                    .collect::<Result<_, _>>()?,
                name,
                kind,
            }),
            GenericArgument::ConstInfer { variable, .. } if self.checking_universe_leaks.is_none() => {
                Err(TypeError::UnresolvedConst(variable))
            }
            argument => Ok(argument),
        }
    }

    fn generic_argument_occurs(&mut self, variable: InferVar, argument: &GenericArgument) -> bool {
        match argument {
            GenericArgument::Type(value) => self.occurs(variable, value),
            GenericArgument::EffectRow(value) => self.effect_row_type_occurs(variable, value),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.occurs(variable, subject)
                    || trait_arguments
                        .iter()
                        .any(|argument| self.generic_argument_occurs(variable, argument))
            }
            GenericArgument::Lifetime(_)
            | GenericArgument::ConstInteger(_)
            | GenericArgument::ConstIntegerExpr(_)
            | GenericArgument::ConstQuantity(_)
            | GenericArgument::ConstGeneric { .. }
            | GenericArgument::ConstInfer { .. } => false,
        }
    }

    /// A type inference variable can be nested in an effect row through an
    /// effect instance, associated-row projection, or a callable carried by
    /// either.  Keep this traversal beside the ordinary occurs check so none
    /// of the mixed-kind generic slots becomes an unchecked back edge.
    fn effect_row_type_occurs(&mut self, variable: InferVar, effects: &EffectRow) -> bool {
        let mut visited_tails = BTreeSet::new();
        self.effect_row_type_occurs_in(variable, effects, &mut visited_tails)
    }

    /// Follow a solved row tail while checking a type occurrence.  A row
    /// binding can itself contain a type argument, so treating a tail as an
    /// opaque leaf would let `α = Nominal<{ | ε }>` escape after `ε` had
    /// already been solved to a row containing `α`. The visited set makes
    /// this defensive traversal total even for malformed imported state.
    fn effect_row_type_occurs_in(
        &mut self,
        variable: InferVar,
        effects: &EffectRow,
        visited_tails: &mut BTreeSet<EffectVar>,
    ) -> bool {
        effects.effects.iter().any(|effect| {
            effect
                .arguments
                .iter()
                .any(|argument| self.generic_argument_occurs(variable, argument))
        }) || effects.projections.iter().any(|projection| {
            self.occurs(variable, &projection.subject)
                || projection
                    .trait_arguments
                    .iter()
                    .any(|argument| self.generic_argument_occurs(variable, argument))
                || projection
                    .item_arguments
                    .iter()
                    .any(|argument| self.generic_argument_occurs(variable, argument))
        }) || effects.tails.iter().any(|tail| match *tail {
            EffectTail::Infer(tail) if visited_tails.insert(tail) => self
                .effect_bindings
                .get(tail.0 as usize)
                .and_then(|binding| binding.clone())
                .is_some_and(|binding| {
                    self.effect_row_type_occurs_in(variable, &binding, visited_tails)
                }),
            _ => false,
        })
    }
}

pub(crate) fn generic_argument_matches_const_kind(argument: &GenericArgument, kind: ConstKind) -> bool {
    match argument {
        GenericArgument::ConstInteger(value) => value.kind() == kind,
        GenericArgument::ConstIntegerExpr(value) => value.scalar().ok().and_then(ConstKind::from_integer_scalar) == Some(kind),
        GenericArgument::ConstQuantity(_) => kind == ConstKind::Quantity,
        GenericArgument::ConstGeneric { kind: found, .. }
        | GenericArgument::ConstInfer { kind: found, .. }
        | GenericArgument::ConstProjection { kind: found, .. } => *found == kind,
        _ => false,
    }
}

pub(crate) fn integer_const_argument_type(argument: &GenericArgument) -> Option<Type> {
    match argument {
        GenericArgument::ConstInteger(value) => Some(Type::Scalar(value.scalar())),
        GenericArgument::ConstIntegerExpr(value) => value.scalar().ok().map(Type::Scalar),
        GenericArgument::ConstGeneric { kind, .. } | GenericArgument::ConstProjection { kind, .. }
        | GenericArgument::ConstInfer { kind, .. } => kind.integer_scalar().map(Type::Scalar),
        _ => None,
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
            item_generic_kinds,
            item_arguments,
        } => {
            output.push(11);
            encode_type(subject, output);
            output.extend_from_slice(&trait_definition.0.as_bytes());
            encode_generic_arguments(trait_arguments, output);
            output.extend_from_slice(&(name.len() as u64).to_le_bytes());
            output.extend_from_slice(name.as_bytes());
            encode_generic_kinds(item_generic_kinds, output);
            encode_generic_arguments(item_arguments, output);
        }
        Type::Tuple(elements) => {
            output.push(4);
            encode_types(elements, output);
        }
        Type::Array(element) => {
            output.push(5);
            encode_type(element, output);
        }
        Type::FixedArray { element, length } => {
            output.push(18);
            encode_type(element, output);
            encode_generic_arguments(std::slice::from_ref(length.as_ref()), output);
        }
        Type::RawPointer { mutability, pointee } => {
            // New identity tag; existing type encodings remain unchanged.
            output.push(16);
            output.push(match mutability {
                PointerMutability::Const => 0,
                PointerMutability::Mut => 1,
            });
            encode_type(pointee, output);
        }
        Type::StaticData {
            element,
            tag,
            alignment,
        } => {
            output.push(15);
            encode_type(element, output);
            output.extend_from_slice(&tag.to_le_bytes());
            output.extend_from_slice(&alignment.to_le_bytes());
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
                Lifetime::Infer(_) => 4,
                Lifetime::Static => 0,
                Lifetime::Generic(_) => 1,
                Lifetime::Bound { .. } => 2,
                Lifetime::Elided => 3,
                Lifetime::Placeholder(_) => 5,
            });
            if let Lifetime::Generic(index) = lifetime {
                output.extend_from_slice(&index.to_le_bytes());
            }
            if let Lifetime::Infer(variable) = lifetime {
                output.extend_from_slice(&variable.0.to_le_bytes());
            }
            if let Lifetime::Placeholder(region) = lifetime {
                output.extend_from_slice(&region.universe.to_le_bytes());
                output.extend_from_slice(&region.index.to_le_bytes());
            }
            if let Lifetime::Bound { depth, index } = lifetime {
                output.extend_from_slice(&depth.to_le_bytes());
                output.extend_from_slice(&index.to_le_bytes());
            }
            encode_type(referent, output);
        }
        Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => {
            // Keep existing safe callable identities stable; unsafe callable
            // contracts occupy a distinct tag, never an erasable effect bit.
            output.push(if *safety == Safety::Safe { 7 } else { 17 });
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
                encode_generic_arguments(&projection.trait_arguments, output);
                output.extend_from_slice(&(projection.name.len() as u64).to_le_bytes());
                output.extend_from_slice(projection.name.as_bytes());
                encode_generic_kinds(&projection.item_generic_kinds, output);
                encode_generic_arguments(&projection.item_arguments, output);
            }
            output.extend_from_slice(&(effects.tails.len() as u64).to_le_bytes());
            for tail in &effects.tails { match tail {
                EffectTail::Infer(variable) => {
                    output.push(0);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                EffectTail::Generic(index) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
            } }
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
        Type::ConstInteger(value) => {
            output.push(12);
            output.extend_from_slice(&value.canonical_bytes());
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
            output.push(kind.tag());
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
    encode_type(&canonicalize_type_identity(value.clone()), &mut bytes);
    bytes
}

/// Tagged canonical encoding for declaration argument sequences.
pub(crate) fn canonical_generic_arguments_encoding(values: &[GenericArgument]) -> Vec<u8> {
    let mut bytes = vec![];
    let values = values
        .iter()
        .cloned()
        .map(canonicalize_generic_argument_identity)
        .collect::<Vec<_>>();
    encode_generic_arguments(&values, &mut bytes);
    bytes
}

/// Normalize representation-only choices in a semantic type tree before it
/// participates in a fingerprint or crosses a frozen-product boundary.
///
/// This intentionally does not try to resolve aliases, projections, or
/// inference: those require their owning signature or inference context.
/// It does erase the choices that have no semantic meaning once such a tree
/// exists: effect-row projection order/duplicates and normalized structural
/// const spelling. Keeping this one operation next to the tagged encoder
/// prevents caches, solver goals, and persisted products from growing
/// different notions of "the same" type.
pub(crate) fn canonicalize_type_identity(value: Type) -> Type {
    match value {
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition,
            arguments: arguments
                .into_iter()
                .map(canonicalize_generic_argument_identity)
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
            subject: Box::new(canonicalize_type_identity(*subject)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(canonicalize_generic_argument_identity)
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(canonicalize_generic_argument_identity)
                .collect(),
        },
        Type::Tuple(elements) => Type::Tuple(
            elements
                .into_iter()
                .map(canonicalize_type_identity)
                .collect(),
        ),
        Type::Array(element) => Type::Array(Box::new(canonicalize_type_identity(*element))),
        Type::FixedArray { element, length } => Type::FixedArray {
            element: Box::new(canonicalize_type_identity(*element)),
            length: Box::new(canonicalize_generic_argument_identity(*length)),
        },
        Type::RawPointer { mutability, pointee } => Type::RawPointer {
            mutability,
            pointee: Box::new(canonicalize_type_identity(*pointee)),
        },
        Type::StaticData {
            element,
            tag,
            alignment,
        } => Type::StaticData {
            element: Box::new(canonicalize_type_identity(*element)),
            tag,
            alignment,
        },
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime,
            referent: Box::new(canonicalize_type_identity(*referent)),
        },
        Type::Callable {
            safety,
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            safety,
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(canonicalize_type_identity)
                .collect(),
            result: Box::new(canonicalize_type_identity(*result)),
            effects: canonicalize_effect_row_identity(effects),
            invocation,
        },
        value => value,
    }
}

pub(crate) fn is_canonical_type_identity(value: &Type) -> bool {
    type_identity_is_well_formed(value) && *value == canonicalize_type_identity(value.clone())
}

pub(crate) fn is_canonical_generic_argument_identity(value: &GenericArgument) -> bool {
    generic_argument_identity_is_well_formed(value)
        && *value == canonicalize_generic_argument_identity(value.clone())
}

pub(crate) fn is_canonical_effect_row_identity(value: &EffectRow) -> bool {
    effect_row_identity_is_well_formed(value)
        && *value == canonicalize_effect_row_identity(value.clone())
}

fn type_identity_is_well_formed(value: &Type) -> bool {
    match value {
        Type::FixedArray { element, length } => type_identity_is_well_formed(element)
            && generic_argument_matches_const_kind(length, ConstKind::Usize)
            && generic_argument_identity_is_well_formed(length),
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .all(generic_argument_identity_is_well_formed),
        Type::Projection {
            subject,
            trait_arguments,
            item_generic_kinds,
            item_arguments,
            ..
        } => {
            type_identity_is_well_formed(subject)
                && trait_arguments
                    .iter()
                    .all(generic_argument_identity_is_well_formed)
                && item_arguments
                    .iter()
                    .all(generic_argument_identity_is_well_formed)
                && projection_item_arguments_match_kinds(item_generic_kinds, item_arguments)
        }
        Type::Tuple(elements) => elements.iter().all(type_identity_is_well_formed),
        Type::Array(element)
        | Type::RawPointer { pointee: element, .. }
        | Type::StaticData { element, .. }
        | Type::Reference {
            referent: element, ..
        } => type_identity_is_well_formed(element),
        Type::Callable {
            parameters,
            result,
            effects,
            invocation,
            ..
        } => {
            quantity_is_well_formed(*invocation)
                && parameters.iter().all(type_identity_is_well_formed)
                && type_identity_is_well_formed(result)
                && effect_row_identity_is_well_formed(effects)
        }
        Type::ConstQuantity(value) => quantity_is_well_formed(*value),
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstInteger(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => true,
    }
}

fn generic_argument_identity_is_well_formed(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => type_identity_is_well_formed(value),
        GenericArgument::EffectRow(value) => effect_row_identity_is_well_formed(value),
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            type_identity_is_well_formed(subject)
                && trait_arguments
                    .iter()
                    .all(generic_argument_identity_is_well_formed)
        }
        GenericArgument::ConstIntegerExpr(value) => {
            !matches!(value, IntegerConstExpr::Literal(_) | IntegerConstExpr::Param { .. })
                && value.normalized().as_ref() == Ok(value)
        }
        GenericArgument::ConstQuantity(value) => quantity_is_well_formed(*value),
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstInteger(_)
        | GenericArgument::ConstGeneric { .. } => true,
        // Allocation-local const holes are not semantic identities.  They
        // can be encoded transiently for deterministic body-local ordering,
        // but no frozen Core/MIR/VM product may retain one.
        GenericArgument::ConstInfer { .. } => false,
    }
}

fn effect_row_identity_is_well_formed(value: &EffectRow) -> bool {
    value.effects.iter().all(|effect| {
        effect
            .arguments
            .iter()
            .all(generic_argument_identity_is_well_formed)
    }) && value.projections.iter().all(|projection| {
        type_identity_is_well_formed(&projection.subject)
            && projection
                .trait_arguments
                .iter()
                .all(generic_argument_identity_is_well_formed)
            && projection
                .item_arguments
                .iter()
                .all(generic_argument_identity_is_well_formed)
            && projection_item_arguments_match_kinds(
                &projection.item_generic_kinds,
                &projection.item_arguments,
            )
    })
}

fn quantity_is_well_formed(value: Quantity) -> bool {
    value.upper.is_none_or(|upper| value.lower <= upper)
}

/// Validate an associated-type application against the declaration-owned GAT
/// binder contract. This protects frozen identities even when they were not
/// produced by source elaboration (for example, a forged Core or MIR test).
pub(crate) fn projection_item_arguments_match_kinds(
    kinds: &[GenericKind],
    arguments: &[GenericArgument],
) -> bool {
    kinds.len() == arguments.len()
        && kinds.iter().zip(arguments).all(|(kind, argument)| match kind {
            GenericKind::Const(kind) => !matches!(argument, GenericArgument::ConstInfer { .. })
                && generic_argument_matches_const_kind(argument, *kind),
            GenericKind::Type => matches!(argument, GenericArgument::Type(_)),
            GenericKind::EffectRow => matches!(argument, GenericArgument::EffectRow(_)),
            GenericKind::Lifetime => matches!(argument, GenericArgument::Lifetime(_)),
        })
}

fn canonicalize_generic_argument_identity(value: GenericArgument) -> GenericArgument {
    match value {
        GenericArgument::Type(value) => GenericArgument::Type(canonicalize_type_identity(value)),
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(canonicalize_effect_row_identity(value))
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(canonicalize_type_identity(*subject)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(canonicalize_generic_argument_identity)
                .collect(),
            name,
            kind,
        },
        GenericArgument::ConstIntegerExpr(value) => match value.clone().normalized() {
            Ok(value) => integer_const_argument(Ok(value)),
            Err(_) => GenericArgument::ConstIntegerExpr(value),
        },
        value => value,
    }
}

fn canonicalize_effect_row_identity(value: EffectRow) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(canonicalize_generic_argument_identity)
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(canonicalize_type_identity(*projection.subject)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(canonicalize_generic_argument_identity)
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(canonicalize_generic_argument_identity)
                    .collect(),
            })
            .collect(),
        tails: value.tails.clone(),
    }
    .canonicalized()
}

fn canonical_generic_arguments(values: &[GenericArgument]) -> Vec<u8> {
    canonical_generic_arguments_encoding(values)
}

fn effect_row_projection_key(value: &EffectRowProjection) -> Vec<u8> {
    let mut bytes = vec![];
    encode_type(&value.subject, &mut bytes);
    bytes.extend_from_slice(&value.trait_definition.0.as_bytes());
    encode_generic_arguments(&value.trait_arguments, &mut bytes);
    bytes.extend_from_slice(&(value.name.len() as u64).to_le_bytes());
    bytes.extend_from_slice(value.name.as_bytes());
    encode_generic_kinds(&value.item_generic_kinds, &mut bytes);
    encode_generic_arguments(&value.item_arguments, &mut bytes);
    bytes
}

fn encode_types(values: &[Type], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        encode_type(value, output);
    }
}

fn encode_generic_kinds(values: &[GenericKind], output: &mut Vec<u8>) {
    output.extend_from_slice(&(values.len() as u64).to_le_bytes());
    for value in values {
        output.push(value.tag());
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
            output.extend_from_slice(&(value.tails.len() as u64).to_le_bytes());
            for tail in &value.tails { match tail {
                EffectTail::Infer(variable) => {
                    output.push(0);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
                EffectTail::Generic(index) => {
                    output.push(1);
                    output.extend_from_slice(&index.to_le_bytes());
                }
            } }
        }
        GenericArgument::Lifetime(value) => {
            output.push(2);
            match value {
                Lifetime::Infer(variable) => {
                    output.push(4);
                    output.extend_from_slice(&variable.0.to_le_bytes());
                }
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
                Lifetime::Placeholder(region) => {
                    output.push(5);
                    output.extend_from_slice(&region.universe.to_le_bytes());
                    output.extend_from_slice(&region.index.to_le_bytes());
                }
            }
        }
        GenericArgument::ConstInteger(value) => {
            output.push(3);
            output.extend_from_slice(&value.canonical_bytes());
        }
        GenericArgument::ConstIntegerExpr(value) => {
            output.push(6);
            encode_structural_integer_expr(value, output);
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
            output.push(kind.tag());
        }
        GenericArgument::ConstInfer { variable, kind } => {
            // Body-local ordering needs a deterministic key while source
            // elaboration matches effect instances. Frozen callers reject it
            // through `generic_argument_identity_is_well_formed`.
            output.push(8);
            output.extend_from_slice(&variable.0.to_le_bytes());
            output.push(kind.tag());
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => {
            output.push(7);
            encode_type(subject, output);
            output.extend_from_slice(&trait_definition.0.as_bytes());
            encode_generic_arguments(trait_arguments, output);
            output.extend_from_slice(&(name.len() as u64).to_le_bytes());
            output.extend_from_slice(name.as_bytes());
            output.push(kind.tag());
        }
    }
}
