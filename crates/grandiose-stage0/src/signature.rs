//! Header elaboration into canonical, body-independent semantic signatures.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    header::{
        CallableHeader, EffectHeader, EffectRowHeader, EnumVariantPayloadHeader, GenericParameters,
        HeaderGenericArgument, HeaderStructuralConst, HeaderStructuralU32Expr, HeaderType,
        ImplementationHeader, NominalLayoutHeader, ParsedHeader, TraitHeader, TraitRefHeader,
    },
    identity::{DefKey, FileKey, ModuleKey},
    interface::{Definition, DefinitionNamespace, PackageInterface},
    quantity::Quantity,
    resolution::{DefinitionIndex, ResolutionState},
    types::{
        ConstKind, EffectInstance, EffectRow, EffectRowProjection, EffectTail, GenericArgument,
        GenericKind, Lifetime, Mutability, StructuralU32Expr, Type,
    },
};

/// The implicit receiver binder of a trait declaration.  It lives outside the
/// densely numbered source binders so it cannot collide with trait or method
/// generic arguments.  A selected implementation replaces it with its
/// concrete self type before a method contract becomes callable.
pub(crate) const TRAIT_SELF_GENERIC: u32 = u32::MAX;

/// Stable identity for the language-provided callable contract.  This is not
/// a prelude spelling: source resolution may bind a user trait named `Fn`,
/// but only an unresolved unqualified `Fn` is elaborated to this identity.
/// Solver-side callable evidence keys exclusively on this value.
pub fn intrinsic_callable_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-intrinsic-callable-trait-v1",
    ))
}

pub fn is_intrinsic_callable_trait(reference: &ElaboratedTraitReference) -> bool {
    reference.definition == intrinsic_callable_trait_definition()
}

/// Stable identity for the compiler-owned nonlocal-exit contract. Like `Fn`,
/// this never relies on a prelude name during solving: a resolved source trait
/// named `Label` is an ordinary trait with no escape authority.
pub fn intrinsic_label_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-intrinsic-label-trait-v1",
    ))
}

pub fn is_intrinsic_label_trait(reference: &ElaboratedTraitReference) -> bool {
    reference.definition == intrinsic_label_trait_definition()
}

/// Stable identity for compiler-created callable-environment evidence. Unlike
/// `Fn` and `Label`, it deliberately has no source spelling fallback: source
/// cannot manufacture an environment brand by writing `RunsIn`.
pub fn intrinsic_runs_in_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-intrinsic-runs-in-trait-v1",
    ))
}

pub fn is_intrinsic_runs_in_trait(reference: &ElaboratedTraitReference) -> bool {
    reference.definition == intrinsic_runs_in_trait_definition()
}

/// Stable identity for compiler-generated execution-environment brands.
/// Source may name the trait in bounds, but implementations are sealed and
/// only the canonical empty environment has compiler-provided evidence.
pub fn intrinsic_environment_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-intrinsic-environment-trait-v1",
    ))
}

pub fn is_intrinsic_environment_trait(reference: &ElaboratedTraitReference) -> bool {
    reference.definition == intrinsic_environment_trait_definition()
}

/// Stable nominal identity for the erased incremental-alternative witness.
/// It deliberately has no source declaration or runtime layout.
pub fn intrinsic_available_type_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-intrinsic-available-type-v1",
    ))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableSignature {
    pub generics: u32,
    /// Generic binder kinds in the same slot order as the source header.
    /// Callers use this to keep const substitutions out of the type namespace.
    pub generic_kinds: Vec<GenericKind>,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub effects: EffectRow,
    pub invocation: Quantity,
    pub where_bounds: Vec<(Type, ElaboratedTraitReference)>,
    /// Equalities declared alongside callable `where` evidence.  Keeping the
    /// selected item separate from the trait relation preserves both the
    /// trait's mixed-kind arguments and the associated item's own GAT
    /// arguments in frozen metadata.
    pub where_associated_type_bindings: Vec<ElaboratedAssociatedTypeBinding>,
    /// Row-kinded associated equalities use the same evidence but retain an
    /// effect-row value rather than masquerading as a type equality.
    pub where_associated_effect_bindings: Vec<ElaboratedAssociatedEffectBinding>,
}

/// The frozen authority identity of one source-declared host import.  A
/// capability is request-granted policy; the symbol is a stable ABI label,
/// intentionally separate from source paths and VM function identities.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct HostImport {
    pub capability: String,
    pub symbol: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedTraitReference {
    pub definition: DefKey,
    /// One canonical argument per declared trait slot. Trait identity keeps
    /// consts, rows, and regions out of the value-type namespace.
    pub arguments: Vec<GenericArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedTypeBinding {
    pub subject: Type,
    pub relation: ElaboratedTraitReference,
    pub name: String,
    pub item_generic_kinds: Vec<GenericKind>,
    pub item_arguments: Vec<GenericArgument>,
    pub value: Type,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedEffectBinding {
    pub subject: Type,
    pub relation: ElaboratedTraitReference,
    pub name: String,
    pub item_generic_kinds: Vec<GenericKind>,
    pub item_arguments: Vec<GenericArgument>,
    pub value: EffectRow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedTrait {
    /// Source-declared auto traits admit structural, coinductive proof search.
    pub auto_trait: bool,
    pub generics: u32,
    /// Kinds of declaration binders in source-slot order.  Traits may bind
    /// regions just like callables, but those regions must never be confused
    /// with a type argument when a method contract is instantiated.
    pub generic_kinds: Vec<GenericKind>,
    pub supertraits: Vec<ElaboratedTraitReference>,
    /// Declared associated type names and their item-generic arities. The
    /// frozen interface retains this metadata so projection syntax can keep
    /// trait and associated-item arguments distinct through normalization.
    pub associated_types: BTreeMap<String, ElaboratedAssociatedType>,
    /// Structural constants selected with the same evidence as associated
    /// types, but never crossing the value-type interface boundary.
    pub associated_consts: BTreeMap<String, ElaboratedAssociatedConst>,
    pub methods: BTreeMap<String, CallableSignature>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedType {
    pub generics: u32,
    /// Kinds of the associated item's binders in source-slot order.  Arity
    /// alone is not a sufficient GAT contract: `Item<'a>` and `Item<T>` have
    /// distinct substitution domains even though each has one binder.
    pub generic_kinds: Vec<GenericKind>,
    pub effect_row: bool,
    /// A trait-declared value default, elaborated in the declaration's
    /// generic environment plus the associated item's binder scope.
    pub default: Option<Type>,
    /// A trait-declared effect-row default.  This remains distinct from the
    /// value default all the way to trait selection.
    pub effect_row_default: Option<EffectRow>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedConst {
    pub kind: ConstKind,
    pub default: Option<GenericArgument>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedImplementation {
    pub generics: u32,
    /// Kinds of implementation binders in source-slot order.  This is part
    /// of the frozen impl identity: in particular `impl<'a> Marker for
    /// &'a T` has a region binder even though that binder never occupies the
    /// type-substitution namespace.
    pub generic_kinds: Vec<GenericKind>,
    pub negative: bool,
    pub relation: ElaboratedTraitReference,
    pub self_ty: Type,
    pub where_bounds: Vec<(Type, ElaboratedTraitReference)>,
    pub associated_types: BTreeMap<String, ElaboratedAssociatedTypeDefinition>,
    pub associated_effect_rows: BTreeMap<String, ElaboratedAssociatedEffectRowDefinition>,
    pub associated_consts: BTreeMap<String, ElaboratedAssociatedConstDefinition>,
    pub methods: BTreeMap<String, CallableSignature>,
}

/// A trait implementation's associated type body. Item generics use slots
/// after the implementation's generic slots, so projection normalization can
/// substitute both environments without conflating them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedTypeDefinition {
    pub generics: u32,
    /// The implementation-side item binder kinds.  These must exactly match
    /// the trait declaration before a projection can safely substitute its
    /// arguments into this value.
    pub generic_kinds: Vec<GenericKind>,
    pub value: Type,
}

/// A trait implementation's associated effect-row body. It mirrors ordinary
/// associated type binders while retaining row kind through normalization.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedEffectRowDefinition {
    pub generics: u32,
    /// The implementation-side item binder kinds for a row-kinded associated
    /// item.  Keeping this separately from `generics` prevents a future
    /// const/region argument elaborator from treating every slot as a type.
    pub generic_kinds: Vec<GenericKind>,
    pub value: EffectRow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedConstDefinition {
    pub kind: ConstKind,
    pub value: GenericArgument,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedEffectOperation {
    pub name: String,
    /// Declaration and operation binders share this namespace.  The first
    /// `effect_generics` slots belong to the protocol declaration.
    pub generics: u32,
    /// Full declaration-plus-operation generic kinds in the same slot order
    /// as `generics`. Effect instantiation must retain quantity, region, and
    /// row identity rather than forcing every protocol argument through a
    /// type-only substitution boundary.
    pub generic_kinds: Vec<GenericKind>,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub terminal: bool,
    pub resumption: Quantity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedEffect {
    pub generics: u32,
    /// Source-slot kinds are retained even though operation value signatures
    /// use only their type-valued subset.
    pub generic_kinds: Vec<GenericKind>,
    pub operations: Vec<ElaboratedEffectOperation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NominalField {
    pub name: String,
    pub ty: Type,
    /// The source entry that alone may structurally access this field. `None`
    /// denotes a public field.
    pub private_authority: Option<FileKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElaboratedEnumVariantPayload {
    Unit,
    Tuple(Vec<Type>),
    Struct(Vec<NominalField>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedEnumVariant {
    pub name: String,
    pub payload: ElaboratedEnumVariantPayload,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElaboratedNominalLayout {
    Struct(Vec<NominalField>),
    Enum(Vec<ElaboratedEnumVariant>),
    Opaque,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ElaboratedHeader {
    Callable(CallableSignature),
    /// A value alias is resolved against the complete frozen definition index
    /// and carries the target's exact callable contract. Core lowers calls to
    /// `target`, never to a synthetic alias body.
    ValueAlias {
        target: DefKey,
        signature: CallableSignature,
    },
    /// A top-level evaluated `let`. The `Option` is `None` only during the
    /// private elaboration prepass; all consumers require the resulting type
    /// to be frozen before reading the value.
    ValueInitializer {
        generic_kinds: Vec<GenericKind>,
        ty: Option<Type>,
    },
    /// Aliases retain both their binder arity and their frozen target.  The
    /// normalizer substitutes these at every consuming signature boundary;
    /// aliases therefore never become runtime nominal identities.
    Alias {
        generics: u32,
        target: Type,
    },
    Constant(Option<Type>),
    /// Struct and enum applications preserve their declared binder arity even
    /// before their bodies lower to runtime layouts.
    Nominal {
        generics: u32,
        generic_kinds: Vec<GenericKind>,
        layout: ElaboratedNominalLayout,
    },
    Trait(ElaboratedTrait),
    Implementation(ElaboratedImplementation),
    Effect(ElaboratedEffect),
    Opaque,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SignatureDiagnostic {
    pub code: &'static str,
    pub message: String,
}

/// A declaration substitution could not cross a type-only boundary without
/// losing its source kind. Callers retain this error instead of turning a
/// lifetime, row, or const into `Type::Error` by accident.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InstantiationError {
    MissingDefinition,
    WrongArity {
        expected: usize,
        found: usize,
    },
    WrongKind {
        slot: usize,
        expected: GenericKind,
    },
    RequiresType {
        slot: usize,
        argument: Box<GenericArgument>,
    },
    WrongLayout,
    MissingMember,
}

#[derive(Clone, Debug, Default)]
pub struct ElaboratedInterface {
    pub definitions: BTreeMap<DefKey, ElaboratedHeader>,
    /// Host imports are interface facts rather than an ambient service map.
    /// Core snapshots this record into every direct host call before MIR.
    pub host_imports: BTreeMap<DefKey, HostImport>,
    pub diagnostics: Vec<SignatureDiagnostic>,
}

fn associated_item_contract_mismatch(
    item_kind: &str,
    name: &str,
    found_arity: u32,
    found_kinds: &[GenericKind],
    expected_arity: u32,
    expected_kinds: &[GenericKind],
) -> String {
    if found_arity != expected_arity {
        format!(
            "{item_kind} `{name}` has arity {found_arity}, but the trait requires {expected_arity}"
        )
    } else {
        format!(
            "{item_kind} `{name}` has generic kinds {found_kinds:?}, but the trait requires {expected_kinds:?}"
        )
    }
}

fn generic_binder_kinds(kinds: &[GenericKind]) -> String {
    let values = kinds
        .iter()
        .map(|kind| match kind {
            GenericKind::Type => "type".to_owned(),
            GenericKind::EffectRow => "effect row".to_owned(),
            GenericKind::Lifetime => "lifetime".to_owned(),
            GenericKind::Const(ConstKind::U32) => "u32 const".to_owned(),
            GenericKind::Const(ConstKind::Quantity) => "quantity const".to_owned(),
        })
        .collect::<Vec<_>>();
    format!("<{}>", values.join(", "))
}

fn callable_signature(header: &ElaboratedHeader) -> Option<&CallableSignature> {
    match header {
        ElaboratedHeader::Callable(signature) | ElaboratedHeader::ValueAlias { signature, .. } => {
            Some(signature)
        }
        _ => None,
    }
}

fn resolve_value_alias(
    key: DefKey,
    aliases: &BTreeMap<DefKey, (ModuleKey, Vec<String>)>,
    index: &DefinitionIndex,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    resolved: &mut BTreeMap<DefKey, (DefKey, CallableSignature)>,
    active: &mut Vec<DefKey>,
) -> Result<(DefKey, CallableSignature), String> {
    if let Some(value) = resolved.get(&key) {
        return Ok(value.clone());
    }
    if active.contains(&key) {
        return Err("value alias cycle cannot be frozen".into());
    }
    let Some((module, path)) = aliases.get(&key) else {
        return Err("value alias has no frozen target declaration".into());
    };
    active.push(key);
    let target = match index.resolve_path(DefinitionNamespace::Value, module, path) {
        ResolutionState::Resolved(target) => target,
        ResolutionState::Inaccessible(_) => {
            active.pop();
            return Err("value alias target is private to another module".into());
        }
        ResolutionState::Ambiguous(_) => {
            active.pop();
            return Err("value alias target is ambiguous".into());
        }
        ResolutionState::Unresolved | ResolutionState::Recovered => {
            match enum_constructor_alias(module, path, index, definitions) {
                Some(value) => {
                    active.pop();
                    resolved.insert(key, value.clone());
                    return Ok(value);
                }
                None => {
                    active.pop();
                    return Err("value alias target is unresolved".into());
                }
            }
        }
    };
    let value = if aliases.contains_key(&target) {
        resolve_value_alias(target, aliases, index, definitions, resolved, active)
    } else {
        definitions
            .get(&target)
            .and_then(callable_signature)
            .cloned()
            .map(|signature| (target, signature))
            .ok_or_else(|| "value alias target is not a callable value".into())
    };
    active.pop();
    if let Ok(value) = &value {
        resolved.insert(key, value.clone());
    }
    value
}

/// Enum constructors are declaration-owned values even though their identity
/// is stored in the nominal layout rather than as a synthetic source `fn`.
/// Freezing their callable shape here admits canonical forwarding declarations
/// such as `let Option::Some = Result::Ok;` without pretending the variant is
/// a module member.
fn enum_constructor_alias(
    module: &ModuleKey,
    path: &[String],
    index: &DefinitionIndex,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
) -> Option<(DefKey, CallableSignature)> {
    let (variant_name, enum_path) = path.split_last()?;
    let definition = match index.resolve_path(DefinitionNamespace::Type, module, enum_path) {
        ResolutionState::Resolved(definition) => definition,
        _ => return None,
    };
    let ElaboratedHeader::Nominal {
        generic_kinds,
        layout: ElaboratedNominalLayout::Enum(variants),
        ..
    } = definitions.get(&definition)?
    else {
        return None;
    };
    let variant = variants
        .iter()
        .find(|variant| variant.name == *variant_name)?;
    let parameters = match &variant.payload {
        ElaboratedEnumVariantPayload::Unit => vec![],
        ElaboratedEnumVariantPayload::Tuple(fields) => fields.clone(),
        ElaboratedEnumVariantPayload::Struct(fields) => {
            fields.iter().map(|field| field.ty.clone()).collect()
        }
    };
    Some((
        definition,
        CallableSignature {
            generics: generic_kinds.len() as u32,
            generic_kinds: generic_kinds.clone(),
            parameters,
            result: Type::Nominal {
                definition,
                arguments: nominal_identity_arguments(generic_kinds),
            },
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        },
    ))
}

fn fallback_structural_const(kind: ConstKind) -> GenericArgument {
    match kind {
        ConstKind::U32 => GenericArgument::ConstU32(0),
        ConstKind::Quantity => GenericArgument::ConstQuantity(Quantity::ONCE),
    }
}

/// Extract the interval carried by the language-owned `Use<Q>` relation.
/// Its prelude identity has exactly one quantity const slot; malformed source
/// is diagnosed by the principal-use validation pass instead of being treated
/// as an arbitrary trait implementation.
fn use_relation_quantity(reference: &ElaboratedTraitReference) -> Option<Quantity> {
    match reference.arguments.as_slice() {
        [GenericArgument::ConstQuantity(quantity)] => Some(*quantity),
        _ => None,
    }
}

/// Instantiate a nominal's own layout under rigid identity arguments. This
/// preserves which generic field occurrences actually contribute to layout
/// while avoiding body-local inference at the declaration boundary.
fn nominal_identity_arguments(kinds: &[GenericKind]) -> Vec<GenericArgument> {
    kinds
        .iter()
        .enumerate()
        .map(|(index, kind)| match kind {
            GenericKind::Type => GenericArgument::Type(Type::Generic(index as u32)),
            GenericKind::EffectRow => GenericArgument::EffectRow(EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(EffectTail::Generic(index as u32)),
            }),
            GenericKind::Lifetime => GenericArgument::Lifetime(Lifetime::Generic(index as u32)),
            GenericKind::Const(kind) => GenericArgument::ConstGeneric {
                index: index as u32,
                kind: *kind,
            },
        })
        .collect()
}

fn owned_nominal_layout_cycle(
    value: &Type,
    signatures: &ElaboratedInterface,
    active: &mut Vec<(DefKey, Vec<GenericArgument>)>,
) -> Option<Vec<DefKey>> {
    match value {
        Type::Nominal {
            definition,
            arguments,
        } => {
            let ElaboratedHeader::Nominal { layout, .. } =
                signatures.definitions.get(definition)?
            else {
                return None;
            };
            if let Some(index) = active.iter().position(|(seen, seen_arguments)| {
                seen == definition && seen_arguments == arguments
            }) {
                return Some(
                    active[index..]
                        .iter()
                        .map(|(definition, _)| *definition)
                        .collect(),
                );
            }
            // A declaration-only stack would reject the finite path
            // `Result<EffectRow, ()> -> EffectRow -> Result<NameUse, ()>`.
            // Distinct applications are therefore explored independently.
            // One distinct re-entry can still terminate: Result<EffectRow,
            // ()> reaches Result<Phantom<EffectRow>, ()> if Phantom erases
            // its field argument. Once the same declaration is active twice,
            // however, a further strict embedding (such as Node<T> ->
            // Node<(T, T)> -> Node<((T, T), (T, T))>) proves unbounded
            // owned growth without conflating a finite first re-entry.
            let mut prior = active
                .iter()
                .enumerate()
                .rev()
                .filter(|(_, (seen, _))| seen == definition);
            if let Some((index, (_, seen_arguments))) = prior.next()
                && prior.next().is_some()
                && nominal_arguments_expand(arguments, seen_arguments)
            {
                return Some(
                    active[index..]
                        .iter()
                        .map(|(definition, _)| *definition)
                        .collect(),
                );
            }
            active.push((*definition, arguments.clone()));
            let cycle = match layout {
                ElaboratedNominalLayout::Struct(fields) => fields.iter().find_map(|field| {
                    let field = substitute_alias_generic_identity(field.ty.clone(), arguments);
                    owned_nominal_layout_cycle(&field, signatures, active)
                }),
                ElaboratedNominalLayout::Enum(variants) => variants.iter().find_map(|variant| {
                    let fields = match &variant.payload {
                        ElaboratedEnumVariantPayload::Unit => vec![],
                        ElaboratedEnumVariantPayload::Tuple(fields) => fields.clone(),
                        ElaboratedEnumVariantPayload::Struct(fields) => {
                            fields.iter().map(|field| field.ty.clone()).collect()
                        }
                    };
                    fields.into_iter().find_map(|field| {
                        let field = substitute_alias_generic_identity(field, arguments);
                        owned_nominal_layout_cycle(&field, signatures, active)
                    })
                }),
                ElaboratedNominalLayout::Opaque => None,
            };
            active.pop();
            cycle
        }
        Type::Tuple(elements) => elements
            .iter()
            .find_map(|element| owned_nominal_layout_cycle(element, signatures, active)),
        // Arrays are heap-backed in the Stage 0 VM. The remaining forms are
        // references or executable contracts, never inline nominal storage.
        Type::Array(_) | Type::Reference { .. } | Type::Callable { .. } => None,
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => None,
        Type::Projection { .. } => {
            // Alias normalization runs before layout validation, but a
            // concrete associated type can become an inline nominal only
            // after its implementation is selected. Treating it as a leaf
            // would let an implementation hide an infinitely-sized Node
            // behind `<Node as Link>::Next`.
            let normalized = crate::TraitSolver::new(signatures)
                .normalize_type(value.clone())
                .ok()?;
            if &normalized == value {
                None
            } else {
                owned_nominal_layout_cycle(&normalized, signatures, active)
            }
        }
    }
}

/// True if a recursively reached nominal application strictly embeds an
/// argument from its earlier active application. Exact applications are
/// handled separately above; this detects unbounded generic growth without
/// conflating unrelated finite instantiations of a reusable nominal.
fn nominal_arguments_expand(current: &[GenericArgument], earlier: &[GenericArgument]) -> bool {
    current.iter().any(|current| {
        earlier
            .iter()
            .any(|earlier| generic_argument_strictly_contains(current, earlier))
    })
}

fn generic_argument_strictly_contains(
    current: &GenericArgument,
    earlier: &GenericArgument,
) -> bool {
    current != earlier && generic_argument_contains(current, earlier)
}

fn generic_argument_contains(current: &GenericArgument, earlier: &GenericArgument) -> bool {
    if current == earlier {
        return true;
    }
    match current {
        GenericArgument::Type(value) => type_contains_generic_argument(value, earlier),
        GenericArgument::EffectRow(row) => effect_row_contains_generic_argument(row, earlier),
        GenericArgument::ConstU32Expr(value) => match earlier {
            GenericArgument::ConstGeneric {
                index,
                kind: ConstKind::U32,
            } => structural_u32_contains_param(value, *index),
            GenericArgument::ConstU32Expr(earlier) => structural_u32_contains(value, earlier),
            _ => false,
        },
        GenericArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => {
            type_contains_generic_argument(subject, earlier)
                || trait_arguments
                    .iter()
                    .any(|argument| generic_argument_contains(argument, earlier))
        }
        GenericArgument::Lifetime(_)
        | GenericArgument::ConstU32(_)
        | GenericArgument::ConstQuantity(_)
        | GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn type_contains_generic_argument(value: &Type, argument: &GenericArgument) -> bool {
    if matches!(argument, GenericArgument::Type(earlier) if value == earlier) {
        return true;
    }
    match value {
        Type::Nominal { arguments, .. } => arguments
            .iter()
            .any(|current| generic_argument_contains(current, argument)),
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => {
            type_contains_generic_argument(subject, argument)
                || trait_arguments
                    .iter()
                    .chain(item_arguments)
                    .any(|current| generic_argument_contains(current, argument))
        }
        Type::Tuple(values) => values
            .iter()
            .any(|current| type_contains_generic_argument(current, argument)),
        Type::Array(value) => type_contains_generic_argument(value, argument),
        Type::Reference { referent, .. } => type_contains_generic_argument(referent, argument),
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters
                .iter()
                .any(|current| type_contains_generic_argument(current, argument))
                || type_contains_generic_argument(result, argument)
                || effect_row_contains_generic_argument(effects, argument)
        }
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => false,
    }
}

fn effect_row_contains_generic_argument(row: &EffectRow, argument: &GenericArgument) -> bool {
    row.effects.iter().any(|effect| {
        effect
            .arguments
            .iter()
            .any(|current| generic_argument_contains(current, argument))
    }) || row.projections.iter().any(|projection| {
        type_contains_generic_argument(&projection.subject, argument)
            || projection
                .trait_arguments
                .iter()
                .chain(&projection.item_arguments)
                .any(|current| generic_argument_contains(current, argument))
    })
}

fn structural_u32_contains(value: &StructuralU32Expr, earlier: &StructuralU32Expr) -> bool {
    value == earlier
        || match value {
            StructuralU32Expr::Literal(_) | StructuralU32Expr::Param(_) => false,
            StructuralU32Expr::Add(left, right)
            | StructuralU32Expr::Sub(left, right)
            | StructuralU32Expr::Mul(left, right)
            | StructuralU32Expr::Div(left, right)
            | StructuralU32Expr::Rem(left, right) => {
                structural_u32_contains(left, earlier) || structural_u32_contains(right, earlier)
            }
        }
}

fn structural_u32_contains_param(value: &StructuralU32Expr, index: u32) -> bool {
    match value {
        StructuralU32Expr::Param(current) => *current == index,
        StructuralU32Expr::Literal(_) => false,
        StructuralU32Expr::Add(left, right)
        | StructuralU32Expr::Sub(left, right)
        | StructuralU32Expr::Mul(left, right)
        | StructuralU32Expr::Div(left, right)
        | StructuralU32Expr::Rem(left, right) => {
            structural_u32_contains_param(left, index)
                || structural_u32_contains_param(right, index)
        }
    }
}

impl ElaboratedInterface {
    pub fn elaborate(interface: &PackageInterface) -> Self {
        let index = DefinitionIndex::from_interface(interface);
        let mut result = Self::elaborate_with_index(interface, &index);
        result.validate_projection_obligations();
        result
            .diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        result
            .diagnostics
            .dedup_by(|left, right| left.code == right.code && left.message == right.message);
        result
    }

    pub fn elaborate_with_index(interface: &PackageInterface, index: &DefinitionIndex) -> Self {
        let mut result = Self::default();
        for definition in &interface.definitions {
            let mut elaborator = Elaborator {
                index,
                module: &definition.module,
                generics: BTreeMap::new(),
                effect_row_generics: BTreeMap::new(),
                lifetime_generics: BTreeMap::new(),
                bound_lifetime_scopes: vec![],
                const_generics: BTreeMap::new(),
                self_type: None,
                diagnostics: vec![],
            };
            let header = elaborator.definition(definition);
            result.definitions.insert(definition.key, header);
            if let Some(capability) = &definition.host_capability {
                let Some(symbol) = &definition.name else {
                    result.diagnostics.push(SignatureDiagnostic {
                        code: "G3318",
                        message: "host import declaration has no callable identity".into(),
                    });
                    continue;
                };
                result.host_imports.insert(
                    definition.key,
                    HostImport {
                        capability: capability.clone(),
                        symbol: symbol.clone(),
                    },
                );
            }
            result.diagnostics.extend(elaborator.diagnostics);
        }
        result.normalize_aliases();
        result.resolve_value_aliases(interface, index);
        result.validate_owned_nominal_layout_recursion();
        result.validate_associated_type_definitions();
        result.validate_trait_supertrait_cycles();
        result.validate_implementation_supertraits();
        result
            .diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        result
    }

    pub fn merge(parts: impl IntoIterator<Item = ElaboratedInterface>) -> Self {
        let mut merged = Self::default();
        for part in parts {
            merged.definitions.extend(part.definitions);
            merged.host_imports.extend(part.host_imports);
            merged.diagnostics.extend(part.diagnostics);
        }
        merged.normalize_aliases();
        merged.validate_owned_nominal_layout_recursion();
        merged.validate_associated_type_definitions();
        merged.validate_trait_supertrait_cycles();
        merged.validate_implementation_supertraits();
        merged.validate_projection_obligations();
        merged
            .diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        merged
    }

    /// Normalize a body-local type annotation through the frozen transparent
    /// alias table. Header elaboration already performs this while freezing
    /// declarations; typed closures need the same identity-preserving bridge
    /// for aliases written inside a body.
    pub fn normalize_type_aliases(&self, value: Type) -> Type {
        normalize_alias_type(value, &self.definitions, &mut vec![], &mut vec![])
    }

    pub fn value_alias_target(&self, definition: DefKey) -> Option<DefKey> {
        match self.definitions.get(&definition) {
            Some(ElaboratedHeader::ValueAlias { target, .. }) => Some(*target),
            _ => None,
        }
    }

    pub fn freeze_value_initializer(
        &mut self,
        definition: DefKey,
        generic_kinds: Vec<GenericKind>,
        ty: Type,
    ) {
        self.definitions.insert(
            definition,
            ElaboratedHeader::ValueInitializer {
                generic_kinds,
                ty: Some(ty),
            },
        );
    }

    /// Validate the language-owned `Use` relation once every nominal layout
    /// has been frozen.  Unlike ordinary trait selection, `Use` has a single
    /// principal interval per type: source implementations may narrow the
    /// structural interval, but cannot add an alternative capability.
    pub fn validate_principal_use_rules(&self) -> Vec<SignatureDiagnostic> {
        let mut diagnostics = Vec::new();

        for implementation in self.definitions.values().filter_map(|header| match header {
            ElaboratedHeader::Implementation(implementation)
                if implementation.relation.definition
                    == crate::resolution::language_use_trait_definition() =>
            {
                Some(implementation)
            }
            _ => None,
        }) {
            let Some(declared) = use_relation_quantity(&implementation.relation) else {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4194",
                    message: "a `Use` implementation must declare exactly one quantity interval"
                        .into(),
                });
                continue;
            };
            if !matches!(implementation.self_ty, Type::Nominal { .. }) {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4194",
                    message: "manual `Use` implementations are restricted to nominal types".into(),
                });
                continue;
            }
            let Some(structural) =
                self.structural_principal_use(&implementation.self_ty, &mut vec![])
            else {
                // A type parameter without an ownership contract has no
                // closed interval at an interface boundary.  Its concrete
                // applications are checked when they become ownership
                // relevant; do not invent an interval here.
                continue;
            };
            if !structural.contains(declared) {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4194",
                    message: format!(
                        "manual `Use` interval {:?} widens the structural principal interval {:?}",
                        declared, structural
                    ),
                });
            }
        }

        // Derive each declared nominal with rigid identity arguments. This
        // catches incompatible field requirements even when the nominal is
        // never constructed by a body in the current package.
        for (definition, header) in &self.definitions {
            let ElaboratedHeader::Nominal {
                generic_kinds,
                layout,
                ..
            } = header
            else {
                continue;
            };
            let nominal = Type::Nominal {
                definition: *definition,
                arguments: nominal_identity_arguments(generic_kinds),
            };
            if let Some((left, right)) =
                self.empty_direct_structural_use_intersection(layout, &nominal)
            {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4195",
                    message: format!(
                        "structural principal use quantity intersection is empty between {:?} and {:?}",
                        left, right
                    ),
                });
            }
        }

        diagnostics
    }

    /// Return the one principal interval for a closed type. `None` means the
    /// type still contains an unconstrained generic or projection and must be
    /// resolved at its concrete use site.
    pub fn principal_use_interval(&self, ty: &Type) -> Option<Quantity> {
        self.principal_use(ty, &mut vec![])
    }

    fn principal_use(&self, ty: &Type, active: &mut Vec<Type>) -> Option<Quantity> {
        self.manual_principal_use(ty)
            .or_else(|| self.structural_principal_use(ty, active))
    }

    fn manual_principal_use(&self, ty: &Type) -> Option<Quantity> {
        self.definitions.values().find_map(|header| {
            let ElaboratedHeader::Implementation(implementation) = header else {
                return None;
            };
            (implementation.relation.definition
                == crate::resolution::language_use_trait_definition()
                && implementation.self_ty == *ty)
                .then(|| use_relation_quantity(&implementation.relation))
                .flatten()
        })
    }

    fn structural_principal_use(&self, ty: &Type, active: &mut Vec<Type>) -> Option<Quantity> {
        match ty {
            Type::Unit | Type::Never | Type::Scalar(_) => Some(Quantity::UNRESTRICTED),
            Type::Tuple(values) => {
                values
                    .iter()
                    .try_fold(Quantity::UNRESTRICTED, |quantity, value| {
                        let field = self.principal_use(value, active)?;
                        quantity.intersection(field).ok()
                    })
            }
            // An array is moved as one aggregate, but every element must be
            // legal under that aggregate's interval.
            Type::Array(value) => self.principal_use(value, active),
            Type::Reference { mutability, .. } => Some(match mutability {
                Mutability::Shared => Quantity::UNRESTRICTED,
                Mutability::Unique => Quantity::AFFINE,
            }),
            Type::Callable { invocation, .. } => Some(*invocation),
            Type::Nominal {
                definition,
                arguments,
            } => {
                if active.iter().any(|value| value == ty) {
                    return None;
                }
                active.push(ty.clone());
                let result = match self.definitions.get(definition) {
                    Some(ElaboratedHeader::Nominal { layout, .. }) => match layout {
                        ElaboratedNominalLayout::Struct(fields) => {
                            fields
                                .iter()
                                .try_fold(Quantity::UNRESTRICTED, |quantity, field| {
                                    let field = substitute_alias_generic_identity(
                                        field.ty.clone(),
                                        arguments,
                                    );
                                    let field = self.principal_use(&field, active)?;
                                    quantity.intersection(field).ok()
                                })
                        }
                        ElaboratedNominalLayout::Enum(variants) => {
                            variants
                                .iter()
                                .try_fold(Quantity::UNRESTRICTED, |quantity, variant| {
                                    let fields: Vec<Type> = match &variant.payload {
                                        ElaboratedEnumVariantPayload::Unit => vec![],
                                        ElaboratedEnumVariantPayload::Tuple(fields) => {
                                            fields.clone()
                                        }
                                        ElaboratedEnumVariantPayload::Struct(fields) => {
                                            fields.iter().map(|field| field.ty.clone()).collect()
                                        }
                                    };
                                    fields.into_iter().try_fold(quantity, |quantity, field| {
                                        let field =
                                            substitute_alias_generic_identity(field, arguments);
                                        let field = self.principal_use(&field, active)?;
                                        quantity.intersection(field).ok()
                                    })
                                })
                        }
                        ElaboratedNominalLayout::Opaque => None,
                    },
                    // `Available<E>` and opaque language carriers do not
                    // have a source-owned structural layout.
                    _ => None,
                };
                active.pop();
                result
            }
            Type::Generic(_)
            | Type::Infer(_)
            | Type::Error
            | Type::Projection { .. }
            | Type::ConstU32(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. } => None,
        }
    }

    /// Find an empty direct field/variant intersection in a nominal layout.
    /// Unknown generic fields are intentionally deferred, while two known
    /// intervals which cannot coexist are an unconditional interface error.
    fn empty_direct_structural_use_intersection(
        &self,
        layout: &ElaboratedNominalLayout,
        nominal: &Type,
    ) -> Option<(Quantity, Quantity)> {
        let Type::Nominal { arguments, .. } = nominal else {
            return None;
        };
        let mut fields = Vec::new();
        match layout {
            ElaboratedNominalLayout::Struct(values) => {
                fields.extend(values.iter().map(|field| field.ty.clone()));
            }
            ElaboratedNominalLayout::Enum(variants) => {
                for variant in variants {
                    match &variant.payload {
                        ElaboratedEnumVariantPayload::Unit => {}
                        ElaboratedEnumVariantPayload::Tuple(values) => {
                            fields.extend(values.clone())
                        }
                        ElaboratedEnumVariantPayload::Struct(values) => {
                            fields.extend(values.iter().map(|field| field.ty.clone()));
                        }
                    }
                }
            }
            ElaboratedNominalLayout::Opaque => return None,
        }
        let mut quantity = Quantity::UNRESTRICTED;
        for field in fields {
            let field = substitute_alias_generic_identity(field, arguments);
            let Some(field) = self.principal_use_interval(&field) else {
                continue;
            };
            if quantity.intersection(field).is_err() {
                return Some((quantity, field));
            }
            quantity = quantity
                .intersection(field)
                .expect("nonempty interval was checked");
        }
        None
    }

    pub fn instantiate_value_initializer_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
    ) -> Result<Type, InstantiationError> {
        let ElaboratedHeader::ValueInitializer {
            generic_kinds,
            ty: Some(ty),
        } = self
            .definitions
            .get(&definition)
            .ok_or(InstantiationError::MissingDefinition)?
        else {
            return Err(InstantiationError::WrongLayout);
        };
        validate_generic_arguments(generic_kinds, arguments)?;
        Ok(substitute_alias_generic_identity(ty.clone(), arguments))
    }

    fn resolve_value_aliases(&mut self, interface: &PackageInterface, index: &DefinitionIndex) {
        let aliases = interface
            .definitions
            .iter()
            .filter_map(|definition| match &definition.syntax.header {
                ParsedHeader::ValueAlias { target, .. } => {
                    Some((definition.key, (definition.module.clone(), target.clone())))
                }
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut resolved = BTreeMap::new();
        for key in aliases.keys().copied().collect::<Vec<_>>() {
            let mut active = vec![];
            match resolve_value_alias(
                key,
                &aliases,
                index,
                &self.definitions,
                &mut resolved,
                &mut active,
            ) {
                Ok((target, signature)) => {
                    self.definitions
                        .insert(key, ElaboratedHeader::ValueAlias { target, signature });
                }
                Err(message) => self.diagnostics.push(SignatureDiagnostic {
                    code: "G3340",
                    message,
                }),
            }
        }
    }

    /// Reject layouts that would require an infinitely-sized owned value.
    /// Alias normalization runs first, so this graph is expressed solely in
    /// nominal identity rather than source spelling. References, callables,
    /// and Stage 0 arrays are runtime handles and therefore terminate an
    /// owned-layout path; tuples and nominal fields remain inline.
    fn validate_owned_nominal_layout_recursion(&mut self) {
        let signatures = ElaboratedInterface {
            definitions: self.definitions.clone(),
            host_imports: self.host_imports.clone(),
            diagnostics: vec![],
        };
        let mut reported = BTreeSet::<Vec<DefKey>>::new();
        let mut diagnostics = vec![];
        for (definition, header) in &signatures.definitions {
            let ElaboratedHeader::Nominal { generic_kinds, .. } = header else {
                continue;
            };
            let root = Type::Nominal {
                definition: *definition,
                arguments: nominal_identity_arguments(generic_kinds),
            };
            let mut active = vec![];
            if let Some(cycle) = owned_nominal_layout_cycle(&root, &signatures, &mut active) {
                let mut members = cycle;
                members.sort();
                members.dedup();
                if reported.insert(members.clone()) {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G3320",
                        message: format!(
                            "owned nominal layout recursion includes {}",
                            members
                                .iter()
                                .map(|definition| format!("{definition:?}"))
                                .collect::<Vec<_>>()
                                .join(", ")
                        ),
                    });
                }
            }
        }
        self.diagnostics.extend(diagnostics);
    }

    fn validate_associated_type_definitions(&mut self) {
        let mut diagnostics = Vec::new();
        for implementation in self.definitions.values().filter_map(|header| match header {
            ElaboratedHeader::Implementation(implementation) => Some(implementation),
            _ => None,
        }) {
            if implementation.negative {
                let mut items = implementation
                    .associated_types
                    .keys()
                    .map(|name| format!("associated type `{name}`"))
                    .chain(
                        implementation
                            .associated_effect_rows
                            .keys()
                            .map(|name| format!("associated effect row `{name}`")),
                    )
                    .chain(
                        implementation
                            .associated_consts
                            .keys()
                            .map(|name| format!("associated constant `{name}`")),
                    )
                    .chain(
                        implementation
                            .methods
                            .keys()
                            .map(|name| format!("method `{name}`")),
                    )
                    .collect::<Vec<_>>();
                items.sort();
                if !items.is_empty() {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G4149",
                        message: format!(
                            "negative implementation cannot define {}",
                            items.join(", ")
                        ),
                    });
                }
                continue;
            }
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.definitions.get(&implementation.relation.definition)
            else {
                continue;
            };
            for (name, item) in &implementation.associated_types {
                match trait_header.associated_types.get(name) {
                    Some(expected) if expected.effect_row => {
                        diagnostics.push(SignatureDiagnostic {
                            code: "G4116",
                            message: format!(
                                "associated effect row `{name}` requires a row literal definition"
                            ),
                        })
                    }
                    Some(expected)
                        if expected.generics == item.generics
                            && expected.generic_kinds == item.generic_kinds => {}
                    Some(expected) => diagnostics.push(SignatureDiagnostic {
                        code: "G4114",
                        message: associated_item_contract_mismatch(
                            "associated type",
                            name,
                            item.generics,
                            &item.generic_kinds,
                            expected.generics,
                            &expected.generic_kinds,
                        ),
                    }),
                    None => diagnostics.push(SignatureDiagnostic {
                        code: "G4115",
                        message: format!("implementation defines unknown associated type `{name}`"),
                    }),
                }
            }
            for (name, item) in &implementation.associated_effect_rows {
                match trait_header.associated_types.get(name) {
                    Some(expected) if !expected.effect_row => diagnostics.push(SignatureDiagnostic {
                        code: "G4116",
                        message: format!("associated type `{name}` cannot be defined with an effect-row literal"),
                    }),
                    Some(expected)
                        if expected.generics == item.generics
                            && expected.generic_kinds == item.generic_kinds => {}
                    Some(expected) => diagnostics.push(SignatureDiagnostic {
                        code: "G4114",
                        message: associated_item_contract_mismatch(
                            "associated effect row",
                            name,
                            item.generics,
                            &item.generic_kinds,
                            expected.generics,
                            &expected.generic_kinds,
                        ),
                    }),
                    None => diagnostics.push(SignatureDiagnostic {
                        code: "G4115",
                        message: format!("implementation defines unknown associated effect row `{name}`"),
                    }),
                }
            }
            for (name, declaration) in &trait_header.associated_types {
                if !implementation.associated_types.contains_key(name)
                    && !implementation.associated_effect_rows.contains_key(name)
                    && declaration.default.is_none()
                    && declaration.effect_row_default.is_none()
                {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G4116",
                        message: format!("implementation omits associated type `{name}`"),
                    });
                }
            }
            for (name, item) in &implementation.associated_consts {
                match trait_header.associated_consts.get(name) {
                    Some(expected) if expected.kind == item.kind => {}
                    Some(expected) => diagnostics.push(SignatureDiagnostic {
                        code: "G4160",
                        message: format!(
                            "associated constant `{name}` has kind {:?} but the trait requires {:?}",
                            item.kind, expected.kind
                        ),
                    }),
                    None => diagnostics.push(SignatureDiagnostic {
                        code: "G4161",
                        message: format!("implementation defines unknown associated constant `{name}`"),
                    }),
                }
            }
            for (name, item) in &trait_header.associated_consts {
                if !implementation.associated_consts.contains_key(name) && item.default.is_none() {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G4162",
                        message: format!("implementation omits associated constant `{name}`"),
                    });
                }
            }
            for (name, method) in &implementation.methods {
                match trait_header.methods.get(name) {
                    // Binder arity is only half of a universally quantified
                    // method contract.  In particular, a lifetime binder
                    // cannot stand in for a type, const, or effect-row
                    // binder just because both occupy one generic slot.  The
                    // body signature may not mention a marker binder at all,
                    // so comparing the elaborated parameter/result types
                    // alone would otherwise let this mismatch through.
                    Some(expected)
                        if expected.generics == method.generics
                            && expected.generic_kinds == method.generic_kinds =>
                    {
                        let required = instantiate_trait_method_contract(
                            expected,
                            implementation,
                        );
                        if required != *method {
                            diagnostics.push(SignatureDiagnostic {
                                code: "G4147",
                                message: format!(
                                    "implementation method `{name}` does not match the required trait contract"
                                ),
                            });
                        }
                    }
                    Some(expected) => diagnostics.push(SignatureDiagnostic {
                        code: "G4119",
                        message: format!(
                            "implementation method `{name}` has incompatible generic binders: {} but the trait requires {}",
                            generic_binder_kinds(&method.generic_kinds),
                            generic_binder_kinds(&expected.generic_kinds),
                        ),
                    }),
                    None => diagnostics.push(SignatureDiagnostic {
                        code: "G4120",
                        message: format!("implementation defines unknown trait method `{name}`"),
                    }),
                }
            }
            for name in trait_header.methods.keys() {
                if !implementation.methods.contains_key(name) {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G4121",
                        message: format!("implementation omits trait method `{name}`"),
                    });
                }
            }
        }
        self.diagnostics.extend(diagnostics);
    }

    /// A positive implementation of a subtrait must establish every declared
    /// supertrait for the same self type and instantiated trait arguments.
    ///
    /// This deliberately validates the implication at interface time instead
    /// of treating a `Child` implementation as synthetic `Parent` method
    /// evidence.  The latter would let `Parent::method` select a `Child`
    /// implementation that contains no parent method body.  Requiring direct
    /// parent evidence retains one callable identity per selected impl while
    /// making declared supertrait contracts semantically meaningful.
    fn validate_implementation_supertraits(&mut self) {
        use crate::{TraitAnswer, TraitGoal, TraitSolver};

        let implementations = self
            .definitions
            .values()
            .filter_map(|header| match header {
                ElaboratedHeader::Implementation(implementation) if !implementation.negative => {
                    Some(implementation.clone())
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        let solver = TraitSolver::new(self);
        let mut diagnostics = Vec::new();
        for implementation in implementations {
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.definitions.get(&implementation.relation.definition)
            else {
                continue;
            };
            // The implementation's where clause is lexical evidence for its
            // own supertrait contract. Do not add the implementation relation
            // itself here: doing so would assume the very `Child` fact this
            // validation is responsible for proving. The solver keeps these
            // facts scoped, so they cannot turn into ambient global impls.
            let assumptions = implementation
                .where_bounds
                .iter()
                .map(|(subject, relation)| TraitGoal {
                    relation: relation.clone(),
                    subject: subject.clone(),
                })
                .collect::<Vec<_>>();
            for supertrait in &trait_header.supertraits {
                let relation = replace_trait_self_trait_reference(
                    substitute_trait_reference(supertrait, &implementation.relation.arguments),
                    &implementation.self_ty,
                );
                let goal = TraitGoal {
                    relation: relation.clone(),
                    subject: implementation.self_ty.clone(),
                };
                match solver.solve_with_assumptions(goal, &assumptions) {
                    TraitAnswer::Proven { .. } => {}
                    TraitAnswer::Refuted { .. } => diagnostics.push(SignatureDiagnostic {
                        code: "G4148",
                        message: "implementation of a subtrait is refuted by a required supertrait"
                            .into(),
                    }),
                    TraitAnswer::NoSolution => diagnostics.push(SignatureDiagnostic {
                        code: "G4148",
                        message: "implementation does not prove a required supertrait".into(),
                    }),
                    TraitAnswer::Ambiguous => diagnostics.push(SignatureDiagnostic {
                        code: "G4148",
                        message: "implementation has ambiguous evidence for a required supertrait"
                            .into(),
                    }),
                    TraitAnswer::Overflow => diagnostics.push(SignatureDiagnostic {
                        code: "G4148",
                        message: "implementation overflows while proving a required supertrait"
                            .into(),
                    }),
                }
            }
        }
        self.diagnostics.extend(diagnostics);
    }

    /// Every symbolic associated selection published in an interface carries
    /// a trait obligation.  Keeping `<T as Trait>::Item` as a symbolic term
    /// is sound only when the declaration contract establishes `T: Trait`;
    /// otherwise downstream callers could instantiate an API that never had
    /// evidence for the selected item.  Concrete heads use the same frozen
    /// solver so negative impls and ambiguities remain distinct from a
    /// missing generic bound.
    ///
    /// This validation intentionally runs on the merged interface as well as
    /// single-package interfaces.  Candidate discovery is global: validating
    /// a module fragment before imported implementations are available would
    /// turn a valid concrete projection into a module-order-dependent error.
    pub fn validate_projection_obligations(&mut self) {
        let definitions = self.definitions.clone();
        let mut diagnostics = Vec::new();

        for (definition, header) in &definitions {
            if *definition == intrinsic_callable_trait_definition() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4169",
                    message: "frozen interfaces cannot define the intrinsic `Fn` trait identity"
                        .into(),
                });
            }
            if *definition == intrinsic_label_trait_definition() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4172",
                    message: "frozen interfaces cannot define the intrinsic `Label` trait identity"
                        .into(),
                });
            }
            if *definition == intrinsic_runs_in_trait_definition() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4173",
                    message:
                        "frozen interfaces cannot define the intrinsic `RunsIn` trait identity"
                            .into(),
                });
            }
            match header {
                ElaboratedHeader::Callable(signature)
                | ElaboratedHeader::ValueAlias { signature, .. } => {
                    self.validate_callable_projection_obligations(
                        signature,
                        vec![],
                        &mut diagnostics,
                    );
                }
                ElaboratedHeader::Alias { target, .. } => {
                    self.validate_type_projection_obligations(target, &[], &mut diagnostics);
                }
                ElaboratedHeader::Constant(Some(ty))
                | ElaboratedHeader::ValueInitializer { ty: Some(ty), .. } => {
                    self.validate_type_projection_obligations(ty, &[], &mut diagnostics);
                }
                ElaboratedHeader::Nominal { layout, .. } => match layout {
                    ElaboratedNominalLayout::Struct(fields) => {
                        for field in fields {
                            self.validate_type_projection_obligations(
                                &field.ty,
                                &[],
                                &mut diagnostics,
                            );
                        }
                    }
                    ElaboratedNominalLayout::Enum(variants) => {
                        for variant in variants {
                            let fields = match &variant.payload {
                                ElaboratedEnumVariantPayload::Unit => &[][..],
                                ElaboratedEnumVariantPayload::Tuple(fields) => fields.as_slice(),
                                ElaboratedEnumVariantPayload::Struct(fields) => {
                                    // Named fields need a borrowed type view without changing
                                    // their declaration-owned order.
                                    for field in fields {
                                        self.validate_type_projection_obligations(
                                            &field.ty,
                                            &[],
                                            &mut diagnostics,
                                        );
                                    }
                                    continue;
                                }
                            };
                            for field in fields {
                                self.validate_type_projection_obligations(
                                    field,
                                    &[],
                                    &mut diagnostics,
                                );
                            }
                        }
                    }
                    ElaboratedNominalLayout::Opaque => {}
                },
                ElaboratedHeader::Trait(trait_header) => {
                    let self_relation = ElaboratedTraitReference {
                        definition: *definition,
                        arguments: nominal_identity_arguments(&trait_header.generic_kinds),
                    };
                    let ambient = vec![(Type::Generic(TRAIT_SELF_GENERIC), self_relation)];
                    for supertrait in &trait_header.supertraits {
                        self.validate_trait_reference_projection_obligations(
                            supertrait,
                            &ambient,
                            &mut diagnostics,
                        );
                    }
                    for item in trait_header.associated_types.values() {
                        if let Some(default) = &item.default {
                            self.validate_type_projection_obligations(
                                default,
                                &ambient,
                                &mut diagnostics,
                            );
                        }
                        if let Some(default) = &item.effect_row_default {
                            self.validate_effect_row_projection_obligations(
                                default,
                                &ambient,
                                &mut diagnostics,
                            );
                        }
                    }
                    for item in trait_header.associated_consts.values() {
                        if let Some(default) = &item.default {
                            self.validate_generic_argument_projection_obligations(
                                default,
                                &ambient,
                                &mut diagnostics,
                            );
                        }
                    }
                    for method in trait_header.methods.values() {
                        self.validate_callable_projection_obligations(
                            method,
                            ambient.clone(),
                            &mut diagnostics,
                        );
                    }
                }
                ElaboratedHeader::Implementation(implementation) => {
                    if is_intrinsic_callable_trait(&implementation.relation) {
                        diagnostics.push(SignatureDiagnostic {
                            code: "G4169",
                            message: "frozen interfaces cannot implement the intrinsic `Fn` trait"
                                .into(),
                        });
                    }
                    if is_intrinsic_label_trait(&implementation.relation) {
                        diagnostics.push(SignatureDiagnostic {
                            code: "G4172",
                            message:
                                "frozen interfaces cannot implement the intrinsic `Label` trait"
                                    .into(),
                        });
                    }
                    if is_intrinsic_runs_in_trait(&implementation.relation) {
                        diagnostics.push(SignatureDiagnostic {
                            code: "G4173",
                            message:
                                "frozen interfaces cannot implement the intrinsic `RunsIn` trait"
                                    .into(),
                        });
                    }
                    let mut ambient = implementation.where_bounds.clone();
                    ambient.push((
                        implementation.self_ty.clone(),
                        implementation.relation.clone(),
                    ));
                    self.validate_trait_reference_projection_obligations(
                        &implementation.relation,
                        &ambient,
                        &mut diagnostics,
                    );
                    self.validate_type_projection_obligations(
                        &implementation.self_ty,
                        &ambient,
                        &mut diagnostics,
                    );
                    for (subject, relation) in &implementation.where_bounds {
                        self.validate_type_projection_obligations(
                            subject,
                            &ambient,
                            &mut diagnostics,
                        );
                        self.validate_trait_reference_projection_obligations(
                            relation,
                            &ambient,
                            &mut diagnostics,
                        );
                    }
                    for item in implementation.associated_types.values() {
                        self.validate_type_projection_obligations(
                            &item.value,
                            &ambient,
                            &mut diagnostics,
                        );
                    }
                    for item in implementation.associated_effect_rows.values() {
                        self.validate_effect_row_projection_obligations(
                            &item.value,
                            &ambient,
                            &mut diagnostics,
                        );
                    }
                    for item in implementation.associated_consts.values() {
                        self.validate_generic_argument_projection_obligations(
                            &item.value,
                            &ambient,
                            &mut diagnostics,
                        );
                    }
                    for method in implementation.methods.values() {
                        self.validate_callable_projection_obligations(
                            method,
                            ambient.clone(),
                            &mut diagnostics,
                        );
                    }
                }
                ElaboratedHeader::Effect(effect) => {
                    for operation in &effect.operations {
                        for parameter in &operation.parameters {
                            self.validate_type_projection_obligations(
                                parameter,
                                &[],
                                &mut diagnostics,
                            );
                        }
                        self.validate_type_projection_obligations(
                            &operation.result,
                            &[],
                            &mut diagnostics,
                        );
                    }
                }
                ElaboratedHeader::Constant(None)
                | ElaboratedHeader::ValueInitializer { ty: None, .. }
                | ElaboratedHeader::Opaque => {}
            }
        }
        self.diagnostics.extend(diagnostics);
        self.diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        self.diagnostics
            .dedup_by(|left, right| left.code == right.code && left.message == right.message);
    }

    /// Validate type terms crossing a later frozen boundary (Typed Core,
    /// persisted instance metadata, or a hand-built test fixture) against the
    /// declaration's lexical trait evidence.  Interface validation calls the
    /// same kernel above; this public read-only entry point prevents Core
    /// consumers from recreating a weaker, type-only projection rule.
    pub fn projection_obligation_diagnostics(
        &self,
        types: &[Type],
        ambient: &[(Type, ElaboratedTraitReference)],
    ) -> Vec<SignatureDiagnostic> {
        self.projection_obligation_diagnostics_for_frozen_terms(
            types.iter(),
            std::iter::empty(),
            std::iter::empty(),
            ambient,
        )
    }

    /// Validate every kinded term retained by a frozen semantic product.
    ///
    /// A projection can be nested in a declaration substitution or effect
    /// row without appearing inside a value `Type`.  Core and persisted
    /// metadata use this entry point so those carriers receive exactly the
    /// same lexical-evidence check as declaration signatures.
    pub fn projection_obligation_diagnostics_for_frozen_terms<'a>(
        &self,
        types: impl IntoIterator<Item = &'a Type>,
        arguments: impl IntoIterator<Item = &'a GenericArgument>,
        effect_rows: impl IntoIterator<Item = &'a EffectRow>,
        ambient: &[(Type, ElaboratedTraitReference)],
    ) -> Vec<SignatureDiagnostic> {
        let mut diagnostics = Vec::new();
        for ty in types {
            self.validate_type_projection_obligations(ty, ambient, &mut diagnostics);
        }
        for argument in arguments {
            self.validate_generic_argument_projection_obligations(
                argument,
                ambient,
                &mut diagnostics,
            );
        }
        for row in effect_rows {
            self.validate_effect_row_projection_obligations(row, ambient, &mut diagnostics);
        }
        diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        diagnostics
            .dedup_by(|left, right| left.code == right.code && left.message == right.message);
        diagnostics
    }

    fn validate_callable_projection_obligations(
        &self,
        signature: &CallableSignature,
        mut ambient: Vec<(Type, ElaboratedTraitReference)>,
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        ambient.extend(signature.where_bounds.clone());
        for parameter in &signature.parameters {
            self.validate_type_projection_obligations(parameter, &ambient, diagnostics);
        }
        self.validate_type_projection_obligations(&signature.result, &ambient, diagnostics);
        self.validate_effect_row_projection_obligations(&signature.effects, &ambient, diagnostics);
        for (subject, relation) in &signature.where_bounds {
            self.validate_type_projection_obligations(subject, &ambient, diagnostics);
            self.validate_trait_reference_projection_obligations(relation, &ambient, diagnostics);
            if is_intrinsic_callable_trait(relation) {
                self.validate_intrinsic_callable_bound(signature, subject, relation, diagnostics);
            }
            if is_intrinsic_label_trait(relation) {
                self.validate_intrinsic_label_bound(subject, relation, diagnostics);
            }
        }
        for binding in &signature.where_associated_type_bindings {
            self.validate_type_projection_obligations(&binding.subject, &ambient, diagnostics);
            self.validate_trait_reference_projection_obligations(
                &binding.relation,
                &ambient,
                diagnostics,
            );
            for argument in &binding.item_arguments {
                self.validate_generic_argument_projection_obligations(
                    argument,
                    &ambient,
                    diagnostics,
                );
            }
            self.validate_type_projection_obligations(&binding.value, &ambient, diagnostics);
        }
        for binding in &signature.where_associated_effect_bindings {
            self.validate_type_projection_obligations(&binding.subject, &ambient, diagnostics);
            self.validate_trait_reference_projection_obligations(
                &binding.relation,
                &ambient,
                diagnostics,
            );
            for argument in &binding.item_arguments {
                self.validate_generic_argument_projection_obligations(
                    argument,
                    &ambient,
                    diagnostics,
                );
            }
            self.validate_effect_row_projection_obligations(&binding.value, &ambient, diagnostics);
        }
    }

    /// Validate the frozen shape of compiler-owned callable evidence.  Source
    /// generics may carry an `Fn` contract without being callable yet, but a
    /// concrete callable cannot lie about its inputs, result, or outward row.
    /// This also rejects manually forged interfaces before a solver could use
    /// their relation as evidence.
    fn validate_intrinsic_callable_bound(
        &self,
        signature: &CallableSignature,
        subject: &Type,
        relation: &ElaboratedTraitReference,
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        let inputs = match relation.arguments.as_slice() {
            [GenericArgument::Type(Type::Tuple(inputs))] => Some(inputs.as_slice()),
            [GenericArgument::Type(Type::Unit)] => Some(&[] as &[Type]),
            _ => {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4164",
                    message: "intrinsic `Fn` requires exactly one tuple input argument".into(),
                });
                None
            }
        };
        let type_bindings = signature
            .where_associated_type_bindings
            .iter()
            .filter(|binding| binding.subject == *subject && binding.relation == *relation)
            .collect::<Vec<_>>();
        let effect_bindings = signature
            .where_associated_effect_bindings
            .iter()
            .filter(|binding| binding.subject == *subject && binding.relation == *relation)
            .collect::<Vec<_>>();
        for binding in &type_bindings {
            if binding.name != "Output" || !binding.item_arguments.is_empty() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4165",
                    message: "intrinsic `Fn` only accepts `Output = Type`".into(),
                });
            }
        }
        for binding in &effect_bindings {
            if binding.name != "Effects" || !binding.item_arguments.is_empty() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4165",
                    message: "intrinsic `Fn` only accepts `Effects = Row`".into(),
                });
            }
        }
        let Type::Callable {
            parameters,
            result,
            effects,
            ..
        } = subject
        else {
            return;
        };
        if inputs.is_some_and(|inputs| inputs != parameters) {
            diagnostics.push(SignatureDiagnostic {
                code: "G4166",
                message: "intrinsic `Fn` input tuple does not match callable parameters".into(),
            });
        }
        if type_bindings.len() > 1 || effect_bindings.len() > 1 {
            diagnostics.push(SignatureDiagnostic {
                code: "G4165",
                message: "intrinsic `Fn` has duplicate associated equality bindings".into(),
            });
        }
        if let Some(binding) = type_bindings.first()
            && binding.name == "Output"
            && binding.value != **result
        {
            diagnostics.push(SignatureDiagnostic {
                code: "G4167",
                message: "intrinsic `Fn` Output equality does not match callable result".into(),
            });
        }
        if let Some(binding) = effect_bindings.first()
            && binding.name == "Effects"
            && binding.value != *effects
        {
            diagnostics.push(SignatureDiagnostic {
                code: "G4168",
                message: "intrinsic `Fn` Effects equality does not match callable effects".into(),
            });
        }
    }

    /// A label value is an escaping one-argument callable.  The concrete
    /// `Never` result prevents an ordinary returning callback from acquiring
    /// nonlocal-exit authority merely by matching the `Label` spelling.
    fn validate_intrinsic_label_bound(
        &self,
        subject: &Type,
        relation: &ElaboratedTraitReference,
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        let [GenericArgument::Type(payload)] = relation.arguments.as_slice() else {
            diagnostics.push(SignatureDiagnostic {
                code: "G4170",
                message: "intrinsic `Label` requires exactly one payload type argument".into(),
            });
            return;
        };
        let Type::Callable {
            parameters, result, ..
        } = subject
        else {
            return;
        };
        if parameters.as_slice() != [payload.clone()] || !matches!(result.as_ref(), Type::Never) {
            diagnostics.push(SignatureDiagnostic {
                code: "G4171",
                message: "intrinsic `Label<B>` requires an escaping callable `(B) -> !`".into(),
            });
        }
    }

    fn validate_type_projection_obligations(
        &self,
        value: &Type,
        ambient: &[(Type, ElaboratedTraitReference)],
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        match value {
            Type::Nominal { arguments, .. } => {
                for argument in arguments {
                    self.validate_generic_argument_projection_obligations(
                        argument,
                        ambient,
                        diagnostics,
                    );
                }
            }
            Type::Projection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                item_arguments,
                ..
            } => {
                self.validate_type_projection_obligations(subject, ambient, diagnostics);
                for argument in trait_arguments.iter().chain(item_arguments) {
                    self.validate_generic_argument_projection_obligations(
                        argument,
                        ambient,
                        diagnostics,
                    );
                }
                self.validate_projection_goal(
                    "type",
                    subject,
                    &ElaboratedTraitReference {
                        definition: *trait_definition,
                        arguments: trait_arguments.clone(),
                    },
                    name,
                    ambient,
                    diagnostics,
                );
            }
            Type::Tuple(values) => {
                for value in values {
                    self.validate_type_projection_obligations(value, ambient, diagnostics);
                }
            }
            Type::Array(value) => {
                self.validate_type_projection_obligations(value, ambient, diagnostics)
            }
            Type::Reference { referent, .. } => {
                self.validate_type_projection_obligations(referent, ambient, diagnostics);
            }
            Type::Callable {
                parameters,
                result,
                effects,
                ..
            } => {
                for parameter in parameters {
                    self.validate_type_projection_obligations(parameter, ambient, diagnostics);
                }
                self.validate_type_projection_obligations(result, ambient, diagnostics);
                self.validate_effect_row_projection_obligations(effects, ambient, diagnostics);
            }
            Type::Unit
            | Type::Never
            | Type::Scalar(_)
            | Type::ConstU32(_)
            | Type::ConstQuantity(_)
            | Type::ConstGeneric { .. }
            | Type::Generic(_)
            | Type::Infer(_)
            | Type::Error => {}
        }
    }

    fn validate_effect_row_projection_obligations(
        &self,
        row: &EffectRow,
        ambient: &[(Type, ElaboratedTraitReference)],
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        for effect in &row.effects {
            for argument in &effect.arguments {
                self.validate_generic_argument_projection_obligations(
                    argument,
                    ambient,
                    diagnostics,
                );
            }
        }
        for projection in &row.projections {
            self.validate_type_projection_obligations(&projection.subject, ambient, diagnostics);
            for argument in projection
                .trait_arguments
                .iter()
                .chain(&projection.item_arguments)
            {
                self.validate_generic_argument_projection_obligations(
                    argument,
                    ambient,
                    diagnostics,
                );
            }
            self.validate_projection_goal(
                "effect-row",
                &projection.subject,
                &ElaboratedTraitReference {
                    definition: projection.trait_definition,
                    arguments: projection.trait_arguments.clone(),
                },
                &projection.name,
                ambient,
                diagnostics,
            );
        }
    }

    fn validate_trait_reference_projection_obligations(
        &self,
        relation: &ElaboratedTraitReference,
        ambient: &[(Type, ElaboratedTraitReference)],
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        for argument in &relation.arguments {
            self.validate_generic_argument_projection_obligations(argument, ambient, diagnostics);
        }
    }

    fn validate_generic_argument_projection_obligations(
        &self,
        argument: &GenericArgument,
        ambient: &[(Type, ElaboratedTraitReference)],
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        match argument {
            GenericArgument::Type(value) => {
                self.validate_type_projection_obligations(value, ambient, diagnostics);
            }
            GenericArgument::EffectRow(row) => {
                self.validate_effect_row_projection_obligations(row, ambient, diagnostics);
            }
            GenericArgument::ConstProjection {
                subject,
                trait_definition,
                trait_arguments,
                name,
                ..
            } => {
                self.validate_type_projection_obligations(subject, ambient, diagnostics);
                for argument in trait_arguments {
                    self.validate_generic_argument_projection_obligations(
                        argument,
                        ambient,
                        diagnostics,
                    );
                }
                self.validate_projection_goal(
                    "const",
                    subject,
                    &ElaboratedTraitReference {
                        definition: *trait_definition,
                        arguments: trait_arguments.clone(),
                    },
                    name,
                    ambient,
                    diagnostics,
                );
            }
            GenericArgument::Lifetime(_)
            | GenericArgument::ConstU32(_)
            | GenericArgument::ConstU32Expr(_)
            | GenericArgument::ConstQuantity(_)
            | GenericArgument::ConstGeneric { .. }
            | GenericArgument::ConstInfer { .. } => {}
        }
    }

    fn validate_projection_goal(
        &self,
        kind: &str,
        subject: &Type,
        relation: &ElaboratedTraitReference,
        name: &str,
        ambient: &[(Type, ElaboratedTraitReference)],
        diagnostics: &mut Vec<SignatureDiagnostic>,
    ) {
        let goal = crate::TraitGoal {
            relation: relation.clone(),
            subject: subject.clone(),
        };
        if self.ambient_projection_goal_proves(&goal, ambient) {
            return;
        }
        let outcome = crate::TraitSolver::new(self).solve(goal);
        let (code, reason) = match outcome {
            crate::TraitAnswer::Proven { .. } => return,
            crate::TraitAnswer::Refuted { .. } => {
                ("G4191", "is refuted by a negative implementation")
            }
            crate::TraitAnswer::NoSolution => (
                "G4190",
                "has no trait obligation or implementation evidence",
            ),
            crate::TraitAnswer::Ambiguous => ("G4192", "has ambiguous trait evidence"),
            crate::TraitAnswer::Overflow => ("G4193", "exceeded the trait solver limit"),
        };
        diagnostics.push(SignatureDiagnostic {
            code,
            message: format!(
                "associated {kind} projection `{name}` {reason} (trait {:?})",
                relation.definition
            ),
        });
    }

    fn ambient_projection_goal_proves(
        &self,
        goal: &crate::TraitGoal,
        ambient: &[(Type, ElaboratedTraitReference)],
    ) -> bool {
        let mut pending = ambient.to_vec();
        let mut seen = Vec::<(Type, ElaboratedTraitReference)>::new();
        while let Some((subject, relation)) = pending.pop() {
            if seen.iter().any(|(known_subject, known_relation)| {
                known_subject == &subject && known_relation == &relation
            }) {
                continue;
            }
            if subject == goal.subject && relation == goal.relation {
                return true;
            }
            seen.push((subject.clone(), relation.clone()));
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.definitions.get(&relation.definition)
            else {
                continue;
            };
            for supertrait in &trait_header.supertraits {
                pending.push((
                    subject.clone(),
                    substitute_trait_reference(supertrait, &relation.arguments),
                ));
            }
        }
        false
    }

    /// Supertrait edges are a declaration-level entailment graph.  A cycle
    /// has no finite inherited-item owner and must be rejected before a body
    /// can turn it into an order-dependent method or projection lookup.
    fn validate_trait_supertrait_cycles(&mut self) {
        let edges = self
            .definitions
            .iter()
            .filter_map(|(definition, header)| match header {
                ElaboratedHeader::Trait(trait_header) => Some((
                    *definition,
                    trait_header
                        .supertraits
                        .iter()
                        .map(|relation| relation.definition)
                        .collect::<Vec<_>>(),
                )),
                _ => None,
            })
            .collect::<BTreeMap<_, _>>();
        let mut diagnostics = Vec::new();
        for definition in edges.keys().copied() {
            if trait_reaches(&edges, definition, definition, &mut Vec::new()) {
                diagnostics.push(SignatureDiagnostic {
                    code: "G4175",
                    message: format!("trait supertrait cycle includes `{definition:?}`"),
                });
            }
        }
        self.diagnostics.extend(diagnostics);
    }

    /// Instantiate a named struct layout at a particular nominal application.
    /// This is the sole bridge from interface-owned generic fields into
    /// body-local inference; callers cannot manufacture a layout from source
    /// spelling or rely on declaration order outside this semantic product.
    pub fn instantiate_struct_fields_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
    ) -> Result<Vec<NominalField>, InstantiationError> {
        let kinds = self.nominal_kinds(definition)?;
        validate_runtime_nominal_arguments(kinds, arguments)?;
        let Some(ElaboratedHeader::Nominal {
            generic_kinds,
            layout,
            ..
        }) = self.definitions.get(&definition)
        else {
            return Err(InstantiationError::WrongLayout);
        };
        if generic_kinds.len() != arguments.len() {
            return Err(InstantiationError::WrongArity {
                expected: generic_kinds.len(),
                found: arguments.len(),
            });
        }
        let ElaboratedNominalLayout::Struct(fields) = layout else {
            return Err(InstantiationError::WrongLayout);
        };
        Ok(fields
            .iter()
            .map(|field| NominalField {
                name: field.name.clone(),
                ty: self.instantiate_runtime_nominal_field(&field.ty, arguments),
                private_authority: field.private_authority,
            })
            .collect())
    }

    pub fn instantiate_struct_fields(
        &self,
        definition: DefKey,
        arguments: &[Type],
    ) -> Option<Vec<NominalField>> {
        let ElaboratedHeader::Nominal {
            generics, layout, ..
        } = self.definitions.get(&definition)?
        else {
            return None;
        };
        if *generics as usize != arguments.len() {
            return None;
        }
        let ElaboratedNominalLayout::Struct(fields) = layout else {
            return None;
        };
        Some(
            fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: substitute_alias_generics(field.ty.clone(), arguments),
                    private_authority: field.private_authority,
                })
                .collect(),
        )
    }

    /// Instantiate a callable signature for one body-local invocation. The
    /// interface-owned generic binders never escape into a caller: every
    /// reference gets a caller-owned inference variable which Typed Core
    /// freezes before MIR can observe it.
    pub fn instantiate_callable_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
    ) -> Result<CallableSignature, InstantiationError> {
        let ElaboratedHeader::Callable(signature) = self
            .definitions
            .get(&definition)
            .ok_or(InstantiationError::MissingDefinition)?
        else {
            return Err(InstantiationError::WrongLayout);
        };
        validate_generic_arguments(&signature.generic_kinds, arguments)?;
        Ok(CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: signature
                .parameters
                .iter()
                .cloned()
                .map(|ty| substitute_alias_generic_identity(ty, arguments))
                .collect(),
            result: substitute_alias_generic_identity(signature.result.clone(), arguments),
            effects: substitute_alias_generic_identity_effect_row(
                signature.effects.clone(),
                arguments,
            ),
            invocation: signature.invocation,
            where_bounds: signature
                .where_bounds
                .iter()
                .map(|(subject, relation)| {
                    (
                        substitute_alias_generic_identity(subject.clone(), arguments),
                        substitute_trait_reference(relation, arguments),
                    )
                })
                .collect(),
            where_associated_type_bindings: signature
                .where_associated_type_bindings
                .iter()
                .cloned()
                .map(|binding| {
                    substitute_alias_generic_identity_associated_type_binding(binding, arguments)
                })
                .collect(),
            where_associated_effect_bindings: signature
                .where_associated_effect_bindings
                .iter()
                .cloned()
                .map(|binding| {
                    substitute_alias_generic_identity_associated_effect_binding(binding, arguments)
                })
                .collect(),
        })
    }

    pub fn instantiate_callable(
        &self,
        definition: DefKey,
        arguments: &[Type],
    ) -> Option<CallableSignature> {
        let ElaboratedHeader::Callable(signature) = self.definitions.get(&definition)? else {
            return None;
        };
        if signature.generics as usize != arguments.len() {
            return None;
        }
        Some(CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: signature
                .parameters
                .iter()
                .cloned()
                .map(|ty| substitute_alias_generics(ty, arguments))
                .collect(),
            result: substitute_alias_generics(signature.result.clone(), arguments),
            effects: substitute_effect_row(signature.effects.clone(), arguments),
            invocation: signature.invocation,
            where_bounds: signature
                .where_bounds
                .iter()
                .map(|(subject, relation)| {
                    (
                        substitute_alias_generics(subject.clone(), arguments),
                        substitute_trait_reference_with_types(relation, arguments),
                    )
                })
                .collect(),
            where_associated_type_bindings: signature
                .where_associated_type_bindings
                .iter()
                .cloned()
                .map(|binding| {
                    substitute_alias_generics_associated_type_binding(binding, arguments)
                })
                .collect(),
            where_associated_effect_bindings: signature
                .where_associated_effect_bindings
                .iter()
                .cloned()
                .map(|binding| {
                    substitute_alias_generics_associated_effect_binding(binding, arguments)
                })
                .collect(),
        })
    }

    /// Instantiate a canonical protocol operation at one concrete protocol
    /// identity and one operation-generic application. Declaration binders
    /// occupy the leading substitution slots; the operation's own binders
    /// follow them, so runtime effect identity stays nominally tied only to
    /// the protocol arguments.
    pub fn instantiate_effect_operation_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
        operation_arguments: &[GenericArgument],
        name: &str,
    ) -> Result<(u32, ElaboratedEffectOperation), InstantiationError> {
        let ElaboratedHeader::Effect(effect) = self
            .definitions
            .get(&definition)
            .ok_or(InstantiationError::MissingDefinition)?
        else {
            return Err(InstantiationError::WrongLayout);
        };
        validate_generic_arguments(&effect.generic_kinds, arguments)?;
        let operation = effect
            .operations
            .iter()
            .find(|operation| operation.name == name)
            .ok_or(InstantiationError::MissingMember)?;
        let operation_kinds = operation
            .generic_kinds
            .get(effect.generics as usize..)
            .ok_or(InstantiationError::WrongLayout)?;
        validate_generic_arguments(operation_kinds, operation_arguments)?;
        let mut substitutions = arguments.to_vec();
        substitutions.extend_from_slice(operation_arguments);
        let (index, operation) = effect
            .operations
            .iter()
            .enumerate()
            .find(|(_, operation)| operation.name == name)
            .ok_or(InstantiationError::MissingMember)?;
        Ok((
            index as u32,
            ElaboratedEffectOperation {
                name: operation.name.clone(),
                generics: 0,
                generic_kinds: vec![],
                parameters: operation
                    .parameters
                    .iter()
                    .cloned()
                    .map(|ty| substitute_alias_generic_identity(ty, &substitutions))
                    .collect(),
                result: substitute_alias_generic_identity(operation.result.clone(), &substitutions),
                terminal: operation.terminal,
                resumption: operation.resumption,
            },
        ))
    }

    pub fn instantiate_effect_operation(
        &self,
        definition: DefKey,
        arguments: &[Type],
        operation_arguments: &[Type],
        name: &str,
    ) -> Option<(u32, ElaboratedEffectOperation)> {
        let ElaboratedHeader::Effect(effect) = self.definitions.get(&definition)? else {
            return None;
        };
        if effect.generics as usize != arguments.len() {
            return None;
        }
        let (index, operation) = effect
            .operations
            .iter()
            .enumerate()
            .find(|(_, operation)| operation.name == name)?;
        let operation_generics = operation.generics.checked_sub(effect.generics)?;
        if operation_generics as usize != operation_arguments.len() {
            return None;
        }
        let mut substitutions = arguments.to_vec();
        substitutions.extend_from_slice(operation_arguments);
        Some((
            index as u32,
            ElaboratedEffectOperation {
                name: operation.name.clone(),
                generics: 0,
                generic_kinds: vec![],
                parameters: operation
                    .parameters
                    .iter()
                    .cloned()
                    .map(|ty| substitute_alias_generics(ty, &substitutions))
                    .collect(),
                result: substitute_alias_generics(operation.result.clone(), &substitutions),
                terminal: operation.terminal,
                resumption: operation.resumption,
            },
        ))
    }

    /// Resolve a unit or tuple enum variant at one concrete nominal
    /// application. Named payload variants use the record-construction path
    /// so their field names remain checked.
    pub fn instantiate_enum_variant_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
        name: &str,
    ) -> Result<(u32, Vec<Type>), InstantiationError> {
        let kinds = self.nominal_kinds(definition)?;
        validate_runtime_nominal_arguments(kinds, arguments)?;
        let Some(ElaboratedHeader::Nominal {
            layout: ElaboratedNominalLayout::Enum(variants),
            ..
        }) = self.definitions.get(&definition)
        else {
            return Err(InstantiationError::WrongLayout);
        };
        let Some((index, variant)) = variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.name == name)
        else {
            return Err(InstantiationError::MissingMember);
        };
        let fields = match &variant.payload {
            ElaboratedEnumVariantPayload::Unit => vec![],
            ElaboratedEnumVariantPayload::Tuple(fields) => fields
                .iter()
                .map(|field| self.instantiate_runtime_nominal_field(field, arguments))
                .collect(),
            ElaboratedEnumVariantPayload::Struct(_) => return Err(InstantiationError::WrongLayout),
        };
        Ok((index as u32, fields))
    }

    pub fn instantiate_enum_variant(
        &self,
        definition: DefKey,
        arguments: &[Type],
        name: &str,
    ) -> Option<(u32, Vec<Type>)> {
        let ElaboratedHeader::Nominal {
            generics, layout, ..
        } = self.definitions.get(&definition)?
        else {
            return None;
        };
        if *generics as usize != arguments.len() {
            return None;
        }
        let ElaboratedNominalLayout::Enum(variants) = layout else {
            return None;
        };
        let (index, variant) = variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.name == name)?;
        let fields = match &variant.payload {
            ElaboratedEnumVariantPayload::Unit => vec![],
            ElaboratedEnumVariantPayload::Tuple(fields) => fields
                .iter()
                .cloned()
                .map(|field| substitute_alias_generics(field, arguments))
                .collect(),
            ElaboratedEnumVariantPayload::Struct(_) => return None,
        };
        Some((index as u32, fields))
    }

    pub fn instantiate_enum_record_variant_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
        name: &str,
    ) -> Result<(u32, Vec<NominalField>), InstantiationError> {
        let kinds = self.nominal_kinds(definition)?;
        validate_runtime_nominal_arguments(kinds, arguments)?;
        let Some(ElaboratedHeader::Nominal {
            layout: ElaboratedNominalLayout::Enum(variants),
            ..
        }) = self.definitions.get(&definition)
        else {
            return Err(InstantiationError::WrongLayout);
        };
        let Some((index, variant)) = variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.name == name)
        else {
            return Err(InstantiationError::MissingMember);
        };
        let ElaboratedEnumVariantPayload::Struct(fields) = &variant.payload else {
            return Err(InstantiationError::WrongLayout);
        };
        Ok((
            index as u32,
            fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: self.instantiate_runtime_nominal_field(&field.ty, arguments),
                    private_authority: field.private_authority,
                })
                .collect(),
        ))
    }

    pub fn instantiate_enum_record_variant(
        &self,
        definition: DefKey,
        arguments: &[Type],
        name: &str,
    ) -> Option<(u32, Vec<NominalField>)> {
        let ElaboratedHeader::Nominal {
            generics, layout, ..
        } = self.definitions.get(&definition)?
        else {
            return None;
        };
        if *generics as usize != arguments.len() {
            return None;
        }
        let ElaboratedNominalLayout::Enum(variants) = layout else {
            return None;
        };
        let (index, variant) = variants
            .iter()
            .enumerate()
            .find(|(_, variant)| variant.name == name)?;
        let ElaboratedEnumVariantPayload::Struct(fields) = &variant.payload else {
            return None;
        };
        Some((
            index as u32,
            fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: substitute_alias_generics(field.ty.clone(), arguments),
                    private_authority: field.private_authority,
                })
                .collect(),
        ))
    }

    /// Instantiate the payload field types for an already-resolved enum
    /// variant. Pattern decision lowering carries declaration indices rather
    /// than source names, so this is its layout bridge. Both tuple and named
    /// payloads deliberately become positional here: field-name authority was
    /// checked during pattern elaboration and is no longer a runtime concern.
    pub fn instantiate_enum_fields_generic(
        &self,
        definition: DefKey,
        arguments: &[GenericArgument],
        index: u32,
    ) -> Result<Vec<NominalField>, InstantiationError> {
        let kinds = self.nominal_kinds(definition)?;
        validate_runtime_nominal_arguments(kinds, arguments)?;
        let Some(ElaboratedHeader::Nominal {
            layout: ElaboratedNominalLayout::Enum(variants),
            ..
        }) = self.definitions.get(&definition)
        else {
            return Err(InstantiationError::WrongLayout);
        };
        let Some(variant) = variants.get(index as usize) else {
            return Err(InstantiationError::MissingMember);
        };
        let fields = match &variant.payload {
            ElaboratedEnumVariantPayload::Unit => vec![],
            ElaboratedEnumVariantPayload::Tuple(fields) => fields
                .iter()
                .enumerate()
                .map(|(index, ty)| NominalField {
                    name: index.to_string(),
                    ty: self.instantiate_runtime_nominal_field(ty, arguments),
                    private_authority: None,
                })
                .collect(),
            ElaboratedEnumVariantPayload::Struct(fields) => fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: self.instantiate_runtime_nominal_field(&field.ty, arguments),
                    private_authority: field.private_authority,
                })
                .collect(),
        };
        Ok(fields)
    }

    pub fn instantiate_enum_fields(
        &self,
        definition: DefKey,
        arguments: &[Type],
        index: u32,
    ) -> Option<Vec<NominalField>> {
        let ElaboratedHeader::Nominal {
            generics, layout, ..
        } = self.definitions.get(&definition)?
        else {
            return None;
        };
        if *generics as usize != arguments.len() {
            return None;
        }
        let ElaboratedNominalLayout::Enum(variants) = layout else {
            return None;
        };
        let variant = variants.get(index as usize)?;
        let fields = match &variant.payload {
            ElaboratedEnumVariantPayload::Unit => vec![],
            ElaboratedEnumVariantPayload::Tuple(fields) => fields
                .iter()
                .enumerate()
                .map(|(index, ty)| NominalField {
                    name: index.to_string(),
                    ty: substitute_alias_generics(ty.clone(), arguments),
                    private_authority: None,
                })
                .collect(),
            ElaboratedEnumVariantPayload::Struct(fields) => fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: substitute_alias_generics(field.ty.clone(), arguments),
                    private_authority: field.private_authority,
                })
                .collect(),
        };
        Some(fields)
    }

    fn nominal_kinds(&self, definition: DefKey) -> Result<&[GenericKind], InstantiationError> {
        let ElaboratedHeader::Nominal { generic_kinds, .. } = self
            .definitions
            .get(&definition)
            .ok_or(InstantiationError::MissingDefinition)?
        else {
            return Err(InstantiationError::WrongLayout);
        };
        Ok(generic_kinds)
    }

    fn instantiate_runtime_nominal_field(
        &self,
        field: &Type,
        arguments: &[GenericArgument],
    ) -> Type {
        let field = substitute_alias_generic_identity(field.clone(), arguments);
        // Symbolic projections stay symbolic, while a field that became
        // concrete through this mixed-kind nominal application is reduced
        // before Core/MIR can consume the layout.
        crate::TraitSolver::new(self)
            .normalize_type(field.clone())
            .unwrap_or(field)
    }

    fn normalize_aliases(&mut self) {
        let aliases = self.definitions.clone();
        let mut diagnostics = vec![];
        for header in self.definitions.values_mut() {
            match header {
                ElaboratedHeader::Callable(signature)
                | ElaboratedHeader::ValueAlias { signature, .. } => {
                    normalize_callable_signature(signature, &aliases, &mut diagnostics);
                }
                ElaboratedHeader::Alias { target, .. } => {
                    *target = normalize_alias_type(
                        target.clone(),
                        &aliases,
                        &mut vec![],
                        &mut diagnostics,
                    );
                }
                ElaboratedHeader::Constant(Some(ty))
                | ElaboratedHeader::ValueInitializer { ty: Some(ty), .. } => {
                    *ty = normalize_alias_type(ty.clone(), &aliases, &mut vec![], &mut diagnostics);
                }
                ElaboratedHeader::Nominal { layout, .. } => {
                    normalize_nominal_layout(layout, &aliases, &mut diagnostics);
                }
                ElaboratedHeader::Trait(trait_header) => {
                    for reference in &mut trait_header.supertraits {
                        normalize_trait_reference(reference, &aliases, &mut diagnostics);
                    }
                    for item in trait_header.associated_types.values_mut() {
                        if let Some(default) = item.default.take() {
                            item.default = Some(normalize_alias_type(
                                default,
                                &aliases,
                                &mut vec![],
                                &mut diagnostics,
                            ));
                        }
                        if let Some(default) = item.effect_row_default.take() {
                            item.effect_row_default =
                                Some(normalize_effect_row(default, &aliases, &mut diagnostics));
                        }
                    }
                    for method in trait_header.methods.values_mut() {
                        normalize_callable_signature(method, &aliases, &mut diagnostics);
                    }
                }
                ElaboratedHeader::Implementation(implementation) => {
                    normalize_trait_reference(
                        &mut implementation.relation,
                        &aliases,
                        &mut diagnostics,
                    );
                    implementation.self_ty = normalize_alias_type(
                        implementation.self_ty.clone(),
                        &aliases,
                        &mut vec![],
                        &mut diagnostics,
                    );
                    for (subject, relation) in &mut implementation.where_bounds {
                        *subject = normalize_alias_type(
                            subject.clone(),
                            &aliases,
                            &mut vec![],
                            &mut diagnostics,
                        );
                        normalize_trait_reference(relation, &aliases, &mut diagnostics);
                    }
                    for value in implementation.associated_types.values_mut() {
                        value.value = normalize_alias_type(
                            value.value.clone(),
                            &aliases,
                            &mut vec![],
                            &mut diagnostics,
                        );
                    }
                    for method in implementation.methods.values_mut() {
                        normalize_callable_signature(method, &aliases, &mut diagnostics);
                    }
                }
                ElaboratedHeader::Effect(effect) => {
                    for operation in &mut effect.operations {
                        operation.parameters = operation
                            .parameters
                            .clone()
                            .into_iter()
                            .map(|ty| {
                                normalize_alias_type(ty, &aliases, &mut vec![], &mut diagnostics)
                            })
                            .collect();
                        operation.result = normalize_alias_type(
                            operation.result.clone(),
                            &aliases,
                            &mut vec![],
                            &mut diagnostics,
                        );
                    }
                }
                ElaboratedHeader::Constant(None)
                | ElaboratedHeader::ValueInitializer { ty: None, .. }
                | ElaboratedHeader::Opaque => {}
            }
        }
        self.diagnostics.extend(diagnostics);
        self.diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        self.diagnostics
            .dedup_by(|left, right| left.code == right.code && left.message == right.message);
    }
}

/// Validate a source-kind-preserving substitution. Effect operation
/// instantiation is identity-sensitive rather than type-only: it may carry
/// lifetime, row, `u32`, and quantity arguments through nested parameter and
/// effect-row terms even when no runtime value is produced for those slots.
fn validate_generic_arguments(
    kinds: &[GenericKind],
    arguments: &[GenericArgument],
) -> Result<(), InstantiationError> {
    if kinds.len() != arguments.len() {
        return Err(InstantiationError::WrongArity {
            expected: kinds.len(),
            found: arguments.len(),
        });
    }
    for (slot, (kind, argument)) in kinds.iter().zip(arguments).enumerate() {
        let valid = match (kind, argument) {
            (GenericKind::Type, GenericArgument::Type(_))
            | (GenericKind::EffectRow, GenericArgument::EffectRow(_))
            | (GenericKind::Lifetime, GenericArgument::Lifetime(_)) => true,
            (GenericKind::Const(kind), argument) => {
                generic_argument_matches_const_kind(argument, *kind)
            }
            _ => false,
        };
        if !valid {
            return Err(InstantiationError::WrongKind {
                slot,
                expected: *kind,
            });
        }
    }
    Ok(())
}

/// Executable nominal layouts retain type and structural-const identity.
/// Lifetimes are erased by the VM value representation, but they remain
/// meaningful while this interface query substitutes fields: `struct
/// Borrowed<'a> { value: &'a T }` must be constructible and projectable before
/// that final erasure. Effect-row applications still have no VM nominal-layout
/// representation, so keep rejecting those at the shared boundary.
fn validate_runtime_nominal_arguments(
    kinds: &[GenericKind],
    arguments: &[GenericArgument],
) -> Result<(), InstantiationError> {
    validate_generic_arguments(kinds, arguments)?;
    if let Some((slot, argument)) = arguments
        .iter()
        .enumerate()
        .find(|(_, argument)| matches!(argument, GenericArgument::EffectRow(_)))
    {
        return Err(InstantiationError::RequiresType {
            slot,
            argument: Box::new(argument.clone()),
        });
    }
    Ok(())
}

fn normalize_callable_signature(
    signature: &mut CallableSignature,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) {
    signature.parameters = signature
        .parameters
        .clone()
        .into_iter()
        .map(|ty| normalize_alias_type(ty, definitions, &mut vec![], diagnostics))
        .collect();
    signature.result = normalize_alias_type(
        signature.result.clone(),
        definitions,
        &mut vec![],
        diagnostics,
    );
    signature.effects = normalize_effect_row(signature.effects.clone(), definitions, diagnostics);
    for (subject, relation) in &mut signature.where_bounds {
        *subject = normalize_alias_type(subject.clone(), definitions, &mut vec![], diagnostics);
        normalize_trait_reference(relation, definitions, diagnostics);
    }
    for binding in &mut signature.where_associated_type_bindings {
        binding.subject = normalize_alias_type(
            binding.subject.clone(),
            definitions,
            &mut vec![],
            diagnostics,
        );
        normalize_trait_reference(&mut binding.relation, definitions, diagnostics);
        binding.item_arguments = binding
            .item_arguments
            .clone()
            .into_iter()
            .map(|argument| normalize_trait_generic_argument(argument, definitions, diagnostics))
            .collect();
        binding.value =
            normalize_alias_type(binding.value.clone(), definitions, &mut vec![], diagnostics);
    }
    for binding in &mut signature.where_associated_effect_bindings {
        binding.subject = normalize_alias_type(
            binding.subject.clone(),
            definitions,
            &mut vec![],
            diagnostics,
        );
        normalize_trait_reference(&mut binding.relation, definitions, diagnostics);
        binding.item_arguments = binding
            .item_arguments
            .clone()
            .into_iter()
            .map(|argument| normalize_trait_generic_argument(argument, definitions, diagnostics))
            .collect();
        binding.value = normalize_effect_row(binding.value.clone(), definitions, diagnostics);
    }
}

/// Instantiate a trait method in an implementation's binder environment.
/// The trait relation supplies its declaration generics; method generics are
/// kept universally quantified in slots after the implementation binders.
fn instantiate_trait_method_contract(
    method: &CallableSignature,
    implementation: &ElaboratedImplementation,
) -> CallableSignature {
    // Trait methods are elaborated in the trait's binder environment, while
    // implementation methods are elaborated after the implementation's own
    // binders. Type generics already pass through `arguments` below, but
    // lifetimes deliberately have their own namespace and therefore need an
    // explicit de Bruijn-style rebase as well. Without it, for example,
    // `impl<T> Borrow for Box<T> { fn get<'a>(...) ... }` compared the
    // trait's method lifetime slot 0 with the implementation method's slot 1
    // and incorrectly rejected an identical contract.
    let trait_generic_count = implementation.relation.arguments.len() as u32;
    let implementation_generic_count = implementation.generics;
    let mut arguments = implementation.relation.arguments.clone();
    arguments.extend(
        method
            .generic_kinds
            .iter()
            .enumerate()
            .map(|(offset, kind)| {
                let implementation_slot = implementation.generics + offset as u32;
                match kind {
                    GenericKind::Type => GenericArgument::Type(Type::Generic(implementation_slot)),
                    GenericKind::EffectRow => GenericArgument::EffectRow(EffectRow {
                        effects: BTreeSet::new(),
                        projections: vec![],
                        tail: Some(EffectTail::Generic(implementation_slot)),
                    }),
                    // Lifetime rebasing below translates this trait-method slot to
                    // the implementation method's binder prefix.
                    GenericKind::Lifetime => GenericArgument::Lifetime(Lifetime::Generic(
                        trait_generic_count + offset as u32,
                    )),
                    GenericKind::Const(kind) => GenericArgument::ConstGeneric {
                        index: implementation_slot,
                        kind: *kind,
                    },
                }
            }),
    );
    CallableSignature {
        generics: method.generics,
        generic_kinds: method.generic_kinds.clone(),
        parameters: method
            .parameters
            .iter()
            .cloned()
            .map(|parameter| {
                rebase_method_lifetimes(
                    replace_trait_self_type(
                        substitute_trait_type_generics(parameter, &arguments),
                        &implementation.self_ty,
                    ),
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
        result: rebase_method_lifetimes(
            replace_trait_self_type(
                substitute_trait_type_generics(method.result.clone(), &arguments),
                &implementation.self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
        effects: rebase_method_lifetime_effect_row(
            replace_trait_self_effect_row(
                substitute_trait_effect_row(method.effects.clone(), &arguments),
                &implementation.self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
        invocation: method.invocation,
        where_bounds: method
            .where_bounds
            .iter()
            .map(|(subject, relation)| {
                (
                    rebase_method_lifetimes(
                        replace_trait_self_type(
                            substitute_trait_type_generics(subject.clone(), &arguments),
                            &implementation.self_ty,
                        ),
                        trait_generic_count,
                        implementation_generic_count,
                    ),
                    rebase_method_lifetime_trait_reference(
                        replace_trait_self_trait_reference(
                            substitute_trait_reference(relation, &arguments),
                            &implementation.self_ty,
                        ),
                        trait_generic_count,
                        implementation_generic_count,
                    ),
                )
            })
            .collect(),
        where_associated_type_bindings: method
            .where_associated_type_bindings
            .iter()
            .cloned()
            .map(|binding| {
                instantiate_trait_method_associated_type_binding(
                    binding,
                    &arguments,
                    &implementation.self_ty,
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
        where_associated_effect_bindings: method
            .where_associated_effect_bindings
            .iter()
            .cloned()
            .map(|binding| {
                instantiate_trait_method_associated_effect_binding(
                    binding,
                    &arguments,
                    &implementation.self_ty,
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
    }
}

/// Substitute the trait-owned implicit receiver after ordinary declaration
/// generics have been instantiated.  `Self` may appear beneath aliases,
/// projections, callback signatures, and effect arguments, so this operates
/// on the canonical semantic tree rather than on the spelling of a parameter.
fn replace_trait_self_type(value: Type, self_ty: &Type) -> Type {
    match value {
        Type::Generic(TRAIT_SELF_GENERIC) => self_ty.clone(),
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition,
            arguments: arguments
                .into_iter()
                .map(|value| replace_trait_self_generic_argument(value, self_ty))
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
            subject: Box::new(replace_trait_self_type(*subject, self_ty)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| replace_trait_self_generic_argument(value, self_ty))
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| replace_trait_self_generic_argument(value, self_ty))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| replace_trait_self_type(value, self_ty))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(replace_trait_self_type(*value, self_ty))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime,
            referent: Box::new(replace_trait_self_type(*referent, self_ty)),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| replace_trait_self_type(value, self_ty))
                .collect(),
            result: Box::new(replace_trait_self_type(*result, self_ty)),
            effects: replace_trait_self_effect_row(effects, self_ty),
            invocation,
        },
        value => value,
    }
}

fn replace_trait_self_trait_reference(
    relation: ElaboratedTraitReference,
    self_ty: &Type,
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .into_iter()
            .map(|value| replace_trait_self_generic_argument(value, self_ty))
            .collect(),
    }
}

fn replace_trait_self_generic_argument(value: GenericArgument, self_ty: &Type) -> GenericArgument {
    match value {
        GenericArgument::Type(value) => {
            GenericArgument::Type(replace_trait_self_type(value, self_ty))
        }
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(replace_trait_self_effect_row(value, self_ty))
        }
        value => value,
    }
}

fn replace_trait_self_effect_row(value: EffectRow, self_ty: &Type) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|value| replace_trait_self_generic_argument(value, self_ty))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(replace_trait_self_type(*projection.subject, self_ty)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|value| replace_trait_self_generic_argument(value, self_ty))
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| replace_trait_self_generic_argument(value, self_ty))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

/// Rebase lifetimes introduced by a trait method into the implementation
/// method's binder prefix. Lifetimes that belong to the trait itself remain
/// untouched; they are part of the selected trait relation rather than the
/// method's universal binder.
fn rebase_method_lifetimes(
    value: Type,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> Type {
    match value {
        Type::Nominal {
            definition,
            arguments,
        } => Type::Nominal {
            definition,
            arguments: arguments
                .into_iter()
                .map(|value| {
                    rebase_method_lifetime_generic_argument(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
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
            subject: Box::new(rebase_method_lifetimes(
                *subject,
                trait_generic_count,
                implementation_generic_count,
            )),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| {
                    rebase_method_lifetime_generic_argument(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| {
                    rebase_method_lifetime_generic_argument(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| {
                    rebase_method_lifetimes(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(rebase_method_lifetimes(
            *value,
            trait_generic_count,
            implementation_generic_count,
        ))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime: match lifetime {
                Lifetime::Generic(index) if index >= trait_generic_count => {
                    Lifetime::Generic(implementation_generic_count + (index - trait_generic_count))
                }
                lifetime => lifetime,
            },
            referent: Box::new(rebase_method_lifetimes(
                *referent,
                trait_generic_count,
                implementation_generic_count,
            )),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| {
                    rebase_method_lifetimes(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
                .collect(),
            result: Box::new(rebase_method_lifetimes(
                *result,
                trait_generic_count,
                implementation_generic_count,
            )),
            effects: rebase_method_lifetime_effect_row(
                effects,
                trait_generic_count,
                implementation_generic_count,
            ),
            invocation,
        },
        value => value,
    }
}

fn rebase_method_lifetime_trait_reference(
    relation: ElaboratedTraitReference,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .into_iter()
            .map(|argument| {
                rebase_method_lifetime_generic_argument(
                    argument,
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
    }
}

fn rebase_method_lifetime_generic_argument(
    argument: GenericArgument,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => GenericArgument::Type(rebase_method_lifetimes(
            value,
            trait_generic_count,
            implementation_generic_count,
        )),
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(rebase_method_lifetime_effect_row(
                value,
                trait_generic_count,
                implementation_generic_count,
            ))
        }
        GenericArgument::Lifetime(Lifetime::Generic(index)) if index >= trait_generic_count => {
            GenericArgument::Lifetime(Lifetime::Generic(
                implementation_generic_count + (index - trait_generic_count),
            ))
        }
        value => value,
    }
}

fn rebase_method_lifetime_effect_row(
    value: EffectRow,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| {
                        rebase_method_lifetime_generic_argument(
                            argument,
                            trait_generic_count,
                            implementation_generic_count,
                        )
                    })
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(rebase_method_lifetimes(
                    *projection.subject,
                    trait_generic_count,
                    implementation_generic_count,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|argument| {
                        rebase_method_lifetime_generic_argument(
                            argument,
                            trait_generic_count,
                            implementation_generic_count,
                        )
                    })
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|argument| {
                        rebase_method_lifetime_generic_argument(
                            argument,
                            trait_generic_count,
                            implementation_generic_count,
                        )
                    })
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

fn normalize_trait_reference(
    reference: &mut ElaboratedTraitReference,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) {
    reference.arguments = reference
        .arguments
        .clone()
        .into_iter()
        .map(|argument| normalize_trait_generic_argument(argument, definitions, diagnostics))
        .collect();
}

fn normalize_trait_generic_argument(
    argument: GenericArgument,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) -> GenericArgument {
    normalize_alias_generic_argument(argument, definitions, &mut vec![], diagnostics)
}

fn substitute_trait_reference(
    relation: &ElaboratedTraitReference,
    arguments: &[GenericArgument],
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .cloned()
            .map(|argument| substitute_trait_generic_argument(argument, arguments))
            .collect(),
    }
}

fn substitute_trait_reference_with_types(
    relation: &ElaboratedTraitReference,
    arguments: &[Type],
) -> ElaboratedTraitReference {
    let arguments = arguments
        .iter()
        .cloned()
        .map(GenericArgument::Type)
        .collect::<Vec<_>>();
    substitute_trait_reference(relation, &arguments)
}

fn instantiate_trait_method_associated_type_binding(
    binding: ElaboratedAssociatedTypeBinding,
    arguments: &[GenericArgument],
    self_ty: &Type,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> ElaboratedAssociatedTypeBinding {
    let rebase_type = |value| {
        rebase_method_lifetimes(
            replace_trait_self_type(substitute_trait_type_generics(value, arguments), self_ty),
            trait_generic_count,
            implementation_generic_count,
        )
    };
    ElaboratedAssociatedTypeBinding {
        subject: rebase_type(binding.subject),
        relation: rebase_method_lifetime_trait_reference(
            replace_trait_self_trait_reference(
                substitute_trait_reference(&binding.relation, arguments),
                self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| {
                rebase_method_lifetime_generic_argument(
                    replace_trait_self_generic_argument(
                        substitute_trait_generic_argument(argument, arguments),
                        self_ty,
                    ),
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
        value: rebase_type(binding.value),
    }
}

fn instantiate_trait_method_associated_effect_binding(
    binding: ElaboratedAssociatedEffectBinding,
    arguments: &[GenericArgument],
    self_ty: &Type,
    trait_generic_count: u32,
    implementation_generic_count: u32,
) -> ElaboratedAssociatedEffectBinding {
    ElaboratedAssociatedEffectBinding {
        subject: rebase_method_lifetimes(
            replace_trait_self_type(
                substitute_trait_type_generics(binding.subject, arguments),
                self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
        relation: rebase_method_lifetime_trait_reference(
            replace_trait_self_trait_reference(
                substitute_trait_reference(&binding.relation, arguments),
                self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| {
                rebase_method_lifetime_generic_argument(
                    replace_trait_self_generic_argument(
                        substitute_trait_generic_argument(argument, arguments),
                        self_ty,
                    ),
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
        value: rebase_method_lifetime_effect_row(
            replace_trait_self_effect_row(
                substitute_trait_effect_row(binding.value, arguments),
                self_ty,
            ),
            trait_generic_count,
            implementation_generic_count,
        ),
    }
}

fn substitute_trait_generic_argument(
    argument: GenericArgument,
    arguments: &[GenericArgument],
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => {
            GenericArgument::Type(substitute_trait_type_generics(value, arguments))
        }
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(substitute_trait_effect_row(value, arguments))
        }
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(substitute_trait_type_generics(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| substitute_trait_generic_argument(argument, arguments))
                .collect(),
            name,
            kind,
        },
        GenericArgument::ConstGeneric { index, kind } => arguments
            .get(index as usize)
            .filter(|argument| generic_argument_matches_const_kind(argument, kind))
            .cloned()
            .unwrap_or(GenericArgument::ConstGeneric {
                index: u32::MAX,
                kind,
            }),
        GenericArgument::ConstU32Expr(value) => match value.substitute(arguments) {
            StructuralU32Expr::Literal(value) => GenericArgument::ConstU32(value),
            value => GenericArgument::ConstU32Expr(value),
        },
        value => value,
    }
}

fn generic_argument_matches_const_kind(argument: &GenericArgument, kind: ConstKind) -> bool {
    matches!(
        (argument, kind),
        (GenericArgument::ConstU32(_), ConstKind::U32)
            | (GenericArgument::ConstU32Expr(_), ConstKind::U32)
            | (
                GenericArgument::ConstProjection {
                    kind: ConstKind::U32,
                    ..
                },
                ConstKind::U32
            )
            | (GenericArgument::ConstQuantity(_), ConstKind::Quantity)
            | (
                GenericArgument::ConstProjection {
                    kind: ConstKind::Quantity,
                    ..
                },
                ConstKind::Quantity
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: ConstKind::U32,
                    ..
                },
                ConstKind::U32
            )
            | (
                GenericArgument::ConstGeneric {
                    kind: ConstKind::Quantity,
                    ..
                },
                ConstKind::Quantity
            )
            | (
                GenericArgument::ConstInfer {
                    kind: ConstKind::U32,
                    ..
                },
                ConstKind::U32
            )
            | (
                GenericArgument::ConstInfer {
                    kind: ConstKind::Quantity,
                    ..
                },
                ConstKind::Quantity
            )
    )
}

fn normalize_effect_row(
    value: EffectRow,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) -> EffectRow {
    normalize_alias_effect_row(value, definitions, &mut vec![], diagnostics)
}

struct Elaborator<'a> {
    index: &'a DefinitionIndex,
    module: &'a ModuleKey,
    generics: BTreeMap<String, u32>,
    effect_row_generics: BTreeMap<String, u32>,
    lifetime_generics: BTreeMap<String, u32>,
    /// Lexical HRTB scopes, innermost last. These map source names to their
    /// alpha-stable binder positions and deliberately never share the
    /// declaration-generic lifetime namespace.
    bound_lifetime_scopes: Vec<BTreeMap<String, u32>>,
    const_generics: BTreeMap<String, (u32, ConstKind)>,
    /// Trait declarations retain an implicit `Self` placeholder; implementation
    /// members instead see their declared implementation head directly.
    self_type: Option<Type>,
    diagnostics: Vec<SignatureDiagnostic>,
}

fn trait_reaches(
    edges: &BTreeMap<DefKey, Vec<DefKey>>,
    start: DefKey,
    current: DefKey,
    active: &mut Vec<DefKey>,
) -> bool {
    if active.contains(&current) {
        return current == start;
    }
    active.push(current);
    let reaches = edges.get(&current).is_some_and(|parents| {
        parents
            .iter()
            .copied()
            .any(|parent| parent == start || trait_reaches(edges, start, parent, active))
    });
    active.pop();
    reaches
}

impl Elaborator<'_> {
    fn generic_binder_count(&self) -> u32 {
        (self.generics.len()
            + self.effect_row_generics.len()
            + self.lifetime_generics.len()
            + self.const_generics.len()) as u32
    }

    fn definition(&mut self, definition: &Definition) -> ElaboratedHeader {
        match &definition.syntax.header {
            ParsedHeader::Function(header) => ElaboratedHeader::Callable(self.callable(header)),
            ParsedHeader::TypeAlias { generics, target } => {
                self.bind_generics(generics);
                ElaboratedHeader::Alias {
                    generics: generics.len() as u32,
                    target: self.ty(target),
                }
            }
            ParsedHeader::Constant { ty } => {
                ElaboratedHeader::Constant(ty.as_ref().map(|value| self.ty(value)))
            }
            ParsedHeader::ValueAlias { .. } => ElaboratedHeader::Opaque,
            ParsedHeader::ValueInitializer { .. } => ElaboratedHeader::ValueInitializer {
                generic_kinds: vec![],
                ty: None,
            },
            ParsedHeader::Nominal { generics, layout } => {
                self.bind_generics(generics);
                ElaboratedHeader::Nominal {
                    generics: generics.len() as u32,
                    generic_kinds: generics.kinds(),
                    layout: self.nominal_layout(layout),
                }
            }
            ParsedHeader::Trait(header) => ElaboratedHeader::Trait(self.trait_header(header)),
            ParsedHeader::Implementation(header) => {
                ElaboratedHeader::Implementation(self.implementation(header))
            }
            ParsedHeader::Effect(header) => ElaboratedHeader::Effect(self.effect_header(header)),
            ParsedHeader::Fixity(_) | ParsedHeader::Import(_) => ElaboratedHeader::Opaque,
            ParsedHeader::Opaque => ElaboratedHeader::Opaque,
        }
    }
    fn callable(&mut self, header: &CallableHeader) -> CallableSignature {
        self.bind_generics(&header.generics);
        let (where_bounds, where_associated_type_bindings, where_associated_effect_bindings) =
            self.callable_where_bounds(&header.where_bounds);
        CallableSignature {
            generics: header.generics.len() as u32,
            generic_kinds: header.generics.kinds(),
            parameters: header
                .parameters
                .iter()
                .map(|parameter| self.ty(&parameter.ty))
                .collect(),
            result: header
                .result
                .as_ref()
                .map(|value| self.ty(value))
                .unwrap_or(Type::Unit),
            effects: self.effect_row(&header.effects),
            invocation: Quantity::ONCE,
            where_bounds,
            where_associated_type_bindings,
            where_associated_effect_bindings,
        }
    }
    fn trait_header(&mut self, header: &TraitHeader) -> ElaboratedTrait {
        self.bind_generics(&header.generics);
        let outer_self_type = self.self_type.replace(Type::Generic(TRAIT_SELF_GENERIC));
        let methods = header
            .methods
            .iter()
            .map(|method| {
                let outer_generics = self.generics.clone();
                let outer_effect_row_generics = self.effect_row_generics.clone();
                let outer_lifetime_generics = self.lifetime_generics.clone();
                let outer_const_generics = self.const_generics.clone();
                let base = self.generic_binder_count();
                self.extend_generics(
                    &method.signature.generics,
                    base,
                    "G4117",
                    "trait method generic shadows an outer generic",
                );
                let (
                    where_bounds,
                    where_associated_type_bindings,
                    where_associated_effect_bindings,
                ) = self.callable_where_bounds(&method.signature.where_bounds);
                let signature = CallableSignature {
                    generics: method.signature.generics.len() as u32,
                    generic_kinds: method.signature.generics.kinds(),
                    parameters: method
                        .signature
                        .parameters
                        .iter()
                        .map(|parameter| self.ty(&parameter.ty))
                        .collect(),
                    result: method
                        .signature
                        .result
                        .as_ref()
                        .map(|value| self.ty(value))
                        .unwrap_or(Type::Unit),
                    effects: self.effect_row(&method.signature.effects),
                    invocation: Quantity::ONCE,
                    where_bounds,
                    where_associated_type_bindings,
                    where_associated_effect_bindings,
                };
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                (method.name.clone(), signature)
            })
            .collect();
        let result = ElaboratedTrait {
            auto_trait: header.auto_trait,
            generics: header.generics.len() as u32,
            generic_kinds: header.generics.kinds(),
            supertraits: header
                .supertraits
                .iter()
                .map(|reference| self.trait_ref(reference))
                .collect(),
            associated_types: header
                .associated_types
                .iter()
                .map(|item| {
                    // Defaults may mention both the trait declaration's
                    // binders and this item's binders.  Give the latter the
                    // same slot assignment used by implementation-side item
                    // definitions, then restore the declaration environment
                    // before elaborating the next item.
                    let outer_generics = self.generics.clone();
                    let outer_effect_row_generics = self.effect_row_generics.clone();
                    let outer_lifetime_generics = self.lifetime_generics.clone();
                    let outer_const_generics = self.const_generics.clone();
                    let base = self.generic_binder_count();
                    self.extend_generics(
                        &item.generics,
                        base,
                        "G4113",
                        "associated type generic shadows an outer generic",
                    );
                    let default = item.default.as_ref().map(|value| self.ty(value));
                    let effect_row_default = item
                        .effect_row_default
                        .as_ref()
                        .map(|value| self.effect_row(value));
                    self.generics = outer_generics;
                    self.effect_row_generics = outer_effect_row_generics;
                    self.lifetime_generics = outer_lifetime_generics;
                    self.const_generics = outer_const_generics;
                    (
                        item.name.clone(),
                        ElaboratedAssociatedType {
                            generics: item.generics.len() as u32,
                            generic_kinds: item.generics.kinds(),
                            effect_row: item.effect_row,
                            default,
                            effect_row_default,
                        },
                    )
                })
                .collect(),
            associated_consts: header
                .associated_consts
                .iter()
                .map(|item| {
                    (
                        item.name.clone(),
                        ElaboratedAssociatedConst {
                            kind: item.kind,
                            default: item
                                .default
                                .as_ref()
                                .map(|value| self.structural_const(value, item.kind)),
                        },
                    )
                })
                .collect(),
            methods,
        };
        self.self_type = outer_self_type;
        result
    }
    fn implementation(&mut self, header: &ImplementationHeader) -> ElaboratedImplementation {
        self.bind_generics(&header.generics);
        if matches!(header.relation.path.as_slice(), [name] if name == "Environment" || name == "RunsIn")
        {
            self.error(
                "G4173",
                format!(
                    "compiler-generated intrinsic `{}` trait is sealed and cannot be manually implemented",
                    header.relation.path.join("::")
                ),
            );
        }
        let relation = self.trait_ref(&header.relation);
        let self_ty = self.ty(&header.self_ty);
        let outer_self_type = self.self_type.replace(self_ty.clone());
        let where_bounds = header
            .where_bounds
            .iter()
            .map(|bound| (self.ty(&bound.subject), self.trait_ref(&bound.relation)))
            .collect();
        let associated_types = header
            .associated_types
            .iter()
            .filter(|item| item.effect_row_value.is_none())
            .map(|item| {
                let outer_generics = self.generics.clone();
                let outer_effect_row_generics = self.effect_row_generics.clone();
                let outer_lifetime_generics = self.lifetime_generics.clone();
                let outer_const_generics = self.const_generics.clone();
                let base = self.generic_binder_count();
                self.extend_generics(
                    &item.generics,
                    base,
                    "G4113",
                    "associated type generic shadows an outer generic",
                );
                let value = self.ty(&item.value);
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                (
                    item.name.clone(),
                    ElaboratedAssociatedTypeDefinition {
                        generics: item.generics.len() as u32,
                        generic_kinds: item.generics.kinds(),
                        value,
                    },
                )
            })
            .collect();
        let associated_effect_rows = header
            .associated_types
            .iter()
            .filter_map(|item| {
                let row = item.effect_row_value.as_ref()?;
                let outer_generics = self.generics.clone();
                let outer_effect_row_generics = self.effect_row_generics.clone();
                let outer_lifetime_generics = self.lifetime_generics.clone();
                let outer_const_generics = self.const_generics.clone();
                let base = self.generic_binder_count();
                self.extend_generics(
                    &item.generics,
                    base,
                    "G4113",
                    "associated effect-row generic shadows an outer generic",
                );
                let value = self.effect_row(row);
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                Some((
                    item.name.clone(),
                    ElaboratedAssociatedEffectRowDefinition {
                        generics: item.generics.len() as u32,
                        generic_kinds: item.generics.kinds(),
                        value,
                    },
                ))
            })
            .collect();
        let associated_consts = header
            .associated_consts
            .iter()
            .map(|item| {
                // Keep literal and binder values source-faithful so the
                // implementation/trait contract pass reports its established
                // kind-mismatch diagnostic. A projection, however, has no
                // intrinsic literal kind: freeze it against the declaration
                // contract that owns this associated item.
                let value = match &item.value {
                    HeaderStructuralConst::U32(value) => GenericArgument::ConstU32(*value),
                    HeaderStructuralConst::Quantity(value) => {
                        GenericArgument::ConstQuantity(*value)
                    }
                    HeaderStructuralConst::Generic(name) => self
                        .const_generics
                        .get(name)
                        .copied()
                        .map(|(index, kind)| GenericArgument::ConstGeneric { index, kind })
                        .unwrap_or_else(|| {
                            self.error(
                                "G4134",
                                format!(
                                    "associated constant `{}` refers to undeclared const binder `{name}`",
                                    item.name
                                ),
                            );
                            GenericArgument::ConstU32(0)
                        }),
                    HeaderStructuralConst::U32Expression(value) => {
                        self.elaborate_structural_u32_expression(value)
                    }
                    HeaderStructuralConst::Projection(_) => {
                        let expected = self
                            .index
                            .associated_const_kind(relation.definition, &item.name)
                            .unwrap_or_else(|| {
                                self.error(
                                    "G4161",
                                    format!(
                                        "implementation defines unknown associated constant `{}`",
                                        item.name
                                    ),
                                );
                                ConstKind::U32
                            });
                        self.structural_const(&item.value, expected)
                    }
                };
                (item.name.clone(), value)
            })
            .collect::<BTreeMap<_, _>>();
        let methods = header
            .methods
            .iter()
            .map(|method| {
                let outer_generics = self.generics.clone();
                let outer_effect_row_generics = self.effect_row_generics.clone();
                let outer_lifetime_generics = self.lifetime_generics.clone();
                let outer_const_generics = self.const_generics.clone();
                let base = self.generic_binder_count();
                self.extend_generics(
                    &method.signature.generics,
                    base,
                    "G4118",
                    "implementation method generic shadows an outer generic",
                );
                let (
                    where_bounds,
                    where_associated_type_bindings,
                    where_associated_effect_bindings,
                ) = self.callable_where_bounds(&method.signature.where_bounds);
                let signature = CallableSignature {
                    generics: method.signature.generics.len() as u32,
                    generic_kinds: method.signature.generics.kinds(),
                    parameters: method
                        .signature
                        .parameters
                        .iter()
                        .map(|parameter| self.ty(&parameter.ty))
                        .collect(),
                    result: method
                        .signature
                        .result
                        .as_ref()
                        .map(|value| self.ty(value))
                        .unwrap_or(Type::Unit),
                    effects: self.effect_row(&method.signature.effects),
                    invocation: Quantity::ONCE,
                    where_bounds,
                    where_associated_type_bindings,
                    where_associated_effect_bindings,
                };
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                (method.name.clone(), signature)
            })
            .collect();
        let result = ElaboratedImplementation {
            generics: header.generics.len() as u32,
            generic_kinds: header.generics.kinds(),
            negative: header.negative,
            relation,
            self_ty,
            where_bounds,
            associated_types,
            associated_effect_rows,
            associated_consts: associated_consts
                .into_iter()
                .map(|(name, value)| {
                    let kind = match &value {
                        GenericArgument::ConstU32(_) => ConstKind::U32,
                        GenericArgument::ConstU32Expr(_) => ConstKind::U32,
                        GenericArgument::ConstQuantity(_) => ConstKind::Quantity,
                        GenericArgument::ConstGeneric { kind, .. } => *kind,
                        GenericArgument::ConstProjection { kind, .. }
                        | GenericArgument::ConstInfer { kind, .. } => *kind,
                        _ => ConstKind::U32,
                    };
                    (name, ElaboratedAssociatedConstDefinition { kind, value })
                })
                .collect(),
            methods,
        };
        self.self_type = outer_self_type;
        result
    }
    fn effect_header(&mut self, header: &EffectHeader) -> ElaboratedEffect {
        self.bind_generics(&header.generics);
        let declaration_generics = self.generics.clone();
        let declaration_effect_row_generics = self.effect_row_generics.clone();
        let declaration_lifetime_generics = self.lifetime_generics.clone();
        let declaration_const_generics = self.const_generics.clone();
        let operations = header
            .operations
            .iter()
            .map(|operation| {
                self.generics = declaration_generics.clone();
                self.effect_row_generics = declaration_effect_row_generics.clone();
                self.lifetime_generics = declaration_lifetime_generics.clone();
                self.const_generics = declaration_const_generics.clone();
                let base = self.generic_binder_count();
                self.extend_generics(
                    &operation.generics,
                    base,
                    "G3301",
                    "effect operation generic shadows a declaration generic",
                );
                ElaboratedEffectOperation {
                    name: operation.name.clone(),
                    generics: base + operation.generics.len() as u32,
                    generic_kinds: header
                        .generics
                        .kinds()
                        .into_iter()
                        .chain(operation.generics.kinds())
                        .collect(),
                    parameters: operation
                        .parameters
                        .iter()
                        .map(|parameter| self.ty(&parameter.ty))
                        .collect(),
                    result: if operation.terminal {
                        Type::Never
                    } else {
                        operation
                            .result
                            .as_ref()
                            .map(|value| self.ty(value))
                            .unwrap_or(Type::Unit)
                    },
                    terminal: operation.terminal,
                    resumption: operation.resumption,
                }
            })
            .collect();
        self.generics = declaration_generics;
        self.effect_row_generics = declaration_effect_row_generics;
        self.lifetime_generics = declaration_lifetime_generics;
        self.const_generics = declaration_const_generics;
        ElaboratedEffect {
            generics: header.generics.len() as u32,
            generic_kinds: header.generics.kinds(),
            operations,
        }
    }
    fn trait_ref(&mut self, value: &TraitRefHeader) -> ElaboratedTraitReference {
        let positional = value
            .arguments
            .iter()
            .filter(|argument| {
                !matches!(
                    argument,
                    HeaderGenericArgument::AssociatedTypeBinding { .. }
                        | HeaderGenericArgument::AssociatedEffectBinding { .. }
                )
            })
            .cloned()
            .collect::<Vec<_>>();
        if positional.len() != value.arguments.len() {
            self.error(
                "G4162",
                "associated type equality is only valid on a callable where-bound".into(),
            );
        }
        self.trait_ref_parts(&value.path, &positional)
    }

    /// Elaborate callable evidence and its associated-item equalities together
    /// so the equality is tied to the exact frozen trait relation rather than
    /// a source path that could resolve differently in an importing module.
    fn callable_where_bounds(
        &mut self,
        bounds: &[crate::header::WhereBoundHeader],
    ) -> (
        Vec<(Type, ElaboratedTraitReference)>,
        Vec<ElaboratedAssociatedTypeBinding>,
        Vec<ElaboratedAssociatedEffectBinding>,
    ) {
        let mut relations = vec![];
        let mut type_bindings = vec![];
        let mut effect_bindings = vec![];
        for bound in bounds {
            let subject = self.ty(&bound.subject);
            let positional = bound
                .relation
                .arguments
                .iter()
                .filter(|argument| {
                    !matches!(
                        argument,
                        HeaderGenericArgument::AssociatedTypeBinding { .. }
                            | HeaderGenericArgument::AssociatedEffectBinding { .. }
                    )
                })
                .cloned()
                .collect::<Vec<_>>();
            let relation = self.trait_ref_parts(&bound.relation.path, &positional);
            for argument in &bound.relation.arguments {
                let HeaderGenericArgument::AssociatedTypeBinding {
                    name,
                    item_arguments,
                    value,
                } = argument
                else {
                    continue;
                };
                let item_generic_kinds = if is_intrinsic_callable_trait(&relation) {
                    if name != "Output" || !item_arguments.is_empty() {
                        self.error(
                            "G4165",
                            "intrinsic `Fn` only accepts the zero-arity `Output = Type` equality"
                                .into(),
                        );
                    }
                    vec![]
                } else if is_intrinsic_runs_in_trait(&relation) {
                    if !matches!(name.as_str(), "Output" | "After") || !item_arguments.is_empty() {
                        self.error(
                            "G4165",
                            "intrinsic `RunsIn` only accepts zero-arity `Output` and `After` type equalities"
                                .into(),
                        );
                    }
                    vec![]
                } else {
                    self.index
                        .associated_type_generic_kinds(relation.definition, name)
                        .map(ToOwned::to_owned)
                        .unwrap_or_else(|| {
                            // An unresolved relation already carries the primary
                            // diagnostic. Preserve the equality in the error
                            // interface rather than inventing an item declaration.
                            if relation.definition
                                != DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait"))
                            {
                                self.error(
                                    "G4163",
                                    format!(
                                        "trait `{}` has no associated type `{name}`",
                                        bound.relation.path.join("::")
                                    ),
                                );
                            }
                            vec![]
                        })
                };
                let elaborated_item_arguments = if item_generic_kinds.is_empty()
                    && relation.definition
                        == DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait"))
                {
                    self.elaborate_unresolved_generic_arguments(item_arguments)
                } else {
                    self.elaborate_type_generic_arguments(name, item_arguments, &item_generic_kinds)
                };
                type_bindings.push(ElaboratedAssociatedTypeBinding {
                    subject: subject.clone(),
                    relation: relation.clone(),
                    name: name.clone(),
                    item_generic_kinds,
                    item_arguments: elaborated_item_arguments,
                    value: self.ty(value),
                });
            }
            for argument in &bound.relation.arguments {
                let HeaderGenericArgument::AssociatedEffectBinding {
                    name,
                    item_arguments,
                    value,
                } = argument
                else {
                    continue;
                };
                let item_generic_kinds = if is_intrinsic_callable_trait(&relation) {
                    if name != "Effects" || !item_arguments.is_empty() {
                        self.error(
                            "G4165",
                            "intrinsic `Fn` only accepts the zero-arity `Effects = Row` equality"
                                .into(),
                        );
                    }
                    vec![]
                } else {
                    self.index
                        .associated_type_generic_kinds(relation.definition, name)
                        .map(ToOwned::to_owned)
                        .unwrap_or_default()
                };
                let elaborated_item_arguments = if item_generic_kinds.is_empty()
                    && relation.definition
                        == DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait"))
                {
                    self.elaborate_unresolved_generic_arguments(item_arguments)
                } else {
                    self.elaborate_type_generic_arguments(name, item_arguments, &item_generic_kinds)
                };
                effect_bindings.push(ElaboratedAssociatedEffectBinding {
                    subject: subject.clone(),
                    relation: relation.clone(),
                    name: name.clone(),
                    item_generic_kinds,
                    item_arguments: elaborated_item_arguments,
                    value: self.effect_row(value),
                });
            }
            relations.push((subject, relation));
        }
        (relations, type_bindings, effect_bindings)
    }

    fn structural_const(
        &mut self,
        value: &HeaderStructuralConst,
        expected: ConstKind,
    ) -> GenericArgument {
        match value {
            HeaderStructuralConst::U32(value) if expected == ConstKind::U32 => {
                GenericArgument::ConstU32(*value)
            }
            HeaderStructuralConst::Quantity(value) if expected == ConstKind::Quantity => {
                GenericArgument::ConstQuantity(*value)
            }
            HeaderStructuralConst::Generic(name) => match self.const_generics.get(name).copied() {
                Some((index, kind)) if kind == expected => {
                    GenericArgument::ConstGeneric { index, kind }
                }
                Some((_, found)) => {
                    self.error(
                        "G4134",
                        format!("structural const binder `{name}` has kind {found:?}, expected {expected:?}"),
                    );
                    fallback_structural_const(expected)
                }
                None => {
                    self.error(
                        "G4134",
                        format!("structural constant refers to undeclared const binder `{name}`"),
                    );
                    fallback_structural_const(expected)
                }
            },
            HeaderStructuralConst::U32Expression(value) if expected == ConstKind::U32 => {
                self.elaborate_structural_u32_expression(value)
            }
            HeaderStructuralConst::Projection(HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            }) => self.associated_const_projection_argument(
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
                expected,
            ),
            value => {
                self.error(
                    "G4134",
                    format!("structural associated constant {value:?} has the wrong kind"),
                );
                fallback_structural_const(expected)
            }
        }
    }

    fn elaborate_structural_u32_expression(
        &mut self,
        value: &HeaderStructuralU32Expr,
    ) -> GenericArgument {
        fn elaborate(
            elaborator: &mut Elaborator<'_>,
            value: &HeaderStructuralU32Expr,
        ) -> Result<StructuralU32Expr, ()> {
            Ok(match value {
                HeaderStructuralU32Expr::Literal(value) => StructuralU32Expr::Literal(*value),
                HeaderStructuralU32Expr::Param(name) => {
                    match elaborator.const_generics.get(name).copied() {
                        Some((index, ConstKind::U32)) => StructuralU32Expr::Param(index),
                        Some((_, found)) => {
                            elaborator.error("G4134", format!("structural const binder `{name}` has kind {found:?}, expected U32"));
                            return Err(());
                        }
                        None => {
                            elaborator.error(
                                "G4134",
                                format!(
                                    "structural constant refers to undeclared const binder `{name}`"
                                ),
                            );
                            return Err(());
                        }
                    }
                }
                HeaderStructuralU32Expr::Add(left, right) => StructuralU32Expr::Add(
                    Box::new(elaborate(elaborator, left)?),
                    Box::new(elaborate(elaborator, right)?),
                ),
                HeaderStructuralU32Expr::Sub(left, right) => StructuralU32Expr::Sub(
                    Box::new(elaborate(elaborator, left)?),
                    Box::new(elaborate(elaborator, right)?),
                ),
                HeaderStructuralU32Expr::Mul(left, right) => StructuralU32Expr::Mul(
                    Box::new(elaborate(elaborator, left)?),
                    Box::new(elaborate(elaborator, right)?),
                ),
                HeaderStructuralU32Expr::Div(left, right) => StructuralU32Expr::Div(
                    Box::new(elaborate(elaborator, left)?),
                    Box::new(elaborate(elaborator, right)?),
                ),
                HeaderStructuralU32Expr::Rem(left, right) => StructuralU32Expr::Rem(
                    Box::new(elaborate(elaborator, left)?),
                    Box::new(elaborate(elaborator, right)?),
                ),
            })
        }
        match elaborate(self, value).and_then(|value| value.normalized().map_err(|_| ())) {
            Ok(StructuralU32Expr::Literal(value)) => GenericArgument::ConstU32(value),
            Ok(value) => GenericArgument::ConstU32Expr(value),
            Err(()) => {
                self.error("G4134", "structural u32 arithmetic overflowed, divided by zero, or exceeded its resource limit".into());
                GenericArgument::ConstU32(0)
            }
        }
    }
    fn trait_ref_parts(
        &mut self,
        path: &[String],
        source_arguments: &[HeaderGenericArgument],
    ) -> ElaboratedTraitReference {
        match self
            .index
            .resolve_path(DefinitionNamespace::Trait, self.module, path)
        {
            ResolutionState::Resolved(definition) => {
                let expected = self.index.trait_generic_arity(definition).unwrap_or(0) as usize;
                let kinds = self.index.trait_generic_kinds(definition).unwrap_or(&[]);
                let name = path.last().map(String::as_str).unwrap_or("<trait>");
                let arguments =
                    self.elaborate_trait_generic_arguments(name, source_arguments, kinds);
                if expected != arguments.len() {
                    self.error(
                        "G3308",
                        format!(
                            "trait `{}` expects {expected} arguments, found {}",
                            path.join("::"),
                            arguments.len()
                        ),
                    );
                }
                ElaboratedTraitReference {
                    definition,
                    arguments,
                }
            }
            ResolutionState::Ambiguous(_) => {
                let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                self.error("G3309", format!("ambiguous trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
            ResolutionState::Inaccessible(_) => {
                let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                self.error("G3310", format!("private trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
            _ => {
                if path == ["Fn"] {
                    let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                    if !matches!(
                        arguments.as_slice(),
                        [GenericArgument::Type(Type::Tuple(_) | Type::Unit)]
                    ) {
                        self.error(
                            "G4164",
                            "intrinsic `Fn` requires exactly one tuple input argument".into(),
                        );
                    }
                    return ElaboratedTraitReference {
                        definition: intrinsic_callable_trait_definition(),
                        arguments,
                    };
                }
                if path == ["Label"] {
                    let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                    if !matches!(arguments.as_slice(), [GenericArgument::Type(_)]) {
                        self.error(
                            "G4170",
                            "intrinsic `Label` requires exactly one payload type argument".into(),
                        );
                    }
                    return ElaboratedTraitReference {
                        definition: intrinsic_label_trait_definition(),
                        arguments,
                    };
                }
                if path == ["RunsIn"] {
                    let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                    if !matches!(
                        arguments.as_slice(),
                        [
                            GenericArgument::Type(_),
                            GenericArgument::Type(Type::Tuple(_) | Type::Unit)
                        ]
                    ) {
                        self.error(
                            "G4173",
                            "intrinsic `RunsIn` requires an environment type and tuple input argument".into(),
                        );
                    }
                    return ElaboratedTraitReference {
                        definition: intrinsic_runs_in_trait_definition(),
                        arguments,
                    };
                }
                if path == ["Environment"] {
                    let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                    if !matches!(arguments.as_slice(), [GenericArgument::Lifetime(_)]) {
                        self.error(
                            "G4173",
                            "intrinsic `Environment` requires exactly one lifetime argument".into(),
                        );
                    }
                    return ElaboratedTraitReference {
                        definition: intrinsic_environment_trait_definition(),
                        arguments,
                    };
                }
                let arguments = self.elaborate_unresolved_generic_arguments(source_arguments);
                self.error("G3310", format!("unresolved trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
        }
    }

    /// Preserve ordinary type arguments for a trait that failed resolution,
    /// while refusing to guess the kind of a structural argument.  A later
    /// resolved interface is the sole authority for admitting const terms.
    fn elaborate_unresolved_generic_arguments(
        &mut self,
        arguments: &[HeaderGenericArgument],
    ) -> Vec<GenericArgument> {
        arguments
            .iter()
            .map(|argument| match argument {
                HeaderGenericArgument::Type(value) => GenericArgument::Type(self.ty(value)),
                HeaderGenericArgument::Lifetime(value) => {
                    GenericArgument::Lifetime(self.lifetime(Some(value)))
                }
                HeaderGenericArgument::EffectRow(value) => {
                    GenericArgument::EffectRow(self.effect_row(value))
                }
                HeaderGenericArgument::U32(value) => GenericArgument::ConstU32(*value),
                HeaderGenericArgument::StructuralConst(value) => {
                    self.structural_const(value, ConstKind::U32)
                }
                HeaderGenericArgument::Quantity(value) => GenericArgument::ConstQuantity(*value),
                HeaderGenericArgument::AssociatedTypeBinding { .. }
                | HeaderGenericArgument::AssociatedEffectBinding { .. } => {
                    self.error(
                        "G4162",
                        "associated type equality is only valid on a callable where-bound".into(),
                    );
                    GenericArgument::Type(Type::Error)
                }
            })
            .collect()
    }
    fn effect_row(&mut self, value: &EffectRowHeader) -> EffectRow {
        let tail = value.tail.as_ref().and_then(|tail| {
            self.effect_row_generics
                .get(tail)
                .copied()
                .map(crate::EffectTail::Generic)
                .or_else(|| {
                    self.error(
                        "G3311",
                        format!("effect-row tail `{tail}` requires a declared `EffectRow` generic binder"),
                    );
                    None
                })
        });
        let mut effects = vec![];
        let mut projections = vec![];
        for effect in &value.effects {
            let (path, arguments) = match effect {
                HeaderType::Path(path) => (path, vec![]),
                HeaderType::Application(base, arguments) => match base.as_ref() {
                    HeaderType::Path(path) => (path, arguments.clone()),
                    _ => {
                        self.error("G3312", "effect row member is not a nominal path".into());
                        continue;
                    }
                },
                HeaderType::Projection {
                    subject,
                    trait_path,
                    trait_arguments,
                    name,
                    item_arguments,
                } => {
                    let subject = self.ty(subject);
                    let relation = self.trait_ref_parts(trait_path, trait_arguments);
                    let item_kinds = self
                        .index
                        .associated_type_generic_kinds(relation.definition, name)
                        .unwrap_or(&[]);
                    projections.push(EffectRowProjection {
                        subject: Box::new(subject),
                        trait_definition: relation.definition,
                        trait_arguments: self.projection_trait_arguments(name, relation.arguments),
                        name: name.clone(),
                        item_generic_kinds: item_kinds.to_vec(),
                        item_arguments: self.elaborate_type_generic_arguments(
                            name,
                            item_arguments,
                            item_kinds,
                        ),
                    });
                    continue;
                }
                _ => {
                    self.error("G3312", "effect row member is not a nominal path".into());
                    continue;
                }
            };
            match self
                .index
                .resolve_path(DefinitionNamespace::Effect, self.module, path)
            {
                ResolutionState::Resolved(definition) => {
                    let expected =
                        self.index.effect_generic_arity(definition).unwrap_or(0) as usize;
                    let kinds = self.index.effect_generic_kinds(definition).unwrap_or(&[]);
                    if expected != arguments.len() {
                        self.error(
                            "G3313",
                            format!(
                                "effect `{}` expects {expected} arguments, found {}",
                                path.join("::"),
                                arguments.len()
                            ),
                        );
                    } else {
                        effects.push(EffectInstance {
                            definition,
                            arguments: self.elaborate_trait_generic_arguments(
                                path.last().map(String::as_str).unwrap_or("<effect>"),
                                &arguments,
                                kinds,
                            ),
                        });
                    }
                }
                ResolutionState::Ambiguous(_) => {
                    self.error("G3314", format!("ambiguous effect `{}`", path.join("::")))
                }
                ResolutionState::Inaccessible(_) => {
                    self.error("G3315", format!("private effect `{}`", path.join("::")))
                }
                _ => self.error("G3315", format!("unresolved effect `{}`", path.join("::"))),
            }
        }
        EffectRow {
            effects: effects.into_iter().collect(),
            projections,
            tail,
        }
        .canonicalized()
    }
    fn nominal_layout(&mut self, layout: &NominalLayoutHeader) -> ElaboratedNominalLayout {
        match layout {
            NominalLayoutHeader::Struct(fields) => ElaboratedNominalLayout::Struct(
                fields
                    .iter()
                    .map(|field| NominalField {
                        name: field.name.clone(),
                        ty: self.ty(&field.ty),
                        private_authority: field.private.then_some(field.span.file),
                    })
                    .collect(),
            ),
            NominalLayoutHeader::Enum(variants) => ElaboratedNominalLayout::Enum(
                variants
                    .iter()
                    .map(|variant| ElaboratedEnumVariant {
                        name: variant.name.clone(),
                        payload: match &variant.payload {
                            EnumVariantPayloadHeader::Unit => ElaboratedEnumVariantPayload::Unit,
                            EnumVariantPayloadHeader::Tuple(fields) => {
                                ElaboratedEnumVariantPayload::Tuple(
                                    fields.iter().map(|field| self.ty(field)).collect(),
                                )
                            }
                            EnumVariantPayloadHeader::Struct(fields) => {
                                ElaboratedEnumVariantPayload::Struct(
                                    fields
                                        .iter()
                                        .map(|field| NominalField {
                                            name: field.name.clone(),
                                            ty: self.ty(&field.ty),
                                            private_authority: field
                                                .private
                                                .then_some(field.span.file),
                                        })
                                        .collect(),
                                )
                            }
                        },
                    })
                    .collect(),
            ),
            NominalLayoutHeader::Opaque => ElaboratedNominalLayout::Opaque,
        }
    }
    fn bind_generics(&mut self, parameters: &GenericParameters) {
        self.generics.clear();
        self.effect_row_generics.clear();
        self.lifetime_generics.clear();
        self.const_generics.clear();
        for (index, name) in parameters.iter().enumerate() {
            if self.generics.contains_key(name)
                || self.effect_row_generics.contains_key(name)
                || self.lifetime_generics.contains_key(name)
                || self.const_generics.contains_key(name)
            {
                self.error("G3301", format!("duplicate generic parameter `{name}`"));
            }
            if parameters.is_effect_row(name) {
                self.effect_row_generics.insert(name.clone(), index as u32);
            } else if parameters.is_lifetime(name) {
                self.lifetime_generics.insert(name.clone(), index as u32);
            } else if let Some(kind) = parameters.const_kind(name) {
                self.const_generics
                    .insert(name.clone(), (index as u32, kind));
            } else {
                self.generics.insert(name.clone(), index as u32);
            }
        }
    }
    fn extend_generics(
        &mut self,
        parameters: &GenericParameters,
        base: u32,
        code: &'static str,
        message: &'static str,
    ) {
        for (offset, name) in parameters.iter().enumerate() {
            if self.generics.contains_key(name)
                || self.effect_row_generics.contains_key(name)
                || self.lifetime_generics.contains_key(name)
                || self.const_generics.contains_key(name)
            {
                self.diagnostics.push(SignatureDiagnostic {
                    code,
                    message: message.into(),
                });
            }
            if parameters.is_effect_row(name) {
                self.effect_row_generics
                    .insert(name.clone(), base + offset as u32);
            } else if parameters.is_lifetime(name) {
                self.lifetime_generics
                    .insert(name.clone(), base + offset as u32);
            } else if let Some(kind) = parameters.const_kind(name) {
                self.const_generics
                    .insert(name.clone(), (base + offset as u32, kind));
            } else {
                self.generics.insert(name.clone(), base + offset as u32);
            }
        }
    }
    fn lifetime(&mut self, spelling: Option<&str>) -> Lifetime {
        match spelling {
            None | Some("'_") => Lifetime::Elided,
            Some("'static") => Lifetime::Static,
            Some(name) => match self
                .bound_lifetime_scopes
                .iter()
                .rev()
                .enumerate()
                .find_map(|(depth, scope)| scope.get(name).map(|index| (depth, index)))
            {
                Some((depth, index)) => Lifetime::Bound {
                    depth: depth as u32,
                    index: *index,
                },
                None => match self.lifetime_generics.get(name) {
                    Some(index) => Lifetime::Generic(*index),
                    None => {
                        self.error("G3315", format!("unbound lifetime `{name}`"));
                        Lifetime::Elided
                    }
                },
            },
        }
    }
    fn ty(&mut self, value: &HeaderType) -> Type {
        match value {
            HeaderType::Never => Type::Never,
            HeaderType::Recovered => Type::Error,
            HeaderType::Tuple(values) if values.is_empty() => Type::Unit,
            HeaderType::Tuple(values) => {
                Type::Tuple(values.iter().map(|value| self.ty(value)).collect())
            }
            HeaderType::Callable {
                lifetime_binders,
                parameters,
                result,
                effects,
            } => {
                let mut scope = BTreeMap::new();
                for (index, name) in lifetime_binders.iter().enumerate() {
                    if scope.insert(name.clone(), index as u32).is_some() {
                        self.error(
                            "G3326",
                            format!("duplicate higher-ranked lifetime `{name}`"),
                        );
                    }
                }
                self.bound_lifetime_scopes.push(scope);
                let parameters = parameters.iter().map(|value| self.ty(value)).collect();
                let result = Box::new(self.ty(result));
                let effects = self.effect_row(effects);
                self.bound_lifetime_scopes.pop();
                Type::Callable {
                    lifetime_binders: lifetime_binders.len() as u32,
                    parameters,
                    result,
                    effects,
                    invocation: Quantity::ONCE,
                }
            }
            HeaderType::Reference {
                unique,
                lifetime,
                referent,
            } => Type::Reference {
                mutability: if *unique {
                    Mutability::Unique
                } else {
                    Mutability::Shared
                },
                lifetime: self.lifetime(lifetime.as_deref()),
                referent: Box::new(self.ty(referent)),
            },
            HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            } => {
                let subject = self.ty(subject);
                let relation = self.trait_ref_parts(trait_path, trait_arguments);
                let item_kinds = self
                    .index
                    .associated_type_generic_kinds(relation.definition, name)
                    .unwrap_or(&[]);
                Type::Projection {
                    subject: Box::new(subject),
                    trait_definition: relation.definition,
                    trait_arguments: self.projection_trait_arguments(name, relation.arguments),
                    name: name.clone(),
                    item_generic_kinds: item_kinds.to_vec(),
                    item_arguments: self.elaborate_type_generic_arguments(
                        name,
                        item_arguments,
                        item_kinds,
                    ),
                }
            }
            HeaderType::Path(path) => self.path(path, vec![]),
            HeaderType::Application(base, arguments) => match base.as_ref() {
                HeaderType::Path(path) => self.path(path, arguments.clone()),
                _ => {
                    self.error(
                        "G3302",
                        "type application base is not a nominal path".into(),
                    );
                    Type::Error
                }
            },
        }
    }
    fn path(&mut self, path: &[String], arguments: Vec<HeaderGenericArgument>) -> Type {
        let Some(name) = path.last() else {
            return Type::Error;
        };
        if path.len() == 1 {
            if name == "Available" {
                let arguments = self.elaborate_unresolved_generic_arguments(&arguments);
                if !matches!(
                    arguments.as_slice(),
                    [GenericArgument::Lifetime(_), GenericArgument::Type(_)]
                ) {
                    self.error(
                        "G4173",
                        "intrinsic `Available` requires a lifetime and environment type argument"
                            .into(),
                    );
                }
                return Type::Nominal {
                    definition: intrinsic_available_type_definition(),
                    arguments,
                };
            }
            if name == "Self" {
                return if arguments.is_empty() {
                    match &self.self_type {
                        Some(value) => value.clone(),
                        None => {
                            self.error(
                                "G3319",
                                "`Self` is only valid in a trait or implementation member".into(),
                            );
                            Type::Error
                        }
                    }
                } else {
                    self.arity(name, 0, arguments.len());
                    Type::Error
                };
            }
            if let Some(index) = self.generics.get(name) {
                return if arguments.is_empty() {
                    Type::Generic(*index)
                } else {
                    self.arity(name, 0, arguments.len());
                    Type::Error
                };
            }
            if self.effect_row_generics.contains_key(name) {
                self.error(
                    "G3313",
                    format!("effect-row generic `{name}` cannot be used as a type"),
                );
                return Type::Error;
            }
            if self.lifetime_generics.contains_key(name) {
                self.error(
                    "G3316",
                    format!("lifetime generic `{name}` cannot be used as a type"),
                );
                return Type::Error;
            }
            if let Some((_, kind)) = self.const_generics.get(name) {
                self.error(
                    "G3317",
                    format!(
                        "const generic `{name}` of kind `{}` cannot be used as a type",
                        const_kind_name(*kind)
                    ),
                );
                return Type::Error;
            }
            // `Bool` is a source-level standard-library carrier in the
            // canonical bootstrap.  A local alias must therefore win over
            // Stage-0's legacy scalar fallback; otherwise
            // `type Bool = Result<(), ()>` is silently ignored and every
            // source-defined truth literal receives the wrong type.
            if name == "Bool"
                && let ResolutionState::Resolved(definition) =
                    self.index
                        .resolve_path(DefinitionNamespace::Type, self.module, path)
            {
                let expected = self.index.type_generic_arity(definition).unwrap_or(0) as usize;
                if expected != arguments.len() {
                    self.arity(name, expected, arguments.len());
                    return Type::Error;
                }
                let kinds = self.index.type_generic_kinds(definition).unwrap_or(&[]);
                return Type::Nominal {
                    definition,
                    arguments: self.elaborate_type_generic_arguments(name, &arguments, kinds),
                };
            }
            if let Some(scalar) = scalar(name) {
                return if arguments.is_empty() {
                    Type::Scalar(scalar)
                } else {
                    self.arity(name, 0, arguments.len());
                    Type::Error
                };
            }
            if name == "Array" {
                return match arguments.as_slice() {
                    [HeaderGenericArgument::Type(element)] => {
                        Type::Array(Box::new(self.ty(element)))
                    }
                    _ => {
                        self.arity(name, 1, arguments.len());
                        Type::Error
                    }
                };
            }
        }
        match self
            .index
            .resolve_path(DefinitionNamespace::Type, self.module, path)
        {
            ResolutionState::Resolved(definition) => {
                let expected = self.index.type_generic_arity(definition).unwrap_or(0) as usize;
                if expected != arguments.len() {
                    self.arity(name, expected, arguments.len());
                    Type::Error
                } else {
                    let kinds = self.index.type_generic_kinds(definition).unwrap_or(&[]);
                    Type::Nominal {
                        definition,
                        arguments: self.elaborate_type_generic_arguments(name, &arguments, kinds),
                    }
                }
            }
            ResolutionState::Ambiguous(_) => {
                self.error("G3303", format!("ambiguous type `{}`", path.join("::")));
                Type::Error
            }
            ResolutionState::Inaccessible(_) => {
                self.error("G3304", format!("private type `{}`", path.join("::")));
                Type::Error
            }
            _ => {
                self.error("G3304", format!("unresolved type `{}`", path.join("::")));
                Type::Error
            }
        }
    }
    fn elaborate_type_generic_arguments(
        &mut self,
        name: &str,
        arguments: &[HeaderGenericArgument],
        kinds: &[GenericKind],
    ) -> Vec<GenericArgument> {
        self.elaborate_trait_generic_arguments(name, arguments, kinds)
    }

    /// Trait references are identity-bearing rather than immediately runtime
    /// callable applications, so retain the kind of each supplied slot.
    fn elaborate_trait_generic_arguments(
        &mut self,
        name: &str,
        arguments: &[HeaderGenericArgument],
        kinds: &[GenericKind],
    ) -> Vec<GenericArgument> {
        if arguments.len() != kinds.len() {
            self.arity(name, kinds.len(), arguments.len());
        }
        arguments
            .iter()
            .zip(kinds)
            .map(|(argument, kind)| match (argument, kind) {
                (HeaderGenericArgument::Type(value), GenericKind::Type) => {
                    GenericArgument::Type(self.ty(value))
                }
                (HeaderGenericArgument::Lifetime(value), GenericKind::Lifetime) => {
                    GenericArgument::Lifetime(self.lifetime(Some(value)))
                }
                (HeaderGenericArgument::EffectRow(value), GenericKind::EffectRow) => {
                    GenericArgument::EffectRow(self.effect_row(value))
                }
                (HeaderGenericArgument::Type(HeaderType::Path(path)), GenericKind::EffectRow)
                    if path.len() == 1 => match self.effect_row_generics.get(&path[0]) {
                        Some(index) => GenericArgument::EffectRow(EffectRow {
                            effects: Default::default(),
                            projections: vec![],
                            tail: Some(EffectTail::Generic(*index)),
                        }),
                        None => {
                            self.error(
                                "G3318",
                                format!("generic argument for `{name}` must be an effect-row generic"),
                            );
                            GenericArgument::EffectRow(EffectRow::empty())
                        }
                    },
                (HeaderGenericArgument::U32(value), GenericKind::Const(ConstKind::U32)) => {
                    GenericArgument::ConstU32(*value)
                }
                (
                    HeaderGenericArgument::Type(HeaderType::Projection {
                        subject,
                        trait_path,
                        trait_arguments,
                        name: projection_name,
                        item_arguments,
                    }),
                    GenericKind::Const(kind),
                ) => self.associated_const_projection_argument(
                    subject,
                    trait_path,
                    trait_arguments,
                    projection_name,
                    item_arguments,
                    *kind,
                ),
                (HeaderGenericArgument::StructuralConst(value), GenericKind::Const(ConstKind::U32)) => {
                    self.structural_const(value, ConstKind::U32)
                }
                (
                    HeaderGenericArgument::Quantity(value),
                    GenericKind::Const(ConstKind::Quantity),
                ) => GenericArgument::ConstQuantity(*value),
                (HeaderGenericArgument::Type(HeaderType::Path(path)), GenericKind::Const(kind))
                    if path.len() == 1 => match self.const_generics.get(&path[0]) {
                        Some((index, found)) if found == kind => GenericArgument::ConstGeneric {
                            index: *index,
                            kind: *kind,
                        },
                        _ => {
                            self.error(
                                "G3318",
                                format!(
                                    "generic argument for `{name}` must be a structural `{}` constant",
                                    const_kind_name(*kind),
                                ),
                            );
                            GenericArgument::ConstGeneric {
                                index: u32::MAX,
                                kind: *kind,
                            }
                        }
                    },
                (HeaderGenericArgument::U32(_), GenericKind::Type)
                | (HeaderGenericArgument::StructuralConst(_), GenericKind::Type)
                | (HeaderGenericArgument::Quantity(_), GenericKind::Type)
                | (HeaderGenericArgument::Lifetime(_), GenericKind::Type)
                | (HeaderGenericArgument::EffectRow(_), GenericKind::Type)
                | (HeaderGenericArgument::AssociatedTypeBinding { .. }, GenericKind::Type)
                | (HeaderGenericArgument::AssociatedEffectBinding { .. }, GenericKind::Type) => {
                    self.error(
                        "G3318",
                        format!("type slot of `{name}` cannot receive a structural constant"),
                    );
                    GenericArgument::Type(Type::Error)
                }
                (_, GenericKind::Const(kind)) => {
                    self.error(
                        "G3318",
                        format!(
                            "generic argument for `{name}` must be a structural `{}` constant",
                            const_kind_name(*kind),
                        ),
                    );
                    GenericArgument::ConstGeneric {
                        index: u32::MAX,
                        kind: *kind,
                    }
                }
                (_, GenericKind::EffectRow) => {
                    self.error(
                        "G3318",
                        format!("generic argument for `{name}` must be an effect-row generic"),
                    );
                    GenericArgument::EffectRow(EffectRow::empty())
                }
                (_, GenericKind::Lifetime) => {
                    self.error(
                        "G3318",
                        format!("generic argument for `{name}` must be a lifetime generic"),
                    );
                    GenericArgument::Lifetime(Lifetime::Elided)
                }
            })
            .collect()
    }

    /// Preserve an associated structural-constant selection in a frozen
    /// signature.  Unlike a body, a declaration may be generic over its
    /// subject, so selecting implementation evidence here would be both
    /// premature and order dependent.  The canonical `ConstProjection`
    /// carrier records the complete mixed-kind trait head for later concrete
    /// instantiation.
    fn associated_const_projection_argument(
        &mut self,
        subject: &HeaderType,
        trait_path: &[String],
        trait_arguments: &[HeaderGenericArgument],
        name: &str,
        item_arguments: &[HeaderGenericArgument],
        kind: ConstKind,
    ) -> GenericArgument {
        if !item_arguments.is_empty() {
            self.error(
                "G4135",
                "associated constants do not accept item arguments".into(),
            );
        }
        let relation = self.trait_ref_parts(trait_path, trait_arguments);
        GenericArgument::ConstProjection {
            subject: Box::new(self.ty(subject)),
            trait_definition: relation.definition,
            trait_arguments: relation.arguments,
            name: name.into(),
            kind,
        }
    }

    /// A projection preserves the enclosing trait's complete source-slot
    /// identity. Runtime lowering still rejects unresolved symbolic types;
    /// it must not erase regions, rows, or structural constants beforehand.
    fn projection_trait_arguments(
        &mut self,
        _name: &str,
        arguments: Vec<GenericArgument>,
    ) -> Vec<GenericArgument> {
        arguments
    }
    fn arity(&mut self, name: &str, expected: usize, found: usize) {
        self.error(
            "G3305",
            format!("type `{name}` expects {expected} arguments, found {found}"),
        );
    }
    fn error(&mut self, code: &'static str, message: String) {
        self.diagnostics.push(SignatureDiagnostic { code, message });
    }
}

fn scalar(name: &str) -> Option<crate::types::ScalarType> {
    use crate::types::ScalarType::*;
    Some(match name {
        "Bool" => Bool,
        "u8" => U8,
        "u16" => U16,
        "u32" => U32,
        "u64" => U64,
        "u128" => U128,
        "i8" => I8,
        "i16" => I16,
        "i32" => I32,
        "i64" => I64,
        "i128" => I128,
        "usize" => Usize,
        "isize" => Isize,
        "f32" => F32,
        "f64" => F64,
        "char" => Char,
        "Text" => Text,
        "Bytes" => Bytes,
        _ => return None,
    })
}

fn const_kind_name(kind: ConstKind) -> &'static str {
    match kind {
        ConstKind::U32 => "u32",
        ConstKind::Quantity => "Quantity",
    }
}

fn normalize_alias_generic_argument(
    argument: GenericArgument,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    stack: &mut Vec<DefKey>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => {
            GenericArgument::Type(normalize_alias_type(value, definitions, stack, diagnostics))
        }
        GenericArgument::EffectRow(value) => GenericArgument::EffectRow(
            normalize_alias_effect_row(value, definitions, stack, diagnostics),
        ),
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(normalize_alias_type(
                *subject,
                definitions,
                stack,
                diagnostics,
            )),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| {
                    normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                })
                .collect(),
            name,
            kind,
        },
        argument => argument,
    }
}

/// Normalize every semantic leaf carried by a row-valued alias argument.
/// Rows can contain delayed associated effects whose subjects and generic
/// applications are every bit as identity-bearing as direct effect instances.
/// Leaving those leaves source-spelled made `Alias<{ <Value as Trait<Count>>::E
/// }>` freeze differently from the alpha-equivalent direct `i64` spelling.
fn normalize_alias_effect_row(
    value: EffectRow,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    stack: &mut Vec<DefKey>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| {
                        normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                    })
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(normalize_alias_type(
                    *projection.subject,
                    definitions,
                    stack,
                    diagnostics,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|argument| {
                        normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                    })
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|argument| {
                        normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                    })
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

fn normalize_alias_type(
    value: Type,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    stack: &mut Vec<DefKey>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) -> Type {
    match value {
        Type::Nominal {
            definition,
            arguments,
        } => {
            let arguments = arguments
                .into_iter()
                .map(|argument| {
                    normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                })
                .collect::<Vec<_>>();
            let Some(ElaboratedHeader::Alias { generics, target }) = definitions.get(&definition)
            else {
                return Type::Nominal {
                    definition,
                    arguments,
                };
            };
            if *generics as usize != arguments.len() {
                diagnostics.push(SignatureDiagnostic {
                    code: "G3306",
                    message: format!(
                        "type alias expects {} arguments, found {}",
                        generics,
                        arguments.len()
                    ),
                });
                return Type::Error;
            }
            if stack.contains(&definition) {
                diagnostics.push(SignatureDiagnostic {
                    code: "G3307",
                    message: "cyclic transparent type alias".into(),
                });
                return Type::Error;
            }
            stack.push(definition);
            let substituted = substitute_alias_generic_identity(target.clone(), &arguments);
            let normalized = normalize_alias_type(substituted, definitions, stack, diagnostics);
            stack.pop();
            normalized
        }
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(normalize_alias_type(
                *subject,
                definitions,
                stack,
                diagnostics,
            )),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| {
                    normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                })
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|argument| {
                    normalize_alias_generic_argument(argument, definitions, stack, diagnostics)
                })
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| normalize_alias_type(value, definitions, stack, diagnostics))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(normalize_alias_type(
            *value,
            definitions,
            stack,
            diagnostics,
        ))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime,
            referent: Box::new(normalize_alias_type(
                *referent,
                definitions,
                stack,
                diagnostics,
            )),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| normalize_alias_type(value, definitions, stack, diagnostics))
                .collect(),
            result: Box::new(normalize_alias_type(
                *result,
                definitions,
                stack,
                diagnostics,
            )),
            effects: normalize_alias_effect_row(effects, definitions, stack, diagnostics),
            invocation,
        },
        value => value,
    }
}

fn normalize_nominal_layout(
    layout: &mut ElaboratedNominalLayout,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) {
    match layout {
        ElaboratedNominalLayout::Struct(fields) => {
            normalize_nominal_fields(fields, definitions, diagnostics)
        }
        ElaboratedNominalLayout::Enum(variants) => {
            for variant in variants {
                match &mut variant.payload {
                    ElaboratedEnumVariantPayload::Unit => {}
                    ElaboratedEnumVariantPayload::Tuple(fields) => {
                        for field in fields {
                            *field = normalize_alias_type(
                                field.clone(),
                                definitions,
                                &mut vec![],
                                diagnostics,
                            );
                        }
                    }
                    ElaboratedEnumVariantPayload::Struct(fields) => {
                        normalize_nominal_fields(fields, definitions, diagnostics)
                    }
                }
            }
        }
        ElaboratedNominalLayout::Opaque => {}
    }
}

fn normalize_nominal_fields(
    fields: &mut [NominalField],
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
    diagnostics: &mut Vec<SignatureDiagnostic>,
) {
    for field in fields {
        field.ty = normalize_alias_type(field.ty.clone(), definitions, &mut vec![], diagnostics);
    }
}

/// Substitute transparent-alias binders without crossing a runtime type-only
/// boundary. Alias applications are nominal identity, so a region, row, or
/// structural constant must survive just as it does in a direct nominal path.
fn substitute_alias_generic_identity(value: Type, arguments: &[GenericArgument]) -> Type {
    match value {
        Type::Generic(TRAIT_SELF_GENERIC) => Type::Generic(TRAIT_SELF_GENERIC),
        Type::Generic(index) => arguments
            .get(index as usize)
            .and_then(generic_argument_as_type)
            .unwrap_or(Type::Error),
        Type::ConstGeneric { index, kind } => arguments
            .get(index as usize)
            .and_then(|argument| generic_argument_as_const_type(argument, kind))
            .unwrap_or(Type::Error),
        Type::Nominal {
            definition,
            arguments: values,
        } => Type::Nominal {
            definition,
            arguments: values
                .into_iter()
                .map(|argument| substitute_alias_generic_identity_argument(argument, arguments))
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
            subject: Box::new(substitute_alias_generic_identity(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_alias_generic_identity_argument(value, arguments))
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_alias_generic_identity_argument(value, arguments))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| substitute_alias_generic_identity(value, arguments))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(substitute_alias_generic_identity(
            *value, arguments,
        ))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime: substitute_alias_lifetime(lifetime, arguments),
            referent: Box::new(substitute_alias_generic_identity(*referent, arguments)),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| substitute_alias_generic_identity(value, arguments))
                .collect(),
            result: Box::new(substitute_alias_generic_identity(*result, arguments)),
            effects: substitute_alias_generic_identity_effect_row(effects, arguments),
            invocation,
        },
        value => value,
    }
}

fn substitute_alias_generic_identity_argument(
    argument: GenericArgument,
    arguments: &[GenericArgument],
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => {
            GenericArgument::Type(substitute_alias_generic_identity(value, arguments))
        }
        GenericArgument::EffectRow(value) => GenericArgument::EffectRow(
            substitute_alias_generic_identity_effect_row(value, arguments),
        ),
        GenericArgument::ConstProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            kind,
        } => GenericArgument::ConstProjection {
            subject: Box::new(substitute_alias_generic_identity(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|argument| substitute_alias_generic_identity_argument(argument, arguments))
                .collect(),
            name,
            kind,
        },
        GenericArgument::Lifetime(value) => {
            GenericArgument::Lifetime(substitute_alias_lifetime(value, arguments))
        }
        GenericArgument::ConstGeneric { index, kind } => arguments
            .get(index as usize)
            .filter(|argument| generic_argument_matches_const_kind(argument, kind))
            .cloned()
            .unwrap_or(GenericArgument::ConstGeneric { index, kind }),
        GenericArgument::ConstU32Expr(value) => match value.substitute(arguments) {
            StructuralU32Expr::Literal(value) => GenericArgument::ConstU32(value),
            value => GenericArgument::ConstU32Expr(value),
        },
        argument => argument,
    }
}

fn substitute_alias_generic_identity_associated_type_binding(
    binding: ElaboratedAssociatedTypeBinding,
    arguments: &[GenericArgument],
) -> ElaboratedAssociatedTypeBinding {
    ElaboratedAssociatedTypeBinding {
        subject: substitute_alias_generic_identity(binding.subject, arguments),
        relation: substitute_trait_reference(&binding.relation, arguments),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| substitute_alias_generic_identity_argument(argument, arguments))
            .collect(),
        value: substitute_alias_generic_identity(binding.value, arguments),
    }
}

fn substitute_alias_generic_identity_associated_effect_binding(
    binding: ElaboratedAssociatedEffectBinding,
    arguments: &[GenericArgument],
) -> ElaboratedAssociatedEffectBinding {
    ElaboratedAssociatedEffectBinding {
        subject: substitute_alias_generic_identity(binding.subject, arguments),
        relation: substitute_trait_reference(&binding.relation, arguments),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| substitute_alias_generic_identity_argument(argument, arguments))
            .collect(),
        value: substitute_alias_generic_identity_effect_row(binding.value, arguments),
    }
}

fn substitute_alias_lifetime(value: Lifetime, arguments: &[GenericArgument]) -> Lifetime {
    match value {
        Lifetime::Generic(index) => arguments
            .get(index as usize)
            .and_then(|argument| match argument {
                GenericArgument::Lifetime(value) => Some(*value),
                _ => None,
            })
            .unwrap_or(value),
        value => value,
    }
}

fn substitute_alias_generic_identity_effect_row(
    value: EffectRow,
    arguments: &[GenericArgument],
) -> EffectRow {
    let mut row = EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| substitute_alias_generic_identity_argument(argument, arguments))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(substitute_alias_generic_identity(
                    *projection.subject,
                    arguments,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|value| substitute_alias_generic_identity_argument(value, arguments))
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_alias_generic_identity_argument(value, arguments))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    };
    if let Some(EffectTail::Generic(index)) = row.tail
        && let Some(GenericArgument::EffectRow(argument)) = arguments.get(index as usize)
    {
        row.effects.extend(argument.effects.clone());
        row.projections.extend(argument.projections.clone());
        row.tail = argument.tail;
    }
    row.canonicalized()
}

fn substitute_alias_generics(value: Type, arguments: &[Type]) -> Type {
    match value {
        Type::Generic(TRAIT_SELF_GENERIC) => Type::Generic(TRAIT_SELF_GENERIC),
        Type::Generic(index) | Type::ConstGeneric { index, .. } => arguments
            .get(index as usize)
            .cloned()
            .unwrap_or(Type::Error),
        Type::Nominal {
            definition,
            arguments: values,
        } => Type::Nominal {
            definition,
            arguments: values
                .into_iter()
                .map(|value| substitute_alias_effect_generic_argument(value, arguments))
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
            subject: Box::new(substitute_alias_generics(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_alias_effect_generic_argument(value, arguments))
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_alias_effect_generic_argument(value, arguments))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| substitute_alias_generics(value, arguments))
                .collect(),
        ),
        Type::Array(value) => Type::Array(Box::new(substitute_alias_generics(*value, arguments))),
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime,
            referent: Box::new(substitute_alias_generics(*referent, arguments)),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| substitute_alias_generics(value, arguments))
                .collect(),
            result: Box::new(substitute_alias_generics(*result, arguments)),
            effects: substitute_effect_row(effects, arguments),
            invocation,
        },
        value => value,
    }
}

fn substitute_effect_row(value: EffectRow, arguments: &[Type]) -> EffectRow {
    EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| substitute_alias_effect_generic_argument(argument, arguments))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(substitute_alias_generics(*projection.subject, arguments)),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|value| substitute_alias_effect_generic_argument(value, arguments))
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_alias_effect_generic_argument(value, arguments))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

fn substitute_alias_effect_generic_argument(
    argument: GenericArgument,
    arguments: &[Type],
) -> GenericArgument {
    match argument {
        GenericArgument::Type(value) => {
            GenericArgument::Type(substitute_alias_generics(value, arguments))
        }
        GenericArgument::EffectRow(value) => {
            GenericArgument::EffectRow(substitute_effect_row(value, arguments))
        }
        GenericArgument::ConstGeneric { index, kind } => arguments
            .get(index as usize)
            .and_then(|value| match (value, kind) {
                (Type::ConstU32(value), ConstKind::U32) => Some(GenericArgument::ConstU32(*value)),
                (Type::ConstQuantity(value), ConstKind::Quantity) => {
                    Some(GenericArgument::ConstQuantity(*value))
                }
                (Type::ConstGeneric { index, kind: found }, expected) if found == &expected => {
                    Some(GenericArgument::ConstGeneric {
                        index: *index,
                        kind: expected,
                    })
                }
                _ => None,
            })
            .unwrap_or(GenericArgument::ConstGeneric { index, kind }),
        argument => argument,
    }
}

fn substitute_alias_generics_associated_type_binding(
    binding: ElaboratedAssociatedTypeBinding,
    arguments: &[Type],
) -> ElaboratedAssociatedTypeBinding {
    ElaboratedAssociatedTypeBinding {
        subject: substitute_alias_generics(binding.subject, arguments),
        relation: substitute_trait_reference_with_types(&binding.relation, arguments),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| substitute_alias_effect_generic_argument(argument, arguments))
            .collect(),
        value: substitute_alias_generics(binding.value, arguments),
    }
}

fn substitute_alias_generics_associated_effect_binding(
    binding: ElaboratedAssociatedEffectBinding,
    arguments: &[Type],
) -> ElaboratedAssociatedEffectBinding {
    ElaboratedAssociatedEffectBinding {
        subject: substitute_alias_generics(binding.subject, arguments),
        relation: substitute_trait_reference_with_types(&binding.relation, arguments),
        name: binding.name,
        item_generic_kinds: binding.item_generic_kinds,
        item_arguments: binding
            .item_arguments
            .into_iter()
            .map(|argument| substitute_alias_effect_generic_argument(argument, arguments))
            .collect(),
        value: substitute_effect_row(binding.value, arguments),
    }
}

/// Substitute declaration generic slots into a type consumer.  This boundary
/// is deliberately type-valued: a row or lifetime argument cannot enter a
/// value type, and a mismatched kind recovers as `Type::Error` instead.
fn substitute_trait_type_generics(value: Type, arguments: &[GenericArgument]) -> Type {
    match value {
        // Trait `Self` is not a source generic slot.  It must survive alias
        // normalization until trait-method instantiation supplies the selected
        // implementation head.
        Type::Generic(TRAIT_SELF_GENERIC) => Type::Generic(TRAIT_SELF_GENERIC),
        Type::Generic(index) => arguments
            .get(index as usize)
            .and_then(generic_argument_as_type)
            .unwrap_or(Type::Error),
        Type::ConstGeneric { index, kind } => arguments
            .get(index as usize)
            .and_then(|argument| generic_argument_as_const_type(argument, kind))
            .unwrap_or(Type::Error),
        Type::Nominal {
            definition,
            arguments: values,
        } => Type::Nominal {
            definition,
            arguments: values
                .into_iter()
                .map(|value| substitute_trait_generic_argument(value, arguments))
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
            subject: Box::new(substitute_trait_type_generics(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_trait_generic_argument(value, arguments))
                .collect(),
            name,
            item_generic_kinds,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_trait_generic_argument(value, arguments))
                .collect(),
        },
        Type::Tuple(values) => Type::Tuple(
            values
                .into_iter()
                .map(|value| substitute_trait_type_generics(value, arguments))
                .collect(),
        ),
        Type::Array(value) => {
            Type::Array(Box::new(substitute_trait_type_generics(*value, arguments)))
        }
        Type::Reference {
            mutability,
            lifetime,
            referent,
        } => Type::Reference {
            mutability,
            lifetime: match lifetime {
                Lifetime::Generic(index) => arguments
                    .get(index as usize)
                    .and_then(|argument| match argument {
                        GenericArgument::Lifetime(lifetime) => Some(*lifetime),
                        _ => None,
                    })
                    .unwrap_or(lifetime),
                lifetime => lifetime,
            },
            referent: Box::new(substitute_trait_type_generics(*referent, arguments)),
        },
        Type::Callable {
            lifetime_binders,
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
            lifetime_binders,
            parameters: parameters
                .into_iter()
                .map(|value| substitute_trait_type_generics(value, arguments))
                .collect(),
            result: Box::new(substitute_trait_type_generics(*result, arguments)),
            effects: substitute_trait_effect_row(effects, arguments),
            invocation,
        },
        value => value,
    }
}

/// Instantiate every type nested in an effect row. Effect arguments are part
/// of a callable's observable protocol, so leaving declaration-owned generic
/// slots here would make `f<T> / State<T>` appear to perform `State<Generic(0)>`
/// at every call site.
fn generic_argument_as_type(argument: &GenericArgument) -> Option<Type> {
    match argument {
        GenericArgument::Type(value) => Some(value.clone()),
        _ => None,
    }
}

fn generic_argument_as_const_type(argument: &GenericArgument, kind: ConstKind) -> Option<Type> {
    match (argument, kind) {
        (GenericArgument::ConstU32(value), ConstKind::U32) => Some(Type::ConstU32(*value)),
        (GenericArgument::ConstQuantity(value), ConstKind::Quantity) => {
            Some(Type::ConstQuantity(*value))
        }
        (GenericArgument::ConstGeneric { index, kind: found }, kind) if *found == kind => {
            Some(Type::ConstGeneric {
                index: *index,
                kind,
            })
        }
        _ => None,
    }
}

fn substitute_trait_effect_row(value: EffectRow, arguments: &[GenericArgument]) -> EffectRow {
    let tail = value.tail;
    let mut result = EffectRow {
        effects: value
            .effects
            .into_iter()
            .map(|effect| EffectInstance {
                definition: effect.definition,
                arguments: effect
                    .arguments
                    .into_iter()
                    .map(|argument| substitute_trait_generic_argument(argument, arguments))
                    .collect(),
            })
            .collect(),
        projections: value
            .projections
            .into_iter()
            .map(|projection| EffectRowProjection {
                subject: Box::new(substitute_trait_type_generics(
                    *projection.subject,
                    arguments,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|value| substitute_trait_generic_argument(value, arguments))
                    .collect(),
                name: projection.name,
                item_generic_kinds: projection.item_generic_kinds,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_trait_generic_argument(value, arguments))
                    .collect(),
            })
            .collect(),
        tail,
    };
    if let Some(EffectTail::Generic(index)) = tail
        && let Some(GenericArgument::EffectRow(row)) = arguments.get(index as usize)
    {
        result.effects.extend(row.effects.iter().cloned());
        result.projections.extend(row.projections.iter().cloned());
        result.tail = row.tail;
    }
    result.canonicalized()
}
