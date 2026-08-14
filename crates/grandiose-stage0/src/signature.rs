//! Header elaboration into canonical, body-independent semantic signatures.

use std::collections::BTreeMap;

use crate::{
    header::{
        CallableHeader, EffectHeader, EffectRowHeader, EnumVariantPayloadHeader, GenericParameters,
        HeaderGenericArgument, HeaderType, ImplementationHeader, NominalLayoutHeader, ParsedHeader,
        TraitHeader, TraitRefHeader,
    },
    identity::{DefKey, ModuleKey},
    interface::{Definition, DefinitionNamespace, PackageInterface},
    quantity::Quantity,
    resolution::{DefinitionIndex, ResolutionState},
    types::{
        ConstKind, EffectInstance, EffectRow, EffectRowProjection, GenericKind, Lifetime,
        Mutability, Type,
    },
};

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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedTraitReference {
    pub definition: DefKey,
    pub arguments: Vec<Type>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedTrait {
    pub generics: u32,
    pub supertraits: Vec<ElaboratedTraitReference>,
    /// Declared associated type names and their item-generic arities. The
    /// frozen interface retains this metadata so projection syntax can keep
    /// trait and associated-item arguments distinct through normalization.
    pub associated_types: BTreeMap<String, ElaboratedAssociatedType>,
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
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedImplementation {
    pub generics: u32,
    pub negative: bool,
    pub relation: ElaboratedTraitReference,
    pub self_ty: Type,
    pub where_bounds: Vec<(Type, ElaboratedTraitReference)>,
    pub associated_types: BTreeMap<String, ElaboratedAssociatedTypeDefinition>,
    pub associated_effect_rows: BTreeMap<String, ElaboratedAssociatedEffectRowDefinition>,
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
pub struct ElaboratedEffectOperation {
    pub name: String,
    /// Declaration and operation binders share this namespace.  The first
    /// `effect_generics` slots belong to the protocol declaration.
    pub generics: u32,
    pub parameters: Vec<Type>,
    pub result: Type,
    pub terminal: bool,
    pub resumption: Quantity,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedEffect {
    pub generics: u32,
    pub operations: Vec<ElaboratedEffectOperation>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NominalField {
    pub name: String,
    pub ty: Type,
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

#[derive(Clone, Debug, Default)]
pub struct ElaboratedInterface {
    pub definitions: BTreeMap<DefKey, ElaboratedHeader>,
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

impl ElaboratedInterface {
    pub fn elaborate(interface: &PackageInterface) -> Self {
        let index = DefinitionIndex::from_interface(interface);
        Self::elaborate_with_index(interface, &index)
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
                const_generics: BTreeMap::new(),
                diagnostics: vec![],
            };
            let header = elaborator.definition(definition);
            result.definitions.insert(definition.key, header);
            result.diagnostics.extend(elaborator.diagnostics);
        }
        result.normalize_aliases();
        result.validate_associated_type_definitions();
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
            merged.diagnostics.extend(part.diagnostics);
        }
        merged.normalize_aliases();
        merged.validate_associated_type_definitions();
        merged.validate_implementation_supertraits();
        merged
            .diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        merged
    }

    fn validate_associated_type_definitions(&mut self) {
        let mut diagnostics = Vec::new();
        for implementation in self.definitions.values().filter_map(|header| match header {
            ElaboratedHeader::Implementation(implementation) if !implementation.negative => {
                Some(implementation)
            }
            _ => None,
        }) {
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
            for name in trait_header.associated_types.keys() {
                if !implementation.associated_types.contains_key(name)
                    && !implementation.associated_effect_rows.contains_key(name)
                {
                    diagnostics.push(SignatureDiagnostic {
                        code: "G4116",
                        message: format!("implementation omits associated type `{name}`"),
                    });
                }
            }
            for (name, method) in &implementation.methods {
                match trait_header.methods.get(name) {
                    Some(expected) if expected.generics == method.generics => {
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
                            "implementation method `{name}` has {} generics, but the trait requires {}",
                            method.generics, expected.generics
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
        let mut solver = TraitSolver::new(self);
        let mut diagnostics = Vec::new();
        for implementation in implementations {
            let Some(ElaboratedHeader::Trait(trait_header)) =
                self.definitions.get(&implementation.relation.definition)
            else {
                continue;
            };
            for supertrait in &trait_header.supertraits {
                let relation =
                    substitute_trait_reference(supertrait, &implementation.relation.arguments);
                let goal = TraitGoal {
                    relation: relation.clone(),
                    subject: implementation.self_ty.clone(),
                };
                match solver.solve(goal) {
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

    /// Instantiate a named struct layout at a particular nominal application.
    /// This is the sole bridge from interface-owned generic fields into
    /// body-local inference; callers cannot manufacture a layout from source
    /// spelling or rely on declaration order outside this semantic product.
    pub fn instantiate_struct_fields(
        &self,
        definition: DefKey,
        arguments: &[Type],
    ) -> Option<Vec<NominalField>> {
        let ElaboratedHeader::Nominal { generics, layout } = self.definitions.get(&definition)?
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
                })
                .collect(),
        )
    }

    /// Instantiate a callable signature for one body-local invocation. The
    /// interface-owned generic binders never escape into a caller: every
    /// reference gets a caller-owned inference variable which Typed Core
    /// freezes before MIR can observe it.
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
                        substitute_trait_reference(relation, arguments),
                    )
                })
                .collect(),
        })
    }

    /// Instantiate a canonical protocol operation at one concrete protocol
    /// identity and one operation-generic application. Declaration binders
    /// occupy the leading substitution slots; the operation's own binders
    /// follow them, so runtime effect identity stays nominally tied only to
    /// the protocol arguments.
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
    pub fn instantiate_enum_variant(
        &self,
        definition: DefKey,
        arguments: &[Type],
        name: &str,
    ) -> Option<(u32, Vec<Type>)> {
        let ElaboratedHeader::Nominal { generics, layout } = self.definitions.get(&definition)?
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

    pub fn instantiate_enum_record_variant(
        &self,
        definition: DefKey,
        arguments: &[Type],
        name: &str,
    ) -> Option<(u32, Vec<NominalField>)> {
        let ElaboratedHeader::Nominal { generics, layout } = self.definitions.get(&definition)?
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
                })
                .collect(),
        ))
    }

    /// Instantiate the payload field types for an already-resolved enum
    /// variant. Pattern decision lowering carries declaration indices rather
    /// than source names, so this is its layout bridge. Both tuple and named
    /// payloads deliberately become positional here: field-name authority was
    /// checked during pattern elaboration and is no longer a runtime concern.
    pub fn instantiate_enum_fields(
        &self,
        definition: DefKey,
        arguments: &[Type],
        index: u32,
    ) -> Option<Vec<NominalField>> {
        let ElaboratedHeader::Nominal { generics, layout } = self.definitions.get(&definition)?
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
                })
                .collect(),
            ElaboratedEnumVariantPayload::Struct(fields) => fields
                .iter()
                .map(|field| NominalField {
                    name: field.name.clone(),
                    ty: substitute_alias_generics(field.ty.clone(), arguments),
                })
                .collect(),
        };
        Some(fields)
    }

    fn normalize_aliases(&mut self) {
        let aliases = self.definitions.clone();
        let mut diagnostics = vec![];
        for header in self.definitions.values_mut() {
            match header {
                ElaboratedHeader::Callable(signature) => {
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
                ElaboratedHeader::Constant(Some(ty)) => {
                    *ty = normalize_alias_type(ty.clone(), &aliases, &mut vec![], &mut diagnostics);
                }
                ElaboratedHeader::Nominal { layout, .. } => {
                    normalize_nominal_layout(layout, &aliases, &mut diagnostics);
                }
                ElaboratedHeader::Trait(trait_header) => {
                    for reference in &mut trait_header.supertraits {
                        normalize_trait_reference(reference, &aliases, &mut diagnostics);
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
                ElaboratedHeader::Constant(None) | ElaboratedHeader::Opaque => {}
            }
        }
        self.diagnostics.extend(diagnostics);
        self.diagnostics
            .sort_by(|left, right| (left.code, &left.message).cmp(&(right.code, &right.message)));
        self.diagnostics
            .dedup_by(|left, right| left.code == right.code && left.message == right.message);
    }
}

/// Normalize the whole observable callable contract, including every nested
/// bound and effect argument. Trait and implementation methods live in frozen
/// interfaces just like top-level callables, so aliases cannot be allowed to
/// survive in only these declarations.
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
    arguments
        .extend((0..method.generics).map(|offset| Type::Generic(implementation.generics + offset)));
    CallableSignature {
        generics: method.generics,
        generic_kinds: method.generic_kinds.clone(),
        parameters: method
            .parameters
            .iter()
            .cloned()
            .map(|parameter| {
                rebase_method_lifetimes(
                    substitute_alias_generics(parameter, &arguments),
                    trait_generic_count,
                    implementation_generic_count,
                )
            })
            .collect(),
        result: rebase_method_lifetimes(
            substitute_alias_generics(method.result.clone(), &arguments),
            trait_generic_count,
            implementation_generic_count,
        ),
        effects: rebase_method_lifetime_effect_row(
            substitute_effect_row(method.effects.clone(), &arguments),
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
                        substitute_alias_generics(subject.clone(), &arguments),
                        trait_generic_count,
                        implementation_generic_count,
                    ),
                    rebase_method_lifetime_trait_reference(
                        substitute_trait_reference(relation, &arguments),
                        trait_generic_count,
                        implementation_generic_count,
                    ),
                )
            })
            .collect(),
    }
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
                    rebase_method_lifetimes(
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
                    rebase_method_lifetimes(
                        value,
                        trait_generic_count,
                        implementation_generic_count,
                    )
                })
                .collect(),
            name,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| {
                    rebase_method_lifetimes(
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
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
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
                rebase_method_lifetimes(argument, trait_generic_count, implementation_generic_count)
            })
            .collect(),
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
                        rebase_method_lifetimes(
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
                        rebase_method_lifetimes(
                            argument,
                            trait_generic_count,
                            implementation_generic_count,
                        )
                    })
                    .collect(),
                name: projection.name,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|argument| {
                        rebase_method_lifetimes(
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
        .map(|ty| normalize_alias_type(ty, definitions, &mut vec![], diagnostics))
        .collect();
}

fn substitute_trait_reference(
    relation: &ElaboratedTraitReference,
    arguments: &[Type],
) -> ElaboratedTraitReference {
    ElaboratedTraitReference {
        definition: relation.definition,
        arguments: relation
            .arguments
            .iter()
            .cloned()
            .map(|argument| substitute_alias_generics(argument, arguments))
            .collect(),
    }
}

fn normalize_effect_row(
    value: EffectRow,
    definitions: &BTreeMap<DefKey, ElaboratedHeader>,
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
                        normalize_alias_type(argument, definitions, &mut vec![], diagnostics)
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
                    &mut vec![],
                    diagnostics,
                )),
                trait_definition: projection.trait_definition,
                trait_arguments: projection
                    .trait_arguments
                    .into_iter()
                    .map(|argument| {
                        normalize_alias_type(argument, definitions, &mut vec![], diagnostics)
                    })
                    .collect(),
                name: projection.name,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|argument| {
                        normalize_alias_type(argument, definitions, &mut vec![], diagnostics)
                    })
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}

struct Elaborator<'a> {
    index: &'a DefinitionIndex,
    module: &'a ModuleKey,
    generics: BTreeMap<String, u32>,
    effect_row_generics: BTreeMap<String, u32>,
    lifetime_generics: BTreeMap<String, u32>,
    const_generics: BTreeMap<String, (u32, ConstKind)>,
    diagnostics: Vec<SignatureDiagnostic>,
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
                self.require_type_generics(generics, "type aliases");
                self.bind_generics(generics);
                ElaboratedHeader::Alias {
                    generics: generics.len() as u32,
                    target: self.ty(target),
                }
            }
            ParsedHeader::Constant { ty } => {
                ElaboratedHeader::Constant(ty.as_ref().map(|value| self.ty(value)))
            }
            ParsedHeader::Nominal { generics, layout } => {
                self.require_type_generics(generics, "nominal declarations");
                self.bind_generics(generics);
                ElaboratedHeader::Nominal {
                    generics: generics.len() as u32,
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
            where_bounds: header
                .where_bounds
                .iter()
                .map(|bound| (self.ty(&bound.subject), self.trait_ref(&bound.relation)))
                .collect(),
        }
    }
    fn trait_header(&mut self, header: &TraitHeader) -> ElaboratedTrait {
        self.require_type_generics(&header.generics, "trait declarations");
        self.bind_generics(&header.generics);
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
                    where_bounds: method
                        .signature
                        .where_bounds
                        .iter()
                        .map(|bound| (self.ty(&bound.subject), self.trait_ref(&bound.relation)))
                        .collect(),
                };
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                (method.name.clone(), signature)
            })
            .collect();
        ElaboratedTrait {
            generics: header.generics.len() as u32,
            supertraits: header
                .supertraits
                .iter()
                .map(|reference| self.trait_ref(reference))
                .collect(),
            associated_types: header
                .associated_types
                .iter()
                .map(|item| {
                    self.require_type_generics(&item.generics, "associated type declarations");
                    (
                        item.name.clone(),
                        ElaboratedAssociatedType {
                            generics: item.generics.len() as u32,
                            generic_kinds: item.generics.kinds(),
                            effect_row: item.effect_row,
                        },
                    )
                })
                .collect(),
            methods,
        }
    }
    fn implementation(&mut self, header: &ImplementationHeader) -> ElaboratedImplementation {
        self.require_type_generics(&header.generics, "implementation declarations");
        self.bind_generics(&header.generics);
        let relation = self.trait_ref(&header.relation);
        let self_ty = self.ty(&header.self_ty);
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
                self.require_type_generics(&item.generics, "associated type definitions");
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
                self.require_type_generics(&item.generics, "associated effect-row definitions");
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
                    where_bounds: method
                        .signature
                        .where_bounds
                        .iter()
                        .map(|bound| (self.ty(&bound.subject), self.trait_ref(&bound.relation)))
                        .collect(),
                };
                self.generics = outer_generics;
                self.effect_row_generics = outer_effect_row_generics;
                self.lifetime_generics = outer_lifetime_generics;
                self.const_generics = outer_const_generics;
                (method.name.clone(), signature)
            })
            .collect();
        ElaboratedImplementation {
            generics: header.generics.len() as u32,
            negative: header.negative,
            relation,
            self_ty,
            where_bounds,
            associated_types,
            associated_effect_rows,
            methods,
        }
    }
    fn effect_header(&mut self, header: &EffectHeader) -> ElaboratedEffect {
        self.require_type_generics(&header.generics, "effect declarations");
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
            operations,
        }
    }
    fn trait_ref(&mut self, value: &TraitRefHeader) -> ElaboratedTraitReference {
        self.trait_ref_parts(&value.path, &value.arguments)
    }
    fn trait_ref_parts(
        &mut self,
        path: &[String],
        source_arguments: &[HeaderType],
    ) -> ElaboratedTraitReference {
        let arguments = source_arguments
            .iter()
            .map(|argument| self.ty(argument))
            .collect::<Vec<_>>();
        match self
            .index
            .resolve_path(DefinitionNamespace::Trait, self.module, path)
        {
            ResolutionState::Resolved(definition) => {
                let expected = self.index.trait_generic_arity(definition).unwrap_or(0) as usize;
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
                self.error("G3309", format!("ambiguous trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
            ResolutionState::Inaccessible(_) => {
                self.error("G3310", format!("private trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
            _ => {
                self.error("G3310", format!("unresolved trait `{}`", path.join("::")));
                ElaboratedTraitReference {
                    definition: DefKey(crate::Digest::of_bytes(b"grandiose-stage0-error-trait")),
                    arguments,
                }
            }
        }
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
                    HeaderType::Path(path) => (
                        path,
                        arguments
                            .iter()
                            .map(|value| match value {
                                HeaderGenericArgument::Type(value) => self.ty(value),
                                HeaderGenericArgument::U32(_) => {
                                    self.error(
                                        "G3318",
                                        "effect arguments must be types, not structural constants"
                                            .into(),
                                    );
                                    Type::Error
                                }
                            })
                            .collect(),
                    ),
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
                    projections.push(EffectRowProjection {
                        subject: Box::new(subject),
                        trait_definition: relation.definition,
                        trait_arguments: relation.arguments,
                        name: name.clone(),
                        item_arguments: item_arguments
                            .iter()
                            .map(|argument| self.ty(argument))
                            .collect(),
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
                            arguments,
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
    fn require_type_generics(&mut self, parameters: &GenericParameters, context: &str) {
        for name in parameters
            .iter()
            .filter(|name| parameters.is_effect_row(name))
        {
            self.error(
                "G3314",
                format!("effect-row binder `{name}` is only valid on a callable, not {context}"),
            );
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
            Some(name) => match self.lifetime_generics.get(name) {
                Some(index) => Lifetime::Generic(*index),
                None => {
                    self.error("G3315", format!("unbound lifetime `{name}`"));
                    Lifetime::Elided
                }
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
            HeaderType::Callable { parameters, result } => Type::Callable {
                parameters: parameters.iter().map(|value| self.ty(value)).collect(),
                result: Box::new(self.ty(result)),
                effects: EffectRow::empty(),
                invocation: Quantity::ONCE,
            },
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
                Type::Projection {
                    subject: Box::new(subject),
                    trait_definition: relation.definition,
                    trait_arguments: relation.arguments,
                    name: name.clone(),
                    item_arguments: item_arguments
                        .iter()
                        .map(|argument| self.ty(argument))
                        .collect(),
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
                        arguments: self.elaborate_generic_arguments(name, &arguments, kinds),
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
    fn elaborate_generic_arguments(
        &mut self,
        name: &str,
        arguments: &[HeaderGenericArgument],
        kinds: &[GenericKind],
    ) -> Vec<Type> {
        arguments
            .iter()
            .zip(kinds)
            .map(|(argument, kind)| match (argument, kind) {
                (HeaderGenericArgument::Type(value), GenericKind::Type) => self.ty(value),
                (HeaderGenericArgument::U32(value), GenericKind::Const(ConstKind::U32)) => {
                    Type::ConstU32(*value)
                }
                (HeaderGenericArgument::Type(HeaderType::Path(path)), GenericKind::Const(kind))
                    if path.len() == 1 =>
                {
                    let const_name = &path[0];
                    match self.const_generics.get(const_name) {
                        Some((index, found)) if found == kind => Type::ConstGeneric {
                            index: *index,
                            kind: *kind,
                        },
                        Some((_, found)) => {
                            self.error(
                                "G3318",
                                format!(
                                    "const generic `{const_name}` of kind `{}` cannot fill `{}` slot of `{name}`",
                                    const_kind_name(*found),
                                    const_kind_name(*kind),
                                ),
                            );
                            Type::Error
                        }
                        None => {
                            self.error(
                                "G3318",
                                format!(
                                    "generic argument for `{name}` must be a structural `{}` constant",
                                    const_kind_name(*kind),
                                ),
                            );
                            Type::Error
                        }
                    }
                }
                (HeaderGenericArgument::U32(_), GenericKind::Type) => {
                    self.error(
                        "G3318",
                        format!("type slot of `{name}` cannot receive a structural constant"),
                    );
                    Type::Error
                }
                (_, GenericKind::Const(kind)) => {
                    self.error(
                        "G3318",
                        format!(
                            "generic argument for `{name}` must be a structural `{}` constant",
                            const_kind_name(*kind),
                        ),
                    );
                    Type::Error
                }
                (_, GenericKind::EffectRow) | (_, GenericKind::Lifetime) => {
                    self.error(
                        "G3318",
                        format!("generic argument for `{name}` has an unsupported non-type kind"),
                    );
                    Type::Error
                }
            })
            .collect()
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
                .map(|argument| normalize_alias_type(argument, definitions, stack, diagnostics))
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
            let substituted = substitute_alias_generics(target.clone(), &arguments);
            let normalized = normalize_alias_type(substituted, definitions, stack, diagnostics);
            stack.pop();
            normalized
        }
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
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
                .map(|argument| normalize_alias_type(argument, definitions, stack, diagnostics))
                .collect(),
            name,
            item_arguments: item_arguments
                .into_iter()
                .map(|argument| normalize_alias_type(argument, definitions, stack, diagnostics))
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
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
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
            effects,
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

fn substitute_alias_generics(value: Type, arguments: &[Type]) -> Type {
    match value {
        Type::Generic(index) => arguments
            .get(index as usize)
            .cloned()
            .unwrap_or(Type::Error),
        Type::ConstGeneric { index, .. } => arguments
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
                .map(|value| substitute_alias_generics(value, arguments))
                .collect(),
        },
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } => Type::Projection {
            subject: Box::new(substitute_alias_generics(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_alias_generics(value, arguments))
                .collect(),
            name,
            item_arguments: item_arguments
                .into_iter()
                .map(|value| substitute_alias_generics(value, arguments))
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
            parameters,
            result,
            effects,
            invocation,
        } => Type::Callable {
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

/// Instantiate every type nested in an effect row. Effect arguments are part
/// of a callable's observable protocol, so leaving declaration-owned generic
/// slots here would make `f<T> / State<T>` appear to perform `State<Generic(0)>`
/// at every call site.
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
                    .map(|argument| substitute_alias_generics(argument, arguments))
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
                    .map(|value| substitute_alias_generics(value, arguments))
                    .collect(),
                name: projection.name,
                item_arguments: projection
                    .item_arguments
                    .into_iter()
                    .map(|value| substitute_alias_generics(value, arguments))
                    .collect(),
            })
            .collect(),
        tail: value.tail,
    }
    .canonicalized()
}
