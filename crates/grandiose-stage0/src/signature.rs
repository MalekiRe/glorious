//! Header elaboration into canonical, body-independent semantic signatures.

use std::collections::BTreeMap;

use crate::{
    header::{
        CallableHeader, EffectHeader, EffectRowHeader, EnumVariantPayloadHeader, HeaderType,
        ImplementationHeader, NominalLayoutHeader, ParsedHeader, TraitHeader, TraitRefHeader,
    },
    identity::{DefKey, ModuleKey},
    interface::{Definition, DefinitionNamespace, PackageInterface},
    quantity::Quantity,
    resolution::{DefinitionIndex, ResolutionState},
    types::{EffectInstance, EffectRow, Mutability, Type},
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallableSignature {
    pub generics: u32,
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
    /// first projection surface is zero-arity, but preserving the declared
    /// arity here keeps the frozen interface ready to reject unsupported GAT
    /// applications rather than silently treating them as ordinary types.
    pub associated_types: BTreeMap<String, ElaboratedAssociatedType>,
    pub methods: BTreeMap<String, CallableSignature>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedType {
    pub generics: u32,
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
    pub methods: BTreeMap<String, CallableSignature>,
}

/// A trait implementation's associated type body. Item generics use slots
/// after the implementation's generic slots, so projection normalization can
/// substitute both environments without conflating them.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ElaboratedAssociatedTypeDefinition {
    pub generics: u32,
    pub value: Type,
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
                diagnostics: vec![],
            };
            let header = elaborator.definition(definition);
            result.definitions.insert(definition.key, header);
            result.diagnostics.extend(elaborator.diagnostics);
        }
        result.normalize_aliases();
        result.validate_associated_type_definitions();
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
                    Some(expected) if expected.generics == item.generics => {}
                    Some(expected) => diagnostics.push(SignatureDiagnostic {
                        code: "G4114",
                        message: format!(
                            "associated type `{name}` has arity {}, but the trait requires {}",
                            item.generics, expected.generics
                        ),
                    }),
                    None => diagnostics.push(SignatureDiagnostic {
                        code: "G4115",
                        message: format!("implementation defines unknown associated type `{name}`"),
                    }),
                }
            }
            for name in trait_header.associated_types.keys() {
                if !implementation.associated_types.contains_key(name) {
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
    let mut arguments = implementation.relation.arguments.clone();
    arguments
        .extend((0..method.generics).map(|offset| Type::Generic(implementation.generics + offset)));
    CallableSignature {
        generics: method.generics,
        parameters: method
            .parameters
            .iter()
            .cloned()
            .map(|parameter| substitute_alias_generics(parameter, &arguments))
            .collect(),
        result: substitute_alias_generics(method.result.clone(), &arguments),
        effects: substitute_effect_row(method.effects.clone(), &arguments),
        invocation: method.invocation,
        where_bounds: method
            .where_bounds
            .iter()
            .map(|(subject, relation)| {
                (
                    substitute_alias_generics(subject.clone(), &arguments),
                    substitute_trait_reference(relation, &arguments),
                )
            })
            .collect(),
    }
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
        tail: value.tail,
    }
}

struct Elaborator<'a> {
    index: &'a DefinitionIndex,
    module: &'a ModuleKey,
    generics: BTreeMap<String, u32>,
    diagnostics: Vec<SignatureDiagnostic>,
}
impl Elaborator<'_> {
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
            ParsedHeader::Nominal { generics, layout } => {
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
        self.bind_generics(&header.generics);
        let methods = header
            .methods
            .iter()
            .map(|method| {
                let outer_generics = self.generics.clone();
                let base = outer_generics.len() as u32;
                for (offset, name) in method.signature.generics.iter().enumerate() {
                    if self
                        .generics
                        .insert(name.clone(), base + offset as u32)
                        .is_some()
                    {
                        self.diagnostics.push(SignatureDiagnostic {
                            code: "G4117",
                            message: "trait method generic shadows an outer generic".into(),
                        });
                    }
                }
                let signature = CallableSignature {
                    generics: method.signature.generics.len() as u32,
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
                    (
                        item.name.clone(),
                        ElaboratedAssociatedType {
                            generics: item.generics.len() as u32,
                            effect_row: item.effect_row,
                        },
                    )
                })
                .collect(),
            methods,
        }
    }
    fn implementation(&mut self, header: &ImplementationHeader) -> ElaboratedImplementation {
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
            .map(|item| {
                let outer_generics = self.generics.clone();
                let base = outer_generics.len() as u32;
                for (offset, name) in item.generics.iter().enumerate() {
                    if self
                        .generics
                        .insert(name.clone(), base + offset as u32)
                        .is_some()
                    {
                        self.diagnostics.push(SignatureDiagnostic {
                            code: "G4113",
                            message: "associated type generic shadows an outer generic".into(),
                        });
                    }
                }
                let value = self.ty(&item.value);
                self.generics = outer_generics;
                (
                    item.name.clone(),
                    ElaboratedAssociatedTypeDefinition {
                        generics: item.generics.len() as u32,
                        value,
                    },
                )
            })
            .collect();
        let methods = header
            .methods
            .iter()
            .map(|method| {
                let outer_generics = self.generics.clone();
                let base = outer_generics.len() as u32;
                for (offset, name) in method.signature.generics.iter().enumerate() {
                    if self
                        .generics
                        .insert(name.clone(), base + offset as u32)
                        .is_some()
                    {
                        self.diagnostics.push(SignatureDiagnostic {
                            code: "G4118",
                            message: "implementation method generic shadows an outer generic"
                                .into(),
                        });
                    }
                }
                let signature = CallableSignature {
                    generics: method.signature.generics.len() as u32,
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
            methods,
        }
    }
    fn effect_header(&mut self, header: &EffectHeader) -> ElaboratedEffect {
        self.bind_generics(&header.generics);
        let declaration_generics = self.generics.clone();
        let operations = header
            .operations
            .iter()
            .map(|operation| {
                self.generics = declaration_generics.clone();
                let base = self.generics.len() as u32;
                for (offset, name) in operation.generics.iter().enumerate() {
                    if self
                        .generics
                        .insert(name.clone(), base + offset as u32)
                        .is_some()
                    {
                        self.error("G3301", format!("duplicate generic parameter `{name}`"));
                    }
                }
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
        if let Some(tail) = &value.tail {
            self.error(
                "G3311",
                format!("effect-row tail `{tail}` requires a declared `EffectRow` generic binder"),
            );
        }
        let mut effects = vec![];
        for effect in &value.effects {
            let (path, arguments) = match effect {
                HeaderType::Path(path) => (path, vec![]),
                HeaderType::Application(base, arguments) => match base.as_ref() {
                    HeaderType::Path(path) => {
                        (path, arguments.iter().map(|value| self.ty(value)).collect())
                    }
                    _ => {
                        self.error("G3312", "effect row member is not a nominal path".into());
                        continue;
                    }
                },
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
        EffectRow::closed_instances(effects)
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
    fn bind_generics(&mut self, names: &[String]) {
        self.generics.clear();
        for (index, name) in names.iter().enumerate() {
            if self.generics.insert(name.clone(), index as u32).is_some() {
                self.error("G3301", format!("duplicate generic parameter `{name}`"));
            }
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
            HeaderType::Reference { unique, referent } => Type::Reference {
                mutability: if *unique {
                    Mutability::Unique
                } else {
                    Mutability::Shared
                },
                referent: Box::new(self.ty(referent)),
            },
            HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
            } => {
                let subject = self.ty(subject);
                let relation = self.trait_ref_parts(trait_path, trait_arguments);
                Type::Projection {
                    subject: Box::new(subject),
                    trait_definition: relation.definition,
                    trait_arguments: relation.arguments,
                    name: name.clone(),
                }
            }
            HeaderType::Path(path) => self.path(path, vec![]),
            HeaderType::Application(base, arguments) => {
                let arguments = arguments.iter().map(|argument| self.ty(argument)).collect();
                match base.as_ref() {
                    HeaderType::Path(path) => self.path(path, arguments),
                    _ => {
                        self.error(
                            "G3302",
                            "type application base is not a nominal path".into(),
                        );
                        Type::Error
                    }
                }
            }
        }
    }
    fn path(&mut self, path: &[String], arguments: Vec<Type>) -> Type {
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
                    [element] => Type::Array(Box::new(element.clone())),
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
                    Type::Nominal {
                        definition,
                        arguments,
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
            referent,
        } => Type::Reference {
            mutability,
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
        } => Type::Projection {
            subject: Box::new(substitute_alias_generics(*subject, arguments)),
            trait_definition,
            trait_arguments: trait_arguments
                .into_iter()
                .map(|value| substitute_alias_generics(value, arguments))
                .collect(),
            name,
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
            referent,
        } => Type::Reference {
            mutability,
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
        tail: value.tail,
    }
}
