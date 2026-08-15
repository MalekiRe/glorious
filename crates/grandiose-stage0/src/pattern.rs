//! Body-local structural pattern elaboration.
//!
//! This is the shared front half of the G1 pattern compiler.  It deliberately
//! produces no compiler-known control flow: later `is` and handler lowering
//! consume the same typed decision tree and choose their own Test/Bindings or
//! dispatch representation.

use crate::{
    BodySyntax, ConstKind, DefKey, DefinitionIndex, DefinitionNamespace, EffectInstance, EffectRow,
    EffectTail, ElaboratedInterface, GenericArgument, GenericKind, Lifetime, ModuleKey, Mutability,
    PatternId, PatternKind, ResolutionState, ScalarType, Span, TraitProjectionAnswer, TraitSolver,
    Type,
};

/// Callable- or implementation-body generic binders visible while checking a
/// source pattern application. Pattern syntax stays body-local, but explicit
/// nominal arguments still need the same source-slot identity as the subject.
#[derive(Clone, Debug, Default)]
pub struct PatternGenericScope {
    pub types: std::collections::BTreeMap<String, u32>,
    pub effect_rows: std::collections::BTreeMap<String, u32>,
    pub lifetimes: std::collections::BTreeMap<String, u32>,
    pub consts: std::collections::BTreeMap<String, (u32, ConstKind)>,
}

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct BinderKey(pub u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BindingMode {
    /// The projected value is structurally duplicable in the bootstrap model.
    Copy,
    /// Later refinement lowering must retain a subject-tied borrow.
    Borrow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternBinding {
    pub key: BinderKey,
    pub name: String,
    pub ty: Type,
    pub mode: BindingMode,
    pub span: Span,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PatternDecision {
    Any,
    Bind(BinderKey),
    Literal(String),
    Tuple(Vec<PatternDecision>),
    Array(Vec<PatternDecision>),
    Record {
        definition: DefKey,
        fields: Vec<(u32, PatternDecision)>,
    },
    Enum {
        definition: DefKey,
        variant: u32,
        /// Explicit indices preserve omitted named payload fields for later
        /// projection and zero-use cleanup planning.
        fields: Vec<(u32, PatternDecision)>,
    },
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternPlan {
    pub subject: Type,
    pub decision: PatternDecision,
    pub bindings: Vec<PatternBinding>,
    /// Omitted/wildcard fields are explicitly retained for the later Use and
    /// cleanup phase; they are never silently counted as an owned match.
    pub discarded: Vec<Type>,
    pub refutable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct PatternElaboration {
    pub plan: PatternPlan,
    pub diagnostics: Vec<PatternDiagnostic>,
    pub recovered: bool,
}

/// Elaborate one parser-owned pattern against a once-evaluated subject type.
/// The returned plan is body-local and intentionally contains no source names
/// as runtime identities: each binder gets a fresh `BinderKey`.
pub fn elaborate_pattern(
    body: &BodySyntax,
    pattern: PatternId,
    subject: Type,
    index: &DefinitionIndex,
    signatures: &ElaboratedInterface,
    module: &ModuleKey,
) -> PatternElaboration {
    elaborate_pattern_with_scope(
        body,
        pattern,
        subject,
        index,
        signatures,
        module,
        &PatternGenericScope::default(),
    )
}

/// Scope-aware variant used by Typed Core when a pattern sits inside a
/// generic callable or implementation body.
pub fn elaborate_pattern_with_scope(
    body: &BodySyntax,
    pattern: PatternId,
    subject: Type,
    index: &DefinitionIndex,
    signatures: &ElaboratedInterface,
    module: &ModuleKey,
    scope: &PatternGenericScope,
) -> PatternElaboration {
    let mut elaborator = Elaborator {
        body,
        index,
        signatures,
        module,
        scope,
        bindings: vec![],
        discarded: vec![],
        diagnostics: vec![],
        next_binder: 0,
        recovered: false,
    };
    let decision = elaborator.pattern(pattern, subject.clone());
    elaborator.diagnostics.sort_by(|left, right| {
        (left.span, left.code, &left.message).cmp(&(right.span, right.code, &right.message))
    });
    PatternElaboration {
        plan: PatternPlan {
            subject,
            refutable: decision_refutable(&decision),
            decision,
            bindings: elaborator.bindings,
            discarded: elaborator.discarded,
        },
        diagnostics: elaborator.diagnostics,
        recovered: elaborator.recovered,
    }
}

/// A tuple and a struct record are already determined by their typed subject;
/// they are refutable only if one of their fields is.  Enum constructors remain
/// refutable because the subject may carry another variant.  This distinction
/// is used by effect-handler coverage as well as ordinary pattern consumers.
fn decision_refutable(decision: &PatternDecision) -> bool {
    match decision {
        PatternDecision::Any | PatternDecision::Bind(_) => false,
        PatternDecision::Literal(_) | PatternDecision::Enum { .. } | PatternDecision::Error => true,
        PatternDecision::Tuple(values) => values.iter().any(decision_refutable),
        PatternDecision::Array(_) => true,
        PatternDecision::Record { fields, .. } => fields
            .iter()
            .any(|(_, decision)| decision_refutable(decision)),
    }
}

struct Elaborator<'a> {
    body: &'a BodySyntax,
    index: &'a DefinitionIndex,
    signatures: &'a ElaboratedInterface,
    module: &'a ModuleKey,
    scope: &'a PatternGenericScope,
    bindings: Vec<PatternBinding>,
    discarded: Vec<Type>,
    diagnostics: Vec<PatternDiagnostic>,
    next_binder: u32,
    recovered: bool,
}

impl Elaborator<'_> {
    fn pattern(&mut self, id: PatternId, subject: Type) -> PatternDecision {
        let pattern = self.body.pattern(id).clone();
        match pattern.kind {
            PatternKind::Wildcard => {
                self.discarded.push(subject);
                PatternDecision::Any
            }
            PatternKind::Binding(name) => {
                let key = BinderKey(self.next_binder);
                self.next_binder += 1;
                self.bindings.push(PatternBinding {
                    key,
                    name,
                    mode: binding_mode(&subject),
                    ty: subject,
                    span: pattern.span,
                });
                PatternDecision::Bind(key)
            }
            PatternKind::Literal(literal) => {
                if let Some((definition, variant)) =
                    canonical_bool_literal_pattern(&subject, self.signatures, &literal)
                {
                    return PatternDecision::Enum {
                        definition,
                        variant,
                        fields: vec![(0, PatternDecision::Any)],
                    };
                }
                let literal_ty = literal_type(&literal);
                // Pattern literals are contextual just like expression
                // literals.  A handler payload such as `Branch::select(0)`
                // receives its concrete width from the operation contract;
                // treating `0` as the legacy `i64` default rejects an exact
                // `u32` arm before the handler matrix can reason about it.
                // The decision retains the source spelling and is lowered
                // against `subject`, so no implicit runtime conversion is
                // introduced here.
                let matches_subject = literal_ty == subject
                    || (literal_is_numeric(&literal)
                        && matches!(&subject, Type::Scalar(scalar) if scalar_is_numeric(*scalar)));
                if !matches_subject {
                    self.error(
                        pattern.span,
                        "G4201",
                        "literal pattern does not match the subject type",
                    );
                    PatternDecision::Error
                } else {
                    PatternDecision::Literal(literal)
                }
            }
            PatternKind::Tuple(values) => {
                let Type::Tuple(types) = subject else {
                    self.error(
                        pattern.span,
                        "G4202",
                        "tuple pattern requires a tuple subject",
                    );
                    return PatternDecision::Error;
                };
                if values.len() != types.len() {
                    self.error(pattern.span, "G4203", "tuple pattern has the wrong arity");
                    return PatternDecision::Error;
                }
                PatternDecision::Tuple(
                    values
                        .into_iter()
                        .zip(types)
                        .map(|(pattern, ty)| self.pattern(pattern, ty))
                        .collect(),
                )
            }
            PatternKind::Array(values) => {
                let Type::Array(element) = subject else {
                    self.error(
                        pattern.span,
                        "G4215",
                        "array pattern requires an array subject",
                    );
                    return PatternDecision::Error;
                };
                PatternDecision::Array(
                    values
                        .into_iter()
                        .map(|value| self.pattern(value, (*element).clone()))
                        .collect(),
                )
            }
            PatternKind::Record {
                path,
                arguments,
                fields,
            } => self.record(pattern.span, path, arguments, fields, subject),
            PatternKind::Enum {
                path,
                arguments,
                fields,
            } => self.enum_tuple(pattern.span, path, arguments, fields, subject),
            PatternKind::Recovered => {
                self.recovered = true;
                PatternDecision::Error
            }
        }
    }

    fn record(
        &mut self,
        span: Span,
        path: Vec<String>,
        source_arguments: Vec<crate::HeaderGenericArgument>,
        fields: Vec<(String, PatternId)>,
        subject: Type,
    ) -> PatternDecision {
        if let Some((variant, enum_path)) = path.split_last()
            && !enum_path.is_empty()
            && let Some((definition, arguments)) = nominal_subject(&subject)
            && self.resolve_type(enum_path) == Some(definition)
            && self.nominal_arguments_match(span, definition, &source_arguments, &arguments)
            && let Some((variant_index, layout)) = self
                .signatures
                .instantiate_enum_record_variant_generic(definition, &arguments, variant)
                .ok()
        {
            return self.record_fields(span, definition, fields, layout, Some(variant_index));
        }
        let Some(definition) = self.resolve_type(&path) else {
            self.error(
                span,
                "G4204",
                "record pattern names an unresolved struct type",
            );
            return PatternDecision::Error;
        };
        let Some((actual, arguments)) = nominal_subject(&subject) else {
            self.error(span, "G4205", "record pattern requires a nominal subject");
            return PatternDecision::Error;
        };
        if actual != definition {
            self.error(
                span,
                "G4206",
                "record pattern type differs from its subject",
            );
            return PatternDecision::Error;
        }
        if !self.nominal_arguments_match(span, definition, &source_arguments, &arguments) {
            return PatternDecision::Error;
        }
        let Some(layout) = self
            .signatures
            .instantiate_struct_fields_generic(definition, &arguments)
            .ok()
        else {
            self.error(
                span,
                "G4207",
                "record pattern does not name a visible struct",
            );
            return PatternDecision::Error;
        };
        self.record_fields(span, definition, fields, layout, None)
    }

    fn record_fields(
        &mut self,
        span: Span,
        definition: DefKey,
        fields: Vec<(String, PatternId)>,
        layout: Vec<crate::NominalField>,
        enum_variant: Option<u32>,
    ) -> PatternDecision {
        // A record pattern is ownership deconstruction even when it omits a
        // field. Omission therefore cannot turn a private payload into an
        // externally destructurable public shell.
        if layout.iter().any(|field| {
            field
                .private_authority
                .is_some_and(|authority| authority != span.file)
        }) {
            self.error(
                span,
                "G4218",
                "record pattern deconstructs a private field outside its declaring source entry",
            );
            return PatternDecision::Error;
        }
        let mut selected = Vec::with_capacity(fields.len());
        let mut seen = std::collections::BTreeSet::new();
        for (name, pattern) in fields {
            if !seen.insert(name.clone()) {
                self.error(
                    span,
                    "G4208",
                    "record pattern selects a field more than once",
                );
                continue;
            }
            let Some((index, field)) = layout
                .iter()
                .enumerate()
                .find(|(_, field)| field.name == name)
            else {
                self.error(span, "G4209", "record pattern names an unknown field");
                continue;
            };
            selected.push((index as u32, self.pattern(pattern, field.ty.clone())));
        }
        for field in &layout {
            if !seen.contains(&field.name) {
                self.discarded.push(field.ty.clone());
            }
        }
        match enum_variant {
            Some(variant) => PatternDecision::Enum {
                definition,
                variant,
                fields: selected,
            },
            None => PatternDecision::Record {
                definition,
                fields: selected,
            },
        }
    }

    fn enum_tuple(
        &mut self,
        span: Span,
        path: Vec<String>,
        source_arguments: Vec<crate::HeaderGenericArgument>,
        fields: Vec<PatternId>,
        subject: Type,
    ) -> PatternDecision {
        let Some((variant, enum_path)) = path.split_last() else {
            self.error(span, "G4210", "enum pattern has no variant name");
            return PatternDecision::Error;
        };
        let Some((definition, arguments)) = nominal_subject(&subject) else {
            self.error(span, "G4211", "enum pattern requires a nominal subject");
            return PatternDecision::Error;
        };
        if self.resolve_type(enum_path) != Some(definition) {
            self.error(span, "G4212", "enum pattern type differs from its subject");
            return PatternDecision::Error;
        }
        if !self.nominal_arguments_match(span, definition, &source_arguments, &arguments) {
            return PatternDecision::Error;
        }
        let Some((variant_index, types)) = self
            .signatures
            .instantiate_enum_variant_generic(definition, &arguments, variant)
            .ok()
        else {
            self.error(span, "G4213", "enum variant has no matching tuple payload");
            return PatternDecision::Error;
        };
        if fields.len() != types.len() {
            self.error(span, "G4214", "enum pattern has the wrong payload arity");
            return PatternDecision::Error;
        }
        PatternDecision::Enum {
            definition,
            variant: variant_index,
            fields: fields
                .into_iter()
                .zip(types)
                .enumerate()
                .map(|(index, (pattern, ty))| (index as u32, self.pattern(pattern, ty)))
                .collect(),
        }
    }

    fn resolve_type(&self, path: &[String]) -> Option<DefKey> {
        match self
            .index
            .resolve_path(DefinitionNamespace::Type, self.module, path)
        {
            ResolutionState::Resolved(definition) => Some(definition),
            _ => None,
        }
    }

    fn nominal_arguments_match(
        &mut self,
        span: Span,
        definition: DefKey,
        source: &[crate::HeaderGenericArgument],
        actual: &[GenericArgument],
    ) -> bool {
        if source.is_empty() {
            return true;
        }
        let kinds = self.index.type_generic_kinds(definition).unwrap_or(&[]);
        if source.len() != kinds.len() || actual.len() != kinds.len() {
            self.error(span, "G4215", "nominal pattern has the wrong generic arity");
            return false;
        }
        let mut supplied = Vec::with_capacity(source.len());
        for (argument, kind) in source.iter().zip(kinds) {
            let Some(argument) = self.generic_argument(span, argument, *kind) else {
                return false;
            };
            supplied.push(argument);
        }
        if supplied != actual {
            self.error(
                span,
                "G4216",
                "nominal pattern generic arguments differ from its subject",
            );
            return false;
        }
        true
    }

    fn generic_argument(
        &mut self,
        span: Span,
        argument: &crate::HeaderGenericArgument,
        kind: GenericKind,
    ) -> Option<GenericArgument> {
        match (argument, kind) {
            (crate::HeaderGenericArgument::Type(value), GenericKind::Type) => {
                self.source_type(span, value).map(GenericArgument::Type)
            }
            (crate::HeaderGenericArgument::Lifetime(value), GenericKind::Lifetime) => self
                .source_lifetime(span, value)
                .map(GenericArgument::Lifetime),
            (crate::HeaderGenericArgument::EffectRow(value), GenericKind::EffectRow) => self
                .source_effect_row(span, value)
                .map(GenericArgument::EffectRow),
            (crate::HeaderGenericArgument::U32(value), GenericKind::Const(ConstKind::U32)) => {
                Some(GenericArgument::ConstU32(*value))
            }
            (
                crate::HeaderGenericArgument::Quantity(value),
                GenericKind::Const(ConstKind::Quantity),
            ) => Some(GenericArgument::ConstQuantity(*value)),
            (
                crate::HeaderGenericArgument::Type(crate::HeaderType::Path(path)),
                GenericKind::Const(kind),
            ) if path.len() == 1 => self
                .scope
                .consts
                .get(&path[0])
                .filter(|(_, found)| *found == kind)
                .map(|(index, kind)| GenericArgument::ConstGeneric {
                    index: *index,
                    kind: *kind,
                })
                .or_else(|| {
                    self.error(
                        span,
                        "G4217",
                        "nominal pattern const argument has the wrong kind",
                    );
                    None
                }),
            _ => {
                self.error(
                    span,
                    "G4217",
                    "nominal pattern generic argument has the wrong kind",
                );
                None
            }
        }
    }

    fn source_type(&mut self, span: Span, value: &crate::HeaderType) -> Option<Type> {
        match value {
            crate::HeaderType::Path(path) => {
                if path.len() == 1 {
                    if let Some(index) = self.scope.types.get(&path[0]) {
                        return Some(Type::Generic(*index));
                    }
                    if let Some(scalar) = scalar(&path[0]) {
                        return Some(Type::Scalar(scalar));
                    }
                }
                let definition = self.resolve_type(path)?;
                if !self
                    .index
                    .type_generic_kinds(definition)
                    .unwrap_or(&[])
                    .is_empty()
                {
                    self.error(
                        span,
                        "G4217",
                        "nominal pattern type argument needs its generic arguments",
                    );
                    return None;
                }
                Some(Type::Nominal {
                    definition,
                    arguments: vec![],
                })
            }
            crate::HeaderType::Application(base, arguments) => {
                let crate::HeaderType::Path(path) = base.as_ref() else {
                    self.error(span, "G4217", "nominal pattern type application is invalid");
                    return None;
                };
                let definition = self.resolve_type(path)?;
                let kinds = self.index.type_generic_kinds(definition).unwrap_or(&[]);
                if arguments.len() != kinds.len() {
                    self.error(
                        span,
                        "G4215",
                        "nominal pattern type argument has the wrong arity",
                    );
                    return None;
                }
                let arguments = arguments
                    .iter()
                    .zip(kinds)
                    .map(|(argument, kind)| self.generic_argument(span, argument, *kind))
                    .collect::<Option<Vec<_>>>()?;
                Some(Type::Nominal {
                    definition,
                    arguments,
                })
            }
            crate::HeaderType::Tuple(values) => values
                .iter()
                .map(|value| self.source_type(span, value))
                .collect::<Option<Vec<_>>>()
                .map(Type::Tuple),
            crate::HeaderType::Reference {
                unique,
                lifetime,
                referent,
            } => Some(Type::Reference {
                mutability: if *unique {
                    Mutability::Unique
                } else {
                    Mutability::Shared
                },
                lifetime: match lifetime {
                    Some(value) => self.source_lifetime(span, value)?,
                    None => Lifetime::Elided,
                },
                referent: Box::new(self.source_type(span, referent)?),
            }),
            crate::HeaderType::Never => Some(Type::Never),
            crate::HeaderType::Callable {
                parameters,
                result,
                effects,
                ..
            } => Some(Type::Callable {
                lifetime_binders: 0,
                parameters: parameters
                    .iter()
                    .map(|value| self.source_type(span, value))
                    .collect::<Option<Vec<_>>>()?,
                result: Box::new(self.source_type(span, result)?),
                effects: self.source_effect_row(span, effects)?,
                invocation: crate::Quantity::AFFINE,
            }),
            crate::HeaderType::Projection {
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            } => self.source_projection(
                span,
                subject,
                trait_path,
                trait_arguments,
                name,
                item_arguments,
            ),
            crate::HeaderType::Recovered => {
                self.error(span, "G4217", "unsupported nominal pattern type argument");
                None
            }
        }
    }

    /// Elaborate a qualified associated type in a nominal pattern argument.
    /// Pattern applications share the declaration source-slot grammar: a
    /// `Box<<T as Trait>::Item>` pattern must retain exactly the same mixed
    /// kind trait identity as a callable signature, and concrete selections
    /// must normalize before they are compared to the subject's instantiated
    /// nominal arguments.  Keeping this here avoids a second, pattern-only
    /// interpretation of projections.
    fn source_projection(
        &mut self,
        span: Span,
        subject: &crate::HeaderType,
        trait_path: &[String],
        trait_arguments: &[crate::HeaderGenericArgument],
        name: &str,
        item_arguments: &[crate::HeaderGenericArgument],
    ) -> Option<Type> {
        let subject = self.source_type(span, subject)?;
        let trait_definition =
            match self
                .index
                .resolve_path(DefinitionNamespace::Trait, self.module, trait_path)
            {
                ResolutionState::Resolved(definition) => definition,
                ResolutionState::Ambiguous(_) => {
                    self.error(
                        span,
                        "G4146",
                        "nominal pattern associated type projection has an ambiguous trait",
                    );
                    return None;
                }
                ResolutionState::Inaccessible(_)
                | ResolutionState::Unresolved
                | ResolutionState::Recovered => {
                    self.error(
                        span,
                        "G4147",
                        "nominal pattern associated type projection has an unresolved trait",
                    );
                    return None;
                }
            };
        let trait_kinds = self
            .index
            .trait_generic_kinds(trait_definition)
            .unwrap_or(&[]);
        if trait_arguments.len() != trait_kinds.len() {
            self.error(
                span,
                "G4215",
                "nominal pattern associated type projection has the wrong trait generic arity",
            );
            return None;
        }
        let trait_arguments = trait_arguments
            .iter()
            .zip(trait_kinds)
            .map(|(argument, kind)| self.generic_argument(span, argument, *kind))
            .collect::<Option<Vec<_>>>()?;
        let Some(item_kinds) = self
            .index
            .associated_type_generic_kinds(trait_definition, name)
        else {
            self.error(
                span,
                "G4150",
                "nominal pattern projection does not select a declared associated type",
            );
            return None;
        };
        if item_arguments.len() != item_kinds.len() {
            self.error(
                span,
                "G4215",
                "nominal pattern associated type projection has the wrong item generic arity",
            );
            return None;
        }
        let item_arguments = item_arguments
            .iter()
            .zip(item_kinds)
            .map(|(argument, kind)| self.generic_argument(span, argument, *kind))
            .collect::<Option<Vec<_>>>()?;
        let projection = Type::Projection {
            subject: Box::new(subject),
            trait_definition,
            trait_arguments,
            name: name.to_owned(),
            item_generic_kinds: item_kinds.to_vec(),
            item_arguments,
        };
        match TraitSolver::new(self.signatures).normalize_type(projection) {
            Ok(value) => Some(value),
            Err(answer) => {
                let (code, message) = match *answer {
                    TraitProjectionAnswer::Refuted { .. } => (
                        "G4151",
                        "nominal pattern associated type projection is refuted by a negative implementation",
                    ),
                    TraitProjectionAnswer::NoSolution => (
                        "G4152",
                        "no implementation can normalize a nominal pattern associated type projection",
                    ),
                    TraitProjectionAnswer::Ambiguous => (
                        "G4153",
                        "nominal pattern associated type projection is ambiguous",
                    ),
                    TraitProjectionAnswer::Overflow => (
                        "G4154",
                        "nominal pattern associated type projection exceeded the trait solver limit",
                    ),
                    TraitProjectionAnswer::MissingAssociatedType { .. } => (
                        "G4155",
                        "selected implementation does not define the nominal pattern associated type",
                    ),
                    TraitProjectionAnswer::AssociatedTypeArity { .. } => (
                        "G4156",
                        "nominal pattern associated type projection has the wrong arity",
                    ),
                    TraitProjectionAnswer::RecursiveProjection => (
                        "G4157",
                        "nominal pattern associated type projection has no finite normal form",
                    ),
                    TraitProjectionAnswer::Normalized { .. } => {
                        unreachable!("normalization results are returned through Ok")
                    }
                };
                self.error(span, code, message);
                None
            }
        }
    }

    fn source_lifetime(&mut self, span: Span, value: &str) -> Option<Lifetime> {
        if value == "'static" {
            return Some(Lifetime::Static);
        }
        self.scope
            .lifetimes
            .get(value)
            .copied()
            .map(Lifetime::Generic)
            .or_else(|| {
                self.error(span, "G4217", "nominal pattern lifetime is not in scope");
                None
            })
    }

    fn source_effect_row(
        &mut self,
        span: Span,
        value: &crate::EffectRowHeader,
    ) -> Option<EffectRow> {
        let mut row = EffectRow::empty();
        for effect in &value.effects {
            let (path, arguments) = match effect {
                crate::HeaderType::Path(path) => (path.as_slice(), vec![]),
                crate::HeaderType::Application(base, arguments) => match base.as_ref() {
                    crate::HeaderType::Path(path) => (path.as_slice(), arguments.clone()),
                    _ => {
                        self.error(
                            span,
                            "G4217",
                            "nominal pattern effect application is invalid",
                        );
                        return None;
                    }
                },
                _ => {
                    self.error(span, "G4217", "nominal pattern effect row is invalid");
                    return None;
                }
            };
            let definition =
                match self
                    .index
                    .resolve_path(DefinitionNamespace::Effect, self.module, path)
                {
                    ResolutionState::Resolved(definition) => definition,
                    _ => {
                        self.error(span, "G4217", "nominal pattern effect is unresolved");
                        return None;
                    }
                };
            let kinds = self.index.effect_generic_kinds(definition).unwrap_or(&[]);
            if arguments.len() != kinds.len() {
                self.error(
                    span,
                    "G4215",
                    "nominal pattern effect has the wrong generic arity",
                );
                return None;
            }
            let arguments = arguments
                .iter()
                .zip(kinds)
                .map(|(argument, kind)| self.generic_argument(span, argument, *kind))
                .collect::<Option<Vec<_>>>()?;
            row.effects.insert(EffectInstance {
                definition,
                arguments,
            });
        }
        if let Some(tail) = &value.tail {
            let Some(index) = self.scope.effect_rows.get(tail).copied() else {
                self.error(
                    span,
                    "G4217",
                    "nominal pattern effect-row tail is not in scope",
                );
                return None;
            };
            row.tail = Some(EffectTail::Generic(index));
        }
        Some(row.canonicalized())
    }

    fn error(&mut self, span: Span, code: &'static str, message: &'static str) {
        self.diagnostics.push(PatternDiagnostic {
            code,
            span,
            message: message.into(),
        });
        self.recovered = true;
    }
}

/// The canonical standard library represents `Bool` as `Result<(), ()>`.
/// Accept its ordinary `true` and `false` source patterns by recognizing only
/// the exact one-unit `Ok` and `Err` constructors of the normalized subject.
fn canonical_bool_literal_pattern(
    subject: &Type,
    signatures: &ElaboratedInterface,
    literal: &str,
) -> Option<(DefKey, u32)> {
    let Type::Nominal {
        definition,
        arguments,
    } = subject
    else {
        return None;
    };
    let name = match literal {
        "true" => "Ok",
        "false" => "Err",
        _ => return None,
    };
    let (variant, fields) = signatures
        .instantiate_enum_variant_generic(*definition, arguments, name)
        .ok()?;
    (fields == vec![Type::Unit]).then_some((*definition, variant))
}

fn nominal_subject(subject: &Type) -> Option<(DefKey, Vec<crate::GenericArgument>)> {
    match subject {
        Type::Nominal {
            definition,
            arguments,
        } => Some((*definition, arguments.clone())),
        _ => None,
    }
}

fn binding_mode(ty: &Type) -> BindingMode {
    match ty {
        Type::Unit | Type::Scalar(_) | Type::Reference { .. } | Type::Callable { .. } => {
            BindingMode::Copy
        }
        _ => BindingMode::Borrow,
    }
}

fn literal_type(value: &str) -> Type {
    if matches!(value, "true" | "false") {
        Type::Scalar(ScalarType::Bool)
    } else if value.starts_with('"') {
        Type::Scalar(ScalarType::Text)
    } else if value.starts_with('\'') {
        Type::Scalar(ScalarType::Char)
    } else if value.contains('.') || value.contains('e') || value.contains('E') {
        Type::Scalar(ScalarType::F64)
    } else {
        Type::Scalar(ScalarType::I64)
    }
}

fn literal_is_numeric(value: &str) -> bool {
    !matches!(value, "true" | "false") && !value.starts_with('"') && !value.starts_with('\'')
}

fn scalar_is_numeric(scalar: ScalarType) -> bool {
    matches!(
        scalar,
        ScalarType::U8
            | ScalarType::U16
            | ScalarType::U32
            | ScalarType::U64
            | ScalarType::U128
            | ScalarType::Usize
            | ScalarType::I8
            | ScalarType::I16
            | ScalarType::I32
            | ScalarType::I64
            | ScalarType::I128
            | ScalarType::Isize
            | ScalarType::F32
            | ScalarType::F64
    )
}

fn scalar(name: &str) -> Option<ScalarType> {
    use ScalarType::*;
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
