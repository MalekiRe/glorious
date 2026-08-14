//! Body-local structural pattern elaboration.
//!
//! This is the shared front half of the G1 pattern compiler.  It deliberately
//! produces no compiler-known control flow: later `is` and handler lowering
//! consume the same typed decision tree and choose their own Test/Bindings or
//! dispatch representation.

use crate::{
    BodySyntax, DefKey, DefinitionIndex, DefinitionNamespace, ElaboratedInterface, ModuleKey,
    PatternId, PatternKind, ResolutionState, ScalarType, Span, Type,
};

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
    let mut elaborator = Elaborator {
        body,
        index,
        signatures,
        module,
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
                let literal_ty = literal_type(&literal);
                if literal_ty != subject {
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
            PatternKind::Record {
                path,
                arguments: _,
                fields,
            } => self.record(pattern.span, path, fields, subject),
            PatternKind::Enum {
                path,
                arguments: _,
                fields,
            } => self.enum_tuple(pattern.span, path, fields, subject),
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
        fields: Vec<(String, PatternId)>,
        subject: Type,
    ) -> PatternDecision {
        if let Some((variant, enum_path)) = path.split_last()
            && !enum_path.is_empty()
            && let Some((definition, arguments)) = nominal_subject(&subject)
            && self.resolve_type(enum_path) == Some(definition)
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

    fn error(&mut self, span: Span, code: &'static str, message: &'static str) {
        self.diagnostics.push(PatternDiagnostic {
            code,
            span,
            message: message.into(),
        });
        self.recovered = true;
    }
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
