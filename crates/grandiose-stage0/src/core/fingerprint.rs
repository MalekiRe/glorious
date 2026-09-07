//! Canonical semantic fingerprinting of frozen Typed Core.

use super::{
    CaptureEnvironment, CoreId, CoreKind, CorePattern, CorePlace, RefinementEnvironment, TypedBody,
};
use crate::{
    identity::Digest,
    types::{
        EffectInstance, EffectRow, GenericArgument, Type, canonical_generic_arguments_encoding,
        canonical_type_encoding,
    },
};

pub(super) fn semantic_fingerprint(body: &TypedBody) -> Digest {
    let mut encoder = CoreFingerprintEncoder {
        body,
        numbers: std::collections::BTreeMap::new(),
        bytes: Vec::new(),
    };
    encoder.bytes(b"grandiose-stage0-typed-core-v1");
    if body.safety == crate::Safety::Unsafe {
        encoder.bytes(b"unsafe-callable-contract");
    }
    if !body.unsafe_implementations.is_empty() {
        encoder.bytes(b"unsafe-implementation-requirements");
        encoder.debug(&body.unsafe_implementations);
    }
    encoder.id(body.root);
    Digest::of_bytes(&encoder.bytes)
}

struct CoreFingerprintEncoder<'a> {
    body: &'a TypedBody,
    numbers: std::collections::BTreeMap<CoreId, u32>,
    bytes: Vec<u8>,
}

impl CoreFingerprintEncoder<'_> {
    fn bytes(&mut self, value: &[u8]) {
        self.bytes
            .extend_from_slice(&(value.len() as u64).to_le_bytes());
        self.bytes.extend_from_slice(value);
    }

    fn debug(&mut self, value: impl std::fmt::Debug) {
        self.bytes(format!("{value:?}").as_bytes());
    }

    fn ty(&mut self, value: &Type) {
        self.bytes(&canonical_type_encoding(value));
    }

    fn types(&mut self, values: &[Type]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.ty(value);
        }
    }

    fn generic_arguments(&mut self, values: &[GenericArgument]) {
        self.bytes(&canonical_generic_arguments_encoding(values));
    }

    fn effect(&mut self, value: &EffectInstance) {
        self.debug(value.definition);
        self.generic_arguments(&value.arguments);
    }

    fn effect_row(&mut self, value: &EffectRow) {
        // Effect rows are already canonical frozen identities at this
        // boundary, including delayed projections and their tail.
        self.debug(value);
    }

    fn pattern(&mut self, value: &CorePattern) {
        match value {
            CorePattern::Any => self.bytes(b"any"),
            CorePattern::Bind { name } => {
                self.bytes(b"bind");
                self.bytes(name.as_bytes());
            }
            CorePattern::Literal(value) => {
                self.bytes(b"literal");
                self.bytes(value.as_bytes());
            }
            CorePattern::Tuple(values) => {
                self.bytes(b"tuple");
                self.bytes(&(values.len() as u64).to_le_bytes());
                for value in values {
                    self.pattern(value);
                }
            }
            CorePattern::Array { element, elements } => {
                self.bytes(b"array");
                self.ty(element);
                self.bytes(&(elements.len() as u64).to_le_bytes());
                for element in elements {
                    self.pattern(element);
                }
            }
            CorePattern::Record {
                definition,
                field_types,
                field_count,
                fields,
            }
            | CorePattern::Enum {
                definition,
                field_types,
                field_count,
                fields,
                ..
            } => {
                self.bytes(if matches!(value, CorePattern::Record { .. }) {
                    b"record"
                } else {
                    b"enum"
                });
                self.debug(definition);
                if let CorePattern::Enum { variant, .. } = value {
                    self.bytes(&variant.to_le_bytes());
                }
                self.bytes(&field_count.to_le_bytes());
                self.bytes(&(field_types.len() as u64).to_le_bytes());
                for field_type in field_types {
                    self.ty(field_type);
                }
                self.bytes(&(fields.len() as u64).to_le_bytes());
                for field in fields {
                    self.bytes(&field.index.to_le_bytes());
                    self.ty(&field.ty);
                    self.pattern(&field.pattern);
                }
            }
            CorePattern::Error => self.bytes(b"error"),
        }
    }

    fn bindings(&mut self, values: &[(String, Type)]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for (name, ty) in values {
            self.bytes(name.as_bytes());
            self.ty(ty);
        }
    }

    fn refinement(&mut self, value: &RefinementEnvironment) {
        self.debug(value.brand);
        self.debug(&value.subject);
        self.bytes(&(value.bindings.len() as u64).to_le_bytes());
        for binding in &value.bindings {
            self.bytes(binding.as_bytes());
        }
        self.bindings(&value.binding_types);
        self.debug(&value.binding_keys);
        self.bytes(&[value.sealed as u8]);
    }

    fn capture_environment(&mut self, value: &CaptureEnvironment) {
        self.debug(value.brand);
        self.bytes(&(value.captures.len() as u64).to_le_bytes());
        for capture in &value.captures {
            self.bytes(capture.name.as_bytes());
            self.debug(capture.mode);
            self.ty(&capture.ty);
        }
        self.debug(&value.post_states);
        self.debug(value.runs_in.environment);
        self.debug(value.runs_in.callable);
        self.effect_row(&value.runs_in.effects);
        self.debug(&value.runs_in.post_states);
        self.bytes(&[value.runs_in.sealed as u8]);
        self.bytes(&[value.sealed as u8]);
    }

    fn place(&mut self, value: &CorePlace) {
        match value {
            CorePlace::Local { name, ty } => {
                self.bytes(b"local");
                self.bytes(name.as_bytes());
                self.ty(ty);
            }
            CorePlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                self.bytes(b"field");
                self.place(base);
                self.bytes(&index.to_le_bytes());
                self.bytes(&field_count.to_le_bytes());
                self.ty(ty);
            }
            CorePlace::Deref {
                reference,
                ty,
                unique,
            } => {
                self.bytes(b"deref");
                self.id(*reference);
                self.ty(ty);
                self.bytes(&[*unique as u8]);
            }
            CorePlace::Error => self.bytes(b"error"),
        }
    }

    fn id(&mut self, id: CoreId) {
        if let Some(number) = self.numbers.get(&id).copied() {
            self.bytes(b"ref");
            self.bytes(&number.to_le_bytes());
            return;
        }
        let number = self.numbers.len() as u32;
        self.numbers.insert(id, number);
        self.bytes(b"node");
        self.bytes(&number.to_le_bytes());
        let Some(expression) = self.body.expressions.get(id.0 as usize) else {
            // Invalid Core never becomes a release product, but representing
            // this state deterministically keeps inspection tools total.
            self.bytes(b"missing");
            self.bytes(&id.0.to_le_bytes());
            return;
        };
        self.ty(&expression.ty);
        if self.body.unsafe_scopes.contains(&id) {
            self.bytes(b"explicit-unsafe-scope");
        }
        self.kind(&expression.kind);
    }

    fn ids(&mut self, values: &[CoreId]) {
        self.bytes(&(values.len() as u64).to_le_bytes());
        for value in values {
            self.id(*value);
        }
    }

    fn kind(&mut self, kind: &CoreKind) {
        match kind {
            CoreKind::Literal(value) => {
                self.bytes(b"literal");
                self.bytes(value.as_bytes());
            }
            CoreKind::Local(name) => {
                self.bytes(b"local");
                self.bytes(name.as_bytes());
            }
            CoreKind::Resumption { id, name } => {
                self.bytes(b"resumption");
                self.debug(id);
                self.bytes(name.as_bytes());
            }
            CoreKind::LabelValue { brand } => {
                self.bytes(b"label-value");
                self.debug(brand);
            }
            CoreKind::Function {
                definition,
                arguments,
                host_import,
            } => {
                self.bytes(b"function");
                self.debug(definition);
                self.generic_arguments(arguments);
                match host_import {
                    Some(import) => {
                        self.bytes(b"host-import");
                        self.bytes(import.capability.as_bytes());
                        self.bytes(import.symbol.as_bytes());
                    }
                    None => self.bytes(b"ordinary-function"),
                }
            }
            CoreKind::TraitMethod {
                evidence,
                method,
                trait_arguments,
                method_arguments,
                deferred,
            } => {
                self.bytes(b"trait-method");
                self.debug(evidence);
                self.debug(method);
                self.generic_arguments(trait_arguments);
                self.generic_arguments(method_arguments);
                if let Some(deferred) = deferred {
                    self.bytes(b"deferred-trait-method");
                    self.debug(&deferred.relation.definition);
                    self.generic_arguments(&deferred.relation.arguments);
                    self.ty(&deferred.subject);
                    self.bytes(deferred.name.as_bytes());
                }
            }
            CoreKind::Constant {
                definition,
                arguments,
            } => {
                self.bytes(b"constant");
                self.debug(definition);
                self.generic_arguments(arguments);
            }
            CoreKind::Tuple(values) => {
                self.bytes(b"tuple");
                self.ids(values);
            }
            CoreKind::Array(values) => {
                self.bytes(b"array");
                self.ids(values);
            }
            CoreKind::Record { definition, fields } => {
                self.bytes(b"record");
                self.debug(definition);
                self.ids(fields);
            }
            CoreKind::Field {
                base,
                index,
                field_count,
            } => {
                self.bytes(b"field");
                self.bytes(&index.to_le_bytes());
                self.bytes(&field_count.to_le_bytes());
                self.id(*base);
            }
            CoreKind::Enum {
                definition,
                variant,
                fields,
            } => {
                self.bytes(b"enum");
                self.debug(definition);
                self.bytes(&variant.to_le_bytes());
                self.ids(fields);
            }
            CoreKind::PatternTest {
                subject,
                pattern,
                refinement,
            } => {
                self.bytes(b"pattern-test");
                self.pattern(pattern);
                self.refinement(refinement);
                self.id(*subject);
            }
            CoreKind::Closure {
                callable,
                parameters,
                environment,
                body,
            } => {
                self.bytes(b"closure");
                self.debug(callable);
                self.bindings(parameters);
                self.capture_environment(environment);
                self.id(*body);
            }
            CoreKind::Let { name, value } => {
                self.bytes(b"let");
                self.bytes(name.as_bytes());
                self.id(*value);
            }
            CoreKind::Label { brand, body } => {
                self.bytes(b"label");
                self.debug(brand);
                self.id(*body);
            }
            CoreKind::Transfer { brand, value } => {
                self.bytes(b"transfer");
                self.debug(brand);
                self.id(*value);
            }
            CoreKind::Assign { place, value } => {
                self.bytes(b"assign");
                self.place(place);
                self.id(*value);
            }
            CoreKind::Call {
                callee,
                arguments,
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                self.bytes(b"call");
                self.id(*callee);
                self.ids(arguments);
                self.debug(reference_contract);
                self.debug(reference_origin);
                self.debug(reference_shape);
            }
            CoreKind::Perform {
                effect,
                operation,
                payload_types,
                arguments,
                terminal,
                reference_contract,
                reference_origin,
                reference_shape,
            } => {
                self.bytes(b"perform");
                self.effect(effect);
                self.bytes(&operation.to_le_bytes());
                self.bytes(&[*terminal as u8]);
                self.types(payload_types);
                self.ids(arguments);
                self.debug(reference_contract);
                self.debug(reference_origin);
                self.debug(reference_shape);
            }
            CoreKind::Handle {
                computation,
                clauses,
            } => {
                self.bytes(b"handle");
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.debug(clause.brand);
                    self.effect(&clause.effect);
                    self.bytes(&clause.operation.to_le_bytes());
                    self.types(&clause.payload_types);
                    self.bytes(&(clause.patterns.len() as u64).to_le_bytes());
                    for pattern in &clause.patterns {
                        self.pattern(pattern);
                    }
                    self.bindings(&clause.bindings);
                    self.debug(&clause.resumption);
                    match &clause.continuation {
                        Some(continuation) => {
                            self.bytes(b"continuation");
                            self.debug(continuation.brand);
                            self.ty(&continuation.parameter);
                            self.ty(&continuation.result);
                            self.ty(&Type::Callable {
                                safety: crate::Safety::Safe,
                                lifetime_binders: 0,
                                parameters: vec![],
                                result: Box::new(Type::Unit),
                                effects: continuation.effects.clone(),
                                invocation: continuation.invocation,
                            });
                            self.bytes(&continuation.direct_uses.to_le_bytes());
                        }
                        None => self.bytes(b"no-continuation"),
                    }
                    self.bytes(&[clause.terminal as u8]);
                    self.id(clause.body);
                }
            }
            CoreKind::Completion {
                computation,
                clauses,
                handles_operations,
                refinement_test,
            } => {
                self.bytes(b"completion");
                if let Some(environment) = refinement_test {
                    self.bytes(b"binding-pack-producer");
                    self.refinement(environment);
                }
                self.bytes(&[*handles_operations as u8]);
                self.id(*computation);
                self.bytes(&(clauses.len() as u64).to_le_bytes());
                for clause in clauses {
                    self.pattern(&clause.pattern);
                    self.bindings(&clause.bindings);
                    match &clause.refinement {
                        Some(refinement) => {
                            self.bytes(b"refinement");
                            self.refinement(&refinement.environment);
                            self.id(refinement.subject);
                            self.pattern(&refinement.pattern);
                        }
                        None => self.bytes(b"no-refinement"),
                    }
                    self.id(clause.body);
                }
            }
            CoreKind::IntrinsicCall {
                operator,
                arguments,
            } => {
                self.bytes(b"intrinsic-call");
                self.bytes(operator.as_bytes());
                self.bytes(&(arguments.len() as u64).to_le_bytes());
                for argument in arguments {
                    self.id(*argument);
                }
            }
            CoreKind::Block(values) => {
                self.bytes(b"block");
                self.ids(values);
            }
            CoreKind::Borrow { unique, value } => {
                self.bytes(b"borrow");
                self.bytes(&[*unique as u8]);
                self.id(*value);
            }
            CoreKind::Deref(value) => {
                self.bytes(b"deref");
                self.id(*value);
            }
            CoreKind::Move(value) => {
                self.bytes(b"move");
                self.id(*value);
            }
            CoreKind::Error => self.bytes(b"error"),
        }
    }
}
