//! Value lookup/application adapter for the shared invocation relation.
use super::*;
use crate::resident_invocations::{CapturedInputs, Inputs, Operand};

fn collect(value: &Value, operands: &mut BTreeSet<Operand<Value>>, represented: &mut bool) {
    match value {
        Value::Closure {
            resident_captures, ..
        } => {
            *represented = true;
            operands.extend(resident_captures.iter().cloned());
        }
        Value::CallableResident {
            footprint,
            resident_captures,
        } => {
            *represented = true;
            operands.extend(resident_captures.iter().cloned());
            // A factory can return an existing callable while also retaining
            // new inputs. Its forwarding footprint keeps that callable's
            // typed invocation inputs, not merely its boundary borrow roots.
            collect(footprint, operands, represented);
        }
        Value::Joined(values) | Value::Alternatives(values) => {
            for value in values {
                collect(value, operands, represented);
            }
        }
        Value::Logical { physical, .. } => collect(physical, operands, represented),
        _ => {}
    }
}

impl Inputs for Analyzer<'_> {
    type Value = Value;

    fn project(&self, value: &Value, path: &[u32]) -> Option<Value> {
        self.reference_path_value(value, path)
    }

    fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> {
        let mut operands = BTreeSet::new();
        let mut represented = false;
        collect(
            &self.resolved_value(&callable.value),
            &mut operands,
            &mut represented,
        );
        let stateless = matches!(&callable.ty, Type::Callable { contract, .. }
            if contract.environment.is_some() && contract.captures.is_empty());
        CapturedInputs {
            operands: operands.into_iter().collect(),
            unresolved: !represented && !stateless,
        }
    }
}

impl crate::callable_control::PayloadInputs for Analyzer<'_> {
    type Value = Value;
    fn project(&self, value: &Value, path: &[u32]) -> Option<Value> { Inputs::project(self, value, path) }
    fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> { Inputs::captures(self, callable) }
    fn reborrow(&self, reference: &Value, fields: &[u32]) -> Option<Value> {
        fn project(value: Value, fields: &[u32]) -> Value {
            match value {
                Value::Borrowed { root, storage, fields: mut prefix } => {
                    prefix.extend_from_slice(fields);
                    Value::Borrowed { root, storage, fields: prefix }
                }
                Value::Joined(values) => join(values.into_iter().map(|value| project(value, fields)).collect()),
                Value::Alternatives(values) => Value::Alternatives(values.into_iter().map(|value| project(value, fields)).collect()),
                Value::Logical { physical, .. } => project(*physical, fields),
                value => value,
            }
        }
        Some(project(self.resolved_value(reference), fields))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factory_wrapper_preserves_existing_typed_capture_inputs() {
        let operand = |root: &str| Operand {
            ty: Type::Reference {
                mutability: crate::Mutability::Shared,
                lifetime: crate::Lifetime::Elided,
                referent: Box::new(Type::Tuple(vec![])),
            },
            value: Value::Borrowed {
                root: root.into(),
                storage: None,
                fields: vec![],
            },
        };
        let existing = operand("existing");
        let additional = operand("additional");
        let resident = Value::CallableResident {
            footprint: Box::new(Value::Closure {
                environment: EnvironmentBrand {
                    owner: crate::DefKey(crate::Digest::of_bytes(b"capture wrapper test")),
                    callable: crate::core::CallableId(0),
                },
                captures: vec![],
                resident_captures: vec![existing.clone()],
                frame_independent: false,
                regions: BTreeSet::new(),
                controls: BTreeSet::new(),
            }),
            resident_captures: vec![additional.clone()],
        };
        let mut operands = BTreeSet::new();
        let mut represented = false;
        collect(&resident, &mut operands, &mut represented);
        assert!(represented);
        assert_eq!(operands, BTreeSet::from([existing, additional]));
    }
}

impl Analyzer<'_> {
    pub(super) fn record_label_exit(&mut self, brand: crate::LabelBrand, value: Value, span: Span) {
        let value = self.resolved_value(&value);
        if let Some(label) = self
            .labels
            .iter_mut()
            .rev()
            .find(|label| label.brand == brand)
        {
            label.exits.push(LabelExit {
                value,
                environment: self.values.clone(),
            });
        } else {
            self.report_return_escape(&value, span);
        }
    }

    pub(super) fn record_invocation_exits(
        &mut self,
        call: CoreId,
        callable: &Value,
        arguments: &[Value],
        span: Span,
    ) {
        let Some(control) = self.continuations.invocation(call).cloned() else {
            return;
        };
        if control.unknown {
            return;
        }
        for transfer in control.transfers {
            let value = self.invocation_payload(&transfer.payload, callable, arguments, span);
            if let Some(target) = transfer.target {
                self.record_label_exit(target, value, span);
            } else {
                self.report_return_escape(&value, span);
            }
        }
    }

    fn invocation_payload(
        &mut self,
        payload: &crate::callable_control::InvocationPayload,
        callable: &Value,
        arguments: &[Value],
        span: Span,
    ) -> Value {
        let value = crate::callable_control::resolve_payload(payload, callable, arguments, self);
        self.materialize_payload(value, span)
    }

    fn materialize_payload(
        &mut self,
        value: crate::callable_control::ResolvedPayload<Value>,
        span: Span,
    ) -> Value {
        use crate::callable_control::ResolvedPayload;
        match value {
            ResolvedPayload::Inputs { values, .. } => join(values),
            ResolvedPayload::Aggregate(fields) => Value::Aggregate(
                fields
                    .into_iter()
                    .map(|field| self.materialize_payload(field, span))
                    .collect(),
            ),
            value @ ResolvedPayload::Callable { .. } => {
                let value = control::known_payload(value, &self.values, &mut self.control_captures, self.signatures).expect("represented constructor");
                if control::unrepresented_capture(&value) {
                    self.error(span, "G5023", "callable payload has an unrepresented capture provenance");
                }
                value
            }
            ResolvedPayload::Unknown(ty) => {
                if crate::core::tail::tail_owned_type(self.signatures, &ty, &mut vec![]) {
                    Value::FrameIndependent
                } else {
                    self.error(
                        span,
                        "G5023",
                        "label payload has no frozen input or frame-independent provenance",
                    );
                    Value::None
                }
            }
        }
    }

    pub(super) fn record_invocation_stores(
        &mut self,
        callee: CoreId,
        callable: Value,
        arguments: &[CoreId],
        values: &[Value],
        span: Span,
    ) {
        let arguments = arguments
            .iter()
            .zip(values)
            .map(|(argument, value)| Operand {
                ty: self.body.expression(*argument).ty.clone(),
                value: value.clone(),
            })
            .collect::<Vec<_>>();
        let relations = crate::resident_invocations::derive(
            self.signatures,
            self.body.expression(callee),
            callable,
            &arguments,
            self,
        );
        for store in relations.stores {
            if value_contains_external_reference(&self.resolved_value(&store.destination)) {
                self.report_external_store_escape(&store.source, span);
            }
            let mut regions = logical_regions(&store.destination);
            let Some(first) = regions.first().cloned() else {
                continue;
            };
            regions.extend(logical_regions(&store.source));
            self.values.regions.connect(&regions);
            self.values
                .regions
                .insert(first, store.source, merge_region_values);
        }
        // An unresolved environment still retains its observed footprint.
        // This does not certify missing capture or invocation-control evidence.
        for callable in relations.unresolved {
            let regions = contained_regions(&callable.value);
            let Some(first) = regions.first().cloned() else {
                continue;
            };
            let value = self.resolved_value(&callable.value);
            self.values.regions.connect(&regions);
            self.values
                .regions
                .insert(first, value, merge_region_values);
        }
    }
}
