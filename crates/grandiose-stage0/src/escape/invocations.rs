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
