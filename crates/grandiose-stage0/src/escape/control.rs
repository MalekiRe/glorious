//! Generative control dependencies ride the existing value/storage snapshots.
//! This adapter consumes the shared lexical brand facts and capture-formation
//! actions; it does not re-evaluate Core or infer labels from callable types.
use super::*;

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) enum ControlBrand {
    Label(crate::LabelBrand),
    Resumption(crate::core::ResumptionId),
}

impl ControlBrand {
    fn diagnostic(self) -> &'static str {
        match self { Self::Label(_) => "G4179", Self::Resumption(_) => "G4174" }
    }
}

/// Augment ordinary result provenance with positively projected inputs.
/// Unknown fields retain the existing declared-result proof obligations;
/// this partial projection never substitutes for those independent checks.
pub(super) fn known_payload(
    payload: crate::callable_control::ResolvedPayload<Value>,
    storage: &ValueEnvironment,
    obligations: &mut BTreeMap<EnvironmentBrand, BTreeSet<ControlBrand>>,
    signatures: &crate::ElaboratedInterface,
) -> Option<Value> {
    payload_value(payload, storage, obligations, signatures, false)
}

fn payload_value(
    payload: crate::callable_control::ResolvedPayload<Value>,
    storage: &ValueEnvironment,
    obligations: &mut BTreeMap<EnvironmentBrand, BTreeSet<ControlBrand>>,
    signatures: &crate::ElaboratedInterface,
    capture: bool,
) -> Option<Value> {
    use crate::callable_control::ResolvedPayload;
    match payload {
        ResolvedPayload::Inputs { values, .. } => Some(join(values.into_iter()
            .map(|value| Analyzer::resolved_value_in(&value, storage)).collect())),
        ResolvedPayload::Aggregate(fields) => {
            let fields = fields.into_iter().map(|field| payload_value(field, storage, obligations, signatures, capture)).collect::<Vec<_>>();
            fields.iter().any(Option::is_some).then(|| {
                Value::Aggregate(
                    fields
                        .into_iter()
                        .map(|value| value.unwrap_or(Value::None))
                        .collect(),
                )
            })
        }
        ResolvedPayload::Callable { constructor, captures, .. } => {
            let environment = constructor.brand();
            let resident_captures = captures.into_iter().map(|(ty, payload)|
                crate::resident_invocations::Operand { ty,
                    value: payload_value(payload, storage, obligations, signatures, true).unwrap_or(Value::None) }).collect::<Vec<_>>();
            let controls = resident_captures.iter().flat_map(|capture| value_controls(&capture.value))
                .chain(constructor.labels().iter().copied().map(ControlBrand::Label)).collect::<BTreeSet<_>>();
            obligations.entry(environment).or_default().extend(&controls);
            let captures = resident_captures.iter().flat_map(|capture| capture_dependency_roots(&capture.value))
                .collect::<BTreeSet<_>>().into_iter().map(|root| Capture::Borrowed { root, environment }).collect();
            let regions = resident_captures.iter().flat_map(|capture| contained_regions(&capture.value)).collect();
            let frame_independent = constructor.labels().is_empty() && controls.is_empty()
                && resident_captures.iter().all(|capture| frame_independent_value(&capture.value));
            Some(Value::Closure { environment, captures, resident_captures, frame_independent, regions, controls })
        }
        // A constructor must describe each resident capture. A missing
        // input projection can still be independently frame-independent
        // (for example, a scalar computed inside the factory). References
        // and opaque callable environments do not receive that permission.
        ResolvedPayload::Unknown(ty) if capture && crate::core::tail::tail_owned_type(signatures, &ty, &mut vec![]) => Some(Value::FrameIndependent),
        ResolvedPayload::Unknown(_) => None,
    }
}

pub(super) fn value_controls(value: &Value) -> BTreeSet<ControlBrand> {
    let mut labels = BTreeSet::new();
    let mut pending = vec![value];
    while let Some(value) = pending.pop() {
        match value {
            Value::Control(brand) => {
                labels.insert(*brand);
            }
            Value::Closure {
                controls: captured, ..
            } => labels.extend(captured),
            Value::Aggregate(values)
            | Value::Variant(values)
            | Value::Alternatives(values)
            | Value::Joined(values) => pending.extend(values),
            Value::Logical {
                physical,
                arguments,
            } => {
                pending.push(physical);
                pending.extend(arguments.values());
            }
            Value::Array {
                length,
                element,
                fields,
            } => pending.extend(array_values(*length, element, fields)),
            Value::CallableResident { footprint, .. } => pending.push(footprint),
            Value::Region(_) => {
                unreachable!("resolve storage snapshots before querying control dependencies")
            }
            Value::None
            | Value::FrameIndependent
            | Value::ExternalBorrowed
            | Value::Borrowed { .. } => {}
        }
    }
    labels
}

pub(super) fn unrepresented_capture(value: &Value) -> bool {
    match value {
        Value::None | Value::Region(_) => true,
        Value::Aggregate(values) | Value::Variant(values) | Value::Alternatives(values) | Value::Joined(values) =>
            values.iter().any(unrepresented_capture),
        Value::Array { length, element, fields } => array_values(*length, element, fields).any(unrepresented_capture),
        Value::Closure { resident_captures, .. } => resident_captures.iter().any(|capture| unrepresented_capture(&capture.value)),
        Value::CallableResident { footprint, resident_captures } => unrepresented_capture(footprint)
            || resident_captures.iter().any(|capture| unrepresented_capture(&capture.value)),
        Value::Logical { physical, arguments } => unrepresented_capture(physical) || arguments.values().any(unrepresented_capture),
        Value::FrameIndependent | Value::ExternalBorrowed | Value::Borrowed { .. } | Value::Control(_) => false,
    }
}

impl Analyzer<'_> {
    pub(super) fn report_control_value_escape(&mut self, value: &Value, span: Span, boundary: &str) {
        for brand in value_controls(value) {
            self.error(
                span,
                brand.diagnostic(),
                format!("control capability {brand:?} is retained beyond its active scope by {boundary}"),
            );
        }
    }

    pub(super) fn report_control_scope_escape(
        &mut self,
        brand: ControlBrand,
        result: &Value,
        incoming: &ValueEnvironment,
        span: Span,
    ) {
        let retains = |value: &Value| value_controls(&self.resolved_value(value)).contains(&brand);
        let retained_by_result = retains(result);
        // These are the exact storage identities that predate this label.
        // Label-local bindings and retired shadowed names are not external
        // destinations merely because their snapshots remain in the arena.
        let retained_by_outer_storage = incoming
            .bindings
            .values()
            .any(|storage| self.values.residents.get(storage).is_some_and(&retains));
        // An exit to an enclosing label has already captured its own snapshot;
        // it does not become a normal exit from the label being ended here.
        let retained_by_outer_exit =
            self.labels
                .iter()
                .flat_map(|label| &label.exits)
                .any(|exit| {
                    let retains = |value: &Value| {
                        // Resolve against the exit's storage graph, not whatever
                        // sibling/normal state happens to be current afterward.
                        value_controls(&Self::resolved_value_in(value, &exit.environment))
                            .contains(&brand)
                    };
                    retains(&exit.value)
                        || incoming.bindings.values().any(|storage| {
                            exit.environment.residents.get(storage).is_some_and(retains)
                        })
                });
        if retained_by_result || retained_by_outer_storage || retained_by_outer_exit {
            self.error(span, brand.diagnostic(), format!(
                "control capability {brand:?} remains in an outgoing value or outer storage after its scope ends"));
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn brand(label: u32) -> ControlBrand {
        ControlBrand::Label(crate::LabelBrand {
            owner: crate::DefKey(crate::Digest::of_bytes(b"control scope snapshots")),
            label,
        })
    }

    #[test]
    fn partial_return_payloads_preserve_field_positions_without_proving_unknown_fields() {
        use crate::callable_control::ResolvedPayload;
        let storage = ValueEnvironment::default();
        let mut obligations = BTreeMap::new();
        let signatures = crate::ElaboratedInterface::default();
        assert_eq!(known_payload(ResolvedPayload::Unknown(Type::Unit), &storage, &mut obligations, &signatures), None);
        let returned = known_payload(ResolvedPayload::Aggregate(vec![
            ResolvedPayload::Unknown(Type::Unit),
            ResolvedPayload::Inputs {
                ty: Type::Unit,
                values: vec![Value::Control(brand(0))],
            },
        ]), &storage, &mut obligations, &signatures)
        .unwrap();
        assert_eq!(
            returned,
            Value::Aggregate(vec![Value::None, Value::Control(brand(0))])
        );
        assert!(!frame_independent_value(&returned));
        assert_eq!(value_controls(&returned), BTreeSet::from([brand(0)]));
    }

    #[test]
    fn control_labels_survive_wrappers_but_not_uninhabited_array_elements() {
        let value = Value::CallableResident {
            footprint: Box::new(Value::Logical {
                physical: Box::new(Value::Aggregate(vec![Value::Control(brand(0))])),
                arguments: BTreeMap::from([(0, Value::Alternatives(vec![Value::Control(brand(1))]))]),
            }),
            resident_captures: vec![],
        };
        assert_eq!(value_controls(&value), BTreeSet::from([brand(0), brand(1)]));
        assert!(!frame_independent_value(&value));
        let empty = Value::Array {
            length: Some(0),
            element: Box::new(value),
            fields: BTreeMap::new(),
        };
        assert!(value_controls(&empty).is_empty());
    }

    #[test]
    fn a_captured_storage_update_revokes_frame_independence_and_retains_its_label() {
        let region = crate::placeflow::regions::Region {
            site: "captured storage".into(),
            path: vec![],
        };
        let mut values = ValueEnvironment::default();
        values
            .regions
            .insert(region.clone(), Value::Control(brand(0)), merge_region_values);
        let value = Value::Closure {
            environment: EnvironmentBrand {
                owner: crate::DefKey(crate::Digest::of_bytes(b"control scope snapshots")),
                callable: crate::CallableId(0),
            },
            captures: vec![],
            resident_captures: vec![],
            frame_independent: true,
            regions: BTreeSet::from([region]),
            controls: BTreeSet::new(),
        };
        let resolved = Analyzer::resolved_value_in(&value, &values);
        assert_eq!(value_controls(&resolved), BTreeSet::from([brand(0)]));
        assert!(!frame_independent_value(&resolved));
        assert!(
            value_controls(&Analyzer::resolved_value_in(
                &value,
                &ValueEnvironment::default()
            ))
            .is_empty()
        );
    }
}
