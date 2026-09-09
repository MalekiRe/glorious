use super::*;
use crate::{
    BodySyntax, DeclarationScan, DefinitionIndex, ElaboratedHeader, FileKey, FixityTable,
    InterfaceSet, LexedFile, PackageKey,
};

struct Fixture {
    bodies: BTreeMap<DefKey, TypedBody>,
    signatures: BTreeMap<DefKey, CallableSignature>,
    names: BTreeMap<String, DefKey>,
    interface: ElaboratedInterface,
}

impl Fixture {
    fn new(source: &str) -> Self {
        let package = PackageKey("bound-control@1".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let index = DefinitionIndex::from_interface(&interface);
        let signatures = ElaboratedInterface::elaborate_with_index(&interface, &index);
        assert!(
            signatures.diagnostics.is_empty(),
            "{:?}",
            signatures.diagnostics
        );
        let fixities = FixityTable::for_module(&interface);
        let mut result = Self {
            bodies: BTreeMap::new(),
            signatures: BTreeMap::new(),
            names: BTreeMap::new(),
            interface: signatures.clone(),
        };
        for definition in &interface.definitions {
            let (Some(ElaboratedHeader::Callable(signature)), Some(range)) =
                (signatures.definitions.get(&definition.key), definition.body)
            else {
                continue;
            };
            let syntax = BodySyntax::parse_with_fixities(&lexed, source, range, &fixities);
            let body = TypedBody::elaborate_with_fixities(
                definition,
                &syntax,
                &index,
                &signatures,
                &fixities,
            );
            assert!(body.diagnostics.is_empty(), "{:?}", body.diagnostics);
            assert!(body.validate().is_empty(), "{:?}", body.validate());
            result
                .names
                .insert(definition.name.clone().unwrap(), definition.key);
            result.signatures.insert(definition.key, signature.clone());
            result.bodies.insert(definition.key, body);
        }
        result
    }

    fn inputs(&self) -> BTreeMap<DefKey, ControlBody<'_>> {
        self.bodies
            .iter()
            .map(|(key, body)| {
                (
                    *key,
                    ControlBody {
                        body,
                        signature: &self.signatures[key],
                        interface: &self.interface,
                    },
                )
            })
            .collect()
    }

    fn call_to(&self, owner: DefKey, target: DefKey) -> CoreId {
        self.bodies[&owner].expressions.iter().enumerate().find_map(|(index, expression)| {
            let CoreKind::Call { callee, .. } = expression.kind else { return None; };
            matches!(self.bodies[&owner].expression(callee).kind, CoreKind::Function { definition, .. } if definition == target)
                .then_some(CoreId(index as u32))
        }).unwrap()
    }
}

const AFTER_UNKNOWN: &str = "#![no_std]
    fn relay<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
    fn select<F>(observe:F) -> i64 where F:Fn<(),Output=()> { observe(); relay(42,@select) }";

#[test]
fn observed_label_addresses_retain_input_identity_through_structural_callable_views() {
    let fixture = Fixture::new("#![no_std]
        fn borrower(value:(i64) -> !) -> ! { { let reference = &value; }; value(42) }
        pub fn main() -> i64 { borrower(@main) }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let bound = summaries.bind(&inputs).unwrap();
    let obligations = bound.label_address_obligations();
    assert_eq!(obligations.len(), 1);
    assert!(!obligations[0].unique);
    assert_eq!(obligations[0].site.location.callable, CallableBrand::Named(fixture.names["borrower"]));
    assert!(matches!(&obligations[0].target, ControlLabelTarget::Lexical { brand, .. } if brand.owner == fixture.names["main"]));
    // The caller invokes a helper that exits through a label; replacing that
    // helper call by a direct leave would erase the body's preceding borrow.
    let call = fixture.call_to(fixture.names["main"], fixture.names["borrower"]);
    assert!(bound.body(fixture.names["main"]).unwrap().get(call).unwrap().direct_label().is_none());
}

#[test]
fn an_unknown_prefix_cannot_discard_an_observed_label_address_obligation() {
    let fixture = Fixture::new("#![no_std]
        fn borrower(value:(i64) -> !) -> ! { { let reference = &value; }; value(42) }
        pub fn caller<F>(observe:F) -> i64 where F:Fn<(),Output=()> { observe(); borrower(@caller) }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    assert!(!summaries.get(CallableBrand::Named(fixture.names["caller"])).unwrap().is_complete());
    let obligations = summaries.bind(&inputs).unwrap().label_address_obligations();
    assert_eq!(obligations.len(), 1);
    assert!(matches!(&obligations[0].target, ControlLabelTarget::Lexical { brand, .. } if brand.owner == fixture.names["caller"]));
}

#[test]
fn exact_local_label_callees_lower_to_transfers_after_their_strict_operands() {
    let fixture = Fixture::new("#![no_std]
        fn keep<T>(value:T) -> T { value }
        pub fn main() -> i64 { keep(@main)(42) }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["main"];
    let body = &fixture.bodies[&owner];
    let call = body.expressions.iter().enumerate().find_map(|(index, expression)| {
        let CoreKind::Call { callee, .. } = expression.kind else { return None; };
        matches!(body.expression(callee).kind, CoreKind::Call { .. }).then_some(CoreId(index as u32))
    }).unwrap();
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    assert!(control.get(call).unwrap().direct_label().is_some());
    assert!(control.get(fixture.call_to(owner, fixture.names["keep"])).unwrap().direct_label().is_none());
    let facts = crate::core_continuations::CoreContinuations::derive_with_invocations(body, Some(control)).unwrap();
    let evaluation = crate::evaluation_mir::EvaluationMir::lower_with_continuations(owner, body, &facts).unwrap();
    let operations = evaluation.regions().iter().flat_map(|region| &region.instructions).collect::<Vec<_>>();
    assert_eq!(operations.iter().filter(|instruction| matches!(instruction.operation, crate::evaluation_mir::EvaluationOperation::Call(_))).count(), 1,
        "the callee-producing keep invocation must still execute");
    assert!(operations.iter().any(|instruction| instruction.source == call
        && matches!(instruction.operation, crate::evaluation_mir::EvaluationOperation::Transfer(_))));
    assert!(crate::control_mir::ControlMir::lower(&evaluation).is_ok());
    let mut forged = body.clone();
    forged.expressions[call.0 as usize].kind = CoreKind::Literal("0".into());
    assert!(crate::evaluation_mir::EvaluationMir::lower_with_continuations(owner, &forged, &facts).is_err());
}

#[test]
fn a_declared_call_contract_does_not_require_an_observed_prefix() {
    let fixture = Fixture::new(AFTER_UNKNOWN);
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["select"];
    let call = fixture.call_to(owner, fixture.names["relay"]);
    let summary = summaries.get(CallableBrand::Named(owner)).unwrap();
    assert!(
        !summary.is_complete(),
        "the preceding callback remains unresolved"
    );
    assert!(
        summary
            .calls()
            .filter(|(site, _)| site.location.expression == call)
            .all(|(_, coverage)| !coverage.is_complete()),
        "do not fabricate complete observations"
    );
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    let invocation = control.get(call).unwrap();
    assert!(!invocation.normal && !invocation.unknown && !invocation.outer_transfer);
    assert_eq!(invocation.labels.len(), 1);
    let facts = crate::core_continuations::CoreContinuations::derive_with_invocations(
        &fixture.bodies[&owner],
        Some(control),
    )
    .unwrap();
    assert!(facts.is_abrupt(call));
    assert!(
        !facts.is_abrupt(fixture.bodies[&owner].root),
        "the function's exact label rejoins"
    );
}

#[test]
fn an_unresolved_label_operand_does_not_gain_a_destination_from_never() {
    let fixture = Fixture::new(
        "#![no_std]
        fn relay<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        fn select<F,L>(observe:F, target:L) -> ! where F:Fn<(),Output=()>, L:Label<i64> {
            observe(); relay(42,target)
        }",
    );
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["select"];
    let call = fixture.call_to(owner, fixture.names["relay"]);
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    assert!(control.get(call).unwrap().unknown);
    assert!(control.get(call).unwrap().labels.is_empty());
}

#[test]
fn binding_checks_dependencies_and_the_complete_local_control_input() {
    let mut fixture = Fixture::new(AFTER_UNKNOWN);
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["select"];
    let helper = fixture.names["relay"];
    let call = fixture.call_to(owner, helper);
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    let mut changed = fixture.bodies[&owner].clone();
    let CoreKind::Call {
        ref mut arguments, ..
    } = changed.expressions[call.0 as usize].kind
    else {
        unreachable!()
    };
    arguments.swap(0, 1);
    assert!(!control.matches(&changed));
    assert!(
        crate::core_continuations::CoreContinuations::derive_with_invocations(
            &changed,
            Some(control)
        )
        .is_err()
    );
    let body = fixture.bodies.get_mut(&helper).unwrap();
    body.expressions[body.root.0 as usize].ty = Type::Unit;
    assert!(
        summaries.bind(&fixture.inputs()).is_err(),
        "an unchanged caller cannot hide a changed helper"
    );
}

#[test]
fn a_failed_work_checkpoint_returns_no_partial_control_product() {
    let fixture = Fixture::new(AFTER_UNKNOWN);
    let mut checkpoints = 0;
    let mut charged = 0;
    let result = derive_control_summaries_with_check(
        &fixture.inputs(),
        Default::default(),
        &mut |_, cost| {
            checkpoints += 1;
            charged += cost;
            if checkpoints == 3 {
                Err("cancelled")
            } else {
                Ok(())
            }
        },
    );
    assert!(matches!(result, Err("cancelled")));
    assert_eq!(checkpoints, 3);
    assert!(charged > 0);
}

#[test]
fn abstract_label_payload_keeps_its_instantiated_input_type() {
    let fixture = Fixture::new(
        "#![no_std]
        fn relay<T,L>(value:T, target:L) -> ! where L:Label<T> { target(value) }
        fn select<F>(observe:F, value:&i64) -> &i64 where F:Fn<(),Output=()> {
            observe(); relay(value,@select)
        }",
    );
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["select"];
    let call = fixture.call_to(owner, fixture.names["relay"]);
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    let transfers = &control.get(call).unwrap().transfers;
    assert_eq!(transfers.len(), 1);
    assert!(matches!(transfers[0].payload.ty, Type::Reference { .. }));
    assert_eq!(
        transfers[0].payload.source,
        payloads::PayloadSource::Argument {
            index: 0,
            path: vec![]
        }
    );
}

#[test]
fn normal_return_payloads_project_captured_and_explicit_inputs() {
    let fixture = Fixture::new("#![no_std]
        fn keep<T>(value:T) -> T { value }
        fn select() -> i64 {
            let target = @select;
            let read = move (target) { (target,) };
            let alias = read(); keep(alias); 42
        }
        fn after<F>(observe:F, value:&i64) -> &i64 where F:Fn<(),Output=()> {
            observe(); keep(value)
        }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let bound = summaries.bind(&inputs).unwrap();
    let owner = fixture.names["select"];
    let body = &fixture.bodies[&owner];
    let control = bound.body(owner).unwrap();
    let read = body.expressions.iter().enumerate().find_map(|(index, expression)| {
        let CoreKind::Call { callee, .. } = expression.kind else { return None; };
        matches!(&body.expression(callee).kind, CoreKind::Local(name) if name == "read")
            .then_some(CoreId(index as u32))
    }).unwrap();
    let invocation = control.get(read).unwrap();
    assert!(invocation.normal && !invocation.unknown && invocation.transfers.is_empty());
    let payloads::PayloadSource::Aggregate(fields) = &invocation.returns[0].source else {
        panic!("captured return must preserve its tuple projection: {invocation:?}");
    };
    assert!(matches!(&fields[0].source, payloads::PayloadSource::Capture { path, .. } if path.is_empty()));
    let owner = fixture.names["after"];
    let control = bound.body(owner).unwrap();
    let invocation = control.get(fixture.call_to(owner, fixture.names["keep"])).unwrap();
    assert!(invocation.normal && !invocation.unknown);
    assert!(matches!(invocation.returns[0].ty, Type::Reference { .. }));
    assert_eq!(invocation.returns[0].source, payloads::PayloadSource::Argument { index: 0, path: vec![] });
}

#[test]
fn an_unconditional_coverage_gap_retains_observed_captured_return_dependencies() {
    let fixture = Fixture::new("#![no_std]
        fn select<F>(observe:F) -> i64 where F:Fn<(),Output=()> {
            observe();
            let target = @select;
            let read = move (target) { target };
            let alias = read(); 42
        }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let owner = fixture.names["select"];
    let body = &fixture.bodies[&owner];
    let read = body.expressions.iter().enumerate().find_map(|(index, expression)| {
        let CoreKind::Call { callee, .. } = expression.kind else { return None; };
        matches!(&body.expression(callee).kind, CoreKind::Local(name) if name == "read")
            .then_some(CoreId(index as u32))
    }).unwrap();
    let summary = summaries.get(CallableBrand::Named(owner)).unwrap();
    let (site, evidence) = summary.invocation_evidence().find(|(site, _)|
        site.calls.is_empty() && site.location.expression == read).unwrap();
    assert!(matches!(evidence.coverage, ControlCallCoverage::Unknown(_)));
    assert!(!summary.call(site).only_returns_normally());
    assert!(!evidence.observed.is_empty());
    assert!(evidence.observed.iter().all(|path|
        path.guards.iter().any(|guard| matches!(guard, ControlGuard::InvocationReturned(_)))));
    let control = summaries.bind(&inputs).unwrap().body(owner).unwrap();
    let invocation = control.get(read).unwrap();
    assert!(invocation.unknown && invocation.normal);
    assert!(invocation.returns.iter().any(|payload|
        matches!(payload.source, payloads::PayloadSource::Capture { .. })));
    assert!(invocation.labels.is_empty() && invocation.transfers.is_empty());
    let facts = crate::core_continuations::CoreContinuations::derive_with_invocations(body, Some(control)).unwrap();
    assert!(!facts.is_abrupt(read), "known dependencies do not settle unknown control coverage");
}

#[test]
fn payload_projection_shares_explicit_and_captured_inputs_without_erasing_unknowns() {
    use crate::resident_invocations::{CapturedInputs, Inputs, Operand};
    type Value = (u32, Vec<u32>);
    struct Domain {
        unresolved: bool,
    }
    impl Inputs for Domain {
        type Value = Value;
        fn project(&self, value: &Value, path: &[u32]) -> Option<Value> {
            if path.contains(&99) {
                return None;
            }
            Some((value.0, value.1.iter().chain(path).copied().collect()))
        }
        fn captures(&self, _: &Operand<Value>) -> CapturedInputs<Value> {
            CapturedInputs {
                operands: vec![Operand {
                    ty: Type::Unit,
                    value: (2, vec![]),
                }],
                unresolved: self.unresolved,
            }
        }
    }
    let payload = InvocationPayload {
        ty: Type::Unit,
        source: payloads::PayloadSource::Aggregate(vec![
            InvocationPayload {
                ty: Type::Unit,
                source: payloads::PayloadSource::Argument {
                    index: 0,
                    path: vec![3],
                },
            },
            InvocationPayload {
                ty: Type::Unit,
                source: payloads::PayloadSource::Capture {
                    receiver_path: vec![],
                    callable_ty: Type::Unit,
                    resident_ty: Type::Unit,
                    path: vec![4],
                },
            },
        ]),
    };
    let receiver = (0, vec![]);
    let arguments = [(1, vec![])];
    let ResolvedPayload::Aggregate(fields) = resolve_payload(
        &payload,
        &receiver,
        &arguments,
        &Domain { unresolved: false },
    ) else {
        panic!("aggregate");
    };
    for (field, expected) in fields.into_iter().zip([(1, vec![3]), (2, vec![4])]) {
        let ResolvedPayload::Inputs { values, .. } = field else {
            panic!("represented input");
        };
        assert_eq!(values, vec![expected]);
    }
    let ResolvedPayload::Aggregate(fields) =
        resolve_payload(&payload, &receiver, &[], &Domain { unresolved: true })
    else {
        panic!("aggregate");
    };
    assert!(
        fields
            .iter()
            .all(|field| matches!(field, ResolvedPayload::Unknown(Type::Unit)))
    );
    let missing = InvocationPayload {
        ty: Type::Unit,
        source: payloads::PayloadSource::Argument {
            index: 0,
            path: vec![99],
        },
    };
    assert!(matches!(
        resolve_payload(
            &missing,
            &receiver,
            &arguments,
            &Domain { unresolved: false }
        ),
        ResolvedPayload::Unknown(Type::Unit)
    ));
}
