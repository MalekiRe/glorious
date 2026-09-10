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
        Self::control_input(source, false)
    }

    fn control_input(source: &str, pending: bool) -> Self {
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
            let body = TypedBody::elaborate_control_input(
                definition,
                &syntax,
                &index,
                &signatures,
                &fixities,
                crate::TraitSolver::new(&signatures),
                pending,
            );
            assert!(body.diagnostics.is_empty(), "{:?}", body.diagnostics);
            let validation = if pending { body.validate_for_control_fusion() } else { body.validate() };
            assert!(validation.is_empty(), "{validation:?}");
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
fn returned_factory_capability_requires_the_exact_checked_body_batch() {
    let fixture = Fixture::new("#![no_std]
        fn wrap(task:(i64) -> i64) -> () -> i64 { move (task) { task(42) } }
        fn main(task:(i64) -> i64) -> i64 { wrap(task)() }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries_with_check(&inputs, Default::default(),
        &mut |_, _| Ok::<_, ()>(())).unwrap();
    let bound = summaries.bind(&inputs).unwrap();
    let solver = crate::TraitSolver::new(&fixture.interface);
    let flows = fixture.bodies.iter().map(|(owner, body)| {
        let facts = crate::core_continuations::CoreContinuations::derive_with_invocations(body, bound.body(*owner)).unwrap();
        let flow = crate::PlaceFlow::analyze_with_frozen_solver(body, &fixture.interface, &[], &[], &solver,
            None, std::sync::Arc::new(facts));
        assert!(flow.diagnostics.is_empty(), "{:?}", flow.diagnostics);
        (*owner, flow)
    }).collect::<BTreeMap<_, _>>();
    let main = fixture.names["main"];
    let wrap = fixture.names["wrap"];
    let mut bodies = fixture.bodies.iter().map(|(owner, body)| (*owner,
        crate::useflow::UseBody { body, flow: &flows[owner] })).collect::<crate::useflow::UseBodies<'_>>();
    let analyze = |bodies: &crate::useflow::UseBodies<'_>| crate::UseFlow::analyze_with_bodies(
        &fixture.bodies[&main], &flows[&main], &fixture.interface, bodies);
    let uses = analyze(&bodies);
    assert!(uses.diagnostics.is_empty(), "{uses:#?}");
    assert!(uses.callable_uses.iter().any(|fact| fact.name == "task" && fact.actual == crate::Quantity::ONCE), "{uses:#?}");
    bodies.remove(&wrap);
    let missing = analyze(&bodies);
    assert!(missing.diagnostics.iter().any(|diagnostic| diagnostic.code == "G5013"), "{missing:#?}");
    let mut changed = fixture.bodies[&wrap].clone();
    let literal = changed.expressions.iter_mut().find(|expression|
        matches!(&expression.kind, CoreKind::Literal(value) if value == "42")).unwrap();
    literal.kind = CoreKind::Literal("43".into());
    bodies.insert(wrap, crate::useflow::UseBody { body: &changed, flow: &flows[&wrap] });
    let stale = analyze(&bodies);
    assert!(stale.diagnostics.iter().any(|diagnostic| diagnostic.code == "G5013"), "{stale:#?}");
}

#[test]
fn pending_control_is_sealed_and_discharged_before_ordinary_core() {
    let mut fixture = Fixture::control_input("#![no_std]
        pub fn main() -> i64 { @done: i64 { let task = () -> ! { @done(42) }; task() } }", true);
    let owner = fixture.names["main"];
    let inputs = fixture.inputs();
    assert!(!fixture.bodies[&owner].validate().is_empty());
    let summaries = derive_fusion_summaries_with_check(&inputs, Default::default(),
        &mut |_, _| Ok::<_, ()>(())).unwrap();
    let bound = summaries.bind(&inputs).unwrap();
    let body = &fixture.bodies[&owner];
    let flow = crate::PlaceFlow::analyze_with_interface(body, &fixture.interface);
    let escapes = crate::EscapeFlow::analyze_with_interface(body, &flow, &fixture.interface);
    let mut captures = crate::escape::ControlCaptures::default();
    captures.include(owner, body, &escapes).unwrap();
    let fused = crate::core::control_fusion::transform(owner, &bound, &captures).unwrap().unwrap();
    assert!(fused.validate().is_empty());
    assert!(crate::core::label_dependencies::LabelDependencies::derive(&fused.expressions)
        .unwrap().pending_closures(fused.root).unwrap().is_empty());
    // The transform accepts only the bound batch, never an independently
    // supplied body that could be paired with stale constructor authority.
    let body = fixture.bodies.get_mut(&owner).unwrap();
    let closure = body.expressions.iter_mut().find(|expression|
        matches!(expression.kind, CoreKind::Closure { .. })).unwrap();
    let Type::Callable { contract, .. } = &mut closure.ty else { panic!("closure type"); };
    contract.environment = Some(Box::new(Type::Unit));
    assert!(!body.validate_for_control_fusion().is_empty(), "pending labels must not excuse a forged environment");
    assert!(summaries.bind(&fixture.inputs()).is_err());
}

#[test]
fn resumption_capture_lifetime_authority_rejects_missing_invalid_and_stale_inputs() {
    let fixture = Fixture::control_input("#![no_std]
        effect Ask { [1,1] ask() -> i64; }
        pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => {
            let task = (value:i64) -> i64 { k(value) }; task(42)
        } } }", true);
    let owner = fixture.names["main"];
    let inputs = fixture.inputs();
    let summaries = derive_fusion_summaries_with_check(&inputs, Default::default(),
        &mut |_, _| Ok::<_, ()>(())).unwrap();
    let bound = summaries.bind(&inputs).unwrap();
    let body = &fixture.bodies[&owner];
    let flow = crate::PlaceFlow::analyze_with_interface(body, &fixture.interface);
    let escapes = crate::EscapeFlow::analyze_with_interface(body, &flow, &fixture.interface);
    let mut captures = crate::escape::ControlCaptures::default();
    assert!(crate::core::control_fusion::transform(owner, &bound, &captures).is_err());
    assert!(captures.include(owner, body, &crate::EscapeFlow::default()).is_err());
    captures.include(owner, body, &escapes).unwrap();
    assert_eq!(captures.bind(owner, body), Ok(true));
    assert!(crate::core::control_fusion::transform(owner, &bound, &captures).unwrap().is_some());
    let mut invalid = escapes.clone();
    invalid.diagnostics.push(crate::escape::EscapeDiagnostic {
        code: "G4174", span: body.expression(body.root).span, message: "invalid lifetime".into(),
    });
    assert!(captures.include(owner, body, &invalid).is_err());
    let mut stale = body.clone();
    stale.expressions[body.root.0 as usize].ty = Type::Never;
    assert!(captures.bind(owner, &stale).is_err());
    assert!(captures.include(owner, &stale, &escapes).is_err());
}

#[test]
fn resumption_handler_label_invocations_use_only_nominal_binder_authority() {
    let fixture = Fixture::new("#![no_std]
        effect Ask { [0,1] ask() -> i64; }
        pub fn main() -> i64 { @done: i64 {
            let alias = @done;
            handle Ask::ask() { Ask::ask() with k => alias(42) }
        } }");
    let owner = fixture.names["main"];
    let inputs = fixture.inputs();
    let summaries = derive_fusion_summaries_with_check(&inputs, Default::default(),
        &mut |_, _| Ok::<_, ()>(())).unwrap();
    let bound = summaries.bind(&inputs).unwrap();
    let body = &fixture.bodies[&owner];
    let call = body.expressions.iter().find(|expression| matches!(&expression.kind,
        CoreKind::Call { callee, .. } if matches!(&body.expression(*callee).kind,
            CoreKind::Local(name) if name == "alias"))).unwrap();
    let labels = crate::core::label_dependencies::LabelDependencies::derive(&body.expressions).unwrap();
    let control = bound.declared_call_control(body, call, &labels).unwrap();
    assert!(!control.unknown);
    assert_eq!(control.direct_labels.len(), 1);
    assert!(matches!(control.transfers[0].payload.source,
        payloads::PayloadSource::Argument { index: 0, ref path } if path.is_empty()));
    let CoreKind::Call { callee, .. } = call.kind else { unreachable!() };
    let mut unbranded = body.clone();
    unbranded.expressions[callee.0 as usize].ty = crate::types::label::callable(
        &body.expression(callee).ty).unwrap();
    assert!(bound.declared_call_control(&unbranded, call, &labels).is_none(),
        "an ordinary bottom callable cannot acquire the nominal destination");
    unbranded.expressions[callee.0 as usize].ty = crate::types::label::new(
        crate::LabelBrand { owner, label: u32::MAX }, Type::Scalar(crate::ScalarType::I64));
    assert!(bound.declared_call_control(&unbranded, call, &labels).is_none(),
        "a different nominal identity cannot acquire this binder's destination");
}

#[test]
fn captured_payload_reborrows_require_storage_identity_not_equal_contents() {
    for (payload, reborrow) in [
        ("@done(&value)", true),
        ("let reference = &value; let copied = *reference; @done(&copied)", false),
    ] {
        let fixture = Fixture::control_input(&format!("#![no_std]
            pub fn main() -> i64 {{ let value = 42;
                let result = @done: &i64 {{ let task = () -> ! {{ {payload} }}; task() }};
                *result
            }}"), true);
        let owner = fixture.names["main"];
        let inputs = fixture.inputs();
        let summaries = derive_fusion_summaries_with_check(&inputs, Default::default(), &mut |_, _| Ok::<_, ()>(())).unwrap();
        let bound = summaries.bind(&inputs).unwrap();
        let body = &fixture.bodies[&owner];
        let call = body.expressions.iter().enumerate().find_map(|(index, expression)| {
            let CoreKind::Call { callee, .. } = expression.kind else { return None; };
            matches!(&body.expression(callee).kind, CoreKind::Local(name) if name == "task")
                .then_some(CoreId(index as u32))
        }).unwrap();
        let control = bound.body(owner).unwrap();
        let transfer = &control.get(call).unwrap().transfers[0];
        if reborrow {
            assert!(matches!(transfer.payload.source, payloads::PayloadSource::Reborrow { .. }), "{transfer:?}");
        } else {
            assert!(matches!(transfer.payload.source, payloads::PayloadSource::Unknown), "a copied scalar is not the captured loan: {transfer:?}");
        }
    }
}

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
fn borrowed_invocation_events_keep_the_evaluated_receiver_projection() {
    let fixture = Fixture::new("#![no_std] fn main() -> i64 {
        let value = 42; let reference = &value;
        let task = move (reference) { reference };
        let result = (&task)(); *result
    }");
    let inputs = fixture.inputs();
    let summaries = derive_control_summaries(&inputs, Default::default());
    let bound = summaries.bind(&inputs).unwrap();
    let owner = fixture.names["main"];
    let body = &fixture.bodies[&owner];
    let call = body.expressions.iter().enumerate().find_map(|(index, expression)|
        matches!(expression.kind, CoreKind::Call { .. }).then_some(CoreId(index as u32))).unwrap();
    let control = bound.body(owner).unwrap();
    let invocation = control.get(call).unwrap();
    assert!(invocation.normal && !invocation.unknown);
    assert!(matches!(&invocation.returns[0].source, payloads::PayloadSource::Capture { receiver_path, .. }
        if receiver_path == &[crate::core::REFERENCE_PATH_DEREF]));
    assert!(summaries.get(CallableBrand::Named(owner)).unwrap().alternatives.iter()
        .flat_map(|path| &path.events).any(|event| matches!(event, ControlEvent::Invoke {
            callee: ControlValue { shape: ControlValueShape::Borrow(_), .. }, ..
        })));
    assert!(matches!(bound.fusion_target(CallableBrand::Named(owner), &[], CallableBrand::Named(owner), call),
        Some(FusionTarget::Callable { brand: CallableBrand::Closure(_), .. })),
        "code selection must use the invocation view without erasing the receiver input");
}

#[test]
fn payload_projection_shares_explicit_and_captured_inputs_without_erasing_unknowns() {
    use crate::resident_invocations::{CapturedInputs, Inputs, Operand};
    type Value = (u32, Vec<u32>);
    struct Domain {
        unresolved: bool,
    }
    impl PayloadInputs for Domain {
        type Value = Value;
        fn project(&self, value: &Value, path: &[u32]) -> Option<Value> { Inputs::project(self, value, path) }
        fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> { Inputs::captures(self, callable) }
        fn reborrow(&self, value: &Value, fields: &[u32]) -> Option<Value> {
            Inputs::project(self, value, fields)
        }
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

#[test]
fn returned_reference_coverage_requires_every_path_and_authenticated_input() {
    use crate::resident_invocations::{CapturedInputs, Operand};
    struct Domain { capture_known: bool, reference_known: bool }
    impl PayloadInputs for Domain {
        type Value = ();
        fn project(&self, _: &(), path: &[u32]) -> Option<()> { (!path.contains(&99)).then_some(()) }
        fn captures(&self, _: &Operand<()>) -> CapturedInputs<()> {
            CapturedInputs { operands: vec![Operand { ty: Type::Unit, value: () }], unresolved: !self.capture_known }
        }
        fn reborrow(&self, _: &(), _: &[u32]) -> Option<()> { Some(()) }
    }
    impl ReferenceInputs for Domain {
        fn reference_known(&self, _: &()) -> bool { self.reference_known }
    }
    let signatures = ElaboratedInterface::default();
    let reference = Type::Reference { mutability: crate::Mutability::Shared,
        lifetime: crate::Lifetime::Elided, referent: Box::new(Type::Unit) };
    let capture = InvocationPayload { ty: reference.clone(), source: payloads::PayloadSource::Capture {
        receiver_path: vec![], callable_ty: Type::Unit, resident_ty: Type::Unit, path: vec![],
    } };
    let argument = InvocationPayload { ty: reference.clone(), source: payloads::PayloadSource::Argument { index: 0, path: vec![] } };
    let result = Type::Tuple(vec![reference.clone(), reference.clone()]);
    let mut control = InvocationControl { normal: true, returns: vec![InvocationPayload {
        ty: result.clone(), source: payloads::PayloadSource::Aggregate(vec![capture.clone(), argument]),
    }], ..Default::default() };
    let domain = Domain { capture_known: true, reference_known: true };
    assert!(control.resolve_returns(&result, &signatures, &(), &[()], &domain).references_complete);
    control.unknown = true;
    let partial = control.resolve_returns(&result, &signatures, &(), &[()], &domain);
    assert!(!partial.references_complete);
    assert_eq!(partial.payloads.len(), 1, "positive dependencies survive a coverage gap");
    control.unknown = false;
    for incomplete in [Domain { capture_known: false, reference_known: true },
        Domain { capture_known: true, reference_known: false }] {
        assert!(!control.resolve_returns(&result, &signatures, &(), &[()], &incomplete).references_complete);
    }
    assert!(!control.resolve_returns(&result, &signatures, &(), &[], &domain).references_complete);
    control.returns.push(InvocationPayload::unknown(result.clone()));
    assert!(!control.resolve_returns(&result, &signatures, &(), &[()], &domain).references_complete);
    control.returns = vec![capture];
    control.returns[0].ty = Type::Unit;
    assert!(!control.resolve_returns(&reference, &signatures, &(), &[], &domain).references_complete);
    control.returns[0].ty = reference.clone();
    let payloads::PayloadSource::Capture { path, .. } = &mut control.returns[0].source else { unreachable!() };
    path.push(99);
    assert!(!control.resolve_returns(&reference, &signatures, &(), &[], &domain).references_complete);
    control.returns.clear();
    assert!(!control.resolve_returns(&reference, &signatures, &(), &[], &domain).references_complete);
}
