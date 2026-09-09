use grandiose_stage0::callable_control::*;
use grandiose_stage0::{
    BodySyntax, CallableBrand, CallableSignature, CoreKind, DeclarationScan, DefKey,
    DefinitionIndex, ElaboratedHeader, ElaboratedInterface, FileKey, FixityTable, InterfaceSet,
    LexedFile, PackageKey, TypedBody,
};
use std::collections::BTreeMap;

struct Fixture {
    bodies: BTreeMap<DefKey, TypedBody>,
    signatures: BTreeMap<DefKey, CallableSignature>,
    names: BTreeMap<String, DefKey>,
    interface: ElaboratedInterface,
}
impl Fixture {
    fn new(source: &str) -> Self {
        let package = PackageKey("callable-control@1".into());
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
        let mut fixture = Self {
            bodies: BTreeMap::new(),
            signatures: BTreeMap::new(),
            names: BTreeMap::new(),
            interface: signatures.clone(),
        };
        for definition in &interface.definitions {
            let Some(ElaboratedHeader::Callable(signature)) =
                signatures.definitions.get(&definition.key)
            else {
                continue;
            };
            fixture
                .names
                .insert(definition.name.clone().unwrap(), definition.key);
            fixture.signatures.insert(definition.key, signature.clone());
            let Some(range) = definition.body else {
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
            assert!(
                body.diagnostics.is_empty(),
                "{}: {:?}",
                definition.name.as_deref().unwrap(),
                body.diagnostics
            );
            assert!(body.validate().is_empty(), "{:?}", body.validate());
            fixture.bodies.insert(definition.key, body);
        }
        fixture
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
    fn derive(&self) -> ControlSummarySet {
        derive_control_summaries(&self.inputs(), ControlSummaryLimits::default())
    }
    fn get<'a>(&self, summaries: &'a ControlSummarySet, name: &str) -> &'a CallableControlSummary {
        summaries
            .get(CallableBrand::Named(self.names[name]))
            .unwrap()
    }
}
fn exits(summary: &CallableControlSummary) -> usize {
    summary
        .alternatives()
        .iter()
        .filter(|path| matches!(path.outcome, ControlOutcome::LabelExit { .. }))
        .count()
}
fn returns(summary: &CallableControlSummary) -> usize {
    summary
        .alternatives()
        .iter()
        .filter(|path| matches!(path.outcome, ControlOutcome::Return(_)))
        .count()
}
fn symbolic_invocations(path: &ControlAlternative) -> Vec<ControlOrigin> {
    path.events
        .iter()
        .filter_map(|event| match event {
            ControlEvent::Invoke {
                callee:
                    ControlValue {
                        origin,
                        shape: ControlValueShape::Unknown,
                        ..
                    },
                ..
            } => Some(origin.clone()),
            _ => None,
        })
        .collect()
}

#[test]
fn maybe_exits_or_returns_but_unused_label_only_returns() {
    let fixture = Fixture::new(
        r#"
        enum Flag { Yes, No }
        fn maybe<L>(flag: Flag, exit: L) where L: Label<i64> {
            handle flag { Flag::Yes => exit(42), Flag::No => () }
        }
        fn ignore_label<L>(exit: L) where L: Label<i64> {}
        fn send<T,L>(value: T, exit: L) -> ! where L: Label<T> { exit(value) }
    "#,
    );
    let summaries = fixture.derive();
    let maybe = fixture.get(&summaries, "maybe");
    assert!(maybe.is_complete(), "{maybe:#?}");
    assert_eq!((exits(maybe), returns(maybe)), (1, 1), "{maybe:#?}");
    assert!(!maybe.only_returns_normally());
    assert!(
        maybe
            .alternatives()
            .iter()
            .all(|path| path.guards.iter().all(|guard| matches!(
                guard,
                ControlGuard::Pattern {
                    subject: ControlOrigin::Parameter(0),
                    ..
                }
            )))
    );
    assert!(
        fixture
            .get(&summaries, "ignore_label")
            .only_returns_normally()
    );
    let send = fixture.get(&summaries, "send");
    assert_eq!((exits(send), returns(send)), (1, 0));
    assert!(matches!(
        &send.alternatives()[0].outcome,
        ControlOutcome::LabelExit {
            target: ControlLabelTarget::Symbolic(ControlOrigin::Parameter(1)),
            value: ControlValue {
                origin: ControlOrigin::Parameter(0),
                ..
            }
        }
    ));
}

#[test]
fn label_aliases_and_generic_helper_forwarding_preserve_actual_destination() {
    let fixture = Fixture::new(
        r#"
        fn send<T,L>(value: T, exit: L) -> ! where L: Label<T> { let alias = exit; alias(value) }
        fn forward<L>(exit: L) -> ! where L: Label<i64> { let renamed = exit; send(42, renamed) }
        fn main() -> i64 { label done { forward(@done) } }
    "#,
    );
    let summaries = fixture.derive();
    let forward = fixture.get(&summaries, "forward");
    assert_eq!(exits(forward), 1, "{forward:#?}");
    assert!(matches!(
        &forward.alternatives()[0].outcome,
        ControlOutcome::LabelExit {
            target: ControlLabelTarget::Symbolic(ControlOrigin::Parameter(0)),
            ..
        }
    ));
    assert!(
        fixture.get(&summaries, "main").only_returns_normally(),
        "{:#?}",
        fixture.get(&summaries, "main")
    );
}

#[test]
fn ordinary_never_callback_is_not_a_label_but_actual_label_resolves_it() {
    let fixture = Fixture::new(
        r#"
        fn invoke<F>(callback: F) -> ! where F: Fn<(i64,), Output=!, Effects={}> { callback(42) }
        fn main() -> i64 { label done { invoke(@done) } }
    "#,
    );
    let summaries = fixture.derive();
    let invoke = fixture.get(&summaries, "invoke");
    assert_eq!(exits(invoke), 0);
    assert!(
        matches!(
            invoke.alternatives()[0].outcome,
            ControlOutcome::UnresolvedInvocation(_)
        ),
        "{invoke:#?}"
    );
    assert!(!invoke.is_complete());
    assert!(
        fixture.get(&summaries, "main").only_returns_normally(),
        "{:#?}",
        fixture.get(&summaries, "main")
    );
}

#[test]
fn structural_alternatives_retain_order_multiplicity_and_conditional_normal_edges() {
    let fixture = Fixture::new(
        r#"
        enum Flag { Yes, No }
        fn ordered(flag: Flag, first: () -> (), second: () -> ()) {
            handle flag { Flag::Yes => { first(); second(); first(); }, Flag::No => second() }
        }
    "#,
    );
    let summaries = fixture.derive();
    let ordered = fixture.get(&summaries, "ordered");
    let normal: Vec<_> = ordered
        .alternatives()
        .iter()
        .filter(|path| matches!(path.outcome, ControlOutcome::Return(_)))
        .collect();
    assert_eq!(normal.len(), 2, "{ordered:#?}");
    assert_eq!(
        symbolic_invocations(normal[0]),
        vec![
            ControlOrigin::Parameter(1),
            ControlOrigin::Parameter(2),
            ControlOrigin::Parameter(1)
        ]
    );
    assert_eq!(
        symbolic_invocations(normal[1]),
        vec![ControlOrigin::Parameter(2)]
    );
    assert_eq!(
        normal[0]
            .guards
            .iter()
            .filter(|guard| matches!(guard, ControlGuard::InvocationReturned(_)))
            .count(),
        3
    );
    assert!(!ordered.only_returns_normally());
}

#[test]
fn actual_result_guards_follow_aliases_and_do_not_follow_similar_results() {
    let fixture = Fixture::new(
        r#"
        enum Result { Accepted, Rejected }
        fn alias(result: Result, callback: () -> ()) {
            let saved = result;
            handle saved { Result::Accepted => {
                handle result { Result::Accepted => callback(), Result::Rejected => () }
            }, Result::Rejected => () }
        }
        fn independent(first: Result, second: Result, callback: () -> ()) {
            handle first { Result::Accepted => {
                handle second { Result::Accepted => callback(), Result::Rejected => () }
            }, Result::Rejected => () }
        }
    "#,
    );
    let summaries = fixture.derive();
    let alias = fixture.get(&summaries, "alias");
    let independent = fixture.get(&summaries, "independent");
    assert_eq!(returns(alias), 2, "{alias:#?}");
    assert_eq!(returns(independent), 3, "{independent:#?}");
    assert!(
        independent
            .alternatives()
            .iter()
            .any(|path| path.guards.iter().any(|guard| matches!(
                guard,
                ControlGuard::Pattern {
                    subject: ControlOrigin::Parameter(1),
                    ..
                }
            )))
    );
}

#[test]
fn repeated_helper_evaluations_rebase_produced_result_guards() {
    let fixture = Fixture::new(
        r#"
        enum Result { Accepted, Rejected }
        fn run(callback: () -> Result) -> Result { callback() }
        fn main(callback: () -> Result) {
            let first = run(callback);
            let second = run(callback);
            handle first { Result::Accepted => {
                handle second { Result::Accepted => (), Result::Rejected => () }
            }, Result::Rejected => () }
        }
    "#,
    );
    let summaries = fixture.derive();
    let main = fixture.get(&summaries, "main");
    let path = main
        .alternatives()
        .iter()
        .find(|path| {
            matches!(path.outcome, ControlOutcome::Return(_))
                && path
                    .guards
                    .iter()
                    .filter(|guard| matches!(guard, ControlGuard::Pattern { .. }))
                    .count()
                    == 2
        })
        .unwrap();
    let subjects: Vec<_> = path
        .guards
        .iter()
        .filter_map(|guard| match guard {
            ControlGuard::Pattern { subject, .. } => Some(subject),
            _ => None,
        })
        .collect();
    assert_ne!(subjects[0], subjects[1], "{main:#?}");
    let (ControlOrigin::Produced(first), ControlOrigin::Produced(second)) =
        (subjects[0], subjects[1])
    else {
        panic!("produced helper results")
    };
    assert_eq!(first.location.callable, second.location.callable);
    assert_eq!(first.location.expression, second.location.expression);
    assert_ne!(first.calls, second.calls);
}

#[test]
fn captured_symbolic_label_and_actual_closure_invocation_remain_branded() {
    let fixture = Fixture::new(
        r#"
        fn captured<L>(exit: L) -> ! where L: Label<i64> { let callback = () -> ! { exit(42) }; callback() }
        fn main() -> i64 { label done { captured(@done) } }
    "#,
    );
    let summaries = fixture.derive();
    let closure = summaries
        .iter()
        .find(|(brand, _)| matches!(brand, CallableBrand::Closure(_)))
        .unwrap()
        .1;
    assert!(
        matches!(
            &closure.alternatives()[0].outcome,
            ControlOutcome::LabelExit {
                target: ControlLabelTarget::Symbolic(ControlOrigin::Capture(0)),
                ..
            }
        ),
        "{closure:#?}"
    );
    assert_eq!(exits(fixture.get(&summaries, "captured")), 1);
    assert!(fixture.get(&summaries, "main").only_returns_normally());
}

#[test]
fn missing_bodies_and_recursive_label_cycles_are_explicitly_unknown() {
    let mut fixture = Fixture::new(
        r#"
        fn recurse<L>(exit: L) -> ! where L: Label<i64> { recurse(exit) }
        fn ignored<L>(exit: L) where L: Label<i64> {}
        fn caller<L>(exit: L) where L: Label<i64> { ignored(exit) }
    "#,
    );
    fixture.bodies.remove(&fixture.names["ignored"]);
    let summaries = fixture.derive();
    assert!(matches!(
        fixture.get(&summaries, "recurse").alternatives()[0].outcome,
        ControlOutcome::Unknown(ControlUnknown::RecursiveCall(_))
    ));
    assert!(matches!(
        fixture.get(&summaries, "caller").alternatives()[0].outcome,
        ControlOutcome::Unknown(ControlUnknown::MissingBody(_))
    ));
}

#[test]
fn summary_seals_reject_changed_body_contract_dependency_and_malformed_core() {
    let mut fixture = Fixture::new("fn helper() -> i64 { 42 } fn main() -> i64 { helper() }");
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    assert!(summary.matches(&fixture.inputs()));
    let helper = fixture.names["helper"];
    let saved = fixture.bodies[&helper].clone();
    fixture
        .bodies
        .get_mut(&helper)
        .unwrap()
        .expressions
        .iter_mut()
        .find(|expr| matches!(expr.kind, CoreKind::Literal(_)))
        .unwrap()
        .kind = CoreKind::Literal("43".into());
    assert!(!summary.matches(&fixture.inputs()));
    fixture.bodies.insert(helper, saved);
    fixture.signatures.get_mut(&helper).unwrap().result = grandiose_stage0::Type::Unit;
    assert!(!summary.matches(&fixture.inputs()));
    let altered = fixture.derive();
    assert!(!fixture.get(&altered, "main").only_returns_normally());
    fixture.bodies.get_mut(&helper).unwrap().root = grandiose_stage0::CoreId(u32::MAX);
    let malformed = fixture.derive();
    assert!(matches!(
        fixture.get(&malformed, "helper").alternatives()[0].outcome,
        ControlOutcome::Unknown(ControlUnknown::InvalidCore(_))
    ));
}

#[test]
fn limiting_analysis_never_turns_omitted_paths_into_a_no_exit_proof() {
    let fixture = Fixture::new(
        r#"
        enum Flag { Yes, No }
        fn maybe<L>(flag: Flag, exit: L) where L: Label<i64> {
            handle flag { Flag::Yes => (), Flag::No => exit(42) }
        }
    "#,
    );
    for limits in [
        ControlSummaryLimits {
            max_steps: 1,
            ..Default::default()
        },
        ControlSummaryLimits {
            max_alternatives: 1,
            ..Default::default()
        },
    ] {
        let summaries = derive_control_summaries(&fixture.inputs(), limits);
        let summary = fixture.get(&summaries, "maybe");
        assert!(!summary.only_returns_normally());
        assert!(
            summary
                .alternatives()
                .iter()
                .any(|path| matches!(path.outcome, ControlOutcome::Unknown(ControlUnknown::Limit)))
        );
    }
}

#[test]
fn familiar_function_names_have_no_control_authority() {
    let fixture = Fixture::new(
        r#"
        fn send<L>(exit: L) where L: Label<i64> {}
        fn ignore_label<L>(exit: L) -> ! where L: Label<i64> { exit(42) }
    "#,
    );
    let summaries = fixture.derive();
    assert!(fixture.get(&summaries, "send").only_returns_normally());
    assert_eq!(exits(fixture.get(&summaries, "ignore_label")), 1);
}

#[test]
fn returned_structural_case_retains_its_corresponding_callback_trace() {
    let fixture = Fixture::new(
        r#"
        enum Flag { Yes, No }
        enum Verdict { Ran, Skipped }
        fn decide(flag: Flag, callback: () -> ()) -> Verdict {
            handle flag { Flag::Yes => { callback(); Verdict::Ran }, Flag::No => Verdict::Skipped }
        }
        fn main(flag: Flag, callback: () -> ()) -> i64 {
            let actual_result = decide(flag, callback);
            let alias = actual_result;
            handle alias { Verdict::Ran => 42, Verdict::Skipped => 0 }
        }
    "#,
    );
    let summaries = fixture.derive();
    let decide = fixture.get(&summaries, "decide");
    let normal: Vec<_> = decide
        .alternatives()
        .iter()
        .filter(|path| matches!(path.outcome, ControlOutcome::Return(_)))
        .collect();
    assert_eq!(normal.len(), 2);
    assert!(matches!(
        normal[0].outcome,
        ControlOutcome::Return(ControlValue {
            shape: ControlValueShape::Enum { variant: 0, .. },
            ..
        })
    ));
    assert_eq!(
        symbolic_invocations(normal[0]),
        vec![ControlOrigin::Parameter(1)]
    );
    assert!(matches!(
        normal[1].outcome,
        ControlOutcome::Return(ControlValue {
            shape: ControlValueShape::Enum { variant: 1, .. },
            ..
        })
    ));
    assert!(symbolic_invocations(normal[1]).is_empty());
    for path in fixture.get(&summaries, "main").alternatives() {
        if let ControlOutcome::Return(ControlValue {
            shape: ControlValueShape::Literal(value),
            ..
        }) = &path.outcome
        {
            assert_eq!(!symbolic_invocations(path).is_empty(), value == "42");
        }
    }
}

#[test]
fn named_generic_composition_instantiates_returned_types_and_guard_layouts() {
    let fixture = Fixture::new(
        r#"
        enum Boxed<T> { Item(T), Empty }
        fn inspect<T>(value: Boxed<T>) -> i64 {
            handle value { Boxed::Item(_) => 42, Boxed::Empty => 0 }
        }
        fn wrap<T>(value: T) -> Boxed<T> { Boxed::Item(value) }
        fn main(value: Boxed<i64>) -> i64 { inspect(value) }
        fn result() -> Boxed<i64> { wrap(42) }
    "#,
    );
    let summaries = fixture.derive();
    let main = fixture.get(&summaries, "main");
    assert!(main.only_returns_normally(), "{main:#?}");
    assert!(main.alternatives().iter().flat_map(|path| &path.guards).any(|guard|
        matches!(guard, ControlGuard::Pattern { pattern: grandiose_stage0::CorePattern::Enum { field_types, .. }, .. }
            if field_types == &[grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64)])));
    let result = fixture.get(&summaries, "result");
    assert!(
        matches!(&result.alternatives()[0].outcome, ControlOutcome::Return(ControlValue {
        ty: grandiose_stage0::Type::Nominal { arguments, .. }, ..
    }) if arguments == &[grandiose_stage0::GenericArgument::Type(grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64))]),
        "{result:#?}"
    );
}

#[test]
fn shared_core_call_nodes_do_not_alias_distinct_evaluated_results() {
    let mut fixture = Fixture::new(
        r#"
        enum Result { Accepted, Rejected }
        fn main(callback: () -> Result) {
            let first = callback();
            let second = callback();
            handle first { Result::Accepted => {
                handle second { Result::Accepted => (), Result::Rejected => () }
            }, Result::Rejected => () }
        }
    "#,
    );
    let body = fixture.bodies.get_mut(&fixture.names["main"]).unwrap();
    let first = body
        .expressions
        .iter()
        .find_map(|expr| match &expr.kind {
            CoreKind::Let { name, value } if name == "first" => Some(*value),
            _ => None,
        })
        .unwrap();
    for expr in &mut body.expressions {
        if let CoreKind::Let { name, value } = &mut expr.kind {
            if name == "second" {
                *value = first;
            }
        }
    }
    assert!(body.validate().is_empty());
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    let path = summary
        .alternatives()
        .iter()
        .find(|path| {
            matches!(path.outcome, ControlOutcome::Return(_))
                && path
                    .guards
                    .iter()
                    .filter(|guard| matches!(guard, ControlGuard::Pattern { .. }))
                    .count()
                    == 2
        })
        .unwrap();
    let subjects: Vec<_> = path
        .guards
        .iter()
        .filter_map(|guard| match guard {
            ControlGuard::Pattern { subject, .. } => Some(subject),
            _ => None,
        })
        .collect();
    let (ControlOrigin::Produced(first), ControlOrigin::Produced(second)) =
        (subjects[0], subjects[1])
    else {
        panic!("callback results")
    };
    assert_eq!(first.location.expression, second.location.expression);
    assert_ne!(first.location.occurrence, second.location.occurrence);
    assert_ne!(subjects[0], subjects[1]);
}

#[test]
fn enum_coverage_and_interface_identity_are_checked_independently() {
    let mut fixture = Fixture::new(
        r#"
        enum Flag { Yes, No }
        fn main(flag: Flag) { handle flag { Flag::Yes => (), Flag::No => () } }
    "#,
    );
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    assert!(summary.only_returns_normally());
    assert!(summary.matches(&fixture.inputs()));
    let saved_interface = fixture.interface.clone();
    fixture.interface.pattern_values.insert(
        fixture.names["main"],
        (
            grandiose_stage0::Type::Unit,
            grandiose_stage0::PatternDecision::Any,
        ),
    );
    assert!(!summary.matches(&fixture.inputs()));
    fixture.interface = saved_interface;
    let body = fixture.bodies.get_mut(&fixture.names["main"]).unwrap();
    for expr in &mut body.expressions {
        if let CoreKind::Completion { clauses, .. } = &mut expr.kind {
            clauses.pop();
        }
    }
    assert!(
        body.validate().is_empty(),
        "Core's generic graph validator is not a coverage certificate"
    );
    let malformed = fixture.derive();
    let summary = fixture.get(&malformed, "main");
    assert!(!summary.only_returns_normally());
    assert!(summary.alternatives().iter().any(|path| matches!(
        path.outcome,
        ControlOutcome::Unknown(ControlUnknown::Unsupported("uncovered completion"))
    )));
}

#[test]
fn concrete_label_capture_resolves_at_closure_creation_and_call() {
    let fixture = Fixture::new(
        r#"
        fn main() -> i64 { label done { let exit = @done; let callback = () -> ! { exit(42) }; callback() } }
    "#,
    );
    let summaries = fixture.derive();
    assert!(
        fixture.get(&summaries, "main").only_returns_normally(),
        "{:#?}",
        fixture.get(&summaries, "main")
    );
    let closure = summaries
        .iter()
        .find(|(brand, _)| matches!(brand, CallableBrand::Closure(_)))
        .unwrap()
        .1;
    // The erased callable ABI is not itself a Label certificate; the actual
    // capture binding in the creating activation supplies that information.
    assert!(!closure.is_complete());
    assert!(matches!(
        closure.alternatives()[0].outcome,
        ControlOutcome::UnresolvedInvocation(_)
    ));
}

#[test]
fn terminal_operation_and_unsupported_handler_are_not_normal_completions() {
    let fixture = Fixture::new(
        r#"
        effect Halt { stop() -> !; }
        fn terminal() -> ! / {Halt} { Halt::stop() }
        fn handled() { handle Halt::stop() { Halt::stop() => () } }
    "#,
    );
    let summaries = fixture.derive();
    assert!(matches!(
        fixture.get(&summaries, "terminal").alternatives()[0].outcome,
        ControlOutcome::TerminalOperation { .. }
    ));
    assert!(matches!(
        fixture.get(&summaries, "handled").alternatives()[0].outcome,
        ControlOutcome::Unknown(ControlUnknown::Unsupported("operation handler"))
    ));
}

#[test]
fn forged_cyclic_core_is_unknown_instead_of_recursive_analysis() {
    let mut fixture = Fixture::new("fn main() {}");
    let body = fixture.bodies.get_mut(&fixture.names["main"]).unwrap();
    body.expressions[body.root.0 as usize].kind = CoreKind::Block(vec![body.root]);
    let summaries = fixture.derive();
    assert!(matches!(
        fixture.get(&summaries, "main").alternatives()[0].outcome,
        ControlOutcome::Unknown(ControlUnknown::InvalidCore(_))
    ));
}

#[test]
fn alternate_literal_spellings_cannot_hide_a_label_exit() {
    let fixture = Fixture::new(
        r#"
        fn main<L>(exit: L) where L: Label<i64> {
            handle 0x2a { 42 => exit(42), _ => () }
        }
    "#,
    );
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    assert_eq!((exits(summary), returns(summary)), (1, 0), "{summary:#?}");
}

#[test]
fn lawful_callable_result_erasure_does_not_erase_the_returned_body_identity() {
    let fixture = Fixture::new(
        r#"
        fn answer() -> i64 { 42 }
        fn make() -> () -> i64 { answer }
        fn main() -> i64 { let callback = make(); callback() }
    "#,
    );
    let summaries = fixture.derive();
    assert!(
        fixture.get(&summaries, "make").only_returns_normally(),
        "{:#?}",
        fixture.get(&summaries, "make")
    );
    assert!(
        fixture.get(&summaries, "main").only_returns_normally(),
        "{:#?}",
        fixture.get(&summaries, "main")
    );
    assert!(
        matches!(&fixture.get(&summaries, "make").alternatives()[0].outcome,
        ControlOutcome::Return(ControlValue { shape: ControlValueShape::Callable { brand: CallableBrand::Named(key), .. }, .. }) if *key == fixture.names["answer"])
    );
}

fn permits_variants(path: &ControlAlternative, variants: &[u32]) -> bool {
    path.guards.iter().all(|guard| match guard {
        ControlGuard::Pattern {
            subject: ControlOrigin::Parameter(index),
            pattern: grandiose_stage0::CorePattern::Enum { variant, .. },
            matches,
        } => (variants[*index as usize] == *variant) == *matches,
        _ => true,
    })
}

#[test]
fn truncated_control_alternatives_keep_an_unknown_after_any_guard_specialization() {
    let fixture = Fixture::new(
        r#"
        enum Choice { First, Second, Third }
        fn main<L>(choice: Choice, exit: L) where L: Label<i64> {
            handle choice {
                Choice::First => (),
                Choice::Second => exit(2),
                Choice::Third => exit(3)
            }
        }
    "#,
    );
    let summaries = derive_control_summaries(
        &fixture.inputs(),
        ControlSummaryLimits {
            max_alternatives: 1,
            ..Default::default()
        },
    );
    let summary = fixture.get(&summaries, "main");
    assert_eq!(summary.alternatives().len(), 1);
    let witness = &summary.alternatives()[0];
    assert!(matches!(
        witness.outcome,
        ControlOutcome::Unknown(ControlUnknown::Limit)
    ));
    assert!(
        witness.guards.is_empty(),
        "one omitted branch must not guard all omitted branches"
    );
    assert!(
        witness.events.is_empty(),
        "one omitted branch's invocation trace is not universal"
    );
    for variant in 0..3 {
        assert!(
            summary
                .alternatives()
                .iter()
                .any(|path| permits_variants(path, &[variant])
                    && matches!(path.outcome, ControlOutcome::Unknown(ControlUnknown::Limit)))
        );
    }
}

#[test]
fn truncated_argument_products_cover_every_dropped_combination() {
    let fixture = Fixture::new(
        r#"
        enum Choice { First, Second }
        fn identity(value: i64) -> i64 { value }
        fn main(left: Choice, right: Choice) -> (i64, i64) {
            (
                handle left { Choice::First => identity(1), Choice::Second => identity(2) },
                handle right { Choice::First => identity(3), Choice::Second => identity(4) }
            )
        }
    "#,
    );
    let complete = fixture.derive();
    assert_eq!(returns(fixture.get(&complete, "main")), 4);
    let summaries = derive_control_summaries(
        &fixture.inputs(),
        ControlSummaryLimits {
            max_alternatives: 2,
            ..Default::default()
        },
    );
    let summary = fixture.get(&summaries, "main");
    assert_eq!(summary.alternatives().len(), 2);
    let witness = summary
        .alternatives()
        .iter()
        .find(|path| matches!(path.outcome, ControlOutcome::Unknown(ControlUnknown::Limit)))
        .unwrap();
    assert!(witness.guards.is_empty());
    assert!(witness.events.is_empty());
    for left in 0..2 {
        for right in 0..2 {
            assert!(
                summary
                    .alternatives()
                    .iter()
                    .any(|path| permits_variants(path, &[left, right])
                        && matches!(path.outcome, ControlOutcome::Unknown(ControlUnknown::Limit))),
                "specializing to ({left}, {right}) must not remove the omitted alternatives"
            );
        }
    }
}

#[test]
fn repeated_label_arena_evaluations_mint_distinct_activation_targets() {
    let mut fixture = Fixture::new(
        r#"
        fn main() -> i64 {
            let first = label first_label { @first_label(42) };
            let second = label second_label { @second_label(42) };
            second
        }
    "#,
    );
    let body = fixture.bodies.get_mut(&fixture.names["main"]).unwrap();
    let first = body
        .expressions
        .iter()
        .find_map(|expr| match &expr.kind {
            CoreKind::Let { name, value } if name == "first" => Some(*value),
            _ => None,
        })
        .unwrap();
    for expr in &mut body.expressions {
        if let CoreKind::Let { name, value } = &mut expr.kind {
            if name == "second" {
                *value = first;
            }
        }
    }
    assert!(body.validate().is_empty());
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    assert!(summary.only_returns_normally(), "{summary:#?}");
    let targets = summary.alternatives()[0]
        .events
        .iter()
        .filter_map(|event| match event {
            ControlEvent::Transfer { target, .. } => Some(target),
            ControlEvent::Invoke {
                callee:
                    ControlValue {
                        shape: ControlValueShape::Label(target),
                        ..
                    },
                ..
            } => Some(target),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(targets.len(), 2);
    let (
        ControlLabelTarget::Lexical {
            brand: first_brand,
            activation: first_activation,
        },
        ControlLabelTarget::Lexical {
            brand: second_brand,
            activation: second_activation,
        },
    ) = (targets[0], targets[1])
    else {
        panic!("two concrete label activations")
    };
    assert_eq!(
        first_brand, second_brand,
        "the same lexical label arena node is re-entered"
    );
    assert_eq!(
        first_activation.calls, second_activation.calls,
        "both evaluations are in the same callable activation"
    );
    assert_eq!(
        first_activation.location.expression,
        second_activation.location.expression
    );
    assert_ne!(
        first_activation.location.occurrence,
        second_activation.location.occurrence
    );
    assert_ne!(targets[0], targets[1]);
}

#[test]
fn repeated_capability_reads_share_the_exact_enclosing_label_activation() {
    let fixture = Fixture::new(
        r#"
        fn ignore<L>(value: L) where L: Label<i64> {}
        fn main() -> i64 { label done { ignore(@done); ignore(@done); @done(42) } }
    "#,
    );
    let summaries = fixture.derive();
    let summary = fixture.get(&summaries, "main");
    assert!(summary.only_returns_normally());
    let targets = summary.alternatives()[0]
        .events
        .iter()
        .filter_map(|event| match event {
            ControlEvent::Transfer { target, .. } => Some(target),
            ControlEvent::Invoke {
                callee:
                    ControlValue {
                        shape: ControlValueShape::Label(target),
                        ..
                    },
                ..
            } => Some(target),
            ControlEvent::Invoke { arguments, .. } => {
                arguments.iter().find_map(|argument| match &argument.shape {
                    ControlValueShape::Label(target) => Some(target),
                    _ => None,
                })
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(targets.len(), 3);
    assert!(targets.iter().all(|target| *target == targets[0]));
}
