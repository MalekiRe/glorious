use grandiose::{
    CompileOptions, OptimizationLevel, OptimizationPass, OptimizationPassOutcome,
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    compile_source_to_phases_with_options,
    compiler_mir::{CleanupAction, CleanupEdge},
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Instruction, NO_RETURN, TEXT, Type, Value, Vm, verify};

fn protocol_id(artifact: &grandiose_vm::Artifact, display_name: &str) -> u32 {
    artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == display_name)
        .unwrap_or_else(|| panic!("missing `{display_name}` protocol")) as u32
}

fn handler_defs_for_protocol(artifact: &grandiose_vm::Artifact, protocol: u32) -> Vec<usize> {
    artifact
        .handler_defs
        .iter()
        .enumerate()
        .filter_map(|(index, definition)| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == protocol)
                .then_some(index)
        })
        .collect()
}

fn only_handler_def_for_protocol(artifact: &grandiose_vm::Artifact, protocol: u32) -> usize {
    let matches = handler_defs_for_protocol(artifact, protocol);
    assert_eq!(matches.len(), 1, "expected exactly one matching handler");
    matches[0]
}

fn handler_function_name(handler_def: usize, suffix: &str) -> String {
    format!("$handler${handler_def}${suffix}")
}

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<InterpreterValue>,
        span: Span,
    ) -> Result<InterpreterValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected effect",
            "the lexical handler should intercept this operation",
            span,
        ))
    }
}

const TERMINAL_PROGRAM: &str = r#"
    effect Stop { stop(value: i64) -> ! }
    test() -> i64 {
        handle perform Stop::stop(42) {
            Stop::stop(value) => value
        }
    }
    main() -> { () }
"#;

fn optimized_phases(source: &str) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        "terminal-optimized.gr",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap()
}

fn control_outcome(phases: &grandiose::CompiledPhases) -> OptimizationPassOutcome {
    phases
        .optimization_report
        .passes
        .iter()
        .find(|pass| pass.pass == OptimizationPass::SpecializeControl)
        .unwrap()
        .outcome
}

#[test]
fn o2_fuses_only_cleanup_empty_single_clause_terminal_handler() {
    let baseline = compile_source_to_phases("terminal-o0.gr", TERMINAL_PROGRAM).unwrap();
    let optimized = optimized_phases(TERMINAL_PROGRAM);
    let repeated = optimized_phases(TERMINAL_PROGRAM);
    assert_eq!(
        control_outcome(&optimized),
        OptimizationPassOutcome::Changed
    );
    assert_eq!(optimized.optimization_report, repeated.optimization_report);
    assert_eq!(optimized.mir, repeated.mir);
    assert_eq!(optimized.artifact.encode(), repeated.artifact.encode());

    let function_id = optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let function = &optimized.artifact.functions[function_id as usize];
    let code = &optimized.artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    assert!(code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 2,
            ..
        }
    )));
    assert!(!code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));

    let baseline_id = baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(baseline.artifact).unwrap())
            .run(baseline_id, vec![])
            .unwrap(),
        Vm::new(verify(optimized.artifact).unwrap())
            .run(function_id, vec![])
            .unwrap()
    );
}

#[test]
fn o2_fuses_computed_terminal_payloads_from_copy_scalar_captures() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        test(marker: i64) -> i64 {
            handle perform Stop::stop(marker + 2) {
                Stop::stop(value) => value
            }
        }
        main() -> { () }
    "#;
    let baseline = compile_source_to_phases("computed-terminal-o0.gr", source).unwrap();
    let optimized = optimized_phases(source);
    assert_eq!(
        control_outcome(&optimized),
        OptimizationPassOutcome::Changed
    );
    let function_id = optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let baseline_id = baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(baseline.artifact).unwrap())
            .run(baseline_id, vec![Value::I64(40)])
            .unwrap(),
        Vm::new(verify(optimized.artifact).unwrap())
            .run(function_id, vec![Value::I64(40)])
            .unwrap()
    );
}

#[test]
fn o2_fuses_a_fresh_owned_aggregate_terminal_payload() {
    let source = r#"
        struct Packet { text: Text }
        effect Stop { stop(value: Packet) -> ! }
        test() -> Text {
            handle perform Stop::stop(Packet { text: "selected" }) {
                Stop::stop(value) => {
                    let Packet { text } = move value;
                    text
                }
            }
        }
        main() -> { () }
    "#;
    let baseline = compile_source_to_phases("owned-terminal-o0.gr", source).unwrap();
    let optimized = optimized_phases(source);
    assert_eq!(
        control_outcome(&optimized),
        OptimizationPassOutcome::Changed
    );
    let optimized_id = optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let optimized_function = &optimized.artifact.functions[optimized_id as usize];
    let optimized_code = &optimized.artifact.code[optimized_function.code_start as usize
        ..(optimized_function.code_start + optimized_function.code_len) as usize];
    assert!(!optimized_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));
    let baseline_id = baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(baseline.artifact).unwrap())
            .run(baseline_id, vec![])
            .unwrap(),
        Vm::new(verify(optimized.artifact).unwrap())
            .run(optimized_id, vec![])
            .unwrap()
    );
}

#[test]
fn o2_fuses_a_shared_reference_terminal_payload_without_losing_its_origin() {
    let source = r#"
        effect Stop { stop(value: &i64) -> ! }
        test() -> i64 {
            let value = 42;
            let borrowed = &value;
            handle perform Stop::stop(borrowed) {
                Stop::stop(returned) => *returned
            }
        }
        main() -> { () }
    "#;
    let baseline = compile_source_to_phases("reference-terminal-o0.gr", source).unwrap();
    let optimized = optimized_phases(source);
    assert_eq!(
        control_outcome(&optimized),
        OptimizationPassOutcome::Changed
    );
    let optimized_id = optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let optimized_function = &optimized.artifact.functions[optimized_id as usize];
    let optimized_code = &optimized.artifact.code[optimized_function.code_start as usize
        ..(optimized_function.code_start + optimized_function.code_len) as usize];
    assert!(!optimized_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));
    let baseline_id = baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(baseline.artifact).unwrap())
            .run(baseline_id, vec![])
            .unwrap(),
        Vm::new(verify(optimized.artifact).unwrap())
            .run(optimized_id, vec![])
            .unwrap()
    );
}

#[test]
fn o2_fuses_a_unique_reference_terminal_payload_only_by_transferring_the_loan() {
    let source = r#"
        effect Stop { stop(value: &mut i64) -> ! }
        test() -> i64 {
            let value = 42;
            let borrowed = &mut value;
            handle perform Stop::stop(borrowed) {
                Stop::stop(returned) => *returned
            }
        }
        main() -> { () }
    "#;
    let baseline = compile_source_to_phases("unique-reference-terminal-o0.gr", source).unwrap();
    let optimized = optimized_phases(source);
    assert_eq!(
        control_outcome(&optimized),
        OptimizationPassOutcome::Changed
    );
    let optimized_id = optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let optimized_function = &optimized.artifact.functions[optimized_id as usize];
    let optimized_code = &optimized.artifact.code[optimized_function.code_start as usize
        ..(optimized_function.code_start + optimized_function.code_len) as usize];
    assert!(!optimized_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));
    let baseline_id = baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(baseline.artifact).unwrap())
            .run(baseline_id, vec![])
            .unwrap(),
        Vm::new(verify(optimized.artifact).unwrap())
            .run(optimized_id, vec![])
            .unwrap()
    );
}

#[test]
fn o2_keeps_the_handler_when_terminal_cleanup_must_end_a_unique_loan() {
    let source = r#"
        effect Stop { stop() -> ! }
        test() -> i64 {
            let value = 42;
            let borrowed = &mut value;
            handle {
                let abandoned = borrowed;
                perform Stop::stop()
            } { Stop::stop() => 7 }
        }
        main() -> { () }
    "#;
    let retained = optimized_phases(source);
    let retained_id = retained
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let retained_function = &retained.artifact.functions[retained_id as usize];
    let retained_code = &retained.artifact.code[retained_function.code_start as usize
        ..(retained_function.code_start + retained_function.code_len) as usize];
    assert!(
        retained_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Handle { .. }))
    );
    assert_eq!(
        Vm::new(verify(retained.artifact).unwrap())
            .run(retained_id, vec![])
            .unwrap(),
        Value::I64(7)
    );
}

#[test]
fn o2_terminal_fusion_preserves_ordered_cleanup_and_resumption_barriers() {
    let cleanup = r#"
        effect Stop { stop() -> ! }
        test() -> i64 {
            handle {
                let abandoned = "released";
                perform Stop::stop()
            } { Stop::stop() => 7 }
        }
        main() -> { () }
    "#;
    let cleanup_baseline = compile_source_to_phases("terminal-cleanup-o0.gr", cleanup).unwrap();
    let cleanup_phases = optimized_phases(cleanup);
    let cleanup_function = cleanup_phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "test")
        .unwrap();
    let cleanup_code = &cleanup_phases.artifact.code[cleanup_function.code_start as usize
        ..(cleanup_function.code_start + cleanup_function.code_len) as usize];
    assert!(!cleanup_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));
    assert!(
        cleanup_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Drop { .. }))
    );
    let cleanup_baseline_id = cleanup_baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let cleanup_optimized_id = cleanup_phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(cleanup_baseline.artifact).unwrap())
            .run(cleanup_baseline_id, vec![])
            .unwrap(),
        Vm::new(verify(cleanup_phases.artifact).unwrap())
            .run(cleanup_optimized_id, vec![])
            .unwrap()
    );

    let multiple = r#"
        effect Stop { first(value: i64) -> ! second(value: i64) -> ! }
        test() -> i64 {
            handle perform Stop::second(9) {
                Stop::first(value) => value,
                Stop::second(value) => value
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        control_outcome(&optimized_phases(multiple)),
        OptimizationPassOutcome::Changed
    );

    let partial = r#"
        effect Stop { first() -> ! second() -> ! }
        test() -> i64 / {Stop} {
            handle perform Stop::first() { Stop::first() => 1 }
        }
        main() -> { () }
    "#;
    assert_eq!(
        control_outcome(&optimized_phases(partial)),
        OptimizationPassOutcome::Changed
    );

    let resumptive = r#"
        effect Stop { [0,1] stop() -> i64 }
        test() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let resumptive_phases = optimized_phases(resumptive);
    let resumptive_function = resumptive_phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "test")
        .unwrap();
    let resumptive_code = &resumptive_phases.artifact.code[resumptive_function.code_start as usize
        ..(resumptive_function.code_start + resumptive_function.code_len) as usize];
    assert!(
        resumptive_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Handle { .. }))
    );

    let clause_capture = r#"
        effect Stop { stop() -> ! }
        test() -> i64 {
            let captured = 17;
            handle perform Stop::stop() { Stop::stop() => captured }
        }
        main() -> { () }
    "#;
    let clause_capture_baseline =
        compile_source_to_phases("terminal-capture-o0.gr", clause_capture).unwrap();
    let clause_capture_optimized = optimized_phases(clause_capture);
    assert_eq!(
        control_outcome(&clause_capture_optimized),
        OptimizationPassOutcome::Changed
    );

    let baseline_id = clause_capture_baseline
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let optimized_id = clause_capture_optimized
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let optimized_function = &clause_capture_optimized.artifact.functions[optimized_id as usize];
    let optimized_code = &clause_capture_optimized.artifact.code[optimized_function.code_start
        as usize
        ..(optimized_function.code_start + optimized_function.code_len) as usize];
    assert!(!optimized_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::MakeHandler { .. } | Instruction::Handle { .. }
    )));

    let baseline_value = Vm::new(verify(clause_capture_baseline.artifact).unwrap())
        .run(baseline_id, vec![])
        .unwrap();
    let optimized_value = Vm::new(verify(clause_capture_optimized.artifact).unwrap())
        .run(optimized_id, vec![])
        .unwrap();
    assert_eq!(baseline_value, Value::I64(17));
    assert_eq!(optimized_value, baseline_value);
}

#[test]
fn terminal_handler_emits_exact_dynamic_descriptors_and_executes() {
    let artifact = compile_source_to_bytecode("terminal.gr", TERMINAL_PROGRAM).unwrap();
    assert_eq!(artifact.required_features, 1 | (1 << 1) | (1 << 3));
    let stop = protocol_id(&artifact, "Stop");
    assert_eq!(artifact.protocols[stop as usize].operations.len(), 1);
    let operation = &artifact.protocols[stop as usize].operations[0];
    assert_eq!(operation.name, "stop");
    assert_eq!(operation.payload_signature.params, [grandiose_vm::I64]);
    assert_eq!(operation.payload_signature.result, grandiose_vm::UNIT);
    assert!(operation.terminal);
    assert_eq!(operation.result_type, grandiose_vm::bytecode::NEVER);
    assert_eq!(
        (operation.resumption_lower, operation.resumption_upper),
        (0, Some(0))
    );

    let handler_def = only_handler_def_for_protocol(&artifact, stop);
    assert!(!artifact.handler_defs[handler_def].partial);
    assert_eq!(
        artifact.handler_defs[handler_def].result_type,
        grandiose_vm::I64
    );
    assert_eq!(artifact.handler_defs[handler_def].clauses.len(), 1);
    assert_eq!(
        artifact.handler_defs[handler_def].clauses[0].resumption_type,
        None
    );
    assert!(artifact.types.iter().any(
        |ty| matches!(ty, Type::Handler { handler_def: index, .. } if *index == handler_def as u32)
    ));

    let test = artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    let body = artifact
        .functions
        .iter()
        .find(|function| function.name == handler_function_name(handler_def, "body"))
        .unwrap();
    assert_eq!(body.flags, NO_RETURN);
    assert_eq!(body.receiver_mode, Some(2));
    assert_eq!(body.outward_protocols, [stop]);
    let body_code =
        &artifact.code[body.code_start as usize..(body.code_start + body.code_len) as usize];
    assert!(matches!(
        body_code.last(),
        Some(Instruction::Perform { dst: None, .. })
    ));
    assert!(
        !body_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Return { .. }))
    );

    let test_function = &artifact.functions[test as usize];
    let test_code = &artifact.code[test_function.code_start as usize
        ..(test_function.code_start + test_function.code_len) as usize];
    assert!(
        test_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::MakeCallable { .. }))
    );
    assert!(
        test_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::MakeHandler { .. }))
    );
    assert!(
        test_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Handle { .. }))
    );

    let bytes = artifact.encode();
    assert_eq!(
        grandiose_vm::Artifact::decode(&bytes).unwrap().encode(),
        bytes
    );
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(vm.run(test, vec![]).unwrap(), Value::I64(42));
}

#[test]
fn effect_core_and_mir_are_explicit_and_phase_fingerprints_are_deterministic() {
    let first = compile_source_to_phases("terminal.gr", TERMINAL_PROGRAM).unwrap();
    let second = compile_source_to_phases("terminal.gr", TERMINAL_PROGRAM).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let core = first.core.canonical_text();
    assert!(core.contains("handle h0"), "{core}");
    assert!(
        core.contains(" perform p") && core.contains("/o0"),
        "{core}"
    );
    let mir = first.mir.canonical_text();
    assert!(mir.contains("MakeCallable"));
    assert!(mir.contains("MakeHandler"));
    assert!(mir.contains("Handle"));
    assert!(mir.contains("Perform"));
}

#[test]
fn total_multi_operation_handler_preserves_declaration_and_clause_order() {
    let source = r#"
        effect Stop {
            first(value: i64) -> !
            second(text: Text) -> !
        }
        test() -> i64 {
            handle perform Stop::second("payload") {
                Stop::first(value) => value,
                Stop::second(_) => 2
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("two-operations.gr", source).unwrap();
    let stop = protocol_id(&artifact, "Stop");
    assert_eq!(
        artifact.protocols[stop as usize]
            .operations
            .iter()
            .map(|operation| operation.name.as_str())
            .collect::<Vec<_>>(),
        ["first", "second"]
    );
    assert_eq!(
        artifact.handler_defs[only_handler_def_for_protocol(&artifact, stop)]
            .clauses
            .iter()
            .map(|clause| (clause.protocol, clause.operation))
            .collect::<Vec<_>>(),
        [(stop, 0), (stop, 1)]
    );
    let test = artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(test, vec![])
            .unwrap(),
        Value::I64(2)
    );
}

#[test]
fn terminal_perform_cleanup_tracks_abandoned_text_and_has_no_normal_return() {
    let source = r#"
        effect Stop { stop() -> ! }
        test() -> i64 {
            handle {
                let abandoned = "released";
                perform Stop::stop()
            } {
                Stop::stop() => 7
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("cleanup.gr", source).unwrap();
    let stop = protocol_id(&artifact, "Stop");
    let handler_def = only_handler_def_for_protocol(&artifact, stop);
    let body_id = artifact
        .functions
        .iter()
        .position(|function| function.name == handler_function_name(handler_def, "body"))
        .unwrap() as u32;
    let body = &artifact.functions[body_id as usize];
    let perform = artifact.code
        [body.code_start as usize..(body.code_start + body.code_len) as usize]
        .iter()
        .position(|instruction| matches!(instruction, Instruction::Perform { .. }))
        .unwrap() as u32;
    let cleanup = artifact
        .cleanups
        .iter()
        .find(|plan| {
            plan.function == body_id
                && plan.first_instruction <= perform
                && perform < plan.end_instruction
        })
        .unwrap();
    assert!(
        cleanup
            .registers
            .iter()
            .any(|register| body.register_types[*register as usize] == TEXT)
    );
    let test = artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(test, vec![])
            .unwrap(),
        Value::I64(7)
    );
}

#[test]
fn terminal_abandonment_classifies_partial_residuals_from_exact_flow_at_all_levels() {
    let source = r#"
        struct Resource { value: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { left: Resource, right: Resource }
        consume(value: Resource) -> () {
            let Resource { value: _ } = move value;
            ()
        }
        effect Stop { stop() -> ! }
        selected() -> i64 {
            handle {
                let parcel = Parcel {
                    left: Resource { value: 1 },
                    right: Resource { value: 2 },
                };
                let left = parcel.left;
                consume(move left);
                perform Stop::stop()
            } {
                Stop::stop() => 7
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "terminal-residual-cleanup.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            phases.mir.functions.iter().any(|function| {
                function.flow.cleanup_plans.iter().any(|plan| {
                    matches!(plan.edge, CleanupEdge::TerminalPerform { .. })
                        && plan.actions.iter().any(|action| {
                            matches!(
                                action,
                                CleanupAction::DestroyResidual {
                                    initialized_fields,
                                    ..
                                } if initialized_fields == &[false, true]
                            )
                        })
                })
            }),
            "{optimization_level:?}: terminal cleanup lost its residual bitmap\n{}",
            phases.mir.canonical_text()
        );
        let verified = verify(phases.artifact).unwrap();
        let selected = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified).run(selected, vec![]).unwrap(),
            Value::I64(7),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn bundle_effect_declaration_and_handler_share_one_namespace() {
    let bundle = SourceBundle::new(
        Segment::new("std-lib.glorious", "effect Stop { stop(value: i64) -> ! }"),
        Segment::new(
            "primary.glorious",
            "test() -> i64 { handle perform Stop::stop(9) { Stop::stop(value) => value } }",
        ),
        [Segment::new("entry.glorious", "main() -> { () }")],
    );
    let first = compile_bundle_to_bytecode(&bundle).unwrap();
    let second = compile_bundle_to_bytecode(&bundle).unwrap();
    assert_eq!(first.encode(), second.encode());
    let test = first
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(first).unwrap()).run(test, vec![]).unwrap(),
        Value::I64(9)
    );
}

#[test]
fn interpreter_and_vm_agree_on_a_closed_terminal_handler() {
    let source = r#"
        effect Stop { stop() -> ! }
        main() -> {
            handle perform Stop::stop() { Stop::stop() => () }
        }
    "#;
    assert_eq!(
        run_source("differential.gr", source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
    let artifact = compile_source_to_bytecode("differential.gr", source).unwrap();
    let entry = artifact.entry_function.unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(entry, vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn genuinely_invalid_terminal_effect_shapes_reject_before_bytecode_verification() {
    let unused_resumptive = compile_source_to_bytecode(
        "unused-resumptive.gr",
        "effect Ask { [1,1] ask() -> i64 } main() -> { () }",
    )
    .unwrap();
    verify(unused_resumptive).unwrap();

    let cases = [
        (
            "effect Stop { stop() -> ! } main() -> { perform Stop::stop() }",
            "outward effect performance",
        ),
        (
            "effect Stop { stop(value: i64) -> ! } main() -> { handle perform Stop::stop(1) { Stop::stop(1) => () } }",
            "non-exhaustive handler pattern",
        ),
        (
            "effect Stop { first() -> ! second() -> ! } main() -> { handle perform Stop::first() { Stop::first() => () } }",
            "missing operation",
        ),
    ];
    for (source, needle) in cases {
        let diagnostics = compile_source_to_bytecode("rejected.gr", source).unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                !diagnostic.title.is_empty()
                    && diagnostic.message.contains(needle)
                    && matches!(diagnostic.code.as_deref(), Some("G1BC001" | "G1BC002"))
            }),
            "expected `{needle}` in {diagnostics:#?}"
        );
        assert!(
            !diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code.as_deref() == Some("G1BC999"))
        );
    }
}

fn run_selected(source_name: &str, source: &str) -> Value {
    let artifact = compile_source_to_bytecode(source_name, source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(selected, vec![])
        .unwrap()
}

#[test]
fn terminal_control_in_a_binary_operand_is_left_to_right_and_uses_the_nearest_handler() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        selected() -> i64 {
            handle {
                handle perform Stop::stop(11) + perform Stop::stop(12) {
                    Stop::stop(value) => value
                }
            } { Stop::stop(_) => 99 }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-binary-operand.gr", source),
        Value::I64(11)
    );
}

#[test]
fn terminal_control_in_a_call_argument_is_left_to_right_and_uses_the_nearest_handler() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        choose(first: i64, second: i64) -> i64 { first + second }
        selected() -> i64 {
            handle {
                handle choose(perform Stop::stop(21), perform Stop::stop(22)) {
                    Stop::stop(value) => value
                }
            } { Stop::stop(_) => 99 }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-call-argument.gr", source),
        Value::I64(21)
    );
}

#[test]
fn terminal_control_in_a_tuple_field_is_left_to_right_and_uses_the_nearest_handler() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        selected() -> i64 {
            handle {
                handle (perform Stop::stop(31), perform Stop::stop(32)) {
                    Stop::stop(value) => value
                }
            } { Stop::stop(_) => 99 }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-tuple-field.gr", source),
        Value::I64(31)
    );
}

#[test]
fn terminal_control_in_a_struct_field_is_left_to_right_and_uses_the_nearest_handler() {
    let source = r#"
        struct Pair { first: i64, second: i64 }
        effect Stop { stop(value: i64) -> ! }
        selected() -> i64 {
            handle {
                handle Pair {
                    first: perform Stop::stop(41),
                    second: perform Stop::stop(42)
                } {
                    Stop::stop(value) => value
                }
            } { Stop::stop(_) => 99 }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-struct-field.gr", source),
        Value::I64(41)
    );
}

#[test]
fn terminal_control_in_an_effect_payload_uses_the_nearest_handler() {
    let effect_payload = r#"
        effect Stop { outer(value: i64) -> ! inner(value: i64) -> ! }
        selected() -> i64 {
            handle {
                handle perform Stop::outer(perform Stop::inner(51)) {
                    Stop::outer(value) => value + 1,
                    Stop::inner(value) => value
                }
            } {
                Stop::outer(_) => 98,
                Stop::inner(_) => 99
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-effect-payload.gr", effect_payload),
        Value::I64(51)
    );
}

#[test]
fn a_locally_handled_terminal_resume_argument_does_not_abandon_the_mandatory_resumption() {
    let resume_argument = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Stop { stop(value: i64) -> ! }
        selected() -> i64 {
            handle {
                handle perform Ask::ask() {
                    Ask::ask() with continuation => {
                        resume(continuation, handle perform Stop::stop(61) {
                            Stop::stop(value) => value
                        })
                    }
                }
            } {
                Stop::stop(_) => 99
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("terminal-resume-argument.gr", resume_argument),
        Value::I64(61)
    );
}

#[test]
fn generic_terminal_instances_and_nested_terminal_handlers_are_required_behavior() {
    let generic = r#"
        effect Stop<E> { stop(value: E) -> ! }
        selected() -> i64 {
            handle perform Stop<i64>::stop(71) {
                Stop<i64>::stop(value) => value
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("generic-terminal-instance.gr", generic),
        Value::I64(71)
    );

    let nested = r#"
        effect Stop { stop(value: i64) -> ! }
        selected() -> i64 {
            handle perform Stop::stop(72) {
                Stop::stop(value) => handle perform Stop::stop(value) {
                    Stop::stop(inner) => inner
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        run_selected("nested-terminal-handler.gr", nested),
        Value::I64(72)
    );
}

#[test]
fn terminal_control_cannot_abandon_live_must_move_values_or_mandatory_resumptions() {
    let cases = [
        (
            "terminal-abandons-must-move.gr",
            r#"
                struct Ticket { value: i64 }
                impl Use<[1,1]> for Ticket {}
                effect Stop { stop() -> ! }
                bad() -> i64 {
                    handle {
                        let ticket = Ticket { value: 1 };
                        perform Stop::stop()
                    } { Stop::stop() => 0 }
                }
                main() -> { () }
            "#,
        ),
        (
            "terminal-abandons-resumption.gr",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                effect Stop { stop() -> ! }
                bad() -> i64 {
                    handle {
                        handle perform Ask::ask() {
                            Ask::ask() with continuation => {
                                resume(continuation, perform Stop::stop())
                            }
                        }
                    } { Stop::stop() => 0 }
                }
                main() -> { () }
            "#,
        ),
    ];
    for (name, source) in cases {
        let diagnostics = compile_source_to_bytecode(name, source)
            .expect_err("terminal control abandoned a mandatory live value");
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.code.is_some()
                    && (diagnostic.message.contains("abandon")
                        || diagnostic.message.contains("Use")
                        || diagnostic.message.contains("resumption"))
            }),
            "missing mandatory-abandonment diagnostic: {diagnostics:#?}"
        );
    }
}
