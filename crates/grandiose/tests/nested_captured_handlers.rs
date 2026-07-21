use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Artifact, Type, Value, Vm, verify};

fn run_artifact(artifact: grandiose_vm::Artifact, function_name: &str) -> Value {
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == function_name)
        .unwrap_or_else(|| panic!("missing `{function_name}`")) as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

fn compile_and_run(source_name: &str, source: &str) -> Value {
    run_artifact(
        compile_source_to_bytecode(source_name, source).unwrap(),
        "selected",
    )
}

fn deterministic_phases(source_name: &str, source: &str) -> Artifact {
    let first = compile_source_to_phases(source_name, source).unwrap();
    let repeated = compile_source_to_phases(source_name, source).unwrap();
    assert_eq!(first.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(first.artifact.encode(), repeated.artifact.encode());
    first.artifact
}

fn handler_count_for(artifact: &Artifact, protocol_name: &str) -> usize {
    let protocols = artifact
        .protocols
        .iter()
        .enumerate()
        .filter_map(|(id, protocol)| (protocol.display_name == protocol_name).then_some(id as u32))
        .collect::<std::collections::BTreeSet<_>>();
    artifact
        .handler_defs
        .iter()
        .filter(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| protocols.contains(&clause.protocol))
        })
        .count()
}

fn assert_distinct_runtime_identities_and_valid_cleanups(artifact: &Artifact) {
    let identities = artifact
        .types
        .iter()
        .filter_map(|ty| match ty.representation() {
            Type::Callable { identity_name, .. } | Type::Handler { identity_name, .. } => {
                Some(identity_name.as_str())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(
        identities.len(),
        identities
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        "callable and handler runtime identities must not alias"
    );
    assert!(artifact.cleanups.iter().all(|cleanup| {
        let function = &artifact.functions[cleanup.function as usize];
        cleanup.end_instruction <= function.code_len
            && cleanup
                .registers
                .iter()
                .all(|register| (*register as usize) < function.register_types.len())
    }));
}

#[test]
fn terminal_handler_nested_inside_resumptive_handler_is_required_positive_behavior() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Stop { stop() -> ! }
        selected() -> i64 {
            handle {
                handle perform Stop::stop() {
                    Stop::stop() => perform Ask::ask()
                }
            } {
                Ask::ask() with continuation => resume(continuation, 42)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("terminal-inside-resumptive.gr", source),
        Value::I64(42)
    );
}

#[test]
fn resumptive_handler_nested_inside_terminal_handler_is_required_positive_behavior() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Stop { stop() -> ! }
        selected() -> i64 {
            handle {
                handle perform Ask::ask() {
                    Ask::ask() with continuation => {
                        resume(continuation, 1);
                        perform Stop::stop()
                    }
                }
            } {
                Stop::stop() => 42
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("resumptive-inside-terminal.gr", source),
        Value::I64(42)
    );
}

#[test]
fn terminal_perform_cannot_abandon_a_mandatory_resumption_argument() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Stop { stop() -> ! }
        selected() -> i64 {
            handle {
                handle perform Ask::ask() {
                    Ask::ask() with continuation => {
                        resume(continuation, perform Stop::stop())
                    }
                }
            } {
                Stop::stop() => 42
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("abandoned-mandatory-resumption.gr", source)
        .expect_err("a terminal payload must not abandon a mandatory resumption");
    assert!(errors.iter().any(|error| {
        error.message.contains("resumption") || error.message.contains("abandon")
    }));
}

#[test]
fn captured_handler_may_be_passed_returned_stored_and_invoked() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        retain<T>(value: T) -> T { value }
        selected() -> i64 {
            let captured = 40;
            let run_handler = { => {
                handle perform Ask::ask() {
                    Ask::ask() with continuation => resume(continuation, captured + 2)
                }
            } };
            let returned = retain(move run_handler);
            let stored = (move returned,);
            let (restored,) = move stored;
            restored()
        }
        main() -> { () }
    "#;
    let artifact = deterministic_phases("captured-handler-roundtrip.gr", source);
    assert_eq!(handler_count_for(&artifact, "Ask"), 1);
    assert_distinct_runtime_identities_and_valid_cleanups(&artifact);
    assert_eq!(run_artifact(artifact, "selected"), Value::I64(42));
}

#[test]
fn directly_invoked_captured_handler_keeps_distinct_runtime_identity_and_cleanup() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            let captured = 40;
            let run_handler = { => {
                handle perform Ask::ask() {
                    Ask::ask() with continuation => resume(continuation, captured + 2)
                }
            } };
            run_handler()
        }
        main() -> { () }
    "#;
    let artifact = deterministic_phases("direct-captured-handler.gr", source);
    assert_eq!(handler_count_for(&artifact, "Ask"), 1);
    assert!(!artifact.cleanups.is_empty());
    assert_distinct_runtime_identities_and_valid_cleanups(&artifact);
    assert_eq!(run_artifact(artifact, "selected"), Value::I64(42));
}

#[test]
fn resumed_nested_computation_reinstalls_the_nearest_handler_deeply() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                handle {
                    let first = perform Ask::ask();
                    let second = perform Ask::ask();
                    first + second
                } {
                    Ask::ask() with continuation => resume(continuation, 21)
                }
            } {
                Ask::ask() with continuation => resume(continuation, 100)
            }
        }
        main() -> { () }
    "#;
    let artifact = deterministic_phases("deep-handler-reinstatement.gr", source);
    assert_eq!(handler_count_for(&artifact, "Ask"), 2);
    assert_eq!(run_artifact(artifact, "selected"), Value::I64(42));
}

#[test]
fn nested_handler_removes_only_its_exact_protocol_from_the_outward_row() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Log { [1,1] log() -> i64 }
        both() -> i64 / {Ask, Log} {
            perform Ask::ask() + perform Log::log()
        }
        forward_log() -> i64 / {Log} {
            handle both() {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        selected() -> i64 {
            handle forward_log() {
                Log::log() with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    let artifact = deterministic_phases("exact-handler-row-subtraction.gr", source);
    let ask = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .unwrap() as u32;
    let log = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Log")
        .unwrap() as u32;
    let both = artifact
        .functions
        .iter()
        .find(|function| function.name == "both")
        .unwrap();
    let forward = artifact
        .functions
        .iter()
        .find(|function| function.name == "forward_log")
        .unwrap();
    let selected = artifact
        .functions
        .iter()
        .find(|function| function.name == "selected")
        .unwrap();
    assert_eq!(both.outward_protocols, [ask, log]);
    assert_eq!(forward.outward_protocols, [log]);
    assert!(selected.outward_protocols.is_empty());
    assert_eq!(run_artifact(artifact, "selected"), Value::I64(42));
}

#[test]
fn inner_partial_handler_forwards_to_outer_resumption() {
    let source = r#"
        enum State { Cold, Hot }
        effect Ask { [1,1] ask(state: State) -> i64 }
        request() -> i64 / {Ask} { perform Ask::ask(State::Hot) + 2 }
        inner() -> i64 / {Ask} {
            handle request() {
                Ask::ask(State::Cold) with continuation => resume(continuation, 1)
            }
        }
        selected() -> i64 {
            handle inner() {
                Ask::ask(State::Cold) with continuation => resume(continuation, 10),
                Ask::ask(State::Hot) with continuation => resume(continuation, 40)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("partial-forward-to-outer-resumption.gr", source),
        Value::I64(42)
    );
}

#[test]
fn private_must_move_payload_is_consumed_by_defining_authority() {
    let owner = r#"
        struct Secret { private value: i64 }
        impl Use<[1,1]> for Secret {}
        effect Deliver { [1,1] deliver(secret: Secret) -> i64 }

        make() -> Secret { Secret { value: 42 } }
        consume(secret: Secret) -> i64 {
            let Secret { value } = move secret;
            value
        }
        selected() -> i64 {
            handle perform Deliver::deliver(make()) {
                Deliver::deliver(secret) with continuation => {
                    resume(continuation, consume(move secret))
                }
            }
        }
    "#;
    let bundle = SourceBundle::new(
        Segment::new("owner.gr", owner),
        Segment::new("entry.gr", "main() -> { selected(); () }"),
        [],
    );
    assert_eq!(
        run_artifact(compile_bundle_to_bytecode(&bundle).unwrap(), "selected"),
        Value::I64(42)
    );
}
