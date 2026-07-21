use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Instruction, TEXT, Type, Value, Vm, verify};

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

const ONE_SHOT: &str = r#"
    effect Ask { [1,1] ask(value: i64) -> i64 }
    test() -> i64 {
        handle perform Ask::ask(0) {
            Ask::ask(value) with k => resume(k, 42)
        }
    }
    main() -> { () }
"#;

#[test]
fn one_shot_resumption_emits_exact_descriptors_and_executes() {
    let artifact = compile_source_to_bytecode("one-shot.gr", ONE_SHOT).unwrap();
    assert_eq!(artifact.required_features, 1 | (1 << 1) | (1 << 3));
    let ask = protocol_id(&artifact, "Ask");
    let handler_def = only_handler_def_for_protocol(&artifact, ask);
    let operation = &artifact.protocols[ask as usize].operations[0];
    let resumption_type = artifact.handler_defs[handler_def].clauses[0]
        .resumption_type
        .unwrap();
    assert!(!operation.terminal);
    assert_eq!(operation.result_type, grandiose_vm::I64);
    assert!(matches!(
        &artifact.types[resumption_type as usize],
        Type::Resumption {
            input_type: grandiose_vm::I64,
            output_type: grandiose_vm::I64,
            effect_signature,
            lower_uses: 1,
            upper_uses: Some(1),
            copy: false,
            ..
        } if effect_signature.params.is_empty()
            && effect_signature.result == grandiose_vm::I64
            && effect_signature.outward_protocols.is_empty()
    ));
    assert_eq!(
        artifact.handler_defs[handler_def].clauses[0]
            .callable_signature
            .params,
        [grandiose_vm::I64, resumption_type]
    );
    let clause = artifact
        .functions
        .iter()
        .find(|function| function.name == handler_function_name(handler_def, "clause$0"))
        .unwrap();
    assert_eq!(clause.receiver_mode, Some(0));
    assert!(matches!(
        artifact.types[clause.register_types[0] as usize],
        Type::RefShared {
            referent: grandiose_vm::UNIT
        }
    ));
    let clause_code =
        &artifact.code[clause.code_start as usize..(clause.code_start + clause.code_len) as usize];
    assert!(clause_code.iter().any(|instruction| matches!(
        instruction,
        Instruction::Resume {
            receiver_mode: 2,
            ..
        }
    )));
    let body = artifact
        .functions
        .iter()
        .find(|function| function.name == handler_function_name(handler_def, "body"))
        .unwrap();
    assert_eq!(body.flags, 0);
    assert!(
        artifact.code[body.code_start as usize..(body.code_start + body.code_len) as usize]
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Perform { dst: Some(_), .. }))
    );

    let bytes = artifact.encode();
    assert_eq!(
        grandiose_vm::Artifact::decode(&bytes).unwrap().encode(),
        bytes
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
        Value::I64(42)
    );
}

#[test]
fn resumption_identity_is_per_handler_group_and_keeps_deep_outward_effects() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Trace { [1,1] trace() -> i64 }
        effect Unused { [1,1] unused() -> i64 }
        first() -> i64 / {Trace, Unused} {
            handle {
                let answer = perform Ask::ask();
                answer + perform Trace::trace()
            } {
                Ask::ask() with k => resume(move k, 1)
            }
        }
        second() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => resume(move k, 2)
            }
        }
        third_recurring() -> i64 / {Trace} {
            handle {
                let first = perform Ask::ask();
                let second = perform Ask::ask();
                first + second
            } {
                Ask::ask() with k => {
                    perform Trace::trace();
                    resume(move k, 3)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("handler-specific-resumptions.gr", source).unwrap();
    let ask = protocol_id(&artifact, "Ask");
    let handlers = handler_defs_for_protocol(&artifact, ask);
    assert_eq!(handlers.len(), 3);
    let first_handler = handlers[0];
    let first = artifact.handler_defs[first_handler].clauses[0]
        .resumption_type
        .unwrap();
    let second = artifact.handler_defs[handlers[1]].clauses[0]
        .resumption_type
        .unwrap();
    let recurring = artifact.handler_defs[handlers[2]].clauses[0]
        .resumption_type
        .unwrap();
    let trace = protocol_id(&artifact, "Trace");
    let unused = protocol_id(&artifact, "Unused");
    assert_ne!(
        first, second,
        "handler sites require distinct resumption identities"
    );
    assert_eq!(
        artifact.types[first as usize].representation(),
        &Type::Resumption {
            input_type: grandiose_vm::I64,
            output_type: grandiose_vm::I64,
            effect_signature: grandiose_vm::bytecode::Signature {
                params: vec![],
                result: grandiose_vm::I64,
                outward_protocols: vec![trace],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: format!(
                "handler#{first_handler} operation-group#0 Ask::ask one-shot resumption"
            ),
            copy: false,
        }
    );
    assert!(!matches!(
        artifact.types[first as usize].representation(),
        Type::Resumption { effect_signature, .. }
            if effect_signature.outward_protocols.contains(&unused)
    ));
    assert!(matches!(
        artifact.types[second as usize].representation(),
        Type::Resumption { effect_signature, .. }
            if effect_signature.outward_protocols.is_empty()
    ));
    assert!(matches!(
        artifact.types[recurring as usize].representation(),
        Type::Resumption { effect_signature, .. }
            if effect_signature.outward_protocols == [trace]
    ));
    verify(artifact).unwrap();
}

#[test]
fn one_shot_resumption_transports_through_identity_and_tuple_storage() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let retained = retain(move k);
                    let stored = (move retained,);
                    let (restored,) = move stored;
                    resume(move restored, 42)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("transported-resumption.gr", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn one_shot_resumption_transports_through_generic_struct_storage() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Box<T> { value: T }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let stored = Box { value: move k };
                    let Box { value: restored } = move stored;
                    resume(move restored, 42)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("struct-transported-resumption.gr", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn one_shot_resumption_transports_through_owned_closure_capture() {
    let source = r#"
        unused() -> i64 { 0 }
        effect Ask { [1,1] ask() -> i64 }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let finish = { => resume(move k, 42) };
                    finish()
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("closure-transported-resumption.gr", source).unwrap();
    let reordered = r#"
        effect Ask { [1,1] ask() -> i64 }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let finish = { => resume(move k, 42) };
                    finish()
                }
            }
        }
        unused() -> i64 { 0 }
        main() -> { () }
    "#;
    assert_eq!(
        artifact.encode(),
        compile_source_to_bytecode("closure-transported-resumption.gr", reordered)
            .unwrap()
            .encode()
    );
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn nested_resume_cannot_launder_an_unused_outer_resumption() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        bad() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with outer => {
                    handle perform Ask::ask() {
                        Ask::ask() with inner => resume(move inner, 42)
                    }
                }
            }
        }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("nested-resumption-laundering.gr", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.message.contains("`outer`")
                && diagnostic.message.contains("exactly once")
                && diagnostic.code.as_deref() == Some("G1BC002")
        }),
        "{diagnostics:#?}"
    );
}

#[test]
fn deep_handler_reinstalls_for_two_sequential_performs() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        test() -> i64 {
            handle {
                let first = perform Ask::ask();
                let second = perform Ask::ask();
                first + second
            } {
                Ask::ask() with k => resume(k, 40)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("deep.gr", source).unwrap();
    let test = artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(test, vec![])
            .unwrap(),
        Value::I64(80)
    );
}

#[test]
fn resumptive_core_and_mir_are_explicit_and_deterministic() {
    let first = compile_source_to_phases("one-shot.gr", ONE_SHOT).unwrap();
    let second = compile_source_to_phases("one-shot.gr", ONE_SHOT).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    // Handler pattern matrices are compiled before Typed Core; their ordinary
    // arm bodies appear in the block MIR, not as a semantic Core match node.
    assert!(!first.core.canonical_text().contains("resume"));
    let mir = first.mir.canonical_text();
    assert!(mir.contains("Perform { result: Some"));
    assert!(mir.contains("Resume"));
}

#[test]
fn resumed_continuation_executes_its_suffix() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        test() -> i64 {
            handle {
                let answer = perform Ask::ask();
                answer + 2
            } {
                Ask::ask() with k => resume(k, 40)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("suffix.gr", source).unwrap();
    let test = artifact
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(test, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn resumptive_perform_cleanup_tracks_owned_values_in_the_continuation() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        test() -> i64 {
            handle {
                let retained = "released after resumption";
                let answer = perform Ask::ask();
                answer
            } {
                Ask::ask() with k => resume(k, 42)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("cleanup.gr", source).unwrap();
    let ask = protocol_id(&artifact, "Ask");
    let handler_def = only_handler_def_for_protocol(&artifact, ask);
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
        Value::I64(42)
    );
}

#[test]
fn bundle_and_interpreter_agree_with_the_compiled_resumptive_handler() {
    let bundle = SourceBundle::new(
        Segment::new("effects.gr", "effect Ask { [1,1] ask() -> i64 }"),
        Segment::new(
            "library.gr",
            "test() -> i64 { handle { let value = perform Ask::ask(); value + 2 } { Ask::ask() with k => resume(k, 40) } }",
        ),
        [Segment::new("entry.gr", "main() -> { () }")],
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
        Value::I64(42)
    );

    let main_source = r#"
        effect Ask { [1,1] ask() -> i64 }
        test() -> i64 {
            handle {
                let value = perform Ask::ask();
                value + 2
            } {
                Ask::ask() with k => resume(k, 40)
            }
        }
        main() -> {
            let result = test();
            ()
        }
    "#;
    assert_eq!(
        run_source("differential.gr", main_source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
    let artifact = compile_source_to_bytecode("differential.gr", main_source).unwrap();
    let entry = artifact.entry_function.unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(entry, vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn resumptive_handler_clauses_capture_duplicable_values_through_shared_receivers() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            let captured = 42;
            handle perform Ask::ask() {
                Ask::ask() with continuation => resume(continuation, captured)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("captured-resumptive.gr", source).unwrap();
    assert!(
        artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectCopy { field: 0, .. }))
    );
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn multiple_resumptive_clause_groups_copy_their_duplicable_environments_independently() {
    let source = r#"
        effect Pick { [1,1] left() -> i64 [1,1] right() -> i64 }
        selected() -> i64 {
            let captured = 42;
            handle perform Pick::right() {
                Pick::left() with continuation => resume(continuation, captured - 1),
                Pick::right() with continuation => resume(continuation, captured)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("multiple-captured-resumptive.gr", source).unwrap();
    assert!(
        !artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::MakeHandlerShared { .. })),
        "borrowed resumptive receivers cannot use the owned shared-handler constructor"
    );
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn nonduplicable_resumptive_clause_captures_are_structured_source_errors() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            let ticket = Ticket { value: 42 };
            handle perform Ask::ask() {
                Ask::ask() with continuation => {
                    let Ticket { value } = move ticket;
                    resume(continuation, value)
                }
            }
        }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("linear-captured-resumptive.gr", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1HE001")
                && diagnostic
                    .message
                    .contains("resumptive clause shares one borrowed environment")
        }),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some("G1BC999")),
        "{diagnostics:#?}"
    );
}

#[test]
fn custom_drop_multishot_clause_captures_cannot_hide_behind_shared_receivers() {
    let source = r#"
        struct Guard { value: i64 }
        impl Drop for Guard { drop(&mut self) -> { self.value; () } }
        effect Ask { [2,2] ask() -> i64 }
        selected() -> i64 {
            let guard = Guard { value: 42 };
            handle perform Ask::ask() {
                Ask::ask() with continuation => {
                    let ignored = resume(continuation, guard.value - 1);
                    resume(move continuation, guard.value)
                }
            }
        }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("drop-captured-resumptive.gr", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1BC001")
                && diagnostic
                    .message
                    .contains("must contain no unique references or custom Drop state")
        }),
        "{diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some("G1BC999")),
        "{diagnostics:#?}"
    );
}

#[test]
fn mixed_terminal_and_resumptive_groups_share_an_exact_linear_environment() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Mixed { left() -> ! right() -> ! [1,1] ask() -> i64 }
        selected() -> i64 {
            let ticket = Ticket { value: 42 };
            handle perform Mixed::left() {
                Mixed::left() => { let Ticket { value } = move ticket; value },
                Mixed::right() => { let Ticket { value } = move ticket; value },
                Mixed::ask() with continuation => resume(continuation, 0)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("mixed-linear-handler-capture.gr", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn mandatory_one_shot_transfers_exact_linear_payload_and_result() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Exchange { [1,1] exchange(ticket: Ticket) -> Ticket }
        selected() -> i64 {
            let outgoing = Ticket { serial: 40 };
            handle {
                let incoming = perform Exchange::exchange(outgoing);
                let Ticket { serial } = incoming;
                serial + 2
            } {
                Exchange::exchange(ticket) with continuation => {
                    let Ticket { serial } = ticket;
                    resume(continuation, Ticket { serial: serial })
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("linear-resumptive-transfer.gr", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn mandatory_one_shot_preserves_unique_loan_and_reference_alias() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        observe(value: &mut i64) -> i64 { 41 }
        selected() -> i64 {
            handle {
                let value = 41;
                let reference = &mut value;
                let answer = perform Ask::ask();
                observe(reference) + answer
            } {
                Ask::ask() with continuation => resume(continuation, 1)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("one-shot-unique-loan.gr", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn mandatory_one_shot_carries_a_partially_moved_owner_residual() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { self.marker; () } }
        consume(value: Resource) -> { () }
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let pair = (Resource { marker: 1 }, 40);
                let resource = pair.0;
                consume(resource);
                let answer = perform Ask::ask();
                pair.1 + answer
            } {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("one-shot-residual.gr", source).unwrap();
    assert!(
        phases
            .mir
            .canonical_text()
            .contains("initialized_fields: [false, true]")
    );
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(function, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn deferred_resumptive_forms_have_stable_source_diagnostics() {
    let cases = [
        (
            "effect Ask { ask() -> i64 } main() -> { () }",
            "must declare `[0,1]` or an exact finite `[n,n]`",
        ),
        (
            "effect Ask { [0,0] ask() -> i64 } main() -> { () }",
            "must declare `[0,1]` or an exact finite `[n,n]`",
        ),
        (
            "effect Ask { [1,2] ask() -> i64 } main() -> { () }",
            "must declare `[0,1]` or an exact finite `[n,n]`",
        ),
        (
            "effect Ask { [1,infinity] ask() -> i64 } main() -> { () }",
            "must declare `[0,1]` or an exact finite `[n,n]`",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { handle perform Ask::ask() { Ask::ask() with k => 42 } } main() -> { () }",
            "must be resumed exactly once",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { handle perform Ask::ask() { Ask::ask() with k => resume(k, resume(k, 1)) } } main() -> { () }",
            "one independent result value",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { handle perform Ask::ask() { Ask::ask() with k => { cancel(k); 42 } } } main() -> { () }",
            "cannot be cancelled",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { handle perform Ask::ask() { Ask::ask() with k => { let escaped = k; resume(k, 42) } } } main() -> { () }",
            "was already transported or consumed",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { resume(k, 2) } main() -> { () }",
            "resumption outside handler clause",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { handle perform Ask::ask() { Ask::ask() with k => resume(k, ()) } } main() -> { () }",
            "expected i64, found Unit",
        ),
        (
            "effect Ask { [1,1] ask() -> i64 } bad() -> i64 { perform Ask::ask() } main() -> { () }",
            "outward effect performance",
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

#[test]
fn one_operation_gets_distinct_resumptions_for_distinct_handler_results() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        as_i64() -> i64 {
            handle perform Ask::ask() { Ask::ask() with k => resume(k, 1) }
        }
        as_unit() -> {
            handle perform Ask::ask() { Ask::ask() with k => { let value = resume(k, 1); () } }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("handler-result-identities.gr", source).unwrap();
    let ask = protocol_id(&artifact, "Ask");
    let handlers = handler_defs_for_protocol(&artifact, ask);
    assert_eq!(handlers.len(), 2);
    let first = handlers
        .iter()
        .find_map(|handler| {
            (artifact.handler_defs[*handler].result_type == grandiose_vm::I64).then(|| {
                artifact.handler_defs[*handler].clauses[0]
                    .resumption_type
                    .unwrap()
            })
        })
        .expect("missing i64-result Ask handler");
    let second = handlers
        .iter()
        .find_map(|handler| {
            (artifact.handler_defs[*handler].result_type == grandiose_vm::UNIT).then(|| {
                artifact.handler_defs[*handler].clauses[0]
                    .resumption_type
                    .unwrap()
            })
        })
        .expect("missing unit-result Ask handler");
    assert_ne!(first, second);
    assert!(matches!(
        artifact.types[first as usize].representation(),
        Type::Resumption {
            output_type: grandiose_vm::I64,
            ..
        }
    ));
    assert!(matches!(
        artifact.types[second as usize].representation(),
        Type::Resumption {
            output_type: grandiose_vm::UNIT,
            ..
        }
    ));
    verify(artifact).unwrap();
}
