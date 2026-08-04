use std::collections::BTreeSet;

use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Instruction, TEXT, Type, Value, Vm, verify};

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

const CANCEL: &str = r#"
    effect Stop { [0,1] stop() -> i64 }
    test() -> i64 {
        handle {
            let retained = "destroyed with the cancelled continuation";
            let ignored = perform Stop::stop();
            ignored + 1000
        } {
            Stop::stop() with k => { cancel(k); 42 }
        }
    }
    main() -> { () }
"#;

#[test]
fn optional_one_shot_cancel_emits_exact_descriptors_cleans_up_and_executes() {
    let artifact = compile_source_to_bytecode("cancel.glorious", CANCEL).unwrap();
    assert_eq!(artifact.required_features, 1 | (1 << 1) | (1 << 3));
    let stop = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap();
    let operation = &artifact.protocols[stop].operations[0];
    let clause = artifact
        .handler_defs
        .iter()
        .flat_map(|handler| &handler.clauses)
        .find(|clause| clause.protocol == stop as u32)
        .unwrap();
    let resumption_type = clause.resumption_type.unwrap();
    assert!(!operation.terminal);
    assert_eq!(operation.result_type, grandiose_vm::I64);
    assert!(matches!(
        &artifact.types[resumption_type as usize],
        Type::Resumption {
            input_type: grandiose_vm::I64,
            output_type: grandiose_vm::I64,
            effect_signature,
            lower_uses: 0,
            upper_uses: Some(1),
            copy: false,
            ..
        } if effect_signature.params.is_empty()
            && effect_signature.result == grandiose_vm::I64
            && effect_signature.outward_protocols.is_empty()
    ));

    let stop_handler = artifact
        .handler_defs
        .iter()
        .position(|handler| {
            handler
                .clauses
                .iter()
                .any(|clause| clause.protocol == stop as u32)
        })
        .expect("Stop must have a handler descriptor");
    let clause_name = format!("$handler${stop_handler}$clause$0");
    let clause = artifact
        .functions
        .iter()
        .find(|function| function.name == clause_name)
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
    assert!(
        clause_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Cancel { .. }))
    );
    assert!(
        !clause_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Resume { .. }))
    );

    let body_name = format!("$handler${stop_handler}$body");
    let body_id = artifact
        .functions
        .iter()
        .position(|function| function.name == body_name)
        .unwrap() as u32;
    let body = &artifact.functions[body_id as usize];
    let perform = artifact.code
        [body.code_start as usize..(body.code_start + body.code_len) as usize]
        .iter()
        .position(|instruction| matches!(instruction, Instruction::Perform { dst: Some(_), .. }))
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
fn optional_one_shot_may_resume_and_deeply_reinstalls_the_handler() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
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
    let artifact = compile_source_to_bytecode("optional-resume.glorious", source).unwrap();
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
fn optional_cancellation_cleans_up_affine_custom_drop_capture() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource {
            drop(&mut self) -> { () }
        }
        effect Stop { [0,1] stop() -> i64 }
        selected() -> i64 {
            handle {
                let resource = Resource { marker: 1 };
                let ignored = perform Stop::stop();
                ignored + 1000
            } {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("affine-cancel-capture.glorious", source).unwrap();
    assert_eq!(
        artifact
            .drop_glue
            .iter()
            .filter(|glue| matches!(
                artifact.types[glue.ty as usize].representation(),
                Type::Struct { name, .. } if name == "Resource"
            ))
            .count(),
        1
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
fn optional_cancellation_releases_whole_and_projected_loans_before_their_owners() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { self.marker; () } }
        struct Pair { left: i64, right: i64 }
        effect Stop { [0,1] stop() -> i64 }

        shared() -> i64 {
            handle {
                let value = 1;
                let reference = &value;
                let ignored = perform Stop::stop();
                reference;
                ignored
            } {
                Stop::stop() with continuation => { cancel(continuation); 40 }
            }
        }
        unique_with_drop() -> i64 {
            handle {
                let resource = Resource { marker: 2 };
                let reference = &mut resource;
                let ignored = perform Stop::stop();
                reference;
                ignored
            } {
                Stop::stop() with continuation => { cancel(continuation); 41 }
            }
        }
        projected() -> i64 {
            handle {
                let pair = Pair { left: 1, right: 2 };
                let reference = &mut pair.left;
                let ignored = perform Stop::stop();
                reference;
                ignored
            } {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("optional-cancel-loans.glorious", source).unwrap();
    assert_eq!(
        artifact
            .drop_glue
            .iter()
            .filter(|glue| matches!(
                artifact.types[glue.ty as usize].representation(),
                Type::Struct { name, .. } if name == "Resource"
            ))
            .count(),
        1
    );
    let functions = ["shared", "unique_with_drop", "projected"].map(|name| {
        artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    });
    let verified = verify(artifact).unwrap();
    for (function, expected) in functions.into_iter().zip([40, 41, 42]) {
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(expected)
        );
    }
}

#[test]
fn optional_outward_call_cancellation_releases_a_projected_loan() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        effect Stop { [0,1] stop() -> i64 }
        stop() -> i64 / {Stop} { perform Stop::stop() }
        selected() -> i64 {
            handle {
                let pair = Pair { left: 1, right: 2 };
                let reference = &mut pair.left;
                let ignored = stop();
                reference;
                ignored
            } {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("optional-call-projected-loan.glorious", source).unwrap();
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
fn optional_cancellation_carries_only_the_initialized_residual_fields() {
    let source = r#"
        struct Resource { serial: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { self.serial; () } }
        consume(value: Resource) -> { () }
        effect Stop { [0,1] stop() -> i64 }
        selected() -> i64 {
            handle {
                let pair = (Resource { serial: 1 }, 40);
                let resource = pair.0;
                consume(resource);
                let answer = perform Stop::stop();
                pair.1 + answer
            } {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("optional-residual-cancel.glorious", source).unwrap();
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
fn optional_cancel_core_mir_and_artifact_are_deterministic() {
    let first = compile_source_to_phases("cancel.glorious", CANCEL).unwrap();
    let second = compile_source_to_phases("cancel.glorious", CANCEL).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(first.core.canonical_text().contains("cancel"));
    assert!(first.mir.canonical_text().contains("Cancel"));
}

#[test]
fn optional_cancel_bundle_and_interpreter_match_the_vm() {
    let bundle = SourceBundle::new(
        Segment::new(
            "effects.glorious",
            "infixl 30 +; effect Stop { [0,1] stop() -> i64 }",
        ),
        Segment::new(
            "library.glorious",
            "test() -> i64 { handle { let ignored = perform Stop::stop(); ignored + 1000 } { Stop::stop() with k => { cancel(k); 42 } } }",
        ),
        [Segment::new(
            "entry.glorious",
            "main() -> { let result = test(); () }",
        )],
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

    let source = r#"
        effect Stop { [0,1] stop() -> i64 }
        test() -> i64 {
            handle { let ignored = perform Stop::stop(); ignored + 1000 } {
                Stop::stop() with k => { cancel(k); 42 }
            }
        }
        main() -> { let result = test(); () }
    "#;
    assert_eq!(
        run_source("cancel-differential.glorious", source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
    let artifact = compile_source_to_bytecode("cancel-differential.glorious", source).unwrap();
    let entry = artifact.entry_function.unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(entry, vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn optional_resumption_transports_through_identity_and_tuple_with_zero_use() {
    let source = r#"
        effect Stop { [0,1] stop() -> i64 }
        retain<T>(value: T) -> T { value }
        cancel_stored() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with k => {
                    let retained = retain(move k);
                    let stored = (move retained,);
                    let (restored,) = move stored;
                    cancel(move restored);
                    42
                }
            }
        }
        abandon_stored() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with k => {
                    let retained = retain(move k);
                    let stored = (move retained,);
                    42
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("optional-transport.glorious", source).unwrap();
    let resumption_types = artifact
        .handler_defs
        .iter()
        .flat_map(|handler| &handler.clauses)
        .filter_map(|clause| clause.resumption_type)
        .collect::<BTreeSet<_>>();
    assert_eq!(resumption_types.len(), 2);
    assert!(artifact.types.iter().any(|ty| {
        matches!(ty.representation(), Type::Tuple { fields, copy: false }
            if fields.len() == 1 && resumption_types.contains(&fields[0]))
            && ty.claimed_zero_use_allowed()
    }));
    let verified = verify(artifact.clone()).unwrap();
    for name in ["cancel_stored", "abandon_stored"] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42)
        );
    }
}

#[test]
fn optional_resumption_late_nominal_supports_projection_and_projected_borrow() {
    let source = r#"
        effect Stop { [0,1] stop() -> i64 }
        struct Envelope<T> { resumption: T, marker: i64 }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with k => {
                    let stored = Envelope { resumption: move k, marker: 42 };
                    let observed = &stored.marker;
                    let answer = stored.marker;
                    let Envelope { resumption: restored, marker: _ } = move stored;
                    cancel(move restored);
                    answer
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("late-nominal-place.glorious", source).unwrap();
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
fn late_resumption_nominal_inherits_private_field_authority() {
    let defining = r#"
        effect Stop { [0,1] stop() -> i64 }
        struct Secret<T> { private value: T }
    "#;
    let allowed = SourceBundle::new(
        Segment::new(
            "owner.glorious",
            format!(
                "{defining} answer() -> i64 {{ handle perform Stop::stop() {{ Stop::stop() with k => {{ let stored = Secret {{ value: move k }}; let Secret {{ value }} = move stored; cancel(move value); 42 }} }} }}"
            ),
        ),
        Segment::new("entry.glorious", "main() -> { () }"),
        [],
    );
    compile_bundle_to_bytecode(&allowed).unwrap();

    let rejected = SourceBundle::new(
        Segment::new("owner.glorious", defining),
        Segment::new(
            "caller.glorious",
            "answer() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { let stored = Secret { value: move k }; 42 } } } main() -> { () }",
        ),
        [],
    );
    let errors = compile_bundle_to_bytecode(&rejected).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("private field `value`")
                && error.message.contains("defining source segment")
        }),
        "{errors:#?}"
    );
}

#[test]
fn invalid_optional_resumption_consumption_has_stable_diagnostics() {
    let cases = [
        (
            "effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { cancel(k); cancel(k); 42 } } } main() -> { () }",
            "consumed more than 1 time(s)",
        ),
        (
            "effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { cancel(k); resume(k, 1) } } } main() -> { () }",
            "consumed more than 1 time(s)",
        ),
        (
            "effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { cancel(k, k); 42 } } } main() -> { () }",
            "`cancel` requires exactly 1 argument, found 2",
        ),
        (
            "effect Stop { [0,1] stop() -> i64 } good() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { cancel(k); 42 } } } bad() -> { cancel(k) } main() -> { () }",
            "resumption outside handler clause",
        ),
        (
            "effect Stop { [1,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { cancel(k); 42 } } } main() -> { () }",
            "cannot be cancelled",
        ),
        (
            "effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => { let escaped = k; cancel(k); 42 } } } main() -> { () }",
            "was already transported or consumed",
        ),
        (
            "effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle perform Stop::stop() { Stop::stop() with k => resume(k, ()) } } main() -> { () }",
            "expected i64, found Unit",
        ),
        (
            "struct Ticket { serial: i64 } impl Use<[1,1]> for Ticket {} effect Stop { [0,1] stop() -> i64 } bad() -> i64 { handle { let ticket = Ticket { serial: 1 }; let answer = perform Stop::stop(); let Ticket { serial } = ticket; answer } { Stop::stop() with k => { cancel(k); 42 } } } main() -> { () }",
            "cancellation/abandonment path has actual Use count 0",
        ),
    ];
    for (source, needle) in cases {
        let diagnostics = compile_source_to_bytecode("rejected.glorious", source).unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains(needle)
                    && matches!(
                        diagnostic.code.as_deref(),
                        Some("G1BC001" | "G1BC002" | "G1BC004")
                    )
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
fn optional_cancel_handlers_use_site_specific_result_types() {
    let source = r#"
        effect Stop { [0,1] stop() -> i64 }
        as_i64() -> i64 {
            handle perform Stop::stop() { Stop::stop() with k => { cancel(k); 1 } }
        }
        as_unit() -> {
            handle perform Stop::stop() { Stop::stop() with k => cancel(k) }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("site-specific-cancel.glorious", source).unwrap();
    let stop = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .expect("Stop must have a protocol descriptor") as u32;
    let resumptions = artifact
        .handler_defs
        .iter()
        .flat_map(|definition| &definition.clauses)
        .filter(|clause| clause.protocol == stop)
        .filter_map(|clause| clause.resumption_type)
        .collect::<Vec<_>>();
    assert_eq!(resumptions.len(), 2);
    let first = resumptions[0];
    let second = resumptions[1];
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
