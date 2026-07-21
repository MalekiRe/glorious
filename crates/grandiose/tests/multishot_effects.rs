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

const TWO_SHOT: &str = r#"
    effect Choose { [2,2] choose() -> i64 }
    test() -> i64 {
        handle {
            let retained = "cloned into each continuation snapshot";
            let selected = perform Choose::choose();
            selected + 1
        } {
            Choose::choose() with k => {
                let ignored = resume(k, 19);
                resume(move k, 41)
            }
        }
    }
    main() -> { () }
"#;

#[test]
fn exact_two_shot_descriptor_copies_snapshots_cleans_up_and_replays() {
    let artifact = compile_source_to_bytecode("two-shot.gr", TWO_SHOT).unwrap();
    let required_for_this_program = 1 | (1 << 1) | (1 << 3) | (1 << 4);
    assert_eq!(
        artifact.required_features & required_for_this_program,
        required_for_this_program
    );
    let choose = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Choose")
        .expect("Choose must have a protocol descriptor") as u32;
    let choose_handler = artifact
        .handler_defs
        .iter()
        .position(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == choose)
        })
        .expect("Choose must have a handler descriptor");
    let resumption_type = artifact.handler_defs[choose_handler]
        .clauses
        .iter()
        .find(|clause| clause.protocol == choose)
        .and_then(|clause| clause.resumption_type)
        .expect("Choose must have a two-shot resumption descriptor");
    assert!(matches!(
        &artifact.types[resumption_type as usize],
        Type::Resumption {
            input_type: grandiose_vm::I64,
            output_type: grandiose_vm::I64,
            effect_signature,
            lower_uses: 2,
            upper_uses: Some(2),
            copy: true,
            ..
        } if effect_signature.params.is_empty()
            && effect_signature.result == grandiose_vm::I64
            && effect_signature.outward_protocols.is_empty()
    ));

    let clause_name = format!("$handler${choose_handler}$clause$0");
    let clause_id = artifact
        .functions
        .iter()
        .position(|function| function.name == clause_name)
        .unwrap() as u32;
    let clause = &artifact.functions[clause_id as usize];
    assert_eq!(clause.receiver_mode, Some(0));
    assert!(matches!(
        artifact.types[clause.register_types[0] as usize],
        Type::RefShared {
            referent: grandiose_vm::UNIT
        }
    ));
    let clause_code =
        &artifact.code[clause.code_start as usize..(clause.code_start + clause.code_len) as usize];
    assert_eq!(
        clause_code
            .iter()
            .filter(|instruction| matches!(
                instruction,
                Instruction::Resume {
                    receiver_mode: 2,
                    ..
                }
            ))
            .count(),
        1
    );
    assert_eq!(
        clause_code
            .iter()
            .filter(|instruction| matches!(
                instruction,
                Instruction::Resume {
                    receiver_mode: 0,
                    ..
                }
            ))
            .count(),
        1
    );
    assert_eq!(
        clause_code
            .iter()
            .filter(
                |instruction| matches!(instruction, Instruction::Copy { dst, .. }
                if clause.register_types[*dst as usize] == resumption_type)
            )
            .count(),
        0
    );
    assert_eq!(
        clause_code
            .iter()
            .filter(
                |instruction| matches!(instruction, Instruction::Move { dst, .. }
                if clause.register_types[*dst as usize] == resumption_type)
            )
            .count(),
        1
    );
    assert!(artifact.cleanups.iter().any(|plan| {
        plan.function == clause_id
            && plan
                .registers
                .iter()
                .any(|register| clause.register_types[*register as usize] == resumption_type)
    }));

    let body_name = format!("$handler${choose_handler}$body");
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
    assert!(artifact.cleanups.iter().any(|plan| {
        plan.function == body_id
            && plan.first_instruction <= perform
            && perform < plan.end_instruction
            && plan
                .registers
                .iter()
                .any(|register| body.register_types[*register as usize] == TEXT)
    }));

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
fn exact_two_shot_resumption_keeps_its_principal_through_generic_box_storage() {
    let source = r#"
        effect Pick { [2,2] choose() -> i64 }
        struct Box<T> { value: T }
        answer() -> i64 {
            handle perform Pick::choose() {
                Pick::choose() with k => {
                    let stored = Box { value: move k };
                    let Box { value: restored } = move stored;
                    resume(restored, 20) + resume(move restored, 22)
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("boxed-two-shot.gr", source).unwrap();
    let pick = phases
        .artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Pick")
        .expect("Pick must have a protocol descriptor") as u32;
    let resumption = phases
        .artifact
        .handler_defs
        .iter()
        .flat_map(|definition| &definition.clauses)
        .find(|clause| clause.protocol == pick)
        .and_then(|clause| clause.resumption_type)
        .expect("Pick must have a two-shot resumption descriptor");
    let boxed = phases
        .artifact
        .types
        .iter()
        .find(|ty| {
            matches!(ty.representation(), Type::Struct { name, fields, .. }
            if name.starts_with("Box<") && fields.len() == 1 && fields[0].ty == resumption)
        })
        .expect("exact late Box<resumption> descriptor");
    assert!(boxed.claimed_duplicable());
    assert!(!boxed.claimed_zero_use_allowed());
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn exact_two_shot_resumption_counts_closure_mediated_invocations() {
    let source = r#"
        effect Pick { [2,2] choose() -> i64 }
        answer() -> i64 {
            handle perform Pick::choose() {
                Pick::choose() with k => {
                    let finish = { => resume(k, 21) };
                    let ignored = finish();
                    move finish()
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("closure-two-shot.gr", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(21)
    );
}

#[test]
fn exact_two_shot_deeply_reinstalls_a_replayed_handler_tree() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        test() -> i64 {
            handle {
                let first = perform Choose::choose();
                let second = perform Choose::choose();
                first + second
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 21)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("deep-two-shot.gr", source).unwrap();
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
fn direct_two_shot_multiplies_only_the_captured_owner_footprint() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        struct Ticket { marker: i64 }
        struct PerReplay { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        impl Use<[1,1]> for PerReplay {}

        test() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let selected = perform Choose::choose();
                let per_replay = PerReplay { marker: selected };
                let PerReplay { marker: suffix } = per_replay;
                let Ticket { marker: prefix } = ticket;
                prefix + suffix
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("two-shot-owned-capture.gr", source).unwrap();
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
fn direct_two_shot_rejects_under_and_overuse_of_a_captured_owner() {
    let cases = [
        (
            r#"
                effect Choose { [2,2] choose() -> i64 }
                struct Ticket { marker: i64 }
                impl Use<[2,2]> for Ticket {}
                bad() -> i64 {
                    handle {
                        let ticket = Ticket { marker: 1 };
                        let selected = perform Choose::choose();
                        selected
                    } {
                        Choose::choose() with k => {
                            let ignored = resume(k, 19);
                            resume(move k, 41)
                        }
                    }
                }
                main() -> { () }
            "#,
            "actual Use count 0",
        ),
        (
            r#"
                effect Choose { [2,2] choose() -> i64 }
                struct Ticket { marker: i64 }
                impl Use<[2,2]> for Ticket {}
                bad() -> i64 {
                    handle {
                        let ticket = Ticket { marker: 1 };
                        let selected = perform Choose::choose();
                        let copy = ticket;
                        let Ticket { marker: first } = copy;
                        let Ticket { marker: second } = ticket;
                        first + second + selected
                    } {
                        Choose::choose() with k => {
                            let ignored = resume(k, 19);
                            resume(move k, 41)
                        }
                    }
                }
                main() -> { () }
            "#,
            "actual Use count 4",
        ),
    ];
    for (source, needle) in cases {
        let diagnostics = compile_source_to_bytecode("bad-two-shot-owned-capture.gr", source)
            .expect_err("invalid multiplied ownership footprint was accepted");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(needle)),
            "missing `{needle}` in {diagnostics:#?}"
        );
    }
}

#[test]
fn two_shot_core_mir_and_artifact_are_deterministic() {
    let first = compile_source_to_phases("two-shot.gr", TWO_SHOT).unwrap();
    let second = compile_source_to_phases("two-shot.gr", TWO_SHOT).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert_eq!(first.core.canonical_text().matches("resume").count(), 0);
    let mir = first.mir.canonical_text();
    assert_eq!(mir.matches("-> Resume {").count(), 2);
    assert!(mir.matches("Copy").count() >= 2);
}

#[test]
fn two_shot_bundle_and_interpreter_match_the_vm() {
    let bundle = SourceBundle::new(
        Segment::new("effects.gr", "effect Choose { [2,2] choose() -> i64 }"),
        Segment::new(
            "library.gr",
            "test() -> i64 { handle { let selected = perform Choose::choose(); selected + 1 } { Choose::choose() with k => { let ignored = resume(k, 19); resume(move k, 41) } } }",
        ),
        [Segment::new(
            "entry.gr",
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
        effect Choose { [2,2] choose() -> i64 }
        test() -> i64 {
            handle { let selected = perform Choose::choose(); selected + 1 } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { let result = test(); () }
    "#;
    assert_eq!(
        run_source("two-shot-differential.gr", source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
    let artifact = compile_source_to_bytecode("two-shot-differential.gr", source).unwrap();
    let entry = artifact.entry_function.unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(entry, vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn two_shot_snapshots_clone_only_initialized_residual_fields() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource { drop(&mut self) -> { self.marker; () } }
        consume(value: Resource) -> { () }
        effect Choose { [2,2] choose() -> i64 }
        selected() -> i64 {
            handle {
                let pair = (Resource { marker: 1 }, 40);
                let resource = pair.0;
                consume(resource);
                let choice = perform Choose::choose();
                pair.1 + choice
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 1);
                    let second = resume(move continuation, 2);
                    first + second
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("two-shot-residual.gr", source).unwrap();
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
        Value::I64(83)
    );
}

#[test]
fn invalid_and_unsupported_multishot_shapes_have_stable_source_diagnostics() {
    let cases = [
        (
            "effect Choose { [2,infinity] choose() -> i64 } main() -> { () }",
            "arbitrary unbounded intervals require a future runtime representation",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => 42 } } main() -> { () }",
            "must be resumed exactly twice",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => resume(k, 1) } } main() -> { () }",
            "must be resumed exactly twice",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let a = resume(k, 1); let b = resume(k, 2); resume(k, 3) } } } main() -> { () }",
            "resumed more than twice",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { cancel(k); 42 } } } main() -> { () }",
            "cannot be cancelled",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let escaped = k; let ignored = resume(k, 1); resume(k, 2) } } } main() -> { () }",
            "actual Use count 0",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let ignored = resume(k, k); resume(k, 2) } } } main() -> { () }",
            "one independent result value",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let ignored = resume(k, ()); resume(k, 2) } } } main() -> { () }",
            "expected i64, found Unit",
        ),
        (
            "effect Choose { [2,2] choose() -> i64 } bad() -> i64 { handle { let value = 1; let reference = &mut value; let selected = perform Choose::choose(); *reference + selected } { Choose::choose() with k => { let ignored = resume(k, 1); resume(move k, 2) } } } main() -> { () }",
            "principal Use interval [0,1]",
        ),
        (
            "struct Owner { value: &mut i64 } struct Residual { owner: Owner, marker: i64 } impl Drop for Residual { drop(&mut self) -> { self.marker; () } } effect Choose { [2,2] choose() -> i64 } bad(value: Residual) -> i64 { let owner = value.owner; handle perform Choose::choose() { Choose::choose() with k => { let ignored = resume(k, 1); resume(k, 2) } } } main() -> { () }",
            "custom Drop hook",
        ),
    ];
    for (source, needle) in cases {
        let diagnostics = compile_source_to_bytecode("rejected.gr", source).unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains(needle)
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
fn direct_two_shot_snapshots_preserve_whole_and_projected_shared_aliases() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        effect Choose { [2,2] choose() -> i64 }
        observe(value: &i64) -> i64 { 40 }
        whole() -> i64 {
            handle {
                let value = 40;
                let reference = &value;
                let selected = perform Choose::choose();
                observe(reference) + selected
            } {
                Choose::choose() with continuation => {
                    let ignored = resume(continuation, 1);
                    resume(move continuation, 2)
                }
            }
        }
        projected() -> i64 {
            handle {
                let pair = Pair { left: 40, right: 0 };
                let reference = &pair.left;
                let selected = perform Choose::choose();
                observe(reference) + selected
            } {
                Choose::choose() with continuation => {
                    let ignored = resume(continuation, 1);
                    resume(move continuation, 2)
                }
            }
        }
        choose_through(reference: &i64) -> i64 / {Choose} {
            let selected = perform Choose::choose();
            observe(reference) + selected
        }
        external() -> i64 {
            handle {
                let value = 40;
                choose_through(&value)
            } {
                Choose::choose() with continuation => {
                    let ignored = resume(continuation, 1);
                    resume(move continuation, 2)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("two-shot-shared-aliases.gr", source).unwrap();
    let functions = ["whole", "projected", "external"].map(|name| {
        artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    });
    let verified = verify(artifact).unwrap();
    for function in functions {
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(42)
        );
    }
}

#[test]
fn multishot_clause_capture_accepts_shared_references_and_reference_aggregates() {
    let source = r#"
        struct SharedCapture { reference: &i64 }
        effect Choose { [2,2] choose() -> i64 }
        observe(reference: &i64) -> i64 { 42 }
        observe_capture(capture: SharedCapture) -> i64 { 42 }
        selected() -> i64 {
            let value = 42;
            let reference = &value;
            handle perform Choose::choose() {
                Choose::choose() with continuation => {
                    let ignored = resume(continuation, observe(reference) - 1);
                    resume(move continuation, observe(reference))
                }
            }
        }
        aggregate(capture: SharedCapture) -> i64 {
            handle perform Choose::choose() {
                Choose::choose() with continuation => {
                    let ignored = resume(continuation, observe_capture(capture) - 1);
                    resume(move continuation, observe_capture(capture))
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("multishot-reference-capture.gr", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert!(
        artifact
            .functions
            .iter()
            .any(|function| function.name == "aggregate")
    );
    let verified = verify(artifact).unwrap();
    assert_eq!(
        Vm::new(verified).run(selected, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn two_shot_handlers_use_site_specific_result_types() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        as_i64() -> i64 {
            handle perform Choose::choose() {
                Choose::choose() with k => { let ignored = resume(k, 1); resume(move k, 2) }
            }
        }
        as_unit() -> {
            handle perform Choose::choose() {
                Choose::choose() with k => { let first = resume(k, 1); let second = resume(move k, 2); () }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("site-specific-two-shot.gr", source).unwrap();
    let choose = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Choose")
        .expect("Choose must have a protocol descriptor") as u32;
    let resumptions = artifact
        .handler_defs
        .iter()
        .flat_map(|definition| &definition.clauses)
        .filter(|clause| clause.protocol == choose)
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
