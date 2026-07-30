use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    source_bundle::{Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::{Instruction, NO_RETURN, TEXT, Value, Vm, verify};

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

#[test]
fn terminal_outward_callable_is_closed_by_a_lexical_handler() {
    let source = r#"
        effect Stop { stop(value: i64) -> ! }
        stop_with(value: i64) -> i64 / {Stop} { perform Stop::stop(value) }
        test() -> i64 {
            handle { stop_with(42) } { Stop::stop(value) => value }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("terminal-call.glorious", source).unwrap();
    let stop_with = artifact
        .functions
        .iter()
        .find(|function| function.name == "stop_with")
        .unwrap();
    let stop = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Stop")
        .unwrap() as u32;
    assert_eq!(stop_with.outward_protocols, [stop]);
    assert_eq!(stop_with.flags, NO_RETURN);
    assert!(
        artifact.code
            [stop_with.code_start as usize..(stop_with.code_start + stop_with.code_len) as usize]
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Perform { dst: None, .. }))
    );
    let stop_handler = artifact
        .handler_defs
        .iter()
        .position(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == stop)
        })
        .expect("Stop must have a handler descriptor");
    let body_name = format!("$handler${stop_handler}$body");
    let body = artifact
        .functions
        .iter()
        .find(|function| function.name == body_name)
        .unwrap();
    assert_eq!(body.outward_protocols, [stop]);
    // The optimizer may preserve the outward call, turn it into a tail call,
    // or inline `stop_with` and leave its terminal perform directly in the
    // generated handler body. Every valid shape retains an outward operation.
    assert!(
        artifact.code[body.code_start as usize..(body.code_start + body.code_len) as usize]
            .iter()
            .any(|instruction| matches!(
                instruction,
                Instruction::Call { .. }
                    | Instruction::TailCall { .. }
                    | Instruction::Perform { .. }
            ))
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
fn transparent_row_alias_closes_terminal_outward_call_and_emits_no_metadata() {
    let explicit = r#"
        effect Stop { stop(value: i64) -> ! }
        stop_with(value: i64) -> i64 / {Stop} { perform Stop::stop(value) }
        test() -> i64 { handle { stop_with(42) } { Stop::stop(value) => value } }
        main() -> { () }
    "#;
    let aliased = r#"
        cases Stops = {Stop};
        effect Stop { stop(value: i64) -> ! }
        stop_with(value: i64) -> i64 / {Stops} { perform Stop::stop(value) }
        test() -> i64 { handle { stop_with(42) } { Stop::stop(value) => value } }
        main() -> { () }
    "#;
    let explicit = compile_source_to_phases("explicit-row.glorious", explicit).unwrap();
    let aliased = compile_source_to_phases("aliased-row.glorious", aliased).unwrap();
    assert_eq!(
        explicit
            .core
            .functions
            .iter()
            .map(|function| (&function.name, &function.outward_protocols))
            .collect::<Vec<_>>(),
        aliased
            .core
            .functions
            .iter()
            .map(|function| (&function.name, &function.outward_protocols))
            .collect::<Vec<_>>()
    );
    assert_eq!(
        explicit
            .mir
            .functions
            .iter()
            .map(|function| (&function.name, &function.outward_protocols))
            .collect::<Vec<_>>(),
        aliased
            .mir
            .functions
            .iter()
            .map(|function| (&function.name, &function.outward_protocols))
            .collect::<Vec<_>>()
    );
    assert_eq!(explicit.artifact.encode(), aliased.artifact.encode());
    let aliased = aliased.artifact;
    let test = aliased
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(aliased).unwrap()).run(test, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn normalized_empty_rows_are_pure_and_byte_equivalent() {
    let omitted = "id<T>(value: T) -> T { value } main() -> { id(42); () }";
    let explicit = "id<T>(value: T) -> T / {} { value } main() -> / {} { id(42); () }";
    let aliased = r#"
        cases Empty = {};
        cases AlsoEmpty = {Empty};
        id<T>(value: T) -> T / {AlsoEmpty} { value }
        main() -> / {Empty} { id(42); () }
    "#;
    let omitted = compile_source_to_bytecode("empty-omitted.glorious", omitted).unwrap();
    let explicit = compile_source_to_bytecode("empty-explicit.glorious", explicit).unwrap();
    let aliased = compile_source_to_bytecode("empty-aliased.glorious", aliased).unwrap();
    assert_eq!(omitted.encode(), explicit.encode());
    assert_eq!(omitted.encode(), aliased.encode());
    assert!(
        aliased
            .functions
            .iter()
            .filter(|function| {
                function.name == "main" || function.name.starts_with("$specialization$id#")
            })
            .all(|function| function.outward_protocols.is_empty())
    );
    assert!(
        aliased
            .functions
            .iter()
            .any(|function| function.name.starts_with("$specialization$id#"))
    );
}

#[test]
fn drop_may_call_a_function_whose_alias_row_normalizes_empty() {
    let source = r#"
        cases Empty = {};
        struct Item { value: i64 }
        safe() -> / {Empty} { () }
        impl Drop for Item { drop(&mut self) -> { safe() } }
        main() -> { let item = Item { value: 1 }; () }
    "#;
    let artifact = compile_source_to_bytecode("empty-drop-row.glorious", source).unwrap();
    verify(artifact).unwrap();
}

const TRANSITIVE: &str = r#"
    effect Ask { [1,1] ask() -> i64 }
    leaf() -> i64 / {Ask} { perform Ask::ask() }
    forward() -> i64 / {Ask} { leaf() + 2 }
    test() -> i64 {
        handle {
            let retained = "owned across the effectful call";
            forward()
        } {
            Ask::ask() with k => resume(k, 40)
        }
    }
    main() -> { () }
"#;

const ALIASED_TRANSITIVE: &str = r#"
    cases AskBase = {Ask};
    cases AskRow = {AskBase, Ask};
    effect Ask { [1,1] ask() -> i64 }
    leaf() -> i64 / {AskRow} { perform Ask::ask() }
    forward() -> i64 / {AskBase} { leaf() + 2 }
    test() -> i64 {
        handle {
            let retained = "owned across the effectful call";
            forward()
        } {
            Ask::ask() with k => resume(k, 40)
        }
    }
    main() -> { () }
"#;

#[test]
fn chained_row_aliases_preserve_transitive_resumption_metadata_and_codec() {
    let artifact =
        compile_source_to_bytecode("aliased-transitive.glorious", ALIASED_TRANSITIVE).unwrap();
    let ask = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("Ask must have a protocol descriptor") as u32;
    for name in ["leaf", "forward"] {
        assert_eq!(
            artifact
                .functions
                .iter()
                .find(|function| function.name == name)
                .unwrap()
                .outward_protocols,
            [ask]
        );
    }
    let bytes = artifact.encode();
    let decoded = grandiose_vm::Artifact::decode(&bytes).unwrap();
    assert_eq!(decoded.encode(), bytes);
    let test = decoded
        .functions
        .iter()
        .position(|function| function.name == "test")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(decoded).unwrap()).run(test, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn row_alias_declaration_order_is_byte_independent() {
    let reordered = r#"
        effect Ask { [1,1] ask() -> i64 }
        leaf() -> i64 / {AskRow} { perform Ask::ask() }
        cases AskRow = {Ask, AskBase};
        forward() -> i64 / {AskBase} { leaf() + 2 }
        cases AskBase = {Ask};
        test() -> i64 {
            handle { forward() } { Ask::ask() with k => resume(k, 40) }
        }
        main() -> { () }
    "#;
    let canonical = ALIASED_TRANSITIVE.replace(
        "let retained = \"owned across the effectful call\";\n            ",
        "",
    );
    assert_eq!(
        compile_source_to_bytecode("alias-order-a.glorious", &canonical)
            .unwrap()
            .encode(),
        compile_source_to_bytecode("alias-order-b.glorious", reordered)
            .unwrap()
            .encode()
    );
}

#[test]
fn invalid_row_aliases_have_structured_member_or_declaration_diagnostics() {
    for (source, needle, marked, code) in [
        (
            "cases IO = {Missing}; main() -> { () }",
            "unknown effect or effect-row alias",
            "Missing",
            "G1BC002",
        ),
        (
            "cases IO = {Outer::Ask}; main() -> { () }",
            "qualified effect-row alias member",
            "Outer::Ask",
            "G1BC001",
        ),
        (
            "cases IO = {&Ask}; main() -> { () }",
            "complex effect-row alias member",
            "&Ask",
            "G1BC001",
        ),
        (
            "cases IO = {(Ask,)}; main() -> { () }",
            "complex effect-row alias member",
            "(Ask,)",
            "G1BC001",
        ),
        (
            "effect Ask { ask() -> ! } cases Ask = {}; main() -> { () }",
            "effect name declared more than once",
            "cases Ask = {};",
            "G0002",
        ),
        (
            "cases IO = {}; cases IO = {}; main() -> { () }",
            "effect name declared more than once",
            "cases IO = {};",
            "G0002",
        ),
        (
            "cases IO = {Ask}; effect Ask { read() -> ! } bad() -> i64 / {IO} { perform IO::read() } main() -> { () }",
            "has not been declared",
            "IO",
            "G0100",
        ),
    ] {
        let errors = compile_source_to_bytecode("invalid-row-alias.glorious", source).unwrap_err();
        let error = errors
            .iter()
            .find(|error| error.message.contains(needle) || error.title.contains(needle))
            .unwrap_or_else(|| panic!("missing `{needle}`: {errors:#?}"));
        assert_eq!(&source[error.span.unwrap().range()], marked);
        assert_eq!(error.code.as_deref(), Some(code));
    }

    let cycle = "cases Left = {Right}; cases Right = {Left}; main() -> { () }";
    let errors = compile_source_to_bytecode("cyclic-row-alias.glorious", cycle).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message.contains("cyclic")
            && error.span.is_some()
            && error.code.as_deref() == Some("G1BC002")
    }));
}

#[test]
fn instantiated_effect_row_aliases_preserve_exact_protocol_identity() {
    let source = r#"
        effect Ask<E> { [1,1] ask(value: E) -> E }
        cases IntegerAsk = {Ask<i64>};
        leaf() -> i64 / {IntegerAsk} { perform Ask<i64>::ask(42) }
        selected() -> i64 {
            handle { leaf() } {
                Ask<i64>::ask(value) with continuation => resume(continuation, value)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("instantiated-row-alias.glorious", source).unwrap();
    let ask = artifact
        .protocols
        .iter()
        .position(|protocol| {
            protocol.display_name == "Ask" && protocol.type_arguments == [grandiose_vm::I64]
        })
        .unwrap() as u32;
    assert_eq!(
        artifact
            .functions
            .iter()
            .find(|function| function.name == "leaf")
            .unwrap()
            .outward_protocols,
        [ask]
    );
    assert_eq!(
        artifact
            .functions
            .iter()
            .find(|function| function.name == "selected")
            .unwrap()
            .outward_protocols,
        []
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
fn open_and_polymorphic_row_alias_syntax_is_rejected_structurally() {
    for source in [
        "cases IO = {Ask | Tail}; main() -> { () }",
        "cases IO<T> = {Ask}; main() -> { () }",
    ] {
        let errors =
            compile_source_to_bytecode("unsupported-row-alias.glorious", source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.span.is_some() && error.code.is_some())
        );
    }
}

#[test]
fn resumptive_transitive_call_rows_have_exact_metadata_cleanup_and_result() {
    let artifact = compile_source_to_bytecode("transitive.glorious", TRANSITIVE).unwrap();
    let ask = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Ask")
        .expect("Ask must have a protocol descriptor") as u32;
    for name in ["leaf", "forward"] {
        assert_eq!(
            artifact
                .functions
                .iter()
                .find(|function| function.name == name)
                .unwrap()
                .outward_protocols,
            [ask]
        );
    }
    let ask_handler = artifact
        .handler_defs
        .iter()
        .position(|definition| {
            definition
                .clauses
                .iter()
                .any(|clause| clause.protocol == ask)
        })
        .expect("Ask must have a handler descriptor");
    let body_name = format!("$handler${ask_handler}$body");
    let body_id = artifact
        .functions
        .iter()
        .position(|function| function.name == body_name)
        .unwrap() as u32;
    let body = &artifact.functions[body_id as usize];
    let call = artifact.code[body.code_start as usize..(body.code_start + body.code_len) as usize]
        .iter()
        .position(|instruction| matches!(instruction, Instruction::Call { .. }))
        .unwrap() as u32;
    assert!(artifact.cleanups.iter().any(|plan| {
        plan.function == body_id
            && plan.first_instruction <= call
            && call < plan.end_instruction
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
fn mandatory_one_shot_outward_call_transfers_exact_linear_argument_and_result() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        relay(ticket: Ticket) -> Ticket / {Ask} {
            let ignored = perform Ask::ask();
            ticket
        }
        selected() -> i64 {
            let outgoing = Ticket { serial: 42 };
            handle {
                let incoming = relay(outgoing);
                let Ticket { serial } = incoming;
                serial
            } {
                Ask::ask() with continuation => resume(continuation, 0)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("linear-one-shot-call.glorious", source).unwrap();
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
fn mandatory_one_shot_outward_call_preserves_a_live_shared_loan() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        ask() -> i64 / {Ask} { perform Ask::ask() }
        selected() -> i64 {
            let value = 40;
            let reference = &value;
            handle { let answer = ask(); reference; answer } {
                Ask::ask() with continuation => resume(continuation, 42)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("mandatory-call-loan.glorious", source).unwrap();
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
fn terminal_sibling_in_an_outward_row_blocks_positive_lower_capture_relaxation() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        effect Ask { [1,1] ask() -> i64 }
        effect Stop { stop() -> ! }
        mixed() -> i64 / {Ask, Stop} { perform Stop::stop() }
        selected() -> i64 {
            handle {
                let ticket = Ticket { serial: 42 };
                let ignored = mixed();
                let Ticket { serial } = ticket;
                serial
            } {
                Ask::ask() with continuation => resume(continuation, 0),
                Stop::stop() => 0
            }
        }
        main() -> { () }
    "#;
    let diagnostics =
        compile_source_to_bytecode("mixed-row-linear-capture.glorious", source).unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1BC001")
                && diagnostic.message.contains("path-sensitive Use analysis")
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
fn optional_outward_call_cancellation_cleans_up_affine_caller_capture() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        impl Drop for Resource {
            drop(&mut self) -> { () }
        }
        effect Stop { [0,1] stop() -> i64 }
        stop() -> i64 / {Stop} { perform Stop::stop() }
        selected() -> i64 {
            handle {
                let resource = Resource { marker: 1 };
                stop() + 1000
            } {
                Stop::stop() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("affine-optional-call.glorious", source).unwrap();
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
fn two_shot_outward_call_replays_independent_snapshots() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        choose() -> i64 / {Choose} { perform Choose::choose() }
        test() -> i64 {
            handle { let selected = choose(); selected + 1 } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("two-shot-call.glorious", source).unwrap();
    assert_eq!(
        artifact.required_features,
        1 | (1 << 1) | (1 << 3) | (1 << 4)
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
fn two_shot_outward_call_multiplies_a_live_exact_caller_owner() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        choose() -> i64 / {Choose} { perform Choose::choose() }
        test() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let selected = choose();
                let Ticket { marker } = ticket;
                marker + selected
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("two-shot-call-owned-capture.glorious", source).unwrap();
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
fn two_shot_row_without_an_actual_perform_does_not_multiply_ownership() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[2,2]> for Ticket {}
        maybe_choose() -> i64 / {Choose} { 41 }
        test() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let selected = maybe_choose();
                let Ticket { marker } = ticket;
                marker + selected
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(move k, 41)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("two-shot-may-effect-call.glorious", source).unwrap();
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
fn named_rows_are_canonical_and_phase_fingerprints_are_deterministic() {
    let source = r#"
        effect Second { stop() -> ! }
        effect First { stop() -> ! }
        declared() -> / {First, Second, First} { () }
        empty() -> / {} { () }
        main() -> { () }
    "#;
    let first = compile_source_to_phases("rows.glorious", source).unwrap();
    let second = compile_source_to_phases("rows.glorious", source).unwrap();
    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let declared = first
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "declared")
        .unwrap();
    let mut declared_protocols = ["First", "Second"].map(|name| {
        first
            .artifact
            .protocols
            .iter()
            .position(|protocol| protocol.display_name == name)
            .unwrap() as u32
    });
    declared_protocols.sort_unstable();
    assert_eq!(declared.outward_protocols, declared_protocols);
    let outward = format!("outward={declared_protocols:?}");
    assert!(first.core.canonical_text().contains(&outward));
    assert!(first.mir.canonical_text().contains(&outward));
    assert!(
        first
            .artifact
            .functions
            .iter()
            .find(|function| function.name == "empty")
            .unwrap()
            .outward_protocols
            .is_empty()
    );
}

#[test]
fn outward_call_bundle_and_interpreter_match_the_vm() {
    let bundle = SourceBundle::distributed(
        Segment::new("effects.glorious", "effect Ask { [1,1] ask() -> i64 }"),
        [
            Segment::new(
                "library.glorious",
                "leaf() -> i64 / {Ask} { perform Ask::ask() } test() -> i64 { handle { let value = leaf(); value + 2 } { Ask::ask() with k => resume(k, 40) } }",
            ),
            Segment::new("entry.glorious", "main() -> { let result = test(); () }"),
        ],
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
        effect Ask { [1,1] ask() -> i64 }
        leaf() -> i64 / {Ask} { perform Ask::ask() }
        test() -> i64 {
            handle { let value = leaf(); value + 2 } {
                Ask::ask() with k => resume(k, 40)
            }
        }
        main() -> { let result = test(); () }
    "#;
    assert_eq!(
        run_source("row-differential.glorious", source, vec![], &mut NoHost).unwrap(),
        InterpreterValue::Unit
    );
    let artifact = compile_source_to_bytecode("row-differential.glorious", source).unwrap();
    let entry = artifact.entry_function.unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(entry, vec![])
            .unwrap(),
        Value::Unit
    );
}

#[test]
fn resumptive_effect_in_a_terminal_payload_resumes_before_the_terminal_handler_runs() {
    let source = r#"
        effect Outer { stop(value: i64) -> ! }
        effect Ask { [1,1] ask() -> i64 }
        ask() -> i64 / {Ask} { perform Ask::ask() }
        selected() -> i64 {
            handle perform Outer::stop(ask()) {
                Outer::stop(value) => value,
                Ask::ask() with continuation => resume(continuation, 1)
            }
        }
        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("resumptive-terminal-payload.glorious", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(1)
    );
}

#[test]
fn invalid_named_effect_rows_and_calls_have_stable_diagnostics() {
    let cases = [
        (
            "effect Stop { stop() -> ! } bad() -> / {Missing} { () } main() -> { () }",
            "is not a declared monomorphic effect",
        ),
        (
            "effect Stop { stop() -> ! } bad() -> / {Stop<i64>} { () } main() -> { () }",
            "expects 0 type argument",
        ),
        (
            "effect Fail<E> { fail(error:E) -> ! } bad() -> / {Fail<i64, Text>} { () } main() -> { () }",
            "expects 1 type argument",
        ),
        (
            "effect Fail<E> { fail(error:E) -> ! } bad() -> / {Fail<E>} { () } main() -> { () }",
            "unresolved",
        ),
        (
            "effect Fail<E> { fail(error:E) -> ! } bad<e: EffectRow>() -> / {Fail<e>} { () } main() -> { () }",
            "effect-row parameter",
        ),
        (
            "effect Stop { stop() -> ! } stop_with() -> i64 / {Stop} { perform Stop::stop() } bad() -> i64 { stop_with() } main() -> { () }",
            "requires outward effect protocol(s) not declared here",
        ),
        (
            "effect First { stop() -> ! } effect Second { stop() -> ! } bad() -> i64 / {First} { perform Second::stop() } main() -> { () }",
            "perform must be covered by a lexical handler or declared",
        ),
        (
            "effect Stop { stop() -> ! } main() -> / {Stop} { () }",
            "declare no outward effects",
        ),
        (
            "effect First { stop() -> ! } effect Second { stop() -> ! } both() -> i64 / {First, Second} { perform First::stop() } bad() -> i64 { handle { both() } { First::stop() => 1 } } main() -> { () }",
            "partial effect handler",
        ),
    ];
    for (source, needle) in cases {
        let diagnostics = compile_source_to_bytecode("rejected.glorious", source).unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains(needle)
                    && matches!(
                        diagnostic.code.as_deref(),
                        Some("G1BC001" | "G1BC002" | "G1BC003")
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
