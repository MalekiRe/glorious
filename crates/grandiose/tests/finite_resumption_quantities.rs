use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Type, Value, Vm, verify};

#[test]
fn exact_four_shot_resumption_replays_four_independent_snapshots() {
    let source = r#"
        effect Choose { [4,4] choose() -> i64 }
        selected() -> i64 {
            handle {
                let retained = 40;
                let choice = perform Choose::choose();
                retained + choice
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 1);
                    let second = resume(continuation, 2);
                    let third = resume(continuation, 3);
                    let fourth = resume(move continuation, 4);
                    first + second + third + fourth
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("four-shot.gr", source).unwrap();
    let choose = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Choose")
        .expect("Choose must have a protocol descriptor") as u32;
    let resumption = artifact
        .handler_defs
        .iter()
        .flat_map(|definition| &definition.clauses)
        .find(|clause| clause.protocol == choose)
        .and_then(|clause| clause.resumption_type)
        .expect("Choose must have a four-shot resumption descriptor");
    assert!(matches!(
        artifact.types[resumption as usize].representation(),
        Type::Resumption {
            lower_uses: 4,
            upper_uses: Some(4),
            copy: true,
            ..
        }
    ));
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(170)
    );
}

#[test]
fn exact_four_shot_call_multiplies_a_live_exact_owner_by_four() {
    let source = r#"
        effect Choose { [4,4] choose() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[4,4]> for Ticket {}
        leaf() -> i64 / {Choose} { perform Choose::choose() }
        selected() -> i64 {
            handle {
                let ticket = Ticket { marker: 1 };
                let choice = leaf();
                let Ticket { marker } = ticket;
                marker + choice
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 1);
                    let second = resume(continuation, 2);
                    let third = resume(continuation, 3);
                    let fourth = resume(move continuation, 4);
                    first + second + third + fourth
                }
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("four-shot-owner.gr", source).unwrap();
    assert!(
        phases
            .core
            .canonical_text()
            .contains("performance \"leaf\" normal=[4] abandon=false widened=false")
    );
    let selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(14)
    );
}

#[test]
fn exact_four_shot_handler_rejects_under_and_over_resumption() {
    let cases = [
        (
            "effect Choose { [4,4] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let a = resume(k, 1); let b = resume(k, 2); resume(move k, 3) } } } main() -> { () }",
            "must be resumed exactly 4 time(s)",
        ),
        (
            "effect Choose { [4,4] choose() -> i64 } bad() -> i64 { handle perform Choose::choose() { Choose::choose() with k => { let a = resume(k, 1); let b = resume(k, 2); let c = resume(k, 3); let d = resume(k, 4); resume(move k, 5) } } } main() -> { () }",
            "resumed more than 4 time(s)",
        ),
    ];
    for (source, expected) in cases {
        let diagnostics = compile_source_to_bytecode("invalid-four-shot.gr", source).unwrap_err();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(expected)),
            "{diagnostics:#?}"
        );
    }
}
