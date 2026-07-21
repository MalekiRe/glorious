use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::{Value, Vm, verify};

const POSITIVE: &str = r#"
    struct Erased { value: i64 }
    struct Wrapper<T> { value: T }
    impl Use<[0,1]> for Erased {}
    impl<T> Use<[0,1]> for Wrapper<T> where T: Use<[0,1]> {}

    discard<T>(value: T) -> () where T: Use<[0,0]> {
        value;
        ()
    }

    discard_pair<T>(left: T, right: T) -> () where T: Use<[0,0]> {
        discard(move left);
        discard(move right)
    }

    erase_pair() -> () {
        discard_pair(Erased { value: 1 }, Erased { value: 2 })
    }

    discard_integer() -> () { discard(42) }
    discard_wrapper() -> () { discard(Wrapper { value: 42 }) }
    main() -> () { () }
"#;

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

#[test]
fn zero_use_evidence_propagates_through_nested_generic_calls_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-zero-use.glorious",
            POSITIVE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        for name in ["erase_pair", "discard_integer", "discard_wrapper"] {
            assert_eq!(
                vm.run(function_id(&artifact, name), vec![]).unwrap(),
                Value::Unit,
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn zero_use_generic_call_rejects_a_must_move_argument() {
    let source = r#"
        struct Ticket { serial: i64 }
        discard<T>(value: T) -> () where T: Use<[0,0]> {
            value;
            ()
        }
        bad() -> () { discard(Ticket { serial: 1 }) }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("generic-zero-use-negative.glorious", source)
        .expect_err("must-move Ticket must not satisfy Use<[0,0]>");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Use")
                && (error.message.contains("no matching implementation")
                    || error.message.contains("principal"))
        }),
        "{errors:#?}"
    );
}
