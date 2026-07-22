use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const BORROW_EVIDENCE: &str = r#"
    make_u64() -> u64 { 40 }
    make_vec() -> Vec<u64> { Vec::new() }

    select_shared<T>(value: &T, fallback: T) -> T { fallback }

    shared_borrow_uses_nondefault_evidence() -> () {
        let value = make_u64();
        select_shared(&value, 2);
        ()
    }

    populated_vec_can_be_iterated() -> u64 {
        let values = make_vec();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        let iterator = Vec::iter(&values);
        SliceIter::next(&mut iterator);
        wrapping_convert_to_u64(Vec::len(&values))
    }

    main() -> () { () }
"#;

#[test]
fn borrow_derived_generic_evidence_precedes_numeric_defaults_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "borrowed-generic-specialization.glorious",
            BORROW_EVIDENCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(
                function_id(&artifact, "populated_vec_can_be_iterated"),
                vec![]
            )
            .unwrap(),
            Value::U64(2),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(
                function_id(&artifact, "shared_borrow_uses_nondefault_evidence"),
                vec![],
            )
            .unwrap(),
            Value::Unit,
            "{optimization_level:?}",
        );
    }
}

#[test]
fn contradictory_borrow_and_value_evidence_is_rejected_in_every_mode() {
    let source = r#"
        make_u64() -> u64 { 40 }
        select_shared<T>(value: &T, fallback: T) -> T { fallback }
        bad() -> () {
            let value = make_u64();
            select_shared(&value, "not a u64");
            ()
        }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_bytecode_with_options(
            "contradictory-borrow-evidence.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("contradictory generic evidence must not be overwritten");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("ambiguous generic arguments")
                    || error.message.contains("type mismatch")
                    || error
                        .message
                        .contains("is not a callable in this compilation unit")
            }),
            "{optimization_level:?}: {errors:#?}",
        );
    }
}
