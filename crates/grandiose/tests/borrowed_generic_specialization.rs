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
fn borrowed_option_predicate_grounds_nested_generic_result_construction() {
    let source = r#"
        is_missing(value: &Option<usize>) -> Bool {
            Option::is_none(value)
        }

        same_missing(left: Option<usize>, right: Option<usize>) -> Bool {
            handle left {
                Result::Err(_) => Option::is_none(&right),
                Result::Ok(left_index) => handle right {
                    Result::Err(_) => false,
                    Result::Ok(right_index) => left_index == right_index
                }
            }
        }

        missing() -> Option<usize> { None }
        missing_u32() -> Option<u32> { None }

        lookup(owner: Option<usize>) -> Result<Option<u32>, u8> {
            let found = missing_u32();
            handle move found {
                Result::Ok(index) =>
                    Result::Ok(Result::Ok(index)),
                Result::Err(_) => if(Option::is_none(&owner)) {
                    Result::Ok(Result::Err(()))
                } else {
                    Result::Ok(Result::Err(()))
                }
            }
        }

        selected() -> u64 {
            let value = missing();
            if(is_missing(&value)
                and { same_missing(missing(), missing()) }
                and { Result::is_ok(lookup(missing())) }) {
                1
            } else {
                0
            }
        }

        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode_with_options(
        "borrowed-option-predicate-specialization.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    assert_eq!(
        Vm::new(verify(artifact.clone()).unwrap())
            .run(function_id(&artifact, "selected"), vec![])
            .unwrap(),
        Value::U64(1),
    );
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
