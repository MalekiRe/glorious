use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Value, Vm, verify};

const SOURCE: &str = r#"
    ok(value: i64) -> Result<i64, i64> { Result::Ok(value) }
    err(value: i64) -> Result<i64, i64> { Result::Err(value) }
    some(value: i64) -> Option<i64> { Option::Some(value) }
    none() -> Option<i64> { None }
    result_is_ok() -> i64 {
        if(Result::is_ok(ok(1))) { 1 } else { 0 }
    }
    result_is_err() -> i64 {
        if(Result::is_err(err(1))) { 2 } else { 0 }
    }
    option_is_some() -> i64 {
        if(Option::is_some(some(1))) { 3 } else { 0 }
    }
    option_is_none() -> i64 {
        if(Option::is_none(none())) { 4 } else { 0 }
    }

    result_map_ok() -> i64 {
        Result::unwrap_or(
            Result::map(ok(10), (value: i64) -> i64 { value + 1 }),
            0
        )
    }
    result_map_err_passthrough() -> i64 {
        Result::unwrap_or(
            not(Result::map(err(12), (value: i64) -> i64 { value + 100 })),
            0
        )
    }
    result_map_err() -> i64 {
        Result::unwrap_or(
            not(Result::map_err(err(5), (error: i64) -> i64 { error + 8 })),
            0
        )
    }
    result_and_then() -> i64 {
        Result::unwrap_or(
            Result::and_then(
                ok(7),
                (value: i64) -> Result<i64, i64> { ok(value * 2) }
            ),
            0
        )
    }
    result_or_else() -> i64 {
        Result::unwrap_or(
            Result::or_else(
                err(9),
                (error: i64) -> Result<i64, i64> { ok(error + 6) }
            ),
            0
        )
    }
    result_unwrap_ok() -> i64 { Result::unwrap_or(ok(16), 0) }
    result_unwrap_err() -> i64 { Result::unwrap_or(err(1), 17) }

    option_map() -> i64 {
        Option::unwrap_or(
            Option::map(some(8), (value: i64) -> i64 { value + 10 }),
            0
        )
    }
    option_and_then() -> i64 {
        Option::unwrap_or(
            Option::and_then(
                some(9),
                (value: i64) -> Option<i64> { some(value + 10) }
            ),
            0
        )
    }
    option_or_else() -> i64 {
        Option::unwrap_or(
            Option::or_else(
                none(),
                () -> Option<i64> { some(20) }
            ),
            0
        )
    }
    option_unwrap_none() -> i64 { Option::unwrap_or(none(), 21) }

    main() -> () { () }
"#;

#[test]
fn distributed_result_and_option_combinators_execute_with_o0_o3_parity() {
    let expected = [
        ("result_is_ok", 1),
        ("result_is_err", 2),
        ("option_is_some", 3),
        ("option_is_none", 4),
        ("result_map_ok", 11),
        ("result_map_err_passthrough", 12),
        ("result_map_err", 13),
        ("result_and_then", 14),
        ("result_or_else", 15),
        ("result_unwrap_ok", 16),
        ("result_unwrap_err", 17),
        ("option_map", 18),
        ("option_and_then", 19),
        ("option_or_else", 20),
        ("option_unwrap_none", 21),
    ];
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "result-option-combinators.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(artifact.clone()).unwrap();
        for (name, answer) in expected {
            let function = artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap_or_else(|| panic!("missing `{name}`")) as u32;
            assert_eq!(
                Vm::new(verified.clone()).run(function, vec![]).unwrap(),
                Value::I64(answer),
                "{optimization_level:?} {name}"
            );
        }
    }
}
