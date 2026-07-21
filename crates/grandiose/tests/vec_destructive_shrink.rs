use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::{Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const POSITIVE: &str = r#"
    struct Scrap { serial: i64 }
    impl Use<[0,1]> for Scrap {}

    empty_i64() -> Vec<i64> { Vec::new() }
    empty_scrap() -> Vec<Scrap> { Vec::new() }

    truncate_and_clear() -> i64 {
        let values = empty_i64();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        Vec::truncate(&mut values, 2);
        Vec::truncate(&mut values, 99);
        let first_ref = Vec::index(&values, 0);
        let first = *first_ref;
        let second_ref = Vec::index(&values, 1);
        let kept = first + *second_ref;
        Vec::clear(&mut values);
        kept
    }

    truncate_length() -> usize {
        let values = empty_i64();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        Vec::truncate(&mut values, 2);
        Vec::truncate(&mut values, 99);
        Vec::len(&values)
    }

    clear_affine_elements() -> usize {
        let values = empty_scrap();
        Vec::push(&mut values, Scrap { serial: 1 });
        Vec::push(&mut values, Scrap { serial: 2 });
        Vec::clear(&mut values);
        Vec::len(&values)
    }

    main() -> () { () }
"#;

#[test]
fn vec_truncate_and_clear_execute_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "vec-destructive-shrink.glorious",
            POSITIVE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(function_id(&artifact, "truncate_and_clear"), vec![])
                .unwrap(),
            Value::I64(30),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(function_id(&artifact, "truncate_length"), vec![])
                .unwrap(),
            Value::U64(2),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(function_id(&artifact, "clear_affine_elements"), vec![])
                .unwrap(),
            Value::U64(0),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn vec_destructive_shrink_rejects_must_move_elements() {
    for operation in ["clear", "truncate"] {
        let call = if operation == "clear" {
            "Vec::clear(&mut values);"
        } else {
            "Vec::truncate(&mut values, 0);"
        };
        let source = format!(
            r#"
                struct Ticket {{ serial: i64 }}
                impl Use<[1,1]> for Ticket {{}}
                empty() -> Vec<Ticket> {{ Vec::new() }}
                bad() -> Vec<Ticket> {{
                    let values = empty();
                    Vec::push(&mut values, Ticket {{ serial: 1 }});
                    {call}
                    values
                }}
                main() -> () {{ () }}
            "#
        );
        let errors =
            compile_source_to_bytecode(&format!("linear-vec-{operation}.glorious"), &source)
                .expect_err(
                    "must-move elements must not satisfy destructive shrinking's zero-use bound",
                );
        assert!(
            errors.iter().any(|error| {
                error.message.contains("Use") || error.message.contains("not a callable")
            }),
            "{operation}: {errors:#?}"
        );
    }
}
