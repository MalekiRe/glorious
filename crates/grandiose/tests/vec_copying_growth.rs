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
    struct CopyItem { value: i64 }
    impl Use<[0,infinity]> for CopyItem {}

    empty_i64() -> Vec<i64> { Vec::new() }
    empty_items() -> Vec<CopyItem> { Vec::new() }

    resize_and_extend() -> i64 {
        let target = empty_i64();
        Vec::resize(&mut target, 3, 7);
        Vec::resize(&mut target, 1, 99);

        let source = empty_i64();
        Vec::push(&mut source, 2);
        Vec::push(&mut source, 3);
        let source_view = Vec::as_slice(&source);
        Vec::extend_from_slice(&mut target, move source_view);

        let first_ref = Vec::index(&target, 0);
        let first = *first_ref;
        let second_ref = Vec::index(&target, 1);
        let second = *second_ref;
        let third_ref = Vec::index(&target, 2);
        first * 100 + second * 10 + *third_ref
    }

    resize_to_zero() -> usize {
        let values = empty_i64();
        Vec::resize(&mut values, 4, 8);
        Vec::resize(&mut values, 0, 9);
        Vec::len(&values)
    }

    copy_generic_nominals() -> usize {
        let source = empty_items();
        Vec::resize(&mut source, 2, CopyItem { value: 4 });
        let target = empty_items();
        let source_view = Vec::as_slice(&source);
        Vec::extend_from_slice(&mut target, move source_view);
        Vec::len(&source) + Vec::len(&target)
    }

    main() -> () { () }
"#;

#[test]
fn vec_resize_and_extend_from_slice_execute_at_optimized_levels() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "vec-copying-growth.glorious",
            POSITIVE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        for (name, expected) in [
            ("resize_and_extend", Value::I64(723)),
            ("resize_to_zero", Value::U64(0)),
            ("copy_generic_nominals", Value::U64(4)),
        ] {
            assert_eq!(
                vm.run(function_id(&artifact, name), vec![]).unwrap(),
                expected,
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn copying_vec_operations_reject_nonduplicable_elements() {
    for (operation, call) in [
        ("resize", "Vec::resize(&mut values, 0, ticket(2));"),
        (
            "extend_from_slice",
            "let view = Vec::as_slice(&values); Vec::extend_from_slice(&mut target, move view);",
        ),
    ] {
        let source = format!(
            r#"
                struct Ticket {{ serial: i64 }}
                impl Use<[1,1]> for Ticket {{}}
                empty() -> Vec<Ticket> {{ Vec::new() }}
                ticket(serial: i64) -> Ticket {{ Ticket {{ serial: move serial }} }}
                bad() -> (Vec<Ticket>, Vec<Ticket>) {{
                    let values = empty();
                    Vec::push(&mut values, ticket(1));
                    let target = empty();
                    {call}
                    (move values, move target)
                }}
                main() -> () {{ () }}
            "#
        );
        let errors =
            compile_source_to_bytecode(&format!("linear-vec-{operation}.glorious"), &source)
                .expect_err("copying Vec operations must reject exact-linear elements");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("Use") || error.message.contains("not a callable")
            }),
            "{operation}: {errors:#?}"
        );
    }
}
