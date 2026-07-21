use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn two_shared_origins_construct_call_project_deconstruct_and_drop() {
    let source = r#"
        forward<'a>(value: (&'a i64, &'a i64)) -> (&'a i64, &'a i64) { move value }

        first<'a>(value: (&'a i64, &'a i64)) -> &'a i64 { value.0 }

        sum<'a>(value: (&'a i64, &'a i64)) -> i64 {
            let (left, right) = value;
            *left + *right
        }

        answer() -> i64 {
            let left = 20;
            let right = 22;
            let projected_pair = forward((&left, &right));
            let first_ref = projected_pair.0;
            let projected = *first_ref;
            let pair = (&left, &right);
            let selected_pair = (&left, &right);
            let selected_ref = first(move selected_pair);
            let selected = *selected_ref;
            projected + sum(forward(move pair)) + selected
        }

        drop_pair() -> () {
            let left = 1;
            let right = 2;
            let pair = (&left, &right);
            pair;
            ()
        }

        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "multi-origin-aggregate.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let answer = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        let drop_pair = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "drop_pair")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
            Value::I64(82)
        );
        assert_eq!(
            Vm::new(verified).run(drop_pair, vec![]).unwrap(),
            Value::Unit
        );
    }
}

#[test]
fn unproven_selected_leaf_is_rejected_as_ambiguous() {
    let source = r#"
        choose<'a>(value: (&'a i64, &'a i64)) -> &'a i64 {
            let selected = value.0;
            selected
        }

        relay<'a>(value: (&'a i64, &'a i64)) -> &'a i64 { choose(move value) }

        main() -> () { () }
    "#;
    let errors = compile_source_to_phases_with_options(
        "ambiguous-multi-origin-selection.gr",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .expect_err("an unproven reference leaf selection must not acquire a summary");
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("unambiguous structural argument mapping")
                || error
                    .message
                    .contains("exactly one region-compatible reference argument")
                || error.message.contains("reference return summary")
        }),
        "{errors:#?}"
    );
}

#[test]
fn exact_first_class_callable_transports_two_reference_result_origins() {
    let source = r#"
        selected() -> i64 {
            let left = 20;
            let right = 22;
            let relay = (value: (&i64, &i64)) -> (&i64, &i64) { move value };
            let returned = relay((&left, &right));
            let returned_left = returned.0;
            let returned_right = returned.1;
            *returned_left + *returned_right
        }

        main() -> { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "indirect-multi-origin-aggregate.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
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
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}
