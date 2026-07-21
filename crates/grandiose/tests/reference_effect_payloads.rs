use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{Value, Vm, verify};

fn run_selected_at_every_level(source_name: &str, source: &str, expected: Value) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            source_name,
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
            expected,
            "{optimization_level:?}"
        );
    }
}

#[test]
fn shared_reference_payload_reaches_a_handler_pattern() {
    let source = r#"
        effect Observe { [1,1] inspect(value: &i64) -> i64 }
        selected() -> i64 {
            let value = 42;
            handle perform Observe::inspect(&value) {
                Observe::inspect(reference) with continuation =>
                    resume(continuation, *reference)
            }
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("shared-reference-effect-payload.gr", source, Value::I64(42));
}

#[test]
fn unique_reference_payload_is_accepted_for_mandatory_one_shot_resumption() {
    let source = r#"
        effect Observe { [1,1] inspect(value: &mut i64) -> i64 }
        selected() -> i64 {
            let value = 42;
            handle perform Observe::inspect(&mut value) {
                Observe::inspect(reference) with continuation =>
                    resume(continuation, *reference)
            }
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("unique-reference-effect-payload.gr", source, Value::I64(42));
}

#[test]
fn shared_reference_result_preserves_its_payload_origin_through_resume() {
    let source = r#"
        effect Echo { [1,1] echo(value: &i64) -> &i64 }
        echoed<'a>(value: &'a i64) -> &'a i64 {
            handle perform Echo::echo(value) {
                Echo::echo(reference) with continuation =>
                    resume(continuation, reference)
            }
        }
        selected() -> i64 {
            let value = 42;
            let returned = echoed(&value);
            *returned
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("shared-reference-effect-result.gr", source, Value::I64(42));
}

#[test]
fn aggregate_reference_leaves_cross_the_effect_and_resume_together() {
    let source = r#"
        effect Echo { [1,1] echo(value: (&i64, &i64)) -> (&i64, &i64) }
        echoed<'a>(value: (&'a i64, &'a i64)) -> (&'a i64, &'a i64) {
            handle perform Echo::echo(value) {
                Echo::echo(references) with continuation =>
                    resume(continuation, references)
            }
        }
        selected() -> i64 {
            let left = 20;
            let right = 22;
            let returned = echoed((&left, &right));
            let returned_left = returned.0;
            let returned_right = returned.1;
            *returned_left + *returned_right
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("aggregate-reference-effect.gr", source, Value::I64(42));
}

#[test]
fn shared_reference_origin_survives_a_deep_resume_that_performs_again() {
    let source = r#"
        effect Echo { [1,1] echo(value: &i64) -> &i64 }
        echoed_twice<'a>(value: &'a i64) -> &'a i64 {
            handle {
                let first = perform Echo::echo(value);
                perform Echo::echo(first)
            } {
                Echo::echo(reference) with continuation =>
                    resume(continuation, reference)
            }
        }
        selected() -> i64 {
            let value = 42;
            let returned = echoed_twice(&value);
            *returned
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("deep-resume-reference-effect.gr", source, Value::I64(42));
}

#[test]
fn generic_effect_payload_and_result_preserve_reference_origin_relations() {
    let source = r#"
        effect Echo<T> { [1,1] echo(value: T) -> T }
        echoed<T>(value: T) -> T {
            handle perform Echo<T>::echo(value) {
                Echo<T>::echo(selected) with continuation =>
                    resume(continuation, selected)
            }
        }
        selected() -> i64 {
            let value = 42;
            let returned = echoed(&value);
            *returned
        }
        main() -> { () }
    "#;
    run_selected_at_every_level(
        "generic-reference-effect-relation.gr",
        source,
        Value::I64(42),
    );
}

#[test]
fn closure_projection_routes_an_effect_result_origin_through_resume() {
    let source = r#"
        effect Select<T, R> { [1,1] select(value: T) -> R }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        select_right<'a>(pair: (&'a i64, &'a i64)) -> &'a i64 {
            handle perform Select<(&'a i64, &'a i64), &'a i64>::select(pair) {
                Select<(&'a i64, &'a i64), &'a i64>::select(payload) with continuation =>
                    resume(continuation, apply(payload,
                        (projected: (&'a i64, &'a i64)) -> &'a i64 { projected.1 }))
            }
        }
        selected() -> i64 {
            let left = 7;
            let right = 42;
            *select_right((&left, &right))
        }
        main() -> { () }
    "#;
    run_selected_at_every_level(
        "closure-reference-effect-relation.gr",
        source,
        Value::I64(42),
    );
}

#[test]
fn direct_tuple_projection_reference_return_keeps_external_origin() {
    let source = r#"
        right<'a>(pair: (&'a i64, &'a i64)) -> &'a i64 { pair.1 }
        selected() -> i64 {
            let left = 7;
            let right = 42;
            *right((&left, &right))
        }
        main() -> { () }
    "#;
    run_selected_at_every_level("direct-tuple-reference-return.gr", source, Value::I64(42));
}

#[test]
fn unique_reference_payload_remains_rejected_for_multishot_resumption() {
    let source = r#"
        effect Replay { [2,2] replay(value: &mut i64) -> i64 }
        bad() -> i64 {
            let value = 1;
            handle perform Replay::replay(&mut value) {
                Replay::replay(reference) with continuation => {
                    let first = resume(continuation, *reference);
                    let second = resume(continuation, *reference);
                    first + second
                }
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("unique-multishot-effect-reject.gr", source)
        .expect_err("a unique reference payload crossed a multishot operation");
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("unique reference payloads require an at-most-one-shot operation")
    }));
}

#[test]
fn future_used_unique_reference_remains_in_the_exact_multishot_capture_set() {
    let source = r#"
        effect Replay { [2,2] replay() -> i64 }
        capture_result(value: i64) -> i64 { value }
        bad() -> i64 {
            let value = 1;
            let reference = &mut value;
            let replayed = capture_result(handle perform Replay::replay() {
                Replay::replay() with continuation => {
                    let first = resume(continuation, 20);
                    let second = resume(continuation, 22);
                    first + second
                }
            });
            *reference + replayed
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("future-unique-multishot-capture.gr", source)
        .expect_err("a future-used unique loan must remain in the continuation capture set");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("unique reference")
                || error.message.contains("multi-shot")
                || error.message.contains("active borrow")
                || error.message.contains("positive Use lower bound")
                || error.message.contains("ownership-aware MIR")
        }),
        "{errors:#?}"
    );
}

#[test]
fn reference_result_cannot_escape_a_local_referent() {
    let source = r#"
        effect Echo { [1,1] echo(value: &i64) -> &i64 }
        bad() -> &i64 {
            let value = 42;
            handle perform Echo::echo(&value) {
                Echo::echo(reference) with continuation =>
                    resume(continuation, reference)
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("reference-effect-local-escape.gr", source)
        .expect_err("an effect result escaped its local referent");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("cannot escape")
                || error.message.contains("does not outlive")
                || error.message.contains("local place")
        }),
        "{errors:#?}"
    );
}

#[test]
fn resume_cannot_send_a_clause_local_reference_into_the_suspended_computation() {
    let source = r#"
        effect Echo { [1,1] echo(seed: &i64) -> &i64 }
        bad<'a>(seed: &'a i64) -> &'a i64 {
            handle perform Echo::echo(seed) {
                Echo::echo(_) with continuation => {
                    let local = 42;
                    resume(continuation, &local)
                }
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("reference-effect-clause-local-escape.gr", source)
        .expect_err("a clause-local reference escaped through resume");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("cannot escape")
                || error.message.contains("does not outlive")
                || error.message.contains("local place")
        }),
        "{errors:#?}"
    );
}
