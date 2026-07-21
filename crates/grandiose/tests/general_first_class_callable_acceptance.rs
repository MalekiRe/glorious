//! Task-5 end-to-end acceptance matrix for general first-class callables.
//!
//! Success cases execute at every optimization level, including recursive
//! closure self-calls through handlers.

use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Instruction, Value, Vm, verify};

fn compile_and_run(source_name: &str, source: &str) -> (grandiose_vm::Artifact, Value) {
    let mut first = None;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .unwrap()
        .artifact;
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .expect("answer function") as u32;
        let value = Vm::new(verify(artifact.clone()).unwrap())
            .run(answer, vec![])
            .unwrap();
        if first.is_none() {
            first = Some((artifact, value));
        }
    }
    first.unwrap()
}

fn assert_rejected(source_name: &str, source: &str, message: &str) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let diagnostics = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("unsafe first-class callable program compiled");
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains(message)),
            "{optimization_level:?}: expected diagnostic containing {message:?}, got {diagnostics:#?}"
        );
    }
}

#[test]
fn explicit_parameter_closure_captures_resumption_and_is_invoked_later() {
    let source = r#"
        effect Stop { [1,1] stop() -> i64 }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let finish = (value: i64) -> i64 {
                        resume(move continuation, value)
                    };
                    let later = move finish;
                    move later(42)
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("late-explicit-resumption.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn late_resumption_callable_carries_a_shared_reference_through_generic_formation() {
    let source = r#"
        effect Stop { [1,1] stop() -> i64 }
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let base = 40;
            let borrowed = &base;
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let finish = (amount: i64) -> i64 {
                        resume(move continuation, *borrowed + amount)
                    };
                    let escaped = retain(move finish);
                    move escaped(2)
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("late-reference-resumption-callable.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn escaping_noncopy_owned_closure_survives_a_generic_boundary() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let ticket = Ticket { value: 40 };
            let closure = (amount: i64) -> i64 {
                let Ticket { value } = move ticket;
                value + amount
            };
            let escaped = retain(move closure);
            move escaped(2)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("escaping-noncopy-callable.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn aggregate_wrapped_resumption_is_captured_by_an_explicit_callable() {
    let source = r#"
        effect Stop { [1,1] stop() -> i64 }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let stored = (move continuation, 40);
                    let finish = (amount: i64) -> i64 {
                        let (restored, base) = move stored;
                        resume(move restored, base + amount)
                    };
                    move finish(2)
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("aggregate-resumption-callable.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn recursive_closure_can_capture_its_own_nominal_identity() {
    let source = r#"
        effect RecurCase { select(value: i64) -> ! }
        answer() -> i64 {
            let recurse = (remaining: i64) -> i64 {
                handle perform RecurCase::select(remaining) {
                    RecurCase::select(0) => 42,
                    RecurCase::select(value) => recurse(value - 1)
                }
            };
            recurse(3)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("recursive-closure.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn recursive_closure_reuses_its_captured_environment_through_a_handler() {
    let source = r#"
        effect RecurCapture { select(value: i64) -> ! }
        answer() -> i64 {
            let base = 40;
            let recurse = (remaining: i64) -> i64 {
                handle perform RecurCapture::select(remaining) {
                    RecurCapture::select(0) => base + 2,
                    RecurCapture::select(value) => recurse(value - 1)
                }
            };
            recurse(3)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("recursive-captured-closure.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn indirect_calls_select_observe_and_move_receiver_modes() {
    let source = r#"
        answer() -> i64 {
            let base = 21;
            let observe = () -> i64 { base };
            observe() + move observe()
        }
        main() -> { () }
    "#;
    let (artifact, value) = compile_and_run("receiver-mode-matrix.gr", source);
    assert_eq!(value, Value::I64(42));
    for expected in [0, 2] {
        assert!(
            artifact.code.iter().any(|instruction| matches!(
                instruction,
                Instruction::CallIndirect { receiver_mode, .. } if *receiver_mode == expected
            )),
            "missing indirect receiver mode {expected}"
        );
    }
}

#[test]
fn move_capture_selects_owned_receiver_mode() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        answer() -> i64 {
            let ticket = Ticket { value: 42 };
            let consume = () -> i64 {
                let Ticket { value } = move ticket;
                value
            };
            move consume()
        }
        main() -> { () }
    "#;
    let (artifact, value) = compile_and_run("owned-receiver-mode.gr", source);
    assert_eq!(value, Value::I64(42));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 2,
            ..
        }
    )));
}

#[test]
fn indirect_mutating_capture_selects_unique_receiver_mode() {
    let source = r#"
        answer() -> i64 {
            let state = 40;
            let mutate = () -> i64 { state = state + 1; state };
            mutate()
        }
        main() -> { () }
    "#;
    let (artifact, value) = compile_and_run("mutating-receiver-mode.gr", source);
    assert_eq!(value, Value::I64(41));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 1,
            ..
        }
    )));
}

#[test]
fn generic_specialization_transports_a_resumption_closure() {
    let source = r#"
        effect Stop { [1,1] stop() -> i64 }
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let finish = { => resume(move continuation, 42) };
                    let escaped = retain(move finish);
                    move escaped()
                }
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("generic-resumption-callable.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn contextual_reference_capture_is_valid_within_the_call_lifetime() {
    let source = r#"
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        answer() -> i64 {
            let value = 40;
            let borrowed = &value;
            invoke(() -> i64 { *borrowed + 2 })
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("contextual-reference-environment.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn shared_reference_environment_escapes_a_generic_boundary_within_its_lifetime() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let value = 42;
            let borrowed = &value;
            let closure = () -> i64 { *borrowed };
            let escaped = retain(move closure);
            move escaped()
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("lifetime-bounded-reference-environment.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn inline_typed_callable_is_formed_directly_as_a_generic_result() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let value = 42;
            let borrowed = &value;
            let escaped = retain(() -> i64 { *borrowed });
            move escaped()
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("inline-generic-callable-formation.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn qualified_associated_callable_alias_forms_a_first_class_value() {
    let source = r#"
        struct Namespace { private marker: () }
        increment(value: i64) -> i64 { value + 1 }
        let Namespace::increment = increment;
        answer() -> i64 {
            let callable = Namespace::increment;
            callable(41)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("qualified-associated-callable-value.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn qualified_associated_callable_value_preserves_its_outward_effect_row() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Namespace { private marker: () }
        add_answer(value: i64) -> i64 / {Ask} {
            value + perform Ask::ask()
        }
        let Namespace::add_answer = add_answer;
        answer() -> i64 {
            let callable = Namespace::add_answer;
            handle callable(40) {
                Ask::ask() with continuation => resume(move continuation, 2)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("qualified-effectful-callable-value.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn generic_associated_function_item_specializes_from_callable_context() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        invoke<T, F>(value: T, body: F) -> T
            where F: Fn<(T), Output=T> { body(value) }
        let Namespace::apply_identity = generic_identity;
        answer() -> i64 { invoke(42, Namespace::apply_identity) }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("generic-associated-function-item.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn deferred_generic_function_item_specializes_at_its_first_later_call() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        let Namespace::apply_identity = generic_identity;
        answer() -> i64 {
            let callable = Namespace::apply_identity;
            callable(42)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("deferred-generic-function-item.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn deferred_generic_function_item_preserves_effects_and_where_evidence() {
    let source = r#"
        trait Approved {}
        impl Approved for i64 {}
        effect Ask { [1,1] ask() -> }
        struct Namespace { private marker: () }
        checked<T>(value: T) -> T / {Ask} where T: Approved {
            perform Ask::ask();
            value
        }
        let Namespace::checked = checked;
        answer() -> i64 {
            let callable = Namespace::checked;
            handle callable(42) {
                Ask::ask() with continuation => resume(move continuation, ())
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("deferred-effectful-constrained-function-item.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn deferred_generic_function_item_allows_multiple_consistent_uses() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        let Namespace::apply_identity = generic_identity;
        answer() -> i64 {
            let callable = Namespace::apply_identity;
            callable(21) + callable(21)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("consistent-deferred-function-item.gr", source).1,
        Value::I64(42)
    );
}

#[test]
fn deferred_generic_function_item_rejects_conflicting_later_shapes() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        let Namespace::apply_identity = generic_identity;
        answer() -> i64 {
            let callable = Namespace::apply_identity;
            let first = callable(42);
            let second = callable("conflict");
            first
        }
        main() -> { () }
    "#;
    assert_rejected(
        "conflicting-deferred-function-item.gr",
        source,
        "expected i64, found Text",
    );
}

#[test]
fn deferred_generic_function_item_cannot_escape_without_a_shape() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        let Namespace::apply_identity = generic_identity;
        answer() -> {
            let callable = Namespace::apply_identity;
            callable
        }
        main() -> { () }
    "#;
    assert_rejected(
        "unresolved-deferred-function-item-escape.gr",
        source,
        "escapes before a concrete callable shape is proven",
    );
}

#[test]
fn deferred_generic_function_item_cannot_be_stored_before_shape_resolution() {
    let source = r#"
        struct Namespace { private marker: () }
        generic_identity<T>(value: T) -> T { value }
        let Namespace::apply_identity = generic_identity;
        answer() -> {
            let callable = Namespace::apply_identity;
            let stored = (callable,);
            ()
        }
        main() -> { () }
    "#;
    assert_rejected(
        "unresolved-deferred-function-item-storage.gr",
        source,
        "escapes before a concrete callable shape is proven",
    );
}

#[test]
fn reference_environment_cannot_outlive_its_referent_scope() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let escaped = {
                let value = 42;
                let borrowed = &value;
                let closure = () -> i64 { *borrowed };
                retain(move closure)
            };
            move escaped()
        }
        main() -> { () }
    "#;
    assert_rejected("outlived-reference-environment.gr", source, "cannot escape");
}

#[test]
fn unique_reference_environment_remains_rejected_without_owned_reborrow_evidence() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let value = 42;
            let borrowed = &mut value;
            let closure = () -> i64 { *borrowed };
            let escaped = retain(move closure);
            move escaped()
        }
        main() -> { () }
    "#;
    assert_rejected(
        "unique-reference-environment.gr",
        source,
        "unique borrowed captures cannot escape",
    );
}

#[test]
fn shared_reference_environment_keeps_its_referent_borrowed_until_consumed() {
    let source = r#"
        answer() -> i64 {
            let value = 42;
            let borrowed = &value;
            let closure = () -> i64 { *borrowed };
            let conflicting = &mut value;
            let result = move closure();
            *conflicting = 0;
            result
        }
        main() -> { () }
    "#;
    assert_rejected(
        "reference-environment-alias-conflict.gr",
        source,
        "incompatible live loan",
    );
}

#[test]
fn owned_noncopy_capture_cannot_be_observed_after_it_moved_into_a_closure() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        answer() -> i64 {
            let ticket = Ticket { value: 42 };
            let closure = () -> i64 {
                let Ticket { value } = move ticket;
                value
            };
            let Ticket { value } = ticket;
            move closure() + value
        }
        main() -> { () }
    "#;
    assert_rejected("moved-capture-reuse.gr", source, "was already moved");
}
