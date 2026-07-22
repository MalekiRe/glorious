//! Task-5 end-to-end acceptance matrix for general first-class callables.
//!
//! Success cases execute at every optimization level, including recursive
//! closure self-calls through handlers.

use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Instruction, Value, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "first-class callable test performed a host effect",
            span,
        ))
    }
}

fn compile_and_run(source_name: &str, source: &str) -> (grandiose_vm::Artifact, Value) {
    let mut first = None;
    for optimization_level in [
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
fn ordinary_control_selects_a_finite_set_of_sealed_callable_targets() {
    let source = r#"
        enum Flag { First, Second }
        struct Holder<F> { callable: F }
        answer() -> i64 {
            let flag = Flag::First();
            let selected = if(flag is Flag::First) {
                (value: i64) -> i64 { value + 1 }
            } else {
                (value: i64) -> i64 { value + 2 }
            };
            let packed = (selected,);
            let (from_tuple,) = move packed;
            let holder = Holder { callable: from_tuple };
            let Holder { callable } = move holder;
            callable(41)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("finite-callable-target-set.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "finite-callable-target-set-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn nested_generic_nominals_transport_effect_shaped_callable_arguments() {
    let source = r#"
        effect Ask { [1,1] ask(hint: i64) -> i64 }
        struct Boxed<T> { value: T }
        struct Envelope<T> { boxed: Boxed<T> }
        enum Payload<T> { Empty, Full(T) }

        answer() -> i64 / {Ask} {
            let callable = (value: i64) -> i64 / {Ask} {
                value + 2
            };
            let boxed = Boxed { value: move callable };
            let envelope = Envelope { boxed: move boxed };
            let Envelope { boxed } = move envelope;
            let Boxed { value } = move boxed;
            let spare = () -> i64 / {Ask} { 0 };
            let payload = Payload::Full(move spare);
            payload;
            move value(40)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("nested-generic-effect-callable.glorious", source).1,
        Value::I64(42)
    );
}

#[test]
fn callable_shaped_nominal_growth_is_rejected_before_layout_emission() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Grow<T> { value: T, next: Option<Grow<(T, T)>> }
        answer() -> () {
            let callable = () -> i64 / {Ask} { 42 };
            let value = Grow { value: move callable, next: None };
            value;
            ()
        }
        main() -> { () }
    "#;
    assert_rejected(
        "callable-generic-layout-growth.glorious",
        source,
        "generic nominal family expands infinitely",
    );
}

#[test]
fn finite_callable_targets_join_identical_symbolic_reference_routes() {
    let source = r#"
        enum Flag { First, Second }
        relay<'a>(value: &'a i64) -> &'a i64 { value }
        answer() -> i64 {
            let value = 42;
            let flag = Flag::First();
            let selected = if(flag is Flag::First) {
                (input: &i64) -> &i64 { input }
            } else {
                (input: &i64) -> &i64 { relay(input) }
            };
            *selected(&value)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("finite-callable-reference-route.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "finite-callable-reference-route-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn finite_callable_targets_join_one_canonical_effect_contract() {
    let source = r#"
        effect Ask { [1,1] ask(hint: i64) -> i64 }
        enum Flag { First, Second }
        answer() -> i64 {
            let flag = Flag::First();
            let selected = if(flag is Flag::First) {
                (value: i64) -> i64 / {Ask} { perform Ask::ask(value) + 2 }
            } else {
                (value: i64) -> i64 / {Ask} { 2 + perform Ask::ask(value) }
            };
            handle selected(4) {
                Ask::ask(hint) with continuation => resume(continuation, hint * 10)
            }
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("finite-callable-effect-route.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "finite-callable-effect-route-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn finite_callable_targets_join_one_canonical_capture_abi() {
    let source = r#"
        enum Flag { First, Second }
        answer() -> i64 {
            let left = 40;
            let right = 40;
            let flag = Flag::First();
            let selected = if(flag is Flag::First) {
                (increment: i64) -> i64 { left + increment }
            } else {
                (increment: i64) -> i64 { right + increment }
            };
            selected(2)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("finite-callable-capture-abi.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "finite-callable-capture-abi-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn finite_callable_targets_infer_a_parameterized_sibling_from_the_canonical_shape() {
    let source = r#"
        enum Flag { First, Second }
        answer() -> i64 {
            let flag = Flag::First();
            let selected = if(flag is Flag::First) {
                { value => value }
            } else {
                (value: i64) -> i64 { value }
            };
            selected(42)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("finite-callable-inferred-sibling.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "finite-callable-inferred-sibling-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn finite_callable_targets_do_not_guess_two_unconstrained_parameter_types() {
    let source = r#"
        enum Flag { First, Second }
        bad(flag: Flag) -> i64 {
            let selected = if(flag is Flag::First) {
                { value => value }
            } else {
                { value => value }
            };
            selected(42)
        }
        main() -> { () }
    "#;
    assert_rejected(
        "finite-callable-unconstrained-inference.glorious",
        source,
        "explicit parameters",
    );
}

#[test]
fn nontransparent_generic_transport_retains_a_vm_sealed_producer_set() {
    let source = r#"
        enum Flag { First, Second }
        choose<T>(flag: Flag, left: T, right: T) -> T
            where T: Fn<(i64), Output=i64> {
            if(flag is Flag::First) { left } else { right }
        }
        answer() -> i64 {
            let selected = choose(
                Flag::First(),
                (value: i64) -> i64 { value + 1 },
                (value: i64) -> i64 { value + 2 }
            );
            selected(41)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("sealed-generic-callable-transport.glorious", source).1,
        Value::I64(42)
    );
    let recovery = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "sealed-generic-callable-transport-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );
}

#[test]
fn nontransparent_generic_transport_rejects_incompatible_sealed_producers() {
    let source = r#"
        enum Flag { First, Second }
        choose<T>(flag: Flag, left: T, right: T) -> T
            where T: Fn<(i64), Output=i64> {
            if(flag is Flag::First) { left } else { right }
        }
        bad() -> i64 {
            let captured = 40;
            let selected = choose(
                Flag::First(),
                (increment: i64) -> i64 {
                    captured = captured + increment;
                    captured
                },
                (increment: i64) -> i64 { captured + increment }
            );
            selected(2)
        }
        main() -> { () }
    "#;
    assert_rejected(
        "sealed-generic-callable-transport-incompatible.glorious",
        source,
        "incompatible producer",
    );
}

#[test]
fn finite_callable_target_sets_reject_incompatible_effect_reference_and_ownership_contracts() {
    let effect = r#"
        effect Ping { [1,1] ping() -> i64 }
        enum Flag { First, Second }
        bad(flag: Flag) -> i64 {
            let selected = if(flag is Flag::First) {
                (value: i64) -> i64 / {Ping} { perform Ping::ping() + value }
            } else {
                (value: i64) -> i64 / {Ping} { perform Ping::ping() + value }
            };
            selected(1)
        }
        main() -> { () }
    "#;
    let reference = r#"
        enum Flag { First, Second }
        bad<'a>(flag: Flag, left: &'a i64, right: &'a i64) -> &'a i64 {
            let selected = if(flag is Flag::First) {
                (first: &i64, second: &i64) -> &i64 { second; first }
            } else {
                (first: &i64, second: &i64) -> &i64 { first; second }
            };
            selected(left, right)
        }
        main() -> { () }
    "#;
    let ownership = r#"
        enum Flag { First, Second }
        bad(flag: Flag) -> i64 {
            let captured = 40;
            let selected = if(flag is Flag::First) {
                (increment: i64) -> i64 {
                    captured = captured + increment;
                    captured
                }
            } else {
                (increment: i64) -> i64 { captured + increment }
            };
            selected(1)
        }
        main() -> { () }
    "#;
    for (name, source, needle) in [
        (
            "finite-callable-effect-mismatch.glorious",
            effect,
            "outward effect",
        ),
        (
            "finite-callable-reference-mismatch.glorious",
            reference,
            "identical symbolic lifetime routes",
        ),
        (
            "finite-callable-ownership-mismatch.glorious",
            ownership,
            "finite callable producer set has incompatible",
        ),
    ] {
        assert_rejected(name, source, needle);
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
        compile_and_run("late-explicit-resumption.glorious", source).1,
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
        compile_and_run("late-reference-resumption-callable.glorious", source).1,
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
        compile_and_run("escaping-noncopy-callable.glorious", source).1,
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
        compile_and_run("aggregate-resumption-callable.glorious", source).1,
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
        compile_and_run("recursive-closure.glorious", source).1,
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
        compile_and_run("recursive-captured-closure.glorious", source).1,
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
    let (artifact, value) = compile_and_run("receiver-mode-matrix.glorious", source);
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
    let (artifact, value) = compile_and_run("owned-receiver-mode.glorious", source);
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
    let (artifact, value) = compile_and_run("mutating-receiver-mode.glorious", source);
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
        compile_and_run("generic-resumption-callable.glorious", source).1,
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
        compile_and_run("contextual-reference-environment.glorious", source).1,
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
        compile_and_run("lifetime-bounded-reference-environment.glorious", source).1,
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
        compile_and_run("inline-generic-callable-formation.glorious", source).1,
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
        compile_and_run("qualified-associated-callable-value.glorious", source).1,
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
        compile_and_run("qualified-effectful-callable-value.glorious", source).1,
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
        compile_and_run("generic-associated-function-item.glorious", source).1,
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
        compile_and_run("deferred-generic-function-item.glorious", source).1,
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
        compile_and_run(
            "deferred-effectful-constrained-function-item.glorious",
            source
        )
        .1,
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
        compile_and_run("consistent-deferred-function-item.glorious", source).1,
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
        "conflicting-deferred-function-item.glorious",
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
        "unresolved-deferred-function-item-escape.glorious",
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
        "unresolved-deferred-function-item-storage.glorious",
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
    assert_rejected(
        "outlived-reference-environment.glorious",
        source,
        "cannot escape",
    );
}

#[test]
fn unique_reference_environment_escapes_with_sealed_owned_capture_evidence() {
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
    assert_eq!(
        compile_and_run("unique-reference-environment.glorious", source).1,
        Value::I64(42)
    );
}

#[test]
fn unique_reference_environment_supports_repeated_then_owned_mutating_calls() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let value = 40;
            let borrowed = &mut value;
            let add = (delta: i64) -> i64 {
                *borrowed = *borrowed + delta;
                *borrowed
            };
            let escaped = retain(move add);
            escaped(1);
            move escaped(1)
        }
        main() -> { () }
    "#;
    assert_eq!(
        compile_and_run("unique-mutating-reference-environment.glorious", source).1,
        Value::I64(42)
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
        "reference-environment-alias-conflict.glorious",
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
    assert_rejected("moved-capture-reuse.glorious", source, "was already moved");
}
