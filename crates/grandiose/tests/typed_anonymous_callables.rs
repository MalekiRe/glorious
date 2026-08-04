//! Explicit typed anonymous callables `(x: T) -> R / {Row} { body }`:
//! signature resolution, capture discovery and enforcement, receiver modes,
//! direct/contextual invocation, recovery/compiled parity, and O1-O3 parity.

use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
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
            "typed-callable test performed a host effect",
            span,
        ))
    }
}

fn compiled(source_name: &str, source: &str, function_name: &str) -> Value {
    let artifact = compile_source_to_bytecode(source_name, source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == function_name)
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

fn has_message(source_name: &str, source: &str, needles: &[&str]) {
    let diagnostics = match compile_source_to_bytecode(source_name, source) {
        Ok(_) => panic!("{source_name}: expected compilation failure"),
        Err(diagnostics) => diagnostics,
    };
    assert!(
        diagnostics.iter().any(|diagnostic| {
            needles
                .iter()
                .all(|needle| diagnostic.message.contains(needle))
        }),
        "expected one diagnostic containing {needles:?}, got {diagnostics:#?}"
    );
    assert!(
        diagnostics
            .iter()
            .all(|diagnostic| diagnostic.span.is_some() || diagnostic.code.is_some()),
        "diagnostics must stay deterministic and structured: {diagnostics:#?}"
    );
}

#[test]
fn explicit_parameter_and_result_types_compile_and_run() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64, y: i64) -> i64 { x * y + 2 };
            f(5, 8)
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-basic.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn omitted_result_type_means_unit() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64) -> { () };
            f(1);
            42
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-unit.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn never_result_with_declared_effect_row_diverges_into_a_handler() {
    let source = r#"
        effect Stop { stop(code: i64) -> ! }
        selected() -> i64 {
            let f = (x: i64) -> ! / {Stop} { perform Stop::stop(x + 2) };
            handle f(40) {
                Stop::stop(code) => code
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-never.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn declared_effect_rows_admit_resumptive_operations() {
    let source = r#"
        effect Ask { [1,1] ask(hint: i64) -> i64 }
        selected() -> i64 {
            let f = (x: i64) -> i64 / {Ask} { perform Ask::ask(x) + 2 };
            handle f(4) {
                Ask::ask(hint) with k => resume(k, hint * 10)
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-resumptive.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn indirect_effectful_calls_preserve_partial_residual_frames_at_all_levels() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { resource: Resource, remaining: Resource }

        selected() -> i64 {
            let parcel = Parcel {
                resource: Resource { marker: 0 },
                remaining: Resource { marker: 2 }
            };
            let resource = parcel.resource;
            resource;
            let f = () -> i64 / {Ask} { perform Ask::ask() };
            let answer = handle f() {
                Ask::ask() with k => resume(k, 40)
            };
            let remaining = parcel.remaining;
            let Resource { marker } = move remaining;
            answer + marker
        }
        main() -> { selected(); () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "typed-indirect-partial-residual.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn nested_indirect_residuals_support_optional_cancellation_and_unknown_multiplicity() {
    let optional = r#"
        effect Maybe { [0,1] ask() -> i64 }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        consume(value: Resource) -> { () }
        selected() -> i64 {
            handle {
                let outer = ((Resource { marker: 1 }, Resource { marker: 2 }), Resource { marker: 3 });
                let inner = outer.0;
                let removed = inner.0;
                consume(removed);
                let f = () -> i64 / {Maybe} { perform Maybe::ask() };
                f()
            } {
                Maybe::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { selected(); () }
    "#;
    let multishot = r#"
        effect Choose { [2,2] choose() -> i64 }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        consume(value: Resource) -> { () }
        selected() -> i64 {
            handle {
                let outer = ((Resource { marker: 1 }, 20), 20);
                let inner = outer.0;
                let removed = inner.0;
                consume(removed);
                let f = () -> i64 / {Choose} { perform Choose::choose() };
                f() + inner.1 + outer.1
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 1);
                    let second = resume(move continuation, 2);
                    first + second
                }
            }
        }
        main() -> { selected(); () }
    "#;
    for (name, source, expected) in [
        (
            "typed-indirect-nested-optional.glorious",
            optional,
            Value::I64(42),
        ),
        (
            "typed-indirect-nested-multishot.glorious",
            multishot,
            Value::I64(83),
        ),
    ] {
        for optimization_level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let artifact = compile_source_to_bytecode_with_options(
                name,
                source,
                CompileOptions { optimization_level },
            )
            .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
            let selected = artifact
                .functions
                .iter()
                .position(|function| function.name == "selected")
                .unwrap() as u32;
            assert_eq!(
                Vm::new(verify(artifact).unwrap())
                    .run(selected, vec![])
                    .unwrap(),
                expected,
                "{optimization_level:?}"
            );
        }
    }
}

#[test]
fn nested_indirect_optional_capture_rejects_a_remaining_ticket() {
    let source = r#"
        effect Maybe { [0,1] ask() -> i64 }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        consume(value: Resource) -> { () }
        bad(outer: ((Resource, Ticket), Resource)) -> i64 / {Maybe} {
            let inner = outer.0;
            let removed = inner.0;
            consume(removed);
            let f = () -> i64 / {Maybe} { perform Maybe::ask() };
            f()
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_bytecode_with_options(
            "typed-indirect-nested-hostile.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error
                    .message
                    .contains("restricted-use value at an indirect effectful call")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}

#[test]
fn indirect_optional_effect_rejects_a_positive_residual_on_every_level() {
    let source = r#"
        effect Maybe { [0,1] ask() -> i64 }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Parcel { resource: Resource, ticket: Ticket }
        impl Use<[1,1]> for Parcel {}

        bad(parcel: Parcel) -> i64 / {Maybe} {
            let resource = parcel.resource;
            resource;
            let f = () -> i64 / {Maybe} { perform Maybe::ask() };
            f()
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_bytecode_with_options(
            "typed-indirect-hostile-residual.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error
                    .message
                    .contains("restricted-use value at an indirect effectful call")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }

    let restricted_result = r#"
        effect Twice { [2,2] ask() -> i64 }
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        bad() -> Ticket / {Twice} {
            let f = () -> Ticket / {Twice} {
                perform Twice::ask();
                Ticket { marker: 1 }
            };
            f()
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_bytecode_with_options(
            "typed-indirect-hostile-result.glorious",
            restricted_result,
            CompileOptions { optimization_level },
        )
        .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error
                    .message
                    .contains("restricted-use value at an indirect effectful call")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}

#[test]
fn captures_are_discovered_and_shared_receiver_allows_repeat_calls() {
    let source = r#"
        selected() -> i64 {
            let base = 20;
            let f = (x: i64) -> i64 { x + base };
            f(0) + f(2)
        }
        main() -> { selected(); () }
    "#;
    let artifact = compile_source_to_bytecode("typed-captures.glorious", source).unwrap();
    // An observe-only capture keeps the least-consuming shared receiver.
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 0,
            ..
        }
    )));
    let id = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(id, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn typed_closures_satisfy_fn_constraints_contextually() {
    let source = r#"
        apply<F>(body: F) -> i64 where F: Fn<(i64,), Output=i64> { body(40) }
        selected() -> i64 { apply((x: i64) -> i64 { x + 2 }) }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-contextual.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn typed_closures_chain_through_indirect_callable_values() {
    let source = r#"
        selected() -> i64 {
            let double = (x: i64) -> i64 { x * 2 };
            let add = (x: i64, y: i64) -> i64 { x + y };
            add(double(20), 2)
        }
        main() -> { selected(); () }
    "#;
    let artifact = compile_source_to_bytecode("typed-chain.glorious", source).unwrap();
    assert!(
        artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::CallIndirect { .. })),
        "typed callables invoke through indirect calls on their runtime values"
    );
    let id = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(id, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn monomorphic_typed_callable_forms_are_planned_at_a_generic_wrapper_site() {
    let source = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        answer() -> i64 {
            apply(42, (value: i64) -> i64 {
                if(true) { value } else { value }
            })
        }

        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "typed-runtime-fallback.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            artifact
                .functions
                .iter()
                .any(|function| function.name.starts_with("$closure$")),
            "{optimization_level:?}: expected a planned closure synthetic"
        );
        assert!(
            artifact
                .functions
                .iter()
                .all(|function| !function.name.starts_with("$runtime$closure$")),
            "{optimization_level:?}: discovery should not require the runtime fallback"
        );
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(function, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn planned_callable_wrappers_enforce_region_and_effect_contracts() {
    let exact_reference = r#"
            struct Receiver { selected: &i64 }
            apply<F, T, R>(value: T, body: F) -> R
                where F: Fn<(T), Output=R> { body(value) }
            answer() -> i64 {
                let value = 42;
                *apply(Receiver { selected: &value }, (input: Receiver) -> &i64 {
                    if(true) { input.selected } else { input.selected }
                })
            }
            main() -> { () }
        "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "typed-runtime-reference-exact.glorious",
            exact_reference,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            artifact
                .functions
                .iter()
                .any(|function| function.name.starts_with("$closure$"))
        );
        assert!(
            artifact
                .functions
                .iter()
                .all(|function| !function.name.starts_with("$runtime$closure$"))
        );
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
    let recovery = exact_reference.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        run_source(
            "typed-runtime-reference-recovery.glorious",
            &recovery,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(42)
    );

    has_message(
        "typed-runtime-reference-opaque.glorious",
        r#"
            apply<F, T, R>(value: T, body: F) -> R
                where F: Fn<(T), Output=R> { body(value) }
            bad<'a>(value: &'a i64, other: &'a i64) -> &'a i64 {
                apply(value, (input: &i64) -> &i64 {
                    if(true) { input } else { other }
                })
            }
            main() -> { () }
        "#,
        &["exact symbolic reference route"],
    );
    for (name, source, needle) in [
        (
            "typed-runtime-reference-escape.glorious",
            r#"
                apply<F, T, R>(value: T, body: F) -> R
                    where F: Fn<(T), Output=R> { body(value) }
                escape<'a>(other: &'a i64) -> &'a i64 {
                    let local = 42;
                    other;
                    apply(&local, (input: &i64) -> &i64 {
                        if(true) { input } else { input }
                    })
                }
                main() -> { () }
            "#,
            "escape",
        ),
        (
            "typed-runtime-reference-alias.glorious",
            r#"
                apply<F, T, R>(value: T, body: F) -> R
                    where F: Fn<(T), Output=R> { body(value) }
                bad() -> {
                    let value = 42;
                    let selected = apply(&mut value, (input: &mut i64) -> &mut i64 {
                        if(true) { input } else { input }
                    });
                    let conflicting = &mut value;
                    selected;
                    conflicting;
                    ()
                }
                main() -> { () }
            "#,
            "incompatible live loan",
        ),
    ] {
        for optimization_level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let errors = compile_source_to_bytecode_with_options(
                name,
                source,
                CompileOptions { optimization_level },
            )
            .expect_err("unsafe sealed runtime reference route compiled");
            assert!(
                errors.iter().any(|error| error.message.contains(needle)),
                "{optimization_level:?}: {errors:#?}"
            );
        }
    }
    let effectful = r#"
            effect Escape { escape(value: i64) -> ! }
            apply<F, T, R>(value: T, body: F) -> R
                where F: Fn<(T), Output=R> { body(value) }
            bad(value: i64) -> i64 / {Escape} {
                apply(value, (input: i64) -> i64 / {Escape} {
                    if(true) { input } else { input }
                })
            }
            main() -> { () }
        "#;
    let artifact = compile_source_to_bytecode("typed-planned-effect.glorious", effectful).unwrap();
    assert!(
        artifact
            .functions
            .iter()
            .any(|function| function.name.starts_with("$closure$"))
    );
    assert!(
        artifact
            .functions
            .iter()
            .all(|function| !function.name.starts_with("$runtime$closure$"))
    );
    let bad = artifact
        .functions
        .iter()
        .position(|function| function.name == "bad")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(bad, vec![Value::I64(42)])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn contextual_typed_closures_may_borrow_captures_within_the_call() {
    let source = r#"
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        selected() -> i64 {
            let value = 40;
            let borrowed = &value;
            invoke(() -> i64 { *borrowed + 2 })
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-ctx-borrow.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn effectful_typed_closures_keep_their_row_through_fn_constraints() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        invoke<F>(body: F) -> i64 where F: Fn<(), Output=i64> { body() }
        selected() -> i64 {
            handle invoke(() -> i64 / {Ask} { perform Ask::ask() + 2 }) {
                Ask::ask() with k => resume(k, 40)
            }
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-fn-effects.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn move_captures_transfer_exact_linear_obligations_into_one_call() {
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        selected() -> i64 {
            let ticket = Ticket { marker: 42 };
            let f = () -> i64 { let Ticket { marker } = move ticket; marker };
            f()
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-linear-capture.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn recovery_and_compiled_paths_agree() {
    let surface = r#"
        effect Ask { [1,1] ask(hint: i64) -> i64 }
        selected() -> i64 {
            let base = 30;
            let pure = (x: i64, y: i64) -> i64 { x * y + base };
            let ask = (x: i64) -> i64 / {Ask} { perform Ask::ask(x) };
            pure(2, 5) + handle ask(4) {
                Ask::ask(hint) with k => resume(k, hint - 2)
            }
        }
    "#;
    let recovery = format!("{surface}\n        main() -> i64 {{ selected() }}");
    let result = run_source("typed-recovery.glorious", &recovery, vec![], &mut NoHost).unwrap();
    assert_eq!(result, RecoveryValue::Int(42));

    let bytecode = format!("{surface}\n        main() -> {{ selected(); () }}");
    assert_eq!(
        compiled("typed-compiled.glorious", &bytecode, "selected"),
        Value::I64(42)
    );
}

#[test]
fn behavior_is_identical_across_optimization_levels() {
    let source = r#"
        effect Stop { stop(code: i64) -> ! }
        apply<F>(body: F) -> i64 where F: Fn<(i64,), Output=i64> { body(11) }
        selected() -> i64 {
            let base = 8;
            let abort = (x: i64) -> ! / {Stop} { perform Stop::stop(x + 12) };
            handle abort(apply((x: i64) -> i64 { x * 2 + base })) {
                Stop::stop(code) => code
            }
        }
        main() -> { selected(); () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "typed-levels.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let id = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap()).run(id, vec![]).unwrap(),
            Value::I64(42),
            "typed callables changed behavior at {optimization_level:?}"
        );
    }
}

#[test]
fn call_site_arity_mismatches_are_rejected() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64) -> i64 { x + 2 };
            f(1, 2)
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-bad-arity.glorious",
        source,
        &["closure expects 1 arguments, got 2"],
    );
}

#[test]
fn call_site_argument_type_mismatches_are_rejected() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64) -> i64 { x + 2 };
            f("nope")
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-bad-argument.glorious",
        source,
        &["expected i64, found Text"],
    );
}

#[test]
fn body_result_mismatches_are_rejected() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64) -> i64 { "nope" };
            f(1)
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-bad-result.glorious",
        source,
        &["typed closure body result does not unify"],
    );
}

#[test]
fn contextual_shape_mismatches_are_rejected() {
    let source = r#"
        apply<F>(body: F) -> i64 where F: Fn<(i64,), Output=i64> { body(40) }
        selected() -> i64 { apply((x: Text) -> i64 { 2 }) }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-bad-context.glorious",
        source,
        &["typed closure parameter 0 does not match its contextual callable shape"],
    );
}

#[test]
fn undeclared_outward_effects_are_rejected() {
    let source = r#"
        effect Stop { stop(code: i64) -> ! }
        selected() -> i64 {
            let f = (x: i64) -> i64 { perform Stop::stop(x); 0 };
            f(1)
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-undeclared-effect.glorious",
        source,
        &[
            "typed closure body performs effect(s) absent from its declared effect row",
            "Stop",
        ],
    );
}

#[test]
fn unknown_effects_in_a_declared_row_are_rejected() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64) -> i64 / {Ghost} { x };
            f(1)
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-unknown-effect.glorious",
        source,
        &["`Ghost` is not a declared effect or effect-row alias"],
    );
}

#[test]
fn open_effect_row_tails_are_rejected() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            let f = (x: i64) -> i64 / {Ask | e} { x };
            f(1)
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-open-row.glorious",
        source,
        &["a typed anonymous callable must declare a closed effect row"],
    );
}

#[test]
fn duplicate_parameters_are_rejected_with_spans() {
    let source = r#"
        selected() -> i64 {
            let f = (x: i64, x: i64) -> i64 { x };
            f(1, 2)
        }
        main() -> { selected(); () }
    "#;
    let diagnostics = compile_source_to_bytecode("typed-dup-param.glorious", source).unwrap_err();
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| {
            diagnostic
                .message
                .contains("parameter `x` appears more than once")
        })
        .unwrap_or_else(|| panic!("missing duplicate-parameter diagnostic: {diagnostics:#?}"));
    assert_eq!(diagnostic.code.as_deref(), Some("G0130"));
    assert!(diagnostic.span.is_some(), "diagnostic must carry a span");
    assert!(!diagnostic.related.is_empty(), "must point at the original");
}

#[test]
fn borrowed_reference_capture_may_live_in_a_single_shot_environment_within_its_lifetime() {
    let source = r#"
        selected() -> i64 {
            let value = 40;
            let borrowed = &value;
            let f = () -> i64 { *borrowed + 2 };
            f()
        }
        main() -> { selected(); () }
    "#;
    assert_eq!(
        compiled("typed-lifetime-bounded-borrow.glorious", source, "selected"),
        Value::I64(42)
    );
}

#[test]
fn move_captures_conflict_with_live_loans() {
    let source = r#"
        struct Box { value: i64 }
        selected() -> i64 {
            let container = Box { value: 40 };
            let loan = &container;
            let f = () -> i64 { let Box { value } = move container; value + 2 };
            let result = f();
            let observed = loan.value;
            result + observed
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-loan-conflict.glorious",
        source,
        &["container", "borrow"],
    );
}

#[test]
fn exact_linear_captures_cannot_be_called_twice() {
    // A move-captured [1,1] value forces the owned receiver mode, so the
    // callable itself is single-shot: the second call re-moves `f`.
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        selected() -> i64 {
            let ticket = Ticket { marker: 21 };
            let f = () -> i64 { let Ticket { marker } = move ticket; marker };
            f() + f()
        }
        main() -> { selected(); () }
    "#;
    has_message(
        "typed-linear-twice.glorious",
        source,
        &["`f` was already moved"],
    );
}

#[test]
fn exact_linear_captures_cannot_be_abandoned_unused() {
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        selected() -> i64 {
            let ticket = Ticket { marker: 21 };
            let f = () -> i64 { let Ticket { marker } = move ticket; marker };
            42
        }
        main() -> { selected(); () }
    "#;
    has_message("typed-linear-unused.glorious", source, &["[1,1]"]);
}

#[test]
fn recovery_evaluator_runs_typed_closures_with_captures() {
    let source = r#"
        selected() -> i64 {
            let base = 2;
            let f = (x: i64, y: i64) -> i64 { x * y + base };
            f(5, 8)
        }
        main() -> i64 { selected() }
    "#;
    let result = run_source("typed-recovery-only.glorious", source, vec![], &mut NoHost).unwrap();
    assert_eq!(result, RecoveryValue::Int(42));
}
