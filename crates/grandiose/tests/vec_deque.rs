use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Type, Value, Vm, verify};

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
            "VecDeque recovery test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const SURFACE: &str = r#"
    struct Ticket { serial: i64 }
    struct Scrap { serial: i64 }
    struct LinearDequeResult { score: i64, remainder: VecDeque<Ticket> }
    impl Use<[1,1]> for Ticket {}
    impl Use<[0,1]> for Scrap {}

    effect I64OptionCase { inspect(value: Result<i64, ()>) -> !; }
    effect TicketOptionCase { inspect(value: Result<Ticket, ()>) -> !; }
    effect BoolCase { inspect(value: Result<(), ()>) -> !; }

    bool_score(value: Bool) -> usize {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }

    i64_or_zero(value: Option<i64>) -> i64 {
        handle perform I64OptionCase::inspect(move value) {
            I64OptionCase::inspect(Result::Ok(item)) => move item,
            I64OptionCase::inspect(Result::Err(_)) => 0
        }
    }

    ticket_serial(value: Option<Ticket>) -> i64 {
        handle perform TicketOptionCase::inspect(move value) {
            TicketOptionCase::inspect(Result::Ok(item)) => {
                let Ticket { serial } = move item;
                move serial
            },
            TicketOptionCase::inspect(Result::Err(_)) => 0
        }
    }

    empty_i64() -> VecDeque<i64> { VecDeque::new() }
    empty_tickets() -> VecDeque<Ticket> { VecDeque::new() }
    empty_scraps() -> VecDeque<Scrap> { VecDeque::new() }
    empty_work() -> WorkList<i64> { WorkList::new() }

    wrap_order() -> i64 {
        let values = empty_i64();
        VecDeque::push_back(&mut values, 1);
        VecDeque::push_back(&mut values, 2);
        VecDeque::push_back(&mut values, 3);
        i64_or_zero(VecDeque::pop_front(&mut values));
        i64_or_zero(VecDeque::pop_front(&mut values));
        VecDeque::push_back(&mut values, 4);
        VecDeque::push_back(&mut values, 5);
        VecDeque::push_front(&mut values, 9);
        let a = i64_or_zero(VecDeque::pop_front(&mut values));
        let b = i64_or_zero(VecDeque::pop_front(&mut values));
        let c = i64_or_zero(VecDeque::pop_front(&mut values));
        let d = i64_or_zero(VecDeque::pop_front(&mut values));
        a * 1000 + b * 100 + c * 10 + d
    }

    growth_and_metadata() -> usize {
        let values = empty_i64();
        VecDeque::reserve(&mut values, 10);
        let capacity = VecDeque::capacity(&values);
        VecDeque::push_front(&mut values, 2);
        VecDeque::push_back(&mut values, 3);
        let length = VecDeque::len(&values);
        i64_or_zero(VecDeque::pop_back(&mut values));
        i64_or_zero(VecDeque::pop_front(&mut values));
        let empty_length = VecDeque::len(&values);
        capacity + length + empty_length
    }

    empty_transitions() -> usize {
        let values = empty_i64();
        let initially = bool_score(VecDeque::is_empty(&values));
        VecDeque::push_back(&mut values, 1);
        let occupied = bool_score(VecDeque::is_empty(&values));
        i64_or_zero(VecDeque::pop_back(&mut values));
        initially + occupied + bool_score(VecDeque::is_empty(&values))
    }

    transfer_linear() -> LinearDequeResult {
        let values = empty_tickets();
        VecDeque::push_front(&mut values, Ticket { serial: 1 });
        VecDeque::push_back(&mut values, Ticket { serial: 2 });
        let first = ticket_serial(VecDeque::pop_front(&mut values));
        let second = ticket_serial(VecDeque::pop_back(&mut values));
        LinearDequeResult {
            score: first * 10 + second,
            remainder: move values
        }
    }

    affine_cleanup_and_clear() -> usize {
        let abandoned = empty_scraps();
        VecDeque::push_back(&mut abandoned, Scrap { serial: 7 });
        VecDeque::push_front(&mut abandoned, Scrap { serial: 8 });
        abandoned;

        let cleared = empty_scraps();
        VecDeque::push_back(&mut cleared, Scrap { serial: 9 });
        VecDeque::clear(&mut cleared);
        VecDeque::len(&cleared)
    }

    work_list_order() -> i64 {
        let work = empty_work();
        WorkList::push(&mut work, 4);
        WorkList::push(&mut work, 5);
        i64_or_zero(WorkList::pop(&mut work)) * 10
            + i64_or_zero(WorkList::pop(&mut work))
    }

    main() -> () { () }
"#;

#[test]
fn vec_deque_wraps_grows_and_transfers_at_optimized_levels() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "vec-deque.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        for (name, expected) in [
            ("wrap_order", Value::I64(9345)),
            ("growth_and_metadata", Value::U64(18)),
            ("empty_transitions", Value::U64(2)),
            ("affine_cleanup_and_clear", Value::U64(0)),
            ("work_list_order", Value::I64(45)),
        ] {
            assert_eq!(
                vm.run(function_id(&phases.artifact, name), vec![]).unwrap(),
                expected,
                "{optimization_level:?} {name}"
            );
        }
        let Value::Aggregate(linear) = vm
            .run(function_id(&phases.artifact, "transfer_linear"), vec![])
            .unwrap()
        else {
            panic!("{optimization_level:?}: linear transfer did not return its owner")
        };
        assert_eq!(
            linear.borrow().fields[0],
            Some(Value::I64(12)),
            "{optimization_level:?}"
        );
        assert!(
            phases.artifact.types.iter().all(|ty| !matches!(
                ty.representation(),
                Type::Struct { name, .. } | Type::Enum { name, .. }
                    if name == "WorkList"
            )),
            "WorkList must remain a source alias at {optimization_level:?}"
        );
    }
}

#[test]
fn vec_deque_clear_and_abandonment_reject_exact_linear_elements() {
    for (operation, body) in [
        ("clear", "VecDeque::clear(&mut values); values"),
        ("abandon", "values; ()"),
    ] {
        let result = if operation == "clear" {
            "VecDeque<Ticket>"
        } else {
            "()"
        };
        let source = format!(
            r#"
                struct Ticket {{ serial: i64 }}
                impl Use<[1,1]> for Ticket {{}}
                empty() -> VecDeque<Ticket> {{ VecDeque::new() }}
                bad() -> {result} {{
                    let values = empty();
                    VecDeque::push_back(&mut values, Ticket {{ serial: 1 }});
                    {body}
                }}
                main() -> () {{ () }}
            "#
        );
        let errors =
            compile_source_to_bytecode(&format!("linear-vec-deque-{operation}.glorious"), &source)
                .expect_err("exact-linear VecDeque elements must not be discarded");
        assert!(
            errors.iter().any(|error| {
                let message = error.message.to_ascii_lowercase();
                message.contains("use")
                    || message.contains("must-move")
                    || message.contains("not a callable")
            }),
            "{operation}: {errors:#?}"
        );
    }
}

#[test]
fn vec_deque_representation_is_private() {
    for (name, source, expected) in [
        (
            "vec-deque-forge.glorious",
            "bad()->VecDeque<i64>{VecDeque{slots:Vec::new(),head:0,length:0}} main()->(){()}",
            "private field",
        ),
        (
            "vec-deque-project.glorious",
            "bad(value:VecDeque<i64>)->usize{value.head} main()->(){()}",
            "private field `head`",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed VecDeque's private ring state");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn vec_deque_has_recovery_parity() {
    let result = run_source(
        "vec-deque-recovery.glorious",
        &SURFACE.replace("main() -> () { () }", "main() -> i64 { wrap_order() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(9345));
}
