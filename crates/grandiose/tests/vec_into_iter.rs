use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

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
            "VecIntoIter recovery test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| {
            function.name == name
                || function
                    .name
                    .strip_prefix("$specialization$")
                    .and_then(|wire| wire.split_once('#'))
                    .is_some_and(|(template, _)| template == name)
        })
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const SURFACE: &str = r#"
    struct Ticket { serial: i64 }
    struct Scrap { serial: i64 }
    impl Use<[1,1]> for Ticket {}
    impl Use<[0,1]> for Scrap {}

    empty_i64() -> Vec<i64> { Vec::new() }
    empty_tickets() -> Vec<Ticket> { Vec::new() }
    empty_scraps() -> Vec<Scrap> { Vec::new() }

    next_i64(
        value: VecIntoIter<i64>
    ) -> Option<(i64, VecIntoIter<i64>)> {
        VecIntoIter::next(move value)
    }

    next_ticket(
        value: VecIntoIter<Ticket>
    ) -> Option<(Ticket, VecIntoIter<Ticket>)> {
        VecIntoIter::next(move value)
    }

    ordered_i64() -> VecIntoIter<i64> {
        let values = empty_i64();
        Vec::push(&mut values, 1);
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 3);
        Vec::into_iter(move values)
    }

    ordered_linear() -> VecIntoIter<Ticket> {
        let values = empty_tickets();
        Vec::push(&mut values, Ticket { serial: 4 });
        Vec::push(&mut values, Ticket { serial: 5 });
        Vec::push(&mut values, Ticket { serial: 6 });
        Vec::into_iter(move values)
    }

    empty_iterator() -> VecIntoIter<i64> {
        Vec::into_iter(empty_i64())
    }

    abandon_affine() -> () {
        let values = empty_scraps();
        Vec::push(&mut values, Scrap { serial: 7 });
        Vec::push(&mut values, Scrap { serial: 8 });
        let iterator = Vec::into_iter(move values);
        iterator;
        ()
    }

    main() -> () { () }
"#;

#[test]
fn vec_into_iter_orders_exhausts_and_handles_linearity_at_optimized_levels() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "vec-into-iter.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(phases.artifact.clone()).unwrap());
        let next_i64 = function_id(&phases.artifact, "next_i64");
        let next_ticket = function_id(&phases.artifact, "next_ticket");

        let mut state = vm
            .run(function_id(&phases.artifact, "ordered_i64"), vec![])
            .unwrap();
        let mut integers = Vec::new();
        loop {
            let Value::Aggregate(step) = vm.run(next_i64, vec![state]).unwrap() else {
                panic!("{optimization_level:?}: i64 next did not return Option")
            };
            if step.borrow().variant == Some(1) {
                break;
            }
            let pair = step.borrow_mut().fields[0].take().unwrap();
            let Value::Aggregate(pair) = pair else {
                panic!("{optimization_level:?}: Some payload was not a tuple")
            };
            let Value::I64(item) = pair.borrow_mut().fields[0].take().unwrap() else {
                panic!("{optimization_level:?}: i64 iterator yielded a non-i64")
            };
            state = pair.borrow_mut().fields[1].take().unwrap();
            integers.push(item);
        }
        assert_eq!(integers, [1, 2, 3], "{optimization_level:?}");

        let mut state = vm
            .run(function_id(&phases.artifact, "ordered_linear"), vec![])
            .unwrap();
        let mut tickets = Vec::new();
        loop {
            let Value::Aggregate(step) = vm.run(next_ticket, vec![state]).unwrap() else {
                panic!("{optimization_level:?}: Ticket next did not return Option")
            };
            if step.borrow().variant == Some(1) {
                break;
            }
            let pair = step.borrow_mut().fields[0].take().unwrap();
            let Value::Aggregate(pair) = pair else {
                panic!("{optimization_level:?}: Ticket Some payload was not a tuple")
            };
            let ticket = pair.borrow_mut().fields[0].take().unwrap();
            let Value::Aggregate(ticket) = ticket else {
                panic!("{optimization_level:?}: iterator yielded a non-Ticket")
            };
            let Value::I64(serial) = ticket.borrow_mut().fields[0].take().unwrap() else {
                panic!("{optimization_level:?}: Ticket serial was not i64")
            };
            state = pair.borrow_mut().fields[1].take().unwrap();
            tickets.push(serial);
        }
        assert_eq!(tickets, [4, 5, 6], "{optimization_level:?}");

        let empty = vm
            .run(function_id(&phases.artifact, "empty_iterator"), vec![])
            .unwrap();
        let Value::Aggregate(done) = vm.run(next_i64, vec![empty]).unwrap() else {
            panic!("{optimization_level:?}: empty next did not return Option")
        };
        assert_eq!(done.borrow().variant, Some(1), "{optimization_level:?}");

        assert_eq!(
            vm.run(function_id(&phases.artifact, "abandon_affine"), vec![])
                .unwrap(),
            Value::Unit,
            "{optimization_level:?}"
        );
    }
}

#[test]
fn exact_linear_vec_iterator_cannot_be_abandoned_early() {
    let errors = compile_source_to_bytecode(
        "linear-vec-into-iter-abandon.glorious",
        r#"
            struct Ticket { serial: i64 }
            impl Use<[1,1]> for Ticket {}
            empty() -> Vec<Ticket> { Vec::new() }
            bad() -> () {
                let values = empty();
                Vec::push(&mut values, Ticket { serial: 1 });
                let iterator = Vec::into_iter(move values);
                iterator;
                ()
            }
            main() -> () { () }
        "#,
    )
    .expect_err("an iterator retaining exact-linear elements must not be abandoned");
    assert!(
        errors.iter().any(|error| {
            let message = error.message.to_ascii_lowercase();
            message.contains("use") || message.contains("must-move")
        }),
        "{errors:#?}"
    );
}

#[test]
fn vec_into_iter_representation_is_private() {
    for (name, source, expected) in [
        (
            "vec-into-iter-forge.glorious",
            "bad(value:Vec<i64>)->VecIntoIter<i64>{VecIntoIter{remaining:move value}} main()->(){()}",
            "private field",
        ),
        (
            "vec-into-iter-project.glorious",
            "bad(value:VecIntoIter<i64>)->Vec<i64>{value.remaining} main()->(){()}",
            "private field `remaining`",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed VecIntoIter's private representation");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn vec_into_iter_has_recovery_parity() {
    let result = run_source(
        "vec-into-iter-recovery.glorious",
        &SURFACE.replace(
            "main() -> () { () }",
            "main() -> Option<(i64, VecIntoIter<i64>)> { next_i64(ordered_i64()) }",
        ),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    let RecoveryValue::Enum {
        name,
        variant,
        fields,
    } = result
    else {
        panic!("recovery next did not return Option")
    };
    assert_eq!(name.as_ref(), "Result");
    assert_eq!(variant.as_ref(), "Ok");
    assert_eq!(fields.len(), 1);
}
