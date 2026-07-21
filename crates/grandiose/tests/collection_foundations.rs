use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Type, Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const STACK_SURFACE: &str = r#"
    effect I64OptionCase { inspect(value: Result<i64, ()>) -> !; }
    effect BoolCase { inspect(value: Result<(), ()>) -> !; }

    option_or_zero(value: Option<i64>) -> i64 {
        handle perform I64OptionCase::inspect(move value) {
            I64OptionCase::inspect(Result::Ok(item)) => move item,
            I64OptionCase::inspect(Result::Err(_)) => 0
        }
    }

    bool_score(value: Bool) -> usize {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }

    borrow_top<'a>(value: &'a Stack<i64>) -> Option<&'a i64> {
        Stack::top(value)
    }

    borrow_stack_mut<'a>(value: &'a mut Stack<i64>) -> &'a mut Stack<i64> {
        value
    }

    preserve_stack_tuple(
        value: (Stack<i64>, i64)
    ) -> (Stack<i64>, i64) {
        value
    }

    empty_i64_stack() -> Stack<i64> { Stack::new() }
    i64_stack_with_capacity(capacity: usize) -> Stack<i64> {
        Stack::with_capacity(move capacity)
    }

    stack_roundtrip() -> i64 {
        let stack = i64_stack_with_capacity(4);
        Stack::push(&mut stack, 10);
        Stack::push(&mut stack, 20);
        let popped = option_or_zero(Stack::pop(&mut stack));
        let remaining = option_or_zero(Stack::pop(&mut stack));
        let empty_pop = option_or_zero(Stack::pop(&mut stack));
        popped + remaining + empty_pop
    }

    stack_metadata() -> usize {
        let stack = i64_stack_with_capacity(4);
        let initially_empty = bool_score(Stack::is_empty(&stack));
        Stack::reserve(&mut stack, 2);
        Stack::push(&mut stack, 10);
        let nonempty = bool_score(Stack::is_empty(&stack));
        let length = Stack::len(&stack);
        let capacity = Stack::capacity(&stack);
        option_or_zero(Stack::pop(&mut stack));
        let finally_empty = bool_score(Stack::is_empty(&stack));
        initially_empty + nonempty + length + capacity + finally_empty
    }

    stack_metadata_nested() -> usize {
        let stack = i64_stack_with_capacity(4);
        Stack::len(&stack) + Stack::capacity(&stack)
    }

    consume_vec(values: Vec<i64>) -> i64 {
        let first = Vec::index(&values, 0);
        let first = *first;
        let second = Vec::index(&values, 1);
        move first * 10 + *second
    }

    stack_is_vec_alias() -> i64 {
        let stack = empty_i64_stack();
        Stack::push(&mut stack, 7);
        Stack::push(&mut stack, 11);
        consume_vec(move stack)
    }

    main() -> () { () }
"#;

#[test]
fn stack_wrapper_executes_at_every_optimization_level() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "stack-foundation.glorious",
            STACK_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        let vm = Vm::new(artifact);

        assert_eq!(
            vm.run(function_id(&phases.artifact, "stack_roundtrip"), vec![])
                .unwrap(),
            Value::I64(30),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(function_id(&phases.artifact, "stack_is_vec_alias"), vec![])
                .unwrap(),
            Value::I64(81),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(function_id(&phases.artifact, "stack_metadata"), vec![])
                .unwrap(),
            Value::U64(7),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(
                function_id(&phases.artifact, "stack_metadata_nested"),
                vec![]
            )
            .unwrap(),
            Value::U64(4),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn stack_alias_adds_no_nominal_or_vm_type() {
    let phases = compile_source_to_phases_with_options(
        "stack-is-source-alias.glorious",
        "empty() -> Stack<i64> { Stack::new() } main() -> () { () }",
        CompileOptions {
            optimization_level: OptimizationLevel::O0,
        },
    )
    .unwrap();
    assert!(
        phases.artifact.types.iter().all(|ty| !matches!(
            ty.representation(),
            Type::Struct { name, .. } | Type::Enum { name, .. } if name == "Stack"
        )),
        "Stack must remain a source alias over Vec"
    );
}
