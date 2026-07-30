use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Value, Vm, verify};

fn run(source_name: &str, source: &str, function_name: &str) -> Value {
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

fn assert_stable_quantity_error(source_name: &str, source: &str) {
    let errors = compile_source_to_bytecode(source_name, source).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| { error.code.as_deref() == Some("G1BC002") && error.span.is_some() }),
        "expected a source-anchored G1BC002 quantity error: {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G1BC999")),
        "internal compiler diagnostic escaped: {errors:#?}"
    );
}

#[test]
fn late_generic_inline_evaluates_each_argument_once() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        forward<T>(value: T, marker: i64) -> T { marker; value }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let restored = forward(move k, 7);
                    resume(move restored, 42)
                }
            }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-once.glorious", source, "answer"),
        Value::I64(42)
    );
}

#[test]
fn late_generic_inline_preserves_control_expression_order() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        finish<T>(continuation: T, before: i64, resumed: i64) -> i64 {
            before + resume(move continuation, resumed)
        }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => finish(move k, 1, 41)
            }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-control-order.glorious", source, "answer"),
        Value::I64(42)
    );
}

#[test]
fn late_generic_inline_distinguishes_block_values_from_callable_blocks() {
    let source = r#"
        forward<T, L>(value: T, destination: L) -> !
            where L: Label<T> {
            destination(value)
        }
        invoke<F, L>(body: F, destination: L) -> !
            where F: Fn<(), Output=i64>, L: Label<i64> {
            destination(body())
        }
        block_value() -> i64 {
            forward({ 42 }, @block_value)
        }
        callable_block() -> i64 {
            invoke({ 42 }, @callable_block)
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-block-value.glorious", source, "block_value"),
        Value::I64(42)
    );
    assert_eq!(
        run(
            "late-inline-callable-block.glorious",
            source,
            "callable_block"
        ),
        Value::I64(42)
    );
}

#[test]
fn static_label_generic_call_preserves_callable_result_context() {
    let source = r#"
        visit<E, F, L>(body: F, exit: L) -> Result<(), E>
        where F: Fn<(), Output=Result<(), E>>,
        L: Label<Result<(), E>> {
            body()
        }
        walk() -> Result<(), i64> {
            visit({ => Result::Err(42) }, @walk)
        }
        answer() -> i64 {
            handle walk() {
                Result::Err(error) => error,
                Result::Ok(_) => 0
            }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-static-label-result.glorious", source, "answer"),
        Value::I64(42)
    );
}

#[test]
fn generic_option_constructor_alias_is_planned_inside_monomorphic_callers() {
    let source = r#"
        struct Item {
            cursor: usize,
            limit: usize,
            parent: Option<usize>
        }

        empty_items() -> Vec<Item> { Vec::new() }

        struct State {
            cursor: usize,
            limit: usize,
            parent: Option<usize>,
            values: Vec<Item>
        }

        complete(values: Vec<Item>) -> Result<i64, i64> {
            let remaining = values;
            handle Vec::pop(&mut remaining) {
                Result::Err(_) => Result::Ok(42),
                Result::Ok(item) => continue_scan(State {
                    cursor: item.cursor,
                    limit: item.limit,
                    parent: move item.parent,
                    values: remaining
                })
            }
        }

        continue_scan(state: State) -> Result<i64, i64> {
            state.cursor;
            state.limit;
            state.parent;
            complete(state.values)
        }

        answer() -> i64 {
            handle complete(empty_items()) {
                Result::Ok(value) => value,
                Result::Err(error) => error
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run(
            "generic-option-constructor-alias.glorious",
            source,
            "answer"
        ),
        Value::I64(42)
    );
}

#[test]
fn recursive_control_recovers_generic_results_from_named_struct_fields() {
    let source = r#"
        enum Binder {
            Wildcard,
            Local(u32)
        }
        struct Binding {
            marker: u8,
            local: Option<u32>
        }

        empty_binders() -> Vec<Binder> { Vec::new() }
        empty_bindings() -> Vec<Binding> { Vec::new() }

        local_field_first(
            binders: &Vec<Binder>,
            index: usize,
            output: &mut Vec<Binding>
        ) {
            if(index < Vec::len(binders)) {
                let binder = *Vec::index(binders, index);
                let local = handle binder {
                    Binder::Wildcard => None,
                    Binder::Local(value) => Option::Some(value)
                };
                Vec::push(&mut *output, Binding { local: local, marker: 1 });
                local_field_first(binders, index + 1, output)
            } else {
                ()
            }
        }

        marker_field_first(
            binders: &Vec<Binder>,
            index: usize,
            output: &mut Vec<Binding>
        ) {
            if(index < Vec::len(binders)) {
                let binder = *Vec::index(binders, index);
                let local = handle binder {
                    Binder::Wildcard => None,
                    Binder::Local(value) => Option::Some(value)
                };
                Vec::push(&mut *output, Binding { marker: 2, local: local });
                marker_field_first(binders, index + 1, output)
            } else {
                ()
            }
        }

        answer() -> usize {
            let binders = empty_binders();
            let left = empty_bindings();
            let right = empty_bindings();
            local_field_first(&binders, 0, &mut left);
            marker_field_first(&binders, 0, &mut right);
            Vec::len(&left) + Vec::len(&right)
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-struct-field-result.glorious", source, "answer"),
        Value::U64(0)
    );
}

#[test]
fn mandatory_resumption_is_consumed_once_by_a_nontransparent_generic_callee() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        finish<T>(continuation: T, answer: i64) -> i64 {
            resume(move continuation, answer)
        }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => finish(move k, 42)
            }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-mandatory-one.glorious", source, "answer"),
        Value::I64(42)
    );
}

#[test]
fn generic_call_learns_type_arguments_from_borrowed_field_projections() {
    let source = r#"
        struct Holder { slot: Option<u64> }
        store<T>(destination: &mut T, value: T) {
            *destination = move value;
        }
        clear(holder: &mut Holder) {
            store(&mut holder.slot, None)
        }
        answer() -> u64 {
            let holder = Holder { slot: Option::Some(7) };
            clear(&mut holder);
            if(Option::is_none(&holder.slot)) { 42 } else { 0 }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run(
            "generic-borrowed-projection-context.glorious",
            source,
            "answer"
        ),
        Value::U64(42)
    );
}

#[test]
fn retained_monomorphic_std_wrapper_keeps_its_generic_specialization() {
    let source = r#"
        answer() -> u8 { __g1_char_utf8_continuation(0, 0) }
        main() -> { () }
    "#;
    assert_eq!(
        run("retained-std-generic-child.glorious", source, "answer"),
        Value::U64(128)
    );
}

#[test]
fn phantom_index_tag_is_recovered_from_the_planned_result() {
    let source = r#"
        struct ExpressionTag {}
        struct TypedFlags {
            values: IndexVec<ExpressionTag, Bool>
        }
        typed_flags() -> TypedFlags {
            let flags = TypedFlags { values: IndexVec::new() };
            handle IndexVec::push(&mut flags.values, false) {
                Result::Err(_) => unreachable(),
                Result::Ok(_) => flags
            }
        }
        answer() -> usize {
            let flags = typed_flags();
            IndexVec::len(&flags.values)
        }
        main() -> () { () }
    "#;

    assert_eq!(
        run("late-inline-phantom-index-tag.glorious", source, "answer"),
        Value::U64(1)
    );
}

#[test]
fn exact_two_resumption_uses_are_consumed_transitively_by_a_generic_callee() {
    let source = r#"
        effect Pick { [2,2] choose() -> i64 }
        finish_twice<T>(continuation: T) -> i64 {
            let first = resume(continuation, 20);
            let second = resume(move continuation, 22);
            first + second
        }
        answer() -> i64 {
            handle perform Pick::choose() {
                Pick::choose() with k => finish_twice(move k)
            }
        }
        main() -> { () }
    "#;

    assert_eq!(
        run("late-inline-exact-two.glorious", source, "answer"),
        Value::I64(42)
    );
}

#[test]
fn transitive_generic_summaries_reject_wrong_exact_quantities() {
    let cases = [
        (
            "late-inline-one-used-zero.glorious",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                consume_zero<T>(continuation: T) -> i64 { 42 }
                answer() -> i64 {
                    handle perform Ask::ask() {
                        Ask::ask() with k => consume_zero(move k)
                    }
                }
                main() -> { () }
            "#,
        ),
        (
            "late-inline-one-used-twice.glorious",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                consume_twice<T>(continuation: T) -> i64 {
                    let first = resume(continuation, 20);
                    let second = resume(move continuation, 22);
                    first + second
                }
                answer() -> i64 {
                    handle perform Ask::ask() {
                        Ask::ask() with k => consume_twice(move k)
                    }
                }
                main() -> { () }
            "#,
        ),
        (
            "late-inline-two-used-once.glorious",
            r#"
                effect Pick { [2,2] choose() -> i64 }
                consume_once<T>(continuation: T) -> i64 {
                    resume(move continuation, 42)
                }
                answer() -> i64 {
                    handle perform Pick::choose() {
                        Pick::choose() with k => consume_once(move k)
                    }
                }
                main() -> { () }
            "#,
        ),
        (
            "late-inline-two-used-three.glorious",
            r#"
                effect Pick { [2,2] choose() -> i64 }
                consume_three<T>(continuation: T) -> i64 {
                    let first = resume(continuation, 10);
                    let second = resume(continuation, 12);
                    let third = resume(move continuation, 20);
                    first + second + third
                }
                answer() -> i64 {
                    handle perform Pick::choose() {
                        Pick::choose() with k => consume_three(move k)
                    }
                }
                main() -> { () }
            "#,
        ),
    ];

    for (source_name, source) in cases {
        assert_stable_quantity_error(source_name, source);
    }
}

#[test]
fn transitive_summary_follows_two_generic_forwarding_layers() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        deepest<T>(continuation: T) -> i64 {
            let first = resume(continuation, 20);
            let second = resume(move continuation, 22);
            first + second
        }
        middle<T>(continuation: T) -> i64 { deepest(move continuation) }
        outer<T>(continuation: T) -> i64 { middle(move continuation) }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => outer(move k)
            }
        }
        main() -> { () }
    "#;

    assert_stable_quantity_error("late-inline-two-layer-forward.glorious", source);
}

#[test]
fn branch_correlated_summary_requires_exact_consumption_on_every_handler_path() {
    let source = r#"
        enum Flag { Yes, No }
        effect Pick { [1,1] choose(flag: Flag) -> i64 }
        consume_once<T>(continuation: T) -> i64 {
            resume(move continuation, 42)
        }
        consume_zero<T>(continuation: T) -> i64 { 42 }
        answer(flag: Flag) -> i64 {
            handle perform Pick::choose(flag) {
                Pick::choose(Flag::Yes) with k => consume_once(move k),
                Pick::choose(Flag::No) with k => consume_zero(move k)
            }
        }
        main() -> { () }
    "#;

    assert_stable_quantity_error("late-inline-branch-correlation.glorious", source);
}

#[test]
fn same_late_generic_template_keeps_handler_resumption_identities_distinct() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        restore<T>(continuation: T, answer: i64) -> i64 {
            resume(move continuation, answer)
        }
        first() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => restore(move k, 41)
            }
        }
        second() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => restore(move k, 42)
            }
        }
        main() -> { () }
    "#;

    let artifact = compile_source_to_bytecode("late-inline-distinct-k.glorious", source).unwrap();
    let resumptions = artifact
        .handler_defs
        .iter()
        .flat_map(|handler| &handler.clauses)
        .filter_map(|clause| clause.resumption_type)
        .collect::<Vec<_>>();
    assert_eq!(resumptions.len(), 2);
    assert_ne!(resumptions[0], resumptions[1]);

    let verified = verify(artifact).unwrap();
    for (name, expected) in [("first", 41), ("second", 42)] {
        let function = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(expected)
        );
    }
}

#[test]
fn recursive_late_generic_inline_reports_a_source_diagnostic() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        recur<T>(continuation: T) -> i64 { recur(move continuation) }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => recur(move k)
            }
        }
        main() -> { () }
    "#;

    let errors = compile_source_to_bytecode("late-inline-recursion.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.span.is_some()
                && matches!(error.code.as_deref(), Some("G1BC001" | "G1BC002"))
                && (error
                    .message
                    .contains("recursive late generic specialization")
                    || error
                        .message
                        .contains("recursive generic calls transporting")
                    || error
                        .message
                        .contains("call target: `recur` is not a callable"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn range_callback_branded_try_leaves_the_enclosing_function() {
    let source = r#"
        check_index(index: usize, rejected: usize) -> Result<(), usize> {
            if(index == rejected) {
                Result::Err(index)
            } else {
                Result::Ok(())
            }
        }

        walk(limit: usize, rejected: usize) -> Result<(), usize> {
            try_for_range(Range::new(0, limit), { index => {
                try(check_index(index, rejected), @walk);
                Result::Ok(())
            } })
        }

        success() -> usize {
            handle walk(4, 9) {
                Result::Ok(_) => 42,
                Result::Err(error) => error
            }
        }

        failure() -> usize {
            handle walk(4, 2) {
                Result::Ok(_) => 90,
                Result::Err(error) => error
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("range-callback-branded-try.glorious", source, "success"),
        Value::U64(42)
    );
    assert_eq!(
        run("range-callback-branded-try.glorious", source, "failure"),
        Value::U64(2)
    );
}

#[test]
fn range_callback_infers_nested_vec_constructors() {
    let source = r#"
        consume(values: &mut Vec<u32>, value: u32) {
            Vec::push(&mut *values, value)
        }

        checked(value: usize) -> Result<u32, usize> {
            Result::Ok(wrapping_convert_to_u32(value))
        }

        walk() -> Result<(), usize> {
            try_for_range(Range::new(0, 2), { index => {
                let values = Vec::new();
                let value = try(checked(index), @walk);
                consume(&mut values, value);
                Result::Ok(())
            } })
        }

        answer() -> usize {
            handle walk() {
                Result::Ok(_) => 42,
                Result::Err(error) => error
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run(
            "range-callback-nested-vec-inference.glorious",
            source,
            "answer"
        ),
        Value::U64(42)
    );
}

#[test]
fn late_generic_inline_does_not_bypass_private_deconstruction_authority() {
    let bundle = SourceBundle::new(
        Segment::new(
            "owner.glorious",
            r#"
                effect Stop { [0,1] stop() -> i64 }
                struct Secret<T> { private value: T }
                seal<T>(value: T, marker: i64) -> Secret<T> {
                    marker;
                    Secret { value: move value }
                }
            "#,
        ),
        Segment::new(
            "caller.glorious",
            r#"
                answer() -> i64 {
                    handle perform Stop::stop() {
                        Stop::stop() with k => {
                            let stored = seal(move k, 0);
                            let Secret { value } = move stored;
                            cancel(move value);
                            42
                        }
                    }
                }
                main() -> { () }
            "#,
        ),
        [],
    );

    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("private fields of struct `Secret`")
                && error
                    .message
                    .contains("deconstructed only within its defining source segment")
        }),
        "{errors:#?}"
    );
}
