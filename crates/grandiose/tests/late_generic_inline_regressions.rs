use grandiose::{
    compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases,
    compiler_mir::Terminator,
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

fn canonical_function_section<'a>(text: &'a str, name: &str) -> &'a str {
    let marker = format!(" \"{name}\" ");
    let start = text
        .match_indices("fn#")
        .find_map(|(start, _)| {
            let end = text[start..]
                .find('\n')
                .map(|offset| start + offset)
                .unwrap_or(text.len());
            text[start..end].contains(&marker).then_some(start)
        })
        .unwrap_or_else(|| panic!("canonical output is missing function `{name}`"));
    let end = text[start + 1..]
        .find("\nfn#")
        .map(|offset| start + 1 + offset)
        .unwrap_or(text.len());
    &text[start..end]
}

#[test]
fn user_named_label_control_helper_forms_a_cached_structural_loop() {
    let source = r#"
        custom_walk<L, F>(
            index: usize,
            limit: usize,
            exit: L,
            body: F
        )
        where L: Label<usize>,
        F: Fn<(usize, L), Output = ()> {
            handle index == limit {
                true => (),
                false => {
                    body(index, exit);
                    custom_walk(index + 1, limit, exit, body)
                }
            }
        }

        answer() -> usize {
            @done: usize {
                custom_walk(0, 4, @done, { index, done =>
                    if(index == 2) { done(7) } else { () }
                });
                90
            }
        }

        main() -> { () }
    "#;

    let phases = compile_source_to_phases("user-control-summary.glorious", source).unwrap();
    let answer = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "answer")
        .unwrap();
    let core = format!("{:#?}", answer.body);
    assert_eq!(
        core.match_indices("kind: ControlLoop {").count(),
        1,
        "a structurally valid user helper should form exactly one control loop"
    );
    assert!(
        core.contains("kind: Leave {"),
        "the callback's branded exit should become a direct Core leave"
    );
    assert!(
        phases
            .artifact
            .functions
            .iter()
            .all(|function| !function.name.starts_with("custom_walk")),
        "the static control helper must not survive as a runtime callable"
    );
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(function, vec![])
            .unwrap(),
        Value::U64(7)
    );
}

#[test]
fn function_label_resolves_lexically_named_ground_generic_payload() {
    let source = r#"
        enum Failure { Rejected }
        enum Attempt<T, E> { NoMatch, Parsed(T), Diagnostic(E) }

        concrete_miss() -> Attempt<(), Failure> { Attempt::NoMatch }

        leave_miss<L>(destination: L) -> !
        where L: Label<Attempt<(), Failure>> {
            destination(concrete_miss())
        }

        probe() -> Attempt<(), Failure> { leave_miss(@probe) }

        answer() -> i64 {
            handle probe() {
                Attempt::NoMatch => 7,
                Attempt::Parsed(_) => 8,
                Attempt::Diagnostic(_) => 9
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("ground-generic-label-payload.glorious", source, "answer"),
        Value::I64(7)
    );
}

#[test]
fn static_control_closure_preserves_colliding_mutable_capture() {
    let source = r#"
        values() -> Vec<usize> {
            let output = Vec::new();
            Vec::push(&mut output, 2);
            Vec::push(&mut output, 3);
            Vec::push(&mut output, 5);
            output
        }

        accept(item: &usize) -> Result<(), usize> {
            if(*item == 5) {
                Result::Err(*item)
            } else {
                Result::Ok(())
            }
        }

        collect(
            value: &mut Vec<usize>,
            source: &Vec<usize>
        ) -> Result<(), usize> {
            Slice::try_for_each(Vec::as_slice(source), { item => {
                try(accept(item), @collect);
                Vec::push(&mut *value, *item);
                Result::Ok(())
            }})
        }

        answer() -> usize {
            let source = values();
            let output = Vec::new();
            handle collect(&mut output, &source) {
                Result::Err(error) => error * 10 + Vec::len(&output),
                Result::Ok(_) => 90
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("static-control-closure-capture.glorious", source, "answer"),
        Value::U64(52)
    );
}

#[test]
fn static_control_closure_preserves_planned_calls_in_branch_conditions() {
    let source = r#"
        values() -> Vec<usize> {
            let output = Vec::new();
            Vec::push(&mut output, 2);
            Vec::push(&mut output, 3);
            Vec::push(&mut output, 5);
            output
        }

        accept(
            value: &mut Vec<usize>,
            item: &usize
        ) -> Result<usize, usize> {
            Vec::push(&mut *value, *item);
            if(*item == 5) {
                Result::Err(*item)
            } else {
                Result::Ok(*item)
            }
        }

        collect(
            value: &mut Vec<usize>,
            output: &mut Vec<usize>,
            source: &Vec<usize>
        ) -> Result<(), usize> {
            Slice::try_for_each(Vec::as_slice(source), { item => {
                if(Vec::len(output) < 2) {
                    let found = try(accept(value, item), @collect);
                    Vec::push(&mut *output, found);
                    Result::Ok(())
                } else {
                    Result::Err(99)
                }
            }})
        }

        answer() -> usize {
            let source = values();
            let visited = Vec::new();
            let output = Vec::new();
            handle collect(&mut visited, &mut output, &source) {
                Result::Err(error) =>
                    error * 100 + Vec::len(&visited) * 10 + Vec::len(&output),
                Result::Ok(_) => 900
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("static-control-planned-call.glorious", source, "answer"),
        Value::U64(9922)
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
fn slice_for_each_callback_branded_try_fuses_direct_recursion_once() {
    let owner = r#"
        struct Edge { value: u32 }

        struct Index { private values: Vec<Edge> }

        struct Headers { private index: Index }

        enum IndexView<'a> {
            Tuple(Slice<'a, Edge>),
            Never
        }

        impl<'a> Use<[0, *]> for IndexView<'a> {}

        headers() -> Headers {
            let values = Vec::new();
            Vec::push(&mut values, Edge { value: 1 });
            Vec::push(&mut values, Edge { value: 1 });
            Headers { index: Index { values: values } }
        }

        parsed_index<'a>(value: &'a Headers) -> &'a Index { &value.index }

        index_view<'a>(value: &'a Index, id: u32) -> IndexView<'a> {
            if(id == 0) {
                IndexView::Tuple(Vec::as_slice(&value.values))
            } else {
                IndexView::Never
            }
        }

        edge_value(value: &Edge) -> u32 { value.value }
    "#;

    let caller = r#"
        enum ResolveError { Rejected(usize) }

        words() -> Vec<u32> { Vec::new() }

        finish(output: &mut Vec<u32>, accepted: &Vec<u32>) -> usize {
            Vec::push(&mut *output, wrapping_convert_to_u32(Vec::len(accepted)));
            Vec::len(output)
        }

        resolve(
            headers: &Headers,
            declarations: &Vec<u32>,
            output: &mut Vec<u32>,
            type_id: u32,
            module: Option<usize>
        ) -> Result<u32, ResolveError> {
            let parsed = parsed_index(headers);
            handle index_view(parsed, type_id) {
                IndexView::Tuple(children) => if(Slice::is_empty(children)) {
                    Result::Ok(0)
                } else {
                    let accepted_values = words();
                    Slice::for_each(children, { value => {
                        let accepted = try(resolve(
                            headers,
                            declarations,
                            &mut *output,
                            edge_value(value),
                            module
                        ), @resolve);
                        Vec::push(&mut accepted_values, accepted)
                    } });
                    finish(output, &accepted_values);
                    Result::Ok(wrapping_convert_to_u32(
                        Vec::len(&accepted_values)
                    ))
                },
                IndexView::Never => Result::Ok(type_id)
            }
        }

        answer() -> usize {
            let headers = headers();
            let declarations = words();
            let output = Vec::new();
            handle resolve(
                &headers,
                &declarations,
                &mut output,
                0,
                Option::Some(7)
            ) {
                Result::Err(_) => 50 + Vec::len(&output),
                Result::Ok(value) => wrapping_convert_to_usize(value)
            }
        }

        main() -> { () }
    "#;

    let bundle = SourceBundle::distributed(
        Segment::new("slice-view-owner.glorious", owner),
        [Segment::new("slice-view-caller.glorious", caller)],
    );
    let phases = grandiose::compile_bundle_to_phases(&bundle).unwrap();
    let resolve = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "resolve")
        .unwrap();
    let control_loops = format!("{:#?}", resolve.body)
        .match_indices("kind: ControlLoop {")
        .count();
    assert_eq!(
        control_loops, 1,
        "the direct recursive slice helper should fuse into one control loop"
    );
    assert_eq!(
        {
            let answer = phases
                .artifact
                .functions
                .iter()
                .position(|function| function.name == "answer")
                .unwrap() as u32;
            Vm::new(verify(phases.artifact).unwrap())
                .run(answer, vec![])
                .unwrap()
        },
        Value::U64(2)
    );
}

#[test]
fn nested_fused_loop_preserves_enclosing_range_continuation() {
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
                for_range(Range::new(0, 1), { inner => {
                    inner;
                    ()
                } });
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
        run(
            "nested-fused-loop-range-continuation.glorious",
            source,
            "success"
        ),
        Value::U64(42)
    );
    assert_eq!(
        run(
            "nested-fused-loop-range-continuation.glorious",
            source,
            "failure"
        ),
        Value::U64(2)
    );
}

#[test]
fn nested_same_range_helper_preserves_both_control_loops() {
    let source = r#"
        nested_sum() -> usize {
            for_range(Range::new(0, 3), { outer => {
                for_range(Range::new(0, 2), { inner => {
                    outer;
                    inner;
                    ()
                } })
            } });
            wrapping_convert_to_usize(42)
        }

        main() -> { () }
    "#;

    let phases = grandiose::compile_source_to_phases("nested-same-range.glorious", source).unwrap();
    let nested = phases
        .core
        .functions
        .iter()
        .find(|function| function.name == "nested_sum")
        .unwrap();
    assert_eq!(
        format!("{:#?}", nested.body)
            .match_indices("kind: ControlLoop {")
            .count(),
        2,
        "each nested invocation of the same recursive helper needs its own loop context"
    );
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "nested_sum")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(function, vec![])
            .unwrap(),
        Value::U64(42)
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
fn range_callback_infers_map_err_input_from_direct_call() {
    let source = r#"
        enum SourceError { Rejected }
        enum TargetError { Rejected(usize) }

        read(index: usize, rejected: usize) -> Result<u32, SourceError> {
            if(index == rejected) {
                Result::Err(SourceError::Rejected)
            } else {
                Result::Ok(wrapping_convert_to_u32(index))
            }
        }

        walk(rejected: usize) -> Result<(), TargetError> {
            try_for_range(Range::new(0, 4), { index => {
                let value = try(
                    Result::map_err(
                        read(index, rejected),
                        { _ => TargetError::Rejected(index) }
                    ),
                    @walk
                );
                value;
                Result::Ok(())
            } })
        }

        success() -> usize {
            handle walk(9) {
                Result::Ok(_) => 42,
                Result::Err(TargetError::Rejected(index)) => index
            }
        }

        failure() -> usize {
            handle walk(2) {
                Result::Ok(_) => 90,
                Result::Err(TargetError::Rejected(index)) => index
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("range-callback-map-err-call.glorious", source, "success"),
        Value::U64(42)
    );
    assert_eq!(
        run("range-callback-map-err-call.glorious", source, "failure"),
        Value::U64(2)
    );
}

#[test]
fn pure_literal_range_callbacks_fuse_but_ordinary_generic_callbacks_do_not() {
    let source = r#"
        effect Stop { stop(index: usize) -> ! }

        observe(index: usize) { index; () }

        single_value() -> Vec<usize> {
            let source = Vec::new();
            Vec::push(&mut source, 17);
            source
        }

        pure_range_impl(limit: usize) -> usize {
            for_range(Range::new(0, limit), { index => {
                observe(index)
            } });
            limit
        }

        pure_range() -> usize { pure_range_impl(5) }
        empty_range() -> usize { pure_range_impl(0) }

        observed_range() -> usize {
            handle {
                for_range(Range::new(0, 5), { index => {
                    if(index == 3) {
                        perform Stop::stop(index)
                    } else {
                        ()
                    }
                } });
                90
            } {
                Stop::stop(index) => index
            }
        }

        observed_slice() -> usize {
            let source = single_value();
            handle {
                Slice::for_each(Vec::as_slice(&source), { item => {
                    perform Stop::stop(*item)
                } });
                90
            } {
                Stop::stop(item) => item
            }
        }

        completed_slice() -> usize {
            let source = single_value();
            Slice::for_each(Vec::as_slice(&source), { item => {
                observe(*item)
            } });
            Vec::len(&source)
        }

        apply<F>(value: usize, body: F) -> usize
        where F: Fn<(usize), Output=usize> {
            body(value)
        }

        ordinary_generic() -> usize {
            apply(41, { value => value + 1 })
        }

        main() -> { () }
    "#;

    assert_eq!(
        run("pure-range-control-fusion.glorious", source, "pure_range"),
        Value::U64(5)
    );
    assert_eq!(
        run("empty-range-control-fusion.glorious", source, "empty_range"),
        Value::U64(0)
    );
    assert_eq!(
        run(
            "observed-range-control-fusion.glorious",
            source,
            "observed_range"
        ),
        Value::U64(3)
    );
    assert_eq!(
        run(
            "ordinary-generic-control.glorious",
            source,
            "ordinary_generic"
        ),
        Value::U64(42)
    );
    assert_eq!(
        run(
            "borrowed-slice-control-fusion.glorious",
            source,
            "observed_slice"
        ),
        Value::U64(17)
    );
    assert_eq!(
        run(
            "completed-borrowed-slice-control-fusion.glorious",
            source,
            "completed_slice"
        ),
        Value::U64(1)
    );

    let phases = compile_source_to_phases("pure-range-control-fusion.glorious", source).unwrap();
    let core = phases.core.canonical_text();
    let pure_core = canonical_function_section(&core, "pure_range_impl");
    assert!(pure_core.contains("control-loop"), "{pure_core}");
    assert!(pure_core.contains("control-continue"), "{pure_core}");
    let ordinary_core = canonical_function_section(&core, "ordinary_generic");
    assert!(!ordinary_core.contains("control-loop"), "{ordinary_core}");
    assert!(
        !ordinary_core.contains("control-continue"),
        "{ordinary_core}"
    );

    let names = phases
        .mir
        .functions
        .iter()
        .map(|function| (function.declaration, function.name.as_str()))
        .collect::<std::collections::BTreeMap<_, _>>();
    for (caller, forbidden) in [
        ("pure_range_impl", vec!["for_range", "__g1_for_range_step"]),
        (
            "observed_slice",
            vec!["slice_for_each", "__g1_slice_for_each_step"],
        ),
        ("ordinary_generic", vec!["__no_forbidden_target__"]),
    ] {
        let function = phases
            .mir
            .functions
            .iter()
            .find(|function| function.name == caller)
            .unwrap();
        let called = function
            .blocks
            .iter()
            .filter_map(|block| match block.terminator {
                Terminator::Call { function, .. } | Terminator::TailCall { function, .. } => {
                    names.get(&function).copied()
                }
                _ => None,
            })
            .collect::<Vec<_>>();
        assert!(
            forbidden
                .iter()
                .all(|forbidden| called.iter().all(|name| !name.contains(forbidden))),
            "{caller} retained a range wrapper/step call: {called:?}"
        );
        if caller == "ordinary_generic" {
            assert!(
                called
                    .iter()
                    .any(|name| name.contains("$specialization$apply")),
                "ordinary generic literal callback was unexpectedly fused: {called:?}"
            );
        }
    }
}

#[test]
fn control_inlined_callback_preserves_manifest_primitive_calls() {
    let source = r#"
        empty_usizes() -> Vec<usize> { Vec::new() }

        collected_length() -> usize {
            let values = fold_range(
                Range::new(0, 4),
                empty_usizes(),
                { values, index => {
                    Vec::push(&mut values, index);
                    move values
                } }
            );
            Vec::len(&values)
        }

        main() -> { () }
    "#;

    assert_eq!(
        run(
            "control-inline-manifest-leaf.glorious",
            source,
            "collected_length"
        ),
        Value::U64(4)
    );
}

#[test]
fn fused_try_range_preserves_external_unique_capture_loan() {
    let source = r#"
        inspect(
            input: &Vec<u32>,
            limit: usize
        ) -> Result<(), usize> {
            let item = Vec::index(input, 0);
            try_for_range(Range::new(0, limit), { _ => {
                *item;
                Result::Ok(())
            } })
        }

        append(
            output: &mut Vec<u32>,
            limit: usize
        ) -> Result<(), usize> {
            try_for_range(Range::new(0, limit), { index => {
                Vec::push(&mut *output, wrapping_convert_to_u32(index));
                Result::Ok(())
            } })
        }

        answer() -> usize {
            let output = Vec::new();
            handle append(&mut output, 3) {
                Result::Err(error) => error,
                Result::Ok(_) => handle inspect(&output, 3) {
                    Result::Err(error) => error,
                    Result::Ok(_) => Vec::len(&output)
                }
            }
        }

        main() -> { () }
    "#;

    assert_eq!(
        run(
            "fused-range-external-unique-capture.glorious",
            source,
            "answer"
        ),
        Value::U64(3)
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
