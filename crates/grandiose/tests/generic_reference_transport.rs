use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

fn run_i64_at_all_levels(source: &str, function: &str) {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "generic-reference-transport.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|candidate| candidate.name == function)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(phases.artifact).unwrap())
                .run(function, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn projected_shared_return_outlives_the_parent_reference_handle() {
    let source = r#"
        struct Wrapper { private value: i64 }
        inner(wrapper: &Wrapper) -> &i64 { &wrapper.value }
        value(wrapper: &Wrapper) -> &i64 { inner(wrapper) }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile_source_to_phases_with_options(
            "projected-reference-return.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}

#[test]
fn aggregate_reference_return_tracks_owned_projection_paths() {
    let source = r#"
        struct Lexed { lexemes: Interner<String> }

        lookup<'a>(value: &'a Lexed, id: Id<String>) -> Option<&'a String> {
            Interner::get(&value.lexemes, move id)
        }

        main() -> { () }
    "#;
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            for optimization_level in [
                OptimizationLevel::O1,
                OptimizationLevel::O2,
                OptimizationLevel::O3,
            ] {
                compile_source_to_phases_with_options(
                    "owned-projection-reference-return.glorious",
                    source,
                    CompileOptions { optimization_level },
                )
                .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn option_as_ref_tracks_the_active_enum_variant() {
    let source = r#"
        lookup<'a>(value: &'a Option<i64>) -> Option<&'a i64> {
            Option::as_ref(value)
        }

        main() -> { () }
    "#;
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || {
            for optimization_level in [
                OptimizationLevel::O1,
                OptimizationLevel::O2,
                OptimizationLevel::O3,
            ] {
                compile_source_to_phases_with_options(
                    "option-as-ref-enum-origin.glorious",
                    source,
                    CompileOptions { optimization_level },
                )
                .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn shared_borrow_of_a_temporary_owner_agrees_with_core_lowering() {
    let source = r#"
        effect TemporaryOwnerCase { inspect() -> !; }
        consume(value: &Bytes) -> usize { Bytes::len(value) }
        answer() -> usize {
            handle perform TemporaryOwnerCase::inspect() {
                TemporaryOwnerCase::inspect() => consume(&String::as_bytes(&"temporary"))
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile_source_to_phases_with_options(
            "temporary-owner-borrow.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}

fn run_i64_at_all_levels_and_recovery(source: &str, function: &str) {
    run_i64_at_all_levels(source, function);
    let recovery_source = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        grandiose::run_source(
            "generic-reference-transport-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

#[test]
fn generic_pair_constructor_transports_two_distinct_reference_origins() {
    let source = r#"
        pair<L, R>(left: L, right: R) -> (L, R) { (left, right) }

        answer() -> i64 {
            let left = 20;
            let right = 22;
            let returned = pair(&left, &right);
            let returned_left = returned.0;
            let returned_right = returned.1;
            *returned_left + *returned_right
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn nested_generic_wrappers_preserve_multi_leaf_reference_paths() {
    let source = r#"
        pair<L, R>(left: L, right: R) -> (L, R) { (left, right) }
        relay<L, R>(left: L, right: R) -> (L, R) { pair(left, right) }

        answer() -> i64 {
            let left = 20;
            let right = 22;
            let returned = relay(&left, &right);
            let returned_left = returned.0;
            let returned_right = returned.1;
            *returned_left + *returned_right
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn generic_nominal_signature_preserves_reference_bearing_fields() {
    let source = r#"
        struct Pair<L, R> { left: L, right: R }

        pair<L, R>(left: L, right: R) -> Pair<L, R> {
            Pair { left: left, right: right }
        }

        answer() -> i64 {
            let left = 20;
            let right = 22;
            let returned = pair(&left, &right);
            let returned_left = returned.left;
            let returned_right = returned.right;
            *returned_left + *returned_right
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn generic_reference_result_cannot_escape_its_concrete_owner() {
    let source = r#"
        retain<T>(value: T) -> T { value }

        escape() -> &i64 {
            let value = 42;
            retain(&value)
        }

        main() -> { () }
    "#;
    let errors = compile_source_to_phases_with_options(
        "generic-reference-escape.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .expect_err("generic specialization must not erase a concrete borrow origin");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("reference")
                && (error.message.contains("escape")
                    || error.message.contains("return")
                    || error.message.contains("lifetime"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn generated_reference_wrapper_can_be_dereferenced_without_a_named_intermediate() {
    let source = r#"
        relay<'a>(value: &'a i64) -> &'a i64 { value }
        answer() -> i64 {
            let value = 42;
            *relay(&value)
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn temporary_aggregate_projection_chain_preserves_the_reference_origin() {
    let source = r#"
        nested<'a>(value: &'a i64) -> ((&'a i64, i64), i64) {
            ((value, 7), 9)
        }

        answer() -> i64 {
            let value = 42;
            *nested(&value).0.0
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn dominating_variant_proof_allows_reference_payload_field_access() {
    let source = r#"
        enum Choice { Yes(&i64), No }

        answer() -> i64 {
            let value = 42;
            let choice = Choice::Yes(&value);
            if(choice is Choice::Yes(_)) {
                *choice.0
            } else { 0 }
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn reference_bearing_tuple_deconstruction_transfers_the_exact_origin() {
    let source = r#"
        consume<'a>(pair: (&'a i64, i64)) -> i64 {
            let (borrowed, increment) = move pair;
            *borrowed + increment
        }

        answer() -> i64 {
            let value = 40;
            consume((&value, 2))
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn reference_to_enum_projection_uses_the_dominating_variant_proof() {
    let source = r#"
        enum Choice { Yes(i64), No }

        inspect(borrowed_choice: &Choice) -> i64 {
            if(*borrowed_choice is Choice::Yes(_)) {
                borrowed_choice.0
            } else { 0 }
        }

        answer() -> i64 {
            let choice = Choice::Yes(42);
            inspect(&choice)
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn projected_shared_reborrow_retains_a_temporary_parent_reference() {
    let source = r#"
        struct Point { x: i64, y: i64 }

        relay<'a>(point: &'a Point) -> &'a Point { point }

        answer() -> i64 {
            let point = Point { x: 40, y: 2 };
            let x = &(*relay(&point)).x;
            *x + point.y
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn projected_unique_reborrow_retains_a_temporary_parent_reference() {
    let source = r#"
        struct Point { x: i64, y: i64 }

        relay<'a>(point: &'a mut Point) -> &'a mut Point { point }

        answer() -> i64 {
            let point = Point { x: 0, y: 2 };
            let result = {
                let x = &mut (*relay(&mut point)).x;
                *x = 40;
                *x
            };
            result + point.y
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn enum_reference_payload_access_requires_proof_and_preserves_escape_safety() {
    let without_proof = r#"
        enum Choice { Yes(&i64), No }
        bad(choice: Choice) -> i64 { *choice.0 }
        main() -> { () }
    "#;
    let escaping = r#"
        enum Choice { Yes(&i64), No }
        escape() -> &i64 {
            let value = 42;
            let choice = Choice::Yes(&value);
            if(choice is Choice::Yes(_)) {
                choice.0
            } else { &value }
        }
        main() -> { () }
    "#;
    let temporary_projection_escape = r#"
        pair<'a>(value: &'a i64) -> (&'a i64, i64) { (value, 7) }
        escape() -> &i64 {
            let value = 42;
            pair(&value).0
        }
        main() -> { () }
    "#;
    let deconstruction_escape = r#"
        escape() -> &i64 {
            let value = 42;
            let pair = (&value, 7);
            let (borrowed, _) = move pair;
            borrowed
        }
        main() -> { () }
    "#;
    let deconstruction_alias = r#"
        bad() -> {
            let value = 42;
            let pair = (&mut value, 7);
            let (borrowed, _) = move pair;
            let conflicting = &mut value;
            borrowed;
            conflicting;
            ()
        }
        main() -> { () }
    "#;
    let temporary_reborrow_escape = r#"
        struct Point { x: i64 }
        relay<'a>(point: &'a Point) -> &'a Point { point }
        escape() -> &i64 {
            let point = Point { x: 42 };
            &(*relay(&point)).x
        }
        main() -> { () }
    "#;
    let temporary_unique_reborrow_alias = r#"
        struct Point { x: i64 }
        relay<'a>(point: &'a mut Point) -> &'a mut Point { point }
        bad() -> {
            let point = Point { x: 42 };
            let projected = &mut (*relay(&mut point)).x;
            let conflicting = &mut point.x;
            projected;
            conflicting;
            ()
        }
        main() -> { () }
    "#;
    for (name, source, needle) in [
        (
            "enum-reference-without-proof.glorious",
            without_proof,
            "dominating",
        ),
        ("enum-reference-escape.glorious", escaping, "escape"),
        (
            "temporary-reference-projection-escape.glorious",
            temporary_projection_escape,
            "escape",
        ),
        (
            "reference-deconstruction-escape.glorious",
            deconstruction_escape,
            "escape",
        ),
        (
            "reference-deconstruction-alias.glorious",
            deconstruction_alias,
            "incompatible live loan",
        ),
        (
            "temporary-projected-reborrow-escape.glorious",
            temporary_reborrow_escape,
            "escape",
        ),
        (
            "temporary-unique-reborrow-alias.glorious",
            temporary_unique_reborrow_alias,
            "incompatible live loan",
        ),
    ] {
        for optimization_level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let errors = compile_source_to_phases_with_options(
                name,
                source,
                CompileOptions { optimization_level },
            )
            .expect_err("unsafe enum reference payload access compiled");
            assert!(
                errors.iter().any(|error| error.message.contains(needle)),
                "{optimization_level:?}: expected {needle:?}, got {errors:#?}"
            );
        }
    }
}

#[test]
fn generic_borrow_expression_creates_a_projected_region() {
    let source = r#"
        struct Cell<T> { value: T }

        project<'a, T>(cell: &'a Cell<T>) -> &'a T { &cell.value }

        answer() -> i64 {
            let cell = Cell { value: 42 };
            let projected = project(&cell);
            *projected
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn generic_nonescaping_closure_transports_its_reference_capture() {
    let source = r#"
        invoke<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }

        relay<'a>(borrowed: &'a i64) -> i64 {
            invoke(() -> i64 { *borrowed })
        }

        answer() -> i64 {
            let value = 42;
            relay(&value)
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn type_parametric_nonescaping_closure_materializes_its_reference_environment_late() {
    let source = r#"
        invoke<F>(body: F) -> () where F: Fn<(), Output=()> { body() }

        touch<'a, T>(borrowed: &'a T) -> () {
            invoke(() -> () {
                let forwarded = borrowed;
                forwarded;
                ()
            })
        }

        answer() -> i64 {
            let value = 42;
            touch(&value);
            value
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn generic_callback_result_transports_a_reference_capture_origin() {
    let source = r#"
        invoke<F, R>(body: F) -> R where F: Fn<(), Output=R> { body() }

        relay<'a>(borrowed: &'a i64) -> &'a i64 {
            invoke(() -> &'a i64 { borrowed })
        }

        answer() -> i64 {
            let value = 42;
            *relay(&value)
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_generic_callback_substitutes_the_selected_reference_lifetime() {
    let source = r#"
        apply2<F, T, R>(left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> { body(left, right) }

        answer() -> i64 {
            let left = 42;
            let right = 7;
            let selected = apply2(&left, &right, { first, second => first });
            *selected
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_callback_projects_a_reference_leaf_from_an_aggregate_parameter() {
    let source = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }

        select_first<'a, T>(pair: (&'a T, &'a T)) -> &'a T {
            apply(pair, { projected => projected.0 })
        }

        answer() -> i64 {
            let left = 42;
            let right = 7;
            let selected = select_first((&left, &right));
            *selected
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_callback_projects_reference_from_receiver_environment() {
    let source = r#"
        struct Receiver<T> { selected: T }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }

        select<'a>(receiver: Receiver<&'a i64>) -> &'a i64 {
            apply(receiver, { current => current.selected })
        }

        answer() -> i64 {
            let value = 42;
            *select(Receiver { selected: &value })
        }
        main() -> { () }
    "#;
    run_i64_at_all_levels_and_recovery(source, "answer");
}

#[test]
fn higher_order_callback_deconstructs_an_enum_reference_payload() {
    let source = r#"
        enum Envelope<T> { Selected(T) }
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        never<'a>(fallback: &'a i64) -> &'a i64 { never(fallback) }

        select<'a>(envelope: Envelope<&'a i64>, fallback: &'a i64) -> &'a i64 {
            apply(envelope, { current =>
                if(current is Envelope::Selected(selected)) {
                    selected
                } else { never(fallback) }
            })
        }

        answer() -> i64 {
            let value = 42;
            *select(Envelope::Selected(&value), &value)
        }
        main() -> { () }
    "#;
    run_i64_at_all_levels_and_recovery(source, "answer");
}

#[test]
fn higher_order_callback_preserves_reference_routes_through_recursive_wrappers() {
    let source = r#"
        enum Step { Done, Again }
        apply_recursive<F, T, R>(step: Step, value: T, body: F) -> R
            where F: Fn<(T), Output=R> {
            if(step is Step::Done) {
                body(value)
            } else {
                apply_recursive(Step::Done(), value, body)
            }
        }

        select<'a>(value: &'a i64) -> &'a i64 {
            apply_recursive(Step::Again(), value, { current => current })
        }

        answer() -> i64 {
            let value = 42;
            *select(&value)
        }
        main() -> { () }
    "#;
    run_i64_at_all_levels_and_recovery(source, "answer");
}

#[test]
fn higher_order_recursive_wrapper_with_an_altered_reference_state_fails_closed() {
    let source = r#"
        enum Step { Done, Again }
        apply_recursive<F, T, R>(step: Step, left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> {
            if(step is Step::Done) {
                body(left, right)
            } else {
                apply_recursive(Step::Done(), right, left, body)
            }
        }
        bad<'a>(left: &'a i64, right: &'a i64) -> &'a i64 {
            apply_recursive(
                Step::Again(),
                left,
                right,
                { first, second => first }
            )
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_phases_with_options(
            "recursive-wrapper-altered-reference-state.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("an altered recursive reference environment compiled as an invariant route");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("exactly one compatible reference")
                    || error.message.contains("uniquely selected")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}

#[test]
fn higher_order_callback_selects_an_exact_capture_over_a_compatible_parameter() {
    let source = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }

        answer() -> i64 {
            let ignored = 7;
            let answer = 42;
            let captured = &answer;
            let selected = apply(&ignored, { argument => captured });
            *selected
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_callback_equal_cfg_arms_preserve_one_symbolic_lifetime() {
    let source = r#"
        enum Flag { Yes, No }

        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }

        select_first<'a>(flag: Flag, pair: (&'a i64, &'a i64)) -> &'a i64 {
            apply(pair, { projected =>
                if(flag is Flag::Yes) { projected.0 } else { projected.0 }
            })
        }

        answer() -> i64 {
            let selected = 42;
            let ignored = 7;
            *select_first(Flag::Yes(), (&selected, &ignored))
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_callback_composes_proved_opaque_wrapper_edges() {
    let source = r#"
        apply2<F, T, R>(left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> { body(left, right) }

        inner<'a>(value: &'a i64) -> &'a i64 { value }
        outer<'a>(value: &'a i64) -> &'a i64 { inner(value) }

        answer() -> i64 {
            let selected = 42;
            let ignored = 7;
            let returned = apply2(
                &selected,
                &ignored,
                { first, second => outer(first) }
            );
            *returned
        }

        main() -> { () }
    "#;
    run_i64_at_all_levels(source, "answer");
}

#[test]
fn higher_order_callback_divergent_cfg_origins_fail_closed() {
    let source = r#"
        enum Flag { Yes, No }

        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }

        choose<'a>(
            flag: Flag,
            pair: (&'a mut i64, &'a mut i64)
        ) -> &'a mut i64 {
            apply(
                pair,
                { projected =>
                    if(flag is Flag::Yes) { projected.0 } else { projected.1 }
                }
            )
        }

        bad() -> {
            let left = 40;
            let right = 2;
            let selected = choose(Flag::Yes(), (&mut left, &mut right));
            let conflicting = &mut left;
            selected;
            conflicting;
            ()
        }

        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_phases_with_options(
            "higher-order-divergent-cfg-origin.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("divergent callback origins compiled as one symbolic lifetime");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("exactly one compatible reference")
                    || error.message.contains("incompatible live loan")
            }),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}

#[test]
fn higher_order_selected_lifetime_cannot_escape_or_alias_its_owner() {
    let escaping = r#"
        apply<F, T, R>(value: T, body: F) -> R
            where F: Fn<(T), Output=R> { body(value) }
        escape<'a>(other: &'a i64) -> &'a i64 {
            let local = 42;
            apply((&local, other), { pair => pair.0 })
        }
        main() -> { () }
    "#;
    let aliasing = r#"
        apply2<F, T, R>(left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> { body(left, right) }
        bad() -> {
            let left = 40;
            let right = 2;
            let selected = apply2(
                &mut left,
                &mut right,
                { first, second => first }
            );
            let conflicting = &mut left;
            selected;
            conflicting;
            ()
        }
        main() -> { () }
    "#;
    let opaque_route = r#"
        enum Flag { Yes, No }
        apply2<F, T, R>(left: T, right: T, body: F) -> R
            where F: Fn<(T, T), Output=R> { body(left, right) }
        choose<'a>(flag: Flag, left: &'a i64, right: &'a i64) -> &'a i64 {
            if(flag is Flag::Yes) { left } else { right }
        }
        bad<'a>(flag: Flag, left: &'a i64, right: &'a i64) -> &'a i64 {
            apply2(left, right, { first, second => choose(flag, first, second) })
        }
        main() -> { () }
    "#;
    for (name, source, needle) in [
        ("higher-order-lifetime-escape.glorious", escaping, "escape"),
        (
            "higher-order-lifetime-alias.glorious",
            aliasing,
            "incompatible live loan",
        ),
        (
            "higher-order-lifetime-opaque-route.glorious",
            opaque_route,
            "exactly one compatible reference",
        ),
    ] {
        for optimization_level in [
            OptimizationLevel::O1,
            OptimizationLevel::O2,
            OptimizationLevel::O3,
        ] {
            let errors = compile_source_to_phases_with_options(
                name,
                source,
                CompileOptions { optimization_level },
            )
            .expect_err("invalid higher-order reference transport compiled");
            assert!(
                errors.iter().any(|error| error.message.contains(needle)),
                "{optimization_level:?}: expected {needle:?}, got {errors:#?}"
            );
        }
    }
}
