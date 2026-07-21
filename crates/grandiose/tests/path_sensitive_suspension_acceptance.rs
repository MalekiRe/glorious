use grandiose::compiler_mir::{CleanupAction, Terminator};
use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{Artifact, Instruction, Value, Vm, verify};

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn run_all_levels(source_name: &str, source: &str, expected: Value) {
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
        let bytes = phases.artifact.encode();
        let decoded = Artifact::decode(&bytes).expect("artifact round-trips through the codec");
        assert_eq!(decoded.encode(), bytes, "{optimization_level:?}");
        let selected = function_id(&decoded, "selected");
        assert_eq!(
            Vm::new(verify(decoded).unwrap())
                .run(selected, vec![])
                .unwrap(),
            expected,
            "{optimization_level:?}"
        );
    }
}

fn assert_rejected(source_name: &str, source: &str, needles: &[&str]) {
    let errors = compile_source_to_bytecode(source_name, source)
        .expect_err("the current conservative suspension frontier accepted the program");
    for needle in needles {
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "missing `{needle}` in {errors:#?}"
        );
    }
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G1BC999")),
        "frontier rejection must remain a source diagnostic: {errors:#?}"
    );
}

fn assert_rejected_all_levels(source_name: &str, source: &str, needles: &[&str]) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("the invalid ownership join was accepted");
        for needle in needles {
            assert!(
                errors.iter().any(|error| error.message.contains(needle)),
                "{optimization_level:?}: missing `{needle}` in {errors:#?}"
            );
        }
    }
}

const PURE_DECLARED_ROW: &str = r#"
    struct Ticket { serial: i64 }
    impl Use<[1,1]> for Ticket {}
    effect Maybe { [0,1] ask() -> i64 }
    pure_but_declared(value: i64) -> i64 / {Maybe} { value }
    selected() -> i64 {
        handle {
            let ticket = Ticket { serial: 40 };
            let answer = pure_but_declared(2);
            let Ticket { serial } = move ticket;
            serial + answer
        } {
            Maybe::ask() with continuation => resume(continuation, 0)
        }
    }
    main() -> { () }
"#;

#[test]
fn desired_pure_interprocedural_summary_ignores_an_unperformed_declared_effect() {
    run_all_levels(
        "pure-declared-row-accept.gr",
        PURE_DECLARED_ROW,
        Value::I64(42),
    );
}

const CONDITIONAL_MULTIPLIER: &str = r#"
    struct Bounded { marker: i64 }
    impl Use<[1,2]> for Bounded {}
    enum Route { Once, Twice }
    effect Branch { select(route: Route) -> ! }
    effect Replay { [2,2] replay() -> i64 }
    conditional(route: Route) -> i64 / {Replay} {
        handle perform Branch::select(route) {
            Branch::select(Route::Once) => 1,
            Branch::select(Route::Twice) => perform Replay::replay()
        }
    }
    selected() -> i64 {
        handle {
            let bounded = Bounded { marker: 40 };
            let answer = conditional(Route::Twice);
            let Bounded { marker } = move bounded;
            marker + answer
        } {
            Replay::replay() with continuation => {
                let first = resume(continuation, 1);
                let second = resume(move continuation, 1);
                first + second
            }
        }
    }
    main() -> { () }
"#;

#[test]
fn desired_conditional_normal_multipliers_are_checked_as_a_finite_set() {
    run_all_levels(
        "conditional-multiplier-accept.gr",
        CONDITIONAL_MULTIPLIER,
        Value::I64(82),
    );
}

const OPTIONAL_ALWAYS_RESUMED: &str = r#"
    struct Ticket { serial: i64 }
    impl Use<[1,1]> for Ticket {}
    effect Maybe { [0,1] ask() -> i64 }
    suspend() -> i64 / {Maybe} { perform Maybe::ask() }
    selected() -> i64 {
        handle {
            let ticket = Ticket { serial: 40 };
            let answer = suspend();
            let Ticket { serial } = move ticket;
            serial + answer
        } {
            Maybe::ask() with continuation => resume(continuation, 2)
        }
    }
    main() -> { () }
"#;

#[test]
fn desired_per_owner_cancellation_disposition_accepts_the_always_resumed_path() {
    run_all_levels(
        "optional-always-resumed-accept.gr",
        OPTIONAL_ALWAYS_RESUMED,
        Value::I64(42),
    );
}

#[test]
fn actual_optional_cancellation_still_rejects_a_positive_lower_owner() {
    let source =
        OPTIONAL_ALWAYS_RESUMED.replace("resume(continuation, 2)", "{ cancel(continuation); 42 }");
    assert_rejected(
        "optional-real-cancel-reject.gr",
        &source,
        &[
            "cancellation/abandonment path",
            "outside principal interval [1,1]",
        ],
    );
}

#[test]
fn affine_cancellation_disposition_executes_and_round_trips() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        effect Maybe { [0,1] ask() -> i64 }
        suspend() -> i64 / {Maybe} { perform Maybe::ask() }
        selected() -> i64 {
            handle {
                let resource = Resource { marker: 1 };
                let ignored = suspend();
                resource;
                ignored
            } {
                Maybe::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    run_all_levels("affine-cancel-disposition.gr", source, Value::I64(42));
}

const RESULT_OWNER: &str = r#"
    struct Ticket { serial: i64 }
    impl Use<[1,1]> for Ticket {}
    effect Choose { [2,2] choose() -> i64 }
    make() -> Ticket / {Choose} {
        let serial = perform Choose::choose();
        Ticket { serial: serial }
    }
    selected() -> i64 {
        handle {
            let ticket = make();
            let Ticket { serial } = move ticket;
            serial
        } {
            Choose::choose() with continuation => {
                let first = resume(continuation, 20);
                let second = resume(move continuation, 22);
                first + second
            }
        }
    }
    main() -> { () }
"#;

#[test]
fn each_multishot_result_owner_carries_an_independent_obligation() {
    run_all_levels("result-owner-obligations.gr", RESULT_OWNER, Value::I64(42));
}

#[test]
fn abandoning_an_effectful_restricted_result_remains_a_use_error() {
    let source = RESULT_OWNER.replace(
        "let Ticket { serial } = move ticket;\n            serial",
        "ticket;\n            0",
    );
    assert_rejected(
        "result-owner-abandon-reject.gr",
        &source,
        &["must-move value cannot be discarded"],
    );
}

#[test]
fn mandatory_suspension_preserves_a_partially_moved_residual_owner() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        consume(value: Resource) -> { () }
        effect Ask { [1,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let pair = (Resource { marker: 1 }, 40);
                let resource = pair.0;
                consume(resource);
                let answer = perform Ask::ask();
                pair.1 + answer
            } {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    run_all_levels("mandatory-residual-owner.gr", source, Value::I64(42));
}

#[test]
fn exact_multishot_preserves_and_replays_a_restricted_residual_field() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[0,2]> for Ticket {}
        struct Resource { prefix: i64 }
        impl Use<[0,1]> for Resource {}
        consume(value: Resource) -> { () }
        struct Pair { resource: Resource, ticket: Ticket }
        impl Use<[0,1]> for Pair {}
        effect Choose { [2,2] choose() -> i64 }
        selected() -> i64 {
            handle {
                let pair = Pair { resource: Resource { prefix: 2 }, ticket: Ticket { serial: 40 } };
                let resource = move pair.resource;
                let Resource { prefix } = move resource;
                let answer = perform Choose::choose();
                let ticket = move pair.ticket;
                let Ticket { serial } = move ticket;
                prefix + serial + answer
            } {
                Choose::choose() with continuation => {
                    let first = resume(continuation, 0);
                    let second = resume(move continuation, 0);
                    first + second
                }
            }
        }
        main() -> { () }
    "#;
    run_all_levels(
        "multishot-restricted-residual-owner.gr",
        source,
        Value::I64(84),
    );
}

#[test]
fn cancellation_rejects_a_partially_moved_residual_with_positive_lower_use() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        consume(value: Resource) -> { () }
        effect Maybe { [0,1] ask() -> i64 }
        selected() -> i64 {
            handle {
                let pair = (Resource { marker: 1 }, Ticket { serial: 40 });
                let resource = pair.0;
                consume(resource);
                let answer = perform Maybe::ask();
                let ticket = pair.1;
                let Ticket { serial } = move ticket;
                serial + answer
            } {
                Maybe::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    assert_rejected(
        "optional-positive-residual-reject.gr",
        source,
        &[
            "owner on a cancellation/abandonment path",
            "actual Use count 0, outside principal interval [1,1]",
        ],
    );
}

#[test]
fn conditional_residual_shell_survives_join_and_mandatory_suspension() {
    let source = r#"
        enum Route { Left, Right }
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Parcel { ticket: Ticket, marker: i64 }
        impl Use<[1,1]> for Parcel {}
        consume_ticket(ticket: Ticket) -> i64 {
            let Ticket { serial } = move ticket;
            serial
        }
        effect Ask { [1,1] ask() -> i64 }
        suspend() -> i64 / {Ask} { perform Ask::ask() }
        selected() -> i64 {
            handle {
                let route = Route::Left;
                let parcel = Parcel { ticket: Ticket { serial: 40 }, marker: 40 };
                if(route is Route::Left) {
                    let ticket = parcel.ticket;
                    consume_ticket(move ticket);
                    ()
                } else {
                    let ticket = parcel.ticket;
                    consume_ticket(move ticket);
                    ()
                };
                let answer = suspend();
                let marker = move parcel.marker;
                marker + answer
            } {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    run_all_levels("conditional-residual-suspension.gr", source, Value::I64(42));
}

#[test]
fn conditional_residual_join_rejects_mismatched_paths_and_field_use_quantities() {
    let base = r#"
        enum Route { Left, Right }
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Parcel { ticket: Ticket, marker: i64 }
        impl Use<[1,1]> for Parcel {}
        consume_ticket(ticket: Ticket) -> i64 {
            let Ticket { serial } = move ticket;
            serial
        }
        effect Ask { [1,1] ask() -> i64 }
        suspend() -> i64 / {Ask} { perform Ask::ask() }
        selected() -> i64 {
            handle {
                let route = Route::Left;
                let parcel = Parcel { ticket: Ticket { serial: 40 }, marker: 40 };
                if(route is Route::Left) {
                    let ticket = parcel.ticket;
                    consume_ticket(move ticket);
                    ()
                } else {
                    let ticket = parcel.ticket;
                    consume_ticket(move ticket);
                    ()
                };
                let answer = suspend();
                let marker = move parcel.marker;
                marker + answer
            } {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    let mismatched = base.replacen(
        "let ticket = parcel.ticket;\n                    consume_ticket(move ticket);\n                    ()",
        "parcel.marker;\n                    ()",
        1,
    );
    assert_rejected_all_levels(
        "conditional-residual-mismatch.gr",
        &mismatched,
        &["branches leave different ownership or borrow states"],
    );

    let invalid_field_quantity = base.replacen("consume_ticket(move ticket);", "ticket;", 1);
    assert_rejected_all_levels(
        "conditional-field-quantity.gr",
        &invalid_field_quantity,
        &["must-move value cannot be discarded after a whole-value move"],
    );
}

#[test]
fn one_sided_affine_partial_move_retires_each_branch_before_the_join() {
    let source = r#"
        enum Route { Left, Right }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { resource: Resource, marker: i64 }
        selected() -> i64 {
            let route = Route::Left;
            let parcel = Parcel {
                resource: Resource { marker: 1 },
                marker: 2
            };
            if(route is Route::Left) {
                let resource = parcel.resource;
                resource;
                ()
            } else {
                ()
            };
            42
        }
        main() -> { () }
    "#;
    run_all_levels("one-sided-partial-retirement.gr", source, Value::I64(42));
}

#[test]
fn one_sided_positive_owner_cannot_be_retired_at_the_join() {
    let source = r#"
        enum Route { Left, Right }
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Parcel { ticket: Ticket, marker: i64 }
        impl Use<[1,1]> for Parcel {}
        consume(ticket: Ticket) -> i64 {
            let Ticket { marker } = move ticket;
            marker
        }
        bad(route: Route, parcel: Parcel) -> i64 {
            if(route is Route::Left) {
                let ticket = parcel.ticket;
                consume(move ticket)
            } else {
                0
            }
        }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "one-sided-positive-partial-join.gr",
        source,
        &["branches leave different ownership or borrow states"],
    );
}

#[test]
fn conditional_zero_use_field_is_retired_before_join_and_suspension() {
    let source = r#"
        enum Route { Left, Right }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { resource: Resource, marker: i64 }
        effect Ask { [1,1] ask() -> i64 }
        suspend() -> i64 / {Ask} { perform Ask::ask() }
        selected() -> i64 {
            handle {
                let route = Route::Left;
                let parcel = Parcel {
                    resource: Resource { marker: 7 },
                    marker: 40
                };
                if(route is Route::Left) {
                    let resource = parcel.resource;
                    resource;
                    ()
                } else {
                    ()
                };
                let answer = suspend();
                answer + 40
            } {
                Ask::ask() with continuation => resume(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    run_all_levels(
        "conditional-field-through-suspension.gr",
        source,
        Value::I64(42),
    );
    let phases = compile_source_to_phases_with_options(
        "conditional-field-through-suspension.gr",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .expect("conditional field facts survive optimized MIR");
    assert!(
        phases
            .mir
            .functions
            .iter()
            .flat_map(|function| &function.flow.drop_flags)
            .all(|flag| flag.field != Some(0)),
        "the disposable zero-use residual retires on its branch edge"
    );
    assert!(
        phases
            .mir
            .functions
            .iter()
            .flat_map(|function| &function.flow.cleanup_plans)
            .flat_map(|plan| &plan.actions)
            .all(|action| !matches!(action, CleanupAction::DestroyResidual { .. })),
        "suspension cleanup does not retain an already retired residual"
    );
    assert!(
        phases
            .mir
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .filter_map(|block| match &block.terminator {
                Terminator::Perform { capture, .. } => Some(capture),
                _ => None,
            })
            .all(|capture| capture.captured_residuals.is_empty()),
        "suspension does not capture an already retired residual"
    );
}

#[test]
fn custom_drop_still_forbids_conditional_partial_moves() {
    let source = r#"
        enum Route { Left, Right }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { resource: Resource, marker: i64 }
        impl Drop for Parcel { drop(&mut self) -> { self.marker; () } }
        bad(route: Route, parcel: Parcel) -> () {
            if(route is Route::Left) {
                let resource = parcel.resource;
                resource;
                ()
            } else {
                ()
            }
        }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "conditional-custom-drop-partial-move.gr",
        source,
        &["custom Drop hook"],
    );
}

#[test]
fn distinct_affine_residuals_retire_before_effectful_tail_call() {
    let source = r#"
        enum Route { Left, Right }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { left: Resource, right: Resource }
        impl Use<[1,1]> for Parcel {}
        consume(resource: Resource) -> i64 {
            let Resource { marker } = move resource;
            marker
        }
        effect Ask { [1,1] ask() -> i64 }
        finish(prefix: i64) -> i64 / {Ask} { prefix + perform Ask::ask() }
        selected() -> i64 {
            handle {
                let route = Route::Left;
                let parcel = Parcel {
                    left: Resource { marker: 40 },
                    right: Resource { marker: 40 }
                };
                let prefix = if(route is Route::Left) {
                    let resource = parcel.left;
                    consume(move resource)
                } else {
                    let resource = parcel.right;
                    consume(move resource)
                };
                finish(prefix)
            } {
                Ask::ask() with continuation => tail(continuation, 2)
            }
        }
        main() -> { () }
    "#;
    run_all_levels("distinct-residual-tail-effect.gr", source, Value::I64(42));
    let phases = compile_source_to_phases_with_options(
        "distinct-residual-tail-effect.gr",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailResume { .. }))
    );
}

#[test]
fn distinct_affine_residuals_retire_before_abandoning_effect() {
    let source = r#"
        enum Route { Left, Right }
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { left: Resource, right: Resource }
        impl Use<[1,1]> for Parcel {}
        consume(resource: Resource) -> i64 {
            let Resource { marker } = move resource;
            marker
        }
        effect Maybe { [0,1] ask() -> i64 }
        suspend() -> i64 / {Maybe} { perform Maybe::ask() }
        selected() -> i64 {
            handle {
                let route = Route::Right;
                let parcel = Parcel {
                    left: Resource { marker: 40 },
                    right: Resource { marker: 40 }
                };
                let ignored = if(route is Route::Left) {
                    let resource = parcel.left;
                    consume(move resource)
                } else {
                    let resource = parcel.right;
                    consume(move resource)
                };
                suspend() + ignored
            } {
                Maybe::ask() with continuation => { cancel(continuation); 42 }
            }
        }
        main() -> { () }
    "#;
    run_all_levels(
        "distinct-residual-abandon-effect.gr",
        source,
        Value::I64(42),
    );
}

#[test]
fn distinct_positive_residuals_cannot_be_retired_at_join() {
    let source = r#"
        enum Route { Left, Right }
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Parcel { left: Ticket, right: Ticket }
        impl Use<[1,1]> for Parcel {}
        consume(ticket: Ticket) -> i64 {
            let Ticket { marker } = move ticket;
            marker
        }
        bad(route: Route, parcel: Parcel) -> i64 {
            if(route is Route::Left) {
                let ticket = parcel.left;
                consume(move ticket)
            } else {
                let ticket = parcel.right;
                consume(move ticket)
            }
        }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "distinct-positive-residual-join.gr",
        source,
        &["branches leave different ownership or borrow states"],
    );
}

#[test]
fn refined_enum_payload_reference_survives_mandatory_suspension_all_levels() {
    let source = r#"
        enum Choice { Yes((i64, i64)), No }
        effect Pause { [1,1] pause() -> () }
        inspect(value: Choice) -> i64 / {Pause} {
            if(value is Choice::Yes(_)) {
                let payload = &value.0;
                let answer = &payload.0;
                perform Pause::pause();
                *answer
            } else { 0 }
        }
        selected() -> i64 {
            handle inspect(Choice::Yes((42, 7))) {
                Pause::pause() with continuation => resume(continuation, ())
            }
        }
        main() -> { () }
    "#;
    run_all_levels(
        "refined-enum-reference-suspension.gr",
        source,
        Value::I64(42),
    );
}

#[test]
fn enum_payload_projection_requires_exact_dominating_variant_and_bounds() {
    let without_proof = r#"
        enum Choice { Yes(i64), No }
        bad(value: Choice) -> { let payload = &value.0; () }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "enum-payload-without-proof.gr",
        without_proof,
        &["dominating active-variant proof"],
    );

    let out_of_bounds = r#"
        enum Choice { Yes(i64), No }
        bad(value: Choice) -> {
            if(value is Choice::Yes(_)) {
                let payload = &value.1;
                ()
            } else { () }
        }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "enum-payload-out-of-bounds.gr",
        out_of_bounds,
        &["no payload field `1`"],
    );

    let proof_does_not_cross_join = r#"
        enum Choice { Yes(i64), No }
        bad(value: Choice) -> {
            if(value is Choice::Yes(_)) { () } else { () };
            let payload = &value.0;
            ()
        }
        main() -> { () }
    "#;
    assert_rejected_all_levels(
        "enum-proof-does-not-cross-join.gr",
        proof_does_not_cross_join,
        &["dominating active-variant proof"],
    );
}
