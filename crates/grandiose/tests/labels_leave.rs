use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    compiler_mir::{CleanupAction, CleanupEdge},
    lexer, parser, validate,
};
use grandiose_vm::{Artifact, Instruction, Value, Vm, verify};

fn validate_source(source: &str) -> Result<(), Vec<grandiose::diagnostic::Diagnostic>> {
    let tokens = lexer::lex(source).map_err(|error| vec![error])?;
    let (program, parse_errors) = parser::parse_recovering(tokens);
    if !parse_errors.is_empty() {
        return Err(parse_errors);
    }
    validate::validate(&program)
}

fn assert_label_error(source: &str, code: &str, message: &str) {
    let errors = validate_source(source).expect_err("invalid label program validated");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some(code) && error.message.contains(message)
        }),
        "expected {code} containing {message:?}, got {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G0124"))
    );
}

fn has_direct_mir_leave(phases: &grandiose::CompiledPhases) -> bool {
    phases.mir.functions.iter().any(|function| {
        function.blocks.iter().any(|block| {
            matches!(
                block.terminator,
                grandiose::compiler_mir::Terminator::Leave { .. }
            )
        })
    })
}

fn has_direct_bytecode_leave(artifact: &Artifact) -> bool {
    artifact
        .code
        .iter()
        .any(|instruction| matches!(instruction, Instruction::Leave { .. }))
}

#[test]
fn nested_typed_destinations_and_unit_destinations_validate_lexically() {
    validate_source(
        r#"
            answer() -> i64 {
                @outer: i64 {
                    @inner: {
                        @inner();
                        @outer(42)
                    }
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn unified_binders_and_label_calls_compile_through_the_existing_leave_pipeline() {
    let source = r#"
        answer() -> i64 {
            @outer: i64 {
                @outer(42)
            }
        }
        main() -> { () }
    "#;
    validate_source(source).unwrap();
    compile_source_to_bytecode("unified-label-call.glorious", source).unwrap();
}

#[test]
fn named_functions_have_implicit_result_labels() {
    let source = r#"
        answer() -> i64 {
            @answer(42)
        }
        main() -> { () }
    "#;
    validate_source(source).unwrap();
    let artifact = compile_source_to_bytecode("implicit-function-label.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(vm.run(answer, vec![]).unwrap(), Value::I64(42));
}

#[test]
fn recursive_calls_and_implicit_labels_target_the_current_activation() {
    let source = r#"
        answer(recurse: i64) -> i64 {
            if(recurse == 1) { answer(0) } else { @answer(42) }
        }
        run() -> i64 { answer(1) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("recursive-implicit-label.glorious", source).unwrap();
    let run = artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(run, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_label_helpers_are_specialized_to_direct_static_transfers() {
    let source = r#"
        exit<T, L>(value: T, destination: L) -> !
            where L: Label<T> {
            destination(value)
        }
        relay<T, L>(value: T, destination: L) -> !
            where L: Label<T> {
            exit(value, destination)
        }
        answer() -> i64 {
            relay(42, @answer)
        }
        main() -> { () }
    "#;
    validate_source(source).unwrap();
    let phases = compile_source_to_phases_with_options(
        "generic-static-label.glorious",
        source,
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        has_direct_mir_leave(&phases),
        "the transitively inlined generic label call did not become a direct MIR leave"
    );
    assert!(
        has_direct_bytecode_leave(&phases.artifact),
        "the transitively inlined generic label call did not become bytecode LEAVE"
    );
    let artifact = phases.artifact;
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(vm.run(answer, vec![]).unwrap(), Value::I64(42));
}

#[test]
fn labels_cannot_escape_mandatory_control_inlining() {
    let source = r#"
        retain_label<T>(value: T) -> T { value }
        bad() -> {
            @out: {
                retain_label(@out);
                ()
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("escaping-static-label.glorious", source)
        .expect_err("a proof-only label escaped as a runtime value");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("escapes as a value")
                && error.message.contains("no runtime representation")
        }),
        "{errors:#?}"
    );
}

#[test]
fn recursive_label_transport_reports_a_directness_failure() {
    let source = r#"
        relay<L>(destination: L) -> ! where L: Label<i64> {
            relay(destination)
        }
        answer() -> i64 { relay(@answer) }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("recursive-label-inline.glorious", source)
        .expect_err("recursive label transport escaped mandatory control inlining");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("recursive")
                && (error.message.contains("label") || error.message.contains("control"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn effects_can_be_instantiated_with_static_label_brands() {
    let source = r#"
        effect Route<L> where L: Label<i64> { finish(destination: L) -> ! }
        route<L>(destination: L) -> i64 where L: Label<i64> {
            handle perform Route<L>::finish(destination) {
                Route<L>::finish(exit) => exit(42)
            }
        }
        answer() -> i64 { route(@answer) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("label-generic-effect.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn effect_label_bounds_reject_runtime_type_instances() {
    let source = r#"
        effect Route<L> where L: Label<i64> { finish(destination: L) -> ! }
        bad(value: i64) -> i64 {
            handle perform Route<i64>::finish(value) {
                Route<i64>::finish(_) => 42
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("runtime-label-effect.glorious", source)
        .expect_err("a runtime type satisfied an effect Label bound");
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("does not satisfy its static Label payload bound")),
        "{errors:#?}"
    );
}

#[test]
fn effect_operations_can_infer_static_label_generics() {
    let source = r#"
        effect Spawn<T> {
            task<L>(work: T, done: L) -> ! where L: Label<T>
        }
        answer() -> i64 {
            handle perform Spawn<i64>::task(41, @answer) {
                Spawn<i64>::task(work, done) => done(work + 1)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "operation-label-generic.glorious",
        source,
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        has_direct_mir_leave(&phases),
        "the operation-local label payload did not fuse into a direct MIR leave"
    );
    assert!(
        has_direct_bytecode_leave(&phases.artifact),
        "the operation-local label payload did not become bytecode LEAVE"
    );
    let artifact = verify(phases.artifact).unwrap();
    let answer = artifact
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(artifact).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn effect_operation_label_bounds_reject_mismatched_payloads() {
    let source = r#"
        effect Spawn {
            task<L>(done: L) -> ! where L: Label<i64>
        }
        answer() -> Text {
            handle perform Spawn::task(@answer) {
                Spawn::task(done) => done("wrong")
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("operation-label-bound.glorious", source)
        .expect_err("a mismatched operation-local label payload was accepted");
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("does not satisfy its static Label payload bound")),
        "{errors:#?}"
    );
}

#[test]
fn effect_operation_label_parameters_reject_runtime_values() {
    let source = r#"
        effect Spawn {
            task<L>(done: L) -> ! where L: Label<i64>
        }
        bad(value: i64) -> i64 {
            handle perform Spawn::task(value) {
                Spawn::task(_) => 42
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("operation-runtime-label.glorious", source)
        .expect_err("a runtime value was accepted for an operation Label parameter");
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("requires a statically known label argument")),
        "{errors:#?}"
    );
}

#[test]
fn standard_try_propagates_through_the_implicit_function_label() {
    let source = r#"
        fail() -> Result<i64, i64> { Result::Err(7) }
        compute() -> Result<Text, i64> {
            let ignored = try(fail(), @compute);
            Result::Ok("unreachable")
        }
        answer() -> i64 {
            handle compute() {
                Result::Ok(_) => 0,
                Result::Err(error) => error
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "standard-try-label.glorious",
        source,
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        has_direct_mir_leave(&phases),
        "try propagation did not lower to a direct MIR leave"
    );
    assert!(
        has_direct_bytecode_leave(&phases.artifact),
        "try propagation did not lower to bytecode LEAVE"
    );
    let artifact = verify(phases.artifact).unwrap();
    let answer = artifact
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(artifact).run(answer, vec![]).unwrap(),
        Value::I64(7)
    );
}

#[test]
fn primitive_consumes_projected_reference_before_try_leaves() {
    let source = r#"
        struct State { values: Vec<i64> }
        fail() -> Result<(), i64> { Result::Err(7) }
        compute(state: &State) -> Result<usize, i64> {
            let count = Vec::len(&state.values);
            try(fail(), @compute);
            Result::Ok(count)
        }
        answer() -> i64 {
            let state = State { values: Vec::new() };
            handle compute(&state) {
                Result::Ok(_) => 0,
                Result::Err(error) => error
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [OptimizationLevel::O1, OptimizationLevel::O2] {
        let phases = compile_source_to_phases_with_options(
            "primitive-reference-before-try.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(phases.artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(7)
        );
    }
}

#[test]
fn try_joins_reference_free_error_with_reference_bearing_success() {
    let source = r#"
        pass<'a>(
            value: &'a i64,
            state: Result<(), ()>
        ) -> Result<&'a i64, ()> {
            try(move state, @pass);
            Result::Ok(value)
        }
        read_ok() -> i64 {
            let value = 42;
            handle pass(&value, Result::Ok(())) {
                Result::Ok(found) => *found,
                Result::Err(_) => 0
            }
        }
        read_error() -> i64 {
            let value = 42;
            handle pass(&value, Result::Err(())) {
                Result::Ok(_) => 0,
                Result::Err(_) => 7
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "try-reference-variant-join.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            has_direct_mir_leave(&phases),
            "{optimization_level:?}: try did not lower to direct MIR LEAVE"
        );
        let artifact = phases.artifact;
        let verified = verify(artifact.clone()).unwrap();
        for (name, expected) in [("read_ok", 42), ("read_error", 7)] {
            let function = artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap() as u32;
            assert_eq!(
                Vm::new(verified.clone()).run(function, vec![]).unwrap(),
                Value::I64(expected),
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn a_label_captured_by_an_inlined_closure_stays_a_direct_transfer() {
    let source = r#"
        invoke<F>(body: F) -> () where F: Fn<(), Output=()> { body() }
        answer() -> i64 {
            @done: i64 {
                invoke({ => @done(42) });
                0
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "captured-static-label.glorious",
        source,
        CompileOptions::default(),
    )
    .unwrap();
    assert!(
        has_direct_mir_leave(&phases),
        "the inlined closure label call did not become a direct MIR leave"
    );
    assert!(
        has_direct_bytecode_leave(&phases.artifact),
        "the inlined closure label call did not become bytecode LEAVE"
    );
    let artifact = phases.artifact;
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn active_static_label_in_inlined_result_handler_has_valid_cleanup_anchors() {
    let source = r#"
        enum Failure { Rejected }

        checked() -> Result<(), ()> { Result::Err(()) }
        invoke<F>(body: F) -> Result<(), Failure>
        where F: Fn<(), Output=Result<(), Failure>> {
            body()
        }

        outer() -> Result<(), Failure> {
            invoke({ => {
                handle checked() {
                    Result::Err(_) =>
                        @outer(Result::Err(Failure::Rejected)),
                    Result::Ok(_) => ()
                };
                Result::Ok(())
            } })
        }

        main() -> { () }
    "#;
    let artifact =
        compile_source_to_bytecode("handler-clause-static-label.glorious", source).unwrap();
    assert!(
        has_direct_bytecode_leave(&artifact),
        "the inlined Result handler did not preserve its static label transfer"
    );
}

#[test]
fn active_labels_cannot_cross_multishot_capture() {
    let source = r#"
        effect Replay { [2,2] replay() -> i64 }
        bad() -> i64 {
            @out: i64 {
                handle perform Replay::replay() {
                    Replay::replay() with continuation => {
                        let first = resume(continuation, 1);
                        let second = resume(continuation, 2);
                        first + second
                    }
                }
            }
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("label-multishot-reject.glorious", source)
        .expect_err("an active label crossed a multi-shot capture");
    assert!(
        errors
            .iter()
            .any(|error| { error.message.contains("active label targets this frame") }),
        "{errors:#?}"
    );
}

#[test]
fn generative_labeled_blocks_expose_their_brand_only_inside_the_body() {
    validate_source(
        r#"
            answer() -> {
                @scope: {
                    @scope;
                    ()
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn label_binders_can_enclose_ordinary_loop_calls() {
    validate_source(
        r#"
            loop<L>(body: L) -> { () }
            answer() -> {
                @outer: {
                    loop {
                        @outer;
                        ()
                    }
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn unknown_and_out_of_scope_labels_are_rejected() {
    assert_label_error(
        r#"
            answer() -> { @missing }
            main() -> { () }
        "#,
        "G0132",
        "not active",
    );
    assert_label_error(
        r#"
            answer() -> {
                @done: { () };
                @done()
            }
            main() -> { () }
        "#,
        "G0132",
        "no active lexical destination",
    );
}

#[test]
fn shadowing_an_active_label_uses_the_inner_brand_and_warns() {
    let source = r#"
        answer() -> {
            @answer: {
                @answer()
            }
        }
        main() -> { () }
    "#;
    validate_source(source).unwrap();
    let phases = compile_source_to_phases_with_options(
        "shadowed-label.glorious",
        source,
        Default::default(),
    )
    .unwrap();
    assert!(
        phases.diagnostics.iter().any(|diagnostic| {
            diagnostic.severity == grandiose::diagnostic::Severity::Warning
                && diagnostic.message.contains("inner generative label")
        }),
        "{:#?}",
        phases.diagnostics
    );
}

#[test]
fn inferred_binders_grant_unit_destination_evidence() {
    validate_source(
        r#"
            answer() -> {
                @scope: { @scope() }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn obvious_leave_value_mismatches_are_source_diagnostics() {
    assert_label_error(
        r#"
            answer() -> i64 {
                @done: i64 { @done("wrong") }
            }
            main() -> { () }
        "#,
        "G0134",
        "incompatible value",
    );
    assert_label_error(
        r#"
            answer() -> i64 {
                @done: i64 { @done() }
            }
            main() -> { () }
        "#,
        "G0134",
        "incompatible value",
    );
}

#[test]
fn nested_leave_executes_the_outer_typed_destination() {
    let source = r#"
        answer() -> i64 {
            @outer: i64 {
                @inner: i64 {
                    @outer(42)
                }
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("nested-leave.glorious", source).unwrap();
}

#[test]
fn leave_cleans_intervening_linear_owners_without_bypassing_use() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        consume(ticket: Ticket) -> { let Ticket { value: _ } = move ticket; () }
        answer() -> i64 {
            @done: i64 {
                let ticket = Ticket { value: 1 };
                consume(move ticket);
                @done(42)
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-cleanup.glorious", source).unwrap();
}

#[test]
fn reference_result_provenance_crosses_leave_but_cannot_escape_its_referent() {
    let source = r#"
        select<'a>(value: &'a i64) -> &'a i64 {
            @done: &'a i64 { @done(value) }
        }
        answer() -> i64 {
            let value = 42;
            let selected = select(&value);
            *selected
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-reference-result.glorious", source).unwrap();
}

#[test]
fn leave_does_not_bypass_private_deconstruction_authority() {
    let source = r#"
        struct Secret { private value: i64 }
        answer(secret: Secret) -> i64 {
            @done: i64 {
                let Secret { value } = move secret;
                @done(value)
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-private-field.glorious", source).unwrap();
}

#[test]
fn nested_leave_cleans_partial_owners_and_loans_at_all_optimization_levels() {
    let source = r#"
        struct Resource { value: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { left: Resource, right: Resource }
        observe(value: &Resource) -> { () }
        answer() -> i64 {
            @outer: i64 {
                let parcel = Parcel {
                    left: Resource { value: 1 },
                    right: Resource { value: 2 },
                };
                let left = parcel.left;
                let right = &parcel.right;
                observe(right);
                @inner: i64 {
                    let scratch = Resource { value: 3 };
                    @outer(42)
                }
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "nested-leave-cleanup.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            phases.mir.functions.iter().any(|function| {
                function.flow.cleanup_plans.iter().any(|plan| {
                    matches!(plan.edge, CleanupEdge::Leave { .. })
                        && plan.actions.iter().any(|action| {
                            matches!(
                                action,
                                CleanupAction::DestroyResidual {
                                    initialized_fields,
                                    ..
                                } if initialized_fields == &[false, true]
                            )
                        })
                }) || {
                    let partial_owners = function
                        .blocks
                        .iter()
                        .flat_map(|block| &block.statements)
                        .filter_map(|statement| {
                            let grandiose::compiler_mir::InstructionKind::ProjectMove {
                                src, ..
                            } = &statement.kind
                            else {
                                return None;
                            };
                            Some(src.register)
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    function.blocks.iter().any(|block| {
                        let grandiose::compiler_mir::Terminator::Leave { .. } = &block.terminator
                        else {
                            return false;
                        };
                        block.statements.iter().any(|statement| {
                            matches!(
                                &statement.kind,
                                grandiose::compiler_mir::InstructionKind::Drop { owner: dropped }
                                    if partial_owners.contains(&dropped.register)
                            )
                        })
                    })
                }
            }),
            "{optimization_level:?}: nested leave lost exact cleanup\n{}",
            phases.mir.canonical_text()
        );
        let verified = verify(phases.artifact).unwrap();
        let answer = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified).run(answer, vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}
