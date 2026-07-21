//! Semantic baselines for the MIR optimizer.
//!
//! These tests compare the mandatory `O0` lowering pipeline with the currently
//! implemented `O1` local simplifier and record observations that later
//! optimization levels must continue to match.

use grandiose::compiler_mir::Terminator as MirTerminator;
use grandiose::{
    CompileOptions, OptimizationLevel, OptimizationPass, OptimizationPassOutcome,
    compile_source_to_phases, compile_source_to_phases_with_options,
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

fn function_id(phases: &grandiose::CompiledPhases, name: &str) -> u32 {
    phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn function_code<'a>(phases: &'a grandiose::CompiledPhases, name: &str) -> &'a [Instruction] {
    let function = &phases.artifact.functions[function_id(phases, name) as usize];
    &phases.artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize]
}

fn run(phases: grandiose::CompiledPhases, name: &str) -> Result<Value, String> {
    let function = function_id(&phases, name);
    Vm::new(verify(phases.artifact).unwrap())
        .run(function, vec![])
        .map_err(|error| error.to_string())
}

fn compile_at(
    source_name: &str,
    source: &str,
    level: OptimizationLevel,
) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        source_name,
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap()
}

fn instruction_count(
    phases: &grandiose::CompiledPhases,
    name: &str,
    predicate: impl Fn(&Instruction) -> bool,
) -> usize {
    function_code(phases, name)
        .iter()
        .filter(|instruction| predicate(instruction))
        .count()
}

const CONTROL_SOURCE: &str = r#"
    effect Ask { [1,1] ask() -> i64 }
    effect Inspect { inspect(value: i64) -> ! }
    deep() -> i64 {
        handle {
            handle {
                let first = perform Ask::ask();
                let second = perform Ask::ask();
                first + second
            } {
                Ask::ask() with inner => resume(inner, 21),
            }
        } {
            Ask::ask() with outer => resume(outer, 100),
        }
    }
    answer() -> i64 {
        handle perform Inspect::inspect(deep()) {
            Inspect::inspect(42) => 42,
            Inspect::inspect(other) => 0,
        }
    }
    main() -> { () }
"#;

#[test]
fn options_default_is_explicit_o0_and_o1_removes_only_cleanup_free_constant_drop() {
    let source = r#"
        answer() -> i64 { let unused = 7; 42 }
        main() -> { () }
    "#;
    let default = compile_source_to_phases("optimizer-options-default.gr", source).unwrap();
    let explicit_o0 = compile_at(
        "optimizer-options-default.gr",
        source,
        OptimizationLevel::O0,
    );
    let o1 = compile_at(
        "optimizer-options-default.gr",
        source,
        OptimizationLevel::O1,
    );

    assert_eq!(default.mir_fingerprint(), explicit_o0.mir_fingerprint());
    assert_eq!(default.artifact.encode(), explicit_o0.artifact.encode());
    assert_eq!(default.optimization_report, explicit_o0.optimization_report);
    assert_eq!(explicit_o0.optimization_report.level, OptimizationLevel::O0);
    assert_eq!(o1.optimization_report.level, OptimizationLevel::O1);
    let backend = explicit_o0
        .optimization_report
        .passes
        .iter()
        .filter(|pass| {
            matches!(
                pass.pass,
                OptimizationPass::LowerRegistersAndEdges
                    | OptimizationPass::LayoutAndPeephole
                    | OptimizationPass::ValidateFinalArtifact
            )
        })
        .collect::<Vec<_>>();
    assert_eq!(
        backend.iter().map(|pass| pass.pass).collect::<Vec<_>>(),
        [
            OptimizationPass::LowerRegistersAndEdges,
            OptimizationPass::LayoutAndPeephole,
            OptimizationPass::ValidateFinalArtifact,
        ]
    );
    assert!(backend.iter().all(|pass| pass.work_units > 0));
    assert_eq!(
        backend.last().unwrap().outcome,
        OptimizationPassOutcome::Unchanged
    );
    assert!(
        o1.optimization_report.passes.iter().any(|pass| {
            pass.pass == OptimizationPass::SparseSimplify
                && matches!(
                    pass.outcome,
                    OptimizationPassOutcome::Changed | OptimizationPassOutcome::Unchanged
                )
        }),
        "O1 report must expose SparseSimplify: {:?}",
        o1.optimization_report
    );
    assert_eq!(
        instruction_count(&o1, "answer", |instruction| matches!(
            instruction,
            Instruction::Const { .. }
        )),
        instruction_count(&explicit_o0, "answer", |instruction| matches!(
            instruction,
            Instruction::Const { .. }
        ))
    );
    assert!(
        !function_code(&o1, "answer")
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Drop { .. }))
    );
    assert!(o1.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SimplifyCleanup
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    assert_eq!(run(explicit_o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o1, "answer").unwrap(), Value::I64(42));
}

#[test]
fn o0_o2_empty_drop_sccp_is_semantically_equal_for_noop_cleanup() {
    let source = r#"
        answer() -> i64 {
            let unused = 7;
            42
        }
        main() -> () { () }
    "#;
    let o0 = compile_at(
        "optimizer-empty-drop-differential.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-empty-drop-differential.gr",
        source,
        OptimizationLevel::O2,
    );

    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SimplifyCleanup
            && matches!(
                pass.outcome,
                OptimizationPassOutcome::Changed | OptimizationPassOutcome::Unchanged
            )
    }));
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o2, "answer").unwrap(), Value::I64(42));
}

#[test]
fn o0_and_o1_are_observationally_equal_across_handlers_and_resumptions() {
    let o0 = compile_at(
        "optimizer-control-differential.gr",
        CONTROL_SOURCE,
        OptimizationLevel::O0,
    );
    let o1 = compile_at(
        "optimizer-control-differential.gr",
        CONTROL_SOURCE,
        OptimizationLevel::O1,
    );

    for instruction in ["perform", "resume"] {
        let count = |phases: &grandiose::CompiledPhases| match instruction {
            "perform" => instruction_count(phases, "deep", |candidate| {
                matches!(candidate, Instruction::Perform { .. })
            }),
            "resume" => phases
                .artifact
                .code
                .iter()
                .filter(|candidate| matches!(candidate, Instruction::Resume { .. }))
                .count(),
            _ => unreachable!(),
        };
        assert_eq!(count(&o0), count(&o1), "O1 changed the {instruction} trace");
    }
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert!(o1.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SimplifyCleanup
            && matches!(
                pass.outcome,
                OptimizationPassOutcome::Changed | OptimizationPassOutcome::Unchanged
            )
    }));
    assert_eq!(run(o1, "answer").unwrap(), Value::I64(42));
}

#[test]
fn o2_statically_selects_the_exact_terminal_clause_in_source_order() {
    let source = r#"
        effect Exit {
            first() -> !
            second(value: i64) -> !
        }
        answer() -> i64 {
            handle perform Exit::second(42) {
                Exit::first() => 1,
                Exit::second(value) => value,
            }
        }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-static-terminal.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-static-terminal.gr",
        source,
        OptimizationLevel::O2,
    );
    let repeated = compile_at(
        "optimizer-static-terminal.gr",
        source,
        OptimizationLevel::O2,
    );
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o2.clone(), "answer").unwrap(), Value::I64(42));
    assert_eq!(
        instruction_count(&o2, "answer", |instruction| matches!(
            instruction,
            Instruction::Handle { .. }
        )),
        0
    );
    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SpecializeControl
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    assert_eq!(o2.optimization_report, repeated.optimization_report);
    assert_eq!(o2.artifact.encode(), repeated.artifact.encode());
}

#[test]
fn o2_terminal_specialization_preserves_partial_fallback_to_the_outer_handler() {
    let source = r#"
        effect Inspect { inspect(value: i64) -> ! }
        answer() -> i64 {
            handle {
                handle perform Inspect::inspect(2) {
                    Inspect::inspect(1) => 1,
                }
            } {
                Inspect::inspect(value) => value + 40,
            }
        }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-partial-terminal.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-partial-terminal.gr",
        source,
        OptimizationLevel::O2,
    );
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o2.clone(), "answer").unwrap(), Value::I64(42));
    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SpecializeControl
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
}

#[test]
fn o2_statically_composes_canonical_one_shot_resume_and_cancel() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        resumed() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => resume(k, 42),
            }
        }
        cancelled() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => { cancel(k); 7 },
            }
        }
        main() -> { () }
    "#;
    for function in ["resumed", "cancelled"] {
        let o0 = compile_at(
            "optimizer-one-shot-barrier.gr",
            source,
            OptimizationLevel::O0,
        );
        let o2 = compile_at(
            "optimizer-one-shot-barrier.gr",
            source,
            OptimizationLevel::O2,
        );
        assert_eq!(
            run(o0, function).unwrap(),
            run(o2.clone(), function).unwrap()
        );
        assert!(
            function_code(&o2, function)
                .iter()
                .all(|instruction| !matches!(
                    instruction,
                    Instruction::MakeHandler { .. }
                        | Instruction::Handle { .. }
                        | Instruction::Perform { .. }
                        | Instruction::Resume { .. }
                        | Instruction::Cancel { .. }
                ))
        );
    }
}

#[test]
fn o2_control_specialization_keeps_custom_drop_before_terminal_clause() {
    let source = r#"
        effect Stop { stop() -> ! }
        struct Guard { marker: i64 }
        impl Use<[0,1]> for Guard {}
        impl Drop for Guard { drop(&mut self) -> { 1 / 0; () } }
        guarded() -> i64 {
            handle {
                let guard = Guard { marker: 0 };
                perform Stop::stop()
            } {
                Stop::stop() => 42,
            }
        }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-control-drop-barrier.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-control-drop-barrier.gr",
        source,
        OptimizationLevel::O2,
    );
    let o0_error = run(o0, "guarded").unwrap_err();
    let o2_error = run(o2.clone(), "guarded").unwrap_err();
    assert_eq!(o0_error, o2_error);
    assert!(o2_error.contains("division by zero"), "{o2_error}");
    assert!(
        function_code(&o2, "guarded")
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Handle { .. }))
    );
}

#[test]
fn o0_and_o1_preserve_dead_traps_and_custom_drop_barriers() {
    let source = r#"
        struct Guard { marker: i64 }
        impl Use<[0,1]> for Guard {}
        impl Drop for Guard { drop(&mut self) -> { 1 / 0; () } }
        leaf() -> i64 { 42 }
        dead_trap() -> i64 { 1 / 0; 42 }
        guarded() -> i64 {
            let guard = Guard { marker: 0 };
            leaf()
        }
        main() -> { () }
    "#;

    for function in ["dead_trap", "guarded"] {
        let o0 = compile_at(
            "optimizer-barrier-differential.gr",
            source,
            OptimizationLevel::O0,
        );
        let o1 = compile_at(
            "optimizer-barrier-differential.gr",
            source,
            OptimizationLevel::O1,
        );
        let o0_error = run(o0, function).unwrap_err();
        let o1_error = run(o1, function).unwrap_err();
        assert_eq!(o0_error, o1_error);
        assert!(o1_error.contains("division by zero"), "{o1_error}");
    }

    let o1 = compile_at("optimizer-barrier-shape.gr", source, OptimizationLevel::O1);
    let guarded = function_code(&o1, "guarded");
    assert!(
        guarded
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Drop { .. }))
    );
    assert!(
        !guarded
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
    );
    assert!(function_code(&o1, "dead_trap").iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::IntCheckedDiv,
                ..
            }
        )
    }));
    assert!(o1.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::SimplifyCleanup
            && matches!(
                pass.outcome,
                OptimizationPassOutcome::Changed | OptimizationPassOutcome::Unchanged
            )
    }));
}

#[test]
fn o0_and_o1_preserve_must_move_deconstruction_and_rejection() {
    let valid = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        answer() -> i64 {
            let ticket = Ticket { value: 42 };
            let Ticket { value } = ticket;
            value
        }
        main() -> { () }
    "#;
    let o0 = compile_at("optimizer-must-move.gr", valid, OptimizationLevel::O0);
    let o1 = compile_at("optimizer-must-move.gr", valid, OptimizationLevel::O1);
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o1, "answer").unwrap(), Value::I64(42));

    let invalid = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        abandon(ticket: Ticket) -> { () }
        main() -> { () }
    "#;
    let compile = |level| {
        compile_source_to_phases_with_options(
            "optimizer-must-move-reject.gr",
            invalid,
            CompileOptions {
                optimization_level: level,
            },
        )
        .expect_err("optimization must not make abandonment of a must-move owner legal")
    };
    let o0_errors = compile(OptimizationLevel::O0);
    let o1_errors = compile(OptimizationLevel::O1);
    assert_eq!(format!("{o0_errors:?}"), format!("{o1_errors:?}"));
    assert!(!o1_errors.is_empty());
}

#[test]
fn o1_reports_fingerprints_and_artifacts_deterministically() {
    let first = compile_at(
        "optimizer-o1-determinism.gr",
        CONTROL_SOURCE,
        OptimizationLevel::O1,
    );
    let second = compile_at(
        "optimizer-o1-determinism.gr",
        CONTROL_SOURCE,
        OptimizationLevel::O1,
    );

    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.optimization_report, second.optimization_report);
    assert_eq!(first.artifact.encode(), second.artifact.encode());
}

#[test]
fn dead_trapping_primitive_remains_observable_at_its_source_position() {
    let phases = compile_source_to_phases(
        "optimizer-dead-trap.gr",
        r#"
            answer() -> i64 { 1 / 0; 42 }
            main() -> { () }
        "#,
    )
    .unwrap();

    assert!(function_code(&phases, "answer").iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::IntCheckedDiv,
                ..
            }
        )
    }));
    let error = run(phases, "answer").unwrap_err();
    assert!(error.contains("division by zero"), "{error}");
}

#[test]
fn constant_folding_must_preserve_checked_overflow_as_a_trap() {
    let phases = compile_source_to_phases(
        "optimizer-overflow.gr",
        r#"
            answer() -> i64 { 9223372036854775807 + 1 }
            main() -> { () }
        "#,
    )
    .unwrap();

    assert!(function_code(&phases, "answer").iter().any(|instruction| {
        matches!(
            instruction,
            Instruction::Primitive {
                op: Primitive::IntCheckedAdd,
                ..
            }
        )
    }));
    let error = run(phases, "answer").unwrap_err();
    assert!(error.contains("checked arithmetic overflow"), "{error}");
}

#[test]
fn custom_drop_is_a_tail_formation_barrier_and_still_runs() {
    let phases = compile_source_to_phases(
        "optimizer-drop-barrier.gr",
        r#"
            struct Guard { marker: i64 }
            impl Use<[0,1]> for Guard {}
            impl Drop for Guard { drop(&mut self) -> { 1 / 0; () } }
            leaf() -> i64 { 42 }
            guarded() -> i64 {
                let guard = Guard { marker: 0 };
                leaf()
            }
            main() -> { () }
        "#,
    )
    .unwrap();

    let guarded = function_code(&phases, "guarded");
    assert!(
        guarded
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }))
    );
    assert!(
        guarded
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Drop { .. }))
    );
    assert!(
        !guarded
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
    );
    let error = run(phases, "guarded").unwrap_err();
    assert!(error.contains("division by zero"), "{error}");
}

#[test]
fn o2_tail_discovery_does_not_move_custom_drop_before_a_callee_trap() {
    let source = r#"
        struct Guard { marker: i64 }
        impl Use<[0,1]> for Guard {}
        impl Drop for Guard { drop(&mut self) -> { 1 / 0; () } }
        overflow() -> i64 { 9223372036854775807 + 1 }
        explode() -> i64 { overflow() }
        guarded() -> i64 {
            let guard = Guard { marker: 0 };
            let answer = explode();
            answer
        }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-tail-drop-order-o0.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-tail-drop-order-o2.gr",
        source,
        OptimizationLevel::O2,
    );
    let o2_code = function_code(&o2, "guarded");
    assert!(
        o2_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Call { .. }))
    );
    assert!(
        !o2_code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
    );
    let o0_error = run(o0, "guarded").unwrap_err();
    let o2_error = run(o2, "guarded").unwrap_err();
    assert_eq!(o0_error, o2_error);
    assert!(
        o2_error.contains("checked arithmetic overflow"),
        "{o2_error}"
    );
}

#[test]
fn constant_handler_branch_keeps_clause_choice_and_resumption_identity() {
    let first = compile_source_to_phases("optimizer-handler-identity.gr", CONTROL_SOURCE).unwrap();
    let second = compile_source_to_phases("optimizer-handler-identity.gr", CONTROL_SOURCE).unwrap();

    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    assert!(
        first
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Switch { .. })),
        "the mandatory baseline must expose the handler-pattern branch to the optimizer"
    );
    assert!(
        first
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Perform { .. }))
    );
    assert!(
        first
            .artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Resume { .. }))
    );
    assert_eq!(run(first, "answer").unwrap(), Value::I64(42));
}

#[test]
fn self_tail_recursion_has_a_bounded_frame_replacement_baseline() {
    let phases = compile_source_to_phases(
        "optimizer-self-tail.gr",
        r#"
            forever() -> ! { forever() }
            main() -> { () }
        "#,
    )
    .unwrap();

    let code = function_code(&phases, "forever");
    assert!(
        matches!(code.last(), Some(Instruction::TailCall { function, .. }) if *function == function_id(&phases, "forever"))
    );
    assert!(!code.iter().any(|instruction| matches!(
        instruction,
        Instruction::Call { .. } | Instruction::Return { .. }
    )));
}

#[test]
fn o2_forms_in_frame_self_backedges_and_keeps_nonself_tail_calls() {
    let source = r#"
        forever() -> ! { forever() }
        tail_swap(left: i64, right: i64) -> ! { tail_swap(right, left) }
        leaf() -> i64 { 42 }
        relay() -> i64 { leaf() }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-self-backedge-o0.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-self-backedge-o2.gr",
        source,
        OptimizationLevel::O2,
    );

    assert!(
        function_code(&o0, "forever")
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
    );
    for function in ["forever", "tail_swap"] {
        let code = function_code(&o2, function);
        assert!(
            code.iter()
                .any(|instruction| matches!(instruction, Instruction::Jump { target: 0 })),
            "{function} must loop inside its existing VM frame: {code:?}"
        );
        assert!(!code.iter().any(|instruction| matches!(
            instruction,
            Instruction::Call { .. } | Instruction::TailCall { .. } | Instruction::Return { .. }
        )));
    }
    let swap = function_code(&o2, "tail_swap");
    assert_eq!(
        swap.iter()
            .filter(|instruction| matches!(instruction, Instruction::Move { .. }))
            .count(),
        4,
        "the parameter swap must snapshot both inputs before assigning either one"
    );
    assert!(
        function_code(&o2, "relay")
            .iter()
            .any(|instruction| matches!(instruction, Instruction::TailCall { .. }))
    );
    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::FormTailCallsAndHoist
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    assert_eq!(run(o0, "relay").unwrap(), Value::I64(42));
    assert_eq!(run(o2, "relay").unwrap(), Value::I64(42));
}

#[test]
fn o2_records_exact_closure_targets_without_erasing_indirect_receiver_semantics() {
    let source =
        "run()->i64 { let captured = 42; let answer = { => captured }; answer() } main()->{()}";
    let o0 = compile_at(
        "optimizer-exact-closure-o0.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-exact-closure-o2.gr",
        source,
        OptimizationLevel::O2,
    );

    let known_targets = |phases: &grandiose::CompiledPhases| {
        phases
            .mir
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .filter_map(|block| match &block.terminator {
                MirTerminator::CallIndirect { known_function, .. }
                | MirTerminator::TailCallIndirect { known_function, .. } => Some(*known_function),
                _ => None,
            })
            .collect::<Vec<_>>()
    };
    assert!(known_targets(&o0).iter().all(Option::is_none));
    assert!(known_targets(&o2).iter().any(Option::is_some));
    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::GlobalSimplify
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    assert!(
        function_code(&o2, "run")
            .iter()
            .any(|instruction| matches!(instruction, Instruction::CallIndirect { .. }))
    );
    // O2's post-emission layout pass may erase fallthrough jumps, so byte-for-
    // byte equality with O0 is no longer the right receiver-semantics oracle.
    // The indirect call remains, and every removed jump is independently
    // covered by verifier/execution and the bytecode peephole tests.
    assert!(function_code(&o2, "run").len() <= function_code(&o0, "run").len());
    assert!(
        function_code(&o2, "run")
            .iter()
            .enumerate()
            .all(|(pc, instruction)| !matches!(
                instruction,
                Instruction::Jump { target } if *target == pc as u32 + 1
            ))
    );
    assert_eq!(run(o0, "run").unwrap(), Value::I64(42));
    assert_eq!(run(o2, "run").unwrap(), Value::I64(42));
}

#[test]
fn o0_and_o1_tuple_scalarization_are_observationally_equal() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        answer() -> i64 {
            let pair = (40, 2);
            let (left, right) = pair;
            left + right
        }
        struct_answer() -> i64 {
            let pair = Pair { left: 20, right: 22 };
            let Pair { left, right } = pair;
            left + right
        }
        main() -> { () }
    "#;
    let o0 = compile_at("optimizer-scalarize-o0.gr", source, OptimizationLevel::O0);
    let o1 = compile_at("optimizer-scalarize-o1.gr", source, OptimizationLevel::O1);

    for function in ["answer", "struct_answer"] {
        assert!(function_code(&o0, function).iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::Construct { .. }
                    | Instruction::ProjectMove { .. }
                    | Instruction::Deconstruct { .. }
            )
        }));
        assert!(!function_code(&o1, function).iter().any(|instruction| {
            matches!(
                instruction,
                Instruction::Construct { .. }
                    | Instruction::ProjectCopy { .. }
                    | Instruction::ProjectMove { .. }
                    | Instruction::Deconstruct { .. }
            )
        }));
    }
    assert!(o1.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::ScalarizeLocals
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    assert_eq!(run(o0, "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o1, "answer").unwrap(), Value::I64(42));

    let o0 = compile_at(
        "optimizer-scalarize-struct-o0.gr",
        source,
        OptimizationLevel::O0,
    );
    let o1 = compile_at(
        "optimizer-scalarize-struct-o1.gr",
        source,
        OptimizationLevel::O1,
    );
    assert_eq!(run(o0, "struct_answer").unwrap(), Value::I64(42));
    assert_eq!(run(o1, "struct_answer").unwrap(), Value::I64(42));
}

#[test]
fn o2_scalarizes_an_immediate_owned_closure_call_observationally() {
    let source = r#"
        struct Ticket { marker: i64 }
        impl Use<[1,1]> for Ticket {}
        answer() -> i64 {
            let ticket = Ticket { marker: 40 };
            let add = { => {
                let Ticket { marker } = move ticket;
                marker + 2
            } };
            move add()
        }
        trap() -> i64 {
            let ticket = Ticket { marker: 42 };
            let divide = { => {
                let Ticket { marker } = move ticket;
                marker / 0
            } };
            move divide()
        }
        effect Stop { stop(value: i64) -> ! }
        invoke_effect() -> i64 / {Stop} {
            let ticket = Ticket { marker: 40 };
            let emit_after_capture = { => {
                let Ticket { marker } = move ticket;
                perform Stop::stop(marker + 2)
            } };
            move emit_after_capture()
        }
        effect_answer() -> i64 {
            handle invoke_effect() {
                Stop::stop(value) => value,
            }
        }
        main() -> { () }
    "#;
    let o0 = compile_at(
        "optimizer-owned-callable-o0.gr",
        source,
        OptimizationLevel::O0,
    );
    let o2 = compile_at(
        "optimizer-owned-callable-o2.gr",
        source,
        OptimizationLevel::O2,
    );

    assert_eq!(run(o0.clone(), "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o2.clone(), "answer").unwrap(), Value::I64(42));
    assert_eq!(run(o0, "effect_answer").unwrap(), Value::I64(42));
    assert_eq!(run(o2.clone(), "effect_answer").unwrap(), Value::I64(42));
    let o0_trap = run(
        compile_at(
            "optimizer-owned-callable-trap-o0.gr",
            source,
            OptimizationLevel::O0,
        ),
        "trap",
    )
    .unwrap_err();
    let o2_trap = run(o2.clone(), "trap").unwrap_err();
    assert_eq!(o0_trap, o2_trap);

    for name in ["answer", "trap", "invoke_effect"] {
        let mir = o2
            .mir
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap();
        assert!(mir.blocks.iter().all(|block| {
            block.statements.iter().all(|statement| {
                !matches!(
                    statement.kind,
                    grandiose::compiler_mir::InstructionKind::MakeCallable { .. }
                )
            }) && !matches!(block.terminator, MirTerminator::CallIndirect { .. })
        }));
    }
    assert!(o2.mir.functions.iter().any(|function| {
        function.name.starts_with("$scalarized$")
            && function.receiver_mode.is_none()
            && function.params.len() == 1
    }));
    assert!(o2.optimization_report.passes.iter().any(|pass| {
        pass.pass == OptimizationPass::ScalarizeCallables
            && pass.outcome == OptimizationPassOutcome::Changed
    }));
    verify(o2.artifact).unwrap();
}
