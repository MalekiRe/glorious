//! End-to-end coverage for the normative ownership-aware MIR: the
//! `ImportAndValidatePlaceFlow` and `ElaborateCleanup` phases, the elaborated
//! cleanup plans, and the behavioral identity of ownership-heavy programs at
//! every optimization level.

use grandiose::compiler_mir::{
    CleanupAction, CleanupEdge, FlowProvenance, OptimizationLevel, OptimizationPass,
    OptimizationPassOutcome,
};
use grandiose::{CompileOptions, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 4] = [
    OptimizationLevel::O0,
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn phases_at(source: &str, level: OptimizationLevel) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        "ownership-mir.glorious",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"))
}

fn run_main(phases: &grandiose::CompiledPhases) -> Value {
    let verified = verify(phases.artifact.clone()).expect("emitted artifact verifies");
    let entry = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .expect("test program exports `run`") as u32;
    Vm::new(verified).run(entry, vec![]).expect("execution")
}

#[test]
fn place_flow_and_cleanup_phases_run_for_real_and_report_work() {
    let source = r#"
        run() -> i64 { 42 }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        for pass in [
            OptimizationPass::ImportAndValidatePlaceFlow,
            OptimizationPass::ElaborateCleanup,
        ] {
            let entry = phases
                .optimization_report
                .passes
                .iter()
                .find(|entry| entry.pass == pass)
                .expect("mandatory phase appears in the report");
            assert_ne!(
                entry.outcome,
                OptimizationPassOutcome::SkippedUnavailable,
                "{pass:?} must be real at {level:?}"
            );
            assert!(entry.work_units > 0);
        }
    }
}

#[test]
fn frontend_exports_place_flow_facts_and_return_edges_carry_plans() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        consume(pair: Pair) -> i64 { let Pair { left, right } = pair; left + right }
        run() -> i64 { consume(Pair { left: 40, right: 2 }) }
        main() -> { () }
    "#;
    let phases = phases_at(source, OptimizationLevel::O0);
    let consume = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "consume")
        .expect("consume was compiled");
    assert_eq!(consume.flow.provenance, FlowProvenance::Exported);
    assert!(!consume.flow.locals.is_empty());
    let run = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "run")
        .expect("run was compiled");
    // Every returning block carries an elaborated cleanup plan.
    for block in &run.blocks {
        if matches!(
            block.terminator,
            grandiose::compiler_mir::Terminator::Return { .. }
        ) {
            assert!(
                run.flow
                    .plan_for(&CleanupEdge::Return { block: block.id })
                    .is_some(),
                "return block {} lacks a cleanup plan",
                block.id
            );
        }
    }
    assert_eq!(run_main(&phases), Value::I64(42));
}

#[test]
fn terminal_perform_frame_abandonment_records_cleanup_plans() {
    let source = r#"
        effect Bail { fail() -> ! }
        struct Wrapper { value: i64 }
        risky() -> i64 / {Bail} {
            let held = Wrapper { value: 5 };
            perform Bail::fail()
        }
        run() -> i64 {
            handle { risky() } { Bail::fail() => 17 }
        }
        main() -> { () }
    "#;
    let phases = phases_at(source, OptimizationLevel::O0);
    let risky = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "risky")
        .expect("risky was compiled");
    let site = risky
        .flow
        .performs
        .iter()
        .find(|site| !site.resumptive)
        .expect("terminal perform site exported");
    let frame = site
        .frame_cleanup
        .expect("terminal perform carries its frame cleanup plan");
    let plan = &risky.flow.cleanup_plans[frame.index()];
    assert_eq!(
        plan.edge,
        CleanupEdge::TerminalPerform { block: site.block }
    );
    assert!(
        plan.actions
            .iter()
            .any(|action| matches!(action, CleanupAction::Destroy(_))),
        "abandoned frame destroys its held owner: {plan:?}"
    );
    assert_eq!(run_main(&phases), Value::I64(17));
}

#[test]
fn effectful_capture_and_resumption_behave_identically_at_o0_through_o3() {
    let source = r#"
        effect Ask { [0,1] ask(hint: i64) -> i64 }
        struct Basket { first: i64, second: i64 }
        gather() -> i64 / {Ask} {
            let basket = Basket { first: 3, second: 4 };
            let bonus = perform Ask::ask(basket.first);
            let Basket { first, second } = basket;
            first + second + bonus
        }
        run() -> i64 {
            handle { gather() } {
                Ask::ask(hint) with k => resume(k, hint * 10)
            }
        }
        main() -> { () }
    "#;
    let mut outputs = Vec::new();
    for level in LEVELS {
        let phases = phases_at(source, level);
        outputs.push(run_main(&phases));
    }
    for output in &outputs {
        assert_eq!(output, &Value::I64(37), "{outputs:?}");
    }
}

#[test]
fn abandoning_a_zero_or_one_shot_continuation_cancels_it_identically_at_all_levels() {
    let source = r#"
        effect Ask { [0,1] ask() -> i64 }
        chatter() -> i64 / {Ask} {
            let bonus = perform Ask::ask();
            bonus + 1
        }
        run() -> i64 {
            handle { chatter() } {
                Ask::ask() with k => 99
            }
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_main(&phases), Value::I64(99), "{level:?}");
    }
}

#[test]
fn moves_partial_moves_and_reinitialization_execute_identically_at_all_levels() {
    let source = r#"
        struct Inner { number: i64 }
        struct Outer { inner: Inner, tag: i64 }
        rebuild(outer: Outer) -> Outer {
            let Outer { inner, tag } = outer;
            let Inner { number } = inner;
            Outer { inner: Inner { number: number + 1 }, tag: tag * 2 }
        }
        run() -> i64 {
            let outer = Outer { inner: Inner { number: 20 }, tag: 3 };
            let rebuilt = rebuild(outer);
            let Outer { inner, tag } = rebuilt;
            let Inner { number } = inner;
            number + tag
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_main(&phases), Value::I64(27), "{level:?}");
    }
}

#[test]
fn borrows_and_loan_expiry_execute_identically_at_all_levels() {
    let source = r#"
        read(value: &i64) -> i64 { *value }
        bump(value: &mut i64) -> () { *value = *value + 1; () }
        run() -> i64 {
            let value = 10;
            let first = read(&value);
            bump(&mut value);
            let second = read(&value);
            first + second
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_main(&phases), Value::I64(21), "{level:?}");
    }
}

#[test]
fn nested_unique_projection_loans_end_as_one_path_at_all_levels() {
    let source = r#"
        struct Cell { value: i64 }
        struct Pair { left: Cell, right: Cell }
        struct Envelope { pair: Pair, tag: i64 }
        bump(value: &mut i64) -> () { *value = *value + 1; () }
        run() -> i64 {
            let envelope = Envelope {
                pair: Pair { left: Cell { value: 19 }, right: Cell { value: 20 } },
                tag: 1
            };
            bump(&mut envelope.pair.left.value);
            bump(&mut envelope.pair.right.value);
            envelope.pair.left.value + envelope.pair.right.value + envelope.tag
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_main(&phases), Value::I64(42), "{level:?}");
        let run = phases
            .mir
            .functions
            .iter()
            .find(|function| function.name == "run")
            .expect("run was compiled");
        assert!(
            run.flow
                .loans
                .iter()
                .any(|loan| loan.borrowed.projection.len() == 3),
            "nested final-place loan was not exported at {level:?}: {:?}",
            run.flow.loans
        );
    }
}

#[test]
fn copied_shared_reference_reborrow_retains_the_original_loan() {
    let source = r#"
        run() -> i64 {
            let value = 21;
            let reference = &value;
            let alias = reference;
            let child = &*alias;
            let left = *child;
            let right = *reference;
            left + right
        }
        main() -> { () }
    "#;
    let phases = phases_at(source, OptimizationLevel::O0);
    assert_eq!(run_main(&phases), Value::I64(42));
    let run = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "run")
        .expect("run was compiled");
    let (child, parent) = run
        .flow
        .loans
        .iter()
        .find_map(|child| {
            let parent = child.parent?;
            Some((child, &run.flow.loans[parent.index()]))
        })
        .expect("the copied shared reference should be reborrowed");
    assert_eq!(
        child.borrowed, parent.borrowed,
        "a shared-reference Copy aliases the same loan rather than borrowing the copy register"
    );
}

#[test]
fn repeated_compilation_is_deterministic_including_flow_facts() {
    let source = r#"
        effect Pick { [1,1] pick() -> i64 }
        struct Node { value: i64 }
        walk() -> i64 / {Pick} {
            let node = Node { value: 6 };
            let extra = perform Pick::pick();
            let Node { value } = node;
            value + extra
        }
        run() -> i64 {
            handle { walk() } { Pick::pick() with k => resume(k, 7) }
        }
        main() -> { () }
    "#;
    for level in [OptimizationLevel::O0, OptimizationLevel::O2] {
        let first = phases_at(source, level);
        let second = phases_at(source, level);
        assert_eq!(first.mir.canonical_text(), second.mir.canonical_text());
        assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
        assert_eq!(run_main(&first), Value::I64(13));
    }
}
