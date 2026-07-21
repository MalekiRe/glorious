use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 4] = [
    OptimizationLevel::O0,
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn compile(source: &str, level: OptimizationLevel) -> Result<grandiose_vm::Artifact, Vec<String>> {
    compile_source_to_phases_with_options(
        "resumption-quantity-breadth.gr",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .map(|phases| phases.artifact)
    .map_err(|diagnostics| {
        diagnostics
            .into_iter()
            .map(|diagnostic| diagnostic.message)
            .collect()
    })
}

fn run_answer(source: &str, level: OptimizationLevel) -> Value {
    let artifact = compile(source, level).unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .expect("answer function") as u32;
    Vm::new(verify(artifact).unwrap())
        .run(answer, vec![])
        .unwrap()
}

#[test]
fn finite_bounded_resumptions_accept_every_proven_count_in_the_interval_o0_o3() {
    let once = r#"
        effect Choice { [0,2] choose() -> i64 }
        answer() -> i64 {
            handle perform Choice::choose() {
                Choice::choose() with continuation => resume(move continuation, 42)
            }
        }
        main() -> () { () }
    "#;
    let twice = r#"
        effect Choice { [1,2] choose() -> i64 }
        answer() -> i64 {
            handle perform Choice::choose() {
                Choice::choose() with continuation => {
                    let first = resume(continuation, 20);
                    let second = resume(move continuation, 22);
                    first + second
                }
            }
        }
        main() -> () { () }
    "#;
    for level in LEVELS {
        assert_eq!(run_answer(once, level), Value::I64(42), "{level:?}");
        assert_eq!(run_answer(twice, level), Value::I64(42), "{level:?}");
    }
}

#[test]
fn late_recursive_generic_resumption_environment_carries_a_reference_o0_o3() {
    let source = r#"
        enum Step { Done, More }
        effect Choice { [1,1] choose() -> i64 }
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let base = 40;
            let borrowed = &base;
            handle perform Choice::choose() {
                Choice::choose() with continuation => {
                    let finish = (step: Step) -> i64 {
                        if(step is Step::Done) {
                            resume(move continuation, *borrowed + 2)
                        } else {
                            finish(Step::Done)
                        }
                    };
                    let escaped = retain(move finish);
                    move escaped(Step::More)
                }
            }
        }
        main() -> () { () }
    "#;
    for level in LEVELS {
        assert_eq!(run_answer(source, level), Value::I64(42), "{level:?}");
    }
}

#[test]
fn recursive_unique_receivers_cannot_abandon_or_reuse_an_owned_resumption_o0_o3() {
    let abandoned = r#"
        enum Step { Done, More }
        effect Choice { [1,1] choose() -> i64 }
        answer() -> i64 {
            handle perform Choice::choose() {
                Choice::choose() with continuation => {
                    let finish = (step: Step) -> i64 {
                        if(step is Step::Done) { 42 } else { finish(Step::Done) }
                    };
                    move finish(Step::More)
                }
            }
        }
        main() -> () { () }
    "#;
    let reused_after_recursive_return = r#"
        enum Step { Done, More }
        effect Choice { [1,1] choose() -> i64 }
        answer() -> i64 {
            handle perform Choice::choose() {
                Choice::choose() with continuation => {
                    let finish = (step: Step) -> i64 {
                        if(step is Step::Done) {
                            resume(move continuation, 40)
                        } else {
                            let inner = finish(Step::Done);
                            resume(move continuation, inner + 2)
                        }
                    };
                    move finish(Step::More)
                }
            }
        }
        main() -> () { () }
    "#;
    for level in LEVELS {
        assert!(
            compile(abandoned, level).is_err(),
            "{level:?}: recursive receiver abandoned an exact resumption"
        );
        assert!(
            compile(reused_after_recursive_return, level).is_err(),
            "{level:?}: parent frame reused a resumption consumed by its recursive child"
        );
    }
}

#[test]
fn finite_bounds_fail_closed_outside_the_interval_and_unbounded_is_explicitly_deferred() {
    let cases = [
        (
            "too-few",
            r#"
                effect Choice { [2,3] choose() -> i64 }
                answer() -> i64 { handle perform Choice::choose() {
                    Choice::choose() with k => resume(k, 42)
                } }
                main() -> () { () }
            "#,
            "at least 2 time(s)",
        ),
        (
            "too-many",
            r#"
                effect Choice { [1,2] choose() -> i64 }
                answer() -> i64 { handle perform Choice::choose() {
                    Choice::choose() with k => {
                        resume(k, 10); resume(k, 11); resume(move k, 21)
                    }
                } }
                main() -> () { () }
            "#,
            "more than 2 time(s)",
        ),
        (
            "unbounded-runtime-representation",
            "effect Choice { [1,infinity] choose() -> i64 } main() -> () { () }",
            "arbitrary unbounded intervals require a future runtime representation",
        ),
    ];
    for level in LEVELS {
        for (name, source, expected) in cases {
            let errors = compile(source, level)
                .expect_err(&format!("{level:?} {name} unexpectedly compiled"));
            assert!(
                errors.iter().any(|message| message.contains(expected)),
                "{level:?} {name}: expected {expected:?}, got {errors:#?}",
            );
        }
    }
}
