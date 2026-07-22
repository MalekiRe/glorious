//! Noncopy mixed terminal/resumptive handler environments: per-clause capture
//! views over one stored environment, exact abandonment/resumption/
//! cancellation cleanup, and O1-O3 parity.

use grandiose::compiler_mir::OptimizationLevel;
use grandiose::{CompileOptions, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const LEVELS: [OptimizationLevel; 3] = [
    OptimizationLevel::O1,
    OptimizationLevel::O2,
    OptimizationLevel::O3,
];

fn phases_at(source: &str, level: OptimizationLevel) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        "handler-environments.glorious",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"))
}

fn run_entry(phases: &grandiose::CompiledPhases, name: &str) -> Value {
    let encoded = phases.artifact.encode();
    let artifact = grandiose_vm::Artifact::decode(&encoded).expect("artifact decodes");
    assert_eq!(artifact.encode(), encoded, "codec round trip is canonical");
    let verified = verify(artifact.clone()).expect("emitted artifact verifies");
    let entry = artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("program exports `{name}`")) as u32;
    Vm::new(verified).run(entry, vec![]).expect("execution")
}

fn expect_errors(source: &str) -> Vec<grandiose::diagnostic::Diagnostic> {
    compile_source_to_phases_with_options(
        "handler-environments.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .expect_err("compilation must be rejected")
}

#[test]
fn noncopy_capture_borrowed_by_a_one_shot_resumptive_clause() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Sack { value: i64 }
        impl Use<[0,1]> for Sack {}
        peek(sack: &Sack) -> i64 { 100 }
        run() -> i64 {
            let sack = Sack { value: 7 };
            handle {
                let bonus = perform Ask::ask();
                bonus + 1
            } {
                Ask::ask() with k => resume(k, peek(&sack) + sack.value)
            }
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_entry(&phases, "run"), Value::I64(108), "{level:?}");
    }
}

#[test]
fn noncopy_capture_used_only_by_a_terminal_clause() {
    let source = r#"
        effect Bail { fail() -> ! }
        struct Payload { value: i64 }
        impl Use<[0,1]> for Payload {}
        run() -> i64 {
            let payload = Payload { value: 41 };
            handle {
                perform Bail::fail()
            } {
                Bail::fail() => { let Payload { value } = payload; value + 1 }
            }
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_entry(&phases, "run"), Value::I64(42), "{level:?}");
    }
}

#[test]
fn mixed_terminal_and_resumptive_clauses_share_a_noncopy_capture() {
    let source = r#"
        effect Duo {
            [1,1] hint() -> i64
            abort() -> !
        }
        struct State { base: i64 }
        impl Use<[0,1]> for State {}
        observe(state: &State) -> i64 { 5 }
        stops(trigger: i64) -> i64 / {Duo} {
            let bonus = perform Duo::hint();
            bonus + trigger + 2
        }
        run() -> i64 {
            let state = State { base: 30 };
            let calm = handle { stops(0) } {
                Duo::hint() with k => resume(k, observe(&state) + state.base)
                Duo::abort() => { let State { base } = state; base }
            };
            calm
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_entry(&phases, "run"), Value::I64(37), "{level:?}");
    }
}

#[test]
fn terminal_selection_consumes_the_shared_environment_after_abandonment() {
    let source = r#"
        effect Duo {
            [1,1] hint() -> i64
            abort() -> !
        }
        struct State { base: i64 }
        impl Use<[0,1]> for State {}
        stops() -> i64 / {Duo} {
            let bonus = perform Duo::hint();
            perform Duo::abort()
        }
        run() -> i64 {
            let state = State { base: 20 };
            handle { stops() } {
                Duo::hint() with k => resume(k, state.base)
                Duo::abort() => { let State { base } = state; base + 2 }
            }
        }
        main() -> { () }
    "#;
    for level in LEVELS {
        let phases = phases_at(source, level);
        assert_eq!(run_entry(&phases, "run"), Value::I64(22), "{level:?}");
    }
}

#[test]
fn resumptive_clause_consuming_a_noncopy_capture_is_rejected() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Sack { value: i64 }
        impl Use<[0,1]> for Sack {}
        eat(sack: Sack) -> i64 { let Sack { value } = sack; value }
        run() -> i64 {
            let sack = Sack { value: 7 };
            handle {
                perform Ask::ask()
            } {
                Ask::ask() with k => resume(k, eat(sack))
            }
        }
        main() -> { () }
    "#;
    let errors = expect_errors(source);
    assert!(
        errors
            .iter()
            .any(|error| error.code.as_deref() == Some("G1HE001")),
        "{errors:#?}"
    );
}

#[test]
fn unique_borrow_of_a_shared_environment_capture_is_rejected() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Sack { value: i64 }
        impl Use<[0,1]> for Sack {}
        bump(sack: &mut Sack) -> i64 { 0 }
        run() -> i64 {
            let sack = Sack { value: 7 };
            handle {
                perform Ask::ask()
            } {
                Ask::ask() with k => resume(k, bump(&mut sack))
            }
        }
        main() -> { () }
    "#;
    let errors = expect_errors(source);
    assert!(
        errors
            .iter()
            .any(|error| error.code.as_deref() == Some("G1HE002")),
        "{errors:#?}"
    );
}
