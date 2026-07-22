//! Regression coverage for quantity-bearing values stored in a
//! `MAKE_HANDLER_SHARED` environment.
//!
//! These programs exercise the mutually-exclusive use model end to end.

use grandiose::compile_source_to_phases;
use grandiose_vm::{Instruction, Value, Vm, verify};

fn compile_verify_run(source: &str, expected: i64) {
    let phases = compile_source_to_phases("shared-handler-resumption-quantities.glorious", source)
        .expect("source lowers to bytecode phases");
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| { matches!(instruction, Instruction::MakeHandlerShared { .. }) }),
        "fixture must exercise MAKE_HANDLER_SHARED"
    );
    let entry = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "run")
        .expect("run is emitted") as u32;
    let verified = verify(phases.artifact).expect("shared quantity identity verifies");
    assert_eq!(
        Vm::new(verified).run(entry, vec![]).expect("execution"),
        Value::I64(expected)
    );
}

#[test]
fn shared_terminal_alternatives_capture_zero_or_one_shot_resumption() {
    compile_verify_run(
        r#"
            effect Carry { [0,1] take() -> i64 }
            effect Gate { left() -> ! right() -> ! }

            run() -> i64 {
                handle { perform Carry::take() } {
                    Carry::take() with k => {
                        handle { perform Gate::left() } {
                            Gate::left() => { let held = &k; 10 }
                            Gate::right() => { let held = &k; 20 }
                        }
                    }
                }
            }
            main() -> { () }
        "#,
        10,
    );
}

#[test]
fn shared_terminal_alternatives_capture_exact_one_shot_resumption() {
    compile_verify_run(
        r#"
            effect Carry { [1,1] take() -> i64 }
            effect Gate { left() -> ! right() -> ! }

            run() -> i64 {
                handle { perform Carry::take() } {
                    Carry::take() with k => {
                        handle { perform Gate::left() } {
                            Gate::left() => resume(k, 10)
                            Gate::right() => resume(k, 20)
                        }
                    }
                }
            }
            main() -> { () }
        "#,
        10,
    );
}

#[test]
fn shared_terminal_alternatives_capture_exact_two_shot_resumption() {
    compile_verify_run(
        r#"
            effect Carry { [2,2] take() -> i64 }
            effect Gate { left() -> ! right() -> ! }

            run() -> i64 {
                handle { perform Carry::take() } {
                    Carry::take() with k => {
                        handle { perform Gate::left() } {
                            Gate::left() => {
                                let ignored = resume(k, 10);
                                resume(move k, 11)
                            }
                            Gate::right() => {
                                let ignored = resume(k, 20);
                                resume(move k, 21)
                            }
                        }
                    }
                }
            }
            main() -> { () }
        "#,
        11,
    );
}

#[test]
fn mixed_terminal_and_resumptive_alternatives_capture_two_shot_resumption() {
    compile_verify_run(
        r#"
            effect Carry { [2,2] take() -> i64 }
            effect Gate { stop() -> ! [1,1] inspect() -> i64 }
            struct Token { value: i64 }
            impl Use<[0,1]> for Token {}

            run() -> i64 {
                handle { perform Carry::take() } {
                    Carry::take() with k => {
                        let token = Token { value: 3 };
                        handle { perform Gate::stop() } {
                            Gate::stop() => {
                                let marker = token.value;
                                let ignored = resume(k, marker);
                                resume(move k, marker + 1)
                            }
                            Gate::inspect() with inner => {
                                let marker = token.value;
                                let inspected = resume(inner, marker);
                                let ignored = resume(k, inspected);
                                resume(k, marker + 1)
                            }
                        }
                    }
                }
            }
            main() -> { () }
        "#,
        4,
    );
}
