//! Focused coverage for the specialization/type-planning half of general
//! first-class callables. Runtime assertions cover plans the current backend
//! can emit; diagnostics pin the remaining late-resumption integration seam.

use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Instruction, Value, Vm, verify};

fn run(source_name: &str, source: &str) -> (grandiose_vm::Artifact, Value) {
    let artifact = compile_source_to_bytecode(source_name, source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .expect("answer function") as u32;
    let value = Vm::new(verify(artifact.clone()).unwrap())
        .run(answer, vec![])
        .unwrap();
    (artifact, value)
}

#[test]
fn noncopy_capture_survives_generic_escape_and_is_consumed_once() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let ticket = Ticket { value: 40 };
            let add = (amount: i64) -> i64 {
                let Ticket { value } = move ticket;
                value + amount
            };
            let escaped = retain(move add);
            move escaped(2)
        }
        main() -> { () }
    "#;
    let (_, value) = run("noncopy-callable-escape.gr", source);
    assert_eq!(value, Value::I64(42));
}

#[test]
fn indirect_receiver_selection_preserves_observe_and_move_calls() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        answer() -> i64 {
            let base = 20;
            let observe = (value: i64) -> i64 { base + value };
            let ticket = Ticket { value: 20 };
            let consume = (value: i64) -> i64 {
                let Ticket { value: base } = move ticket;
                base + value
            };
            observe(2) + move consume(20) - 20
        }
        main() -> { () }
    "#;
    let (artifact, value) = run("callable-receiver-modes.gr", source);
    assert_eq!(value, Value::I64(42));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 0,
            ..
        }
    )));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 2,
            ..
        }
    )));
}

#[test]
fn explicit_parameter_resumption_capture_executes_through_late_lowering() {
    let source = r#"
        effect Stop { [1,1] stop() -> i64 }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let finish = (value: i64) -> i64 {
                        resume(move continuation, value)
                    };
                    move finish(42)
                }
            }
        }
        main() -> { () }
    "#;
    let (artifact, value) = run("late-parameter-closure.gr", source);
    assert_eq!(value, Value::I64(42));
    assert!(artifact.code.iter().any(|instruction| matches!(
        instruction,
        Instruction::CallIndirect {
            receiver_mode: 2,
            ..
        }
    )));
}

#[test]
fn borrowed_capture_crosses_a_generic_boundary_within_its_lifetime() {
    let source = r#"
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            let value = 42;
            let borrowed = &value;
            let closure = () -> i64 { *borrowed };
            let escaped = retain(move closure);
            move escaped()
        }
        main() -> { () }
    "#;
    let (_, value) = run("borrowed-callable-bounded-escape.gr", source);
    assert_eq!(value, Value::I64(42));
}
