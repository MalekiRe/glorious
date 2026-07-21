use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Instruction, Value, Vm, verify};

fn run_answer(source_name: &str, source: &str) -> (grandiose_vm::Artifact, Value) {
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
fn exact_two_shot_capture_is_borrowed_once_then_consumed_by_the_final_call() {
    let source = r#"
        effect Pick { [2,2] choose() -> i64 }
        answer() -> i64 {
            handle perform Pick::choose() {
                Pick::choose() with continuation => {
                    let resume_once = { => resume(continuation, 21) };
                    resume_once() + move resume_once()
                }
            }
        }
        main() -> { () }
    "#;
    let (artifact, value) = run_answer("closure-mode0-mode2.gr", source);
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
fn optional_resumption_capture_may_be_abandoned_with_its_closure() {
    let source = r#"
        effect Stop { [0,1] stop() -> i64 }
        answer() -> i64 {
            handle perform Stop::stop() {
                Stop::stop() with continuation => {
                    let abandoned = { => { cancel(move continuation); 0 } };
                    42
                }
            }
        }
        main() -> { () }
    "#;
    let (_, value) = run_answer("abandoned-optional-closure.gr", source);
    assert_eq!(value, Value::I64(42));
}

#[test]
fn captured_resumption_closure_survives_retain_and_aggregate_roundtrip() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        retain<T>(value: T) -> T { value }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with continuation => {
                    let finish = { => resume(move continuation, 42) };
                    let retained = retain(move finish);
                    let stored = (move retained,);
                    let (restored,) = move stored;
                    move restored()
                }
            }
        }
        main() -> { () }
    "#;
    let (_, value) = run_answer("retained-aggregate-closure.gr", source);
    assert_eq!(value, Value::I64(42));
}

#[test]
fn duplicated_callable_aliases_cannot_exceed_one_shared_capture_quantity() {
    let source = r#"
        effect Pick { [2,2] choose() -> i64 }
        answer() -> i64 {
            handle perform Pick::choose() {
                Pick::choose() with continuation => {
                    let resume_once = { => resume(continuation, 14) };
                    let duplicate = resume_once;
                    resume_once() + duplicate() + move duplicate() + move resume_once()
                }
            }
        }
        main() -> { () }
    "#;
    let diagnostics = compile_source_to_bytecode("duplicated-closure-alias.gr", source)
        .expect_err("duplicated aliases laundered excess resumes through a [2,2] capture");
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1BC002")
                && diagnostic.message.to_lowercase().contains("resum")
        }),
        "expected a stable source quantity diagnostic: {diagnostics:#?}"
    );
}
