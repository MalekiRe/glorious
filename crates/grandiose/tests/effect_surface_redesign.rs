use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

fn run(source: &str, function: &str) -> Value {
    let artifact = compile_source_to_bytecode("effect-surface-redesign.glorious", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|candidate| candidate.name == function)
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

#[test]
fn operation_calls_and_continuation_calls_use_ordinary_call_syntax() {
    let source = r#"
        effect Ask { ask() -> i64 }
        answer() -> i64 {
            handle Ask::ask() {
                Ask::ask(k) => k(42)
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn payload_only_operation_arms_tail_resume() {
    let source = r#"
        effect Ask { ask() -> i64 }
        answer() -> i64 {
            handle Ask::ask() {
                Ask::ask() => 42
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn completion_and_operation_arms_share_one_handle_surface() {
    let source = r#"
        effect Ask { ask() -> i64 }
        compute() -> Result<i64, ()> / Ask {
            Result::Ok(Ask::ask())
        }
        answer() -> i64 {
            handle compute() {
                Result::Ok(value) => value,
                Result::Err(_) => 0,
                Ask::ask() => 42
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn completion_only_handle_replaces_inspection_effects() {
    let source = r#"
        make() -> Result<i64, ()> { Result::Ok(42) }
        answer() -> i64 {
            handle make() {
                Result::Ok(value) => value,
                Result::Err(_) => 0
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn nested_completion_handles_preserve_following_local_identities() {
    let source = r#"
        answer() -> i64 {
            let code = handle 0 {
                0 => handle 1 {
                    1 => 42,
                    _ => 41
                },
                _ => 40
            };
            let copied = code;
            copied
        }
        main() { () }
    "#;
    std::thread::Builder::new()
        .stack_size(16 * 1024 * 1024)
        .spawn(move || assert_eq!(run(source, "answer"), Value::I64(42)))
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn arrowless_unit_signatures_singleton_rows_and_terminal_calls_compile() {
    let source = r#"
        effect Out { write(value: i64) }
        effect Stop { stop(value: i64) -> ! }
        emit() / Out { Out::write(1) }
        answer() -> i64 {
            handle Stop::stop(42) {
                Stop::stop(value) => value
            }
        }
        exercise() -> i64 {
            handle { emit(); 42 } {
                Out::write(_) => ()
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
    assert_eq!(run(source, "exercise"), Value::I64(42));
}

#[test]
fn wildcard_continuation_pattern_discards_optional_resumption() {
    let source = r#"
        effect Poll { [0,1] poll() -> i64 }
        answer() -> i64 {
            handle Poll::poll() {
                Poll::poll(_) => 42
            }
        }
        main() { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}
