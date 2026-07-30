use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

#[test]
fn effect_clause_keeps_context_through_a_nested_result_handler() {
    let source = r#"
        effect Observe {
            [1,1] item(id: usize, value: usize) -> ()
        }

        select() -> Result<usize, usize> / {Observe} {
            perform Observe::item(1, 3);
            Result::Err(2)
        }

        answer() -> usize {
            handle {
                handle select() {
                    Result::Err(id) => id,
                    Result::Ok(value) => value
                }
            } {
                Observe::item(id, value) with continuation => {
                    id + value + resume(continuation, ())
                }
            }
        }

        main() -> () { () }
    "#;

    let artifact =
        compile_source_to_bytecode("nested-handler-contextual-inference.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();

    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::U64(6)
    );
}

#[test]
fn generic_effect_substitution_types_payload_and_resumption_across_nested_handler() {
    let source = r#"
        effect Observe<T> {
            [1,1] item(value: T) -> T
        }

        select() -> Result<usize, usize> / {Observe<usize>} {
            let observed = perform Observe<usize>::item(3);
            Result::Err(observed)
        }

        answer() -> usize {
            handle {
                handle select() {
                    Result::Err(value) => value,
                    Result::Ok(value) => value
                }
            } {
                Observe<usize>::item(value) with continuation => {
                    value + resume(continuation, value)
                }
            }
        }

        main() -> () { () }
    "#;

    let artifact =
        compile_source_to_bytecode("generic-nested-handler-context.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();

    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::U64(6)
    );
}

#[test]
fn mixed_const_and_type_effect_arguments_keep_type_substitution_position() {
    let source = r#"
        effect Observe<const N: u32, T> {
            [1,1] item(value: T) -> T
        }

        select() -> Result<usize, usize> / {Observe<7, usize>} {
            let observed = perform Observe<7, usize>::item(3);
            Result::Err(observed)
        }

        answer() -> usize {
            handle {
                handle select() {
                    Result::Err(value) => value,
                    Result::Ok(value) => value
                }
            } {
                Observe<7, usize>::item(value) with continuation => {
                    value + resume(continuation, value)
                }
            }
        }

        main() -> () { () }
    "#;

    let artifact =
        compile_source_to_bytecode("mixed-effect-argument-context.glorious", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();

    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::U64(6)
    );
}
