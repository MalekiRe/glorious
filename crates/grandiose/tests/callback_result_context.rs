use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

#[test]
fn generic_try_callback_uses_the_enclosing_label_result_context() {
    let source = r#"
        enum WalkError { Rejected }

        walk(source: &Vec<u32>) -> Result<usize, WalkError> {
            try(Slice::try_for_each(
                Vec::as_slice(source),
                { _ => Result::Ok(()) }
            ), @walk);
            Result::Ok(Vec::len(source))
        }

        answer() -> usize {
            let source = Vec::new();
            Vec::push(&mut source, 2);
            Vec::push(&mut source, 3);
            handle walk(&source) {
                Result::Err(_) => 0,
                Result::Ok(found) => found
            }
        }

        main() -> { () }
    "#;

    let artifact = compile_source_to_bytecode("callback-result-context.glorious", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();
    assert_eq!(
        Vm::new(verified).run(function, vec![]).unwrap(),
        Value::U64(2)
    );
}

#[test]
fn generic_try_callback_keeps_result_context_through_source_if() {
    let source = r#"
        enum WalkError { Rejected }

        walk(source: &Vec<u32>) -> Result<usize, WalkError> {
            if(not(
                Slice::first(Vec::as_slice(source)) is Option::Some(_)
            ) and {
                Slice::is_empty(Vec::as_slice(source))
            }) {
                Result::Ok(0)
            } else {
                try(Slice::try_for_each(
                    Vec::as_slice(source),
                    { _ => Result::Ok(()) }
                ), @walk);
                Result::Ok(Vec::len(source))
            }
        }

        answer() -> usize {
            let source = Vec::new();
            Vec::push(&mut source, 2);
            Vec::push(&mut source, 3);
            handle walk(&source) {
                Result::Err(_) => 0,
                Result::Ok(found) => found
            }
        }

        main() -> { () }
    "#;

    let artifact =
        compile_source_to_bytecode("callback-result-source-if.glorious", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();
    assert_eq!(
        Vm::new(verified).run(function, vec![]).unwrap(),
        Value::U64(2)
    );
}
