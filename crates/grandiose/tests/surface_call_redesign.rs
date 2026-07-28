use grandiose_vm::{Value, Vm, verify};

#[test]
fn hyphenated_whitespace_calls_compile_and_execute() {
    let source = r#"
        sum-three(first: i64, second: i64, third: i64) -> i64 {
            first + second + third
        }

        nested(value: i64) -> i64 { value + 1 }

        selected() -> i64 {
            sum-three 10, 20, nested(11)
        }

        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("surface-call-redesign.glorious", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn dollar_references_produce_first_class_callables() {
    let source = r#"
        sum-three(first: i64, second: i64, third: i64) -> i64 {
            first + second + third
        }

        apply<F>(callable: F) -> i64
        where F: Fn<(i64, i64, i64), Output = i64> {
            callable(10, 20, 12)
        }

        selected() -> i64 { apply($sum-three) }
        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("dollar-function-reference.glorious", source)
            .unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn symbolic_add_is_an_ordinary_trait_method() {
    let source = r#"
        struct Wrapped { value: i64 }

        impl Add for Wrapped {
            +(self: Wrapped, other: Wrapped) -> Wrapped {
                self;
                other
            }
        }

        selected() -> i64 {
            let result = Wrapped { value: 10 } + Wrapped { value: 42 };
            result.value
        }

        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("symbolic-add-trait.glorious", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}
