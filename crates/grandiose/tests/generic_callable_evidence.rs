use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

fn run_i64(source: &str, function: &str) -> i64 {
    let artifact = compile_source_to_bytecode("generic-callable-evidence.gr", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|candidate| candidate.name == function)
        .unwrap() as u32;
    match Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
    {
        Value::I64(value) => value,
        value => panic!("expected i64, found {value:?}"),
    }
}

#[test]
fn generic_callable_evidence_forwards_through_nested_generic_calls() {
    let source = r#"
        invoke<F, R>(body: F) -> R
            where F: Fn<(), Output=R> { body() }
        forward<F, R>(body: F) -> R
            where F: Fn<(), Output=R> { invoke(body) }
        answer() -> i64 { forward({ => 42 }) }
        main() -> { () }
    "#;
    assert_eq!(run_i64(source, "answer"), 42);
}

#[test]
fn generic_callable_identity_preserves_symbolic_callable_evidence() {
    let source = r#"
        retain_callable<F, R>(body: F) -> F
            where F: Fn<(), Output=R> { body }
        answer() -> i64 {
            let retained = retain_callable({ => 42 });
            retained()
        }
        main() -> { () }
    "#;
    assert_eq!(run_i64(source, "answer"), 42);
}

#[test]
fn callable_and_marker_evidence_are_substituted_together() {
    let source = r#"
        trait Mark {}
        impl Mark for i64 {}
        invoke<F, T>(value: T, body: F) -> T
            where F: Fn<(T), Output=T>, T: Mark { body(value) }
        forward<F, T>(value: T, body: F) -> T
            where F: Fn<(T), Output=T>, T: Mark { invoke(value, body) }
        answer() -> i64 { forward(42, { value => value }) }
        main() -> { () }
    "#;
    assert_eq!(run_i64(source, "answer"), 42);
}

#[test]
fn uninstantiated_generic_callable_bodies_are_symbolically_checked() {
    let source = r#"
        invalid<F, R>(body: F) -> R
            where F: Fn<(i64), Output=R> { body() }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("invalid-generic-callable-body.gr", source)
        .expect_err("an uninstantiated generic body must still be checked");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("expects 1 argument")
        }),
        "{errors:#?}"
    );
}
