use grandiose::compile_source_to_bytecode;
use grandiose_vm::verify;

#[test]
fn higher_ranked_type_and_lifetime_prerequisites_compile_with_rigid_evidence() {
    let source = r#"
        trait Every<T, 'a> {}
        trait Universal {}
        struct Witness { marker: i64 }

        impl<T, 'a> Every<T, 'a> for Text {}
        impl Universal for Witness where for<T, 'a> Text: Every<T, 'a> {}

        require<X>(value: X) -> X where X: Universal { value }
        answer() -> Witness { require(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("hrtb-positive.gr", source)
        .expect("blanket evidence must prove a universally quantified prerequisite");
    verify(artifact).unwrap();
}

#[test]
fn one_concrete_impl_does_not_prove_a_higher_ranked_type_goal() {
    let source = r#"
        trait Only<T> {}
        trait Universal {}
        struct Witness { marker: i64 }

        impl Only<i64> for Text {}
        impl Universal for Witness where for<T> Text: Only<T> {}

        require<X>(value: X) -> X where X: Universal { value }
        bad() -> Witness { require(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("hrtb-negative.gr", source)
        .expect_err("one concrete implementation must not prove `for<T>`");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Universal")
                && (error.message.contains("no matching implementation")
                    || error.message.contains("no evidence"))
        }),
        "{errors:#?}"
    );
}
