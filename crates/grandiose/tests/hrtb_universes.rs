use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::verify;

#[test]
fn higher_ranked_type_and_lifetime_prerequisites_compile_with_rigid_evidence() {
    let source = r#"
        trait Every<T, 'a> {}
        trait Universal {}
        struct Witness { marker: i64 }

        impl<T, 'a> Every<T, 'a> for Text {}
        impl Universal for Witness where for<T, 'a> Text: Every<T, 'a> {}

        require_universal<X>(value: X) -> X where X: Universal { value }
        answer() -> Witness { require_universal(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "hrtb-positive.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect("blanket evidence must prove a universally quantified prerequisite");
        verify(artifact).unwrap();
    }
}

#[test]
fn one_concrete_impl_does_not_prove_a_higher_ranked_type_goal() {
    let source = r#"
        trait Only<T> {}
        trait Universal {}
        struct Witness { marker: i64 }

        impl Only<i64> for Text {}
        impl Universal for Witness where for<T> Text: Only<T> {}

        require_universal<X>(value: X) -> X where X: Universal { value }
        bad() -> Witness { require_universal(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("hrtb-negative.glorious", source)
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

#[test]
fn higher_ranked_const_prerequisites_use_fresh_rigid_values() {
    let positive = r#"
        trait Every<const N: u32> {}
        trait Universal {}
        struct Witness { marker: i64 }
        impl<const N: u32> Every<N> for Text {}
        impl Universal for Witness where for<const N: u32> Text: Every<N> {}
        require_universal<X>(value: X) -> X where X: Universal { value }
        answer() -> Witness { require_universal(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    verify(
        compile_source_to_bytecode("hrtb-const-positive.glorious", positive)
            .expect("blanket const evidence must prove the universal prerequisite"),
    )
    .unwrap();

    let negative = r#"
        trait Only<const N: u32> {}
        trait Universal {}
        struct Witness { marker: i64 }
        impl Only<7> for Text {}
        impl Universal for Witness where for<const N: u32> Text: Only<N> {}
        require_universal<X>(value: X) -> X where X: Universal { value }
        bad() -> Witness { require_universal(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("hrtb-const-negative.glorious", negative)
        .expect_err("one const implementation must not prove a universal const goal");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Universal")
                && (error.message.contains("no matching implementation")
                    || error.message.contains("no evidence"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn higher_ranked_effect_row_gat_prerequisites_are_universal() {
    let source = r#"
        effect Ask { ask() -> ! }
        trait Capability { type Effects<r: EffectRow>: EffectRow; }
        trait Universal {}
        struct Carrier { marker: i64 }
        struct Witness { marker: i64 }
        impl Capability for Carrier {
            type Effects<r: EffectRow> = {Ask | r};
        }
        impl Universal for Witness
            where for<r: EffectRow> Carrier: Capability<Effects<r> = {Ask | r}> {}
        require_universal<X>(value: X) -> X where X: Universal { value }
        answer() -> Witness { require_universal(Witness { marker: 42 }) }
        main() -> () { () }
    "#;
    verify(
        compile_source_to_bytecode("hrtb-effect-row-positive.glorious", source)
            .expect("the associated effect-row GAT must hold for every row tail"),
    )
    .unwrap();

    let negative = source.replace("{Ask | r};", "{Ask};");
    let errors = compile_source_to_bytecode("hrtb-effect-row-negative.glorious", &negative)
        .expect_err("a closed associated row must not prove every open row tail");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Universal")
                && (error.message.contains("no matching implementation")
                    || error.message.contains("no evidence"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn higher_ranked_outlives_constraints_are_scoped_and_universal() {
    let positive = "check() -> () where for<'a> 'static: 'a { () } main() -> () { () }";
    verify(compile_source_to_bytecode("hrtb-outlives-positive.glorious", positive).unwrap())
        .unwrap();

    let impossible = "check() -> () where for<'a, 'b> 'a: 'b { () } main() -> () { () }";
    let errors = compile_source_to_bytecode("hrtb-outlives-impossible.glorious", impossible)
        .expect_err("unrelated universal lifetimes do not have an outlives relation");
    assert!(
        errors.iter().any(|error| {
            error.title == "unprovable higher-ranked outlives constraint" && error.span.is_some()
        }),
        "{errors:#?}"
    );

    let shadow = "bad<'a, 'b>(value: &'a i64) -> &'b i64 where for<'a> 'static: 'a { value } main() -> () { () }";
    let errors = compile_source_to_bytecode("hrtb-outlives-shadow.glorious", shadow).expect_err(
        "a scoped HRT binder must not add facts for the outer lifetime of the same name",
    );
    assert!(
        errors.iter().any(|error| {
            error.message.contains("outlive") || error.message.contains("return lifetime")
        }),
        "{errors:#?}"
    );
}
