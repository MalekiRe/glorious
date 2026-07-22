use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::{Value, Vm, verify};

fn run_i64(source: &str, function: &str) -> i64 {
    let artifact =
        compile_source_to_bytecode("generic-callable-evidence.glorious", source).unwrap();
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

fn assert_answer_all_modes(source: &str) {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-callable-evidence-all-modes.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|candidate| candidate.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
    let recovery_source = source.replace("main() -> { () }", "main() -> i64 { answer() }");
    assert_eq!(
        grandiose::run_source(
            "generic-callable-evidence-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

fn assert_rejected_all_modes(source: &str, needle: &str) {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_source_to_bytecode_with_options(
            "generic-callable-evidence-negative.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .expect_err("invalid generic callable evidence compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "{optimization_level:?}: {errors:#?}"
        );
    }
}

#[test]
fn structural_else_completes_complementary_generic_result_constructors() {
    let source = r#"
        choose<T, E>(flag: Result<(), ()>, ok: T, error: E) -> Result<T, E> {
            if(flag) { Result::Ok(ok) } else { Result::Err(error) }
        }
        answer() -> i64 {
            let selected = choose(Result::Ok(()), 42, ());
            if(selected is Result::Ok(_)) { selected.0 } else { 0 }
        }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}

#[test]
fn structural_else_completes_option_alias_and_reordered_result_branches() {
    let source = r#"
        choose_option<T>(flag: Result<(), ()>, value: T) -> Option<T> {
            if(flag) { Option::Some(value) } else { None }
        }
        choose_reordered<T, E>(flag: Result<(), ()>, ok: T, error: E) -> Result<T, E> {
            if(flag) { Result::Err(error) } else { Result::Ok(ok) }
        }
        answer() -> i64 {
            let optional = choose_option(Result::Ok(()), 20);
            let selected = choose_reordered(Result::Err(()), 22, ());
            let left = if(optional is Result::Ok(_)) { optional.0 } else { 0 };
            let right = if(selected is Result::Ok(_)) { selected.0 } else { 0 };
            left + right
        }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}

#[test]
fn structural_else_rejects_incompatible_complementary_payloads() {
    let source = r#"
        bad(flag: Result<(), ()>) -> Result<i64, ()> {
            if(flag) { Result::Ok(42) } else { Result::Err("wrong") }
        }
        main() -> { bad(Result::Ok(())); () }
    "#;
    assert_rejected_all_modes(source, "conflicting type arguments");
}

#[test]
fn callable_evidence_carries_lifetime_const_and_effect_environments_together() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Tag<const N: u32> { value: i64 }
        tag7() -> Tag<7> { Tag { value: 40 } }
        invoke<'a, const N: u32, F, e: EffectRow>(
            tag: Tag<N>, witness: &'a i64, body: F
        ) -> i64
            where F: Fn<(&'a i64), Output=i64, Effects={Ask | e}> {
            tag.value + body(witness)
        }
        answer() -> i64 {
            let value = 2;
            handle invoke(
                tag7(),
                &value,
                (seen: &i64) -> i64 / {Ask} { *seen + perform Ask::ask() }
            ) {
                Ask::ask() with continuation => resume(continuation, 0)
            }
        }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}

#[test]
fn finite_recursive_specialization_cycle_compiles_in_every_mode() {
    let source = r#"
        first<T>(value: T) -> () { second(value) }
        second<T>(value: T) -> () { first(value) }
        main() -> { first(()); () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "finite-recursive-specialization.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        verify(artifact).unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}

#[test]
fn structurally_growing_recursive_specialization_fails_before_unbounded_discovery() {
    let source = r#"
        grow<T>(value: T) -> () { grow((value,)) }
        main() -> { grow(()); () }
    "#;
    assert_rejected_all_modes(source, "recursive specialization is non-well-founded");
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
fn callable_signature_normalizes_lexical_associated_projection_evidence() {
    let source = r#"
        trait Value { type Item; }
        struct Good { marker: i64 }
        impl Value for Good { type Item = i64; }
        invoke<T, F>(owner: T, body: F) -> <T as Value>::Item
            where T: Value<Item=i64>,
                  F: Fn<(), Output=<T as Value>::Item> {
            owner;
            body()
        }
        answer() -> i64 { invoke(Good { marker: 0 }, { => 42 }) }
        main() -> { () }
    "#;
    assert_eq!(run_i64(source, "answer"), 42);
}

#[test]
fn callable_signature_normalizes_lexical_gat_projection_evidence() {
    let source = r#"
        trait Keyed { type At<K>; }
        struct Good { marker: i64 }
        impl Keyed for Good { type At<K> = K; }
        invoke<T, K, F>(owner: T, body: F) -> <T as Keyed>::At<K>
            where T: Keyed<At<K> = K>,
                  F: Fn<(), Output=<T as Keyed>::At<K>> {
            owner;
            body()
        }
        answer() -> i64 { invoke(Good { marker: 0 }, { => 42 }) }
        main() -> { () }
    "#;
    assert_eq!(run_i64(source, "answer"), 42);
}

#[test]
fn callable_signature_projection_without_exact_equality_fails_closed() {
    let source = r#"
        trait Value { type Item; }
        invalid<T, F>(body: F) -> <T as Value>::Item
            where T: Value,
                  F: Fn<(), Output=<T as Value>::Item> {
            body()
        }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("callable-projection-without-equality.glorious", source)
            .expect_err("an unproved callable projection compiled");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Fn<Tuple")
                || error.message.contains("projection")
                || error.message.contains("equality")
        }),
        "{errors:#?}"
    );
}

#[test]
fn uninstantiated_generic_callable_bodies_are_symbolically_checked() {
    let source = r#"
        invalid<F, R>(body: F) -> R
            where F: Fn<(i64), Output=R> { body() }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("invalid-generic-callable-body.glorious", source)
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

#[test]
fn callable_evidence_composes_with_ordinary_trait_method_evidence() {
    let source = r#"
        trait Transform { transform(self: &Self, value: i64) -> i64; }
        struct Increment { marker: i64 }
        impl Transform for Increment {
            transform(self: &Increment, value: i64) -> i64 { value + 1 }
        }
        invoke<T, F>(owner: T, body: F) -> i64
            where T: Transform, F: Fn<(i64), Output=i64> {
            body(owner.transform(41))
        }
        answer() -> i64 { invoke(Increment { marker: 0 }, { value => value }) }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}

#[test]
fn ground_impl_normalizes_callable_associated_output_without_lexical_equality() {
    let source = r#"
        trait Value { type Item; }
        struct Good { marker: i64 }
        impl Value for Good { type Item = i64; }
        invoke<T, F>(owner: T, body: F) -> <T as Value>::Item
            where T: Value, F: Fn<(), Output=<T as Value>::Item> {
            owner;
            body()
        }
        answer() -> i64 { invoke(Good { marker: 0 }, { => 42 }) }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}

#[test]
fn ground_impl_normalizes_callable_gat_output_without_lexical_equality() {
    let source = r#"
        trait Keyed { type At<K>; }
        struct Good { marker: i64 }
        impl Keyed for Good { type At<K> = K; }
        invoke<T, K, F>(owner: T, seed: K, body: F) -> <T as Keyed>::At<K>
            where T: Keyed, F: Fn<(), Output=<T as Keyed>::At<K>> {
            owner;
            seed;
            body()
        }
        answer() -> i64 { invoke(Good { marker: 0 }, 0, { => 42 }) }
        main() -> { () }
    "#;
    assert_answer_all_modes(source);
}
