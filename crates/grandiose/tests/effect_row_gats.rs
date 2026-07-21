use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn open_effect_row_gat_binders_normalize_to_members_plus_the_original_tail() {
    let source = r#"
        effect Fail<E> { fail(error:E) -> ! }
        struct Carrier { marker:i64 }
        trait Capability { type Effects<e:EffectRow>: EffectRow; }
        impl Capability for Carrier {
            type Effects<r:EffectRow> = {Fail<i64> | r};
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("open-effect-row-gat.gr", source)
        .expect("an open associated row must retain its declared tail");
    verify(artifact).unwrap();
}

#[test]
fn open_associated_rows_close_through_callable_specialization_at_all_levels() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        effect Trace { [1,1] trace() -> i64 }
        struct Carrier{}
        trait Capability { type Effects<e:EffectRow>:EffectRow; }
        impl Capability for Carrier { type Effects<r:EffectRow> = {Ask|r}; }
        invoke<F,e:EffectRow>(body:F)->i64
            where F:Fn<(),Output=i64,Effects={<Carrier as Capability>::Effects<e>}> {
            body()
        }
        ask()->i64 / {Ask} { invoke({=>perform Ask::ask()}) }
        ask_trace()->i64 / {Ask,Trace} {
            invoke({=>{perform Ask::ask();perform Trace::trace()}})
        }
        main()->{()}
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "specialized-open-effect-row-gat.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        verify(artifact).unwrap();
    }
}

#[test]
fn open_associated_row_specialization_rejects_ungrounded_and_conflicting_tails() {
    let ungrounded = r#"
        trait Capability{type Effects<e:EffectRow>:EffectRow;}
        invoke<C,F,e:EffectRow>(capability:&C,body:F)->i64
            where F:Fn<(),Output=i64,Effects={<C as Capability>::Effects<e>}> {
            body()
        }
        main()->{()}
    "#;
    let errors = compile_source_to_bytecode("ungrounded-open-row-gat.gr", ungrounded)
        .expect_err("a symbolic owner without exact equality evidence must not reach MIR");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error
                    .message
                    .contains("equality projection could not be normalized")
        }),
        "{errors:#?}"
    );

    let conflicting = r#"
        effect Ask{[1,1] ask()->i64}
        struct Carrier{}
        trait Capability{type Effects<e:EffectRow>:EffectRow;}
        impl Capability for Carrier{type Effects<r:EffectRow> = {Ask|r};}
        invoke<F,e:EffectRow,x:EffectRow>(body:F)->i64
            where F:Fn<(),Output=i64,Effects={<Carrier as Capability>::Effects<e>|x}> {
            body()
        }
        main()->{()}
    "#;
    let errors = compile_source_to_bytecode("conflicting-open-row-gat.gr", conflicting)
        .expect_err("two distinct residual tails must not be merged");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("cannot merge distinct open tails")
        }),
        "{errors:#?}"
    );
}

#[test]
fn open_effect_row_gat_arguments_are_kinded_and_tails_are_bound() {
    for (source, expected) in [
        (
            "trait C{type E<e:EffectRow>:EffectRow;} struct S{} impl C for S{type E<T> = {|T};} main()->{()}",
            "wrong kind",
        ),
        (
            "trait C{type E<e:EffectRow>;} main()->{()}",
            "only on callable",
        ),
        (
            "trait C{type E<e:EffectRow>:EffectRow;} struct S{} impl C for S{type E<r:EffectRow> = {|missing};} main()->{()}",
            "unbound",
        ),
    ] {
        let errors = compile_source_to_bytecode("invalid-open-effect-row-gat.gr", source)
            .expect_err("invalid open associated rows must be rejected");
        assert!(
            errors.iter().any(|error| {
                error.code.is_some() && error.span.is_some() && error.message.contains(expected)
            }),
            "{errors:#?}"
        );
    }

    let wrong_projection = r#"
        effect Fail { fail() -> ! }
        struct S{}
        trait C{type E<e:EffectRow>:EffectRow;}
        impl C for S{type E<r:EffectRow> = {Fail|r};}
        bad<T>() -> / {<S as C>::E<T>} { () }
        main()->{()}
    "#;
    let errors = compile_source_to_bytecode("wrong-open-row-argument.gr", wrong_projection)
        .expect_err("a type binder must not masquerade as an effect-row binder");
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("requires an in-scope EffectRow binder")),
        "{errors:#?}"
    );
}

#[test]
fn grounded_effect_row_gat_projects_into_callable_rows_at_all_levels() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        struct Carrier { marker: i64 }
        trait Capability { type Effects<T>: EffectRow; }
        impl Capability for Carrier { type Effects<U> = {Fail<U>}; }

        projected(error: i64) -> ! / {<Carrier as Capability>::Effects<i64>} {
            perform Fail<i64>::fail(error)
        }
        selected() -> i64 {
            handle { projected(42) } { Fail<i64>::fail(error) => error }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "effect-row-gat.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn effect_row_gats_require_exact_evidence_and_value_kinds() {
    let unresolved = r#"
        effect Fail<E> { fail(error: E) -> ! }
        struct Carrier { marker: i64 }
        trait Capability { type Effects<T>: EffectRow; }
        bad() -> / {<Carrier as Capability>::Effects<i64>} { () }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("unresolved-effect-row-gat.gr", unresolved)
        .expect_err("a row projection without implementation evidence must fail");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error
                    .message
                    .contains("associated effect-row projection is unresolved")
        }),
        "{errors:#?}",
    );

    for source in [
        "trait Capability{type Effects<T>:EffectRow;} struct Carrier{marker:i64} impl Capability for Carrier{type Effects<U> = U;} main()->{()}",
        "trait Family{type Item<T>;} struct Carrier{marker:i64} impl Family for Carrier{type Item<U> = {};} main()->{()}",
    ] {
        let errors = compile_source_to_bytecode("wrong-associated-kind.gr", source)
            .expect_err("associated item values must match their declared kind");
        assert!(
            errors.iter().any(|error| {
                error.code.is_some()
                    && error.span.is_some()
                    && (error.message.contains("requires `{...}` row syntax")
                        || error.message.contains("requires a type value"))
            }),
            "{errors:#?}",
        );
    }
}

#[test]
fn symbolic_effect_row_gat_equalities_close_generic_callable_rows() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        struct Carrier { marker: i64 }
        trait Capability { type Effects<T>: EffectRow; }
        impl Capability for Carrier { type Effects<U> = {Fail<U>}; }

        forward<C, T>(capability: &C, value: T) -> !
            / {<C as Capability>::Effects<T>}
            where C: Capability<Effects<T> = {Fail<T>}> {
            perform Fail<T>::fail(value)
        }
        selected() -> i64 {
            let capability = Carrier { marker: 0 };
            handle { forward(&capability, 42) } {
                Fail<i64>::fail(error) => error
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "symbolic-effect-row-gat.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let selected = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(selected, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn symbolic_effect_row_projections_require_lexical_equality_evidence() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        trait Capability { type Effects<T>: EffectRow; }
        unresolved<C, T>(capability: &C, value: T) -> !
            / {<C as Capability>::Effects<T>}
            where C: Capability {
            perform Fail<T>::fail(value)
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("symbolic-row-without-equality.gr", source)
        .expect_err("a symbolic row projection requires an exact lexical equality");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error
                    .message
                    .contains("associated effect-row projection is unresolved")
        }),
        "{errors:#?}",
    );

    let conflicting = r#"
        effect Fail<E> { fail(error: E) -> ! }
        effect Other<E> { fail(error: E) -> ! }
        struct Carrier { marker: i64 }
        trait Capability { type Effects<T>: EffectRow; }
        impl Capability for Carrier { type Effects<U> = {Fail<U>}; }
        forward<C, T>(capability: &C, value: T) -> !
            / {<C as Capability>::Effects<T>}
            where C: Capability<Effects<T> = {Other<T>}> {
            perform Other<T>::fail(value)
        }
        bad(capability: Carrier) -> ! { forward(&capability, 42) }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("conflicting-symbolic-row-equality.gr", conflicting)
        .expect_err("ground impl evidence must agree with the lexical row equality");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("no matching implementation")
        }),
        "{errors:#?}",
    );
}
