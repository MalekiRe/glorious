use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options, lexer, parser,
    validate,
};
use grandiose_vm::{Value, Vm, verify};

fn parse(source: &str) -> grandiose::ast::Program {
    parser::parse(lexer::lex(source).unwrap()).unwrap()
}

#[test]
fn ordinary_trait_methods_preserve_declarations_and_impl_bodies() {
    let program = parse(
        r#"
            trait Describe { describe(self: &Self) -> Text; }
            struct Item { value: i64 }
            impl Describe for Item {
                describe(self: &Item) -> Text { "item" }
            }
            main() -> { () }
        "#,
    );
    assert_eq!(program.traits[0].methods.len(), 1);
    assert!(program.traits[0].methods[0].body.is_none());
    assert_eq!(program.impls[0].methods.len(), 1);
    assert!(program.impls[0].methods[0].body.is_some());
    validate::validate(&program).unwrap();
}

#[test]
fn trait_method_signature_substitutes_self_in_ground_impls() {
    let valid = parse(
        "trait Read{read(self:&Self)->i64;} struct Item{value:i64} impl Read for Item{read(self:&Item)->i64{42}} main()->{()}",
    );
    validate::validate(&valid).unwrap();

    let invalid = parse(
        "trait Read{read(self:&Self)->i64;} struct Item{value:i64} impl Read for Item{read(self:Item)->Text{\"bad\"}} main()->{()}",
    );
    let errors = validate::validate(&invalid).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.code.as_deref() == Some("G0142")
            && error.message.contains("does not match")
            && error.span.is_some()
    }));
}

#[test]
fn trait_method_sets_are_complete_and_exact() {
    for (source, code) in [
        (
            "trait Read{read(self:&Self)->i64;} struct Item{value:i64} impl Read for Item{} main()->{()}",
            "G0141",
        ),
        (
            "trait Read{} struct Item{value:i64} impl Read for Item{extra(self:&Item)->i64{42}} main()->{()}",
            "G0143",
        ),
        (
            "trait Read{read(self:&Self)->i64;} struct Item{value:i64} impl !Read for Item{read(self:&Item)->i64{42}} main()->{()}",
            "G0140",
        ),
    ] {
        let errors = validate::validate(&parse(source)).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.as_deref() == Some(code)),
            "{errors:#?}"
        );
        if code == "G0140" {
            assert!(
                errors.iter().all(|error| {
                    !matches!(error.code.as_deref(), Some("G0141" | "G0142" | "G0143"))
                }),
                "negative impl diagnostics cascaded: {errors:#?}"
            );
        }
    }
}

#[test]
fn grounded_qualified_trait_method_dispatches_statically() {
    let source = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        impl Read for Item {
            read(self: &Item) -> i64 { self.value }
        }
        answer(item: Item) -> i64 { Read::read(&item) }
        selected() -> i64 { answer(Item { value: 42 }) }
        main() -> { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("trait-method-dispatch.gr", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert!(
        artifact
            .functions
            .iter()
            .any(|function| function.name == "$trait$Read$Item$read")
    );
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_qualified_trait_methods_specialize_with_where_evidence_at_all_levels() {
    let source = r#"
        trait Mark {}
        impl Mark for i64 {}
        trait Select {
            select<T>(self: &Self, value: T) -> T where T: Mark;
        }
        struct Box<T> { value: T }
        impl Select for Box<i64> {
            select<U>(self: &Box<i64>, value: U) -> U where U: Mark { value }
        }
        answer(item: Box<i64>) -> i64 {
            Select::select(&item, 42)
        }
        selected() -> i64 { answer(Box { value: 0 }) }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-trait-method.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "selected")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn generic_trait_method_contracts_require_matching_binders_and_evidence() {
    let reordered = parse(
        "trait Left{} trait Right{} trait Pair{first<T,U>(self:&Self,left:T,right:U)->T where T:Left,U:Right;} struct Item{value:i64} impl Pair for Item{first<A,B>(self:&Item,left:A,right:B)->A where B:Right,A:Left{left}} main()->{()}",
    );
    validate::validate(&reordered).unwrap();

    for source in [
        "trait Mark{} trait Pick{pick<T>(self:&Self,value:T)->T where T:Mark;} struct Item{value:i64} impl Pick for Item{pick(self:&Item,value:i64)->i64{value}} main()->{()}",
        "trait Mark{} trait Pick{pick<T>(self:&Self,value:T)->T where T:Mark;} struct Item{value:i64} impl Pick for Item{pick<U>(self:&Item,value:U)->U{value}} main()->{()}",
        "trait Mark{} trait Pick{pick<T>(self:&Self,value:T)->T where T:Mark;} struct Item{value:i64} impl Pick for Item{pick<U>(self:&Item,value:U)->U where U:!Mark{value}} main()->{()}",
    ] {
        let errors = validate::validate(&parse(source)).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.code.as_deref() == Some("G0142")),
            "{errors:#?}",
        );
    }
}

#[test]
fn generic_trait_method_calls_require_where_evidence_and_exact_receiver_access() {
    let prelude = r#"
        trait Mark {}
        impl Mark for i64 {}
        trait Pick { pick<T>(self: &Self, value: T) -> T where T: Mark; }
        struct Item { value: i64 }
        impl Pick for Item {
            pick<U>(self: &Item, value: U) -> U where U: Mark { value }
        }
    "#;
    for (name, body, expected) in [
        (
            "missing-method-evidence.gr",
            "bad(item:Item)->Text{Pick::pick(&item, \"no evidence\")} main()->{()}",
            "no matching implementation",
        ),
        (
            "wrong-method-receiver-mode.gr",
            "bad(item:Item)->i64{Pick::pick(item, 42)} main()->{()}",
            "not a callable",
        ),
    ] {
        let errors = grandiose::compile_source_to_bytecode(name, &format!("{prelude}{body}"))
            .expect_err("an invalid generic trait-method call must be rejected");
        assert!(
            errors.iter().any(|error| {
                error.code.is_some() && error.span.is_some() && error.message.contains(expected)
            }),
            "{name}: {errors:#?}",
        );
    }
}

#[test]
fn const_generic_trait_method_binders_infer_and_specialize() {
    let source = r#"
        struct Token<const N: u32> { value: i64 }
        struct Reader { marker: i64 }
        trait Read {
            read<const N: u32>(self: &Self, token: Token<N>) -> i64;
        }
        impl Read for Reader {
            read<const M: u32>(self: &Reader, token: Token<M>) -> i64 { token.value }
        }
        answer(reader: Reader, token: Token<7>) -> i64 {
            Read::read(&reader, token)
        }
        selected() -> i64 {
            answer(Reader { marker: 0 }, Token { value: 42 })
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
            "const-generic-trait-method.gr",
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
fn qualified_methods_select_after_ground_gat_receiver_normalization() {
    let source = r#"
        struct Box<T> { value: T }
        struct Carrier { marker: i64 }
        trait Family { type Item<T>; }
        impl Family for Carrier { type Item<U> = Box<U>; }
        trait Read { read(self: &Self) -> i64; }
        impl Read for Box<i64> {
            read(self: &Box<i64>) -> i64 { self.value }
        }
        answer(value: <Carrier as Family>::Item<i64>) -> i64 {
            Read::read(&value)
        }
        selected() -> i64 { answer(Box { value: 42 }) }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "projected-trait-method-receiver.gr",
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
fn qualified_method_projection_selection_requires_exact_associated_evidence() {
    let source = r#"
        struct Box<T> { value: T }
        struct Carrier { marker: i64 }
        trait Family { type Item<T>; }
        trait Read { read(self: &Self) -> i64; }
        impl Read for Box<i64> { read(self: &Box<i64>) -> i64 { self.value } }
        bad(value: <Carrier as Family>::Item<i64>) -> i64 { Read::read(&value) }
        main() -> { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("unproven-projected-method.gr", source)
        .expect_err("an unproven associated receiver projection must be rejected");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error
                    .message
                    .contains("associated type projection is unresolved")
        }),
        "{errors:#?}",
    );
}

#[test]
fn qualified_methods_specialize_through_open_generic_impl_heads() {
    let source = r#"
        trait Mark {}
        impl Mark for i64 {}
        struct Box<T> { value: T }
        trait Select {
            select<T>(self: &Self, value: T) -> T where T: Mark;
        }
        impl<U> Select for Box<U> where U: Mark {
            select<T>(self: &Box<U>, value: T) -> T where T: Mark { value }
        }
        answer(item: Box<i64>) -> i64 { Select::select(&item, 42) }
        selected() -> i64 { answer(Box { value: 7 }) }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "open-generic-method-impl.gr",
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
fn open_generic_method_impl_heads_preserve_their_where_evidence() {
    let source = r#"
        trait Mark {}
        impl Mark for i64 {}
        struct Box<T> { value: T }
        trait Select { select<T>(self: &Self, value: T) -> T where T: Mark; }
        impl<U> Select for Box<U> where U: Mark {
            select<T>(self: &Box<U>, value: T) -> T where T: Mark { value }
        }
        bad(item: Box<Text>) -> i64 { Select::select(&item, 42) }
        main() -> { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("open-impl-missing-evidence.gr", source)
        .expect_err("an open impl head must retain its own where evidence");
    assert!(
        errors.iter().any(|error| {
            error.code.is_some()
                && error.span.is_some()
                && error.message.contains("no matching implementation")
        }),
        "{errors:#?}",
    );
}
