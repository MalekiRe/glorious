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
        grandiose::compile_source_to_bytecode("trait-method-dispatch.glorious", source).unwrap();
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
fn qualified_trait_calls_in_dereferenced_assignment_destinations_are_normalized() {
    let source = r#"
        trait AddIndex { add(self: Self, other: Self) -> Self; }
        impl AddIndex for i64 {
            add(self: i64, other: i64) -> i64 { self + other }
        }
        struct Cell { value: i64 }
        slot<'a>(cell: &'a mut Cell, index: i64) -> &'a mut i64 {
            let _ = index;
            &mut cell.value
        }
        set(cell: &mut Cell, base: i64) -> () {
            *slot(cell, AddIndex::add(base, 2)) = 42;
            ()
        }
        selected() -> i64 {
            let cell = Cell { value: 0 };
            set(&mut cell, 0);
            cell.value
        }
        main() -> { () }
    "#;
    let artifact = grandiose::compile_source_to_bytecode(
        "trait-method-assignment-destination.glorious",
        source,
    )
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
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-trait-method.glorious",
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
fn bounded_symbolic_field_receivers_and_receiverless_results_defer_to_specialization() {
    let source = r#"
        trait Same { same(self: &Self, other: &Self) -> Bool; }
        impl Same for i64 {
            same(self: &i64, other: &i64) -> Bool { *self == *other }
        }
        impl<A> Same for (A,) where A: Same {
            same(self: &(A,), other: &(A,)) -> Bool {
                Same::same(&self.0, &other.0)
            }
        }

        trait Make { make() -> Self; }
        impl Make for i64 { make() -> i64 { 42 } }
        impl<A> Make for (A,) where A: Make {
            make() -> (A,) { (Make::make(),) }
        }
        impl<A, E> Make for Result<A, E> where A: Make {
            make() -> Result<A, E> { Result::Ok(Make::make()) }
        }

        equal_pair() -> Bool {
            let left = (42,);
            let right = (42,);
            Same::same(&left, &right)
        }
        make_pair() -> (i64,) { Make::make() }
        make_result() -> Result<i64, Text> { Make::make() }
        main() -> { equal_pair(); make_pair(); make_result(); () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "symbolic-bounded-trait-calls.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        verify(artifact).unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}

#[test]
fn receiverless_default_selection_uses_the_expected_result_type() {
    let source = r#"
        selected() -> i64 { Default::default() }
        main() -> () { () }
    "#;
    let artifact = grandiose::compile_source_to_bytecode(
        "receiverless-default-expected-type.glorious",
        source,
    )
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
        Value::I64(0),
    );
    let recovery_source = source.replace("main() -> () { () }", "main() -> i64 { selected() }");
    assert_eq!(
        grandiose::run_source(
            "receiverless-default-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(0),
    );
}

#[test]
fn trait_method_selection_canonicalizes_alias_impl_heads_and_results() {
    let source = r#"
        type AliasText = Text;

        trait AliasDefault { make() -> Self; }
        impl AliasDefault for AliasText {
            make() -> AliasText { "canonical" }
        }

        trait AliasRead { read(self: &Self) -> i64; }
        impl AliasRead for AliasText {
            read(self: &AliasText) -> i64 { 42 }
        }

        selected_default() -> Text { AliasDefault::make() }
        selected_read(value: AliasText) -> i64 { AliasRead::read(&value) }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "alias-trait-method-selection.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let function = |name: &str| {
            artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap() as u32
        };
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(function("selected_default"), vec![]).unwrap(),
            Value::Text("canonical".into()),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(
                function("selected_read"),
                vec![Value::Text("ignored".into())],
            )
            .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn receiverless_associated_method_reports_missing_result_evidence() {
    let source = r#"
        struct Missing { marker: i64 }
        selected() -> Missing { Default::default() }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode(
        "receiverless-default-missing-evidence.glorious",
        source,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains(
                "no `Default::default` implementation produces the expected result `Missing`",
            ) && error.span.is_some()
        }),
        "{errors:#?}"
    );

    let recovery_errors = grandiose::run_source(
        "receiverless-default-missing-evidence-recovery.glorious",
        source,
        vec![],
        &mut grandiose::eval::SystemHost::default(),
    )
    .unwrap_err();
    assert!(
        recovery_errors.iter().any(|error| {
            error.message.contains(
                "no `Default::default` implementation produces the expected result `Missing`",
            ) && error.span.is_some()
        }),
        "{recovery_errors:#?}"
    );
}

#[test]
fn dot_trait_calls_match_qualified_calls_and_infer_shared_receivers() {
    let source = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        impl Read for Item { read(self: &Item) -> i64 { self.value } }

        dotted(item: Item) -> i64 { item.read() }
        qualified(item: Item) -> i64 { Read::read(&item) }
        relay<T>(item: T) -> i64 where T: Read { item.read() }
        answer() -> i64 {
            dotted(Item { value: 10 }) +
            qualified(Item { value: 20 }) +
            relay(Item { value: 12 })
        }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "dot-trait-method.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
    let recovery_source = source.replace("main() -> () { () }", "main() -> i64 { answer() }");
    assert_eq!(
        grandiose::run_source(
            "dot-trait-method-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

#[test]
fn dot_trait_calls_report_missing_and_ambiguous_selection() {
    let missing = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        struct Other { value: i64 }
        impl Read for Item { read(self: &Item) -> i64 { self.value } }
        selected(other: Other) -> i64 { other.read() }
        main() -> () { () }
    "#;
    let errors =
        grandiose::compile_source_to_bytecode("dot-method-missing.glorious", missing).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("no trait method `read` matches receiver `Other`")
                && error.span.is_some()
        }),
        "{errors:#?}"
    );

    let ambiguous = r#"
        trait Left { select(self: &Self) -> i64; }
        trait Right { select(self: &Self) -> i64; }
        struct Item { value: i64 }
        impl Left for Item { select(self: &Item) -> i64 { 1 } }
        impl Right for Item { select(self: &Item) -> i64 { 2 } }
        selected(item: Item) -> i64 { item.select() }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("dot-method-ambiguous.glorious", ambiguous)
        .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("trait method `select` is ambiguous for receiver `Item`")
                && error
                    .note
                    .as_deref()
                    .is_some_and(|note| note.contains("`Left`") && note.contains("`Right`"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn dot_trait_calls_preserve_existing_borrows_and_owned_access() {
    let source = r#"
        trait Peek { peek(self: &Self) -> i64; }
        trait Touch { touch(self: &mut Self) -> i64; }
        trait Take { take(self: Self) -> i64; }
        struct Item { value: i64 }
        impl Peek for Item { peek(self: &Item) -> i64 { self.value } }
        impl Touch for Item { touch(self: &mut Item) -> i64 { self.value } }
        impl Take for Item { take(self: Item) -> i64 { self.value } }

        through_shared(item: &Item) -> i64 { item.peek() }
        through_unique(item: &mut Item) -> i64 { item.touch() }
        through_owned(item: Item) -> i64 { item.take() }
        answer() -> i64 {
            let shared = Item { value: 10 };
            let unique = Item { value: 20 };
            through_shared(&shared) +
            through_unique(&mut unique) +
            through_owned(Item { value: 12 })
        }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "dot-trait-receiver-access.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
    }
    let recovery_source = source.replace("main() -> () { () }", "main() -> i64 { answer() }");
    assert_eq!(
        grandiose::run_source(
            "dot-trait-receiver-access-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

#[test]
fn trait_calls_inside_generic_bodies_dispatch_from_ground_evidence() {
    let source = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        impl Read for Item {
            read(self: &Item) -> i64 { self.value }
        }
        relay<T>(value: &T) -> i64 where T: Read { Read::read(value) }
        selected() -> i64 {
            let item = Item { value: 42 };
            relay(&item)
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-body-trait-dispatch.glorious",
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
fn generic_body_trait_dispatch_requires_lexical_and_ground_evidence() {
    let missing_lexical = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        impl Read for Item { read(self: &Item) -> i64 { self.value } }
        bad<T>(value: &T) -> i64 { Read::read(value) }
        main() -> { () }
    "#;
    let missing_ground = r#"
        trait Read { read(self: &Self) -> i64; }
        struct Item { value: i64 }
        bad<T>(value: &T) -> i64 where T: Read { Read::read(value) }
        selected() -> i64 {
            let item = Item { value: 42 };
            bad(&item)
        }
        main() -> { () }
    "#;
    for (name, source, needle) in [
        (
            "generic-trait-missing-lexical.glorious",
            missing_lexical,
            "no ground",
        ),
        (
            "generic-trait-missing-ground.glorious",
            missing_ground,
            "no matching implementation",
        ),
    ] {
        let errors = grandiose::compile_source_to_bytecode(name, source)
            .expect_err("unproved generic trait dispatch compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(needle)),
            "{errors:#?}",
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
            "missing-method-evidence.glorious",
            "bad(item:Item)->Text{Pick::pick(&item, \"no evidence\")} main()->{()}",
            "no matching implementation",
        ),
        (
            "wrong-method-receiver-mode.glorious",
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
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "const-generic-trait-method.glorious",
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
        answer_dot(value: <Carrier as Family>::Item<i64>) -> i64 {
            value.read()
        }
        selected() -> i64 {
            answer(Box { value: 20 }) + answer_dot(Box { value: 22 })
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "projected-trait-method-receiver.glorious",
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
    let recovery_source = source.replace("main() -> { () }", "main() -> i64 { selected() }");
    assert_eq!(
        grandiose::run_source(
            "projected-dot-trait-method-recovery.glorious",
            &recovery_source,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

#[test]
fn trait_addition_infers_through_arithmetic_on_typed_locals() {
    let source = r#"
        left() -> usize { 4 }
        right() -> usize { 5 }
        selected() -> usize {
            let left_value = left();
            let right_value = right();
            left_value * 2 + right_value * 3
        }
        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("binary-result-trait-add.glorious", source).unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::U64(23),
    );
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
    let errors =
        grandiose::compile_source_to_bytecode("unproven-projected-method.glorious", source)
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
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "open-generic-method-impl.glorious",
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
    let errors =
        grandiose::compile_source_to_bytecode("open-impl-missing-evidence.glorious", source)
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

#[test]
fn divergent_first_match_arm_does_not_poison_later_operator_typing() {
    let source = r#"
        selected(value: Result<i64, ()>) -> i64 {
            let found = handle value {
                Result::Err(_) => unreachable(),
                Result::Ok(found) => found
            };
            if(found == 42) { found } else { 0 }
        }
        answer() -> i64 { selected(Result::Ok(42)) }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "divergent-match-operator-context.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let answer = artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verify(artifact).unwrap())
                .run(answer, vec![])
                .unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}
