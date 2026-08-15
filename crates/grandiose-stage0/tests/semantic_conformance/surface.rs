use super::*;

#[test]
fn semantic_only_struct_and_enum_are_nominal_declaration_spellings() {
    for keyword in ["class", "union", "record", "variant"] {
        let package = PackageKey(format!("invalid-{keyword}@0.1.0"));
        let source = format!("{keyword} Invalid {{}}");
        let file = FileKey::new(
            &package,
            LogicalPath::parse("src/main.glorious").unwrap().as_str(),
        );
        let lexed = LexedFile::lex(file, &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        assert!(
            scan.declarations.is_empty(),
            "{keyword} became a nominal declaration: {scan:#?}"
        );
        assert!(
            scan.diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G2003"),
            "{keyword} was not rejected as a top-level declaration: {scan:#?}"
        );
    }

    let source = concat!(
        "struct Pair { left: i64, right: i64 } ",
        "enum Choice { Pair(Pair), Empty } ",
        "pub main() -> i64 { ",
        "handle Choice::Pair(Pair { left: 40, right: 2 }) { ",
        "Choice::Pair(Pair { left: left, right: right }) => left + right, ",
        "Choice::Empty => 0 } }",
    );
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_canonical_callable_surface_and_compact_labels_execute() {
    let source = r#"
        effect Exit { exit(value: i64) -> i64; }
        relay(value: i64) -> i64 { value }
        pub main() -> i64 {
            @done: i64 {
                handle Exit::exit(relay(41)) {
                    Exit::exit(value) => @done(value + 1)
                }
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_callable_omission_spellings_are_semantically_equivalent() {
    for declaration in [
        "touch() -> { () }",
        "touch() -> () { () }",
        "touch() -> / {} { () }",
        "touch() -> () / {} { () }",
    ] {
        let source = format!("{declaration} pub main() -> i64 {{ touch(); 42 }}");
        let outcome = StageZeroCompiler::new()
            .compile(request(&source))
            .unwrap_or_else(|error| panic!("{declaration}: {error:#?}"));
        assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn semantic_named_function_implicit_labels_are_fresh_per_activation() {
    let source = r#"
        descend(value: i64) -> i64 {
            handle value {
                0 => @descend(40),
                _ => descend(value - 1) + 1,
            }
        }
        pub main() -> i64 { descend(2) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_generic_labels_are_diverging_callable_values() {
    let source = r#"
        escape<L>(exit: L, value: i64) -> !
        where L: Label<i64>
        {
            exit(value)
        }
        pub main() -> i64 {
            @done: i64 { escape(@done, 42) }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_label_generic_effects_route_only_with_their_brand() {
    let accepted = r#"
        effect Route<L> where L: Label<i64> { exit(value: i64) -> !; }
        route<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            handle Route<L>::exit(value) {
                Route<L>::exit(routed) => destination(routed)
            }
        }
        pub main() -> i64 { @done: i64 { route(@done, 42) } }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = r#"
        effect Route<L> where L: Label<i64> { exit(value: i64) -> !; }
        bad<L, M>(left: L, right: M) -> i64
        where L: Label<i64>, M: Label<i64>
        {
            handle Route<L>::exit(41) {
                Route<M>::exit(value) => value
            }
        }
        pub main() -> i64 {
            @left: i64 { @right: i64 { bad(@left, @right) } }
        }
    "#;
    assert_semantic_rejection(
        rejected,
        "a handler cannot intercept another label brand",
        &[
            &["effect", "protocol"],
            &["row", "unhandled", "brand", "instance"],
        ],
    );
}

#[test]
fn semantic_nested_generic_labels_rejoin_after_refutable_forwarding_and_completion() {
    let source = r#"
        escape<L>(destination: L, value: i64) -> !
        where L: Label<i64>
        {
            destination(value)
        }
        effect Ask { [1, 1] ask(value: i64) -> i64; }
        pub main() -> i64 {
            handle {
                @outer: i64 {
                    @inner: i64 {
                        handle {
                            handle Ask::ask(1) {
                                Ask::ask(0) with k => k(0),
                            }
                        } {
                            Ask::ask(value) => escape(@inner, value + 41),
                        }
                    }
                }
            } {
                value => value + 100,
            }
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 142);
}

#[test]
fn semantic_control_names_are_ordinary_source_bindings() {
    let source = r#"
        if(value: i64) -> i64 { value }
        else(value: i64) -> i64 { value }
        and(value: i64) -> i64 { value }
        or(value: i64) -> i64 { value }
        not(value: i64) -> i64 { value }
        match(value: i64) -> i64 { value }
        loop(value: i64) -> i64 { value }
        for(value: i64) -> i64 { value }
        break(value: i64) -> i64 { value }
        continue(value: i64) -> i64 { value }
        return(value: i64) -> i64 { value }
        yield(value: i64) -> i64 { value }
        await(value: i64) -> i64 { value }
        fail(value: i64) -> i64 { value }
        pub main() -> i64 {
            let v01 = if(42);
            let v02 = else(v01);
            let v03 = and(v02);
            let v04 = or(v03);
            let v05 = not(v04);
            let v06 = match(v05);
            let v07 = loop(v06);
            let v08 = for(v07);
            let v09 = break(v08);
            let v10 = continue(v09);
            let v11 = return(v10);
            let v12 = yield(v11);
            let v13 = await(v12);
            fail(v13)
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_contextual_blocks_follow_fn_constraints_not_names() {
    let source = r#"
        delayed<T>(body: T) -> i64
        where T: Fn<(), Output = i64>
        {
            body()
        }
        eager(value: i64) -> i64 { value }
        pub main() -> i64 {
            delayed() { 21 } + eager({ 21 })
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_source_defined_conditional_is_an_ordinary_selector() {
    let source = r#"
        if<F, G>(condition: Bool, first: F, second: G) -> i64
        where F: Fn<(), Output = i64>, G: Fn<(), Output = i64>
        {
            handle condition {
                true => first(),
                false => second(),
            }
        }
        pub main() -> i64 {
            let captured = 42;
            if(
                true,
                () -> i64 { captured },
                () -> i64 { 0 },
            )
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_capture_free_callable_uses_unit_environment() {
    let source = r#"
        invoke<F>(body: F) -> i64
        where
            F: Fn<(), Output = i64>,
            F: RunsIn<(), (), Output = i64, After = ()>
        {
            body()
        }
        pub main() -> i64 { invoke(() -> i64 { 42 }) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_named_callable_uses_compiler_generated_unit_runs_in_evidence() {
    let source = r#"
        apply<F>(body: F) -> i64
        where
            F: Fn<(), Output = i64>,
            F: RunsIn<(), (), Output = i64, After = ()>
        {
            body()
        }
        answer() -> i64 { 42 }
        pub main() -> i64 { apply(answer) }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_capturing_callable_runs_in_its_compiler_generated_environment() {
    let source = r#"
        invoke<E, S, F>(body: F) -> i64
        where
            E: Environment<'static>,
            S: Environment<'static>,
            F: Fn<(), Output = i64>,
            F: RunsIn<E, (), Output = i64, After = S>
        {
            body()
        }
        pub main() -> i64 {
            let captured = 41;
            invoke(() -> i64 { captured + 1 })
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_runs_in_borrowed_access_matches_sealed_capture_authority() {
    let source = r#"
        observe<E, F>(body: F) -> i64
        where
            E: Environment<'static>,
            F: Fn<(), Output = i64>,
            F: RunsIn<&'static E, (), Output = i64, After = E>
        {
            body()
        }

        update<E, F>(body: F) -> i64
        where
            E: Environment<'static>,
            F: Fn<(), Output = i64>,
            F: RunsIn<&'static mut E, (), Output = i64, After = E>
        {
            body()
        }

        pub main() -> i64 {
            let observed = 40;
            let updated = 1;
            observe(() -> i64 { observed })
                + update(() -> i64 { updated = updated + 1; updated })
        }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn semantic_shared_runs_in_cannot_claim_a_moving_environment() {
    let source = r#"
        observe<E, F>(body: F) -> i64
        where
            E: Environment<'static>,
            F: Fn<(), Output = i64>,
            F: RunsIn<&'static E, (), Output = i64, After = E>
        {
            body()
        }

        pub main() -> i64 {
            let moved = 42;
            observe(() -> i64 { move moved })
        }
    "#;
    assert_semantic_rejection(
        source,
        "shared RunsIn cannot manufacture moving environment evidence",
        &[&["RunsIn"], &["environment", "sealed", "evidence"]],
    );
}

#[test]
fn semantic_runs_in_access_is_expressed_with_ordinary_types() {
    let source = r#"
        owned<E, F, S>(body: F) ->
        where F: RunsIn<E, (), After = S>
        {}

        shared<'e, E, F, S>(body: F) ->
        where F: RunsIn<&'e E, (), After = S>
        {}

        unique<'e, E, F, S>(body: F) ->
        where F: RunsIn<&'e mut E, (), After = S>
        {}

        pub main() -> i64 { 42 }
    "#;
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}
