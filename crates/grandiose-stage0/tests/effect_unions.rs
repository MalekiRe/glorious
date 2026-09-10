//! Language §10.2: a row union is not an equality between its operands.
use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("effect-unions@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"effect-unions")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

const SOURCE: &str = r#"
    effect Read { read() -> i64; }
    effect Offset { offset() -> i64; }
    fn read() -> i64 / Read { Read::read() }
    fn offset() -> i64 / Offset { Offset::offset() }
    fn combine<e1: EffectRow, e2: EffectRow>(first: () -> i64 / {|e1}, second: () -> i64 / {|e2})
        -> i64 / {|e1, e2, e1} { first() + second() }
    fn forward<e2: EffectRow, e1: EffectRow>(first: () -> i64 / {|e1}, second: () -> i64 / {|e2})
        -> i64 / {|e2, e1} { combine(first, second) }
    pub fn main() -> i64 {
        handle forward(read, offset) { Read::read(k) => k(40), Offset::offset(k) => k(2) }
    }
"#;

#[test]
fn contextual_callback_rows_are_inferred_from_their_own_bodies() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        effect Offset { offset() -> (); }
        fn read() -> i64 / Read { Read::read() }
        fn offset() / Offset { Offset::offset() }
        fn invoke<F,e: EffectRow>(body: F) -> i64 / {|e}
            where F: Fn<(),Output=i64,Effects=e> { body() }
        pub fn main() -> i64 {
            handle invoke({ BODY }) { Read::read() => 42, Offset::offset() => () }
        }
    "#;
    for body in ["Read::read()", "read()", "offset(); read()",
        "Offset::offset(); Read::read()", "invoke({ offset(); read() })",
        "handle read() { Read::read() => 42 }",
        "handle read() { Read::read(k) => k(42) }",
        "offset(); handle read() { Read::read(k) => k(42) }",
        "let task = () -> i64 / Read { read() }; task()"] {
        for level in ["0", "2"] {
            let mut input = request(&source.replace("BODY", body));
            input.codegen_options.insert("optimization-level".into(), level.into());
            let artifact = StageZeroCompiler::new().compile(input)
                .unwrap_or_else(|error| panic!("{body} O{level}: {error:#?}")).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn contextual_rows_wait_for_independent_callback_input_evidence() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        fn relay<e: EffectRow>(body: (() -> i64 / {|e}) -> i64 / {|e}, input: () -> i64 / {|e})
            -> i64 / {|e} { body(input) }
        pub fn main() -> i64 {
            handle relay({ f => f() }, { Read::read() }) { Read::read() => 42 }
        }
    "#;
    for level in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), level.into());
        let artifact = StageZeroCompiler::new().compile(input).unwrap_or_else(|error| panic!("{error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn independent_contextual_rows_and_symbolic_projections_remain_distinct() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        effect Offset { offset() -> (); }
        fn read() -> i64 / Read { Read::read() }
        fn offset() / Offset { Offset::offset() }
        fn both<F,G,e1: EffectRow,e2: EffectRow>(first: F, second: G) -> i64 / {|e1,e2}
            where F: Fn<(),Output=i64,Effects=e1>, G: Fn<(),Output=(),Effects=e2> {
            second(); first()
        }
        fn invoke<F>(body: F) -> i64 / { <F as Fn<()>>::Effects }
            where F: Fn<(),Output=i64> { body() }
        fn forward<F>(body: F) -> i64 / { <F as Fn<()>>::Effects }
            where F: Fn<(),Output=i64> { invoke({ body() }) }
        pub fn main() -> i64 {
            handle EXPRESSION { Read::read() => 42, Offset::offset() => () }
        }
    "#;
    for expression in ["both({ read() }, { offset() })", "invoke({ read() })", "forward(read)"] {
        let artifact = StageZeroCompiler::new().compile(request(&source.replace("EXPRESSION", expression)))
            .unwrap_or_else(|error| panic!("{expression}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn inferred_callback_rows_keep_handler_and_nested_callable_boundaries() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        fn read() -> i64 / Read { Read::read() }
        fn pure<F>(body: F) -> i64 where F: Fn<(),Output=i64,Effects={}> { body() }
        pub fn main() -> i64 { let task = { => { BODY } }; pure(task) }
    "#;
    for body in ["handle read() { Read::read() => 42 }",
        "let inner = () -> i64 / Read { read() }; 42",
        "let inner = { => read() }; 42"] {
        let artifact = StageZeroCompiler::new().compile(request(&source.replace("BODY", body)))
            .unwrap_or_else(|error| panic!("{body}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn inferred_callback_effects_cannot_borrow_permission_or_override_annotations() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        fn invoke<F,e: EffectRow>(body: F) -> i64 / {|e}
            where F: Fn<(),Output=i64,Effects=e> { body() }
        fn explicit<F>(body: F) -> i64 / Read
            where F: Fn<(),Output=i64,Effects=Read> { body() }
        pub fn main() -> i64 { EXPRESSION }
    "#;
    for expression in ["invoke({ Read::read() })",
        "handle { let task = () -> i64 { Read::read() }; task() } { Read::read() => 42 }",
        "handle explicit(() -> i64 { Read::read() }) { Read::read() => 42 }"] {
        let rejected = StageZeroCompiler::new().compile(request(&source.replace("EXPRESSION", expression)))
            .expect_err("inference cannot authorize an unadmitted effect or change an explicit row");
        assert!(rejected.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G4155" | "G4113")), "{rejected:#?}");
    }
}

#[test]
fn inferred_rows_subtract_only_the_expressions_exact_handler_coverage() {
    let source = r#"#![no_std]
        effect Read { read() -> i64; }
        effect Many { first() -> i64; second() -> i64; }
        trait Source {
            type Effects: EffectRow;
            fn read(value: Self) -> i64 / { <Self as Source>::Effects };
        }
        impl Source for i64 {
            type Effects = {Read};
            fn read(value: i64) -> i64 / Read { Read::read() }
        }
        fn many() -> i64 / Many { Many::first() }
        fn pure<F>(body: F) -> i64 where F: Fn<(),Output=i64,Effects={}> { body() }
        pub fn main() -> i64 { let task = { => { BODY } }; pure(task) }
    "#;
    for body in ["handle Source::read(0) { Read::read() => 42 }",
        "handle Many::first() { Many::first() => 42 }",
        "handle { handle many() { Many::first() => 42 } } { Many::second() => 42 }"] {
        let artifact = StageZeroCompiler::new().compile(request(&source.replace("BODY", body)))
            .unwrap_or_else(|error| panic!("{body}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
    for body in ["handle many() { Many::first() => 42 }",
        "Many::first(); handle 42 { Many::first() => 42, Many::second() => 42 }"] {
        let error = StageZeroCompiler::new().compile(request(&source.replace("BODY", body)))
            .expect_err("a partial or later handler cannot discharge the earlier call row");
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4168"), "{error:#?}");
    }
}

#[test]
fn independent_callback_rows_union_and_survive_reordered_generic_forwarding() {
    let outcome = StageZeroCompiler::new().compile(request(SOURCE)).unwrap();
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn explicit_row_arguments_and_typed_closure_unions_preserve_every_operand() {
    for source in [
        SOURCE.replace("forward(read, offset)", "forward<{Offset}, {Read}>(read, offset)"),
        SOURCE.replace("{|e2, e1} { combine(first, second) }", "{|e2, e1} { let callback = () -> i64 / {|e1,e2} { combine(first, second) }; callback() }"),
        SOURCE.replace("pub fn main()", "trait Joined<e1: EffectRow,e2: EffectRow> { type Effects: EffectRow = {|e1,e2}; } struct Value {} impl<e1: EffectRow,e2: EffectRow> Joined<{|e1},{|e2}> for Value {} fn projected() -> i64 / {| <Value as Joined<{Read},{Offset}>>::Effects} { combine(read, offset) } pub fn main()")
            .replace("forward(read, offset)", "projected()"),
    ] {
        let artifact = StageZeroCompiler::new().compile(request(&source)).unwrap().artifact.unwrap();
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn union_permission_does_not_erase_an_omitted_operand() {
    let source = SOURCE.replace("-> i64 / {|e2, e1} { combine", "-> i64 / {|e1} { combine");
    let error = StageZeroCompiler::new().compile(request(&source)).expect_err("e2 is not permitted");
    assert!(error.diagnostics().iter().any(|d| d.code == "G4155"), "{error:?}");
}

#[test]
fn associated_row_union_matches_the_exact_subject_in_either_order() {
    let source = r#"#![no_std]
        effect First { [1,1] first() -> i64; }
        effect Second { [1,1] second() -> i64; }
        trait Source {
            type Effects: EffectRow;
            fn read(value: &Self) -> i64 / { | <Self as Source>::Effects };
        }
        struct A {} struct B {}
        impl Source for A { type Effects = {First}; fn read(value: &Self) -> i64 / First { First::first() } }
        impl Source for B { type Effects = {Second}; fn read(value: &Self) -> i64 / Second { Second::second() } }
        fn both<I,J>(left: &I, right: &J) -> i64 / { | <I as Source>::Effects, <J as Source>::Effects }
            where I: Source, J: Source { Source::read(right); Source::read(left) }
        pub fn main() -> i64 {
            let a = A {}; let b = B {};
            let result = handle both(&a, &b) { First::first() with k => k(42), Second::second() with k => k(2) };
            let A {} = a; let B {} = b; result
        }
    "#;
    for level in ["0", "2"] {
        for source in [source.to_owned(), source.replace("<I as Source>::Effects, <J as Source>::Effects", "<J as Source>::Effects, <I as Source>::Effects")] {
            let mut input = request(&source);
            input.codegen_options.insert("optimization-level".into(), level.into());
            let artifact = StageZeroCompiler::new().compile(input).unwrap_or_else(|error| panic!("{error:#?}")).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
    let rejected = source.replace("<I as Source>::Effects, <J as Source>::Effects", "<I as Source>::Effects");
    let failure = StageZeroCompiler::new().compile(request(&rejected)).expect_err("J's row cannot be erased");
    assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4155"), "{failure:#?}");
}

#[test]
fn union_operands_are_inferred_from_later_arguments_before_solving_the_union() {
    let source = SOURCE.replace("pub fn main()", r#"
        fn both() -> i64 / {Read, Offset} { read() + offset() }
        fn constrained<e1: EffectRow, e2: EffectRow>(
            both: () -> i64 / {|e1,e2}, first: () -> i64 / {|e1}, second: () -> i64 / {|e2})
            -> i64 / {|e1,e2} { first(); second(); both() }
        pub fn main()"#).replace("handle forward(read, offset)", "handle constrained(both, read, offset)");
    let outcome = StageZeroCompiler::new().compile(request(&source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn an_unknown_union_partition_is_an_ambiguity_not_an_arbitrary_split() {
    let source = SOURCE.replace("pub fn main()", r#"
        fn both() -> i64 / {Read, Offset} { read() + offset() }
        fn ambiguous<e1: EffectRow, e2: EffectRow>(both: () -> i64 / {|e1,e2})
            -> i64 / {|e1,e2} { both() }
        pub fn main()"#).replace("handle forward(read, offset)", "handle ambiguous(both)");
    let error = StageZeroCompiler::new().compile(request(&source)).expect_err("no unique operand split");
    assert!(error.diagnostics().iter().any(|d| d.class == grandiose_stage0::DiagnosticClass::Source), "{error:?}");
}

#[test]
fn coherence_rejects_overlapping_union_heads_and_keeps_operand_correlations() {
    for (second, overlap) in [
        ("impl Gate<{Read}, {Read}, {}> for Value {}", true),
        ("impl Gate<{Read}, {}, {Read}> for Value {}", true),
        ("impl Gate<{Read}, {}, {}> for Value {}", false),
        ("impl Gate<{}, {Read}, {}> for Value {}", false),
    ] {
        let source = format!(r#"
            effect Read {{ read() -> i64; }}
            trait Gate<all: EffectRow, left: EffectRow, right: EffectRow> {{}}
            struct Value {{}}
            impl<e1: EffectRow,e2: EffectRow> Gate<{{|e1,e2}}, {{|e1}}, {{|e2}}> for Value {{}}
            {second}
            pub fn main() -> i64 {{42}}
        "#);
        let result = StageZeroCompiler::new().compile(request(&source));
        if overlap {
            let error = result.expect_err("a concrete overlap witness exists");
            assert!(error.diagnostics().iter().any(|d| d.message.contains("overlap")), "{error:?}");
        } else {
            assert_eq!(result.unwrap().artifact.unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn trait_row_union_matching_uses_later_relation_arguments() {
    let source = r#"
        effect Read { read() -> i64; }
        effect Offset { offset() -> i64; }
        trait Rows<all: EffectRow, left: EffectRow, right: EffectRow> { type Output; }
        struct Value {}
        impl<e1: EffectRow,e2: EffectRow> Rows<{|e1,e2}, {|e1}, {|e2}> for Value { type Output = i64; }
        pub fn main() -> <Value as Rows<{Read,Offset}, {Read}, {Offset}>>::Output { 42 }
    "#;
    let result = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(result.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn selected_trait_methods_materialize_all_independent_row_operands() {
    let source = r#"
        effect Read { read() -> i64; }
        effect Offset { offset() -> i64; }
        trait Rows<all: EffectRow, left: EffectRow, right: EffectRow> { fn answer(receiver: Self) -> i64; }
        struct Value {}
        impl<e1: EffectRow,e2: EffectRow> Rows<{|e1,e2}, {|e1}, {|e2}> for Value {
            fn answer(receiver: Self) -> i64 { 42 }
        }
        pub fn main() -> i64 { Rows<{Read,Offset}, {Read}, {Offset}>::answer(Value {}) }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source)).unwrap().artifact.unwrap();
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn coherence_unifies_fixed_effect_arguments_before_comparing_union_membership() {
    let source = r#"
        effect Trace<T> { trace(T); }
        trait Gate<e: EffectRow> {}
        struct Value {}
        impl<T,e: EffectRow> Gate<{Trace<T> | e}> for Value {}
        impl Gate<{Trace<i64>}> for Value {}
        pub fn main() -> i64 {42}
    "#;
    let error = StageZeroCompiler::new().compile(request(source)).expect_err("T=i64 and e={} witness overlap");
    assert!(error.diagnostics().iter().any(|d| d.message.contains("overlap")), "{error:?}");
}
