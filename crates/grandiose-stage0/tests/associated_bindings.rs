use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("associated-bindings@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"associated-bindings")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

const IMPLEMENTATIONS: &str = r#"
    trait Source { type Item; }
    struct Number {}
    struct Wrong {}
    impl Source for Number { type Item = i64; }
    impl Source for Wrong { type Item = u32; }
    trait Selected { fn answer(value: &Self) -> i64; }
    struct Wrapper<T> { item: T }
    impl<T> Selected for Wrapper<T> where T: Source<Item = i64> {
        fn answer(value: &Self) -> i64 { 42 }
    }
"#;

#[test]
fn concrete_gat_reference_elements_infer_call_lifetimes_before_array_matching() {
    let declarations = "trait View { type Item<'a>; } impl View for i64 { type Item<'a> = &'a i64; } fn keep<'a>(items: [<i64 as View>::Item<'a>;2]) -> [<i64 as View>::Item<'a>;2] { items }";
    for body in [
        "let a:i64=20; let b:i64=22; let items:[&i64;2]=[&a,&b]; let [a,b]=keep(items); *a + *b",
        "let a:i64=20; let b:i64=22; let [a,b]=keep([&a,&b]); *a + *b",
    ] {
        let source = format!("{declarations} pub fn main() -> i64 {{ {body} }}");
        for optimization in ["0", "2"] {
            let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
                .unwrap_or_else(|error| panic!("{source}\n{:#?}", error.diagnostics())).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        }
    }
}

#[test]
fn implementation_associated_equalities_admit_matching_items() {
    let source = format!("{IMPLEMENTATIONS} pub fn main() -> i64 {{ let value = Wrapper {{ item: Number {{}} }}; Selected::answer(&value) }}");
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
            .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn implementation_associated_equalities_reject_nonmatching_items() {
    let source = format!("{IMPLEMENTATIONS} pub fn main() -> i64 {{ let value = Wrapper {{ item: Wrong {{}} }}; Selected::answer(&value) }}");
    let error = StageZeroCompiler::new().compile(request(&source, "0"))
        .expect_err("an associated equality is an implementation obligation, not documentation");
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4169"), "{:#?}", error.diagnostics());
}

#[test]
fn implementation_equalities_are_available_in_generic_callers_without_leaking() {
    let good = format!(r#"{IMPLEMENTATIONS}
        fn delegate<T>(value: &Wrapper<T>) -> i64 where T: Source<Item=i64> {{ Selected::answer(value) }}
        pub fn main() -> i64 {{ let value = Wrapper {{ item: Number {{}} }}; delegate(&value) }}
    "#);
    let artifact = StageZeroCompiler::new().compile(request(&good, "0"))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    let bad = format!(r#"{IMPLEMENTATIONS}
        fn delegate<T>(value: &Wrapper<T>) -> i64 where T: Source<Item=i64> {{ Selected::answer(value) }}
        fn unbounded<T>(value: &Wrapper<T>) -> i64 where T: Source {{ Selected::answer(value) }}
        pub fn main() -> i64 {{ let value = Wrapper {{ item: Number {{}} }}; delegate(&value) }}
    "#);
    let error = StageZeroCompiler::new().compile(request(&bad, "0"))
        .expect_err("a different body cannot inherit a previous body's associated equality");
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4169"), "{:#?}", error.diagnostics());
}

#[test]
fn implementation_bindings_keep_inherited_items_gat_arguments_and_effect_kinds() {
    for (declarations, accepted, rejected) in [
        (r#"
            trait Source { type Item; }
            trait Child: Source {}
            struct Number {} struct Wrong {}
            impl Source for Number { type Item = i64; }
            impl Source for Wrong { type Item = u32; }
            impl Child for Number {} impl Child for Wrong {}
            trait Selected { fn answer(value: &Self) -> i64; }
            struct Wrapper<T> { item: T }
            impl<T> Selected for Wrapper<T> where T: Child<Item=i64> { fn answer(value: &Self) -> i64 { 42 } }
        "#, "Number", "Wrong"),
        (r#"
            trait Source { type Item<T>; }
            struct Number {} struct Wrong {}
            impl Source for Number { type Item<T> = T; }
            impl Source for Wrong { type Item<T> = u32; }
            trait Selected { fn answer(value: &Self) -> i64; }
            struct Wrapper<T> { item: T }
            impl<T> Selected for Wrapper<T> where T: Source<Item<i64>=i64> { fn answer(value: &Self) -> i64 { 42 } }
        "#, "Number", "Wrong"),
        (r#"
            effect Ask { ask() -> i64; }
            trait Source { type Effects: EffectRow; }
            struct Number {} struct Wrong {}
            impl Source for Number { type Effects = {}; }
            impl Source for Wrong { type Effects = {Ask}; }
            trait Selected { fn answer(value: &Self) -> i64; }
            struct Wrapper<T> { item: T }
            impl<T> Selected for Wrapper<T> where T: Source<Effects={}> { fn answer(value: &Self) -> i64 { 42 } }
        "#, "Number", "Wrong"),
    ] {
        for optimization in ["0", "2"] {
            let good = format!("{declarations} pub fn main() -> i64 {{ let value = Wrapper {{ item: {accepted} {{}} }}; Selected::answer(&value) }}");
            let artifact = StageZeroCompiler::new().compile(request(&good, optimization))
                .unwrap_or_else(|error| panic!("{good}: {:#?}", error.diagnostics())).artifact.unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            let bad = format!("{declarations} pub fn main() -> i64 {{ let value = Wrapper {{ item: {rejected} {{}} }}; Selected::answer(&value) }}");
            let error = StageZeroCompiler::new().compile(request(&bad, optimization))
                .expect_err("selection must prove the named associated item equality");
            assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4169"), "{:#?}", error.diagnostics());
        }
    }
}

#[test]
fn imported_implementation_bindings_preserve_selection_obligations() {
    let library = r#"
        pub trait Source { type Item; }
        pub struct Number {} pub struct Wrong {}
        pub impl Source for Number { type Item = i64; }
        pub impl Source for Wrong { type Item = u32; }
        pub trait Selected { fn answer(value: &Self) -> i64; }
        pub struct Wrapper<T> { pub item: T }
        pub impl<T> Selected for Wrapper<T> where T: Source<Item=i64> {
            fn answer(value: &Self) -> i64 { 42 }
        }
    "#;
    for optimization in ["0", "2"] {
        for (item, accepted) in [("Number", true), ("Wrong", false)] {
            let source = format!("use selection::*; pub fn main() -> i64 {{ let value = Wrapper {{ item: {item} {{}} }}; Selected::answer(&value) }}");
            let mut request = request(&source, optimization);
            request.sources.push(SourceInput::new(PackageKey("selection@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(), library.as_bytes()));
            let result = StageZeroCompiler::new().compile(request);
            if accepted {
                let artifact = result.unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
                assert_eq!(artifact.run_i64().unwrap(), 42);
                assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            } else {
                let error = result.expect_err("imported equality must remain a selection obligation");
                assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4169"), "{:#?}", error.diagnostics());
            }
        }
    }
}
