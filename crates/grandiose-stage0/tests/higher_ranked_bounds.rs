use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("higher-ranked-bounds@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"higher-ranked-bounds")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(), codegen_options: BTreeMap::new(),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

#[test]
fn universal_user_trait_evidence_forwards_through_functions_and_impls_at_o0_o2() {
    let source = r#"
        trait Marker { type Output; type Effects: EffectRow; }
        impl<'a> Marker for &'a i64 { type Output = i64; type Effects = {}; }
        trait Ready { type Item; fn take(value: Self) -> <Self as Ready>::Item; }
        struct Wrap<T> { value: T }
        impl<T> Ready for Wrap<T> where for<'a> &'a T: Marker<Output=i64,Effects={}> {
            type Item = T;
            fn take(value: Self) -> T { forward(value.value) }
        }
        fn require<T>(value: T) -> T where for<'a> &'a T: Marker<Output=i64,Effects={}> { value }
        fn ordinary<'a,T>(value: &'a T) -> &'a T where &'a T: Marker<Output=i64,Effects={}> { value }
        fn forward<T>(value: T) -> T where for<'b> &'b T: Marker<Output=i64,Effects={}> {
            let _ = ordinary(&value);
            require(value)
        }
        fn ready<T>(value: T) -> T where T: Ready { value }
        pub fn main() -> i64 {
            let wrapped = ready(Wrap { value: forward(42) });
            Ready::take(wrapped)
        }
    "#;
    for level in ["0", "2"] {
        let mut request = request(source);
        request.codegen_options.insert("optimization-level".into(), level.into());
        let artifact = StageZeroCompiler::new().compile(request)
            .unwrap_or_else(|error| panic!("O{level}: {:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn universal_user_traits_reject_static_only_evidence_and_wrong_equalities() {
    for implementation in [
        "impl Marker for &'static i64 { type Output = i64; }",
        "impl<'a> Marker for &'a i64 { type Output = u8; }",
    ] {
        let source = format!(r#"
            trait Marker {{ type Output; }}
            {implementation}
            fn require<T>(value: T) -> T where for<'a> &'a T: Marker<Output=i64> {{ value }}
            pub fn main() -> i64 {{ require(42) }}
        "#);
        let diagnostics = StageZeroCompiler::new().compile(request(&source)).expect_err("universal obligation must hold with its exact equality").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4140"), "{diagnostics:#?}");
        assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
    }
    let source = r#"
        effect Trace { note(); }
        trait Marker { type Effects: EffectRow; }
        impl<'a> Marker for &'a i64 { type Effects = {Trace}; }
        fn require<T>(value: T) -> T where for<'a> &'a T: Marker<Effects={}> { value }
        pub fn main() -> i64 { require(42) }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("quantified associated rows are exact").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4140"), "{diagnostics:#?}");
}

#[test]
fn universal_impl_requirements_are_checked_and_nested_regions_stay_distinct() {
    for source in [r#"
        trait Marker {}
        impl Marker for &'static i64 {}
        trait Ready {}
        struct Wrap<T> { value: T }
        impl<T> Ready for Wrap<T> where for<'a> &'a T: Marker {}
        fn require<T>(value: T) -> T where T: Ready { value }
        pub fn main() -> i64 { require(Wrap { value: 42 }).value }
    "#, r#"
        trait Rel<'a> {}
        impl<'a> Rel<'a> for &'a i64 {}
        trait Outer<'a> {}
        impl<'a> Outer<'a> for i64 where for<'b> &'b i64: Rel<'a> {}
        fn require<T>(value: T) -> T where for<'a> T: Outer<'a> { value }
        pub fn main() -> i64 { require(42) }
    "#] {
        let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("quantified impl requirements cannot be erased or capture an outer region").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4140" | "G4143")), "{diagnostics:#?}");
        assert!(!diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198"), "{diagnostics:#?}");
    }
}

#[test]
fn higher_ranked_shared_callable_bound_accepts_every_borrow_region() {
    let source = r#"
        fn answer() -> i64 { 42 }
        fn require<F>(body: F) -> i64
        where F: Use<[0,1]>, for<'a> &'a F: Fn<(),Output=i64,Effects={}> { 42 }
        pub fn main() -> i64 { require(answer) }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn higher_ranked_argument_region_cannot_be_satisfied_by_a_static_only_callable() {
    let source = r#"
        fn static_only(value: &'static i64) -> i64 { *value }
        fn require<F>(body: F) -> i64
        where F: Use<[0,1]>, for<'a> F: Fn<(&'a i64,),Output=i64,Effects={}> { 42 }
        pub fn main() -> i64 { require(static_only) }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("a single static region is not a universal proof").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| matches!(diagnostic.code, "G4166" | "G5017" | "G4160")),
        "rejection must come from the callable/lifetime obligation, not unsupported binder syntax: {diagnostics:#?}");
}

#[test]
fn higher_ranked_callable_is_instantiated_independently_for_a_rigid_argument_region() {
    let source = r#"
        fn read<'b>(value: &'b i64) -> i64 { *value }
        fn require<F>(body: F) -> F
        where for<'a> F: Fn<(&'a i64,),Output=i64,Effects={}> { body }
        pub fn main() -> i64 {
            let callback: for<'b> (&'b i64) -> i64 = read;
            let checked = require(callback);
            let value = 42;
            checked(&value)
        }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn universal_output_cannot_capture_the_fresh_input_region_in_an_outer_type_hole() {
    let source = r#"
        fn identity<'b>(value: &'b i64) -> &'b i64 { value }
        fn require<F, T>(body: F) -> F
        where for<'a> F: Fn<(&'a i64,),Output=T,Effects={}> { body }
        pub fn main() -> i64 {
            let callback: for<'b> (&'b i64) -> &'b i64 = identity;
            let checked = require(callback);
            let value = 42;
            *checked(&value)
        }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("T cannot depend on a newer universal region").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017" && diagnostic.message.contains("leak")), "{diagnostics:#?}");
}

#[test]
fn storing_a_quantified_function_cannot_erase_its_where_contract() {
    let source = r#"
        fn answer() -> i64 { 42 }
        fn require<F>(body: F) -> i64
        where F: Use<[0,1]>, for<'a> &'a F: Fn<(),Output=i64,Effects={}> { 42 }
        pub fn main() -> i64 {
            let escaped: (() -> i64) -> i64 = require;
            escaped(answer)
        }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("first-class erasure is not evidence").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4198" && diagnostic.message.contains("first-class")), "{diagnostics:#?}");
}

#[test]
fn a_generic_body_can_invoke_a_callback_from_its_universal_fn_evidence() {
    let source = r#"
        fn read<'b>(value: &'b i64) -> i64 { *value }
        fn invoke<'v, F>(body: F, value: &'v i64) -> i64
        where for<'a> F: Fn<(&'a i64,),Output=i64,Effects={}> { body(value) }
        pub fn main() -> i64 {
            let callback: for<'b> (&'b i64) -> i64 = read;
            let value = 42;
            invoke(callback, &value)
        }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn universal_body_evidence_preserves_input_to_output_borrow_provenance() {
    let source = r#"
        fn identity<'b>(value: &'b i64) -> &'b i64 { value }
        fn invoke<'v, F>(body: F, value: &'v i64) -> &'v i64
        where for<'a> F: Fn<(&'a i64,),Output = &'a i64,Effects={}> { body(value) }
        pub fn main() -> i64 {
            let callback: for<'b> (&'b i64) -> &'b i64 = identity;
            let value = 42;
            *invoke(callback, &value)
        }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn universal_body_evidence_does_not_extend_an_input_borrow_to_static() {
    let source = r#"
        fn bad<'v, F>(body: F, value: &'v i64) -> &'static i64
        where for<'a> F: Fn<(&'a i64,),Output = &'a i64,Effects={}> { body(value) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("universal evidence cannot lengthen the selected input borrow").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}

#[test]
fn universal_body_evidence_keeps_enclosing_lifetimes_rigid() {
    let source = r#"
        fn bad<'fixed, 'short, F>(body: F, fixed: &'fixed i64, short: &'short i64) -> i64
        where for<'a> F: Fn<(&'fixed i64,),Output=i64,Effects={}> { body(short) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source)).expect_err("a free enclosing region is not a callable-local binder").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}

#[test]
fn lexical_fn_evidence_preserves_free_input_and_output_regions() {
    for quantifier in ["", "for<'a>"] {
        let source = format!(r#"
            fn invoke<'fixed, F>(body: F, fixed: &'fixed i64) -> &'fixed i64
            where {quantifier} F: Fn<(&'fixed i64,),Output = &'fixed i64,Effects={{}}> {{ body(fixed) }}
            pub fn main() -> i64 {{ 42 }}
        "#);
        let artifact = StageZeroCompiler::new().compile(request(&source))
            .unwrap_or_else(|error| panic!("{quantifier}: {:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn ordinary_fn_body_evidence_keeps_enclosing_lifetimes_rigid() {
    let source = r#"
        fn bad<'fixed, 'short, F>(body: F, fixed: &'fixed i64, short: &'short i64) -> i64
        where F: Fn<(&'fixed i64,),Output=i64,Effects={}> { body(short) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source))
        .expect_err("ordinary lexical evidence does not own enclosing regions").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}

#[test]
fn structural_callable_values_keep_enclosing_lifetimes_rigid() {
    for binder in ["", "for<'a>"] {
        let source = format!(r#"
            fn bad<'fixed, 'short>(body: {binder} (&'fixed i64) -> i64, short: &'short i64) -> i64 {{ body(short) }}
            pub fn main() -> i64 {{ 42 }}
        "#);
        let diagnostics = StageZeroCompiler::new().compile(request(&source))
            .expect_err("a structural callable does not own its enclosing declaration regions").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{binder}: {diagnostics:#?}");
    }
}

#[test]
fn structural_callable_values_preserve_free_input_and_output_lifetimes() {
    let source = r#"
        fn identity<'v>(value: &'v i64) -> &'v i64 { value }
        fn invoke<'fixed>(body: (&'fixed i64) -> &'fixed i64, value: &'fixed i64) -> &'fixed i64 { body(value) }
        pub fn main() -> i64 { let value = 42; *invoke(identity, &value) }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn an_inferred_named_function_alias_retains_its_call_lifetime_relation() {
    let source = r#"
        fn identity<'v>(value: &'v i64) -> &'v i64 { value }
        pub fn main() -> i64 { let callback = identity; let value = 42; *callback(&value) }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn an_explicit_direct_call_lifetime_is_not_an_omitted_binder() {
    let source = r#"
        fn read<'v>(value: &'v i64) -> i64 { *value }
        fn bad<'fixed, 'short>(short: &'short i64) -> i64 { read<'fixed>(short) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source))
        .expect_err("an explicitly supplied lifetime is fixed at its application").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}

#[test]
fn callback_input_inference_cannot_hide_a_static_only_requirement() {
    let source = r#"
        fn static_only(value: &'static i64) -> i64 { *value }
        fn invoke<'v>(body: (&'v i64) -> i64, value: &'v i64) -> i64 { body(value) }
        fn bad<'short>(value: &'short i64) -> i64 { invoke(static_only, value) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source))
        .expect_err("callback contravariance must constrain the inferred call region").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}

#[test]
fn explicit_lifetime_arguments_are_preserved_even_when_absent_from_the_value_contract() {
    let source = r#"
        fn answer<'unused>() -> i64 { 42 }
        fn relay<'outer>() -> i64 { answer<'outer>() }
        pub fn main() -> i64 { relay<'static>() }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn explicit_inferred_call_lifetimes_follow_the_input_region() {
    let source = r#"
        fn identity<'v>(value: &'v i64) -> &'v i64 { value }
        fn relay<'outer>(value: &'outer i64) -> &'outer i64 { identity<'_>(value) }
        pub fn main() -> i64 { let value = 42; *relay(&value) }
    "#;
    let artifact = StageZeroCompiler::new().compile(request(source))
        .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn explicit_inferred_call_lifetimes_cannot_extend_the_input_region() {
    let source = r#"
        fn identity<'v>(value: &'v i64) -> &'v i64 { value }
        fn bad<'outer>(value: &'outer i64) -> &'static i64 { identity<'_>(value) }
        pub fn main() -> i64 { 42 }
    "#;
    let diagnostics = StageZeroCompiler::new().compile(request(source))
        .expect_err("an anonymous call region is inferred from evidence, not a lifetime extension").diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G5017"), "{diagnostics:#?}");
}
