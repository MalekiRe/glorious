use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

fn request(source: &str, level: &str) -> CompilationRequest {
    let package = PackageKey("projection-normalization@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"projection-normalization")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), level.into())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for level in ["0", "2"] {
        let artifact = StageZeroCompiler::new()
            .compile(request(source, level))
            .unwrap_or_else(|error| panic!("O{level}: {source}\n{:#?}", error.diagnostics()))
            .artifact
            .unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

fn rejects(source: &str, codes: &[&str]) {
    for level in ["0", "2"] {
        let failure = StageZeroCompiler::new()
            .compile(request(source, level))
            .expect_err("invalid lexical projection was accepted");
        assert!(
            failure
                .diagnostics()
                .iter()
                .any(|diagnostic| codes.contains(&diagnostic.code)),
            "O{level}: {source}\n{:#?}",
            failure.diagnostics()
        );
    }
}

#[test]
fn ordinary_generic_function_normalizes_structural_projection_with_lexical_evidence() {
    accepts(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        trait Family { type Item; }
        impl<T> Family for Wrapper<T> where T: Mark { type Item = T; }
        fn forward<T>(value: T) -> <Wrapper<T> as Family>::Item where T: Mark { value }
        pub fn main() -> i64 { forward<i64>(42) }
    "#,
    );
}

#[test]
fn structural_projection_normalization_reaches_mutable_generic_arguments() {
    accepts(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        struct Cell<T> { value: T }
        trait Family { type Item; }
        impl<T> Family for Wrapper<T> where T: Mark { type Item = T; }
        fn fill<T>(slot: &mut Cell<<Wrapper<T> as Family>::Item>, value: T) where T: Mark {
            slot.value = value;
        }
        pub fn main() -> i64 { let mut slot = Cell { value: 0 }; fill<i64>(&mut slot, 42); slot.value }
    "#,
    );
}

#[test]
fn inferred_generic_calls_revisit_projections_after_argument_substitution() {
    accepts(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        struct Cell<T> { value: T }
        trait Family { type Item; }
        impl<T> Family for Wrapper<T> where T: Mark { type Item = T; }
        fn consume<G>(owner: &G, slot: &mut Cell<<G as Family>::Item>, value: <G as Family>::Item)
            where G: Family { slot.value = value; }
        fn forward<T>(owner: &Wrapper<T>, slot: &mut Cell<T>, value: T) where T: Mark {
            consume(owner, slot, value)
        }
        pub fn main() -> i64 {
            let owner = Wrapper { value: 0 }; let mut slot = Cell { value: 0 };
            forward(&owner, &mut slot, 42); slot.value
        }
    "#,
    );
}

#[test]
fn structural_rows_normalize_inside_callable_parameters_and_invocations() {
    accepts(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        effect Read { read() -> i64; }
        trait Family { type Effects: EffectRow; }
        impl<T> Family for Wrapper<T> where T: Mark { type Effects = {Read}; }
        fn read() -> i64 / Read { Read::read() }
        fn invoke<T>(job: () -> i64 / {<Wrapper<T> as Family>::Effects}) -> i64
            / {<Wrapper<T> as Family>::Effects} where T: Mark { job() }
        pub fn main() -> i64 { handle invoke<i64>(read) { Read::read() => 42 } }
    "#,
    );
}

#[test]
fn structural_projection_prerequisites_do_not_leak_to_another_declaration() {
    rejects(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        trait Family { type Item; }
        impl<T> Family for Wrapper<T> where T: Mark { type Item = T; }
        fn valid<T>(value: T) -> <Wrapper<T> as Family>::Item where T: Mark { value }
        fn invalid<T>(value: T) -> <Wrapper<T> as Family>::Item { value }
        pub fn main() -> i64 { valid<i64>(42) }
    "#,
        &["G4190", "G4303"],
    );
    rejects(
        r#"#![no_std]
        struct Wrapper<T> { value: T }
        trait Family { type Item; }
        impl Family for Wrapper<i64> { type Item = i64; }
        fn invalid<T>(value: T) -> <Wrapper<T> as Family>::Item { value }
        pub fn main() -> i64 { 42 }
    "#,
        &["G4190", "G4303"],
    );
}

#[test]
fn lexical_normalization_does_not_make_a_gat_domain_true() {
    rejects(
        r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        struct Wrapper<T> { value: T }
        trait Family { type Item<'a> where 'a: 'static; }
        impl<T> Family for Wrapper<T> where T: Mark {
            type Item<'a> = &'a T where 'a: 'static;
        }
        fn invalid<'a,T>(value: &'a T) -> <Wrapper<T> as Family>::Item<'a> where T: Mark { value }
        pub fn main() -> i64 { 42 }
    "#,
        &["G4303"],
    );
}
