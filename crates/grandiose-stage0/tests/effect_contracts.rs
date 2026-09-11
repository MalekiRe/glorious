use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};
use std::collections::BTreeMap;

fn request(source: &str, level: &str) -> CompilationRequest {
    let package = PackageKey("effect-contracts@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"effect-contracts")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), level.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for level in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, level))
            .unwrap_or_else(|error| panic!("O{level}: {source}\n{:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

fn rejects(source: &str, codes: &[&str]) {
    for level in ["0", "2"] {
        let outcome = StageZeroCompiler::new().compile(request(source, level));
        assert!(outcome.is_err(), "O{level}: invalid effect contract was accepted: {source}");
        let failure = outcome.unwrap_err();
        assert!(failure.diagnostics().iter().any(|diagnostic| codes.contains(&diagnostic.code)),
            "O{level}: {source}\n{:#?}", failure.diagnostics());
    }
}

#[test]
fn unspecified_callback_effects_are_forwarded_not_defaulted_to_empty() {
    let prefix = r#"#![no_std]
        effect Read { read() -> i64; }
        fn pure() -> i64 { 42 }
        fn effectful() -> i64 / Read { Read::read() }
        fn invoke<F>(action: F) -> i64 / { <F as Fn<()>>::Effects }
            where F: Fn<(),Output=i64> { action() }
        fn relay<F>(action: F) -> i64 / { <F as Fn<()>>::Effects }
            where F: Fn<(),Output=i64> { invoke(action) }
    "#;
    accepts(&format!("{prefix} pub fn main() -> i64 {{ relay(pure) }}"));
    accepts(&format!("{prefix} pub fn main() -> i64 {{
        handle relay(effectful) {{ Read::read() => 42 }}
    }}"));
    rejects(&format!("{prefix} pub fn main() -> i64 {{ relay(effectful) }}"), &["G4155"]);
    // Preserve the rejected pre-migration contract. Even when one caller
    // supplies a pure function, generic checking may not invent F::Effects={}
    // for a declaration that admits arbitrary effectful callables as well.
    rejects(&format!("{prefix}
        fn concealed<F>(action: F) -> i64 where F: Fn<(),Output=i64> {{ action() }}
        pub fn main() -> i64 {{ concealed(pure) }}"), &["G4155"]);
}

#[test]
fn family_and_operation_projection_contracts_are_lexical() {
    accepts(r#"#![no_std]
        trait Source { type Item; }
        impl Source for i64 { type Item = i64; }
        effect Read<T> where T: Source { read(T) -> <T as Source>::Item; }
        effect Select { select<T>(T) -> <T as Source>::Item where T: Source; }
        fn declared<T>(value: T) -> <T as Source>::Item / Read<T> where T: Source {
            Read<T>::read(value)
        }
        pub fn main() -> i64 { handle Read<i64>::read(42) { Read<i64>::read(value) => value } }
    "#);
    rejects(r#"#![no_std]
        trait Source { type Item; }
        effect Read<T> where T: Source { read(T) -> <T as Source>::Item; }
        effect Select { valid<T>(T) -> <T as Source>::Item where T: Source;
            invalid<T>(T) -> <T as Source>::Item; }
        pub fn main() -> i64 { 42 }
    "# , &["G4190", "G4303"]);
}

#[test]
fn family_prerequisites_apply_even_to_phantom_arguments_and_unused_rows() {
    for declaration in [
        "fn invalid() / Restricted<i64> {}",
        "fn invalid<T>() / Restricted<T> {}",
        "type Bad = () -> () / Restricted<i64>;",
    ] {
        rejects(&format!("#![no_std]\ntrait Mark {{}} effect Restricted<T> where T: Mark {{ ping(); }} {declaration} pub fn main() -> i64 {{ 42 }}"), &["G4303"]);
    }
    accepts(r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        effect Restricted<T> where T: Mark { ping(); }
        fn valid<T>() / Restricted<T> where T: Mark { Restricted<T>::ping() }
        pub fn main() -> i64 { handle { valid<i64>(); 42 } { Restricted<i64>::ping() => () } }
    "#);
}

#[test]
fn operation_prerequisites_are_checked_after_payload_inference() {
    accepts(r#"#![no_std]
        trait Mark {} impl Mark for i64 {}
        effect Pass { pass<T>(T) -> T where T: Mark; }
        fn valid(value: i64) -> i64 / Pass { Pass::pass(value) }
        pub fn main() -> i64 { handle valid(42) { Pass::pass<i64>(value) => value } }
    "#);
    for argument in ["value", "Pass::pass<i64>(value)"] {
        let invocation = if argument == "value" { "Pass::pass(value)" } else { argument };
        rejects(&format!("#![no_std]\ntrait Mark {{}} effect Pass {{ pass<T>(T) -> T where T: Mark; }} fn invalid(value: i64) -> i64 / Pass {{ {invocation} }} pub fn main() -> i64 {{ 42 }}"), &["G4143"]);
    }
}

#[test]
fn operation_outlives_constraints_cannot_create_a_longer_scope() {
    rejects(r#"#![no_std]
        effect Keep { keep<'scope,T>(T) where T: 'scope; }
        fn invalid<'a>(value: &'a i64) / Keep { Keep::keep<'static,&'a i64>(value) }
        pub fn main() -> i64 { 42 }
    "#, &["G4304"]);
}

#[test]
fn callable_operation_equalities_retain_output_and_row_authority() {
    accepts(r#"#![no_std]
        effect Run { run<F,e: EffectRow>(F) -> i64 where F: Fn<(),Output=i64,Effects=e>; }
        type Job = () -> i64;
        fn answer() -> i64 { 42 }
        fn forward<F,e: EffectRow>(job: F) -> i64 / Run where F: Fn<(),Output=i64,Effects=e> {
            Run::run<F,e>(job)
        }
        pub fn main() -> i64 { handle forward(answer) { Run::run<Job,{}>(job) => job() } }
    "#);
    rejects(r#"#![no_std]
        effect Run { run<F>(F) -> i64 where F: Fn<(),Output=i64,Effects={}>; }
        fn wrong() -> u8 { 42 }
        fn invalid() -> i64 / Run { Run::run(wrong) }
        pub fn main() -> i64 { 42 }
    "#, &["G4167"]);
    rejects(r#"#![no_std]
        effect Need { need() -> i64; }
        effect Run { run<F>(F) -> i64 where F: Fn<(),Output=i64,Effects={}>; }
        fn effectful() -> i64 / Need { Need::need() }
        fn invalid() -> i64 / Run { Run::run(effectful) }
        pub fn main() -> i64 { 42 }
    "#, &["G4168"]);
}

#[test]
fn quantified_effect_prerequisites_remain_universal_after_substitution() {
    accepts(r#"#![no_std]
        trait Mark {} impl<'a> Mark for &'a i64 {}
        effect Gate<T> where for<'a> &'a T: Mark {
            check<U>(U) -> U where for<'b> &'b U: Mark;
        }
        pub fn main() -> i64 { handle Gate<i64>::check<i64>(42) { Gate<i64>::check<i64>(value) => value } }
    "#);
    rejects(r#"#![no_std]
        trait Mark {} impl Mark for &'static i64 {}
        effect Gate { check<T>(T) -> T where for<'a> &'a T: Mark; }
        fn invalid(value: i64) -> i64 / Gate { Gate::check(value) }
        pub fn main() -> i64 { 42 }
    "#, &["G4140"]);
}

#[test]
fn imported_operation_contracts_keep_the_declaring_trait_identity() {
    let library = r#"#![no_std]
        pub trait Mark {} pub impl Mark for i64 {}
        pub effect Pass { pass<T>(T) -> T where T: Mark; }
    "#;
    for ty in ["i64", "u8"] {
        let source = format!(r#"#![no_std]
            use facade::Pass;
            trait Mark {{}} impl Mark for u8 {{}}
            fn apply(value: {ty}) -> {ty} / Pass {{ Pass::pass(value) }}
            pub fn main() -> i64 {{ handle {{ let _: {ty} = apply(42); 42 }} {{ Pass::pass<{ty}>(value) => value }} }}
        "#);
        for level in ["0", "2"] {
            let mut input = request(&source, level);
            for (package, text) in [("provider@0.1.0", library), ("facade@0.1.0", "#![no_std]\npub use provider::Pass;")] {
                input.sources.push(SourceInput::new(PackageKey(package.into()), LogicalPath::parse("src/lib.glorious").unwrap(), text.as_bytes()));
            }
            let outcome = StageZeroCompiler::new().compile(input);
            if ty == "i64" {
                let artifact = outcome.unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
                assert_eq!(artifact.run_i64().unwrap(), 42);
                assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            } else {
                assert!(outcome.is_err(), "a same-spelled local trait must not satisfy the imported operation");
                assert!(outcome.unwrap_err().diagnostics().iter().any(|diagnostic| diagnostic.code == "G4143"));
            }
        }
    }
}

#[test]
fn operation_environment_prerequisites_use_the_actual_captured_callable() {
    accepts(r#"#![no_std]
        effect Enqueue {
            enqueue<'scope,'env,E0,E1,F,e: EffectRow>(F) -> i64
            where 'env: 'scope, E0: Environment<'env>, E1: Environment<'env>,
                F: Fn<(),Output=i64,Effects=e> + RunsIn<E0,(),After=E1> + 'scope;
        }
        fn submit() -> i64 / Enqueue {
            let value = 42;
            Enqueue::enqueue(move(value) { value })
        }
        pub fn main() -> i64 { 42 }
    "#);
    rejects(r#"#![no_std]
        effect Enqueue { enqueue<F>(F) -> i64 where F: Fn<(),Output=i64,Effects={}> + 'static; }
        fn submit<'a>(value: &'a i64) -> i64 / Enqueue { Enqueue::enqueue(move(value) { *value }) }
        pub fn main() -> i64 { 42 }
    "#, &["G4304"]);
}
