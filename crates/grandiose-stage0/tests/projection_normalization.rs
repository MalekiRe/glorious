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

fn accepts_native(source: &str) {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("{error:#?}"));
        // SAFETY: execute only this locally compiled, closed pure fixture.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
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
fn nested_patterns_normalize_associated_payloads_after_call_inference() {
    for literal in ["{ let value: f64 = 0.5; value }", "0.5"] {
        accepts(&format!(
            r#"#![no_std]
            enum Result<T, E> {{ Ok(T), Err(E) }}
            enum Failure {{ Range }}
            trait Convert<T> {{
                type Error;
                fn convert(value: Self) -> Result<T, <Self as Convert<T>>::Error>;
            }}
            impl Convert<i64> for f32 {{
                type Error = Failure;
                fn convert(value: Self) -> Result<i64, Failure> {{ Result::Err(Failure::Range) }}
            }}
            impl Convert<i64> for f64 {{
                type Error = Failure;
                fn convert(value: Self) -> Result<i64, Failure> {{ Result::Err(Failure::Range) }}
            }}
            pub fn main() -> i64 {{
                handle Convert<i64>::convert({literal}) {{
                    Result::Err(Failure::Range) => 42,
                    _ => 0,
                }}
            }}
        "#,
        ));
    }
}

#[test]
fn nested_tuple_patterns_normalize_associated_nominal_payloads() {
    accepts(
        r#"#![no_std]
        enum Result<T> { Ok(T), Empty }
        trait Family {
            type Item;
            fn produce(value: Self) -> Result<<Self as Family>::Item>;
        }
        impl Family for f32 {
            type Item = (i64, i64);
            fn produce(value: Self) -> Result<(i64, i64)> { Result::Ok((42, 0)) }
        }
        impl Family for f64 {
            type Item = (i64, i64);
            fn produce(value: Self) -> Result<(i64, i64)> { Result::Ok((42, 0)) }
        }
        pub fn main() -> i64 {
            handle Family::produce(0.5) {
                Result::Ok((first, 0)) => first,
                _ => 0,
            }
        }
    "#,
    );
}

#[test]
fn structural_pattern_constraints_do_not_default_dependent_numeric_payloads() {
    for (item, value, pattern) in [
        ("(u8, u16)", "(42, 1)", "(42, 1)"),
        ("[u8; 2]", "[42, 1]", "[42, 1]"),
        ("u8", "42", "42"),
        ("()", "()", "()"),
        ("Entry<u8>", "Entry { value: 42 }", "Entry { value: 42 }"),
        ("Packed<u8>", "Packed(42)", "Packed(42)"),
        ("Named<u8>", "Named::Good { value: 42 }", "Named::Good { value: 42 }"),
    ] {
        let fallback = if item == "()" { "" } else { ", _ => 0" };
        accepts(&format!(
            r#"#![no_std]
            struct Entry<T> {{ value: T }}
            struct Packed<T>(T);
            enum Named<T> {{ Good {{ value: T }}, Empty }}
            trait Family {{
                type Item;
                fn produce(value: Self) -> <Self as Family>::Item;
            }}
            impl Family for f64 {{
                type Item = {item};
                fn produce(input: Self) -> {item} {{ {value} }}
            }}
            impl Family for f32 {{
                type Item = {item};
                fn produce(input: Self) -> {item} {{ {value} }}
            }}
            pub fn main() -> i64 {{
                handle Family::produce(0.5) {{ {pattern} => 42 {fallback} }}
            }}
        "#,
        ));
    }
}

#[test]
fn inferred_pattern_literals_reject_wrong_widths_after_projection_normalization() {
    for (item, value, pattern) in [("u8", "0", "256"), ("u8", "0", "-1"), ("u8", "0", "1.5"),
        ("f32", "0.0", "1e39"), ("(u8, u16)", "(0, 0)", "(256, 1)"), ("[u8; 2]", "[0, 0]", "[1, 256]")] {
        let source = format!(r#"#![no_std]
            trait Family {{
                type Item;
                fn produce(value: Self) -> <Self as Family>::Item;
            }}
            impl Family for f32 {{
                type Item = {item};
                fn produce(input: Self) -> {item} {{ {value} }}
            }}
            impl Family for f64 {{
                type Item = {item};
                fn produce(input: Self) -> {item} {{ {value} }}
            }}
            pub fn main() -> i64 {{ handle Family::produce(0.5) {{ {pattern} => 42, _ => 0 }} }}
        "#);
        // Check mode must reject before an executable verifier has to catch
        // an out-of-range pattern. The methods are never executed here.
        for mode in [CompilationMode::Check, CompilationMode::Build] {
            let mut check = request(&source, "0");
            check.mode = mode;
            let failure = StageZeroCompiler::new().compile(check).expect_err("invalid dependent pattern was accepted");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4201"),
                "{source}\n{:#?}", failure.diagnostics());
        }
    }
}

#[test]
fn pattern_constraints_preserve_later_nonnumeric_evidence_and_do_not_select_impl_heads() {
    let declarations = r#"#![no_std]
        enum Expected { Value, Empty }
        enum Other { Value }
        trait Family {
            type Item;
            fn produce(value: Self) -> <Self as Family>::Item;
        }
        impl Family for f32 {
            type Item = Expected;
            fn produce(value: Self) -> Expected { Expected::Value }
        }
        impl Family for f64 {
            type Item = Other;
            fn produce(value: Self) -> Other { Other::Value }
        }
        fn constrain(value: f32) {}
    "#;
    accepts(&format!(r#"{declarations}
        pub fn main() -> i64 {{
            let input = 0.5;
            let result = handle Family::produce(input) {{ Expected::Value => 42, _ => 0 }};
            constrain(input);
            result
        }}
    "#));
    rejects(&format!(r#"{declarations}
        pub fn main() -> i64 {{
            handle Family::produce(0.5) {{ Expected::Value => 42, _ => 0 }}
        }}
    "#), &["G4110", "G4201"]);
    rejects(&format!(r#"{declarations}
        fn invalid<T>(input: T) -> i64 where T: Family {{
            handle Family::produce(input) {{ Expected::Value => 42, _ => 0 }}
        }}
        pub fn main() -> i64 {{ invalid(0.5) }}
    "#), &["G4110", "G4201"]);
}

#[test]
fn nested_patterns_use_exact_lexical_associated_equalities() {
    accepts(r#"#![no_std]
        enum Result<T> { Ok(T), Empty }
        struct Pair { left: i64, right: u8 }
        trait Family {
            type Item;
            fn produce(value: Self) -> Result<<Self as Family>::Item>;
        }
        impl Family for i64 {
            type Item = Pair;
            fn produce(value: Self) -> Result<Pair> { Result::Ok(Pair { left: value, right: 1 }) }
        }
        fn inspect<T>(input: T) -> i64 where T: Family<Item = Pair> {
            handle Family::produce(input) {
                Result::Ok(Pair { left: answer, right: 1 }) => answer,
                _ => 0,
            }
        }
        pub fn main() -> i64 { inspect<i64>(42) }
    "#);
}

#[test]
fn inferred_pattern_subjects_execute_in_generated_code_and_remain_exhaustive() {
    let source = r#"#![no_std]
        enum Result<T> { Ok(T), Empty }
        trait Family {
            type Item;
            fn produce(input: Self) -> <Self as Family>::Item;
        }
        impl Family for f64 {
            type Item = Result<(u8, u16)>;
            fn produce(input: Self) -> Result<(u8, u16)> { Result::Ok((42, 1)) }
        }
        impl Family for f32 {
            type Item = Result<(u8, u16)>;
            fn produce(input: Self) -> Result<(u8, u16)> { Result::Ok((42, 1)) }
        }
        pub fn main() -> i64 {
            handle Family::produce(0.5) {
                Result::Ok((42, 1)) => 42,
                Result::Ok(_) => 0,
                Result::Empty => 0,
            }
        }
    "#;
    accepts(source);
    accepts_native(source);
    rejects(&source.replace("Result::Empty => 0,", ""), &["G4166"]);
    rejects(&source.replace("Result::Ok(_) => 0,", "Result::Ok(_) => 0, Result::Ok((42, 1)) => 1,"), &["G4168"]);
}

#[test]
fn inferred_patterns_compose_with_is_and_scoped_operation_payloads() {
    accepts(r#"#![no_std]
        enum Test<Y, N> { Yes(Y), No(N) }
        struct Pair { value: u8 }
        trait Family { type Item; fn produce(value: Self) -> <Self as Family>::Item; }
        impl Family for f32 {
            type Item = Pair;
            fn produce(value: Self) -> Pair { Pair { value: 42 } }
        }
        impl Family for f64 {
            type Item = Pair;
            fn produce(value: Self) -> Pair { Pair { value: 42 } }
        }
        pub fn main() -> i64 {
            handle Family::produce(0.5) is Pair { value: 42 } {
                Test::Yes(_) => 42,
                Test::No(_) => 0,
            }
        }
    "#);
    accepts(r#"#![no_std]
        struct Pair { value: u8 }
        trait Family { type Item; }
        impl Family for i64 { type Item = Pair; }
        effect Probe<T> where T: Family {
            check(value: <T as Family>::Item) -> i64;
        }
        fn inspect<T>(input: <T as Family>::Item) -> i64 where T: Family<Item = Pair> {
            handle Probe<T>::check(input) {
                Probe<T>::check(Pair { value: 42 }) => 42,
                Probe<T>::check(_) => 0,
            }
        }
        pub fn main() -> i64 { inspect<i64>(Pair { value: 42 }) }
    "#);
}

#[test]
fn inferred_nominal_patterns_do_not_bypass_selected_destructors() {
    let declarations = r#"#![no_std]
        struct Owner { value: u8 }
        impl Drop for Owner { drop(&mut self) -> {} }
        trait Family { type Item; fn produce(value: Self) -> <Self as Family>::Item; }
        impl Family for f32 {
            type Item = Owner;
            fn produce(value: Self) -> Owner { Owner { value: 42 } }
        }
        impl Family for f64 {
            type Item = Owner;
            fn produce(value: Self) -> Owner { Owner { value: 42 } }
        }
        fn consume(value: Owner) -> i64 { 42 }
    "#;
    accepts(&format!("{declarations} pub fn main() -> i64 {{ consume(Family::produce(0.5)) }}"));
    rejects(&format!("{declarations} pub fn main() -> i64 {{ handle Family::produce(0.5) {{ Owner {{ value: _ }} => 42 }} }}"), &["G4188"]);
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
