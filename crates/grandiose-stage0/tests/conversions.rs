//! Ordinary trait-backed conversions, including source/context inference.
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

fn request(source: &str) -> CompilationRequest {
    let app = PackageKey("casts@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"trait-conversions-v1")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(
                app,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            ),
            SourceInput::new(
                PackageKey("std@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn run(source: &str) -> i64 {
    let outcome = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_or_else(|error| {
            panic!(
                "conversion source failed: {:#?}\n{source}",
                error.diagnostics()
            )
        });
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    decode_and_verify_program(&bytes)
        .unwrap()
        .run_i64()
        .unwrap()
}

fn sum(source: &mut String, mut calls: Vec<String>) -> String {
    // Bound each generated body as well as expression depth; this tests the
    // conversion matrix, not the authoring frontend's large-body limits.
    let mut next = 0;
    while calls.len() > 4 {
        calls = calls
            .chunks(4)
            .map(|group| {
                let name = format!("sum_{next}");
                next += 1;
                source.push_str(&format!("fn {name}() -> i64 {{ {} }}\n", group.join(" + ")));
                format!("{name}()")
            })
            .collect();
    }
    calls.join(" + ")
}

#[test]
fn as_function_accepts_explicit_and_contextual_targets() {
    assert_eq!(
        run(r#"
        use std::*;
        fn consume(value: f32) -> i64 { handle f32_eq(value, 1.0) { true => 40, false => 0 } }
        fn contextual(value: u32) -> i64 { as(value) }
        pub struct Reading { value: f32 }
        pub fn main() -> i64 {
            let explicit = as<f32>(1);
            let reading = Reading { value: as(1) };
            consume(explicit) + consume(as(1)) + consume(reading.value) + contextual(std::as<u32>(2))
        }
    "#),
        122
    );
}

#[test]
fn as_function_dispatches_to_an_ordinary_user_implementation() {
    assert_eq!(
        run(r#"
        use std::*;
        pub struct Count { value: i64 }
        pub impl Use<[1, 1]> for Count {}
        pub struct Reading { value: f32 }
        pub impl As<i64> for Count { cast(value: Count) -> i64 { let Count { value } = value; value } }
        pub impl As<Reading> for Count { cast(value: Count) -> Reading { let Count { value } = value; Reading { value: as(value) } } }
        fn forward<T, S>(value: S) -> T where S: As<T> { as(value) }
        fn extract(value: Count) -> i64 { as(value) }
        pub fn main() -> i64 {
            let reading = as<Reading>(Count { value: 2 });
            extract(Count { value: 40 }) + forward<i64>(reading.value)
        }
    "#),
        42
    );
}

#[test]
fn as_function_preserves_ownership_and_effect_checks() {
    let source = r#"
        use std::*;
        pub struct Token { value: i64 }
        pub impl Use<[1, 1]> for Token {}
        pub impl As<i64> for Token { cast(value: Token) -> i64 { value.value } }
        effect Read { number() -> i64; }
        pub struct Effectful {}
        pub impl As<i64> for Effectful { cast(value: Effectful) -> i64 { Read::number() } }
        pub fn reused() -> i64 { let token = Token { value: 1 }; let n = as<i64>(token); n + as<i64>(token) }
        pub fn main() -> i64 { 0 }
    "#;
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .expect_err("casts cannot hide effects or copy a linear value");
    for fragment in ["pub impl As<i64> for Effectful", "pub fn reused"] {
        let start = source.find(fragment).unwrap();
        let end = source[start..].find('\n').unwrap() + start;
        assert!(
            error.diagnostics().iter().any(|d| d
                .primary
                .is_some_and(|s| (start..end).contains(&(s.start as usize)))),
            "missing rejection for {fragment}: {:#?}",
            error.diagnostics()
        );
    }
}

#[test]
fn as_is_an_ordinary_renameable_library_function() {
    assert_eq!(
        run(r#"
        use std::as as convert;
        fn as<T, S>(value: S, answer: T) -> T where S: Use<[0, 1]> { answer }
        pub fn main() -> i64 { as<i64>(0, 40) + convert<i64>(convert<u8>(2)) }
    "#),
        42
    );
}

#[test]
fn as_function_covers_every_numeric_pair() {
    let types = [
        "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
        "f32", "f64",
    ];
    let mut source = String::from("use std::*;\n");
    for ty in types {
        let literal = if ty.starts_with('f') { "42.0" } else { "42" };
        source.push_str(&format!("fn source_{ty}() -> {ty} {{ {literal} }}\n"));
        let compare = if ty.starts_with('f') {
            format!("{ty}_eq(value, {literal})")
        } else {
            format!("value == {literal}")
        };
        source.push_str(&format!(
            "fn check_{ty}(value: {ty}) -> i64 {{ handle {compare} {{ true => 1, false => 0 }} }}\n"
        ));
    }
    let mut calls = Vec::new();
    for from in types {
        for to in types {
            calls.push(format!("check_{to}(as<{to}>(source_{from}()))"));
        }
    }
    let total = sum(&mut source, calls);
    source.push_str(&format!("pub fn main() -> i64 {{ {total} }}"));
    assert_eq!(run(&source), 196);
}

#[test]
fn as_function_float_boundaries_match_rust_policy() {
    let mut source = String::from("use std::*;\n");
    let mut calls = Vec::new();
    for (ty, min, max, upper) in [
        ("u8", "0", "255", "256.0"),
        ("u16", "0", "65535", "65536.0"),
        ("u32", "0", "4294967295", "4294967296.0"),
        ("u64", "0", "18446744073709551615", "18446744073709551616.0"),
        (
            "usize",
            "0",
            "18446744073709551615",
            "18446744073709551616.0",
        ),
        (
            "u128",
            "0",
            "340282366920938463463374607431768211455",
            "340282366920938463463374607431768211456.0",
        ),
        ("i8", "wrapping_add(127, 1)", "127", "128.0"),
        ("i16", "wrapping_add(32767, 1)", "32767", "32768.0"),
        (
            "i32",
            "wrapping_add(2147483647, 1)",
            "2147483647",
            "2147483648.0",
        ),
        (
            "i64",
            "wrapping_add(9223372036854775807, 1)",
            "9223372036854775807",
            "9223372036854775808.0",
        ),
        (
            "isize",
            "wrapping_add(9223372036854775807, 1)",
            "9223372036854775807",
            "9223372036854775808.0",
        ),
        (
            "i128",
            "wrapping_add(170141183460469231731687303715884105727, 1)",
            "170141183460469231731687303715884105727",
            "170141183460469231731687303715884105728.0",
        ),
    ] {
        source.push_str(&format!(
            "fn min_{ty}() -> {ty} {{ {min} }} fn max_{ty}() -> {ty} {{ {max} }}\n"
        ));
        source.push_str(&format!(
            "fn eq_{ty}(a: {ty}, b: {ty}) -> i64 {{ handle a == b {{ true => 1, false => 0 }} }}\n"
        ));
        for float in ["f32", "f64"] {
            calls.push(format!("eq_{ty}(as<{ty}>({float}_div(0.0, 0.0)), 0)"));
            calls.push(format!(
                "eq_{ty}(as<{ty}>({float}_div(1.0, 0.0)), max_{ty}())"
            ));
            calls.push(format!(
                "eq_{ty}(as<{ty}>({float}_div(-1.0, 0.0)), min_{ty}())"
            ));
            calls.push(format!("eq_{ty}(as<{ty}>({float}_add(42.9, 0.0)), 42)"));
            calls.push(format!("eq_{ty}(as<{ty}>({float}_add(-0.9, 0.0)), 0)"));
        }
        calls.push(format!("eq_{ty}(as<{ty}>({upper}), max_{ty}())"));
    }
    let expected = calls.len() as i64;
    let total = sum(&mut source, calls);
    source.push_str(&format!("pub fn main() -> i64 {{ {total} }}"));
    assert_eq!(run(&source), expected);
}

#[test]
fn as_function_numeric_precision_and_character_policy() {
    assert_eq!(
        run(r#"
        use std::*;
        fn wide() -> u64 { 9223372586610589697 }
        fn widest() -> u128 { 340282366920938463463374607431768211455 }
        fn yes(value: Bool) -> i64 { handle value { true => 1, false => 0 } }
        fn small(value: u8) -> u8 { value }
        fn numeric() -> i64 {
            let rounded = as<f32>(wide());
            yes(f32_eq(rounded, 9223373136366403584.0)) +
            yes(f32_eq(as<f32>(widest()), f32_div(1.0, 0.0)))
        }
        fn zero() -> i64 {
            let negative_zero = as<f32>(-0.0);
            yes(f64_eq(as<f64>(negative_zero), -0.0)) +
            yes(f32_eq(f32_div(1.0, negative_zero), f32_div(-1.0, 0.0)))
        }
        fn characters() -> i64 {
            yes(as<u32>('A') == 65) + yes(as<char>(small(65)) == 'A')
        }
        fn wrapping() -> i64 {
            yes(as<u8>(-1) == 255) + yes(as<u8>(256) == 0) +
            yes(as<i64>(as<u64>(-1)) == -1)
        }
        pub fn main() -> i64 { numeric() + zero() + characters() + wrapping() }
    "#),
        9
    );
}

#[test]
fn as_function_requires_target_evidence_and_an_implementation() {
    let source = r#"
        use std::*;
        pub struct Missing {}
        pub fn ambiguous() -> () { let value = as(1); () }
        pub fn unsupported() -> i64 { as(Missing {}) }
        pub fn too_many() -> i64 { as<i64, i64, i64>(1) }
        pub fn invalid_char() -> char { as(as<u32>(55296)) }
        pub fn main() -> i64 { 0 }
    "#;
    let error = StageZeroCompiler::new()
        .compile(request(source))
        .expect_err("invalid conversions must fail before bytecode");
    for function in ["ambiguous", "unsupported", "too_many", "invalid_char"] {
        let start = source.find(&format!("pub fn {function}")).unwrap();
        let end = source[start..].find("\n").unwrap() + start;
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|d| d.primary.is_some_and(|s| s.file
                    == grandiose_stage0::FileKey::new(
                        &PackageKey("casts@0.1.0".into()),
                        "src/main.glorious"
                    )
                    && (start..end).contains(&(s.start as usize)))),
            "{function} must be diagnosed: {:#?}",
            error.diagnostics()
        );
    }
}
