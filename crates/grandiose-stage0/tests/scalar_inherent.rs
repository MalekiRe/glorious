use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, VerifiedVmProgram, decode_and_verify_program};

fn outcome(source: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("scalar-inherent@0.1.0".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"scalar-inherent")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(), codegen_options: Default::default(),
        capability_manifest: vec![], runtime_manifest: None,
    })
}

fn compile(source: &str) -> VerifiedVmProgram {
    let outcome = outcome(source).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    outcome.artifact.unwrap()
}

#[test]
fn scalar_inherent_functions_preserve_self_and_each_machine_width() {
    macro_rules! check {
        ($ty:literal, $literal:literal, $run:ident, $expected:expr) => {{
            let source = concat!("impl ", $ty, " { pub fn answer() -> Self { ", $literal,
                " } pub fn identity(value: Self) -> Self { value } } pub fn main() -> ", $ty,
                " { ", $ty, "::identity(", $ty, "::answer()) }");
            let artifact = compile(source);
            assert_eq!(artifact.$run().unwrap(), $expected);
            assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().$run().unwrap(), $expected);
        }};
    }
    check!("u8", "42", run_u8, 42);
    check!("u16", "42", run_u16, 42);
    check!("u32", "42", run_u32, 42);
    check!("u64", "42", run_u64, 42);
    check!("u128", "42", run_u128, 42);
    check!("usize", "42", run_usize, 42);
    check!("i8", "42", run_i8, 42);
    check!("i16", "42", run_i16, 42);
    check!("i32", "42", run_i32, 42);
    check!("i64", "42", run_i64, 42);
    check!("i128", "42", run_i128, 42);
    check!("isize", "42", run_isize, 42);
    check!("f32", "42.0", run_f32, 42.0);
    check!("f64", "42.0", run_f64, 42.0);
}

#[test]
fn scalar_inherent_functions_keep_member_generic_arguments() {
    let artifact = compile("impl u8 { pub fn keep<T>(value: T) -> T { value } } pub fn main() -> i64 { u8::keep<i64>(42) }");
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn inherent_methods_use_the_source_method_name_for_their_implicit_label() {
    let artifact = compile("impl f32 { pub fn exit(value: Self) -> Self { @exit(value) } } pub fn main() -> f32 { f32::exit(42.0) }");
    assert_eq!(artifact.run_f32().unwrap(), 42.0);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_f32().unwrap(), 42.0);
    let artifact = compile("use std::*; struct Item { value: i64 } impl Item { pub fn exit(value: Self) -> i64 { return(value.value, @exit) } } pub fn main() -> i64 { Item::exit(Item { value: 42 }) }");
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn scalar_inherent_functions_resolve_through_their_declaring_module() {
    let artifact = compile("mod numeric { impl u8 { pub fn answer() -> i64 { 42 } } } pub fn main() -> i64 { numeric::u8::answer() }");
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn scalar_inherent_functions_preserve_module_aliases_and_private_descendant_access() {
    let artifact = compile("mod numeric { impl u8 { fn answer() -> i64 { 42 } } pub mod child { pub fn read() -> i64 { u8::answer() } } } use numeric::child as api; pub fn main() -> i64 { api::read() }");
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
}

#[test]
fn scalar_inherent_functions_do_not_bypass_privacy_or_duplicate_checks() {
    for source in [
        "mod numeric { impl u8 { fn answer() -> i64 { 42 } } } pub fn main() -> i64 { numeric::u8::answer() }",
        "mod numeric { impl u8 { pub fn answer() -> i64 { 42 } } } mod sibling { pub fn read() -> i64 { u8::answer() } } pub fn main() -> i64 { sibling::read() }",
        "impl u8 { pub fn answer() -> i64 { 41 } } impl u8 { pub fn answer() -> i64 { 42 } } pub fn main() -> i64 { u8::answer() }",
    ] {
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = outcome(source) else {
            panic!("unexpectedly accepted {source}");
        };
        assert!(diagnostics.iter().any(|diagnostic|
            matches!(diagnostic.code, "G4104" | "G3001")), "{diagnostics:?}");
    }
}
