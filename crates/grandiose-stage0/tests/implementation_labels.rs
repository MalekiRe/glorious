use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::collections::BTreeMap;

fn request(source: &str, optimization: &str, dependency: Option<&str>) -> CompilationRequest {
    let package = PackageKey("implementation-labels@0.1.0".into());
    let mut sources = vec![SourceInput::new(package.clone(), LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())];
    if let Some(dependency) = dependency {
        sources.push(SourceInput::new(PackageKey("choices@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(), dependency.as_bytes()));
    }
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"implementation-labels")),
        mode: CompilationMode::Build, root_package: package, sources,
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn accepts(source: &str, dependency: Option<&str>) {
    for optimization in ["0", "2"] {
        let outcome = StageZeroCompiler::new().compile(request(source, optimization, dependency)).unwrap();
        let artifact = outcome.artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn implementation_method_owns_its_named_exit() {
    accepts("trait Choose { fn choose(value: Self, number: i64) -> i64; } struct Choice {} impl Choose for Choice { fn choose(value: Self, number: i64) -> i64 { @choose(number) } } pub fn main() -> i64 { Choose::choose(Choice {}, 42) }", None);
}

#[test]
fn implementation_label_context_infers_generic_return_payload() {
    accepts("use std::*; trait Choose<T> { fn choose(value: Self, number: T) -> Result<T,()>; } struct Choice {} impl<T> Choose<T> for Choice { fn choose(value: Self, number: T) -> Result<T,()> { return(Result::Ok(number), @choose) } } pub fn main() -> i64 { let result = Choose<i64>::choose(Choice {}, 42); handle result { Result::Ok(value) => value, Result::Err(_) => 0 } }", None);
}

#[test]
fn imported_implementation_label_keeps_the_method_identity() {
    accepts("use choices::{Choose,Choice}; pub fn main() -> i64 { Choose::choose(Choice {}, 42) }",
        Some("pub trait Choose { fn choose(value: Self, number: i64) -> i64; } pub struct Choice {} pub impl Choose for Choice { fn choose(value: Self, number: i64) -> i64 { @choose(number) } }"));
}

#[test]
fn implementation_label_still_checks_payload_type_and_capture_scope() {
    for source in [
        "trait Choose { fn choose() -> i64; } struct Choice {} impl Choose for Choice { fn choose() -> i64 { @choose(()) } } pub fn main() -> i64 { 42 }",
        "trait Choose { fn choose() -> i64; } struct Choice {} impl Choose for Choice { fn choose() -> i64 { let run = () -> i64 { @choose(42) }; run() } } pub fn main() -> i64 { 42 }",
    ] {
        let error = StageZeroCompiler::new().compile(request(source, "0", None)).expect_err("invalid method exit must be rejected");
        assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G4107" | "G4178" | "G4177" | "G4179")), "{error:?}");
    }
}
