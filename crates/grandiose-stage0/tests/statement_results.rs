use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str, optimization: u8) -> CompilationRequest {
    let package = PackageKey("statement-results@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"statement-results")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.to_string())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

const SOURCES: &[&str] = &[
    "fn produce(count: &mut i64) -> i64 { *count = *count + 1; 99 } fn statement(count: &mut i64) { produce(count); } fn apply(body: () -> ()) { body() } pub fn main() -> i64 { let mut count = 40; statement(&mut count); apply() { produce(&mut count); }; count }",
    "struct Probe<'a> { count: &'a mut i64 } impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } fn make<'a>(count: &'a mut i64) -> Probe<'a> { Probe { count: count } } fn statement(count: &mut i64) { make(count); } pub fn main() -> i64 { let mut count = 41; statement(&mut count); count }",
    "struct Probe<'a> { count: &'a mut i64 } impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } } pub fn main() -> i64 { let mut count = 0; let result = @done: i64 { let resident = Probe { count: &mut count }; @done(41); }; result + count }",
];

#[test]
fn terminated_statements_preserve_effects_cleanup_and_nonlocal_exits() {
    for source in SOURCES {
        for optimization in [0, 2] {
            let artifact = StageZeroCompiler::new()
                .compile(request(source, optimization))
                .unwrap_or_else(|error| panic!("O{optimization}: {source}\n{error:#?}"))
                .artifact
                .unwrap();
            assert_eq!(artifact.run_i64().unwrap(), 42, "{source}");
            assert_eq!(
                decode_and_verify_program(&artifact.canonical_bytes())
                    .unwrap()
                    .run_i64()
                    .unwrap(),
                42,
                "{source}"
            );
        }
    }
}

#[test]
fn terminated_statements_preserve_effects_cleanup_and_exits_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    for source in SOURCES {
        for optimization in [0, 2] {
            let ir = StageZeroCompiler::new()
                .compile_llvm(request(source, optimization), LlvmTarget::host().unwrap())
                .unwrap_or_else(|error| panic!("O{optimization}: {source}\n{error:#?}"));
            // SAFETY: compile and execute only the locally checked safe source.
            let native = unsafe {
                ir.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap();
            let actual = unsafe { native.run_i64_profiled(Default::default()) }
                .unwrap()
                .0;
            assert_eq!(actual, 42, "O{optimization}: {source}");
        }
    }
}

#[test]
fn semicolons_cannot_return_a_value_or_discard_a_linear_result() {
    for (source, code) in [
        ("pub fn main() -> i64 { 42; }", "G4110"),
        (
            "struct Ticket {} impl Use<[1,1]> for Ticket {} fn make() -> Ticket { Ticket {} } pub fn main() { make(); }",
            "G5024",
        ),
    ] {
        for optimization in [0, 2] {
            let error = StageZeroCompiler::new()
                .compile(request(source, optimization))
                .unwrap_err();
            assert!(
                error
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| diagnostic.code == code),
                "{source}\n{error:#?}"
            );
        }
    }
}
