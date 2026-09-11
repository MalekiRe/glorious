use std::collections::BTreeMap;
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("tuple-types@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"tuple-types")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), "0".into())]),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

#[test]
fn grouping_and_tuple_arity_survive_elaboration_and_execution() {
    for source in [
        "type Number = ((i64)); fn identity(value: (Number)) -> (i64) { value } pub fn main() -> (i64) { let value: ((Number)) = 42; identity(value) }",
        "fn unwrap(value: ((i64,),)) -> (i64) { value.0.0 } pub fn main() -> i64 { let value: ((i64,),) = ((42,),); unwrap(value) }",
        "pub fn main() -> i64 { let task = (value: (i64)) -> (i64) { value + 1 }; let view: &((i64) -> (i64)) = &task; view(41) }",
        "fn invoke<F>(task: F) -> i64 where F: Fn<(i64,), Output = i64, Effects = {}> { task(41) } pub fn main() -> i64 { invoke((value: i64) -> i64 { value + 1 }) }",
        "fn invoke<F>(task: F) -> i64 where F: Fn<((i64, i64),), Output = i64, Effects = {}> { task((40, 2)) } pub fn main() -> i64 { invoke((value: (i64, i64)) -> i64 { value.0 + value.1 }) }",
    ] {
        let input = request(source);
        let artifact = StageZeroCompiler::new().compile(input.clone())
            .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42, "{source}");
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42, "{source}");
        use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
        let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap()).unwrap();
        for optimization in [0, 2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42, "O{optimization}: {source}");
        }
    }
}

#[test]
fn callable_argument_packs_reject_grouped_scalars() {
    for argument in ["(i64)", "((i64))", "(&i64)"] {
        let source = format!("fn reject<F>(task: F) where F: Fn<{argument}, Output = i64, Effects = {{}}> {{}} pub fn main() -> i64 {{ 42 }}");
        let diagnostics = StageZeroCompiler::new().compile(request(&source))
            .expect_err("a grouped scalar is not an argument tuple").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4164"), "{source}: {diagnostics:#?}");
    }
}

#[test]
fn tuple_callback_shapes_remain_distinct_and_effect_rows_require_evidence() {
    for (source, code) in [
        ("fn invoke<F>(task: F) -> i64 where F: Fn<((i64, i64),), Output = i64, Effects = {}> { task((40, 2)) } pub fn main() -> i64 { invoke((first: i64, second: i64) -> i64 { first + second }) }", "G4166"),
        ("fn read(task: &((i64) -> (i64))) -> i64 { task(41) } pub fn main() -> i64 { let task = (value: (i64)) -> (i64) { value + 1 }; let view: &((i64) -> (i64)) = &task; read(view) }", "G4180"),
        ("fn invoke<F>(task: F) -> i64 where F: Fn<(i64,), Output = i64> { task(41) } pub fn main() -> i64 { invoke((value: i64) -> i64 { value + 1 }) }", "G4155"),
        ("fn unwrap(value: (i64,)) -> i64 { value.0 } pub fn main() -> i64 { unwrap(42) }", "G4107"),
        ("pub fn main() -> (i64) { (42,) }", "G4110"),
    ] {
        let diagnostics = StageZeroCompiler::new().compile(request(source))
            .expect_err("tuple arity and effect evidence are not implicit conversions").diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == code), "{source}: {diagnostics:#?}");
    }
}
