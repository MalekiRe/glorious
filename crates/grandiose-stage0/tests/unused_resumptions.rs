//! Language §10.6: an unused optional continuation cancels its residual.
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("unused-resumptions@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"unused-resumptions")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn runs(source: &str) {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let native = StageZeroCompiler::new().compile_llvm(request(source), LlvmTarget::host().unwrap()).unwrap();
    for plan in [native.clone(), native.with_vm_functions([native.entry_key()]).unwrap(),
        native.with_vm_functions(native.function_keys().iter().copied().filter(|key| *key != native.entry_key())).unwrap()]
    {
        for optimization in [0, 2] {
            let module = unsafe { plan.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(module.run_i64_with_limits(Default::default()).unwrap_or_else(|error|
                panic!("O{optimization}: {source}\n{error:#?}")), 42);
        }
    }
}

#[test]
fn unused_optional_token_skips_the_protected_suffix() {
    runs(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { Ask::ask(); 1 / 0 } { Ask::ask(k) => 42 } }",
    );
}

#[test]
fn cancellation_does_not_run_a_normal_completion_clause() {
    runs(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => 42, result => result + 5 } }",
    );
}

#[test]
fn unused_optional_token_cancels_across_a_callee_frame() {
    runs(
        "effect Ask { [0,1] ask() -> i64; } fn helper() -> i64 / Ask { Ask::ask() + 1 } pub fn main() -> i64 { handle helper() { Ask::ask(k) => 42 } }",
    );
}

#[test]
fn cancellation_preserves_distinct_operation_and_handler_result_types() {
    runs(
        "effect Ask { [0,1] ask() -> u64; } pub fn main() -> i64 { handle { Ask::ask(); 0 } { Ask::ask(k) => 42 } }",
    );
}

#[test]
fn an_invoked_optional_token_is_not_canceled_as_unused() {
    runs(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { Ask::ask() + 1 } { Ask::ask(k) => k(41) } }",
    );
}

#[test]
fn an_alias_invocation_is_not_canceled_as_unused() {
    runs(
        "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { Ask::ask() + 1 } { Ask::ask(k) => { let resume = k; resume(41) } } }",
    );
}

#[test]
fn an_unused_required_resumption_remains_a_source_error() {
    let error = StageZeroCompiler::new().compile(request("effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => 42 } }")).unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"
                && diagnostic.message.contains("declared quantity is [1, 1]")),
        "{error:?}"
    );
}

#[test]
fn unused_token_cancellation_destroys_callee_owners_exactly_once() {
    runs(
        r#"
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> {
            drop(&mut self) -> { *self.target = *self.target + 1; }
        }
        effect Ask { [0,1] ask() -> i64; }
        fn helper(target: &mut i64) -> i64 / Ask {
            let owner = Probe { target: target };
            Ask::ask();
            0
        }
        fn finish(target: &mut i64) -> i64 {
            handle helper(target) { Ask::ask(k) => 0 }
        }
        pub fn main() -> i64 {
            let mut count = 41;
            finish(&mut count);
            count
        }
    "#,
    );
}
