use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, VmExecutionLimits, decode_and_verify_program,
};

fn compile(source: &str, optimization: &str) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    let package = PackageKey("mandatory-tail-labels@0.1.0".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"mandatory-tail-labels")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.into())].into_iter().collect(),
        capability_manifest: vec![], runtime_manifest: None,
    })
}

fn accepts(source: &str, expected: i64) {
    for optimization in ["0", "2"] {
        let artifact = compile(source, optimization).unwrap_or_else(|error| panic!("{source}: {error:?}")).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        for artifact in [&artifact, &decoded] {
            assert_eq!(artifact.run_i64_with_limits(VmExecutionLimits {
                max_call_depth: 16, ..VmExecutionLimits::default()
            }).unwrap_or_else(|error| panic!("{source}: {error:?}")), expected);
        }
    }
}

#[test]
fn final_lexical_and_named_labels_discharge_before_tail_transfer() {
    for source in [
        "fn answer() -> i64 { 42 } pub fn main() -> i64 { label active { tail answer() } }",
        "fn walk(n: i64, total: i64) -> i64 { handle n { 0 => @walk(total), _ => tail walk(n - 1, total + 1) } } pub fn main() -> i64 { walk(10000, 0) - 9958 }",
        "fn walk(n: i64, total: i64) -> i64 { label done { handle n { 0 => @done(total), _ => tail walk(n - 1, total + 1) } } } pub fn main() -> i64 { walk(10000, 0) - 9958 }",
        "use std::*; fn walk(n: i64, total: i64) -> i64 { handle n == 0 { true => return(total, @walk), false => () }; tail walk(n - 1, total + 1) } pub fn main() -> i64 { walk(10000, 0) - 9958 }",
    ] { accepts(source, 42); }
}

#[test]
fn label_tail_still_disposes_current_frame_owners_once() {
    accepts("struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        fn answer(value: i64) -> i64 { value }
        fn relay<'a>(probe: Probe<'a>, early: Bool) -> i64 {
            handle early { true => @relay(0), false => () };
            tail answer(*probe.target + 1)
        }
        pub fn main() -> i64 { let mut count = 20; let result = relay(Probe { target: &mut count }, false); result + count }", 42);
}

#[test]
fn labels_are_not_frame_independent_tail_payloads() {
    for source in [
        "fn invoke<L>(exit: L) -> i64 where L: Label<i64> { exit(42) } pub fn main() -> i64 { tail invoke(@main) }",
        "fn invoke<L>(exit: L) -> i64 where L: Label<i64> { exit(42) } pub fn main() -> i64 { let exit = @main; tail invoke(exit) }",
        "fn apply(callback: () -> !) -> i64 { callback() } pub fn main() -> i64 { let exit = @main; let callback = move (exit) { exit(42) }; tail apply(callback) }",
    ] {
        let error = compile(source, "0").expect_err("the ending label destination cannot cross a tail transfer");
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4403"), "{source}: {error:?}");
    }
}

#[test]
fn label_rejoins_do_not_authorize_following_work() {
    let error = compile("fn answer() -> i64 { 41 } pub fn main() -> i64 { let value = label done { tail answer() }; value + 1 }", "0").unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4401"), "{error:?}");
}
