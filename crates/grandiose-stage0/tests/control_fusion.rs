//! Structural control fusion must preserve the complete source invocation:
//! formation, strict inputs, resident capture storage, and all exit paths.
use grandiose_stage0::{CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, decode_and_verify_program};

fn request(source: &str, optimization: u8) -> CompilationRequest {
    let package = PackageKey("control-fusion@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"control-fusion")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.to_string())].into(),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn executes(body: &str) {
    let source = format!("use std::*;\n{body}");
    for optimization in [0, 2] {
        let artifact = StageZeroCompiler::new().compile(request(&source, optimization))
            .unwrap_or_else(|error| panic!("O{optimization}: {source}\n{error:#?}")).artifact.unwrap();
        let emitted = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
        assert!(!emitted.functions.values().flat_map(|function| &function.instructions)
            .any(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::MakeLabel { .. })),
            "fused lexical destinations must not survive as runtime label carriers: {source}");
        assert_eq!(artifact.run_i64().unwrap(), 42, "{source}");
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42, "{source}");
    }
}

#[test]
fn lexical_captures_survive_aliases_aggregates_and_generic_forwarding() {
    for body in [
        "pub fn main() -> i64 { @done: i64 { let task = () -> ! { @done(42) }; let (alias,) = (task,); alias() } }",
        "fn apply<F>(task:F) -> ! where F:Fn<(),Output = ! > { let alias = task; alias() }
         pub fn main() -> i64 { let value = 42; @done: i64 { apply(() -> ! { @done(value) }) } }",
        "fn keep<F>(task:F) -> F { task } fn apply<F>(task:F) -> ! where F:Fn<(),Output = ! > { task() }
         pub fn main() -> i64 { let value = 42; @done: i64 { let task = keep(() -> ! { @done(value) }); apply(task) } }",
        "pub fn main() -> i64 { let value = 42; @done: i64 { let outer = () -> ! { let inner = () -> ! { @done(value) }; inner() }; outer() } }",
    ] { executes(body); }
}

#[test]
fn closure_environment_preserves_shared_and_unique_capture_storage() {
    executes("pub fn main() -> i64 { let value = 42; @done: i64 {
        let task = () -> ! { let borrowed = &value; @done(*borrowed) }; task()
    } }");
    executes("pub fn main() -> i64 { let mut value = 40; @done: i64 {
        let task = () -> ! { value = value + 2; @done(value) }; task()
    } }");
}

#[test]
fn a_label_bearing_closure_can_return_normally_without_executing_the_label() {
    executes("fn run<F>(task:F) -> i64 where F:Fn<(),Output=i64> { task() }
        pub fn main() -> i64 { @done: i64 { run(() -> i64 { let target = @done; 42 }) } }");
}

#[test]
fn closure_formation_and_arguments_keep_source_order_and_storage() {
    executes("fn apply<F>(task:F, value:i64) -> ! where F:Fn<(i64,),Output = ! > { task(value) }
        pub fn main() -> i64 { let mut value = 10; @done: i64 {
            let task = move (value) { @done(value + 32) };
            value = 99; task()
        } }");
    executes("fn apply<F>(task:F, value:i64) -> ! where F:Fn<(i64,),Output = ! > { task(value) }
        pub fn main() -> i64 { let value = 40; @done: i64 {
            apply((extra:i64) -> ! { @done(value + extra) }, 2)
        } }");
}

#[test]
fn fusion_is_required_in_unobserved_but_well_typed_branches_too() {
    for flag in ["Yes", "No"] {
        executes(&format!("enum Flag {{ Yes, No }} fn apply<F>(task:F) -> ! where F:Fn<(),Output = ! > {{ task() }}
            pub fn main() -> i64 {{ @done: i64 {{ handle Flag::{flag} {{
                Flag::Yes => apply(() -> ! {{ @done(42) }}), Flag::No => 42
            }} }} }}"));
    }
}

#[test]
fn replacing_a_callable_cannot_reuse_its_initial_code_identity() {
    executes("pub fn main() -> i64 { @done: i64 {
        let mut task: () -> ! = () -> ! { @done(41) };
        task = () -> ! { @done(42) }; task()
    } }");
    executes("enum Flag { Yes, No } fn select(flag:Flag) -> i64 { @done: i64 {
        let mut task: () -> ! = () -> ! { @done(41) };
        handle flag { Flag::Yes => { task = () -> ! { @done(42) }; () }, Flag::No => () }; task()
    } } pub fn main() -> i64 { select(Flag::Yes) }");
}

#[test]
fn structural_callable_parameters_and_results_keep_their_selected_environment() {
    executes("fn keep(task: () -> ! ) -> () -> ! { task }
        fn apply(task: () -> ! ) -> ! { task() }
        pub fn main() -> i64 { @done: i64 {
            let task = keep(() -> ! { @done(42) }); apply(task)
        } }");
}

#[test]
fn borrowed_receivers_keep_the_original_control_environment() {
    executes("pub fn main() -> i64 { let value = 42; @done: i64 {
        let task = () -> ! { @done(value) }; let receiver = &task; receiver()
    } }");
    executes("pub fn main() -> i64 { let mut value = 40; @done: i64 {
        let mut task = () -> ! { value = value + 2; @done(value) };
        let receiver = &mut task; receiver()
    } }");
}

#[test]
fn fused_transfers_dispose_resident_captures_exactly_once() {
    executes("struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        pub fn main() -> i64 { let mut count = 41;
            @done: () { let probe = Probe { target: &mut count };
                let task = move (probe) { let observation = &probe; @done(()) }; task()
            }; count
        }");
}

#[test]
fn fused_label_payloads_retain_the_callers_backing_loan() {
    executes("pub fn main() -> i64 { let value = 42;
        let result = @done: &i64 {
            let task = () -> ! { @done(&value) }; task()
        }; *result
    }");
    executes("pub fn main() -> i64 { let value = (10,42);
        let result = @done: &i64 {
            let task = () -> ! { @done(&value.1) }; task()
        }; *result
    }");
}

#[test]
fn equal_copied_contents_do_not_grant_a_backing_loan() {
    for source in [
        "pub fn main() -> i64 { let value = 42;
            let result = @done: &i64 {
                let task = () -> ! { let reference = &value; let copied = *reference; @done(&copied) }; task()
            }; *result
        }",
        "pub fn main() -> i64 { let value = 42;
            let result = @done: &i64 {
                let task = move (value) { @done(&value) }; task()
            }; *result
        }",
    ] {
        for optimization in [0, 2] {
            let error = StageZeroCompiler::new().compile(request(&format!("#![no_std]\n{source}"), optimization)).unwrap_err();
            assert!(error.diagnostics().iter().any(|diagnostic|
                matches!(diagnostic.code, "G5013" | "G5023")), "{error:#?}");
        }
    }
}

#[test]
fn fusion_does_not_erase_invalid_source_ownership() {
    let source = "#![no_std]
        struct Token { value:i64 } impl Use<[1,1]> for Token {}
        fn consume(value:Token) -> i64 { let Token { value: result } = value; result }
        pub fn main() -> i64 { let value = Token { value:42 }; @done: i64 {
            let task = () -> ! { consume(value); @done(consume(value)) }; task()
        } }";
    for optimization in [0, 2] {
        let error = StageZeroCompiler::new().compile(request(source, optimization)).unwrap_err();
        assert!(error.diagnostics().iter().any(|diagnostic|
            diagnostic.code == "G5003"), "{error:#?}");
    }
}

#[test]
fn fused_owned_captures_execute_in_native_and_mixed_programs() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std]
        struct Token { value:i64 } impl Use<[1,1]> for Token {}
        fn consume(value:Token) -> i64 { let Token { value: result } = value; result }
        fn apply<F>(task:F) -> ! where F:Fn<(),Output = ! > { task() }
        fn compute() -> i64 { let value = Token { value:42 }; @done: i64 { apply(() -> ! { @done(consume(value)) }) } }
        fn finish(value:i64) -> i64 { let marker = 41003; value }
        pub fn main() -> i64 { finish(compute()) }";
    for optimization in [0, 2] {
        for mixed in [false, true] {
            let selected = std::cell::Cell::new(0);
            let ir = StageZeroCompiler::new().compile_llvm_partitioned(request(source, optimization), LlvmTarget::host().unwrap(), |function| {
                let use_vm = mixed && function.instructions.iter().any(|instruction| matches!(instruction,
                    grandiose_stage0::VmInstruction::ConstI64 { value: 41003, .. }));
                if use_vm { selected.set(selected.get() + 1); }
                use_vm
            }).unwrap_or_else(|error| panic!("O{optimization}, mixed={mixed}: {error:#?}"));
            assert_eq!(selected.get() > 0, mixed, "mixed execution must really cross a VM boundary");
            assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
        }
    }
}
