//! Deep handler re-entry and independent auditing of every resumed suffix.
use grandiose_stage0::{
    CandidateVmProgram, CompilationMode, CompilationRequest, CompilerBuildIdentity, DefKey, Digest,
    LogicalPath, PackageKey, SourceInput, StageZeroCompiler, VmArtifactError, VmContinuationPolicy,
    VmInstruction, VmType, decode_and_verify_program, decode_program, verify_vm_program,
};

const THREE_PERFORMANCES: &str = r#"
    effect Tick { [1,1] tick(i64) -> i64; }
    pub fn main() -> i64 {
        handle {
            let a = Tick::tick(10);
            let b = Tick::tick(12);
            let c = Tick::tick(20);
            a + b + c
        } { Tick::tick(value, k) => k(value) }
    }
"#;

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("handler-reentry@0.1.0".into());
    CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"handler-reentry")),
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

fn candidate(source: &str) -> CandidateVmProgram {
    let request = request(source);
    let outcome = StageZeroCompiler::new().compile(request.clone()).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    let bytes = artifact.canonical_bytes();
    assert_eq!(
        decode_and_verify_program(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    // Exercise the same verified graph across both engine directions. The
    // entry installs handlers while helpers may perform in another engine.
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let decoded = decode_program(&bytes).unwrap();
    let all_native = StageZeroCompiler::new().compile_llvm(request, LlvmTarget::host().unwrap()).unwrap();
    for selected in [
        std::collections::BTreeSet::new(),
        std::collections::BTreeSet::from([decoded.entry]),
        decoded.functions.keys().copied().filter(|key| *key != decoded.entry).collect(),
    ] {
        let ir = all_native.with_vm_functions(selected).unwrap();
        for optimization in [0, 2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap_or_else(|error|
                panic!("O{optimization}: {source}\n{error:#?}")), 42);
        }
    }
    decode_program(&bytes).unwrap()
}

#[test]
fn one_clause_resumes_three_distinct_performance_sites() {
    candidate(THREE_PERFORMANCES);
}

#[test]
fn explicit_resumption_returns_the_transformed_completion_result() {
    candidate("effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask(k) => k(40) + 1 } }");
}

#[test]
fn ordinary_helpers_transport_and_invoke_the_same_resumption_authority() {
    let program = candidate("effect Ask { [1,1] ask() -> i64; }
        fn apply<F>(task:F, value:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { task(value) }
        fn relay<F>(task:F, value:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { apply(task,value) }
        pub fn main() -> i64 { handle Ask::ask() {
            Ask::ask() with k => relay(k,40) + 2
        } }");
    assert!(program.functions.values().filter(|function| function.instructions.iter().any(|instruction|
        matches!(instruction, VmInstruction::CallOwned { arguments, .. }
            if arguments.iter().any(|argument| matches!(function.registers[*argument as usize], VmType::Callable { .. }))))).count() >= 2,
        "the proof must support ordinary executable frames, not require source inlining");
}

#[test]
fn ordinary_helpers_return_resumption_products_to_their_live_owner() {
    candidate("effect Ask { [1,1] ask() -> i64; }
        fn keep<T>(value:T) -> T { value }
        pub fn main() -> i64 { handle Ask::ask() {
            Ask::ask() with k => { let returned = keep((7,k)); returned.1(40) + 2 }
        } }");
}

#[test]
fn ordinary_helpers_preserve_completion_abi_and_branch_invocations() {
    candidate("struct Answer { value:i64 } effect Ask { [1,1] ask() -> i64; }
        fn apply<F,R>(task:F, choice:i64) -> R where F:Fn<(i64,),Output=R,Effects={}> {
            handle choice { 0 => task(40), _ => task(40) }
        }
        pub fn main() -> i64 { let answer = handle Ask::ask() {
            value => Answer { value:value + 2 }, Ask::ask() with k => apply(k,0)
        }; answer.value }");
}

#[test]
fn ordinary_helpers_cannot_erase_a_required_resumption_invocation() {
    let source = "effect Ask { [1,1] ask() -> i64; }
        fn ignore<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { 42 }
        pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => ignore(k) } }";
    let error = StageZeroCompiler::new().compile(request(source)).unwrap_err();
    assert!(format!("{error:?}").contains("G5012"), "{error:?}");
}

#[test]
fn decoded_helper_mutation_cannot_forge_a_guaranteed_resumption() {
    let mut program = candidate("effect Ask { [1,1] ask() -> i64; }
        fn apply<F>(task:F, choice:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> {
            handle choice { 0 => task(42), _ => task(42) }
        }
        pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => apply(k,0) } }");
    let helper = program.functions.values_mut().find(|function|
        function.parameters == 2 && function.instructions.iter().any(|instruction| matches!(instruction, VmInstruction::CallIndirectOwned { .. }))).unwrap();
    assert_eq!(helper.instructions.iter().filter(|instruction| matches!(instruction, VmInstruction::CallIndirectOwned { .. })).count(), 2);
    let call = helper.instructions.iter_mut().find(|instruction| matches!(instruction, VmInstruction::CallIndirectOwned { .. })).unwrap();
    let VmInstruction::CallIndirectOwned { dst, .. } = call else { unreachable!() };
    *call = VmInstruction::ConstI64 { dst:*dst, value:42 };
    program.fingerprint = program.computed_fingerprint();
    assert!(verify_vm_program(program.clone()).is_err(), "removing a helper invocation must leave the handler suspended");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&program)).is_err());
}

#[test]
fn each_replay_runs_completion_before_returning_to_its_clause() {
    candidate("effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask(k) => k(19) + k(21) } }");
}

#[test]
fn completion_changes_the_resumption_result_type() {
    candidate("struct Answer { value: i64 } effect Ask { [1,1] ask() -> i64; } fn transformed() -> Answer { handle Ask::ask() { value => Answer { value: value + 2 }, Ask::ask(k) => k(40) } } pub fn main() -> i64 { transformed().value }");
}

#[test]
fn cancellation_bypasses_nonidentity_completion() {
    candidate("effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 100, Ask::ask(_) => 42 } }");
}

#[test]
fn reentry_applies_completion_once_to_the_protected_result() {
    candidate(&THREE_PERFORMANCES.replace("a + b + c", "a + b + c - 1").replace("{ Tick::tick(value, k)", "{ result => result + 1, Tick::tick(value, k)"));
}

#[test]
fn completion_of_a_resumed_helper_call_returns_to_the_clause() {
    candidate("effect Ask { [1,1] ask() -> i64; } fn helper() -> i64 / Ask { Ask::ask() + 1 } pub fn main() -> i64 { handle helper() { value => value + 1, Ask::ask(k) => k(39) + 1 } }");
}

#[test]
fn effectful_completion_runs_inside_an_outer_resumption() {
    candidate("effect Ask { [1,1] ask() -> i64; } effect Add { [1,1] add(i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask() { value => Add::add(value), Ask::ask(k) => k(40) + 1 } } { Add::add(value, k) => k(value + 1) } }");
}

#[test]
fn repeated_pattern_dispatch_retains_first_match_and_forwarding() {
    candidate(&THREE_PERFORMANCES.replace(
        "Tick::tick(value, k) => k(value)",
        "Tick::tick(0, k) => k(100), Tick::tick(value, k) => k(value)",
    ));
}

#[test]
fn reentrant_clause_suffixes_return_through_their_own_resumptions() {
    candidate(
        &THREE_PERFORMANCES
            .replace("tick(20)", "tick(17)")
            .replace("=> k(value)", "=> k(value) + 1"),
    );
}

#[test]
fn optional_cancellation_exits_before_a_later_performance() {
    candidate(
        "effect Ask { [0,1] ask(i64) -> i64; } pub fn main() -> i64 { handle { let a = Ask::ask(1); let b = Ask::ask(2); a + b } { Ask::ask(1, _) => 42, Ask::ask(value, k) => k(value) } }",
    );
}

#[test]
fn shared_payloads_keep_their_original_owner_across_resumed_helpers() {
    candidate("effect Ask { [1,1] ask(value:&i64) -> &i64; }
        fn leaf(value:&i64) -> i64 / Ask { let returned = Ask::ask(value); *returned + 2 }
        fn relay(value:&i64) -> i64 / Ask { leaf(value) }
        pub fn main() -> i64 { let value = 40; handle relay(&value) {
            Ask::ask(payload) with k => { let resume = (value:&i64) -> i64 { k(value) }; resume(payload) }
        } }");
}

#[test]
fn returning_resumptions_use_the_clauses_current_outer_handlers() {
    candidate("effect Ask { [1,1] ask() -> i64; } effect Log { [1,1] log(value:i64) -> i64; }
        fn leaf() -> i64 / Log { handle { let answer = Ask::ask(); Log::log(answer) } {
            Ask::ask() with k => { let saved = k; handle saved(41) { Log::log(value) => 42 } }
        } } pub fn main() -> i64 { handle leaf() { Log::log(value) => 99 } }");
}

#[test]
fn resumed_writes_reach_enclosing_source_storage() {
    candidate("effect Ask { [1,1] ask() -> i64; }
        fn relay(target:&mut i64) -> i64 / Ask { let value = Ask::ask(); *target = *target + 10; value }
        pub fn main() -> i64 { let mut count = 30;
            let answer = handle relay(&mut count) { Ask::ask() with k => k(1) * 2 }; count + answer }");
}

#[test]
fn three_shot_replay_restores_each_suspended_aggregate() {
    candidate("effect Ask { [3,3] ask() -> i64; }
        fn relay(value:(i64,i64)) -> i64 / Ask { let selected = Ask::ask(); value.0 + value.1 + selected }
        pub fn main() -> i64 { handle relay((5,6)) { Ask::ask(k) => k(2) + k(3) + k(4) } }");
}

#[test]
fn partial_inner_patterns_forward_to_the_exact_outer_instance() {
    candidate("effect Ask<T> { [1,1] ask(value:T) -> T; }
        fn leaf() -> i64 / {Ask<i64>,Ask<u64>} {
            let ignored = Ask<u64>::ask(1); Ask<i64>::ask(40)
        }
        pub fn main() -> i64 { handle { handle leaf() {
            Ask<i64>::ask(0) with k => k(100)
        } } { Ask<u64>::ask(value) with k => k(value), Ask<i64>::ask(value) with k => k(value + 2) } }");
}

#[test]
fn later_resumed_suffix_cannot_read_an_uninitialized_register() {
    let mut program = candidate(THREE_PERFORMANCES);
    let entry = program.functions.get_mut(&program.entry).unwrap();
    let last_perform = entry
        .instructions
        .iter()
        .rposition(|instruction| matches!(instruction, VmInstruction::PerformOwned { .. }))
        .unwrap();
    let uninitialized = entry.registers.len() as u32;
    entry.registers.push(VmType::I64);
    entry.instructions[last_perform + 1] = VmInstruction::Return {
        value: uninitialized,
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(
        matches!(verify_vm_program(program), Err(VmArtifactError::ReadBeforeWrite { register }) if register == uninitialized)
    );
}

#[test]
fn later_completion_cannot_violate_the_resumption_result_abi() {
    let mut program = candidate(THREE_PERFORMANCES);
    let entry = program.functions.get_mut(&program.entry).unwrap();
    let flag = entry
        .instructions
        .iter()
        .find_map(|instruction| match instruction {
            VmInstruction::SetDropFlag { flag, .. } => Some(*flag),
            _ => None,
        })
        .unwrap();
    let mut pc = entry
        .instructions
        .iter()
        .rposition(|instruction| matches!(instruction, VmInstruction::PerformOwned { .. }))
        .unwrap()
        + 1;
    let mut visited = std::collections::BTreeSet::new();
    loop {
        assert!(visited.insert(pc), "completion suffix unexpectedly loops");
        match entry.instructions[pc] {
            VmInstruction::CompleteHandler { .. } => {
                entry.instructions[pc] = VmInstruction::CompleteHandler { value: flag };
                break;
            }
            VmInstruction::Jump { target } => pc = target as usize,
            _ => pc += 1,
        }
    }
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::TypeMismatch {
            expected: VmType::I64,
            found: VmType::Bool,
            ..
        })
    ));
}

#[test]
fn resumed_backedge_cannot_reinstall_an_already_live_frame_brand() {
    let mut program = candidate(THREE_PERFORMANCES);
    let entry = program.functions.get_mut(&program.entry).unwrap();
    let install = entry
        .instructions
        .iter()
        .position(|instruction| matches!(instruction, VmInstruction::InstallHandlerOwned { .. }))
        .unwrap();
    let perform = entry
        .instructions
        .iter()
        .position(|instruction| matches!(instruction, VmInstruction::PerformOwned { .. }))
        .unwrap();
    entry.instructions[perform + 1] = VmInstruction::Jump {
        target: install as u32,
    };
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::HandlerStateMismatch)
    ));
}

#[test]
fn repeated_reentry_reaches_a_finite_static_fixed_point() {
    let suffix = "Tick::tick(0); ".repeat(11);
    candidate(&format!(
        "effect Tick {{ [1,1] tick(i64) -> i64; }} pub fn main() -> i64 {{ handle {{ {suffix} Tick::tick(42) }} {{ Tick::tick(value, k) => k(value) }} }}"
    ));
}

#[test]
fn ordinary_control_flow_still_rejects_incompatible_handler_stacks() {
    let mut program = candidate(THREE_PERFORMANCES);
    let entry = program.functions.get_mut(&program.entry).unwrap();
    entry.registers = vec![VmType::Bool, VmType::I64];
    entry.instructions = vec![
        VmInstruction::DeclareResult {
            result: VmType::I64,
            returns: true,
        },
        VmInstruction::ConstBool {
            dst: 0,
            value: true,
        },
        VmInstruction::ConstI64 { dst: 1, value: 42 },
        VmInstruction::BranchBool {
            condition: 0,
            then_target: 4,
            else_target: 6,
        },
        VmInstruction::InstallHandler {
            effect: DefKey(Digest::of_bytes(b"ordinary-join-effect")),
            effect_arguments: vec![],
            operation: 0,
            payload_destinations: vec![],
            resume_type: VmType::I64,
            continuation: VmContinuationPolicy::Consume,
            target: 8,
        },
        VmInstruction::Jump { target: 6 },
        VmInstruction::Return { value: 1 },
        VmInstruction::Trap,
        VmInstruction::Resume { value: 1 },
    ];
    program.fingerprint = program.computed_fingerprint();
    assert!(matches!(
        verify_vm_program(program),
        Err(VmArtifactError::HandlerStateMismatch)
    ));
}
