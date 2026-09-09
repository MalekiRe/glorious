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

fn candidate(source: &str) -> CandidateVmProgram {
    let package = PackageKey("handler-reentry@0.1.0".into());
    let outcome = StageZeroCompiler::new()
        .compile(CompilationRequest {
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
        })
        .unwrap();
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
