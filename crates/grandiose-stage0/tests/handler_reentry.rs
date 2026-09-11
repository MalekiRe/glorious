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
    let outcome = StageZeroCompiler::new().compile(request.clone()).unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42, "{source}");
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
fn replay_resumptions_cross_multiple_ordinary_helper_calls() {
    let original = candidate("effect Ask { [2,2] ask() -> i64; }
        fn apply<F>(task:F, value:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { task(value) }
        pub fn main() -> i64 { handle Ask::ask() {
            value => value + 1, Ask::ask() with k => apply(k,19) + apply(k,21)
        } }");
    for policy in [VmContinuationPolicy::Optional, VmContinuationPolicy::Consume] {
        let mut malformed = original.clone();
        let mut changed = false;
        for function in malformed.functions.values_mut() {
            for instruction in &mut function.instructions {
                if let VmInstruction::InstallHandlerOwned { continuation, .. } = instruction
                    && matches!(continuation, VmContinuationPolicy::Replay { .. }) {
                    *continuation = policy;
                    changed = true;
                }
            }
        }
        assert!(changed);
        malformed.fingerprint = malformed.computed_fingerprint();
        assert!(verify_vm_program(malformed.clone()).is_err());
        assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&malformed)).is_err());
    }
    let mut malformed = original;
    let retained = malformed.functions.values_mut().flat_map(|function| &mut function.instructions)
        .find(|instruction| matches!(instruction, VmInstruction::RetainResumption { fields, .. } if fields.is_empty())).unwrap();
    let VmInstruction::RetainResumption { dst, src, .. } = retained else { unreachable!() };
    *retained = VmInstruction::Copy { dst: *dst, src: *src };
    malformed.fingerprint = malformed.computed_fingerprint();
    let copy_result = verify_vm_program(malformed.clone());
    assert!(matches!(copy_result, Err(VmArtifactError::AffineValueCopy { .. })), "{copy_result:#?}");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&malformed)).is_err());
}

fn replay_transport_binding(binding: &str, callee: &str) {
        candidate(&format!("effect Ask {{ [2,2] ask() -> i64; }}
            fn keep<T>(value:T) -> T {{ value }}
            fn apply<F>(task:F, value:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={{}}> {{ task(value) }}
            pub fn main() -> i64 {{ handle Ask::ask() {{
                value => value + 1, Ask::ask() with k => {{ {binding} apply({callee},19) + apply({callee},21) }}
            }} }}"));
}

#[test]
fn replay_helper_transport_preserves_aliases() { replay_transport_binding("let saved = k;", "saved"); }
#[test]
fn replay_helper_transport_preserves_products() { replay_transport_binding("let saved = (7,k);", "saved.1"); }
#[test]
fn replay_helper_transport_preserves_returned_handles() { replay_transport_binding("let saved = keep(k);", "saved"); }

#[test]
fn one_ordinary_helper_can_perform_both_ordered_replays() {
    candidate("effect Ask { [2,2] ask() -> i64; }
        fn twice<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { task(19) + task(21) }
        pub fn main() -> i64 { handle Ask::ask() {
            value => value + 1, Ask::ask() with k => twice(k)
        } }");
}

fn reject_changed_replay_counts(original: &CandidateVmProgram, counts: &[u32]) {
    for &uses in counts {
        let mut malformed = original.clone();
        let mut changed = false;
        for instruction in malformed.functions.values_mut().flat_map(|function| &mut function.instructions) {
            if let VmInstruction::InstallHandlerOwned { continuation, .. } = instruction
                && matches!(continuation, VmContinuationPolicy::Replay { .. }) {
                *continuation = VmContinuationPolicy::Replay { uses };
                changed = true;
            }
        }
        assert!(changed);
        malformed.fingerprint = malformed.computed_fingerprint();
        assert!(verify_vm_program(malformed.clone()).is_err(), "accepted exact replay count {uses}");
        assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&malformed)).is_err());
    }
}

#[test]
fn decoded_replay_policy_cannot_under_or_over_count_ordered_helper_uses() {
    let original = candidate("effect Ask { [3,3] ask() -> i64; }
        fn thrice<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { task(12) + task(14) + task(16) }
        pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => thrice(k) } }");
    reject_changed_replay_counts(&original, &[2, 4]);
}

#[test]
fn decoded_replay_counts_are_checked_for_performances_in_an_ordinary_callee() {
    let source = "effect Ask { [3,3] ask() -> i64; }
        fn leaf() -> i64 / Ask { Ask::ask() }
        pub fn main() -> i64 { handle leaf() { Ask::ask() with k => k(12) + k(14) + k(16) } }";
    let original = candidate(source);
    reject_changed_replay_counts(&original, &[2, 4]);
    let mut unavailable_result = original;
    let entry = unavailable_result.functions.get_mut(&unavailable_result.entry).unwrap();
    let call_result = entry.instructions.iter().find_map(|instruction| match instruction {
        VmInstruction::CallOwned { dst, .. } => Some(*dst), _ => None,
    }).unwrap();
    let clause = entry.instructions.iter().find_map(|instruction| match instruction {
        VmInstruction::InstallHandlerOwned { target, .. } => Some(*target as usize), _ => None,
    }).unwrap();
    let instruction = entry.instructions[clause..].iter_mut().find(|instruction|
        matches!(instruction, VmInstruction::ConstI64 { .. })).unwrap();
    let VmInstruction::ConstI64 { dst, .. } = instruction else { unreachable!() };
    *instruction = VmInstruction::Copy { dst: *dst, src: call_result };
    unavailable_result.fingerprint = unavailable_result.computed_fingerprint();
    let error = verify_vm_program(unavailable_result.clone()).unwrap_err();
    assert!(matches!(error, VmArtifactError::UseAfterMove { .. } | VmArtifactError::ReadBeforeWrite { .. }),
        "a clause cannot read the future normal call result: {error:?}");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&unavailable_result)).is_err());
}

#[test]
fn cross_frame_replay_preserves_the_ordinary_callee_result_abi() {
    let original = candidate("effect Ask { [3,3] ask() -> Bool; }
        fn leaf() -> (i64,) / Ask { handle Ask::ask() { true => (14,), false => (0,) } }
        fn relay() -> (i64,) / Ask { leaf() }
        pub fn main() -> i64 { handle relay().0 { Ask::ask() with k => k(true) + k(true) + k(true) } }");
    reject_changed_replay_counts(&original, &[2, 4]);
}

#[test]
fn indirect_callee_effect_rows_cannot_hide_replay_clause_audits() {
    let original = candidate("effect Ask { [3,3] ask() -> i64; }
        fn leaf() -> i64 / Ask { Ask::ask() }
        fn invoke<F>(task:F) -> i64 / Ask where F:Fn<(),Output=i64,Effects={Ask}> { task() }
        pub fn main() -> i64 { handle invoke(leaf) { Ask::ask() with k => k(12) + k(14) + k(16) } }");
    reject_changed_replay_counts(&original, &[2, 4]);
    reject_concealed_callee_effect_rows(original);
}

#[test]
fn indirect_replay_preserves_a_specialized_copy_capture_environment() {
    candidate("effect Ask { [3,3] ask() -> i64; }
        fn invoke<F>(task:F) -> i64 / Ask where F:Fn<(),Output=i64,Effects={Ask}> { task() }
        pub fn main() -> i64 {
            let number=14;
            let task=move(number) { number + Ask::ask() };
            handle invoke(task) { Ask::ask() with k => k(0)+k(0)+k(0) }
        }");
}

#[test]
fn indirect_callee_effect_rows_cannot_hide_one_shot_clause_audits() {
    let original = candidate("effect Ask { [1,1] ask() -> i64; }
        fn leaf() -> i64 / Ask { Ask::ask() }
        fn invoke<F>(task:F) -> i64 / Ask where F:Fn<(),Output=i64,Effects={Ask}> { task() }
        pub fn main() -> i64 { handle invoke(leaf) { Ask::ask() with k => k(42) } }");
    reject_concealed_callee_effect_rows(original);
}

fn reject_concealed_callee_effect_rows(mut concealed: CandidateVmProgram) {
    let mut changed = false;
    for function in concealed.functions.values_mut() {
        for ty in &mut function.registers {
            if let VmType::Callable { effects, .. } = ty && !effects.effects.is_empty() {
                **effects = Default::default();
                changed = true;
            }
        }
    }
    assert!(changed);
    concealed.fingerprint = concealed.computed_fingerprint();
    let error = verify_vm_program(concealed.clone()).unwrap_err();
    assert!(matches!(error, VmArtifactError::MalformedEncoding {
        message: "callable effect row conceals an executable performance",
    }), "{error:?}");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&concealed)).is_err());
}

#[test]
fn partial_callee_handler_forwards_to_its_callers_delimiter() {
    candidate("effect Ask { [1,1] ask(value:i64) -> i64; }
        fn leaf() -> i64 / Ask { Ask::ask(40) }
        fn relay() -> i64 / Ask { handle leaf() { Ask::ask(0) with k => k(100) } }
        pub fn main() -> i64 { handle relay() { Ask::ask(value) with k => k(value + 2) } }");
}

#[test]
fn ordered_replay_helpers_compose_with_forwarded_product_aliases() {
    candidate("effect Ask { [2,2] ask() -> i64; }
        fn keep<T>(value:T) -> T { value }
        fn twice<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> {
            let saved = (keep(task),); saved.0(19) + saved.0(21)
        }
        fn relay<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { twice(task) }
        pub fn main() -> i64 { handle Ask::ask() {
            value => value + 1, Ask::ask() with k => relay(k)
        } }");
}

#[test]
fn ordinary_generic_field_invocation_preserves_the_capture_environment() {
    candidate("fn twice<F>(task:F) -> i64 where F:Fn<(),Output=i64,Effects={}> {
            let saved = (task,); saved.0() + saved.0()
        }
        pub fn main() -> i64 {
            let mut count = 20;
            let task = () -> i64 { count = count + 1; count };
            twice(task) - 1
        }");
}

#[test]
fn computed_field_receiver_is_evaluated_once_before_its_arguments() {
    candidate("fn answer(value:i64) -> i64 { value }
        fn receiver(count:&mut i64) -> ((i64)->i64,) {
            *count = *count * 10 + 1; (answer,)
        }
        fn argument(count:&mut i64) -> i64 { *count = *count * 10 + 2; 30 }
        pub fn main() -> i64 {
            let mut count = 0;
            let result = receiver(&mut count).0(argument(&mut count));
            result + count
        }");
}

fn replaced_argument_candidate(invocation: &str) {
    candidate(&format!("fn first(value:i64) -> i64 {{42}}
            fn second(value:i64) -> i64 {{0}}
            fn invoke<F>(task:F, value:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={{}}> {{task(value)}}
            pub fn main() -> i64 {{
                let mut callback:(i64)->i64=first;
                let replacement:(i64)->i64=second;
                {invocation}
            }}"));
}

#[test]
fn argument_snapshot_survives_later_source_replacement() {
    replaced_argument_candidate("invoke(callback, {callback=replacement; 0})");
}

#[test]
fn aggregate_snapshot_survives_later_source_replacement() {
    replaced_argument_candidate("{let saved=(callback, {callback=replacement; 0}); invoke(saved.0, saved.1)}");
}

#[test]
fn factory_capture_snapshots_preserve_their_resumption_input() {
    candidate("effect Ask { [1,1] ask() -> i64; }
        fn wrap<F>(task:F) -> () -> i64 where F:Fn<(i64,),Output=i64,Effects={}> {
            move(task) {task(42)}
        }
        pub fn main() -> i64 {handle Ask::ask() {Ask::ask() with k => wrap(k)()}}");
}

#[test]
fn prepared_receiver_keeps_the_value_selected_before_argument_mutation() {
    candidate("fn first(value:i64) -> i64 { 42 }
        fn second(value:i64) -> i64 { 0 }
        pub fn main() -> i64 {
            let mut callback: (i64)->i64 = first;
            let replacement: (i64)->i64 = second;
            callback({ callback = replacement; 0 })
        }");
}

#[test]
fn prepared_receiver_keeps_captures_before_argument_replacement() {
    candidate("pub fn main() -> i64 {
            let first = 42;
            let second = 0;
            let mut callback:(i64)->i64 = (argument:i64)->i64 {first};
            let replacement:(i64)->i64 = (argument:i64)->i64 {second};
            callback({callback = replacement; 0})
        }");
}

#[test]
fn repeated_owned_receiver_invocation_preserves_mutable_capture_storage() {
    candidate("pub fn main() -> i64 {
        let mut count = 19;
        let task = move(count) {count = count + 1; count};
        task() + task() + 1
    }");
}

#[test]
fn prepared_borrowed_receiver_keeps_its_selected_reference_handle() {
    candidate("fn first(value:i64) -> i64 {42}
        fn second(value:i64) -> i64 {0}
        pub fn main() -> i64 {
            let first:(i64)->i64=first;
            let second:(i64)->i64=second;
            let mut callback = &first;
            callback({callback = &second; 0})
        }");
}

#[test]
fn field_receiver_prepared_before_an_argument_performance_survives_replay() {
    candidate("effect Ask { [2,2] ask() -> i64; }
        fn answer(value:i64) -> i64 { value }
        pub fn main() -> i64 {
            handle {
                let callback: (i64)->i64 = answer;
                let saved = (callback,);
                saved.0(Ask::ask())
            } { Ask::ask() with k => k(19) + k(23) }
        }");
}

#[test]
fn ordered_replay_helpers_compose_with_forwarded_handles() {
    candidate("effect Ask { [2,2] ask() -> i64; }
        fn keep<T>(value:T) -> T { value }
        fn twice<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> {
            let saved = keep(task); saved(19) + saved(21)
        }
        fn relay<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { twice(task) }
        pub fn main() -> i64 { handle Ask::ask() {
            value => value + 1, Ask::ask() with k => relay(k)
        } }");
}

#[test]
fn ordered_helper_inputs_can_alias_the_same_replay_budget() {
    candidate("effect Ask { [2,2] ask() -> i64; }
        fn both<A,B>(first:A, second:B) -> i64
            where A:Fn<(i64,),Output=i64,Effects={}>, B:Fn<(i64,),Output=i64,Effects={}> {
            second(19) + first(21)
        }
        pub fn main() -> i64 { handle Ask::ask() {
            value => value + 1, Ask::ask() with k => both(k,k)
        } }");
}

#[test]
fn ordered_replay_helper_branches_remain_distinct_execution_alternatives() {
    for choice in ["0", "1"] {
        candidate(&format!("effect Ask {{ [2,2] ask() -> i64; }}
            fn choose<F>(task:F, choice:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={{}}> {{
                handle choice {{ 0 => task(19) + task(21), _ => task(21) + task(19) }}
            }}
            pub fn main() -> i64 {{ handle Ask::ask() {{
                value => value + 1, Ask::ask() with k => choose(k,{choice})
            }} }}"));
    }
}

#[test]
fn optional_resumption_cancellation_inside_an_ordinary_helper() {
    let source = "effect Ask { [0,1] ask() -> i64; }
        fn choose<F>(task:F, choice:i64) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> {
            handle choice { 0 => 42, _ => task(42) }
        }
        pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => choose(k,0) } }";
    let mut program = candidate(source);
    let mut missing_disposal = program.clone();
    let helper = missing_disposal.functions.values_mut().find(|function| function.parameters == 2).unwrap();
    for instruction in &mut helper.instructions {
        if let VmInstruction::DestroyCallable { dst, .. } = instruction {
            *instruction = VmInstruction::ConstUnit { dst: *dst };
        }
    }
    missing_disposal.fingerprint = missing_disposal.computed_fingerprint();
    assert!(verify_vm_program(missing_disposal.clone()).is_err());
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&missing_disposal)).is_err());
    for function in program.functions.values_mut() {
        for instruction in &mut function.instructions {
            if let VmInstruction::InstallHandlerOwned { continuation, .. } = instruction
                && *continuation == VmContinuationPolicy::Optional {
                *continuation = VmContinuationPolicy::Consume;
            }
        }
    }
    program.fingerprint = program.computed_fingerprint();
    assert!(verify_vm_program(program.clone()).is_err(), "cancellation must not discharge an exact-once policy");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&program)).is_err());
    candidate(&source.replace("choose(k,0)", "choose(k,1)"));
}

#[test]
fn optional_helper_cancellation_destroys_protected_owners_once() {
    let source = "use std::*;
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        effect Ask { [0,1] ask() -> i64; }
        fn ignore<F>(task:F) -> i64 where F:Fn<(i64,),Output=i64,Effects={}> { 41 }
        fn worker(target: &mut i64) -> i64 / Ask { let owner = Probe { target: target }; Ask::ask() }
        pub fn main() -> i64 {
            let mut count = 0;
            let result = handle { let owner = Probe { target: &mut count }; Ask::ask() }
                { Ask::ask() with k => ignore(k) };
            result + count
        }";
    candidate(source);
    candidate(&source.replace("handle { let owner = Probe { target: &mut count }; Ask::ask() }", "handle worker(&mut count)"));
}

#[test]
fn borrowed_resumption_handles_can_cross_a_noninvoking_helper() {
    let mut program = candidate("effect Ask { [1,1] ask() -> i64; }
        fn observe<T>(value:&T) -> i64 { 2 }
        pub fn main() -> i64 { handle Ask::ask() {
            Ask::ask() with k => { let extra = observe(&k); k(40) + extra }
        } }");
    // Remove the observer call so that changing the borrow's permission
    // cannot fail merely because the helper expects a shared parameter.
    let entry = program.functions.get_mut(&program.entry).unwrap();
    for instruction in &mut entry.instructions {
        if let VmInstruction::CallOwned { dst, .. } = instruction {
            *instruction = VmInstruction::ConstI64 { dst: *dst, value: 2 };
        }
    }
    program.fingerprint = program.computed_fingerprint();
    verify_vm_program(program.clone()).unwrap();
    let entry = program.functions.get_mut(&program.entry).unwrap();
    let (dst, unique) = entry.instructions.iter_mut().find_map(|instruction| match instruction {
        VmInstruction::Borrow { dst, unique, .. } => Some((*dst, unique)),
        _ => None,
    }).unwrap();
    *unique = true;
    let borrowed_type = entry.registers[dst as usize].clone();
    for ty in &mut entry.registers {
        if *ty == borrowed_type {
            let VmType::Reference { unique, .. } = ty else { panic!() };
            *unique = true;
        }
    }
    program.fingerprint = program.computed_fingerprint();
    let error = verify_vm_program(program.clone()).unwrap_err();
    assert!(matches!(error, VmArtifactError::HandlerResumeUnavailable), "{error:?}");
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&program)).is_err());
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
        function.parameters == 2 && function.instructions.iter().any(|instruction| matches!(instruction, VmInstruction::CallPrepared { .. }))).unwrap();
    assert_eq!(helper.instructions.iter().filter(|instruction| matches!(instruction, VmInstruction::CallPrepared { .. })).count(), 2);
    let call = helper.instructions.iter_mut().find(|instruction| matches!(instruction, VmInstruction::CallPrepared { .. })).unwrap();
    let VmInstruction::CallPrepared { dst, .. } = call else { unreachable!() };
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
    let mut program = candidate("effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 100, Ask::ask(_) => 42 } }");
    for instruction in &mut program.functions.get_mut(&program.entry).unwrap().instructions {
        if let VmInstruction::InstallHandlerOwned { continuation, .. } = instruction {
            *continuation = VmContinuationPolicy::Consume;
        }
    }
    program.fingerprint = program.computed_fingerprint();
    assert!(verify_vm_program(program.clone()).is_err());
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&program)).is_err());
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
