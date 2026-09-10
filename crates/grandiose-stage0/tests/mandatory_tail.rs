use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, VmExecutionLimits, VmInstruction, decode_and_verify_program,
};

fn compile(
    source: &str,
) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    compile_at(source, "0")
}

fn compile_at(
    source: &str,
    optimization: &str,
) -> Result<grandiose_stage0::CompilationOutcome, grandiose_stage0::ServiceError> {
    StageZeroCompiler::new().compile(request_at(source, optimization))
}

fn request_at(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("mandatory-tail@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"mandatory-tail")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.into())]
            .into_iter()
            .collect(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn run_native(source: &str, optimization: u8) -> i64 {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let ir = StageZeroCompiler::new().compile_llvm(request_at(source, &optimization.to_string()), LlvmTarget::host().unwrap())
        .unwrap_or_else(|error| panic!("native O{optimization}: {error:#?}"));
    // SAFETY: execute only the locally checked source in this test.
    let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
    unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0
}

#[test]
fn mandatory_tail_transfers_generic_callback_results_from_incoming_storage() {
    let source = r#"
        fn fold<'a,T,A,F>(item: &'a T, state: A, step: &mut F, remaining: i64) -> A
        where for<'call> &'call mut F: Fn<(A,&'a T),Output=A,Effects={}> {
            handle remaining {
                0 => state,
                _ => { let next = step(state, item); tail fold(item, next, step, remaining - 1) },
            }
        }
        pub fn main() -> i64 {
            let item = 1;
            let mut step = (state: i64, item: &i64) -> i64 { state + *item };
            fold(&item, 40, &mut step, 2)
        }
    "#;
    for optimization in ["0", "2"] {
        let artifact = compile_at(source, optimization)
            .unwrap_or_else(|error| panic!("O{optimization}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

#[test]
fn mandatory_tail_transfers_constructed_optional_incoming_references() {
    let source = r#"
        fn walk<'a,T>(item: &'a T, first: Option<&'a T>, remaining: i64) -> &'a T {
            handle remaining {
                0 => item,
                _ => handle first {
                    Result::Ok(value) => value,
                    Result::Err(_) => tail walk(item, Some(item), remaining - 1),
                },
            }
        }
        pub fn main() -> i64 { let item = 42; *walk(&item, None, 2) }
    "#;
    for optimization in ["0", "2"] {
        let artifact = compile_at(source, optimization)
            .unwrap_or_else(|error| panic!("O{optimization}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        assert_eq!(run_native(source, optimization.parse().unwrap()), 42);
    }
}

#[test]
fn mandatory_tail_retains_nested_incoming_carriers_when_seeding_logical_regions() {
    let source = r#"
        use std::PhantomData;
        struct Inner<T> { value: T }
        struct Outer<T> { value: Inner<T>, marker: PhantomData<T> }
        fn walk<'a,T>(value: Outer<&'a T>, remaining: i64) -> Outer<&'a T> {
            handle remaining { 0 => value, _ => tail walk(value, remaining - 1) }
        }
        pub fn main() -> i64 {
            let item = 42;
            let result = walk(Outer { value: Inner { value: &item }, marker: PhantomData {} }, 2);
            *result.value.value
        }
    "#;
    for optimization in ["0", "2"] {
        let artifact = compile_at(source, optimization)
            .unwrap_or_else(|error| panic!("O{optimization}: {error:#?}")).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        assert_eq!(run_native(source, optimization.parse().unwrap()), 42);
    }
}

#[test]
fn mandatory_tail_keeps_branch_joined_incoming_logical_residents() {
    let source = r#"
        use std::*;
        fn finish<'a,T>(yes: Vec<&'a T>, no: Vec<&'a T>) -> (Vec<&'a T>,Vec<&'a T>) { (yes,no) }
        fn partition<'a,T>(item: &'a T, yes: Vec<&'a T>, no: Vec<&'a T>, flag: Bool)
            -> (Vec<&'a T>,Vec<&'a T>) {
            let mut yes = yes;
            let mut no = no;
            handle flag { true => Vec::push(&mut yes, item), false => Vec::push(&mut no, item) };
            tail finish(yes,no)
        }
        pub fn main() -> i64 {
            let item = 42;
            let (yes,no) = partition(&item, Vec::new(), Vec::new(), false);
            *(*Vec::get_unchecked(&no,0))
        }
    "#;
    for optimization in ["0", "2"] {
        let artifact = compile_at(source, optimization)
            .unwrap_or_else(|error| panic!("O{optimization}: {error:#?}")).artifact.unwrap();
        // SAFETY: this locally compiled fixture uses the bundled Vec raw
        // storage implementation, like the standard-library execution tests.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(run_native(source, optimization.parse().unwrap()), 42);
    }
}

#[test]
fn source_tail_proofs_do_not_treat_local_generic_or_logical_loans_as_incoming() {
    for source in [
        "fn keep<T>(value:T) -> T { value } fn finish(value:&i64) -> i64 { *value } pub fn main() -> i64 { let local=42; let result=keep(&local); tail finish(result) }",
        "fn finish(value:Option<&i64>) -> i64 { handle value { Result::Ok(value) => *value, Result::Err(_) => 0 } } pub fn main() -> i64 { let local=42; tail finish(Some(&local)) }",
        "struct Inner<T> { value:T } struct Outer<T> { value:Inner<T> } fn finish(value:Outer<&i64>) -> i64 { *value.value.value } pub fn main() -> i64 { let local=42; tail finish(Outer { value:Inner { value:&local } }) }",
        "fn finish(value:&i64) -> i64 { *value } fn make<'a>(value:&'a i64) -> () -> &'a i64 { move(value) { value } } pub fn main() -> i64 { let local=42; let callback=make(&local); tail finish(callback()) }",
    ] {
        for optimization in ["0", "2"] {
            let error = compile_at(source, optimization).expect_err("local backing must survive neither generic forwarding nor a logical wrapper");
            assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G4403" | "G5017" | "G5013")),
                "{source}\n{error:#?}");
        }
    }
}

#[test]
fn source_tail_checks_accept_rigid_callback_results_before_runtime_materialization() {
    let source = r#"
        fn relay<T,F>(value:T, body:&F) -> T where for<'a> &'a F:Fn<(T,),Output=T,Effects={}> {
            let value=body(value); tail finish(value)
        }
        fn finish<T>(value:T) -> T { value }
        pub fn main() -> i64 { let body=(value:i64)->i64 { value+1 }; relay(41,&body) }
    "#;
    let mut request = request_at(source, "0");
    request.mode = CompilationMode::Check;
    let outcome = StageZeroCompiler::new().compile(request).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:?}", outcome.diagnostics);
    assert!(outcome.artifact.is_none());
}

#[test]
fn mandatory_mutual_tail_calls_replace_the_activation_without_profiling() {
    let source = "fn first(n: i64, total: i64) -> i64 { handle n { 0 => total, _ => tail second(n - 1, total + 1) } }
        fn second(n: i64, total: i64) -> i64 { handle n { 0 => total, _ => tail first(n - 1, total + 1) } }
        pub fn main() -> i64 { tail first(10000, 0) }";
    let artifact = compile(source).unwrap().artifact.unwrap();
    let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert!(
        grandiose_stage0::decode_program(&artifact.canonical_bytes())
            .unwrap()
            .functions
            .values()
            .any(|function| function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::TailCallOwned { .. })))
    );
    for artifact in [&artifact, &decoded] {
        assert_eq!(
            artifact
                .run_i64_with_limits(VmExecutionLimits {
                    max_call_depth: 2,
                    ..VmExecutionLimits::default()
                })
                .unwrap(),
            10000
        );
    }
}

#[test]
fn mandatory_tail_transfers_incoming_borrows_and_nested_carriers() {
    for source in [
        "fn read(value: &i64) -> i64 { *value }
         fn relay(value: &i64) -> i64 { let alias = value; tail read(&(*alias)) }
         pub fn main() -> i64 { let answer = 42; relay(&answer) }",
        "fn apply(callback: () -> i64) -> i64 { callback() }
         pub fn main() -> i64 { tail apply(() -> i64 { 42 }) }",
        "fn apply(callback: () -> i64) -> i64 { callback() }
         pub fn main() -> i64 { let answer = 42; let callback = () -> i64 { answer }; tail apply(callback) }",
        "fn apply(callback: () -> i64) -> i64 { callback() }
         fn relay(value: &i64) -> i64 { let callback = move (value) { *value }; tail apply(callback) }
         pub fn main() -> i64 { let answer = 42; relay(&answer) }",
        "fn read(value: &i64) -> i64 { *value }
         fn forward<'a>(value: &'a i64, remaining: i64) -> &'a i64 {
             handle remaining { 0 => value, _ => tail forward(value, remaining - 1) }
         }
         fn relay(value: &i64) -> i64 { tail read(forward(value, 10000)) }
         pub fn main() -> i64 { let answer = 42; relay(&answer) }",
        "fn forward<'a>(value: &'a mut i64, remaining: i64) -> &'a mut i64 {
             handle remaining { 0 => value, _ => tail forward(value, remaining - 1) }
         }
         pub fn main() -> i64 { let mut answer = 40; let view = forward(&mut answer, 10000); *view = 42; answer }",
        "fn read(value: &i64) -> i64 { *value }
         fn choose<'a>(first: &'a i64, second: &'a i64, flag: Bool) -> i64 {
             let mut selected = first;
             handle flag { true => { selected = first; }, false => { selected = second; } };
             tail read(selected)
         }
         pub fn main() -> i64 { let answer = 42; choose(&answer, &answer, false) }",
        "fn read(value: &i64) -> i64 { *value }
         fn relay(value: &i64) -> i64 {
             { let local = 0; let value = &local; *value; };
             tail read(value)
         }
         pub fn main() -> i64 { let answer = 42; relay(&answer) }",
        "struct View<'a> { value: &'a i64 }
         fn walk<'a>(value: View<'a>, remaining: i64) -> i64 {
             handle remaining { 0 => *value.value, _ => tail walk(value, remaining - 1) }
         }
         pub fn main() -> i64 { let answer = 42; walk(View { value: &answer }, 10000) }",
        "struct View<'a> { value: &'a i64 }
         fn read<'a>(value: View<'a>) -> i64 { *value.value }
         fn relay<'a>(value: &'a i64) -> i64 { let nested = (value, 0); tail read(View { value: nested.0 }) }
         pub fn main() -> i64 { let answer = 42; relay(&answer) }",
    ] {
        for optimization in ["0", "2"] {
            let artifact = compile_at(source, optimization).unwrap_or_else(|error| panic!("{source}: {error:?}"))
                .artifact.unwrap();
            let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            for artifact in [&artifact, &decoded] {
                assert_eq!(artifact.run_i64_with_limits(VmExecutionLimits {
                    max_call_depth: 4, ..VmExecutionLimits::default()
                }).unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
            }
        }
    }
}

#[test]
fn mandatory_tail_does_not_promote_local_borrows_at_alias_or_join_boundaries() {
    for source in [
        "fn read(value: &i64) -> i64 { *value }
         pub fn main() -> i64 { let local = 42; let alias = &local; tail read(&(*alias)) }",
        "fn apply(callback: () -> i64) -> i64 { callback() }
         pub fn main() -> i64 {
             let local = 42;
             let borrowed = &local;
             let callback = move (borrowed) { *borrowed };
             tail apply(callback)
         }",
        "fn read(value: &i64) -> i64 { *value }
         fn choose(incoming: &i64, flag: Bool) -> i64 {
             let local = 42;
             let selected = handle flag { true => incoming, false => &local };
             tail read(selected)
         }
         pub fn main() -> i64 { let answer = 42; choose(&answer, false) }",
        "fn read(value: &i64) -> i64 { *value }
         fn choose(incoming: &i64, flag: Bool) -> i64 {
             let local = 42;
             let mut selected = incoming;
             handle flag { true => { selected = &local; }, false => () };
             tail read(selected)
         }
         pub fn main() -> i64 { let answer = 42; choose(&answer, true) }",
    ] {
        let error = compile(source).expect_err(source);
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4403"),
            "missing tail provenance rejection: {error:?}");
    }
}

#[test]
fn mandatory_tail_rejects_following_work_and_frame_dependencies() {
    for (source, code) in [
        (
            "fn done() -> i64 { 42 } pub fn main() -> i64 { tail done(); 1 }",
            "G4401",
        ),
        (
            "fn done() -> i64 { 42 } pub fn main() -> i64 { 1 + tail done() }",
            "G4401",
        ),
        (
            "fn done() -> i64 { 42 } pub fn main() -> i64 { let answer = tail done(); answer }",
            "G4401",
        ),
        (
            "fn unique<'a>(value: &'a mut i64) -> &'a mut i64 { value }
             fn shared<'a>(value: &'a mut i64) -> &'a i64 { tail unique(value) }
             pub fn main() -> i64 { let mut value = 42; *shared(&mut value) }",
            "G4400",
        ),
        (
            "fn unique<'a>(value: &'a mut i64) -> &'a mut i64 { value }
             fn explicit<'a>(value: &'a mut i64) -> &'a mut i64 { tail (&mut (*unique(value))) }
             pub fn main() -> i64 { let mut value = 42; *explicit(&mut value) }",
            "G4400",
        ),
        (
            "fn read(value: &i64) -> i64 { *value } pub fn main() -> i64 { let value = 42; tail read(&value) }",
            "G4403",
        ),
        (
            "struct Wrap<T> { value: T } fn read<'a>(value: Wrap<Wrap<&'a i64>>) -> i64 { *value.value.value } pub fn main() -> i64 { let value = 42; tail read(Wrap { value: Wrap { value: &value } }) }",
            "G4403",
        ),
        (
            "effect Read { read() -> i64; } fn done() -> i64 { 42 } pub fn main() -> i64 { handle Read::read() { Read::read() with k => { cancel(k); tail done() } } }",
            "G4402",
        ),
    ] {
        let error = compile(source).expect_err(source);
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == code
                    && diagnostic.class == grandiose_stage0::DiagnosticClass::Source),
            "{source}: {error:?}"
        );
    }
}

#[test]
fn mandatory_tail_protects_arguments_then_destroys_remaining_frame_owners() {
    let source = "struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        fn accept(value: i64) -> i64 { value }
        fn leave<'a>(probe: Probe<'a>) -> i64 { tail accept(*probe.target + 1) }
        pub fn main() -> i64 { let mut count = 40; let result = leave(Probe { target: &mut count }); result + count }";
    let artifact = compile(source).unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 82);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        82
    );
    let program = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    let function = program
        .functions
        .values()
        .find(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::TailCallOwned { .. }))
        })
        .unwrap();
    assert!(
        function
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::CallOwned { .. }))
    );
}

#[test]
fn mandatory_tail_moves_linear_payloads_without_discarding_or_duplicating_them() {
    let source = "struct Ticket { value: i64 } impl Use<[1, 1]> for Ticket {}
        fn accept(ticket: Ticket) -> i64 { let Ticket { value } = ticket; value }
        fn forward(ticket: Ticket) -> i64 { tail accept(ticket) }
        pub fn main() -> i64 { tail forward(Ticket { value: 42 }) }";
    let artifact = compile(source).unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn mandatory_tail_preserves_the_enclosing_callers_handler_destination() {
    let source = "effect Read { read() -> i64; }
        fn target() -> i64 / {Read} { Read::read() }
        fn forward() -> i64 / {Read} { tail target() }
        pub fn main() -> i64 { handle forward() { Read::read() with k => k(42) } }";
    let artifact = compile(source).unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn an_ordinary_recursive_call_still_retains_its_continuation() {
    let artifact = compile("fn again() -> i64 { again() } pub fn main() -> i64 { again() }")
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 2,
            ..VmExecutionLimits::default()
        }),
        Err(grandiose_stage0::VmArtifactError::CallDepthLimit { .. })
    ));
}

#[test]
fn a_stateless_closure_can_tail_transfer_its_result_destination() {
    let artifact = compile("fn answer() -> i64 { 42 } pub fn main() -> i64 { let callback = () -> i64 { tail answer() }; callback() }")
        .unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn mandatory_tail_allows_branch_local_cleanup_and_bottom_callees() {
    let artifact = compile("struct Ticket {} impl Use<[0, 1]> for Ticket {} impl Drop for Ticket { drop(&mut self) {} }
        fn answer() -> i64 { 42 }
        fn choose(value: i64) -> i64 { handle value { 0 => tail answer(), _ => { let ticket = Ticket {}; tail answer() } } }
        pub fn main() -> i64 { choose(0) + choose(1) }")
        .unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 84);
    let forever =
        compile("fn forever() -> ! { tail forever() } pub fn main() -> i64 { tail forever() }")
            .unwrap()
            .artifact
            .unwrap();
    assert!(matches!(
        forever.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 2,
            max_instructions: 100,
            ..VmExecutionLimits::default()
        }),
        Err(grandiose_stage0::VmArtifactError::InstructionLimit { .. })
    ));
}

#[test]
fn mandatory_tail_cleans_nested_aggregate_residents() {
    let artifact = compile("struct Ticket {} impl Use<[0, 1]> for Ticket {} impl Drop for Ticket { drop(&mut self) {} }
        struct Pair { ticket: Ticket } impl Use<[0, 1]> for Pair {}
        fn answer() -> i64 { 42 }
        pub fn main() -> i64 { let ticket = Ticket {}; let pair = Pair { ticket: ticket }; tail answer() }")
        .unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn mandatory_tail_destroys_partially_moved_nested_owners_exactly_once() {
    let artifact = compile("struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) { *self.target = *self.target + 1; } }
        struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
        fn answer() -> i64 { 30 }
        fn leave<'a>(pair: Pair<'a>) -> i64 { let moved = move pair.first; tail answer() }
        pub fn main() -> i64 {
            let mut first = 0; let mut second = 0;
            let result = leave(Pair { first: Probe { target: &mut first }, second: Probe { target: &mut second } });
            result + first * 10 + second
        }").unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 41);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        41
    );
}

#[test]
fn mandatory_tail_evaluates_effectful_arguments_left_to_right() {
    let artifact = compile("effect Log { emit(value: i64) -> i64; }
        fn accept(left: i64, right: i64) -> i64 { left * 10 + right }
        fn prepare() -> i64 / {Log} { tail accept(Log::emit(1), Log::emit(2)) }
        pub fn main() -> i64 { let mut trace = 0;
            let result = handle prepare() { Log::emit(value) with k => { trace = trace * 10 + value; k(value) } };
            result + trace }")
        .unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 24);
    assert_eq!(
        decode_and_verify_program(&artifact.canonical_bytes())
            .unwrap()
            .run_i64()
            .unwrap(),
        24
    );
}

#[test]
fn direct_tail_depth_is_bounded_at_zero_and_optimized_configurations() {
    for optimization in ["0", "3"] {
        for count in [32, 4096] {
            let source = format!(
                "fn repeat(n: i64, total: i64) -> i64 {{ handle n {{ 0 => total, _ => tail repeat(n - 1, total + 1) }} }} pub fn main() -> i64 {{ tail repeat({count}, 0) }}"
            );
            let artifact = compile_at(&source, optimization).unwrap().artifact.unwrap();
            let limits = VmExecutionLimits {
                max_call_depth: 2,
                ..VmExecutionLimits::default()
            };
            assert_eq!(artifact.run_i64_with_limits(limits).unwrap(), count);
            let (value, profile) = artifact.run_i64_for_authoring(limits).unwrap();
            assert_eq!(value, count);
            assert!(profile.peak_call_depth <= 2, "{profile:?}");
            assert!(profile.recycled_tail_calls >= count as u64, "{profile:?}");
        }
    }
}

#[test]
fn untrusted_tail_artifacts_must_prove_carriers_and_destination_abi() {
    let artifact = compile("fn accept(left: i64, right: i64) -> i64 { left + right } pub fn main() -> i64 { tail accept(40, 2) }")
        .unwrap().artifact.unwrap();
    let original = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    for mutation in 0..4 {
        let mut candidate = original.clone();
        let function = candidate.functions.get_mut(&candidate.entry).unwrap();
        let index = function
            .instructions
            .iter()
            .position(|instruction| matches!(instruction, VmInstruction::TailCallOwned { .. }))
            .unwrap();
        match mutation {
            0 => {
                if let VmInstruction::TailCallOwned { callee, .. } =
                    &mut function.instructions[index]
                {
                    *callee = grandiose_stage0::DefKey(Digest::of_bytes(b"missing-tail-target"));
                }
            }
            1 => {
                if let VmInstruction::TailCallOwned { arguments, .. } =
                    &mut function.instructions[index]
                {
                    arguments.pop();
                }
            }
            2 => {
                if let VmInstruction::TailCallOwned { arguments, .. } =
                    &mut function.instructions[index]
                {
                    arguments[1] = arguments[0];
                }
            }
            3 => {
                if let VmInstruction::DeclareResult { result, .. } = &mut function.instructions[0] {
                    *result = grandiose_stage0::VmType::Text;
                }
            }
            _ => unreachable!(),
        }
        candidate.fingerprint = candidate.computed_fingerprint();
        assert!(
            grandiose_stage0::verify_vm_program(candidate.clone()).is_err(),
            "mutation {mutation}"
        );
        assert!(
            decode_and_verify_program(&grandiose_stage0::encode_program(&candidate)).is_err(),
            "wire mutation {mutation}"
        );
    }
}

#[test]
fn untrusted_tail_cannot_hide_a_destructor_carrier_in_a_temporary() {
    let artifact = compile(
        "struct Ticket { value: i64 } impl Use<[0, 1]> for Ticket {}
        impl Drop for Ticket { drop(&mut self) {} }
        fn accept() -> i64 { 42 } fn leave(ticket: Ticket) -> i64 { tail accept() }
        pub fn main() -> i64 { leave(Ticket { value: 1 }) }",
    )
    .unwrap()
    .artifact
    .unwrap();
    let mut candidate = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    let function = candidate
        .functions
        .values_mut()
        .find(|function| {
            function
                .instructions
                .iter()
                .any(|instruction| matches!(instruction, VmInstruction::TailCallOwned { .. }))
        })
        .unwrap();
    let drop = function
        .instructions
        .iter_mut()
        .find(|instruction| matches!(instruction, VmInstruction::CallOwned { .. }))
        .unwrap();
    let VmInstruction::CallOwned { dst, .. } = drop else {
        unreachable!()
    };
    *drop = VmInstruction::ConstUnit { dst: *dst };
    let mutated = format!("{function:#?}");
    candidate.fingerprint = candidate.computed_fingerprint();
    assert!(
        grandiose_stage0::verify_vm_program(candidate.clone()).is_err(),
        "discarded a live destructor carrier: {mutated}"
    );
    assert!(decode_and_verify_program(&grandiose_stage0::encode_program(&candidate)).is_err());
}

#[test]
fn untrusted_tail_rejects_nonconsuming_store_and_aggregate_carriers() {
    let artifact = compile("struct Ticket {} impl Use<[0, 1]> for Ticket {}
        impl Drop for Ticket { drop(&mut self) {} }
        struct Pair { ticket: Ticket }
        fn answer() -> i64 { 42 }
        pub fn main() -> i64 { let ticket = Ticket {}; let pair = Pair { ticket: ticket }; tail answer() }")
        .unwrap().artifact.unwrap();
    let original = grandiose_stage0::decode_program(&artifact.canonical_bytes()).unwrap();
    for aggregate in [false, true] {
        let mut candidate = original.clone();
        let function = candidate.functions.get_mut(&candidate.entry).unwrap();
        let mut changed = false;
        for instruction in &mut function.instructions {
            let replacement = match instruction.clone() {
                VmInstruction::StoreOwned { dst, src } if !aggregate => {
                    VmInstruction::Store { dst, src }
                }
                VmInstruction::MakeRecordOwned {
                    dst,
                    definition,
                    fields,
                    field_types,
                } if aggregate && !fields.is_empty() => VmInstruction::MakeRecord {
                    dst,
                    definition,
                    fields,
                    field_types,
                },
                _ => continue,
            };
            *instruction = replacement;
            changed = true;
            break;
        }
        assert!(changed);
        candidate.fingerprint = candidate.computed_fingerprint();
        assert!(
            grandiose_stage0::verify_vm_program(candidate.clone()).is_err(),
            "aggregate: {aggregate}"
        );
        assert!(
            decode_and_verify_program(&grandiose_stage0::encode_program(&candidate)).is_err(),
            "wire aggregate: {aggregate}"
        );
    }
}
