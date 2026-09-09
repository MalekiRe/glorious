//! These fixtures execute LLVM-generated Glorious, not Rust native callbacks.
use grandiose_stage0::vm_backend::llvm::{
    LlvmCompileOptions, LlvmError, LlvmIrProgram, LlvmTarget,
};
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, VmArtifactError, VmExecutionLimits,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("llvm-source@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"llvm-native-source-tests")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), "0".into())]
            .into_iter()
            .collect(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn compile(source: &str) -> LlvmIrProgram {
    StageZeroCompiler::new()
        .compile_llvm(request(source), LlvmTarget::host().unwrap())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

#[test]
fn actual_llvm_native_scalar_control_matches_vm_at_o0_and_o2() {
    for source in [
        "pub fn main() -> i64 { 42 }",
        "fn add(left: i64, right: i64) -> i64 { left + right } pub fn main() -> i64 { add(40, 2) }",
        "struct Pair { first: i64, second: i64 } fn sum(value: &Pair) -> i64 { value.first + value.second } pub fn main() -> i64 { let pair = Pair { first: 40, second: 2 }; sum(&pair) }",
        "enum Choice { Yes(i64), No } fn choose(value: Choice) -> i64 { handle value { Choice::Yes(number) => number, Choice::No => 0 } } pub fn main() -> i64 { choose(Choice::Yes(42)) }",
        "fn update(value: &mut i64) { *value = *value + 2; } pub fn main() -> i64 { let mut value = 40; update(&mut value); value }",
        "pub fn main() -> i64 { let value: i128 = 170141183460469231731687303715884105700; handle value + 27 == 170141183460469231731687303715884105727 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { let left: f64 = 8.5; let right: f64 = 3.0; handle left % right == 2.5 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { let value: f32 = 20.0; handle value * 2.0 + 2.0 == 42.0 { true => 42, false => 0 } }",
    ] {
        let ir = compile(source);
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
        assert!(ir.ir().contains("define internal i32 @g1_body_"));
        for optimization in [0, 2] {
            let module = unsafe {
                ir.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
            assert_eq!(module.run_i64_with_limits(Default::default()).unwrap(), 42);
        }
    }
}

#[test]
fn actual_native_source_destructors_and_zero_sized_residents() {
    let source = "struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        struct Empty {}
        fn consume(value: Empty) { () }
        fn relay<'a>(probe: Probe<'a>) -> i64 { *probe.target + 1 }
        pub fn main() -> i64 { consume(Empty {}); let mut count = 20; let result = relay(Probe { target: &mut count }); result + count }";
    let ir = compile(source);
    assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn actual_native_mutual_tail_calls_have_bounded_storage_at_o0() {
    let ir = compile(
        "fn first(n: i64, sum: i64) -> i64 { handle n { 0 => sum, _ => tail second(n - 1, sum + 1) } } fn second(n: i64, sum: i64) -> i64 { handle n { 0 => sum, _ => tail first(n - 1, sum + 1) } } pub fn main() -> i64 { tail first(10000, 0) }",
    );
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        let limits = VmExecutionLimits {
            max_call_depth: 16,
            ..Default::default()
        };
        let (value, profile) = unsafe { native.run_i64_profiled(limits) }.unwrap();
        assert_eq!(value, 10000);
        assert!(profile.peak_call_depth <= 16, "{profile:?}");
        assert!(profile.recycled_tail_calls >= 10000, "{profile:?}");
    }
}

#[test]
fn native_checked_faults_and_limits_are_explicit() {
    let ir = compile(
        "fn add(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { add(9223372036854775807) }",
    );
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert!(matches!(
            native.run_i64_with_limits(Default::default()),
            Err(LlvmError::Runtime(VmArtifactError::ArithmeticOverflow))
        ));
        assert!(matches!(
            native.run_i64_with_limits(VmExecutionLimits {
                max_instructions: 0,
                ..Default::default()
            }),
            Err(LlvmError::Runtime(VmArtifactError::InstructionLimit {
                limit: 0
            }))
        ));
    }
}

#[test]
fn native_abi_rejects_every_independent_contract_mismatch() {
    let ir = compile("pub fn main() -> i64 { 42 }");
    for change in 0..12 {
        let mut descriptor = ir.abi().clone();
        match change {
            0 => descriptor.generation += 1,
            1 => descriptor.target.triple = "aarch64-unknown-linux-gnu".into(),
            2 => descriptor.target.pointer_bits = 32,
            3 => descriptor.target.little_endian = false,
            4 => descriptor.target.data_layout.push_str("-i64:32"),
            5 => descriptor.layout_identity = Digest::of_bytes(b"another layout"),
            6 => descriptor.source_identity = Digest::of_bytes(b"another source lifetime contract"),
            7 => descriptor.runtime_manifest = Some(Digest::of_bytes(b"another runtime")),
            8 => descriptor.control_convention.push_str("-replay"),
            9 => descriptor.allocation_domain.push_str("-foreign"),
            10 => {
                descriptor.code_identity =
                    Digest::of_bytes(b"another source destructor implementation")
            }
            _ => descriptor.execution_partition = Digest::of_bytes(b"another engine partition"),
        }
        assert!(
            ir.validate_abi(&descriptor).is_err(),
            "accepted mutation {change}"
        );
    }
}

#[test]
fn unsupported_native_effects_reject_before_execution() {
    let source = "effect Ask { ask() -> i64; } fn ask() -> i64 / {Ask} { Ask::ask() } pub fn main() -> i64 { handle ask() { Ask::ask() with k => k(42) } }";
    let error = StageZeroCompiler::new()
        .compile_llvm(request(source), LlvmTarget::host().unwrap())
        .unwrap_err();
    assert!(matches!(error, LlvmError::Unsupported { .. }), "{error:?}");
}

#[test]
fn generated_llvm_and_vm_share_references_and_owned_results() {
    let cases = [
        (41, "fn vm_step(value: &mut i64) -> i64 { *value = *value + 1; 41 }
            fn native_step(value: &mut i64) -> i64 { let answer = vm_step(value); *value = *value + 1; answer + 1 }
            pub fn main() -> i64 { let mut value = 0; let answer = native_step(&mut value); answer + value - 2 }"),
        (1, "struct Pair { first: i64, second: i64 }
            fn vm_shift(value: Pair) -> Pair { Pair { first: value.first + 1, second: value.second } }
            fn native_relay(value: Pair) -> Pair { vm_shift(value) }
            pub fn main() -> i64 { let value = native_relay(Pair { first: 20, second: 21 }); value.first + value.second }"),
        (41001, "fn vm_return(value: &mut i64) -> &mut i64 { let marker = 41001; value }
            fn native_return(value: &mut i64) -> &mut i64 { vm_return(value) }
            pub fn main() -> i64 { let mut value = 40; let view = native_return(&mut value); *view = *view + 2; value }"),
    ];
    for (marker, source) in cases {
        let ir = compile(source);
        assert_eq!(
            unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
        let selected = ir.function_keys().iter().copied().filter(|key| ir.function(*key).unwrap().instructions.iter()
            .any(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::ConstI64 { value, .. } if *value == marker))).collect::<Vec<_>>();
        assert_eq!(selected.len(), 1, "marker {marker}: {source}");
        let mixed = ir.with_vm_functions([ir.entry_key(), selected[0]]).unwrap();
        assert_ne!(
            ir.abi().execution_partition,
            mixed.abi().execution_partition
        );
        for optimization in [0, 2] {
            let native = unsafe {
                mixed.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap();
            assert_eq!(
                unsafe { native.run_i64_with_unsafe(Default::default()) }
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")),
                42
            );
        }
    }
}

#[test]
fn generated_native_preserves_actual_reference_backing_addresses() {
    let source = "use std::*;
        fn vm_observe(value: &i64, expected: usize) -> i64 { handle ptr_address(ptr_from_ref(value)) == expected { true => 41, false => 0 } }
        fn native_observe(value: &i64, expected: usize) -> i64 { vm_observe(value, expected) + 1 }
        pub fn main() -> i64 { let value = 20; let expected = ptr_address(ptr_from_ref(&value)); native_observe(&value, expected) }";
    let mut input = request(source);
    input.sources.push(SourceInput::new(
        PackageKey("std@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        format!(
            "{}\n{}\n{}",
            include_str!("../../../stdlib/src/lib.glorious"),
            include_str!("../../../stdlib/src/foundation.glorious"),
            include_str!("../../../stdlib/src/memory.glorious")
        )
        .as_bytes(),
    ));
    let ir = StageZeroCompiler::new()
        .compile_llvm(input, LlvmTarget::host().unwrap())
        .unwrap();
    assert_eq!(
        unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(),
        42
    );
    let observer = ir
        .function_keys()
        .iter()
        .copied()
        .find(|key| {
            ir.function(*key)
                .unwrap()
                .instructions
                .iter()
                .any(|instruction| {
                    matches!(
                        instruction,
                        grandiose_stage0::VmInstruction::ConstI64 { value: 41, .. }
                    )
                })
        })
        .unwrap();
    let mixed = ir.with_vm_functions([ir.entry_key(), observer]).unwrap();
    for optimization in [0, 2] {
        let native = unsafe {
            mixed.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(
            unsafe { native.run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
        );
    }
}

#[test]
fn cross_engine_mandatory_tail_rejects_before_loading() {
    let ir = compile("fn answer() -> i64 { 42 } pub fn main() -> i64 { tail answer() }");
    assert!(matches!(
        ir.with_vm_functions([ir.entry_key()]),
        Err(LlvmError::Unsupported { .. })
    ));
}

fn compile_mixed(source: &str) -> LlvmIrProgram {
    StageZeroCompiler::new()
        .compile_llvm_partitioned(request(source), LlvmTarget::host().unwrap(), |function| {
            function.instructions.iter().any(|instruction| {
                matches!(
                    instruction,
                    grandiose_stage0::VmInstruction::ConstI64 {
                        value: 41001 | 41002,
                        ..
                    }
                )
            })
        })
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
}

#[test]
fn mixed_native_fixed_arrays_zero_sized_owners_and_source_drop_identity() {
    let cases = [
        "fn vm_shift(value: [i64;2]) -> [i64;2] { let marker = 41001; let [a,b] = value; [a + 1,b] }
            fn native_relay(value: [i64;2]) -> [i64;2] { vm_shift(value) }
            pub fn main() -> i64 { let marker = 41002; let [a,b] = native_relay([20,21]); a+b }",
        "struct Token {} impl Use<[1,1]> for Token {}
            fn vm_relay(value: Token) -> Token { let marker = 41001; value }
            fn native_relay(value: Token) -> Token { vm_relay(value) }
            pub fn main() -> i64 { let marker = 41002; let Token {} = native_relay(Token {}); 42 }",
        "struct Probe<'a> { count: &'a mut i64 }
            impl<'a> Use<[0,1]> for Probe<'a> {}
            impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 2; } }
            fn vm_relay<'a>(value: Probe<'a>) -> Probe<'a> { let marker = 41001; value }
            fn native_relay<'a>(value: Probe<'a>) -> Probe<'a> { vm_relay(value) }
            pub fn main() -> i64 { let marker = 41002; let mut count = 40; { let probe = native_relay(Probe { count: &mut count }); () }; count }",
        "struct Probe<'a> { count: &'a mut i64 }
            impl<'a> Use<[0,1]> for Probe<'a> {}
            impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 2; } }
            fn vm_consume<'a>(value: Probe<'a>) { let marker = 41001; () }
            fn native_consume<'a>(value: Probe<'a>) { vm_consume(value) }
            pub fn main() -> i64 { let marker = 41002; let mut count = 40; native_consume(Probe { count: &mut count }); count }",
    ];
    for source in cases {
        let mixed = compile_mixed(source);
        assert_eq!(mixed.vm_program().run_i64().unwrap(), 42);
        for optimization in [0, 2] {
            let native = unsafe {
                mixed.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap();
            assert_eq!(
                native
                    .run_i64_with_limits(Default::default())
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")),
                42
            );
        }
    }
}

#[test]
fn mixed_engines_share_instruction_memory_and_call_depth_limits() {
    let ir = compile_mixed(
        "fn vm_step(value: i64) -> i64 { let marker = 41001; value + 1 }
        fn native_step(value: i64) -> i64 { vm_step(value) + 1 }
        pub fn main() -> i64 { let marker = 41002; native_step(40) }",
    );
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
        let instructions = native.run_i64_with_limits(VmExecutionLimits {
            max_instructions: 20,
            ..Default::default()
        });
        assert!(
            matches!(
                instructions,
                Err(LlvmError::Runtime(VmArtifactError::InstructionLimit {
                    limit: 20
                }))
            ),
            "{instructions:?}"
        );
        let depth = native.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 2,
            ..Default::default()
        });
        assert!(
            matches!(
                depth,
                Err(LlvmError::Runtime(VmArtifactError::CallDepthLimit {
                    limit: 2
                }))
            ),
            "{depth:?}"
        );
        assert!(
            native
                .run_i64_with_limits(VmExecutionLimits {
                    max_native_bytes: 128,
                    ..Default::default()
                })
                .is_err()
        );
        assert!(
            native
                .run_i64_with_limits(VmExecutionLimits {
                    max_native_allocation_bytes: 128,
                    ..Default::default()
                })
                .is_err()
        );
    }
}

#[test]
fn explicit_vm_selection_does_not_hide_unsupported_mixed_control() {
    let source = "effect Ask { ask() -> i64; } fn ask() -> i64 / {Ask} { Ask::ask() }
        pub fn main() -> i64 { handle ask() { Ask::ask() with k => k(42) } }";
    let error = StageZeroCompiler::new()
        .compile_llvm_partitioned(request(source), LlvmTarget::host().unwrap(), |_| true)
        .unwrap_err();
    assert!(matches!(error, LlvmError::Unsupported { .. }), "{error:?}");
}
