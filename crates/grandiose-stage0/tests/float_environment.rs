//! The embedding thread's floating-point controls are not source semantics.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use grandiose_stage0::{
    CandidateVmArtifact, CandidateVmProgram, CompilationMode, CompilationRequest,
    CompilerBuildIdentity, DefKey, Digest, LogicalPath, PackageKey, STAGE0_VM_SCHEMA, Safety,
    ScalarType, SourceInput, StageZeroCompiler, VerifiedVmArtifact, VerifiedVmProgram,
    VmArtifactError, VmCompare, VmExecutionLimits, VmFunction, VmHost, VmInstruction as I,
    VmNativeImports, VmNativeStatus, VmType, decode_and_verify_artifact, decode_and_verify_program,
    encode_artifact, encode_program,
    runtime_manifest::{FloatBinaryOp, FloatPrimitive, FloatWidth},
};

struct Ambient {
    mxcsr: u32,
    x87: u16,
}
impl Ambient {
    fn read() -> Self {
        let mut value = Self { mxcsr: 0, x87: 0 };
        // SAFETY: the x86_64 control-register stores require only aligned
        // u32/u16 storage; they do not modify the calling thread's state.
        unsafe {
            std::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut value.mxcsr, options(nostack));
            std::arch::asm!("fnstcw [{p}]", p = in(reg) &mut value.x87, options(nostack));
        }
        value
    }
    fn write(&self) {
        // SAFETY: all installed words are captured controls or explicit
        // architectural values with every exception masked.
        unsafe {
            std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &self.mxcsr, options(nostack));
            std::arch::asm!("fldcw [{p}]", p = in(reg) &self.x87, options(nostack));
        }
    }
}

fn i64_probe(mut prefix: Vec<I>) -> VmFunction {
    let offset = prefix.len() as u32;
    prefix.extend([
        I::ConstF32 { dst: 0, bits: 1 },
        I::FloatIntrinsic {
            dst: 1,
            primitive: FloatPrimitive::Binary {
                width: FloatWidth::F32,
                operation: FloatBinaryOp::Add,
            },
            arguments: vec![0, 0],
        },
        I::FloatIntrinsic {
            dst: 2,
            primitive: FloatPrimitive::ToBits {
                width: FloatWidth::F32,
            },
            arguments: vec![1],
        },
        I::ConstU32 { dst: 3, value: 2 },
        I::CompareU32 {
            dst: 4,
            left: 2,
            right: 3,
            op: VmCompare::Equal,
        },
        I::BranchBool {
            condition: 4,
            then_target: offset + 7,
            else_target: offset + 9,
        },
        I::ConstI64 { dst: 5, value: 42 },
        I::Return { value: 5 },
        I::ConstI64 { dst: 5, value: 0 },
        I::Return { value: 5 },
    ]);
    function(
        vec![
            VmType::F32,
            VmType::F32,
            VmType::U32,
            VmType::U32,
            VmType::Bool,
            VmType::I64,
            VmType::Text,
            VmType::Unit,
        ],
        VmType::I64,
        prefix,
    )
}

#[test]
fn pure_vm_float_environment_covers_unsafe_authoring_display_and_budget_errors() {
    let (artifact, program) = checked(i64_probe(vec![]));
    for rounding in [0, 0x2000, 0x4000, 0x6000] {
        assert_eq!(
            hostile(rounding, 0x8040, || artifact.run_i64()).unwrap(),
            42
        );
        assert_eq!(
            hostile(rounding, 0x8040, || unsafe {
                artifact.run_i64_with_unsafe(Default::default())
            })
            .unwrap(),
            42
        );
        assert_eq!(hostile(rounding, 0x8040, || program.run_i64()).unwrap(), 42);
        assert_eq!(
            hostile(rounding, 0x8040, || unsafe {
                program.run_i64_with_unsafe(Default::default())
            })
            .unwrap(),
            42
        );
        assert_eq!(
            hostile(rounding, 0x8040, || program
                .run_i64_for_authoring(Default::default()))
            .unwrap()
            .0,
            42
        );
        assert_eq!(
            hostile(rounding, 0x8040, || unsafe {
                program.run_i64_for_authoring_with_unsafe(Default::default())
            })
            .unwrap()
            .0,
            42
        );
        assert_eq!(
            hostile(rounding, 0x8040, || program.run_display()).unwrap(),
            "42"
        );
        assert_eq!(
            hostile(rounding, 0x8040, || unsafe {
                program.run_display_with_unsafe(Default::default(), None)
            })
            .unwrap(),
            "42"
        );
        let limits = VmExecutionLimits {
            max_instructions: 3,
            ..Default::default()
        };
        assert!(matches!(
            hostile(rounding, 0x8040, || artifact.run_i64_with_limits(limits)),
            Err(VmArtifactError::InstructionLimit { .. })
        ));
        assert!(matches!(
            hostile(rounding, 0x8040, || program.run_i64_with_limits(limits)),
            Err(VmArtifactError::InstructionLimit { .. })
        ));
    }
}

struct MutatingHost {
    fail: bool,
    panic: bool,
    calls: usize,
}
impl VmHost for MutatingHost {
    fn process_args(&mut self) -> Result<Vec<String>, String> {
        unreachable!()
    }
    fn read_file(&mut self, _: &str) -> Result<Vec<u8>, String> {
        unreachable!()
    }
    fn write_file(&mut self, _: &str, _: &[u8]) -> Result<(), String> {
        unreachable!()
    }
    fn write_diagnostic(&mut self, text: &str) -> Result<(), String> {
        assert_eq!(text, "FP boundary");
        self.calls += 1;
        Ambient {
            mxcsr: 0xffd5,
            x87: 0x0f7f,
        }
        .write();
        assert!(!self.panic, "deliberate host panic");
        if self.fail {
            Err("deliberate host failure".into())
        } else {
            Ok(())
        }
    }
}

#[test]
fn vm_host_boundary_restores_profile_before_source_resumes() {
    let function = i64_probe(vec![
        I::ConstText {
            dst: 6,
            value: "FP boundary".into(),
        },
        I::HostCall {
            dst: 7,
            capability: "diagnostic".into(),
            symbol: "__g1_diagnostic_write".into(),
            source_contract: Digest::of_bytes(b"float-host-profile-contract"),
            parameters: vec![VmType::Text],
            result: VmType::Unit,
            resident_operations: vec![],
            arguments: vec![6],
        },
    ]);
    let mut candidate = CandidateVmProgram {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec!["diagnostic".into()],
        entry: function.definition,
        functions: [(function.definition, function)].into(),
        callable_environments: Default::default(),
        fingerprint: Digest::of_bytes(b"pending"),
    };
    candidate.fingerprint = candidate.computed_fingerprint();
    let program = decode_and_verify_program(&encode_program(&candidate)).unwrap();
    let mut host = MutatingHost {
        fail: false,
        panic: false,
        calls: 0,
    };
    assert_eq!(
        hostile(0x2000, 0, || program.run_display_with_host(&mut host)).unwrap(),
        "42"
    );
    assert_eq!(host.calls, 1);
    host.fail = true;
    assert!(matches!(
        hostile(0x2000, 0, || program.run_display_with_host(&mut host)),
        Err(VmArtifactError::HostCallFailed { .. })
    ));
    assert_eq!(host.calls, 2);
    host.panic = true;
    assert!(
        hostile(0x2000, 0, || std::panic::catch_unwind(
            std::panic::AssertUnwindSafe(|| program.run_display_with_host(&mut host))
        ))
        .is_err()
    );
    assert_eq!(host.calls, 3);
}

fn source_program(source: &str) -> VerifiedVmProgram {
    let package = PackageKey("float-native-environment@0.1.0".into());
    let input = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"float-native-environment")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![
            SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            ),
            SourceInput::new(
                PackageKey("std@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: Default::default(),
        capability_manifest: vec!["interop".into()],
        runtime_manifest: None,
    };
    let result = StageZeroCompiler::new()
        .compile(input)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    decode_and_verify_program(&result.artifact.unwrap().canonical_bytes()).unwrap()
}

#[test]
fn native_callback_and_return_reestablish_vm_profile_and_restore_each_caller() {
    let program = source_program("use std::*;
        host interop fn outer(callback: (u32) -> f32) -> f32;
        fn convert(value: u32) -> f32 { as<f32>(value) }
        pub fn main() -> i64 {
            let from_callback = outer(convert);
            let value: u32 = 4294967295;
            handle f32_eq(from_callback, 4294967296.0) {
                true => handle f32_eq(as<f32>(value), 4294967296.0) { true => 42, false => 0 }, false => 0,
            }
        }");
    for behavior in 0..3 {
        let mut imports = VmNativeImports::default();
        // SAFETY: the callback takes one initialized u32 and initializes
        // one f32 slot, synchronously, without retaining either pointer.
        unsafe {
            imports
                .insert(program.native_imports().unwrap().remove(0), move |call| {
                    let host_mode = Ambient {
                        mxcsr: 0xffd5,
                        x87: 0x0f7f,
                    };
                    host_mode.write();
                    let value = u32::MAX;
                    let slots = [(&value as *const u32).cast::<u8>()];
                    let mut output = std::mem::MaybeUninit::<f32>::uninit();
                    let status = call.with_callback(0, |callback| {
                        (callback.invoke)(
                            callback.context,
                            slots.as_ptr(),
                            1,
                            output.as_mut_ptr().cast(),
                        )
                    })?;
                    assert_eq!(status, VmNativeStatus::Ok);
                    let after = Ambient::read();
                    assert_eq!((after.mxcsr, after.x87), (host_mode.mxcsr, host_mode.x87));
                    let output = output.assume_init();
                    assert_eq!(output.to_bits(), 0x4f800000);
                    if behavior == 1 {
                        return Err(VmArtifactError::NativeAbi {
                            message: "deliberate native failure",
                        });
                    }
                    assert!(behavior != 2, "deliberate native panic");
                    call.set_result_from((&output as *const f32).cast())
                })
                .unwrap();
        }
        let outcome = hostile(0x2000, 0, || unsafe {
            program.run_i64_with_native(&imports, Default::default())
        });
        if behavior == 1 {
            assert!(matches!(
                outcome,
                Err(VmArtifactError::NativeAbi {
                    message: "deliberate native failure"
                })
            ));
        } else if behavior == 2 {
            assert!(matches!(
                outcome,
                Err(VmArtifactError::NativeAbi {
                    message: "native implementation panicked"
                })
            ));
        } else {
            assert_eq!(outcome.unwrap(), 42);
        }
    }
}
impl Drop for Ambient {
    fn drop(&mut self) {
        self.write();
    }
}

fn hostile<T>(rounding: u32, denormals: u32, body: impl FnOnce() -> T) -> T {
    let _saved = Ambient::read();
    let requested = Ambient {
        mxcsr: 0x1f80 | rounding | denormals | 0x15,
        x87: 0x037f | ((rounding >> 3) as u16),
    };
    requested.write();
    let value = body();
    let after = Ambient::read();
    assert_eq!(
        (after.mxcsr, after.x87),
        (requested.mxcsr, requested.x87),
        "caller controls/status were not restored"
    );
    value
}

fn checked(function: VmFunction) -> (VerifiedVmArtifact, VerifiedVmProgram) {
    let mut artifact = CandidateVmArtifact {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        function: function.clone(),
        fingerprint: Digest::of_bytes(b"pending"),
    };
    artifact.fingerprint = artifact.computed_fingerprint();
    let mut program = CandidateVmProgram {
        schema: STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry: function.definition,
        functions: [(function.definition, function)].into(),
        callable_environments: Default::default(),
        fingerprint: Digest::of_bytes(b"pending"),
    };
    program.fingerprint = program.computed_fingerprint();
    (
        decode_and_verify_artifact(&encode_artifact(&artifact)).unwrap(),
        decode_and_verify_program(&encode_program(&program)).unwrap(),
    )
}

fn function(registers: Vec<VmType>, result: VmType, mut instructions: Vec<I>) -> VmFunction {
    instructions.insert(
        0,
        I::DeclareResult {
            result,
            returns: true,
        },
    );
    VmFunction {
        definition: DefKey(Digest::of_bytes(b"float-environment-entry")),
        safety: Safety::Safe,
        unsafe_execution: false,
        nominal_copy_descriptors: vec![],
        captures: 0,
        parameters: 0,
        registers,
        instructions,
    }
}

#[test]
fn pure_vm_float_environment_covers_artifact_and_program_entries() {
    let (narrow_artifact, narrow_program) = checked(function(
        vec![VmType::U32, VmType::F32],
        VmType::F32,
        vec![
            I::ConstU32 {
                dst: 0,
                value: u32::MAX,
            },
            I::FloatIntrinsic {
                dst: 1,
                primitive: FloatPrimitive::Convert {
                    from: ScalarType::U32,
                    to: ScalarType::F32,
                    checked: false,
                },
                arguments: vec![0],
            },
            I::Return { value: 1 },
        ],
    ));
    let (wide_artifact, wide_program) = checked(function(
        vec![VmType::U64, VmType::F64],
        VmType::F64,
        vec![
            I::ConstU64 {
                dst: 0,
                value: 9_007_199_254_740_995,
            },
            I::FloatIntrinsic {
                dst: 1,
                primitive: FloatPrimitive::Convert {
                    from: ScalarType::U64,
                    to: ScalarType::F64,
                    checked: false,
                },
                arguments: vec![0],
            },
            I::Return { value: 1 },
        ],
    ));
    let (subnormal_artifact, subnormal_program) = checked(function(
        vec![VmType::F32, VmType::F32],
        VmType::F32,
        vec![
            I::ConstF32 { dst: 0, bits: 1 },
            I::FloatIntrinsic {
                dst: 1,
                primitive: FloatPrimitive::Binary {
                    width: FloatWidth::F32,
                    operation: FloatBinaryOp::Add,
                },
                arguments: vec![0, 0],
            },
            I::Return { value: 1 },
        ],
    ));
    let narrow_text = narrow_program.run_display().unwrap();
    let wide_text = wide_program.run_display().unwrap();
    let subnormal_text = subnormal_program.run_display().unwrap();
    for rounding in [0, 0x2000, 0x4000, 0x6000] {
        for denormals in [0, 0x8040] {
            assert_eq!(
                hostile(rounding, denormals, || narrow_program.run_display()).unwrap(),
                narrow_text
            );
            assert_eq!(
                hostile(rounding, denormals, || wide_program.run_display()).unwrap(),
                wide_text
            );
            assert_eq!(
                hostile(rounding, denormals, || subnormal_program.run_display()).unwrap(),
                subnormal_text
            );
            for value in [
                hostile(rounding, denormals, || narrow_artifact.run_f32()),
                hostile(rounding, denormals, || narrow_program.run_f32()),
            ] {
                let value = value.unwrap();
                assert_eq!(value.to_bits(), 0x4f800000);
            }
            for value in [
                hostile(rounding, denormals, || wide_artifact.run_f64()),
                hostile(rounding, denormals, || wide_program.run_f64()),
            ] {
                let value = value.unwrap();
                assert_eq!(value.to_bits(), 0x4340000000000002);
            }
            for value in [
                hostile(rounding, denormals, || subnormal_artifact.run_f32()),
                hostile(rounding, denormals, || subnormal_program.run_f32()),
            ] {
                let value = value.unwrap();
                assert_eq!(value.to_bits(), 2);
            }
        }
    }
}

#[test]
fn pure_vm_float_environment_restores_after_checked_failure() {
    let (artifact, program) = checked(function(
        vec![VmType::F64, VmType::U8],
        VmType::U8,
        vec![
            I::ConstF64 {
                dst: 0,
                bits: (1_u64 << 63) | 1,
            },
            I::FloatIntrinsic {
                dst: 1,
                primitive: FloatPrimitive::Convert {
                    from: ScalarType::F64,
                    to: ScalarType::U8,
                    checked: true,
                },
                arguments: vec![0],
            },
            I::Return { value: 1 },
        ],
    ));
    assert!(matches!(
        hostile(0x6000, 0x8040, || artifact.run_u8()),
        Err(VmArtifactError::Trap)
    ));
    assert!(matches!(
        hostile(0x6000, 0x8040, || program.run_u8()),
        Err(VmArtifactError::Trap)
    ));
}

#[test]
fn vm_profile_masks_exceptions_without_changing_the_host_masks() {
    const CHILD: &str = "GRANDIOSE_FLOAT_TRAP_TEST_CHILD";
    if std::env::var_os(CHILD).is_none() {
        // An unmasked hardware exception would terminate only this child,
        // leaving the parent test harness and embedding process untouched.
        let outcome = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "vm_profile_masks_exceptions_without_changing_the_host_masks",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            outcome.status.success(),
            "unmasked-host child {:?}: {}{}",
            outcome.status,
            String::from_utf8_lossy(&outcome.stdout),
            String::from_utf8_lossy(&outcome.stderr)
        );
        return;
    }
    let (artifact, program) = checked(function(
        vec![VmType::F64, VmType::F64],
        VmType::F64,
        vec![
            I::ConstF64 { dst: 0, bits: 0 },
            I::DivF64 {
                dst: 1,
                left: 0,
                right: 0,
            },
            I::Return { value: 1 },
        ],
    ));
    let _saved = Ambient::read();
    let requested = Ambient {
        mxcsr: 0,
        x87: 0x0340,
    };
    requested.write();
    assert_eq!(artifact.run_f64().unwrap().to_bits(), 0x7ff8000000000000);
    assert_eq!(program.run_f64().unwrap().to_bits(), 0x7ff8000000000000);
    let after = Ambient::read();
    assert_eq!((after.mxcsr, after.x87), (requested.mxcsr, requested.x87));
}
