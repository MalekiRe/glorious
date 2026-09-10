//! Bit-exact checks of machine conversion leaves. Public conversion policy is
//! separately exercised by source tests; it is not reimplemented in this table.
use super::*;
use crate::vm_backend::{
    ExecutionBudget, NativeMemory, VmFunction, VmInstruction as I, VmValue,
    native_memory::native_layout,
};
use crate::{ScalarType, runtime_manifest::FloatPrimitive};

#[cfg(target_arch = "x86_64")]
struct AmbientFloatMode {
    mxcsr: u32,
    x87: u16,
}

#[cfg(target_arch = "x86_64")]
impl AmbientFloatMode {
    fn current() -> Self {
        let mut original = Self { mxcsr: 0, x87: 0 };
        // SAFETY: x86_64 always has SSE. Both operands are initialized,
        // aligned u32 storage, and the installed control word uses only
        // architectural bits with every exception masked.
        unsafe {
            std::arch::asm!("stmxcsr [{address}]", address = in(reg) &mut original.mxcsr, options(nostack));
            std::arch::asm!("fnstcw [{address}]", address = in(reg) &mut original.x87, options(nostack));
        }
        original
    }

    fn install(rounding: u32, denormals: u32) -> Self {
        let original = Self::current();
        let mxcsr = 0x1f80_u32 | rounding | denormals | 0x15;
        let x87 = 0x037f_u16 | ((rounding >> 3) as u16);
        // SAFETY: only architectural control/status bits are used, every
        // exception remains masked, and the guard restores on this thread.
        unsafe {
            std::arch::asm!("ldmxcsr [{address}]", address = in(reg) &mxcsr, options(nostack));
            std::arch::asm!("fldcw [{address}]", address = in(reg) &x87, options(nostack));
        }
        original
    }

    fn assert_restored(rounding: u32, denormals: u32) {
        let actual = Self::current();
        assert_eq!(actual.mxcsr, 0x1f80 | rounding | denormals | 0x15);
        assert_eq!(actual.x87, 0x037f | ((rounding >> 3) as u16));
    }
}

#[cfg(target_arch = "x86_64")]
impl Drop for AmbientFloatMode {
    fn drop(&mut self) {
        // SAFETY: restore the same thread's previously valid control word,
        // including on an assertion unwind. No other thread is modified.
        unsafe {
            std::arch::asm!("ldmxcsr [{address}]", address = in(reg) &self.mxcsr, options(nostack));
            std::arch::asm!("fldcw [{address}]", address = in(reg) &self.x87, options(nostack));
        }
    }
}

fn budget() -> ExecutionBudget {
    ExecutionBudget {
        native_memory: NativeMemory::default(),
        unsafe_execution: false,
        limits: Default::default(),
        instructions: 0,
        allocated_elements: 0,
    }
}

fn vm_type(ty: ScalarType) -> VmType {
    match ty {
        ScalarType::U8 => VmType::U8,
        ScalarType::I8 => VmType::I8,
        ScalarType::U16 => VmType::U16,
        ScalarType::I16 => VmType::I16,
        ScalarType::U32 => VmType::U32,
        ScalarType::I32 => VmType::I32,
        ScalarType::U64 => VmType::U64,
        ScalarType::I64 => VmType::I64,
        ScalarType::U128 => VmType::U128,
        ScalarType::I128 => VmType::I128,
        ScalarType::Usize => VmType::Usize,
        ScalarType::Isize => VmType::Isize,
        ScalarType::F32 => VmType::F32,
        ScalarType::F64 => VmType::F64,
        _ => panic!("non-numeric conversion fixture"),
    }
}

fn constant(value: VmValue) -> I {
    match value {
        VmValue::U8(value) => I::ConstU8 { dst: 0, value },
        VmValue::I8(value) => I::ConstI8 { dst: 0, value },
        VmValue::U16(value) => I::ConstU16 { dst: 0, value },
        VmValue::I16(value) => I::ConstI16 { dst: 0, value },
        VmValue::U32(value) => I::ConstU32 { dst: 0, value },
        VmValue::I32(value) => I::ConstI32 { dst: 0, value },
        VmValue::U64(value) => I::ConstU64 { dst: 0, value },
        VmValue::I64(value) => I::ConstI64 { dst: 0, value },
        VmValue::U128(value) => I::ConstU128 { dst: 0, value },
        VmValue::I128(value) => I::ConstI128 { dst: 0, value },
        VmValue::Usize(value) => I::ConstUsize { dst: 0, value },
        VmValue::Isize(value) => I::ConstIsize { dst: 0, value },
        VmValue::F32(value) => I::ConstF32 {
            dst: 0,
            bits: value.to_bits(),
        },
        VmValue::F64(value) => I::ConstF64 {
            dst: 0,
            bits: value.to_bits(),
        },
        _ => panic!("non-numeric conversion fixture"),
    }
}

#[test]
fn native_float_conversion_matrix_matches_vm_bits_and_checked_errors() {
    let mut cases = Vec::new();
    let mut add = |from, to, value, checked| {
        let label = format!("conversion-{}-{from:?}-{to:?}-{value:?}", cases.len());
        let definition = DefKey(Digest::of_bytes(label.as_bytes()));
        let result = vm_type(to);
        cases.push((
            label,
            VmFunction {
                definition,
                safety: crate::Safety::Safe,
                unsafe_execution: false,
                nominal_copy_descriptors: vec![],
                captures: 0,
                parameters: 0,
                registers: vec![vm_type(from), result.clone()],
                instructions: vec![
                    I::DeclareResult {
                        result,
                        returns: true,
                    },
                    constant(value),
                    I::FloatIntrinsic {
                        dst: 1,
                        primitive: FloatPrimitive::Convert { from, to, checked },
                        arguments: vec![0],
                    },
                    I::Return { value: 1 },
                ],
            },
        ));
    };
    macro_rules! integers {
        ($scalar:ident, $variant:ident, $rust:ty) => {
            for value in [<$rust>::MIN, 0, 42, <$rust>::MAX] {
                for to in [ScalarType::F32, ScalarType::F64] {
                    add(ScalarType::$scalar, to, VmValue::$variant(value), false);
                }
            }
        };
    }
    integers!(U8, U8, u8);
    integers!(I8, I8, i8);
    integers!(U16, U16, u16);
    integers!(I16, I16, i16);
    integers!(U32, U32, u32);
    integers!(I32, I32, i32);
    integers!(U64, U64, u64);
    integers!(I64, I64, i64);
    integers!(U128, U128, u128);
    integers!(I128, I128, i128);
    integers!(Usize, Usize, u64);
    integers!(Isize, Isize, i64);
    for value in [
        9_223_372_586_610_589_697,
        16_777_217,
        16_777_219,
        9_007_199_254_740_993,
        9_007_199_254_740_995,
    ] {
        for to in [ScalarType::F32, ScalarType::F64] {
            add(ScalarType::U64, to, VmValue::U64(value), false);
            add(ScalarType::Usize, to, VmValue::Usize(value), false);
            add(
                ScalarType::U128,
                to,
                VmValue::U128(u128::from(value)),
                false,
            );
            add(
                ScalarType::I128,
                to,
                VmValue::I128(i128::from(value)),
                false,
            );
            add(
                ScalarType::I128,
                to,
                VmValue::I128(-i128::from(value)),
                false,
            );
        }
    }
    let half_subnormal = f64::from_bits((1023 - 150) << 52);
    for value in [
        0.0,
        -0.0,
        f64::NAN,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::MAX,
        f64::from_bits(1),
        -f64::from_bits(1),
        half_subnormal,
        f64::from_bits(half_subnormal.to_bits() + 1),
        1.000000059604644775390625,
        1.000000178813934326171875,
        f32::MAX as f64,
    ] {
        add(ScalarType::F64, ScalarType::F32, VmValue::F64(value), false);
    }
    for value in [
        0.0,
        -0.0,
        f32::NAN,
        f32::INFINITY,
        f32::NEG_INFINITY,
        f32::MAX,
        f32::from_bits(1),
        -f32::from_bits(1),
        42.75,
        -128.5,
    ] {
        add(ScalarType::F32, ScalarType::F64, VmValue::F32(value), false);
    }
    for (to, bits, signed) in [
        (ScalarType::U8, 8, false),
        (ScalarType::I8, 8, true),
        (ScalarType::U16, 16, false),
        (ScalarType::I16, 16, true),
        (ScalarType::U32, 32, false),
        (ScalarType::I32, 32, true),
        (ScalarType::U64, 64, false),
        (ScalarType::I64, 64, true),
        (ScalarType::U128, 128, false),
        (ScalarType::I128, 128, true),
        (ScalarType::Usize, 64, false),
        (ScalarType::Isize, 64, true),
    ] {
        let upper = f64::from_bits((1023 + bits - u64::from(signed)) << 52);
        let lower = if signed { -upper } else { 0.0 };
        let before_lower = if signed {
            f64::from_bits(lower.to_bits() + 1)
        } else {
            -f64::from_bits(1)
        };
        for value in [
            0.0,
            -0.0,
            42.75,
            -0.5,
            255.75,
            -128.5,
            lower,
            before_lower,
            upper,
            f64::from_bits(upper.to_bits() - 1),
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
        ] {
            add(ScalarType::F64, to, VmValue::F64(value), true);
        }
        let upper = upper as f32;
        let lower = lower as f32;
        let before_lower = if signed {
            f32::from_bits(lower.to_bits() + 1)
        } else {
            -f32::from_bits(1)
        };
        for value in [
            0.0,
            -0.0,
            42.75,
            -0.5,
            255.75,
            -128.5,
            lower,
            before_lower,
            upper,
            f32::from_bits(upper.to_bits() - 1),
            f32::NAN,
            f32::INFINITY,
            f32::NEG_INFINITY,
        ] {
            add(ScalarType::F32, to, VmValue::F32(value), true);
        }
    }
    let entry = cases[0].1.definition;
    let mut program = CandidateVmProgram {
        schema: crate::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        host_capabilities: vec![],
        entry,
        functions: cases
            .iter()
            .map(|(_, function)| (function.definition, function.clone()))
            .collect(),
        callable_environments: Default::default(),
        fingerprint: Digest::of_bytes(b"pending"),
    };
    program.fingerprint = program.computed_fingerprint();
    let verified = crate::vm_backend::verify_program(program).unwrap();
    let ir = LlvmIrProgram::lower_partitioned(
        verified,
        Digest::of_bytes(b"exact-float-conversion-matrix"),
        LlvmTarget::host().unwrap(),
        Default::default(),
    )
    .unwrap();
    let expected = cases
        .iter()
        .map(|(_, function)| crate::vm_backend::execute(function, &mut budget()))
        .collect::<Vec<_>>();
    assert!(cases.len() >= 450);
    #[repr(align(16))]
    struct Slot([u8; 16]);
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        let mut unbound = NativeContext::new(Default::default());
        let mut untouched = Slot([0xa5; 16]);
        let rejected = unsafe { native.invoke_native(0, &mut unbound, std::ptr::null(), untouched.0.as_mut_ptr()) };
        assert!(matches!(unbound.result(rejected), Err(LlvmError::Runtime(VmArtifactError::NativeAbi { message }))
            if message.contains("bound execution-domain")));
        assert_eq!(untouched.0, [0xa5; 16]);
        for (rounding, denormals) in [0, 0x2000, 0x4000, 0x6000]
            .into_iter()
            .flat_map(|rounding| [0, 0x8040].map(|denormals| (rounding, denormals)))
        {
            for ((label, function), expected) in cases.iter().zip(&expected) {
                let index = ir
                    .function_keys()
                    .iter()
                    .position(|key| *key == function.definition)
                    .unwrap();
                let mut context = NativeContext::new(Default::default());
                let mut execution = budget();
                let mut allocation = super::memory::AllocationContext::new(&mut execution.native_memory, execution.limits.max_native_bytes);
                let callables = super::callables::CallableContext::new(&native, &mut execution);
                unsafe { allocation.install(&mut context); callables.install(&mut context); }
                let mut actual = Slot([0; 16]);
                let status = {
                    #[cfg(target_arch = "x86_64")]
                    let _ambient = AmbientFloatMode::install(rounding, denormals);
                    let status = unsafe {
                        native.invoke_native(
                            index,
                            &mut context,
                            std::ptr::null(),
                            actual.0.as_mut_ptr(),
                        )
                    };
                    #[cfg(target_arch = "x86_64")]
                    AmbientFloatMode::assert_restored(rounding, denormals);
                    status
                };
                match expected {
                    Err(VmArtifactError::Trap) => assert!(
                        matches!(
                            context.result(status),
                            Err(LlvmError::Runtime(VmArtifactError::Trap))
                        ),
                        "{label}: {context:?}"
                    ),
                    Err(error) => panic!("unexpected VM result {label}: {error:?}"),
                    Ok(expected) => {
                        context
                            .result(status)
                            .unwrap_or_else(|error| panic!("{label}: {error:?}"));
                        let layout = native_layout(
                            &function.registers[1],
                            &std::sync::Arc::from([]),
                            &mut vec![],
                        )
                        .unwrap();
                        let mut bytes = Slot([0; 16]);
                        unsafe { layout.write(bytes.0.as_mut_ptr(), expected.clone(), &mut budget()) }.unwrap();
                        assert_eq!(
                            &actual.0[..layout.memory.size()],
                            &bytes.0[..layout.memory.size()],
                            "{label}, LLVM O{optimization}"
                        );
                    }
                }
                assert_eq!((context.depth, context.live_bytes), (0, 0), "{label}");
            }
        }
    }
}
