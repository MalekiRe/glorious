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
fn generated_native_fixed_array_patterns_preserve_borrowed_shells() {
    for source in [
        "fn keep<T,const N: usize>(value: [T;N]) -> [T;N] { value } pub fn main() -> i64 { let [a,b]: [i64;2] = keep([20,22]); a+b }",
        "pub fn main() -> i64 { let [a,..,b]: [i64;4] = [20,1,2,22]; a+b }",
        "pub fn main() -> i64 { let [[_,_],[a,b]]: [[i64;2];2] = [[1,2],[20,22]]; a+b }",
        "fn empty(value: &[i64;0]) -> i64 { handle *value { [] => 42 } } pub fn main() -> i64 { empty(&[]) }",
        "enum State { Full(i64), Empty } fn inspect(value: &[State;2]) -> i64 { handle *value { [State::Full(20),State::Empty] => 42, _ => 0 } } pub fn main() -> i64 { let value: [State;2] = [State::Full(20),State::Empty]; inspect(&value) }",
        "enum State { Full(i64), Empty } fn inspect(value: &mut [State;2]) -> i64 { handle *value { [State::Full(20),State::Empty] => 42, _ => 0 } } pub fn main() -> i64 { let mut value: [State;2] = [State::Full(20),State::Empty]; inspect(&mut value) }",
        "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {}
            impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } }
            enum State<'a> { Full(Probe<'a>), Empty } struct Slot<'a> { states: [State<'a>;2] }
            fn inspect<'a,'b>(slot: &'a Slot<'b>) -> i64 { handle slot.states { [State::Full(_),State::Empty] => 41, _ => 0 } }
            pub fn main() -> i64 { let mut count = 0; let observed = { let slot = Slot { states: [State::Full(Probe { count: &mut count }),State::Empty] }; inspect(&slot) }; observed + count }",
    ] {
        let ir = compile(source);
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
        for optimization in [0,2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default())
                .unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
        }
    }
}

#[test]
fn native_partial_owner_sidecars_preserve_exactly_once_source_drop_across_engines() {
    let declarations =
        "struct Probe<'a> { count: &'a mut i64 } impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 1; } }";
    for body in [
        "struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
            pub fn main() -> i64 { let mut a = 20; let mut b = 20; {
                let pair = Pair { first: Probe { count: &mut a },second: Probe { count: &mut b } };
                let first = pair.first; ()
            }; a+b }",
        "pub fn main() -> i64 { let mut a = 20; let mut b = 20; {
            let [first,..]: [Probe<'_>;2] = [Probe { count: &mut a },Probe { count: &mut b }]; ()
        }; a+b }",
        "enum Group<'a> { Pair(Probe<'a>,Probe<'a>), Empty }
            pub fn main() -> i64 { let mut a = 20; let mut b = 20; {
                let values: [Group<'_>;2] = [Group::Pair(Probe { count: &mut a },Probe { count: &mut b }),Group::Empty];
                handle values { [Group::Pair(first,_),Group::Empty] => (), _ => () }
            }; a+b }",
        "struct Pair<'a> { first: Probe<'a>, second: Probe<'a> }
            pub fn main() -> i64 { let mut a = 20; let mut b = 20; {
                let [Pair { first: first,second: _ },..]: [Pair<'_>;1] = [Pair { first: Probe { count: &mut a },second: Probe { count: &mut b } }]; ()
            }; a+b }",
    ] {
        let source = format!("{declarations} {body}");
        let ir = compile(&source);
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
        let cleanup_keys = ir.function_keys().iter().copied().filter(|key| {
            let function = ir.function(*key).unwrap();
            function.parameters == 1 && matches!(function.registers[0], grandiose_stage0::VmType::Nominal { .. }
                | grandiose_stage0::VmType::Tuple(_) | grandiose_stage0::VmType::FixedArray { .. })
        }).collect::<Vec<_>>();
        assert!(!cleanup_keys.is_empty());
        let plans = [ir.clone(), ir.with_vm_functions([ir.entry_key()]).unwrap(), ir.with_vm_functions(cleanup_keys).unwrap()];
        for plan in plans {
            for optimization in [0,2] {
                let native = unsafe { plan.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(native.run_i64_with_limits(Default::default())
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")), 42, "{source}");
            }
        }
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

const MEMORY_HELPERS: &str = r#"
    pub unsafe fn native_home<T>(value: T) -> *mut T {
        unsafe {
            let bytes = __g1_memory_allocate(__g1_memory_size_of<T>(), __g1_memory_align_of<T>());
            let pointer = __g1_memory_cast<u8,T>(bytes);
            __g1_memory_write(pointer, value);
            pointer
        }
    }
    pub unsafe fn native_take<T>(pointer: *mut T) -> T {
        unsafe {
            let value = __g1_memory_read(__g1_memory_as_const(pointer));
            __g1_memory_deallocate(__g1_memory_cast<T,u8>(pointer), __g1_memory_size_of<T>(), __g1_memory_align_of<T>());
            value
        }
    }
    pub unsafe fn native_grow(pointer: *mut i64) -> *mut i64 {
        unsafe {
            let bytes = __g1_memory_reallocate(__g1_memory_cast<i64,u8>(pointer), 8, 8, 16);
            let pointer = __g1_memory_cast<u8,i64>(bytes);
            __g1_memory_write(__g1_memory_offset(pointer, 1), 22);
            pointer
        }
    }
    pub unsafe fn native_sum_take(pointer: *mut i64) -> i64 {
        unsafe {
            let first = __g1_memory_read(__g1_memory_as_const(pointer));
            let second = __g1_memory_read(__g1_memory_offset_const(__g1_memory_as_const(pointer), 1));
            __g1_memory_deallocate(__g1_memory_cast<i64,u8>(pointer), 16, 8);
            first + second
        }
    }
    pub unsafe fn native_unique<'a,T>(pointer: *mut T) -> &'a mut T {
        unsafe { __g1_memory_borrow_unique(pointer) }
    }
    pub unsafe fn native_overlap_copy() -> i64 {
        unsafe {
            let allocation = __g1_memory_allocate(24, 8);
            let pointer = __g1_memory_cast<u8,i64>(allocation);
            __g1_memory_write(pointer, 20);
            __g1_memory_write(__g1_memory_offset(pointer, 1), 21);
            __g1_memory_copy(__g1_memory_as_const(pointer), __g1_memory_offset(pointer, 1), 2);
            let answer = __g1_memory_read(__g1_memory_as_const(__g1_memory_offset(pointer, 1)))
                + __g1_memory_read(__g1_memory_as_const(__g1_memory_offset(pointer, 2))) + 1;
            __g1_memory_deallocate(allocation, 24, 8);
            answer
        }
    }
    pub unsafe fn native_nonoverlap_copy() -> i64 {
        unsafe {
            let original = native_grow(native_home(20));
            let destination = __g1_memory_cast<u8,i64>(__g1_memory_allocate(16, 8));
            __g1_memory_copy_nonoverlapping(__g1_memory_as_const(original), destination, 2);
            __g1_memory_deallocate(__g1_memory_cast<i64,u8>(original), 16, 8);
            native_sum_take(destination)
        }
    }
    pub unsafe fn native_bad_layout() { unsafe { let pointer = __g1_memory_allocate(1, 3); () } }
    pub unsafe fn native_bad_extent() { unsafe { let pointer = __g1_memory_offset(__g1_memory_dangling<i64>(), 18446744073709551615); () } }
    pub unsafe fn native_bad_reference<'a>() -> &'a mut i64 { unsafe { __g1_memory_borrow_unique(__g1_memory_null<i64>()) } }
    pub unsafe fn native_allocate_and_release(size: usize) {
        unsafe { let pointer = __g1_memory_allocate(size, 8); __g1_memory_deallocate(pointer, size, 8) }
    }
"#;

fn memory_request(source: &str) -> CompilationRequest {
    let mut input = request(&format!("use std::*; {source}"));
    let standard_library = PackageKey("std@0.1.0".into());
    let path = LogicalPath::parse("src/lib.glorious").unwrap();
    input.sources.push(SourceInput::new(
        standard_library.clone(),
        path.clone(),
        include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
    ));
    // Pin the existing machine-leaf manifest before adding ordinary source
    // helpers. The fixture cannot mint a new machine operation by spelling.
    let compiler = StageZeroCompiler::new();
    let revision = compiler.import_revision(input.clone(), None).unwrap();
    input.runtime_manifest = compiler
        .open_session(revision)
        .unwrap()
        .snapshot()
        .world()
        .runtime_manifest
        .clone();
    input.sources[1] = SourceInput::new(
        standard_library,
        path,
        format!(
            "{}\n{MEMORY_HELPERS}",
            include_str!("../../../stdlib/src/lib.glorious")
        )
        .as_bytes(),
    );
    input
}

#[test]
fn generated_native_allocations_memory_operations_and_zero_byte_owners() {
    for source in [
        "pub fn main() -> i64 { unsafe { native_take(native_home(42)) } }",
        "pub fn main() -> i64 { unsafe { native_sum_take(native_grow(native_home(20))) } }",
        "pub fn main() -> i64 { unsafe { native_overlap_copy() } }",
        "pub fn main() -> i64 { unsafe { native_nonoverlap_copy() } }",
        "pub fn main() -> i64 { unsafe { let pointer = native_home(40); { let view = native_unique(pointer); *view = *view + 2; }; native_take(pointer) } }",
        "struct Token {} impl Use<[1,1]> for Token {} pub fn main() -> i64 { unsafe { let Token {} = native_take(native_home(Token {})); }; 42 }",
    ] {
        let ir = StageZeroCompiler::new()
            .compile_llvm(memory_request(source), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(
            unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(),
            42
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
                Err(LlvmError::Runtime(
                    VmArtifactError::UnsafeExecutionRequiresUnsafeApi
                ))
            ));
            assert_eq!(
                unsafe { native.run_i64_with_unsafe(Default::default()) }
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")),
                42
            );
        }
    }
}

#[test]
fn generated_and_vm_allocate_resize_and_release_in_the_same_domain() {
    use grandiose_stage0::{MemoryPrimitive as M, VmInstruction as I};
    let source =
        "pub fn main() -> i64 { unsafe { native_sum_take(native_grow(native_home(20))) } }";
    let ir = StageZeroCompiler::new()
        .compile_llvm(memory_request(source), LlvmTarget::host().unwrap())
        .unwrap();
    for selected in [M::Allocate, M::Reallocate, M::Deallocate] {
        let vm_functions = ir
            .function_keys()
            .iter()
            .copied()
            .filter(|key| {
                *key == ir.entry_key()
                    || ir
                        .function(*key)
                        .unwrap()
                        .instructions
                        .iter()
                        .any(|instruction| {
                            matches!(instruction,
                I::MemoryIntrinsic { primitive, .. } if *primitive == selected)
                        })
            })
            .collect::<Vec<_>>();
        assert_eq!(vm_functions.len(), 2);
        let mixed = ir.with_vm_functions(vm_functions).unwrap();
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
}

#[test]
fn native_raw_memory_checks_preserve_errors_and_finite_allocation_limits() {
    for (source, expected) in [
        (
            "pub fn main() -> i64 { unsafe { native_bad_layout(); }; 42 }",
            "invalid raw allocation layout",
        ),
        (
            "pub fn main() -> i64 { unsafe { native_bad_extent(); }; 42 }",
            "native layout size overflow",
        ),
        (
            "pub fn main() -> i64 { unsafe { let pointer = native_bad_reference(); }; 42 }",
            "native reference requires a non-null aligned pointer",
        ),
    ] {
        let ir = StageZeroCompiler::new()
            .compile_llvm(memory_request(source), LlvmTarget::host().unwrap())
            .unwrap();
        for optimization in [0, 2] {
            let native = unsafe {
                ir.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap();
            let error = unsafe { native.run_i64_with_unsafe(Default::default()) }.unwrap_err();
            assert!(
                matches!(error, LlvmError::Runtime(VmArtifactError::NativeMemory { message }) if message == expected),
                "{error:?}"
            );
        }
    }
    let input = memory_request(
        "pub fn main() -> i64 { unsafe { native_allocate_and_release(2097152); }; 42 }",
    );
    let ir = StageZeroCompiler::new()
        .compile_llvm(input, LlvmTarget::host().unwrap())
        .unwrap();
    for optimization in [0, 2] {
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(
            unsafe {
                native.run_i64_with_unsafe(VmExecutionLimits {
                    max_native_allocation_bytes: 4194304,
                    ..Default::default()
                })
            }
            .unwrap(),
            42
        );
        for limits in [
            VmExecutionLimits {
                max_native_allocation_bytes: 1048576,
                ..Default::default()
            },
            VmExecutionLimits {
                max_native_bytes: 1048576,
                max_native_allocation_bytes: 4194304,
                ..Default::default()
            },
        ] {
            let error = unsafe { native.run_i64_with_unsafe(limits) }.unwrap_err();
            assert!(
                matches!(
                    error,
                    LlvmError::Runtime(VmArtifactError::NativeMemory {
                        message: "native memory budget exceeded"
                    })
                ),
                "{error:?}"
            );
        }
    }
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
fn cross_engine_mandatory_tails_release_frames_and_permute_arguments() {
    let source = "fn vm_even(n: i64, a: i64, b: i64) -> i64 {
            let marker = 41001;
            handle n == 0 { true => a * 10 + b, false => tail native_odd(b, a, n - 1) }
        }
        fn native_odd(a: i64, b: i64, n: i64) -> i64 {
            handle n == 0 { true => a * 10 + b, false => tail vm_even(n - 1, b, a) }
        }
        pub fn main() -> i64 { let marker = 41002; tail vm_even(10000, 4, 2) }";
    let mixed = compile_mixed(source);
    let limits = VmExecutionLimits {
        max_call_depth: 16,
        ..Default::default()
    };
    assert_eq!(mixed.vm_program().run_i64_with_limits(limits).unwrap(), 42);
    for optimization in [0, 2] {
        let native = unsafe {
            mixed.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(native.run_i64_with_limits(limits).unwrap(), 42);
    }
}

#[test]
fn mixed_tail_packets_preserve_reference_returns_owned_drop_and_zero_sized_values() {
    let cases = [
        "fn vm_bounce<'a>(n: i64, value: &'a mut i64) -> &'a mut i64 {
            let marker = 41001;
            handle n == 0 { true => value, false => tail native_bounce(value, n - 1) }
        }
        fn native_bounce<'a>(value: &'a mut i64, n: i64) -> &'a mut i64 {
            handle n == 0 { true => value, false => tail vm_bounce(n - 1, value) }
        }
        pub fn main() -> i64 {
            let marker = 41002; let mut count = 40;
            let view = vm_bounce(1000, &mut count); *view = *view + 2; count
        }",
        "struct Probe<'a> { count: &'a mut i64 }
        impl<'a> Use<[0,1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.count = *self.count + 2; } }
        fn vm_bounce<'a>(n: i64, value: Probe<'a>) -> Probe<'a> {
            let marker = 41001;
            handle n == 0 { true => value, false => tail native_bounce(value, n - 1) }
        }
        fn native_bounce<'a>(value: Probe<'a>, n: i64) -> Probe<'a> {
            handle n == 0 { true => value, false => tail vm_bounce(n - 1, value) }
        }
        pub fn main() -> i64 {
            let marker = 41002; let mut count = 40;
            { let probe = vm_bounce(1000, Probe { count: &mut count }); () }; count
        }",
        "struct Token {} impl Use<[1,1]> for Token {}
        fn vm_bounce(n: i64, value: Token) -> Token {
            let marker = 41001;
            handle n == 0 { true => value, false => tail native_bounce(value, n - 1) }
        }
        fn native_bounce(value: Token, n: i64) -> Token {
            handle n == 0 { true => value, false => tail vm_bounce(n - 1, value) }
        }
        pub fn main() -> i64 {
            let marker = 41002; let Token {} = vm_bounce(1000, Token {}); 42
        }",
    ];
    for source in cases {
        let ir = compile_mixed(source);
        let limits = VmExecutionLimits {
            max_call_depth: 16,
            max_native_bytes: 128 * 1024,
            ..Default::default()
        };
        assert_eq!(ir.vm_program().run_i64_with_limits(limits).unwrap(), 42);
        for optimization in [0, 2] {
            let native = unsafe {
                ir.compile(&LlvmCompileOptions {
                    optimization,
                    ..Default::default()
                })
            }
            .unwrap();
            assert_eq!(
                native
                    .run_i64_with_limits(limits)
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")),
                42
            );
        }
    }
}

#[test]
fn mixed_tail_handoff_keeps_surviving_ordinary_vm_callers() {
    let source = "fn native_answer() -> i64 { 40 }
        fn vm_inner() -> i64 { let marker = 41001; tail native_answer() }
        fn vm_outer() -> i64 { let marker = 41001; vm_inner() + 2 }
        fn native_entry() -> i64 { tail vm_outer() }
        pub fn main() -> i64 { let marker = 41002; native_entry() }";
    let ir = compile_mixed(source);
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
