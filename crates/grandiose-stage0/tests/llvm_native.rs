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
fn generated_borrowed_captures_share_original_and_nested_storage() {
    for source in [
        "pub fn main() -> i64 { let mut value = 40; let task = () -> () { value = value + 1; }; task(); task(); value }",
        "pub fn main() -> i64 { let mut value = 40; let outer = () -> () { let inner = () -> () { value = value + 1; }; inner(); value = value + 1; }; outer(); value }",
        "struct Counter { value: i64 } pub fn main() -> i64 { let mut counter = Counter { value: 40 }; let task = () -> () { counter.value = counter.value + 2; }; task(); counter.value }",
        "pub fn main() -> i64 { let mut seed = 41; let outer = move (seed) { let inner = () -> () { seed = seed + 1; }; inner(); seed }; outer() }",
        "fn bad() -> () -> i64 { let value = 42; () -> i64 { value } } pub fn main() -> i64 { bad()() }",
        "pub fn main() -> i64 { let value = 42; let result = { let reader = () -> &i64 { &value }; reader() }; *result }",
    ] {
        check_mixed_capture_source(source);
    }
}

#[test]
fn generated_borrowed_capture_storage_does_not_extend_source_permission() {
    for (source, codes) in [
        ("fn bad() -> () -> i64 { let value = 42; () -> i64 { let observed = &value; *observed } } pub fn main() -> i64 { bad()() }", &["G5014"][..]),
        ("pub fn main() -> i64 { let mut value = 41; let task = () -> () { value = 42; }; let observed = &value; task(); *observed }", &["G5004", "G5006", "G5007"][..]),
    ] {
        let error = match StageZeroCompiler::new().compile_llvm(request(source), LlvmTarget::host().unwrap()) {
            Err(error) => error,
            Ok(_) => panic!("source unexpectedly admitted: {source}"),
        };
        let grandiose_stage0::vm_backend::llvm::LlvmError::Source(error) = error else { panic!("expected source rejection: {error:#?}"); };
        assert!(error.diagnostics().iter().any(|diagnostic| codes.contains(&diagnostic.code)), "{source}\n{error:#?}");
    }
}

#[test]
fn mixed_callable_capture_loans_preserve_storage_and_partial_cleanup() {
    for source in [
        "pub fn main() -> i64 { let empty = (); let task = move (empty) { let observed = empty; 42 }; task() }",
        "pub fn main() -> i64 { let mut seed = 20; let mut first = move (seed) { seed = seed + 1; seed }; let mut second = first; (&mut first)() + (&mut second)() }",
        "pub fn main() -> i64 { let mut seed = 19; let mut task = move (seed) { seed = seed + 1; seed }; let first = (&mut task)(); let second = (&mut task)(); first + second + 1 }",
        "fn keep<T>(value:T) -> T { value } fn make(value:i64) -> () -> i64 { move (value) { value } } pub fn main() -> i64 { let (task,) = keep((make(42),)); task() }",
        "fn make<'a>(value:&'a i64) -> () -> i64 { let inner = move (value) { *value }; move (inner) { inner() } } pub fn main() -> i64 { let value = 42; make(&value)() }",
        "struct Probe<'a> { counter:&'a mut i64 } impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.counter = *self.counter + 1; } } pub fn main() -> i64 { let mut left = 20; let mut right = 20; { let pair = (Probe { counter:&mut left }, Probe { counter:&mut right }); let task = move (pair) { let first = pair.0; () }; task() }; left + right }",
    ] {
        check_mixed_capture_source(source);
    }
}

#[test]
fn mixed_returned_capture_references_preserve_their_backing_loan() {
    check_mixed_capture_source("fn make<'a>(value:&'a i64) -> () -> &'a i64 { move (value) { value } } pub fn main() -> i64 { let value = 42; let task = make(&value); *task() }");
}

#[test]
fn mixed_returned_unique_capture_references_transfer_their_handle() {
    check_mixed_capture_source("fn make<'a>(value:&'a mut i64) -> () -> &'a mut i64 { move (value) { value } } pub fn main() -> i64 { let mut value = 41; let result = make(&mut value)(); *result = *result + 1; *result }");
}

#[test]
fn generated_borrowed_referents_preserve_move_and_restore_through_capture_calls() {
    let source = "pub fn main() -> i64 { let mut value = (1,2); let reference = &mut value; let task = move (reference) { let old = move *reference; *reference = (20,22); old }; let old = task(); value.0 + value.1 + old.0 + old.1 - 3 }";
    let artifact = StageZeroCompiler::new().compile(request(source)).unwrap().artifact.unwrap();
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert_eq!(grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    check_mixed_capture_source(source);
}

#[test]
fn generated_references_to_capture_storage_survive_the_invocation_frame() {
    for source in [
        "pub fn main() -> i64 { let value = (20,22); let task = move (value) { &value }; let result = (&task)(); result.0 + result.1 }",
        "pub fn main() -> i64 { let backing = 42; let value = (&backing,0); let task = move (value) { &value }; let result = (&task)(); *result.0 }",
        "pub fn main() -> i64 { let value = (0,42); let task = move (value) { &value.1 }; let result = (&task)(); *result }",
        "pub fn main() -> i64 { let mut value = 41; let mut task = move (value) { &mut value }; let result = (&mut task)(); *result = *result + 1; *result }",
        "pub fn main() -> i64 { let first = 1; let final_value = 42; let mut value = (&first,0); let mut task = move (value) { &mut value }; let result = (&mut task)(); result.0 = &final_value; *result.0 }",
        "pub fn main() -> i64 { let a = 1; let b = 42; let first = (&a,0); let second = (&b,0); let task = move (first,second) { let unused = first.1; &second }; let result = (&task)(); *result.0 }",
        "pub fn main() -> i64 { let empty = (); let task = move (empty) { &empty }; let result = (&task)(); let observed = *result; 42 }",
        "pub fn main() -> i64 { let mut value = (1,2); let mut task = move (value) { &mut value }; { let result = (&mut task)(); let old = move *result; *result = (20,22); () }; let result = (&mut task)(); result.0 + result.1 }",
    ] { check_mixed_capture_source(source); }
}

#[test]
fn generated_nested_capture_storage_keeps_logical_owners() {
    for source in [
        "pub fn main() -> i64 { let value = 42; let inner = move (value) { &value }; let outer = move (inner) { &inner }; let borrowed = (&outer)(); let result = borrowed(); *result }",
        "pub fn main() -> i64 { let value = 42; let task = move (value) { &value }; let copied = task; let result = (&copied)(); let moved = move task; *result }",
        "struct Pair { first:i64, second:i64 } pub fn main() -> i64 { let value = Pair { first:20, second:22 }; let task = move (value) { &value }; let result = (&task)(); result.first + result.second }",
        "pub fn main() -> i64 { let value: [i64;2] = [20,22]; let task = move (value) { &value }; let result = (&task)(); handle *result { [first,second] => first + second } }",
    ] { check_mixed_capture_source(source); }
}

fn check_mixed_capture_source(source: &str) {
    let ir = compile(source);
    assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
    assert_eq!(grandiose_stage0::decode_and_verify_program(&ir.vm_program().canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    for optimization in [0, 2] {
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap_or_else(|error|
            panic!("all-native O{optimization}: {source}: {error:#?}")), 42);
    }
    for partition in 0..3 {
        let selected = ir.function_keys().iter().copied().filter(|key| {
            let captured = ir.function(*key).unwrap().captures != 0;
            match partition { 0 => *key == ir.entry_key(), 1 => captured, _ => !captured }
        }).collect::<Vec<_>>();
        assert!(!selected.is_empty() && selected.len() < ir.function_keys().len());
        let mixed = ir.with_vm_functions(selected).unwrap_or_else(|error| panic!("partition {partition}: {source}: {error:#?}"));
        for optimization in [0, 2] {
            let native = unsafe { mixed.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap_or_else(|error|
                panic!("partition {partition}, O{optimization}: {source}: {error:#?}")), 42);
        }
    }
}

#[test]
fn mixed_capture_faults_preserve_the_original_runtime_error() {
    let ir = compile("pub fn main() -> i64 { let value = 42; let task = move (value) { value / 0 }; task() }");
    for vm_captures in [false, true] {
        let selected = ir.function_keys().iter().copied().filter(|key|
            (ir.function(*key).unwrap().captures != 0) == vm_captures).collect::<Vec<_>>();
        let mixed = ir.with_vm_functions(selected).unwrap();
        for optimization in [0, 2] {
            let native = unsafe { mixed.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            let failure = native.run_i64_with_limits(Default::default());
            assert!(matches!(failure, Err(LlvmError::Runtime(VmArtifactError::DivisionByZero))), "{failure:?}");
        }
    }
}

#[test]
fn ordinary_native_callable_environments_execute_and_return_through_products() {
    for source in [
        "pub fn main() -> i64 { let value = 42; let reader = move (value) { value }; reader() }",
        "fn make(value:i64) -> () -> i64 { move (value) { value } } pub fn main() -> i64 { let reader = make(42); reader() }",
        "fn keep<T>(value:T) -> T { value } pub fn main() -> i64 { let value = 42; let reader = move (value) { value }; let (reader,) = keep((reader,)); reader() }",
        "fn invoke<F>(task:F) -> i64 where F:Fn<(),Output=i64,Effects={}> { task() } fn relay<F>(task:F) -> i64 where F:Fn<(),Output=i64,Effects={}> { tail invoke(task) } pub fn main() -> i64 { let value = 42; let reader = move (value) { value }; relay(reader) }",
        "enum Flag { Yes, No } fn make(flag:Flag) -> () -> i64 { let value = 42; let pair = (20,22); handle flag { Flag::Yes => move (value) { value }, Flag::No => move (pair) { pair.0 + pair.1 } } } pub fn main() -> i64 { make(Flag::Yes)() + make(Flag::No)() - 42 }",
    ] {
        for optimization in [0, 2] {
            let mut input = request(source);
            input.codegen_options.insert("optimization-level".into(), optimization.to_string());
            let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap())
                .unwrap_or_else(|error| panic!("{source}: {error:#?}"));
            if optimization == 0 {
                assert!(ir.function_keys().iter().any(|key| ir.function(*key).unwrap().captures != 0),
                    "the native environment ABI must actually be exercised");
            }
            assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
            assert_eq!(grandiose_stage0::decode_and_verify_program(&ir.vm_program().canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }
                .unwrap_or_else(|error| panic!("{source}: {error:#?}")).0, 42);
        }
    }
}

#[test]
fn ordinary_native_callable_loans_copy_and_capture_destruction_compose() {
    for source in [
        "fn make() -> () -> i64 { let mut seed = 41; move (seed) { seed = seed + 1; seed } } pub fn main() -> i64 { make()() }",
        "fn make<'a>(value:&'a i64) -> () -> i64 { let inner = move (value) { *value }; move (inner) { inner() } } pub fn main() -> i64 { let value = 42; make(&value)() }",
        "fn twice<F>(body:&F) -> i64 where for<'a> &'a F:Fn<(),Output=i64,Effects={}> { body() + body() } pub fn main() -> i64 { let value = 21; let reader = move (value) { value }; twice(&reader) }",
        "pub fn main() -> i64 { let value = 21; let reader = move (value) { value }; let second = reader; reader() + second() }",
        "pub fn main() -> i64 { let mut seed = 19; let mut task = move (seed) { seed = seed + 1; seed }; let first = (&mut task)(); let second = (&mut task)(); first + second + 1 }",
        "pub fn main() -> i64 { let mut seed = 20; let mut first = move (seed) { seed = seed + 1; seed }; let mut second = first; (&mut first)() + (&mut second)() }",
        "struct Probe<'a> { counter:&'a mut i64 } impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.counter = *self.counter + 1; } } pub fn main() -> i64 { let mut counter = 41; { let probe = Probe { counter:&mut counter }; let task = move (probe) { let observation = &probe; () }; () }; counter }",
    ] {
        for optimization in [0, 2] {
            let mut input = request(source);
            input.codegen_options.insert("optimization-level".into(), optimization.to_string());
            let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap())
                .unwrap_or_else(|error| panic!("{source}: {error:#?}"));
            assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
            assert_eq!(grandiose_stage0::decode_and_verify_program(&ir.vm_program().canonical_bytes()).unwrap().run_i64().unwrap(), 42);
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }
                .unwrap_or_else(|error| panic!("{source}: {error:#?}")).0, 42);
        }
    }
}

#[test]
fn ordinary_native_callable_partial_captures_destroy_each_remaining_owner_once() {
    let source = "struct Probe<'a> { counter:&'a mut i64 } impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.counter = *self.counter + 1; } }
        pub fn main() -> i64 { let mut left = 20; let mut right = 20; {
            let pair = (Probe { counter:&mut left }, Probe { counter:&mut right });
            let task = move (pair) { let first = pair.0; () }; task()
        }; left + right }";
    for optimization in [0, 2] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.to_string());
        let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("{source}: {error:#?}"));
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
        assert_eq!(grandiose_stage0::decode_and_verify_program(&ir.vm_program().canonical_bytes()).unwrap().run_i64().unwrap(), 42);
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }
            .unwrap_or_else(|error| panic!("{source}: {error:#?}")).0, 42);
    }
}

#[test]
fn ordinary_native_callable_raw_heap_transport_preserves_its_environment() {
    let source = "pub fn main() -> i64 { let value = 42; let reader = move (value) { value }; unsafe { let restored = native_take(native_home(reader)); restored() } }";
    for optimization in [0, 2] {
        let mut input = memory_request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.to_string());
        let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap()).unwrap();
        assert_eq!(unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { grandiose_stage0::decode_and_verify_program(&ir.vm_program().canonical_bytes()).unwrap()
            .run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
    }
}

#[test]
fn ordinary_native_callable_partial_raw_overwrite_cannot_retain_authority() {
    let source = "pub fn main() -> i64 { let value = 42; let reader = move (value) { value }; unsafe {
        let pointer = native_home(reader); native_rewrite_prefix(pointer);
        let restored = native_take(pointer); restored()
    } }";
    for optimization in [0, 2] {
        let mut input = memory_request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.to_string());
        let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap()).unwrap();
        assert!(matches!(unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) },
            Err(VmArtifactError::NativeMemory { message }) if message.contains("callable")));
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert!(matches!(unsafe { native.run_i64_profiled(Default::default()) },
            Err(LlvmError::Runtime(VmArtifactError::NativeMemory { message })) if message.contains("callable")));
    }
}

#[test]
fn ordinary_native_callable_faults_and_activation_limits_remain_explicit() {
    for optimization in [0, 2] {
        let ir = compile("pub fn main() -> i64 { let value = 42; let task = move (value) { value / 0 }; task() }");
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert!(matches!(unsafe { native.run_i64_profiled(Default::default()) },
            Err(LlvmError::Runtime(VmArtifactError::DivisionByZero))));
        let limits = VmExecutionLimits { max_native_allocation_bytes: 1, ..Default::default() };
        let failure = unsafe { native.run_i64_profiled(limits) };
        assert!(matches!(failure,
            Err(LlvmError::Runtime(VmArtifactError::NativeMemory { message }))
                if message.contains("shared byte budget")), "{failure:#?}");
    }
}

#[test]
fn erased_label_products_cross_native_and_mixed_forwarding_abis() {
    check_erased_label_product("let ((destination,), value) = native_keep(((@main,),42)); destination(value)");
}

#[test]
fn erased_label_products_preserve_captures_in_native_and_mixed_execution() {
    check_erased_label_product("let value = 42; let reader = move (value) { value }; let (destination, callback) = native_keep((@main,reader)); destination(callback())");
}

fn check_erased_label_product(body: &str) {
        let source = format!("fn vm_keep<T>(value:T) -> T {{ let marker = 41001; value }}
            fn native_keep<T>(value:T) -> T {{ vm_keep(value) }}
            pub fn main() -> i64 {{ let marker = 41002; {body} }}");
        for optimization in [0, 2] {
            let mut input = request(&source);
            input.codegen_options.insert("optimization-level".into(), optimization.to_string());
            for mixed in [false, true] {
                let selected = std::cell::Cell::new(0);
                let unselected = std::cell::Cell::new(0);
                let ir = StageZeroCompiler::new().compile_llvm_partitioned(input.clone(), LlvmTarget::host().unwrap(), |function| {
                    let use_vm = mixed && function.instructions.iter().any(|instruction| matches!(instruction,
                        grandiose_stage0::VmInstruction::ConstI64 { value: 41001 | 41002, .. }));
                    if use_vm { selected.set(selected.get() + 1); } else { unselected.set(unselected.get() + 1); }
                    use_vm
                })
                    .unwrap_or_else(|error| panic!("{source}, mixed={mixed}: {error:#?}"));
                assert!(unselected.get() >= 1);
                if mixed { assert!(selected.get() >= 2, "the mixed fixture must retain both VM endpoints"); }
                else { assert_eq!(selected.get(), 0); }
                assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
                let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(native.run_i64_with_limits(Default::default())
                    .unwrap_or_else(|error| panic!("{source}, mixed={mixed}: {error:#?}")), 42);
            }
        }
}

fn with_hostile_float_mode<T>(body: impl FnOnce() -> T) -> T {
    #[cfg(target_arch = "x86_64")]
    {
        struct Restore { mxcsr: u32, x87: u16 }
        impl Drop for Restore {
            fn drop(&mut self) {
                // SAFETY: these control words were captured on this thread.
                unsafe {
                    std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &self.mxcsr, options(nostack));
                    std::arch::asm!("fldcw [{p}]", p = in(reg) &self.x87, options(nostack));
                }
            }
        }
        let mut saved = Restore { mxcsr: 0, x87: 0 };
        let hostile_mxcsr = 0xffd5_u32; // toward zero, FTZ/DAZ, masked exceptions, status flags
        let hostile_x87 = 0x0f7f_u16;
        // SAFETY: x86_64 supports SSE; all operands are aligned and all
        // exception masks stay set. The guard also restores on unwinding.
        unsafe {
            std::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut saved.mxcsr, options(nostack));
            std::arch::asm!("fnstcw [{p}]", p = in(reg) &mut saved.x87, options(nostack));
            std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &hostile_mxcsr, options(nostack));
            std::arch::asm!("fldcw [{p}]", p = in(reg) &hostile_x87, options(nostack));
        }
        let result = body();
        let mut after_mxcsr = 0_u32;
        let mut after_x87 = 0_u16;
        unsafe {
            std::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut after_mxcsr, options(nostack));
            std::arch::asm!("fnstcw [{p}]", p = in(reg) &mut after_x87, options(nostack));
        }
        assert_eq!((after_mxcsr, after_x87), (hostile_mxcsr, hostile_x87));
        result
    }
    #[cfg(not(target_arch = "x86_64"))]
    body()
}

#[test]
fn actual_llvm_native_scalar_control_matches_vm_at_o0_and_o2() {
    for source in [
        "pub fn main() -> i64 { 42 }",
        "fn add(left: i64, right: i64) -> i64 { left + right } pub fn main() -> i64 { add(40, 2) }",
        "struct Pair { first: i64, second: i64 } fn sum(value: &Pair) -> i64 { value.first + value.second } pub fn main() -> i64 { let pair = Pair { first: 40, second: 2 }; sum(&pair) }",
        "enum Choice { Yes(i64), No } fn choose(value: Choice) -> i64 { handle value { Choice::Yes(number) => number, Choice::No => 0 } } pub fn main() -> i64 { choose(Choice::Yes(42)) }",
        "enum Choice { Small(u8,i64), Wide(i128,i64), Other(Bool) } fn choose(value: Choice) -> i64 { handle value { Choice::Small(_,number) => number, Choice::Wide(_,number) => number, _ => 0 } } pub fn main() -> i64 { choose(Choice::Small(1,20)) + choose(Choice::Wide(1,22)) }",
        "enum Inner { Number(i64), Flag(Bool) } enum Outer { Nested(Inner), Number(i128) } fn choose(value: &Outer) -> i64 { handle *value { Outer::Nested(Inner::Number(number)) => number, _ => 0 } } pub fn main() -> i64 { let value = Outer::Nested(Inner::Number(42)); choose(&value) }",
        "fn update(value: &mut i64) { *value = *value + 2; } pub fn main() -> i64 { let mut value = 40; update(&mut value); value }",
        "pub fn main() -> i64 { let value: i128 = 170141183460469231731687303715884105700; handle value + 27 == 170141183460469231731687303715884105727 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { let left: f64 = 8.5; let right: f64 = 3.0; handle left % right == 2.5 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { let value: f32 = 20.0; handle value * 2.0 + 2.0 == 42.0 { true => 42, false => 0 } }",
    ] {
        let ir = compile(source);
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);
        assert!(ir.ir().contains("define i32 @g1_export_"));
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
fn native_float_conversions_preserve_public_source_policy_across_engines() {
    let mut source = String::from("use std::*; fn yes(value: Bool) -> i64 { handle value { true => 1, false => 0 } }\n");
    let mut groups = Vec::new();
    for (ty, maximum, signed) in [
        ("u8", "255", false), ("i8", "127", true),
        ("u16", "65535", false), ("i16", "32767", true),
        ("u32", "4294967295", false), ("i32", "2147483647", true),
        ("u64", "18446744073709551615", false), ("i64", "9223372036854775807", true),
        ("u128", "340282366920938463463374607431768211455", false),
        ("i128", "170141183460469231731687303715884105727", true),
        ("usize", "18446744073709551615", false), ("isize", "9223372036854775807", true),
    ] {
        let minimum = if signed { format!("wrapping_add({maximum}, 1)") } else { "0".into() };
        source.push_str(&format!("fn min_{ty}() -> {ty} {{ {minimum} }} fn max_{ty}() -> {ty} {{ {maximum} }}\n"));
        let mut checks = vec![
            "yes(f32_eq(as<f32>(value), 42.0))".to_owned(),
            "yes(f64_eq(as<f64>(value), 42.0))".to_owned(),
        ];
        for float in ["f32", "f64"] {
            checks.extend([
                format!("yes(as<{ty}>({float}_div(0.0, 0.0)) == 0)"),
                format!("yes(as<{ty}>({float}_div(1.0, 0.0)) == max_{ty}())"),
                format!("yes(as<{ty}>({float}_div(-1.0, 0.0)) == min_{ty}())"),
                format!("yes(as<{ty}>({float}_add(42.9, 0.0)) == value)"),
                format!("yes(as<{ty}>({float}_add(-0.9, 0.0)) == 0)"),
            ]);
        }
        source.push_str(&format!("fn check_{ty}(value: {ty}) -> i64 {{ {} }}\n", checks.join(" + ")));
        groups.push(format!("check_{ty}(42)"));
    }
    source.push_str("fn wide() -> u64 { 9223372586610589697 }
        fn widest() -> u128 { 340282366920938463463374607431768211455 }
        fn odd() -> u64 { 9007199254740993 }
        fn precision() -> i64 {
            let zero = as<f32>(-0.0);
            yes(f32_eq(as<f32>(wide()), 9223373136366403584.0)) +
            yes(f32_eq(as<f32>(widest()), f32_div(1.0, 0.0))) +
            yes(f64_eq(as<f64>(odd()), 9007199254740992.0)) +
            yes(f32_eq(as<f32>(16777217), 16777216.0)) +
            yes(f32_eq(as<f32>(16777219), 16777220.0)) +
            yes(f32_eq(as<f32>(1.000000059604644775390625), 1.0)) +
            yes(f32_eq(f32_div(1.0, zero), f32_div(-1.0, 0.0))) +
            yes(f64_eq(f64_div(1.0, as<f64>(zero)), f64_div(-1.0, 0.0)))
        }\n");
    groups.push("precision()".into());
    let expected = 12 * 12 + 8;
    for (index, group) in groups.chunks(4).enumerate() {
        source.push_str(&format!("fn group_{index}() -> i64 {{ {} }}\n", group.join(" + ")));
    }
    source.push_str("pub fn main() -> i64 { group_0() + group_1() + group_2() + group_3() }");
    let mut input = request(&source);
    input.sources.push(SourceInput::new(
        PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(),
        include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
    ));
    let ir = StageZeroCompiler::new().compile_llvm(input, LlvmTarget::host().unwrap())
        .unwrap_or_else(|error| panic!("{source}: {error:?}"));
    assert_eq!(ir.vm_program().run_i64().unwrap(), expected);
    let conversions = ir.function_keys().iter().copied().filter(|key| {
        ir.function(*key).unwrap().instructions.iter().any(|instruction| matches!(instruction,
            grandiose_stage0::VmInstruction::FloatIntrinsic { primitive: grandiose_stage0::runtime_manifest::FloatPrimitive::Convert { .. }, .. }))
    }).collect::<Vec<_>>();
    assert!(!conversions.is_empty() && conversions.len() < ir.function_keys().len());
    for plan in [ir.clone(), ir.with_vm_functions(conversions).unwrap(), ir.with_vm_functions([ir.entry_key()]).unwrap()] {
        for optimization in [0, 2] {
            let native = unsafe { plan.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), expected);
            assert_eq!(with_hostile_float_mode(|| native.run_i64_with_limits(Default::default())).unwrap(), expected);
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
fn static_byte_and_utf8_slots_share_native_backing_across_engines() {
    for source in [
        "fn literal() -> Slice<'static,u8> { b\"*\" } pub fn main() -> i64 { handle *Slice::get_unchecked(literal(), 0) == 42 { true => 42, false => 0 } }",
        "fn literal() -> Str<'static> { \"é🙂\" } pub fn main() -> i64 { handle Str::len(literal()) == 6 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { let value: Slice<'static,u8> = b\"\"; handle Slice::len(&value) == 0 { true => 42, false => 0 } }",
        "pub fn main() -> i64 { handle Str::len(\"\") == 0 { true => 42, false => 0 } }",
    ] {
        let ir = compile(source);
        assert_eq!(unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        let wrappers = ir.function_keys().iter().copied().filter(|key| {
            let function = ir.function(*key).unwrap();
            function.parameters > 0 && matches!(function.registers[0], grandiose_stage0::VmType::StaticData { .. })
        }).collect::<Vec<_>>();
        let literals = ir.function_keys().iter().copied().filter(|key| {
            ir.function(*key).unwrap().instructions.iter().any(|instruction|
                matches!(instruction, grandiose_stage0::VmInstruction::ConstStaticData { .. }))
        }).collect::<Vec<_>>();
        assert!(!wrappers.is_empty() && !literals.is_empty());
        for plan in [ir.clone(), ir.with_vm_functions(wrappers).unwrap(), ir.with_vm_functions(literals).unwrap()] {
            for optimization in [0,2] {
                let native = unsafe { plan.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(unsafe { native.run_i64_with_unsafe(Default::default()) }
                    .unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
            }
        }
    }
}

#[test]
fn static_literal_addresses_and_derived_views_survive_engine_returns() {
    for marker in ["", "let marker = 41001;"] {
        let source = format!("use std::*;
            fn literal() -> Slice<'static,u8> {{ {marker} b\"!*\" }}
            fn vm_observe<'a>(value: Slice<'a,u8>, expected: *const u8) -> i64 {{
                let marker = 41001;
                handle ptr_eq(ptr_from_ref(Slice::get_unchecked(value, 0)), expected) {{
                    true => handle *Slice::get_unchecked(value,0) == 42 {{ true => 42, false => 0 }}, false => 0,
                }}
            }}
            fn native_relay<'a>(value: Slice<'a,u8>, expected: *const u8) -> i64 {{
                handle Slice::slice(value, Range {{ start: 1, end: 2 }}) {{
                    Result::Ok(view) => vm_observe(view, expected), Result::Err(_) => 0,
                }}
            }}
            pub fn main() -> i64 {{
                let marker = 41002;
                let value = literal(); let again = literal();
                let expected = ptr_from_ref(Slice::get_unchecked(value,1));
                handle ptr_eq(ptr_from_ref(Slice::get_unchecked(again,1)), expected) {{
                    true => native_relay(value,expected), false => 0,
                }}
            }}");
        let mut input = request(&source);
        input.sources.push(SourceInput::new(
            PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(),
            format!("{}\n{}\n{}", include_str!("../../../stdlib/src/lib.glorious"),
                include_str!("../../../stdlib/src/foundation.glorious"),
                include_str!("../../../stdlib/src/memory.glorious")).as_bytes(),
        ));
        let ir = StageZeroCompiler::new().compile_llvm_partitioned(input, LlvmTarget::host().unwrap(), |function|
            function.instructions.iter().any(|instruction| matches!(instruction,
                grandiose_stage0::VmInstruction::ConstI64 { value: 41001 | 41002, .. })))
            .unwrap_or_else(|error| panic!("{source}: {error:?}"));
        assert_eq!(unsafe { ir.vm_program().run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        for optimization in [0,2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            assert_eq!(unsafe { native.run_i64_with_unsafe(Default::default()) }
                .unwrap_or_else(|error| panic!("{source}: {error:?}")), 42);
        }
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
fn native_effects_resume_across_an_ordinary_generated_call() {
    let source = "effect Ask { ask() -> i64; } fn ask() -> i64 / {Ask} { Ask::ask() } pub fn main() -> i64 { handle ask() { Ask::ask() with k => k(42) } }";
    let ir = StageZeroCompiler::new()
        .compile_llvm(request(source), LlvmTarget::host().unwrap())
        .unwrap();
    for optimization in [0, 2] {
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
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
    pub unsafe fn native_rewrite_prefix<T>(pointer: *mut T) {
        unsafe {
            let word = __g1_memory_cast<T,u64>(pointer);
            let bits = __g1_memory_read(__g1_memory_as_const(word));
            __g1_memory_write(word, bits);
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
fn explicit_vm_selection_uses_the_same_handler_control_runtime() {
    let source = "effect Ask { ask() -> i64; } fn ask() -> i64 / {Ask} { Ask::ask() }
        pub fn main() -> i64 { handle ask() { Ask::ask() with k => k(42) } }";
    let ir = StageZeroCompiler::new()
        .compile_llvm_partitioned(request(source), LlvmTarget::host().unwrap(), |_| true)
        .unwrap();
    for optimization in [0, 2] {
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}
