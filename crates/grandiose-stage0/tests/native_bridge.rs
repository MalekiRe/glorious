//! Executed VM/native ABI fixtures, not Rust-only shared-pointer probes.

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, VerifiedVmProgram, VmArtifactError, VmExecutionLimits,
    VmNativeCallback, VmNativeImports, VmNativeLayoutShape, VmNativeStatus, VmType,
};
use std::{
    cell::Cell,
    collections::BTreeMap,
    mem::{MaybeUninit, align_of, offset_of, size_of},
    rc::Rc,
};

const NATIVE_HOMES: &str = r#"
    // Test-owned ordinary source helpers. The original std manifest is kept
    // unchanged: these functions receive no new machine-primitive authority.
    pub unsafe fn native_home<T>(value: T) -> *mut T {
        unsafe {
            let bytes = __g1_memory_allocate(__g1_memory_size_of<T>(), __g1_memory_align_of<T>());
            let pointer = __g1_memory_cast<u8, T>(bytes);
            __g1_memory_write(pointer, value);
            pointer
        }
    }
    pub unsafe fn native_take<T>(pointer: *mut T) -> T {
        unsafe {
            let value = __g1_memory_read(__g1_memory_as_const(pointer));
            __g1_memory_deallocate(__g1_memory_cast<T, u8>(pointer), __g1_memory_size_of<T>(), __g1_memory_align_of<T>());
            value
        }
    }
    pub unsafe fn native_unique<'a, T>(pointer: *mut T) -> &'a mut T {
        unsafe { __g1_memory_borrow_unique(pointer) }
    }
    pub unsafe fn native_shared<'a, T>(pointer: *mut T) -> &'a T {
        unsafe { __g1_memory_borrow_shared(__g1_memory_as_const(pointer)) }
    }
"#;

fn request(source: &str) -> CompilationRequest {
    let app = PackageKey("native-bridge-fixture@0.1.0".into());
    let std = PackageKey("std@0.1.0".into());
    let mut request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"native-bridge-fixtures")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(
                app,
                LogicalPath::parse("src/main.glorious").unwrap(),
                // Operators and Boolean control flow are canonical source
                // library bindings, not an implicit compiler prelude.
                format!("use std::*;\n{source}").as_bytes(),
            ),
            SourceInput::new(
                std.clone(),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec!["interop".into()],
        runtime_manifest: None,
    };
    let compiler = StageZeroCompiler::new();
    let revision = compiler.import_revision(request.clone(), None).unwrap();
    request.runtime_manifest = compiler
        .open_session(revision)
        .unwrap()
        .snapshot()
        .world()
        .runtime_manifest
        .clone();
    request.sources[1] = SourceInput::new(
        std,
        LogicalPath::parse("src/lib.glorious").unwrap(),
        format!(
            "{}\n{NATIVE_HOMES}",
            include_str!("../../../stdlib/src/lib.glorious")
        )
        .as_bytes(),
    );
    request
}

fn compile(source: &str) -> VerifiedVmProgram {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    // Exercise the real codec, not an unchecked candidate execution shortcut.
    grandiose_stage0::decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes())
        .unwrap()
}

#[repr(C)]
struct NativePair {
    first: i64,
    second: i64,
}

#[test]
fn source_pointer_address_is_the_actual_backing_address_seen_by_native_code() {
    let mut input = request(r#"
        host interop fn inspect(pointer: *mut i64, address: usize) -> ();
        pub fn main() -> i64 {
            unsafe {
                let pointer = native_home(as<i64>(40));
                inspect(pointer, native_pointer_address(pointer));
                native_take(pointer)
            }
        }
    "#);
    input.sources[1] = SourceInput::new(PackageKey("std@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        format!("{}\n{NATIVE_HOMES}\n{}", include_str!("../../../stdlib/src/lib.glorious"), r#"
            pub fn native_pointer_address<T>(pointer: *mut T) -> usize {
                let readable = unsafe { __g1_memory_as_const(pointer) };
                __g1_memory_pointer_address(readable)
            }
        "#).as_bytes());
    let artifact = StageZeroCompiler::new().compile(input).unwrap().artifact.unwrap();
    let decoded = grandiose_stage0::decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    for program in [&artifact, &decoded] {
        let observed = Rc::new(Cell::new(false));
        let seen = observed.clone();
        let mut imports = VmNativeImports::default();
        let contract = program.native_imports().unwrap().remove(0);
        // SAFETY: source owns an initialized aligned i64 allocation throughout
        // this callback. Native code neither retains nor frees its pointer.
        unsafe {
            imports.insert(contract, move |call| {
                let mut pointer = MaybeUninit::<*mut i64>::uninit();
                let mut address = MaybeUninit::<usize>::uninit();
                call.write_argument(0, pointer.as_mut_ptr().cast())?;
                call.write_argument(1, address.as_mut_ptr().cast())?;
                let pointer = pointer.assume_init();
                assert_eq!(address.assume_init(), pointer.addr());
                assert_eq!(*pointer, 40);
                *pointer += 2;
                seen.set(true);
                Ok(())
            }).unwrap();
            assert_eq!(program.run_i64_with_native(&imports, Default::default()).unwrap(), 42);
        }
        assert!(observed.get());
    }
}

#[test]
fn ordinary_native_resident_arguments_copy_into_distinct_callee_homes() {
    for invocation in ["amend(pair)", "invoke(amend, pair)"] {
        let program = compile(&format!(
            r#"
            struct Pair {{ first: i64, second: i64 }}
            host interop fn observe(value: &Pair) -> ();
            host interop fn update(value: &mut Pair) -> ();
            fn amend(value: Pair) -> i64 {{
                let mut value = value;
                update(&mut value);
                value.first + value.second
            }}
            fn invoke(callback: (Pair) -> i64, value: Pair) -> i64 {{ callback(value) }}
            pub fn main() -> i64 {{
                let pair = Pair {{ first: 19, second: 20 }};
                observe(&pair);
                let result = {invocation};
                result
            }}
        "#
        ));
        let original = Rc::new(Cell::new(std::ptr::null::<NativePair>()));
        let updates = Rc::new(Cell::new(0));
        let mut imports = VmNativeImports::default();
        for contract in program.native_imports().unwrap() {
            let original = original.clone();
            let updates = updates.clone();
            // SAFETY: each argument borrows one live repr(C) Pair. The saved
            // address is compared only, never dereferenced after its call.
            unsafe {
                imports
                    .insert(contract.clone(), move |call| {
                        let mut slot = MaybeUninit::<*mut NativePair>::uninit();
                        call.write_argument(0, slot.as_mut_ptr().cast())?;
                        let pointer = slot.assume_init();
                        if contract.symbol == "observe" {
                            original.set(pointer);
                        } else {
                            assert_eq!(contract.symbol, "update");
                            assert!(!original.get().is_null());
                            assert_ne!(pointer.cast_const(), original.get());
                            (*pointer).first += 1;
                            (*pointer).second += 2;
                            updates.set(updates.get() + 1);
                        }
                        Ok(())
                    })
                    .unwrap();
            }
        }
        assert_eq!(
            unsafe { program.run_i64_with_native(&imports, VmExecutionLimits::default()) }.unwrap(),
            42
        );
        assert_eq!(updates.get(), 1);
    }
}

#[test]
fn native_linking_binds_selected_destructor_code_and_its_helpers() {
    fn source(delta: i64, unrelated: i64) -> String {
        format!(
            r#"
            struct Widget {{ value: i64 }}
            impl Use<[0, 1]> for Widget {{}}
            impl Drop for Widget {{ drop(&mut self) -> {{ note(delta()); }} }}
            fn delta() -> i64 {{ {delta} }}
            fn unrelated() -> i64 {{ {unrelated} }}
            host interop fn inspect(value: &Widget) -> i64;
            host interop fn note(value: i64) -> ();
            pub fn main() -> i64 {{ let value = Widget {{ value: 42 }}; inspect(&value) }}
        "#
        )
    }
    let original = compile(&source(1, 10));
    let changed = compile(&source(2, 10));
    let unrelated = compile(&source(1, 20));
    let contract = original
        .native_imports()
        .unwrap()
        .into_iter()
        .find(|import| import.symbol == "inspect")
        .unwrap();
    let replacement = changed
        .native_imports()
        .unwrap()
        .into_iter()
        .find(|import| import.symbol == "inspect")
        .unwrap();
    let unchanged = unrelated
        .native_imports()
        .unwrap()
        .into_iter()
        .find(|import| import.symbol == "inspect")
        .unwrap();
    assert_eq!(contract.parameters, replacement.parameters);
    assert_eq!(contract.nominals, replacement.nominals);
    assert_eq!(contract.source_contract, replacement.source_contract);
    assert_eq!(contract.residents.len(), 1);
    assert_eq!(
        contract.residents[0].resident,
        replacement.residents[0].resident
    );
    assert_ne!(
        contract.residents[0].destruction_code,
        replacement.residents[0].destruction_code
    );
    assert_eq!(
        contract, unchanged,
        "an unrelated body is not part of the destructor contract"
    );
    let calls = Rc::new(Cell::new(0));
    let drops = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in original.native_imports().unwrap() {
        let calls = calls.clone();
        let drops = drops.clone();
        // SAFETY: inspect only borrows the declared one-i64 resident; note is
        // the scalar source destructor hook. Neither retains native storage.
        unsafe {
            imports
                .insert(contract.clone(), move |call| {
                    if contract.symbol == "inspect" {
                        calls.set(calls.get() + 1);
                        let mut slot = MaybeUninit::<*const i64>::uninit();
                        call.write_argument(0, slot.as_mut_ptr().cast())?;
                        call.set_result_from(slot.assume_init().cast())
                    } else {
                        assert_eq!(contract.symbol, "note");
                        let mut slot = MaybeUninit::<i64>::uninit();
                        call.write_argument(0, slot.as_mut_ptr().cast())?;
                        drops.set(drops.get() + slot.assume_init());
                        Ok(())
                    }
                })
                .unwrap();
        }
    }
    assert_eq!(
        unsafe { original.run_i64_with_native(&imports, VmExecutionLimits::default()) }.unwrap(),
        42
    );
    assert_eq!(calls.get(), 1);
    assert_eq!(drops.get(), 1);
    assert!(matches!(
        unsafe { changed.run_i64_with_native(&imports, VmExecutionLimits::default()) },
        Err(VmArtifactError::NativeAbi {
            message: "native import source contract or concrete layout mismatch"
        })
    ));
    assert_eq!(
        calls.get(),
        1,
        "stale destructor code fails before any native call"
    );
    assert_eq!(drops.get(), 1);
}

#[test]
fn native_resident_operation_metadata_is_structurally_checked() {
    let program = compile(
        r#"
        struct Widget { value: i64 }
        impl Use<[0, 1]> for Widget {}
        impl Drop for Widget { drop(&mut self) -> { note(); } }
        host interop fn inspect(value: &Widget) -> i64;
        host interop fn note() -> ();
        pub fn main() -> i64 { let value = Widget { value: 42 }; inspect(&value) }
    "#,
    );
    for changed in 0..4 {
        let mut candidate = grandiose_stage0::decode_program(&program.canonical_bytes()).unwrap();
        let entry = candidate.entry;
        let residents = candidate
            .functions
            .get_mut(&entry)
            .unwrap()
            .instructions
            .iter_mut()
            .find_map(|instruction| {
                if let grandiose_stage0::VmInstruction::HostCall {
                    symbol,
                    resident_operations,
                    ..
                } | grandiose_stage0::VmInstruction::HostCallOwned {
                    symbol,
                    resident_operations,
                    ..
                } = instruction
                    && symbol == "inspect"
                {
                    Some(resident_operations)
                } else {
                    None
                }
            })
            .unwrap();
        match changed {
            0 => residents.clear(),
            1 => residents[0].destructor = Some(entry),
            2 => residents.push(residents[0].clone()),
            _ => residents[0].ty = VmType::I64,
        }
        candidate.fingerprint = candidate.computed_fingerprint();
        assert!(
            grandiose_stage0::decode_and_verify_program(&grandiose_stage0::encode_program(
                &candidate
            ))
            .is_err(),
            "mutation {changed}"
        );
    }
}

#[test]
fn native_host_invokes_selected_bytecode_drop_without_an_explicit_callback_argument() {
    for (body, expected_drops, zero_bytes) in [
        (
            r#"
            use std::*;
            struct Widget { value: i64 }
            impl Use<[0, 1]> for Widget {}
            impl Drop for Widget { drop(&mut self) -> { note(); } }
            host interop fn dispose(value: Vec<Widget>) -> i64;
            pub fn main() -> i64 {
                let mut values = Vec<Widget>::with_capacity(4);
                Vec::push(&mut values, Widget { value: 19 });
                Vec::push(&mut values, Widget { value: 23 });
                dispose(values)
            }
        "#,
            2,
            false,
        ),
        (
            r#"
            struct Marker {}
            impl Use<[0, 1]> for Marker {}
            impl Drop for Marker { drop(&mut self) -> { note(); } }
            host interop fn dispose(value: Marker) -> i64;
            pub fn main() -> i64 { dispose(Marker {}) }
        "#,
            1,
            true,
        ),
        (
            r#"
            struct Marker {}
            impl Use<[0, 1]> for Marker {}
            impl Drop for Marker { drop(&mut self) -> { note(); } }
            host interop fn dispose(value: (Marker, Marker)) -> i64;
            pub fn main() -> i64 { dispose((Marker {}, Marker {})) }
        "#,
            2,
            true,
        ),
    ] {
        let program = compile(&format!("host interop fn note() -> ();\n{body}"));
        let drops = Rc::new(Cell::new(0));
        let calls = Rc::new(Cell::new(0));
        let mut imports = VmNativeImports::default();
        for contract in program.native_imports().unwrap() {
            let drops = drops.clone();
            let calls = calls.clone();
            // SAFETY: dispose takes the declared resident once, invokes its
            // bound source destructor once and retains no argument slot or
            // callback. Native code has no element/drop/allocator algorithm.
            unsafe {
                imports
                    .insert(contract.clone(), move |call| {
                        if contract.symbol == "note" {
                            drops.set(drops.get() + 1);
                            return Ok(());
                        }
                        assert_eq!(contract.symbol, "dispose");
                        let selected = contract
                            .residents
                            .iter()
                            .position(|resident| resident.resident.ty == contract.parameters[0])
                            .unwrap();
                        assert!(contract.residents[selected].destruction_code.is_some());
                        let input = call.take_argument(0)?;
                        if !zero_bytes {
                            let vector = &*input.cast::<NativeVec<i64>>();
                            assert_eq!(vector.length, 2);
                            assert_eq!(*vector.pointer + *vector.pointer.add(1), 42);
                        }
                        assert_eq!(drops.get(), 0);
                        let slots = [input.cast_const()];
                        let status = call.with_destructor(selected, |callback| {
                            (callback.invoke)(
                                callback.context,
                                slots.as_ptr(),
                                slots.len(),
                                std::ptr::null_mut(),
                            )
                        })?;
                        assert_eq!(status, VmNativeStatus::Ok);
                        assert_eq!(
                            drops.get(),
                            expected_drops,
                            "all hooks run during native re-entry"
                        );
                        calls.set(calls.get() + 1);
                        let output = 42i64;
                        call.set_result_from((&output as *const i64).cast())
                    })
                    .unwrap();
            }
        }
        let limits = if zero_bytes {
            VmExecutionLimits {
                max_native_bytes: 0,
                max_native_allocation_bytes: 0,
                ..Default::default()
            }
        } else {
            VmExecutionLimits::default()
        };
        assert_eq!(
            unsafe { program.run_i64_with_native(&imports, limits) }.unwrap(),
            42
        );
        assert_eq!(calls.get(), 1);
        assert_eq!(
            drops.get(),
            expected_drops,
            "source caller does not destroy a transferred resident again"
        );
    }
}

#[test]
fn native_return_only_referent_retains_its_uninvoked_destructor_selection() {
    let program = compile(
        r#"
        struct Widget { value: i64 }
        impl Use<[0, 1]> for Widget {}
        impl Drop for Widget { drop(&mut self) -> { note(helper()); } }
        fn helper() -> i64 { 1 }
        host interop fn note(value: i64) -> ();
        host interop fn acquire() -> &'static Widget;
        pub fn main() -> i64 { acquire().value }
    "#,
    );
    let imports = program.native_imports().unwrap();
    let contract = imports
        .iter()
        .find(|import| import.symbol == "acquire")
        .unwrap();
    assert_eq!(contract.residents.len(), 1);
    assert!(contract.residents[0].resident.destructor.is_some());
    assert!(contract.residents[0].destruction_code.is_some());
    assert!(
        imports.iter().any(|import| import.symbol == "note"),
        "exported source operations retain their native capability dependencies"
    );
}

unsafe extern "C" fn update_pair(pointer: *mut NativePair) -> *mut NativePair {
    // SAFETY: the linked contract lends this exact initialized unique resident.
    unsafe {
        (*pointer).first += 1;
        (*pointer).second += 2;
    }
    pointer
}

const PAIR_SOURCE: &str = r#"
    use std::*;
    struct Pair { first: i64, second: i64 }
    host interop fn update<'a>(value: &'a mut Pair) -> &'a mut Pair;
    pub fn main() -> i64 {
        unsafe {
            let pointer = native_home(Pair { first: 19, second: 20 });
            let returned = update(native_unique(pointer));
            let observed = returned.first + returned.second;
            let moved = native_take(pointer);
            handle moved.first + moved.second == observed { true => observed, false => 0 }
        }
    }
"#;

#[test]
fn native_owned_pair_uses_existing_argument_and_caller_result_slots() {
    unsafe extern "C" fn transform(input: *mut NativePair, output: *mut NativePair) {
        let value = unsafe { input.read() };
        unsafe {
            output.write(NativePair {
                first: value.first + 1,
                second: value.first + value.second + 3,
            });
        }
    }
    let program = compile(
        r#"
        struct Pair { first: i64, second: i64 }
        host interop fn transform(value: Pair) -> Pair;
        pub fn main() -> i64 {
            let value = transform(Pair { first: 19, second: 20 });
            // Keep this two-Pair storage bound specific to the ABI slots;
            // source operators borrow scalar homes of their own.
            value.second
        }
    "#,
    );
    let calls = Rc::new(Cell::new(0));
    let observed = calls.clone();
    let mut imports = VmNativeImports::default();
    // SAFETY: both aggregate slots have the exact checked Pair layout. The C
    // callee consumes its argument and initializes the caller slot once; neither
    // pointer survives this call, and no transport aggregate is constructed.
    unsafe {
        imports
            .insert(program.native_imports().unwrap().remove(0), move |call| {
                let input = call.take_argument(0)?.cast::<NativePair>();
                let output = call.result_pointer()?.cast::<NativePair>();
                assert_ne!(input, output);
                assert!(call.take_argument(0).is_err(), "owned input is taken once");
                transform(input, output);
                assert_eq!((*output).first, 20);
                observed.set(observed.get() + 1);
                call.finish_result()
            })
            .unwrap();
    }
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: (2 * size_of::<NativePair>()) as u64,
                    max_native_allocation_bytes: size_of::<NativePair>() as u64,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
    assert_eq!(calls.get(), 1);
}

#[test]
fn native_owned_result_checks_initialization_and_argument_transfer() {
    let program = compile(
        r#"
        struct Flags { ready: Bool }
        host interop fn forward_flags(value: Flags) -> Flags;
        pub fn main() -> i64 {
            let value = forward_flags(Flags { ready: true });
            handle value.ready { true => 42, false => 0 }
        }
    "#,
    );
    for case in 0..4 {
        let mut imports = VmNativeImports::default();
        let contract = program.native_imports().unwrap().remove(0);
        let layout = contract.layout_of(&contract.result).unwrap();
        assert_eq!((layout.size, layout.alignment), (size_of::<u32>(), align_of::<u32>()));
        let VmNativeLayoutShape::Product(fields) = &layout.shape else { panic!("Flags is a record"); };
        let VmNativeLayoutShape::Enum { variants, .. } = &fields[0].layout.shape else { panic!("canonical Bool is a two-variant enum"); };
        assert_eq!(variants.len(), 2);
        // SAFETY: canonical Bool is Result<(), ()>, not C/Rust bool. Initialize
        // its entire u32 discriminant, including in the invalid-tag case.
        // No uninitialized upper bytes or invalid Rust bool are read.
        unsafe {
            imports
                .insert(contract, move |call| {
                    if case != 1 {
                        call.take_argument(0)?;
                    }
                    if case == 2 {
                        return Ok(());
                    }
                    let result = call.result_pointer()?;
                    result.cast::<u32>().write(if case == 0 { 2 } else { 0 });
                    call.finish_result()?;
                    assert!(
                        call.finish_result().is_err(),
                        "result initialization commits once"
                    );
                    assert!(
                        call.result_pointer().is_err(),
                        "committed results cannot be reinitialized"
                    );
                    Ok(())
                })
                .unwrap();
        }
        let outcome =
            unsafe { program.run_i64_with_native(&imports, VmExecutionLimits::default()) };
        match case {
            0 => assert!(matches!(
                outcome,
                Err(VmArtifactError::NativeMemory {
                    message: "invalid native enum discriminant"
                })
            )),
            1 => assert!(matches!(
                outcome,
                Err(VmArtifactError::NativeAbi {
                    message: "native implementation did not take its owned argument"
                })
            )),
            2 => assert!(matches!(
                outcome,
                Err(VmArtifactError::NativeAbi {
                    message: "native implementation did not initialize its result"
                })
            )),
            _ => assert_eq!(outcome.unwrap(), 42),
        }
    }
}

#[test]
fn native_owned_callback_binds_native_caller_storage_and_returns_specialized_value() {
    unsafe extern "C" fn invoke_pair(
        callback: VmNativeCallback,
        input: *mut NativePair,
        output: *mut NativePair,
    ) -> VmNativeStatus {
        let slots = [input.cast_const().cast::<u8>()];
        unsafe { (callback.invoke)(callback.context, slots.as_ptr(), slots.len(), output.cast()) }
    }
    let program = compile(
        r#"
        struct Pair { first: i64, second: i64 }
        host interop fn outer(callback: (Pair) -> Pair) -> i64;
        host interop fn observe(value: &Pair) -> ();
        fn identity<T>(value: T) -> T { value }
        fn amend(value: Pair) -> Pair {
            observe(&value);
            identity(Pair { first: value.first + 1, second: value.second + 2 })
        }
        pub fn main() -> i64 { outer(amend) }
    "#,
    );
    let address = Rc::new(Cell::new(std::ptr::null::<NativePair>()));
    let visits = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in program.native_imports().unwrap() {
        let address = address.clone();
        let visits = visits.clone();
        // SAFETY: native caller owns the Pair slots for the entire synchronous
        // invocation. Bytecode consumes the input and initializes the output.
        unsafe {
            imports
                .insert(contract.clone(), move |call| {
                    if contract.symbol == "observe" {
                        let mut slot = MaybeUninit::<*const NativePair>::uninit();
                        call.write_argument(0, slot.as_mut_ptr().cast())?;
                        assert_eq!(
                            slot.assume_init(),
                            address.get(),
                            "callback borrows the native input, not an adapter copy"
                        );
                        visits.set(visits.get() + 1);
                        call.set_result_from(std::ptr::null())
                    } else {
                        assert_eq!(contract.symbol, "outer");
                        let mut input = NativePair {
                            first: 19,
                            second: 20,
                        };
                        address.set(&input);
                        let mut output = MaybeUninit::<NativePair>::uninit();
                        let status = call.with_callback(0, |callback| {
                            invoke_pair(callback, &mut input, output.as_mut_ptr())
                        })?;
                        assert_eq!(status, VmNativeStatus::Ok);
                        let output = output.assume_init();
                        let result = output.first + output.second;
                        call.set_result_from((&result as *const i64).cast())
                    }
                })
                .unwrap();
        }
    }
    assert_eq!(
        unsafe { program.run_i64_with_native(&imports, VmExecutionLimits::default()) }.unwrap(),
        42
    );
    assert_eq!(visits.get(), 1);
}

#[test]
fn native_owned_zero_sized_return_transfers_one_source_destructor_obligation() {
    let program = compile(
        r#"
        use std::*;
        struct Marker {}
        impl Use<[0, 1]> for Marker {}
        impl Drop for Marker { drop(&mut self) -> { dropped(); } }
        host interop fn dropped() -> ();
        host interop fn forward_marker(value: Marker, callback: (Marker) -> Marker) -> Marker;
        fn identity(value: Marker) -> Marker { value }
        pub fn main() -> i64 { { let value = forward_marker(Marker {}, identity); () }; 42 }
    "#,
    );
    let drops = Rc::new(Cell::new(0));
    let transfers = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in program.native_imports().unwrap() {
        let (drops, transfers) = (drops.clone(), transfers.clone());
        unsafe {
            imports
                .insert(contract.clone(), move |call| {
                    if contract.symbol == "dropped" {
                        drops.set(drops.get() + 1);
                        Ok(())
                    } else {
                        assert_eq!(contract.symbol, "forward_marker");
                        assert_eq!(drops.get(), 0);
                        let input = call.take_argument(0)?;
                        let output = call.result_pointer()?;
                        let slots = [input.cast_const()];
                        let status = call.with_callback(1, |callback| {
                            (callback.invoke)(callback.context, slots.as_ptr(), 1, output)
                        })?;
                        assert_eq!(status, VmNativeStatus::Ok);
                        transfers.set(transfers.get() + 1);
                        // SAFETY: moving this empty Marker transfers a logical owner;
                        // there are no payload bytes to read or write.
                        call.finish_result()
                    }
                })
                .unwrap();
        }
    }
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: 0,
                    max_native_allocation_bytes: 0,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
    assert_eq!(transfers.get(), 1);
    assert_eq!(drops.get(), 1);
}

#[test]
fn effect_payload_native_home_survives_a_delimited_resumption() {
    let program = compile(
        r#"
        struct Pair { first: i64, second: i64 }
        effect Ask { [1, 1] ask(value: Pair) -> Pair; }
        host interop fn update<'a>(value: &'a mut Pair) -> &'a mut Pair;
        fn relay(value: Pair) -> Pair / Ask { Ask::ask(value) }
        fn sum(value: Pair) -> i64 { value.first + value.second }
        pub fn main() -> i64 {
            sum(handle relay(Pair { first: 19, second: 20 }) {
                Ask::ask(payload) with k => {
                    let mut payload = payload;
                    let returned = update(&mut payload);
                    k(*returned)
                }
            })
        }
    "#,
    );
    let mut imports = VmNativeImports::default();
    // SAFETY: a live source Pair is borrowed for this call only; the returned
    // pointer names the same resident, and no native pointer survives the call.
    unsafe {
        imports
            .insert(program.native_imports().unwrap().remove(0), |call| {
                let mut argument = MaybeUninit::<*mut NativePair>::uninit();
                call.write_argument(0, argument.as_mut_ptr().cast())?;
                let pointer = argument.assume_init();
                let returned = update_pair(pointer);
                assert_eq!(returned, pointer);
                call.set_result_from((&returned as *const *mut NativePair).cast())
            })
            .unwrap();
    }
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: size_of::<NativePair>() as u64,
                    max_native_allocation_bytes: size_of::<NativePair>() as u64,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
}

#[test]
fn addressable_reference_local_keeps_the_original_referent() {
    let program = compile(
        r#"
        struct Pair { first: i64, second: i64 }
        host interop fn inspect(value: & &Pair) -> i64;
        fn first(value: &Pair) -> i64 { value.first }
        pub fn main() -> i64 {
            let pair = Pair { first: 19, second: 23 };
            let reference = &pair;
            let second = inspect(&reference);
            first(& *reference) + second
        }
    "#,
    );
    let calls = Rc::new(Cell::new(0));
    let observed = calls.clone();
    let mut imports = VmNativeImports::default();
    // SAFETY: both pointer layers describe initialized source-owned storage;
    // the host only reads it during this call and retains neither pointer.
    unsafe {
        imports
            .insert(program.native_imports().unwrap().remove(0), move |call| {
                let mut argument = MaybeUninit::<*const *const NativePair>::uninit();
                call.write_argument(0, argument.as_mut_ptr().cast())?;
                let pair = *argument.assume_init();
                assert_eq!((*pair).first, 19);
                observed.set(observed.get() + 1);
                call.set_result_from((&(*pair).second as *const i64).cast())
            })
            .unwrap();
    }
    let bytes = size_of::<NativePair>() + size_of::<*const NativePair>();
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: bytes as u64,
                    max_native_allocation_bytes: size_of::<NativePair>() as u64,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
    assert_eq!(calls.get(), 1);
}

#[test]
fn ordinary_source_local_has_one_native_home_before_the_call() {
    let program = compile(
        r#"
        struct Pair { first: i64, second: i64 }
        host interop fn update<'a>(value: &'a mut Pair) -> &'a mut Pair;
        pub fn main() -> i64 {
            let mut pair = Pair { first: 19, second: 20 };
            let returned = update(&mut pair);
            let observed = returned.first + returned.second;
            handle observed == 42 { true => pair.first + pair.second, false => 0 }
        }
    "#,
    );
    let contract = program.native_imports().unwrap().remove(0);
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(contract, |call| {
                let mut argument = MaybeUninit::<*mut NativePair>::uninit();
                call.write_argument(0, argument.as_mut_ptr().cast())?;
                let pointer = argument.assume_init();
                let returned = update_pair(pointer);
                assert_eq!(returned, pointer);
                call.set_result_from((&returned as *const *mut NativePair).cast())
            })
            .unwrap();
    }
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: size_of::<NativePair>() as u64,
                    max_native_allocation_bytes: size_of::<NativePair>() as u64,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
}

#[test]
fn native_call_and_borrowed_return_use_the_same_source_resident() {
    let program = compile(PAIR_SOURCE);
    let [contract] = program.native_imports().unwrap().try_into().unwrap();
    let VmType::Reference {
        referent,
        unique: true,
    } = &contract.parameters[0]
    else {
        panic!("unique Pair ABI");
    };
    let layout = contract.layout_of(referent).unwrap();
    assert_eq!(
        (layout.size, layout.alignment),
        (size_of::<NativePair>(), align_of::<NativePair>())
    );
    let VmNativeLayoutShape::Product(fields) = layout.shape else {
        panic!("Pair layout");
    };
    assert_eq!(
        fields.iter().map(|field| field.offset).collect::<Vec<_>>(),
        [
            offset_of!(NativePair, first),
            offset_of!(NativePair, second)
        ]
    );
    let calls = Rc::new(Cell::new(0));
    let observed = calls.clone();
    let mut imports = VmNativeImports::default();
    // SAFETY: exact concrete Pair layout checked above; no pointer is retained,
    // the returned borrow aliases only its input, and the C function cannot unwind.
    unsafe {
        imports
            .insert(contract, move |call| {
                let mut argument = MaybeUninit::<*mut NativePair>::uninit();
                call.write_argument(0, argument.as_mut_ptr().cast())?;
                let original = argument.assume_init();
                let returned = update_pair(original);
                assert_eq!(returned, original);
                observed.set(observed.get() + 1);
                call.set_result_from((&returned as *const *mut NativePair).cast())
            })
            .unwrap();
    }
    let limits = VmExecutionLimits {
        max_native_bytes: size_of::<NativePair>() as u64,
        max_native_allocation_bytes: size_of::<NativePair>() as u64,
        ..Default::default()
    };
    // SAFETY: freshly compiled source allocates/releases the exact Pair home,
    // and all native loans end before the source moves and releases it.
    assert_eq!(
        unsafe { program.run_i64_with_native(&imports, limits) }.unwrap(),
        42
    );
    assert_eq!(calls.get(), 1);
    assert!(matches!(
        program.run_i64(),
        Err(VmArtifactError::UnsafeExecutionRequiresUnsafeApi)
    ));
}

#[test]
fn native_return_only_referents_retain_transitive_and_specialized_layouts() {
    #[repr(C)]
    struct NativeView {
        pair: &'static NativePair,
    }
    static PAIR: NativePair = NativePair {
        first: 19,
        second: 23,
    };
    static VIEW: NativeView = NativeView { pair: &PAIR };
    for source in [
        r#"
            struct Pair { first: i64, second: i64 }
            struct View { pair: &'static Pair }
            host interop fn acquire() -> &'static View;
            pub fn main() -> i64 { let view = acquire(); view.pair.first + view.pair.second }
        "#,
        r#"
            struct Pair<T> { first: T, second: T }
            struct View<T> { pair: &'static Pair<T> }
            host interop fn acquire<T>() -> &'static View<T>;
            fn obtain<T>() -> &'static View<T> { acquire<T>() }
            pub fn main() -> i64 { let view = obtain<i64>(); view.pair.first + view.pair.second }
        "#,
    ] {
        let program = compile(source);
        let contract = program.native_imports().unwrap().remove(0);
        assert_eq!(
            contract.nominals.len(),
            2,
            "both referents are required despite no source-owned value of either type"
        );
        let mut imports = VmNativeImports::default();
        // SAFETY: these immutable native residents genuinely live for the
        // source contract's static lifetime; their repr(C) layouts agree.
        unsafe {
            imports
                .insert(contract, |call| {
                    let view = &VIEW as *const NativeView;
                    call.set_result_from((&view as *const *const NativeView).cast())
                })
                .unwrap();
        }
        assert_eq!(
            unsafe {
                program.run_i64_with_native(
                    &imports,
                    VmExecutionLimits {
                        max_native_bytes: 0,
                        max_native_allocation_bytes: 0,
                        ..Default::default()
                    },
                )
            }
            .unwrap(),
            42
        );
    }
}

#[test]
fn native_layout_contracts_terminate_pointer_cycles_and_reject_expanding_generic_cycles() {
    #[repr(C)]
    struct NativeNode {
        next: *const NativeNode,
        value: i64,
    }
    let recursive = compile(
        r#"
        struct Node { next: *const Node, value: i64 }
        host interop fn acquire() -> &'static Node;
        pub fn main() -> i64 { acquire().value }
    "#,
    );
    let contract = recursive.native_imports().unwrap().remove(0);
    assert_eq!(contract.nominals.len(), 1);
    let VmType::Reference { referent, .. } = &contract.result else {
        panic!("native Node reference");
    };
    assert_eq!(
        contract.layout_of(referent).unwrap().size,
        size_of::<NativeNode>()
    );

    let expanding = r#"
        struct Node<T> { next: *const Node<(T,)>, value: T }
        host interop fn acquire() -> &'static Node<i64>;
        pub fn main() -> i64 { acquire().value }
    "#;
    let failure = StageZeroCompiler::new()
        .compile(request(expanding))
        .unwrap_err();
    assert!(
        failure
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G7032"
                && diagnostic.message == "concrete nominal layout expansion exceeds its finite representation budget"),
        "{failure:#?}"
    );
}

#[test]
fn native_linking_rejects_missing_or_incompatible_bindings_before_execution() {
    let program = compile(PAIR_SOURCE);
    let contract = program.native_imports().unwrap().remove(0);
    let empty = VmNativeImports::default();
    assert!(matches!(
        unsafe { program.run_i64_with_native(&empty, Default::default()) },
        Err(VmArtifactError::HostCallRequiresAuthority { .. })
    ));
    for changed in 0..4 {
        let mut wrong = contract.clone();
        match changed {
            0 => wrong.source_contract = Digest::of_bytes(b"different-source-loan-contract"),
            1 => {
                wrong.parameters[0] = VmType::RawPointer {
                    mutability: grandiose_stage0::PointerMutability::Mut,
                    pointee: Box::new(VmType::I64),
                }
            }
            2 => wrong.nominals[0].variants[0].swap(0, 1),
            _ => wrong.result = VmType::I64,
        }
        // Same-typed Pair fields make swapping ineffective; alter a field type
        // for the layout-mismatch case while retaining nominal identity.
        if changed == 2 {
            wrong.nominals[0].variants[0][0] = VmType::U64;
        }
        let mut imports = VmNativeImports::default();
        unsafe {
            imports
                .insert(wrong, |_| {
                    panic!("link mismatch must precede native execution")
                })
                .unwrap();
        }
        assert!(
            matches!(
                unsafe { program.run_i64_with_native(&imports, Default::default()) },
                Err(VmArtifactError::NativeAbi { .. })
            ),
            "case {changed}"
        );
    }
}

unsafe extern "C" fn invoke_i64(
    callback: VmNativeCallback,
    value: i64,
    output: *mut i64,
) -> VmNativeStatus {
    let arguments = [(&value as *const i64).cast::<u8>()];
    // SAFETY: the live callback's declared ABI is (i64)->i64. Both slots have
    // exact native layout; the callback is invoked once and never retained.
    unsafe {
        (callback.invoke)(
            callback.context,
            arguments.as_ptr(),
            arguments.len(),
            output.cast(),
        )
    }
}

#[test]
fn native_target_duplicate_and_result_contracts_are_checked() {
    let program = compile("host interop fn answer() -> i64; pub fn main() -> i64 { answer() }");
    let contract = program.native_imports().unwrap().remove(0);
    for changed in 0..6 {
        let mut wrong = contract.clone();
        match changed {
            0 => wrong.abi.generation += 1,
            1 => wrong.abi.architecture.push_str("-other"),
            2 => wrong.abi.operating_system.push_str("-other"),
            3 => wrong.abi.pointer_bits += 1,
            4 => wrong.abi.little_endian = !wrong.abi.little_endian,
            _ => wrong.abi.allocation_domain.push_str("-foreign"),
        }
        let mut imports = VmNativeImports::default();
        assert!(matches!(
            unsafe { imports.insert(wrong, |_| unreachable!()) },
            Err(VmArtifactError::NativeAbi { .. })
        ));
    }
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(contract.clone(), |call| {
                let answer = 42i64;
                call.set_result_from((&answer as *const i64).cast())
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe { imports.insert(contract.clone(), |_| unreachable!()) },
        Err(VmArtifactError::NativeAbi { .. })
    ));
    assert_eq!(
        unsafe { program.run_i64_with_native(&imports, Default::default()) }.unwrap(),
        42,
        "duplicate registration did not replace the binding"
    );
    let mut missing = VmNativeImports::default();
    unsafe {
        missing.insert(contract.clone(), |_| Ok(())).unwrap();
    }
    assert!(matches!(
        unsafe { program.run_i64_with_native(&missing, Default::default()) },
        Err(VmArtifactError::NativeAbi {
            message: "native implementation did not initialize its result"
        })
    ));
    let mut twice = VmNativeImports::default();
    unsafe {
        twice
            .insert(contract, |call| {
                let answer = 42i64;
                call.set_result_from((&answer as *const i64).cast())?;
                call.set_result_from((&answer as *const i64).cast())
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe { program.run_i64_with_native(&twice, Default::default()) },
        Err(VmArtifactError::NativeAbi {
            message: "native result was already initialized"
        })
    ));
}

#[test]
fn callback_slot_preflight_rejects_bad_tables_values_and_results() {
    let program = compile(
        r#"
        host interop fn outer(callback: (i64) -> i64) -> i64;
        fn identity(value: i64) -> i64 { value }
        pub fn main() -> i64 { outer(identity) }
    "#,
    );
    for changed in 0..6 {
        let mut imports = VmNativeImports::default();
        unsafe {
            imports
                .insert(program.native_imports().unwrap().remove(0), move |call| {
                    let value = 42i64;
                    let mut output = MaybeUninit::<i64>::uninit();
                    let mut slots = [(&value as *const i64).cast::<u8>()];
                    if changed == 3 {
                        slots[0] = std::ptr::null();
                    }
                    if changed == 4 {
                        slots[0] = slots[0].wrapping_add(1);
                    }
                    let table = match changed {
                        1 => std::ptr::null(),
                        2 => slots.as_ptr().cast::<u8>().wrapping_add(1).cast(),
                        _ => slots.as_ptr(),
                    };
                    let count = if changed == 0 { 0 } else { 1 };
                    let result = if changed == 5 {
                        std::ptr::null_mut()
                    } else {
                        output.as_mut_ptr().cast()
                    };
                    // Each deliberately malformed slot is rejected before it is read;
                    // no dangling pointer is dereferenced or failed result consumed.
                    let ignored = call.with_callback(0, |callback| {
                        assert_eq!(
                            (callback.invoke)(callback.context, table, count, result),
                            VmNativeStatus::Failed
                        );
                    });
                    assert!(ignored.is_err());
                    call.set_result_from((&value as *const i64).cast())
                })
                .unwrap();
        }
        assert!(
            matches!(
                unsafe { program.run_i64_with_native(&imports, Default::default()) },
                Err(VmArtifactError::NativeAbi { .. })
            ),
            "case {changed}"
        );
    }
}

#[test]
fn native_callback_reenters_bytecode_with_captures_and_nested_host_authority() {
    let program = compile(
        r#"
        use std::*;
        host interop fn outer(callback: (i64) -> i64, value: i64) -> i64;
        host interop fn inner(value: i64) -> i64;
        pub fn main() -> i64 {
            let increment = 1;
            let callback = (value: i64) -> i64 { inner(value) + increment };
            outer(callback, 40)
        }
    "#,
    );
    let order = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in program.native_imports().unwrap() {
        let order = order.clone();
        // SAFETY: each adapter implements the inspected scalar/callback ABI,
        // invokes the callback once, retains no context and permits re-entry.
        unsafe {
            if contract.symbol == "inner" {
                imports
                    .insert(contract, move |call| {
                        assert_eq!(order.get(), 1);
                        order.set(2);
                        let mut input = MaybeUninit::<i64>::uninit();
                        call.write_argument(0, input.as_mut_ptr().cast())?;
                        let result = input.assume_init() + 1;
                        call.set_result_from((&result as *const i64).cast())
                    })
                    .unwrap();
            } else {
                assert_eq!(contract.symbol, "outer");
                imports
                    .insert(contract, move |call| {
                        assert_eq!(order.get(), 0);
                        order.set(1);
                        let mut input = MaybeUninit::<i64>::uninit();
                        call.write_argument(1, input.as_mut_ptr().cast())?;
                        let mut output = MaybeUninit::<i64>::uninit();
                        let status = call.with_callback(0, |callback| {
                            invoke_i64(callback, input.assume_init(), output.as_mut_ptr())
                        })?;
                        assert_eq!(status, VmNativeStatus::Ok);
                        assert_eq!(order.get(), 2);
                        order.set(3);
                        call.set_result_from(output.as_ptr().cast())
                    })
                    .unwrap();
            }
        }
    }
    // SAFETY: the local closure captures one immutable scalar. No native
    // storage is needed by either direction of this scalar callback fixture.
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: 0,
                    max_native_allocation_bytes: 0,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
    assert_eq!(order.get(), 3);
}

#[repr(C)]
struct NativeWidget {
    value: i64,
    counter: *mut i64,
}
#[repr(C)]
struct NativeVec<T> {
    pointer: *mut T,
    length: usize,
    capacity: usize,
}

unsafe extern "C" fn update_vector(
    owner: *mut NativeVec<NativeWidget>,
    callback: VmNativeCallback,
    initial: usize,
) -> *mut NativeVec<NativeWidget> {
    unsafe {
        let backing = (*owner).pointer;
        let capacity = (*owner).capacity;
        assert_eq!((*owner).length, initial);
        assert!(capacity >= initial);
        (*backing).value += 1;
        let arguments = [(&owner as *const *mut NativeVec<NativeWidget>).cast::<u8>()];
        let mut returned = MaybeUninit::<*mut NativeVec<NativeWidget>>::uninit();
        if (callback.invoke)(
            callback.context,
            arguments.as_ptr(),
            1,
            returned.as_mut_ptr().cast(),
        ) != VmNativeStatus::Ok
        {
            return std::ptr::null_mut();
        }
        let returned = returned.assume_init();
        assert_eq!(returned, owner);
        if initial < capacity {
            assert_eq!((*returned).pointer, backing);
        } else {
            assert!((*returned).capacity > capacity);
        }
        assert_eq!((*returned).length, initial + 1);
        // A source growth callback may legitimately relocate the backing.
        // Reload the same header, never use a pointer invalidated by growth.
        let current = (*returned).pointer;
        assert_eq!((*current).value, 20);
        assert_eq!((*current.add(initial)).value, 20);
        returned
    }
}

#[test]
fn native_owned_vec_roundtrip_grows_and_drops_only_in_bytecode() {
    let program = compile(
        r#"
        use std::*;
        struct Widget { value: i64, counter: *mut i64 }
        impl Use<[0, 1]> for Widget {}
        impl Drop for Widget { drop(&mut self) -> {
            unsafe { let count = native_unique(self.counter); *count = *count + 1; }
        } }
        host interop fn roundtrip(value: Vec<Widget>, callback: (Vec<Widget>) -> Vec<Widget>) -> Vec<Widget>;
        host interop fn observe(value: &Vec<Widget>) -> ();
        fn append(value: Vec<Widget>) -> Vec<Widget> {
            observe(&value);
            let mut value = value;
            let counter = Vec::get_unchecked(&value, 0).counter;
            Vec::push(&mut value, Widget { value: 23, counter: counter });
            value
        }
        pub fn main() -> i64 {
            unsafe {
                let counter = native_home(as<i64>(0));
                let total = {
                    let mut value = Vec<Widget>::with_capacity(4);
                    Vec::push(&mut value, Widget { value: 19, counter: counter });
                    Vec::push(&mut value, Widget { value: 0, counter: counter });
                    Vec::push(&mut value, Widget { value: 0, counter: counter });
                    Vec::push(&mut value, Widget { value: 0, counter: counter });
                    let returned = roundtrip(value, append);
                    Vec::get_unchecked(&returned, 0).value + Vec::get_unchecked(&returned, 4).value
                };
                handle native_take(counter) == 5 { true => total, false => 0 }
            }
        }
    "#,
    );
    let address = Rc::new(Cell::new(std::ptr::null::<NativeVec<NativeWidget>>()));
    let backing = Rc::new(Cell::new(std::ptr::null_mut::<NativeWidget>()));
    let visits = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in program.native_imports().unwrap() {
        let address = address.clone();
        let backing = backing.clone();
        let visits = visits.clone();
        // SAFETY: header layout is Glorious's declared concrete ABI, not Rust
        // Vec. Native code forwards ownership once and never grows, drops,
        // frees or reconstructs the collection or any element.
        unsafe {
            imports
                .insert(contract.clone(), move |call| {
                    if contract.symbol == "observe" {
                        let mut slot = MaybeUninit::<*const NativeVec<NativeWidget>>::uninit();
                        call.write_argument(0, slot.as_mut_ptr().cast())?;
                        let observed = slot.assume_init();
                        assert_eq!(observed, address.get());
                        assert_eq!((*observed).pointer, backing.get());
                        visits.set(visits.get() + 1);
                        call.set_result_from(std::ptr::null())
                    } else {
                        assert_eq!(contract.symbol, "roundtrip");
                        let input = call.take_argument(0)?.cast::<NativeVec<NativeWidget>>();
                        let output = call.result_pointer()?.cast::<NativeVec<NativeWidget>>();
                        address.set(input);
                        backing.set((*input).pointer);
                        assert_eq!((*input).length, 4);
                        assert_eq!((*input).capacity, 4);
                        let slots = [input.cast_const().cast::<u8>()];
                        let status = call.with_callback(1, |callback| {
                            (callback.invoke)(callback.context, slots.as_ptr(), 1, output.cast())
                        })?;
                        assert_eq!(status, VmNativeStatus::Ok);
                        assert_eq!((*output).length, 5);
                        assert!((*output).capacity >= 5);
                        // Growth may resize in place or relocate. No native code
                        // retains a view into the old allocation across that operation.
                        assert_eq!(
                            *(*(*output).pointer).counter,
                            0,
                            "neither engine dropped a live element"
                        );
                        call.finish_result()
                    }
                })
                .unwrap();
        }
    }
    assert_eq!(
        unsafe { program.run_i64_with_native(&imports, VmExecutionLimits::default()) }.unwrap(),
        42
    );
    assert_eq!(visits.get(), 1);
}

#[test]
fn native_vec_callback_mutates_source_specialization_and_runs_resident_drop() {
    for initial in [1usize, 4] {
        let program = compile(&r#"
        use std::*;
        struct Widget { value: i64, counter: *mut i64 }
        impl Use<[0, 1]> for Widget {}
        impl Drop for Widget { drop(&mut self) -> {
            unsafe { let counter = native_unique(self.counter); *counter = *counter + 1; }
        } }
        host interop fn update<'a>(value: &'a mut Vec<Widget>, callback: for<'b> (&'b mut Vec<Widget>) -> &'b mut Vec<Widget>) -> &'a mut Vec<Widget>;
        fn append<'a>(value: &'a mut Vec<Widget>) -> &'a mut Vec<Widget> {
            let counter = Vec::get_unchecked(& *value, 0).counter;
            handle Vec::get_mut(&mut *value, 0) { Result::Ok(first) => { (*first).value = first.value + 1; }, Result::Err(_) => () };
            Vec::push(&mut *value, Widget { value: 20, counter: counter });
            value
        }
        fn fill(value: &mut Vec<Widget>, counter: *mut i64, remaining: usize) -> () {
            handle remaining {
                0 => (),
                _ => { Vec::push(&mut *value, Widget { value: 0, counter: counter }); fill(value, counter, remaining - 1) },
            }
        }
        pub fn main() -> i64 {
            unsafe {
                let counter = native_home(as<i64>(0));
                let total = {
                    let mut vector = Vec<Widget>::with_capacity(4);
                    Vec::push(&mut vector, Widget { value: 18, counter: counter });
                    fill(&mut vector, counter, @EXTRA@);
                    let returned = update(&mut vector, append);
                    Vec::get_unchecked(& *returned, 0).value + Vec::get_unchecked(& *returned, Vec::len(& *returned) - 1).value
                };
                handle native_take(counter) == @DROPS@ { true => total + 2, false => 0 }
            }
        }
    "#.replace("@EXTRA@", &(initial - 1).to_string()).replace("@DROPS@", &(initial + 1).to_string()));
        let contract = program.native_imports().unwrap().remove(0);
        let VmType::Reference { referent, .. } = &contract.parameters[0] else {
            panic!("Vec reference");
        };
        let vector = contract.layout_of(referent).unwrap();
        assert_eq!(
            (vector.size, vector.alignment),
            (
                size_of::<NativeVec<NativeWidget>>(),
                align_of::<NativeVec<NativeWidget>>()
            )
        );
        let VmNativeLayoutShape::Product(fields) = vector.shape else {
            panic!("Vec product");
        };
        assert_eq!(
            fields
                .iter()
                .take(3)
                .map(|field| field.offset)
                .collect::<Vec<_>>(),
            [
                offset_of!(NativeVec<NativeWidget>, pointer),
                offset_of!(NativeVec<NativeWidget>, length),
                offset_of!(NativeVec<NativeWidget>, capacity)
            ]
        );
        let VmType::RawPointer { pointee, .. } = &fields[0].layout.ty else {
            panic!("Vec data pointer");
        };
        let widget = contract.layout_of(pointee).unwrap();
        assert_eq!(
            (widget.size, widget.alignment),
            (size_of::<NativeWidget>(), align_of::<NativeWidget>())
        );
        let mut imports = VmNativeImports::default();
        // SAFETY: exact Vec<Widget> and Widget layouts were checked, including
        // declaration identities in the linked contract. Neither C nor the bridge
        // grows/drops elements; the supplied ordinary source callback does that.
        unsafe {
            imports
                .insert(contract, move |call| {
                    let mut argument = MaybeUninit::<*mut NativeVec<NativeWidget>>::uninit();
                    call.write_argument(0, argument.as_mut_ptr().cast())?;
                    let returned = call.with_callback(1, |callback| {
                        update_vector(argument.assume_init(), callback, initial)
                    })?;
                    call.set_result_from((&returned as *const *mut NativeVec<NativeWidget>).cast())
                })
                .unwrap();
        }
        let capacity = if initial == 1 { 4 } else { 8 };
        let native_bytes = size_of::<i64>()
            + 2 * size_of::<NativeVec<NativeWidget>>()
            + capacity * size_of::<NativeWidget>()
            + size_of::<NativeWidget>();
        // Source cleanup moves the header and each destroyed Widget into an
        // addressable glue parameter. These frame homes share the raw-memory
        // budget; the callback itself still borrows the original header.
        // SAFETY: source cleanup destroys all Widgets before releasing the counter.
        assert_eq!(
            unsafe {
                program.run_i64_with_native(
                    &imports,
                    VmExecutionLimits {
                        max_native_bytes: native_bytes as u64,
                        max_native_allocation_bytes: (capacity * size_of::<NativeWidget>()) as u64,
                        ..Default::default()
                    },
                )
            }
            .unwrap(),
            42
        );
    }
}

#[test]
fn source_lifetime_changes_invalidate_otherwise_identical_native_abis() {
    let ordinary = compile(PAIR_SOURCE);
    let changed = compile(&PAIR_SOURCE.replace("-> &'a mut Pair;", "-> &'static mut Pair;"));
    let before = ordinary.native_imports().unwrap().remove(0);
    let after = changed.native_imports().unwrap().remove(0);
    assert_eq!(before.parameters, after.parameters);
    assert_eq!(before.result, after.result);
    assert_eq!(before.nominals, after.nominals);
    assert_ne!(before.source_contract, after.source_contract);
    assert_ne!(ordinary.fingerprint(), changed.fingerprint());
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(before, |_| panic!("stale loan contract must not execute"))
            .unwrap();
    }
    assert!(matches!(
        unsafe { changed.run_i64_with_native(&imports, Default::default()) },
        Err(VmArtifactError::NativeAbi { .. })
    ));
}

#[test]
fn nominal_field_lifetime_changes_invalidate_same_layout_native_bindings() {
    let source = r#"
        use std::*;
        struct View<'a, 'b> { first: &'a i64, second: &'b i64 }
        host interop fn inspect<'a, 'b>(value: &View<'a, 'b>) -> i64;
        pub fn main() -> i64 {
            unsafe {
                let first = native_home(as<i64>(19));
                let second = native_home(as<i64>(23));
                let view = native_home(View { first: native_shared(first), second: native_shared(second) });
                let answer = inspect(native_shared(view));
                let old_view = native_take(view);
                let old_first = native_take(first);
                let old_second = native_take(second);
                answer
            }
        }
    "#;
    let original = compile(source);
    let changed = compile(&source.replace(
        "first: &'a i64, second: &'b i64",
        "first: &'b i64, second: &'a i64",
    ));
    let before = original.native_imports().unwrap().remove(0);
    let after = changed.native_imports().unwrap().remove(0);
    assert_eq!(
        before.source_contract, after.source_contract,
        "callable declaration is unchanged"
    );
    assert_eq!(before.parameters, after.parameters);
    assert_eq!(before.result, after.result);
    assert_eq!(before.nominals.len(), 1);
    assert_eq!(before.nominals[0].definition, after.nominals[0].definition);
    assert_eq!(before.nominals[0].arguments, after.nominals[0].arguments);
    assert_eq!(before.nominals[0].variants, after.nominals[0].variants);
    assert_ne!(
        before.nominals[0].source_contract,
        after.nominals[0].source_contract
    );
    assert_ne!(original.fingerprint(), changed.fingerprint());
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(before, |_| {
                panic!("stale field loan contract must not execute")
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe { changed.run_i64_with_native(&imports, Default::default()) },
        Err(VmArtifactError::NativeAbi { .. })
    ));
}

#[test]
fn callback_failures_share_vm_limits_and_cannot_be_swallowed_by_native_code() {
    let program = compile(
        r#"
        use std::*;
        host interop fn outer(callback: (i64) -> i64, value: i64) -> i64;
        fn forever(value: i64) -> i64 { forever(value) }
        pub fn main() -> i64 { outer(forever, 0) }
    "#,
    );
    let calls = Rc::new(Cell::new(0));
    let observed = calls.clone();
    let mut imports = VmNativeImports::default();
    // SAFETY: all scalar slots and the callback lifetime are valid. Deliberate
    // failure swallowing tests the bridge's sticky execution-error contract.
    unsafe {
        imports
            .insert(program.native_imports().unwrap().remove(0), move |call| {
                observed.set(observed.get() + 1);
                let mut output = MaybeUninit::<i64>::uninit();
                let ignored = call.with_callback(0, |callback| {
                    let status = invoke_i64(callback, 0, output.as_mut_ptr());
                    assert_eq!(status, VmNativeStatus::Failed);
                });
                assert!(ignored.is_err());
                let fabricated_success = 42i64;
                call.set_result_from((&fabricated_success as *const i64).cast())
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_call_depth: 32,
                    ..Default::default()
                },
            )
        },
        Err(VmArtifactError::CallDepthLimit { limit: 32 })
    ));
    assert!(matches!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_call_depth: 1000,
                    max_instructions: 200,
                    ..Default::default()
                },
            )
        },
        Err(VmArtifactError::InstructionLimit { limit: 200 })
    ));
    assert_eq!(
        calls.get(),
        2,
        "both failures occur inside the callback, not before native dispatch"
    );
}

#[test]
fn callbacks_share_native_allocation_domain_and_bound_native_stack_reentry() {
    let allocation = compile(
        r#"
        use std::*;
        host interop fn outer(callback: (i64) -> i64, value: i64) -> i64;
        fn allocate(value: i64) -> i64 { unsafe { let pointer = native_home(value); native_take(pointer) } }
        pub fn main() -> i64 {
            unsafe {
                let resident = native_home(as<i64>(42));
                let answer = outer(allocate, 0);
                native_take(resident) + answer
            }
        }
    "#,
    );
    let recursion = compile(
        r#"
        host interop fn outer(callback: (i64) -> i64, value: i64) -> i64;
        fn recur(value: i64) -> i64 { outer(recur, value) }
        pub fn main() -> i64 { outer(recur, 0) }
    "#,
    );
    for (index, program) in [&allocation, &recursion].into_iter().enumerate() {
        let calls = Rc::new(Cell::new(0));
        let observed = calls.clone();
        let mut imports = VmNativeImports::default();
        unsafe {
            imports
                .insert(program.native_imports().unwrap().remove(0), move |call| {
                    observed.set(observed.get() + 1);
                    let mut output = MaybeUninit::<i64>::uninit();
                    call.with_callback(0, |callback| invoke_i64(callback, 0, output.as_mut_ptr()))?;
                    call.set_result_from(output.as_ptr().cast())
                })
                .unwrap();
        }
        let limits = VmExecutionLimits {
            max_native_bytes: 8,
            max_native_allocation_bytes: 8,
            max_call_depth: 1000,
            ..Default::default()
        };
        let failure = unsafe { program.run_i64_with_native(&imports, limits) }.unwrap_err();
        if index == 0 {
            assert_eq!(
                failure,
                VmArtifactError::NativeMemory {
                    message: "native memory budget exceeded"
                }
            );
            assert_eq!(
                calls.get(),
                1,
                "the allocation failure occurs after native re-entry"
            );
        } else {
            assert_eq!(
                failure,
                VmArtifactError::NativeAbi {
                    message: "native callback re-entry limit"
                }
            );
            assert_eq!(
                calls.get(),
                33,
                "native stack limit is separate from VM frame depth"
            );
        }
    }
}

#[test]
fn native_boundary_rejects_private_callable_results_and_outward_callback_effects() {
    let aggregate = compile(
        r#"
        host interop fn acquire() -> () -> i64;
        pub fn main() -> i64 { let callback = acquire(); callback() }
    "#,
    );
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(aggregate.native_imports().unwrap().remove(0), |_| {
                panic!("private callable result must fail linking")
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe { aggregate.run_i64_with_native(&imports, Default::default()) },
        Err(VmArtifactError::NativeAbi {
            message: "native private array/callable layout is not supported"
        })
    ));

    let effects = compile(
        r#"
        use std::*;
        effect Trace { note(value: i64) -> i64; }
        host interop fn outer(callback: (i64) -> i64 / Trace, value: i64) -> i64;
        fn callback(value: i64) -> i64 / Trace { Trace::note(value) }
        pub fn main() -> i64 { outer(callback, 42) }
    "#,
    );
    let mut imports = VmNativeImports::default();
    unsafe {
        imports
            .insert(effects.native_imports().unwrap().remove(0), |_| {
                panic!("outward effects must fail linking")
            })
            .unwrap();
    }
    assert!(matches!(
        unsafe { effects.run_i64_with_native(&imports, Default::default()) },
        Err(VmArtifactError::NativeAbi {
            message: "native callback cannot carry outward effects across this boundary"
        })
    ));
}

#[test]
fn unsafe_created_reference_loans_survive_forwarding_and_reject_overlapping_reborrows() {
    for body in [
        "let parent = native_unique(pointer); let child = &mut *parent; *child = *child + 2; native_take(pointer)",
        "let parent = { native_unique(pointer) }; let child = &mut *parent; *child = *child + 2; native_take(pointer)",
        "let parent = forward(native_unique(pointer)); let child = &mut *parent; *child = *child + 2; native_take(pointer)",
    ] {
        let program = compile(&format!(
            r#"
            use std::*;
            fn forward<'a>(value: &'a mut i64) -> &'a mut i64 {{ value }}
            pub fn main() -> i64 {{ unsafe {{ let pointer = native_home(as<i64>(40)); {body} }} }}
        "#
        ));
        assert_eq!(
            unsafe { program.run_i64_with_native(&VmNativeImports::default(), Default::default()) }
                .unwrap(),
            42
        );
    }
    for body in [
        "let parent = native_unique(pointer); let child = &mut *parent; *parent = 1; *child = 42; native_take(pointer)",
        "let parent = native_shared(pointer); let child = &mut *parent; *child = 42; native_take(pointer)",
        "let parent = native_unique(pointer); let child = &mut *parent; let other = &mut *parent; *child = 1; *other = 42; native_take(pointer)",
    ] {
        let source = format!(
            "use std::*; pub fn main() -> i64 {{ unsafe {{ let pointer = native_home(as<i64>(40)); {body} }} }}"
        );
        let error = StageZeroCompiler::new()
            .compile(request(&source))
            .unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code.starts_with("G50") || diagnostic.code == "G4141"),
            "{error:#?}"
        );
    }
}

unsafe extern "C" fn clear_vector(
    owner: *mut NativeVec<()>,
    callback: VmNativeCallback,
) -> VmNativeStatus {
    let arguments = [(&owner as *const *mut NativeVec<()>).cast::<u8>()];
    // SAFETY: a unit result has no resident bytes. The exact callback lends
    // the existing Vec header and invokes source clear/drop; no native
    // element algorithm or native-specialized destructor is supplied.
    unsafe {
        (callback.invoke)(
            callback.context,
            arguments.as_ptr(),
            1,
            std::ptr::null_mut(),
        )
    }
}

#[test]
fn native_callback_runs_zero_sized_resident_destructors_as_bytecode() {
    let program = compile(
        r#"
        use std::*;
        struct Marker {}
        impl Use<[0, 1]> for Marker {}
        host interop fn dropped() -> ();
        impl Drop for Marker { drop(&mut self) -> { dropped(); } }
        host interop fn clear_native(value: &mut Vec<Marker>, callback: (&mut Vec<Marker>) -> ()) -> i64;
        fn clear(value: &mut Vec<Marker>) -> () { Vec::clear(value) }
        pub fn main() -> i64 {
            unsafe {
                let mut vector = Vec<Marker>::new();
                Vec::push(&mut vector, Marker {}); Vec::push(&mut vector, Marker {}); Vec::push(&mut vector, Marker {});
                clear_native(&mut vector, clear)
            }
        }
    "#,
    );
    let drops = Rc::new(Cell::new(0));
    let mut imports = VmNativeImports::default();
    for contract in program.native_imports().unwrap() {
        let drops = drops.clone();
        unsafe {
            if contract.symbol == "dropped" {
                imports
                    .insert(contract, move |_| {
                        drops.set(drops.get() + 1);
                        Ok(())
                    })
                    .unwrap();
            } else {
                assert_eq!(contract.symbol, "clear_native");
                let VmType::Reference { referent, .. } = &contract.parameters[0] else {
                    panic!("Vec reference");
                };
                let vector = contract.layout_of(referent).unwrap();
                assert_eq!(
                    (vector.size, vector.alignment),
                    (size_of::<NativeVec<()>>(), align_of::<NativeVec<()>>())
                );
                let VmNativeLayoutShape::Product(fields) = vector.shape else {
                    panic!("Vec fields");
                };
                let VmType::RawPointer { pointee, .. } = &fields[0].layout.ty else {
                    panic!("data pointer");
                };
                assert_eq!(contract.layout_of(pointee).unwrap().size, 0);
                imports
                    .insert(contract, move |call| {
                        let mut argument = MaybeUninit::<*mut NativeVec<()>>::uninit();
                        call.write_argument(0, argument.as_mut_ptr().cast())?;
                        let owner = argument.assume_init();
                        let backing = (*owner).pointer;
                        assert_eq!((*owner).length, 3);
                        assert_eq!(drops.get(), 0);
                        assert_eq!(
                            call.with_callback(1, |callback| clear_vector(owner, callback))?,
                            VmNativeStatus::Ok
                        );
                        assert_eq!(
                            drops.get(),
                            3,
                            "source hooks execute while the native call is active"
                        );
                        assert_eq!((*owner).length, 0);
                        assert_eq!((*owner).pointer, backing);
                        let result = 42i64;
                        call.set_result_from((&result as *const i64).cast())
                    })
                    .unwrap();
            }
        }
    }
    // The original Vec home and its moved cleanup parameter occupy bytes;
    // the three Marker residents and their destruction frames occupy none.
    // SAFETY: all three source hooks run during the real bytecode callback.
    assert_eq!(
        unsafe {
            program.run_i64_with_native(
                &imports,
                VmExecutionLimits {
                    max_native_bytes: (2 * size_of::<NativeVec<()>>()) as u64,
                    max_native_allocation_bytes: size_of::<NativeVec<()>>() as u64,
                    ..Default::default()
                },
            )
        }
        .unwrap(),
        42
    );
    assert_eq!(drops.get(), 3);
}
