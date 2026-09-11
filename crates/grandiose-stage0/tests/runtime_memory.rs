//! Ordinary source specialization over general machine memory operations.

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    MemoryPrimitive, PackageKey, PrimitiveRole,
    SourceInput, StageZeroCompiler, VerifiedVmProgram, VmExecutionLimits, decode_and_verify_program,
};
use std::collections::BTreeMap;

const DECLARATIONS: &str = r#"
    fn size_of<T>() -> usize;
    fn align_of<T>() -> usize;
    unsafe fn null<T>() -> *mut T;
    unsafe fn dangling<T>() -> *mut T;
    unsafe fn allocate(size: usize, alignment: usize) -> *mut u8;
    unsafe fn reallocate(pointer: *mut u8, old_size: usize, alignment: usize, new_size: usize) -> *mut u8;
    unsafe fn deallocate(pointer: *mut u8, size: usize, alignment: usize) -> ();
    unsafe fn is_null<T>(pointer: *mut T) -> u32;
    fn pointer_eq<T>(left: *const T, right: *const T) -> u32;
    fn pointer_address<T>(pointer: *const T) -> usize;
    unsafe fn offset<T>(pointer: *mut T, count: usize) -> *mut T;
    unsafe fn offset_const<T>(pointer: *const T, count: usize) -> *const T;
    unsafe fn cast<T, U>(pointer: *mut T) -> *mut U;
    unsafe fn as_const<T>(pointer: *mut T) -> *const T;
    unsafe fn read<T>(pointer: *const T) -> T;
    unsafe fn write<T>(pointer: *mut T, value: T) -> ();
    unsafe fn copy<T>(source: *const T, destination: *mut T, count: usize) -> ();
    unsafe fn copy_nonoverlapping<T>(source: *const T, destination: *mut T, count: usize) -> ();
    unsafe fn borrow_shared<'a, T>(pointer: *const T) -> &'a T;
    unsafe fn borrow_unique<'a, T>(pointer: *mut T) -> &'a mut T;
    unsafe fn as_raw_shared<T>(value: &T) -> *const T;
    unsafe fn as_raw_unique<T>(value: &mut T) -> *mut T;
    unsafe fn cast_const<T, U>(pointer: *const T) -> *const U;
    unsafe fn forget<T>(value: T) -> ();
"#;

const NATIVE_VIEWS: &str = r#"
    enum Maybe<T> { None, Some(T) }
    struct Owner<T> { pointer: *mut T, length: usize }
    impl<T> Use<[0, 1]> for Owner<T> {}
    // The zero-sized referent carries the owner loan; the reference's actual
    // pointer is the data address. No extra pointer or phantom runtime field.
    struct Window<'a, T> { storage: &'a (), length: usize }
    struct WindowMut<'a, T> { storage: &'a mut (), length: usize }
    fn window<'a, T>(owner: &'a Owner<T>) -> Window<'a, T> {
        unsafe {
            Window<'a, T> { storage: borrow_shared(cast_const<T, ()>(as_const(owner.pointer))), length: owner.length }
        }
    }
    fn window_mut<'a, T>(owner: &'a mut Owner<T>) -> WindowMut<'a, T> {
        unsafe {
            WindowMut<'a, T> { storage: borrow_unique(cast<T, ()>(owner.pointer)), length: owner.length }
        }
    }
    fn first<'a, T>(value: Window<'a, T>) -> Maybe<&'a T> {
        handle value.length {
            0 => Maybe::None,
            _ => unsafe { Maybe::Some(borrow_shared(cast_const<(), T>(as_raw_shared(value.storage)))) },
        }
    }
    fn first_mut<'a, T>(value: WindowMut<'a, T>) -> Maybe<&'a mut T> {
        handle value.length {
            0 => Maybe::None,
            _ => unsafe { Maybe::Some(borrow_unique(cast<(), T>(as_raw_unique(value.storage)))) },
        }
    }
    fn split<'a, T>(value: WindowMut<'a, T>, index: usize) -> Maybe<(WindowMut<'a, T>, WindowMut<'a, T>)> {
        handle index <= value.length {
            false => Maybe::None,
            true => unsafe {
                let pointer = cast<(), T>(as_raw_unique(value.storage));
                Maybe::Some((
                    WindowMut<'a, T> { storage: borrow_unique(cast<T, ()>(pointer)), length: index },
                    WindowMut<'a, T> { storage: borrow_unique(cast<T, ()>(offset(pointer, index))), length: value.length - index },
                ))
            },
        }
    }
"#;

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("memory-fixture@0.1.0".into());
    let standard = PackageKey("std@0.1.0".into());
    let canonical = include_str!("../../../stdlib/src/lib.glorious");
    let mut request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"runtime-memory-tests")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![
            SourceInput::new(package, LogicalPath::parse("src/lib.glorious").unwrap(),
                format!("use std::*; use std::memory_fixture::*;\n{source}").as_bytes()),
            SourceInput::new(standard.clone(), LogicalPath::parse("src/lib.glorious").unwrap(), canonical.as_bytes()),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };
    // Keep canonical operators/Bool and all their finite machine bindings.
    // Replace only general memory declarations with the test-owned, bodyless
    // names above, rebinding the exact roles rather than introducing compiler
    // spellings or forwarding bodies. Static-data authority stays unchanged.
    let compiler = StageZeroCompiler::new();
    let revision = compiler.import_revision(request.clone(), None).unwrap();
    let mut manifest = compiler.open_session(revision).unwrap()
        .snapshot().world().runtime_manifest.clone().unwrap();
    let mut replacements = Vec::new();
    for selector in &mut manifest.selectors {
        if matches!(selector.role, PrimitiveRole::Memory(primitive)
            if !matches!(primitive, MemoryPrimitive::StaticUtf8Address | MemoryPrimitive::StaticBytesAddress | MemoryPrimitive::StaticBytesLen)) {
            let short = selector.name.strip_prefix("__g1_memory_").unwrap().to_owned();
            replacements.push((selector.name.clone(), short.clone()));
            selector.name = short;
            selector.module_path = "crate::memory_fixture".into();
        }
    }
    let mut library = canonical.lines().filter(|line| !replacements.iter().any(|(name, _)| {
        let line = line.trim_start().strip_prefix("unsafe fn ").unwrap_or(line.trim_start());
        line.ends_with(';') && line.contains(" -> ")
            && (line.starts_with(&format!("{name}<")) || line.starts_with(&format!("{name}(")))
    })).collect::<Vec<_>>().join("\n");
    // Long names first avoids accidentally treating `offset_const` as `offset`.
    replacements.sort_by_key(|(name, _)| std::cmp::Reverse(name.len()));
    for (name, short) in replacements { library = library.replace(&name, &format!("memory_fixture::{short}")); }
    let declarations = DECLARATIONS.replace("    fn ", "    pub fn ")
        .replace("    unsafe fn ", "    pub unsafe fn ");
    request.sources[1] = SourceInput::new(standard, LogicalPath::parse("src/lib.glorious").unwrap(),
        format!("{library}\npub mod memory_fixture {{ {declarations} }}").as_bytes());
    request.runtime_manifest = Some(manifest);
    request
}

fn compile(source: &str) -> VerifiedVmProgram {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    outcome.artifact.unwrap()
}

#[test]
fn mandatory_tail_preserves_incoming_storage_after_typed_memory_updates() {
    for source in [
        r#"
            fn read_value(value: &mut i64) -> i64 { *value }
            fn relay(value: &mut i64) -> i64 {
                unsafe { write(as_raw_unique(&mut *value), 42) };
                tail read_value(value)
            }
            pub fn main() -> i64 { let mut value = 0; relay(&mut value) }
        "#,
        r#"
            struct Storage { pointer: *mut i64 }
            fn replace_storage(storage: &mut Storage) {
                unsafe {
                    let pointer = cast<u8, i64>(allocate(8, 8));
                    write(pointer, 42);
                    deallocate(cast<i64, u8>(storage.pointer), 8, 8);
                    (*storage).pointer = pointer;
                }
            }
            fn finish(storage: &mut Storage) -> i64 {
                unsafe {
                    let value = read(as_const(storage.pointer));
                    deallocate(cast<i64, u8>(storage.pointer), 8, 8);
                    value
                }
            }
            fn relay(storage: &mut Storage) -> i64 {
                replace_storage(&mut *storage);
                tail finish(storage)
            }
            pub fn main() -> i64 {
                unsafe {
                    let pointer = cast<u8, i64>(allocate(8, 8));
                    write(pointer, 0);
                    let mut storage = Storage { pointer: pointer };
                    relay(&mut storage)
                }
            }
        "#,
    ] {
        for optimization in ["0", "2"] {
            let mut request = request(source);
            request.codegen_options.insert("optimization-level".into(), optimization.into());
            let program = StageZeroCompiler::new().compile(request)
                .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics())).artifact.unwrap();
            let decoded = decode_and_verify_program(&program.canonical_bytes()).unwrap();
            for program in [&program, &decoded] {
                // SAFETY: the fixtures initialize, consume, and release each
                // allocated resident before its storage is retired.
                assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 42);
            }
        }
    }
}

#[test]
fn mandatory_tail_rejects_current_frame_pointers_written_into_surviving_storage() {
    for update in [
        "(*storage).pointer = pointer;",
        "write(as_raw_unique(&mut storage.pointer), pointer);",
        "install(&mut *storage, pointer);",
        "copy(as_raw_shared(&pointer), as_raw_unique(&mut storage.pointer), 1);",
        "copy_nonoverlapping(as_raw_shared(&pointer), as_raw_unique(&mut storage.pointer), 1);",
    ] {
        let source = format!(r#"
            struct Storage {{ pointer: *mut i64 }}
            fn install(storage: &mut Storage, pointer: *mut i64) {{
                unsafe {{ write(as_raw_unique(&mut storage.pointer), pointer) }}
            }}
            fn finish(storage: &mut Storage) -> i64 {{
                unsafe {{ read(as_const(storage.pointer)) }}
            }}
            fn relay(storage: &mut Storage) -> i64 {{
                let mut local = 42;
                unsafe {{
                    let pointer = as_raw_unique(&mut local);
                    {update}
                }};
                tail finish(storage)
            }}
            pub fn main() -> i64 {{
                unsafe {{
                    let mut storage = Storage {{ pointer: null<i64>() }};
                    relay(&mut storage)
                }}
            }}
        "#);
        let diagnostics = StageZeroCompiler::new().compile(request(&source))
            .expect_err("a memory-write or helper summary cannot hide an outgoing frame pointer")
            .diagnostics();
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G7042"
            && diagnostic.message.contains("mandatory tail carrier has no frame-independent provenance proof")),
            "{source}: {diagnostics:#?}");
    }
}

#[test]
fn mandatory_tail_preserves_incoming_memory_across_local_early_return_helpers() {
    let source = r#"
        struct Storage { pointer: *mut i64 }
        fn observe(storage: &Storage, early: Bool) -> i64 {
            handle early { true => return(1, @observe), false => () };
            2
        }
        fn finish(storage: &Storage) -> i64 { unsafe { read(as_const(storage.pointer)) } }
        fn relay(storage: &Storage) -> i64 {
            observe(storage, true);
            observe(storage, false);
            tail finish(storage)
        }
        pub fn main() -> i64 {
            unsafe {
                let pointer = cast<u8,i64>(allocate(8, 8));
                write(pointer, 42);
                let storage = Storage { pointer: pointer };
                let answer = relay(&storage);
                deallocate(cast<i64,u8>(pointer), 8, 8);
                answer
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        for program in [&artifact, &decoded] {
            // SAFETY: the fixture initializes and frees its sole allocation.
            assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
}

#[test]
fn mandatory_tail_preserves_untouched_pointer_fields_in_returned_owned_products() {
    let source = r#"
        struct Storage<T> { pointer: *mut T, count: usize }
        struct Carrier<T> { storage: Storage<T> }
        fn update<T>(value: Carrier<T>) -> Carrier<T> {
            let mut value = value; value.storage.count = 0; value
        }
        fn finish(value: Carrier<i64>) -> i64 { unsafe { read(as_const(value.storage.pointer)) } }
        fn relay(value: Carrier<i64>) -> i64 { let rest = update(value); tail finish(rest) }
        pub fn main() -> i64 {
            unsafe {
                let pointer = cast<u8,i64>(allocate(8, 8)); write(pointer, 42);
                let answer = relay(Carrier { storage: Storage { pointer: pointer, count: 1 } });
                deallocate(cast<i64,u8>(pointer), 8, 8); answer
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input)
            .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        for program in [&artifact, &decoded] {
            // SAFETY: the allocation is initialized and retained until relay
            // returns, and the helper changes only its scalar count field.
            assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
}

#[test]
fn mandatory_tail_return_proofs_cannot_hide_replaced_or_uncovered_pointer_fields() {
    let prefix = r#"
        struct Storage { pointer: *mut i64, count: usize }
        fn update(value: Storage) -> Storage { let mut value = value; value.count = 0; value }
        fn replace(value: Storage, pointer: *mut i64) -> Storage {
            let mut value = value; value.pointer = pointer; value
        }
        fn choose(value: Storage, flag: i64) -> Storage {
            handle flag {
                0 => update(value),
                _ => unsafe { let mut local = 42; replace(value, as_raw_unique(&mut local)) },
            }
        }
        fn finish(value: Storage) -> i64 { unsafe { read(as_const(value.pointer)) } }
    "#;
    for body in [
        "let mut local = 42; let rest = unsafe { replace(value, as_raw_unique(&mut local)) }; tail finish(rest)",
        "let rest = choose(value, flag); tail finish(rest)",
    ] {
        let source = format!("{prefix}
            fn relay(value: Storage, flag: i64) -> i64 {{ {body} }}
            pub fn main() -> i64 {{ unsafe {{ relay(Storage {{ pointer: null<i64>(), count: 1 }}, 1) }} }}");
        for optimization in ["0", "2"] {
            let mut input = request(&source);
            input.codegen_options.insert("optimization-level".into(), optimization.into());
            let failure = StageZeroCompiler::new().compile(input)
                .expect_err("untouched siblings or one known return cannot prove a replaced pointer independent");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4403"),
                "{source}: {:#?}", failure.diagnostics());
        }
    }
}

#[test]
fn mandatory_tail_preserves_owned_headers_across_machine_memory_operations() {
    let source = r#"
        struct Storage { pointer: *mut i64, count: i64 }
        fn update(value: Storage) -> Storage {
            let mut value = value;
            unsafe {
                let pointer = offset(value.pointer, 0);
                value.count = read(as_const(pointer));
                copy(as_const(pointer), pointer, 1);
            };
            value
        }
        fn finish(value: Storage) -> i64 { unsafe { read(as_const(value.pointer)) } }
        fn relay(value: Storage) -> i64 { let rest = update(value); tail finish(rest) }
        pub fn main() -> i64 {
            unsafe {
                let pointer = cast<u8,i64>(allocate(8, 8)); write(pointer, 42);
                let answer = relay(Storage { pointer: pointer, count: 0 });
                deallocate(cast<i64,u8>(pointer), 8, 8); answer
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input)
            .unwrap_or_else(|error| panic!("{:#?}", error.diagnostics())).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        for program in [&artifact, &decoded] {
            // SAFETY: one initialized scalar is read/copied within the same
            // allocation; the owner is released only after the tail returns.
            assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let ir = StageZeroCompiler::new().compile_llvm(request(source), LlvmTarget::host().unwrap()).unwrap();
    for optimization in [0, 2] {
        // SAFETY: the same initialized allocation stays live through the tail
        // transfer, then is released once by its caller.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
    }
}

#[test]
fn mandatory_tail_preserves_incoming_memory_across_proven_short_circuit_callbacks() {
    let source = r#"
        struct Storage { pointer: *mut i64 }
        fn finish(storage: &Storage) -> i64 { unsafe { read(as_const(storage.pointer)) } }
        fn relay(storage: &Storage, value: u8) -> i64 {
            let selected = value >= 48 and { value <= 57 };
            handle selected { true => (), false => () };
            tail finish(storage)
        }
        pub fn main() -> i64 {
            unsafe {
                let pointer = cast<u8,i64>(allocate(8, 8));
                write(pointer, 42);
                let storage = Storage { pointer: pointer };
                relay(&storage, 0);
                relay(&storage, 99);
                let answer = relay(&storage, 50);
                deallocate(cast<i64,u8>(pointer), 8, 8);
                answer
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        for program in [&artifact, &decoded] {
            // SAFETY: the fixture initializes and frees its sole allocation.
            assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
}

#[test]
fn mandatory_tail_rejects_mutation_in_closed_short_circuit_callbacks() {
    for invoke in [
        "value >= 48 and { unsafe { write(destination, pointer) }; true }",
        "invoke(() -> Bool { unsafe { write(destination, pointer) }; true })",
    ] {
        let source = format!(r#"
            struct Storage {{ pointer: *mut i64 }}
            fn invoke<F>(action: F) -> Bool where F: Fn<(), Output = Bool, Effects = {{}}> {{ action() }}
            fn finish(storage: &Storage) -> i64 {{ unsafe {{ read(as_const(storage.pointer)) }} }}
            fn relay(storage: &mut Storage, value: u8) -> i64 {{
                let mut local = 42;
                let pointer = unsafe {{ as_raw_unique(&mut local) }};
                let destination = unsafe {{ as_raw_unique(&mut storage.pointer) }};
                let selected = {invoke};
                handle selected {{ true => (), false => () }};
                tail finish(storage)
            }}
            pub fn main() -> i64 {{
                let mut storage = Storage {{ pointer: unsafe {{ null<i64>() }} }};
                relay(&mut storage, 50)
            }}
        "#);
        for optimization in ["0", "2"] {
            let mut input = request(&source);
            input.codegen_options.insert("optimization-level".into(), optimization.into());
            let diagnostics = StageZeroCompiler::new().compile(input)
                .expect_err("vacant cleanup cannot hide executed callback mutation").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G7042"
                && diagnostic.message.contains("no frame-independent provenance proof")), "{diagnostics:#?}");
        }
    }
}

#[test]
fn mandatory_tail_rejects_reference_mutation_hidden_in_an_invoked_callback() {
    for invoke in ["action()", "invoke(action)"] {
        let source = format!(r#"
            struct Storage {{ pointer: *mut i64 }}
            fn invoke<F>(action: F) / {{ <F as Fn<()>>::Effects }}
                where F: Fn<(), Output = ()> {{ action() }}
            fn finish(storage: &Storage) -> i64 {{ unsafe {{ read(as_const(storage.pointer)) }} }}
            fn relay(storage: &mut Storage) -> i64 {{
                let mut local = 42;
                let pointer = unsafe {{ as_raw_unique(&mut local) }};
                let destination = unsafe {{ as_raw_unique(&mut storage.pointer) }};
                let action = () -> () {{ unsafe {{ write(destination, pointer) }} }};
                {invoke};
                tail finish(storage)
            }}
            pub fn main() -> i64 {{
                let mut storage = Storage {{ pointer: unsafe {{ null<i64>() }} }};
                relay(&mut storage)
            }}
        "#);
        for optimization in ["0", "2"] {
            let mut input = request(&source);
            input.codegen_options.insert("optimization-level".into(), optimization.into());
            let diagnostics = StageZeroCompiler::new().compile(input)
                .expect_err("callable invocation must not hide a pointer to the outgoing frame").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G7042"
                && diagnostic.message.contains("no frame-independent provenance proof")), "{diagnostics:#?}");
        }
    }
}

#[test]
fn mandatory_tail_distinguishes_getter_contents_from_a_local_owner_address() {
    let mixed = "fn pointer(address: &mut Storage, contents: &mut Storage, choose_address: Bool) -> *mut i64 { handle choose_address { true => unsafe { cast<Storage,i64>(as_raw_unique(address)) }, false => contents.pointer } }";
    for (getter, call, valid) in [
        ("fn pointer(value: &mut Storage) -> *mut i64 { value.pointer }", "pointer(&mut scratch)", true),
        ("fn pointer(value: &mut Storage) -> *mut i64 { unsafe { cast<Storage,i64>(as_raw_unique(value)) } }", "pointer(&mut scratch)", false),
        (mixed, "pointer(&mut *storage, &mut scratch, false)", true),
        (mixed, "pointer(&mut scratch, &mut *storage, false)", false),
    ] {
        let source = format!(r#"
            struct Storage {{ pointer: *mut i64 }}
            {getter}
            fn finish(storage: &Storage) -> i64 {{ unsafe {{ read(as_const(storage.pointer)) }} }}
            fn relay(storage: &mut Storage) -> i64 {{
                let mut scratch = Storage {{ pointer: storage.pointer }};
                let copied = {call};
                (*storage).pointer = copied;
                tail finish(storage)
            }}
            pub fn main() -> i64 {{ unsafe {{
                let allocation = cast<u8,i64>(allocate(8, 8));
                write(allocation, 42);
                let mut storage = Storage {{ pointer: allocation }};
                let result = relay(&mut storage);
                deallocate(cast<i64,u8>(allocation), 8, 8);
                result
            }} }}
        "#);
        let outcome = StageZeroCompiler::new().compile(request(&source));
        if valid {
            let artifact = outcome.unwrap_or_else(|error| panic!("{source}: {error:#?}")).artifact.unwrap();
            let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
            for program in [&artifact, &decoded] {
                // SAFETY: only the initialized heap allocation is dereferenced and freed.
                assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
            }
            use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
            let ir = StageZeroCompiler::new().compile_llvm(request(&source), LlvmTarget::host().unwrap()).unwrap();
            for optimization in [0, 2] {
                // SAFETY: execute the same checked local allocation fixture.
                let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
                assert_eq!(unsafe { native.run_i64_profiled(Default::default()) }.unwrap().0, 42);
            }
        } else {
            let diagnostics = outcome.expect_err("a getter must not hide the outgoing scratch address").diagnostics();
            assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G7042"
                && diagnostic.message.contains("no frame-independent provenance proof")), "{diagnostics:#?}");
        }
    }
}

#[test]
fn mandatory_tail_keeps_incoming_proof_across_local_scratch_owner_mutation() {
    let source = r#"
        struct Storage { pointer: *mut i64 }
        fn rewrite(storage: &mut Storage) {
            let pointer = storage.pointer;
            unsafe { write(as_raw_unique(&mut storage.pointer), pointer) }
        }
        fn finish(storage: &Storage) -> i64 { unsafe { read(as_const(storage.pointer)) } }
        fn relay(storage: &Storage) -> i64 {
            let mut scratch = Storage { pointer: storage.pointer };
            rewrite(&mut scratch);
            tail finish(storage)
        }
        pub fn main() -> i64 {
            unsafe {
                let pointer = cast<u8,i64>(allocate(8, 8));
                write(pointer, 42);
                let storage = Storage { pointer: pointer };
                let answer = relay(&storage);
                deallocate(cast<i64,u8>(pointer), 8, 8);
                answer
            }
        }
    "#;
    for optimization in ["0", "2"] {
        let mut input = request(source);
        input.codegen_options.insert("optimization-level".into(), optimization.into());
        let artifact = StageZeroCompiler::new().compile(input).unwrap().artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the fixture allocates, initializes and frees its sole native resident.
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
}

#[test]
fn mandatory_tail_memory_copies_and_resize_preserve_scalar_residents() {
    for copy in ["copy", "copy_nonoverlapping"] {
        let source = format!(r#"
            struct Storage {{ pointer: *mut i64 }}
            fn update(storage: &mut Storage, remaining: usize) -> i64 {{
                handle remaining {{
                    0 => unsafe {{
                        let value = read(as_const(storage.pointer));
                        deallocate(cast<i64, u8>(storage.pointer), 16, 8);
                        value
                    }},
                    _ => {{
                        unsafe {{
                            let source = cast<u8, i64>(allocate(8, 8));
                            write(source, 42);
                            {copy}(as_const(source), storage.pointer, 1);
                            deallocate(cast<i64, u8>(source), 8, 8);
                        }};
                        tail update(storage, remaining - 1)
                    }},
                }}
            }}
            fn relay(storage: &mut Storage) -> i64 {{
                unsafe {{
                    (*storage).pointer = cast<u8, i64>(reallocate(cast<i64, u8>(storage.pointer), 8, 8, 16));
                }};
                tail update(storage, 42)
            }}
            pub fn main() -> i64 {{
                unsafe {{
                    let pointer = cast<u8, i64>(allocate(8, 8));
                    write(pointer, 0);
                    let mut storage = Storage {{ pointer: pointer }};
                    relay(&mut storage)
                }}
            }}
        "#);
        for optimization in ["0", "2"] {
            let mut request = request(&source);
            request.codegen_options.insert("optimization-level".into(), optimization.into());
            let program = StageZeroCompiler::new().compile(request)
                .unwrap_or_else(|error| panic!("{source}: {:#?}", error.diagnostics())).artifact.unwrap();
            let decoded = decode_and_verify_program(&program.canonical_bytes()).unwrap();
            for program in [&program, &decoded] {
                // SAFETY: scalar residents are duplicable and every allocation
                // is released with its current size after its last access.
                assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits {
                    max_call_depth: 16, ..VmExecutionLimits::default()
                }) }.unwrap(), 42);
            }
        }
    }
}

#[test]
fn address_inspection_preserves_null_dangling_cast_and_one_past_addresses() {
    let candidate = compile(r#"
        fn inspect(first: *const i64, next: *const i64, end: *const i64,
                   round_trip: *const i64, empty: *const i64, aligned: *const i64) -> i64 {
            let equal = pointer_eq(first, first) + pointer_eq(first, round_trip) + pointer_eq(empty, empty);
            let distinct = pointer_eq(first, next) + pointer_eq(first, end) + pointer_eq(empty, aligned);
            handle equal == 3 { false => 0, true => handle distinct == 0 {
                false => 0, true => handle pointer_address(empty) == 0 {
                    false => 0, true => handle pointer_address(next) - pointer_address(first) == size_of<i64>() {
                        false => 0, true => handle pointer_address(end) - pointer_address(first) == 2 * size_of<i64>() {
                            false => 0, true => handle pointer_address(aligned) % align_of<i64>() == 0 { false => 0, true => 42 },
                        },
                    },
                },
            } }
        }
        pub fn main() -> i64 {
            unsafe {
                // No residents are initialized or read: only addresses are inspected.
                let allocation = allocate(16, 8);
                let first = as_const(cast<u8, i64>(allocation));
                let result = inspect(first, offset_const(first, 1), offset_const(first, 2),
                    cast_const<u8, i64>(cast_const<i64, u8>(first)), as_const(null<i64>()), as_const(dangling<i64>()));
                deallocate(allocation, 16, 8);
                result
            }
        }
    "#);
    let decoded = decode_and_verify_program(&candidate.canonical_bytes()).unwrap();
    for program in [&candidate, &decoded] {
        // SAFETY: the source forms only in-range/one-past pointers and releases
        // its allocation without reading uninitialized storage.
        assert_eq!(unsafe { program.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
    let mut malformed = grandiose_stage0::decode_program(&candidate.canonical_bytes()).unwrap();
    let instruction = malformed.functions.values_mut().flat_map(|function| &mut function.instructions)
        .find(|instruction| matches!(instruction, grandiose_stage0::VmInstruction::MemoryIntrinsic {
            primitive: MemoryPrimitive::PointerEq, ..
        })).expect("source must lower to the manifest-bound equality operation");
    let grandiose_stage0::VmInstruction::MemoryIntrinsic { primitive, .. } = instruction else { unreachable!() };
    *primitive = MemoryPrimitive::PointerAddress;
    malformed.fingerprint = malformed.computed_fingerprint();
    assert!(grandiose_stage0::verify_vm_program(malformed).is_err(), "the two-argument equality encoding is not a valid address operation");
}

#[test]
fn authoring_native_profile_measures_raw_extents_and_bulk_copy_bytes() {
    let candidate = compile(r#"
        pub fn main() -> i64 {
            unsafe {
                let source = allocate(16, 8);
                write(cast<u8, i64>(source), 42);
                let destination = allocate(16, 8);
                copy_nonoverlapping(as_const(cast<u8, i64>(source)), cast<u8, i64>(destination), 1);
                let result = read(as_const(cast<u8, i64>(destination)));
                copy(as_const(destination), offset(destination, 1), 7);
                let grown = reallocate(destination, 16, 8, 32);
                copy(as_const(grown), grown, 0);
                deallocate(source, 16, 8);
                deallocate(grown, 32, 8);
                result
            }
        }
    "#);
    let program = decode_and_verify_program(&candidate.canonical_bytes()).unwrap();
    // SAFETY: the local fixture initializes every byte it copies/reads, uses
    // the overlapping leaf only for overlap, and releases both owned buffers.
    let (value, profile) = unsafe { program.run_i64_for_authoring_with_unsafe(Default::default()) }.unwrap();
    assert_eq!(value, 42);
    let native = profile.native_memory;
    assert_eq!((native.raw_allocations, native.raw_reallocations, native.raw_deallocations), (2, 1, 2));
    assert_eq!((native.raw_live_bytes, native.raw_peak_bytes), (0, 48));
    assert_eq!(native.raw_bulk_copy_bytes, 15, "8 disjoint + 7 overlapping bytes; allocator relocation is not counted");
    assert_eq!(native.home_live_bytes, 0);
    assert!(native.peak_live_bytes >= native.raw_peak_bytes);
    assert!(native.peak_live_bytes <= VmExecutionLimits::default().max_native_bytes);
    assert!(!native.counters_saturated);
    // SAFETY: each run has the same local source obligations and a new domain.
    let (again, second) = unsafe { program.run_i64_for_authoring_with_unsafe(Default::default()) }.unwrap();
    assert_eq!(again, 42);
    assert_eq!(second.native_memory, native, "measurements cannot leak across runs");
}

#[test]
fn authoring_native_profile_keeps_outstanding_raw_bytes_visible_before_domain_teardown() {
    let candidate = compile("pub fn main() -> i64 { unsafe { let abandoned = allocate(8, 8); 42 } }");
    let program = decode_and_verify_program(&candidate.canonical_bytes()).unwrap();
    // SAFETY: no residents are initialized, borrowed, or accessed. The fixture
    // deliberately leaves its raw owner to the execution domain's final drop.
    let (value, profile) = unsafe { program.run_i64_for_authoring_with_unsafe(Default::default()) }.unwrap();
    assert_eq!(value, 42);
    assert_eq!(profile.native_memory.raw_live_bytes, 8);
    assert_eq!((profile.native_memory.raw_allocations, profile.native_memory.raw_deallocations), (1, 0));
    assert_eq!(profile.native_memory.home_live_bytes, 0);
}

#[test]
fn finite_replay_destroys_residual_owners_once_per_execution() {
    let program = compile(r#"
        effect Ask { [2, 2] ask() -> i64; }
        struct Counter { pointer: *mut i64 }
        impl Use<[0, 1]> for Counter {}
        impl Drop for Counter {
            drop(&mut self) -> {
                unsafe { write(self.pointer, read(as_const(self.pointer)) + 1); }
            }
        }
        fn worker(pointer: *mut i64) -> i64 / Ask {
            let value = Ask::ask();
            let owner = Counter { pointer: pointer };
            value
        }
        fn replay(pointer: *mut i64) -> i64 {
            handle worker(pointer) { Ask::ask() with k => k(20) + k(21) }
        }
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<i64>(), align_of<i64>());
                let pointer = cast<u8, i64>(bytes);
                write(pointer, 0);
                let answer = replay(pointer);
                let count = read(as_const(pointer));
                deallocate(bytes, size_of<i64>(), align_of<i64>());
                count * 100 + answer
            }
        }
    "#);
    // SAFETY: both sequential residuals borrow the same initialized counter;
    // it remains allocated until both destructors and the replay have ended.
    assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 241);
    let decoded = grandiose_stage0::decode_and_verify_program(&program.canonical_bytes()).unwrap();
    // SAFETY: independently decoded execution has the same closed allocation lifecycle.
    assert_eq!(unsafe { decoded.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 241);
}

#[test]
fn source_defined_ownership_markers_have_zero_layout_and_preserve_owner_moves() {
    let declarations = r#"
        struct PhantomData<T> {}
        impl<T, q: Quantity> Use<q> for PhantomData<T> where T: Use<q> {}
        struct NoCopy {}
        impl Use<[0, 1]> for NoCopy {}
        struct Owner<T> { pointer: *mut T, ownership: PhantomData<T>, unique: NoCopy }
        fn inspect<T>(value: &Owner<T>) -> usize { size_of<PhantomData<T>>() }
        fn take<T>(value: Owner<T>) -> usize { inspect(&value) }
    "#;
    let program = compile(&format!(r#"{declarations}
        pub fn main() -> i64 {{
            unsafe {{
                let owner = Owner<i64> {{ pointer: dangling(), ownership: PhantomData {{}}, unique: NoCopy {{}} }};
                let consumed = take(owner);
                handle consumed {{ 0 => 42, _ => 0 }}
            }}
        }}
    "#));
    // SAFETY: only an aligned dangling pointer is constructed; it is never
    // dereferenced, and both source ownership marker fields are zero-sized.
    assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 42);
    let rejected = format!(r#"{declarations}
        pub fn main() -> i64 {{
            unsafe {{
                let owner = Owner<i64> {{ pointer: dangling(), ownership: PhantomData {{}}, unique: NoCopy {{}} }};
                take(owner);
                inspect(&owner);
                42
            }}
        }}
    "#);
    let error = StageZeroCompiler::new().compile(request(&rejected)).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code.starts_with("G50")), "{error:#?}");
}

#[test]
fn native_reference_residents_store_actual_referent_pointers_and_write_through() {
    let program = compile(r#"
        struct Borrowed<'a> { value: &'a mut i64, suffix: u8 }
        fn increment(value: &mut Borrowed<'_>) -> () {
            *value.value = *value.value + 1;
        }
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<i64>(), align_of<i64>());
                let pointer = cast<u8, i64>(bytes);
                write(pointer, 40);
                let record_bytes = allocate(size_of<Borrowed<'_>>(), align_of<Borrowed<'_>>());
                let record_pointer = cast<u8, Borrowed<'_>>(record_bytes);
                write(record_pointer, Borrowed { value: borrow_unique(pointer), suffix: 1 });
                increment(borrow_unique(record_pointer));
                let moved = read(as_const(record_pointer));
                let result = *moved.value + 1;
                deallocate(record_bytes, size_of<Borrowed<'_>>(), align_of<Borrowed<'_>>());
                deallocate(bytes, size_of<i64>(), align_of<i64>());
                result
            }
        }
    "#);
    // SAFETY: the two exact allocations remain live throughout all references;
    // the unique resident is moved once, its last access precedes both releases.
    assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 42);
}

#[test]
fn reference_indirection_terminates_recursive_native_layouts() {
    let program = compile(r#"
        enum Link<'a> { End, Next(&'a Node<'a>) }
        struct Node<'a> { value: i64, next: Link<'a> }
        pub fn main() -> i64 {
            unsafe {
                let first_bytes = allocate(size_of<Node<'_>>(), align_of<Node<'_>>());
                let first = cast<u8, Node<'_>>(first_bytes);
                write(first, Node { value: 40, next: Link::End });
                let second_bytes = allocate(size_of<Node<'_>>(), align_of<Node<'_>>());
                let second = cast<u8, Node<'_>>(second_bytes);
                write(second, Node { value: 2, next: Link::Next(borrow_shared(as_const(first))) });
                let node = read(as_const(second));
                let result = handle node.next {
                    Link::End => 0,
                    Link::Next(previous) => previous.value + node.value,
                };
                deallocate(second_bytes, size_of<Node<'_>>(), align_of<Node<'_>>());
                deallocate(first_bytes, size_of<Node<'_>>(), align_of<Node<'_>>());
                result
            }
        }
    "#);
    // SAFETY: the linked nodes are fully initialized, their shared link stays
    // live until its last read, and both exact owners are subsequently released.
    assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 42);
}

#[test]
fn source_native_views_keep_owner_loans_and_split_disjoint_mutable_windows() {
    let source = format!(r#"{NATIVE_VIEWS}
        pub fn main() -> i64 {{
            unsafe {{
                let bytes = allocate(2 * size_of<i64>(), align_of<i64>());
                let pointer = cast<u8, i64>(bytes);
                write(pointer, 40);
                write(offset(pointer, 1), 0);
                let mut owner = Owner {{ pointer: pointer, length: 2 }};
                let result = handle split(window_mut(&mut owner), 1) {{
                    Maybe::None => 0,
                    Maybe::Some((left, right)) => handle first_mut(left) {{
                        Maybe::None => 0,
                        Maybe::Some(a) => handle first_mut(right) {{
                            Maybe::None => 0,
                            Maybe::Some(b) => {{ *a = *a + 1; *b = 1; *a + *b }},
                        }},
                    }},
                }};
                deallocate(bytes, 2 * size_of<i64>(), align_of<i64>());
                handle size_of<Window<'_, i64>>() {{ 16 => result, _ => 0 }}
            }}
        }}
    "#);
    let program = compile(&source);
    // SAFETY: both initialized elements stay allocated throughout the owner
    // loan, and checked source splitting produces disjoint mutable windows.
    assert_eq!(unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(), 42);

    let invalid = format!(r#"{NATIVE_VIEWS}
        pub fn bad(owner: &mut Owner<i64>) -> () {{
            let borrowed = window(&*owner);
            window_mut(owner);
            first(borrowed);
        }}
        pub fn main() -> i64 {{ 42 }}
    "#);
    let mut input = request(&invalid);
    input.mode = CompilationMode::Check;
    let error = StageZeroCompiler::new().compile(input).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code.starts_with("G50")), "{error:#?}");
}

#[test]
fn bodyless_memory_declarations_bind_and_execute_without_stub_bodies() {
    let program = compile(
        r#"
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<i64>(), align_of<i64>());
                let pointer = cast<u8, i64>(bytes);
                write(pointer, 42);
                let value = read(as_const(pointer));
                deallocate(bytes, size_of<i64>(), align_of<i64>());
                value
            }
        }
    "#,
    );
    // SAFETY: this source initializes one correctly aligned i64, reads it,
    // releases its exact allocation, and retains no pointer or reference.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
    let decoded = grandiose_stage0::decode_and_verify_program(&program.canonical_bytes()).unwrap();
    // SAFETY: round-tripping preserves the same tested source program.
    assert_eq!(
        unsafe { decoded.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn bodyless_runtime_declaration_without_a_binding_is_an_error() {
    let mut input = request("pub fn main() -> i64 { 42 }");
    input
        .runtime_manifest
        .as_mut()
        .unwrap()
        .selectors
        .retain(|selector| selector.role != PrimitiveRole::Memory(MemoryPrimitive::Allocate));
    let error = StageZeroCompiler::new().compile(input).unwrap_err();
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G7002"
        && diagnostic.message.contains("allocate")), "{error:#?}");
}

#[test]
fn runtime_binding_does_not_erase_a_declarations_unsafe_contract() {
    let input = request("pub fn main() -> *mut i64 { null<i64>() }");
    let error = StageZeroCompiler::new().compile(input).unwrap_err();
    assert!(
        error
            .diagnostics()
            .iter()
            .any(|diagnostic| diagnostic.code == "G4201"),
        "{error:#?}"
    );
}

#[test]
fn generic_raw_exchange_moves_a_linear_padded_record() {
    let program = compile(
        r#"
        struct Ticket { flag: u8, value: i64 }
        impl Use<[1, 1]> for Ticket {}
        unsafe fn exchange<T>(value: T) -> T {
            unsafe {
                let bytes = allocate(size_of<T>(), align_of<T>());
                let pointer = cast<u8, T>(bytes);
                write(pointer, value);
                let result = read(as_const(pointer));
                deallocate(bytes, size_of<T>(), align_of<T>());
                result
            }
        }
        pub fn main() -> i64 {
            let ticket = unsafe { exchange(Ticket { flag: 7, value: 42 }) };
            ticket.value
        }
    "#,
    );
    // SAFETY: exchange moves each initialized resident once out of its exact
    // concrete allocation before release. Ticket contains no interior loans.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn native_record_fields_follow_natural_host_padding() {
    let program = compile(
        r#"
        struct Padded { flag: u8, value: i64, tail: u8 }
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<Padded>(), align_of<Padded>());
                write(cast<u8, Padded>(bytes), Padded { flag: 7, value: 42, tail: 9 });
                let field = cast<u8, i64>(offset(bytes, 8));
                let value = read(as_const(field));
                deallocate(bytes, size_of<Padded>(), align_of<Padded>());
                value
            }
        }
    "#,
    );
    // SAFETY: the i64 field is at offset 8 in this natural-layout record.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
    let sizes = compile(
        r#"
        struct Padded { flag: u8, value: i64, tail: u8 }
        pub fn main() -> usize { size_of<Padded>() + align_of<Padded>() }
    "#,
    );
    assert_eq!(sizes.run_usize().unwrap(), 32);
}

#[test]
fn single_and_multiple_variant_enums_retain_discriminants_and_payloads() {
    const MULTIPLE: &str = "enum Choice { Empty, Value(i64), Pair(u8, i64) }";
    const ARMS: &str = "Choice::Empty => 7, Choice::Value(found) => found, Choice::Pair(first, second) => as<i64>(first) + second";
    for (declaration, constructor, arms, expected) in [
        ("enum Choice { Value(i64) }", "Choice::Value(42)", "Choice::Value(found) => found", 42),
        (
            MULTIPLE, "Choice::Value(42)", ARMS, 42,
        ),
        (MULTIPLE, "Choice::Pair(7, 35)", ARMS, 42),
        (MULTIPLE, "Choice::Empty", ARMS, 7),
    ] {
        let program = compile(&format!(
            r#"
            {declaration}
            pub fn main() -> i64 {{
                unsafe {{
                    let bytes = allocate(size_of<Choice>(), align_of<Choice>());
                    let pointer = cast<u8, Choice>(bytes);
                    write(pointer, {constructor});
                    let value = read(as_const(pointer));
                    deallocate(bytes, size_of<Choice>(), align_of<Choice>());
                    handle value {{ {arms} }}
                }}
            }}
        "#
        ));
        // SAFETY: each enum is initialized and moved out using its identical
        // concrete type, with the allocation released after the move.
        assert_eq!(
            unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
            expected
        );
    }
}

#[test]
fn zero_sized_linear_residents_move_without_allocating_bytes() {
    let program = compile(
        r#"
        struct Ticket {}
        impl Use<[1, 1]> for Ticket {}
        fn consume(ticket: Ticket) -> i64 { handle ticket { Ticket {} => 42 } }
        pub fn main() -> i64 {
            unsafe {
                let pointer = dangling<Ticket>();
                write(pointer, Ticket {});
                let ticket = read(as_const(offset(pointer, 100)));
                consume(ticket)
            }
        }
    "#,
    );
    let limits = VmExecutionLimits {
        max_native_bytes: 0,
        max_native_allocation_bytes: 0,
        ..VmExecutionLimits::default()
    };
    // SAFETY: one logical ZST resident is written and consumed exactly once;
    // aligned dangling storage needs no byte allocation even after ZST offset.
    assert_eq!(unsafe { program.run_i64_with_unsafe(limits) }.unwrap(), 42);
}

#[test]
fn typed_offsets_copies_and_resize_preserve_initialized_values() {
    let program = compile(
        r#"
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(24, align_of<i64>());
                let pointer = cast<u8, i64>(bytes);
                write(pointer, 2);
                write(offset(pointer, 1), 40);
                copy(as_const(pointer), offset(pointer, 1), 2);
                let resized = reallocate(bytes, 24, align_of<i64>(), 32);
                let current = cast<u8, i64>(resized);
                copy_nonoverlapping(offset_const(as_const(current), 2), current, 1);
                let answer = read(as_const(current)) + read(offset_const(as_const(current), 1));
                deallocate(resized, 32, align_of<i64>());
                answer
            }
        }
    "#,
    );
    // SAFETY: overlapping copy uses memmove semantics within three slots;
    // disjoint copy uses separate slots in the resized live allocation. Old
    // pointer values are never used after resize, and all reads are initialized.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn pointers_stored_in_raw_residents_retain_provenance() {
    let program = compile(
        r#"
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<i64>(), align_of<i64>());
                let value = cast<u8, i64>(bytes);
                write(value, 42);
                let pointer_bytes = allocate(size_of<*mut i64>(), align_of<*mut i64>());
                let slot = cast<u8, *mut i64>(pointer_bytes);
                write(slot, value);
                let restored = read(as_const(slot));
                let result = read(as_const(restored));
                deallocate(pointer_bytes, size_of<*mut i64>(), align_of<*mut i64>());
                deallocate(bytes, size_of<i64>(), align_of<i64>());
                result
            }
        }
    "#,
    );
    // SAFETY: the pointer is stored and loaded as a pointer, never reconstructed
    // from an integer. Its pointee stays live and initialized until the read.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn native_references_write_through_nested_calls_and_project_real_fields() {
    let program = compile(
        r#"
        struct Item { flag: u8, value: i64 }
        fn bump(value: &mut i64) -> () { *value = *value + 2; }
        fn nested(item: &mut Item) -> () { bump(&mut (*item).value); }
        fn inspect(item: &Item) -> i64 { item.value }
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<Item>(), align_of<Item>());
                let pointer = cast<u8, Item>(bytes);
                write(pointer, Item { flag: 7, value: 40 });
                nested(borrow_unique(pointer));
                let observed = inspect(borrow_shared(as_const(pointer)));
                let raw = read(as_const(cast<u8, i64>(offset(bytes, 8))));
                deallocate(bytes, size_of<Item>(), align_of<Item>());
                handle observed { 42 => raw, _ => 0 }
            }
        }
    "#,
    );
    // SAFETY: each temporary reference ends before the next access; the same
    // initialized Item remains in its allocation throughout both nested calls.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn native_reference_return_preserves_storage_and_does_not_freeze_a_snapshot() {
    let program = compile(
        r#"
        struct Owner { pointer: *mut i64 }
        fn get<'a>(owner: &'a Owner) -> &'a i64 {
            unsafe { borrow_shared(as_const(owner.pointer)) }
        }
        fn get_mut<'a>(owner: &'a mut Owner) -> &'a mut i64 {
            unsafe { borrow_unique(owner.pointer) }
        }
        fn relay<'a>(value: &'a mut i64) -> &'a mut i64 { value }
        pub fn main() -> i64 {
            unsafe {
                let bytes = allocate(size_of<i64>(), align_of<i64>());
                let mut owner = Owner { pointer: cast<u8, i64>(bytes) };
                write(owner.pointer, 40);
                *relay(get_mut(&mut owner)) = 42;
                let result = *get(&owner);
                deallocate(bytes, size_of<i64>(), align_of<i64>());
                result
            }
        }
    "#,
    );
    // SAFETY: Owner's safe methods tie each view to its borrow. The allocation
    // outlives those views, including the returned and reborrowed unique view.
    assert_eq!(
        unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
        42
    );
}

#[test]
fn safe_native_reference_facades_cannot_extend_or_overlap_their_owner_loan() {
    let facade = r#"
        struct Owner { pointer: *mut i64 }
        fn get<'a>(owner: &'a Owner) -> &'a i64 {
            unsafe { borrow_shared(as_const(owner.pointer)) }
        }
        fn get_mut<'a>(owner: &'a mut Owner) -> &'a mut i64 {
            unsafe { borrow_unique(owner.pointer) }
        }
    "#;
    for invalid in [
        "pub fn bad<'a>(owner: &'a Owner) -> &'static i64 { get(owner) }",
        "pub fn bad(owner: &mut Owner) -> i64 { let shared = get(&*owner); let unique = get_mut(&mut *owner); *unique = 7; *shared }",
        "pub fn bad(pointer: *mut i64) -> () { borrow_unique(pointer); }",
    ] {
        let mut input = request(&format!(
            "{facade}\n{invalid}\npub fn main() -> i64 {{ 0 }}"
        ));
        input.mode = CompilationMode::Check;
        let error = StageZeroCompiler::new().compile(input).unwrap_err();
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code.starts_with("G50") || diagnostic.code == "G4201"),
            "{error:#?}"
        );
    }
}
