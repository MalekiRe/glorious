//! Ordinary source specialization over general machine memory operations.

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath,
    MemoryPrimitive, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput,
    SourceInput, StageZeroCompiler, VerifiedVmProgram, VmExecutionLimits,
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
    unsafe fn offset<T>(pointer: *mut T, count: usize) -> *mut T;
    unsafe fn offset_const<T>(pointer: *const T, count: usize) -> *const T;
    unsafe fn cast<T, U>(pointer: *mut T) -> *mut U;
    unsafe fn as_const<T>(pointer: *mut T) -> *const T;
    unsafe fn read<T>(pointer: *const T) -> T;
    unsafe fn write<T>(pointer: *mut T, value: T) -> ();
    unsafe fn copy<T>(source: *const T, destination: *mut T, count: usize) -> ();
    unsafe fn copy_nonoverlapping<T>(source: *const T, destination: *mut T, count: usize) -> ();
"#;

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("memory-fixture@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"runtime-memory-tests")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package.clone(),
            LogicalPath::parse("src/lib.glorious").unwrap(),
            format!("{DECLARATIONS}\n{source}").as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: Some(RuntimeManifestInput {
            standard_library: package,
            selectors: MemoryPrimitive::ALL
                .into_iter()
                .map(|primitive| PrimitiveSelector {
                    role: PrimitiveRole::Memory(primitive),
                    module_path: "crate".into(),
                    name: primitive
                        .selector_name()
                        .strip_prefix("memory-")
                        .unwrap()
                        .replace('-', "_"),
                })
                .collect(),
            host_imports: vec![],
        }),
    }
}

fn compile(source: &str) -> VerifiedVmProgram {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    outcome.artifact.unwrap()
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
    for (declaration, constructor) in [
        ("enum Choice { Value(i64) }", "Choice::Value(42)"),
        (
            "enum Choice { Empty, Value(i64), Pair(u8, i64) }",
            "Choice::Value(42)",
        ),
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
                    handle value {{ Choice::Value(found) => found, _ => 0 }}
                }}
            }}
        "#
        ));
        // SAFETY: each enum is initialized and moved out using its identical
        // concrete type, with the allocation released after the move.
        assert_eq!(
            unsafe { program.run_i64_with_unsafe(VmExecutionLimits::default()) }.unwrap(),
            42
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
