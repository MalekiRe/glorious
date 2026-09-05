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
    unsafe fn borrow_shared<'a, T>(pointer: *const T) -> &'a T;
    unsafe fn borrow_unique<'a, T>(pointer: *mut T) -> &'a mut T;
    unsafe fn as_raw_shared<T>(value: &T) -> *const T;
    unsafe fn as_raw_unique<T>(value: &mut T) -> *mut T;
    unsafe fn cast_const<T, U>(pointer: *const T) -> *const U;
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
                // Static-data spellings are sealed to canonical std. Their
                // address leaves are exercised by the standard-library suite.
                .filter(|primitive| !matches!(primitive, MemoryPrimitive::StaticUtf8Address | MemoryPrimitive::StaticBytesAddress))
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
                let owner = Owner {{ pointer: pointer, length: 2 }};
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
                let owner = Owner { pointer: cast<u8, i64>(bytes) };
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
