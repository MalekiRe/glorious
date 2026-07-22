use grandiose::{
    CompileOptions, GenericParameterKind, HostImportRole, MachineTypeRole, ManifestHostImportLeaf,
    ManifestMachineType, ManifestPrimitiveLeaf, OptimizationLevel, TrustedRuntimeManifest,
    TrustedTraitManifest, compile_bundle_to_bytecode_with_manifest,
    compile_bundle_to_phases_with_manifest, compile_bundle_to_phases_with_manifest_and_options,
    compile_source_to_bytecode_with_manifest, run_bundle_entry_with_manifest_for_conformance,
    source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_NAME, Segment, SourceBundle},
};
use grandiose_vm::{Primitive, Value, Vm, verify};

fn array_type(id: u64, name: &str) -> ManifestMachineType {
    ManifestMachineType {
        id,
        display_name: name.into(),
        parameters: vec![GenericParameterKind::Type],
        role: MachineTypeRole::Array,
    }
}

fn leaf(id: u64, name: &str, primitive: Primitive) -> ManifestPrimitiveLeaf {
    ManifestPrimitiveLeaf {
        id,
        display_name: name.into(),
        primitive,
    }
}

fn manifest(
    types: Vec<ManifestMachineType>,
    leaves: Vec<ManifestPrimitiveLeaf>,
) -> TrustedTraitManifest {
    TrustedTraitManifest::trusted_default().with_runtime(
        TrustedRuntimeManifest::new(types, leaves).expect("test runtime manifest must be valid"),
    )
}

fn bundle(standard_library: &str, primary: &str) -> SourceBundle {
    SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("std.glorious", standard_library),
        Segment::new("main.glorious", primary),
        [],
    )
}

fn messages(error: Vec<grandiose::diagnostic::Diagnostic>) -> Vec<String> {
    error
        .into_iter()
        .map(|diagnostic| {
            assert_eq!(diagnostic.title, "error");
            assert!(diagnostic.span.is_none());
            diagnostic.message
        })
        .collect()
}

#[test]
fn runtime_manifest_accepts_the_closed_array_frontend_slice() {
    let unordered = TrustedRuntimeManifest::new(
        vec![array_type(100, "SecretBuffer")],
        vec![
            leaf(105, "seal_empty", Primitive::ArrayFinishDrained),
            leaf(101, "birth", Primitive::ArrayEmpty),
            leaf(104, "take_last", Primitive::ArrayPopMove),
            leaf(102, "measure", Primitive::ArrayLen),
            leaf(103, "append", Primitive::ArrayPushMove),
        ],
    )
    .expect("the five generation-1 Array leaves form a valid runtime manifest");
    let ordered = TrustedRuntimeManifest::new(
        vec![array_type(100, "SecretBuffer")],
        vec![
            leaf(101, "birth", Primitive::ArrayEmpty),
            leaf(102, "measure", Primitive::ArrayLen),
            leaf(103, "append", Primitive::ArrayPushMove),
            leaf(104, "take_last", Primitive::ArrayPopMove),
            leaf(105, "seal_empty", Primitive::ArrayFinishDrained),
        ],
    )
    .unwrap();

    assert_eq!(
        unordered, ordered,
        "manifest order must not create identity"
    );
}

#[test]
fn runtime_manifest_accepts_the_complete_frozen_array_surface_deterministically() {
    let primitives = [
        Primitive::ArrayNew,
        Primitive::ArrayLen,
        Primitive::ArrayGetCopy,
        Primitive::ArrayGetMove,
        Primitive::ArrayGetBorrowShared,
        Primitive::ArrayGetBorrowUnique,
        Primitive::ArraySetMove,
        Primitive::ArrayEmpty,
        Primitive::ArrayPushMove,
        Primitive::ArrayPopMove,
        Primitive::ArrayCapacity,
        Primitive::ArrayReserve,
        Primitive::ArrayFinishDrained,
    ];
    let ordered = primitives
        .iter()
        .enumerate()
        .map(|(index, primitive)| leaf(101 + index as u64, &format!("leaf_{index}"), *primitive))
        .collect::<Vec<_>>();
    let mut reversed = ordered.clone();
    reversed.reverse();

    assert_eq!(
        TrustedRuntimeManifest::new(vec![array_type(100, "OpaqueStorage")], ordered).unwrap(),
        TrustedRuntimeManifest::new(vec![array_type(100, "OpaqueStorage")], reversed).unwrap(),
    );
}

#[test]
fn runtime_manifest_rejects_duplicate_ids_across_kinds() {
    let errors = TrustedRuntimeManifest::new(
        vec![array_type(100, "Raw")],
        vec![leaf(100, "make", Primitive::ArrayEmpty)],
    )
    .unwrap_err();

    assert!(
        messages(errors).iter().any(|message| {
            message.contains("trusted runtime manifest contains duplicate id 100")
        })
    );
}

#[test]
fn runtime_manifest_rejects_names_shared_by_primitive_and_host_leaves() {
    let errors = TrustedRuntimeManifest::with_host_imports(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "same_leaf", Primitive::ArrayEmpty)],
        vec![ManifestHostImportLeaf {
            id: 102,
            display_name: "same_leaf".into(),
            role: HostImportRole::DiagnosticWrite,
        }],
    )
    .unwrap_err();
    assert!(messages(errors).iter().any(|message| {
        message.contains("duplicate or empty host-import leaf name `same_leaf`")
    }));
}

#[test]
fn runtime_manifest_rejects_duplicate_names_roles_and_primitive_identities() {
    let errors = TrustedRuntimeManifest::new(
        vec![array_type(100, "Raw"), array_type(101, "Raw")],
        vec![
            leaf(102, "make", Primitive::ArrayEmpty),
            leaf(103, "make", Primitive::ArrayLen),
            leaf(104, "also_make", Primitive::ArrayEmpty),
        ],
    )
    .unwrap_err();
    let messages = messages(errors);

    assert!(
        messages
            .iter()
            .any(|message| { message.contains("duplicate or empty machine type name `Raw`") })
    );
    assert!(
        messages
            .iter()
            .any(|message| { message.contains("duplicate machine type role Array") })
    );
    assert!(
        messages
            .iter()
            .any(|message| { message.contains("duplicate or empty primitive leaf name `make`") })
    );
    assert!(
        messages
            .iter()
            .any(|message| { message.contains("duplicate primitive identity ArrayEmpty") })
    );
}

#[test]
fn runtime_manifest_rejects_the_wrong_machine_schema() {
    let mut raw = array_type(100, "Raw");
    raw.parameters.clear();
    let errors = TrustedRuntimeManifest::new(vec![raw], vec![]).unwrap_err();

    assert!(messages(errors).iter().any(|message| {
        message.contains("trusted machine type `Raw` does not match the frozen Array schema")
    }));
}

#[test]
fn runtime_manifest_rejects_leaves_without_their_machine_type() {
    let errors =
        TrustedRuntimeManifest::new(vec![], vec![leaf(100, "make", Primitive::ArrayEmpty)])
            .unwrap_err();

    assert!(messages(errors).iter().any(|message| {
        message
            .contains("Array-dependent primitive leaves require one Array machine type constructor")
    }));
}

#[test]
fn immutable_text_and_bytes_leaves_do_not_require_the_array_constructor() {
    TrustedRuntimeManifest::new(
        vec![],
        vec![
            leaf(100, "text_len", Primitive::TextByteLen),
            leaf(101, "text_concat", Primitive::TextConcat),
            leaf(102, "text_eq", Primitive::TextEq),
            leaf(103, "text_utf8", Primitive::TextFromUtf8Checked),
            leaf(104, "text_bytes", Primitive::TextAsBytes),
            leaf(105, "bytes_len", Primitive::BytesLen),
            leaf(106, "bytes_concat", Primitive::BytesConcat),
            leaf(107, "bytes_get", Primitive::BytesGet),
            leaf(108, "bytes_slice", Primitive::BytesSlice),
        ],
    )
    .expect("immutable Text/Bytes leaves have no Array machine dependency");

    let errors = TrustedRuntimeManifest::new(
        vec![],
        vec![leaf(109, "bytes_to_array", Primitive::BytesToArray)],
    )
    .unwrap_err();
    assert!(
        messages(errors).iter().any(|message| message.contains(
            "Array-dependent primitive leaves require one Array machine type constructor"
        ))
    );
}

#[test]
fn concrete_text_leaf_identity_requires_both_trusted_declaration_and_call_site() {
    let manifest = manifest(
        vec![],
        vec![leaf(100, "secret_text_len", Primitive::TextByteLen)],
    );
    let standard_library = r#"
        secret_text_len(value: Text) -> usize { () }
        public_text_len(value: Text) -> usize { secret_text_len(move value) }
    "#;
    let artifact = compile_bundle_to_bytecode_with_manifest(
        &bundle(
            standard_library,
            "answer() -> usize { public_text_len(\"abc\") } main() -> () { () }",
        ),
        &manifest,
    )
    .unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::U64(3)
    );

    let primary = "steal() -> usize { secret_text_len(\"abc\") } main() -> () { () }";
    let forged = bundle(standard_library, primary);
    let errors = compile_bundle_to_bytecode_with_manifest(&forged, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| {
            error.message.contains(
                "manifest-bound primitive leaves may be called only from their trusted standard-library source segment",
            )
        })
        .expect("the concrete primitive identity must not cross into an untrusted call site");
    let mapped = forged.map_span(error.span.unwrap()).unwrap();
    assert_eq!(mapped.segment.name(), "main.glorious");
    assert_eq!(&primary[mapped.span.range()], "secret_text_len(\"abc\")");
}

#[test]
fn runtime_manifest_rejects_primitives_outside_the_frozen_slice() {
    let errors = TrustedRuntimeManifest::new(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "add", Primitive::IntCheckedAdd)],
    )
    .unwrap_err();

    assert!(messages(errors).iter().any(|message| {
        message.contains(
            "trusted primitive leaf `add` is outside the generation-1 Text/Bytes/Array frontend slice",
        )
    }));
}

#[test]
fn compilation_requires_every_manifest_leaf_to_exist() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let errors =
        compile_bundle_to_bytecode_with_manifest(&bundle("", "main() -> () { () }"), &manifest)
            .unwrap_err();

    assert!(errors.iter().any(|error| {
        error.span.is_none()
            && error
                .message
                .contains("trusted primitive leaf declaration `secret_birth` is missing")
    }));
}

#[test]
fn a_later_bundle_entry_cannot_forge_primitive_leaf_authority() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let primary = "secret_birth<T>() -> Raw<T> { () }\nmain() -> () { () }";
    let bundle = bundle("", primary);
    let errors = compile_bundle_to_bytecode_with_manifest(&bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| {
            error
                .message
                .contains("explicitly trusted standard-library bundle entry")
        })
        .expect("the forged leaf must be rejected for lack of authority");
    let mapped = bundle.map_span(error.span.unwrap()).unwrap();

    assert_eq!(mapped.segment.name(), "main.glorious");
    assert_eq!(
        &primary[mapped.span.range()],
        "secret_birth<T>() -> Raw<T> { () }"
    );
}

#[test]
fn a_caller_controlled_raw_first_segment_has_no_primitive_leaf_authority() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let forged = "secret_birth<T>() -> Raw<T> { () }";
    let bundle = SourceBundle::raw_for_conformance(
        Segment::new(DISTRIBUTED_STANDARD_LIBRARY_NAME, forged),
        Segment::new("main.glorious", "main() -> () { () }"),
        [],
    );
    let errors = compile_bundle_to_bytecode_with_manifest(&bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| {
            error
                .message
                .contains("explicitly trusted standard-library bundle entry")
        })
        .expect("raw position zero must not acquire distributed-standard authority");
    assert_eq!(
        bundle
            .map_span(error.span.unwrap())
            .unwrap()
            .segment
            .source(),
        forged
    );
}

#[test]
fn repeating_the_standard_library_segment_name_does_not_forge_authority() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let forged = "secret_birth<T>() -> Raw<T> { () }";
    let bundle = SourceBundle::distributed(
        Segment::new("main.glorious", "main() -> () { () }"),
        [Segment::new(DISTRIBUTED_STANDARD_LIBRARY_NAME, forged)],
    );
    let errors = compile_bundle_to_bytecode_with_manifest(&bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| {
            error
                .message
                .contains("explicitly trusted standard-library bundle entry")
        })
        .expect("a repeated segment display name must not recreate its authority identity");
    let mapped = bundle.map_span(error.span.unwrap()).unwrap();

    assert_eq!(mapped.segment.source(), forged);
    assert_eq!(
        mapped.segment.global_range(),
        bundle.segments()[2].global_range()
    );
}

#[test]
fn a_single_source_compile_has_no_implicit_primitive_leaf_authority() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let source = "secret_birth<T>() -> Raw<T> { () }\nmain() -> () { () }";
    let errors =
        compile_source_to_bytecode_with_manifest("forged.glorious", source, &manifest).unwrap_err();

    assert!(errors.iter().any(|error| {
        error.source_name == "forged.glorious"
            && error
                .message
                .contains("explicitly trusted standard-library bundle entry")
    }));
}

#[test]
fn user_code_cannot_call_a_valid_bound_leaf_directly() {
    let manifest = manifest(
        vec![array_type(100, "Raw")],
        vec![leaf(101, "secret_birth", Primitive::ArrayEmpty)],
    );
    let standard_library = "secret_birth<T>() -> Raw<T> { () }";
    let primary = r#"
        steal() -> Raw<i64> { secret_birth() }
        main() -> () { () }
    "#;
    let owned_bundle = bundle(standard_library, primary);
    let errors = compile_bundle_to_bytecode_with_manifest(&owned_bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| {
            error.message.contains(
                "manifest-bound primitive leaves may be called only from their trusted standard-library source segment",
            )
        })
        .expect("a direct user call must be rejected even when the leaf itself is validly bound");
    let mapped = owned_bundle.map_span(error.span.unwrap()).unwrap();

    assert_eq!(mapped.segment.name(), "main.glorious");
    assert_eq!(&primary[mapped.span.range()], "secret_birth()");
}

#[test]
fn machine_type_identity_cannot_be_redeclared_as_a_source_nominal() {
    let manifest = manifest(vec![array_type(100, "Raw")], vec![]);
    let source = "struct Raw<T> { value: T }";
    let bundle = bundle(source, "main() -> () { () }");
    let errors = compile_bundle_to_bytecode_with_manifest(&bundle, &manifest).unwrap_err();

    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("`Raw` is a trusted machine type and cannot be redeclared in source")
    }));
}

#[test]
fn primitive_leaves_require_their_exact_frozen_generic_signatures() {
    let cases = [
        (
            Primitive::CharFromU32Checked,
            "bad(value: u64) -> Char { 'x' }",
        ),
        (Primitive::CharToU32, "bad(value: Char) -> u64 { 0 }"),
        (Primitive::TextByteLen, "bad(value: Bytes) -> usize { 0 }"),
        (
            Primitive::TextConcat,
            "bad(left: Text, right: Bytes) -> Text { left }",
        ),
        (
            Primitive::TextEq,
            "bad(left: Text, right: Text) -> usize { 0 }",
        ),
        (
            Primitive::TextFromUtf8Checked,
            "bad(value: Text) -> Text { value }",
        ),
        (
            Primitive::TextAsBytes,
            "bad(value: Bytes) -> Bytes { value }",
        ),
        (Primitive::BytesLen, "bad(value: Text) -> usize { 0 }"),
        (
            Primitive::BytesConcat,
            "bad(left: Bytes, right: Text) -> Bytes { left }",
        ),
        (
            Primitive::BytesGet,
            "bad(value: Bytes, index: u32) -> u8 { 0 }",
        ),
        (
            Primitive::BytesSlice,
            "bad(value: Bytes, start: usize) -> Bytes { value }",
        ),
        (
            Primitive::BytesFromArrayMove,
            "bad(value: Raw<i64>) -> Bytes { () }",
        ),
        (
            Primitive::BytesToArray,
            "bad(value: Bytes) -> Raw<i64> { () }",
        ),
        (
            Primitive::ArrayNew,
            "bad<T>(length: u32, fill: T) -> Raw<T> where T: Use<[0,infinity]> { () }",
        ),
        (Primitive::ArrayEmpty, "bad<T>(seed: T) -> Raw<T> { () }"),
        (
            Primitive::ArrayLen,
            "bad<T>(value: &mut Raw<T>) -> usize { 0 }",
        ),
        (
            Primitive::ArrayPushMove,
            "bad<T>(value: &Raw<T>, item: T) -> () { () }",
        ),
        (
            Primitive::ArrayPopMove,
            "bad<T>(value: &Raw<T>) -> T { () }",
        ),
        (
            Primitive::ArrayFinishDrained,
            "bad<T>(value: &mut Raw<T>) -> () { () }",
        ),
        (
            Primitive::ArrayGetCopy,
            "bad<T>(value: &mut Raw<T>, index: usize) -> T where T: Use<[0,infinity]> { () }",
        ),
        (
            Primitive::ArrayGetMove,
            "bad<T>(value: &Raw<T>, index: usize) -> T { () }",
        ),
        (
            Primitive::ArrayGetBorrowShared,
            "bad<T>(value: &Raw<T>, index: usize) -> &mut T { () }",
        ),
        (
            Primitive::ArrayGetBorrowUnique,
            "bad<T>(value: &mut Raw<T>, index: usize) -> &T { () }",
        ),
        (
            Primitive::ArraySetMove,
            "bad<T>(value: &mut Raw<T>, item: T, index: usize) -> () { () }",
        ),
        (
            Primitive::ArrayCapacity,
            "bad<T>(value: &mut Raw<T>) -> usize { () }",
        ),
        (
            Primitive::ArrayReserve,
            "bad<T>(value: &Raw<T>, additional: usize) -> () { () }",
        ),
    ];

    for (primitive, declaration) in cases {
        let manifest = manifest(
            vec![array_type(100, "Raw")],
            vec![leaf(101, "bad", primitive)],
        );
        let errors = compile_bundle_to_bytecode_with_manifest(
            &bundle(declaration, "main() -> () { () }"),
            &manifest,
        )
        .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.message.contains("does not match the frozen")
                    && error.message.contains(&format!("{primitive:?}"))
            }),
            "wrong {primitive:?} signature unexpectedly escaped manifest validation: {errors:#?}",
        );
    }
}

#[test]
fn array_element_borrow_origin_blocks_conflicting_mutation_until_end_borrow() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "make_empty", Primitive::ArrayEmpty),
            leaf(102, "append", Primitive::ArrayPushMove),
            leaf(103, "borrow_at", Primitive::ArrayGetBorrowShared),
        ],
    );
    let standard_library = r#"
        infixr 1 else;
        enum Route { Stop, Recur }
        make_empty<T>() -> HiddenArray<T> { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        borrow_at<T>(value: &HiddenArray<T>, index: usize) -> &T { () }
        empty_i64() -> HiddenArray<i64> { make_empty() }
        bad() -> () {
            let values = empty_i64();
            append(&mut values, 1);
            let loan = borrow_at(&values, 0);
            append(&mut values, 2);
            loan;
            ()
        }
    "#;
    let errors = compile_bundle_to_bytecode_with_manifest(
        &bundle(standard_library, "main() -> () { bad() }"),
        &manifest,
    )
    .unwrap_err();

    assert!(
        errors.iter().any(|error| {
            (error.message.contains("borrow") || error.message.contains("loan"))
                && (error.message.contains("active")
                    || error.message.contains("already")
                    || error.message.contains("unique"))
        }),
        "the element reference must retain a loan on its Array origin: {errors:#?}",
    );
}

#[test]
fn specialization_proves_intrinsic_unrestricted_use_for_predefined_scalars() {
    let source = r#"
        scalar_identity<T>(value: T) -> T where T: Use<[0,infinity]> { value }
        answer() -> i64 { scalar_identity(42) }
        main() -> () { answer(); () }
    "#;
    let artifact = grandiose::compile_source_to_bytecode("use.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;

    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn copy_primitives_require_exact_unrestricted_use_evidence() {
    for primitive in [Primitive::ArrayNew, Primitive::ArrayGetCopy] {
        let signature = match primitive {
            Primitive::ArrayNew => "bad<T>(length: usize, fill: T) -> Raw<T>",
            Primitive::ArrayGetCopy => "bad<T>(value: &Raw<T>, index: usize) -> T",
            _ => unreachable!(),
        };
        for suffix in [
            " { () }",
            " where T: Use<[1,infinity]> { () }",
            " where T: Use<[0,1]> { () }",
        ] {
            let declaration = format!("{signature}{suffix}");
            let manifest = manifest(
                vec![array_type(100, "Raw")],
                vec![leaf(101, "bad", primitive)],
            );
            let errors = compile_bundle_to_bytecode_with_manifest(
                &bundle(&declaration, "main() -> () { () }"),
                &manifest,
            )
            .unwrap_err();
            assert!(errors.iter().any(|error| {
                error.message.contains("does not match the frozen")
                    && error.message.contains(&format!("{primitive:?}"))
            }));
        }
    }
}

#[test]
fn complete_array_surface_executes_through_trusted_ordinary_code_with_tracked_borrows() {
    let primitives = [
        ("make_filled", Primitive::ArrayNew),
        ("array_length", Primitive::ArrayLen),
        ("copy_at", Primitive::ArrayGetCopy),
        ("move_at", Primitive::ArrayGetMove),
        ("borrow_at", Primitive::ArrayGetBorrowShared),
        ("borrow_at_mut", Primitive::ArrayGetBorrowUnique),
        ("put_at", Primitive::ArraySetMove),
        ("make_empty", Primitive::ArrayEmpty),
        ("append", Primitive::ArrayPushMove),
        ("remove_last", Primitive::ArrayPopMove),
        ("array_capacity", Primitive::ArrayCapacity),
        ("reserve_more", Primitive::ArrayReserve),
        ("finish", Primitive::ArrayFinishDrained),
    ];
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        primitives
            .iter()
            .enumerate()
            .map(|(index, (name, primitive))| leaf(101 + index as u64, name, *primitive))
            .collect(),
    );
    let standard_library = r#"
        make_filled<T>(length: usize, fill: T) -> HiddenArray<T>
            where T: Use<[0,infinity]> { () }
        array_length<T>(value: &HiddenArray<T>) -> usize { () }
        copy_at<T>(value: &HiddenArray<T>, index: usize) -> T
            where T: Use<[0,infinity]> { () }
        move_at<T>(value: &mut HiddenArray<T>, index: usize) -> T { () }
        borrow_at<T>(value: &HiddenArray<T>, index: usize) -> &T { () }
        borrow_at_mut<T>(value: &mut HiddenArray<T>, index: usize) -> &mut T { () }
        put_at<T>(value: &mut HiddenArray<T>, index: usize, item: T) -> () { () }
        make_empty<T>() -> HiddenArray<T> { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        remove_last<T>(value: &mut HiddenArray<T>) -> T { () }
        array_capacity<T>(value: &HiddenArray<T>) -> usize { () }
        reserve_more<T>(value: &mut HiddenArray<T>, additional: usize) -> () { () }
        finish<T>(value: HiddenArray<T>) -> () { () }
        empty_i64() -> HiddenArray<i64> { make_empty() }

        exercise() -> i64 {
            let values = empty_i64();
            reserve_more(&mut values, 3);
            let reserved = array_capacity(&values);
            append(&mut values, 10);
            append(&mut values, 20);
            let length = array_length(&values);
            { let shared = borrow_at(&values, 0); (); };
            { let unique = borrow_at_mut(&mut values, 1); (); };
            let first = move_at(&mut values, 0);
            put_at(&mut values, 0, 30);
            let copied = copy_at(&values, 0);
            let last = remove_last(&mut values);
            let replacement = move_at(&mut values, 0);
            finish(move values);

            let filled = make_filled(2, 7);
            { let shared_fill = borrow_at(&filled, 0); (); };
            { let unique_fill = borrow_at_mut(&mut filled, 1); (); };
            let fill_copy = copy_at(&filled, 0);
            move_at(&mut filled, 0);
            move_at(&mut filled, 1);
            finish(move filled);
            length;
            reserved;
            first + copied + last + replacement + fill_copy
        }
    "#;
    let bundle = bundle(
        standard_library,
        "answer() -> i64 { exercise() } main() -> () { answer(); () }",
    );
    assert_eq!(
        run_bundle_entry_with_manifest_for_conformance(
            &bundle,
            "answer",
            &mut grandiose::eval::SystemHost::default(),
            &manifest,
        )
        .unwrap(),
        grandiose::eval::Value::Int(97),
        "the recovery interpreter and compiled VM must agree on the complete Array leaf sequence",
    );
    let first = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();
    let second = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();

    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let core = first.core.canonical_text();
    for (_, primitive) in primitives {
        assert!(
            core.contains(&format!("primitive {primitive:?}")),
            "missing {primitive:?} in Core:\n{core}",
        );
    }
    let verified = verify(first.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(97)
    );
}

#[test]
fn source_array_slot_summaries_compose_through_nested_wrappers_at_all_levels() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "make_empty", Primitive::ArrayEmpty),
            leaf(102, "append", Primitive::ArrayPushMove),
            leaf(103, "move_at", Primitive::ArrayGetMove),
            leaf(104, "put_at", Primitive::ArraySetMove),
            leaf(105, "finish", Primitive::ArrayFinishDrained),
            leaf(106, "array_length", Primitive::ArrayLen),
        ],
    );
    let standard_library = r#"
        make_empty<T>() -> HiddenArray<T> { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        move_at<T>(value: &mut HiddenArray<T>, index: usize) -> T { () }
        put_at<T>(value: &mut HiddenArray<T>, index: usize, item: T) -> () { () }
        finish<T>(value: HiddenArray<T>) -> () { () }
        array_length<T>(value: &HiddenArray<T>) -> usize { () }

        take<T>(value: &mut HiddenArray<T>, index: usize) -> T {
            move_at(value, index)
        }
        take_zero<T>(value: &mut HiddenArray<T>) -> T { take(value, 0) }
        restore_zero<T>(value: &mut HiddenArray<T>, item: T) -> () {
            put_at(value, 0, move item)
        }
        close<T>(value: HiddenArray<T>) -> () { finish(move value) }
        empty_i64() -> HiddenArray<i64> { make_empty() }
        effect Ask { [1,1] ask() -> i64 }
        suspend() -> i64 / {Ask} { perform Ask::ask() }
        exercise() -> i64 {
            handle {
                let values = empty_i64();
                append(&mut values, 41);
                let first = take_zero(&mut values);
                restore_zero(&mut values, 42);
                let paused = suspend();
                let answer = take(&mut values, 0);
                close(move values);
                first;
                answer + paused
            } {
                Ask::ask() with continuation => resume(continuation, 0)
            }
        }
    "#;
    let bundle = bundle(
        standard_library,
        "answer() -> i64 { exercise() } main() -> () { answer(); () }",
    );
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_bundle_to_phases_with_manifest_and_options(
            &bundle,
            &manifest,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
        let verified = verify(phases.artifact).unwrap();
        let answer = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified).run(answer, vec![]).unwrap(),
            Value::I64(42)
        );
    }
}

#[test]
fn source_array_slot_summaries_fail_closed_for_invalid_and_opaque_calls() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "make_empty", Primitive::ArrayEmpty),
            leaf(102, "append", Primitive::ArrayPushMove),
            leaf(103, "move_at", Primitive::ArrayGetMove),
            leaf(104, "put_at", Primitive::ArraySetMove),
            leaf(105, "finish", Primitive::ArrayFinishDrained),
            leaf(106, "array_length", Primitive::ArrayLen),
        ],
    );
    let standard_library = r#"
        make_empty<T>() -> HiddenArray<T> { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        move_at<T>(value: &mut HiddenArray<T>, index: usize) -> T { () }
        put_at<T>(value: &mut HiddenArray<T>, index: usize, item: T) -> () { () }
        finish<T>(value: HiddenArray<T>) -> () { () }
        array_length<T>(value: &HiddenArray<T>) -> usize { () }
        take<T>(value: &mut HiddenArray<T>, index: usize) -> T { move_at(value, index) }
        close<T>(value: HiddenArray<T>) -> () { finish(move value) }
        opaque<T>(value: &mut HiddenArray<T>) -> () { () }
        observe_twice<T>(left: &HiddenArray<T>, right: &HiddenArray<T>) -> () {
            array_length(left);
            array_length(right);
            ()
        }
        empty_i64() -> HiddenArray<i64> { make_empty() }
    "#;
    let cases = [
        (
            "double",
            "bad() -> () { let a = empty_i64(); append(&mut a, 1); take(&mut a, 0); take(&mut a, 0); () }",
            "already moved out",
        ),
        (
            "overwrite",
            "bad() -> () { let a = empty_i64(); append(&mut a, 1); put_at(&mut a, 0, 2); () }",
            "overwrites initialized",
        ),
        (
            "bounds",
            "bad() -> () { let a = empty_i64(); append(&mut a, 1); take(&mut a, 1); () }",
            "out-of-bounds",
        ),
        (
            "dynamic-finish",
            "bad(index: usize) -> () { let a = empty_i64(); append(&mut a, 1); take(&mut a, index); close(move a) }",
            "exact proof",
        ),
        (
            "opaque",
            "bad() -> () { let a = empty_i64(); opaque(&mut a); () }",
            "no inferred ownership summary",
        ),
        (
            "alias",
            "bad() -> () { let a = empty_i64(); observe_twice(&a, &a); () }",
            "aliases two summarized owner parameters",
        ),
    ];
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        for (name, primary, expected) in cases {
            let trusted = format!("{standard_library}\n{primary}");
            let reach = if name == "dynamic-finish" {
                "reach(index: usize) -> () { bad(index) } main() -> () { () }"
            } else {
                "reach() -> () { bad() } main() -> () { () }"
            };
            let errors = compile_bundle_to_phases_with_manifest_and_options(
                &bundle(&trusted, reach),
                &manifest,
                CompileOptions {
                    optimization_level: level,
                },
            )
            .unwrap_err();
            assert!(
                errors.iter().any(|error| error.message.contains(expected)),
                "{level:?} {name}: {errors:#?}"
            );
        }
    }
}

#[test]
fn reference_array_slots_cross_exact_read_wrappers_at_all_levels() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "make_empty", Primitive::ArrayEmpty),
            leaf(102, "append", Primitive::ArrayPushMove),
            leaf(103, "pop", Primitive::ArrayPopMove),
            leaf(104, "finish", Primitive::ArrayFinishDrained),
            leaf(105, "move_at", Primitive::ArrayGetMove),
        ],
    );
    let standard_library = r#"
        make_empty<T>() -> HiddenArray<T> { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        pop<T>(value: &mut HiddenArray<T>) -> T { () }
        finish<T>(value: HiddenArray<T>) -> () { () }
        move_at<T>(value: &mut HiddenArray<T>, index: usize) -> T { () }

        empty_refs<'a>() -> HiddenArray<&'a i64> { make_empty() }
        push_ref<'a>(value: &mut HiddenArray<&'a i64>, item: &'a i64) -> () {
            append(value, item)
        }
        relay_push_ref<'a>(value: &mut HiddenArray<&'a i64>, item: &'a i64) -> () {
            push_ref(value, item)
        }
        push_pair_ref<'a>(value: &mut HiddenArray<&'a i64>, item: (i64, &'a i64)) -> () {
            push_ref(value, item.1)
        }
        close_refs<'a>(value: HiddenArray<&'a i64>) -> () { finish(value) }
        pop_ref<'a>(value: &mut HiddenArray<&'a i64>) -> &'a i64 { pop(value) }
        take_last<'a>(value: &mut HiddenArray<&'a i64>) -> &'a i64 {
            pop_ref(value)
        }
    "#;
    let source = bundle(
        standard_library,
        r#"
            keep<'a>(value: &mut HiddenArray<&'a i64>) -> &'a i64 { take_last(value) }
            round_trip<'a>(seed: &'a i64) -> () {
                let values = empty_refs();
                push_pair_ref(&mut values, (7, seed));
                keep(&mut values);
                close_refs(move values)
            }
            main() -> () { () }
        "#,
    );
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_bundle_to_phases_with_manifest_and_options(
            &source,
            &manifest,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
        verify(phases.artifact)
            .unwrap_or_else(|error| panic!("{level:?}: reference array failed: {error:?}"));
    }
}

#[test]
fn dynamic_reference_array_slot_origins_fail_closed_at_all_levels() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "move_at", Primitive::ArrayGetMove),
            leaf(102, "make_empty", Primitive::ArrayEmpty),
            leaf(103, "append", Primitive::ArrayPushMove),
        ],
    );
    let source = bundle(
        r#"
            move_at<T>(value: &mut HiddenArray<T>, index: usize) -> T { () }
            make_empty<T>() -> HiddenArray<T> { () }
            append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
            empty_refs<'a>() -> HiddenArray<&'a i64> { make_empty() }
            take_dynamic<'a>(value: &mut HiddenArray<&'a i64>, index: usize) -> &'a i64 {
                move_at(value, index)
            }
            bad() -> () {
                let seed = 1;
                let values = empty_refs();
                append(&mut values, &seed);
                take_dynamic(&mut values, 0);
                ()
            }
        "#,
        "main() -> () { bad() }",
    );
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let errors = compile_bundle_to_phases_with_manifest_and_options(
            &source,
            &manifest,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1BC999")
                    || error.message.contains("unambiguous")
                    || error.message.contains("verification")
                    || error
                        .message
                        .contains("cannot place a reference origin at an unknown array index")
            }),
            "{level:?}: {errors:#?}"
        );
    }
}

#[test]
fn arbitrary_manifest_names_lower_to_core_primitive_identities_behind_a_private_wrapper() {
    let manifest = manifest(
        vec![array_type(100, "SecretBuffer")],
        vec![
            leaf(101, "birth", Primitive::ArrayEmpty),
            leaf(102, "seal", Primitive::ArrayFinishDrained),
        ],
    );
    let standard_library = r#"
        birth<T>() -> SecretBuffer<T> { () }
        seal<T>(value: SecretBuffer<T>) -> () { () }

        struct VecI64 { private storage: SecretBuffer<i64> }
        vec_new() -> VecI64 { VecI64 { storage: birth() } }
        vec_finish(value: VecI64) -> () {
            let VecI64 { storage } = value;
            seal(move storage)
        }
    "#;
    let bundle = bundle(standard_library, "main() -> () { vec_finish(vec_new()) }");
    let phases = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();
    let core = phases.core.canonical_text();

    assert!(core.contains("primitive ArrayEmpty"), "{core}");
    assert!(core.contains("primitive ArrayFinishDrained"), "{core}");
    let artifact = verify(phases.artifact).unwrap();
    let main = artifact
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "main")
        .unwrap() as u32;
    assert_eq!(Vm::new(artifact).run(main, vec![]).unwrap(), Value::Unit);
}

#[test]
fn user_code_cannot_project_the_private_storage_behind_a_wrapper() {
    let manifest = manifest(
        vec![array_type(100, "SecretBuffer")],
        vec![leaf(101, "birth", Primitive::ArrayEmpty)],
    );
    let standard_library = r#"
        birth<T>() -> SecretBuffer<T> { () }
        struct VecI64 { private storage: SecretBuffer<i64> }
        vec_new() -> VecI64 { VecI64 { storage: birth() } }
    "#;
    let primary = r#"
        steal(value: VecI64) -> SecretBuffer<i64> { value.storage }
        main() -> () { () }
    "#;
    let owned_bundle = bundle(standard_library, primary);
    let errors = compile_bundle_to_bytecode_with_manifest(&owned_bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| error.message.contains("private field `storage`"))
        .expect("the ordinary wrapper's storage must retain its declaring entry's privacy");
    let mapped = owned_bundle.map_span(error.span.unwrap()).unwrap();

    assert_eq!(mapped.segment.name(), "main.glorious");
    assert_eq!(&primary[mapped.span.range()], "value.storage");
    assert!(error.related.iter().any(|(span, _)| {
        owned_bundle
            .map_span(*span)
            .is_some_and(|mapped| mapped.segment.name() == "std.glorious")
    }));

    let reference_primary = r#"
        steal_ref(value: &VecI64) -> &SecretBuffer<i64> { &value.storage }
        main() -> () { () }
    "#;
    let reference_bundle = bundle(standard_library, reference_primary);
    let errors =
        compile_bundle_to_bytecode_with_manifest(&reference_bundle, &manifest).unwrap_err();
    let error = errors
        .iter()
        .find(|error| error.message.contains("private field `storage`"))
        .expect("reference-root projection must retain the wrapper's private authority");
    let mapped = reference_bundle.map_span(error.span.unwrap()).unwrap();
    assert_eq!(mapped.segment.name(), "main.glorious");
    assert_eq!(&reference_primary[mapped.span.range()], "value.storage");
}

#[test]
fn nested_arrays_move_through_every_leaf_deterministically() {
    let manifest = manifest(
        vec![array_type(900, "Storage")],
        vec![
            leaf(905, "close_storage", Primitive::ArrayFinishDrained),
            leaf(901, "empty_storage", Primitive::ArrayEmpty),
            leaf(904, "remove_last", Primitive::ArrayPopMove),
            leaf(902, "storage_length", Primitive::ArrayLen),
            leaf(903, "append_value", Primitive::ArrayPushMove),
        ],
    );
    let standard_library = r#"
        empty_storage<T>() -> Storage<T> { () }
        storage_length<T>(value: &Storage<T>) -> usize { () }
        append_value<T>(value: &mut Storage<T>, item: T) -> () { () }
        remove_last<T>(value: &mut Storage<T>) -> T { () }
        close_storage<T>(value: Storage<T>) -> () { () }

        empty_i64() -> Storage<i64> { empty_storage() }
        empty_nested() -> Storage<Storage<i64>> { empty_storage() }
        round_trip() -> i64 {
            let inner = empty_i64();
            append_value(&mut inner, 42);
            let outer = empty_nested();
            append_value(&mut outer, move inner);
            storage_length(&outer);
            let recovered = remove_last(&mut outer);
            close_storage(move outer);
            let answer = remove_last(&mut recovered);
            close_storage(move recovered);
            answer
        }
    "#;
    let bundle = bundle(
        standard_library,
        "answer() -> i64 { round_trip() } main() -> () { answer(); () }",
    );
    let first = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();
    let second = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();

    assert_eq!(first.core_fingerprint(), second.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), second.mir_fingerprint());
    assert_eq!(first.artifact.encode(), second.artifact.encode());
    let core = first.core.canonical_text();
    for primitive in [
        Primitive::ArrayEmpty,
        Primitive::ArrayLen,
        Primitive::ArrayPushMove,
        Primitive::ArrayPopMove,
        Primitive::ArrayFinishDrained,
    ] {
        assert!(
            core.contains(&format!("primitive {primitive:?}")),
            "missing {primitive:?} in Core:\n{core}",
        );
    }

    let verified = verify(first.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_vec_wrapper_transfers_an_exact_linear_element_end_to_end() {
    let manifest = manifest(
        vec![array_type(100, "Storage")],
        vec![
            leaf(101, "empty_storage", Primitive::ArrayEmpty),
            leaf(102, "append_value", Primitive::ArrayPushMove),
            leaf(103, "remove_last", Primitive::ArrayPopMove),
            leaf(104, "close_storage", Primitive::ArrayFinishDrained),
        ],
    );
    let standard_library = r#"
        empty_storage<T>() -> Storage<T> { () }
        append_value<T>(value: &mut Storage<T>, item: T) -> () { () }
        remove_last<T>(value: &mut Storage<T>) -> T { () }
        close_storage<T>(value: Storage<T>) -> () { () }

        struct Vec<T> { private storage: Storage<T> }
        vec_new<T>() -> Vec<T> { Vec { storage: empty_storage() } }
        vec_push<T>(value: Vec<T>, item: T) -> Vec<T> {
            let Vec { storage } = value;
            append_value(&mut storage, move item);
            Vec { storage: move storage }
        }
        vec_pop<T>(value: Vec<T>) -> (Vec<T>, T) {
            let Vec { storage } = value;
            let item = remove_last(&mut storage);
            (Vec { storage: move storage }, move item)
        }
        vec_finish<T>(value: Vec<T>) -> () {
            let Vec { storage } = value;
            close_storage(move storage)
        }

        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        make_ticket_vec() -> Vec<Ticket> { vec_new() }
        exercise_vec() -> i64 {
            let values = vec_push(make_ticket_vec(), Ticket { serial: 42 });
            let result = vec_pop(move values);
            let (empty, ticket) = result;
            let Ticket { serial } = ticket;
            vec_finish(move empty);
            serial
        }
    "#;
    let bundle = bundle(
        standard_library,
        "answer() -> i64 { exercise_vec() } main() -> () { answer(); () }",
    );
    let phases = compile_bundle_to_phases_with_manifest(&bundle, &manifest).unwrap();
    let verified = verify(phases.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;

    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn generic_private_array_wrapper_projects_borrows_through_reference_roots() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "make_empty", Primitive::ArrayEmpty),
            leaf(102, "array_length", Primitive::ArrayLen),
            leaf(103, "reserve_more", Primitive::ArrayReserve),
            leaf(104, "append", Primitive::ArrayPushMove),
            leaf(105, "borrow_at", Primitive::ArrayGetBorrowShared),
            leaf(106, "borrow_at_mut", Primitive::ArrayGetBorrowUnique),
        ],
    );
    let standard_library = r#"
        make_empty<T>() -> HiddenArray<T> { () }
        array_length<T>(value: &HiddenArray<T>) -> usize { () }
        reserve_more<T>(value: &mut HiddenArray<T>, additional: usize) -> () { () }
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        borrow_at<T>(value: &HiddenArray<T>, index: usize) -> &T { () }
        borrow_at_mut<T>(value: &mut HiddenArray<T>, index: usize) -> &mut T { () }

        struct Buffer<T> { private storage: HiddenArray<T> }
        buffer_new<T>() -> Buffer<T> { Buffer { storage: make_empty() } }
        buffer_new_i64() -> Buffer<i64> { buffer_new() }
        buffer_len<T>(value: &Buffer<T>) -> usize {
            array_length(&value.storage)
        }
        buffer_reserve<T>(value: &mut Buffer<T>, additional: usize) -> () {
            reserve_more(&mut value.storage, additional)
        }
        buffer_push<T>(value: &mut Buffer<T>, item: T) -> () {
            append(&mut value.storage, move item)
        }
        buffer_get<'a, T>(value: &'a Buffer<T>, index: usize) -> &'a T {
            borrow_at(&value.storage, index)
        }
        buffer_get_elided<T>(value: &Buffer<T>, index: usize) -> &T {
            borrow_at(&value.storage, index)
        }
        buffer_get_mut<'a, T>(value: &'a mut Buffer<T>, index: usize) -> &'a mut T {
            borrow_at_mut(&mut value.storage, index)
        }
        buffer_get_mut_elided<T>(value: &mut Buffer<T>, index: usize) -> &mut T {
            borrow_at_mut(&mut value.storage, index)
        }

        exercise() -> usize {
            let values = buffer_new_i64();
            buffer_reserve(&mut values, 4);
            buffer_push(&mut values, 42);
            let length = buffer_len(&values);
            let shared = buffer_get(&values, 0);
            shared;
            let elided = buffer_get_elided(&values, 0);
            elided;
            { let unique = buffer_get_mut(&mut values, 0); unique; (); };
            { let unique = buffer_get_mut_elided(&mut values, 0); unique; (); };
            length
        }
    "#;
    let phases = compile_bundle_to_phases_with_manifest(
        &bundle(
            standard_library,
            "answer() -> usize { exercise() } main() -> () { answer(); () }",
        ),
        &manifest,
    )
    .unwrap();
    let verified = verify(phases.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::U64(1)
    );
}

#[test]
fn projected_element_loan_suspends_unique_wrapper_reference_and_regions_reject_ambiguity() {
    let manifest = manifest(
        vec![array_type(100, "HiddenArray")],
        vec![
            leaf(101, "append", Primitive::ArrayPushMove),
            leaf(102, "borrow_at_mut", Primitive::ArrayGetBorrowUnique),
        ],
    );
    let standard_library = r#"
        append<T>(value: &mut HiddenArray<T>, item: T) -> () { () }
        borrow_at_mut<T>(value: &mut HiddenArray<T>, index: usize) -> &mut T { () }
        struct Buffer<T> { private storage: HiddenArray<T> }
        buffer_push<T>(value: &mut Buffer<T>, item: T) -> () {
            append(&mut value.storage, move item)
        }
        buffer_get_mut<'a, T>(value: &'a mut Buffer<T>, index: usize) -> &'a mut T {
            borrow_at_mut(&mut value.storage, index)
        }
        bad(value: &mut Buffer<i64>) -> () {
            let element = buffer_get_mut(&mut *value, 0);
            buffer_push(&mut *value, 1);
            element;
            ()
        }
    "#;
    let errors = compile_bundle_to_bytecode_with_manifest(
        &bundle(
            standard_library,
            "reach(value: &mut Buffer<i64>) -> () { bad(value) } main() -> () { () }",
        ),
        &manifest,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("suspended") || error.message.contains("live loan")
        }),
        "a returned projected element loan must suspend its unique wrapper parent: {errors:#?}"
    );

    let ambiguous = r#"
        choose<'a>(select_first: i64, value: (&'a i64, &'a i64)) -> &'a i64 {
            if(select_first == 0) { value.0 } else { value.1 }
        }
        bad<'a>(value: (&'a i64, &'a i64)) -> &'a i64 { choose(0, move value) }
        main() -> () { () }
    "#;
    let errors =
        grandiose::compile_source_to_bytecode("ambiguous-regions.glorious", ambiguous).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("exactly one region-compatible reference argument")
                || error
                    .message
                    .contains("unambiguous structural argument mapping")
                || error.message.contains("reference return summary")
        }),
        "unproven multi-reference returns must remain ambiguous: {errors:#?}"
    );
}

#[test]
fn an_array_of_exact_linear_elements_cannot_be_abandoned_even_when_empty() {
    let manifest = manifest(
        vec![array_type(100, "Storage")],
        vec![leaf(101, "empty_storage", Primitive::ArrayEmpty)],
    );
    let standard_library = r#"
        empty_storage<T>() -> Storage<T> { () }
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        empty_tickets() -> Storage<Ticket> { empty_storage() }
    "#;
    let primary = "bad() -> () { empty_tickets(); () } main() -> () { () }";
    let bundle = bundle(standard_library, primary);
    let errors = compile_bundle_to_bytecode_with_manifest(&bundle, &manifest).unwrap_err();

    assert!(
        errors.iter().any(|error| {
            error.span.is_some()
                && (error.message.contains("cannot be discarded")
                    || error.message.contains("requires at least 1 owned use")
                    || error
                        .message
                        .contains("actual Use count 0, outside principal interval [1,1]"))
        }),
        "an empty shell must retain its element type's must-move obligation: {errors:#?}",
    );
}
