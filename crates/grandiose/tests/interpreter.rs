use grandiose::{
    GenericParameterKind, MachineTypeRole, ManifestMachineType, ManifestPrimitiveLeaf,
    TrustedRuntimeManifest, TrustedTraitManifest,
    diagnostic::Diagnostic,
    eval::{Host, Value},
    run_bundle, run_bundle_entry_with_manifest_for_conformance, run_source,
    source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_NAME, Segment, SourceBundle},
    span::Span,
};
use grandiose_vm::Primitive;

#[derive(Default)]
struct TestHost {
    lines: Vec<String>,
    host_calls: Vec<(String, String)>,
    writes: Vec<(String, Vec<u8>)>,
    diagnostics: Vec<String>,
}

#[test]
fn distributed_array_leaf_identity_is_authorized_only_inside_the_canonical_std_segment() {
    let errors = run_source(
        "forged-array-leaf.glorious",
        "main() -> Array<i64> { __g1_array_empty() }",
        vec![],
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert!(errors.iter().any(|error| {
        error
            .message
            .contains("manifest-bound runtime primitive leaves may be called only")
    }));

    let copied_name = SourceBundle::raw_for_conformance(
        Segment::new(
            DISTRIBUTED_STANDARD_LIBRARY_NAME,
            "__g1_array_empty<T>() -> Array<T> { () }",
        ),
        Segment::new(
            "main.glorious",
            "main() -> Array<i64> { __g1_array_empty() }",
        ),
        [],
    );
    assert_eq!(
        run_bundle(&copied_name, vec![], &mut TestHost::default()).unwrap(),
        Value::Unit,
        "copying the trusted segment's display name must execute an ordinary dummy body, not an Array primitive",
    );
}

#[test]
fn associated_alias_to_array_leaf_retains_user_call_authority() {
    let source = r#"
        struct Wrapper { marker: () }
        let Wrapper::empty = __g1_array_empty;
        main() -> Array<i64> { Wrapper::empty() }
    "#;
    let error = run_source(
        "forged-array-leaf-alias.glorious",
        source,
        vec![],
        &mut TestHost::default(),
    )
    .unwrap_err()
    .into_iter()
    .find(|error| {
        error
            .message
            .contains("manifest-bound runtime primitive leaves may be called only")
    })
    .expect("an associated alias must not move a user call into the trusted authority domain");
    let span = error
        .span
        .expect("the authority rejection must identify the user call site");
    assert_eq!(error.source_name, "forged-array-leaf-alias.glorious");
    assert_eq!(&source[span.range()], "Wrapper::empty()");
}

#[test]
fn trusted_text_bytes_calls_dispatch_by_identity_and_copied_names_stay_inert() {
    let leaves = [
        (1, "text_len", Primitive::TextByteLen),
        (2, "__g1_text_concat", Primitive::TextConcat),
        (3, "text_equal", Primitive::TextEq),
        (4, "text_from_utf8", Primitive::TextFromUtf8Checked),
        (5, "text_as_bytes", Primitive::TextAsBytes),
        (6, "bytes_len", Primitive::BytesLen),
        (7, "bytes_cat", Primitive::BytesConcat),
        (8, "bytes_get", Primitive::BytesGet),
        (9, "bytes_slice", Primitive::BytesSlice),
        (10, "bytes_from_array", Primitive::BytesFromArrayMove),
        (11, "bytes_to_array", Primitive::BytesToArray),
    ];
    let runtime = TrustedRuntimeManifest::new(
        vec![ManifestMachineType {
            id: 20,
            display_name: "HiddenArray".into(),
            parameters: vec![GenericParameterKind::Type],
            role: MachineTypeRole::Array,
        }],
        leaves
            .iter()
            .map(|(id, name, primitive)| ManifestPrimitiveLeaf {
                id: *id,
                display_name: (*name).into(),
                primitive: *primitive,
            })
            .collect(),
    )
    .unwrap();
    let manifest = TrustedTraitManifest::trusted_default().with_runtime(runtime);
    let standard = r#"
        text_len(value: Text) -> usize { () }
        __g1_text_concat(left: Text, right: Text) -> Text { () }
        text_equal(left: Text, right: Text) -> u32 { () }
        text_from_utf8(value: Bytes) -> Text { () }
        text_as_bytes(value: Text) -> Bytes { () }
        bytes_len(value: Bytes) -> usize { () }
        bytes_cat(left: Bytes, right: Bytes) -> Bytes { () }
        bytes_get(value: Bytes, index: usize) -> u8 { () }
        bytes_slice(value: Bytes, start: usize, end: usize) -> Bytes { () }
        bytes_from_array(value: HiddenArray<u8>) -> Bytes { () }
        bytes_to_array(value: Bytes) -> HiddenArray<u8> { () }

        unicode_len() -> usize { text_len("a😀") }
        equality() -> u32 { text_equal(__g1_text_concat("grand", "iose"), "grandiose") }
        selected_byte() -> u8 {
            bytes_get(bytes_slice(text_as_bytes("abcd"), 1, 4), 1)
        }
        round_trip_len() -> usize {
            bytes_len(bytes_from_array(bytes_to_array(text_as_bytes("hé"))))
        }
        utf8_round_trip() -> Text { text_from_utf8(text_as_bytes("valid")) }
    "#;
    let bundle = SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("std.glorious", standard),
        Segment::new("main.glorious", "main() -> () { () }"),
        [],
    );
    let mut host = TestHost::default();
    for (entry, expected) in [
        ("unicode_len", Value::Int(5)),
        ("equality", Value::Int(1)),
        ("selected_byte", Value::Int(i64::from(b'c'))),
        ("round_trip_len", Value::Int(3)),
        ("utf8_round_trip", Value::String("valid".into())),
    ] {
        assert_eq!(
            run_bundle_entry_with_manifest_for_conformance(&bundle, entry, &mut host, &manifest)
                .unwrap(),
            expected,
            "trusted entry {entry} must execute its manifest-bound primitives",
        );
    }

    let copied = SourceBundle::raw_for_conformance(
        Segment::new(
            DISTRIBUTED_STANDARD_LIBRARY_NAME,
            "__g1_text_concat(left: Text, right: Text) -> Text { () }",
        ),
        Segment::new(
            "main.glorious",
            "main() -> Text { __g1_text_concat(\"not \" , \"primitive\") }",
        ),
        [],
    );
    assert_eq!(
        run_bundle(&copied, vec![], &mut TestHost::default()).unwrap(),
        Value::Unit,
        "copying a Text primitive display name must execute its ordinary source body",
    );
}

#[test]
fn associated_alias_to_text_leaf_retains_the_user_call_site_authority() {
    let source = r#"
        struct Wrapper { marker: () }
        let Wrapper::concat = __g1_text_concat;
        main() -> Text { Wrapper::concat("forged", " call") }
    "#;
    let error = run_source(
        "forged-text-leaf-alias.glorious",
        source,
        vec![],
        &mut TestHost::default(),
    )
    .unwrap_err()
    .into_iter()
    .find(|error| {
        error
            .message
            .contains("manifest-bound runtime primitive leaves may be called only")
    })
    .expect("an associated alias must not grant Text primitive authority");
    let span = error
        .span
        .expect("the authority rejection must identify the user alias call");
    assert_eq!(error.source_name, "forged-text-leaf-alias.glorious");
    assert_eq!(
        &source[span.range()],
        "Wrapper::concat(\"forged\", \" call\")"
    );
}

#[test]
fn canonical_public_text_bytes_and_vec_wrappers_execute_in_recovery() {
    let result = run_source(
        "public-text-bytes-recovery.glorious",
        r#"
            byte(value: u8) -> u8 { value }
            main() -> usize {
                let unicode = "a😀";
                let unicode_len = String::byte_len(&unicode);
                let joined = String::concat("grand", "iose");
                let joined_len = String::byte_len(&joined);
                let text = "hé";
                let text_bytes = String::as_bytes(&text);
                let text_bytes_len = Bytes::len(&text_bytes);
                let same_left = "same";
                let same_right = "same";
                let equal_score = if(String::eq(&same_left, &same_right)) {
                    1
                } else {
                    1000
                };
                let different = "different";
                let unequal_score = if(String::eq(&same_left, &different)) {
                    1000
                } else {
                    2
                };
                let left_text = "ab";
                let right_text = "cde";
                let left = String::as_bytes(&left_text);
                let right = String::as_bytes(&right_text);
                let joined_bytes = Bytes::concat(move left, move right);
                let joined_bytes_len = Bytes::len(&joined_bytes);

                let values = Vec::with_capacity(8);
                Vec::push(&mut values, byte(65));
                Vec::push(&mut values, byte(66));
                let bytes = Bytes::from_vec(move values);
                let restored = Bytes::to_vec(move bytes);
                let restored_len = Vec::len(&restored);
                let restored_capacity = Vec::capacity(&restored);
                let first = *Vec::index(&restored, 0);
                let second = *Vec::index(&restored, 1);
                unicode_len + joined_len + text_bytes_len + joined_bytes_len
                    + restored_len + restored_capacity
                    + equal_score + unequal_score
            }
        "#,
        vec![],
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(29));
}

impl Host for TestHost {
    fn perform(
        &mut self,
        effect: &str,
        operation: &str,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value, Diagnostic> {
        match (effect, operation, args.as_slice()) {
            ("fs.read", "read", [Value::String(path)]) => {
                self.host_calls.push((effect.into(), operation.into()));
                Ok(Value::Bytes(format!("contents:{path}").into_bytes().into()))
            }
            ("fs.write", "write", [Value::String(path), Value::Bytes(contents)]) => {
                self.host_calls.push((effect.into(), operation.into()));
                self.writes
                    .push((path.to_string(), contents.as_ref().to_vec()));
                Ok(Value::Unit)
            }
            ("diagnostic", "write", [Value::String(message)]) => {
                self.host_calls.push((effect.into(), operation.into()));
                self.diagnostics.push(message.to_string());
                Ok(Value::Unit)
            }
            ("Console", "write_line", [Value::String(line)]) => {
                self.lines.push(line.to_string());
                Ok(Value::Unit)
            }
            _ => Err(Diagnostic::error("test host", "unexpected operation", span)),
        }
    }
}

#[test]
fn manifest_host_leaves_preserve_args_and_invoke_the_exact_host_surface() {
    let mut host = TestHost::default();
    let args = run_source(
        "host-process-args.glorious",
        "main() -> Array<Text> { __g1_process_args_get() }",
        vec!["compiler.glorious".into(), "--emit".into()],
        &mut host,
    )
    .unwrap();
    assert!(matches!(args, Value::Array(_)));
    assert_eq!(
        format!("{args:?}"),
        "Array(Array { len: 2, capacity: 2, initialized: 2 })"
    );

    let result = run_source(
        "host-file-io.glorious",
        r#"
            struct HostAlias { marker: () }
            let HostAlias::read = __g1_fs_read;
            main() -> () {
                let contents = HostAlias::read("input.glorious");
                __g1_fs_write("output.g1bc", contents);
                __g1_diagnostic_write("compiled\n")
            }
        "#,
        vec![],
        &mut host,
    )
    .unwrap();
    assert_eq!(result, Value::Unit);
    assert_eq!(
        host.host_calls,
        [
            ("fs.read".into(), "read".into()),
            ("fs.write".into(), "write".into()),
            ("diagnostic".into(), "write".into()),
        ]
    );
    assert_eq!(
        host.writes,
        [("output.g1bc".into(), b"contents:input.glorious".to_vec())]
    );
    assert_eq!(host.diagnostics, ["compiled\n"]);
}

#[test]
fn public_compiler_host_runner_accepts_a_named_function_item_in_recovery() {
    let mut host = TestHost::default();
    let source = r#"
        compiler_main() -> () / {ProcessArgs, FileRead, FileWrite, Diagnostic} {
            let arguments = process_args();
            Vec::len(&arguments);
            let contents = read_file("input.glorious");
            write_file("output.g1bc", move contents);
            write_diagnostic("compiled\n")
        }
        main() -> () { run_compiler_host(compiler_main) }
    "#;
    assert_eq!(
        run_source(
            "public-compiler-host.glorious",
            source,
            vec!["compiler.glorious".into(), "--emit".into()],
            &mut host,
        )
        .unwrap(),
        Value::Unit
    );
    assert_eq!(
        host.host_calls,
        [
            ("fs.read".into(), "read".into()),
            ("fs.write".into(), "write".into()),
            ("diagnostic".into(), "write".into()),
        ]
    );
    assert_eq!(
        host.writes,
        [("output.g1bc".into(), b"contents:input.glorious".to_vec())]
    );
    assert_eq!(host.diagnostics, ["compiled\n"]);
}

#[test]
fn copied_host_leaf_names_have_no_authority() {
    let copied = SourceBundle::raw_for_conformance(
        Segment::new(
            DISTRIBUTED_STANDARD_LIBRARY_NAME,
            "__g1_fs_read(path: Text) -> Bytes { () }",
        ),
        Segment::new(
            "main.glorious",
            "main() -> Bytes { __g1_fs_read(\"not-read\") }",
        ),
        [],
    );
    let mut host = TestHost::default();
    assert_eq!(run_bundle(&copied, vec![], &mut host).unwrap(), Value::Unit);
    assert!(host.host_calls.is_empty());
}

#[test]
fn host_leaf_faults_propagate_without_becoming_grandiose_effects() {
    #[derive(Default)]
    struct FaultHost;
    impl Host for FaultHost {
        fn perform(
            &mut self,
            effect: &str,
            operation: &str,
            _args: Vec<Value>,
            span: Span,
        ) -> Result<Value, Diagnostic> {
            Err(Diagnostic::error(
                "host fault",
                format!("{effect}/{operation} failed"),
                span,
            ))
        }
    }

    let error = run_source(
        "host-fault.glorious",
        "main() -> Bytes { __g1_fs_read(\"missing\") }",
        vec![],
        &mut FaultHost,
    )
    .unwrap_err()
    .into_iter()
    .next()
    .unwrap();
    assert_eq!(error.title, "host fault");
    assert_eq!(error.message, "fs.read/read failed");

    let public_error = run_source(
        "public-host-fault.glorious",
        r#"
            compiler_main() -> () / {FileRead} {
                read_file("missing");
                ()
            }
            main() -> () { run_compiler_host(compiler_main) }
        "#,
        vec![],
        &mut FaultHost,
    )
    .unwrap_err()
    .into_iter()
    .next()
    .unwrap();
    assert_eq!(public_error.title, "host fault");
    assert_eq!(public_error.message, "fs.read/read failed");
}

#[test]
fn recovery_system_host_hardens_only_the_exact_g1_file_and_diagnostic_surface() {
    let directory = tempfile::tempdir().unwrap();
    std::fs::write(directory.path().join("output.g1bc"), b"old").unwrap();

    let limits = grandiose_vm::HostLimits {
        max_file_bytes: 3,
        max_diagnostic_bytes: 3,
        ..grandiose_vm::HostLimits::default()
    };
    let mut host = grandiose::eval::SystemHost::with_limits(limits);
    host.working_directory = directory.path().to_owned();

    assert_eq!(
        host.perform(
            "fs.write",
            "write",
            vec![
                Value::String("output.g1bc".into()),
                Value::Bytes(b"new".to_vec().into()),
            ],
            Span::default(),
        )
        .unwrap(),
        Value::Unit
    );
    assert_eq!(
        std::fs::read(directory.path().join("output.g1bc")).unwrap(),
        b"new"
    );
    assert!(
        std::fs::read_dir(directory.path())
            .unwrap()
            .all(|entry| !entry
                .unwrap()
                .file_name()
                .to_string_lossy()
                .starts_with(".grandiose-write-")),
        "the atomic replacement must not leave its private temporary file behind"
    );

    let write_fault = host
        .perform(
            "fs.write",
            "write",
            vec![
                Value::String("output.g1bc".into()),
                Value::Bytes(b"four".to_vec().into()),
            ],
            Span::default(),
        )
        .unwrap_err();
    assert_eq!(
        write_fault.message,
        "fs.write: contents exceed per-call byte limit of 3"
    );
    assert_eq!(
        std::fs::read(directory.path().join("output.g1bc")).unwrap(),
        b"new",
        "a rejected replacement must leave the destination intact"
    );

    let diagnostic_fault = host
        .perform(
            "diagnostic",
            "write",
            vec![Value::String("four".into())],
            Span::default(),
        )
        .unwrap_err();
    assert_eq!(
        diagnostic_fault.message,
        "diagnostic.write: message exceeds per-call byte limit of 3"
    );

    // The historical evaluator effects intentionally retain their prior behavior and are not
    // constrained by the bytecode ABI's G1 limits.
    assert_eq!(
        host.perform(
            "Files",
            "write_string",
            vec![
                Value::String("legacy.txt".into()),
                Value::String("longer than three bytes".into()),
            ],
            Span::default(),
        )
        .unwrap(),
        Value::Unit
    );
    assert_eq!(
        std::fs::read_to_string(directory.path().join("legacy.txt")).unwrap(),
        "longer than three bytes"
    );
}

#[test]
fn evaluates_calls_bindings_operators_and_effects() {
    let source = r#"
        effect Console { [1,1] write_line(text: &str) ->; }
        twice(value: i64) -> i64 { value * 2 }
        main() -> / {Console} {
            let answer = twice(20) + 2;
            perform Console::write_line(core::int_to_string(answer));
            answer
        }
    "#;
    let mut host = TestHost::default();
    let result = run_source("test.gr", source, Vec::new(), &mut host).unwrap();
    assert_eq!(result, Value::Int(42));
    assert_eq!(host.lines, ["42"]);
}

#[test]
fn associated_callable_aliases_execute_as_ordinary_generic_functions() {
    let source = r#"
        struct Box<T> { private value: T }
        alias_identity<T>(value: T) -> T { value }
        let Box::identity = alias_identity;
        let Box::again = Box::identity;
        main() -> i64 { Box::again(42) }
    "#;
    let result = run_source(
        "associated-callable-alias.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn reference_root_struct_fields_read_and_borrow_the_projected_value() {
    let source = r#"
        struct Inner { item: i64 }
        struct Outer { inner: Inner }
        read(value: &Outer) -> i64 { value.inner.item }
        project<'a>(value: &'a Outer) -> &'a i64 { &value.inner.item }
        read_reference(value: &i64) -> i64 { *value }
        main() -> i64 {
            let value = Outer { inner: Inner { item: 42 } };
            let direct = read(&value);
            direct + read_reference(project(&value)) - 42
        }
    "#;
    assert_eq!(
        run_source(
            "reference-root-field.gr",
            source,
            Vec::new(),
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn straight_line_local_borrow_cases_match_the_compiled_vm_cases() {
    let source = r#"
        take_shared(value: &i64) -> { () }
        take_unique(value: &mut i64) -> { () }
        main() -> i64 {
            let value = 40;
            take_shared(&value);
            let unique = &mut value;
            take_unique(unique);
            value + 2
        }
    "#;
    assert_eq!(
        run_source(
            "borrow-differential.gr",
            source,
            vec![],
            &mut TestHost::default()
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn assignment_mutates_addressable_local_and_projected_storage() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        main() -> i64 {
            let value = Pair { left: 1, right: 2 };
            value.left = 40;
            value.right = value.right + 1;
            value.left + value.right - 1
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-local-assignment.gr",
            source,
            vec![],
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn assignment_through_unique_reference_updates_original_local() {
    let source = r#"
        write(value: &mut i64) -> { *value = 42; }
        main() -> i64 {
            let value = 1;
            write(&mut value);
            value
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-reference-assignment.gr",
            source,
            vec![],
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn moved_local_can_be_reinitialized_without_destroying_the_hole() {
    let source = r#"
        main() -> i64 {
            let value = 40;
            let old = move value;
            value = 2;
            old + value
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-reinitialize.gr",
            source,
            vec![],
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn unique_reference_survives_deref_move_until_store_reinitializes_its_hole() {
    let source = r#"
        replace_for_recovery_test(value: &mut i64) -> i64 {
            let old = move *value;
            *value = 2;
            old
        }
        main() -> i64 {
            let value = 40;
            replace_for_recovery_test(&mut value) + value
        }
    "#;
    assert_eq!(
        run_source(
            "recovery-deref-move-store.gr",
            source,
            vec![],
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn reports_source_spans_for_runtime_failures() {
    let source = "main() -> i64 { 10 / 0 }";
    let error = run_source("bad.gr", source, Vec::new(), &mut TestHost::default())
        .unwrap_err()
        .remove(0);
    assert_eq!(error.title, "runtime error");
    assert!(error.span.is_some());
    assert!(error.message.contains("division by zero"));
}

#[test]
fn evaluates_checked_unary_negation() {
    let source = "main() -> i64 { -42 }";
    let result = run_source(
        "unary-negation.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(-42));
}

#[test]
fn evaluates_shared_and_unique_borrow_dereference() {
    let source = r#"
        shared(value: &i64) -> i64 { *value }
        unique(value: &mut i64) -> i64 { *value }
        reborrow_shared(value: &mut i64) -> i64 {
            let shared_again = &*value;
            *shared_again
        }
        reborrow_unique(value: &mut i64) -> i64 {
            let unique_again = &mut *value;
            *unique_again
        }
        main() -> i64 {
            let answer = 42;
            shared(&answer) + unique(&mut answer) +
                reborrow_shared(&mut answer) + reborrow_unique(&mut answer) - 126
        }
    "#;
    let result = run_source(
        "references.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn rejects_unique_reborrow_from_shared_reference() {
    let source = r#"
        invalid(value: &i64) -> i64 {
            let unique = &mut *value;
            *unique
        }
        main() -> i64 { invalid(&42) }
    "#;
    let error = run_source(
        "invalid-reborrow.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert!(error.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("cannot create a unique reborrow from a shared reference")
    }));
}

#[test]
fn custom_drop_runs_before_reverse_structural_destruction() {
    let outer_first = r#"
        struct Inner {}
        struct Outer { inner: Inner }
        impl Drop for Inner {
            drop(&mut self) -> { missing_inner() }
        }
        impl Drop for Outer {
            drop(&mut self) -> { missing_outer() }
        }
        main() -> i64 {
            let value = Outer { inner: Inner {} };
            destroy(value);
            0
        }
    "#;
    let errors = run_source(
        "drop-order.gr",
        outer_first,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert!(errors[0].message.contains("missing_outer"));

    let reverse_fields = r#"
        struct First {}
        struct Second {}
        struct Pair { first: First, second: Second }
        impl Drop for First {
            drop(&mut self) -> { missing_first() }
        }
        impl Drop for Second {
            drop(&mut self) -> { missing_second() }
        }
        main() -> i64 {
            let value = Pair { first: First {}, second: Second {} };
            destroy(value);
            0
        }
    "#;
    let errors = run_source(
        "drop-field-order.gr",
        reverse_fields,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert!(errors[0].message.contains("missing_second"));
}

#[test]
fn rejects_effectful_drop_hooks() {
    let source = r#"
        effect Log { write() ->; }
        struct Resource {}
        impl Drop for Resource {
            drop(&mut self) -> { perform Log::write() }
        }
        main() -> i64 { 0 }
    "#;
    let errors = run_source(
        "effectful-drop.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0202"));
}

#[test]
fn drop_hook_may_handle_its_effects_internally() {
    let source = r#"
        effect Cleanup { finish() -> !; }
        struct Resource {}
        impl Drop for Resource {
            drop(&mut self) -> {
                handle perform Cleanup::finish() {
                    Cleanup::finish() => ()
                }
            }
        }
        main() -> i64 {
            destroy(Resource {});
            42
        }
    "#;
    let result = run_source(
        "handled-drop.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn passes_command_line_arguments_to_main() {
    let source = "main(args: List<String>) -> i64 { core::list_len(args) }";
    let result = run_source(
        "args.gr",
        source,
        vec!["a".into(), "b".into()],
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(2));
}

#[test]
fn rejects_undeclared_effects_before_execution() {
    let source = r#"main() -> / {Console} { perform Console::write_line("no") }"#;
    let errors =
        run_source("effects.gr", source, Vec::new(), &mut TestHost::default()).unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0100"));
    assert!(
        errors[0]
            .help
            .as_deref()
            .unwrap()
            .contains("effect Console")
    );
}

#[test]
fn duplicate_callables_have_a_related_source_span() {
    let source = "main() -> { () } main() -> { () }";
    let errors =
        run_source("duplicate.gr", source, Vec::new(), &mut TestHost::default()).unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0001"));
    assert_eq!(errors[0].related.len(), 1);
}

#[test]
fn duplicate_globals_in_the_value_namespace_are_rejected() {
    let source = "let answer = 41; let answer = 42; main() -> i64 { answer }";
    let errors =
        run_source("duplicate.gr", source, Vec::new(), &mut TestHost::default()).unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0006"));
    assert_eq!(errors[0].related.len(), 1);
}

#[test]
fn globals_and_callables_share_one_value_namespace() {
    let source = "let answer = 42; answer() -> i64 { 0 } main() -> i64 { answer }";
    let errors =
        run_source("duplicate.gr", source, Vec::new(), &mut TestHost::default()).unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0006"));
    assert_eq!(errors[0].related.len(), 1);
}

#[test]
fn nominal_declarations_share_one_type_namespace() {
    let source = "struct Answer {} enum Answer { Value } main() -> i64 { 42 }";
    let errors = run_source(
        "duplicate-type.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0007"));
    assert_eq!(errors[0].related.len(), 1);
}

#[test]
fn aliases_and_nominal_declarations_share_one_type_namespace() {
    let source = "type Answer = i64; struct Answer {} main() -> i64 { 42 }";
    let errors = run_source(
        "duplicate-type.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err();
    assert_eq!(errors[0].code.as_deref(), Some("G0007"));
    assert_eq!(errors[0].related.len(), 1);
}

#[test]
fn nominal_values_closures_and_pattern_handlers_define_selection() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        enum Choice { False, True }
        effect Case { case(value: Choice) -> !; }

        choose(condition: Choice, first: F, second: G) -> R {
            handle perform Case::case(condition) {
                Case::case(Choice::True) => first(),
                Case::case(Choice::False) => second()
            }
        }

        main() -> i64 {
            let offset = 2;
            let pair = Pair { left: 40, right: 0 };
            choose(Choice::True, { => pair.left + offset }, { => pair.right })
        }
    "#;
    let result = run_source("selection.gr", source, Vec::new(), &mut TestHost::default()).unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn guarantees_tail_calls_through_closures_and_handlers() {
    let source = r#"
        effect Select { select(value: Result) -> !; }
        choose(condition: Result, yes: F, no: G) -> R {
            handle perform Select::select(condition) {
                Select::select(Result::Ok(_)) => yes(),
                Select::select(Result::Err(_)) => no()
            }
        }
        countdown(n: i64) -> i64 {
            choose(n == 0, { => n }, { => countdown(n - 1) })
        }
        main() -> i64 { countdown(100000) }
    "#;
    let result = run_source(
        "tail-calls.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(0));
}

#[test]
fn terminal_handler_clauses_run_outside_the_selected_handler() {
    let source = r#"
        effect Escape { escape(value: i64) -> !; }

        main() -> i64 {
            handle {
                handle perform Escape::escape(1) {
                    Escape::escape(value) => perform Escape::escape(value + 20)
                }
            } {
                Escape::escape(value) => value + 21
            }
        }
    "#;
    let result = run_source(
        "terminal-handler-transfer.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn resumptive_handlers_capture_and_deeply_reinstall_the_continuation() {
    let source = r#"
        effect Ask { [1,1] ask(value: i64) -> i64; }

        main() -> i64 {
            handle {
                let first = perform Ask::ask(1);
                let second = perform Ask::ask(first);
                second + 1
            } {
                Ask::ask(value) with k => resume(k, value + 20)
            }
        }
    "#;
    let result = run_source(
        "deep-resumption.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn cancelling_a_resumption_discards_the_remaining_computation() {
    let source = r#"
        effect Stop { [0,1] stop() -> i64; }

        main() -> i64 {
            handle {
                let ignored = perform Stop::stop();
                ignored + 1000
            } {
                Stop::stop() with k => {
                    cancel(k);
                    42
                }
            }
        }
    "#;
    let result = run_source(
        "cancel-resumption.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn consuming_a_one_shot_resumption_twice_is_a_runtime_error() {
    let source = r#"
        effect Once { [1,1] value() -> i64; }

        main() -> i64 {
            handle {
                let answer = perform Once::value();
                answer
            } {
                Once::value() with k => {
                    let first = resume(k, 40);
                    resume(k, first + 2)
                }
            }
        }
    "#;
    let error = run_source(
        "one-shot-resumption.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err()
    .remove(0);
    assert!(error.message.contains("upper bound"));
}

#[test]
fn multi_shot_resumptions_replay_the_delimited_continuation() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64; }

        main() -> i64 {
            handle {
                let selected = perform Choose::choose();
                selected + 1
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 19);
                    resume(k, 41)
                }
            }
        }
    "#;
    let result = run_source(
        "multi-shot-resumption.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn multi_shot_replay_snapshots_addressable_assignment_cells() {
    let source = r#"
        effect Choose { [2,2] choose() -> i64; }

        main() -> i64 {
            handle {
                let state = 0;
                let selected = perform Choose::choose();
                state = state + selected;
                state
            } {
                Choose::choose() with k => {
                    let ignored = resume(k, 1);
                    resume(k, 42)
                }
            }
        }
    "#;
    assert_eq!(
        run_source(
            "multi-shot-assignment-snapshot.gr",
            source,
            Vec::new(),
            &mut TestHost::default(),
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn cancellation_respects_the_resumption_lower_bound() {
    let source = r#"
        effect Required { [1,2] value() -> i64; }
        main() -> i64 {
            handle perform Required::value() {
                Required::value() with k => { cancel(k); 42 }
            }
        }
    "#;
    let error = run_source(
        "required-resumption.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err()
    .remove(0);
    assert!(error.message.contains("lower bound"));
}

#[test]
fn validates_resumption_bindings_against_operation_terminality() {
    let missing = r#"
        effect Ask { [1,1] ask() -> i64; }
        main() -> i64 {
            handle perform Ask::ask() { Ask::ask() => 42 }
        }
    "#;
    let error = run_source(
        "missing-resumption.gr",
        missing,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err()
    .remove(0);
    assert_eq!(error.code.as_deref(), Some("G0103"));

    let terminal = r#"
        effect Stop { stop() -> !; }
        main() -> i64 {
            handle perform Stop::stop() { Stop::stop() with k => 42 }
        }
    "#;
    let error = run_source(
        "terminal-resumption.gr",
        terminal,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap_err()
    .remove(0);
    assert_eq!(error.code.as_deref(), Some("G0102"));
}

#[test]
fn packaged_result_truth_and_source_declared_fn_operators_replace_booleans() {
    let source = r#"
        main() -> i64 {
            if(false or { true and { not false } }, { => 42 }) else { 0 }
        }
    "#;
    let result = run_source(
        "result-operators.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}

#[test]
fn callable_constraints_contextually_turn_trailing_blocks_into_closures() {
    let source = r#"
        main() -> i64 {
            if(false) {
                0
            } else {
                42
            }
        }
    "#;
    let result = run_source(
        "contextual-blocks.gr",
        source,
        Vec::new(),
        &mut TestHost::default(),
    )
    .unwrap();
    assert_eq!(result, Value::Int(42));
}
