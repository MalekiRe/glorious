use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
    eval::{Host, Value},
    run_source,
    span::Span,
};
use grandiose_vm::{Value as VmValue, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<Value>,
        span: Span,
    ) -> Result<Value, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "view/builder test performed a host effect",
            span,
        ))
    }
}

const SURFACE: &str = r#"
    effect TextViewResult {
        inspect(value: Result<TextView, TextRangeError>) -> !;
    }
    effect ByteViewResult {
        inspect(value: Result<ByteView, BytesRangeError>) -> !;
    }

    text_piece(value: String, start: usize, end: usize) -> String {
        handle perform TextViewResult::inspect(
            TextView::new(&value, Range { start: move start, end: move end })
        ) {
            TextViewResult::inspect(Result::Ok(view)) =>
                TextView::to_string(&view),
            TextViewResult::inspect(Result::Err(_)) => ""
        }
    }

    text_range_error(value: String, start: usize, end: usize) -> usize {
        handle perform TextViewResult::inspect(
            TextView::new(&value, Range { start: move start, end: move end })
        ) {
            TextViewResult::inspect(Result::Ok(_)) => 9,
            TextViewResult::inspect(Result::Err(TextRangeError::Reversed)) => 0,
            TextViewResult::inspect(Result::Err(TextRangeError::OutOfBounds)) => 1,
            TextViewResult::inspect(Result::Err(TextRangeError::NotCharBoundary)) => 2
        }
    }

    byte_piece(value: Bytes, start: usize, end: usize) -> Bytes {
        handle perform ByteViewResult::inspect(
            ByteView::new(&value, Range { start: move start, end: move end })
        ) {
            ByteViewResult::inspect(Result::Ok(view)) => ByteView::to_bytes(&view),
            ByteViewResult::inspect(Result::Err(_)) => {
                let empty = "";
                String::as_bytes(&empty)
            }
        }
    }

    byte_range_error(value: Bytes, start: usize, end: usize) -> usize {
        handle perform ByteViewResult::inspect(
            ByteView::new(&value, Range { start: move start, end: move end })
        ) {
            ByteViewResult::inspect(Result::Ok(_)) => 9,
            ByteViewResult::inspect(Result::Err(BytesRangeError::Reversed)) => 0,
            ByteViewResult::inspect(Result::Err(BytesRangeError::OutOfBounds)) => 1
        }
    }

    build_text(prefix: String, suffix: String) -> Result<String, Utf8Error> {
        let builder = StringBuilder::with_capacity(16);
        StringBuilder::append_string(&mut builder, &prefix);
        let suffix_view = TextView::all(&suffix);
        StringBuilder::append_view(&mut builder, &suffix_view);
        StringBuilder::finish(move builder)
    }

    build_invalid(byte: u8) -> Result<String, Utf8Error> {
        let builder = StringBuilder::new();
        StringBuilder::push_byte(&mut builder, move byte);
        StringBuilder::finish(move builder)
    }

    builder_length(value: String) -> usize {
        let builder = StringBuilder::new();
        StringBuilder::reserve(&mut builder, 32);
        StringBuilder::append_string(&mut builder, &value);
        StringBuilder::len(&builder)
    }

    build_bytes(prefix: Bytes, suffix: Bytes) -> Bytes {
        let builder = ByteBuf::with_capacity(16);
        ByteBuf::append_bytes(&mut builder, &prefix);
        let suffix_view = ByteView::all(&suffix);
        ByteBuf::append_view(&mut builder, &suffix_view);
        ByteBuf::push(&mut builder, 33);
        ByteBuf::finish(move builder)
    }

    main() -> () { () }
"#;

#[test]
fn distributed_views_and_builders_execute_at_optimized_levels() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "builders-views.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let verified = verify(artifact.clone()).unwrap();
        let function = |name: &str| {
            artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap() as u32
        };
        let vm = Vm::new(verified);

        assert_eq!(
            vm.run(
                function("text_piece"),
                vec![
                    VmValue::Text("aé💩z".into()),
                    VmValue::U64(1),
                    VmValue::U64(3)
                ],
            )
            .unwrap(),
            VmValue::Text("é".into())
        );
        for (start, end, expected) in [(3, 1, 0), (0, 20, 1), (1, 2, 2), (1, 3, 9)] {
            assert_eq!(
                vm.run(
                    function("text_range_error"),
                    vec![
                        VmValue::Text("aé💩z".into()),
                        VmValue::U64(start),
                        VmValue::U64(end)
                    ],
                )
                .unwrap(),
                VmValue::U64(expected)
            );
        }
        assert_eq!(
            vm.run(
                function("byte_piece"),
                vec![
                    VmValue::Bytes((&b"abcdef"[..]).into()),
                    VmValue::U64(2),
                    VmValue::U64(5)
                ],
            )
            .unwrap(),
            VmValue::Bytes((&b"cde"[..]).into())
        );
        for (start, end, expected) in [(4, 2, 0), (0, 7, 1), (2, 4, 9)] {
            assert_eq!(
                vm.run(
                    function("byte_range_error"),
                    vec![
                        VmValue::Bytes((&b"abcdef"[..]).into()),
                        VmValue::U64(start),
                        VmValue::U64(end),
                    ],
                )
                .unwrap(),
                VmValue::U64(expected)
            );
        }

        let text_result = artifact.functions[function("build_text") as usize].return_type;
        assert_eq!(
            vm.run(
                function("build_text"),
                vec![VmValue::Text("grand".into()), VmValue::Text("iose".into())],
            )
            .unwrap(),
            VmValue::aggregate_with_variant(
                text_result,
                Some(0),
                [VmValue::Text("grandiose".into())],
            )
        );
        let invalid = vm
            .run(function("build_invalid"), vec![VmValue::U64(0xff)])
            .unwrap();
        let VmValue::Aggregate(invalid) = invalid else {
            panic!("StringBuilder::finish did not return Result")
        };
        assert_eq!(invalid.borrow().variant, Some(1));
        assert_eq!(
            vm.run(
                function("builder_length"),
                vec![VmValue::Text("aé💩".into())],
            )
            .unwrap(),
            VmValue::U64(7)
        );
        assert_eq!(
            vm.run(
                function("build_bytes"),
                vec![
                    VmValue::Bytes((&b"G1"[..]).into()),
                    VmValue::Bytes((&b"BC"[..]).into()),
                ],
            )
            .unwrap(),
            VmValue::Bytes((&b"G1BC!"[..]).into())
        );
    }
}

#[test]
fn view_invariants_cannot_be_forged_outside_the_standard_library() {
    for source in [
        "bad(text: String) -> TextView { TextView { text: move text, start: 0, end: 99 } } main() -> () { () }",
        "bad(bytes: Bytes) -> ByteView { ByteView { bytes: move bytes, start: 0, end: 99 } } main() -> () { () }",
    ] {
        let errors = compile_source_to_bytecode("forge-view.glorious", source).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("private field")),
            "unexpected diagnostics: {errors:?}"
        );
    }
}

#[test]
fn views_and_builders_have_recovery_parity() {
    let value = run_source(
        "builders-views-recovery.glorious",
        r#"
            effect Finished { inspect(value: Result<String, Utf8Error>) -> !; }
            main() -> usize {
                let text = "aéz";
                let builder = StringBuilder::new();
                StringBuilder::append_string(&mut builder, &text);
                let text_length = handle perform Finished::inspect(
                    StringBuilder::finish(move builder)
                ) {
                    Finished::inspect(Result::Ok(finished)) =>
                        String::byte_len(&finished),
                    Finished::inspect(Result::Err(_)) => 100
                };
                let bytes = String::as_bytes(&"G1BC");
                let binary = ByteBuf::new();
                ByteBuf::append_bytes(&mut binary, &bytes);
                ByteBuf::push(&mut binary, 33);
                let binary = ByteBuf::finish(move binary);
                move text_length + Bytes::len(&binary)
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(value, Value::Int(9));
}
