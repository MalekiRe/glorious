use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "text iteration test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const SOURCE: &str = r#"
    effect ByteStep { inspect(value: Result<u8, ()>) -> !; }
    effect CharStep { inspect(value: Result<u32, ()>) -> !; }
    effect IndexStep { inspect(value: Result<usize, ()>) -> !; }
    effect ViewCase { inspect(value: Result<TextView, TextRangeError>) -> !; }
    effect FormatCase { inspect(value: Result<String, Utf8Error>) -> !; }

    hash_text_view(value: &TextView) -> u64 {
        let state = Hasher::new();
        Hash::hash(value, &mut state);
        Hasher::finish(&state)
    }

    hash_string(value: &String) -> u64 {
        let state = Hasher::new();
        Hash::hash(value, &mut state);
        Hasher::finish(&state)
    }

    second_byte() -> Result<u8, ()> {
        let text = "A☃";
        let iterator = String::bytes(&text);
        BytesIter::next(&mut iterator);
        BytesIter::next(&mut iterator)
    }

    second_scalar() -> Result<u32, ()> {
        let text = "A☃";
        let iterator = String::chars(&text);
        Chars::next_scalar(&mut iterator);
        Chars::next_scalar(&mut iterator)
    }

    second_offset() -> Result<usize, ()> {
        let text = "A☃";
        let iterator = String::char_indices(&text);
        CharIndices::next_offset(&mut iterator);
        CharIndices::next_offset(&mut iterator)
    }

    iterator_score() -> u64 {
        let byte = handle perform ByteStep::inspect(second_byte()) {
            ByteStep::inspect(Option::Some(value)) =>
                wrapping_convert_to_u64(value),
            ByteStep::inspect(None) => wrapping_convert_to_u64(0)
        };
        let scalar = handle perform CharStep::inspect(second_scalar()) {
            CharStep::inspect(Option::Some(value)) =>
                wrapping_convert_to_u64(value),
            CharStep::inspect(None) => wrapping_convert_to_u64(0)
        };
        let offset = handle perform IndexStep::inspect(second_offset()) {
            IndexStep::inspect(Option::Some(value)) =>
                wrapping_convert_to_u64(value),
            IndexStep::inspect(None) => wrapping_convert_to_u64(0)
        };
        move byte + move scalar * 1000 + move offset * 10000000
    }

    view_hashes_match() -> Bool {
        let text = "x☃z";
        handle perform ViewCase::inspect(
            TextView::new(&text, Range { start: 1, end: 4 })
        ) {
            ViewCase::inspect(Result::Ok(view)) => {
                let expected = "☃";
                hash_text_view(&view) == hash_string(&expected)
            },
            ViewCase::inspect(Result::Err(_)) => false
        }
    }

    formatted() -> String {
        let formatter = Formatter::new();
        let prefix = "0x";
        Formatter::literal(&mut formatter, &prefix);
        Formatter::append_hex_u64(&mut formatter, 3735928559);
        let separator = "/";
        Formatter::literal(&mut formatter, &separator);
        Formatter::append_hex_u128(
            &mut formatter,
            340282366920938463463374607431768211455
        );
        handle perform FormatCase::inspect(Formatter::finish(move formatter)) {
            FormatCase::inspect(Result::Ok(text)) => move text,
            FormatCase::inspect(Result::Err(_)) => "invalid"
        }
    }

    ordinary_format(value: i64) -> String {
        handle perform FormatCase::inspect(format(&value)) {
            FormatCase::inspect(Result::Ok(text)) => move text,
            FormatCase::inspect(Result::Err(_)) => "invalid"
        }
    }

    debug_formatted() -> String {
        let value = "a\n";
        handle perform FormatCase::inspect(format_debug(&value)) {
            FormatCase::inspect(Result::Ok(text)) => move text,
            FormatCase::inspect(Result::Err(_)) => "invalid"
        }
    }

    rendered_diagnostic() -> String {
        let sources = SourceMap::new();
        SourceMap::add(&mut sources, "first.glorious", "éx\n");
        SourceMap::add(&mut sources, "second.glorious", "zq\n");
        let diagnostic = SourceDiagnostic::new(
            DiagnosticSeverity::Warning,
            "ordered annotations"
        );
        SourceDiagnostic::annotate(
            &mut diagnostic,
            Range { start: 2, end: 3 },
            "secondary first",
            false
        );
        SourceDiagnostic::annotate(
            &mut diagnostic,
            Range { start: 5, end: 6 },
            "primary second",
            true
        );
        SourceDiagnostic::annotate(
            &mut diagnostic,
            Range { start: 99, end: 100 },
            "outside sources",
            false
        );
        SourceDiagnostic::note(&mut diagnostic, "try again");
        handle perform FormatCase::inspect(
            SourceDiagnostic::render(&diagnostic, &sources)
        ) {
            FormatCase::inspect(Result::Ok(text)) => move text,
            FormatCase::inspect(Result::Err(_)) => "invalid"
        }
    }

    main() -> () { () }
"#;

fn bool_value(artifact: &grandiose_vm::Artifact, function: u32, value: bool) -> Value {
    let ty = artifact.functions[function as usize].return_type;
    Value::aggregate_with_variant(ty, Some(u32::from(!value)), [Value::Unit])
}

fn expected_diagnostic() -> &'static str {
    concat!(
        "warning: ordered annotations\n",
        " --> first.glorious:1:3\n",
        "  = label: secondary first\n",
        " --> second.glorious:1:2\n",
        "  = primary: primary second\n",
        " --> <unknown>:0:0\n",
        "  = label: outside sources\n",
        "  = note: try again",
    )
}

#[test]
fn text_iterators_view_hashing_and_hex_format_work_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "text-iteration-formatting.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_eq!(
            vm.run(function_id(&artifact, "iterator_score"), vec![])
                .unwrap(),
            Value::U64(19_731_226),
            "{optimization_level:?}",
        );
        let hash_function = function_id(&artifact, "view_hashes_match");
        assert_eq!(
            vm.run(hash_function, vec![]).unwrap(),
            bool_value(&artifact, hash_function, true),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "formatted"), vec![]).unwrap(),
            Value::Text("0xdeadbeef/ffffffffffffffffffffffffffffffff".into(),),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(
                function_id(&artifact, "ordinary_format"),
                vec![Value::I64(-42)],
            )
            .unwrap(),
            Value::Text("-42".into()),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "debug_formatted"), vec![])
                .unwrap(),
            Value::Text("\"a\\n\"".into()),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "rendered_diagnostic"), vec![])
                .unwrap(),
            Value::Text(expected_diagnostic().into()),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn iterator_and_format_surface_has_recovery_parity() {
    let value = run_source(
        "text-iteration-formatting-recovery.glorious",
        &SOURCE.replace("main() -> () { () }", "main() -> u64 { iterator_score() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 19_731_226,
        },
    );
}

#[test]
fn diagnostic_renderer_has_recovery_parity() {
    let value = run_source(
        "diagnostic-renderer-recovery.glorious",
        &SOURCE.replace(
            "main() -> () { () }",
            "main() -> String { rendered_diagnostic() }",
        ),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(value, RecoveryValue::String(expected_diagnostic().into()));
}
