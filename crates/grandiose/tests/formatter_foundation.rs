use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
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
            "Formatter recovery test performed a host effect",
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

fn assert_ok_text(value: Value, expected: &str, context: &str) {
    let Value::Aggregate(result) = value else {
        panic!("{context}: Formatter::finish did not return a Result")
    };
    let result = result.borrow();
    assert_eq!(result.variant, Some(0), "{context}: expected Result::Ok");
    assert_eq!(
        result.fields,
        [Some(Value::Text(expected.into()))],
        "{context}",
    );
}

fn expected_bool(artifact: &grandiose_vm::Artifact, function: u32, value: bool) -> Value {
    let ty = artifact.functions[function as usize].return_type;
    Value::aggregate_with_variant(ty, Some(u32::from(!value)), [Value::Unit])
}

const SURFACE: &str = r#"
    nested_document() -> Result<String, Utf8Error> {
        let formatter = Formatter::new();
        let root = "root";
        Formatter::literal(&mut formatter, &root);
        Formatter::newline(&mut formatter);

        Formatter::indent(&mut formatter);
        let child = "child=";
        Formatter::literal(&mut formatter, &child);
        Formatter::append_u64(&mut formatter, 7);
        let separator = ", signed=";
        Formatter::literal(&mut formatter, &separator);
        Formatter::append_i64(&mut formatter, -42);
        Formatter::append_char(&mut formatter, '☃');
        Formatter::newline(&mut formatter);

        Formatter::indent(&mut formatter);
        let nested = "nested=";
        Formatter::literal(&mut formatter, &nested);
        Formatter::append_u64(&mut formatter, 99);
        Formatter::newline(&mut formatter);
        Formatter::dedent(&mut formatter);

        let sibling = "sibling";
        Formatter::literal(&mut formatter, &sibling);
        Formatter::newline(&mut formatter);
        Formatter::newline(&mut formatter);
        Formatter::dedent(&mut formatter);

        let ending = "tail";
        Formatter::literal(&mut formatter, &ending);
        Formatter::finish(move formatter)
    }

    underflow_document() -> Result<String, Utf8Error> {
        let formatter = Formatter::new();
        Formatter::dedent(&mut formatter);
        let first = "first";
        Formatter::literal(&mut formatter, &first);
        Formatter::newline(&mut formatter);
        Formatter::dedent(&mut formatter);
        let second = "second";
        Formatter::literal(&mut formatter, &second);
        Formatter::finish(move formatter)
    }

    underflow_status() -> Bool {
        let formatter = Formatter::new();
        let status = Formatter::dedent(&mut formatter);
        Formatter::finish(move formatter);
        move status
    }

    successful_indent_and_dedent() -> Bool {
        let formatter = Formatter::new();
        Formatter::indent(&mut formatter);
        let status = Formatter::dedent(&mut formatter);
        Formatter::finish(move formatter);
        move status
    }

    main() -> () { () }
"#;

#[test]
fn formatter_emits_nested_indentation_and_integers_at_o0_through_o3() {
    let nested = concat!(
        "root\n",
        "    child=7, signed=-42☃\n",
        "        nested=99\n",
        "    sibling\n",
        "\n",
        "tail",
    );

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "formatter-foundation.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());

        assert_ok_text(
            vm.run(function_id(&artifact, "nested_document"), vec![])
                .unwrap(),
            nested,
            &format!("nested document at {optimization_level:?}"),
        );
        assert_ok_text(
            vm.run(function_id(&artifact, "underflow_document"), vec![])
                .unwrap(),
            "first\nsecond",
            &format!("underflow document at {optimization_level:?}"),
        );

        for (name, expected) in [
            ("underflow_status", false),
            ("successful_indent_and_dedent", true),
        ] {
            let function = function_id(&artifact, name);
            assert_eq!(
                vm.run(function, vec![]).unwrap(),
                expected_bool(&artifact, function, expected),
                "{name} at {optimization_level:?}",
            );
        }
    }
}

#[test]
fn formatter_has_recovery_parity() {
    let value = run_source(
        "formatter-foundation-recovery.glorious",
        r#"
            effect Finished { inspect(value: Result<String, Utf8Error>) -> !; }

            main() -> String {
                let formatter = Formatter::new();
                let heading = "answer";
                Formatter::literal(&mut formatter, &heading);
                Formatter::newline(&mut formatter);
                Formatter::indent(&mut formatter);
                Formatter::append_i64(&mut formatter, -2048);
                Formatter::append_char(&mut formatter, '☃');
                Formatter::newline(&mut formatter);
                Formatter::newline(&mut formatter);
                Formatter::dedent(&mut formatter);
                let done = "done";
                Formatter::literal(&mut formatter, &done);
                handle perform Finished::inspect(Formatter::finish(move formatter)) {
                    Finished::inspect(Result::Ok(text)) => move text,
                    Finished::inspect(Result::Err(_)) => "invalid utf-8"
                }
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::String("answer\n    -2048☃\n\ndone".into()),
    );
}

#[test]
fn formatter_representation_remains_private() {
    for (name, source) in [
        (
            "project-formatter.glorious",
            "bad(value: Formatter) -> usize { value.indentation } main() -> () { () }",
        ),
        (
            "forge-formatter.glorious",
            r#"
                bad(builder: StringBuilder) -> Formatter {
                    Formatter {
                        builder: move builder,
                        indentation: 0,
                        line_start: true
                    }
                }
                main() -> () { () }
            "#,
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("user code accessed Formatter's private representation");
        assert!(
            errors
                .iter()
                .any(|error| error.message.contains("private field")),
            "{name}: unexpected diagnostics: {errors:#?}",
        );
    }
}
