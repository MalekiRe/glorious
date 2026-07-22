use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options, compile_source_to_phases,
    eval::{Host, Value},
    lexer::{self, TokenKind},
    run_bundle, run_source,
    source_bundle::{Segment, SourceBundle},
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
            "the test program performed an effect",
            span,
        ))
    }
}

#[test]
fn distributed_result_option_and_truth_are_ordinary_source_definitions() {
    let source = r#"
        some_number() -> Option<i64> { Option::Some(42) }
        no_number() -> Option<i64> { None }
        no_text() -> Option<Text> { None }
        truth() -> Bool { true }
        falsehood() -> Bool { false }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("standard-values.glorious", source).unwrap();
    let function = |name: &str| {
        artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32
    };
    let some_number = function("some_number");
    let no_number = function("no_number");
    let no_text = function("no_text");
    let truth = function("truth");
    let falsehood = function("falsehood");
    let number_option = artifact.functions[some_number as usize].return_type;
    let text_option = artifact.functions[no_text as usize].return_type;
    let bool_type = artifact.functions[truth as usize].return_type;
    assert_eq!(
        artifact.functions[no_number as usize].return_type,
        number_option
    );
    assert_eq!(
        artifact.functions[falsehood as usize].return_type,
        bool_type
    );
    assert_ne!(number_option, text_option);

    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(
        vm.run(some_number, vec![]).unwrap(),
        VmValue::aggregate_with_variant(number_option, Some(0), [VmValue::I64(42)])
    );
    assert_eq!(
        vm.run(no_number, vec![]).unwrap(),
        VmValue::aggregate_with_variant(number_option, Some(1), [VmValue::Unit])
    );
    assert_eq!(
        vm.run(no_text, vec![]).unwrap(),
        VmValue::aggregate_with_variant(text_option, Some(1), [VmValue::Unit])
    );
    assert_eq!(
        vm.run(truth, vec![]).unwrap(),
        VmValue::aggregate_with_variant(bool_type, Some(0), [VmValue::Unit])
    );
    assert_eq!(
        vm.run(falsehood, vec![]).unwrap(),
        VmValue::aggregate_with_variant(bool_type, Some(1), [VmValue::Unit])
    );

    assert_eq!(
        run_source(
            "interpreted-truth.glorious",
            "main() -> Bool { true }",
            Vec::new(),
            &mut NoHost,
        )
        .unwrap(),
        Value::Enum {
            name: "Result".into(),
            variant: "Ok".into(),
            fields: std::rc::Rc::new(vec![Value::Unit]),
        }
    );
    assert_eq!(
        run_source(
            "interpreted-none.glorious",
            "main() -> Option<i64> { None }",
            Vec::new(),
            &mut NoHost,
        )
        .unwrap(),
        Value::Enum {
            name: "Result".into(),
            variant: "Err".into(),
            fields: std::rc::Rc::new(vec![Value::Unit]),
        }
    );
}

#[test]
fn distributed_programs_request_only_host_imports_they_call() {
    let unused = compile_source_to_bytecode("no-host.glorious", "main() -> () { () }").unwrap();
    assert!(unused.imports.is_empty());
    assert_eq!(unused.required_features & (1 << 5), 0);
    verify(unused).unwrap();

    let diagnostic = compile_source_to_bytecode(
        "diagnostic-host.glorious",
        r#"main() -> () { __g1_diagnostic_write("hello") }"#,
    )
    .unwrap();
    assert_eq!(diagnostic.required_features & (1 << 5), 1 << 5);
    assert_eq!(diagnostic.imports.len(), 1);
    assert_eq!(diagnostic.imports[0].capability, "diagnostic");
    assert_eq!(diagnostic.imports[0].symbol, "write");
    assert_eq!(
        diagnostic.imports[0].signature.params,
        vec![grandiose_vm::TEXT]
    );
    assert_eq!(diagnostic.imports[0].signature.result, grandiose_vm::UNIT);
    assert!(diagnostic.imports[0].may_trap);
    assert!(diagnostic.code.iter().any(|instruction| matches!(
        instruction,
        grandiose_vm::Instruction::HostCall { import: 0, .. }
    )));
    #[derive(Default)]
    struct DiagnosticHost;
    impl grandiose_vm::Host for DiagnosticHost {
        fn process_args(&self) -> Result<Vec<String>, grandiose_vm::HostFault> {
            unreachable!()
        }
        fn fs_read(&self, _path: String) -> Result<Vec<u8>, grandiose_vm::HostFault> {
            unreachable!()
        }
        fn fs_write(
            &self,
            _path: String,
            _contents: Vec<u8>,
        ) -> Result<(), grandiose_vm::HostFault> {
            unreachable!()
        }
        fn diagnostic_write(&self, message: String) -> Result<(), grandiose_vm::HostFault> {
            assert_eq!(message, "hello");
            Ok(())
        }
    }
    let entry = diagnostic.entry_function.unwrap();
    let vm = Vm::with_host(verify(diagnostic).unwrap(), ["diagnostic"], DiagnosticHost).unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), VmValue::Unit);
}

#[test]
fn distributed_public_host_effects_are_closed_by_the_compiler_host_runner() {
    use std::sync::Mutex;

    let source = r#"
        compiler_main() -> usize / {ProcessArgs, FileRead, FileWrite, Diagnostic} {
            let arguments = process_args();
            let contents = read_file("input.glorious");
            write_file("output.g1bc", move contents);
            write_diagnostic("compiled\n");
            Vec::len(&arguments)
        }
        exercise() -> usize {
            run_compiler_host(compiler_main)
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("public-host.glorious", source).unwrap();
    let exercise = artifact
        .functions
        .iter()
        .position(|function| function.name == "exercise")
        .unwrap() as u32;
    assert_eq!(artifact.imports.len(), 4);
    assert!(
        artifact.functions[exercise as usize]
            .outward_protocols
            .is_empty()
    );
    let host_handler = artifact
        .handler_defs
        .iter()
        .find(|handler| handler.clauses.len() == 4)
        .expect("run_compiler_host must install all four public protocols");
    assert!(host_handler.clauses.iter().all(|clause| {
        let Some(resumption) = clause.resumption_type else {
            return false;
        };
        matches!(
            artifact.types[resumption as usize].representation(),
            grandiose_vm::Type::Resumption {
                lower_uses: 1,
                upper_uses: Some(1),
                ..
            }
        )
    }));

    #[derive(Default)]
    struct CompilerHost {
        writes: Mutex<Vec<(String, Vec<u8>)>>,
        diagnostics: Mutex<Vec<String>>,
    }
    impl grandiose_vm::Host for CompilerHost {
        fn process_args(&self) -> Result<Vec<String>, grandiose_vm::HostFault> {
            Ok(vec!["compiler.glorious".into(), "--emit".into()])
        }
        fn fs_read(&self, path: String) -> Result<Vec<u8>, grandiose_vm::HostFault> {
            assert_eq!(path, "input.glorious");
            Ok(b"source".to_vec())
        }
        fn fs_write(&self, path: String, contents: Vec<u8>) -> Result<(), grandiose_vm::HostFault> {
            self.writes.lock().unwrap().push((path, contents));
            Ok(())
        }
        fn diagnostic_write(&self, message: String) -> Result<(), grandiose_vm::HostFault> {
            self.diagnostics.lock().unwrap().push(message);
            Ok(())
        }
    }

    let host = CompilerHost::default();
    let vm = Vm::with_host(
        verify(artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        host,
    )
    .unwrap();
    assert_eq!(vm.run(exercise, vec![]).unwrap(), VmValue::U64(2));
}

#[test]
fn capture_free_named_function_items_are_exact_fn_values_and_respect_shadowing() {
    let source = r#"
        apply<F>(value: i64, body: F) -> i64
            where F: Fn<(i64), Output=i64, Effects={}> {
            body(value)
        }
        add_one(value: i64) -> i64 { value + 1 }
        target() -> i64 { 1 }
        shadow<F>(target: F) -> i64
            where F: Fn<(), Output=i64, Effects={}> { target() }
        parameterized() -> i64 { apply(41, add_one) }
        shadowed() -> i64 { shadow({ => 2 }) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("function-items.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for (name, expected) in [("parameterized", 42), ("shadowed", 2)] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            VmValue::I64(expected)
        );
    }
}

#[test]
fn named_function_item_cannot_hide_an_effect_absent_from_the_exact_fn_row() {
    let errors = compile_source_to_bytecode(
        "effectful-function-item.glorious",
        r#"
            effect Ask { [1,1] ask() -> i64 }
            effectful() -> i64 / {Ask} { perform Ask::ask() }
            pure<F>(body: F) -> i64
                where F: Fn<(), Output=i64, Effects={}> { body() }
            bad() -> i64 { pure(effectful) }
            main() -> () { () }
        "#,
    )
    .expect_err("an effectful function item must not coerce to a pure Fn identity");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("effect")
                && (error.message.contains("absent")
                    || error.message.contains("ambiguous")
                    || error.message.contains("requires outward"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn public_host_fault_terminates_through_run_compiler_host() {
    let artifact = compile_source_to_bytecode(
        "public-host-fault.glorious",
        r#"
            compiler_main() -> () / {FileRead} {
                read_file("missing");
                ()
            }
            exercise() -> () { run_compiler_host(compiler_main) }
            main() -> () { () }
        "#,
    )
    .unwrap();
    let exercise = artifact
        .functions
        .iter()
        .position(|function| function.name == "exercise")
        .unwrap() as u32;
    #[derive(Default)]
    struct FaultHost;
    impl grandiose_vm::Host for FaultHost {
        fn process_args(&self) -> Result<Vec<String>, grandiose_vm::HostFault> {
            unreachable!()
        }
        fn fs_read(&self, _path: String) -> Result<Vec<u8>, grandiose_vm::HostFault> {
            Err(grandiose_vm::HostFault::new("missing input"))
        }
        fn fs_write(
            &self,
            _path: String,
            _contents: Vec<u8>,
        ) -> Result<(), grandiose_vm::HostFault> {
            unreachable!()
        }
        fn diagnostic_write(&self, _message: String) -> Result<(), grandiose_vm::HostFault> {
            unreachable!()
        }
    }
    let error = Vm::with_host(
        verify(artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        FaultHost,
    )
    .unwrap()
    .run(exercise, vec![])
    .unwrap_err();
    assert!(error.to_string().contains("missing input"));
}

#[test]
fn distributed_host_imports_are_canonical_independent_of_call_declaration_order() {
    let wrappers = [
        "call_args() -> Array<Text> { __g1_process_args_get() }",
        "call_read(path: Text) -> Bytes { __g1_fs_read(path) }",
        "call_write(path: Text, bytes: Bytes) -> () { __g1_fs_write(path, bytes) }",
        "call_diagnostic(text: Text) -> () { __g1_diagnostic_write(text) }",
    ];
    let compile = |order: &[usize]| {
        let mut source = order
            .iter()
            .map(|index| wrappers[*index])
            .collect::<Vec<_>>()
            .join("\n");
        source.push_str("\nmain() -> () { () }");
        compile_source_to_bytecode("all-hosts.glorious", &source).unwrap()
    };
    let forward = compile(&[0, 1, 2, 3]);
    let reverse = compile(&[3, 2, 1, 0]);
    let tuples = |artifact: &grandiose_vm::Artifact| {
        artifact
            .imports
            .iter()
            .map(|import| (import.capability.clone(), import.symbol.clone()))
            .collect::<Vec<_>>()
    };
    let expected = vec![
        ("diagnostic".to_owned(), "write".to_owned()),
        ("fs.read".to_owned(), "read".to_owned()),
        ("fs.write".to_owned(), "write".to_owned()),
        ("process.args".to_owned(), "get".to_owned()),
    ];
    assert_eq!(tuples(&forward), expected);
    assert_eq!(tuples(&reverse), expected);
    assert_eq!(
        forward.imports[0].signature.params,
        vec![grandiose_vm::TEXT]
    );
    assert_eq!(forward.imports[0].signature.result, grandiose_vm::UNIT);
    assert_eq!(
        forward.imports[1].signature.params,
        vec![grandiose_vm::TEXT]
    );
    assert_eq!(forward.imports[1].signature.result, grandiose_vm::BYTES);
    assert_eq!(
        forward.imports[2].signature.params,
        vec![grandiose_vm::TEXT, grandiose_vm::BYTES]
    );
    assert_eq!(forward.imports[2].signature.result, grandiose_vm::UNIT);
    assert!(forward.imports[3].signature.params.is_empty());
    assert!(matches!(
        forward.types[forward.imports[3].signature.result as usize].representation(),
        grandiose_vm::Type::Array { element } if *element == grandiose_vm::TEXT
    ));
    assert!(
        forward
            .imports
            .iter()
            .all(|import| { import.may_trap && import.signature.outward_protocols.is_empty() })
    );
    verify(forward).unwrap();
    verify(reverse).unwrap();
}

#[test]
fn copied_host_leaf_spelling_has_no_manifest_authority() {
    let raw = SourceBundle::raw_for_conformance(
        Segment::new(
            "<grandiose:std>",
            "__g1_diagnostic_write(text: Text) -> () { () }",
        ),
        Segment::new(
            "caller.glorious",
            r#"main() -> () { __g1_diagnostic_write("not a host call") }"#,
        ),
        [],
    );
    let artifact = compile_bundle_to_bytecode(&raw).unwrap();
    assert!(artifact.imports.is_empty());
    assert_eq!(artifact.required_features & (1 << 5), 0);
    assert!(
        !artifact
            .code
            .iter()
            .any(|instruction| matches!(instruction, grandiose_vm::Instruction::HostCall { .. }))
    );
    verify(artifact).unwrap();
}

#[test]
fn associated_host_leaf_aliases_remain_host_calls_at_every_optimization_level() {
    let source = r#"
        struct Diagnostic {}
        let Diagnostic::write = __g1_diagnostic_write;
        main() -> () { Diagnostic::write("alias") }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "host-alias.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap();
        assert_eq!(artifact.imports.len(), 1);
        assert_eq!(artifact.imports[0].capability, "diagnostic");
        assert!(artifact.imports[0].may_trap);
        assert_eq!(artifact.required_features & (1 << 5), 1 << 5);
        assert!(artifact.code.iter().any(|instruction| matches!(
            instruction,
            grandiose_vm::Instruction::HostCall { import: 0, .. }
        )));
        verify(artifact).unwrap();
    }
}

#[test]
fn distributed_result_control_runs_every_success_and_failure_path() {
    let source = r#"
        truth() -> Bool { true }
        falsehood() -> Bool { false }
        some(value: i64) -> Option<i64> { Option::Some(value) }
        none_i64() -> Option<i64> { None }
        ok_i64(value: i64) -> Result<i64, i64> { Result::Ok(value) }
        err_i64(value: i64) -> Result<i64, i64> { Result::Err(value) }

        if_success() -> i64 { if(truth()) { 11 } else { 0 } }
        if_failure() -> i64 { if(falsehood()) { 0 } else { 12 } }

        else_success() -> i64 { some(13) else { 0 } }
        else_failure() -> i64 { none_i64() else { 14 } }

        and_success() -> i64 {
            (truth() and { some(15) }) else { 0 }
        }
        and_failure() -> i64 {
            (falsehood() and { some(0) }) else { 16 }
        }

        or_success() -> i64 {
            (some(17) or { some(0) }) else { 0 }
        }
        or_failure() -> i64 {
            (none_i64() or { some(18) }) else { 0 }
        }

        not_success() -> i64 {
            not err_i64(19) else { 0 }
        }
        not_failure() -> i64 {
            not ok_i64(20) else { 21 }
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("result-control.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for (name, expected) in [
        ("if_success", 11),
        ("if_failure", 12),
        ("else_success", 13),
        ("else_failure", 14),
        ("and_success", 15),
        ("and_failure", 16),
        ("or_success", 17),
        ("or_failure", 18),
        ("not_success", 19),
        ("not_failure", 21),
    ] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap_or_else(|| panic!("missing `{name}`")) as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            VmValue::I64(expected),
            "{name}"
        );
    }
}

#[test]
fn distributed_result_control_requires_zero_use_only_on_discarding_paths() {
    let prelude = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
    "#;
    for body in [
        "bad(value: Result<Token, ()>) -> Result<i64, ()> { if(value, { => 1 }) }",
        "bad(value: Result<Token, ()>) -> Result<i64, ()> { value and { Result::Ok(1) } }",
        "bad(value: Result<i64, Token>) -> i64 { value else { 1 } }",
        "bad(value: Result<i64, Token>) -> Result<i64, ()> { value or { Result::Err(()) } }",
    ] {
        let source = format!("{prelude}{body} main() -> () {{ () }}");
        let errors = compile_source_to_bytecode("result-control-use.glorious", &source)
            .expect_err("a result operator discarded a must-move payload");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("Use")
                    && (error.message.contains("marker constraint")
                        || error.message.contains("matching implementation")
                        || error.message.contains("refuted"))
            }),
            "{errors:#?}"
        );
    }

    compile_source_to_bytecode(
        "result-not-preserves.glorious",
        &format!(
            "{prelude} flip_result(value: Result<Token, Token>) -> Result<Token, Token> {{ not(value) }} main() -> () {{ () }}"
        ),
    )
    .expect("not preserves both must-move payloads instead of discarding either one");
}

#[test]
fn distributed_result_control_delays_rhs_callables_without_spelling_magic() {
    let source = r#"
        effect Boom { boom() -> ! }
        truth() -> Bool { true }
        falsehood() -> Bool { false }
        some(value: i64) -> Option<i64> { Option::Some(value) }

        skipped_if_result() -> Option<i64> / {Boom} {
            if(falsehood(), { => perform Boom::boom() })
        }
        skipped_if() -> i64 / {Boom} {
            skipped_if_result() else { 31 }
        }
        skipped_else() -> i64 / {Boom} {
            some(32) else { perform Boom::boom() }
        }
        skipped_and_result() -> Option<i64> / {Boom} {
            falsehood() and { perform Boom::boom() }
        }
        skipped_and() -> i64 / {Boom} {
            skipped_and_result() else { 33 }
        }
        skipped_or_result() -> Option<i64> / {Boom} {
            some(34) or { perform Boom::boom() }
        }
        skipped_or() -> i64 / {Boom} {
            skipped_or_result() else { 0 }
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("result-control-lazy.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    for (name, expected) in [
        ("skipped_if", 31),
        ("skipped_else", 32),
        ("skipped_and", 33),
        ("skipped_or", 34),
    ] {
        let function = artifact
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            artifact.functions[function as usize]
                .outward_protocols
                .len(),
            1
        );
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            VmValue::I64(expected)
        );
    }
}

#[test]
fn bootstrap_interpreter_executes_packaged_result_control_as_source() {
    assert_eq!(
        run_source(
            "interpreted-result-control.glorious",
            "main() -> i64 { if(false) { 0 } else { 42 } }",
            Vec::new(),
            &mut NoHost,
        )
        .unwrap(),
        Value::Int(42)
    );
}

#[test]
fn distributed_vec_wrappers_compile_verify_and_execute_in_both_engines() {
    let source = r#"
        make_values() -> Vec<i64> { Vec::with_capacity(4) }
        answer() -> usize {
            let values = make_values();
            Vec::reserve(&mut values, 2);
            Vec::push(&mut values, 40);
            Vec::push(&mut values, 2);
            { let first = Vec::index(&values, 0); first; (); };
            { let second = Vec::index_mut(&mut values, 1); second; (); };
            Vec::len(&values) + Vec::capacity(&values)
        }
        main() -> () { answer(); () }
    "#;
    let artifact = compile_source_to_bytecode("distributed-vec.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        VmValue::U64(6)
    );
    assert_eq!(
        run_source("interpreted-vec.glorious", source, Vec::new(), &mut NoHost,).unwrap(),
        Value::Unit
    );
}

#[test]
fn distributed_checked_vec_access_and_pop_run_in_both_engines_at_every_level() {
    let source = r#"
        effect I64OptionCase { inspect(value: Result<i64, ()>) -> !; }

        empty_i64() -> Vec<i64> { Vec::new() }
        empty_nested() -> Vec<Vec<i64>> { Vec::new() }

        pop_some_option() -> Option<i64> {
            let values = empty_i64();
            Vec::push(&mut values, 7);
            Vec::pop(&mut values)
        }
        pop_empty_option() -> Option<i64> {
            let values = empty_i64();
            Vec::pop(&mut values)
        }
        pop_value() -> i64 {
            let values = empty_i64();
            Vec::push(&mut values, 42);
            handle perform I64OptionCase::inspect(Vec::pop(&mut values)) {
                I64OptionCase::inspect(Result::Ok(value)) => value,
                I64OptionCase::inspect(Result::Err(_)) => -1
            }
        }

        borrow_at<'a>(values: &'a Vec<i64>, index: usize)
            -> Option<&'a i64> {
            Vec::get(values, index)
        }
        first_of<'a>(values: &'a Vec<i64>) -> Option<&'a i64> {
            Vec::first(values)
        }
        last_of<'a>(values: &'a Vec<i64>) -> Option<&'a i64> {
            Vec::last(values)
        }
        borrow_nested<'a>(values: &'a mut Vec<Vec<i64>>, index: usize)
            -> Option<&'a mut Vec<i64>> {
            Vec::get_mut(values, index)
        }
        push_inner(values: &mut Vec<i64>) -> () {
            Vec::push(values, 42)
        }
        nested_len(values: &Vec<Vec<i64>>) -> usize {
            Vec::len(Vec::index(values, 0))
        }
        empty_score() -> i64 {
            let values = empty_i64();
            handle perform I64OptionCase::inspect(Vec::pop(&mut values)) {
                I64OptionCase::inspect(Result::Ok(_)) => 0,
                I64OptionCase::inspect(Result::Err(_)) => 1
            }
        }
        exercise_guards() -> () {
            let values = empty_i64();
            Vec::push(&mut values, 1);
            Vec::get(&values, 0);
            Vec::get(&values, 9);
            Vec::first(&values);
            Vec::last(&values);
            Vec::is_empty(&values);
            let inner = empty_i64();
            Vec::push(&mut inner, 3);
            let outer = empty_nested();
            Vec::push(&mut outer, move inner);
            Vec::get_mut(&mut outer, 0);
            Vec::get_mut(&mut outer, 4);
            ()
        }
        answer() -> i64 {
            exercise_guards();
            pop_value() + empty_score()
        }
        main() -> () { answer(); () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "checked-vec.glorious",
            source,
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
            vm.run(function("answer"), vec![]).unwrap(),
            VmValue::I64(43)
        );

        let some = function("pop_some_option");
        let option_type = artifact.functions[some as usize].return_type;
        assert_eq!(
            vm.run(some, vec![]).unwrap(),
            VmValue::aggregate_with_variant(option_type, Some(0), [VmValue::I64(7)])
        );
        let none = function("pop_empty_option");
        assert_eq!(
            vm.run(none, vec![]).unwrap(),
            VmValue::aggregate_with_variant(option_type, Some(1), [VmValue::Unit])
        );

        let borrow_at = function("borrow_at");
        let shared_vec_type = match artifact.types
            [artifact.functions[borrow_at as usize].params[0] as usize]
            .representation()
        {
            grandiose_vm::Type::RefShared { referent } => *referent,
            other => panic!("borrow_at parameter is not shared Vec: {other:?}"),
        };
        let shared_vec = VmValue::aggregate(
            shared_vec_type,
            [VmValue::array(
                grandiose_vm::I64,
                [VmValue::I64(11), VmValue::I64(22)],
            )],
        );
        let VmValue::Aggregate(shared_storage) = shared_vec else {
            unreachable!()
        };
        let shared_argument = VmValue::Reference {
            referent_type: shared_vec_type,
            unique: false,
            target: grandiose_vm::value::ReferenceTarget::Aggregate(shared_storage.clone()),
        };
        for (name, index, expected_variant) in [
            ("borrow_at", 9, 1),
            ("borrow_at", 0, 0),
            ("first_of", 0, 0),
            ("last_of", 0, 0),
        ] {
            let mut args = vec![shared_argument.clone()];
            if name == "borrow_at" {
                args.push(VmValue::U64(index));
            }
            let result = vm.run(function(name), args).unwrap();
            let VmValue::Aggregate(result) = result else {
                panic!("{name} did not return Option")
            };
            assert_eq!(result.borrow().variant, Some(expected_variant), "{name}");
            if expected_variant == 0 {
                assert!(matches!(
                    result.borrow().fields[0],
                    Some(VmValue::Reference { .. })
                ));
            }
        }

        let borrow_nested = function("borrow_nested");
        let outer_vec_type = match artifact.types
            [artifact.functions[borrow_nested as usize].params[0] as usize]
            .representation()
        {
            grandiose_vm::Type::RefUnique { referent } => *referent,
            other => panic!("borrow_nested parameter is not unique Vec: {other:?}"),
        };
        let inner_vec_type = match artifact.types[outer_vec_type as usize].representation() {
            grandiose_vm::Type::Struct { fields, .. } => {
                match artifact.types[fields[0].ty as usize].representation() {
                    grandiose_vm::Type::Array { element } => *element,
                    other => panic!("Vec storage is not Array: {other:?}"),
                }
            }
            other => panic!("Vec is not a struct: {other:?}"),
        };
        let inner = VmValue::aggregate(inner_vec_type, [VmValue::array(grandiose_vm::I64, [])]);
        let outer = VmValue::aggregate(outer_vec_type, [VmValue::array(inner_vec_type, [inner])]);
        let VmValue::Aggregate(outer_storage) = outer else {
            unreachable!()
        };
        let unique_outer = VmValue::Reference {
            referent_type: outer_vec_type,
            unique: true,
            target: grandiose_vm::value::ReferenceTarget::Aggregate(outer_storage.clone()),
        };
        let borrowed = vm
            .run(borrow_nested, vec![unique_outer, VmValue::U64(0)])
            .unwrap();
        let VmValue::Aggregate(borrowed) = borrowed else {
            panic!("get_mut did not return Option")
        };
        let target = borrowed.borrow_mut().fields[0].take().unwrap();
        vm.run(function("push_inner"), vec![target]).unwrap();
        let shared_outer = VmValue::Reference {
            referent_type: outer_vec_type,
            unique: false,
            target: grandiose_vm::value::ReferenceTarget::Aggregate(outer_storage),
        };
        assert_eq!(
            vm.run(function("nested_len"), vec![shared_outer]).unwrap(),
            VmValue::U64(1)
        );
    }

    assert_eq!(
        run_source(
            "interpreted-checked-vec.glorious",
            source,
            Vec::new(),
            &mut NoHost,
        )
        .unwrap(),
        Value::Unit
    );
}

#[test]
fn vec_get_mut_returned_loan_blocks_parent_mutation_until_consumed() {
    let errors = compile_source_to_bytecode(
        "vec-get-mut-loan.glorious",
        r#"
            hold(value: Result<&mut i64, ()>) -> () { () }
            empty_i64() -> Vec<i64> { Vec::new() }
            bad() -> () {
                let values = empty_i64();
                Vec::push(&mut values, 1);
                let borrowed = Vec::get_mut(&mut values, 0);
                Vec::push(&mut values, 2);
                hold(move borrowed)
            }
            main() -> () { () }
        "#,
    )
    .expect_err("an Option-wrapped unique element loan must suspend the parent Vec loan");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("borrow")
                || error.message.contains("loan")
                || error.message.contains("unique")
        }),
        "{errors:#?}"
    );
}

#[test]
fn vec_pop_transfers_an_exact_linear_element_obligation() {
    let source = r#"
        struct Ticket { serial: i64 }
        struct PopResult { popped: Option<Ticket>, remainder: Vec<Ticket> }
        impl Use<[1,1]> for Ticket {}
        empty_tickets() -> Vec<Ticket> { Vec::new() }
        pop_ticket_bundle() -> PopResult {
            let values = empty_tickets();
            Vec::push(&mut values, Ticket { serial: 42 });
            let popped = Vec::pop(&mut values);
            PopResult { popped: move popped, remainder: move values }
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("linear-vec-pop.glorious", source).unwrap();
    let pop_ticket_bundle = artifact
        .functions
        .iter()
        .position(|function| function.name == "pop_ticket_bundle")
        .unwrap() as u32;
    let result = Vm::new(verify(artifact).unwrap())
        .run(pop_ticket_bundle, vec![])
        .unwrap();
    let VmValue::Aggregate(result) = result else {
        panic!("linear pop did not return its result tuple")
    };
    let option = result.borrow_mut().fields[0].take().unwrap();
    let VmValue::Aggregate(option) = option else {
        panic!("linear pop did not return Option")
    };
    assert_eq!(option.borrow().variant, Some(0));
    let ticket = option.borrow_mut().fields[0].take().unwrap();
    let VmValue::Aggregate(ticket) = ticket else {
        panic!("linear pop did not transfer Ticket")
    };
    assert_eq!(ticket.borrow().fields[0], Some(VmValue::I64(42)));

    let interpreted = r#"
        struct Ticket { serial: i64 }
        struct PopResult { popped: Option<Ticket>, remainder: Vec<Ticket> }
        impl Use<[1,1]> for Ticket {}
        empty_tickets() -> Vec<Ticket> { Vec::new() }
        main() -> PopResult {
            let values = empty_tickets();
            Vec::push(&mut values, Ticket { serial: 42 });
            let popped = Vec::pop(&mut values);
            PopResult { popped: move popped, remainder: move values }
        }
    "#;
    run_source(
        "interpreted-linear-vec-pop.glorious",
        interpreted,
        Vec::new(),
        &mut NoHost,
    )
    .unwrap();

    let errors = compile_source_to_bytecode(
        "discard-linear-vec-pop.glorious",
        r#"
            struct Ticket { serial: i64 }
            impl Use<[1,1]> for Ticket {}
            empty_tickets() -> Vec<Ticket> { Vec::new() }
            bad() -> Vec<Ticket> {
                let values = empty_tickets();
                Vec::push(&mut values, Ticket { serial: 1 });
                Vec::pop(&mut values);
                values
            }
            main() -> () { () }
        "#,
    )
    .expect_err("discarding Option<Ticket> would lose the transferred obligation");
    assert!(
        errors
            .iter()
            .any(|error| error.message.to_ascii_lowercase().contains("use")),
        "{errors:#?}"
    );
}

#[test]
fn distributed_vec_rearrangement_removal_insertion_and_append_are_checked_at_every_level() {
    let source = r#"
        effect I64OptionCase { inspect(value: Result<i64, ()>) -> !; }
        effect I64InsertCase { inspect(value: Result<(), i64>) -> !; }
        effect BoolCase { inspect(value: Bool) -> !; }

        empty_i64() -> Vec<i64> { Vec::new() }
        read(value: &i64) -> i64 { *value }
        option_or_zero(value: Option<i64>) -> i64 {
            handle perform I64OptionCase::inspect(value) {
                I64OptionCase::inspect(Result::Ok(item)) => item,
                I64OptionCase::inspect(Result::Err(_)) => 0
            }
        }
        insert_score(value: Result<(), i64>) -> i64 {
            handle perform I64InsertCase::inspect(value) {
                I64InsertCase::inspect(Result::Ok(_)) => 1,
                I64InsertCase::inspect(Result::Err(item)) => item
            }
        }
        bool_score(value: Bool) -> i64 {
            handle perform BoolCase::inspect(value) {
                BoolCase::inspect(Result::Ok(_)) => 1,
                BoolCase::inspect(Result::Err(_)) => 0
            }
        }

        answer() -> i64 {
            let values = empty_i64();
            Vec::push(&mut values, 10);
            Vec::push(&mut values, 20);
            Vec::push(&mut values, 30);
            let swap_ok = bool_score(Vec::swap(&mut values, 0, 2));
            Vec::reverse(&mut values);
            let insert_ok = insert_score(Vec::insert(&mut values, 1, 15));
            let removed = option_or_zero(Vec::remove(&mut values, 2));
            let swapped = option_or_zero(Vec::swap_remove(&mut values, 0));

            let invalid_swap = bool_score(Vec::swap(&mut values, 9, 0));
            let invalid_remove = option_or_zero(Vec::remove(&mut values, 9));
            let invalid_swap_remove = option_or_zero(
                Vec::swap_remove(&mut values, 9)
            );
            let failed_insert = insert_score(Vec::insert(&mut values, 9, 99));

            let source = empty_i64();
            Vec::push(&mut source, 1);
            Vec::push(&mut source, 2);
            Vec::append(&mut values, move source);

            read(Vec::index(&values, 0))
                + read(Vec::index(&values, 1))
                + read(Vec::index(&values, 2))
                + read(Vec::index(&values, 3))
                + removed
                + swapped
                + swap_ok
                + insert_ok
                + invalid_swap
                + invalid_remove
                + invalid_swap_remove
                + failed_insert
        }
        main() -> () { answer(); () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "vec-rearrangement.glorious",
            source,
            CompileOptions { optimization_level },
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
            VmValue::I64(179),
            "wrong checked Vec result at {optimization_level:?}"
        );
    }

    assert_eq!(
        run_source(
            "interpreted-vec-rearrangement.glorious",
            &source.replace(
                "main() -> () { answer(); () }",
                "main() -> i64 { answer() }"
            ),
            Vec::new(),
            &mut NoHost,
        )
        .unwrap(),
        Value::Int(179)
    );
}

#[test]
fn vec_moving_operations_preserve_every_exact_linear_element_obligation() {
    let source = r#"
        struct Ticket { serial: i64 }
        struct LinearVecResult {
            removed: Option<Ticket>,
            swapped: Option<Ticket>,
            valid_insert: Result<(), Ticket>,
            invalid_insert: Result<(), Ticket>,
            remainder: Vec<Ticket>
        }
        impl Use<[1,1]> for Ticket {}

        empty_tickets() -> Vec<Ticket> { Vec::new() }
        ticket(serial: i64) -> Ticket { Ticket { serial: move serial } }
        exercise() -> LinearVecResult {
            let values = empty_tickets();
            Vec::push(&mut values, ticket(1));
            Vec::push(&mut values, ticket(2));
            Vec::push(&mut values, ticket(3));
            Vec::swap(&mut values, 0, 2);
            Vec::reverse(&mut values);
            let valid_insert = Vec::insert(&mut values, 1, ticket(4));
            let removed = Vec::remove(&mut values, 2);
            let swapped = Vec::swap_remove(&mut values, 0);
            let invalid_insert = Vec::insert(&mut values, 99, ticket(5));
            let source = empty_tickets();
            Vec::push(&mut source, ticket(6));
            Vec::push(&mut source, ticket(7));
            Vec::append(&mut values, move source);
            LinearVecResult {
                removed: move removed,
                swapped: move swapped,
                valid_insert: move valid_insert,
                invalid_insert: move invalid_insert,
                remainder: move values
            }
        }
        main() -> () { () }
    "#;

    let artifact = compile_source_to_bytecode("linear-vec-moving.glorious", source).unwrap();
    let exercise = artifact
        .functions
        .iter()
        .position(|function| function.name == "exercise")
        .unwrap() as u32;
    let result = Vm::new(verify(artifact).unwrap())
        .run(exercise, vec![])
        .unwrap();
    let VmValue::Aggregate(result) = result else {
        panic!("linear Vec exercise did not return its ownership result")
    };
    let fields = result.borrow();
    for (field, expected_variant) in [(0, 0), (1, 0), (2, 0), (3, 1)] {
        let VmValue::Aggregate(option) = fields.fields[field].as_ref().unwrap() else {
            panic!("linear Vec result field {field} is not an Option")
        };
        assert_eq!(option.borrow().variant, Some(expected_variant));
    }
    let VmValue::Aggregate(remainder) = fields.fields[4].as_ref().unwrap() else {
        panic!("linear Vec remainder is not a Vec")
    };
    let remainder_fields = remainder.borrow();
    let VmValue::Array(storage) = remainder_fields.fields[0].as_ref().unwrap() else {
        panic!("linear Vec remainder has no Array storage")
    };
    assert_eq!(storage.borrow().slots.len(), 4);
    drop(remainder_fields);
    drop(fields);

    run_source(
        "interpreted-linear-vec-moving.glorious",
        &source.replace(
            "main() -> () { () }",
            "main() -> LinearVecResult { exercise() }",
        ),
        Vec::new(),
        &mut NoHost,
    )
    .unwrap();
}

#[test]
fn recursive_vec_moving_algorithms_form_tail_edges_and_run_in_constant_frame_space() {
    let source = r#"
        effect LoopCase { inspect(value: Bool) -> !; }
        empty_i64() -> Vec<i64> { Vec::new() }
        fill(value: &mut Vec<i64>, remaining: usize) -> () {
            handle perform LoopCase::inspect(remaining == 0) {
                LoopCase::inspect(Result::Ok(_)) => (),
                LoopCase::inspect(Result::Err(_)) => {
                    Vec::push(&mut *value, 1);
                    fill(move value, remaining - 1)
                }
            }
        }
        stress() -> usize {
            let target = empty_i64();
            fill(&mut target, 32768);
            Vec::reverse(&mut target);
            Vec::remove(&mut target, 0);
            Vec::insert(&mut target, 0, 1);
            let source = empty_i64();
            fill(&mut source, 8192);
            Vec::append(&mut target, move source);
            Vec::len(&target)
        }
        main() -> () { stress(); () }
    "#;

    let artifact = compile_source_to_bytecode_with_options(
        "large-vec-moving.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O1,
        },
    )
    .unwrap();
    let function = |name: &str| {
        let specialization = format!("$specialization${name}#");
        artifact
            .functions
            .iter()
            .position(|function| {
                function.name == name || function.name.starts_with(&specialization)
            })
            .unwrap() as u32
    };
    let recursive_targets = [
        function("__g1_vec_reverse_between"),
        function("__g1_vec_rotate_to_end"),
        function("__g1_vec_rotate_inserted"),
        function("__g1_vec_append_drain"),
    ];
    let mut ordinary_edges = [0usize; 4];
    let mut tail_edges = [0usize; 4];
    for generated in artifact
        .functions
        .iter()
        .filter(|generated| generated.name.starts_with("$handler$"))
    {
        for instruction in &artifact.code
            [generated.code_start as usize..(generated.code_start + generated.code_len) as usize]
        {
            match instruction {
                grandiose_vm::Instruction::Call { function, .. } => {
                    if let Some(index) = recursive_targets
                        .iter()
                        .position(|target| target == function)
                    {
                        ordinary_edges[index] += 1;
                    }
                }
                grandiose_vm::Instruction::TailCall { function, .. } => {
                    if let Some(index) = recursive_targets
                        .iter()
                        .position(|target| target == function)
                    {
                        tail_edges[index] += 1;
                    }
                }
                _ => {}
            }
        }
    }
    assert_eq!(
        ordinary_edges,
        [0, 1, 1, 0],
        "only remove/insert's non-tail rotate-then-finish calls may remain ordinary"
    );
    assert!(
        tail_edges.iter().all(|edges| *edges >= 1),
        "each recursive Vec helper must form its own TailCall edge: {tail_edges:?}"
    );

    let stress = function("stress");
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(stress, vec![])
            .unwrap(),
        VmValue::U64(40960)
    );
}

#[test]
fn distributed_text_bytes_and_vec_bridges_execute_at_every_optimization_level() {
    let source = r#"
        text_len() -> usize {
            let value = "hello";
            String::byte_len(&value)
        }
        joined_text() -> String { String::concat("grand", "iose") }
        text_bytes_len() -> usize {
            let value = "bytes";
            let bytes = String::as_bytes(&value);
            Bytes::len(&bytes)
        }
        equal_text() -> Bool {
            let left = "same";
            let right = "same";
            String::eq(&left, &right)
        }
        unequal_text() -> Bool {
            let left = "left";
            let right = "right";
            String::eq(&left, &right)
        }
        joined_bytes_len() -> usize {
            let left_text = "ab";
            let right_text = "cde";
            let left = String::as_bytes(&left_text);
            let right = String::as_bytes(&right_text);
            let joined = Bytes::concat(move left, move right);
            Bytes::len(&joined)
        }
        byte_values(capacity: usize) -> Vec<u8> { Vec::with_capacity(capacity) }
        byte(value: u8) -> u8 { value }
        byte_vec_roundtrip_shape() -> usize {
            let values = byte_values(8);
            Vec::push(&mut values, byte(65));
            Vec::push(&mut values, byte(66));
            let bytes = Bytes::from_vec(move values);
            let restored = Bytes::to_vec(move bytes);
            Vec::len(&restored) + Vec::capacity(&restored)
        }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "distributed-text-bytes.glorious",
            source,
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
            vm.run(function("text_len"), vec![]).unwrap(),
            VmValue::U64(5)
        );
        assert_eq!(
            vm.run(function("joined_text"), vec![]).unwrap(),
            VmValue::Text("grandiose".into())
        );
        assert_eq!(
            vm.run(function("text_bytes_len"), vec![]).unwrap(),
            VmValue::U64(5)
        );
        let bool_type = artifact.functions[function("equal_text") as usize].return_type;
        assert_eq!(
            vm.run(function("equal_text"), vec![]).unwrap(),
            VmValue::aggregate_with_variant(bool_type, Some(0), [VmValue::Unit])
        );
        assert_eq!(
            vm.run(function("unequal_text"), vec![]).unwrap(),
            VmValue::aggregate_with_variant(bool_type, Some(1), [VmValue::Unit])
        );
        assert_eq!(
            vm.run(function("joined_bytes_len"), vec![]).unwrap(),
            VmValue::U64(5)
        );
        assert_eq!(
            vm.run(function("byte_vec_roundtrip_shape"), vec![])
                .unwrap(),
            VmValue::U64(4),
            "Bytes::to_vec must return a dense Vec with capacity exactly equal to byte length"
        );
    }
}

#[test]
fn distributed_safe_bytes_predicates_access_and_slices_run_at_every_optimization_level() {
    let source = r#"
        empty_string() -> String { String::empty() }
        empty_string_is_empty() -> Bool {
            let value = String::empty();
            String::is_empty(&value)
        }
        nonempty_string_is_empty() -> Bool {
            let value = "x";
            String::is_empty(&value)
        }
        empty_bytes_is_empty() -> Bool {
            let text = "";
            let value = String::as_bytes(&text);
            Bytes::is_empty(&value)
        }
        nonempty_bytes_is_empty() -> Bool {
            let text = "abc";
            let value = String::as_bytes(&text);
            Bytes::is_empty(&value)
        }
        equal_bytes() -> Bool {
            let left_text = "abc";
            let right_text = "abc";
            let left = String::as_bytes(&left_text);
            let right = String::as_bytes(&right_text);
            Bytes::eq(&left, &right)
        }
        equal_empty_bytes() -> Bool {
            let left_text = "";
            let right_text = "";
            let left = String::as_bytes(&left_text);
            let right = String::as_bytes(&right_text);
            Bytes::eq(&left, &right)
        }
        unequal_byte_bytes() -> Bool {
            let left_text = "abc";
            let right_text = "abd";
            let left = String::as_bytes(&left_text);
            let right = String::as_bytes(&right_text);
            Bytes::eq(&left, &right)
        }
        unequal_length_bytes() -> Bool {
            let left_text = "abc";
            let right_text = "ab";
            let left = String::as_bytes(&left_text);
            let right = String::as_bytes(&right_text);
            Bytes::eq(&left, &right)
        }
        equal_byte_arguments(left: Bytes, right: Bytes) -> Bool {
            Bytes::eq(&left, &right)
        }
        get_zero() -> Result<u8, BytesIndexError> {
            let text = "abc";
            let value = String::as_bytes(&text);
            Bytes::get(&value, 0)
        }
        get_len() -> Result<u8, BytesIndexError> {
            let text = "abc";
            let value = String::as_bytes(&text);
            Bytes::get(&value, 3)
        }
        get_past_len() -> Result<u8, BytesIndexError> {
            let text = "abc";
            let value = String::as_bytes(&text);
            Bytes::get(&value, 4)
        }
        slice_valid() -> Result<Bytes, BytesRangeError> {
            let text = "abcd";
            let value = String::as_bytes(&text);
            Bytes::slice(&value, 1, 3)
        }
        slice_reversed() -> Result<Bytes, BytesRangeError> {
            let text = "abcd";
            let value = String::as_bytes(&text);
            Bytes::slice(&value, 3, 1)
        }
        slice_oob() -> Result<Bytes, BytesRangeError> {
            let text = "abcd";
            let value = String::as_bytes(&text);
            Bytes::slice(&value, 0, 5)
        }
        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "distributed-safe-bytes.glorious",
            source,
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
            vm.run(function("empty_string"), vec![]).unwrap(),
            VmValue::Text("".into())
        );

        let bool_type = artifact.functions[function("empty_string_is_empty") as usize].return_type;
        let truth = || VmValue::aggregate_with_variant(bool_type, Some(0), [VmValue::Unit]);
        let falsehood = || VmValue::aggregate_with_variant(bool_type, Some(1), [VmValue::Unit]);

        let equality_loop = function("__g1_bytes_eq_at");
        let mut ordinary_recursive_edges = 0;
        let mut tail_recursive_edges = 0;
        for generated in artifact
            .functions
            .iter()
            .filter(|generated| generated.name.starts_with("$handler$"))
        {
            for instruction in &artifact.code[generated.code_start as usize
                ..(generated.code_start + generated.code_len) as usize]
            {
                match instruction {
                    grandiose_vm::Instruction::Call { function, .. }
                        if *function == equality_loop =>
                    {
                        ordinary_recursive_edges += 1;
                    }
                    grandiose_vm::Instruction::TailCall { function, .. }
                        if *function == equality_loop =>
                    {
                        tail_recursive_edges += 1;
                    }
                    _ => {}
                }
            }
        }
        assert_eq!(
            ordinary_recursive_edges, 0,
            "Bytes::eq retained a recursive handler Call at {optimization_level:?}"
        );
        assert!(
            tail_recursive_edges >= 2,
            "both the initial and looping Bytes::eq handler paths must tail-call at {optimization_level:?}"
        );

        for name in [
            "empty_string_is_empty",
            "empty_bytes_is_empty",
            "equal_bytes",
            "equal_empty_bytes",
        ] {
            assert_eq!(vm.run(function(name), vec![]).unwrap(), truth(), "{name}");
        }
        for name in [
            "nonempty_string_is_empty",
            "nonempty_bytes_is_empty",
            "unequal_byte_bytes",
            "unequal_length_bytes",
        ] {
            assert_eq!(
                vm.run(function(name), vec![]).unwrap(),
                falsehood(),
                "{name}"
            );
        }

        if optimization_level == OptimizationLevel::O1 {
            let large_equal = vec![b'a'; 32 * 1024];
            let mut large_common_prefix = large_equal.clone();
            *large_common_prefix.last_mut().unwrap() = b'b';
            assert_eq!(
                vm.run(
                    function("equal_byte_arguments"),
                    vec![
                        VmValue::Bytes(large_equal.clone().into()),
                        VmValue::Bytes(large_equal.into()),
                    ],
                )
                .unwrap(),
                truth(),
                "large equal Bytes must execute in constant call-frame space"
            );
            assert_eq!(
                vm.run(
                    function("equal_byte_arguments"),
                    vec![
                        VmValue::Bytes(vec![b'a'; 32 * 1024].into()),
                        VmValue::Bytes(large_common_prefix.into()),
                    ],
                )
                .unwrap(),
                falsehood(),
                "large final-byte mismatch must preserve equality semantics"
            );
        }

        let get_type = artifact.functions[function("get_zero") as usize].return_type;
        let grandiose_vm::Type::Enum { variants, .. } =
            artifact.types[get_type as usize].representation()
        else {
            panic!("Bytes::get did not return Result")
        };
        let index_error_type = variants[1].fields[0].ty;
        assert_eq!(
            vm.run(function("get_zero"), vec![]).unwrap(),
            VmValue::aggregate_with_variant(get_type, Some(0), [VmValue::U64(97)])
        );
        let index_error = || {
            VmValue::aggregate_with_variant(
                get_type,
                Some(1),
                [VmValue::aggregate_with_variant(
                    index_error_type,
                    Some(0),
                    [],
                )],
            )
        };
        assert_eq!(vm.run(function("get_len"), vec![]).unwrap(), index_error());
        assert_eq!(
            vm.run(function("get_past_len"), vec![]).unwrap(),
            index_error()
        );

        let slice_type = artifact.functions[function("slice_valid") as usize].return_type;
        let grandiose_vm::Type::Enum { variants, .. } =
            artifact.types[slice_type as usize].representation()
        else {
            panic!("Bytes::slice did not return Result")
        };
        let range_error_type = variants[1].fields[0].ty;
        assert_eq!(
            vm.run(function("slice_valid"), vec![]).unwrap(),
            VmValue::aggregate_with_variant(
                slice_type,
                Some(0),
                [VmValue::Bytes((&b"bc"[..]).into())]
            )
        );
        let range_error = |variant| {
            VmValue::aggregate_with_variant(
                slice_type,
                Some(1),
                [VmValue::aggregate_with_variant(
                    range_error_type,
                    Some(variant),
                    [],
                )],
            )
        };
        assert_eq!(
            vm.run(function("slice_reversed"), vec![]).unwrap(),
            range_error(0),
            "a reversed range must return Err without executing bytes.slice"
        );
        assert_eq!(
            vm.run(function("slice_oob"), vec![]).unwrap(),
            range_error(1),
            "an out-of-bounds range must return Err without executing bytes.slice"
        );
    }
}

#[test]
fn distributed_utf8_validation_and_text_slicing_are_safe_and_tail_recursive() {
    let source = r#"
        parse(value: Bytes) -> Result<String, Utf8Error> {
            String::from_utf8(move value)
        }
        slice_text(
            value: String,
            start: usize,
            end: usize
        ) -> Result<String, TextRangeError> {
            String::slice(&value, Range { start: move start, end: move end })
        }
        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "distributed-utf8.glorious",
            source,
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
        let parse = function("parse");
        let slice = function("slice_text");
        let parse_type = artifact.functions[parse as usize].return_type;
        let grandiose_vm::Type::Enum { variants, .. } =
            artifact.types[parse_type as usize].representation()
        else {
            panic!("String::from_utf8 did not return Result")
        };
        let utf8_error_type = variants[1].fields[0].ty;
        let parse_ok = |text: &str| {
            VmValue::aggregate_with_variant(parse_type, Some(0), [VmValue::Text(text.into())])
        };
        let parse_err = |valid_up_to: u64| {
            VmValue::aggregate_with_variant(
                parse_type,
                Some(1),
                [VmValue::aggregate(
                    utf8_error_type,
                    [VmValue::U64(valid_up_to)],
                )],
            )
        };
        let vm = Vm::new(verified);

        for (bytes, text) in [
            (&b""[..], ""),
            (&b"plain ASCII"[..], "plain ASCII"),
            (&[0xc2, 0x80][..], "\u{80}"),
            (&[0xdf, 0xbf][..], "\u{7ff}"),
            (&[0xe0, 0xa0, 0x80][..], "\u{800}"),
            (&[0xed, 0x9f, 0xbf][..], "\u{d7ff}"),
            (&[0xee, 0x80, 0x80][..], "\u{e000}"),
            (&[0xc2, 0xa2][..], "¢"),
            (&[0xe2, 0x82, 0xac][..], "€"),
            (&[0xf0, 0x90, 0x80, 0x80][..], "\u{10000}"),
            (&[0xf4, 0x8f, 0xbf, 0xbf][..], "\u{10ffff}"),
            (&[0xf0, 0x9f, 0x92, 0xa9][..], "💩"),
            (
                &[b'a', 0xc2, 0xa2, 0xe2, 0x82, 0xac, 0xf0, 0x9f, 0x92, 0xa9][..],
                "a¢€💩",
            ),
        ] {
            assert_eq!(
                vm.run(parse, vec![VmValue::Bytes(bytes.into())]).unwrap(),
                parse_ok(text),
                "valid UTF-8 rejected at {optimization_level:?}: {bytes:?}"
            );
        }

        for (bytes, valid_up_to) in [
            (&[0xc0, 0x80][..], 0),
            (&[0xe0, 0x80, 0x80][..], 0),
            (&[0xed, 0xa0, 0x80][..], 0),
            (&[0xf0, 0x8f, 0xbf, 0xbf][..], 0),
            (&[0xf4, 0x90, 0x80, 0x80][..], 0),
            (&[0xf5, 0x80, 0x80, 0x80][..], 0),
            (&[0x80][..], 0),
            (&[0xc2][..], 0),
            (&[0xe2, 0x82][..], 0),
            (&[0xf0, 0x9f, 0x92][..], 0),
            (&[0xc2, b'A'][..], 0),
            (&[b'a', b'b', 0xed, 0xa0, 0x80][..], 2),
            (&[b'a', b'b', 0xf0, 0x9f, 0x92][..], 2),
        ] {
            assert_eq!(
                vm.run(parse, vec![VmValue::Bytes(bytes.into())]).unwrap(),
                parse_err(valid_up_to),
                "invalid UTF-8 had the wrong valid_up_to at {optimization_level:?}: {bytes:?}"
            );
        }

        let slice_type = artifact.functions[slice as usize].return_type;
        let grandiose_vm::Type::Enum { variants, .. } =
            artifact.types[slice_type as usize].representation()
        else {
            panic!("String::slice did not return Result")
        };
        let text_range_error_type = variants[1].fields[0].ty;
        let slice_ok = |text: &str| {
            VmValue::aggregate_with_variant(slice_type, Some(0), [VmValue::Text(text.into())])
        };
        let slice_err = |variant| {
            VmValue::aggregate_with_variant(
                slice_type,
                Some(1),
                [VmValue::aggregate_with_variant(
                    text_range_error_type,
                    Some(variant),
                    [],
                )],
            )
        };
        let run_slice = |start, end| {
            vm.run(
                slice,
                vec![
                    VmValue::Text("aé💩z".into()),
                    VmValue::U64(start),
                    VmValue::U64(end),
                ],
            )
            .unwrap()
        };
        assert_eq!(run_slice(1, 3), slice_ok("é"));
        assert_eq!(run_slice(3, 7), slice_ok("💩"));
        assert_eq!(run_slice(0, 0), slice_ok(""));
        assert_eq!(run_slice(8, 8), slice_ok(""));
        assert_eq!(run_slice(3, 1), slice_err(0));
        assert_eq!(run_slice(9, 1), slice_err(0), "reversed takes precedence");
        assert_eq!(run_slice(0, 9), slice_err(1));
        assert_eq!(run_slice(9, 9), slice_err(1));
        assert_eq!(run_slice(2, 3), slice_err(2));
        assert_eq!(run_slice(1, 2), slice_err(2));

        let validator = function("__g1_utf8_validate_at");
        let continuations = function("__g1_utf8_continuations");
        let mut ordinary_recursive_edges = 0;
        let mut tail_recursive_edges = 0;
        for generated in artifact
            .functions
            .iter()
            .filter(|generated| generated.name.starts_with("$handler$"))
        {
            for instruction in &artifact.code[generated.code_start as usize
                ..(generated.code_start + generated.code_len) as usize]
            {
                match instruction {
                    grandiose_vm::Instruction::Call { function, .. }
                        if *function == validator || *function == continuations =>
                    {
                        ordinary_recursive_edges += 1;
                    }
                    grandiose_vm::Instruction::TailCall { function, .. }
                        if *function == validator || *function == continuations =>
                    {
                        tail_recursive_edges += 1;
                    }
                    _ => {}
                }
            }
        }
        assert!(
            ordinary_recursive_edges <= 1,
            "UTF-8 recursion retained an ordinary Call at {optimization_level:?}"
        );
        assert!(
            tail_recursive_edges >= 2,
            "UTF-8 recursion must lower to tail calls at {optimization_level:?}"
        );

        if optimization_level == OptimizationLevel::O1 {
            let large = vec![b'a'; 32 * 1024];
            let expected = std::str::from_utf8(&large).unwrap().to_owned();
            assert_eq!(
                vm.run(parse, vec![VmValue::Bytes(large.into())]).unwrap(),
                parse_ok(&expected),
                "large UTF-8 input must execute in constant call-frame space"
            );
        }
    }
}

#[test]
fn distributed_utf8_internal_validation_helpers_cannot_reach_the_trapping_leaf() {
    let artifact = compile_source_to_bytecode(
        "direct-utf8-helper.glorious",
        r#"
            skip_prefix(value: Bytes, index: usize) -> Result<(), Utf8Error> {
                __g1_utf8_validate_at(move value, move index)
            }
            direct_second(
                value: Bytes,
                start: usize,
                minimum: u8,
                maximum: u8,
                end: usize
            ) -> Result<(), Utf8Error> {
                __g1_utf8_second(
                    move value, move start, move minimum, move maximum, move end
                )
            }
            direct_continuations(
                value: Bytes,
                start: usize,
                cursor: usize,
                end: usize
            ) -> Result<(), Utf8Error> {
                __g1_utf8_continuations(
                    move value, move start, move cursor, move end
                )
            }
            direct_four(
                value: Bytes,
                index: usize,
                lead: u8
            ) -> Result<(), Utf8Error> {
                __g1_utf8_validate_four(
                    move value, move index, move lead
                )
            }
            direct_slice(
                value: Bytes,
                start: usize,
                end: usize
            ) -> Result<String, TextRangeError> {
                __g1_string_slice_bounds(
                    move value, move start, move end
                )
            }
            main() -> () { () }
        "#,
    )
    .unwrap();
    let skip = artifact
        .functions
        .iter()
        .position(|function| function.name == "skip_prefix")
        .unwrap() as u32;
    let result_type = artifact.functions[skip as usize].return_type;
    let vm = Vm::new(verify(artifact).unwrap());
    assert_eq!(
        vm.run(
            skip,
            vec![VmValue::Bytes((&[0x80][..]).into()), VmValue::U64(1)],
        )
        .unwrap(),
        VmValue::aggregate_with_variant(result_type, Some(0), [VmValue::Unit]),
        "a direct helper call may skip validation, but must only return a non-authoritative unit proof"
    );
    for (name, args) in [
        (
            "direct_second",
            vec![
                VmValue::Bytes((&[0xc2][..]).into()),
                VmValue::U64(u64::MAX),
                VmValue::U64(128),
                VmValue::U64(191),
                VmValue::U64(u64::MAX),
            ],
        ),
        (
            "direct_continuations",
            vec![
                VmValue::Bytes((&[0x80][..]).into()),
                VmValue::U64(0),
                VmValue::U64(u64::MAX),
                VmValue::U64(0),
            ],
        ),
        (
            "direct_four",
            vec![
                VmValue::Bytes((&[0xf4][..]).into()),
                VmValue::U64(u64::MAX),
                VmValue::U64(244),
            ],
        ),
    ] {
        let helper = vm
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert!(
            vm.run(helper, args).is_ok(),
            "direct call to {name} must be total"
        );
    }
    let direct_slice = vm
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "direct_slice")
        .unwrap() as u32;
    for (bytes, start, end) in [
        (&[0xc2][..], 0, 1),
        (&[b'a'][..], 1, 0),
        (&[b'a'][..], 0, 2),
    ] {
        assert!(
            vm.run(
                direct_slice,
                vec![
                    VmValue::Bytes(bytes.into()),
                    VmValue::U64(start),
                    VmValue::U64(end),
                ],
            )
            .is_ok(),
            "direct calls to ordinary slice helpers must not reach a trapping leaf"
        );
    }
}

#[test]
fn distributed_utf8_and_text_slice_have_recovery_parity() {
    let result = run_source(
        "utf8-recovery.glorious",
        r#"
            effect ParseObserved {
                inspect(value: Result<String, Utf8Error>) -> !;
            }
            effect SliceObserved {
                inspect(value: Result<String, TextRangeError>) -> !;
            }
            byte(value: u8) -> u8 { value }
            main() -> usize {
                let values = Vec::new();
                Vec::push(&mut values, byte(97));
                Vec::push(&mut values, byte(237));
                Vec::push(&mut values, byte(160));
                Vec::push(&mut values, byte(128));
                let bytes = Bytes::from_vec(move values);
                let invalid_offset = handle perform ParseObserved::inspect(
                    String::from_utf8(move bytes)
                ) {
                    ParseObserved::inspect(Result::Ok(_)) => 1000,
                    ParseObserved::inspect(Result::Err(error)) =>
                        error.valid_up_to
                };
                let text = "aéz";
                let slice_length = handle perform SliceObserved::inspect(
                    String::slice(&text, Range { start: 1, end: 3 })
                ) {
                    SliceObserved::inspect(Result::Ok(piece)) =>
                        String::byte_len(&piece),
                    SliceObserved::inspect(Result::Err(_)) => 1000
                };
                move invalid_offset + move slice_length
            }
        "#,
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, Value::Int(3));
}

#[test]
fn bytes_from_vec_consumes_the_vec_shell() {
    let errors = compile_source_to_bytecode(
        "bytes-from-vec-move.glorious",
        r#"
            empty_bytes() -> Vec<u8> { Vec::new() }
            bad() -> usize {
                let values = empty_bytes();
                let bytes = Bytes::from_vec(move values);
                Bytes::len(&bytes) + Vec::len(&values)
            }
            main() -> () { () }
        "#,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| error.message.contains("moved")),
        "{errors:#?}"
    );
}

#[test]
fn distributed_vec_preserves_linear_push_obligations_across_its_public_boundary() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        make_ticket() -> Ticket { Ticket { serial: 42 } }
        empty_tickets() -> Vec<Ticket> { Vec::new() }
        make_tickets() -> Vec<Ticket> {
            let values = empty_tickets();
            Vec::push(&mut values, make_ticket());
            values
        }
        main() -> () { () }
    "#;
    verify(compile_source_to_bytecode("linear-vec.glorious", source).unwrap()).unwrap();
}

#[test]
fn distributed_vec_index_methods_are_explicitly_trapping() {
    let source = r#"
        empty_values() -> Vec<i64> { Vec::new() }
        main() -> () {
            let values = empty_values();
            Vec::index(&values, 0);
            ()
        }
    "#;
    let artifact = compile_source_to_bytecode("trapping-vec-index.glorious", source).unwrap();
    let entry = artifact.entry_function.unwrap();
    let error = Vm::new(verify(artifact).unwrap())
        .run(entry, vec![])
        .unwrap_err();
    assert!(error.to_string().contains("out of bounds"), "{error}");

    let errors = run_source(
        "interpreted-trapping-vec-index.glorious",
        source,
        Vec::new(),
        &mut NoHost,
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("out of bounds")),
        "{errors:#?}"
    );
}

#[test]
fn distributed_vec_storage_is_private_and_has_no_drained_shell_escape() {
    for body in [
        "steal(value: Vec<i64>) -> Array<i64> { value.storage }",
        "steal_ref(value: &Vec<i64>) -> &Array<i64> { &value.storage }",
        "open(value: Vec<i64>) -> Array<i64> { let Vec { storage } = value; storage }",
    ] {
        let source = format!("{body} main() -> () {{ () }}");
        let errors = compile_source_to_bytecode("private-vec.glorious", &source)
            .expect_err("user code projected or deconstructed Vec's private Array storage");
        assert!(
            errors.iter().any(|error| {
                error.message.contains("private")
                    && error.message.contains("storage")
                    && error.message.contains("defining source segment")
            }),
            "{errors:#?}"
        );
    }

    let errors = compile_source_to_bytecode(
        "no-vec-finish.glorious",
        "finish(value: Vec<i64>) -> () { Vec::finish_drained(move value) } main() -> () { () }",
    )
    .expect_err("the internal drained-shell transition acquired a public Vec alias");
    assert!(
        errors
            .iter()
            .any(|error| { error.message.contains("unknown") && error.message.contains("Vec") }),
        "{errors:#?}"
    );
}

#[test]
fn raw_bundles_do_not_acquire_distributed_vec_names() {
    let source = "main() -> Vec<i64> { Vec::new() }";
    let raw = SourceBundle::raw_for_conformance(
        Segment::new("empty-std.glorious", ""),
        Segment::new("raw.glorious", source),
        [],
    );
    let compile_errors = compile_bundle_to_bytecode(&raw).unwrap_err();
    assert!(
        compile_errors.iter().any(|error| error
            .message
            .contains("must return a supported monomorphic type")),
        "{compile_errors:#?}"
    );
    let interpreter_errors = run_bundle(&raw, Vec::new(), &mut NoHost).unwrap_err();
    assert!(
        interpreter_errors
            .iter()
            .any(|error| error.message.contains("unknown value `Vec::new`")),
        "{interpreter_errors:#?}"
    );
}

#[test]
fn standard_option_and_truth_names_are_not_compiler_or_interpreter_intrinsics() {
    let source = "main() -> Option<i64> { Option::Some(42) }";
    let raw = SourceBundle::raw_for_conformance(
        Segment::new("empty-std.glorious", ""),
        Segment::new("raw.glorious", source),
        [],
    );
    let compile_errors = compile_bundle_to_bytecode(&raw).unwrap_err();
    assert!(
        compile_errors.iter().any(|error| error
            .message
            .contains("must return a supported monomorphic type")),
        "{compile_errors:#?}"
    );
    let interpreter_errors = run_bundle(&raw, Vec::new(), &mut NoHost).unwrap_err();
    assert!(
        interpreter_errors
            .iter()
            .any(|error| error.message.contains("unknown value `Option::Some`")),
        "{interpreter_errors:#?}"
    );
}

#[test]
fn distributed_standard_names_keep_ordinary_duplicate_diagnostics() {
    let source = "type Bool = i64; main() -> { () }";
    let bundle = SourceBundle::distributed(Segment::new("duplicate.glorious", source), []);
    let diagnostics = compile_bundle_to_bytecode(&bundle).unwrap_err();
    let duplicate = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.title == "type declared more than once")
        .expect("missing duplicate standard-library alias diagnostic");
    let mapped = bundle.map_diagnostic(duplicate);
    assert_eq!(mapped.span.unwrap().segment.name(), "duplicate.glorious");
    assert!(
        mapped
            .related
            .iter()
            .any(|(span, _)| span.segment.name() == "<grandiose:std>")
    );
}

#[test]
fn source_facing_compilation_localizes_spans_after_the_embedded_standard_library() {
    let source = "main() -> i64 { @ }";
    let diagnostic = compile_source_to_bytecode("primary.glorious", source)
        .unwrap_err()
        .remove(0);
    assert_eq!(diagnostic.source_name, "primary.glorious");
    let span = diagnostic.span.expect("lexer diagnostic must have a span");
    assert_eq!(&source[span.range()], "@");
}

#[test]
fn source_facing_entry_diagnostics_keep_the_primary_source_name() {
    let source = "answer() -> i64 { 42 }";
    let compiled = compile_source_to_bytecode("compile.glorious", source)
        .unwrap_err()
        .into_iter()
        .find(|diagnostic| diagnostic.span.is_none())
        .expect("missing-main compilation diagnostic");
    assert_eq!(compiled.source_name, "compile.glorious");

    let interpreted = run_source("run.glorious", source, Vec::new(), &mut NoHost)
        .unwrap_err()
        .into_iter()
        .find(|diagnostic| diagnostic.span.is_none())
        .expect("missing-main interpreter diagnostic");
    assert_eq!(interpreted.source_name, "run.glorious");
}

#[test]
fn inserted_boundary_separates_tokens_and_line_comments() {
    let tokens = SourceBundle::new(
        Segment::new("std-lib.glorious", "alpha"),
        Segment::new("main.glorious", "beta"),
        [],
    );
    let identifiers = lexer::lex(tokens.source())
        .unwrap()
        .into_iter()
        .filter_map(|token| match token.kind {
            TokenKind::Ident(name) => Some(name),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(identifiers, ["alpha", "beta"]);

    let commented = SourceBundle::new(
        Segment::new("std-lib.glorious", "// final standard-library comment"),
        Segment::new("main.glorious", "main() -> i64 { 42 }"),
        [],
    );
    assert_eq!(
        run_bundle(&commented, Vec::new(), &mut NoHost).unwrap(),
        Value::Int(42)
    );
}

#[test]
fn bundle_runs_with_one_shared_value_namespace() {
    let bundle = SourceBundle::new(
        Segment::new("std-lib.glorious", "answer() -> i64 { 42 }"),
        Segment::new("main.glorious", "main() -> i64 { answer() }"),
        [Segment::new(
            "later.glorious",
            "unused() -> i64 { answer() }",
        )],
    );
    assert_eq!(
        run_bundle(&bundle, Vec::new(), &mut NoHost).unwrap(),
        Value::Int(42)
    );
}

#[test]
fn duplicates_across_files_are_ordinary_global_errors_with_local_mappings() {
    let first = "duplicate() -> i64 { 1 }";
    let second = "duplicate() -> i64 { 2 }\nmain() -> i64 { 0 }";
    let bundle = SourceBundle::new(
        Segment::new("std-lib.glorious", first),
        Segment::new("main.glorious", second),
        [],
    );
    let diagnostics = run_bundle(&bundle, Vec::new(), &mut NoHost).unwrap_err();
    let duplicate = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.title == "callable declared more than once")
        .unwrap();
    let mapped = bundle.map_diagnostic(duplicate);

    let primary = mapped.span.unwrap();
    assert_eq!(primary.segment.name(), "main.glorious");
    assert_eq!(&second[primary.span.range()], "duplicate() -> i64 { 2 }");
    assert_eq!(mapped.related.len(), 1);
    assert_eq!(mapped.related[0].0.segment.name(), "std-lib.glorious");
    assert_eq!(&first[mapped.related[0].0.span.range()], first);
}

#[test]
fn lexer_diagnostic_maps_to_its_original_file_and_byte_offset() {
    let primary = "main() -> i64 { 0 }";
    let additional = "  @";
    let bundle = SourceBundle::new(
        Segment::new("std-lib.glorious", ""),
        Segment::new("main.glorious", primary),
        [Segment::new("broken.glorious", additional)],
    );
    let diagnostic = run_bundle(&bundle, Vec::new(), &mut NoHost)
        .unwrap_err()
        .remove(0);
    let mapped = bundle.map_diagnostic(&diagnostic).span.unwrap();
    assert_eq!(mapped.segment.name(), "broken.glorious");
    assert_eq!(mapped.span, Span::new(2, 3));
    assert_eq!(&additional[mapped.span.range()], "@");
}

#[test]
fn rendering_names_both_files_for_cross_file_related_labels() {
    let bundle = SourceBundle::new(
        Segment::new("std-lib.glorious", "same() -> i64 { 1 }"),
        Segment::new("main.glorious", "same() -> i64 { 2 }\nmain() -> i64 { 0 }"),
        [],
    );
    let diagnostic = run_bundle(&bundle, Vec::new(), &mut NoHost)
        .unwrap_err()
        .remove(0);
    let mut rendered = Vec::new();
    bundle.write_diagnostic(&diagnostic, &mut rendered).unwrap();
    let rendered = String::from_utf8(rendered).unwrap();
    assert!(rendered.contains("main.glorious"));
    assert!(rendered.contains("std-lib.glorious"));
}

#[test]
fn private_fields_allow_defining_segment_deconstruction_and_cross_segment_transfer() {
    let defining = r#"
        struct Vault { private secret: i64, visible: i64 }
        make() -> Vault { Vault { secret: 40, visible: 2 } }
        inspect(value: Vault) -> i64 { value.secret }
        open(value: Vault) -> i64 {
            let Vault { secret, visible } = value;
            secret + visible
        }
    "#;
    let caller = r#"
        public_projection(value: Vault) -> i64 { value.visible }
        main() -> { open(make()); () }
    "#;
    let bundle = SourceBundle::new(
        Segment::new("vault.glorious", defining),
        Segment::new("caller.glorious", caller),
        [],
    );
    verify(compile_bundle_to_bytecode(&bundle).unwrap()).unwrap();
}

#[test]
fn field_visibility_is_erased_from_runtime_and_phase_fingerprints() {
    let public = r#"
        struct Vault {         secret: i64 }
        inspect(value: Vault) -> i64 { value.secret }
        main() -> { inspect(Vault { secret: 42 }); () }
    "#;
    let private = r#"
        struct Vault { private secret: i64 }
        inspect(value: Vault) -> i64 { value.secret }
        main() -> { inspect(Vault { secret: 42 }); () }
    "#;
    let public = compile_source_to_phases("public.glorious", public).unwrap();
    let private = compile_source_to_phases("private.glorious", private).unwrap();
    assert_eq!(public.artifact.encode(), private.artifact.encode());
    assert_eq!(
        public.provisional_fingerprint(),
        private.provisional_fingerprint()
    );
    assert_eq!(public.core_fingerprint(), private.core_fingerprint());
    assert_eq!(public.mir_fingerprint(), private.mir_fingerprint());
}

#[test]
fn private_fields_reject_cross_segment_projection_even_with_equal_segment_names() {
    let bundle = SourceBundle::new(
        Segment::new(
            "same.glorious",
            "struct Vault { private secret: i64, visible: i64 } make() -> Vault { Vault { secret: 40, visible: 2 } }",
        ),
        Segment::new(
            "same.glorious",
            "peek(value: Vault) -> i64 { value.secret } main() -> { peek(make()); () }",
        ),
        [],
    );
    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1BC002")
                && error.message.contains("private field `secret`")
                && error.message.contains("defining source segment")
        }),
        "{errors:#?}"
    );
}

#[test]
fn private_fields_reject_cross_segment_struct_deconstruction() {
    for caller in [
        "open(value: Vault) -> i64 { let Vault { secret, visible } = value; secret + visible } main() -> { open(make()); () }",
        "open(value: Vault) -> i64 { let Vault { visible } = value; visible } main() -> { open(make()); () }",
        "open(value: Vault) -> i64 { let Vault { visible, .. } = value; visible } main() -> { open(make()); () }",
    ] {
        let bundle = SourceBundle::new(
            Segment::new(
                "vault.glorious",
                "struct Vault { private secret: i64, visible: i64 } make() -> Vault { Vault { secret: 40, visible: 2 } }",
            ),
            Segment::new("caller.glorious", caller),
            [],
        );
        let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1BC002")
                    && error.message.contains("private-field authority")
                    && error.message.contains("`secret`")
                    && error.message.contains("deconstruction")
                    && error.message.contains("defining source segment")
            }),
            "{errors:#?}"
        );
    }
}
