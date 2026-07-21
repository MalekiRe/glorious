use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Instruction, Value, Vm, verify};

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
            "assertion test performed a host effect",
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
    passing() -> i64 {
        assert(true);
        let left = 41;
        let right = 41;
        assert_eq(&left, &right);
        42
    }

    failed_assert() -> () { assert(false) }
    failed_equality() -> () {
        let left = 1;
        let right = 2;
        assert_eq(&left, &right)
    }
    explicit_abort() -> ! { abort() }
    impossible() -> ! { unreachable() }
    main() -> () { () }
"#;

#[test]
fn assertion_and_abort_wrappers_select_terminal_vm_abort_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "abort-assert-surface.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(artifact.clone()).unwrap();
        let vm = Vm::new(verified);

        assert_eq!(
            vm.run(function_id(&artifact, "passing"), vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}",
        );
        for name in [
            "failed_assert",
            "failed_equality",
            "explicit_abort",
            "impossible",
        ] {
            let error = vm
                .run(function_id(&artifact, name), vec![])
                .expect_err(name);
            assert!(
                error.to_string().contains("explicit source abort"),
                "{name} at {optimization_level:?}: {error}",
            );
        }

        let abort = &artifact.functions[function_id(&artifact, "__g1_abort") as usize];
        let instructions =
            &artifact.code[abort.code_start as usize..(abort.code_start + abort.code_len) as usize];
        assert_eq!(
            instructions,
            [Instruction::Abort {
                message: Some("explicit source abort".into()),
            }],
            "{optimization_level:?}",
        );
        let abort_function = function_id(&artifact, "__g1_abort");
        assert!(
            artifact
                .cleanups
                .iter()
                .filter(|plan| plan.function == abort_function)
                .all(|plan| plan.registers.is_empty()),
            "abort must not drop ordinary owners at {optimization_level:?}",
        );
    }
}

#[test]
fn recovery_execution_matches_passing_and_aborting_assertions() {
    let passing = run_source(
        "abort-assert-recovery-pass.glorious",
        &SOURCE.replace("main() -> () { () }", "main() -> i64 { passing() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(passing, RecoveryValue::Int(42));

    let errors = run_source(
        "abort-assert-recovery-fail.glorious",
        &SOURCE.replace("main() -> () { () }", "main() -> () { failed_assert() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("explicit source abort")),
        "{errors:#?}",
    );
}

#[test]
fn trusted_abort_leaf_cannot_be_called_directly_from_user_source() {
    let errors = compile_source_to_bytecode(
        "abort-leaf-forgery.glorious",
        "bad() -> ! { __g1_abort() } main() -> () { bad() }",
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("may be called only from their trusted standard-library")
        }),
        "{errors:#?}",
    );
}
