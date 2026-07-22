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
            "Slot recovery test performed a host effect",
            span,
        ))
    }
}

fn run(level: OptimizationLevel, name: &str) -> Value {
    let source = r#"
        slot_roundtrip() -> i64 {
            let slot = slot_filled(41);
            let replaced = slot_replace(&mut slot, 42);
            let taken = slot_take(&mut slot);
            let first = if(replaced is Option::Some(_)) { replaced.0 } else { 0 };
            let second = if(taken is Option::Some(_)) { taken.0 } else { 0 };
            first + second
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode_with_options(
        "slot.glorious",
        source,
        CompileOptions {
            optimization_level: level,
        },
    )
    .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
    let verified = verify(artifact).unwrap();
    let function = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap() as u32;
    Vm::new(verified).run(function, vec![]).unwrap()
}

#[test]
fn slot_reinitializes_moved_storage_at_every_optimization_level() {
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        assert_eq!(run(level, "slot_roundtrip"), Value::I64(83), "{level:?}");
    }
}

#[test]
fn slot_private_storage_cannot_be_destructured_by_user_source() {
    let errors = compile_source_to_bytecode(
        "private_slot.glorious",
        "steal(value: Slot<i64>) -> Option<i64> { let Slot { value } = move value; value } main() -> () { () }",
    )
    .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| { error.message.contains("private") || error.title.contains("private") }),
        "{errors:#?}"
    );
}

#[test]
fn slot_empty_is_inferred_from_its_result_context() {
    compile_source_to_bytecode(
        "empty-slot.glorious",
        "empty() -> Slot<i64> { slot_empty() } main() -> () { () }",
    )
    .unwrap();
}

#[test]
fn slot_has_recovery_evaluator_parity() {
    let result = run_source(
        "slot-recovery.glorious",
        "main() -> i64 { let slot = slot_filled(41); slot_replace(&mut slot, 42); let taken = slot_take(&mut slot); if(taken is Option::Some(_)) { taken.0 } else { 0 } }",
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(42));
}
