use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

#[test]
fn step_budget_is_monotonic_and_failed_spends_are_atomic_at_o0_through_o3() {
    let source = r#"
        spend() -> usize {
            let budget = StepBudget::new(5);
            StepBudget::try_take(&mut budget, 3);
            StepBudget::remaining(&budget)
        }
        reject() -> usize {
            let budget = StepBudget::new(5);
            StepBudget::try_take(&mut budget, 6);
            StepBudget::remaining(&budget)
        }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "step-budget.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(artifact.clone())
                .run(function_id(&phases.artifact, "spend"), vec![])
                .unwrap(),
            Value::U64(2),
            "{optimization_level:?}"
        );
        assert_eq!(
            Vm::new(artifact)
                .run(function_id(&phases.artifact, "reject"), vec![])
                .unwrap(),
            Value::U64(5),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn user_code_cannot_replenish_step_budget_through_its_private_state() {
    let errors = compile_source_to_bytecode(
        "forge-step-budget.glorious",
        "cheat(value: StepBudget) -> StepBudget { value.remaining = 99; value } main() -> () { () }",
    )
    .expect_err("StepBudget state must remain owned by the defining standard-library segment");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("private field `remaining`")
                && error.message.contains("defining source segment")
        }),
        "{errors:#?}"
    );
}
