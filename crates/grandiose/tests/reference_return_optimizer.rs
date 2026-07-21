use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Value, Vm, verify};

const SOURCE: &str = r#"
    u64_vec() -> Vec<u64> { Vec::new() }
    push(value: &mut Vec<u64>, item: u64) -> () {
        Vec::push(move value, move item)
    }

    score() -> u64 {
        let values = u64_vec();
        push(&mut values, 41);
        let first = Vec::index(&values, 0);
        *first
    }

    main() -> () { () }
"#;

#[test]
fn optimized_reference_return_keeps_the_borrowed_owner_live() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "reference-return-optimizer.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let entry = artifact
            .functions
            .iter()
            .position(|function| function.name == "score")
            .expect("missing score") as u32;
        let vm = Vm::new(verify(artifact).expect("compiler output must verify"));
        assert_eq!(
            vm.run(entry, vec![]).expect("score must execute"),
            Value::U64(41),
            "{optimization_level:?}",
        );
    }
}
