use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Instruction, Value, Vm, verify};

const SOURCE: &str = r#"
    string_map() -> HashMap<String, u64> { HashMap::new() }

    entry<'a>(value: &'a mut HashMap<String, u64>, key: String, fallback: u64)
        -> &'a mut u64 {
        HashMapEntry::or_insert(HashMap::entry(move value, move key), move fallback)
    }

    unrelated<'a>(returned: &'a mut u64, other: &u64) -> &'a mut u64 {
        let view = &*other;
        *view;
        move returned
    }

    score() -> u64 {
        let map = string_map();
        let selected = entry(&mut map, "answer", 41);
        *selected = *selected + 1;
        *selected
    }

    main() -> () { () }
"#;

#[test]
fn entry_reference_return_survives_cfg_join_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "entry-return-reborrow.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let score = artifact
            .functions
            .iter()
            .position(|function| function.name == "score")
            .expect("missing score") as u32;
        let unrelated = artifact
            .functions
            .iter()
            .find(|function| function.name == "unrelated")
            .expect("missing unrelated-borrow control");
        let start = unrelated.code_start as usize;
        let end = start + unrelated.code_len as usize;
        assert!(
            artifact.code[start..end]
                .iter()
                .any(|instruction| matches!(instruction, Instruction::EndBorrow { .. })),
            "{optimization_level:?}: an unrelated dead borrow must still end normally",
        );
        let vm = Vm::new(verify(artifact).expect("compiler output must verify"));
        assert_eq!(
            vm.run(score, vec![]).expect("score must execute"),
            Value::U64(42),
            "{optimization_level:?}",
        );
    }
}
