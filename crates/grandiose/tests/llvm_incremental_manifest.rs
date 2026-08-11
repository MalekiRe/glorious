use std::collections::BTreeMap;

use grandiose::{
    compile_source_to_phases_with_options, llvm_incremental_manifest, LlvmOptions,
    OptimizationLevel,
};

fn phases(source: &str) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        "llvm-incremental-manifest.glorious",
        source,
        grandiose::CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap()
}

fn declarations(phases: &grandiose::CompiledPhases) -> BTreeMap<String, u32> {
    phases
        .mir
        .functions
        .iter()
        .map(|function| (function.name.clone(), function.declaration))
        .collect()
}

#[test]
fn body_only_change_rebuilds_the_changed_leaf_not_its_direct_caller() {
    let before = phases(
        r#"
            first() -> i64 { 1 }
            second() -> i64 { first() }
            main() -> () { second(); () }
        "#,
    );
    let after = phases(
        r#"
            first() -> i64 { 2 }
            second() -> i64 { first() }
            main() -> () { second(); () }
        "#,
    );
    let options = LlvmOptions::default();
    let before_manifest = llvm_incremental_manifest(&before, &options);
    let after_manifest = llvm_incremental_manifest(&after, &options);
    let declarations = declarations(&after);
    let invalidated = after_manifest.invalidated_functions(&before_manifest);

    assert!(invalidated.contains(&declarations["first"]));
    assert!(!invalidated.contains(&declarations["second"]));
    assert!(!invalidated.contains(&declarations["main"]));
}

#[test]
fn target_option_change_invalidates_every_fragment() {
    let phases = phases(
        r#"
            answer() -> i64 { 42 }
            main() -> () { () }
        "#,
    );
    let base = LlvmOptions::default();
    let mut changed = base.clone();
    changed.emit_entry_wrapper = !changed.emit_entry_wrapper;
    let before = llvm_incremental_manifest(&phases, &base);
    let after = llvm_incremental_manifest(&phases, &changed);
    let expected = after
        .functions
        .iter()
        .map(|function| function.declaration)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(after.invalidated_functions(&before), expected);
}
