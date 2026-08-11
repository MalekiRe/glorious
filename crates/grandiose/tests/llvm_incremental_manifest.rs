use std::collections::BTreeMap;

use grandiose::{
    compile_source_to_phases_with_options, emit_llvm_ir, emit_llvm_ir_with_fragment_cache,
    llvm_incremental_manifest, LlvmFragmentCache, LlvmOptions, OptimizationLevel,
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

#[test]
fn fragment_cache_replays_metadata_and_returns_exact_canonical_ir() {
    let phases = phases(
        r#"
            answer() -> i64 { 42 }
            main() -> () { () }
        "#,
    );
    let options = LlvmOptions::default();
    let fresh = emit_llvm_ir(&phases, &options).unwrap();
    let mut cache = LlvmFragmentCache::default();
    let first = emit_llvm_ir_with_fragment_cache(&phases, &options, &mut cache).unwrap();
    assert_eq!(first, fresh);
    assert_eq!(cache.reused_fragments(), 0);

    let second = emit_llvm_ir_with_fragment_cache(&phases, &options, &mut cache).unwrap();
    assert_eq!(second, fresh);
    assert_eq!(
        cache.reused_fragments(),
        1,
        "only LLVM-reachable fragments are cached"
    );
    // The cache's fragment representation includes intrinsic and effect
    // callback metadata, which is replayed before module-scope declarations.
}

#[test]
fn fragment_cache_reuses_body_unchanged_callers_and_invalidates_interface_users() {
    let options = LlvmOptions::default();
    let initial = phases(
        r#"
            leaf() -> i64 { 1 }
            caller() -> i64 { leaf() }
            main() -> () { caller(); () }
        "#,
    );
    let body_changed = phases(
        r#"
            leaf() -> i64 { 2 }
            caller() -> i64 { leaf() }
            main() -> () { caller(); () }
        "#,
    );
    let interface_changed = phases(
        r#"
            leaf(argument: ()) -> i64 { 2 }
            caller() -> i64 { leaf(()) }
            main() -> () { caller(); () }
        "#,
    );
    let mut cache = LlvmFragmentCache::default();
    emit_llvm_ir_with_fragment_cache(&initial, &options, &mut cache).unwrap();
    let body_cached =
        emit_llvm_ir_with_fragment_cache(&body_changed, &options, &mut cache).unwrap();
    assert_eq!(body_cached, emit_llvm_ir(&body_changed, &options).unwrap());
    assert_eq!(
        cache.reused_fragments(),
        2,
        "caller and main must survive a leaf body edit"
    );

    let interface_cached =
        emit_llvm_ir_with_fragment_cache(&interface_changed, &options, &mut cache).unwrap();
    assert_eq!(
        interface_cached,
        emit_llvm_ir(&interface_changed, &options).unwrap()
    );
    assert_eq!(
        cache.reused_fragments(),
        1,
        "only main may survive a leaf ABI change"
    );
}
