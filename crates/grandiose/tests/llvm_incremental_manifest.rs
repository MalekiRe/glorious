use std::{
    collections::BTreeMap,
    fs,
    process::Command,
};

use grandiose::{
    compile_source_to_phases_with_options, emit_llvm_ir, emit_llvm_ir_with_fragment_cache,
    default_target_data_layout, emit_llvm_native_object_units,
    llvm_incremental_manifest, LlvmFragmentCache, LlvmOptions, OptimizationLevel,
};

fn phases(source: &str) -> grandiose::CompiledPhases {
    phases_at(source, OptimizationLevel::O2)
}

fn phases_at(source: &str, optimization_level: OptimizationLevel) -> grandiose::CompiledPhases {
    compile_source_to_phases_with_options(
        "llvm-incremental-manifest.glorious",
        source,
        grandiose::CompileOptions {
            optimization_level,
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
fn callee_abi_change_invalidates_only_direct_native_callers() {
    let initial = phases(
        r#"
            leaf() -> i64 { 1 }
            caller() -> i64 { leaf() }
            outer() -> i64 { caller() }
            main() -> () { outer(); () }
        "#,
    );
    let options = LlvmOptions::default();
    let previous = llvm_incremental_manifest(&initial, &options);
    let mut current = previous.clone();
    let declarations = declarations(&initial);
    let leaf = declarations["leaf"];
    let caller = declarations["caller"];
    let outer = declarations["outer"];
    let main = declarations["main"];

    // Model an ABI edit without changing a caller's own ABI. This is the
    // boundary separate object compilation needs: the direct call site must
    // rebuild, whereas its callers keep the same exported symbol/ABI and are
    // relinked unchanged.
    let leaf_entry = current
        .functions
        .iter_mut()
        .find(|function| function.declaration == leaf)
        .unwrap();
    leaf_entry.interface_fingerprint ^= 1;
    leaf_entry.fragment_fingerprint ^= 1;
    let caller_entry = current
        .functions
        .iter_mut()
        .find(|function| function.declaration == caller)
        .unwrap();
    caller_entry
        .callee_interfaces
        .iter_mut()
        .find(|callee| callee.declaration == leaf)
        .unwrap()
        .interface_fingerprint ^= 1;

    let invalidated = current.invalidated_functions(&previous);
    assert!(invalidated.contains(&leaf));
    assert!(
        invalidated.contains(&caller),
        "direct caller must rebuild for its callee ABI"
    );
    assert!(
        !invalidated.contains(&outer) && !invalidated.contains(&main),
        "an unchanged caller ABI permits relinking outer objects unchanged: {invalidated:?}"
    );
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
fn global_literal_table_change_invalidates_retained_native_fragments() {
    let before = phases_at(
        r#"
            literal_anchor() -> String { "z" }
            literal_edit() -> String { "zz" }
            main() -> () { let left = literal_anchor(); let right = literal_edit(); () }
        "#,
        OptimizationLevel::O0,
    );
    // `edited` changes only its own source body, but adding a lexically
    // earlier literal changes the module-global byte-literal index used by
    // `stable`. A function-object cache must not retain that stale address.
    let after = phases_at(
        r#"
            literal_anchor() -> String { "z" }
            literal_edit() -> String { "a" }
            main() -> () { let left = literal_anchor(); let right = literal_edit(); () }
        "#,
        OptimizationLevel::O0,
    );
    let options = LlvmOptions::default();
    let before_manifest = llvm_incremental_manifest(&before, &options);
    let after_manifest = llvm_incremental_manifest(&after, &options);
    let expected = after_manifest
        .functions
        .iter()
        .map(|function| function.declaration)
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(after_manifest.invalidated_functions(&before_manifest), expected);

    let before_units = emit_llvm_native_object_units(&before, &options).unwrap();
    let after_units = emit_llvm_native_object_units(&after, &options).unwrap();
    assert_ne!(before_units.shared_fingerprint, after_units.shared_fingerprint);
}

#[test]
fn native_partition_keys_bind_target_and_shared_entry_abi() {
    let phases = phases(
        r#"
            helper(value: i64) -> i64 { value + 1 }
            main() -> () { helper(41); () }
        "#,
    );
    let base_options = LlvmOptions::default();
    let base = emit_llvm_native_object_units(&phases, &base_options).unwrap();
    let function_keys = |units: &grandiose::LlvmNativeObjectUnits| {
        units
            .functions
            .iter()
            .map(|unit| (unit.declaration, unit.fragment_fingerprint))
            .collect::<BTreeMap<_, _>>()
    };

    let mut aarch64 = base_options.clone();
    aarch64.target_triple = "aarch64-unknown-linux-gnu".into();
    aarch64.target_data_layout = default_target_data_layout(&aarch64.target_triple).map(str::to_owned);
    let target_changed = emit_llvm_native_object_units(&phases, &aarch64).unwrap();
    assert_eq!(target_changed.shared.target_triple, aarch64.target_triple);
    assert_ne!(base.shared_fingerprint, target_changed.shared_fingerprint);
    assert_ne!(function_keys(&base), function_keys(&target_changed));

    let mut no_entry = base_options;
    no_entry.emit_entry_wrapper = false;
    let entry_changed = emit_llvm_native_object_units(&phases, &no_entry).unwrap();
    assert!(!entry_changed.shared.ir.contains("define i32 @main()"));
    assert_ne!(base.shared_fingerprint, entry_changed.shared_fingerprint);
    assert_ne!(function_keys(&base), function_keys(&entry_changed));
}

#[test]
fn native_function_units_exclude_unreferenced_sibling_abi_declarations() {
    let before = phases_at(
        r#"
            incremental_unit_changed() -> String { "changed" }
            incremental_unit_stable() -> String { "stable" }
            main() -> () {
                __g1_diagnostic_write(incremental_unit_changed());
                __g1_diagnostic_write(incremental_unit_stable());
                ()
            }
        "#,
        OptimizationLevel::O0,
    );
    let after = phases_at(
        r#"
            incremental_unit_changed(unused: ()) -> String { "changed" }
            incremental_unit_stable() -> String { "stable" }
            main() -> () {
                __g1_diagnostic_write(incremental_unit_changed(()));
                __g1_diagnostic_write(incremental_unit_stable());
                ()
            }
        "#,
        OptimizationLevel::O0,
    );
    let options = LlvmOptions::default();
    let before_units = emit_llvm_native_object_units(&before, &options).unwrap();
    let after_units = emit_llvm_native_object_units(&after, &options).unwrap();
    let before_declarations = declarations(&before);
    let after_declarations = declarations(&after);
    let stable_before = before_units
        .functions
        .iter()
        .find(|unit| unit.declaration == before_declarations["incremental_unit_stable"])
        .unwrap();
    let stable_after = after_units
        .functions
        .iter()
        .find(|unit| unit.declaration == after_declarations["incremental_unit_stable"])
        .unwrap();

    assert_eq!(
        stable_before.module.ir, stable_after.module.ir,
        "an unrelated sibling ABI must not alter a reusable function unit"
    );
    assert_ne!(before_units.shared_fingerprint, after_units.shared_fingerprint);
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

#[test]
fn native_function_units_compile_separately_and_link_through_wild() {
    let phases = phases(
        r#"
            leaf(value: i64) -> i64 { value + 1 }
            caller(value: i64) -> i64 { leaf(value) }
            main() -> () { caller(41); () }
        "#,
    );
    let units = emit_llvm_native_object_units(&phases, &LlvmOptions::default()).unwrap();
    assert_eq!(units.functions.len(), 3);
    assert!(units.shared.ir.contains("define i32 @main()"));
    for unit in &units.functions {
        let own = format!("@g1_f{}", unit.declaration);
        assert!(unit.module.ir.contains(&format!("define i64 {own}")) || unit.module.ir.contains(&format!("define void {own}")));
        assert!(
            !unit.module.ir.contains("define internal"),
            "function unit must import shared runtime helpers rather than duplicate them"
        );
    }

    let directory = tempfile::tempdir().unwrap();
    let shared_ir = directory.path().join("shared.ll");
    let shared_object = directory.path().join("shared.o");
    fs::write(&shared_ir, &units.shared.ir).unwrap();
    let compile = |input: &std::path::Path, output: &std::path::Path| {
        Command::new("clang")
            .args(["-x", "ir", "-O3", "-c"])
            .arg(input)
            .arg("-o")
            .arg(output)
            .status()
            .unwrap()
    };
    assert!(compile(&shared_ir, &shared_object).success());
    let mut objects = vec![shared_object];
    for unit in &units.functions {
        let input = directory.path().join(format!("function-{}.ll", unit.declaration));
        let output = directory.path().join(format!("function-{}.o", unit.declaration));
        fs::write(&input, &unit.module.ir).unwrap();
        assert!(compile(&input, &output).success(), "unit {}", unit.declaration);
        objects.push(output);
    }
    let executable = directory.path().join("native-units");
    assert!(
        Command::new("clang")
            .arg("--ld-path=wild")
            .args(&objects)
            .arg("-x")
            .arg("c")
            .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/src/native_host_runtime.c"))
            .arg(concat!(env!("CARGO_MANIFEST_DIR"), "/src/native_runtime.c"))
            .arg("-o")
            .arg(&executable)
            .status()
            .unwrap()
            .success()
    );
    assert!(Command::new(executable).status().unwrap().success());
}

#[test]
fn native_function_units_retain_effect_guard_runtime_declarations() {
    let phases = phases_at(
        r#"
            effect Ask { [1,1] ask() -> i64 }
            selected() -> i64 {
                let captured = 1;
                let answer = { => perform Ask::ask() + captured };
                handle { answer() } {
                    Ask::ask() with k => resume(k, 41)
                }
            }
            main() -> () {
                selected();
                ()
            }
        "#,
        OptimizationLevel::O0,
    );
    let units = emit_llvm_native_object_units(&phases, &LlvmOptions::default()).unwrap();
    let guard_symbols = units
        .shared
        .ir
        .lines()
        .filter_map(|line| {
            line.strip_prefix("declare void ")
                .and_then(|symbol| symbol.split_once('('))
                .map(|(symbol, _)| symbol)
                .filter(|symbol| symbol.starts_with("@g1_effect_guard_drop_f"))
        })
        .collect::<Vec<_>>();
    assert!(
        !guard_symbols.is_empty(),
        "effect fixture must exercise emitted guard-drop helpers"
    );

    let directory = tempfile::tempdir().unwrap();
    for unit in &units.functions {
        for symbol in &guard_symbols {
            assert!(
                unit.module.ir.contains(&format!("declare void {symbol}("))
                    || unit.module.ir.contains(&format!("define void {symbol}(")),
                "function unit {} lost shared effect helper {symbol}",
                unit.declaration,
            );
        }
        let input = directory.path().join(format!("effect-{}.ll", unit.declaration));
        let output = directory.path().join(format!("effect-{}.o", unit.declaration));
        fs::write(&input, &unit.module.ir).unwrap();
        assert!(
            Command::new("clang")
                .args(["-x", "ir", "-O3", "-c"])
                .arg(&input)
                .arg("-o")
                .arg(&output)
                .status()
                .unwrap()
                .success(),
            "effect function unit {} must compile independently",
            unit.declaration,
        );
    }
}
