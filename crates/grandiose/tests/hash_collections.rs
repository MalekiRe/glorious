use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
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
            "hash collection tests must not perform host effects",
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

const HASH_SURFACE: &str = r#"
    previous_or_zero(value: Option<u64>) -> u64 {
        if(value is Result::Ok(_)) { value.0 } else { 0 }
    }

    borrowed_or_zero(value: Option<&u64>) -> u64 {
        if(value is Result::Ok(_)) { *value.0 } else { 0 }
    }

    bool_score(value: Bool) -> u64 {
        if(value is Result::Ok(_)) { 1 } else { 0 }
    }

    string_map() -> HashMap<String, u64> { HashMap::new() }
    string_set() -> HashSet<String> { HashSet::new() }
    map_insert(
        value: &mut HashMap<String, u64>,
        key: String,
        item: u64
    ) -> Option<u64> {
        HashMap::insert(move value, move key, move item)
    }
    set_insert(value: &mut HashSet<String>, key: String) -> Bool {
        HashSet::insert(move value, move key)
    }
    set_capacity(value: &HashSet<String>) -> usize {
        HashSet::capacity(move value)
    }
    set_is_empty(value: &HashSet<String>) -> Bool {
        HashSet::is_empty(move value)
    }

    map_score() -> u64 {
        let map = string_map();
        map_insert(&mut map, "zero", 10);
        map_insert(&mut map, "one", 11);
        map_insert(&mut map, "two", 12);
        map_insert(&mut map, "three", 13);
        map_insert(&mut map, "four", 14);
        map_insert(&mut map, "five", 15);
        map_insert(&mut map, "six", 16);
        map_insert(&mut map, "seven", 17);
        map_insert(&mut map, "eight", 18);
        let replacement = map_insert(&mut map, "three", 99);
        let lookup = "three";
        wrapping_convert_to_u64(HashMap::len(&map)) * 1000
            + previous_or_zero(move replacement) * 10
            + borrowed_or_zero(HashMap::get(&map, &lookup))
    }

    set_score() -> u64 {
        let set = string_set();
        let initially_empty = set_is_empty(&set);
        let first = set_insert(&mut set, "alpha");
        let duplicate = set_insert(&mut set, "alpha");
        let second = set_insert(&mut set, "beta");
        let probe = "beta";
        wrapping_convert_to_u64(HashSet::len(&set)) * 1000
            + bool_score(move initially_empty) * 10000
            + bool_score(0 < set_capacity(&set))
            + bool_score(move first) * 100
            + bool_score(move duplicate) * 10
            + bool_score(HashSet::contains(&set, &probe))
            + bool_score(move second)
    }

    main() -> () { () }
"#;

const HASH_REMOVAL_SURFACE: &str = r#"
    // FNV-1a's low three bits for these one-byte strings are equal, so they
    // occupy one probe cluster at the initial eight-bucket capacity.
    collision_map() -> HashMap<String, u64> { HashMap::new() }
    collision_set() -> HashSet<String> { HashSet::new() }
    map_insert_u64(value: &mut HashMap<String, u64>, key: String, item: u64)
        -> Option<u64> {
        HashMap::insert(move value, move key, move item)
    }
    map_remove_u64(value: &mut HashMap<String, u64>, key: &String)
        -> Option<u64> {
        HashMap::remove(move value, move key)
    }
    map_get_u64<'a>(value: &'a HashMap<String, u64>, key: &String)
        -> Option<&'a u64> {
        HashMap::get(move value, move key)
    }
    set_insert_u64(value: &mut HashSet<String>, key: String) -> Bool {
        HashSet::insert(move value, move key)
    }
    set_remove_u64(value: &mut HashSet<String>, key: &String) -> Bool {
        HashSet::remove(move value, move key)
    }
    set_contains_u64(value: &HashSet<String>, key: &String) -> Bool {
        HashSet::contains(move value, move key)
    }
    option_value(value: Option<u64>) -> u64 {
        if(value is Result::Ok(_)) { value.0 } else { 0 }
    }
    option_ref_value(value: Option<&u64>) -> u64 {
        if(value is Result::Ok(_)) { *value.0 } else { 0 }
    }
    bool_value(value: Bool) -> u64 {
        if(value is Result::Ok(_)) { 1 } else { 0 }
    }

    removal_score() -> u64 {
        let map = collision_map();
        map_insert_u64(&mut map, "a", 10);
        map_insert_u64(&mut map, "i", 20);
        map_insert_u64(&mut map, "q", 30);
        map_insert_u64(&mut map, "y", 40);
        let removed = "i";
        let absent = "missing";
        let retained_three = "q";
        let retained_four = "y";
        let removed_value = map_remove_u64(&mut map, &removed);
        let absent_value = map_remove_u64(&mut map, &absent);

        let set = collision_set();
        set_insert_u64(&mut set, "b");
        set_insert_u64(&mut set, "j");
        let set_removed = "b";
        let set_retained = "j";
        let first_set_remove = set_remove_u64(&mut set, &set_removed);
        let second_set_remove = set_remove_u64(&mut set, &set_removed);

        wrapping_convert_to_u64(HashMap::len(&map)) * 10000
            + option_value(move removed_value) * 100
            + option_value(move absent_value) * 10
            + option_ref_value(map_get_u64(&map, &retained_three))
            + option_ref_value(map_get_u64(&map, &retained_four))
            + bool_value(move first_set_remove) * 1000
            + bool_value(move second_set_remove) * 100
            + bool_value(set_contains_u64(&set, &set_retained))
            + wrapping_convert_to_u64(HashSet::len(&set))
    }

    main() -> () { () }
"#;

const HASH_ITERATION_SURFACE: &str = r#"
    previous_or_zero(value: Option<u64>) -> u64 {
        if(value is Result::Ok(_)) { value.0 } else { 0 }
    }
    borrowed_or_zero(value: Option<&u64>) -> u64 {
        if(value is Result::Ok(_)) { *value.0 } else { 0 }
    }
    bool_score(value: Bool) -> u64 {
        if(value is Result::Ok(_)) { 1 } else { 0 }
    }

    encode_values_step(
        step: ((String, u64), HashMapIntoIter<String, u64>)
    ) -> u64 {
        let (entry, remaining) = move step;
        let (key, value) = move entry;
        key;
        move value + 10 * encode_values(move remaining)
    }

    encode_values(iterator: HashMapIntoIter<String, u64>) -> u64 {
        Option::unwrap_or(Option::map(
            HashMapIntoIter::next(move iterator),
            encode_values_step
        ), 0)
    }

    consume_set_step(step: (String, HashSetIntoIter<String>)) -> u64 {
        let (key, remaining) = move step;
        key;
        1 + consume_set(move remaining)
    }

    consume_set(iterator: HashSetIntoIter<String>) -> u64 {
        Option::unwrap_or(Option::map(
            HashSetIntoIter::next(move iterator),
            consume_set_step
        ), 0)
    }

    u64_map() -> HashMap<String, u64> { HashMap::new() }
    string_set() -> HashSet<String> { HashSet::new() }
    insert_u64(value: &mut HashMap<String, u64>, key: String, item: u64)
        -> Option<u64> {
        HashMap::insert(move value, move key, move item)
    }
    insert_string(value: &mut HashSet<String>, key: String) -> Bool {
        HashSet::insert(move value, move key)
    }
    entry_insert(
        value: &mut HashMap<String, u64>,
        key: String,
        item: u64
    ) -> u64 {
        let entry = HashMap::entry(move value, move key);
        let occupied = HashMapEntry::is_occupied(&entry);
        let previous = HashMapEntry::insert(move entry, move item);
        bool_score(move occupied) * 100 + previous_or_zero(move previous)
    }
    iteration_score() -> u64 {
        let map = u64_map();
        insert_u64(&mut map, "a", 1);
        insert_u64(&mut map, "i", 2);
        insert_u64(&mut map, "q", 3);
        insert_u64(&mut map, "y", 4);
        let removed = "i";
        HashMap::remove(&mut map, &removed);
        insert_u64(&mut map, "i", 2);
        let encoded = encode_values(HashMap::into_iter(move map));

        let set = string_set();
        insert_string(&mut set, "alpha");
        insert_string(&mut set, "beta");
        let set_count = consume_set(HashSet::into_iter(move set));

        let entries = u64_map();
        let vacant = entry_insert(&mut entries, "entry", 5);
        let occupied = entry_insert(&mut entries, "entry", 7);

        (move vacant + move occupied) * 1000000
            + move encoded * 100
            + move set_count
    }

    main() -> () { () }
"#;

#[test]
fn generic_hash_map_and_set_execute_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "hash-collections.glorious",
            HASH_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(artifact.clone())
                .run(function_id(&phases.artifact, "map_score"), vec![])
                .unwrap(),
            Value::U64(9_229),
            "{optimization_level:?}"
        );
        assert_eq!(
            Vm::new(artifact)
                .run(function_id(&phases.artifact, "set_score"), vec![])
                .unwrap(),
            Value::U64(12_103),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn generic_hash_map_has_recovery_parity() {
    let source = HASH_SURFACE.replace(
        "main() -> () { () }",
        "main() -> i64 { wrapping_convert_to_i64(map_score() + set_score()) }",
    );
    assert_eq!(
        run_source(
            "hash-collections-recovery.glorious",
            &source,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Int(21_332)
    );
}

#[test]
fn hash_collection_representation_is_private() {
    for (name, source, field) in [
        (
            "forge-hash-map.glorious",
            "bad(value:HashMap<String,u64>)->usize{value.length}main()->(){()}",
            "length",
        ),
        (
            "forge-hash-set.glorious",
            "bad(value:HashSet<String>)->HashMap<String,()>{value.values}main()->(){()}",
            "values",
        ),
        (
            "forge-hash-entry.glorious",
            "bad<'a>(value:HashMapEntry<'a,String,u64>)->usize{value.probe.index}main()->(){()}",
            "probe",
        ),
        (
            "forge-hash-iterator.glorious",
            "bad(value:HashMapIntoIter<String,u64>)->(){value.buckets;()}main()->(){()}",
            "buckets",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.message.contains(&format!("private field `{field}`"))
                    && error.message.contains("defining source segment")
            }),
            "{errors:#?}"
        );
    }
}

#[test]
fn removal_repairs_collision_clusters_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "hash-removal.glorious",
            HASH_REMOVAL_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(artifact)
                .run(function_id(&phases.artifact, "removal_score"), vec![])
                .unwrap(),
            Value::U64(33_072),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn removal_has_recovery_parity() {
    let source = HASH_REMOVAL_SURFACE.replace(
        "main() -> () { () }",
        "main() -> i64 { wrapping_convert_to_i64(removal_score()) }",
    );
    assert_eq!(
        run_source(
            "hash-removal-recovery.glorious",
            &source,
            vec![],
            &mut NoHost
        )
        .unwrap(),
        RecoveryValue::Int(33_072)
    );
}

#[test]
fn deterministic_owning_iteration_transfers_every_entry() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "hash-iteration.glorious",
            HASH_ITERATION_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let artifact = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(artifact)
                .run(function_id(&phases.artifact, "iteration_score"), vec![])
                .unwrap(),
            Value::U64(105_243_102),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn entry_and_owning_iteration_have_recovery_parity() {
    let source = HASH_ITERATION_SURFACE.replace(
        "main() -> () { () }",
        "main() -> i64 { wrapping_convert_to_i64(iteration_score()) }",
    );
    assert_eq!(
        run_source(
            "hash-iteration-recovery.glorious",
            &source,
            vec![],
            &mut NoHost
        )
        .unwrap(),
        RecoveryValue::Int(105_243_102)
    );
}
