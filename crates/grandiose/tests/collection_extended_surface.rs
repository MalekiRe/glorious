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
            "extended collection test performed a host effect",
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
    effect RemovedCase { inspect(value: Result<(String, u64), ()>) -> !; }
    effect VecCase { inspect(value: Result<Vec<u64>, ()>) -> !; }
    bool_score(value: Bool) -> u64 {
        if(value is Result::Ok(_)) { 1 } else { 0 }
    }
    false_score(value: Bool) -> u64 {
        if(value is Result::Err(_)) { 1 } else { 0 }
    }
    vec_error_score(value: Result<Vec<u64>, ()>) -> u64 {
        if(value is Result::Err(_)) { 1 } else { 0 }
    }
    removed_score(value: Option<(String, u64)>) -> u64 {
        handle perform RemovedCase::inspect(move value) {
            RemovedCase::inspect(Result::Ok(pair)) => {
                let (key, item) = move pair;
                key;
                move item
            },
            RemovedCase::inspect(Result::Err(_)) => 0
        }
    }
    borrowed_score(value: Option<&u64>) -> u64 {
        if(value is Result::Ok(_)) { *value.0 } else { 0 }
    }
    vec_len_score(value: Result<Vec<u64>, ()>) -> u64 {
        handle perform VecCase::inspect(move value) {
            VecCase::inspect(Result::Ok(vector)) =>
                wrapping_convert_to_u64(Vec::len(&vector)),
            VecCase::inspect(Result::Err(_)) => 0
        }
    }
    hash_string(value: &String) -> u64 {
        let state = Hasher::new();
        Hash::hash(value, &mut state);
        Hasher::finish(&state)
    }
    string_map() -> HashMap<String, u64> { HashMap::new() }
    string_set() -> HashSet<String> { HashSet::new() }
    map_insert(value: &mut HashMap<String, u64>, key: String, item: u64)
        -> Option<u64> { HashMap::insert(move value, move key, move item) }
    map_reserve(value: &mut HashMap<String, u64>, additional: usize) -> Bool {
        HashMap::reserve_additional(move value, move additional)
    }
    map_remove_entry(value: &mut HashMap<String, u64>, key: &String)
        -> Option<(String, u64)> { HashMap::remove_entry(move value, move key) }
    map_raw_get<'a>(value: &'a HashMap<String, u64>, key: &String, hash: u64)
        -> Option<&'a u64> { HashMap::raw_get(move value, move key, move hash) }
    map_clear(value: &mut HashMap<String, u64>) -> () {
        HashMap::clear(move value)
    }
    set_insert(value: &mut HashSet<String>, key: String) -> Bool {
        HashSet::insert(move value, move key)
    }
    set_union(value: &mut HashSet<String>, other: &HashSet<String>) -> () {
        HashSet::union_with(move value, move other)
    }
    set_intersection(left: &HashSet<String>, right: &HashSet<String>)
        -> HashSet<String> { HashSet::intersection(move left, move right) }
    u64_vec() -> Vec<u64> { Vec::new() }
    vec_push(value: &mut Vec<u64>, item: u64) -> () {
        Vec::push(move value, move item)
    }
    vec_split(value: &mut Vec<u64>, at: usize) -> Result<Vec<u64>, ()> {
        Vec::split_off(move value, move at)
    }
    vec_drain(value: &mut Vec<u64>, range: Range<usize>)
        -> Result<Vec<u64>, ()> { Vec::drain(move value, move range) }

    reserve_score(value: &mut HashMap<String, u64>) -> u64 {
        bool_score(map_reserve(move value, 20)) * 100000
    }
    remove_score(value: &mut HashMap<String, u64>) -> u64 {
        let key = "i";
        removed_score(map_remove_entry(move value, &key)) * 1000
    }
    raw_score(value: &HashMap<String, u64>) -> u64 {
        let key = "q";
        let hash = hash_string(&key);
        borrowed_score(map_raw_get(value, &key, hash)) * 10
            + borrowed_score(map_raw_get(value, &key, hash + 1))
    }
    clear_score(value: &mut HashMap<String, u64>) -> u64 {
        map_clear(&mut *value);
        wrapping_convert_to_u64(HashMap::len(&*value))
    }

    map_extended_score() -> u64 {
        let map = string_map();
        map_insert(&mut map, "a", 10);
        map_insert(&mut map, "i", 20);
        map_insert(&mut map, "q", 30);
        reserve_score(&mut map) + remove_score(&mut map)
            + raw_score(&map) + clear_score(&mut map)
    }

    set_extended_score() -> u64 {
        let left = string_set();
        set_insert(&mut left, "a");
        set_insert(&mut left, "i");
        let right = string_set();
        set_insert(&mut right, "i");
        set_insert(&mut right, "q");
        set_union(&mut left, &right);
        let common = set_intersection(&left, &right);
        wrapping_convert_to_u64(HashSet::len(&left)) * 10
            + wrapping_convert_to_u64(HashSet::len(&common))
    }

    vec_extended_score() -> u64 {
        let values = u64_vec();
        vec_push(&mut values, 1);
        vec_push(&mut values, 2);
        vec_push(&mut values, 3);
        vec_push(&mut values, 4);
        vec_push(&mut values, 5);
        let split = vec_split(&mut values, 3);
        let prefix_length = wrapping_convert_to_u64(Vec::len(&values));
        let split_length = vec_len_score(move split);
        let drained = vec_drain(&mut values, Range { start: 1, end: 3 });
        move prefix_length * 1000 + move split_length * 100
            + wrapping_convert_to_u64(Vec::len(&values)) * 10
            + vec_len_score(move drained)
    }

    invalid_vec_ranges_score() -> u64 {
        let values = u64_vec();
        vec_push(&mut values, 1);
        vec_push(&mut values, 2);
        vec_push(&mut values, 3);
        let reversed = vec_drain(&mut values, Range { start: 2, end: 1 });
        let out_of_bounds = vec_drain(&mut values, Range { start: 0, end: 4 });
        let split_out_of_bounds = vec_split(&mut values, 4);
        vec_error_score(move reversed) * 1000
            + vec_error_score(move out_of_bounds) * 100
            + vec_error_score(move split_out_of_bounds) * 10
            + wrapping_convert_to_u64(Vec::len(&values))
    }

    reserve_overflow_is_atomic() -> u64 {
        let map = string_map();
        map_insert(&mut map, "a", 1);
        let before_length = HashMap::len(&map);
        let before_capacity = HashMap::capacity(&map);
        let reserved = map_reserve(&mut map, 18446744073709551615);
        false_score(move reserved)
            + bool_score(before_length == HashMap::len(&map)) * 10
            + bool_score(before_capacity == HashMap::capacity(&map)) * 100
    }

    main() -> () { () }
"#;

#[test]
fn extended_collection_operations_execute_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "collection-extended-surface.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        for (name, expected) in [
            ("map_extended_score", 120_300),
            ("set_extended_score", 32),
            ("vec_extended_score", 3_212),
            ("invalid_vec_ranges_score", 1_113),
            ("reserve_overflow_is_atomic", 111),
        ] {
            assert_eq!(
                vm.run(function_id(&artifact, name), vec![]).unwrap(),
                Value::U64(expected),
                "{name} at {optimization_level:?}",
            );
        }
    }
}

#[test]
fn extended_collection_operations_have_recovery_parity() {
    let value = run_source(
        "collection-extended-recovery.glorious",
        &SOURCE.replace(
            "main() -> () { () }",
            "main() -> u64 { map_extended_score() + set_extended_score() + vec_extended_score() + invalid_vec_ranges_score() + reserve_overflow_is_atomic() }",
        ),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 124_768,
        },
    );
}

#[test]
fn restricted_elements_must_be_transferred_and_cannot_be_cleared() {
    let accepted = r#"
        struct Ticket { value: u64 }
        impl Use<[1,1]> for Ticket {}
        split(value: Vec<Ticket>)
            -> (Vec<Ticket>, Result<Vec<Ticket>, ()>) {
            let retained = move value;
            let moved = Vec::split_off(&mut retained, 1);
            (move retained, move moved)
        }
        drain(value: Vec<Ticket>)
            -> (Vec<Ticket>, Result<Vec<Ticket>, ()>) {
            let retained = move value;
            let moved = Vec::drain(
                &mut retained,
                Range { start: 0, end: 1 }
            );
            (move retained, move moved)
        }
        main() -> () { () }
    "#;
    compile_source_to_bytecode("restricted-collection-transfer.glorious", accepted)
        .unwrap_or_else(|errors| panic!("{errors:#?}"));

    let rejected = r#"
        struct Ticket { value: u64 }
        impl Use<[1,1]> for Ticket {}
        bad(value: Vec<Ticket>) -> () { Vec::clear(&mut value) }
        main() -> () { () }
    "#;
    let errors =
        compile_source_to_bytecode("restricted-collection-clear.glorious", rejected).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| { error.message.contains("Use") || error.message.contains("zero-use") }),
        "{errors:#?}",
    );
}
