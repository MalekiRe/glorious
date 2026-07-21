use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::value::{ArenaObject, ArrayValue, ReferenceTarget};
use grandiose_vm::{Type, Value, Vm, verify};

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
            "borrowed collection iterator test performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| {
            function.name == name
                || function
                    .name
                    .strip_prefix("$specialization$")
                    .and_then(|wire| wire.split_once('#'))
                    .is_some_and(|(template, _)| template == name)
        })
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn shared_aggregate(value: Value, referent_type: u32) -> (Value, u128) {
    let Value::Aggregate(owner) = value else {
        panic!("borrowed iterator owner is not an aggregate")
    };
    let identity = owner.identity();
    (
        Value::Reference {
            referent_type,
            unique: false,
            target: ReferenceTarget::Aggregate(owner),
        },
        identity,
    )
}

fn some_payload(value: Value) -> Option<Value> {
    let Value::Aggregate(option) = value else {
        panic!("iterator next result is not an Option aggregate")
    };
    let option = option.borrow();
    match option.variant {
        Some(0) => option.fields[0].clone(),
        Some(1) => None,
        variant => panic!("unexpected Option variant {variant:?}"),
    }
}

fn pair_fields(value: Value) -> (Value, Value) {
    let Value::Aggregate(pair) = value else {
        panic!("iterator Some payload is not a pair")
    };
    let pair = pair.borrow();
    (
        pair.fields[0].clone().expect("missing pair head"),
        pair.fields[1].clone().expect("missing pair tail"),
    )
}

fn assert_iterator_owner(iterator: &Value, owner_identity: u128) {
    let Value::Aggregate(state) = iterator else {
        panic!("iterator continuation is not an aggregate")
    };
    let state = state.borrow();
    let Some(Value::Reference {
        unique: false,
        target,
        ..
    }) = state.fields[0].as_ref()
    else {
        panic!("iterator continuation lost its shared owner reference")
    };
    let owner = match target {
        ReferenceTarget::Aggregate(owner)
        | ReferenceTarget::AggregateField {
            aggregate: owner, ..
        } => owner,
        target => panic!("iterator continuation has unexpected owner target {target:?}"),
    };
    assert_eq!(owner.identity(), owner_identity);
}

fn walk_map_iterator(
    vm: &Vm,
    start: u32,
    next: u32,
    owner: Value,
    owner_identity: u128,
    pair_payload: bool,
) {
    let Value::Aggregate(iterator) = vm.run(start, vec![owner]).unwrap() else {
        panic!("borrowed iterator constructor did not return state")
    };
    let iterator_type = iterator.borrow().ty;
    let mut count = 0;
    loop {
        let state = Value::Reference {
            referent_type: iterator_type,
            unique: true,
            target: ReferenceTarget::Aggregate(iterator.clone()),
        };
        let Some(borrowed) = some_payload(vm.run(next, vec![state]).unwrap()) else {
            break;
        };
        if pair_payload {
            let (key, item) = pair_fields(borrowed);
            assert!(matches!(key, Value::Reference { unique: false, .. }));
            assert!(matches!(item, Value::Reference { unique: false, .. }));
        } else {
            assert!(matches!(borrowed, Value::Reference { unique: false, .. }));
        }
        assert_iterator_owner(&Value::Aggregate(iterator.clone()), owner_identity);
        count += 1;
    }
    assert_eq!(count, 3, "collision cluster was not traversed exhaustively");
}

fn inspect_concrete_iterator_states(artifact: &grandiose_vm::Artifact, vm: &Vm) {
    let prepared_map = function_id(artifact, "prepared_map");
    let map_type = artifact.functions[prepared_map as usize].return_type;
    let (map_owner, map_identity) =
        shared_aggregate(vm.run(prepared_map, vec![]).unwrap(), map_type);
    for (start, next, pair_payload) in [
        ("__g1_hash_map_iter", "__g1_hash_map_iter_next", true),
        ("__g1_hash_map_keys", "__g1_hash_map_keys_next", false),
        ("__g1_hash_map_values", "__g1_hash_map_values_next", false),
    ] {
        walk_map_iterator(
            vm,
            function_id(artifact, start),
            function_id(artifact, next),
            map_owner.clone(),
            map_identity,
            pair_payload,
        );
    }

    let prepared_set = function_id(artifact, "prepared_set");
    let set_type = artifact.functions[prepared_set as usize].return_type;
    let (set_owner, set_identity) =
        shared_aggregate(vm.run(prepared_set, vec![]).unwrap(), set_type);
    walk_map_iterator(
        vm,
        function_id(artifact, "__g1_hash_set_iter"),
        function_id(artifact, "__g1_hash_set_iter_next"),
        set_owner,
        set_identity,
        false,
    );

    let vec_iter = function_id(artifact, "__g1_vec_iter");
    let Type::RefShared { referent: vec_type } =
        artifact.types[artifact.functions[vec_iter as usize].params[0] as usize].representation()
    else {
        panic!("Vec::iter parameter is not a shared Vec reference")
    };
    let array = ArenaObject::new(ArrayValue {
        element_type: grandiose_vm::U64,
        slots: [10, 20, 30]
            .into_iter()
            .map(|value| Some(Value::U64(value)))
            .collect(),
        logical_capacity: 3,
    });
    let vec_owner = Value::aggregate(*vec_type, [Value::Array(array)]);
    let (vec_owner, vec_identity) = shared_aggregate(vec_owner, *vec_type);
    let Value::Aggregate(iterator) = vm.run(vec_iter, vec![vec_owner]).unwrap() else {
        panic!("Vec::iter did not return state")
    };
    let next = function_id(artifact, "__g1_slice_iter_next");
    let Type::RefUnique {
        referent: iterator_type,
    } = artifact.types[artifact.functions[next as usize].params[0] as usize].representation()
    else {
        panic!("SliceIter::next does not take unique state")
    };
    for expected in 0..3 {
        let state = Value::Reference {
            referent_type: *iterator_type,
            unique: true,
            target: ReferenceTarget::Aggregate(iterator.clone()),
        };
        let index = some_payload(vm.run(next, vec![state]).unwrap())
            .expect("populated Vec::iter exhausted early");
        assert_eq!(index, Value::U64(expected));
        assert_iterator_owner(&Value::Aggregate(iterator.clone()), vec_identity);
    }
    let state = Value::Reference {
        referent_type: *iterator_type,
        unique: true,
        target: ReferenceTarget::Aggregate(iterator),
    };
    assert!(some_payload(vm.run(next, vec![state]).unwrap()).is_none());
}

const SOURCE: &str = r#"
    u64_vec() -> Vec<u64> { Vec::new() }
    string_map() -> HashMap<String, u64> { HashMap::new() }
    string_set() -> HashSet<String> { HashSet::new() }

    map_insert(value: &mut HashMap<String, u64>, key: String, item: u64)
        -> Option<u64> { HashMap::insert(move value, move key, move item) }
    map_entry_or_insert<'a>(
        value: &'a mut HashMap<String, u64>,
        key: String,
        fallback: u64
    ) -> &'a mut u64 {
        HashMapEntry::or_insert(
            HashMap::entry(move value, move key),
            move fallback
        )
    }
    entry_update<'a>(
        value: &'a mut HashMap<String, u64>,
        key: String,
        fallback: u64,
        delta: u64
    ) -> u64 {
        let item = map_entry_or_insert(move value, move key, move fallback);
        *item = *item + move delta;
        *item
    }
    set_insert(value: &mut HashSet<String>, key: String) -> Bool {
        HashSet::insert(move value, move key)
    }

    vec_touch() -> u64 {
        let values = u64_vec();
        Vec::push(&mut values, 10);
        Vec::push(&mut values, 20);
        Vec::push(&mut values, 30);
        let iterator = Vec::iter(&values);
        SliceIter::next(&mut iterator);
        wrapping_convert_to_u64(Vec::len(&values))
    }

    prepared_map() -> HashMap<String, u64> {
        let map = string_map();
        // These keys collide in the initial deterministic eight-bucket table.
        map_insert(&mut map, "a", 10);
        map_insert(&mut map, "i", 25);
        map_insert(&mut map, "q", 37);
        move map
    }

    entry_score() -> u64 {
        let map = string_map();
        map_insert(&mut map, "a", 10);
        map_insert(&mut map, "i", 20);
        let occupied = entry_update(&mut map, "i", 99, 5);
        let vacant = entry_update(&mut map, "q", 30, 7);
        move occupied * 100 + move vacant
    }

    map_touch() -> u64 {
        let map = prepared_map();
        let iterator = HashMap::iter(&map);
        HashMapIter::next(&mut iterator);
        let keys = HashMap::keys(&map);
        HashMapKeys::next(&mut keys);
        let values = HashMap::values(&map);
        HashMapValues::next(&mut values);
        wrapping_convert_to_u64(HashMap::len(&map))
    }

    prepared_set() -> HashSet<String> {
        let set = string_set();
        set_insert(&mut set, "a");
        set_insert(&mut set, "i");
        set_insert(&mut set, "q");
        move set
    }

    set_touch() -> u64 {
        let set = prepared_set();
        let iterator = HashSet::iter(&set);
        HashSetIter::next(&mut iterator);
        wrapping_convert_to_u64(HashSet::len(&set))
    }

    combined_score() -> u64 {
        vec_touch() * 1_000_000
            + entry_score() * 1_000
            + map_touch() * 10
            + set_touch()
    }

    main() -> () { () }
"#;

#[test]
fn borrowed_collection_state_machines_execute_at_o0_through_o3() {
    std::thread::Builder::new()
        .name("borrowed-collection-compiler".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            for optimization_level in [
                OptimizationLevel::O0,
                OptimizationLevel::O1,
                OptimizationLevel::O2,
                OptimizationLevel::O3,
            ] {
                let artifact = compile_source_to_bytecode_with_options(
                    "borrowed-collection-iterators.glorious",
                    SOURCE,
                    CompileOptions { optimization_level },
                )
                .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
                let vm = Vm::new(verify(artifact.clone()).unwrap());
                for (name, expected) in [
                    ("vec_touch", 3),
                    ("entry_score", 2_537),
                    ("map_touch", 3),
                    ("set_touch", 3),
                    ("combined_score", 5_537_033),
                ] {
                    assert_eq!(
                        vm.run(function_id(&artifact, name), vec![]).unwrap(),
                        Value::U64(expected),
                        "{optimization_level:?}: {name}",
                    );
                }
                inspect_concrete_iterator_states(&artifact, &vm);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn borrowed_collection_state_machines_have_recovery_parity() {
    let value = run_source(
        "borrowed-collection-iterators-recovery.glorious",
        &SOURCE.replace("main() -> () { () }", "main() -> u64 { combined_score() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(
        value,
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 5_537_033,
        },
    );
}
