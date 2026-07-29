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
            "compiler toolkit recovery test performed a host effect",
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

#[test]
fn step_budget_is_monotonic_and_failed_spends_are_atomic_at_o1_through_o3() {
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

#[test]
fn id_from_usize_specialization_survives_reference_result_pattern_handling() {
    let source = r#"
        struct NodeTag {}

        struct Node { value: i64 }

        empty_nodes() -> Arena<NodeTag, Node> { Arena::new() }

        select<'a>(
            value: &'a Arena<NodeTag, Node>,
            index: usize
        ) -> Option<&'a Node> {
            handle Id::from_usize(index) {
                Result::Err(_) => None,
                Result::Ok(id) => Arena::get(value, id)
            }
        }

        main() -> () {
            let nodes = empty_nodes();
            select(&nodes, 0);
            ()
        }
    "#;
    compile_source_to_bytecode("id-from-usize-reference-result.glorious", source).unwrap();
}

#[test]
fn shadowed_pattern_payload_does_not_constrain_a_generic_initializer() {
    let source = r#"
        struct NodeTag {}
        enum Maybe<T> { Some(T), None }

        consume(value: Id<NodeTag>) -> () {
            value;
            ()
        }

        make<T>() -> Maybe<T> { unreachable() }

        exercise() -> () {
            let value = make();
            handle move value {
                Maybe::Some(payload) => {
                    let tag = NodeTag {};
                    let payload = Id::with_tag(1, &tag);
                    consume(payload)
                },
                Maybe::None => ()
            }
        }

        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("shadowed-pattern-payload.glorious", source)
        .expect_err("a nested shadow must not infer the outer generic payload");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("unresolved")
                || error.message.contains("ambiguous")
                || error.message.contains("cannot infer")
                || error.message.contains("variant pattern requires an enum")
        }),
        "{errors:#?}"
    );
}

#[test]
fn initializer_inference_rejects_incompatible_later_uses() {
    let source = r#"
        empty<T>() -> Vec<T> { Vec::new() }
        consume_i64(value: &Vec<i64>) -> () { value; () }
        consume_u64(value: &Vec<u64>) -> () { value; () }

        exercise() -> () {
            let values = empty();
            consume_i64(&values);
            consume_u64(&values)
        }

        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("incompatible-initializer-uses.glorious", source)
        .expect_err("incompatible uses must not select an arbitrary traversal-order candidate");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("ambiguous")
                || error.message.contains("expected")
                || error.message.contains("cannot infer")
        }),
        "{errors:#?}"
    );
}

#[test]
fn initializer_alias_survives_shadowing_of_the_original_name() {
    let source = r#"
        empty<T>() -> Vec<T> { Vec::new() }
        consume(value: &Vec<i64>) -> () { value; () }

        exercise() -> () {
            let values = empty();
            let retained = move values;
            let values = 1;
            values;
            consume(&retained)
        }

        main() -> () { exercise() }
    "#;
    compile_source_to_bytecode("initializer-alias-survives-shadow.glorious", source).unwrap();
}

#[test]
fn multimap_remove_handle_alias_preserves_the_initializer_wrapper_expectation() {
    let source = r#"
        struct Key { raw: i64 }
        impl Use<[0, infinity]> for Key {}
        impl Eq for Key {
            eq(self: &Key, other: &Key) -> Bool { self.raw == other.raw }
        }
        impl Hash for Key {
            hash(self: &Key, state: &mut Hasher) -> () {
                Hasher::write_u64(move state, wrapping_convert_to_u64(self.raw))
            }
        }

        empty_values() -> MultiMap<Key, i64> { MultiMap::new() }

        exercise() -> () {
            let values = empty_values();
            MultiMap::add(&mut values, Key { raw: 1 }, 7)
        }

        main() -> () { exercise() }
    "#;
    compile_source_to_bytecode("multimap-remove-handle-alias.glorious", source).unwrap();
}

#[test]
fn generic_hash_map_with_typed_ids_preserves_projected_assignment_expectations() {
    let source = r#"
        struct NodeTag {}

        empty_values() -> HashMap<Id<NodeTag>, usize> { HashMap::new() }

        insert_value() -> Bool {
            let tag = NodeTag {};
            let id = Id::with_tag(1, &tag);
            let values = empty_values();
            HashMap::insert(&mut values, id, 9);
            HashMap::contains_key(&values, &id)
        }

        main() -> () { () }
    "#;
    compile_source_to_phases_with_options(
        "typed-id-hash-map.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O1,
        },
    )
    .unwrap();
}

#[test]
fn generic_bool_refinement_accepts_a_moved_global_tail_inside_a_block() {
    let source = r#"
        struct Witness {}

        choose<T>(value: Bool, witness: &T) -> Bool {
            witness;
            handle move value {
                Result::Ok(_) => {
                    let ignored = 0;
                    ignored;
                    true
                },
                Result::Err(_) => false
            }
        }

        selected() -> Bool {
            let witness = Witness {};
            choose(true, &witness)
        }

        main() -> () { () }
    "#;
    compile_source_to_bytecode("generic-bool-refinement.glorious", source).unwrap();
}

const TYPED_TOOLKIT_SURFACE: &str = r#"
    struct NodeTag {}
    struct MultiKey { raw: i64 }
    impl Use<[0,infinity]> for MultiKey {}
    impl Eq for MultiKey {
        eq(self: &MultiKey, other: &MultiKey) -> Bool { self.raw == other.raw }
    }
    impl Hash for MultiKey {
        hash(self: &MultiKey, state: &mut Hasher) -> () {
            Hasher::write_u64(move state, wrapping_convert_to_u64(self.raw))
        }
    }
    effect BoolCase { inspect(value: Bool) -> !; }

    bool_score(value: Bool) -> usize {
        handle perform BoolCase::inspect(move value) {
            BoolCase::inspect(Result::Ok(_)) => 1,
            BoolCase::inspect(Result::Err(_)) => 0
        }
    }

    uadd(left: usize, right: usize) -> usize { move left + move right }
    umul(left: usize, right: usize) -> usize { move left * move right }

    empty_bits() -> BitSet<NodeTag> { BitSet::new() }
    empty_sparse() -> SparseSet<NodeTag> { SparseSet::new() }
    empty_queue() -> WorkQueue<NodeTag> { WorkQueue::new() }
    empty_multimap() -> MultiMap<MultiKey, i64> { MultiMap::new() }
    empty_id_map() -> HashMap<Id<NodeTag>, usize> { HashMap::new() }

    id_identity_evidence() -> usize {
        let tag = NodeTag {};
        let one = Id::with_tag(1, &tag);
        let same_one = Id::with_tag(1, &tag);
        let two = Id::with_tag(2, &tag);
        let values = empty_id_map();
        HashMap::insert(&mut values, one, 9);
        uadd(
            uadd(
                umul(bool_score(one == same_one), 100),
                uadd(
                    umul(bool_score(Eq::eq(&one, &same_one)), 10),
                    bool_score(HashMap::contains_key(&values, &one))
                )
            ),
            bool_score(HashMap::contains_key(&values, &two))
        )
    }

    bit_set_algebra() -> usize {
        let left = empty_bits();
        let right = empty_bits();
        let tag = NodeTag {};
        let one = Id::with_tag(1, &tag);
        let high = Id::with_tag(130, &tag);
        BitSet::insert(&mut left, one);
        BitSet::insert(&mut right, high);
        BitSet::union_with(&mut left, &right);
        let score = uadd(
            bool_score(BitSet::contains(&left, one)),
            bool_score(BitSet::contains(&left, high))
        );
        BitSet::intersect_with(&mut left, &right);
        uadd(
            uadd(
                umul(score, 10),
                bool_score(BitSet::contains(&left, high))
            ),
            bool_score(BitSet::contains(&left, one))
        )
    }

    sparse_set_roundtrip() -> usize {
        let values = empty_sparse();
        let tag = NodeTag {};
        let two = Id::with_tag(2, &tag);
        let nine = Id::with_tag(9, &tag);
        let inserted = bool_score(SparseSet::insert(&mut values, two));
        let duplicate = bool_score(SparseSet::insert(&mut values, two));
        SparseSet::insert(&mut values, nine);
        let removed = bool_score(SparseSet::remove(&mut values, two));
        uadd(
            uadd(umul(inserted, 100), umul(duplicate, 10)),
            uadd(removed, SparseSet::len(&values))
        )
    }

    work_queue_deduplicates() -> usize {
        let queue = empty_queue();
        let tag = NodeTag {};
        let seven = Id::with_tag(7, &tag);
        let first = bool_score(WorkQueue::push(&mut queue, seven));
        let duplicate = bool_score(WorkQueue::push(&mut queue, seven));
        WorkQueue::pop(&mut queue);
        let requeued = bool_score(WorkQueue::push(&mut queue, seven));
        uadd(uadd(umul(first, 100), umul(duplicate, 10)), requeued)
    }

    multimap_groups_values() -> usize {
        let values = empty_multimap();
        let two = MultiKey { raw: 2 };
        MultiMap::add(&mut values, two, 7);
        MultiMap::add(&mut values, two, 9);
        uadd(MultiMap::key_count(&values), MultiMap::value_count(&values, &two))
    }

    accounting_is_checked() -> usize {
        let counter = CheckedCounter::new(5);
        let first = bool_score(CheckedCounter::try_add(&mut counter, 3));
        let rejected = bool_score(CheckedCounter::try_add(&mut counter, 4));
        let stats = CompilerStatistics::new();
        let recorded = bool_score(CompilerStatistics::record_tokens(&mut stats, 7));
        CompilerStatistics::record_syntax_nodes(&mut stats, 5);
        uadd(
            umul(first, 1000),
            uadd(
                umul(rejected, 100),
                uadd(
                    umul(recorded, 10),
                    uadd(
                        CheckedCounter::get(&counter),
                        uadd(stats.tokens, stats.syntax_nodes)
                    )
                )
            )
        )
    }

    id_capacity_is_checked() -> usize {
        uadd(
            umul(bool_score(id_fits_usize(10)), 10),
            bool_score(id_fits_usize(__g1_toolkit_usize_max()))
        )
    }

    main() -> () { () }
"#;

#[test]
fn typed_compiler_toolkit_executes_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "typed-toolkit.glorious",
            TYPED_TOOLKIT_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        let vm = Vm::new(artifact);
        for (name, expected) in [
            ("bit_set_algebra", 21),
            ("sparse_set_roundtrip", 102),
            ("work_queue_deduplicates", 101),
            ("multimap_groups_values", 3),
            ("id_identity_evidence", 111),
            ("accounting_is_checked", 1025),
            ("id_capacity_is_checked", 10),
        ] {
            assert_eq!(
                vm.run(function_id(&phases.artifact, name), vec![]).unwrap(),
                Value::U64(expected),
                "{optimization_level:?}: {name}"
            );
        }
    }
}

#[test]
fn typed_compiler_toolkit_has_recovery_parity() {
    let result = run_source(
        "typed-toolkit-recovery.glorious",
        &TYPED_TOOLKIT_SURFACE.replace(
            "main() -> () { () }",
            "main() -> usize { bit_set_algebra() }",
        ),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(21));
}

const STORAGE_TOOLKIT_SURFACE: &str = r#"
    struct ItemTag {}
    effect UsizeOptionCase { inspect(value: Result<usize, ()>) -> !; }
    effect UsizeReplaceCase { inspect(value: Result<usize, usize>) -> !; }

    usize_or_zero(value: Option<usize>) -> usize {
        handle perform UsizeOptionCase::inspect(move value) {
            UsizeOptionCase::inspect(Result::Ok(item)) => move item,
            UsizeOptionCase::inspect(Result::Err(_)) => 0
        }
    }

    replace_or_zero(value: Result<usize, usize>) -> usize {
        handle perform UsizeReplaceCase::inspect(move value) {
            UsizeReplaceCase::inspect(Result::Ok(item)) => move item,
            UsizeReplaceCase::inspect(Result::Err(item)) => move item
        }
    }

    uadd(left: usize, right: usize) -> usize { move left + move right }
    umul(left: usize, right: usize) -> usize { move left * move right }
    empty_index() -> IndexVec<ItemTag, usize> { IndexVec::new() }
    empty_arena() -> Arena<ItemTag, usize> { Arena::new() }
    empty_string_interner() -> Interner<String> { Interner::new() }
    alloc_item(value: &mut Arena<ItemTag, usize>, item: usize)
        -> Result<Id<ItemTag>, usize> {
        Arena::alloc(move value, move item)
    }
    push_item(value: &mut IndexVec<ItemTag, usize>, item: usize)
        -> Result<Id<ItemTag>, usize> {
        IndexVec::push(move value, move item)
    }

    index_vec_growth() -> usize {
        let values = empty_index();
        push_item(&mut values, 10);
        push_item(&mut values, 20);
        let tag = ItemTag {};
        let second = Id::with_tag(1, &tag);
        let previous = replace_or_zero(IndexVec::replace(&mut values, second, 30));
        *IndexVec::index_mut(&mut values, second) = 40;
        let current = *IndexVec::index(&values, second);
        uadd(umul(IndexVec::len(&values), 100), uadd(previous, current))
    }

    arena_rollback() -> usize {
        let arena = empty_arena();
        let tag = ItemTag {};
        let first = handle alloc_item(&mut arena, 1) {
            Result::Ok(id) => id,
            Result::Err(_) => Id::with_tag(0, &tag)
        };
        let mark = Arena::mark(&arena);
        alloc_item(&mut arena, 2);
        alloc_item(&mut arena, 3);
        let removed = Arena::drain_rollback(&mut arena, mark);
        *Arena::index_mut(&mut arena, first) = 4;
        let retained = *Arena::index(&arena, first);
        uadd(
            umul(Arena::len(&arena), 100),
            uadd(Vec::len(&removed), retained)
        )
    }

    interner_is_canonical() -> usize {
        let values = empty_string_interner();
        Interner::intern_string(&mut values, "alpha");
        Interner::intern_string(&mut values, "beta");
        Interner::intern_string(&mut values, "alpha");
        let alpha_text = "alpha";
        let beta_text = "beta";
        let missing_text = "missing";
        let alpha = Interner::string_index_or_len(&values, &alpha_text);
        let beta = Interner::string_index_or_len(&values, &beta_text);
        let missing = Interner::string_index_or_len(&values, &missing_text);
        uadd(
            umul(Interner::len(&values), 100),
            uadd(umul(alpha, 10), uadd(beta, missing))
        )
    }

    source_map_lines() -> usize {
        let sources = SourceMap::new();
        SourceMap::add(&mut sources, "first", "a\nbc");
        SourceMap::add(&mut sources, "second", "z");
        let line = usize_or_zero(SourceMap::line_at(&sources, 2));
        let column = usize_or_zero(SourceMap::column_at(&sources, 2));
        uadd(
            umul(SourceMap::file_count(&sources), 100),
            uadd(umul(SourceMap::total_length(&sources), 10), uadd(line, column))
        )
    }

    main() -> () { () }
"#;

#[test]
fn storage_and_source_toolkit_execute_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "storage-toolkit.glorious",
            STORAGE_TOOLKIT_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        let vm = Vm::new(artifact);
        for (name, expected) in [
            ("index_vec_growth", 260),
            ("arena_rollback", 106),
            ("interner_is_canonical", 203),
            ("source_map_lines", 251),
        ] {
            assert_eq!(
                vm.run(function_id(&phases.artifact, name), vec![]).unwrap(),
                Value::U64(expected),
                "{optimization_level:?}: {name}"
            );
        }
    }
}

#[test]
fn storage_and_source_toolkit_have_recovery_parity() {
    let result = run_source(
        "storage-toolkit-recovery.glorious",
        &STORAGE_TOOLKIT_SURFACE.replace(
            "main() -> () { () }",
            "main() -> usize { source_map_lines() }",
        ),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(251));
}

#[test]
fn compiler_toolkit_representations_are_private_and_arena_truncate_is_bounded() {
    for (name, source, expected) in [
        (
            "forge-id.glorious",
            "struct Tag {} bad() -> Id<Tag> { Id { raw: 0 } } main() -> () { () }",
            "private field",
        ),
        (
            "forge-index-vec.glorious",
            "struct Tag {} bad() -> IndexVec<Tag, i64> { IndexVec { values: Vec::new() } } main() -> () { () }",
            "private field",
        ),
        (
            "forge-source-map.glorious",
            "bad(value: SourceMap) -> usize { value.total_length } main() -> () { () }",
            "private field `total_length`",
        ),
        (
            "forge-interner-buckets.glorious",
            "bad(value: Interner<String>) -> usize { Vec::len(&value.buckets) } main() -> () { () }",
            "private field `buckets`",
        ),
        (
            "linear-arena-truncate.glorious",
            "struct Tag {} struct Ticket { value: i64 } impl Use<[1,1]> for Ticket {} empty() -> Arena<Tag, Ticket> { Arena::new() } bad() -> () { let arena = empty(); Arena::truncate(&mut arena, 0) } main() -> () { () }",
            "does not contain the requested quantity",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source)
            .expect_err("toolkit invariant violation must be rejected");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn invariant_typed_indexing_traps_while_fallible_lookup_stays_optional() {
    let source = r#"
        struct ItemTag {}

        empty_index() -> IndexVec<ItemTag, usize> { IndexVec::new() }
        empty_arena() -> Arena<ItemTag, usize> { Arena::new() }

        missing_index() -> usize {
            let values = empty_index();
            let tag = ItemTag {};
            *IndexVec::index(&values, Id::with_tag(0, &tag))
        }

        missing_arena() -> usize {
            let values = empty_arena();
            let tag = ItemTag {};
            *Arena::index(&values, Id::with_tag(0, &tag))
        }

        fallible_miss() -> usize {
            let values = empty_index();
            let tag = ItemTag {};
            handle IndexVec::get_copy(&values, Id::with_tag(0, &tag)) {
                Result::Ok(_) => 1,
                Result::Err(_) => 0
            }
        }

        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("typed-index-invariants.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    let vm = Vm::new(verified);
    assert_eq!(
        vm.run(function_id(&artifact, "fallible_miss"), vec![])
            .unwrap(),
        Value::U64(0)
    );
    for name in ["missing_index", "missing_arena"] {
        let error = vm
            .run(function_id(&artifact, name), vec![])
            .expect_err("invariant indexing must retain Vec's trapping contract");
        assert!(
            error.to_string().contains("out of bounds"),
            "{name}: {error}"
        );
    }
}

#[test]
fn generic_eq_and_hash_evidence_dispatches_for_string() {
    let source = r#"
        effect BoolCase { inspect(value: Bool) -> !; }
        same<K>(left: &K, right: &K) -> Bool where K: Eq {
            Eq::eq(left, right)
        }
        digest<K>(value: &K) -> u64 where K: Hash {
            let state = Hasher::new();
            Hash::hash(value, &mut state);
            Hasher::finish(&state)
        }
        score(value: Bool) -> usize {
            handle perform BoolCase::inspect(move value) {
                BoolCase::inspect(Result::Ok(_)) => 1,
                BoolCase::inspect(Result::Err(_)) => 0
            }
        }
        selected() -> usize {
            let first = "alpha";
            let same_value = "alpha";
            let other = "beta";
            let equal = score(same(&first, &same_value));
            let unequal = score(same(&first, &other));
            let stable = score(digest(&first) == digest(&same_value));
            equal * 100 + unequal * 10 + stable
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("eq-hash-evidence.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&artifact, "selected"), vec![])
            .unwrap(),
        Value::U64(101)
    );
}

#[test]
fn symbolic_equal_dispatches_for_owned_strings() {
    let source = r#"
        effect BoolCase { inspect(value: Bool) -> !; }
        score(value: Bool) -> usize {
            handle perform BoolCase::inspect(move value) {
                BoolCase::inspect(Result::Ok(_)) => 1,
                BoolCase::inspect(Result::Err(_)) => 0
            }
        }
        selected() -> usize {
            let equal_left = "alpha";
            let equal_right = "alpha";
            let different_left = "alpha";
            let different_right = "beta";
            let equal = score(equal_left == equal_right);
            let different = score(different_left == different_right);
            equal * 10 + different
        }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("string-symbolic-equal.glorious", source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&artifact, "selected"), vec![])
            .unwrap(),
        Value::U64(10)
    );
}

#[test]
fn generic_interner_is_canonical_under_hash_bucket_collisions() {
    fn bucket(value: u64) -> u64 {
        value
            .to_le_bytes()
            .into_iter()
            .fold(0xcbf2_9ce4_8422_2325, |hash, byte| {
                (hash ^ u64::from(byte)).wrapping_mul(0x0000_0100_0000_01b3)
            })
            % 64
    }

    let mut collision = None;
    'outer: for left in 0_u64..128 {
        for right in left + 1..128 {
            if bucket(left) == bucket(right) {
                collision = Some((left, right));
                break 'outer;
            }
        }
    }
    let (left, right) = collision.expect("64 buckets must collide within 128 values");
    let source = format!(
        r#"
        effect InternCase {{ inspect(value: Result<Id<u64>, u64>) -> !; }}
        empty() -> Interner<u64> {{ Interner::new() }}
        intern_id(value: &mut Interner<u64>, item: u64) -> u32 {{
            handle perform InternCase::inspect(Interner::intern(move value, move item)) {{
                InternCase::inspect(Result::Ok(id)) => Id::to_u32(move id),
                InternCase::inspect(Result::Err(rejected)) => {{ rejected; 99 }}
            }}
        }}
        selected() -> u64 {{
            let values = empty();
            let first = intern_id(&mut values, {left});
            let second = intern_id(&mut values, {right});
            let duplicate = intern_id(&mut values, {left});
            wrapping_convert_to_u64(first) * 100
                + wrapping_convert_to_u64(second) * 10
                + wrapping_convert_to_u64(duplicate)
        }}
        main() -> () {{ () }}
        "#
    );
    let artifact = compile_source_to_bytecode("generic-interner.glorious", &source).unwrap();
    let verified = verify(artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&artifact, "selected"), vec![])
            .unwrap(),
        Value::U64(10)
    );
}
