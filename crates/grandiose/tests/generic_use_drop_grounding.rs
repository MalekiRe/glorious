use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::verify;

fn assert_compiles_all_modes(source: &str) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "generic-use-drop-grounding.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        verify(artifact).unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
    }
}

#[test]
fn enclosing_expected_nominal_fixes_payload_free_generic_variant() {
    let source = r#"
        enum Storage<K, V> { Empty, Ready(HashMap<K, Vec<V>>) }
        struct Multi<K, V> { storage: Storage<K, V>, keys: usize }
        fresh<K, V>() -> Multi<K, V> {
            Multi { storage: Storage::Empty, keys: 0 }
        }
        reset<K, V>(value: &mut Multi<K, V>) -> Storage<K, V> {
            replace(&mut value.storage, Storage::Empty)
        }
        expose() -> Multi<i64, i64> { fresh() }
        exercise_reset(value: &mut Multi<i64, i64>) -> Storage<i64, i64> {
            reset(move value)
        }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn nested_vec_use_evidence_grounds_through_hash_map_hooks() {
    let source = r#"
        test_nested_put<K, V>(map: &mut HashMap<K, Vec<V>>, key: K, bucket: Vec<V>) -> ()
            where K: Eq, K: Hash, K: Use<[0,infinity]>, V: Use<[0,infinity]> {
            HashMap::insert(move map, move key, move bucket);
            ()
        }
        test_nested_take<K, V>(map: &mut HashMap<K, Vec<V>>, key: &K) -> Option<Vec<V>>
            where K: Eq, K: Hash, K: Use<[0,infinity]>, V: Use<[0,infinity]> {
            HashMap::remove(move map, move key)
        }
        exercise(
            insert_map: &mut HashMap<i64, Vec<i64>>,
            remove_map: &mut HashMap<i64, Vec<i64>>
        ) -> () {
            test_nested_put(move insert_map, 1, Vec::new());
            let key = 1;
            test_nested_take(move remove_map, &key);
            ()
        }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn nested_vec_zero_use_is_derived_from_its_symbolic_element() {
    let source = r#"
        abandon<T>(value: T) -> () where T: Use<[0,0]> { () }
        abandon_bucket<V>(bucket: Vec<V>) -> () where V: Use<[0,infinity]> {
            abandon(move bucket)
        }
        exercise(bucket: Vec<i64>) -> () { abandon_bucket(move bucket) }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn receiverless_associated_method_uses_generic_where_evidence() {
    let source = r#"
        generic_default<T>() -> T where T: Default { Default::default() }
        generic_take<T>(value: &mut T) -> T where T: Default {
            replace(move value, generic_default())
        }
        answer() -> i64 {
            let value = 42;
            generic_take(&mut value)
        }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
    let recovery = source.replace("main() -> () { () }", "main() -> i64 { answer() }");
    assert_eq!(
        grandiose::run_source(
            "generic-default-recovery.gr",
            &recovery,
            vec![],
            &mut grandiose::eval::SystemHost::default(),
        )
        .unwrap(),
        grandiose::eval::Value::Int(42),
    );
}

#[test]
fn nested_affine_enums_are_inspected_through_shared_and_unique_references() {
    let source = r#"
        struct Token { value: i64 }
        impl Use<[0,1]> for Token {}
        enum Inner { Empty, Full(Token) }
        enum Outer { Empty, Wrap(Inner) }

        shared_probe(value: &Outer) -> i64 {
            if(*value is Outer::Wrap(Inner::Full(_))) { 1 } else { 0 }
        }
        unique_probe(value: &mut Outer) -> i64 {
            if(*value is Outer::Wrap(Inner::Full(_))) { 1 } else { 0 }
        }
        expose_shared(value: &Outer) -> i64 { shared_probe(move value) }
        expose_unique(value: &mut Outer) -> i64 { unique_probe(move value) }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn borrowed_pattern_view_does_not_authorize_mutation_through_an_aliased_unique_reference() {
    let source = r#"
        struct Token { value: i64 }
        impl Use<[0,1]> for Token {}
        enum Outer { Empty, Full(Token) }
        bad(value: &mut Outer) -> i64 {
            let shared = &*value;
            (*value) = Outer::Empty;
            if(*shared is Outer::Full(_)) { 1 } else { 0 }
        }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("borrowed-pattern-alias.gr", source)
        .expect_err("mutation while a shared alias is live must be rejected");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("borrow")
                || error.message.contains("loan")
                || error.message.contains("alias")
                || error.message.contains("moved or suspended")
        }),
        "{errors:#?}"
    );
}

#[test]
fn generic_use_and_drop_heads_allow_coherent_binder_permutations() {
    let source = r#"
        struct Pair<A, B> { left: A, right: B }
        impl<R, L> Use<[0,infinity]> for Pair<L, R>
            where L: Use<[0,infinity]>, R: Use<[0,infinity]> {}

        struct Watched<A, B> { left: A, right: B }
        impl<R, L> Drop for Watched<L, R> {
            drop(&mut self) -> { self.left; self.right; () }
        }

        duplicate(value: Pair<i64, u64>) -> (Pair<i64, u64>, Pair<i64, u64>) {
            (value, value)
        }
        inspect(value: Watched<i64, u64>) -> () { value; () }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn conditional_generic_drop_accepts_structural_where_subjects() {
    let source = r#"
        trait TupleMarker {}
        impl TupleMarker for (i64, u64) {}

        struct Watched<T> { value: T }
        impl<T> Drop for Watched<T> where (T, u64): TupleMarker {
            drop(&mut self) -> { self.value; () }
        }

        inspect(value: Watched<i64>) -> () { value; () }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn specialized_repeated_nested_and_disjoint_ownership_heads_ground() {
    let source = r#"
        struct Specialized<A, B> { marker: i64 }
        impl<T> Use<[0,infinity]> for Specialized<T, i64> {}
        impl<T> Use<[0,infinity]> for Specialized<T, Text> {}

        struct Repeated<A, B> { marker: i64 }
        impl<T> Use<[0,infinity]> for Repeated<T, T> {}

        struct Nested<A> { marker: i64 }
        impl<T> Use<[0,infinity]> for Nested<Vec<T>> {}

        struct Watched<A, B> { marker: i64 }
        impl<T> Drop for Watched<T, i64> {
            drop(&mut self) -> { self.marker; () }
        }
        impl<T> Drop for Watched<T, Text> {
            drop(&mut self) -> { self.marker; () }
        }

        exercise(
            a: Specialized<u64, i64>,
            b: Specialized<u64, Text>,
            repeated: Repeated<i64, i64>,
            nested: Nested<Vec<i64>>,
            left: Watched<u64, i64>,
            right: Watched<u64, Text>
        ) -> () {
            a; b; repeated; nested; left; right; ()
        }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn overlapping_structural_ownership_heads_are_rejected() {
    let source = r#"
        struct Ambiguous<A, B> { marker: i64 }
        impl<T> Use<[0,infinity]> for Ambiguous<T, T> {}
        impl<U> Use<[0,infinity]> for Ambiguous<i64, U> {}
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("overlapping-use-heads.gr", source)
        .expect_err("the two heads overlap at Ambiguous<i64, i64>");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("overlapping") && error.message.contains("Use")),
        "{errors:#?}"
    );
}

#[test]
fn overlapping_structural_drop_heads_are_rejected() {
    let source = r#"
        struct Ambiguous<A, B> { marker: i64 }
        impl<T> Drop for Ambiguous<T, T> {
            drop(&mut self) -> { self.marker; () }
        }
        impl<U> Drop for Ambiguous<i64, U> {
            drop(&mut self) -> { self.marker; () }
        }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("overlapping-drop-heads.gr", source)
        .expect_err("the two heads overlap at Ambiguous<i64, i64>");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("overlapping") && error.message.contains("Drop")
        }),
        "{errors:#?}"
    );
}

#[test]
fn ownership_where_subjects_normalize_ground_associated_projections() {
    let source = r#"
        trait Value { type Item; }
        trait Marker {}
        struct Good { marker: i64 }
        impl Value for Good { type Item = Text; }
        impl Marker for Text {}

        struct Ticket<T> { marker: i64 }
        impl<T> Use<[0,infinity]> for Ticket<T>
            where <T as Value>::Item: Marker {}

        struct Watched<T> { marker: i64 }
        impl<T> Drop for Watched<T>
            where <T as Value>::Item: Marker {
            drop(&mut self) -> { self.marker; () }
        }

        duplicate(value: Ticket<Good>) -> (Ticket<Good>, Ticket<Good>) {
            (value, value)
        }
        inspect(value: Watched<Good>) -> () { value; () }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn unresolved_ownership_projection_reports_the_missing_ground_evidence() {
    let source = r#"
        trait Value { type Item; }
        trait Marker {}
        struct Missing { marker: i64 }
        struct Ticket<T> { marker: i64 }
        impl<T> Use<[0,infinity]> for Ticket<T>
            where <T as Value>::Item: Marker {}

        duplicate(value: Ticket<Missing>) -> (Ticket<Missing>, Ticket<Missing>) {
            (value, value)
        }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("missing-ownership-projection.gr", source)
        .expect_err("an unresolved ground ownership projection must be diagnosed");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("conditional Use where subject")
                && error
                    .message
                    .contains("associated projection has no matching implementation")
        }),
        "{errors:#?}"
    );
}

#[test]
fn generic_fields_and_payloads_close_ground_projection_layouts() {
    let source = r#"
        trait Family { type Item; }
        struct Good { marker: i64 }
        struct Inner<T> { value: T }
        impl Family for Good { type Item = Inner<i64>; }

        struct Holder<T> { value: <T as Family>::Item }
        impl<T> Use<[0,infinity]> for Holder<T>
            where <T as Family>::Item: Use<[0,infinity]> {}

        enum Parcel<T> { Empty, Full(<T as Family>::Item) }
        impl<T> Use<[0,infinity]> for Parcel<T>
            where <T as Family>::Item: Use<[0,infinity]> {}

        retain_holder(value: Holder<Good>) -> Holder<Good> { value }
        retain_parcel(value: Parcel<Good>) -> Parcel<Good> { value }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}

#[test]
fn projection_hidden_owned_cycles_and_growth_are_rejected() {
    let cycle = r#"
        trait Next { type Item; }
        struct Loop<T> { next: <T as Next>::Item }
        impl<T> Next for T { type Item = Loop<T>; }
        expose(value: Loop<i64>) -> Loop<i64> { value }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("projection-cycle.gr", cycle)
        .expect_err("projection-normalized owned recursion must be rejected");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("cycles through")),
        "{errors:#?}"
    );

    let growth = r#"
        trait Next { type Item; }
        struct Grow<T> { next: <T as Next>::Item }
        impl<T> Next for T { type Item = Grow<(T, T)>; }
        expose(value: Grow<i64>) -> Grow<i64> { value }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("projection-growth.gr", growth)
        .expect_err("projection-normalized constructor growth must be rejected");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("expands infinitely")),
        "{errors:#?}"
    );
}

#[test]
fn projection_normalized_decreasing_recursion_reaches_a_finite_base() {
    let source = r#"
        trait Next { type Item; }
        struct End { marker: i64 }
        struct Chain<T> { next: <T as Next>::Item }
        impl Next for i64 { type Item = End; }
        impl<T> Next for (T, T) { type Item = Chain<T>; }

        retain(value: Chain<(i64, i64)>) -> Chain<(i64, i64)> { value }
        main() -> () { () }
    "#;
    assert_compiles_all_modes(source);
}
