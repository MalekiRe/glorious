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
            "ordering algorithm test performed a host effect",
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

const ALGORITHM_SURFACE: &str = r#"
    effect UsizeCase { inspect(value: Option<usize>) -> !; }
    effect BoolCase { inspect(value: Bool) -> !; }
    effect OrderingCase { inspect(value: Ordering) -> !; }

    option_or_len(value: Option<usize>, length: usize) -> usize {
        handle perform UsizeCase::inspect(move value) {
            UsizeCase::inspect(Result::Ok(index)) => move index,
            UsizeCase::inspect(Result::Err(_)) => move length
        }
    }

    ordering_score(value: Ordering) -> usize {
        handle perform OrderingCase::inspect(move value) {
            OrderingCase::inspect(Ordering::Less) => 1,
            OrderingCase::inspect(Ordering::Equal) => 2,
            OrderingCase::inspect(Ordering::Greater) => 3
        }
    }

    empty_i64() -> Vec<i64> { Vec::new() }
    i64_at(value: &Vec<i64>, index: usize) -> i64 {
        let item = Vec::index(value, index);
        *item
    }

    push_descending(value: &mut Vec<i64>, remaining: usize) -> () {
        handle perform BoolCase::inspect(remaining == 0) {
            BoolCase::inspect(Result::Ok(_)) => { value; () },
            BoolCase::inspect(Result::Err(_)) => {
                Vec::push(&mut *value, wrapping_convert_to_i64(remaining));
                push_descending(move value, remaining - 1)
            }
        }
    }

    push_equal(value: &mut Vec<i64>, remaining: usize) -> () {
        handle perform BoolCase::inspect(remaining == 0) {
            BoolCase::inspect(Result::Ok(_)) => { value; () },
            BoolCase::inspect(Result::Err(_)) => {
                Vec::push(&mut *value, 7);
                push_equal(move value, remaining - 1)
            }
        }
    }

    weighted(value: &Vec<i64>, cursor: usize, result: i64) -> i64 {
        handle perform BoolCase::inspect(cursor < Vec::len(value)) {
            BoolCase::inspect(Result::Err(_)) => move result,
            BoolCase::inspect(Result::Ok(_)) => weighted(
                value, cursor + 1,
                move result + i64_at(value, cursor)
                    * wrapping_convert_to_i64(cursor + 1)
            )
        }
    }

    introsort_hostile() -> i64 {
        let descending = empty_i64();
        push_descending(&mut descending, 96);
        Vec::sort(&mut descending);
        let first = i64_at(&descending, 0);
        let last = i64_at(&descending, 95);

        let equal = empty_i64();
        push_equal(&mut equal, 128);
        Vec::sort(&mut equal);
        move first * 10000 + move last * 100 + weighted(&equal, 0, 0)
    }

    bounds_partition_dedup() -> usize {
        let values = empty_i64();
        Vec::push(&mut values, 1);
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 4);
        Vec::push(&mut values, 9);
        let two = 2;
        let four = 4;
        let three = 3;
        let lower = Vec::lower_bound(&values, &two);
        let upper = Vec::upper_bound(&values, &two);
        let found = option_or_len(Vec::binary_search(&values, &four), 99);
        let absent = option_or_len(Vec::binary_search(&values, &three), 9);
        Vec::dedup(&mut values);

        let mixed = empty_i64();
        Vec::push(&mut mixed, 5);
        Vec::push(&mut mixed, 1);
        Vec::push(&mut mixed, 4);
        Vec::push(&mut mixed, 2);
        Vec::push(&mut mixed, 3);
        let boundary = Vec::partition(&mut mixed, &three);
        lower * 100000 + upper * 10000 + found * 1000
            + absent * 100 + Vec::len(&values) * 10 + boundary
    }

    lexicographic() -> usize {
        let left = empty_i64();
        Vec::push(&mut left, 1);
        Vec::push(&mut left, 2);
        let greater = empty_i64();
        Vec::push(&mut greater, 1);
        Vec::push(&mut greater, 3);
        let equal = empty_i64();
        Vec::push(&mut equal, 1);
        Vec::push(&mut equal, 2);
        let prefix = empty_i64();
        Vec::push(&mut prefix, 1);
        ordering_score(Vec::lexicographic_cmp(&left, &greater)) * 100
            + ordering_score(Vec::lexicographic_cmp(&left, &equal)) * 10
            + ordering_score(Vec::lexicographic_cmp(&left, &prefix))
    }

    stable_merge() -> i64 {
        let values = empty_i64();
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 1);
        Vec::push(&mut values, 2);
        Vec::push(&mut values, 1);
        Vec::push(&mut values, 2);
        Vec::sort_stable(&mut values);
        i64_at(&values, 0) * 10000
            + i64_at(&values, 1) * 1000
            + i64_at(&values, 2) * 100
            + i64_at(&values, 3) * 10
            + i64_at(&values, 4)
    }

    cmp_i64(left: &i64, right: &i64) -> Ordering { Ord::cmp(left, right) }
    struct Record { key: i64, sequence: i64 }
    impl Ord for Record {
        cmp(self: &Record, other: &Record) -> Ordering {
            cmp_i64(&self.key, &other.key)
        }
    }
    empty_records() -> Vec<Record> { Vec::new() }
    record_sequence(value: &Vec<Record>, index: usize) -> i64 {
        let item = Vec::index(value, index);
        item.sequence
    }
    stable_records() -> i64 {
        let values = empty_records();
        Vec::push(&mut values, Record { key: 2, sequence: 0 });
        Vec::push(&mut values, Record { key: 1, sequence: 1 });
        Vec::push(&mut values, Record { key: 2, sequence: 2 });
        Vec::push(&mut values, Record { key: 1, sequence: 3 });
        Vec::push(&mut values, Record { key: 2, sequence: 4 });
        Vec::sort_stable(&mut values);
        record_sequence(&values, 0) * 10000
            + record_sequence(&values, 1) * 1000
            + record_sequence(&values, 2) * 100
            + record_sequence(&values, 3) * 10
            + record_sequence(&values, 4)
    }

    comprehensive() -> usize {
        bounds_partition_dedup() + lexicographic()
            + wrapping_convert_to_usize(stable_merge())
            + wrapping_convert_to_usize(stable_records())
    }

    main() -> () { () }
"#;

#[test]
fn algorithms_execute_on_hostile_inputs_at_o0_through_o3() {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "ordering-algorithms.glorious",
            ALGORITHM_SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let artifact = verify(phases.artifact.clone()).unwrap();
        let vm = Vm::new(artifact);
        for (name, expected) in [
            ("introsort_hostile", Value::I64(77_392)),
            ("bounds_partition_dedup", Value::U64(144_942)),
            ("lexicographic", Value::U64(123)),
            ("stable_merge", Value::I64(11_222)),
            ("stable_records", Value::I64(13_024)),
            ("comprehensive", Value::U64(169_311)),
        ] {
            assert_eq!(
                vm.run(function_id(&phases.artifact, name), vec![]).unwrap(),
                expected,
                "{optimization_level:?}: {name}"
            );
        }
    }
}

#[test]
fn algorithms_have_recovery_execution_parity() {
    let result = run_source(
        "ordering-algorithms-recovery.glorious",
        &ALGORITHM_SURFACE.replace("main() -> () { () }", "main() -> usize { comprehensive() }"),
        vec![],
        &mut NoHost,
    )
    .unwrap();
    assert_eq!(result, RecoveryValue::Int(169_311));
}

#[test]
fn sort_does_not_require_generic_elements_to_be_discardable_or_copyable() {
    let source = r#"
        cmp_i64(left: &i64, right: &i64) -> Ordering { Ord::cmp(left, right) }
        struct Linear { key: i64 }
        impl Use<[1,1]> for Linear {}
        impl Ord for Linear {
            cmp(self: &Linear, other: &Linear) -> Ordering {
                cmp_i64(&self.key, &other.key)
            }
        }
        sort_linear(values: &mut Vec<Linear>) -> () {
            Vec::sort(&mut *values);
            Vec::sort_stable(move values)
        }
        main() -> () { () }
    "#;
    compile_source_to_bytecode("must-move-sort.glorious", source).unwrap();
}
