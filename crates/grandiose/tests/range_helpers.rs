use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::{Value, Vm, verify};

const SOURCE: &str = r#"
    usize_range(start: usize, end: usize) -> Range<usize> {
        Range { start: move start, end: move end }
    }
    bool_as_usize(value: Bool) -> usize {
        if(value) { 1 } else { 0 }
    }
    range_contains(value: &Range<usize>, candidate: usize) -> Bool {
        Range::contains(value, move candidate)
    }

    len_normal() -> usize {
        let range = usize_range(3, 8);
        Range::len(&range)
    }
    len_empty() -> usize {
        let range = usize_range(5, 5);
        Range::len(&range)
    }
    len_reversed() -> usize {
        let range = usize_range(8, 3);
        Range::len(&range)
    }

    empty_equal() -> usize {
        let range = usize_range(5, 5);
        bool_as_usize(Range::is_empty(&range))
    }
    empty_reversed() -> usize {
        let range = usize_range(8, 3);
        bool_as_usize(Range::is_empty(&range))
    }
    nonempty() -> usize {
        let range = usize_range(3, 8);
        bool_as_usize(Range::is_empty(&range))
    }

    contains_start() -> usize {
        let range = usize_range(3, 8);
        bool_as_usize(range_contains(&range, 3))
    }
    contains_middle() -> usize {
        let range = usize_range(3, 8);
        bool_as_usize(range_contains(&range, 7))
    }
    excludes_end() -> usize {
        let range = usize_range(3, 8);
        bool_as_usize(range_contains(&range, 8))
    }
    reversed_contains_nothing() -> usize {
        let range = usize_range(8, 3);
        bool_as_usize(range_contains(&range, 5))
    }

    intersection_overlap() -> usize {
        let left = usize_range(2, 7);
        let right = usize_range(4, 9);
        let overlap = Option::unwrap_or(
            Range::intersection(&left, &right),
            usize_range(9, 0)
        );
        overlap.start * 10 + overlap.end
    }
    intersection_disjoint() -> usize {
        let left = usize_range(1, 3);
        let right = usize_range(5, 8);
        let overlap = Option::unwrap_or(
            Range::intersection(&left, &right),
            usize_range(9, 1)
        );
        overlap.start * 10 + overlap.end
    }
    intersection_touching() -> usize {
        let left = usize_range(1, 3);
        let right = usize_range(3, 8);
        let overlap = Option::unwrap_or(
            Range::intersection(&left, &right),
            usize_range(9, 2)
        );
        overlap.start * 10 + overlap.end
    }

    offset_zero() -> usize {
        let range = usize_range(3, 8);
        Option::unwrap_or(Range::checked_offset(&range, 0), 90)
    }
    offset_last() -> usize {
        let range = usize_range(3, 8);
        Option::unwrap_or(Range::checked_offset(&range, 4), 90)
    }
    offset_at_end() -> usize {
        let range = usize_range(3, 8);
        Option::unwrap_or(Range::checked_offset(&range, 5), 93)
    }
    offset_overflow() -> usize {
        let maximum = wrapping_convert_to_usize(-1);
        let range = usize_range(maximum - 1, maximum);
        Option::unwrap_or(Range::checked_offset(&range, 2), 94)
    }

    add_index(total: usize, index: usize) -> usize { total + index }
    zero() -> usize { 0 }
    seven() -> usize { 7 }
    checked_add_index(total: usize, index: usize) -> Result<usize, usize> {
        if(index == 3) { Result::Err(total) } else { Result::Ok(total + index) }
    }
    accept_index(index: usize) -> Result<(), usize> {
        if(index == 3) { Result::Err(index) } else { Result::Ok(()) }
    }
    is_three(index: usize) -> Bool { index == 3 }
    ignore_index(index: usize) -> () { index; () }

    range_for_each() -> usize {
        for_range(usize_range(0, 5), ignore_index);
        10
    }
    range_fold() -> usize {
        fold_range(usize_range(0, 5), 0, add_index)
    }
    range_try_for_each() -> usize {
        handle try_for_range(usize_range(0, 6), accept_index) {
            Result::Err(index) => index,
            Result::Ok(_) => 90
        }
    }
    range_try_fold() -> usize {
        handle try_fold_range(usize_range(0, 6), 0, checked_add_index) {
            Result::Err(total) => total,
            Result::Ok(total) => total
        }
    }
    range_find() -> usize {
        Option::unwrap_or(find_range(usize_range(0, 6), is_three), 90)
    }
    range_reversed_for_each() -> usize {
        for_range(usize_range(6, 2), ignore_index);
        seven()
    }

    effect AskIndex { [1,1] ask(index: usize) -> usize }
    effect_add_index(total: usize, index: usize) -> usize / {AskIndex} {
        total + perform AskIndex::ask(index)
    }
    range_effect_fold() -> usize {
        handle fold_range(usize_range(0, 5), 0, effect_add_index) {
            AskIndex::ask(index) with continuation => resume(continuation, index)
        }
    }

    values() -> Vec<usize> {
        let output = Vec::new();
        Vec::push(&mut output, 2);
        Vec::push(&mut output, 3);
        Vec::push(&mut output, 5);
        Vec::push(&mut output, 7);
        output
    }
    add_item(total: usize, item: &usize) -> usize { total + *item }
    checked_add_item(total: usize, item: &usize) -> Result<usize, usize> {
        if(*item == 5) { Result::Err(total) } else { Result::Ok(total + *item) }
    }
    accept_item(item: &usize) -> Result<(), usize> {
        if(*item == 5) { Result::Err(*item) } else { Result::Ok(()) }
    }
    is_five(item: &usize) -> Bool { *item == 5 }
    ignore_item(item: &usize) -> () { *item; () }

    slice_for_each() -> usize {
        let source = values();
        Slice::for_each(Vec::as_slice(&source), ignore_item);
        17
    }
    slice_fold() -> usize {
        let source = values();
        Slice::fold(Vec::as_slice(&source), 0, add_item)
    }
    slice_try_for_each() -> usize {
        let source = values();
        handle Slice::try_for_each(Vec::as_slice(&source), accept_item) {
            Result::Err(item) => item,
            Result::Ok(_) => 90
        }
    }
    slice_try_fold() -> usize {
        let source = values();
        handle Slice::try_fold(Vec::as_slice(&source), 0, checked_add_item) {
            Result::Err(total) => total,
            Result::Ok(total) => total
        }
    }
    slice_find_index() -> usize {
        let source = values();
        Option::unwrap_or(Slice::find_index(Vec::as_slice(&source), is_five), 90)
    }
    slice_find() -> usize {
        let source = values();
        handle Slice::find(Vec::as_slice(&source), is_five) {
            Option::Some(item) => *item,
            None => 90
        }
    }

    main() -> () { () }
"#;

#[test]
fn distributed_range_helpers_execute_with_o0_o3_boundary_parity() {
    let expected = [
        ("len_normal", 5),
        ("len_empty", 0),
        ("len_reversed", 0),
        ("empty_equal", 1),
        ("empty_reversed", 1),
        ("nonempty", 0),
        ("contains_start", 1),
        ("contains_middle", 1),
        ("excludes_end", 0),
        ("reversed_contains_nothing", 0),
        ("intersection_overlap", 47),
        ("intersection_disjoint", 91),
        ("intersection_touching", 92),
        ("offset_zero", 3),
        ("offset_last", 7),
        ("offset_at_end", 93),
        ("offset_overflow", 94),
        ("range_for_each", 10),
        ("range_fold", 10),
        ("range_try_for_each", 3),
        ("range_try_fold", 3),
        ("range_find", 3),
        ("range_reversed_for_each", 7),
        ("range_effect_fold", 10),
        ("slice_for_each", 17),
        ("slice_fold", 17),
        ("slice_try_for_each", 5),
        ("slice_try_fold", 5),
        ("slice_find_index", 2),
        ("slice_find", 5),
    ];

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "range-helpers.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(artifact.clone()).unwrap();
        for (name, answer) in expected {
            let function = artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap_or_else(|| panic!("missing `{name}`")) as u32;
            assert_eq!(
                Vm::new(verified.clone()).run(function, vec![]).unwrap(),
                Value::U64(answer),
                "{optimization_level:?} {name}"
            );
        }
    }
}
