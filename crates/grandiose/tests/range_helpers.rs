use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

const SOURCE: &str = r#"
    usize_range(start: usize, end: usize) -> Range<usize> {
        Range { start: move start, end: move end }
    }
    bool_as_usize(value: Bool) -> usize {
        if(value) { 1 } else { 0 }
    }
    recoverable_report() -> usize {
        handle { perform Report<usize>::emit(40); 2 } {
            Report<usize>::emit(diagnostic) with continuation =>
                diagnostic + resume(continuation, ())
        }
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
    inline_range_fold() -> usize {
        fold_range(usize_range(0, 4), 0, { total, index =>
            add_index(add_index(total, index), 1)
        })
    }
    inline_range_find() -> usize {
        Option::unwrap_or(
            find_range(usize_range(0, 6), { index => index + 1 == 4 }),
            90
        )
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
    map_three(index: usize) -> Option<usize> {
        if(index == 3) { Option::Some(index + 10) } else { None }
    }
    is_odd_match(index: usize) -> Bool {
        if(index == 1) { true } else { index == 3 }
    }
    is_two(index: usize) -> Bool { index == 2 }
    below_five(index: usize) -> Bool { index < 5 }
    range_find_map() -> usize {
        Option::unwrap_or(find_map_range(usize_range(0, 6), map_three), 90)
    }
    range_find_map_alias() -> usize {
        Option::unwrap_or(find_map(usize_range(0, 6), map_three), 90)
    }
    range_position_alias() -> usize {
        Option::unwrap_or(position(usize_range(0, 6), is_three), 90)
    }
    range_any() -> usize {
        bool_as_usize(any_range(usize_range(0, 6), is_three))
    }
    range_any_alias() -> usize {
        bool_as_usize(any(usize_range(0, 6), is_three))
    }
    range_all() -> usize {
        bool_as_usize(all_range(usize_range(0, 5), below_five))
    }
    range_all_alias() -> usize {
        bool_as_usize(all(usize_range(0, 5), below_five))
    }
    range_first_error() -> usize {
        Option::unwrap_or(first_error_range(usize_range(0, 6), accept_index), 90)
    }
    range_first_error_alias() -> usize {
        Option::unwrap_or(first_error(usize_range(0, 6), accept_index), 90)
    }
    range_unique_missing() -> usize {
        handle find_unique_by(usize_range(0, 2), is_three) {
            UniqueMatch::Missing => 91,
            UniqueMatch::Unique(value) => value,
            UniqueMatch::Ambiguous(first, second) => first * 10 + second
        }
    }
    range_unique_single() -> usize {
        handle find_unique_by(usize_range(0, 4), is_two) {
            UniqueMatch::Missing => 90,
            UniqueMatch::Unique(value) => value,
            UniqueMatch::Ambiguous(first, second) => first * 10 + second
        }
    }
    range_unique_ambiguous() -> usize {
        handle find_unique_by(usize_range(0, 5), is_odd_match) {
            UniqueMatch::Missing => 90,
            UniqueMatch::Unique(value) => value,
            UniqueMatch::Ambiguous(first, second) => first * 10 + second
        }
    }
    range_unique_alias() -> usize {
        handle find_unique(usize_range(0, 4), is_two) {
            UniqueMatch::Missing => 90,
            UniqueMatch::Unique(value) => value,
            UniqueMatch::Ambiguous(first, second) => first * 10 + second
        }
    }
    collect_until_complete() -> usize {
        @done: usize {
            let values = collect_until(
                usize_range(0, 4),
                @done,
                { index, _ => __g1_usize_successor(index) }
            );
            Vec::len(&values)
        }
    }
    collect_until_early() -> usize {
        @done: usize {
            let values = collect_until(
                usize_range(0, 5),
                @done,
                { index, exit => if(index == 3) { exit(30 + index) } else { index } }
            );
            Vec::len(&values)
        }
    }
    double_index(index: usize) -> usize { index * 2 }
    checked_double_index(index: usize) -> Result<usize, usize> {
        if(index == 3) { Result::Err(index) } else { Result::Ok(index * 2) }
    }
    range_append_builder() -> usize {
        let output = values();
        let appended = append_range(&mut output, usize_range(0, 2), double_index);
        appended.start * 100 + appended.end * 10 + Vec::len(&output)
    }
    range_map_builder() -> usize {
        let output = map_range(usize_range(0, 3), double_index);
        Vec::len(&output) * 100 + Slice::fold(Vec::as_slice(&output), 0, add_item)
    }
    range_try_map_error() -> usize {
        handle try_map_range(usize_range(0, 5), checked_double_index) {
            Result::Ok(output) => Vec::len(&output) + 90,
            Result::Err(error) => error
        }
    }
    append_digit(total: usize, item: usize) -> usize { total * 10 + item }
    new_usize_stack() -> Stack<usize> { Stack::new() }
    new_usize_worklist() -> WorkList<usize> { WorkList::new() }
    new_usize_solver(limit: usize) -> WorklistSolver<usize> {
        WorklistSolver::new(limit)
    }
    drain_stack_order() -> usize {
        let work = new_usize_stack();
        Stack::push(&mut work, 1);
        Stack::push(&mut work, 2);
        Stack::push(&mut work, 3);
        drain_stack(move work, 0, append_digit)
    }
    drain_queue_order() -> usize {
        let work = new_usize_worklist();
        WorkList::push(&mut work, 1);
        WorkList::push(&mut work, 2);
        WorkList::push(&mut work, 3);
        drain_queue(move work, 0, append_digit)
    }
    enqueue_successor(
        total: usize,
        item: usize,
        work: WorkList<usize>
    ) -> WorklistUpdate<usize, usize> {
        if(item < 3) {
            WorkList::push(&mut work, item + 1)
        } else {
            ()
        };
        worklist_update(move work, total * 10 + item)
    }
    drain_worklist_growth() -> usize {
        let work = new_usize_worklist();
        WorkList::push(&mut work, 1);
        solve_worklist(move work, 0, enqueue_successor)
    }
    bounded_worklist_step(
        total: usize,
        item: usize
    ) -> WorklistStep<usize, usize> {
        let dependents = Vec::new();
        if(item < 3) {
            Vec::push(&mut dependents, item + 1);
            Vec::push(&mut dependents, item + 1)
        } else { () };
        worklist_step(move dependents, total * 10 + item)
    }
    bounded_worklist_success() -> usize {
        let solver = new_usize_solver(4);
        WorklistSolver::enqueue(&mut solver, 1);
        WorklistSolver::enqueue(&mut solver, 1);
        handle solve_worklist_bounded(move solver, 0, bounded_worklist_step) {
            Result::Err(_) => 90,
            Result::Ok(value) => value
        }
    }
    bounded_worklist_limit() -> usize {
        let solver = new_usize_solver(2);
        WorklistSolver::enqueue(&mut solver, 1);
        handle solve_worklist_bounded(move solver, 0, bounded_worklist_step) {
            Result::Err(WorklistFailure::StepLimitExceeded) => 92,
            Result::Ok(value) => value
        }
    }
    bounded_worklist_witness() -> usize {
        @found: usize {
        let solver = new_usize_solver(4);
        WorklistSolver::enqueue(&mut solver, 1);
        handle solve_worklist_bounded(move solver, zero(), {
            total, item => if(item == wrapping_convert_to_usize(2)) {
                @found(item)
            } else {
                let dependents = Vec::new();
                Vec::push(&mut dependents, item + wrapping_convert_to_usize(1));
                worklist_step(move dependents, total + item)
            }
            }) {
                Result::Err(_) => wrapping_convert_to_usize(90),
                Result::Ok(_) => wrapping_convert_to_usize(91)
            }
        }
    }
    increment_until_four(value: usize) -> Stability<usize> {
        if(value < 4) { changed(value + 1) } else { stable(value) }
    }
    fixed_point_four() -> usize { fixed_point(0, increment_until_four) }
    range_reversed_for_each() -> usize {
        for_range(usize_range(6, 2), ignore_index);
        seven()
    }
    fold_until_sum(stop: usize) -> usize {
        @done: usize {
            fold_until(usize_range(0, 5), 0, @done, {
                total, index, exit => if(index == stop) {
                    exit(total)
                } else {
                    total + index
                }
            })
        }
    }
    fold_until_complete() -> usize { fold_until_sum(9) }
    fold_until_early() -> usize { fold_until_sum(3) }
    scan_until_early() -> usize {
        @done: usize {
            scan_until(usize_range(0, 5), 0, @done, { total, index, exit =>
                if(index == 3) { exit(total) } else { total + index }
            })
        }
    }
    fold_control_complete() -> usize {
        @done: usize {
            fold_control(usize_range(0, 4), 0, @done, { total, index, exit =>
                total + index
            })
        }
    }
    for_range_control_early() -> usize {
        @done: usize {
            for_range_control(usize_range(0, 5), @done, { index, exit =>
                if(index == 2) { exit(8) } else { () }
            });
            9
        }
    }

    loop_state_count() -> usize {
        @done: usize {
            loop_state(zero(), @done, { state, exit =>
                if(state == 5) {
                    loop_break(state, state, exit)
                } else {
                    loop_continue(state + 1, exit)
                }
            })
        }
    }
    repeat_count() -> usize {
        @done: usize {
            repeat(zero(), @done, { state, exit =>
                if(state == 4) {
                    loop_break(state, state, exit)
                } else {
                    loop_continue(state + 1, exit)
                }
            })
        }
    }
    below_four(value: &usize) -> Bool { *value < 4 }
    increment_state(value: usize) -> usize { value + 1 }
    while_state_count() -> usize { while_state(0, below_four, increment_state) }
    loop_state_capture() -> usize {
        let limit = wrapping_convert_to_usize(4);
        @done: usize {
            loop_state(zero(), @done, { state, exit =>
                if(state == limit) {
                    loop_break(state, state, exit)
                } else {
                    loop_continue(state + 1, exit)
                }
            })
        }
    }
    loop_state_continue_only() -> usize {
        @done: usize {
            loop_state(zero(), @done, { state, exit =>
                if(state == 3) {
                    exit(state)
                } else {
                    loop_continue(state + 1, exit)
                }
            })
        }
    }
    loop_state_nested() -> usize {
        @outer: usize {
            loop_state(zero(), @outer, { state, outer_exit =>
                if(state == 2) {
                    loop_break(state, state, outer_exit)
                } else {
                    let increment = @inner: usize {
                        loop_state(zero(), @inner, { inner, inner_exit =>
                            if(inner == 1) {
                                loop_break(inner, inner, inner_exit)
                            } else {
                                loop_continue(inner + 1, inner_exit)
                            }
                        })
                    };
                    loop_continue(state + increment, outer_exit)
                }
            })
        }
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
    loop_state_effect() -> usize {
        handle @done: usize {
            loop_state(zero(), @done, { state, exit =>
                if(state == 3) {
                    loop_break(state, state, exit)
                } else {
                    loop_continue(perform AskIndex::ask(state), exit)
                }
            })
        } {
            AskIndex::ask(index) with continuation =>
                resume(continuation, index + 1)
        }
    }

    guard_failure() -> usize {
        handle @failed: Result<usize, usize> {
            ensure(false, 7, @failed);
            Result::Ok(9)
        } {
            Result::Err(error) => error,
            Result::Ok(value) => value
        }
    }
    leave_if_taken() -> usize {
        @done: usize {
            leave_if(true, 8, @done);
            9
        }
    }
    require_failure() -> usize {
        handle @failed: Result<usize, usize> {
            Result::Ok(require(None, 6, @failed))
        } {
            Result::Err(error) => error,
            Result::Ok(value) => value
        }
    }
    some_leave_failure() -> usize {
        @failed: usize {
            some_or_leave(None, 5, @failed)
        }
    }
    require_eq_failure() -> usize {
        handle @failed: Result<usize, usize> {
            require_eq(false, 4, @failed);
            Result::Ok(9)
        } {
            Result::Err(error) => error,
            Result::Ok(value) => value
        }
    }
    require_index_failure() -> usize {
        handle @failed: Result<usize, usize> {
            Result::Ok(require_index(None, 3, @failed))
        } {
            Result::Err(error) => error,
            Result::Ok(value) => value
        }
    }
    require_conversion_failure() -> usize {
        handle @failed: Result<usize, usize> {
            Result::Ok(require_conversion(Result::Err(2), @failed))
        } {
            Result::Err(error) => error,
            Result::Ok(value) => value
        }
    }
    return_if_taken() -> usize {
        @done: usize {
            return_if(true, 1, @done);
            9
        }
    }

    struct TestVecCheckpoint<'a> {
        value: &'a mut Vec<usize>,
        length: usize,
        armed: Bool
    }
    impl<'a> Drop for TestVecCheckpoint<'a> {
        drop(&mut self) -> {
            if(self.armed) { Vec::truncate(&mut *self.value, self.length) }
            else { () }
        }
    }
    test_checkpoint_new<'a>(value: &'a mut Vec<usize>) -> TestVecCheckpoint<'a> {
        let length = Vec::len(&*value);
        TestVecCheckpoint { value: move value, length: move length, armed: true }
    }
    test_checkpoint_commit<'a>(value: &mut TestVecCheckpoint<'a>) {
        (*value).armed = false;
        ()
    }
    test_try_with_range<F, e: EffectRow>(
        value: &mut Vec<usize>, body: F
    ) -> Result<Range<usize>, usize>
    where F: Fn<(&mut Vec<usize>,), Output=Result<(), usize>, Effects={ | e}>,
    F: Use<[0, 0]> {
        @failed: Result<Range<usize>, usize> {
            let checkpoint = test_checkpoint_new(move value);
            let start = checkpoint.length;
            try(body(&mut *checkpoint.value), @failed);
            let end = Vec::len(&*checkpoint.value);
            test_checkpoint_commit(&mut checkpoint);
            Result::Ok(Range { start: move start, end: move end })
        }
    }
    append_then_fail(value: &mut Vec<usize>) -> Result<(), usize> {
        Vec::push(&mut *value, 8);
        Vec::push(&mut *value, 9);
        Result::Err(7)
    }
    append_two(value: &mut Vec<usize>) {
        Vec::push(&mut *value, 8);
        Vec::push(&mut *value, 9)
    }
    checkpoint_rollback() -> usize {
        let output = values();
        handle test_try_with_range(&mut output, append_then_fail) {
            Result::Err(error) => Vec::len(&output) * 10 + error,
            Result::Ok(_) => 90
        }
    }
    diagnostic_frame_leave(value: &mut Vec<usize>) -> usize {
        @done: usize {
            with_diagnostic_context(&mut *value, { output => {
                Vec::push(&mut *output, 9);
                @done(seven())
            }})
        }
    }
    diagnostic_frame_rollback() -> usize {
        let output = values();
        let result = diagnostic_frame_leave(&mut output);
        Vec::len(&output) * 10 + result
    }
    with_range_success() -> usize {
        let output = values();
        let appended = with_range(&mut output, append_two);
        appended.start * 100 + appended.end * 10 + Vec::len(&output)
    }
    try_with_range_rollback() -> usize {
        let output = values();
        handle try_with_range(&mut output, append_then_fail) {
            Result::Err(error) => Vec::len(&output) * 10 + error,
            Result::Ok(_) => 90
        }
    }

    struct TestIndexTag {}
    new_test_index_vec() -> IndexVec<TestIndexTag, usize> { IndexVec::new() }
    append_index_values(value: &mut IndexVec<TestIndexTag, usize>) {
        IndexVec::push(&mut *value, 11);
        IndexVec::push(&mut *value, 13);
        ()
    }
    append_index_then_fail(
        value: &mut IndexVec<TestIndexTag, usize>
    ) -> Result<(), usize> {
        IndexVec::push(&mut *value, 17);
        Result::Err(8)
    }
    index_vec_with_range() -> usize {
        let output = new_test_index_vec();
        IndexVec::push(&mut output, 7);
        let appended = IndexVec::with_range(&mut output, append_index_values);
        appended.start * 100 + appended.end * 10 + IndexVec::len(&output)
    }
    index_vec_try_rollback() -> usize {
        let output = new_test_index_vec();
        IndexVec::push(&mut output, 7);
        handle IndexVec::try_with_range(&mut output, append_index_then_fail) {
            Result::Err(error) => IndexVec::len(&output) * 10 + error,
            Result::Ok(_) => 90
        }
    }

    new_test_arena() -> Arena<TestIndexTag, usize> { Arena::new() }
    append_arena_values(value: &mut Arena<TestIndexTag, usize>) {
        Arena::alloc(&mut *value, 11);
        Arena::alloc(&mut *value, 13);
        ()
    }
    append_arena_then_fail(
        value: &mut Arena<TestIndexTag, usize>
    ) -> Result<(), usize> {
        Arena::alloc(&mut *value, 17);
        Result::Err(9)
    }
    arena_with_range() -> usize {
        let output = new_test_arena();
        Arena::alloc(&mut output, 7);
        let appended = Arena::with_range(&mut output, append_arena_values);
        appended.start * 100 + appended.end * 10 + Arena::len(&output)
    }
    arena_try_rollback() -> usize {
        let output = new_test_arena();
        Arena::alloc(&mut output, 7);
        handle Arena::try_with_range(&mut output, append_arena_then_fail) {
            Result::Err(error) => Arena::len(&output) * 10 + error,
            Result::Ok(_) => 90
        }
    }

    byte_buf_append_two(value: &mut ByteBuf) {
        ByteBuf::push(&mut *value, 8);
        ByteBuf::push(&mut *value, 9)
    }
    byte_buf_append_then_fail(value: &mut ByteBuf) -> Result<(), usize> {
        ByteBuf::push(&mut *value, 8);
        Result::Err(6)
    }
    byte_buf_with_record() -> usize {
        let output = ByteBuf::new();
        ByteBuf::push(&mut output, 1);
        let record = ByteBuf::with_record(&mut output, byte_buf_append_two);
        record.start * 100 + record.end * 10 + ByteBuf::len(&output)
    }
    byte_buf_try_rollback() -> usize {
        let output = ByteBuf::new();
        ByteBuf::push(&mut output, 1);
        handle ByteBuf::try_with_record(&mut output, byte_buf_append_then_fail) {
            Result::Err(error) => ByteBuf::len(&output) * 10 + error,
            Result::Ok(_) => 90
        }
    }
    byte_buf_length_prefix() -> usize {
        let output = ByteBuf::new();
        handle ByteBuf::with_length_prefix(&mut output, byte_buf_append_two) {
            Result::Ok(payload) => {
                let bytes = ByteBuf::finish(move output);
                let reader = ByteReader::new(&bytes);
                let length = Option::unwrap_or(ByteReader::read_u32_le(&mut reader), 99);
                payload.start * 100 + payload.end * 10 + wrapping_convert_to_usize(length)
            },
            Result::Err(_) => 90
        }
    }
    byte_buf_offset_record(value: &mut ByteBuf, index: usize) {
        ByteBuf::push(&mut *value, wrapping_convert_to_u8(index + 1));
        if(index == 1) { ByteBuf::push(&mut *value, 9) } else { () }
    }
    byte_buf_offset_table() -> usize {
        let output = ByteBuf::new();
        ByteBuf::push(&mut output, 9);
        handle ByteBuf::with_offset_table(&mut output, 3, byte_buf_offset_record) {
            Result::Err(_) => 99,
            Result::Ok(payload) => {
                let bytes = ByteBuf::finish(move output);
                let reader = ByteReader::new(&bytes);
                let prefix = wrapping_convert_to_usize(Option::unwrap_or(
                    ByteReader::read_u8(&mut reader),
                    0
                ));
                let first = wrapping_convert_to_usize(Option::unwrap_or(
                    ByteReader::read_u32_le(&mut reader),
                    90
                ));
                let second = wrapping_convert_to_usize(Option::unwrap_or(
                    ByteReader::read_u32_le(&mut reader),
                    90
                ));
                let third = wrapping_convert_to_usize(Option::unwrap_or(
                    ByteReader::read_u32_le(&mut reader),
                    90
                ));
                prefix * 10000 + first * 1000 + second * 100 + third * 10
                    + payload.end - payload.start
            }
        }
    }
    byte_buf_offset_leave(value: &mut ByteBuf) -> usize {
        @done: usize {
            handle ByteBuf::with_offset_table(&mut *value, 2, {
                output, index => {
                    ByteBuf::push(&mut *output, 8);
                    if(index == 1) { @done(seven()) } else { () }
                }
            }) {
                Result::Err(_) => 90,
                Result::Ok(_) => 91
            }
        }
    }
    byte_buf_offset_rollback() -> usize {
        let output = ByteBuf::new();
        ByteBuf::push(&mut output, 1);
        let result = byte_buf_offset_leave(&mut output);
        ByteBuf::len(&output) * 10 + result
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
        ("recoverable_report", 42),
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
        ("inline_range_fold", 10),
        ("inline_range_find", 3),
        ("range_try_for_each", 3),
        ("range_try_fold", 3),
        ("range_find", 3),
        ("range_find_map", 13),
        ("range_find_map_alias", 13),
        ("range_position_alias", 3),
        ("range_any", 1),
        ("range_any_alias", 1),
        ("range_all", 1),
        ("range_all_alias", 1),
        ("range_first_error", 3),
        ("range_first_error_alias", 3),
        ("range_unique_missing", 91),
        ("range_unique_single", 2),
        ("range_unique_ambiguous", 13),
        ("range_unique_alias", 2),
        ("collect_until_complete", 4),
        ("collect_until_early", 33),
        ("range_append_builder", 466),
        ("range_map_builder", 306),
        ("range_try_map_error", 3),
        ("drain_stack_order", 321),
        ("drain_queue_order", 123),
        ("drain_worklist_growth", 123),
        ("bounded_worklist_success", 123),
        ("bounded_worklist_limit", 92),
        ("bounded_worklist_witness", 2),
        ("fixed_point_four", 4),
        ("range_reversed_for_each", 7),
        ("fold_until_complete", 10),
        ("fold_until_early", 3),
        ("scan_until_early", 3),
        ("fold_control_complete", 6),
        ("for_range_control_early", 8),
        ("loop_state_count", 5),
        ("repeat_count", 4),
        ("while_state_count", 4),
        ("loop_state_capture", 4),
        ("loop_state_continue_only", 3),
        ("loop_state_nested", 2),
        ("range_effect_fold", 10),
        ("loop_state_effect", 3),
        ("guard_failure", 7),
        ("leave_if_taken", 8),
        ("require_failure", 6),
        ("some_leave_failure", 5),
        ("require_eq_failure", 4),
        ("require_index_failure", 3),
        ("require_conversion_failure", 2),
        ("return_if_taken", 1),
        ("checkpoint_rollback", 47),
        ("diagnostic_frame_rollback", 47),
        ("with_range_success", 466),
        ("try_with_range_rollback", 47),
        ("index_vec_with_range", 133),
        ("index_vec_try_rollback", 18),
        ("arena_with_range", 133),
        ("arena_try_rollback", 19),
        ("byte_buf_with_record", 133),
        ("byte_buf_try_rollback", 16),
        ("byte_buf_length_prefix", 462),
        ("byte_buf_offset_table", 90134),
        ("byte_buf_offset_rollback", 17),
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
        let phases = compile_source_to_phases_with_options(
            "range-helpers.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        if optimization_level == OptimizationLevel::O1 {
            let loop_plans = phases
                .core
                .control_plans
                .iter()
                .filter(|plan| plan.helper.contains("loop_state"))
                .collect::<Vec<_>>();
            assert!(!loop_plans.is_empty(), "missing loop_state control plans");
            assert!(
                loop_plans.iter().all(|plan| {
                    !plan.residual_callable_allocation
                        && !plan.residual_effect_handler
                        && plan.failure_reason.is_none()
                }),
                "loop_state left residual runtime control machinery: {loop_plans:#?}"
            );
            assert!(
                loop_plans.iter().any(|plan| {
                    plan.helper == "__g1_loop_state_step"
                        && plan.tail_recursive_cycle
                        && plan.formed_control_loop.is_some()
                }),
                "loop_state recursion did not form a direct Core loop: {loop_plans:#?}"
            );
            let fixed_point_plans = phases
                .core
                .control_plans
                .iter()
                .filter(|plan| plan.helper == "__g1_repeat_until_stable_step")
                .collect::<Vec<_>>();
            assert!(
                fixed_point_plans.iter().any(|plan| {
                    plan.tail_recursive_cycle
                        && plan.formed_control_loop.is_some()
                        && !plan.residual_callable_allocation
                        && !plan.residual_effect_handler
                        && plan.failure_reason.is_none()
                }),
                "fixed-point recursion did not fuse to a direct Core loop: {fixed_point_plans:#?}"
            );
            let bounded_solver_plans = phases
                .core
                .control_plans
                .iter()
                .filter(|plan| plan.helper == "__g1_solve_worklist_bounded_step")
                .collect::<Vec<_>>();
            assert!(
                bounded_solver_plans.iter().any(|plan| {
                    plan.tail_recursive_cycle
                        && plan.formed_control_loop.is_some()
                        && !plan.residual_callable_allocation
                        && !plan.residual_effect_handler
                        && plan.failure_reason.is_none()
                }),
                "bounded worklist recursion did not fuse to a direct Core loop: {bounded_solver_plans:#?}"
            );
        }
        let artifact = phases.artifact;
        let verified = verify(artifact.clone()).unwrap();
        for (name, answer) in expected {
            let function = artifact
                .functions
                .iter()
                .position(|function| function.name == name)
                .unwrap_or_else(|| panic!("missing `{name}`")) as u32;
            assert_eq!(
                Vm::new(verified.clone())
                    .run(function, vec![])
                    .unwrap_or_else(|error| panic!("{optimization_level:?} {name}: {error}")),
                Value::U64(answer),
                "{optimization_level:?} {name}"
            );
        }
    }
}

#[test]
fn distributed_slice_index_returns_a_copy_without_reference_specialization() {
    let source = r#"
        values() -> Vec<usize> {
            let output = Vec::new();
            Vec::push(&mut output, 2);
            Vec::push(&mut output, 3);
            Vec::push(&mut output, 5);
            output
        }
        slice_index_value() -> usize {
            let source = values();
            Slice::index(Vec::as_slice(&source), 2)
        }
        main() -> () { () }
    "#;
    let phases = compile_source_to_phases_with_options(
        "slice-index.glorious",
        source,
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let function = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "slice_index_value")
        .unwrap() as u32;
    let verified = verify(phases.artifact).unwrap();
    assert_eq!(Vm::new(verified).run(function, vec![]).unwrap(), Value::U64(5));
}
