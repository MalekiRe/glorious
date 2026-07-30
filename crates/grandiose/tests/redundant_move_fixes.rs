use grandiose::{compile_source_to_phases, diagnostic::Severity};

const REDUNDANT_MOVE_CODE: &str = "G1RM001";

#[test]
fn monomorphic_noncopy_move_has_an_exact_machine_fix() {
    let source = r#"
        forward(value: Vec<i64>) -> Vec<i64> { move value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("redundant-move.glorious", source).unwrap();
    let diagnostic = phases
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .expect("the redundant non-Copy move should be diagnosed");
    assert_eq!(diagnostic.severity, Severity::Advice);
    assert_eq!(diagnostic.source_name, "redundant-move.glorious");
    let fix = diagnostic
        .fix
        .as_ref()
        .expect("the advice should be machine-applicable");
    assert_eq!(&source[fix.span.range()], "move");
    assert_eq!(fix.replacement, "");

    let mut fixed = source.to_owned();
    fixed.replace_range(fix.span.range(), &fix.replacement);
    let fixed_phases = compile_source_to_phases("redundant-move.glorious", &fixed).unwrap();
    assert!(
        fixed_phases
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some(REDUNDANT_MOVE_CODE))
    );
    let lowered = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap();
    let fixed_lowered = fixed_phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap();
    assert_eq!(lowered.blocks.len(), fixed_lowered.blocks.len());
    for (block, fixed_block) in lowered.blocks.iter().zip(&fixed_lowered.blocks) {
        assert_eq!(
            block
                .statements
                .iter()
                .map(|statement| &statement.kind)
                .collect::<Vec<_>>(),
            fixed_block
                .statements
                .iter()
                .map(|statement| &statement.kind)
                .collect::<Vec<_>>()
        );
        assert_eq!(block.terminator, fixed_block.terminator);
    }
}

#[test]
fn final_copy_moves_are_rewritten_but_generic_source_is_not() {
    let copy_source = r#"
        forward(value: i64) -> i64 { move value }
        main() -> { () }
    "#;
    let copy = compile_source_to_phases("copy-move.glorious", copy_source).unwrap();
    assert!(
        copy.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
    );

    // A closed program may currently instantiate this only with Vec, but a
    // future caller can instantiate it with a Copy type. Source fixes for
    // generic definitions therefore require a universal non-Copy bound.
    let generic_source = r#"
        forward<T>(value: T) -> T { move value }
        run() -> Vec<i64> { forward(Vec::new()) }
        main() -> { () }
    "#;
    let generic = compile_source_to_phases("generic-move.glorious", generic_source).unwrap();
    assert!(
        generic
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some(REDUNDANT_MOVE_CODE))
    );
}

#[test]
fn bare_final_copy_use_lowers_as_transfer() {
    let source = r#"
        forward(value: i64) -> i64 { value }
        struct Relevant { value: i64 }
        impl Use<[1,infinity]> for Relevant {}
        duplicate_then_transfer(value: Relevant) -> (Relevant, Relevant) { (value, value) }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("final-use-transfer.glorious", source).unwrap();
    let forward = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "forward")
        .unwrap();
    assert!(matches!(
        forward.blocks[0].terminator,
        grandiose::compiler_mir::Terminator::Return {
            value: Some(grandiose::compiler_mir::Operand {
                register: 1,
                mode: grandiose::compiler_mir::UseMode::Move,
            })
        }
    ));
    assert!(
        !forward
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| matches!(
                statement.kind,
                grandiose::compiler_mir::InstructionKind::Copy { .. }
            ))
    );

    let duplicate = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "duplicate_then_transfer")
        .unwrap();
    assert!(
        duplicate
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| matches!(
                statement.kind,
                grandiose::compiler_mir::InstructionKind::Copy { .. }
            ))
    );
    assert!(
        duplicate
            .blocks
            .iter()
            .flat_map(|block| &block.statements)
            .any(|statement| matches!(
                statement.kind,
                grandiose::compiler_mir::InstructionKind::Move { .. }
            ))
    );
}

#[test]
fn locals_introduced_by_nested_blocks_infer_their_final_transfer() {
    let source = r#"
        answer() -> i64 {
            {
                let value = 42;
                move value
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-local-final-use.glorious", source).unwrap();
    let fix = phases
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .and_then(|diagnostic| diagnostic.fix.as_ref())
        .expect("a nested block's own final local use has an exact fix");
    assert_eq!(&source[fix.span.range()], "move");
    assert!(fix.replacement.is_empty());
}

#[test]
fn outer_locals_transfer_only_when_a_nested_use_is_final() {
    let source = r#"
        nested_final(value: i64) -> i64 {
            { move value }
        }
        nested_then_later(value: i64) -> i64 {
            { value; };
            move value
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("nested-outer-final-use.glorious", source).unwrap();
    let fixes = phases
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .collect::<Vec<_>>();
    assert_eq!(fixes.len(), 2);
    assert!(fixes.iter().all(|fix| &source[fix.span.range()] == "move"));
}

#[test]
fn mutually_exclusive_if_arms_each_infer_their_final_transfer() {
    let source = r#"
        choose(condition: Bool, value: i64) -> i64 {
            if(condition) { move value } else { move value }
        }
        branch_then_later(condition: Bool, value: i64) -> i64 {
            if(condition) { value } else { value };
            move value
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("branch-final-use.glorious", source).unwrap();
    let fixes = phases
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .collect::<Vec<_>>();
    assert_eq!(fixes.len(), 3);
    assert!(fixes.iter().all(|fix| &source[fix.span.range()] == "move"));
}

#[test]
fn compiler_owned_try_wrappers_preserve_final_use_transfer() {
    let source = r#"
        struct Relevant { value: i64 }
        impl Use<[0,infinity]> for Relevant {}

        forward(
            status: Result<(), i64>,
            value: Relevant
        ) -> Result<Relevant, i64> {
            try(status, @forward);
            Result::Ok(value)
        }
        combine(
            status: Result<(), i64>,
            value: Relevant
        ) -> Result<((), Relevant), i64> {
            Result::Ok((try(status, @combine), move value))
        }
        observe(
            value: Relevant,
            status: Result<(), i64>
        ) -> Result<(), i64> {
            value;
            status
        }
        preserve_after_try_argument(
            status: Result<(), i64>,
            value: Relevant
        ) -> Result<Relevant, i64> {
            try(observe(value, status), @preserve_after_try_argument);
            Result::Ok(value)
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("try-final-use-transfer.glorious", source).unwrap();
    let diagnostic = phases
        .diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .expect("the final sibling after try should receive redundant-move advice");
    let fix = diagnostic
        .fix
        .as_ref()
        .expect("the advice should be exactly machine-applicable");
    assert_eq!(&source[fix.span.range()], "move");
    assert_eq!(fix.replacement, "");
    for name in ["forward", "combine"] {
        let function = phases
            .mir
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap();
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| &block.statements)
                .any(|statement| matches!(
                    statement.kind,
                    grandiose::compiler_mir::InstructionKind::Move {
                        src: grandiose::compiler_mir::Operand {
                            register: 1,
                            mode: grandiose::compiler_mir::UseMode::Move,
                        },
                        ..
                    }
                )),
            "{name} did not transfer its final status argument:\n{}",
            phases.mir.canonical_text()
        );
        assert!(
            function.blocks.iter().any(|block| matches!(
                block.terminator,
                grandiose::compiler_mir::Terminator::Leave { .. }
            )),
            "{name}:\n{}",
            phases.mir.canonical_text()
        );
    }
}

#[test]
fn completion_match_arms_each_infer_their_final_transfer() {
    let source = r#"
        preserve(value: Bool) -> Bool {
            handle value {
                Result::Ok(_) => move value,
                Result::Err(_) => move value
            }
        }
        preserve_after_match(value: Bool) -> Bool {
            handle value {
                Result::Ok(_) => value,
                Result::Err(_) => value
            };
            move value
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("final-use-control.glorious", source).unwrap();
    let fixes = phases
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code.as_deref() == Some(REDUNDANT_MOVE_CODE))
        .filter_map(|diagnostic| diagnostic.fix.as_ref())
        .collect::<Vec<_>>();
    assert_eq!(
        fixes.len(),
        3,
        "{:?}",
        fixes
            .iter()
            .map(|fix| (fix.span, &source[fix.span.range()]))
            .collect::<Vec<_>>()
    );
}

#[test]
fn pattern_binding_final_use_transfers_within_its_own_arm() {
    let source = r#"
        enum Target {
            Missing,
            Function(u32),
            Variant(u32)
        }
        impl Use<[0,infinity]> for Target {}

        kind(target: Target) -> u32 {
            handle target {
                Target::Missing => 0,
                Target::Function(_) => 1,
                Target::Variant(_) => 2
            }
        }

        select(target: Target) -> u32 {
            handle target {
                Target::Function(shell) => shell,
                remaining => kind(remaining)
            }
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("final-use-pattern-arm.glorious", source).unwrap();
    let kind = phases
        .mir
        .functions
        .iter()
        .position(|function| function.name == "kind")
        .unwrap() as u32;
    let select = phases
        .mir
        .functions
        .iter()
        .find(|function| function.name == "select")
        .unwrap();
    assert!(
        select.blocks.iter().any(|block| matches!(
            &block.terminator,
            grandiose::compiler_mir::Terminator::Call {
                function,
                args,
                ..
            } | grandiose::compiler_mir::Terminator::TailCall {
                function,
                args,
            } if *function == kind
                && matches!(
                    args.as_slice(),
                    [grandiose::compiler_mir::Operand {
                        mode: grandiose::compiler_mir::UseMode::Move,
                        ..
                    }]
                )
        )),
        "{}",
        phases.mir.canonical_text()
    );
}

#[test]
fn nested_block_liveness_does_not_consume_an_outer_local() {
    let source = r#"
        preserve(value: i64) -> i64 {
            { value };
            value
        }
        main() -> { () }
    "#;
    compile_source_to_phases("final-use-nested-block.glorious", source).unwrap();
}

#[test]
fn final_use_inference_respects_live_loans_and_custom_drop() {
    let loan_source = r#"
        preserve(value: i64) -> i64 {
            let borrowed = &value;
            let copied = value;
            *borrowed
        }
        main() -> { () }
    "#;
    compile_source_to_phases("final-use-loan.glorious", loan_source).unwrap();

    let drop_source = r#"
        struct Guard { marker: i64 }
        impl Use<[0,infinity]> for Guard {}
        impl Drop for Guard { drop(&mut self) -> { self.marker; () } }
        forward(value: Guard) -> Guard { move value }
        copy(value: Guard) -> Guard { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("final-use-drop.glorious", drop_source).unwrap();
    assert!(
        phases
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some(REDUNDANT_MOVE_CODE))
    );
}

#[test]
fn lazy_if_joins_whole_transfer_with_exhaustive_field_transfers() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        consume_pair_for_join(value: Pair) -> i64 { value.left + value.right }
        select(condition: Bool, value: Pair) -> i64 {
            if(condition) {
                consume_pair_for_join(move value)
            } else {
                let left = move value.left;
                let right = move value.right;
                left + right
            }
        }
        main() -> { select(true, Pair { left: 20, right: 22 }); () }
    "#;
    compile_source_to_phases("lazy-if-exhaustive-fields.glorious", source).unwrap();
}

#[test]
fn lazy_if_joins_whole_transfer_with_droppable_partial_residual() {
    let source = r#"
        struct State { selected: i64, cursor: usize, finished: Bool }
        consume_state_for_join(value: State) -> i64 { value.selected }
        select_partial(condition: Bool, value: State) -> i64 {
            if(condition) {
                consume_state_for_join(move value)
            } else {
                move value.selected
            }
        }
        main() -> {
            select_partial(
                false,
                State { selected: 42, cursor: 0, finished: false }
            );
            ()
        }
    "#;
    compile_source_to_phases("lazy-if-partial-residual.glorious", source).unwrap();
}
