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
fn copy_and_generic_moves_are_not_rewritten() {
    let copy_source = r#"
        forward(value: i64) -> i64 { move value }
        main() -> { () }
    "#;
    let copy = compile_source_to_phases("copy-move.glorious", copy_source).unwrap();
    assert!(
        copy.diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code.as_deref() != Some(REDUNDANT_MOVE_CODE))
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
