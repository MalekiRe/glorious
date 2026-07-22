use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases,
    compile_source_to_phases_with_options, diagnostic::Severity,
};

fn warnings(source: &str) -> Vec<grandiose::diagnostic::Diagnostic> {
    compile_source_to_phases("pattern-reachability.glorious", source)
        .unwrap_or_else(|diagnostics| panic!("program did not compile: {diagnostics:#?}"))
        .diagnostics
        .into_iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Warning)
        .collect()
}

#[test]
fn irrefutable_row_makes_later_handler_rows_unreachable() {
    let source = r#"
        enum State { Hot, Cold }
        effect Pick { pick(value: State) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(State::Hot) {
                Pick::pick(_) => 42,
                Pick::pick(State::Hot) => 0
            }
        }
        main() -> { selected(); () }
    "#;
    let warnings = warnings(source);
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    let warning = &warnings[0];
    assert_eq!(warning.code.as_deref(), Some("G1PW001"));
    assert_eq!(warning.title, "unreachable handler pattern");
    let span = warning.span.expect("warning has a source span");
    assert!(source[span.range()].starts_with("Pick::pick(State::Hot)"));
}

#[test]
fn earlier_rows_can_jointly_cover_a_later_enum_row() {
    let source = r#"
        enum State { Hot, Cold }
        effect Pick { pick(value: State) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(State::Hot) {
                Pick::pick(State::Hot) => 40,
                Pick::pick(State::Cold) => 2,
                Pick::pick(_) => 0
            }
        }
        main() -> { selected(); () }
    "#;
    let warnings = warnings(source);
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    let span = warnings[0].span.unwrap();
    assert!(source[span.range()].starts_with("Pick::pick(_)"));
}

#[test]
fn nested_product_columns_are_checked_as_a_matrix() {
    let source = r#"
        enum State { Hot, Cold }
        effect Pick { pick(left: State, right: State) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(State::Hot, State::Cold) {
                Pick::pick(State::Hot, _) => 42,
                Pick::pick(State::Cold, State::Hot) => 1,
                Pick::pick(State::Cold, State::Cold) => 2,
                Pick::pick(State::Cold, _) => 0
            }
        }
        main() -> { selected(); () }
    "#;
    let warnings = warnings(source);
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    let span = warnings[0].span.unwrap();
    assert!(source[span.range()].starts_with("Pick::pick(State::Cold, _)"));
}

#[test]
fn scalar_literals_only_cover_the_same_exact_value() {
    let source = r#"
        effect Pick { pick(value: u128) -> ! }
        selected() -> u128 {
            handle perform Pick::pick(18446744073709551616) {
                Pick::pick(18446744073709551616) => 42,
                Pick::pick(18446744073709551617) => 1,
                Pick::pick(18446744073709551616) => 0,
                Pick::pick(_) => 2
            }
        }
        main() -> { selected(); () }
    "#;
    let warnings = warnings(source);
    assert_eq!(warnings.len(), 1, "{warnings:#?}");
    let span = warnings[0].span.unwrap();
    assert!(source[span.range()].starts_with("Pick::pick(18446744073709551616)"));
}

#[test]
fn rows_for_distinct_operations_do_not_cover_each_other() {
    let source = r#"
        effect Pick {
            first(value: i64) -> !
            second(value: i64) -> !
        }
        selected() -> i64 {
            handle perform Pick::first(1) {
                Pick::first(1) => 40,
                Pick::first(_) => 41,
                Pick::second(1) => 2,
                Pick::second(_) => 3
            }
        }
        main() -> { selected(); () }
    "#;
    assert!(warnings(source).is_empty());
}

#[test]
fn warning_identity_and_span_are_stable_at_every_optimization_level() {
    let source = r#"
        effect Pick { pick(value: i64) -> ! }
        selected() -> i64 {
            handle perform Pick::pick(7) {
                Pick::pick(7) => 42,
                Pick::pick(7) => 0,
                Pick::pick(_) => 1
            }
        }
        main() -> { selected(); () }
    "#;
    let expected_start = source.rfind("Pick::pick(7) => 0").unwrap();
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "stable-pattern-warning.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|diagnostics| panic!("{optimization_level:?}: {diagnostics:#?}"));
        let [warning] = phases.diagnostics.as_slice() else {
            panic!("{optimization_level:?}: {:#?}", phases.diagnostics);
        };
        assert_eq!(warning.code.as_deref(), Some("G1PW001"));
        assert_eq!(warning.span.unwrap().start, expected_start);
    }
}
