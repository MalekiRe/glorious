use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Value, Vm, verify};

fn run(source_name: &str, source: &str, expected: i64) -> String {
    let phases = compile_source_to_phases(source_name, source).unwrap();
    let mir = phases.mir.canonical_text();
    let selected = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(expected)
    );
    mir
}

const PRELUDE: &str = r#"
    struct Resource { marker: i64 }
    impl Use<[0,1]> for Resource {}
    impl Drop for Resource { drop(&mut self) -> { self.marker; () } }
    consume(value: Resource) -> { () }
"#;

#[test]
fn multiple_projected_moves_cross_mandatory_and_optional_captures() {
    let mandatory = format!(
        r#"
        {PRELUDE}
        struct Values {{ first: Resource, second: Resource, retained: i64 }}
        effect Ask {{ [1,1] ask() -> i64 }}
        selected() -> i64 {{
            handle {{
                let values = Values {{ first: Resource {{ marker: 1 }}, second: Resource {{ marker: 2 }}, retained: 40 }};
                let first = values.first;
                let second = values.second;
                consume(first);
                consume(second);
                let answer = perform Ask::ask();
                values.retained + answer
            }} {{
                Ask::ask() with continuation => resume(continuation, 2)
            }}
        }}
        main() -> {{ () }}
        "#
    );
    let mir = run("multiple-mandatory-residual.gr", &mandatory, 42);
    assert!(mir.contains("initialized_fields: [false, false, true]"));

    let optional = format!(
        r#"
        {PRELUDE}
        effect Stop {{ [0,1] stop() -> i64 }}
        selected() -> i64 {{
            handle {{
                let values = (Resource {{ marker: 1 }}, Resource {{ marker: 2 }}, 40);
                let first = values.0;
                let second = values.1;
                consume(first);
                consume(second);
                let answer = perform Stop::stop();
                values.2 + answer
            }} {{
                Stop::stop() with continuation => {{ cancel(continuation); 42 }}
            }}
        }}
        main() -> {{ () }}
        "#
    );
    let mir = run("multiple-optional-residual.gr", &optional, 42);
    assert!(mir.contains("initialized_fields: [false, false, true]"));
}

#[test]
fn multiple_and_nested_residual_owners_cross_multishot_capture() {
    let multiple = format!(
        r#"
        {PRELUDE}
        effect Choose {{ [2,2] choose() -> i64 }}
        selected() -> i64 {{
            handle {{
                let values = (Resource {{ marker: 1 }}, Resource {{ marker: 2 }}, 40);
                let first = values.0;
                let second = values.1;
                consume(first);
                consume(second);
                let choice = perform Choose::choose();
                values.2 + choice
            }} {{
                Choose::choose() with continuation => {{
                    let first = resume(continuation, 1);
                    let second = resume(move continuation, 2);
                    first + second
                }}
            }}
        }}
        main() -> {{ () }}
        "#
    );
    let mir = run("multiple-multishot-residual.gr", &multiple, 83);
    assert!(mir.contains("initialized_fields: [false, false, true]"));

    let nested = format!(
        r#"
        {PRELUDE}
        effect Choose {{ [2,2] choose() -> i64 }}
        selected() -> i64 {{
            handle {{
                let outer = ((Resource {{ marker: 1 }}, 20), 20);
                let inner = outer.0;
                let resource = inner.0;
                consume(resource);
                let choice = perform Choose::choose();
                inner.1 + outer.1 + choice
            }} {{
                Choose::choose() with continuation => {{
                    let first = resume(continuation, 1);
                    let second = resume(move continuation, 2);
                    first + second
                }}
            }}
        }}
        main() -> {{ () }}
        "#
    );
    let mir = run("nested-multishot-residual.gr", &nested, 83);
    assert!(mir.matches("initialized_fields: [false, true]").count() >= 2);
}

#[test]
fn multiple_moves_remain_disjoint_and_custom_drop_safe() {
    let repeated = format!(
        r#"
        {PRELUDE}
        bad() -> {{
            let values = (Resource {{ marker: 1 }}, Resource {{ marker: 2 }});
            let first = values.0;
            let repeated = values.0;
            consume(first);
            consume(repeated)
        }}
        main() -> {{ () }}
        "#
    );
    let diagnostics = compile_source_to_bytecode("repeated-projected-move.gr", &repeated)
        .expect_err("moving the same child twice was accepted");
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("field `0` of local `values` was already moved")
    }));

    let custom_parent = r#"
        struct Owner { value: &mut i64 }
        struct Pair { left: Owner, marker: i64 }
        impl Drop for Pair { drop(&mut self) -> { self.marker; () } }
        bad(value: Pair) -> Owner { value.left }
        main() -> { () }
    "#;
    let diagnostics = compile_source_to_bytecode("custom-drop-projected-move.gr", custom_parent)
        .expect_err("a custom-Drop parent was partially moved");
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("because it has a custom Drop hook")
    }));
}
