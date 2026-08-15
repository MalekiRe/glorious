use super::*;

#[test]
fn semantic_typed_core_excludes_builtin_control_and_arithmetic_nodes() {
    let source = fs::read_to_string(crate_path("src/core.rs")).unwrap();
    let start = source
        .find("pub enum CoreKind")
        .expect("CoreKind declaration");
    let end = source[start..]
        .find("impl CoreKind")
        .map(|offset| start + offset)
        .expect("CoreKind implementation");
    let variants = source[start..end]
        .lines()
        .filter_map(|line| {
            let rest = line.strip_prefix("    ")?;
            if rest.starts_with(' ') || rest.starts_with('/') || rest.starts_with('#') {
                return None;
            }
            let name = rest
                .split(|character: char| {
                    character == '('
                        || character == '{'
                        || character == ','
                        || character.is_whitespace()
                })
                .next()?;
            (!name.is_empty()).then_some(name.to_owned())
        })
        .collect::<BTreeSet<_>>();
    let forbidden = [
        "If", "Else", "Match", "Loop", "For", "Break", "Continue", "Return", "Yield",
        "Await", "Fail", "Add", "Compare", "And", "Or", "Binary", "Unary",
    ];
    let present = forbidden
        .into_iter()
        .filter(|name| variants.contains(*name))
        .collect::<Vec<_>>();
    assert!(
        present.is_empty(),
        "Typed Core still contains compiler-known control/arithmetic nodes: \
         {present:?}; variants={variants:?}"
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum EvalResult {
    Value(i64),
    Leave(LabelBrand, i64),
}

fn evaluate_label_core(body: &TypedBody, id: CoreId) -> EvalResult {
    match &body.expression(id).kind {
        CoreKind::Literal(value) => EvalResult::Value(
            value
                .parse::<i64>()
                .unwrap_or_else(|error| panic!("non-i64 literal {value:?}: {error}")),
        ),
        CoreKind::Block(expressions) => {
            let mut result = EvalResult::Value(0);
            for expression in expressions {
                result = evaluate_label_core(body, *expression);
                if matches!(result, EvalResult::Leave(_, _)) {
                    break;
                }
            }
            result
        }
        CoreKind::Label { brand, body: inner } => match evaluate_label_core(body, *inner) {
            EvalResult::Leave(target, value) if target == *brand => EvalResult::Value(value),
            other => other,
        },
        CoreKind::Transfer { brand, value } => match evaluate_label_core(body, *value) {
            EvalResult::Value(value) => EvalResult::Leave(*brand, value),
            leave @ EvalResult::Leave(_, _) => leave,
        },
        other => panic!("label differential evaluator reached unsupported Core: {other:#?}"),
    }
}

#[test]
fn semantic_core_and_verified_vm_agree_on_label_execution() {
    let source = "pub fn main() -> i64 { @done: i64 { @done(42); 0 } }";
    let core = core_for("semantic-core-vm-differential@0.1.0", source);
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let EvalResult::Value(core_value) = evaluate_label_core(&core, core.root) else {
        panic!("the function body leaked an unhandled label transfer")
    };
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    let vm_value = outcome.artifact.unwrap().run_i64().unwrap();
    assert_eq!(core_value, 42);
    assert_eq!(vm_value, core_value);
}

#[test]
fn semantic_brand_escape_diagnostics_use_source_terms() {
    let fixtures = [
        (
            concat!(
                "pub fn main() -> i64 { @done: i64 { ",
                "let delayed = (value: i64) -> i64 { @done(value) }; 0 } }",
            ),
            &["done", "label"][..],
        ),
        (
            concat!(
                "pub fn main() -> i64 { let captured = 42; ",
                "let once = () -> i64 { move captured }; once(); once() }",
            ),
            &["captured", "once", "callable", "closure", "use"][..],
        ),
    ];
    for (source, source_terms) in fixtures {
        let diagnostics = rejection(source);
        let source_diagnostic = diagnostics
            .iter()
            .find(|diagnostic| diagnostic.class == DiagnosticClass::Source)
            .unwrap_or_else(|| panic!("missing source diagnostic: {diagnostics:#?}"));
        let text = published_diagnostic_text(source_diagnostic);
        let lower = text.to_ascii_lowercase();
        assert!(
            source_terms.iter().any(|term| lower.contains(term)),
            "diagnostic did not explain the source label/environment: {diagnostics:#?}"
        );
        for internal in [
            "LabelBrand",
            "EnvironmentBrand",
            "CallableId",
            "DefKey",
            "Digest",
            "owner:",
        ] {
            assert!(
                !text.contains(internal),
                "diagnostic exposed internal identity {internal}: {diagnostics:#?}"
            );
        }
    }
}

#[test]
fn semantic_one_shot_resumptions_cannot_resume_twice() {
    let source = r#"
        effect Ask { [1, 1] ask() -> i64; }
        pub main() -> i64 {
            handle Ask::ask() {
                Ask::ask() with k => k(20) + k(22)
            }
        }
    "#;
    assert_semantic_rejection(
        source,
        "one-shot resumption cannot be resumed twice",
        &[&["resumption", "continuation"], &["quantity", "use", "twice", "upper"]],
    );
}

#[test]
fn semantic_multishot_resumptions_reject_unique_and_label_captures() {
    let unique = r#"
        effect Ask { [2, 2] ask() -> i64; }
        pub main() -> i64 {
            let value = 0;
            let reference = &mut value;
            handle {
                let answer = Ask::ask();
                *reference = answer;
                *reference
            } {
                Ask::ask() with k => k(20) + k(22)
            }
        }
    "#;
    assert_semantic_rejection(
        unique,
        "multi-shot resumption cannot capture a unique borrow",
        &[&["unique", "borrow"], &["resumption", "continuation", "replay", "multi-shot"]],
    );

    let label = r#"
        effect Ask { [2, 2] ask() -> i64; }
        pub main() -> i64 {
            @done: i64 {
                handle {
                    let answer = Ask::ask();
                    @done(answer)
                } {
                    Ask::ask() with k => k(20) + k(22)
                }
            }
        }
    "#;
    assert_semantic_rejection(
        label,
        "multi-shot resumption cannot capture an active label",
        &[&["label"], &["resumption", "continuation", "replay", "multi-shot"]],
    );
}
