use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str) -> CompilationRequest {
    let package = PackageKey("constructor-lifetimes@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"constructor-lifetimes")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn run(source: &str) -> i64 {
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    decode_and_verify_program(&outcome.artifact.unwrap().canonical_bytes())
        .unwrap()
        .run_i64()
        .unwrap()
}

fn rejects_lifetime(source: &str) {
    let diagnostics = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap_err()
        .diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "expected a source lifetime rejection, got {diagnostics:#?}"
    );
}

#[test]
fn destructor_owned_loans_remain_live_until_the_owner_is_destroyed() {
    const PREFIX: &str = r#"
        struct Probe<'a> { target: &'a mut i64 }
        impl<'a> Use<[0, 1]> for Probe<'a> {}
        impl<'a> Drop for Probe<'a> { drop(&mut self) -> { *self.target = *self.target + 1; } }
        struct Outer<'a> { nested: Probe<'a> }
    "#;
    for owners in [
        "let owner = Probe { target: &mut count };",
        "let owner = Outer { nested: Probe { target: &mut count } };",
        "let owner = Probe { target: &mut count }; let owner = 0;",
    ] {
        let source = format!(
            "{PREFIX} pub fn main() -> i64 {{ let count = 0; {{ {owners} count = 41; () }}; count }}"
        );
        let diagnostics = StageZeroCompiler::new()
            .compile(request(&source))
            .unwrap_err()
            .diagnostics();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5007"),
            "destructor-owned borrow must prohibit mutation: {diagnostics:#?}"
        );
    }
    let source = format!(
        "{PREFIX} pub fn main() -> i64 {{ let count = 0; {{
        let first = Probe {{ target: &mut count }};
        let second = Probe {{ target: &mut count }}; () }}; count }}"
    );
    let diagnostics = StageZeroCompiler::new()
        .compile(request(&source))
        .unwrap_err()
        .diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5006"),
        "{diagnostics:#?}"
    );
    let source = format!(
        "{PREFIX} pub fn main() -> i64 {{ let count = 0; {{
        let owner = Probe {{ target: &mut count }}; owner = owner; count = 41; () }}; count }}"
    );
    let diagnostics = StageZeroCompiler::new()
        .compile(request(&source))
        .unwrap_err()
        .diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "{diagnostics:#?}"
    );
    // The frontend retains NLL for plain references: only an actual owning
    // destructor adds the implicit scope-exit use. This checks frontend
    // admission, not runtime success: executable MIR still needs explicit
    // loan ending for this same-block storage replacement (documented gap).
    let mut plain = request(&format!("{PREFIX} struct Plain<'a> {{ target: &'a mut i64 }}
        pub fn main() -> i64 {{ let count = 0; let owner = Plain {{ target: &mut count }}; count = 42; count }}"));
    plain.mode = CompilationMode::Check;
    let outcome = StageZeroCompiler::new().compile(plain).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert!(outcome.artifact.is_none());
}

#[test]
fn record_constructor_lifetimes_follow_fields_without_result_context() {
    assert_eq!(
        run(r#"
        struct Probe<'a> { target: &'a i64 }
        struct Outer<'a> { nested: Probe<'a> }
        fn inspect<'a>(value: Probe<'a>) -> i64 {
            let outer = Outer { nested: value };
            *outer.nested.target
        }
        pub fn main() -> i64 { let count = 42; inspect(Probe { target: &count }) }
    "#),
        42
    );
}

#[test]
fn nested_record_constructor_lifetimes_follow_the_declared_result() {
    assert_eq!(
        run(r#"
        struct Probe<'a> { target: &'a i64 }
        struct Outer<'a> { nested: Probe<'a> }
        fn wrap<'a>(value: &'a i64) -> Outer<'a> { Outer { nested: Probe { target: value } } }
        pub fn main() -> i64 { let count = 42; let outer = wrap(&count); *outer.nested.target }
    "#),
        42
    );
}

#[test]
fn separate_constructors_have_independent_lifetime_variables() {
    assert_eq!(
        run(r#"
        struct Probe<'a> { target: &'a i64 }
        fn first<'a, 'b>(left: &'a i64, right: &'b i64) -> &'a i64 {
            let other = Probe { target: right };
            let selected = Probe { target: left };
            selected.target
        }
        pub fn main() -> i64 { let left = 42; let right = 7; *first(&left, &right) }
    "#),
        42
    );
}

#[test]
fn a_lifetime_absent_from_fields_can_be_inferred_from_context() {
    assert_eq!(
        run(r#"
        struct Marker<'a> {}
        fn marker<'a>(value: &'a i64) -> Marker<'a> { Marker {} }
        pub fn main() -> i64 { let count = 41; marker(&count); count + 1 }
    "#),
        42
    );
}

#[test]
fn both_enum_payload_forms_infer_constructor_lifetimes() {
    assert_eq!(
        run(r#"
        enum Choice<'a> { Empty, Tuple(&'a i64), Record { value: &'a i64 } }
        fn tuple<'a>(value: &'a i64) -> Choice<'a> { Choice::Tuple(value) }
        fn record<'a>(value: &'a i64) -> Choice<'a> { Choice::Record { value: value } }
        pub fn main() -> i64 { let count = 41; tuple(&count); record(&count); count + 1 }
    "#),
        42
    );
}

#[test]
fn constructor_inference_cannot_lengthen_a_local_borrow() {
    let source = r#"
        struct Probe<'a> { target: &'a i64 }
        fn invalid<'a>(input: &'a i64) -> Probe<'a> {
            let local = 42;
            Probe { target: &local }
        }
        pub fn main() -> i64 { 42 }
    "#;
    rejects_lifetime(source);
}

#[test]
fn constructor_inference_does_not_rebind_declared_lifetimes() {
    let source = r#"
        struct Same<'a> { left: &'a i64, right: &'a i64 }
        fn invalid<'a, 'b>(left: &'a i64, right: &'b i64) -> Same<'a> {
            Same { left: left, right: right }
        }
        pub fn main() -> i64 { 42 }
    "#;
    rejects_lifetime(source);
}

#[test]
fn constructor_inference_preserves_unique_referent_invariance() {
    let source = r#"
        struct Hold<'a, 'b> { slot: &'a mut &'b i64 }
        fn invalid<'a, 'b>(slot: &'a mut &'b i64) -> Hold<'a, 'static> { Hold { slot: slot } }
        pub fn main() -> i64 { 42 }
    "#;
    rejects_lifetime(source);
}

#[test]
fn multiple_possible_source_loans_compose_through_nested_calls() {
    assert_eq!(
        run(r#"
        fn pick<'a>(left: &'a mut i64, right: &'a mut i64) -> &'a mut i64 { right }
        fn relay<'a>(value: &'a mut i64) -> &'a mut i64 { value }
        pub fn main() -> i64 {
            let left = 1;
            let right = 7;
            let selected = relay(pick(&mut left, &mut right));
            *selected = 42;
            *selected
        }
    "#),
        42
    );
}

#[test]
fn multi_source_reference_carriers_preserve_loans_through_moves_and_reborrows() {
    let source = r#"
        struct Hold<'a> { loan: &'a mut i64 }
        fn pick<'a>(left: &'a mut i64, right: &'a mut i64) -> &'a mut i64 { right }
        pub fn main() -> i64 {
            let left = 1;
            let right = 7;
            let selected = pick(&mut left, &mut right);
            let carrier = Hold { loan: selected };
            let carrier = carrier;
            let child = &mut *carrier.loan;
            *child = 42;
            *child
        }
    "#;
    assert_eq!(run(source), 42);
    for update in ["left = 0", "right = 0", "*carrier.loan = 0"] {
        let invalid = source.replace("*child = 42;", &format!("{update}; *child = 42;"));
        let diagnostics = StageZeroCompiler::new()
            .compile(request(&invalid))
            .unwrap_err()
            .diagnostics();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5007")),
            "lost possible source loan after {update}: {diagnostics:#?}"
        );
    }
}

#[test]
fn a_same_region_result_keeps_differently_shaped_input_loans() {
    let source = r#"
        struct Outer { field: i64 }
        fn project<'a>(whole: &'a Outer, other: &'a i64) -> &'a i64 { &whole.field }
        pub fn main() -> i64 {
            let whole = Outer { field: 42 };
            let other = 0;
            let selected = project(&whole, &other);
            *selected
        }
    "#;
    assert_eq!(run(source), 42);
    let invalid = source.replace("*selected\n", "whole.field = 0; *selected\n");
    let diagnostics = StageZeroCompiler::new()
        .compile(request(&invalid))
        .unwrap_err()
        .diagnostics();
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "{diagnostics:#?}"
    );
}
