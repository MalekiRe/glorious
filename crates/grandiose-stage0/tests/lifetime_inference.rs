use std::collections::BTreeMap;

mod support;

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
        sources: vec![
            SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(),
                format!("use std::*;\n{source}").as_bytes()),
            SourceInput::new(PackageKey("std@0.1.0".into()), LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice()),
        ],
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
fn inferred_nominal_view_joins_accept_shorter_borrows_and_static_fallbacks() {
    for selection in [
        "handle flag { true => input, false => empty }",
        "handle flag { false => empty, true => input }",
        "handle flag { false => static_view(), true => input }",
        "(handle flag { false => (empty,), true => (input,) }).0",
        "(handle flag { false => Wrapped { view: empty }, true => Wrapped { view: input } }).view",
        "@selected: Slice<'_,u8> { handle flag { false => @selected(empty), true => @selected(input) } }",
        "handle { handle flag { true => input, false => { Pick::pick(); input } } } { Pick::pick() with _ => empty }",
        "handle Slice::slice(input, Range { start: 0, end: 1 }) { Result::Ok(view) => view, Result::Err(_) => b\"\" }",
    ] {
        let source = format!("struct Wrapped<T> {{ view: T }} effect Pick {{ [0,1] pick() -> (); }} fn static_view() -> Slice<'static,u8> {{ b\"\" }} fn choose<'a>(input: Slice<'a,u8>, flag: Bool) -> usize {{ let empty: Slice<'static,u8> = b\"\"; let selected = {selection}; Slice::len(&selected) }} pub fn main() -> i64 {{ as<i64>(choose(b\"*\", true) + choose(b\"\", false)) + 41 }}");
        let artifact = StageZeroCompiler::new().compile(request(&source))
            .unwrap_or_else(|error| panic!("{source}: {error:#?}")).artifact.unwrap();
        let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
        // SAFETY: the only native view is a checked one-byte static input.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        assert_eq!(unsafe { decoded.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
        let ir = StageZeroCompiler::new().compile_llvm(request(&source), LlvmTarget::host().unwrap()).unwrap();
        for optimization in [0, 2] {
            let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
            // SAFETY: the native variant executes the same checked static views.
            assert_eq!(unsafe { native.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
        }
    }
}

#[test]
fn inferred_nominal_view_joins_cannot_promote_a_borrow_to_static() {
    for selection in [
        "handle flag { true => input, false => empty }",
        "handle flag { false => empty, true => input }",
        "@selected: Slice<'_,u8> { handle flag { false => @selected(empty), true => @selected(input) } }",
    ] {
        rejects_lifetime(&format!("fn invalid<'a>(input: Slice<'a,u8>, flag: Bool) -> Slice<'static,u8> {{ let empty: Slice<'static,u8> = b\"\"; let selected = {selection}; selected }} pub fn main() -> i64 {{ 42 }}"));
    }
}

#[test]
fn inferred_byte_literal_view_joins_do_not_depend_on_branch_order() {
    for selection in [
        "handle flag { true => input, false => b\"\" }",
        "handle flag { false => b\"\", true => input }",
    ] {
        let source = format!("fn choose<'a>(input: Slice<'a,u8>, flag: Bool) -> usize {{ let selected = {selection}; Slice::len(&selected) }} pub fn main() -> i64 {{ as<i64>(choose(b\"*\", true)) + 41 }}");
        let artifact = StageZeroCompiler::new().compile(request(&source))
            .unwrap_or_else(|error| panic!("{source}: {error:#?}")).artifact.unwrap();
        // SAFETY: this program reads only compiler-emitted static octets.
        assert_eq!(unsafe { artifact.run_i64_with_unsafe(Default::default()) }.unwrap(), 42);
    }
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
            "{PREFIX} pub fn main() -> i64 {{ let mut count = 0; {{ {owners} count = 41; () }}; count }}"
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
        "{PREFIX} pub fn main() -> i64 {{ let mut count = 0; {{
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
        "{PREFIX} pub fn main() -> i64 {{ let mut count = 0; {{
        let mut owner = Probe {{ target: &mut count }}; owner = owner; count = 41; () }}; count }}"
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
    // Check-mode service requests also validate executable MIR. Use the
    // frontend boundary explicitly for this frontend-only NLL assertion.
    let plain = format!("{PREFIX} struct Plain<'a> {{ target: &'a mut i64 }}
        pub fn main() -> i64 {{ let mut count = 0; let owner = Plain {{ target: &mut count }}; count = 42; count }}");
    let (_, core, signatures) = support::frontend("plain-reference-nll@0.1.0", &plain, "main");
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = grandiose_stage0::PlaceFlow::analyze_with_interface(&core, &signatures);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn later_call_context_does_not_put_callee_regions_in_an_earlier_generic_instance() {
    assert_eq!(run(r#"
        struct Marker<'a, 'b> {}
        fn carry<T>(value: T) -> T { value }
        fn inspect<'a, 'b>(value: &Marker<'a, 'b>) -> i64 { 42 }
        pub fn main() -> i64 {
            let marker = carry(Marker {});
            inspect(&marker)
        }
    "#), 42);
}

#[test]
fn call_context_shares_an_open_region_across_unconstrained_operands() {
    assert_eq!(run(r#"
        struct Marker<'a> {}
        fn carry<T>(value: T) -> T { value }
        fn inspect<'a>(left: &Marker<'a>, right: &Marker<'a>) -> i64 { 42 }
        pub fn main() -> i64 {
            let left = carry(Marker {});
            let right = carry(Marker {});
            inspect(&left, &right)
        }
    "#), 42);
}

#[test]
fn call_context_preserves_caller_regions_nested_in_generic_type_arguments() {
    assert_eq!(run(r#"
        struct Probe<'a> { target: &'a i64 }
        fn carry<T>(value: T) -> T { value }
        fn inspect<'a, 'b>(value: &Probe<'a>, other: &'b i64) -> i64 { *value.target }
        fn forward<'a, 'b>(value: &'a i64, other: &'b i64) -> i64 {
            let probe = carry(Probe { target: value });
            inspect(&probe, other)
        }
        pub fn main() -> i64 { let value = 42; let other = 7; forward(&value, &other) }
    "#), 42);
}

#[test]
fn call_context_opens_a_higher_ranked_callback_region_into_a_caller_hole() {
    assert_eq!(run(r#"
        struct Marker<'a> {}
        fn carry<T>(value: T) -> T { value }
        fn inspect<'a>(value: Marker<'a>) -> i64 { 42 }
        fn invoke(callback: for<'a> (Marker<'a>) -> i64) -> i64 {
            let marker = carry(Marker {});
            callback(marker)
        }
        pub fn main() -> i64 { invoke(inspect) }
    "#), 42);
}

#[test]
fn covariant_carriers_can_share_a_shorter_region_without_equating_caller_regions() {
    // Preserve the former negative fixture verbatim. Section 9.2 derives
    // Probe's covariance from its shared reference field: selecting a fresh
    // common shorter region does not prove 'a:'b or 'b:'a.
    assert_eq!(run(r#"
        struct Probe<'a> { target: &'a i64 }
        fn need_same<'a>(left: Probe<'a>, right: Probe<'a>) -> i64 { 42 }
        fn invalid<'a, 'b>(left: &'a i64, right: &'b i64) -> i64 {
            need_same(Probe { target: left }, Probe { target: right })
        }
        pub fn main() -> i64 { 42 }
    "#), 42);
    assert_eq!(run(r#"
        struct Probe<'a> { target: &'a i64 }
        fn add<'a>(left: Probe<'a>, right: Probe<'a>) -> i64 { *left.target + *right.target }
        fn inner<'a>(incoming: &'a i64) -> i64 {
            let local = 2; add(Probe { target: incoming }, Probe { target: &local })
        }
        pub fn main() -> i64 { let incoming = 40; inner(&incoming) }
    "#), 42);
}

#[test]
fn call_context_cannot_lengthen_or_merge_rigid_caller_regions() {
    for source in [r#"
        struct Probe<'a> { target: &'a i64 }
        fn carry<T>(value: T) -> T { value }
        fn need_static(value: Probe<'static>) -> i64 { 42 }
        fn invalid(value: &i64) -> i64 {
            let probe = carry(Probe { target: value });
            need_static(probe)
        }
        pub fn main() -> i64 { 42 }
    "#, r#"
        struct Probe<'a> { target: &'a i64 }
        fn need_same<'a>(left: Probe<'a>, right: Probe<'a>) -> i64 { 42 }
        fn invalid<'a, 'b>(left: &'a i64, right: &'b i64) -> &'b i64 {
            need_same(Probe { target: left }, Probe { target: right });
            left
        }
        pub fn main() -> i64 { 42 }
    "#, r#"
        struct Hold<'a, 'b> { slot: &'a mut &'b i64 }
        fn carry<T>(value: T) -> T { value }
        fn need_static<'a>(value: Hold<'a, 'static>) -> i64 { 42 }
        fn invalid<'a, 'b>(slot: &'a mut &'b i64) -> i64 {
            let holder = carry(Hold { slot: slot });
            need_static(holder)
        }
        pub fn main() -> i64 { 42 }
    "#, r#"
        fn static_only(value: &'static i64) -> i64 { 42 }
        fn invoke(callback: for<'a> (&'a i64) -> i64) -> i64 { 42 }
        pub fn main() -> i64 { invoke(static_only) }
    "#] { rejects_lifetime(source); }
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
            let mut left = 1;
            let mut right = 7;
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
            let mut left = 1;
            let mut right = 7;
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
            let mut whole = Outer { field: 42 };
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
