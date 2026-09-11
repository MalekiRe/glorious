use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("reference-result-contracts@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"reference-result-contracts")),
        mode: CompilationMode::Build, root_package: package.clone(),
        sources: vec![SourceInput::new(package, LogicalPath::parse("src/main.glorious").unwrap(), source.as_bytes())],
        target: "stage0-vm".into(), semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.into())].into(),
        capability_manifest: vec![], runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new().compile(request(source, optimization))
            .unwrap_or_else(|error| panic!("O{optimization}: {source}\n{:#?}", error.diagnostics())).artifact.unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), 42);
    }
}

const PREFIX: &str = r#"#![no_std]
    struct View<'a,T> { storage: &'a i64 }
    enum Outcome<T> { Ok(T), Err }
    fn get<'a,T>(value: View<'a,T>) -> &'a i64 { value.storage }
    fn pair<'a,T>(value: View<'a,T>) -> Outcome<(View<'a,T>,View<'a,T>)> {
        Outcome::Ok((View { storage: value.storage }, View { storage: value.storage }))
    }
"#;

#[test]
fn associated_nominal_result_fields_use_the_selected_layout() {
    for (declaration, construct, extract) in [
        ("struct Carrier<I> where I: Items { item: <I as Items>::Item }",
            "Carrier { item: item }", "result.item"),
        ("enum Carrier<I> where I: Items { Present(<I as Items>::Item), Absent }",
            "Carrier::Present(item)", "handle result { Carrier::Present(item) => item, Carrier::Absent => 0 }"),
    ] {
        accepts(&format!("#![no_std]
            trait Items {{ type Item; }}
            struct Numbers {{}}
            impl Items for Numbers {{ type Item = i64; }}
            {declaration}
            fn wrap<I>(item: <I as Items>::Item) -> Carrier<I> where I: Items {{ {construct} }}
            pub fn main() -> i64 {{ let result = wrap<Numbers>(42); {extract} }}"));
    }
}

#[test]
fn associated_nominal_result_fields_preserve_borrowed_residents() {
    let prefix = "#![no_std]
        trait Items { type Item; }
        struct Borrowed<'a> {}
        impl<'a> Items for Borrowed<'a> { type Item = &'a i64; }
        struct Carrier<I> where I: Items { item: <I as Items>::Item }
        fn wrap<'a>(item: &'a i64) -> Carrier<Borrowed<'a>> { Carrier { item: item } }
        fn read<'a>(value: Carrier<Borrowed<'a>>) -> i64 { *value.item }";
    for optimization in ["0", "2"] {
        let source = format!("{prefix}
            pub fn main() -> i64 {{ let mut value = 42; let result = wrap(&value); value = 0; read(result) }}");
        let failure = StageZeroCompiler::new().compile(request(&source, optimization))
            .expect_err("normalizing an associated resident must not discard its loan");
        assert!(failure.diagnostics().iter().any(|diagnostic|
            matches!(diagnostic.code, "G5004" | "G5006" | "G5007")), "{:?}", failure.diagnostics());
    }
    accepts(&format!("{prefix}
        pub fn main() -> i64 {{ let value = 42; let result = wrap(&value); read(result) }}"));
}

#[test]
fn associated_nominal_inferred_lifetime_field_dereference() {
    // Keep the direct caller-field composition as an independent acceptance
    // gate: its inferred lifetime must eventually normalize before dereference,
    // not only after a generic helper has supplied a rigid lexical region.
    accepts("#![no_std]
        trait Items { type Item; }
        struct Borrowed<'a> {}
        impl<'a> Items for Borrowed<'a> { type Item = &'a i64; }
        struct Carrier<I> where I: Items { item: <I as Items>::Item }
        fn wrap<'a>(item: &'a i64) -> Carrier<Borrowed<'a>> { Carrier { item: item } }
        pub fn main() -> i64 { let value = 42; let result = wrap(&value); *result.item }");
}

#[test]
fn inferred_associated_references_preserve_unique_access_and_reborrows() {
    let prefix = "#![no_std]
        trait Items { type Item; }
        struct Borrowed<'a> {} impl<'a> Items for Borrowed<'a> { type Item = &'a mut i64; }
        struct Carrier<I> where I: Items { item: <I as Items>::Item }
        fn wrap<'a>(item: &'a mut i64) -> Carrier<Borrowed<'a>> { Carrier { item: item } }";
    for body in [
        "*result.item = 42; *result.item",
        "{ let alias = &mut *result.item; *alias = 42; }; *result.item",
    ] {
        accepts(&format!("{prefix} pub fn main() -> i64 {{ let mut value = 0; let result = wrap(&mut value); {body} }}"));
    }
}

#[test]
fn inferred_associated_references_cannot_invent_write_or_static_authority() {
    let prefix = "#![no_std]
        trait Items { type Item; }
        struct Borrowed<'a> {} impl<'a> Items for Borrowed<'a> { type Item = &'a i64; }
        struct Carrier<I> where I: Items { item: <I as Items>::Item }
        fn wrap<'a>(item: &'a i64) -> Carrier<Borrowed<'a>> { Carrier { item: item } }";
    for body in [
        "*result.item = 0; *result.item",
        "let alias = &mut *result.item; *alias = 0; *result.item",
    ] {
        for optimization in ["0", "2"] {
            let source = format!("{prefix} pub fn main() -> i64 {{ let value = 42; let result = wrap(&value); {body} }}");
            let failure = StageZeroCompiler::new().compile(request(&source, optimization)).expect_err("shared associated references cannot become writable");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4141"), "{:?}", failure.diagnostics());
        }
    }
    for optimization in ["0", "2"] {
        let source = format!("{prefix}
            fn escape() -> &'static i64 {{ let value = 42; let result = wrap(&value); &(*result.item) }}
            pub fn main() -> i64 {{ *escape() }}");
        let failure = StageZeroCompiler::new().compile(request(&source, optimization)).expect_err("opening a parametric query cannot extend a local loan");
        assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5017" | "G4304")), "{:?}", failure.diagnostics());
    }
}

#[test]
fn associated_nominal_callable_fields_keep_their_invocation_obligations() {
    let prefix = "#![no_std]
        trait Items { type Item; }
        struct Functions {} impl Items for Functions { type Item = (i64) -> i64; }
        struct Carrier<I> where I: Items { item: <I as Items>::Item }
        fn identity(value: i64) -> i64 { value }";
    accepts(&format!("{prefix}
        fn apply(value: Carrier<Functions>) -> i64 {{
            let invoke = (argument: i64) -> i64 {{ value.item(argument) }}; invoke(42)
        }}
        pub fn main() -> i64 {{ apply(Carrier {{ item: identity }}) }}"));
    for body in ["0", "let ignored = move value.item; 0"] {
        let source = format!("{prefix}
            fn discard(value: Carrier<Functions>) -> i64 {{ {body} }}
            pub fn main() -> i64 {{ discard(Carrier {{ item: identity }}) }}");
        for optimization in ["0", "2"] {
            let failure = StageZeroCompiler::new().compile(request(&source, optimization))
                .expect_err("an associated callable field retains its minimum invocation count");
            assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5011"), "{:?}", failure.diagnostics());
        }
    }
}

#[test]
fn strict_reference_inputs_keep_their_original_loans_after_handle_replacement() {
    for expression in [
        "keep(reference, { reference = &second; first = 7; })",
        "(reference, { reference = &second; first = 7; }).0",
        "keep({ reference }, { reference = &second; first = 7; })",
        "{ let kept = keep(reference, { reference = &second; }); first = 7; kept }",
        "{ let kept = (reference, { reference = &second; }).0; first = 7; kept }",
    ] {
        let source = format!("#![no_std]
            fn keep<'a>(value:&'a i64, ignored:()) -> &'a i64 {{ value }}
            pub fn main() -> i64 {{
                let mut first = 42; let second = 0; let mut reference = &first;
                let result = {expression}; *result
            }}");
        for optimization in ["0", "2"] {
            let Err(failure) = StageZeroCompiler::new().compile(request(&source, optimization)) else {
                panic!("O{optimization}: replacing the handle must not retire the evaluated input's loan: {source}");
            };
            assert!(failure.diagnostics().iter().any(|diagnostic|
                matches!(diagnostic.code, "G5004" | "G5006" | "G5007")), "{source}\n{:?}", failure.diagnostics());
        }
    }
}

#[test]
fn strict_reference_results_keep_the_selected_referent_after_handle_replacement() {
    for expression in [
        "keep(reference, { reference = &second; })",
        "(reference, { reference = &second; }).0",
        "keep({ reference }, { reference = &second; })",
    ] {
        accepts(&format!("#![no_std]
            fn keep<'a>(value:&'a i64, ignored:()) -> &'a i64 {{ value }}
            pub fn main() -> i64 {{
                let first = 42; let second = 0; let mut reference = &first;
                let result = {expression}; *result
            }}"));
    }
}

#[test]
fn strict_reference_transport_preserves_upstream_reborrow_debt() {
    for (input, parameter) in [("child", "&'a i64"), ("move child", "&'a mut i64")] {
        let borrow = if input == "child" { "&(*parent)" } else { "&mut *parent" };
        let source = format!("#![no_std]
            fn keep<'a>(value:{parameter}, ignored:()) -> {parameter} {{ value }}
            pub fn main() -> i64 {{
                let mut first = 42; let mut second = 0;
                let mut parent = &mut first; let child = {borrow};
                let result = keep({input}, {{ parent = &mut second; }}); *result
            }}");
        for optimization in ["0", "2"] {
            let failure = StageZeroCompiler::new().compile(request(&source, optimization))
                .expect_err("transport cannot discard the upstream unique parent's suspension");
            assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5006" | "G5007")),
                "{source}\n{:?}", failure.diagnostics());
        }
    }
    accepts("#![no_std] fn read(value:&i64, ignored:()) -> i64 { *value }
        pub fn main() -> i64 {
            let mut first = 42; let mut second = 0;
            let mut parent = &mut first; let child = &(*parent);
            let result = read(child, ()); parent = &mut second; *parent = result;
            second
        }");
}

#[test]
fn assignment_inputs_are_retained_before_computed_destination_evaluation() {
    let prefix = "#![no_std] pub fn main() -> i64 {
        let mut first = 42; let second = 0; let mut reference = &first;
        let mut destination = &second;";
    accepts(&format!("{prefix}
        *{{ reference = &second; &mut destination }} = reference;
        *destination
    }}"));
    for mutation in [
        "*{ reference = &second; first = 7; &mut destination } = reference;",
        "*{ reference = &second; &mut destination } = reference; first = 7;",
    ] {
        let source = format!("{prefix} {mutation} *destination }}");
        let failure = StageZeroCompiler::new().compile(request(&source, "0"))
            .expect_err("the assignment consumes its retained RHS, not the replaced source handle");
        assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5006" | "G5007")),
            "{source}\n{:?}", failure.diagnostics());
    }
}

#[test]
fn strict_reference_snapshots_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std]
        fn keep<'a>(value:&'a i64, ignored:()) -> &'a i64 { value }
        pub fn main() -> i64 {
            let first = 42; let second = 22; let replacement = 0;
            let mut a = &first; let mut b = &second;
            let selected = (keep(a, { a = &replacement; }), b, { b = &replacement; });
            *selected.0
        }";
    accepts(source);
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn strict_callable_inputs_retain_their_captured_reference_residents() {
    let source = |mutation: &str| format!("#![no_std]
        fn invoke<F>(task:F, ignored:()) -> i64 where F:Fn<(),Output=i64,Effects={{}}> {{ task() }}
        pub fn main() -> i64 {{
            let mut first = 42; let second = 0; let mut reference = &first;
            let callback = move(reference) {{ *reference }};
            invoke(callback, {{ reference = &second; {mutation} }})
        }}");
    accepts(&source(""));
    let failure = StageZeroCompiler::new().compile(request(&source("first = 7;"), "0"))
        .expect_err("evaluated callable inputs keep their captured backing loans");
    assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5006" | "G5007")),
        "{:?}", failure.diagnostics());
}

#[test]
fn borrowed_unique_receivers_retain_view_authority_during_arguments() {
    let source = |argument: &str| format!("#![no_std]
        fn first(value:i64) -> i64 {{ 42 }} fn second(value:i64) -> i64 {{ 0 }}
        pub fn main() -> i64 {{
            let mut first:(i64)->i64 = first; let mut second:(i64)->i64 = second;
            let mut callback = &mut first;
            callback({argument})
        }}");
    accepts(&source("0"));
    let failure = StageZeroCompiler::new().compile(request(&source("{ callback = &mut second; 0 }"), "0"))
        .expect_err("a borrowed unique view suspends its source carrier until invocation");
    assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5006" | "G5007")),
        "{:?}", failure.diagnostics());
}

#[test]
fn handler_payloads_keep_the_reference_selected_before_argument_replacement() {
    for aggregate in [false, true] {
      for invocation in ["Select<'a>::read", "emit<'a>"] {
        let ty = if aggregate { "(&'a i64,)" } else { "&'a i64" };
        let argument = if aggregate { "(reference,)" } else { "reference" };
        let pattern = if aggregate { "(payload,)" } else { "payload" };
        let source = |mutation: &str| format!("#![no_std]
        effect Select<'a> {{ [1,1] read(value:{ty}, ignored:()) -> i64; }}
        fn emit<'a>(value:{ty}, ignored:()) -> i64 / {{Select<'a>}} {{ Select<'a>::read(value, ignored) }}
        fn choose<'a>(first:&'a mut i64, second:&'a i64) -> i64 {{
            let mut reference = &(*first);
            handle {invocation}({argument}, {{ reference = second; }}) {{
                Select<'a>::read({pattern}, _) with k => {{ {mutation} k(*payload) }}
            }}
        }}
        pub fn main() -> i64 {{ let mut first = 42; let second = 0; choose(&mut first, &second) }}");
        accepts(&source(""));
        let Err(failure) = StageZeroCompiler::new().compile(request(&source("*first = 7;"), "0")) else {
            panic!("{aggregate}, {invocation}: the handler must retain the evaluated operation payload's original loan");
        };
        assert!(failure.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5006" | "G5007")),
            "{aggregate}, {invocation}: {:?}", failure.diagnostics());
      }
    }
}

#[test]
fn deferred_handler_payloads_preserve_and_release_upstream_carrier_debt() {
    let source = |inside: &str, after: &str| format!("#![no_std]
        effect Select<'a> {{ [1,1] read(value:&'a i64, ignored:()) -> i64; }}
        fn choose<'a>(first:&'a mut i64, second:&'a i64, third:&'a mut i64) -> i64 {{
            let mut parent = first; let mut reference = &(*parent);
            let result = handle Select<'a>::read(reference, {{ reference = second; }}) {{
                Select<'a>::read(payload, _) with k => {{ {inside} k(*payload) }}
            }};
            {after} result
        }}
        pub fn main() -> i64 {{ let mut first = 42; let second = 0; let mut third = 0; choose(&mut first, &second, &mut third) }}");
    accepts(&source("", "parent = third;"));
    let Err(failure) = StageZeroCompiler::new().compile(request(&source("parent = third;", ""), "0")) else {
        panic!("a pending payload retains its upstream parent's carrier suspension");
    };
    assert!(failure.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5004"), "{:?}", failure.diagnostics());
}

#[test]
fn acquired_handler_reference_payloads_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std]
        effect Select<'a> { [1,1] read(value:&'a i64, ignored:()) -> i64; }
        fn emit<'a>(value:&'a i64, ignored:()) -> i64 / {Select<'a>} { Select<'a>::read(value, ignored) }
        fn choose<'a>(first:&'a mut i64, second:&'a i64) -> i64 {
            let mut reference = &(*first);
            handle emit<'a>(reference, { reference = second; }) {
                Select<'a>::read(payload, _) with k => k(*payload)
            }
        }
        pub fn main() -> i64 { let mut first = 42; let second = 0; choose(&mut first, &second) }";
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn an_absent_variant_payload_is_not_missing_reference_provenance() {
    accepts(r#"#![no_std]
        enum Maybe<T> { Some(T), None }
        fn select<'a>(fallback: &'a i64, previous: Maybe<&'a i64>) -> &'a i64 {
            handle previous { Maybe::Some(value) => value, Maybe::None => fallback }
        }
        pub fn main() -> i64 { let backing = 42; *select(&backing, Maybe::None) }
    "#);
}

#[test]
fn absent_variant_payloads_survive_aliases_and_aggregate_storage() {
    accepts(r#"#![no_std]
        enum Maybe<T> { Some(T), None }
        struct State<'a> { previous: Maybe<&'a i64> }
        fn select<'a>(fallback: &'a i64, state: State<'a>) -> &'a i64 {
            handle state.previous { Maybe::Some(value) => value, Maybe::None => fallback }
        }
        pub fn main() -> i64 { let backing = 42; let previous: Maybe<&i64> = Maybe::None; let state = State { previous: previous }; *select(&backing, state) }
    "#);
}

#[test]
fn initializer_results_preserve_absent_variant_reference_paths() {
    accepts(r#"#![no_std]
        enum Maybe<T> { Some(T), None(()) }
        pub let absent = Maybe::None(());
        fn select<'a>(fallback: &'a i64, previous: Maybe<&'a i64>) -> &'a i64 {
            handle previous { Maybe::Some(value) => value, Maybe::None(_) => fallback }
        }
        pub fn main() -> i64 { let backing = 42; *select(&backing, absent) }
    "#);
}

#[test]
fn returned_variant_alternatives_keep_present_references_and_empty_payloads() {
    accepts(r#"#![no_std]
        enum Maybe<T> { Some(T), None(()) }
        fn optional<'a>(backing: &'a i64, pick: i64) -> Maybe<&'a i64> {
            handle pick { 0 => Maybe::None(()), _ => Maybe::Some(backing) }
        }
        fn select<'a>(fallback: &'a i64, previous: Maybe<&'a i64>) -> &'a i64 {
            handle previous { Maybe::Some(value) => value, Maybe::None(_) => fallback }
        }
        pub fn main() -> i64 { let backing = 42; let mut pick = 0; pick = 1; *select(&backing, optional(&backing, pick)) }
    "#);
}

#[test]
fn an_empty_variant_cannot_hide_a_present_or_replaced_local_loan() {
    let prefix = r#"#![no_std]
        enum Maybe<T> { Some(T), None(()) }
        struct State<'a> { previous: Maybe<&'a i64> }
        fn select<'a>(fallback: &'a i64, previous: Maybe<&'a i64>) -> &'a i64 {
            handle previous { Maybe::Some(value) => value, Maybe::None(_) => fallback }
        }
        fn state_select<'a>(fallback: &'a i64, state: State<'a>) -> &'a i64 { select(fallback, state.previous) }
    "#;
    for body in [
        "let local = 1; let previous = handle pick { 0 => Maybe::Some(&local), _ => Maybe::None(()) }; select(fallback, previous)",
        "let local = 1; let mut previous: Maybe<&i64> = Maybe::None(()); previous = Maybe::Some(&local); select(fallback, previous)",
        "let local = 1; let mut state: State<'_> = State { previous: Maybe::None(()) }; state.previous = Maybe::Some(&local); state_select(fallback, state)",
    ] {
        let source = format!("{prefix} fn bad<'a>(fallback: &'a i64, pick: i64) -> &'a i64 {{ {body} }} pub fn main() -> i64 {{ let backing = 42; *bad(&backing, 1) }}");
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(&source, optimization)).expect_err("present variant loans must not disappear");
            assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5013" | "G5017")), "{:#?}", error.diagnostics());
        }
    }
}

#[test]
fn initializer_results_cannot_publish_local_reference_payloads() {
    let source = r#"#![no_std]
        enum Maybe<T> { Some(T), None(()) }
        pub let invalid = { let local = 42; Maybe::Some(&local) };
        pub fn main() -> i64 { handle invalid { Maybe::Some(value) => *value, Maybe::None(_) => 0 } }
    "#;
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(source, optimization)).expect_err("an initializer cannot publish its stack loan");
        assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5013" | "G5017")), "{:#?}", error.diagnostics());
    }
}

#[test]
fn helper_stores_revoke_absence_and_retain_the_new_backing_loan() {
    let prefix = r#"#![no_std]
        enum Maybe<T> { Some(T), None(()) }
        struct State<'a> { previous: Maybe<&'a i64> }
        fn set<'a>(state: &mut State<'a>, value: &'a i64) { state.previous = Maybe::Some(value); }
        fn select<'a>(fallback: &'a i64, state: State<'a>) -> &'a i64 {
            handle state.previous { Maybe::Some(value) => value, Maybe::None(_) => fallback }
        }
    "#;
    accepts(&format!("{prefix} pub fn main() -> i64 {{ let first = 0; let second = 42; let mut state: State<'_> = State {{ previous: Maybe::None(()) }}; set(&mut state, &second); *select(&first, state) }}"));
    let source = format!("{prefix} pub fn main() -> i64 {{ let first = 0; let mut second = 42; let mut state: State<'_> = State {{ previous: Maybe::None(()) }}; set(&mut state, &second); second = 43; *select(&first, state) }}");
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(&source, optimization)).expect_err("a helper store revokes an old absence proof");
        assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5007"), "{:#?}", error.diagnostics());
    }
}

#[test]
fn absent_initializer_payloads_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std] enum Maybe<T> { Some(T), None(()) } pub let absent = Maybe::None(()); fn select<'a>(fallback: &'a i64, previous: Maybe<&'a i64>) -> &'a i64 { handle previous { Maybe::Some(value) => value, Maybe::None(_) => fallback } } pub fn main() -> i64 { let backing = 42; *select(&backing, absent) }";
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn generic_result_keeps_known_reference_fields_beside_open_logical_arguments() {
    accepts(&format!(r#"{PREFIX}
        fn select<'a,T>(value: &'a i64) -> &'a i64 {{
            let original = View<'a,T> {{ storage: value }};
            let (left, right) = handle pair(original) {{
                Outcome::Ok(parts) => parts, Outcome::Err => @select(value),
            }};
            get(left)
        }}
        pub fn main() -> i64 {{ let value = 42; *select<'_,i64>(&value) }}
    "#));
}

#[test]
fn generic_result_keeps_each_distinct_input_region() {
    accepts(r#"#![no_std]
        struct View<'a,'b,T> { first: &'a i64, second: &'b i64 }
        fn forward<'a,'b,T>(value: View<'a,'b,T>) -> View<'a,'b,T> { value }
        fn first<'a,'b,T>(value: View<'a,'b,T>) -> &'a i64 { value.first }
        fn select<'a,T>(value: &'a i64) -> &'a i64 {
            let local = 0;
            first(forward(View<'a,'_,T> { first: value, second: &local }))
        }
        pub fn main() -> i64 { let value = 42; *select<'_,i64>(&value) }
    "#);
}

#[test]
fn open_result_arguments_cannot_hide_a_returned_local_reference() {
    let source = format!(r#"{PREFIX}
        fn bad<'a,T>(fallback: &'a i64) -> &'a i64 {{
            let local = 0;
            let original = View<'_,T> {{ storage: &local }};
            let (left, right) = handle pair(original) {{
                Outcome::Ok(parts) => parts, Outcome::Err => @bad(fallback),
            }};
            get(left)
        }}
        pub fn main() -> i64 {{ let value = 42; *bad<'_,i64>(&value) }}
    "#);
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(&source, optimization))
            .expect_err("a partial contract cannot authorize a local reference escape");
        assert!(error.diagnostics().iter().any(|diagnostic|
            matches!(diagnostic.code, "G5013" | "G5017")), "{:#?}", error.diagnostics());
    }
}

#[test]
fn open_physical_residents_cannot_hide_local_loans_beside_known_fields() {
    for field in ["before: T, known: &'a i64", "known: &'a i64, after: T"] {
        let resident = if field.starts_with("before") { "before" } else { "after" };
        let source = format!(r#"#![no_std]
            struct Mixed<'a,T> {{ {field} }}
            fn forward<'a,T>(value: Mixed<'a,T>) -> Mixed<'a,T> {{ value }}
            fn bad<'a>(value: &'a i64) -> Mixed<'a,&'a i64> {{
                let local = 0;
                forward(Mixed {{ known: value, {resident}: &local }})
            }}
            pub fn main() -> i64 {{ let value = 42; let escaped = bad(&value); *escaped.{resident} }}
        "#);
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(&source, optimization))
                .expect_err("a known sibling cannot certify an unknown resident's lifetime");
            assert!(error.diagnostics().iter().any(|diagnostic|
                matches!(diagnostic.code, "G5013" | "G5017")), "{:#?}", error.diagnostics());
        }
    }
}

#[test]
fn generic_result_preserves_a_known_field_after_an_open_physical_resident() {
    accepts(r#"#![no_std]
        struct Mixed<'a,T> { resident: T, known: &'a i64 }
        fn forward<'a,T>(value: Mixed<'a,T>) -> Mixed<'a,T> { value }
        fn get<'a,T>(value: Mixed<'a,T>) -> &'a i64 where T: Use<[0,*]> { value.known }
        fn select<'a,T>(resident: T, value: &'a i64) -> &'a i64 where T: Use<[0,*]> {
            get(forward(Mixed { resident: resident, known: value }))
        }
        pub fn main() -> i64 { let value = 42; *select(0, &value) }
    "#);
}

#[test]
fn partial_generic_results_preserve_distinct_unique_reference_outputs() {
    accepts(r#"#![no_std]
        struct View<'a,T> { storage: &'a mut i64 }
        fn forward<'a,'b,T>(value: (View<'a,T>,View<'b,T>)) -> (View<'a,T>,View<'b,T>) { value }
        fn write<'a,T>(value: View<'a,T>) { *value.storage = 42; }
        fn assign<'a,'b,T>(left: &'a mut i64, right: &'b mut i64) {
            let (first, second) = forward((View<'a,T> { storage: left }, View<'b,T> { storage: right }));
            write(first); write(second);
        }
        pub fn main() -> i64 {
            let mut left = 0; let mut right = 0;
            assign<'_,'_,i64>(&mut left, &mut right);
            right
        }
    "#);
}

const AUTHENTICATED_INPUTS: &str = r#"#![no_std]
    struct Mixed<'a,T> { resident: T, known: &'a i64 }
    fn forward<'a,T>(value: Mixed<'a,T>) -> Mixed<'a,T> { value }
    fn get<'a,T>(value: Mixed<'a,T>) -> &'a i64 where T: Use<[0,*]> { value.known }
    fn select<'a,T>(resident: T, value: &'a i64) -> &'a i64 where T: Use<[0,*]> {
        get(forward(Mixed { resident: resident, known: value }))
    }
"#;

#[test]
fn authenticated_reference_fields_compose_with_captures_replacement_and_short_residents() {
    for body in [
        "fn relay<'a>(value: &'a i64) -> &'a i64 { let local = 0; select(&local, value) } pub fn main() -> i64 { let value = 42; *relay(&value) }",
        "fn capture<'a,T>(value: Mixed<'a,T>) -> () -> &'a i64 where T: Use<[0,*]> { let result = get(forward(value)); move (result) { result } } pub fn main() -> i64 { let value = 42; let task = capture(Mixed { resident: 0, known: &value }); *task() }",
        "pub fn main() -> i64 { let first = 0; let last = 42; let mut value = forward(Mixed { resident: 0, known: &first }); value.known = &last; *get(value) }",
    ] { accepts(&format!("{AUTHENTICATED_INPUTS}\n{body}")); }
}

#[test]
fn authenticated_reference_fields_do_not_erase_local_escape_or_replacement_obligations() {
    for body in [
        "fn bad<'a,T>(resident: T, fallback: &'a i64) -> &'a i64 where T: Use<[0,*]> { let local = 0; select(resident, &local) } pub fn main() -> i64 { let value = 42; *bad(0, &value) }",
        "fn bad<'a,T>(resident: T, fallback: &'a i64) -> () -> &'a i64 where T: Use<[0,*]> { let local = 0; let result = select(resident, &local); move (result) { result } } pub fn main() -> i64 { let value = 42; *bad(0, &value)() }",
        "fn bad<'a,T>(resident: T, fallback: &'a i64) -> &'a i64 where T: Use<[0,*]> { let local = 0; let mut value = forward(Mixed { resident: resident, known: fallback }); value.known = &local; get(value) } pub fn main() -> i64 { let value = 42; *bad(0, &value) }",
    ] {
        let source = format!("{AUTHENTICATED_INPUTS}\n{body}");
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new().compile(request(&source, optimization))
                .expect_err("reference authentication cannot erase an escaping local loan");
            assert!(error.diagnostics().iter().any(|diagnostic|
                matches!(diagnostic.code, "G5013" | "G5017")), "{body}: {:#?}", error.diagnostics());
            // A rejected caller may already contain recovered lifetime/type
            // metadata. The independently valid generic helpers must retain
            // their reference proof; the caller must report the local escape.
            assert!(!error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G5023"
                && diagnostic.primary.as_ref().is_some_and(|span| (span.start as usize) < AUTHENTICATED_INPUTS.len())),
                "valid helper reference proof was lost: {body}: {:#?}", error.diagnostics());
        }
    }
}

#[test]
fn authenticated_reference_results_keep_backing_storage_borrowed() {
    let source = format!("{AUTHENTICATED_INPUTS}\npub fn main() -> i64 {{ let mut value = 42; let reference = select(0, &value); value = 0; *reference }}");
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new().compile(request(&source, optimization))
            .expect_err("authentication is not permission to mutate borrowed storage");
        assert!(error.diagnostics().iter().any(|diagnostic| matches!(diagnostic.code, "G5004" | "G5007")), "{:#?}", error.diagnostics());
    }
}

#[test]
fn returned_reference_destinations_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std] struct Slot<'a> { value: &'a i64 } struct Carrier<'a,'b> { target: &'b mut Slot<'a> } fn get<'a,'b,'c>(carrier: &'c mut Carrier<'a,'b>) -> &'c mut Slot<'a> { &mut *carrier.target } pub fn main() -> i64 { let first = 40; let second = 42; let mut slot = Slot { value: &first }; let mut carrier = Carrier { target: &mut slot }; let target = get(&mut carrier); *target = Slot { value: &second }; *get(&mut carrier).value }";
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn authenticated_partial_reference_results_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = format!("{AUTHENTICATED_INPUTS}\npub fn main() -> i64 {{ let value = 42; *select(0, &value) }}");
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(&source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

#[test]
fn directional_reference_store_edges_execute_in_generated_code() {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let source = "#![no_std] struct Slot<'a> { value: &'a i64 } fn set<'a,'b>(slot: &mut Slot<'b>, value: &'a i64) where 'a: 'b { slot.value = value; } pub fn main() -> i64 { let first = 40; let second = 42; let mut slot = Slot { value: &first }; set(&mut slot, &second); *slot.value }";
    for optimization in [0, 2] {
        let ir = StageZeroCompiler::new().compile_llvm(request(source, &optimization.to_string()), LlvmTarget::host().unwrap())
            .unwrap_or_else(|error| panic!("source O{optimization}: {error:#?}"));
        // SAFETY: execute only this locally compiled and checked source.
        let native = unsafe { ir.compile(&LlvmCompileOptions { optimization, ..Default::default() }) }.unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}
