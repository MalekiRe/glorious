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
