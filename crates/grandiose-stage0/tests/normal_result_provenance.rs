use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("normal-result-provenance@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"normal-result-provenance")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.into())].into(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

fn accepts(source: &str) {
    for optimization in ["0", "2"] {
        let artifact = StageZeroCompiler::new()
            .compile(request(source, optimization))
            .unwrap_or_else(|error| panic!("O{optimization}: {source}\n{:#?}", error.diagnostics()))
            .artifact
            .unwrap();
        assert_eq!(artifact.run_i64().unwrap(), 42);
        assert_eq!(
            decode_and_verify_program(&artifact.canonical_bytes())
                .unwrap()
                .run_i64()
                .unwrap(),
            42
        );
    }
}

fn accepts_generated(source: &str) {
    use grandiose_stage0::vm_backend::llvm::{LlvmCompileOptions, LlvmTarget};
    let ir = StageZeroCompiler::new()
        .compile_llvm(request(source, "0"), LlvmTarget::host().unwrap())
        .unwrap_or_else(|error| panic!("{source}\n{error:#?}"));
    for optimization in [0, 2] {
        // SAFETY: execute only this locally compiled, checked source fixture.
        let native = unsafe {
            ir.compile(&LlvmCompileOptions {
                optimization,
                ..Default::default()
            })
        }
        .unwrap();
        assert_eq!(native.run_i64_with_limits(Default::default()).unwrap(), 42);
    }
}

const PREFIX: &str = r#"#![no_std]
    enum Flag { Yes, No }
    struct Wrapper<'a> { value: &'a i64 }
    fn get<'a>(wrapper: Wrapper<'a>) -> &'a i64 { wrapper.value }
    fn send<T,L>(value: T, exit: L) -> ! where L: Label<T> { exit(value) }
"#;

fn completion_source(terminal: &str, flag: &str) -> String {
    format!(
        r#"{PREFIX}
        fn select<'a>(value: &'a i64, flag: Flag) -> &'a i64 {{
            let wrapper = handle flag {{
                Flag::Yes => Wrapper {{ value: value }}, Flag::No => {terminal},
            }};
            get(wrapper)
        }}
        pub fn main() -> i64 {{ let value = 42; *select(&value, {flag}) }}
    "#
    )
}

#[test]
fn completion_normal_results_exclude_terminal_arm_placeholders() {
    for terminal in [
        "@select(value)",
        "send(value, @select)",
        "{ let exit = @select; send(value, exit) }",
    ] {
        for flag in ["Flag::Yes", "Flag::No"] {
            accepts(&completion_source(terminal, flag));
        }
    }
}

#[test]
fn direct_completion_reference_results_execute_in_generated_code() {
    for flag in ["Flag::Yes", "Flag::No"] {
        accepts_generated(&completion_source("@select(value)", flag));
    }
}

// Active acceptance failure: source/VM result provenance is valid, but the
// generic helper still leaves a MakeLabel carrier unsupported by native code.
// Keep the source and success requirement intact until that lowering is fixed.
#[test]
fn generic_completion_reference_results_execute_in_generated_code() {
    for terminal in [
        "send(value, @select)",
        "{ let exit = @select; send(value, exit) }",
    ] {
        for flag in ["Flag::Yes", "Flag::No"] {
            accepts_generated(&completion_source(terminal, flag));
        }
    }
}

#[test]
fn handler_normal_results_exclude_terminal_arm_placeholders() {
    for flag in ["Flag::Yes", "Flag::No"] {
        accepts(&format!(
            r#"{PREFIX}
            effect Raise {{ raise(); }}
            fn select<'a>(value: &'a i64, flag: Flag) -> &'a i64 {{
                let wrapper = handle {{
                    handle flag {{ Flag::Yes => Raise::raise(), Flag::No => () }};
                    Wrapper {{ value: value }}
                }} {{ Raise::raise() => @select(value) }};
                get(wrapper)
            }}
            pub fn main() -> i64 {{ let value = 42; *select(&value, {flag}) }}
        "#
        ));
    }
}

#[test]
fn handler_normal_results_exclude_a_terminal_computation_placeholder() {
    accepts(&format!(
        r#"{PREFIX}
        effect Stop {{ stop() -> !; }}
        fn select<'a>(value: &'a i64) -> &'a i64 {{
            let wrapper = handle Stop::stop() {{ Stop::stop() => Wrapper {{ value: value }} }};
            get(wrapper)
        }}
        pub fn main() -> i64 {{ let value = 42; *select(&value) }}
    "#
    ));
}

#[test]
fn terminal_operations_preserve_their_executed_payload_without_a_normal_result() {
    accepts(&format!(
        r#"{PREFIX}
        effect Stop<'a> {{ stop(value: Wrapper<'a>) -> !; }}
        fn select<'a>(value: &'a i64) -> &'a i64 {{
            let wrapper = handle Stop<'a>::stop(Wrapper {{ value: value }}) {{
                Stop<'a>::stop(payload) => payload,
            }};
            get(wrapper)
        }}
        pub fn main() -> i64 {{ let value = 42; *select(&value) }}
    "#
    ));
}

#[test]
fn an_operation_with_a_terminal_argument_never_publishes_a_payload() {
    accepts(
        r#"#![no_std]
        effect Stop { stop(&i64, i64) -> !; }
        pub fn main() -> i64 {
            let local = 0;
            handle Stop::stop(&local, @main(42)) { Stop::stop(_, _) => 0 }
        }
    "#,
    );
}

#[test]
fn a_terminal_operation_cannot_export_its_abandoned_local_storage() {
    let source = r#"#![no_std]
        effect Stop { stop(&i64) -> !; }
        pub fn main() -> i64 {
            handle { let local = 42; Stop::stop(&local) } { Stop::stop(value) => *value }
        }
    "#;
    for optimization in ["0", "2"] {
        let error = StageZeroCompiler::new()
            .compile(request(source, optimization))
            .expect_err("terminal payloads cannot borrow the abandoned protected local");
        assert!(
            error
                .diagnostics()
                .iter()
                .any(|diagnostic| diagnostic.code == "G5015"),
            "O{optimization}: {:#?}",
            error.diagnostics()
        );
    }
}

#[test]
fn terminal_arm_payloads_still_retain_local_reference_escape_obligations() {
    for (terminal, codes) in [
        ("@select(&local)", &["G5013", "G5017"][..]),
        // The generic forms reject earlier: a local reference cannot satisfy
        // the nominal label's declared payload lifetime at the call boundary.
        ("send(&local, @select)", &["G4143"][..]),
        ("{ let exit = @select; send(&local, exit) }", &["G4143"][..]),
    ] {
        let source = format!(
            r#"{PREFIX}
            fn select<'a>(value: &'a i64, flag: Flag) -> &'a i64 {{
                let local = 0;
                let wrapper = handle flag {{
                    Flag::Yes => Wrapper {{ value: value }}, Flag::No => {terminal},
                }};
                get(wrapper)
            }}
            pub fn main() -> i64 {{ let value = 42; *select(&value, Flag::No) }}
        "#
        );
        for optimization in ["0", "2"] {
            let error = StageZeroCompiler::new()
                .compile(request(&source, optimization))
                .expect_err("an outer transfer must not erase its local reference dependency");
            assert!(
                error
                    .diagnostics()
                    .iter()
                    .any(|diagnostic| codes.contains(&diagnostic.code)),
                "O{optimization}: {source}\n{:#?}",
                error.diagnostics()
            );
        }
    }
}
