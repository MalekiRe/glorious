use grandiose_stage0::{
    BOOTSTRAP_MANIFEST_SCHEMA, BootstrapConvergenceError, BootstrapLimits, BootstrapManifest,
    BootstrapManifestError, BootstrapStage, CompilationMode, CompilationRequest,
    CompilerBuildIdentity, DiagnosticClass, Digest, LogicalPath, PackageKey, Severity, SourceInput,
    StageZeroCompiler, VmArtifactError, VmExecutionLimits, VmInstruction,
    decode_and_verify_program, decode_program,
};
use std::collections::BTreeMap;

fn request(source: &str) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"service"),
            language_generation: 1,
            query_generation: 1,
            interface_generation: 1,
            cache_generation: 1,
            bytecode_generation: 1,
            verifier_generation: 1,
        },
        mode: CompilationMode::Build,
        root_package: PackageKey("app@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("app@0.1.0".into()),
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

fn request_with_module(root: &str, child: &str) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    request.sources.push(SourceInput::new(
        package,
        LogicalPath::parse("src/math/math.glorious").unwrap(),
        child.as_bytes(),
    ));
    request
}

fn request_with_modules(root: &str, modules: &[(&str, &str)]) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    for (name, source) in modules {
        request.sources.push(SourceInput::new(
            package.clone(),
            LogicalPath::parse(format!("src/{name}/{name}.glorious")).unwrap(),
            source.as_bytes(),
        ));
    }
    request
}
#[test]
fn service_compiles_and_runs_a_verified_vm_artifact_from_an_immutable_request() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 40 + 2 }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_word_boolean_operators_as_short_circuit_cfg() {
    let false_and = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { false and (1 / 0 == 0) }"))
        .unwrap();
    assert!(!false_and.artifact.unwrap().run_bool().unwrap());

    let true_or = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true or (1 / 0 == 0) }"))
        .unwrap();
    assert!(true_or.artifact.unwrap().run_bool().unwrap());
}

#[test]
fn service_exposes_canonical_verified_vm_program_bytes_for_external_tools() {
    let artifact = StageZeroCompiler::new()
        .compile(request(
            "pub fn helper() -> i64 { 40 } pub fn main() -> i64 { helper() + 2 }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    let decoded = decode_and_verify_program(&artifact.canonical_bytes()).unwrap();
    assert_eq!(decoded.fingerprint(), artifact.fingerprint());
    assert_eq!(decoded.run_i64().unwrap(), 42);
}

#[test]
fn service_renders_any_verified_vm_entry_value_for_host_tools() {
    let tuple = StageZeroCompiler::new()
        .compile(request("pub fn main() -> (i64, i64) { (40, 2) }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(tuple.run_display().unwrap(), "(40, 2)");

    let text = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Text { \"glorious\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(text.run_display().unwrap(), "\"glorious\"");
}

#[test]
fn service_lowers_addressable_local_assignment_through_placeflow_and_the_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; value = 42; value }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn assignment_reinitializes_a_local_after_a_whole_value_move() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; move value; value = 42; value }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rebuilds_and_stores_statically_selected_record_fields() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> Pair { let pair = Pair { left: 1, right: 2 }; pair.left = 42; pair }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42, 2]
    );
}

#[test]
fn service_rebuilds_nested_record_write_paths_from_leaf_to_root() {
    let source = "pub struct Inner { value: i64 } pub struct Outer { inner: Inner } pub fn main() -> Inner { let outer = Outer { inner: Inner { value: 1 } }; outer.inner.value = 42; outer.inner }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42]
    );
}

#[test]
fn service_failures_preserve_source_identity_classification_and_request_provenance() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let expected_world = request.clone().normalize().unwrap().fingerprint;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("unresolved source unexpectedly compiled");
    };
    let diagnostic = diagnostics
        .iter()
        .find(|diagnostic| diagnostic.code == "G4104")
        .expect("missing-name diagnostic");
    assert_eq!(diagnostic.class, DiagnosticClass::Source);
    assert_eq!(diagnostic.severity, Severity::Error);
    assert!(
        diagnostic.primary.is_some(),
        "source diagnostic lost its span"
    );
    assert_eq!(diagnostic.input_fingerprint, Some(expected_world));
}

#[test]
fn service_instantiates_generic_callable_signatures_at_each_direct_call() {
    let source =
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_proves_and_enforces_direct_callable_trait_bounds() {
    let accepted = "trait Sendable {} impl Sendable for i64 {} pub fn identity<T>(value: T) -> T where T: Sendable { value } pub fn main() -> i64 { identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Sendable {} impl Sendable for i64 {} pub fn identity<T>(value: T) -> T where T: Sendable { value } pub fn main() -> Text { identity(\"not sendable\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("an unproven callable trait bound unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing callable trait-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_type_checks_implementation_method_bodies() {
    let source = "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> i64 { \"not an integer\" } } pub fn main() -> i64 { 42 }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("ill-typed implementation method unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4110"),
        "missing implementation method result diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_type_checks_implementation_method_bodies_with_impl_generics() {
    let source = "trait Identity<T> { fn identity(value: T) -> T; } struct Box<T> {} impl<T> Identity<T> for Box<T> { fn identity(value: T) -> T { value } } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_and_executes_explicit_trait_method_calls() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_selects_generic_qualified_trait_method_arguments() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn main() -> Text { Replace::replace(0, \"selected\") }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_selects_explicit_trait_method_operation_arguments() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn main() -> Text { Replace::replace<Text>(0, \"selected\") }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_selects_generic_qualified_trait_instances() {
    let source = "trait Identity<T> { fn identity(value: T) -> T; } impl<T> Identity<T> for T { fn identity(value: T) -> T { value } } pub fn main() -> i64 { Identity<i64>::identity(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_enforces_selected_trait_method_where_bounds() {
    let accepted = "trait Mark {} trait Convert { fn convert<T>(receiver: i64, value: T) -> T where T: Mark; } impl Mark for i64 {} impl Convert for i64 { fn convert<T>(receiver: i64, value: T) -> T where T: Mark { value } } pub fn main() -> i64 { Convert::convert(0, 42) }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let rejected = "trait Mark {} trait Convert { fn convert<T>(receiver: i64, value: T) -> T where T: Mark; } impl Mark for i64 {} impl Convert for i64 { fn convert<T>(receiver: i64, value: T) -> T where T: Mark { value } } pub fn main() -> Text { Convert::convert(0, \"not marked\") }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(rejected))
    else {
        panic!("unproven trait method bound unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing trait method bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_lowers_structural_is_patterns_into_verified_vm_tests() {
    let enum_source = "pub enum Result { Ok(i64), Err(Text) } pub fn main() -> Bool { Result::Ok(42) is Result::Ok(42) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(enum_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.unwrap().run_bool().unwrap());

    let record_source = "pub struct Pair { left: i64, right: Text } pub fn main() -> Bool { Pair { left: 42, right: \"stable\" } is Pair { right: \"stable\", left: 42 } }";
    let outcome = StageZeroCompiler::new()
        .compile(request(record_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.unwrap().run_bool().unwrap());

    let mismatch_source = "pub enum Result { Ok(i64), Err(Text) } pub fn main() -> Bool { Result::Ok(42) is Result::Ok(7) }";
    let outcome = StageZeroCompiler::new()
        .compile(request(mismatch_source))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(!outcome.artifact.unwrap().run_bool().unwrap());
}

#[test]
fn service_checks_effect_operation_identity_and_declared_rows() {
    let accepted = "effect Console { read() -> i64; } pub fn helper() -> i64 / Console { Console::read() } pub fn main() -> i64 { 42 }";
    let outcome = StageZeroCompiler::new().compile(request(accepted)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let missing_row = "effect Console { read() -> i64; } pub fn main() -> i64 { Console::read() }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(missing_row))
    else {
        panic!("undeclared effect performance unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "missing outward-effect diagnostic: {diagnostics:#?}"
    );

    let leaking_call = "effect Console { read() -> i64; } pub fn helper() -> i64 / Console { Console::read() } pub fn main() -> i64 { helper() }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(leaking_call))
    else {
        panic!("effectful direct call escaped through an empty row");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_executes_a_terminal_handler_without_leaking_an_unhandled_effect() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { handle { Stop::stop() } { Stop::stop() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_binds_terminal_handler_payloads_before_executing_the_clause() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn main() -> i64 { handle Stop::stop(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_terminal_handlers_for_the_exact_generic_effect_instance() {
    let source = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<i64>::fail(error) => error } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_terminal_handler_patterns_through_verified_cfg() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn choose(value: i64) -> i64 { handle Stop::stop(value) { Stop::stop(1) => 41, Stop::stop(other) => other } } pub fn main() -> i64 { choose(1) + choose(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_dispatches_structural_terminal_handler_patterns_through_verified_cfg() {
    let source = "pub enum Choice { Left, Right } effect Stop { stop(value: Choice) -> !; } pub fn choose(value: Choice) -> i64 { handle Stop::stop(value) { Stop::stop(Choice::Left) => 41, Stop::stop(_) => 42 } } pub fn main() -> i64 { choose(Choice::Left) + choose(Choice::Right) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_proves_enum_operation_coverage_without_an_irrefutable_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { ask(value: Choice) -> i64; } pub fn main() -> i64 { handle Ask::ask(Choice::Left) { Ask::ask(Choice::Left) => 41, Ask::ask(Choice::Right) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_bool_operation_coverage_without_an_irrefutable_catch_all() {
    let source = "effect Ask { ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true) { Ask::ask(true) => 41, Ask::ask(false) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_multi_argument_bool_operation_coverage_without_a_catch_all() {
    let source = "effect Ask { ask(left: Bool, right: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true, false) { Ask::ask(true, _) => 41, Ask::ask(false, _) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_mixed_enum_and_bool_operation_coverage_without_a_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { ask(choice: Choice, enabled: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(Choice::Left, false) { Ask::ask(Choice::Left, _) => 41, Ask::ask(Choice::Right, _) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_keeps_a_partial_finite_operation_in_the_outward_effect_row() {
    let source = "effect Ask { ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(false) { Ask::ask(true) => 41 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial Bool handler unexpectedly compiled as closed");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_keeps_a_partial_multi_argument_bool_matrix_in_the_outward_effect_row() {
    let source = "effect Ask { ask(left: Bool, right: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true, false) { Ask::ask(true, true) => 41, Ask::ask(false, false) => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial Bool matrix unexpectedly compiled as closed");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155")
    );
}

#[test]
fn service_dispatches_record_terminal_handler_patterns_through_verified_cfg() {
    let source = "pub struct Ticket { serial: i64 } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket { serial: 41 }) => 1, Stop::stop(_) => 2 } } pub fn main() -> i64 { choose(Ticket { serial: 41 }) + choose(Ticket { serial: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 3);
}

#[test]
fn service_projects_nested_record_binders_in_a_terminal_handler_arm() {
    let source = "pub struct Ticket { serial: i64 } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket { serial: serial }) => serial, Stop::stop(_) => 0 } } pub fn main() -> i64 { choose(Ticket { serial: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_projects_nested_enum_binders_in_a_terminal_handler_arm() {
    let source = "pub enum Ticket { Number(i64), Empty } effect Stop { stop(value: Ticket) -> !; } pub fn choose(value: Ticket) -> i64 { handle Stop::stop(value) { Stop::stop(Ticket::Number(serial)) => serial, Stop::stop(_) => 0 } } pub fn main() -> i64 { choose(Ticket::Number(42)) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_projects_tuple_binders_in_a_terminal_handler_arm() {
    let source = "effect Stop { stop(pair: (i64, i64)) -> !; } pub fn choose(pair: (i64, i64)) -> i64 { handle Stop::stop(pair) { Stop::stop((left, right)) => left + right } } pub fn main() -> i64 { choose((40, 2)) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_requires_all_terminal_handler_payload_patterns_before_selecting_an_arm() {
    let source = "effect Stop { stop(left: i64, right: i64) -> !; } pub fn choose(left: i64, right: i64) -> i64 { handle Stop::stop(left, right) { Stop::stop(1, 2) => 41, Stop::stop(first, second) => first + second } } pub fn main() -> i64 { choose(1, 2) + choose(3, 4) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 48);
}

#[test]
fn service_executes_a_direct_one_shot_resumption_at_the_handler_root() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_a_direct_operation_arm_with_a_normal_completion_arm() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_full_control_operation_dispatch_with_normal_completion() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(1) { value => value + 1, Ask::ask(1, k) => k(41), Ask::ask(_, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_mixed_handler_uses_explicit_trap_miss_for_finite_operation_coverage() {
    let source = "effect Ask { [1,1] ask(value: Bool) -> i64; } pub fn main() -> i64 { handle Ask::ask(true) { value => value, Ask::ask(true) => 41, Ask::ask(false) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_preserves_setup_before_a_mixed_direct_handler_operation() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 41; Ask::ask(seed) } { value => value + 1, Ask::ask(payload) => payload } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_terminal_operation_arms_bypass_normal_completion() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { handle Stop::stop() { value => value, Stop::stop() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_discarded_operation_arms_bypass_normal_completion() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { value => value + 1, Ask::ask(_) => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_mixed_resumptive_and_discarded_arms_take_distinct_completion_paths() {
    let source = "effect Ask { [0,1] ask(value: Bool) -> i64; } pub fn choose(value: Bool) -> i64 { handle Ask::ask(value) { result => result + 1, Ask::ask(true) => 41, Ask::ask(false, _) => 7 } } pub fn main() -> i64 { choose(true) + choose(false) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 49);
}

#[test]
fn service_runs_completion_for_a_pure_computation_inside_an_operation_handler() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle 41 { value => value + 1, Ask::ask() => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_effect_free_calls_inside_an_unexercised_handler_scope() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn identity(value: i64) -> i64 { value } pub fn main() -> i64 { handle identity(41) { value => value + 1, Ask::ask() => 0 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_resume_migration_syntax_to_the_same_direct_resumption() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => resume(k, 42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_the_pattern_slot_full_control_handler_form() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(42) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_allows_an_affine_pattern_slot_continuation_to_be_discarded() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_discard_of_a_required_pattern_slot_continuation() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 42 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("required continuation discard unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160")
    );
}

#[test]
fn service_dispatches_direct_resumptions_after_pattern_selection() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn choose(value: i64) -> i64 { handle Ask::ask(value) { Ask::ask(1) with k => k(41), Ask::ask(_) with k => resume(k, 42) } } pub fn main() -> i64 { choose(1) + choose(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_tail_resumes_a_direct_resumptive_operation_with_the_clause_value() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_enters_a_nonempty_let_bound_continuation_via_a_cfg_parameter() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask() with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_affine_discard_bypasses_a_nonempty_residual_continuation() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(_) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_uses_complete_enum_coverage_without_a_catch_all() {
    let source = "pub enum Choice { Left, Right } effect Ask { [1,1] ask(value: Choice) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(Choice::Left); value + 1 } { Ask::ask(Choice::Left, k) => k(41), Ask::ask(Choice::Right, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_preserves_pure_setup_before_the_intercepted_operation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 40; let value = Ask::ask(seed); value + 1 } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_preserves_pure_setup_before_the_root_handler() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { let seed = 41; handle { let value = Ask::ask(seed); value + 1 } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_reinstalls_static_dispatch_for_a_second_linear_performance() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(20); let right = Ask::ask(21); left + right } { Ask::ask(payload) with k => k(payload) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_reuses_ordered_pattern_dispatch_at_each_linear_performance() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(1); let right = Ask::ask(2); left + right } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_linear_resumption_uses_complete_bool_coverage_without_a_catch_all() {
    let source = "effect Ask { [1,1] ask(value: Bool) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(true); let right = Ask::ask(false); left + right } { Ask::ask(true, k) => k(40), Ask::ask(false, k) => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_affine_discard_exits_a_linear_handler_before_later_performances() {
    let source = "effect Ask { [0,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle { let left = Ask::ask(1); let right = Ask::ask(2); left + right } { Ask::ask(1, _) => 42, Ask::ask(_, k) => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_dispatches_each_operation_identity_in_a_linear_handler() {
    let source = "effect Pair { [1,1] first() -> i64; [1,1] second() -> i64; } pub fn main() -> i64 { handle { let left = Pair::first(); let right = Pair::second(); left + right } { Pair::first() with k => k(40); Pair::second() with k => k(2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_an_irrefutable_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 41 { value => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_the_implicit_identity_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 42 {} }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_a_wildcard_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle 41 { _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_ordered_literal_normal_completion_arms_through_verified_cfg() {
    let source = "pub fn choose(value: i64) -> i64 { handle value { 1 => 41, _ => 42 } } pub fn main() -> i64 { choose(1) + choose(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn service_binds_tuple_values_in_a_normal_completion_arm() {
    let source = "pub fn main() -> i64 { handle (40, 2) { (left, right) => left + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_classifies_qualified_enum_constructor_arms_as_completion_patterns() {
    let source = "pub enum Choice { Left, Right } pub fn main() -> i64 { handle Choice::Left { Choice::Left => 41, _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_classifies_record_completion_arms_before_effect_operation_syntax() {
    let source = "pub struct Ticket { serial: i64 } pub fn main() -> i64 { handle Ticket { serial: 41 } { Ticket { serial: 41 } => 41, _ => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_enum_normal_completion_coverage_without_a_wildcard() {
    let source = "pub enum Choice { Left, Right } pub fn main() -> i64 { handle Choice::Right { Choice::Left => 41, Choice::Right => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_proves_bool_normal_completion_coverage_without_a_wildcard() {
    let source = "pub fn main() -> i64 { handle false { true => 41, false => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_partial_normal_completion_coverage_without_a_fallback() {
    let source = "pub fn main() -> i64 { handle false { true => 41 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("partial completion handler unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4166")
    );
}

#[test]
fn service_tail_resumption_enters_the_same_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask() => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_a_direct_one_shot_handler_through_vm_handler_frames() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(41) { Ask::ask(value) with k => k(value + 1) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_nested_partial_one_shot_handler_through_vm_frames() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 / Choice { handle { handle Choice::second(40) { Choice::first(seed) => seed } } { Choice::second(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_through_an_arbitrary_depth_one_shot_handler_chain() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0) } } { Ask::ask(1) with k => k(1) } } { Ask::ask(2) with k => k(2) } } { Ask::ask(value) with k => k(value + 2) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    let artifact = outcome.artifact.unwrap();
    let program = decode_program(&artifact.canonical_bytes()).unwrap();
    let entry = program.functions.get(&program.entry).unwrap();
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::InstallHandler { .. }))
            .count(),
        4
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::Forward))
            .count(),
        3
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_refutable_inner_one_shot_clause_to_an_outer_frame() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0 } } { Ask::ask(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_a_refutable_generic_effect_clause_to_the_matching_outer_instance() {
    let source = "effect State<T> { [1,1] set(value: T) -> T; } pub fn main() -> i64 { handle { handle State<i64>::set(40) { State<i64>::set(0) => 0 } } { State<i64>::set(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_tries_ordered_refutable_one_shot_clauses_before_forwarding() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0, Ask::ask(40) => 42 } } { Ask::ask(seed) => seed + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_an_irrefutable_inner_fallback_before_the_outer_handler() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0, Ask::ask(seed) => seed + 2 } } { Ask::ask(seed) => seed + 10 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_nested_handler_setup_inside_its_outer_frame_scope() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let seed = 40; handle Ask::ask(seed) { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_inner_computation_setup_inside_its_inner_frame_scope() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let seed = 40; Ask::ask(seed) } { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_installs_sibling_operation_frames_for_nested_handler_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 / Choice { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_installs_distinct_sibling_operation_frames_for_nested_handler_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; [1,1] third(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); let second = Choice::second(first); Choice::third(second) } { Choice::first(value) => value + 1, Choice::second(value) => value + 1, Choice::third(value) => value } } { Choice::third(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_ordered_refutable_clauses_for_distinct_sibling_operation_frames() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; [1,1] third(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); let second = Choice::second(first); Choice::third(second) } { Choice::first(0) => 0, Choice::first(value) => value + 1, Choice::second(value) => value + 1, Choice::third(value) => value } } { Choice::third(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_uses_ordered_sibling_handler_clauses_during_nested_setup() {
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 / Choice { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(0) => 0, Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_executes_a_generic_effect_handler_through_vm_frames() {
    let source = "effect State<T> { [1,1] get() -> T; } pub fn main() -> i64 { handle State<i64>::get() { State<i64>::get() => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_instantiates_generic_effect_operations_at_the_call_and_handler() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask<i64>(41) { Ask::ask<i64>(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_infers_generic_effect_operation_arguments_at_the_call_and_handler() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask(41) { Ask::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_protocol_and_operation_generic_arguments_in_distinct_slots() {
    let source = "effect State<T> { replace<U>(value: T, replacement: U) -> U; } pub fn main() -> Text { handle State<i64>::replace<Text>(0, \"selected\") { State<i64>::replace<Text>(value, replacement) => replacement } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
}

#[test]
fn service_rejects_wrong_generic_effect_operation_arity() {
    let source = "effect Ask { ask<T>(value: T) -> T; } pub fn main() -> i64 { handle Ask::ask<i64, Text>(41) { Ask::ask<i64>(value) => value + 1 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("wrong operation generic arity unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4152"),
        "missing generic operation arity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_a_direct_one_resume_lowering_for_an_exact_two_shot_contract() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => k(42) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("single direct resume unexpectedly satisfied a two-shot contract");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "missing direct-resumption quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_executes_every_exact_finite_direct_resumption() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(20) + k(22) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_replays_a_pure_nonempty_finite_resumption_per_explicit_use() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_replays_the_full_pure_residual_prefix_per_finite_resumption() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); let bumped = value + 1; bumped * 2 } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 86);
}

#[test]
fn service_dispatches_ordered_finite_resumption_patterns_before_replay() {
    let source = "effect Ask { [2,2] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(2); value + 1 } { Ask::ask(1) with k => k(10) + k(11), Ask::ask(seed) with k => k(seed * 10) + k(seed * 11) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 44);
}

#[test]
fn service_selects_the_first_matching_finite_resumption_clause() {
    let source = "effect Ask { [2,2] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(1); value + 1 } { Ask::ask(1) with k => k(20) + k(21), Ask::ask(seed) with k => k(seed * 10) + k(seed * 11) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_replays_a_bounded_interval_resumption_when_the_static_uses_fit() {
    let source = "effect Ask { [1,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(k) => k(20) + k(21) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_generated_resumption_shadows_a_same_named_parameter() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn identity(value: i64) -> i64 { value } pub fn choose(k: (i64) -> i64) -> i64 { handle Ask::ask() { Ask::ask(k) => k(42) } } pub fn main() -> i64 { choose(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_named_functions_as_first_class_callable_values() {
    let source = "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn apply(function: (i64) -> i64) -> i64 { function(40) } pub fn main() -> i64 { apply(add_two) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_materializes_a_concretely_instantiated_generic_function_value() {
    let source = "pub fn identity<T>(value: T) -> T { value } pub fn apply(function: (i64) -> i64) -> i64 { function(42) } pub fn main() -> i64 { apply(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_direct_resumption_overuse_against_an_exact_quantity() {
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => k(1) + k(2) + k(3) } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overused direct resumption unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G6005"),
        "missing direct-resumption quantity diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_allows_an_explicit_unused_affine_direct_resumption() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_direct_effectful_helper_call_with_the_enclosing_handler() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { handle helper(41) { Ask::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_helper_parameter_order_when_intercepting_a_performance() {
    let source = "effect Ask { [1,1] ask(left: i64, right: i64) -> i64; } pub fn helper(left: i64, right: i64) -> i64 / Ask { Ask::ask(left, right) } pub fn main() -> i64 { handle helper(20, 22) { Ask::ask(left, right) => left + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_helper_performance_through_local_aliases_and_reordering() {
    let source = "effect Ask { [1,1] ask(left: i64, right: i64) -> i64; } pub fn helper(left: i64, right: i64) -> i64 / Ask { let first = right; let second = left; Ask::ask(first, second) } pub fn main() -> i64 { handle helper(20, 22) { Ask::ask(left, right) => left * 10 + right } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 240);
}

#[test]
fn service_instantiates_generic_helper_effect_rows_before_static_handler_interception() {
    let source = "effect Ask<T> { [1,1] ask(value: T) -> T; } pub fn helper<T>(value: T) -> T / Ask<T> { Ask<T>::ask(value) } pub fn main() -> i64 { handle helper(41) { Ask<i64>::ask(value) => value + 1 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_composes_an_intercepted_helper_call_with_normal_completion() {
    let source = "effect Ask { [1,1] ask(value: i64) -> i64; } pub fn helper(value: i64) -> i64 / Ask { Ask::ask(value) } pub fn main() -> i64 { handle helper(41) { result => result + 1, Ask::ask(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_intercepts_a_terminal_performance_reached_through_a_helper() {
    let source = "effect Stop { stop(value: i64) -> !; } pub fn helper(value: i64) -> i64 / Stop { Stop::stop(value) } pub fn main() -> i64 { handle helper(42) { Stop::stop(value) => value } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_binds_payloads_before_entering_a_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(41); value + 1 } { Ask::ask(seed) with k => k(seed) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_projects_nested_record_binders_before_entering_continuation() {
    let source = "pub struct Ticket { serial: i64 } effect Ask { [1,1] ask(ticket: Ticket) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(Ticket { serial: 41 }); value + 1 } { Ask::ask(Ticket { serial: serial }) with k => k(serial); Ask::ask(_) with k => k(0) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_projects_tuple_binders_before_entering_continuation() {
    let source = "effect Ask { [1,1] ask(pair: (i64, i64)) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask((40, 1)); value + 1 } { Ask::ask((left, right)) with k => k(left + right) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumption_selects_ordered_payload_patterns_before_a_nonempty_continuation() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(1); value + 1 } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_resumption_uses_the_irrefutable_fallback_after_a_payload_pattern_miss() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(2); value + 1 } { Ask::ask(1) with k => k(40); Ask::ask(_) with k => k(41) } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn generic_vm_calls_preserve_nominal_argument_relationships() {
    let source = "pub struct Box<T> { value: T } pub fn identity<T>(value: Box<T>) -> Box<T> { value } pub fn main() -> Box<i64> { identity(Box { value: 42 }) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![42]
    );
}

#[test]
fn generic_vm_calls_instantiate_binders_nested_inside_array_types() {
    let source = "pub fn identity<T>(value: Array<T>) -> Array<T> { value } pub fn main() -> Array<i64> { identity([42]) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_array_i64().unwrap(), vec![42]);
}

#[test]
fn check_mode_reuses_semantic_validation_without_publishing_a_vm_artifact() {
    let mut check = request("pub fn main() -> i64 { 40 + 2 }");
    check.mode = CompilationMode::Check;
    let outcome = StageZeroCompiler::new().compile(check).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert!(outcome.artifact.is_none());
    assert!(outcome.bootstrap_manifest.is_none());
}

#[test]
fn bootstrap_stages_record_path_free_manifests_and_prove_convergence() {
    let source = "pub fn main() -> i64 { 40 + 2 }";
    let mut stage_one = request(source);
    stage_one.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: None,
    });
    let compiler = StageZeroCompiler::new();
    let first = compiler.compile(stage_one).unwrap();
    let first_manifest = first.bootstrap_manifest.unwrap();
    assert_eq!(first.artifact.unwrap().run_i64().unwrap(), 42);

    let mut stage_two = request(source);
    stage_two.build.compiler = Digest::of_bytes(b"stage-one-compiler");
    stage_two.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"stage-one-artifact"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(first_manifest.artifact),
    });
    let second = compiler.compile(stage_two).unwrap();
    let second_manifest = second.bootstrap_manifest.unwrap();
    assert_ne!(first_manifest.world, second_manifest.world);
    assert_eq!(
        first_manifest.source_semantics,
        second_manifest.source_semantics
    );
    assert_eq!(first_manifest.codegen, second_manifest.codegen);
    first_manifest
        .compare_convergence(&second_manifest)
        .unwrap();
}

#[test]
fn bootstrap_stage_rejects_a_nonconvergent_expected_artifact() {
    let mut request = request("pub fn main() -> i64 { 42 }");
    request.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"stage-one-artifact"),
        optimization_level: 2,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: Some(Digest::of_bytes(b"not-this-program")),
    });
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request)
    else {
        panic!("nonconvergent bootstrap unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7012")
    );
}

#[test]
fn bootstrap_manifest_rejects_mismatched_codegen_even_when_artifacts_match() {
    let mut first = request("pub fn main() -> i64 { 42 }");
    first.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"seed"),
        optimization_level: 1,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: None,
    });
    let first = StageZeroCompiler::new()
        .compile(first)
        .unwrap()
        .bootstrap_manifest
        .unwrap();
    let mut second = request("pub fn main() -> i64 { 42 }");
    second.target = "different-vm".into();
    second.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"first"),
        optimization_level: 1,
        limits: BootstrapLimits::new(4, 16 * 1024),
        expected_artifact: None,
    });
    let second = StageZeroCompiler::new()
        .compile(second)
        .unwrap()
        .bootstrap_manifest
        .unwrap();
    assert!(matches!(
        first.compare_convergence(&second),
        Err(BootstrapConvergenceError::CodegenInputMismatch { .. })
    ));
}

#[test]
fn bootstrap_manifests_round_trip_canonically_and_reject_corruption() {
    let manifest = BootstrapManifest {
        schema: BOOTSTRAP_MANIFEST_SCHEMA,
        stage: BootstrapStage {
            ordinal: 2,
            producer: Digest::of_bytes(b"stage-one"),
            optimization_level: 2,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact: Some(Digest::of_bytes(b"stage-one-artifact")),
        },
        world: Digest::of_bytes(b"world"),
        source_semantics: Digest::of_bytes(b"source"),
        codegen: Digest::of_bytes(b"codegen"),
        artifact: Digest::of_bytes(b"artifact"),
    };
    let bytes = manifest.encode().unwrap();
    assert_eq!(BootstrapManifest::decode(&bytes).unwrap(), manifest);
    assert_eq!(
        manifest.encode().unwrap(),
        bytes,
        "manifest encoding is not canonical"
    );

    let mut wrong_magic = bytes.clone();
    wrong_magic[0] ^= 1;
    assert!(matches!(
        BootstrapManifest::decode(&wrong_magic),
        Err(BootstrapManifestError::InvalidMagic)
    ));
    assert!(matches!(
        BootstrapManifest::decode(&bytes[..bytes.len() - 1]),
        Err(BootstrapManifestError::Truncated)
    ));
    let mut trailing = bytes;
    trailing.push(0);
    assert!(matches!(
        BootstrapManifest::decode(&trailing),
        Err(BootstrapManifestError::TrailingBytes)
    ));

    let mut invalid = manifest;
    invalid.schema += 1;
    assert!(matches!(
        invalid.encode(),
        Err(BootstrapManifestError::UnsupportedSchema { .. })
    ));
}

#[test]
fn service_lowers_tuple_construction_through_the_verified_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> (i64, i64) { (40, 2) }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_tuple_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn service_lowers_typed_array_literals_through_the_verified_vm() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Array<i64> { [40, 2] }"))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_array_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn empty_array_literals_infer_their_element_type_from_the_result_contract() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Array<i64> { [] }"))
        .unwrap();
    assert_eq!(
        outcome.artifact.unwrap().run_array_i64().unwrap(),
        Vec::<i64>::new()
    );
}

#[test]
fn service_lowers_generic_struct_construction_through_the_verified_vm() {
    let source = "pub struct Pair<T> { left: T, right: T } pub fn main() -> Pair<i64> { Pair { left: 40, right: 2 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(
        outcome.artifact.unwrap().run_record_i64().unwrap(),
        vec![40, 2]
    );
}

#[test]
fn service_resolves_empty_braced_nominals_without_stealing_callable_blocks() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub struct Empty {} pub fn main() -> Empty { Empty {} }",
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_record_i64().unwrap(), vec![]);

    let ordinary = StageZeroCompiler::new()
        .compile(request(
            "pub fn choose(body: () -> ()) -> () { body() } pub fn main() -> () { choose {} }",
        ))
        .unwrap();
    ordinary.artifact.unwrap().run_unit().unwrap();
}

#[test]
fn service_constructs_empty_named_enum_payloads_from_the_same_braced_surface() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub enum Token { End {} } pub fn main() -> Token { Token::End {} }",
        ))
        .unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![]);
}

#[test]
fn service_lowers_struct_field_projection_through_the_verified_vm() {
    let source = "pub struct Pair<T> { left: T, right: T } pub fn main() -> i64 { Pair { left: 40, right: 2 }.left + Pair { left: 40, right: 2 }.right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_generic_tuple_enum_construction_through_the_verified_vm() {
    let source =
        "pub enum Choice<T> { Value(T), Empty } pub fn main() -> Choice<i64> { Choice::Value(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![42]);
}

#[test]
fn service_lowers_named_enum_payload_construction_through_the_verified_vm() {
    let source = "pub enum Result<T> { Ok(T), Err { code: i64 } } pub fn main() -> Result<i64> { Result::Err { code: 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty());
    assert_eq!(outcome.artifact.unwrap().run_enum_i64().unwrap(), vec![42]);
}

#[test]
fn service_lowers_validated_radix_integer_literals() {
    let outcome = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 0x2a + 0b0 }"))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_parses_checks_and_executes_typed_constant_initializers() {
    let source = "const forty: i64 = 40; const two: i64 = 2; pub fn main() -> i64 { forty + two }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_public_constants_from_another_module() {
    let root = "mod math; pub fn main() -> i64 { math::answer }";
    let child = "pub const answer: i64 = 42;";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_constant_initializer_cycles_before_vm_emission() {
    let source =
        "const first: i64 = second; const second: i64 = first; pub fn main() -> i64 { first }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("constant cycle unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7008")
    );
}

#[test]
fn service_executes_transparent_type_alias_contracts() {
    let source = "type Count = i64; pub fn add_two(value: Count) -> Count { value + 2 } pub fn main() -> Count { add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_normalizes_transparent_aliases_imported_from_another_module() {
    let root = "mod types; use types::Count; pub fn add_two(value: Count) -> Count { value + 2 } pub fn main() -> Count { add_two(40) }";
    let child = "pub type Count = i64;";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(root, &[("types", child)]))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_f64_arithmetic_and_typed_calls_to_the_verified_vm() {
    let source = "pub fn double(value: f64) -> f64 { value * 2.0 } pub fn main() -> f64 { double(20.5) + 1.0 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_f64().unwrap(), 42.0);
}

#[test]
fn verified_vm_executes_division_and_remainder_without_host_panics() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 84 / 2 % 43 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(integer.run_i64().unwrap(), 42);
    let float = StageZeroCompiler::new()
        .compile(request("pub fn main() -> f64 { 84.0 / 2.0 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(float.run_f64().unwrap(), 42.0);
    let zero = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { 1 / 0 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        zero.run_i64(),
        Err(VmArtifactError::DivisionByZero)
    ));
}

#[test]
fn service_lowers_source_defined_prefix_numeric_operators() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> i64 { -40 + +2 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(integer.run_i64().unwrap(), -38);
    let float = StageZeroCompiler::new()
        .compile(request("pub fn main() -> f64 { -40.5 + +82.5 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(float.run_f64().unwrap(), 42.0);
}

#[test]
fn service_lowers_boolean_prefix_negation() {
    let artifact = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { !false }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(artifact.run_bool().unwrap());
}

#[test]
fn service_lowers_char_literals_and_scalar_comparisons() {
    let character = StageZeroCompiler::new()
        .compile(request("pub fn main() -> char { '\\u{1f980}' }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(character.run_char().unwrap(), '🦀');

    let comparison = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { 'a' < 'z' }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(comparison.run_bool().unwrap());

    let boolean = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true != false }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(boolean.run_bool().unwrap());
}

#[test]
fn service_lowers_shared_text_handles_and_text_equality() {
    let text = StageZeroCompiler::new()
        .compile(request(
            "pub fn echo(value: Text) -> Text { value } pub fn main() -> Text { echo(\"hello, \\u{1f980}\") }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(text.run_text().unwrap(), "hello, 🦀");

    let equality = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { \"same\" == \"same\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(equality.run_bool().unwrap());

    let concatenated = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Text { \"hello, \" + \"world\" }"))
        .unwrap()
        .artifact
        .unwrap();
    assert_eq!(concatenated.run_text().unwrap(), "hello, world");
}

#[test]
fn service_lowers_empty_blocks_to_verified_unit_values() {
    let artifact = StageZeroCompiler::new()
        .compile(request(
            "pub fn noop() -> () { } pub fn main() -> () { noop() }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    artifact.run_unit().unwrap();
}

#[test]
fn prefix_operators_reject_incompatible_operand_types_before_mir() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> Bool { -true }"))
    else {
        panic!("invalid prefix operand unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4117")
    );
}

#[test]
fn service_lowers_bool_literals_and_typed_numeric_comparisons() {
    let integer = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { 20 + 22 == 42 }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(integer.run_bool().unwrap());
    let float = StageZeroCompiler::new()
        .compile(request(
            "pub fn below(value: f64) -> Bool { value < 2.0 } pub fn main() -> Bool { below(1.5) }",
        ))
        .unwrap()
        .artifact
        .unwrap();
    assert!(float.run_bool().unwrap());
    let literal = StageZeroCompiler::new()
        .compile(request("pub fn main() -> Bool { true }"))
        .unwrap()
        .artifact
        .unwrap();
    assert!(literal.run_bool().unwrap());
}

#[test]
fn service_lowers_immediately_invoked_typed_closures_with_captures() {
    let source =
        "pub fn main() -> i64 { let value = 40; ((extra: i64) -> i64 { value + extra })(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_infers_and_lowers_immediately_invoked_compact_closures() {
    let source = "pub fn main() -> i64 { { extra => extra + 2 }(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_lowers_lexically_bound_closures_with_creation_time_captures() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn lexical_closure_calls_rebind_parameters_on_each_invocation() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; add(1) + add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 83);
}

#[test]
fn lexical_closure_captures_are_stable_across_later_shadowing() {
    let source = "pub fn main() -> i64 { let value = 40; let add = (extra: i64) -> i64 { value + extra }; let value = 100; add(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn callables_cross_direct_call_boundaries_and_remain_indirectly_invocable() {
    let source = "pub fn make(value: i64) -> (i64) -> i64 { (extra: i64) -> i64 { value + extra } } pub fn main() -> i64 { make(40)(2) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_source_lexing_failures_through_the_release_root() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> i64 { 0b102 }"))
    else {
        panic!("malformed numeric literal unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G1008")
    );
}

#[test]
fn service_never_emits_a_release_artifact_from_recovered_body_or_core() {
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request("pub fn main() -> i64 { unresolved }"))
    else {
        panic!("recovered Typed Core unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G7007")
    );
}

#[test]
fn service_emits_a_verified_deterministic_program_for_direct_helper_calls() {
    let source = "pub fn forty() -> i64 { 40 } pub fn main() -> i64 { forty() + 2 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_passes_header_typed_arguments_through_verified_vm_frames() {
    let source =
        "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn main() -> i64 { add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn verified_vm_program_enforces_explicit_runtime_call_depth_limits() {
    let source = "pub fn recurse() -> i64 { recurse() } pub fn main() -> i64 { recurse() }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 4,
            max_handler_depth: 4_096,
            max_instructions: 100
        }),
        Err(VmArtifactError::CallDepthLimit { limit: 4 })
    ));
}

#[test]
fn verified_vm_program_enforces_explicit_handler_depth_limits() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) => 0 } } { Ask::ask(value) => value + 2 } }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 100,
            max_handler_depth: 1,
            max_instructions: 100,
        }),
        Err(VmArtifactError::HandlerDepthLimit { limit: 1 })
    ));
}

#[test]
fn verified_vm_program_enforces_explicit_instruction_limits() {
    let source = "pub fn recurse() -> i64 { recurse() } pub fn main() -> i64 { recurse() }";
    let artifact = StageZeroCompiler::new()
        .compile(request(source))
        .unwrap()
        .artifact
        .unwrap();
    assert!(matches!(
        artifact.run_i64_with_limits(VmExecutionLimits {
            max_call_depth: 100,
            max_handler_depth: 4_096,
            max_instructions: 2
        }),
        Err(VmArtifactError::InstructionLimit { limit: 2 })
    ));
}

#[test]
fn service_compiles_explicit_external_modules_from_the_request_source_world() {
    let root = "mod math; pub fn main() -> i64 { math::add_two(40) }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_module_qualified_values_without_last_segment_collisions() {
    let root = "mod math; mod other; pub fn main() -> i64 { math::add(40) + other::add(0) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            root,
            &[
                ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
                ("other", "pub fn add(value: i64) -> i64 { value }"),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_explicit_import_aliases() {
    let root = "mod math; use math::add_two as add; pub fn main() -> i64 { add(40) }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_grouped_import_bindings() {
    let root =
        "mod math; use math::{add_two as add, zero}; pub fn main() -> i64 { add(40) + zero() }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 } pub fn zero() -> i64 { 0 }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resolves_public_import_reexports_from_another_module() {
    let root = "mod math; mod facade; pub fn main() -> i64 { facade::add(40) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_modules(
            root,
            &[
                ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
                ("facade", "pub use crate::math::add;"),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn private_imports_cannot_be_used_as_module_reexports() {
    let root = "mod math; mod facade; pub fn main() -> i64 { facade::add(40) }";
    let error = StageZeroCompiler::new().compile(request_with_modules(
        root,
        &[
            ("math", "pub fn add(value: i64) -> i64 { value + 2 }"),
            ("facade", "use crate::math::add;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private import unexpectedly acted as a reexport")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104")
    );
}

#[test]
fn service_compiles_callables_declared_in_inline_modules() {
    let source = "mod math { pub fn add_two(value: i64) -> i64 { value + 2 } } pub fn main() -> i64 { math::add_two(40) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn equivalent_module_source_enumeration_orders_emit_the_same_verified_program() {
    let root = "mod math; pub fn main() -> i64 { math::add_two(40) }";
    let child = "pub fn add_two(value: i64) -> i64 { value + 2 }";
    let first = StageZeroCompiler::new()
        .compile(request_with_module(root, child))
        .unwrap();
    let mut reversed = request_with_module(root, child);
    reversed.sources.reverse();
    let second = StageZeroCompiler::new().compile(reversed).unwrap();
    assert_eq!(
        first.artifact.unwrap().fingerprint(),
        second.artifact.unwrap().fingerprint()
    );
}

#[test]
fn service_rejects_incoherent_impl_heads_before_body_elaboration() {
    let source = r#"
        trait Marker<T> {}
        struct Box<T> {}
        impl<T> Marker<T> for Box<T> {}
        impl Marker<i64> for Box<i64> {}
        pub fn main() -> i64 { 42 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overlapping implementations unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3404")
    );
}
