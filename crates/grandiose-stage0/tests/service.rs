use grandiose_stage0::{
    BOOTSTRAP_MANIFEST_SCHEMA, BootstrapConvergenceError, BootstrapLimits, BootstrapManifest,
    BootstrapManifestError, BootstrapStage, Budget, CancellationToken, CompilationMode,
    CompilationRequest, CompileDiagnostic, CompilerBuildIdentity, DependencyNode, DependencyStatus,
    DiagnosticClass, Digest, InstanceLimits, LogicalPath, ModuleKey, PackageKey, RetentionReport,
    Severity, SourceInput, StageZeroCompiler, VmArtifactError, VmExecutionLimits, VmInstruction,
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

fn request_with_logical_sources(root: &str, sources: &[(&str, &str)]) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    let mut request = request(root);
    for (path, source) in sources {
        request.sources.push(SourceInput::new(
            package.clone(),
            LogicalPath::parse(*path).unwrap(),
            source.as_bytes(),
        ));
    }
    request
}

#[test]
fn service_exposes_malformed_requests_as_structured_diagnostics() {
    let mut malformed = request("pub fn main() -> i64 { 0 }");
    malformed.sources.clear();

    let error = StageZeroCompiler::new().compile(malformed).unwrap_err();
    let diagnostics = error.diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "G7015");
    assert_eq!(diagnostics[0].class, DiagnosticClass::Request);
    assert_eq!(diagnostics[0].severity, Severity::Error);
    assert!(diagnostics[0].primary.is_none());
    assert!(diagnostics[0].input_fingerprint.is_none());
}

#[test]
fn service_classifies_untrusted_source_bytes_as_input_corruption() {
    let mut malformed = request("pub fn main() -> i64 { 0 }");
    malformed.sources[0].bytes = vec![0xff].into();
    malformed.sources[0].digest = Digest::of_bytes(&[0xff]);

    let error = StageZeroCompiler::new().compile(malformed).unwrap_err();
    let diagnostics = error.diagnostics();
    assert_eq!(diagnostics.len(), 1);
    assert_eq!(diagnostics[0].code, "G7018");
    assert_eq!(diagnostics[0].class, DiagnosticClass::InputCorruption);
    assert!(diagnostics[0].input_fingerprint.is_none());
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
fn service_applies_host_instance_discovery_limits_before_lowering() {
    let compiler = StageZeroCompiler::with_instance_limits(InstanceLimits {
        total: 1,
        per_definition: 1,
    });
    let error = compiler
        .compile(request(
            "pub fn helper() -> i64 { 41 } pub fn main() -> i64 { helper() + 1 }",
        ))
        .unwrap_err();

    let diagnostics = error.diagnostics();
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "G7031"
            && diagnostic.class == DiagnosticClass::Resource
            && diagnostic.message.contains("TotalLimit { limit: 1")
    }));
}

#[test]
fn service_discovers_concrete_generic_direct_call_instances() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }",
        ))
        .unwrap();
    let instances = outcome
        .instance_graph
        .expect("instance discovery evidence")
        .ordered();
    assert_eq!(instances.len(), 2, "{instances:#?}");
    assert!(
        instances
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_executes_a_concrete_generic_mir_instance_through_vm_linking() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity(42) }",
        ))
        .unwrap();
    let artifact = outcome.artifact.expect("build must publish a VM program");
    assert_eq!(artifact.run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("instance graph")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_finalizes_main_as_a_closed_zero_argument_effect_boundary() {
    for (source, message) in [
        (
            "pub fn main(value: i64) -> i64 { value }",
            "executable entry `main` must not declare parameters",
        ),
        (
            "pub fn main<T>() -> i64 { 0 }",
            "executable entry `main` cannot declare generic binders",
        ),
        (
            "pub fn main<e: EffectRow>() -> i64 / {| e} { 0 }",
            "executable entry `main` cannot declare generic binders",
        ),
        (
            "effect Trace { note(); } pub fn main() -> i64 / {Trace} { 0 }",
            "executable entry `main` must have a closed empty outward effect row",
        ),
    ] {
        let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
            StageZeroCompiler::new().compile(request(source))
        else {
            panic!("invalid executable entry unexpectedly compiled: {source}");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| { diagnostic.code == "G7028" && diagnostic.message == message }),
            "missing executable-boundary diagnostic for {source}: {diagnostics:#?}"
        );
    }
}

#[test]
fn service_compiles_explicit_parent_and_child_revisions_without_world_mixing() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 2 }"), None)
        .unwrap();
    let parent_outcome = compiler.compile_revision(parent).unwrap();
    assert_eq!(parent_outcome.artifact.unwrap().run_i64().unwrap(), 42);

    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 3 }"), Some(parent))
        .unwrap();
    let child_outcome = compiler.compile_revision(child).unwrap();
    assert_eq!(child_outcome.artifact.unwrap().run_i64().unwrap(), 43);
}

#[test]
fn service_tracks_private_body_edits_without_invalidating_public_products() {
    let compiler = StageZeroCompiler::new();
    let parent_request = request("pub fn helper() -> i64 { 1 } pub fn main() -> i64 { helper() }");
    let parent = compiler.import_revision(parent_request, None).unwrap();
    compiler.compile_revision(parent).unwrap();
    let child_request = request("pub fn helper() -> i64 { 2 } pub fn main() -> i64 { helper() }");
    let changed_file = child_request.sources[0].key;
    let child = compiler
        .import_revision(child_request, Some(parent))
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(child)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        2
    );

    let crate_module = ModuleKey {
        package: PackageKey("app@0.1.0".into()),
        path: "crate".into(),
    };
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Input(changed_file))
            .unwrap()
            .status,
        DependencyStatus::Red { .. }
    ));
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Interface(crate_module.clone()))
            .unwrap()
            .status,
        DependencyStatus::Green { parent: green_parent } if green_parent == parent
    ));
    assert!(matches!(
        compiler
            .dependency_trace(child, &DependencyNode::Fixity(crate_module))
            .unwrap()
            .status,
        DependencyStatus::Green { .. }
    ));
    let traces = compiler.dependency_traces(child);
    assert!(
        traces
            .iter()
            .any(|trace| matches!(trace.node, DependencyNode::Core(_))
                && matches!(trace.status, DependencyStatus::Red { .. }))
    );
    assert!(matches!(
        traces
            .iter()
            .find(|trace| matches!(trace.node, DependencyNode::Artifact(_)))
            .unwrap()
            .status,
        DependencyStatus::Red { ref first_changed, .. } if *first_changed == DependencyNode::Input(changed_file)
    ));
}

#[test]
fn service_traces_concrete_instances_and_invalidates_changed_callee_edges() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request("pub fn helper() -> i64 { 1 } pub fn main() -> i64 { helper() }"),
            None,
        )
        .unwrap();
    let parent_outcome = compiler.compile_revision(parent).unwrap();
    let parent_graph = parent_outcome.instance_graph.expect("instance graph");
    assert_eq!(parent_graph.ordered().len(), 2);
    let main = parent_graph
        .roots()
        .keys()
        .next()
        .expect("entry instance")
        .clone();
    let helper = parent_graph
        .callees(&main)
        .unwrap()
        .iter()
        .next()
        .unwrap()
        .clone();
    assert!(matches!(
        compiler
            .dependency_trace(parent, &DependencyNode::Instance(main.clone()))
            .unwrap()
            .status,
        DependencyStatus::Cold
    ));
    let child = compiler
        .import_revision(
            request("pub fn helper() -> i64 { 2 } pub fn main() -> i64 { helper() }"),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();
    let trace = compiler
        .dependency_trace(child, &DependencyNode::Instance(helper))
        .unwrap();
    assert!(
        trace
            .dependencies
            .iter()
            .any(|dependency| matches!(dependency, DependencyNode::Body(_)))
    );
}

#[test]
fn service_tracks_public_interface_edits_without_invalidating_unaffected_bodies() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request("pub struct Version { value: i64 } pub fn main() -> i64 { 42 }"),
            None,
        )
        .unwrap();
    compiler.compile_revision(parent).unwrap();
    let child = compiler
        .import_revision(
            request("pub struct Version { value: i64, next: i64 } pub fn main() -> i64 { 42 }"),
            Some(parent),
        )
        .unwrap();
    compiler.compile_revision(child).unwrap();
    let traces = compiler.dependency_traces(child);
    assert!(matches!(
        compiler
            .dependency_trace(
                child,
                &DependencyNode::Interface(ModuleKey {
                    package: PackageKey("app@0.1.0".into()),
                    path: "crate".into(),
                }),
            )
            .unwrap()
            .status,
        DependencyStatus::Red { .. }
    ));
    // The body was revalidated against the new interface but its frozen Core
    // is equal, so no downstream work need treat it as red.
    assert!(
        traces
            .iter()
            .any(|trace| matches!(trace.node, DependencyNode::Core(_))
                && matches!(trace.status, DependencyStatus::Green { .. }))
    );
}

#[test]
fn service_sessions_pin_retired_revisions_without_mixing_live_worlds() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 2 }"), None)
        .unwrap();
    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 40 + 3 }"), Some(parent))
        .unwrap();
    let parent_session = compiler.open_session(parent).unwrap();
    let child_session = compiler.open_session(child).unwrap();
    assert_eq!(parent_session.metadata().parent, None);
    assert_eq!(child_session.metadata().parent, Some(parent));
    assert_ne!(
        parent_session.metadata().input_fingerprint,
        child_session.metadata().input_fingerprint
    );

    compiler.retire_revision(parent).unwrap();
    assert!(matches!(
        compiler.open_session(parent),
        Err(error) if error.diagnostics()[0].code == "G7027"
    ));
    assert_eq!(
        compiler.collect_retired(),
        RetentionReport {
            collected: 0,
            retained_pinned: 1,
        }
    );

    // Retirement cannot redirect either already-admitted request to a newer
    // source world. The pinned parent remains executable while the child
    // observes its own independent revision.
    assert_eq!(
        compiler
            .compile_session(&parent_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(
        compiler
            .compile_session(&child_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
    assert!(matches!(
        StageZeroCompiler::new().compile_session(&child_session),
        Err(error) if error.diagnostics()[0].code == "G7026"
    ));

    drop(parent_session);
    assert_eq!(
        compiler.collect_retired(),
        RetentionReport {
            collected: 1,
            retained_pinned: 0,
        }
    );
    assert!(matches!(
        compiler.open_session(parent),
        Err(error) if error.diagnostics()[0].code == "G7025"
    ));
    assert_eq!(
        compiler
            .compile_session(&child_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
}

#[test]
fn cancelled_service_sessions_discard_staged_cache_artifacts_and_release_pins() {
    let compiler = StageZeroCompiler::new();
    let revision = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() }",
                "pub fn answer() -> i64 { 42 }",
            ),
            None,
        )
        .unwrap();
    let cancellation = CancellationToken::new();
    let budget = Budget::root("request", 4);
    let session = compiler
        .open_session_with_controls(revision, cancellation.clone(), budget.clone())
        .unwrap();
    cancellation.cancel();

    let error = compiler.compile_session(&session).unwrap_err();
    assert_eq!(error.diagnostics()[0].code, "G7029");
    // `compile_session` returned no `CompilationOutcome`, so no artifact can
    // cross the request publication boundary.
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(revision).is_empty());
    assert_eq!(budget.spent(), 0);

    compiler.retire_revision(revision).unwrap();
    assert_eq!(compiler.collect_retired().retained_pinned, 1);
    drop(session);
    assert_eq!(compiler.collect_retired().collected, 1);
}

#[test]
fn failed_and_resource_limited_sessions_do_not_publish_staged_interfaces() {
    let compiler = StageZeroCompiler::new();
    let failed_revision = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn helper() -> i64 { math::answer() }",
                "pub fn answer() -> i64 { 42 }",
            ),
            None,
        )
        .unwrap();
    let failed_session = compiler.open_session(failed_revision).unwrap();
    assert!(compiler.compile_session(&failed_session).is_err());
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(failed_revision).is_empty());

    let limited_revision = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();
    let budget = Budget::root("request", 0);
    let limited_session = compiler
        .open_session_with_controls(limited_revision, CancellationToken::new(), budget.clone())
        .unwrap();
    let error = compiler.compile_session(&limited_session).unwrap_err();
    assert_eq!(error.diagnostics()[0].code, "G7030");
    assert_eq!(budget.spent(), 0);
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(compiler.dependency_traces(limited_revision).is_empty());
}

#[test]
fn service_reuses_only_unchanged_frozen_module_interfaces_across_revisions() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 1 }",
                "pub fn answer() -> i64 { 41 }",
            ),
            None,
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(parent)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 2);

    // Replacing only the root source must recollect that interface while the
    // unchanged external module is validated and reused in the child world.
    let root_changed = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 2 }",
                "pub fn answer() -> i64 { 41 }",
            ),
            Some(parent),
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(root_changed)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        43
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        grandiose_stage0::InterfaceCacheStats { hits: 1, misses: 3 }
    );

    // The next child changes the dependency interface itself. The root can
    // reuse its exact frozen interface, but `math` must be recollected and the
    // new executable result proves no old interface/body product leaked.
    let dependency_changed = compiler
        .import_revision(
            request_with_module(
                "mod math; pub fn main() -> i64 { math::answer() + 2 }",
                "pub fn answer() -> i64 { 42 }",
            ),
            Some(root_changed),
        )
        .unwrap();
    assert_eq!(
        compiler
            .compile_revision(dependency_changed)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        44
    );
    assert_eq!(
        compiler.interface_cache_stats(),
        grandiose_stage0::InterfaceCacheStats { hits: 2, misses: 4 }
    );
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
fn service_lowers_unique_borrow_deref_and_mutation_without_copying_the_place() {
    let outcome = StageZeroCompiler::new()
        .compile(request(
            "pub fn main() -> i64 { let value = 1; let reference = &mut value; *reference = 42; *reference }",
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn shared_dereference_cannot_be_used_as_a_mutation_place() {
    let diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn main() -> i64 { let value = 1; let reference = &value; *reference = 42; value }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("shared-reference mutation unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4141")
    );
}

#[test]
fn reference_to_body_local_cannot_escape_as_a_return_value() {
    let diagnostics = match StageZeroCompiler::new()
        .compile(request("pub fn main() -> &i64 { let value = 1; &value }"))
    {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("body-local reference unexpectedly escaped: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "missing body-local reference escape diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn active_unique_loan_rejects_move_of_its_referent() {
    let diagnostics = match StageZeroCompiler::new().compile(request(
        "pub fn main() -> i64 { let value = 1; let reference = &mut value; move value; *reference }",
    )) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("move while uniquely borrowed unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "missing move-while-borrowed diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn unique_field_borrow_preserves_the_projected_place_identity() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let reference = &mut pair.left; *reference = 42; pair.left }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn unique_reborrow_reuses_the_original_vm_place() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = &mut *parent; *child = 42; *parent }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn parent_unique_reference_is_suspended_while_a_unique_reborrow_is_live() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = &mut *parent; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("active unique reborrow failed to suspend its parent: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "missing parent-reborrow conflict: {diagnostics:#?}"
    );
}

#[test]
fn sibling_shared_reborrows_keep_the_parent_region_live() {
    let source = "pub fn main() -> i64 { let value = 21; let parent = &mut value; let left = & *parent; let right = & *parent; *left + *right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn handler_join_retains_shared_reborrow_region_provenance() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 21; let parent = &mut value; let child = & *parent; handle Stop::stop() { Stop::stop() => 0 }; *child + *child }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn handler_join_keeps_shared_reborrow_parent_suspended() {
    let source = "effect Stop { stop() -> !; } pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = & *parent; handle Stop::stop() { Stop::stop() => 0 }; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("handler join reopened a suspended parent: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004")
    );
}

#[test]
fn shared_reborrow_still_suspends_unique_parent_mutation() {
    let source = "pub fn main() -> i64 { let value = 1; let parent = &mut value; let child = & *parent; *parent = 2; *child }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("shared reborrow failed to suspend parent mutation: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004")
    );
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
fn service_preserves_disjoint_aggregate_fields_after_a_partial_move() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.right }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 2);
}

#[test]
fn service_reports_overlapping_use_after_a_partial_move() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.left }";
    let diagnostics = match StageZeroCompiler::new().compile(request(source)) {
        Err(grandiose_stage0::ServiceError::Failed(diagnostics)) => diagnostics,
        outcome => panic!("partial move overlap unexpectedly compiled: {outcome:#?}"),
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "missing projection use-after-move diagnostic: {diagnostics:#?}"
    );
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
fn compile_diagnostic_canonicalization_is_stable_and_deduplicates_exact_facts() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let source = grandiose_stage0::SourceSpan {
        file,
        start: 12,
        end: 24,
    };
    let duplicate = CompileDiagnostic {
        code: "G4104",
        message: "unresolved name `missing_name`".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(source),
        input_fingerprint: Some(Digest::of_bytes(b"first-world")),
    };
    let same_code_different_location = CompileDiagnostic {
        primary: Some(grandiose_stage0::SourceSpan {
            start: 25,
            end: 37,
            ..source
        }),
        input_fingerprint: Some(Digest::of_bytes(b"second-world")),
        ..duplicate.clone()
    };

    let diagnostics = CompileDiagnostic::canonicalize(vec![
        same_code_different_location.clone(),
        duplicate.clone(),
        duplicate,
    ]);

    assert_eq!(diagnostics.len(), 2);
    assert_eq!(diagnostics[0].primary, Some(source));
    assert_eq!(diagnostics[1], same_code_different_location);
}

#[test]
fn compile_diagnostic_json_lines_are_deterministic_and_escape_control_text() {
    let request = request("pub fn main() -> i64 { 0 }");
    let diagnostic = CompileDiagnostic {
        code: "G0001",
        message: "line\n\"quoted\"\\tab\t\u{001b}🙂".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: Some(grandiose_stage0::SourceSpan {
            file: request.sources[0].key,
            start: 4,
            end: 9,
        }),
        input_fingerprint: Some(Digest::of_bytes(b"json-world")),
    };

    assert_eq!(
        diagnostic.to_json_line(),
        format!(
            "{{\"code\":\"G0001\",\"class\":\"source\",\"severity\":\"warning\",\"message\":\"line\\n\\\"quoted\\\"\\\\tab\\t\\u001b🙂\",\"primary\":{{\"file\":\"{}\",\"start_byte\":4,\"end_byte\":9}},\"input_fingerprint\":\"{}\"}}",
            request.sources[0].key.0,
            Digest::of_bytes(b"json-world"),
        )
    );
}

#[test]
fn compile_diagnostic_canonicalization_presents_source_facts_by_span_then_severity_and_code() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let at_ten = grandiose_stage0::SourceSpan {
        file,
        start: 10,
        end: 11,
    };
    let at_twenty = grandiose_stage0::SourceSpan {
        file,
        start: 20,
        end: 21,
    };
    let at_ten_warning = CompileDiagnostic {
        code: "G0002",
        message: "warning at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: Some(at_ten),
        input_fingerprint: None,
    };
    let at_ten_error_later_code = CompileDiagnostic {
        code: "G0003",
        message: "later error code at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_ten),
        input_fingerprint: None,
    };
    let at_ten_error_earlier_code = CompileDiagnostic {
        code: "G0001",
        message: "earlier error code at byte ten".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_ten),
        input_fingerprint: None,
    };
    let at_twenty_error = CompileDiagnostic {
        code: "G0000",
        message: "error at byte twenty".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(at_twenty),
        input_fingerprint: None,
    };
    let unspanned_request = CompileDiagnostic {
        code: "G9999",
        message: "request failure".into(),
        class: DiagnosticClass::Request,
        severity: Severity::Error,
        primary: None,
        input_fingerprint: None,
    };

    let diagnostics = CompileDiagnostic::canonicalize(vec![
        unspanned_request.clone(),
        at_twenty_error.clone(),
        at_ten_warning.clone(),
        at_ten_error_later_code.clone(),
        at_ten_error_earlier_code.clone(),
    ]);

    assert_eq!(
        diagnostics,
        vec![
            at_ten_error_earlier_code,
            at_ten_error_later_code,
            at_ten_warning,
            at_twenty_error,
            unspanned_request,
        ]
    );
}

#[test]
fn compile_diagnostic_span_validation_replaces_invalid_phase_locations() {
    let request = request("pub fn main() -> i64 { 42 }");
    let file = request.sources[0].key;
    let foreign_file = SourceInput::new(
        PackageKey("app@0.1.0".into()),
        LogicalPath::parse("src/foreign.glorious").unwrap(),
        b"foreign".as_slice(),
    )
    .key;
    let fingerprint = Digest::of_bytes(b"diagnostic-world");
    let valid = CompileDiagnostic {
        code: "G0001",
        message: "valid source fact".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Error,
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 0,
            end: 1,
        }),
        input_fingerprint: Some(fingerprint),
    };
    let past_end = CompileDiagnostic {
        code: "G0002",
        message: "past the source end".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 0,
            end: 99,
        }),
        ..valid.clone()
    };
    let backwards = CompileDiagnostic {
        code: "G0003",
        message: "backwards range".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file,
            start: 3,
            end: 2,
        }),
        ..valid.clone()
    };
    let unknown_file = CompileDiagnostic {
        code: "G0004",
        message: "unknown file".into(),
        primary: Some(grandiose_stage0::SourceSpan {
            file: foreign_file,
            start: 0,
            end: 1,
        }),
        ..valid.clone()
    };

    let diagnostics = CompileDiagnostic::validate_primary_spans(
        vec![valid.clone(), past_end, backwards, unknown_file],
        &BTreeMap::from([(file, request.sources[0].bytes.len() as u32)]),
    );

    assert_eq!(diagnostics[0], valid);
    assert_eq!(diagnostics.len(), 4);
    for diagnostic in &diagnostics[1..] {
        assert_eq!(diagnostic.code, "G7014");
        assert_eq!(diagnostic.class, DiagnosticClass::Invariant);
        assert_eq!(diagnostic.severity, Severity::Error);
        assert_eq!(diagnostic.primary, None);
        assert_eq!(diagnostic.input_fingerprint, Some(fingerprint));
    }
    assert_eq!(
        diagnostics[1].message,
        "compiler produced diagnostic G0002 with an invalid primary source span"
    );
}

#[test]
fn compile_diagnostic_error_limit_keeps_the_earliest_facts_and_reports_suppression() {
    let request = request("pub fn main() -> i64 { missing_name }");
    let file = request.sources[0].key;
    let mut diagnostics = Vec::new();
    for start in (0..5).rev() {
        diagnostics.push(CompileDiagnostic {
            code: "G4104",
            message: format!("unresolved name at byte {start}"),
            class: DiagnosticClass::Source,
            severity: Severity::Error,
            primary: Some(grandiose_stage0::SourceSpan {
                file,
                start,
                end: start + 1,
            }),
            input_fingerprint: None,
        });
    }
    diagnostics.push(CompileDiagnostic {
        code: "G0002",
        message: "context warning".into(),
        class: DiagnosticClass::Source,
        severity: Severity::Warning,
        primary: None,
        input_fingerprint: None,
    });

    let diagnostics = CompileDiagnostic::limit_errors(diagnostics, 3);
    assert_eq!(
        diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.severity == Severity::Error)
            .count(),
        3
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter_map(|diagnostic| diagnostic.primary)
            .map(|span| span.start)
            .collect::<Vec<_>>(),
        vec![0, 1]
    );
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code == "G7013"
            && diagnostic.class == DiagnosticClass::Resource
            && diagnostic.message
                == "diagnostic error limit of 3 reached; 3 additional error(s) suppressed"
    }));
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.severity == Severity::Warning && diagnostic.message == "context warning"
    }));
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
fn service_executes_explicit_generic_callable_applications() {
    let source =
        "pub fn identity<T>(value: T) -> T { value } pub fn main() -> i64 { identity<i64>(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_instantiates_non_type_direct_callable_arguments_at_the_contract_boundary() {
    for source in [
        "pub fn region<'a>() -> i64 { 0 } pub fn main() -> i64 { region<'static>() }",
        "pub fn row<e: EffectRow>() -> i64 { 0 } pub fn main() -> i64 { row<{}>() }",
        "pub fn count<n: u32>() -> i64 { 0 } pub fn main() -> i64 { count<3>() }",
        "pub fn amount<q: Quantity>() -> i64 { 0 } pub fn main() -> i64 { amount<[1, 2]>() }",
    ] {
        let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
        assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
        assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 0);
    }
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
fn service_uses_implementation_where_bounds_while_type_checking_method_bodies() {
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } trait Relay<T> { fn relay(value: T) -> T; } impl<T> Relay<T> for i64 where T: Mark { fn relay(value: T) -> T { requires_mark(value) } } impl Mark for i64 {} pub fn main() -> i64 { Relay<i64>::relay(42) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
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
fn service_rejects_direct_qualified_trait_calls_without_a_selected_implementation() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } pub fn main() -> i64 { Increment::increment(41) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("trait call without an implementation unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4169"),
        "missing selected-trait diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_overlapping_direct_qualified_trait_call_candidates_at_coherence() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 2 } } pub fn main() -> i64 { Increment::increment(40) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overlapping trait implementations unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3404"),
        "missing trait coherence diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_selects_trait_methods_using_the_implicit_self_receiver_type() {
    let source = "trait Increment { fn increment(value: Self) -> Self; } impl Increment for i64 { fn increment(value: Self) -> Self { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
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
    assert!(
        outcome
            .instance_graph
            .expect("selected trait method must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_materializes_selected_trait_method_values_from_callable_context() {
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn apply(function: (i64) -> i64) -> i64 { function(41) } pub fn main() -> i64 { apply(Increment::increment) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("selected trait method value must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
}

#[test]
fn service_materializes_generic_selected_trait_method_values_from_callable_context() {
    let source = "trait Replace { fn replace<T>(value: i64, replacement: T) -> T; } impl Replace for i64 { fn replace<T>(value: i64, replacement: T) -> T { replacement } } pub fn apply(function: (i64, Text) -> Text) -> Text { function(0, \"selected\") } pub fn main() -> Text { apply(Replace::replace) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_text().unwrap(), "selected");
    assert!(
        outcome
            .instance_graph
            .expect("generic selected trait method value must materialize an instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
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
fn service_executes_an_aliased_one_shot_resumption_with_vm_parity() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => { let saved = k; saved(41) } } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_keeps_a_statement_handler_alias_closed_before_later_shadowing() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let saved = k; saved(41) } }; let saved = (value: i64) -> i64 { value + 1 }; saved(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_resumes_statement_handler_residual_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => k(41) }; let saved = (value: i64) -> i64 { value + 1 }; saved(41) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_restores_statement_handler_residual_through_an_aliased_snapshot() {
    let source = "effect Ask { [1,1] ask() -> i64; } pub fn main() -> i64 { handle { let answer = Ask::ask(); answer + 1 } { Ask::ask() with k => { let saved = k; saved(41) } }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_dispatches_refutable_statement_handler_clauses_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(2) { Ask::ask(1) with k => k(40), Ask::ask(seed) with k => k(seed + 40) }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_an_affine_statement_handler_before_outer_suffix() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(_) => 41 }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_cancels_a_nested_affine_handler_without_reentering_the_outer_frame() {
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { handle Ask::ask() { Ask::ask(_) => 40 } } { Ask::ask(_) => 41 }; 42 }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_forwards_nested_statement_handler_before_outer_suffix() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0) } } { Ask::ask(value) with k => k(value + 2) }; 42 }";
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
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing declarative cancellation quantity diagnostic: {diagnostics:#?}"
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
fn service_proves_nested_enum_payload_coverage_without_a_wildcard() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } pub fn main() -> i64 { handle Packet::Data(Bit::One) { Packet::Data(Bit::Zero) => 40, Packet::Data(Bit::One) => 41, Packet::End => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_nested_tuple_bool_coverage_without_a_wildcard() {
    let source = "pub fn main() -> i64 { handle (true, false) { (true, true) => 40, (true, false) => 41, (false, true) => 42, (false, false) => 43 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_proves_record_field_coverage_without_a_wildcard() {
    let source = "pub struct Flagged { value: Bool } pub fn main() -> i64 { handle Flagged { value: false } { Flagged { value: true } => 40, Flagged { value: false } => 41 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
}

#[test]
fn service_rejects_an_unreachable_nested_completion_arm() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } pub fn main() -> i64 { handle Packet::Data(Bit::One) { Packet::Data(Bit::Zero) => 40, Packet::Data(Bit::One) => 41, Packet::Data(Bit::One) => 42, Packet::End => 43 } }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unreachable completion arm unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4168"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_discharges_an_effect_through_nested_payload_coverage() {
    let source = "pub enum Bit { Zero, One } pub enum Packet { Data(Bit), End } effect Inspect { [1,1] inspect(value: Packet) -> i64; } pub fn worker(value: Packet) -> i64 / Inspect { Inspect::inspect(value) } pub fn main() -> i64 { handle worker(Packet::Data(Bit::One)) { Inspect::inspect(Packet::Data(Bit::Zero)) => 40, Inspect::inspect(Packet::Data(Bit::One)) => 41, Inspect::inspect(Packet::End) => 42 } }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 41);
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
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Choice::second(40) { Choice::first(seed) => seed } } { Choice::second(seed) => seed + 2 } }";
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
fn service_tries_ordered_refutable_clauses_at_every_deep_one_shot_handler_layer() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { handle Ask::ask(40) { Ask::ask(0) with k => k(0), Ask::ask(2) with k => k(2) } } { Ask::ask(0) with k => k(0), Ask::ask(1) with k => k(1) } } { Ask::ask(0) with k => k(0), Ask::ask(value) with k => k(value + 2) } }";
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
        3
    );
    assert_eq!(
        entry
            .instructions
            .iter()
            .filter(|instruction| matches!(instruction, VmInstruction::Forward))
            .count(),
        2
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_specializes_refutable_direct_dispatch_with_multiple_sibling_groups() {
    let source = "effect Choice { [1,1] direct(seed: i64) -> i64; [1,1] alpha(seed: i64) -> i64; [1,1] beta(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle Choice::direct(40) { Choice::direct(0) with k => k(0), Choice::direct(1) with k => k(1), Choice::alpha(0) with k => k(0), Choice::beta(seed) with k => k(seed) } } { Choice::direct(seed) with k => k(seed + 2) } }";
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
    assert!(
        entry
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, VmInstruction::Forward))
    );
    assert_eq!(artifact.run_i64().unwrap(), 42);
}

#[test]
fn service_preserves_lexical_setup_at_every_deep_one_shot_handler_layer() {
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let outer_seed = 40; handle { let middle_seed = outer_seed; handle { let inner_seed = middle_seed; Ask::ask(inner_seed) } { Ask::ask(0) with k => k(0) } } { Ask::ask(1) with k => k(1) } } { Ask::ask(value) with k => k(value + 2) } }";
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
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
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
    let source = "effect Choice { [1,1] first(seed: i64) -> i64; [1,1] second(seed: i64) -> i64; } pub fn main() -> i64 { handle { handle { let first = Choice::first(40); Choice::second(first) } { Choice::first(0) => 0, Choice::first(value) => value + 1, Choice::second(0) => 0 } } { Choice::second(value) => value + 1 } }";
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
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5012"),
        "missing structured continuation-use diagnostic: {diagnostics:#?}"
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
fn service_reenters_a_dynamic_replayable_handler_clause_per_resume() {
    // Assignment keeps the residual off the pure Core replayer, so this
    // exercises the VM replay frame and its clause-return edge instead.
    let source = "effect Ask { [2,2] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); let mutable = value; mutable = mutable + 1; mutable } { Ask::ask(k) => k(20) + k(21) } }";
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
fn service_rejects_excessive_local_callable_use_before_mir() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn twice(function: (i64) -> i64) -> i64 { function(20) + function(21) } pub fn main() -> i64 { twice(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("twice-used exact callable unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing structured callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_multiplies_captured_callable_use_by_closure_invocations() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through_closure(function: (i64) -> i64) -> i64 { let call = (value: i64) -> i64 { function(value) }; call(20) + call(21) } pub fn main() -> i64 { through_closure(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("repeated closure capture unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing captured callable-use diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_rejects_an_unfulfilled_callable_lower_bound_on_normal_exit() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn ignores(function: (i64) -> i64) -> i64 { 42 } pub fn main() -> i64 { ignores(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("unused exact callable unexpectedly satisfied its lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing callable lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_checks_callable_lower_bounds_after_branch_hulls() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: i64, function: (i64) -> i64) -> i64 { handle value { 0 => function(41), _ => 0 } } pub fn main() -> i64 { choose(0, add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("branch-optional callable use unexpectedly satisfied an exact lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing branch-hull callable lower-bound diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_transfers_callable_obligations_through_a_typed_argument_boundary() {
    let source = "pub fn add_one(value: i64) -> i64 { value + 1 } pub fn apply(function: (i64) -> i64) -> i64 { function(41) } pub fn relay(function: (i64) -> i64) -> i64 { apply(function) } pub fn main() -> i64 { relay(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_transfers_an_exact_callable_obligation_out_of_a_tuple_field_move() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn take(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; let taken = move pair.function; taken(41) } pub fn main() -> i64 { take(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_overwriting_an_unfulfilled_aggregate_callable_obligation() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn replace(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; pair.function = (value: i64) -> i64 { value }; 0 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn main() -> i64 { replace(add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("overwriting an exact aggregate callback unexpectedly compiled");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "missing aggregate overwrite obligation diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_counts_callable_obligations_captured_through_an_aggregate_closure() {
    let source = "pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn through(function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; let call = (value: i64) -> i64 { pair.function(value) }; call(41) } pub fn main() -> i64 { through(add_one) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_checks_aggregate_callable_obligations_at_handler_branch_exits() {
    let source = "effect Pick { [0,1] pick(value: Bool) -> i64; } pub struct Pair { function: (i64) -> i64, value: i64 } pub fn add_one(value: i64) -> i64 { value + 1 } pub fn choose(value: Bool, function: (i64) -> i64) -> i64 { let pair = Pair { function: function, value: 0 }; handle Pick::pick(value) { Pick::pick(true) => pair.function(41), Pick::pick(false) => 0 } } pub fn main() -> i64 { choose(true, add_one) }";
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("handler-optional aggregate callback use unexpectedly satisfied exact lower bound");
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5011"),
        "missing aggregate handler-join obligation diagnostic: {diagnostics:#?}"
    );
}

#[test]
fn service_materializes_a_concretely_instantiated_generic_function_value() {
    let source = "pub fn identity<T>(value: T) -> T { value } pub fn apply(function: (i64) -> i64) -> i64 { function(42) } pub fn main() -> i64 { apply(identity) }";
    let outcome = StageZeroCompiler::new().compile(request(source)).unwrap();
    assert!(outcome.diagnostics.is_empty(), "{:#?}", outcome.diagnostics);
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
    assert!(
        outcome
            .instance_graph
            .expect("closed function value must discover an executable instance")
            .ordered()
            .iter()
            .any(|instance| !instance.arguments().is_empty())
    );
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
            max_instructions: 100,
            ..VmExecutionLimits::default()
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
            ..VmExecutionLimits::default()
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
            max_instructions: 2,
            ..VmExecutionLimits::default()
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
fn service_resolves_glob_imported_values_and_public_nested_reexports() {
    let root = "pub mod math; pub mod facade; use facade::*; pub fn main() -> i64 { add(40) }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                (
                    "src/math/math.glorious",
                    "pub mod nested; pub fn ignored() -> i64 { 0 }",
                ),
                (
                    "src/math/nested/nested.glorious",
                    "pub fn add(value: i64) -> i64 { value + 2 }",
                ),
                (
                    "src/facade/facade.glorious",
                    "pub use crate::math::nested::*;",
                ),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_ambiguous_glob_imported_values() {
    let root = "mod left; mod right; use left::*; use right::*; pub fn main() -> i64 { answer() }";
    let error = StageZeroCompiler::new().compile(request_with_modules(
        root,
        &[
            ("left", "pub fn answer() -> i64 { 1 }"),
            ("right", "pub fn answer() -> i64 { 2 }"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("ambiguous glob imports unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4103"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_private_glob_imports_before_body_elaboration() {
    let root = "mod outer; mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            ("src/facade/facade.glorious", "use crate::outer::hidden::*;"),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private glob import unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3326"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_public_glob_reexports_through_private_modules() {
    let root = "pub mod outer; pub mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::*;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private public glob reexport unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "{diagnostics:#?}"
    );
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
fn service_rejects_public_members_reached_through_a_private_nested_module() {
    let root = "mod outer; pub fn main() -> i64 { outer::hidden::answer() }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("private nested module unexpectedly leaked its public member")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_allows_public_nested_module_paths_end_to_end() {
    let root = "mod outer; pub fn main() -> i64 { outer::hidden::answer() }";
    let outcome = StageZeroCompiler::new()
        .compile(request_with_logical_sources(
            root,
            &[
                ("src/outer/outer.glorious", "pub mod hidden;"),
                (
                    "src/outer/hidden/hidden.glorious",
                    "pub fn answer() -> i64 { 42 }",
                ),
            ],
        ))
        .unwrap();
    assert_eq!(outcome.artifact.unwrap().run_i64().unwrap(), 42);
}

#[test]
fn service_rejects_public_reexport_of_a_private_nested_module_member() {
    let root = "mod outer; mod facade; pub fn main() -> i64 { facade::answer() }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::answer;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("public reexport unexpectedly leaked a private nested module member")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4104"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_exported_private_reexports_even_when_no_body_uses_them() {
    let root = "pub mod outer; pub mod facade; pub fn main() -> i64 { 42 }";
    let error = StageZeroCompiler::new().compile(request_with_logical_sources(
        root,
        &[
            ("src/outer/outer.glorious", "mod hidden;"),
            (
                "src/outer/hidden/hidden.glorious",
                "pub fn answer() -> i64 { 42 }",
            ),
            (
                "src/facade/facade.glorious",
                "pub use crate::outer::hidden::answer;",
            ),
        ],
    ));
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) = error else {
        panic!("invalid exported reexport unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "{diagnostics:#?}"
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
    let root = "mod math; mod util; pub fn main() -> i64 { math::add_two(util::forty()) }";
    let modules = [
        ("math", "pub fn add_two(value: i64) -> i64 { value + 2 }"),
        ("util", "pub fn forty() -> i64 { 40 }"),
    ];
    let first = StageZeroCompiler::new()
        .compile(request_with_modules(root, &modules))
        .unwrap();
    let mut reversed = request_with_modules(root, &modules);
    reversed.sources.reverse();
    let second = StageZeroCompiler::new().compile(reversed).unwrap();
    assert_eq!(first.diagnostics, second.diagnostics);
    let first = first.artifact.unwrap();
    let second = second.artifact.unwrap();
    assert_eq!(first.fingerprint(), second.fingerprint());
    assert_eq!(first.canonical_bytes(), second.canonical_bytes());
    assert_eq!(first.run_i64().unwrap(), 42);
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

#[test]
fn service_rejects_references_to_body_locals_in_returned_aggregates() {
    let source = r#"
        pub struct Pair { left: i64, right: i64 }
        pub fn bad() -> (&i64, i64) {
            let pair = Pair { left: 1, right: 2 };
            (&pair.left, pair.right)
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("body-local aggregate reference unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_rejects_closure_and_effect_payload_lifetime_escapes() {
    let closure = r#"
        pub fn bad() -> () -> &i64 {
            let value = 1;
            let loan = &value;
            () -> &i64 { loan }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(closure))
    else {
        panic!("closure borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5014"),
        "{diagnostics:#?}"
    );

    let payload = r#"
        effect Store { save(value: &i64); }
        pub fn bad() -> i64 / {Store} {
            let value = 1;
            Store::save(&value);
            0
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(payload))
    else {
        panic!("effect payload borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5015"),
        "{diagnostics:#?}"
    );

    let handler = r#"
        effect Tick { tick() -> i64; }
        pub fn bad() -> &i64 / {Tick} {
            let value = 1;
            handle Tick::tick() { Tick::tick() => &value }
        }
        pub fn main() -> i64 { 0 }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(handler))
    else {
        panic!("handler result borrowing a body local unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5013"),
        "{diagnostics:#?}"
    );
}

#[test]
fn service_reports_outlives_contract_failures_before_vm_lowering() {
    let source = r#"
        pub fn needs_static(value: &'static i64) -> i64 { 0 }
        pub fn bad_return<'a>() -> &'a i64 { let value = 1; &value }
        pub fn main() -> i64 { let value = 1; needs_static(&value) }
    "#;
    let Err(grandiose_stage0::ServiceError::Failed(diagnostics)) =
        StageZeroCompiler::new().compile(request(source))
    else {
        panic!("outlives-invalid program unexpectedly compiled")
    };
    assert!(
        diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5017"),
        "{diagnostics:#?}"
    );
}
