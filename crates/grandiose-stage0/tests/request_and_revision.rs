use std::collections::BTreeMap;

use grandiose_stage0::{
    BootstrapLimits, BootstrapStage, CompilationMode, CompilationRequest, CompilerBuildIdentity,
    CompilerDatabase, Digest, InputError, LogicalPath, PackageKey, PrimitiveRole,
    PrimitiveSelector, RetentionReport, RevisionError, RuntimeManifestInput,
    STAGE0_BYTECODE_GENERATION, STAGE0_VERIFIER_GENERATION, SourceInput,
};

fn build_identity() -> CompilerBuildIdentity {
    CompilerBuildIdentity {
        compiler: Digest::of_bytes(b"stage0-test"),
        language_generation: 1,
        query_generation: 1,
        interface_generation: 1,
        cache_generation: 1,
        bytecode_generation: 1,
        verifier_generation: 1,
    }
}

fn request(sources: Vec<SourceInput>) -> CompilationRequest {
    CompilationRequest {
        build: build_identity(),
        mode: CompilationMode::Build,
        root_package: PackageKey("app@0.1.0".into()),
        sources,
        target: "g1-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

#[test]
fn normalization_is_independent_of_host_input_enumeration_order() {
    let package = PackageKey("app@0.1.0".into());
    let a = SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/a.glorious").unwrap(),
        b"a() { () }".as_slice(),
    );
    let b = SourceInput::new(
        package,
        LogicalPath::parse("src/b.glorious").unwrap(),
        b"b() { () }".as_slice(),
    );
    let left = request(vec![a.clone(), b.clone()]).normalize().unwrap();
    let right = request(vec![b, a]).normalize().unwrap();
    assert_eq!(left.fingerprint, right.fingerprint);
}

#[test]
fn stage_zero_build_identity_advances_the_vm_artifact_boundary() {
    let identity = CompilerBuildIdentity::stage0(Digest::of_bytes(b"stage0-vm"));
    assert_eq!(identity.bytecode_generation, STAGE0_BYTECODE_GENERATION);
    assert_eq!(identity.verifier_generation, STAGE0_VERIFIER_GENERATION);
    assert_eq!(STAGE0_BYTECODE_GENERATION, 3);
    assert_eq!(STAGE0_VERIFIER_GENERATION, 3);

    let package = PackageKey("app@0.1.0".into());
    let source = SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { 42 }".as_slice(),
    );
    let mut current = request(vec![source.clone()]);
    current.build = identity;
    let mut stale = current.clone();
    stale.build.bytecode_generation = 1;
    stale.build.verifier_generation = 1;
    assert_ne!(
        current.normalize().unwrap().fingerprint,
        stale.normalize().unwrap().fingerprint,
        "artifact-format generation must participate in the immutable world identity"
    );
}

#[test]
fn snapshots_remain_pinned_to_their_immutable_world() {
    let package = PackageKey("app@0.1.0".into());
    let first = request(vec![SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { 1 }".as_slice(),
    )]);
    let second = request(vec![SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { 2 }".as_slice(),
    )]);
    let database = CompilerDatabase::new();
    let first_id = database.import(first, None).unwrap();
    let first_snapshot = database.open(first_id).unwrap();
    let second_id = database.import(second, Some(first_id)).unwrap();
    assert_ne!(first_id, second_id);
    assert_eq!(
        first_snapshot.world().sources[0].bytes.as_ref(),
        b"main() { 1 }"
    );
    assert_eq!(database.open(second_id).unwrap().parent(), Some(first_id));
}

#[test]
fn retired_revisions_remain_coherent_while_pinned_then_collect_at_a_safe_point() {
    let package = PackageKey("app@0.1.0".into());
    let request = request(vec![SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { 42 }".as_slice(),
    )]);
    let database = CompilerDatabase::new();
    let revision = database.import(request, None).unwrap();
    let snapshot = database.open(revision).unwrap();
    database.retire_revision(revision).unwrap();
    assert!(matches!(
        database.open(revision),
        Err(RevisionError::RetiredRevision(found)) if found == revision
    ));
    assert_eq!(snapshot.world().sources[0].bytes.as_ref(), b"main() { 42 }");
    assert_eq!(
        database.collect_retired(),
        RetentionReport {
            collected: 0,
            retained_pinned: 1,
        }
    );
    drop(snapshot);
    assert_eq!(
        database.collect_retired(),
        RetentionReport {
            collected: 1,
            retained_pinned: 0,
        }
    );
    assert!(matches!(
        database.open(revision),
        Err(RevisionError::UnknownRevision(found)) if found == revision
    ));
}

#[test]
fn reimporting_a_retired_equivalent_world_creates_a_fresh_revision() {
    let package = PackageKey("app@0.1.0".into());
    let source = SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    let database = CompilerDatabase::new();
    let first = database
        .import(request(vec![source.clone()]), None)
        .unwrap();
    database.retire_revision(first).unwrap();
    let second = database.import(request(vec![source]), None).unwrap();
    assert_ne!(first, second);
    assert!(database.open(second).is_ok());
}

#[test]
fn a_digest_claim_is_verified_before_import() {
    let package = PackageKey("app@0.1.0".into());
    let mut source = SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    source.digest = Digest::of_bytes(b"wrong");
    assert!(request(vec![source]).normalize().is_err());
}

#[test]
fn runtime_manifest_selectors_are_canonical_semantic_world_inputs() {
    let package = PackageKey("app@0.1.0".into());
    let source = SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    let without_manifest = request(vec![source.clone()]).normalize().unwrap();
    let mut with_manifest = request(vec![source]);
    with_manifest.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("std@0.1.0".into()),
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::BranchBool,
            module_path: "crate".into(),
            name: "branch_bool".into(),
        }],
    });
    assert_ne!(
        without_manifest.fingerprint,
        with_manifest.normalize().unwrap().fingerprint
    );
}

#[test]
fn bootstrap_worlds_canonically_include_producer_and_enforce_fixed_bounds() {
    let package = PackageKey("compiler@0.1.0".into());
    let source = SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    let mut first = request(vec![source.clone()]);
    first.root_package = package.clone();
    first.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(2, 128),
        expected_artifact: None,
    });
    let mut second = first.clone();
    second.mode = CompilationMode::Bootstrap(BootstrapStage {
        producer: Digest::of_bytes(b"stage-one"),
        ordinal: 2,
        ..match first.mode {
            CompilationMode::Bootstrap(ref stage) => stage.clone(),
            _ => unreachable!(),
        }
    });
    assert_ne!(
        first.clone().normalize().unwrap().fingerprint,
        second.normalize().unwrap().fingerprint,
        "producer identity is part of the exact bootstrap world"
    );

    let mut bounded = first;
    bounded.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 1),
        expected_artifact: None,
    });
    assert!(matches!(
        bounded.normalize(),
        Err(InputError::BootstrapSourceLimit { .. })
    ));
}

#[test]
fn bootstrap_rejects_an_optimization_option_that_disagrees_with_its_stage_contract() {
    let package = PackageKey("compiler@0.1.0".into());
    let mut request = request(vec![SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    )]);
    request.root_package = package;
    request
        .codegen_options
        .insert("optimization-level".into(), "3".into());
    request.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 128),
        expected_artifact: None,
    });
    assert!(matches!(
        request.normalize(),
        Err(InputError::InvalidBootstrapStage { .. })
    ));
}
