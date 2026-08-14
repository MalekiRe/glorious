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
fn normalization_rejects_forged_file_identity_for_a_logical_source() {
    let package = PackageKey("app@0.1.0".into());
    let other = PackageKey("other@0.1.0".into());
    let mut source = SourceInput::new(
        package,
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { 42 }".as_slice(),
    );
    source.key = grandiose_stage0::FileKey::new(&other, "src/forged.glorious");
    assert!(matches!(
        request(vec![source]).normalize(),
        Err(InputError::SourceIdentityMismatch { .. })
    ));
}

#[test]
fn stage_zero_build_identity_advances_the_vm_artifact_boundary() {
    let identity = CompilerBuildIdentity::stage0(Digest::of_bytes(b"stage0-vm"));
    assert_eq!(identity.bytecode_generation, STAGE0_BYTECODE_GENERATION);
    assert_eq!(identity.verifier_generation, STAGE0_VERIFIER_GENERATION);
    assert_eq!(STAGE0_BYTECODE_GENERATION, 37);
    assert_eq!(STAGE0_VERIFIER_GENERATION, 6);

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
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::BranchBool,
                module_path: "crate".into(),
                name: "branch_bool".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextByteLen,
                module_path: "crate".into(),
                name: "__g1_text_byte_len".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextConcat,
                module_path: "crate".into(),
                name: "__g1_text_concat".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextEq,
                module_path: "crate".into(),
                name: "__g1_text_eq".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextFromUtf8Checked,
                module_path: "crate".into(),
                name: "__g1_text_from_utf8_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextAsBytes,
                module_path: "crate".into(),
                name: "__g1_text_as_bytes".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharFromU32Checked,
                module_path: "crate".into(),
                name: "__g1_char_from_u32_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharToU32,
                module_path: "crate".into(),
                name: "__g1_char_to_u32".into(),
            },
        ],
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
    first.build.compiler = Digest::of_bytes(b"rust-seed");
    first.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"rust-seed"),
        optimization_level: 2,
        limits: BootstrapLimits::new(2, 128),
        expected_artifact: None,
    });
    let mut second = first.clone();
    let stage_one_artifact = Digest::of_bytes(b"stage-one-artifact");
    second.build.compiler = stage_one_artifact;
    second.mode = CompilationMode::Bootstrap(BootstrapStage {
        producer: stage_one_artifact,
        ordinal: 2,
        expected_artifact: Some(stage_one_artifact),
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
fn bootstrap_rejects_a_non_seed_stage_without_its_exact_producer_artifact() {
    let package = PackageKey("compiler@0.1.0".into());
    let source = SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    let mut missing_predecessor = request(vec![source.clone()]);
    missing_predecessor.root_package = package.clone();
    missing_predecessor.build.compiler = Digest::of_bytes(b"unbound-stage-one");
    missing_predecessor.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"unbound-stage-one"),
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 128),
        expected_artifact: None,
    });
    assert!(matches!(
        missing_predecessor.normalize(),
        Err(InputError::InvalidBootstrapStage {
            reason: "non-seed stages must pin their predecessor artifact"
        })
    ));

    let mut substituted_producer = request(vec![source]);
    substituted_producer.root_package = package;
    substituted_producer.build.compiler = Digest::of_bytes(b"substituted-producer");
    substituted_producer.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2,
        producer: Digest::of_bytes(b"substituted-producer"),
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 128),
        expected_artifact: Some(Digest::of_bytes(b"stage-one-artifact")),
    });
    assert!(matches!(
        substituted_producer.normalize(),
        Err(InputError::InvalidBootstrapStage {
            reason: "non-seed producer must equal the pinned predecessor artifact"
        })
    ));
}

#[test]
fn bootstrap_rejects_a_stage_producer_that_does_not_name_the_actual_compiler() {
    let package = PackageKey("compiler@0.1.0".into());
    let mut request = request(vec![SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    )]);
    request.root_package = package;
    request.build.compiler = Digest::of_bytes(b"actual-stage-zero");
    request.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: Digest::of_bytes(b"forged-seed-provenance"),
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 128),
        expected_artifact: None,
    });
    assert!(matches!(
        request.normalize(),
        Err(InputError::InvalidBootstrapStage {
            reason: "bootstrap producer must match compiler build identity"
        })
    ));
}

#[test]
fn bootstrap_rejects_a_seed_stage_with_forged_predecessor_artifact_evidence() {
    let package = PackageKey("compiler@0.1.0".into());
    let seed = Digest::of_bytes(b"rust-seed");
    let mut request = request(vec![SourceInput::new(
        package.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    )]);
    request.root_package = package;
    request.build.compiler = seed;
    request.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 1,
        producer: seed,
        optimization_level: 2,
        limits: BootstrapLimits::new(1, 128),
        expected_artifact: Some(Digest::of_bytes(b"forged-stage-zero-artifact")),
    });
    assert!(matches!(
        request.normalize(),
        Err(InputError::InvalidBootstrapStage {
            reason: "seed stage must not pin a predecessor artifact"
        })
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
    request.build.compiler = Digest::of_bytes(b"rust-seed");
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
