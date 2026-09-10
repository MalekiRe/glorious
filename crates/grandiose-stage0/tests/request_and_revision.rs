use std::collections::BTreeMap;

use grandiose_stage0::{
    BootstrapLimits, BootstrapStage, CompilationMode, CompilationRequest, CompilerBuildIdentity,
    CompilerDatabase, Digest, HostImportSelector, InputError, LogicalPath, PackageKey, PrimitiveRole,
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

fn authority_tag_requests() -> (CompilationRequest, CompilationRequest) {
    let mut integer = request(vec![SourceInput::new(
        PackageKey("app@0.1.0".into()),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    )]);
    integer.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("std@0.1.0".into()),
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntCheckedDiv,
            module_path: "crate".into(),
            name: "primitive".into(),
        }],
        host_imports: vec![],
    });
    let mut float = integer.clone();
    float.runtime_manifest.as_mut().unwrap().selectors[0].role =
        PrimitiveRole::parse_selector_name("f32-add").unwrap();
    (integer, float)
}

#[test]
fn malformed_float_authority_returns_input_error_instead_of_panicking() {
    let (mut input, _) = authority_tag_requests();
    input.runtime_manifest.as_mut().unwrap().selectors[0].role = PrimitiveRole::Float(
        grandiose_stage0::runtime_manifest::FloatPrimitive::Convert {
            from: grandiose_stage0::ScalarType::F32,
            to: grandiose_stage0::ScalarType::F32,
            checked: false,
        });
    assert!(matches!(input.normalize(), Err(InputError::InvalidRuntimeManifest)));
}

#[test]
fn authority_tags_distinguish_checked_division_from_float_addition_in_world_fingerprints() {
    let (integer, float) = authority_tag_requests();
    assert_ne!(
        integer.normalize().unwrap().fingerprint,
        float.normalize().unwrap().fingerprint,
        "different runtime grants must not alias before declaration binding"
    );
}

#[test]
fn authority_tag_changes_cannot_deduplicate_distinct_revision_worlds() {
    let (integer, float) = authority_tag_requests();
    let database = CompilerDatabase::new();
    let integer_id = database.import(integer, None).unwrap();
    let float_id = database.import(float, Some(integer_id)).unwrap();
    assert_ne!(integer_id, float_id, "runtime authority is semantic world input");
    let integer = database.open(integer_id).unwrap();
    let float = database.open(float_id).unwrap();
    assert_ne!(
        integer.world().runtime_manifest.as_ref().unwrap().selectors,
        float.world().runtime_manifest.as_ref().unwrap().selectors,
        "opening the float revision must not return the old integer grant"
    );
}

#[test]
fn authority_tag_correction_invalidates_the_previous_canonical_cache_generation() {
    let (mut current, _) = authority_tag_requests();
    current.build = CompilerBuildIdentity::stage0(Digest::of_bytes(b"stage0-test"));
    assert_eq!(current.build.cache_generation, 131);
    assert_eq!(grandiose_stage0::STAGE0_CACHE_GENERATION, 131);
    let mut stale = current.clone();
    stale.build.cache_generation = 2;
    assert_ne!(
        current.normalize().unwrap().fingerprint,
        stale.normalize().unwrap().fingerprint
    );
}

#[test]
fn framed_worlds_invalidate_the_previous_canonical_cache_generation() {
    let (mut current, _) = authority_tag_requests();
    current.build = CompilerBuildIdentity::stage0(Digest::of_bytes(b"stage0-test"));
    let mut stale = current.clone();
    stale.build.cache_generation = 3;
    assert_ne!(current.normalize().unwrap().fingerprint, stale.normalize().unwrap().fingerprint);
}

#[test]
fn world_fingerprint_frames_semantic_and_codegen_option_maps_separately() {
    let (mut semantic, _) = authority_tag_requests();
    semantic.runtime_manifest = None;
    semantic.semantic_options.insert("flag".into(), "value".into());
    let mut codegen = semantic.clone();
    codegen.semantic_options.clear();
    codegen.codegen_options.insert("flag".into(), "value".into());
    assert_ne!(
        semantic.clone().normalize().unwrap().fingerprint,
        codegen.clone().normalize().unwrap().fingerprint,
        "moving a pair between distinct option maps must change the world"
    );
    let database = CompilerDatabase::new();
    let first = database.import(semantic, None).unwrap();
    let second = database.import(codegen, Some(first)).unwrap();
    assert_ne!(first, second);
}

#[test]
fn world_fingerprint_frames_capabilities_separately_from_optional_runtime_manifests() {
    let (mut capabilities, _) = authority_tag_requests();
    capabilities.runtime_manifest = None;
    capabilities.capability_manifest = vec!["runtime-manifest".into(), "std@0.1.0".into()];
    let mut runtime = capabilities.clone();
    runtime.capability_manifest.clear();
    runtime.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("std@0.1.0".into()),
        selectors: vec![], host_imports: vec![],
    });
    assert_ne!(
        capabilities.clone().normalize().unwrap().fingerprint,
        runtime.clone().normalize().unwrap().fingerprint,
        "capability strings cannot impersonate an optional manifest section"
    );
    let database = CompilerDatabase::new();
    let first = database.import(capabilities, None).unwrap();
    let second = database.import(runtime, Some(first)).unwrap();
    assert_ne!(first, second);
}

#[test]
fn world_v2_matches_an_independently_written_complete_framed_transcript() {
    let producer = Digest::of_bytes(b"v2-producer");
    let package = PackageKey("app@0.1.0".into());
    let a = SourceInput::new(package.clone(), LogicalPath::parse("src/a.glorious").unwrap(), b"".as_slice());
    let z = SourceInput::new(package, LogicalPath::parse("src/z.glorious").unwrap(), b"z()".as_slice());
    let mut input = request(vec![z.clone(), a.clone()]);
    input.build = CompilerBuildIdentity {
        compiler: producer, language_generation: 11, query_generation: 12,
        interface_generation: 13, cache_generation: 4, bytecode_generation: 15,
        verifier_generation: 16,
    };
    input.mode = CompilationMode::Bootstrap(BootstrapStage {
        ordinal: 2, producer, optimization_level: 2,
        limits: BootstrapLimits::new(4, 4096), expected_artifact: Some(producer),
    });
    input.semantic_options = BTreeMap::from([("".into(), "\0".into()), ("mode".into(), "é".into())]);
    input.codegen_options.insert("optimization-level".into(), "2".into());
    input.capability_manifest = vec!["é:io".into(), "fs.read".into()];
    input.runtime_manifest = Some(RuntimeManifestInput {
        standard_library: PackageKey("std@0.1.0".into()),
        selectors: vec![
            PrimitiveSelector { role: PrimitiveRole::IntCheckedDiv, module_path: "crate::int".into(), name: "divide".into() },
            PrimitiveSelector { role: PrimitiveRole::parse_selector_name("f32-add").unwrap(), module_path: "crate::float".into(), name: "add".into() },
        ],
        host_imports: vec![
            HostImportSelector { module_path: "crate::io".into(), name: "write".into(), capability: "fs.write".into(), symbol: "host-write".into() },
            HostImportSelector { module_path: "crate::io".into(), name: "read".into(), capability: "fs.read".into(), symbol: "host\0read".into() },
        ],
    });
    let world = input.clone().normalize().unwrap();
    // Do not call the production encoder or walk its normalized containers:
    // this transcript locks field widths, boundaries, option tags, and order.
    fn field(bytes: &mut Vec<u8>, value: impl AsRef<[u8]>) {
        let value = value.as_ref();
        bytes.extend((value.len() as u64).to_le_bytes());
        bytes.extend(value);
    }
    let mut bytes = Vec::new();
    field(&mut bytes, b"grandiose-stage0-world-v2");
    field(&mut bytes, producer.as_bytes());
    for generation in [11_u32, 12, 13, 4, 15, 16] { field(&mut bytes, generation.to_le_bytes()); }
    field(&mut bytes, [5]);
    field(&mut bytes, b"bootstrap-stage-v2");
    field(&mut bytes, 2_u32.to_le_bytes());
    field(&mut bytes, producer.as_bytes());
    field(&mut bytes, [2]);
    field(&mut bytes, 4_u32.to_le_bytes());
    field(&mut bytes, 4096_u64.to_le_bytes());
    field(&mut bytes, [1]);
    field(&mut bytes, producer.as_bytes());
    field(&mut bytes, b"app@0.1.0");
    field(&mut bytes, b"g1-vm");
    field(&mut bytes, 2_u64.to_le_bytes());
    for (source, path) in [(&a, "src/a.glorious"), (&z, "src/z.glorious")] {
        field(&mut bytes, b"app@0.1.0");
        field(&mut bytes, path);
        field(&mut bytes, source.key.0.as_bytes());
        field(&mut bytes, source.digest.as_bytes());
    }
    field(&mut bytes, 2_u64.to_le_bytes());
    for value in ["", "\0", "mode", "é"] { field(&mut bytes, value); }
    field(&mut bytes, 1_u64.to_le_bytes());
    field(&mut bytes, b"optimization-level");
    field(&mut bytes, b"2");
    field(&mut bytes, 2_u64.to_le_bytes());
    field(&mut bytes, b"fs.read");
    field(&mut bytes, "é:io");
    field(&mut bytes, [1]);
    field(&mut bytes, b"std@0.1.0");
    field(&mut bytes, 2_u64.to_le_bytes());
    field(&mut bytes, [69]);
    field(&mut bytes, b"crate::float");
    field(&mut bytes, b"add");
    field(&mut bytes, [182]);
    field(&mut bytes, b"crate::int");
    field(&mut bytes, b"divide");
    field(&mut bytes, 2_u64.to_le_bytes());
    for value in ["crate::io", "read", "fs.read", "host\0read", "crate::io", "write", "fs.write", "host-write"] {
        field(&mut bytes, value);
    }
    assert_eq!(world.fingerprint, Digest::of_bytes(&bytes));
    input.sources.reverse();
    input.capability_manifest.reverse();
    let runtime = input.runtime_manifest.as_mut().unwrap();
    runtime.selectors.reverse();
    runtime.host_imports.reverse();
    assert_eq!(world.fingerprint, input.normalize().unwrap().fingerprint);
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
fn normalization_rejects_invalid_and_colliding_dependency_source_module_aliases() {
    let root = PackageKey("app@0.1.0".into());
    let root_source = SourceInput::new(
        root.clone(),
        LogicalPath::parse("src/main.glorious").unwrap(),
        b"main() { () }".as_slice(),
    );
    let invalid = SourceInput::new(
        PackageKey("9lives@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub fn answer() { () }".as_slice(),
    );
    assert!(matches!(
        request(vec![root_source.clone(), invalid]).normalize(),
        Err(InputError::InvalidPackageModuleAlias(package)) if package.0 == "9lives@0.1.0"
    ));

    let hyphenated = SourceInput::new(
        PackageKey("math-lib@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub fn answer() { () }".as_slice(),
    );
    let underscored = SourceInput::new(
        PackageKey("math_lib@0.1.0".into()),
        LogicalPath::parse("src/lib.glorious").unwrap(),
        b"pub fn answer() { () }".as_slice(),
    );
    assert!(matches!(
        request(vec![root_source, hyphenated, underscored]).normalize(),
        Err(InputError::DuplicatePackageModuleAlias { alias, first, second })
            if alias == "math_lib"
                && first.0 == "math-lib@0.1.0"
                && second.0 == "math_lib@0.1.0"
    ));
}

#[test]
fn stage_zero_build_identity_advances_the_vm_artifact_boundary() {
    let identity = CompilerBuildIdentity::stage0(Digest::of_bytes(b"stage0-vm"));
    assert_eq!(identity.bytecode_generation, STAGE0_BYTECODE_GENERATION);
    assert_eq!(identity.verifier_generation, STAGE0_VERIFIER_GENERATION);
    assert_eq!(STAGE0_BYTECODE_GENERATION, 72);
    assert_eq!(STAGE0_VERIFIER_GENERATION, 40);
    assert_eq!(grandiose_stage0::STAGE0_CACHE_GENERATION, 131);
    assert_eq!(grandiose_stage0::vm_backend::llvm::LLVM_NATIVE_ABI_GENERATION, 13);
    assert_eq!(grandiose_stage0::STAGE0_VM_SCHEMA, 116);
    assert_eq!(grandiose_stage0::STAGE0_LANGUAGE_GENERATION, 4);
    assert_eq!(grandiose_stage0::STAGE0_INTERFACE_GENERATION, 22);

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
        host_imports: vec![],
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
