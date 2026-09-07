//! Observable Stage0 retention contracts from self-hosted compiler docs 02
//! sections 28 and 37.6.  These deliberately use only public inspection and
//! request APIs: allocator details and transient body arenas stay private.

use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, CompilerDatabase, Digest,
    LogicalPath, PackageKey, PackageSessionStatus, RetentionReport, RevisionError, SourceInput,
    StageZeroCompiler,
};

fn request(source: &str) -> CompilationRequest {
    CompilationRequest {
        build: CompilerBuildIdentity {
            compiler: Digest::of_bytes(b"stage0-retention-tests"),
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

#[test]
fn retention_accounting_reports_exact_snapshot_and_session_pins_until_collection() {
    let database = CompilerDatabase::new();
    let revision = database
        .import(request("pub fn main() -> i64 { 42 }"), None)
        .unwrap();

    assert_eq!(
        database.retention_stats(),
        grandiose_stage0::RetentionStats {
            retained_revisions: 1,
            retired_revisions: 0,
            pinned_revisions: 0,
            snapshot_pins: 0,
        }
    );
    assert_eq!(
        database.revision_retention(revision).unwrap().snapshot_pins,
        0
    );

    let snapshot = database.open(revision).unwrap();
    let session = database.open_session(revision).unwrap();
    assert_eq!(
        database.revision_retention(revision).unwrap(),
        grandiose_stage0::RevisionRetentionMetadata {
            revision,
            retired: false,
            snapshot_pins: 2,
        },
        "one direct snapshot and one request session must be individually visible"
    );
    assert_eq!(
        database.retention_stats(),
        grandiose_stage0::RetentionStats {
            retained_revisions: 1,
            retired_revisions: 0,
            pinned_revisions: 1,
            snapshot_pins: 2,
        }
    );

    database.retire_revision(revision).unwrap();
    assert_eq!(
        database.collect_retired(),
        RetentionReport {
            collected: 0,
            retained_pinned: 1,
        },
        "retirement must retain the exact world while either lease remains live"
    );
    assert!(database.revision_retention(revision).unwrap().retired);

    drop(snapshot);
    assert_eq!(
        database.revision_retention(revision).unwrap().snapshot_pins,
        1
    );
    drop(session);
    assert_eq!(
        database.collect_retired(),
        RetentionReport {
            collected: 1,
            retained_pinned: 0,
        }
    );
    assert_eq!(database.retention_stats(), Default::default());
    assert!(matches!(
        database.revision_retention(revision),
        Err(RevisionError::UnknownRevision(found)) if found == revision
    ));
}

#[test]
fn failed_body_sessions_roll_back_all_request_local_products_before_their_pin_releases() {
    let compiler = StageZeroCompiler::new();
    let revision = compiler
        .import_revision(request("pub fn main() -> i64 { missing_name }"), None)
        .unwrap();
    let session = compiler.open_session(revision).unwrap();

    assert!(compiler.compile_session(&session).is_err());
    assert_eq!(
        session
            .package_sessions()
            .into_iter()
            .map(|entry| entry.status)
            .collect::<Vec<_>>(),
        vec![PackageSessionStatus::RolledBack; 2], // Application and distributed std.
        "a failed body must not leave staged parser, Core, PlaceFlow, or MIR state reusable"
    );
    assert_eq!(compiler.interface_cache_stats().hits, 0);
    assert_eq!(compiler.interface_cache_stats().misses, 0);
    assert!(
        compiler.dependency_traces(revision).is_empty(),
        "a failed body session must not publish a partial dependency product"
    );

    compiler.retire_revision(revision).unwrap();
    assert_eq!(compiler.collect_retired().retained_pinned, 1);
    drop(session);
    assert_eq!(compiler.collect_retired().collected, 1);
}

#[test]
fn collecting_an_unpinned_retired_parent_does_not_change_a_live_childs_vm_output() {
    let compiler = StageZeroCompiler::new();
    let parent = compiler
        .import_revision(request("pub fn main() -> i64 { 41 }"), None)
        .unwrap();
    let child = compiler
        .import_revision(request("pub fn main() -> i64 { 42 }"), Some(parent))
        .unwrap();
    let parent_session = compiler.open_session(parent).unwrap();

    let before_collection = compiler
        .compile_revision(child)
        .unwrap()
        .artifact
        .unwrap()
        .run_i64()
        .unwrap();
    assert_eq!(before_collection, 42);

    compiler.retire_revision(parent).unwrap();
    assert_eq!(
        compiler
            .compile_session(&parent_session)
            .unwrap()
            .artifact
            .unwrap()
            .run_i64()
            .unwrap(),
        41,
        "retirement cannot redirect an admitted session to its child world"
    );
    drop(parent_session);
    assert_eq!(compiler.collect_retired().collected, 1);

    let after_collection = compiler
        .compile_revision(child)
        .unwrap()
        .artifact
        .unwrap()
        .run_i64()
        .unwrap();
    assert_eq!(after_collection, before_collection);
}
