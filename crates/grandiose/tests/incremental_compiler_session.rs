use grandiose::compiler_session::{CompilationDriver, IncrementalCompilerSession};
use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{CompileOptions, OptimizationLevel};

fn bundle(helper_body: &str, helper_result: &str) -> SourceBundle {
    SourceBundle::distributed(
        Segment::new(
            "main.glorious",
            format!(
                "helper() -> {helper_result} {{ {helper_body} }}\n\
                 untouched() -> i64 {{ 7 }}\n\
                 main() -> () {{ () }}\n"
            ),
        ),
        [],
    )
}

fn options() -> CompileOptions {
    CompileOptions {
        optimization_level: OptimizationLevel::O0,
    }
}

#[test]
fn incremental_session_reuses_only_valid_unchanged_body_inference() {
    let mut session = IncrementalCompilerSession::new();
    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    let first = session.stats();
    assert!(first.elaborated_bodies > 2, "std + user bodies: {first:?}");
    assert_eq!(first.reused_bodies, 0);
    assert!(first.lowered_mir_bodies > 2, "{first:?}");
    assert_eq!(first.reused_mir_bodies, 0);

    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    let unchanged = session.stats();
    assert_eq!(unchanged.elaborated_bodies, 0, "{unchanged:?}");
    assert_eq!(unchanged.reused_bodies, first.elaborated_bodies);
    assert_eq!(unchanged.reused_phase_artifacts, 1, "{unchanged:?}");

    session
        .compile_bundle(&bundle("2", "i64"), options())
        .unwrap();
    let one_body_changed = session.stats();
    assert_eq!(one_body_changed.reused_phase_artifacts, 0);
    assert_eq!(
        one_body_changed.elaborated_bodies, 1,
        "{one_body_changed:?}"
    );
    assert_eq!(
        one_body_changed.reused_bodies + 1,
        first.elaborated_bodies,
        "{one_body_changed:?}"
    );
    assert_eq!(
        one_body_changed.lowered_mir_bodies, 1,
        "{one_body_changed:?}"
    );
    assert_eq!(
        one_body_changed.reused_mir_bodies + 1,
        first.lowered_mir_bodies,
        "{one_body_changed:?}"
    );

    // A length-changing body edit shifts following spans. The shifted body is
    // conservatively re-elaborated rather than reusing stale typed spans.
    session
        .compile_bundle(&bundle("200", "i64"), options())
        .unwrap();
    let shifted = session.stats();
    assert!(shifted.elaborated_bodies >= 2, "{shifted:?}");

    // A signature/context change cannot reuse entries *under the new context*,
    // but must retain the prior context rather than clearing every body.
    session
        .compile_bundle(&bundle("1", "u64"), options())
        .unwrap();
    let context_changed = session.stats();
    assert_eq!(context_changed.reused_bodies, 0, "{context_changed:?}");
    assert_eq!(context_changed.elaborated_bodies, first.elaborated_bodies);

    // Returning to the original signature context with one body edit should
    // reuse its unchanged siblings from the retained namespace. This guards
    // against a context transition clearing the complete typed/MIR cache.
    session
        .compile_bundle(&bundle("3", "i64"), options())
        .unwrap();
    let returned_context = session.stats();
    assert_eq!(returned_context.reused_phase_artifacts, 0, "{returned_context:?}");
    assert!(
        returned_context.elaborated_bodies < first.elaborated_bodies,
        "a context return must not re-elaborate every body: {returned_context:?}"
    );
    assert!(returned_context.reused_bodies > 0, "{returned_context:?}");
    assert!(
        returned_context.lowered_mir_bodies < first.lowered_mir_bodies,
        "a context return must not re-lower every body: {returned_context:?}"
    );
    assert!(returned_context.reused_mir_bodies > 0, "{returned_context:?}");
}

#[test]
fn incremental_session_reuses_cleanup_mir_only_after_exact_dependency_validation() {
    let original = bundle("1", "i64");
    let edited = bundle("2", "i64");
    let mut incremental = IncrementalCompilerSession::new();

    incremental.compile_bundle(&original, options()).unwrap();
    let warm = incremental.compile_bundle(&edited, options()).unwrap();
    let stats = incremental.stats();
    assert!(
        stats.reused_cleanup_mir_bodies > 0,
        "a no-call unchanged body has no interprocedural summary dependencies: {stats:?}"
    );

    // The cache is an implementation detail at the Raw -> Cleanup boundary;
    // it must be observationally identical to a cold import/elaboration.
    let cold = IncrementalCompilerSession::new()
        .compile_bundle(&edited, options())
        .unwrap();
    assert_eq!(warm.core_fingerprint(), cold.core_fingerprint());
    assert_eq!(warm.mir_fingerprint(), cold.mir_fingerprint());
    assert_eq!(warm.artifact, cold.artifact);
}

#[test]
fn failed_revision_rolls_back_incremental_inference_transaction() {
    let mut session = IncrementalCompilerSession::new();
    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    let total = session.stats().elaborated_bodies;
    let total_mir = session.stats().lowered_mir_bodies;
    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    assert_eq!(session.stats().reused_bodies, total);

    let broken = SourceBundle::distributed(
        Segment::new("main.glorious", "helper( -> i64 { 9 }\nmain() -> () { () }"),
        [],
    );
    assert!(session.compile_bundle(&broken, options()).is_err());
    assert_eq!(session.stats().reused_bodies, 0);
    assert_eq!(session.stats().reused_mir_bodies, 0);

    // Changing only the optimizer level bypasses the exact phase cache. The
    // failed request must still leave all unoptimized per-body MIR reusable.
    session
        .compile_bundle(
            &bundle("1", "i64"),
            CompileOptions {
                optimization_level: OptimizationLevel::O1,
            },
        )
        .unwrap();
    assert_eq!(session.stats().elaborated_bodies, 0);
    assert_eq!(session.stats().reused_bodies, total);
    assert_eq!(session.stats().reused_phase_artifacts, 0);
    assert_eq!(session.stats().reused_mir_bodies, total_mir);
}

#[test]
fn incremental_o1_reuses_exact_local_optimizer_snapshots() {
    let o1 = CompileOptions {
        optimization_level: OptimizationLevel::O1,
    };
    let mut session = IncrementalCompilerSession::new();
    session.compile_bundle(&bundle("1", "i64"), o1).unwrap();

    let warm = session.compile_bundle(&bundle("2", "i64"), o1).unwrap();
    let stats = session.stats();
    assert_eq!(stats.reused_phase_artifacts, 0, "{stats:?}");
    assert!(
        stats.reused_optimizer_body_snapshots > 0,
        "unchanged O1 bodies should restore exact local snapshots: {stats:?}"
    );

    let mut ordinary = IncrementalCompilerSession::new();
    let expected = ordinary.compile_bundle(&bundle("2", "i64"), o1).unwrap();
    assert_eq!(warm.core_fingerprint(), expected.core_fingerprint());
    assert_eq!(warm.mir_fingerprint(), expected.mir_fingerprint());
    assert_eq!(warm.artifact, expected.artifact);
}

#[test]
fn verified_phase_cache_is_exact_and_compile_option_sensitive() {
    let source = bundle("1", "i64");
    let mut session = IncrementalCompilerSession::new();
    let initial = session.compile_bundle(&source, options()).unwrap();

    let cached = session.compile_bundle(&source, options()).unwrap();
    assert_eq!(session.stats().reused_phase_artifacts, 1);
    assert_eq!(cached.core_fingerprint(), initial.core_fingerprint());
    assert_eq!(cached.mir_fingerprint(), initial.mir_fingerprint());
    assert_eq!(cached.artifact, initial.artifact);

    let different_options = CompileOptions {
        optimization_level: OptimizationLevel::O1,
    };
    session.compile_bundle(&source, different_options).unwrap();
    assert_eq!(session.stats().reused_phase_artifacts, 0);
    session.compile_bundle(&source, options()).unwrap();
    assert_eq!(session.stats().reused_phase_artifacts, 1);
    assert_eq!(session.stats().reused_historical_phase_artifacts, 1);

    let same_text_in_a_different_bundle = SourceBundle::raw_for_conformance(
        Segment::new(
            "<grandiose:std>",
            grandiose::source_bundle::DISTRIBUTED_STANDARD_LIBRARY_SOURCE,
        ),
        Segment::new(
            "main.glorious",
            "helper() -> i64 { 1 }\nuntouched() -> i64 { 7 }\nmain() -> () { () }\n",
        ),
        [],
    );
    assert_eq!(same_text_in_a_different_bundle.source(), source.source());
    assert!(
        session
            .compile_bundle(&same_text_in_a_different_bundle, options())
            .is_err()
    );
    assert_eq!(session.stats().reused_phase_artifacts, 0);
}

#[test]
fn historical_phase_cache_makes_editor_undo_an_exact_verified_hit() {
    let original = bundle("1", "i64");
    let edited = bundle("2", "i64");
    let mut driver = CompilationDriver::new();

    let first = driver
        .compile_bundle_with_interfaces(&original, options())
        .unwrap();
    driver
        .compile_bundle_with_interfaces(&edited, options())
        .unwrap();
    let body_edit = driver.stats();
    assert_eq!(body_edit.frontend.lexed_segments, 1, "{body_edit:?}");
    assert_eq!(body_edit.frontend.reused_segments, 1, "{body_edit:?}");

    let restored = driver
        .compile_bundle_with_interfaces(&original, options())
        .unwrap();
    let undo = driver.stats();
    assert_eq!(undo.reused_phase_artifacts, 1, "{undo:?}");
    assert_eq!(undo.reused_historical_phase_artifacts, 1, "{undo:?}");
    assert_eq!(undo.elaborated_bodies, 0, "{undo:?}");
    assert_eq!(undo.lowered_mir_bodies, 0, "{undo:?}");
    assert_eq!(restored.interfaces.user, first.interfaces.user);
    assert_eq!(
        restored.phases.core_fingerprint(),
        first.phases.core_fingerprint()
    );
}

#[test]
fn compilation_driver_shares_frontend_work_with_interface_snapshots() {
    let first = bundle("1", "i64");
    let changed = bundle("2", "i64");
    let mut driver = CompilationDriver::new();

    let initial = driver
        .compile_bundle_with_interfaces(&first, options())
        .unwrap();
    let separately_scanned = grandiose::interface::scan_interface_bundle(&first).unwrap();
    assert_eq!(initial.interfaces.user, separately_scanned.user);
    assert_eq!(
        initial.interfaces.standard_library,
        separately_scanned.standard_library
    );
    assert!(
        initial
            .interfaces
            .user
            .declarations
            .iter()
            .any(|declaration| declaration.name == "helper")
    );
    assert_eq!(driver.stats().frontend.lexed_segments, 1);
    assert_eq!(driver.stats().frontend.reused_segments, 1);

    let cached = driver
        .compile_bundle_with_interfaces(&first, options())
        .unwrap();
    assert_eq!(driver.stats().reused_phase_artifacts, 1);
    assert_eq!(cached.interfaces.user, initial.interfaces.user);

    let edited = driver
        .compile_bundle_with_interfaces(&changed, options())
        .unwrap();
    assert_eq!(driver.stats().frontend.lexed_segments, 1);
    assert_eq!(driver.stats().frontend.reused_segments, 1);
    assert_eq!(edited.interfaces.user, initial.interfaces.user);
}
