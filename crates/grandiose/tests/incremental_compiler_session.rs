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

    // Signature/context changes invalidate every retained body inference.
    session
        .compile_bundle(&bundle("1", "u64"), options())
        .unwrap();
    let context_changed = session.stats();
    assert_eq!(context_changed.reused_bodies, 0, "{context_changed:?}");
    assert_eq!(context_changed.elaborated_bodies, first.elaborated_bodies);
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
    assert_eq!(session.stats().reused_phase_artifacts, 0);

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
    assert_eq!(driver.stats().frontend.lexed_segments, 2);

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
