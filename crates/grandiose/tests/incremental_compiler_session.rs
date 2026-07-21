use grandiose::compiler_session::IncrementalCompilerSession;
use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{CompileOptions, OptimizationLevel};

fn bundle(helper_body: &str, helper_result: &str) -> SourceBundle {
    SourceBundle::distributed(
        Segment::new(
            "main.gr",
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

    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    let unchanged = session.stats();
    assert_eq!(unchanged.elaborated_bodies, 0, "{unchanged:?}");
    assert_eq!(unchanged.reused_bodies, first.elaborated_bodies);

    session
        .compile_bundle(&bundle("2", "i64"), options())
        .unwrap();
    let one_body_changed = session.stats();
    assert_eq!(
        one_body_changed.elaborated_bodies, 1,
        "{one_body_changed:?}"
    );
    assert_eq!(
        one_body_changed.reused_bodies + 1,
        first.elaborated_bodies,
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
    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    assert_eq!(session.stats().reused_bodies, total);

    let broken = SourceBundle::distributed(
        Segment::new("main.gr", "helper( -> i64 { 9 }\nmain() -> () { () }"),
        [],
    );
    assert!(session.compile_bundle(&broken, options()).is_err());
    assert_eq!(session.stats().reused_bodies, 0);

    session
        .compile_bundle(&bundle("1", "i64"), options())
        .unwrap();
    assert_eq!(session.stats().elaborated_bodies, 0);
    assert_eq!(session.stats().reused_bodies, total);
}
