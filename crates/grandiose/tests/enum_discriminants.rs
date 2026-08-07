//! Enum explicit `= <const-expr>` variant discriminants.
//!
//! The syntax is accepted by the parser and captured in the AST, but the
//! emission path that turns a declared discriminant into an explicit runtime
//! tag is not implemented yet. Until it lands, an explicit discriminant is
//! rejected at validation so the compiler never silently emits an implicit
//! index tag for a variant that declared a different discriminant.

use grandiose::{
    compile_bundle_to_bytecode,
    source_bundle::{Segment, SourceBundle},
};

fn compile(source: &str) -> Result<grandiose_vm::Artifact, Vec<grandiose::diagnostic::Diagnostic>> {
    compile_bundle_to_bytecode(&SourceBundle::raw_for_conformance(
        Segment::new("empty-std.glorious", ""),
        Segment::new("enum-discriminants.glorious", source),
        [],
    ))
}

#[test]
fn explicit_discriminant_is_rejected_until_emission_lands() {
    // Ensures we never silently emit index tags for a variant that declared an
    // explicit discriminant, while ordinary enums (no `= <const-expr>`) still
    // compile unchanged.
    let err = compile(
        "enum E { A = 1, B = 5 }\nmain() -> i64 { match E::A { E::A => 10, E::B => 20 } }",
    )
    .unwrap_err();
    assert!(
        err.iter()
            .any(|d| d.title.contains("explicit variant discriminants")),
        "{err:#?}"
    );
}

#[test]
fn ordinary_enums_still_compile() {
    let artifact = compile("enum E { A, B } main() -> { () }")
        .expect("ordinary enums without explicit discriminants keep compiling");
    // Two-variant enum emits an implicit index-based tag path.
    assert!(artifact.functions.iter().any(|f| f.name == "main"));
}
