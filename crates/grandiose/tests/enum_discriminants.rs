//! Enum explicit `= <const-expr>` variant discriminants.
//!
//! The syntax is parsed, captured in the AST, and now EMITTED: a variant's
//! declared discriminant becomes its runtime tag in the bytecode (VM), while
//! pattern-match dispatch discriminates on those real tags. Ordinary enums (no
//! `= <const-expr>`) keep implicit index tags.

use grandiose::{CompileOptions, compile_source_to_bytecode_with_options};
use grandiose_vm::{Type, Value, Vm, verify};

fn compile(source: &str) -> Result<grandiose_vm::Artifact, Vec<grandiose::diagnostic::Diagnostic>> {
    compile_source_to_bytecode_with_options(
        "enum-discriminants.glorious",
        source,
        CompileOptions::default(),
    )
}

fn run_function(artifact: &grandiose_vm::Artifact, name: &str) -> Value {
    let index = artifact
        .functions
        .iter()
        .position(|f| f.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32;
    Vm::new(verify(artifact.clone()).unwrap()).run(index, vec![]).unwrap()
}

fn enum_variants<'a>(
    artifact: &'a grandiose_vm::Artifact,
    name: &'a str,
) -> &'a [grandiose_vm::bytecode::EnumVariant] {
    artifact
        .types
        .iter()
        .find_map(|descriptor| match descriptor.representation() {
            Type::Enum { name: n, variants, .. } if n == name => Some(variants),
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing enum type `{name}`"))
}

#[test]
fn explicit_discriminants_emit_real_tags_and_dispatch() {
    let source = r#"
        enum E { A = 1, B = 5 }
        pick_b() -> i64 { match E::B { E::A => 10, E::B => 20 } }
        pick_a() -> i64 { match E::A { E::A => 10, E::B => 20 } }
        main() -> { () }
    "#;
    let artifact = compile(source)
        .expect("explicit enum discriminants compile to bytecode with real tags");
    // The enum type carries the declared runtime tags, not the declaration
    // indices 0/1.
    let variants = enum_variants(&artifact, "E");
    assert_eq!(
        variants
            .iter()
            .map(|variant| (variant.name.as_str(), variant.tag))
            .collect::<Vec<_>>(),
        vec![("A", Some(1)), ("B", Some(5))],
        "explicit discriminants must be threaded into the enum type"
    );
    // The dispatcher must resolve the real runtime tags (1 for A, 5 for B).
    assert_eq!(run_function(&artifact, "pick_a"), Value::I64(10));
    assert_eq!(run_function(&artifact, "pick_b"), Value::I64(20));
}

#[test]
fn explicit_discriminants_dispatch_on_real_tags_across_variants() {
    let source = r#"
        enum Direction { North = 100, East = 200, South = 300, West = 400 }
        north() -> i64 { match Direction::North { Direction::North => 1, Direction::East => 2, Direction::South => 3, Direction::West => 4 } }
        east() -> i64 { match Direction::East { Direction::North => 1, Direction::East => 2, Direction::South => 3, Direction::West => 4 } }
        south() -> i64 { match Direction::South { Direction::North => 1, Direction::East => 2, Direction::South => 3, Direction::West => 4 } }
        west() -> i64 { match Direction::West { Direction::North => 1, Direction::East => 2, Direction::South => 3, Direction::West => 4 } }
        main() -> { () }
    "#;
    let artifact = compile(source).expect("explicit discriminants compile with wide tag spacing");
    // Distinct real tags (100/200/300/400) must dispatch to the right arms.
    assert_eq!(run_function(&artifact, "north"), Value::I64(1));
    assert_eq!(run_function(&artifact, "east"), Value::I64(2));
    assert_eq!(run_function(&artifact, "south"), Value::I64(3));
    assert_eq!(run_function(&artifact, "west"), Value::I64(4));
    let variants = enum_variants(&artifact, "Direction");
    for (index, (name, discriminant)) in
        [("North", 100u32), ("East", 200u32), ("South", 300u32), ("West", 400u32)]
            .iter()
            .enumerate()
    {
        assert_eq!(
            variants[index].discriminant(index as u32),
            *discriminant,
            "{name}"
        );
    }
}

#[test]
fn ordinary_enums_still_compile_and_use_index_tags() {
    let source = r#"
        enum E { A, B }
        pick() -> i64 { match E::B { E::A => 10, E::B => 20 } }
        main() -> { () }
    "#;
    let artifact =
        compile(source).expect("ordinary enums without explicit discriminants keep compiling");
    assert_eq!(run_function(&artifact, "pick"), Value::I64(20));
    assert!(
        enum_variants(&artifact, "E")
            .iter()
            .all(|variant| variant.tag.is_none()),
        "ordinary enums keep implicit (index) tags"
    );
}

#[test]
fn mixed_implicit_explicit_variants_continue_the_running_discriminator() {
    // C-style semantics: an unannotated variant after an explicit one continues
    // the running tag (here B follows A=3, so B gets 4).
    let source = r#"
        enum E { A = 3, B, C = 10 }
        pick_b() -> i64 { match E::B { E::A => 1, E::B => 2, E::C => 3 } }
        pick_c() -> i64 { match E::C { E::A => 1, E::B => 2, E::C => 3 } }
        main() -> { () }
    "#;
    let artifact = compile(source).expect("mixed discriminants compile");
    assert_eq!(run_function(&artifact, "pick_b"), Value::I64(2));
    assert_eq!(run_function(&artifact, "pick_c"), Value::I64(3));
    assert_eq!(
        enum_variants(&artifact, "E")
            .iter()
            .map(|variant| (variant.name.as_str(), variant.tag))
            .collect::<Vec<_>>(),
        vec![("A", Some(3)), ("B", Some(4)), ("C", Some(10))]
    );
}

#[test]
fn discriminant_equal_to_u32_max_is_rejected() {
    let err = compile("enum E { A = 4294967295 } main() -> { () }").unwrap_err();
    assert!(
        err.iter().any(|d| d.title.contains("reserved tag sentinel")),
        "{err:#?}"
    );
}
