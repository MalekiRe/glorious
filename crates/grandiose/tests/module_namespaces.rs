use grandiose::{
    compile_bundle_to_bytecode,
    interface::{InterfaceSelection, scan_interfaces},
    resolve::resolve_bundle,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::verify;

fn bundle(primary: &str, additional: &[(&str, &str)]) -> SourceBundle {
    SourceBundle::distributed(
        Segment::new("/crate/src/main.glorious", primary),
        additional
            .iter()
            .map(|(path, source)| Segment::new(*path, *source)),
    )
}

#[test]
fn types_variants_traits_impls_and_effects_cross_module_boundaries() {
    let bundle = bundle(
        r#"
        pub mod model;
        use crate::model::{Thing as ImportedThing, Choice, Marker};
        impl Marker for ImportedThing {}
        make() -> ImportedThing { ImportedThing { value: 1 } }
        choose() -> Choice { Choice::One }
        probe() -> i64 {
            handle perform crate::model::Ask::ask() {
                crate::model::Ask::ask() with k => resume(k, 42)
            }
        }
        main() -> { () }
        "#,
        &[(
            "/crate/src/model/model.glorious",
            r#"
            pub struct Thing { value: i64 }
            pub enum Choice { One, Two }
            pub trait Marker {}
            pub effect Ask { [1,1] ask() -> i64 }
            "#,
        )],
    );
    let artifact = compile_bundle_to_bytecode(&bundle).unwrap();
    verify(artifact).unwrap();
    resolve_bundle(&bundle).unwrap();
}

#[test]
fn duplicate_leaf_names_in_distinct_modules_have_distinct_identities() {
    let bundle = bundle(
        r#"
        pub mod left;
        pub mod right;
        use crate::left::Thing as LeftThing;
        use crate::right::Thing as RightThing;
        main() -> {
            let left = LeftThing { value: 1 };
            let right = RightThing { value: 2 };
            ()
        }
        "#,
        &[
            (
                "/crate/src/left/left.glorious",
                "pub struct Thing { value: i64 }",
            ),
            (
                "/crate/src/right/right.glorious",
                "pub struct Thing { value: i64 }",
            ),
        ],
    );
    let artifact = compile_bundle_to_bytecode(&bundle).unwrap();
    let names = artifact
        .types
        .iter()
        .filter_map(|ty| {
            let ty = match ty {
                grandiose_vm::Type::Restricted { base, .. } => base.as_ref(),
                ty => ty,
            };
            match ty {
                grandiose_vm::Type::Struct { name, .. } if name.contains("Thing") => Some(name),
                _ => None,
            }
        })
        .collect::<Vec<_>>();
    assert_eq!(names.len(), 2, "{names:#?}");
    assert_ne!(names[0], names[1]);
}

#[test]
fn ambiguous_globs_and_fixities_are_diagnosed_before_body_lowering() {
    let ambiguous_values = bundle(
        r#"
        pub mod left;
        pub mod right;
        use crate::left::*;
        use crate::right::*;
        bad() -> i64 { item() }
        main() -> { () }
        "#,
        &[
            ("/crate/src/left/left.glorious", "pub item() -> i64 { 1 }"),
            ("/crate/src/right/right.glorious", "pub item() -> i64 { 2 }"),
        ],
    );
    let errors = compile_bundle_to_bytecode(&ambiguous_values).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("ambiguous") && error.span.is_some()),
        "{errors:#?}"
    );

    let fixity = bundle(
        r#"
        pub mod left;
        pub mod right;
        use crate::left::*;
        use crate::right::*;
        bad() -> i64 { 1 merge 2 }
        main() -> { () }
        "#,
        &[
            (
                "/crate/src/left/left.glorious",
                "pub infixl 5 merge; pub merge(a: i64, b: i64) -> i64 { a }",
            ),
            (
                "/crate/src/right/right.glorious",
                "pub infixr 8 merge; pub merge(a: i64, b: i64) -> i64 { b }",
            ),
        ],
    );
    let errors = compile_bundle_to_bytecode(&fixity).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("fixity `merge` is ambiguous") && error.span.is_some()
        }),
        "{errors:#?}"
    );
}

#[test]
fn private_items_do_not_leak_transitively_through_sibling_modules() {
    let bundle = bundle(
        r#"
        mod outer {
            mod hidden { secret() -> i64 { 42 } }
            mod sibling { pub leak() -> i64 { super::hidden::secret() } }
        }
        main() -> { () }
        "#,
        &[],
    );
    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("private") && error.span.is_some()),
        "{errors:#?}"
    );
}

#[test]
fn duplicate_physical_module_claims_are_rejected() {
    let bundle = bundle(
        "mod value; mod value; main() -> { () }",
        &[("/crate/src/value/value.glorious", "pub get() -> i64 { 1 }")],
    );
    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("declared more than once")),
        "{errors:#?}"
    );
}

#[test]
fn interfaces_keep_structured_module_identity_and_visibility() {
    let bundle = bundle(
        "pub mod api; main() -> { () }",
        &[(
            "/crate/src/api/api.glorious",
            "pub exposed() -> i64 { 1 } hidden() -> i64 { 2 }",
        )],
    );
    let declarations = scan_interfaces(&bundle, InterfaceSelection::User).unwrap();
    let exposed = declarations
        .iter()
        .find(|declaration| declaration.name == "exposed")
        .unwrap();
    assert_eq!(exposed.module.as_deref(), Some("api"));
    assert_eq!(exposed.visibility, "public");
    assert_eq!(exposed.identity, "user:value:api::exposed");
    let hidden = declarations
        .iter()
        .find(|declaration| declaration.name == "hidden")
        .unwrap();
    assert_eq!(hidden.module.as_deref(), Some("api"));
    assert_eq!(hidden.visibility, "private");
    assert_ne!(hidden.identity, exposed.identity);
}

#[test]
fn resolved_occurrence_keys_are_exact_source_path_spans() {
    let bundle = bundle(
        r#"
        pub mod api;
        use crate::api::answer as chosen;
        probe() -> i64 { chosen() }
        main() -> { () }
        "#,
        &[("/crate/src/api/api.glorious", "pub answer() -> i64 { 42 }")],
    );
    let program = grandiose::modules::parse_bundle(&bundle).unwrap();
    let program = grandiose::parser::normalize_for_legacy_consumers(program);
    let resolved = grandiose::modules::resolve_program(&bundle, program).unwrap();
    let occurrences = resolved
        .resolution
        .resolved_paths
        .keys()
        .filter_map(|(start, end)| bundle.source().get(*start..*end))
        .collect::<Vec<_>>();
    assert!(occurrences.contains(&"chosen"), "{occurrences:#?}");
    assert!(
        occurrences.iter().all(|occurrence| {
            !occurrence.contains('(') && !occurrence.contains('{') && !occurrence.contains('<')
        }),
        "{occurrences:#?}"
    );
}

#[test]
fn is_pattern_bindings_are_scoped_to_the_positive_library_branch() {
    let positive = bundle(
        r#"
        probe(value: Result<i64, i64>) -> i64 {
            if(value is Result::Ok(found)) { found } else { 0 }
        }
        main() -> { () }
        "#,
        &[],
    );
    resolve_bundle(&positive).unwrap();

    for source in [
        r#"
        probe(value: Result<i64, i64>) -> i64 {
            if(value is Result::Ok(found)) { 1 } else { found }
        }
        main() -> { () }
        "#,
        r#"
        probe(value: Result<i64, i64>) -> i64 {
            let selected = if(value is Result::Ok(found)) { found } else { 0 };
            found
        }
        main() -> { () }
        "#,
    ] {
        let invalid = bundle(source, &[]);
        let errors = resolve_bundle(&invalid).unwrap_err();
        let unresolved = errors
            .iter()
            .find(|error| error.code.as_deref() == Some("G1R001"))
            .unwrap_or_else(|| panic!("missing resolver diagnostic: {errors:#?}"));
        let span = unresolved.span.expect("resolver diagnostic span");
        assert_eq!(&invalid.source()[span.start..span.end], "found");
    }
}
