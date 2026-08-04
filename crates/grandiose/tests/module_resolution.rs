use grandiose::{
    compile_bundle_to_bytecode,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Value, Vm, verify};

fn bundle(primary: (&str, &str), additional: &[(&str, &str)]) -> SourceBundle {
    SourceBundle::distributed(
        Segment::new(primary.0, primary.1),
        additional
            .iter()
            .map(|(name, source)| Segment::new(*name, *source)),
    )
}

fn package_bundle(
    primary: (&str, &str),
    dependencies: &[(&str, &str, &str)],
    fragments: &[(&str, &str)],
) -> SourceBundle {
    SourceBundle::distributed(
        Segment::new(primary.0, primary.1),
        dependencies
            .iter()
            .map(|(package, path, source)| Segment::new(*path, *source).with_package_root(*package))
            .chain(
                fragments
                    .iter()
                    .map(|(path, source)| Segment::new(*path, *source)),
            ),
    )
}

fn run_root_i64(bundle: &SourceBundle, function: &str) -> i64 {
    let artifact = compile_bundle_to_bytecode(bundle).expect("module fixture compiles");
    let function = artifact
        .functions
        .iter()
        .position(|candidate| candidate.name == function)
        .expect("root function remains externally addressable") as u32;
    match Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
    {
        Value::I64(value) => value,
        value => panic!("expected i64, found {value:?}"),
    }
}

#[test]
fn external_modules_resolve_from_the_crate_root_exception() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            mod math;
            use crate::math::answer as selected;
            probe() -> i64 { selected() }
            main() -> { () }
            "#,
        ),
        &[("/work/src/math/math.glorious", "pub answer() -> i64 { 42 }")],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn generic_drop_target_tracks_its_module_qualified_nominal() {
    let bundle = bundle(
        ("/work/src/main.glorious", "mod guard; main() -> { () }"),
        &[(
            "/work/src/guard/guard.glorious",
            r#"
            pub struct Guard<'a> { private value: &'a mut i64 }
            impl<'a> Drop for Guard<'a> { drop(&mut self) -> { () } }
            "#,
        )],
    );
    let parsed = grandiose::modules::parse_bundle(&bundle).unwrap();
    let resolved = grandiose::modules::resolve_program(&bundle, parsed).unwrap();
    let guard = resolved
        .program
        .structs
        .iter()
        .find(|declaration| declaration.name.contains("Guard"))
        .expect("qualified guard nominal");
    let drop = resolved
        .program
        .drops
        .iter()
        .find(|declaration| declaration.target.contains("Guard"))
        .expect("guard Drop hook");
    assert_eq!(drop.target, guard.name);
    assert_eq!(drop.target_type.simple_name(), None);
    let grandiose::ast::TypeSyntaxKind::Application { constructor, .. } = &drop.target_type.kind
    else {
        panic!("generic Drop target remains an application")
    };
    assert_eq!(constructor.simple_name(), Some(guard.name.as_str()));
}

#[test]
fn unresolved_qualified_root_call_is_rejected_during_module_resolution() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            mod frontend;
            mod backend;
            main() -> { () }
            "#,
        ),
        &[
            (
                "/work/src/frontend/frontend.glorious",
                "pub existing() -> { () }",
            ),
            ("/work/src/backend/backend.glorious", "pub mod lowering;"),
            (
                "/work/src/backend/lowering/lowering.glorious",
                r#"
                pub probe() -> {
                    super::super::frontend::missing()
                }
                "#,
            ),
        ],
    );
    let errors = compile_bundle_to_bytecode(&bundle)
        .expect_err("an unresolved root-package module call must fail during name resolution");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1MOD001")
                && error.message.contains("super::super::frontend::missing")
        }),
        "{errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G1BC001")),
        "{errors:#?}"
    );
}

#[test]
fn implicit_function_labels_follow_canonical_module_names() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            mod worker;
            use crate::worker::answer;
            probe() -> i64 {
                handle answer() {
                    Result::Ok(value) => value,
                    Result::Err(error) => error
                }
            }
            main() -> { () }
            "#,
        ),
        &[(
            "/work/src/worker/worker.glorious",
            r#"
            fail() -> Result<i64, i64> { Result::Err(42) }
            pub answer() -> Result<i64, i64> {
                let value = try(fail(), @answer);
                Result::Ok(value)
            }
            "#,
        )],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn qualified_sibling_enum_patterns_survive_completion_normalization() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            mod model;
            mod consumer;
            use consumer::inspect;
            probe() -> i64 {
                inspect(model::View::Number(42))
            }
            main() -> { () }
            "#,
        ),
        &[
            (
                "/work/src/model/model.glorious",
                r#"
                pub enum View { Number(i64) }
                impl Use<[0, *]> for View {}
                "#,
            ),
            (
                "/work/src/consumer/consumer.glorious",
                r#"
                pub inspect(value: super::model::View) -> i64 {
                    handle value {
                        super::model::View::Number(value) => value
                    }
                }
                "#,
            ),
        ],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn nested_external_and_inline_modules_use_the_logical_module_directory() {
    let bundle = bundle(
        (
            "/work/src/app.glorious",
            r#"
            mod syntax { pub mod tokens; }
            use crate::syntax::tokens::{Token, make};
            probe() -> i64 { let token = make(); let Token { value } = token; value }
            main() -> { () }
            "#,
        ),
        &[(
            "/work/src/syntax/tokens/tokens.glorious",
            r#"
            pub struct Token { value: i64 }
            pub make() -> Token { Token { value: 9 } }
            "#,
        )],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 9);
}

#[test]
fn grouped_glob_self_and_renamed_imports_are_usable() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            pub mod values;
            use crate::values::{self as source, direct as renamed, nested::*};
            probe() -> i64 { renamed() + source::offset() + extra() }
            main() -> { () }
            "#,
        ),
        &[(
            "/work/src/values/values.glorious",
            r#"
            pub direct() -> i64 { 30 }
            pub offset() -> i64 { 10 }
            pub mod nested { pub extra() -> i64 { 2 } }
            "#,
        )],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn benign_public_import_cycles_converge() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            pub mod a;
            pub mod b;
            use crate::a::from_a;
            probe() -> i64 { from_a() }
            main() -> { () }
            "#,
        ),
        &[
            (
                "/work/src/a/a.glorious",
                r#"
                pub use crate::b::from_b;
                pub from_a() -> i64 { from_b() }
                "#,
            ),
            (
                "/work/src/b/b.glorious",
                r#"
                pub use crate::a::from_a;
                pub from_b() -> i64 { 42 }
                "#,
            ),
        ],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn named_module_items_are_private_by_default() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            mod secret;
            bad() -> i64 { secret::hidden() }
            main() -> { () }
            "#,
        ),
        &[("/work/src/secret/secret.glorious", "hidden() -> i64 { 42 }")],
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
fn missing_or_orphan_external_modules_are_structured_errors() {
    let missing = bundle(
        ("/work/src/main.glorious", "mod absent; main() -> { () }"),
        &[],
    );
    let errors = compile_bundle_to_bytecode(&missing).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("absent/absent.glorious") && error.span.is_some()
        }),
        "{errors:#?}"
    );

    let orphan = bundle(
        ("/work/src/main.glorious", "mod present; main() -> { () }"),
        &[
            ("/work/src/present/present.glorious", "pub ok() -> { () }"),
            ("/work/src/orphan/orphan.glorious", "pub stray() -> { () }"),
        ],
    );
    let errors = compile_bundle_to_bytecode(&orphan).unwrap_err();
    assert!(
        errors.iter().any(|error| error.message.contains("orphan")),
        "{errors:#?}"
    );
}

#[test]
fn module_resolution_is_independent_of_supplied_segment_order() {
    let primary = (
        "/work/src/main.glorious",
        r#"
        mod left;
        mod right;
        probe() -> i64 { left::value() + right::value() }
        main() -> { () }
        "#,
    );
    let left = ("/work/src/left/left.glorious", "pub value() -> i64 { 40 }");
    let right = ("/work/src/right/right.glorious", "pub value() -> i64 { 2 }");
    let forward = compile_bundle_to_bytecode(&bundle(primary, &[left, right])).unwrap();
    let reverse = compile_bundle_to_bytecode(&bundle(primary, &[right, left])).unwrap();
    assert_eq!(forward.encode(), reverse.encode());
}

#[test]
fn fixities_are_module_scoped_and_follow_imported_operator_bindings() {
    let bundle = bundle(
        (
            "/work/src/main.glorious",
            r#"
            pub mod loose;
            pub mod tight;
            use crate::loose::join;
            loose_result() -> i64 { loose::calculate() }
            tight_result() -> i64 { tight::calculate() }
            imported_result() -> i64 { 1 join 2 * 3 }
            main() -> { () }
            "#,
        ),
        &[
            (
                "/work/src/loose/loose.glorious",
                r#"
                pub infixl 5 join;
                pub join(left: i64, right: i64) -> i64 { left - right }
                pub calculate() -> i64 { 1 join 2 * 3 }
                "#,
            ),
            (
                "/work/src/tight/tight.glorious",
                r#"
                pub infixl 50 join;
                pub join(left: i64, right: i64) -> i64 { left - right }
                pub calculate() -> i64 { 1 join 2 * 3 }
                "#,
            ),
        ],
    );
    assert_eq!(run_root_i64(&bundle, "loose_result"), -5);
    assert_eq!(run_root_i64(&bundle, "tight_result"), -3);
    assert_eq!(run_root_i64(&bundle, "imported_result"), -5);
}

#[test]
fn dependency_roots_are_explicit_packages_and_crate_is_package_local() {
    let bundle = package_bundle(
        (
            "/work/app/main.glorious",
            "use cool_pkg::answer; helper()->i64{1} probe()->i64{answer()} main()->{()}",
        ),
        &[(
            "cool-pkg",
            "/deps/cool/src/lib.glorious",
            "mod inner; helper()->i64{40} pub answer()->i64{crate::helper() + inner::two()}",
        )],
        &[("/deps/cool/src/inner/inner.glorious", "pub two()->i64{2}")],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn dependency_control_callables_and_fixities_retain_specialization_identity() {
    let bundle = package_bundle(
        (
            "/work/app/main.glorious",
            r#"
            use control::{when, otherwise};
            condition() -> Result<(), ()> { Result::Ok(()) }
            probe() -> i64 {
                let captured = 40;
                when(condition()) { captured + 2 } otherwise { 0 }
            }
            main() -> { () }
            "#,
        ),
        &[(
            "control",
            "/deps/control/src/lib.glorious",
            r#"
            pub infixr 1 otherwise;
            effect BranchCase<A, E> { inspect(value: Result<A, E>) -> !; }

            pub when<A, E, B, F>(condition: Result<A, E>, body: F) -> Result<B, E>
                where F: Fn<(), Output=B>, A: Use<[0,0]> {
                handle perform BranchCase<A, E>::inspect(condition) {
                    BranchCase<A, E>::inspect(Result::Ok(_)) => Result::Ok(body()),
                    BranchCase<A, E>::inspect(Result::Err(error)) => Result::Err(error)
                }
            }

            pub otherwise<A, E, F>(value: Result<A, E>, fallback: F) -> A
                where F: Fn<(), Output=A>, E: Use<[0,0]> {
                handle perform BranchCase<A, E>::inspect(value) {
                    BranchCase<A, E>::inspect(Result::Ok(result)) => result,
                    BranchCase<A, E>::inspect(Result::Err(_)) => fallback()
                }
            }
            "#,
        )],
        &[],
    );
    assert_eq!(run_root_i64(&bundle, "probe"), 42);
}

#[test]
fn dependency_aliases_are_valid_unique_and_do_not_disable_orphan_checks() {
    let invalid = package_bundle(
        ("/work/app/main.glorious", "main()->{()}"),
        &[("9bad", "/deps/bad/lib.glorious", "pub value()->{()}")],
        &[],
    );
    let errors = compile_bundle_to_bytecode(&invalid).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("valid identifier"))
    );

    let collision = package_bundle(
        ("/work/app/main.glorious", "main()->{()}"),
        &[
            ("same-name", "/deps/a/lib.glorious", "pub a()->{()}"),
            ("same_name", "/deps/b/lib.glorious", "pub b()->{()}"),
        ],
        &[],
    );
    let errors = compile_bundle_to_bytecode(&collision).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("both normalize"))
    );

    let orphan = package_bundle(
        ("/work/app/main.glorious", "mod declared; main()->{()}"),
        &[("dep", "/deps/dep/lib.glorious", "pub value()->{()}")],
        &[
            ("/work/app/declared/declared.glorious", "pub ok()->{()}"),
            ("/work/app/orphan/orphan.glorious", "pub stray()->{()}"),
        ],
    );
    let errors = compile_bundle_to_bytecode(&orphan).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("orphan.glorious"))
    );

    let module_collision = package_bundle(
        ("/work/app/main.glorious", "mod same_name; main()->{()}"),
        &[("same-name", "/deps/same/lib.glorious", "pub value()->{()}")],
        &[(
            "/work/app/same_name/same_name.glorious",
            "pub local()->{()}",
        )],
    );
    let errors = compile_bundle_to_bytecode(&module_collision).unwrap_err();
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("conflicts with dependency"))
    );

    let private = package_bundle(
        (
            "/work/app/main.glorious",
            "use dep::secret; main()->{secret()}",
        ),
        &[("dep", "/deps/dep/lib.glorious", "secret()->{()}")],
        &[],
    );
    let errors = compile_bundle_to_bytecode(&private).unwrap_err();
    assert!(
        errors.iter().any(|error| error.message.contains("private")),
        "{errors:#?}"
    );

    let unqualified_leak = package_bundle(
        (
            "/work/app/main.glorious",
            "use dep::answer; helper()->i64{99} probe()->i64{answer()} main()->{()}",
        ),
        &[(
            "dep",
            "/deps/dep/lib.glorious",
            "pub answer()->i64{helper()}",
        )],
        &[],
    );
    let errors = compile_bundle_to_bytecode(&unqualified_leak)
        .expect_err("a dependency must not bind an unqualified name from the application root");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("helper") || error.message.contains("call target")),
        "{errors:#?}"
    );
}
