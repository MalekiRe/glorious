use grandiose::{compile_source_to_bytecode, lexer, parser, validate};

fn frontend(source: &str) -> Result<(), Vec<grandiose::diagnostic::Diagnostic>> {
    let tokens = lexer::lex(source).map_err(|error| vec![error])?;
    let (program, parse_errors) = parser::parse_recovering(tokens);
    if !parse_errors.is_empty() {
        return Err(parse_errors);
    }
    validate::validate(&program)
}

fn assert_error(source: &str, code: &str, message: &str) {
    let errors = frontend(source).expect_err("invalid refinement pattern validated");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some(code) && error.message.contains(message)
        }),
        "expected {code} containing {message:?}, got {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G0126"))
    );
}

#[test]
fn nested_variant_tuple_and_struct_refinement_patterns_validate() {
    frontend(
        r#"
            struct Point { x: i64, y: i64 }
            enum Shape { Empty, One(Point), Pair((i64, i64)) }
            test(value: Shape) -> Bool {
                value is Shape::Pair((left, right))
            }
            inspect(value: Shape) -> Bool {
                value is Shape::One(Point { x, y: _, .. })
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn wildcard_and_binding_patterns_are_irrefutable_frontend_forms() {
    frontend(
        r#"
            any(value: i64) -> Bool { value is _ }
            bind(value: i64) -> Bool { value is captured }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn unknown_enum_types_and_variants_are_rejected() {
    assert_error(
        r#"
            enum Choice { Yes, No }
            test(value: Choice) -> Bool { value is Missing::Yes }
            main() -> { () }
        "#,
        "G0135",
        "not a declared enum",
    );
    assert_error(
        r#"
            enum Choice { Yes, No }
            test(value: Choice) -> Bool { value is Choice::Maybe }
            main() -> { () }
        "#,
        "G0135",
        "no variant",
    );
}

#[test]
fn enum_pattern_arity_is_exact() {
    assert_error(
        r#"
            enum Pair { Both(i64, i64) }
            test(value: Pair) -> Bool { value is Pair::Both(one) }
            main() -> { () }
        "#,
        "G0136",
        "has 2 field(s)",
    );
}

#[test]
fn struct_pattern_field_validation_is_shared_with_handlers() {
    assert_error(
        r#"
            struct Point { x: i64, y: i64 }
            test(value: Point) -> Bool { value is Point { z, .. } }
            main() -> { () }
        "#,
        "G0129",
        "no field named `z`",
    );
    assert_error(
        r#"
            test(value: i64) -> Bool { value is Missing { field, .. } }
            main() -> { () }
        "#,
        "G0135",
        "not a declared struct",
    );
}

#[test]
fn duplicate_pattern_binders_are_rejected_before_refinement_environments_exist() {
    let errors = frontend(
        r#"
            enum Pair { Both(i64, i64) }
            test(value: Pair) -> Bool { value is Pair::Both(item, item) }
            main() -> { () }
        "#,
    )
    .expect_err("duplicate refinement binders parsed");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("appears more than once")),
        "{errors:#?}"
    );
}

#[test]
fn variant_pattern_test_executes() {
    let source = r#"
        enum Choice { Yes(i64), No }
        answer() -> Bool {
            let value = Choice::Yes(42);
            value is Choice::Yes(found)
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("variant-is.gr", source).unwrap();
}

#[test]
fn positive_binder_visibility_is_branch_scoped() {
    let source = r#"
        enum Choice { Yes(i64), No }
        answer(value: Choice) -> i64 {
            if(value is Choice::Yes(found)) { found } else { 0 }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("positive-refinement-binding.gr", source).unwrap();
}

#[test]
fn negative_environment_excludes_the_tested_variant() {
    let source = r#"
        enum Choice { Yes(i64), No }
        answer(value: Choice) -> Bool {
            not(value is Choice::Yes(_))
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("negative-refinement.gr", source).unwrap();
}

#[test]
fn refinement_does_not_bypass_private_projection_or_reference_lifetimes() {
    let source = r#"
        struct Secret<'a> { private value: &'a i64 }
        inspect<'a>(secret: Secret<'a>) -> Bool {
            secret is Secret { value, .. }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("private-reference-refinement.gr", source).unwrap();
}
