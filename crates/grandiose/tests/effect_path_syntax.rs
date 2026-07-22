use grandiose::{
    ast::{ExprKind, Stmt, TypeSyntax, TypeSyntaxKind},
    lexer, parser,
};

fn parse(source: &str) -> grandiose::ast::Program {
    parser::parse(lexer::lex(source).unwrap()).unwrap()
}

fn application(ty: &TypeSyntax) -> (&TypeSyntax, &[TypeSyntax]) {
    let TypeSyntaxKind::Application {
        constructor,
        arguments,
        ..
    } = &ty.kind
    else {
        panic!("expected generic application: {ty:#?}")
    };
    (constructor, arguments)
}

#[test]
fn perform_and_handler_paths_retain_effect_type_arguments_with_compatibility_names() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        selected() -> i64 {
            handle perform Fail<i64>::fail(42) {
                Fail<Text>::fail(error) => 0
            }
        }
        main() -> { () }
    "#;
    let program = parse(source);
    assert_eq!(program.effect_paths.len(), 2);
    for (path, argument) in program.effect_paths.iter().zip(["i64", "Text"]) {
        let (constructor, arguments) = application(&path.effect);
        assert_eq!(constructor.simple_name(), Some("Fail"));
        assert_eq!(arguments.len(), 1);
        assert_eq!(arguments[0].simple_name(), Some(argument));
        assert_eq!(
            &source[path.effect.span.range()],
            format!("Fail<{argument}>").as_str()
        );
    }

    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!("selected body must be a block")
    };
    let Stmt::Expr(expression) = &statements[0] else {
        panic!("selected block must contain its handler expression")
    };
    let ExprKind::Handle {
        computation,
        clauses,
    } = &expression.kind
    else {
        panic!("selected expression must be a handler")
    };
    let ExprKind::Perform { effect, .. } = &computation.kind else {
        panic!("handler computation must be a perform")
    };
    assert_eq!(effect.as_ref(), "Fail");
    assert_eq!(clauses[0].effect, "Fail");
    assert_eq!(
        program.effect_path(computation.span),
        Some(&program.effect_paths[0].effect)
    );
    assert_eq!(
        program.effect_path(clauses[0].span),
        Some(&program.effect_paths[1].effect)
    );
}

#[test]
fn callable_effect_rows_already_retain_the_same_generic_type_syntax() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        forward<E>() -> / {Fail<E>} { () }
        main() -> { () }
    "#;
    let program = parse(source);
    let row = program.functions[0].outward_effects.as_ref().unwrap();
    let (constructor, arguments) = application(&row.effects[0]);
    assert_eq!(constructor.simple_name(), Some("Fail"));
    assert_eq!(arguments.len(), 1);
    assert_eq!(arguments[0].simple_name(), Some("E"));
}

#[test]
fn simple_effect_paths_remain_backward_compatible_and_gain_sidecar_syntax() {
    let source = r#"
        effect Stop { stop() -> ! }
        selected() -> i64 {
            handle perform Stop::stop() { Stop::stop() => 42 }
        }
        main() -> { () }
    "#;
    let program = parse(source);
    assert_eq!(program.effect_paths.len(), 2);
    assert!(
        program
            .effect_paths
            .iter()
            .all(|path| path.effect.simple_name() == Some("Stop"))
    );
}

#[test]
fn instantiated_perform_path_parses_inside_a_parameterized_closure() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        invoke<E, F>(error: E, body: F) -> ! / {Fail<E>}
            where F: Fn<(E), Output=!, Effects={Fail<E>}> { body(error) }
        selected() -> ! / {Fail<i64>} {
            invoke(42, { error => perform Fail<i64>::fail(error) })
        }
        main() -> { () }
    "#;
    let program = parse(source);
    assert!(program.effect_paths.iter().any(|path| {
        let (constructor, arguments) = application(&path.effect);
        constructor.simple_name() == Some("Fail")
            && arguments.first().and_then(TypeSyntax::simple_name) == Some("i64")
    }));
}
