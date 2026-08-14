use grandiose_stage0::{
    BodySyntax, DeclarationScan, ExprKind, FileKey, LexedFile, LogicalPath, PackageKey,
    PatternKind, TokenRange,
};

fn parse(source: &str) -> BodySyntax {
    let package = PackageKey("body@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    BodySyntax::parse(
        &lexed,
        source,
        TokenRange {
            start: 0,
            end: lexed.tokens.len() - 1,
        },
    )
}

#[test]
fn body_parser_keeps_operator_grouping_flat_and_contextual_blocks_deferred() {
    let body = parse("{ let value = add { 1 + 2 }; value * 3 }");
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(expressions) = &body.expression(body.root).kind else {
        panic!("expected block")
    };
    let ExprKind::Let { value, .. } = body.expression(expressions[0]).kind else {
        panic!("expected let")
    };
    let ExprKind::Call { arguments, .. } = &body.expression(value).kind else {
        panic!("expected call")
    };
    assert!(matches!(
        body.expression(arguments[0]).kind,
        ExprKind::ContextualBlock(_)
    ));
    assert!(matches!(
        body.expression(expressions[1]).kind,
        ExprKind::OperatorChain { .. }
    ));
}

#[test]
fn body_parser_marks_malformed_bodies_recovered_without_nontermination() {
    let body = parse("{ let = ; }");
    assert!(body.recovered);
    assert!(!body.diagnostics.is_empty());
}

#[test]
fn assignments_are_block_statements_with_a_required_terminator() {
    let body = parse("{ let value = 1; value = 2; value }");
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected block");
    };
    assert!(matches!(
        body.expression(values[1]).kind,
        ExprKind::Assign { .. }
    ));

    let missing_terminator = parse("{ let value = 1; value = 2 value }");
    assert!(missing_terminator.recovered);
    assert!(
        missing_terminator
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4015")
    );
}

#[test]
fn body_parser_preserves_structural_is_patterns_and_rejects_duplicate_binders() {
    let body = parse("{ subject is Result::Ok((left, right)) }");
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected block");
    };
    let ExprKind::Is { subject, pattern } = body.expression(values[0]).kind else {
        panic!("expected core is expression");
    };
    assert!(matches!(body.expression(subject).kind, ExprKind::Path(_)));
    assert!(matches!(
        body.pattern(pattern).kind,
        PatternKind::Enum { ref path, ref fields }
            if path == &vec!["Result".to_owned(), "Ok".to_owned()] && fields.len() == 1
    ));

    let duplicate = parse("{ subject is (value, value) }");
    assert!(duplicate.recovered);
    assert!(
        duplicate
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4017")
    );
}

#[test]
fn body_parser_preserves_structural_handler_arms_and_legacy_perform_spelling() {
    let body = parse(
        "{ handle perform Console::read(7) { Console::read(value) with continuation => value } }",
    );
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected block");
    };
    let ExprKind::Handle {
        computation,
        clauses,
    } = &body.expression(values[0]).kind
    else {
        panic!("expected handler expression");
    };
    assert!(matches!(
        body.expression(*computation).kind,
        ExprKind::Call { .. }
    ));
    assert_eq!(clauses.len(), 1);
    assert_eq!(clauses[0].path, ["Console", "read"]);
    assert_eq!(clauses[0].resumption.as_deref(), Some("continuation"));
}

#[test]
fn body_parser_keeps_literal_and_tuple_completion_arms_distinct_from_operations() {
    let body = parse("{ handle 1 { 1 => 2, (left, right) => left } }");
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Handle { clauses, .. } = &body.expression(values[0]).kind else {
        panic!("expected handler expression");
    };
    assert_eq!(clauses.len(), 2);
    assert!(matches!(
        body.pattern(clauses[0].completion.expect("literal completion"))
            .kind,
        PatternKind::Literal(_)
    ));
    assert!(matches!(
        body.pattern(clauses[1].completion.expect("tuple completion"))
            .kind,
        PatternKind::Tuple(_)
    ));
}

#[test]
fn body_parser_keeps_qualified_nullary_constructor_arms_as_completion_patterns() {
    let source = "{ handle Choice::Left { Choice::Left => 41, _ => 42 } }";
    let body = parse(source);
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Handle { clauses, .. } = &body.expression(values[0]).kind else {
        panic!("expected handler expression");
    };
    assert!(matches!(
        body.pattern(clauses[0].completion.expect("qualified completion"))
            .kind,
        PatternKind::Enum { ref path, ref fields }
            if path == &vec!["Choice".to_owned(), "Left".to_owned()] && fields.is_empty()
    ));
}

#[test]
fn body_parser_keeps_generic_effect_instance_arguments_on_calls_and_handlers() {
    let package = PackageKey("body-handler-generic@0.1.0".into());
    let source = "{ handle perform Fail<i64>::fail(7) { Fail<i64>::fail(error) => error } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let range = TokenRange {
        start: 0,
        end: lexed.tokens.len() - 1,
    };
    let body = BodySyntax::parse(&lexed, source, range);
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected outer block")
    };
    let ExprKind::Handle {
        computation,
        clauses,
    } = &body.expression(values[0]).kind
    else {
        panic!("expected handler")
    };
    let ExprKind::Call { callee, .. } = &body.expression(*computation).kind else {
        panic!("expected effect operation call")
    };
    assert!(matches!(
        body.expression(*callee).kind,
        ExprKind::GenericPath { ref path, ref effect_arguments, .. }
            if path == &["Fail", "fail"] && effect_arguments.len() == 1
    ));
    assert_eq!(clauses[0].path, ["Fail", "fail"]);
    assert_eq!(clauses[0].effect_arguments.len(), 1);
}

#[test]
fn body_parser_keeps_operation_generic_arguments_separate_from_effect_arguments() {
    let package = PackageKey("body-operation-generic@0.1.0".into());
    let source =
        "{ handle perform Ask<i64>::ask<Text>(\"value\") { Ask<i64>::ask<Text>(value) => value } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let range = TokenRange {
        start: 0,
        end: lexed.tokens.len() - 1,
    };
    let body = BodySyntax::parse(&lexed, source, range);
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected outer block")
    };
    let ExprKind::Handle {
        computation,
        clauses,
    } = &body.expression(values[0]).kind
    else {
        panic!("expected handler")
    };
    let ExprKind::Call { callee, .. } = &body.expression(*computation).kind else {
        panic!("expected effect operation call")
    };
    assert!(matches!(
        body.expression(*callee).kind,
        ExprKind::GenericPath {
            ref path,
            ref effect_arguments,
            ref operation_arguments,
        } if path == &["Ask", "ask"]
            && effect_arguments.len() == 1
            && operation_arguments.len() == 1
    ));
    assert_eq!(clauses[0].effect_arguments.len(), 1);
    assert_eq!(clauses[0].operation_arguments.len(), 1);
}

#[test]
fn body_parser_preserves_compact_and_typed_closure_syntax_without_elaboration() {
    let package = PackageKey("body-closures@0.1.0".into());
    let source =
        "pub fn main() { {left, right => left + right}; (value: i64) -> i64 / {Trace} { value } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let body = BodySyntax::parse(&lexed, source, scan.declarations[0].body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    assert!(body.expressions.iter().any(|expression| matches!(
        expression.kind,
        ExprKind::Closure { ref parameters, .. } if parameters == &["left", "right"]
    )));
    assert!(body.expressions.iter().any(|expression| matches!(
        expression.kind,
        ExprKind::TypedClosure { ref parameters, ref result, ref effects, .. }
            if parameters.len() == 1 && result.is_some() && effects.effects.len() == 1
    )));
}

#[test]
fn body_parser_preserves_open_effect_row_tails_in_typed_closures() {
    let package = PackageKey("body-open-closure-row@0.1.0".into());
    let source = "pub fn main() { () -> i64 / {Trace | e} { 0 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let body = BodySyntax::parse(&lexed, source, scan.declarations[0].body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    assert!(body.expressions.iter().any(|expression| matches!(
        &expression.kind,
        ExprKind::TypedClosure { effects, .. }
            if effects.effects.len() == 1 && effects.tail.as_deref() == Some("e")
    )));
}

#[test]
fn conditional_surface_syntax_desugars_to_contextual_library_calls() {
    let package = PackageKey("body-conditional@0.1.0".into());
    let source = "pub fn main() -> i64 { if(true) { 1 } else { 2 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let body = BodySyntax::parse(&lexed, source, scan.declarations[0].body.unwrap());
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("function body was not a block")
    };
    let ExprKind::Call { callee, arguments } = &body.expression(values[0]).kind else {
        panic!("conditional was not desugared to a call")
    };
    assert!(matches!(
        &body.expression(*callee).kind,
        ExprKind::Path(path) if path == &["else"]
    ));
    assert!(matches!(
        &body.expression(arguments[1]).kind,
        ExprKind::ContextualBlock(_)
    ));
    let ExprKind::Call {
        arguments: positive,
        ..
    } = &body.expression(arguments[0]).kind
    else {
        panic!("positive conditional arm was not a call")
    };
    assert!(matches!(
        &body.expression(positive[0]).kind,
        ExprKind::ContextualBlock(_)
    ));
}

#[test]
fn body_parser_preserves_array_literals_without_assigning_an_element_type() {
    let package = PackageKey("body-array@0.1.0".into());
    let source = "pub fn main() -> Array<i64> { [40, 2] }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let body = BodySyntax::parse(&lexed, source, scan.declarations[0].body.unwrap());
    let root = body.expression(body.root);
    let crate::ExprKind::Block(values) = &root.kind else {
        panic!("function body did not parse as a block")
    };
    assert!(matches!(
        body.expression(*values.last().unwrap()).kind,
        crate::ExprKind::Array(ref values) if values.len() == 2
    ));
}

#[test]
fn body_parser_preserves_prefix_operator_structure_before_fixity_elaboration() {
    let package = PackageKey("body-prefix@0.1.0".into());
    let source = "pub fn main() -> i64 { -value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let body = BodySyntax::parse(&lexed, source, scan.declarations[0].body.unwrap());
    assert!(
        body.expressions
            .iter()
            .any(|expression| matches!(expression.kind, grandiose_stage0::ExprKind::Prefix { .. }))
    );
}
