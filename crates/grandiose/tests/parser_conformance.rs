//! Parser conformance over the normative structural AST returned by
//! `parser::parse_recovering`: every normative source form has a positive
//! test, malformed forms produce deterministic diagnostics with exact spans,
//! and recovery always advances.

use grandiose::{
    ast::{ExprKind, PatternKind, Program, Stmt},
    diagnostic::Diagnostic,
    lexer, parser,
    span::Span,
};

fn parse_ok(source: &str) -> Program {
    let (program, diagnostics) = parser::parse_recovering(lexer::lex(source).unwrap());
    assert!(diagnostics.is_empty(), "{source}: {diagnostics:#?}");
    program
}

fn parse_err(source: &str) -> Vec<Diagnostic> {
    let (_, diagnostics) = parser::parse_recovering(lexer::lex(source).unwrap());
    assert!(!diagnostics.is_empty(), "{source} parsed cleanly");
    diagnostics
}

fn body_expr(program: &Program, name: &str) -> ExprKind {
    let function = program
        .functions
        .iter()
        .find(|function| function.name == name)
        .unwrap_or_else(|| panic!("no function `{name}`"));
    let ExprKind::Block(statements) = &function.body.kind else {
        panic!("function body is a block");
    };
    let Some(Stmt::Expr(expression)) = statements.last() else {
        panic!("function body ends with an expression");
    };
    expression.kind.clone()
}

#[test]
fn declaration_only_programs_parse() {
    let program = parse_ok("struct Point { x: i64, y: i64 }");
    assert_eq!(program.structs.len(), 1);
    assert!(program.functions.is_empty());
    let program = parse_ok("");
    assert!(program.functions.is_empty());
}

#[test]
fn direct_perform_handlers_allow_operation_head_elision() {
    let program = parse_ok(
        "effect Case<T> { inspect(value: T) -> !; } \
         enum Result<T, E> { Ok(T), Err(E) } \
         pick(value: Result<i64, ()>) -> i64 { \
           handle perform Case<Result<i64, ()>>::inspect(value) { \
             Result::Ok(answer) => answer, Result::Err(_) => 0 \
           } \
         }",
    );
    let ExprKind::Handle {
        computation,
        clauses,
    } = body_expr(&program, "pick")
    else {
        panic!("pick ends in a handler")
    };
    assert!(
        matches!(&computation.kind, ExprKind::Perform { effect, operation, .. }
        if effect.as_ref() == "Case" && operation.as_ref() == "inspect")
    );
    assert!(clauses.iter().all(|clause| {
        clause.effect == "Case"
            && clause.operation == "inspect"
            && matches!(
                clause.patterns.as_slice(),
                [grandiose::ast::Pattern {
                    kind: PatternKind::Variant { .. },
                    ..
                }]
            )
    }));
}

#[test]
fn numeric_source_payloads_survive_parsing_without_eager_narrowing() {
    let integer = "0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff";
    let oversized = "340282366920938463463374607431768211456";
    let float =
        "1.00000005960464477539062582718061255302767487140869206996285356581211090087890625";
    let source = format!(
        "wide() -> u128 {{ {integer} }} oversized() -> u128 {{ {oversized} }} \
         direct() -> f32 {{ {float} }} main() -> {{ () }}"
    );
    let program = parse_ok(&source);

    let integer_start = source.find(integer).unwrap();
    let integer_literal = program
        .numeric_literal(Span::new(integer_start, integer_start + integer.len()))
        .expect("wide integer token remains attached to its exact source span");
    assert_eq!(integer_literal.spelling, integer);
    assert_eq!(integer_literal.as_u128(Span::default()).unwrap(), u128::MAX);

    let oversized_start = source.find(oversized).unwrap();
    let oversized_literal = program
        .numeric_literal(Span::new(
            oversized_start,
            oversized_start + oversized.len(),
        ))
        .expect("out-of-range magnitude is preserved until contextual selection");
    assert_eq!(oversized_literal.spelling, oversized);
    assert!(oversized_literal.as_u128(Span::default()).is_err());

    let float_start = source.find(float).unwrap();
    let float_literal = program
        .numeric_literal(Span::new(float_start, float_start + float.len()))
        .expect("float token remains attached to its exact source span");
    assert_eq!(float_literal.spelling, float);
    assert_eq!(
        float_literal.as_f32(Span::default()).unwrap().to_bits(),
        0x3f80_0001
    );
    assert_eq!(
        float_literal.as_f64(Span::default()).unwrap() as f32,
        1.0,
        "the fixture distinguishes direct f32 rounding from f64-then-f32"
    );
}

#[test]
fn typed_anonymous_callables_are_distinct_from_groups_and_tuples() {
    let program = parse_ok("infixl 30 +; main() -> { (x: i64, y: i64) -> i64 { x + y } }");
    let ExprKind::TypedClosure {
        params,
        return_type,
        effectful,
        ..
    } = body_expr(&program, "main")
    else {
        panic!("expected a typed closure");
    };
    assert_eq!(params.len(), 2);
    assert_eq!(params[0].name, "x");
    assert!(return_type.is_some());
    assert!(!effectful);

    // Unit-result and effect-row signature forms.
    let program = parse_ok("main() -> { (x: i64) -> / {Console} { x } }");
    let ExprKind::TypedClosure {
        return_type,
        effectful,
        outward_effects,
        ..
    } = body_expr(&program, "main")
    else {
        panic!("expected a typed closure");
    };
    assert!(return_type.is_none());
    assert!(effectful);
    assert_eq!(outward_effects.unwrap().effects.len(), 1);

    // A parenthesized group and a tuple stay ordinary expressions.
    let program = parse_ok("main() -> { (1) }");
    assert!(matches!(body_expr(&program, "main"), ExprKind::Int(1)));
    let program = parse_ok("main() -> { (1, 2) }");
    assert!(matches!(body_expr(&program, "main"), ExprKind::Tuple(_)));
}

#[test]
fn labels_parse_as_structural_nodes() {
    let program = parse_ok("main() -> { @outer: { 1 } }");
    let ExprKind::Labeled { label, body } = body_expr(&program, "main") else {
        panic!("expected a labeled block");
    };
    assert_eq!(label.name.as_ref(), "outer");
    assert!(matches!(body.kind, ExprKind::Block(_)));

    let program = parse_ok("main() -> { label @done: i64 { 1 } }");
    let ExprKind::LabelDestination { label, ty, .. } = body_expr(&program, "main") else {
        panic!("expected a label destination");
    };
    assert_eq!(label.name.as_ref(), "done");
    assert!(ty.is_some());

    let program = parse_ok("main() -> { leave@done(42) }");
    let ExprKind::Leave { label, value } = body_expr(&program, "main") else {
        panic!("expected a leave");
    };
    assert_eq!(label.name.as_ref(), "done");
    assert!(matches!(value.unwrap().kind, ExprKind::Int(42)));

    // Labeled trailing application is a call with a labeled contextual block.
    let program = parse_ok("main() -> { loop @outer: { 1 } }");
    let ExprKind::Call(callee, args) = body_expr(&program, "main") else {
        panic!("expected a labeled trailing application");
    };
    assert!(matches!(&callee.kind, ExprKind::Variable(path) if path[0].as_ref() == "loop"));
    let ExprKind::Labeled { label, body } = &args[0].kind else {
        panic!("expected a labeled argument");
    };
    assert_eq!(label.name.as_ref(), "outer");
    assert!(matches!(body.kind, ExprKind::ContextBlock(_)));

    // A bare reference names an existing identity.
    let program = parse_ok("main() -> { retry(@outer) }");
    let ExprKind::Call(_, args) = body_expr(&program, "main") else {
        panic!("expected a call");
    };
    assert!(
        matches!(&args[0].kind, ExprKind::LabelReference(label) if label.name.as_ref() == "outer")
    );
}

#[test]
fn resumption_operations_are_structural_not_spelled_calls() {
    let program = parse_ok("main() -> { resume(k, 1) }");
    assert!(matches!(
        body_expr(&program, "main"),
        ExprKind::Resume { value: Some(_), .. }
    ));
    let program = parse_ok("main() -> { cancel(k) }");
    assert!(matches!(
        body_expr(&program, "main"),
        ExprKind::Cancel { .. }
    ));
    let program = parse_ok("main() -> { tail(k, 1) }");
    assert!(matches!(
        body_expr(&program, "main"),
        ExprKind::TailResume { value: Some(_), .. }
    ));
    let diagnostics = parse_err("main() -> { cancel(k, k) }");
    assert_eq!(diagnostics[0].title, "invalid resumption operation");
    assert_eq!(
        diagnostics[0].message,
        "`cancel` requires exactly 1 argument, found 2"
    );
}

#[test]
fn is_expressions_retain_subject_and_nested_pattern() {
    let source = "main() -> { value is Shape::Circle(radius, (x, y), Point { x: px, .. }) }";
    let program = parse_ok(source);
    let ExprKind::Is { subject, pattern } = body_expr(&program, "main") else {
        panic!("expected an is expression");
    };
    assert!(matches!(subject.kind, ExprKind::Variable(_)));
    let PatternKind::Variant { path, fields, .. } = &pattern.kind else {
        panic!("expected a variant pattern");
    };
    assert_eq!(path.segments, ["Shape", "Circle"]);
    assert_eq!(&source[path.span.range()], "Shape::Circle");
    assert!(matches!(fields[0].kind, PatternKind::Binding(_)));
    let PatternKind::Tuple { elements, rest } = &fields[1].kind else {
        panic!("expected a tuple pattern");
    };
    assert_eq!(elements.len(), 2);
    assert!(rest.is_none());
    let PatternKind::Struct {
        name,
        name_span,
        fields,
        rest,
    } = &fields[2].kind
    else {
        panic!("expected a struct pattern");
    };
    assert_eq!(name, "Point");
    assert_eq!(&source[name_span.range()], "Point");
    assert_eq!(fields[0].field, "x");
    assert!(rest.is_some());

    let diagnostics = parse_err("main() -> { x is P is Q }");
    assert!(diagnostics[0].title.contains("chained pattern test"));
}

#[test]
fn pattern_binders_and_remainders_are_validated() {
    let diagnostics = parse_err("main() -> { x is Shape::Pair(a, (b, a)) }");
    assert_eq!(diagnostics[0].title, "duplicate pattern binder");
    assert!(diagnostics[0].message.contains("binding `a`"));
    assert_eq!(diagnostics[0].related.len(), 1);

    let diagnostics = parse_err("main() -> { x is (a, .., b, ..) }");
    assert_eq!(diagnostics[0].title, "duplicate pattern remainder");

    let diagnostics = parse_err("main() -> { x is Point { .., y } }");
    assert_eq!(diagnostics[0].title, "misplaced pattern remainder");

    let diagnostics = parse_err("main() -> { x is Point { y: 1, y: 2 } }");
    assert_eq!(diagnostics[0].title, "duplicate struct pattern field");

    let program = parse_ok("main() -> { x is Shape::Circle(first, .., last) }");
    let ExprKind::Is { pattern, .. } = body_expr(&program, "main") else {
        panic!("expected an is expression");
    };
    let PatternKind::Variant { fields, rest, .. } = &pattern.kind else {
        panic!("expected a variant pattern");
    };
    assert_eq!(fields.len(), 2);
    assert_eq!(rest.expect("variant remainder").before, 1);

    let diagnostics = parse_err("main() -> { x is Shape::Circle(a, .., b, ..) }");
    assert_eq!(diagnostics[0].title, "duplicate pattern remainder");
}

#[test]
fn scalar_literal_patterns_cover_new_literal_kinds() {
    let program = parse_ok("main() -> { x is 'a' }");
    let ExprKind::Is { pattern, .. } = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(pattern.kind, PatternKind::Char('a')));
    let program = parse_ok("main() -> { x is b'A' }");
    let ExprKind::Is { pattern, .. } = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(pattern.kind, PatternKind::Byte(65)));
    let program = parse_ok("main() -> { x is 2.5 }");
    let ExprKind::Is { pattern, .. } = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(pattern.kind, PatternKind::Float(_)));
}

#[test]
fn contextual_blocks_stay_undecided_in_trailing_and_operand_positions() {
    // Trailing call block.
    let program = parse_ok("main() -> { select() { 1 } }");
    let ExprKind::Call(_, args) = body_expr(&program, "main") else {
        panic!("expected a call");
    };
    assert!(matches!(
        args.last().unwrap().kind,
        ExprKind::ContextBlock(_)
    ));

    // Operator operand block.
    let program = parse_ok("infixr 1 else; main() -> { compute() else { 0 } }");
    let ExprKind::Call(callee, args) = body_expr(&program, "main") else {
        panic!("expected the word operator call");
    };
    assert!(matches!(&callee.kind, ExprKind::Variable(path) if path[0].as_ref() == "else"));
    assert!(matches!(args[1].kind, ExprKind::ContextBlock(_)));

    // An ordinary block expression stays an eager block.
    let program = parse_ok("main() -> { let x = { 1 }; x }");
    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!();
    };
    let Stmt::Let { value, .. } = &statements[0] else {
        panic!();
    };
    assert!(matches!(value.kind, ExprKind::Block(_)));
}

#[test]
fn flat_operator_sequences_group_by_declared_fixity() {
    // A library declaration gives the operator left associativity.
    let program = parse_ok("infixl 30 -; main() -> { 1 - 2 - 3 }");
    let ExprKind::Binary { lhs, .. } = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(lhs.kind, ExprKind::Binary { .. }));

    // Declared symbolic operator, spelled as a punctuation run.
    let program = parse_ok("infixl 35 <*>; main() -> { a <*> b <*> c }");
    let ExprKind::Call(callee, args) = body_expr(&program, "main") else {
        panic!("expected operator call");
    };
    assert!(matches!(&callee.kind, ExprKind::Variable(path) if path[0].as_ref() == "<*>"));
    assert!(matches!(&args[0].kind, ExprKind::Call(_, _)));

    // Right associativity.
    let program = parse_ok("infixr 30 cons; main() -> { a cons b cons c }");
    let ExprKind::Call(_, args) = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(&args[1].kind, ExprKind::Call(_, _)));

    // Symbolic prefix operator.
    let program = parse_ok("prefix 90 ~; main() -> { ~x }");
    let ExprKind::Call(callee, _) = body_expr(&program, "main") else {
        panic!();
    };
    assert!(matches!(&callee.kind, ExprKind::Variable(path) if path[0].as_ref() == "~"));

    // Operators are ordinary names: an undeclared adjacent run is atomic and
    // is not an operator, so the leftover tokens are diagnosed.
    let diagnostics = parse_err("main() -> { a ==- b }");
    assert!(!diagnostics.is_empty());
}

#[test]
fn mixed_associativity_and_nonassociative_chains_are_diagnosed() {
    let diagnostics =
        parse_err("infixl 7 plusish; infixr 7 minusish; main() -> { a plusish b minusish c }");
    let conflict = &diagnostics[0];
    assert_eq!(conflict.title, "mixed operator associativity");
    assert_eq!(
        conflict.related.len(),
        2,
        "both declaration sites: {conflict:#?}"
    );

    let diagnostics = parse_err("infix 9 veq; main() -> { a veq b veq c }");
    let chained = &diagnostics[0];
    assert_eq!(chained.title, "chained nonassociative operators");
    assert!(!chained.related.is_empty());
}

#[test]
fn fixity_redeclaration_of_a_declared_operator_is_diagnosed_with_both_sites() {
    let diagnostics = parse_err("infixl 5 dot; infixr 6 dot; main() -> { () }");
    let duplicate = &diagnostics[0];
    assert_eq!(duplicate.title, "operator fixity declared more than once");
    assert_eq!(duplicate.related.len(), 1);

    // A single source declaration establishes the operator's fixity.
    parse_ok("infixl 30 +; main() -> { 1 + 2 }");
}

#[test]
fn recovery_reports_every_malformed_declaration_and_always_advances() {
    let diagnostics = parse_err(
        "struct Good { x: i64 }\nstruct Bad { x: }\nenum Also { }\nbroken( -> { 1 }\nfine() -> i64 { 2 }",
    );
    assert!(diagnostics.len() >= 2, "{diagnostics:#?}");
    let (program, _) = parser::parse_recovering(
        lexer::lex(
            "struct Good { x: i64 }\nstruct Bad { x: }\nenum Also { }\nbroken( -> { 1 }\nfine() -> i64 { 2 }",
        )
        .unwrap(),
    );
    // Recovered declarations never enter the interface tables.
    assert_eq!(program.structs.len(), 1);
    assert_eq!(program.structs[0].name, "Good");
    assert_eq!(program.enums.len(), 1);
    assert!(
        program
            .functions
            .iter()
            .any(|function| function.name == "fine")
    );
    assert!(
        !program
            .functions
            .iter()
            .any(|function| function.name == "broken")
    );
}

#[test]
fn new_literal_expressions_parse_structurally() {
    let program = parse_ok("main() -> { 2.5 }");
    assert!(matches!(body_expr(&program, "main"), ExprKind::Float(_)));
    let program = parse_ok("main() -> { 'a' }");
    assert!(matches!(body_expr(&program, "main"), ExprKind::Char('a')));
    let program = parse_ok("main() -> { b'A' }");
    assert!(matches!(body_expr(&program, "main"), ExprKind::Byte(65)));
    let program = parse_ok("main() -> { b\"ok\" }");
    assert!(matches!(
        body_expr(&program, "main"),
        ExprKind::ByteString(_)
    ));
    let program = parse_ok("infixl 30 +; main() -> { 0xFF + 0b1_01 }");
    assert!(matches!(
        body_expr(&program, "main"),
        ExprKind::Binary { .. }
    ));
}

#[test]
fn parse_preserves_structural_resumptions_and_context_blocks() {
    let source = "main() -> { resume(k, 1); cancel(k); tail(k, 2); select() { 2 } }";
    let (program, diagnostics) = parser::parse_recovering(lexer::lex(source).unwrap());
    assert!(diagnostics.is_empty());
    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!();
    };
    let Stmt::Expr(first) = &statements[0] else {
        panic!();
    };
    let ExprKind::Resume { value, .. } = &first.kind else {
        panic!("resume must remain structural");
    };
    assert!(value.is_some());
    let Stmt::Expr(third) = &statements[2] else {
        panic!();
    };
    let ExprKind::TailResume { value, .. } = &third.kind else {
        panic!("tail resume must remain structural");
    };
    assert!(value.is_some());
    let Stmt::Expr(fourth) = &statements[3] else {
        panic!();
    };
    let ExprKind::Call(_, args) = &fourth.kind else {
        panic!();
    };
    assert!(matches!(
        args.last().unwrap().kind,
        ExprKind::ContextBlock(_)
    ));
}

#[test]
fn spans_are_exact_for_new_syntax_nodes() {
    let source = "main() -> { leave@done(42) }";
    let program = parse_ok(source);
    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!();
    };
    let Stmt::Expr(leave) = &statements[0] else {
        panic!();
    };
    assert_eq!(&source[leave.span.start..leave.span.end], "leave@done(42)");
    let ExprKind::Leave { label, .. } = &leave.kind else {
        panic!();
    };
    assert_eq!(&source[label.span.start..label.span.end], "@done");

    let source = "main() -> { subject is Point { x, .. } }";
    let program = parse_ok(source);
    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!();
    };
    let Stmt::Expr(test) = &statements[0] else {
        panic!();
    };
    assert_eq!(
        &source[test.span.start..test.span.end],
        "subject is Point { x, .. }"
    );
    let ExprKind::Is { pattern, .. } = &test.kind else {
        panic!();
    };
    assert_eq!(
        &source[pattern.span.start..pattern.span.end],
        "Point { x, .. }"
    );
}

/// Arbitrary token streams cannot hang the parser: recovery always advances.
#[test]
fn arbitrary_sources_never_hang_the_parser() {
    let fragments = [
        "struct", "enum", "impl", "{", "}", "(", ")", "->", "=>", "::", ";", ",", "let", "=",
        "handle", "perform", "resume", "@x", "@x:", "label", "leave", "is", "..", "1", "\"s\"",
        "'c'", "b'0'", "2.5", "name", "<*>", "+", "|", "&", "where", "for", "<", ">", "[", "]",
    ];
    let mut state = 0x9E3779B97F4A7C15u64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..500 {
        let length = (next() % 40) as usize;
        let source = (0..length)
            .map(|_| fragments[(next() % fragments.len() as u64) as usize])
            .collect::<Vec<_>>()
            .join(" ");
        if let Ok(tokens) = lexer::lex(&source) {
            let _ = parser::parse_recovering(tokens);
        }
    }
}
