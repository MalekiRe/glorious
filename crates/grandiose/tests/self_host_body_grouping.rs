use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    ast::{
        BinaryOp, Expr, ExprKind, FixityKind, Pattern, PatternKind, Program, Stmt, TypeSyntax,
        TypeSyntaxKind, UnaryOp,
    },
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        "mod frontend;\nmod probe;\n\nmain() { run_compiler_host(probe::bodies::application) }\n",
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/bodies/bodies.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "")
                    .replace("pub mod headers;\n", "");
            }
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn push_u32(output: &mut Vec<u8>, value: u32) {
    output.extend(value.to_le_bytes());
}

fn push_u64(output: &mut Vec<u8>, value: u64) {
    output.extend(value.to_le_bytes());
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value.as_bytes());
}

fn encode_effect_type(output: &mut Vec<u8>, source: &str, ty: &TypeSyntax) -> Result<(), ()> {
    push_string(output, &source[ty.span.range()]);
    match &ty.kind {
        TypeSyntaxKind::Path(segments) if segments.len() == 1 => {
            output.push(1);
            push_string(output, &segments[0].name);
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } if lifetime_arguments.is_empty() => {
            output.push(2);
            encode_effect_type(output, source, constructor)?;
            push_u32(output, arguments.len().try_into().map_err(|_| ())?);
            for argument in arguments {
                encode_effect_type(output, source, argument)?;
            }
        }
        _ => return Err(()),
    }
    Ok(())
}

fn binary_spelling(operator: BinaryOp) -> &'static str {
    match operator {
        BinaryOp::Add => "+",
        BinaryOp::Sub => "-",
        BinaryOp::Mul => "*",
        BinaryOp::Div => "/",
        BinaryOp::Rem => "%",
        BinaryOp::Eq => "==",
        BinaryOp::NotEq => "!=",
        BinaryOp::Lt => "<",
        BinaryOp::LtEq => "<=",
        BinaryOp::Gt => ">",
        BinaryOp::GtEq => ">=",
    }
}

fn unary_spelling(operator: UnaryOp) -> &'static str {
    match operator {
        UnaryOp::Negate => "-",
        UnaryOp::BorrowShared => "&",
        UnaryOp::BorrowUnique => "&mut",
        UnaryOp::Dereference => "*",
    }
}

fn call_operator<'a>(
    program: &'a Program,
    source: &str,
    expression: &Expr,
    callee: &'a Expr,
    arity: usize,
) -> Option<&'a str> {
    let ExprKind::Variable(path) = &callee.kind else {
        return None;
    };
    if let ([trait_name, operator], 2) = (path.as_ref(), arity)
        && matches!(
            (trait_name.as_ref(), operator.as_ref()),
            ("Add", "+") | ("Equal", "==") | ("Less", "<") | ("Greater", ">")
        )
    {
        return Some(operator);
    }
    let [operator] = path.as_ref() else {
        return None;
    };
    let fixity = program
        .fixities
        .iter()
        .find(|fixity| fixity.name == operator.as_ref())?;
    match (fixity.kind, arity) {
        (FixityKind::Infix(_), 2) if expression.span.start < callee.span.start => Some(operator),
        (FixityKind::Prefix, 1) => {
            let followed_by_call = source
                .get(callee.span.end..expression.span.end)
                .is_some_and(|tail| tail.trim_start().starts_with('('));
            (!followed_by_call).then_some(operator.as_ref())
        }
        _ => None,
    }
}

fn encode_statement(
    output: &mut Vec<u8>,
    program: &Program,
    source: &str,
    statement: &Stmt,
) -> Result<(), ()> {
    match statement {
        Stmt::Let { name, value, .. } => {
            output.push(1);
            push_string(output, name);
            encode_expression(output, program, source, value)
        }
        Stmt::Expr(expression) => {
            output.push(2);
            encode_expression(output, program, source, expression)
        }
        Stmt::Deconstruct { .. } | Stmt::Assign { .. } => Err(()),
    }
}

fn variable_named(expression: &Expr, expected: &str) -> bool {
    matches!(
        &expression.kind,
        ExprKind::Variable(path)
            if matches!(path.as_ref(), [name] if name.as_ref() == expected)
    )
}

fn single_context_expression(expression: &Expr) -> Option<&Expr> {
    let ExprKind::ContextBlock(statements) = &expression.kind else {
        return None;
    };
    let [Stmt::Expr(expression)] = statements.as_slice() else {
        return None;
    };
    Some(expression)
}

fn collect_completion_arms<'a>(
    expression: &'a Expr,
    binding: &str,
    output: &mut Vec<(&'a Pattern, &'a Expr)>,
) -> Option<()> {
    let ExprKind::Call(else_callee, else_arguments) = &expression.kind else {
        return variable_named(expression, "unreachable").then_some(());
    };
    if variable_named(else_callee, "unreachable") && else_arguments.is_empty() {
        return Some(());
    }
    if !variable_named(else_callee, "else") {
        return None;
    }
    let [conditional, negative] = else_arguments.as_slice() else {
        return None;
    };
    let ExprKind::Call(if_callee, if_arguments) = &conditional.kind else {
        return None;
    };
    if !variable_named(if_callee, "if") {
        return None;
    }
    let [condition, positive] = if_arguments.as_slice() else {
        return None;
    };
    let ExprKind::Is { subject, pattern } = &condition.kind else {
        return None;
    };
    if !variable_named(subject, binding) {
        return None;
    }
    output.push((pattern, single_context_expression(positive)?));
    collect_completion_arms(single_context_expression(negative)?, binding, output)
}

fn normalized_direct_enum_handle(expression: &Expr) -> Option<(&Expr, Vec<(&Pattern, &Expr)>)> {
    let ExprKind::Block(statements) = &expression.kind else {
        return None;
    };
    let [
        Stmt::Let {
            name,
            value: subject,
            ..
        },
        Stmt::Expr(completion),
    ] = statements.as_slice()
    else {
        return None;
    };
    if !name.starts_with("$handle$result$") {
        return None;
    }
    let mut arms = Vec::new();
    collect_completion_arms(completion, name, &mut arms)?;
    Some((subject, arms))
}

fn encode_enum_arm(
    output: &mut Vec<u8>,
    program: &Program,
    source: &str,
    pattern: &Pattern,
    body: &Expr,
) -> Result<(), ()> {
    let PatternKind::Variant {
        path,
        fields,
        rest: None,
    } = &pattern.kind
    else {
        return Err(());
    };
    let [enum_name, variant_name] = path.segments.as_slice() else {
        return Err(());
    };
    push_string(output, enum_name);
    output.push(0);
    push_string(output, variant_name);
    push_u32(output, fields.len().try_into().map_err(|_| ())?);
    for field in fields {
        match &field.kind {
            PatternKind::Wildcard => output.push(0),
            PatternKind::Binding(name) => {
                output.push(1);
                push_string(output, name);
            }
            _ => return Err(()),
        }
    }
    encode_expression(output, program, source, body)
}

fn encode_direct_enum_handle(
    output: &mut Vec<u8>,
    program: &Program,
    source: &str,
    computation: &Expr,
    arms: &[(&Pattern, &Expr)],
) -> Result<(), ()> {
    output.push(12);
    encode_expression(output, program, source, computation)?;
    push_u32(output, arms.len().try_into().map_err(|_| ())?);
    for (pattern, body) in arms {
        encode_enum_arm(output, program, source, pattern, body)?;
    }
    Ok(())
}

fn encode_effect_handle(
    output: &mut Vec<u8>,
    program: &Program,
    source: &str,
    computation: &Expr,
    clauses: &[grandiose::ast::HandlerClause],
) -> Result<(), ()> {
    output.push(12);
    encode_expression(output, program, source, computation)?;
    push_u32(output, clauses.len().try_into().map_err(|_| ())?);
    for clause in clauses {
        push_string(output, &clause.effect);
        output.push(1);
        encode_effect_type(output, source, program.effect_path(clause.span).ok_or(())?)?;
        push_string(output, &clause.operation);
        push_u32(output, clause.patterns.len().try_into().map_err(|_| ())?);
        for pattern in &clause.patterns {
            match &pattern.kind {
                PatternKind::Wildcard => output.push(0),
                PatternKind::Binding(name) => {
                    output.push(1);
                    push_string(output, name);
                }
                _ => return Err(()),
            }
        }
        let body = match (&clause.resumption, &clause.body.kind) {
            (
                Some(expected),
                ExprKind::TailResume {
                    resumption,
                    value: Some(value),
                },
            ) if matches!(
                &resumption.kind,
                ExprKind::Variable(path)
                    if matches!(path.as_ref(), [name] if name.as_ref() == expected)
            ) =>
            {
                value.as_ref()
            }
            (None, _) => &clause.body,
            _ => return Err(()),
        };
        encode_expression(output, program, source, body)?;
    }
    Ok(())
}

fn encode_pattern(output: &mut Vec<u8>, source: &str, pattern: &Pattern) -> Result<(), ()> {
    match &pattern.kind {
        PatternKind::Int(_) | PatternKind::Float(_) => {
            output.push(if matches!(&pattern.kind, PatternKind::Int(_)) {
                1
            } else {
                2
            });
            push_string(output, &source[pattern.span.range()]);
        }
        PatternKind::String(value) => {
            output.push(3);
            push_string(output, value);
        }
        PatternKind::Char(value) => {
            output.push(4);
            push_u32(output, *value as u32);
        }
        PatternKind::Byte(value) => {
            output.push(5);
            output.push(*value);
        }
        PatternKind::Unit => output.push(6),
        _ => return Err(()),
    }
    push_u32(output, pattern.span.start.try_into().map_err(|_| ())?);
    push_u32(output, pattern.span.end.try_into().map_err(|_| ())?);
    Ok(())
}

fn encode_expression(
    output: &mut Vec<u8>,
    program: &Program,
    source: &str,
    expression: &Expr,
) -> Result<(), ()> {
    push_u32(output, expression.span.start.try_into().map_err(|_| ())?);
    push_u32(output, expression.span.end.try_into().map_err(|_| ())?);
    if let Some((computation, arms)) = normalized_direct_enum_handle(expression) {
        return encode_direct_enum_handle(output, program, source, computation, &arms);
    }
    if let ExprKind::Handle {
        computation,
        clauses,
    } = &expression.kind
    {
        return encode_effect_handle(output, program, source, computation, clauses);
    }
    match &expression.kind {
        ExprKind::Variable(path) => {
            output.push(1);
            push_string(
                output,
                &path
                    .iter()
                    .map(|part| part.as_ref())
                    .collect::<Vec<_>>()
                    .join("::"),
            );
        }
        ExprKind::Int(_) => {
            let literal = program.numeric_literal(expression.span).ok_or(())?;
            let value = literal.as_u64(expression.span).map_err(|_| ())?;
            output.push(2);
            push_u64(output, value);
        }
        ExprKind::Is { subject, pattern } => {
            output.push(16);
            encode_expression(output, program, source, subject)?;
            encode_pattern(output, source, pattern)?;
        }
        ExprKind::Unit => output.push(3),
        ExprKind::Call(callee, arguments)
            if call_operator(program, source, expression, callee, arguments.len()).is_some() =>
        {
            let operator =
                call_operator(program, source, expression, callee, arguments.len()).unwrap();
            match arguments.len() {
                1 => {
                    output.push(5);
                    push_string(output, operator);
                    encode_expression(output, program, source, &arguments[0])?;
                }
                2 => {
                    output.push(6);
                    push_string(output, operator);
                    encode_expression(output, program, source, &arguments[0])?;
                    encode_expression(output, program, source, &arguments[1])?;
                }
                _ => unreachable!(),
            }
        }
        ExprKind::Binary { op, lhs, rhs } => {
            output.push(6);
            push_string(output, binary_spelling(*op));
            encode_expression(output, program, source, lhs)?;
            encode_expression(output, program, source, rhs)?;
        }
        ExprKind::Unary { op, operand } => {
            output.push(5);
            push_string(output, unary_spelling(*op));
            encode_expression(output, program, source, operand)?;
        }
        ExprKind::Call(callee, arguments) => {
            output.push(7);
            encode_expression(output, program, source, callee)?;
            push_u32(output, arguments.len().try_into().map_err(|_| ())?);
            for argument in arguments.iter() {
                encode_expression(output, program, source, argument)?;
            }
        }
        ExprKind::Perform {
            effect,
            operation,
            args,
        } => {
            output.push(14);
            push_string(output, effect);
            encode_effect_type(
                output,
                source,
                program.effect_path(expression.span).ok_or(())?,
            )?;
            push_string(output, operation);
            push_u32(output, args.len().try_into().map_err(|_| ())?);
            for argument in args.iter() {
                encode_expression(output, program, source, argument)?;
            }
        }
        ExprKind::Block(statements) => {
            output.push(8);
            push_u32(output, statements.len().try_into().map_err(|_| ())?);
            for statement in statements.iter() {
                encode_statement(output, program, source, statement)?;
            }
        }
        ExprKind::ContextBlock(statements) => {
            output.push(16);
            push_u32(output, expression.span.start.try_into().map_err(|_| ())?);
            push_u32(output, expression.span.end.try_into().map_err(|_| ())?);
            push_u32(output, statements.len().try_into().map_err(|_| ())?);
            for statement in statements.iter() {
                encode_statement(output, program, source, statement)?;
            }
        }
        ExprKind::Closure { params, body } => {
            output.push(15);
            push_u32(output, params.len().try_into().map_err(|_| ())?);
            for parameter in params.iter() {
                push_string(output, parameter);
            }
            encode_expression(output, program, source, body)?;
        }
        ExprKind::Tuple(elements) => {
            output.push(9);
            push_u32(output, elements.len().try_into().map_err(|_| ())?);
            for element in elements.iter() {
                encode_expression(output, program, source, element)?;
            }
        }
        ExprKind::Struct { name, fields } => {
            output.push(10);
            push_string(output, name);
            push_u32(output, fields.len().try_into().map_err(|_| ())?);
            for (field, value) in fields.iter() {
                push_string(output, field);
                encode_expression(output, program, source, value)?;
            }
        }
        ExprKind::Field(subject, field) => {
            output.push(11);
            encode_expression(output, program, source, subject)?;
            push_string(output, field);
        }
        _ => return Err(()),
    }
    Ok(())
}

fn raw_source_bundle(source: &str) -> SourceBundle {
    SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("<empty-std>", ""),
        Segment::new("body-grouping-input.glorious", source),
        [],
    )
}

fn encode_rust_grouping(output: &mut Vec<u8>, source: &str) {
    let bundle = raw_source_bundle(source);
    let Ok(program) = grandiose::modules::parse_bundle(&bundle) else {
        output.push(3);
        return;
    };
    let mut functions = program.functions.iter().collect::<Vec<_>>();
    functions.sort_by_key(|function| function.span.start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, functions.len().try_into().unwrap());
    for function in functions {
        push_string(&mut encoded, &function.name);
        if encode_expression(&mut encoded, &program, bundle.source(), &function.body).is_err() {
            output.push(3);
            return;
        }
    }
    output.push(0);
    output.extend(encoded);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let valid = [
        "probe_ident() { alpha }",
        "probe_u64() { 18_446_744_073_709_551_615 }",
        "probe_unit() { () }",
        "infixl 30 <+>; probe_left() { a <+> b <+> c }",
        "infixr 30 cons; probe_right() { a cons b cons c }",
        "infixl 10 low; infixl 20 high; probe_precedence() { a low b high c }",
        "infixl 10 low; infixl 20 high; probe_parentheses() { (a low b) high c }",
        "infix 10 eqish; probe_nonassoc_grouped() { (a eqish b) eqish c }",
        "prefix 90 !!; probe_prefix_nested() { !! !! value }",
        "prefix 50 neg; infixl 60 tight; infixl 40 loose; probe_prefix_precedence() { neg a tight b loose c }",
        "infixr 20 otherwise; probe_word() { first otherwise second otherwise third }",
        "infixl 35 <*>=; probe_adjacent_operator() { a <*>= b <*>= c }",
        "infixl 10 join; \
         probe_root() { a join b join c } \
         mod local { infixr 10 join; probe_local() { a join b join c } } \
         mod fallback { probe_fallback() { a join b join c } }",
        "probe_empty() {}",
        "probe_zero_call() { ping() }",
        "probe_args() { send(alpha, 42, ()) }",
        "probe_nested_call() { outer(inner(1), leaf()) }",
        "effect Signal { raise(value: u64) -> u64 } \
         probe_perform(value: u64) -> u64 / {Signal} { \
             perform Signal::raise(value) \
         }",
        "effect Signal { raise(value: u64) -> u64 } \
         probe_implicit_perform(value: u64) -> u64 / {Signal} { \
             Signal::raise(value) \
         }",
        "effect Signal { inspect(value: u64) -> u64 } \
         probe_effect_handle(value: u64) -> u64 { \
             handle perform Signal::inspect(value) { \
                 Signal::inspect(found) => found \
             } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_generic_effect_path() -> i64 { \
             handle perform Fail<i64>::fail(42) { \
                 Fail<Text>::fail(error) => 0 \
             } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_generic_effect_row<E>() -> / {Fail<E>} { () }",
        "effect Stop { stop() -> ! } \
         probe_simple_effect_path() -> i64 { \
             handle perform Stop::stop() { Stop::stop() => 42 } \
         }",
        "effect Fail<E> { fail(error: E) -> ! } \
         invoke<E, F>(error: E, body: F) -> ! / {Fail<E>} \
             where F: Fn<(E), Output=!, Effects={Fail<E>}> { body(error) } \
         probe_effect_path_closure() -> ! / {Fail<i64>} { \
             invoke(42, { error => perform Fail<i64>::fail(error) }) \
         }",
        "infixl 10 op; probe_operator_arg() { combine(a op b, c) }",
        "infixl 10 op; probe_postfix_binds() { left() op right(2) }",
        "probe_let() { let x = 1; x }",
        "probe_lets() { let x = make(); let y = combine(x, 2); finish(y) }",
        "probe_statements() { prepare(); work(1); done }",
        "probe_nested_block() { let x = { let y = 1; y }; x }",
        "probe_block_argument() { consume({ let x = 1; x }) }",
        "probe_contextual_trailing() { select() { 1 } }",
        "infixr 1 else; probe_contextual_operand() { compute() else { 0 } }",
        "probe_eager_block() { let x = { 1 }; x }",
        "probe_single_tuple() { (value,) }",
        "probe_tuple() { (first, second, third) }",
        "probe_struct() { Pair { right: second, left: first } }",
        "probe_projection() { value.field.0 }",
        "probe_variant_path() { Choice::Some(value) }",
        "probe_enum_handle() { \
            handle value { \
                Choice::Empty => 0, \
                Choice::Number(found) => found, \
                Choice::Pair(left, _) => left \
            } \
        }",
    ];
    let malformed = [
        "infixl 10 op; probe_missing_operand() { a op }",
        "infixl 10 op; probe_malformed_group() { (a op) }",
        "probe_undeclared() { a <*>= b }",
        "infixl 10 leftish; infixr 10 rightish; \
         probe_mixed() { a leftish b rightish c }",
        "infix 10 eqish; probe_nonassoc() { a eqish b eqish c }",
        "probe_bad_call() { f(, a) }",
        "probe_bad_call_separator() { f(a; b) }",
        "probe_bad_let_name() { let = 1; () }",
        "probe_bad_let_value() { let x = ; x }",
        "probe_bad_tuple() { (first, ; second) }",
        "probe_bad_struct_field() { Pair { : first } }",
        "probe_bad_struct_colon() { Pair { left first } }",
        "probe_bad_projection() { value. }",
        "probe_bad_path() { Choice::(value) }",
        "effect Signal { raise() -> u64 } \
         probe_bad_perform() -> u64 / {Signal} { perform Signal::() }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_empty_effect_arguments() -> ! { perform Fail<>::fail(1) }",
        "effect Fail<E> { fail(error: E) -> ! } \
         probe_unclosed_effect_arguments() -> ! { perform Fail<i64::fail(1) }",
        "probe_bad_closure() { consume({ value, 42 => value }) }",
    ];

    let mut paths = Vec::new();
    for (index, source) in valid.into_iter().enumerate() {
        let path = directory.join(format!("valid-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    for (index, source) in malformed.into_iter().enumerate() {
        let path = directory.join(format!("error-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }
    paths
}

fn scalar_literal_pattern_corpus(directory: &Path) -> Vec<PathBuf> {
    [
        "probe_integer() { value is 42 }",
        "probe_character() { value is 'a' }",
        "probe_text() { value is \"hello\" }",
        "probe_byte() { value is b'A' }",
        "probe_float() { value is 2.5 }",
        "probe_unit() { value is () }",
        "probe_bad_pattern() { value is }",
    ]
    .into_iter()
    .enumerate()
    .map(|(index, source)| {
        let path = directory.join(format!("scalar-{index}.glorious"));
        fs::write(&path, source).unwrap();
        path
    })
    .collect()
}

#[test]
fn rust_body_grouping_oracle_classifies_and_encodes_the_focused_corpus() {
    let directory = tempfile::tempdir().unwrap();
    let corpus = corpus(directory.path());
    for path in &corpus {
        let source = fs::read_to_string(path).unwrap();
        let mut encoded = Vec::new();
        encode_rust_grouping(&mut encoded, &source);
        let expected = if path
            .file_name()
            .unwrap()
            .to_string_lossy()
            .starts_with("valid-")
        {
            0
        } else {
            3
        };
        assert_eq!(
            encoded.first().copied(),
            Some(expected),
            "unexpected Rust-oracle status for input {}: {encoded:?}",
            path.display()
        );
    }
}

#[test]
fn self_host_body_scalar_literal_patterns_match_bootstrap_ast() {
    // The component probe carries the complete scalar-pattern wire contract.
    // Keep VM and native outputs byte-for-byte identical.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let corpus = scalar_literal_pattern_corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_grouping(&mut expected, &fs::read_to_string(path).unwrap());
            }
            fs::write(&expected_path, &expected).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let verified = verify(phases.artifact.clone()).unwrap();
            let vm = Vm::with_host(
                verified,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(
                    std::iter::once(vm_path.clone().into_os_string())
                        .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                        .collect::<Vec<_>>(),
                ),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(&vm_path).unwrap(), expected);

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("scalar-patterns.ll");
            let executable = directory.path().join("scalar-patterns");
            fs::write(&llvm, module.ir).unwrap();
            let clang = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0")
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );
            let native = Command::new(&executable)
                .arg(&directory.path().join("native.bin"))
                .args(&corpus)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            assert_eq!(
                fs::read(directory.path().join("native.bin")).unwrap(),
                expected
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_body_contextual_blocks_match_bootstrap_ast() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("contextual-blocks.glorious");
            let vm_output = directory.path().join("contextual-blocks-vm.bin");
            let native_output = directory.path().join("contextual-blocks-native.bin");
            let source = "probe_trailing() { select() { 1 } }\ninfixr 1 else; probe_operand() { compute() else { 0 } }\nprobe_eager() { let x = { 1 }; x }";
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            encode_rust_grouping(&mut expected, source);
            assert_eq!(expected.first().copied(), Some(0));

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![
                    vm_output.clone().into_os_string(),
                    input.clone().into_os_string(),
                ]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            let mut expected_one = Vec::new();
            push_u32(&mut expected_one, 1);
            expected_one.extend(&expected);
            assert_eq!(fs::read(&vm_output).unwrap(), expected_one);

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("contextual-blocks.ll");
            let executable = directory.path().join("contextual-blocks");
            fs::write(&llvm, module.ir).unwrap();
            let clang = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0")
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "{}",
                String::from_utf8_lossy(&native.stderr)
            );
            assert_eq!(fs::read(&native_output).unwrap(), expected_one);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_hosted_effect_path_syntax_and_body_grouping_match_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_BODY_GROUPING_CHECK_ONLY").is_some() {
                grandiose::compile_bundle_to_phases_with_options(
                    &self_host_bundle(),
                    CompileOptions {
                        optimization_level: OptimizationLevel::O0,
                    },
                )
                .unwrap();
                return;
            }

            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_grouping(&mut expected, &fs::read_to_string(path).unwrap());
            }
            fs::write(&expected_path, &expected).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let verified = verify(phases.artifact.clone()).unwrap();
            for (index, path) in corpus.iter().enumerate() {
                let vm_one_path = directory.path().join(format!("vm-{index}.bin"));
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        vm_one_path.clone().into_os_string(),
                        path.clone().into_os_string(),
                    ]),
                )
                .unwrap();
                assert_eq!(
                    vm.run(entry, vec![]).unwrap_or_else(|error| {
                        panic!("VM input {index} ({}) failed: {error:?}", path.display())
                    }),
                    Value::Unit
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_grouping(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&vm_one_path).unwrap(),
                    expected_one,
                    "VM body grouping diverged for input {index} ({})",
                    path.display()
                );
            }
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verified,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(
                fs::read(&vm_path).unwrap(),
                expected,
                "VM body grouping diverged"
            );

            let asan = std::env::var_os("G1_SELF_HOST_BODY_GROUPING_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-body-grouping-debug");
            if asan {
                fs::create_dir_all(&debug_directory).unwrap();
                let functions = phases
                    .mir
                    .functions
                    .iter()
                    .enumerate()
                    .map(|(index, function)| format!("{index}\t{}\n", function.name))
                    .collect::<String>();
                fs::write(debug_directory.join("functions.txt"), functions).unwrap();
            }
            let llvm = if asan {
                debug_directory.join("self-host-body-grouping.ll")
            } else {
                directory.path().join("self-host-body-grouping.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-body-grouping")
            } else {
                directory.path().join("self-host-body-grouping")
            };
            fs::write(&llvm, module.ir).unwrap();
            let mut clang_command = Command::new("clang");
            clang_command
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O0");
            if asan {
                clang_command.args(["-fsanitize=address", "-fno-omit-frame-pointer", "-g"]);
            }
            let clang = clang_command.arg("-o").arg(&executable).output().unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );

            let native_all_path = directory.path().join("native-all.bin");
            let native_all = Command::new(&executable)
                .arg(&native_all_path)
                .args(&corpus)
                .output()
                .unwrap();
            assert!(
                native_all.status.success(),
                "native whole-corpus status: {:?}\n{}",
                native_all.status,
                String::from_utf8_lossy(&native_all.stderr)
            );
            assert_eq!(
                fs::read(&native_all_path).unwrap(),
                expected,
                "native whole-corpus body grouping diverged"
            );
            for (index, path) in corpus.iter().enumerate() {
                let native_path = directory.path().join(format!("native-{index}.bin"));
                let native = Command::new(&executable)
                    .arg(&native_path)
                    .arg(path)
                    .output()
                    .unwrap();
                assert!(
                    native.status.success(),
                    "native input {index} ({}) status: {:?}\n{}",
                    native.status,
                    path.display(),
                    String::from_utf8_lossy(&native.stderr)
                );
                let mut expected_one = Vec::new();
                push_u32(&mut expected_one, 1);
                encode_rust_grouping(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native body grouping diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_body_fixity_grouping_matches_bootstrap_ast() {
    // Keep the acceptance name tied to the bootstrap assertion it covers.
    self_hosted_effect_path_syntax_and_body_grouping_match_rust_in_vm_and_native_execution();
}
