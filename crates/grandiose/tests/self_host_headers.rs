use std::{
    ffi::OsString,
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    ast::{
        self, AssociatedArgumentSyntax, EffectDecl, EffectRowSyntax, FieldVisibility, Function, GenericParamKind,
        GenericParams, StructDecl, TypeSyntax, TypeSyntaxKind, Visibility,
    },
    source_bundle::{Segment, SourceBundle},
    CompileOptions, LlvmOptions, OptimizationLevel,
};
use grandiose_vm::{verify, SystemHost, Value, Vm};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_bundle(application: &str) -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_source = format!(
        "mod frontend;\nmod probe;\n\nmain() {{ run_compiler_host({application}) }}\n"
    );
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        primary_source,
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/headers/headers.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod bodies;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "");
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

fn push_bytes(output: &mut Vec<u8>, value: &[u8]) {
    push_u32(output, value.len().try_into().unwrap());
    output.extend(value);
}

fn push_string(output: &mut Vec<u8>, value: &str) {
    push_bytes(output, value.as_bytes());
}

fn push_span(output: &mut Vec<u8>, span: grandiose::span::Span) {
    push_u64(output, span.start as u64);
    push_u64(output, span.end as u64);
}

fn assert_wire_eq(actual: &[u8], expected: &[u8], context: &str) {
    if actual == expected {
        return;
    }
    let first = actual
        .iter()
        .zip(expected)
        .position(|(left, right)| left != right)
        .unwrap_or(actual.len().min(expected.len()));
    let actual_end = (first + 24).min(actual.len());
    let expected_end = (first + 24).min(expected.len());
    panic!(
        "{context} at byte {first}; lengths {} != {}; actual {:?}; expected {:?}",
        actual.len(),
        expected.len(),
        &actual[first..actual_end],
        &expected[first..expected_end],
    );
}

fn encode_optional_lifetime(output: &mut Vec<u8>, lifetime: Option<&str>) {
    match lifetime {
        Some(lifetime) => {
            output.push(1);
            push_string(output, lifetime);
        }
        None => output.push(0),
    }
}

fn encode_trait_ref(
    output: &mut Vec<u8>,
    source: &str,
    trait_ref: &ast::TraitRefSyntax,
) -> Result<(), ()> {
    let first = trait_ref.path.first().ok_or(())?;
    let last = trait_ref.path.last().ok_or(())?;
    output.push(5);
    push_u32(output, trait_ref.span.start.try_into().unwrap());
    push_u32(output, trait_ref.span.end.try_into().unwrap());
    output.push(1);
    push_u32(output, first.span.start.try_into().unwrap());
    push_u32(output, last.span.end.try_into().unwrap());
    push_u32(output, trait_ref.path.len().try_into().unwrap());
    for segment in &trait_ref.path {
        push_string(output, &segment.name);
        push_u32(output, segment.span.start.try_into().unwrap());
        push_u32(output, segment.span.end.try_into().unwrap());
    }
    let mut lifetimes = Vec::new();
    let mut types = Vec::new();
    for argument in &trait_ref.arguments {
        match argument {
            ast::GoalArgument::Lifetime { name, span } => lifetimes.push((name, *span)),
            ast::GoalArgument::Type(ty) => types.push(ty),
            _ => return Err(()),
        }
    }
    push_u32(output, lifetimes.len().try_into().unwrap());
    for (name, span) in lifetimes {
        push_string(output, name);
        push_u32(output, span.start.try_into().unwrap());
        push_u32(output, span.end.try_into().unwrap());
    }
    push_u32(output, types.len().try_into().unwrap());
    for ty in types {
        encode_type(output, source, ty)?;
    }
    Ok(())
}

fn encode_type(output: &mut Vec<u8>, _source: &str, ty: &TypeSyntax) -> Result<(), ()> {
    match &ty.kind {
        TypeSyntaxKind::Path(segments) => {
            output.push(1);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            push_u32(output, segments.len().try_into().unwrap());
            for segment in segments {
                push_string(output, &segment.name);
                push_u32(output, segment.span.start.try_into().unwrap());
                push_u32(output, segment.span.end.try_into().unwrap());
            }
        }
        TypeSyntaxKind::SharedReference { lifetime, referent } => {
            output.push(2);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            encode_optional_lifetime(output, lifetime.as_ref().map(|value| value.name.as_str()));
            encode_type(output, _source, referent)?;
        }
        TypeSyntaxKind::UniqueReference { lifetime, referent } => {
            output.push(3);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            encode_optional_lifetime(output, lifetime.as_ref().map(|value| value.name.as_str()));
            encode_type(output, _source, referent)?;
        }
        TypeSyntaxKind::Tuple(elements) => {
            output.push(4);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            push_u32(output, elements.len().try_into().unwrap());
            for element in elements {
                encode_type(output, _source, element)?;
            }
        }
        TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } => {
            output.push(5);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            encode_type(output, _source, constructor)?;
            push_u32(output, lifetime_arguments.len().try_into().unwrap());
            for lifetime in lifetime_arguments {
                push_string(output, &lifetime.lifetime.name);
                push_u32(output, lifetime.lifetime.span.start.try_into().unwrap());
                push_u32(output, lifetime.lifetime.span.end.try_into().unwrap());
            }
            push_u32(output, arguments.len().try_into().unwrap());
            for argument in arguments {
                encode_type(output, _source, argument)?;
            }
        }
        TypeSyntaxKind::Never => {
            output.push(6);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
        }
        TypeSyntaxKind::Projection {
            subject,
            trait_ref,
            item,
            arguments,
            ..
        } => {
            output.push(7);
            push_u32(output, ty.span.start.try_into().unwrap());
            push_u32(output, ty.span.end.try_into().unwrap());
            encode_type(output, _source, subject)?;
            encode_trait_ref(output, _source, trait_ref)?;
            push_string(output, &item.name);
            push_u32(output, item.span.start.try_into().unwrap());
            push_u32(output, item.span.end.try_into().unwrap());
            push_u32(output, arguments.len().try_into().unwrap());
            for argument in arguments {
                match argument {
                    AssociatedArgumentSyntax::Lifetime { name, .. } => {
                        output.push(2);
                        output.push(0);
                        push_string(output, name);
                    }
                    AssociatedArgumentSyntax::Type(argument) => {
                        output.push(1);
                        output.push(1);
                        push_span(output, argument.span);
                        encode_type(output, _source, argument)?;
                    }
                }
            }
        }
    }
    Ok(())
}

fn encode_generics(output: &mut Vec<u8>, generics: Option<&GenericParams>) -> Result<(), ()> {
    let parameters = generics.map_or(&[][..], |generics| generics.params.as_slice());
    push_u32(output, parameters.len().try_into().unwrap());
    for parameter in parameters {
        let kind = match parameter.kind {
            GenericParamKind::Type => 1,
            GenericParamKind::Lifetime => 2,
            GenericParamKind::EffectRow => 3,
            GenericParamKind::Const(_) => return Err(()),
        };
        output.push(kind);
        push_string(output, &parameter.name);
        if parameter.const_default.is_some() {
            return Err(());
        }
    }
    Ok(())
}

fn encode_effect_row(
    output: &mut Vec<u8>,
    source: &str,
    row: &EffectRowSyntax,
) -> Result<(), ()> {
    push_u32(output, row.effects.len().try_into().unwrap());
    for effect in &row.effects {
        push_span(output, effect.span);
        encode_type(output, source, effect)?;
    }
    push_span(output, row.span);
    match &row.tail {
        Some(tail) => {
            output.push(1);
            push_string(output, &tail.name);
        }
        None => output.push(0),
    }
    Ok(())
}

fn encode_where_contract(
    output: &mut Vec<u8>,
    source: &str,
    clause: Option<&ast::WhereClause>,
) {
    let Some(clause) = clause else {
        output.push(0);
        return;
    };
    output.push(1);
    push_span(output, clause.span);
    push_u32(output, clause.goals.len().try_into().unwrap());
    for goal in &clause.goals {
        push_span(output, goal.span);
        push_u32(
            output,
            goal.higher_ranked_lifetimes.len().try_into().unwrap(),
        );
        for parameter in &goal.higher_ranked_lifetimes {
            let kind = match parameter.kind {
                GenericParamKind::Type => 1,
                GenericParamKind::Lifetime => 2,
                GenericParamKind::EffectRow => 3,
                GenericParamKind::Const(_) => return,
            };
            output.push(kind);
            push_string(output, &parameter.name);
        }
        push_span(output, goal.subject.span);
        encode_type(output, source, &goal.subject).unwrap();
        output.push(u8::from(goal.polarity == ast::GoalPolarity::Negative));
        push_u32(output, goal.relation.path.len().try_into().unwrap());
        for segment in &goal.relation.path {
            push_string(output, &segment.name);
        }
        push_u32(output, goal.relation.arguments.len().try_into().unwrap());
        for argument in &goal.relation.arguments {
            match argument {
                ast::GoalArgument::Type(ty) => {
                    output.push(1);
                    output.push(1);
                    push_span(output, ty.span);
                    encode_type(output, source, ty).unwrap();
                }
                ast::GoalArgument::Lifetime { .. } => {
                    output.push(2);
                    output.push(0);
                }
                ast::GoalArgument::Quantity(_) => {
                    output.push(3);
                    output.push(0);
                }
                ast::GoalArgument::U32 { .. } => {
                    output.push(4);
                    output.push(0);
                }
            }
        }
        push_u32(output, goal.relation.bindings.len().try_into().unwrap());
        for binding in &goal.relation.bindings {
            push_string(output, &binding.name);
            push_span(output, binding.span);
            push_u32(output, binding.arguments.len().try_into().unwrap());
            for argument in &binding.arguments {
                match argument {
                    ast::AssociatedArgumentSyntax::Lifetime { name, .. } => {
                        output.push(2);
                        output.push(0);
                        push_string(output, name);
                    }
                    ast::AssociatedArgumentSyntax::Type(ty) => {
                        output.push(1);
                        output.push(1);
                        push_span(output, ty.span);
                        encode_type(output, source, ty).unwrap();
                    }
                }
            }
            match &binding.value {
                ast::AssociatedBindingValue::Type(ty) => {
                    output.push(1);
                    push_span(output, ty.span);
                    encode_type(output, source, ty).unwrap();
                }
                ast::AssociatedBindingValue::EffectRow(row) => {
                    output.push(2);
                    encode_effect_row(output, source, row).unwrap();
                }
            }
        }
    }
    push_u32(output, clause.lifetime_outlives.len().try_into().unwrap());
    for constraint in &clause.lifetime_outlives {
        push_u32(
            output,
            constraint.higher_ranked_lifetimes.len().try_into().unwrap(),
        );
        for parameter in &constraint.higher_ranked_lifetimes {
            let kind = match parameter.kind {
                GenericParamKind::Type => 1,
                GenericParamKind::Lifetime => 2,
                GenericParamKind::EffectRow => 3,
                GenericParamKind::Const(_) => return,
            };
            output.push(kind);
            push_string(output, &parameter.name);
        }
        push_string(output, &constraint.longer.name);
        push_string(output, &constraint.shorter.name);
        push_u32(output, constraint.span.start as u32);
        push_u32(output, constraint.span.end as u32);
    }
}

fn encode_callable(
    output: &mut Vec<u8>,
    source: &str,
    program: &grandiose::ast::Program,
    declaration: &Function,
) -> Result<(), ()> {
    output.push(u8::from(
        program.visibility(declaration.span) == Visibility::Public,
    ));
    push_string(output, &declaration.name);
    encode_generics(output, declaration.generics.as_ref())?;
    if let Some(generics) = declaration.generics.as_ref() {
        push_span(output, generics.span);
    } else {
        push_u64(output, 0);
        push_u64(output, 0);
    }
    push_u32(output, declaration.params.len().try_into().unwrap());
    for parameter in &declaration.params {
        push_string(output, &parameter.name);
        encode_type(output, source, &parameter.ty)?;
    }
    match &declaration.return_type {
        Some(return_type) => {
            output.push(1);
            encode_type(output, source, return_type)?;
        }
        None => output.push(0),
    }
    match &declaration.outward_effects {
        Some(effects) => {
            output.push(1);
            encode_effect_row(output, source, effects)?;
        }
        None => output.push(0),
    }
    encode_where_contract(output, source, declaration.where_clause.as_ref());
    Ok(())
}

fn encode_effect(
    output: &mut Vec<u8>,
    source: &str,
    program: &grandiose::ast::Program,
    declaration: &EffectDecl,
) -> Result<(), ()> {
    output.push(u8::from(
        program.visibility(declaration.span) == Visibility::Public,
    ));
    push_string(output, &declaration.name);
    encode_generics(output, declaration.generics.as_ref())?;
    output.push(u8::from(declaration.where_clause.is_some()));
    push_u32(output, declaration.operations.len().try_into().unwrap());
    for operation in &declaration.operations {
        push_string(output, &operation.name);
        encode_generics(output, operation.generics.as_ref())?;
        push_u32(output, operation.params.len().try_into().unwrap());
        for parameter in &operation.params {
            push_string(output, &parameter.name);
            encode_type(output, source, &parameter.ty)?;
        }
        match &operation.return_type {
            Some(result) => {
                output.push(1);
                encode_type(output, source, result)?;
            }
            None => output.push(0),
        }
        output.push(u8::from(operation.terminal));
        push_u64(output, operation.resumption_lower.try_into().unwrap());
        match operation.resumption_upper {
            Some(upper) => {
                output.push(1);
                push_u64(output, upper.try_into().unwrap());
            }
            None => output.push(0),
        }
        output.push(u8::from(operation.has_resumption_quantity));
        output.push(u8::from(operation.where_clause.is_some()));
    }
    Ok(())
}

fn encode_effect_row_alias(
    output: &mut Vec<u8>,
    source: &str,
    program: &grandiose::ast::Program,
    declaration: &grandiose::ast::EffectRowAliasDecl,
) -> Result<(), ()> {
    output.push(u8::from(program.visibility(declaration.span) == Visibility::Public));
    push_string(output, &declaration.name);
    encode_effect_row(output, source, &declaration.row)?;
    push_span(output, declaration.span);
    Ok(())
}

fn encode_struct(
    output: &mut Vec<u8>,
    source: &str,
    program: &grandiose::ast::Program,
    declaration: &StructDecl,
) -> Result<(), ()> {
    output.push(u8::from(
        program.visibility(declaration.span) == Visibility::Public,
    ));
    push_string(output, &declaration.name);
    encode_generics(output, declaration.generics.as_ref())?;
    push_u32(output, declaration.fields.len().try_into().unwrap());
    for field in &declaration.fields {
        output.push(u8::from(field.visibility == FieldVisibility::Public));
        push_string(output, &field.name);
        encode_type(output, source, &field.ty)?;
        push_u64(output, field.span.start as u64);
        push_u64(output, field.span.end as u64);
    }
    Ok(())
}

fn encode_drop(output: &mut Vec<u8>, source: &str, declaration: &ast::DropDecl) {
    push_span(output, declaration.span);
    encode_generics(output, declaration.generics.as_ref()).unwrap();
    push_span(output, declaration.target_type.span);
    encode_type(output, source, &declaration.target_type).unwrap();
    encode_where_contract(output, source, declaration.where_clause.as_ref());
}

fn encode_use(output: &mut Vec<u8>, source: &str, declaration: &ast::UseDecl) {
    push_span(output, declaration.span);
    encode_generics(output, declaration.generics.as_ref()).unwrap();
    push_u64(output, declaration.quantity.lower as u64);
    match declaration.quantity.upper {
        Some(upper) => { output.push(1); push_u64(output, upper as u64); }
        None => output.push(0),
    }
    push_span(output, declaration.target.span);
    encode_type(output, source, &declaration.target).unwrap();
    encode_where_contract(output, source, declaration.where_clause.as_ref());
}

fn bootstrap_header_error_code(source: &str, error: &grandiose::diagnostic::Diagnostic) -> u32 {
    let span = error.span.unwrap();
    let prefix = source[..span.start.min(source.len())].trim_end();
    match (error.title.as_str(), error.message.as_str()) {
        ("empty generic application", _) => 5,
        (_, "expected `>` after generic type arguments") => 4,
        (_, "expected `)` to close the tuple type") => 3,
        (_, "expected `:` and a parameter type") => 7,
        (_, "expected `,` between quantity bounds") => 19,
        (_, "expected `]` after quantity bounds") => 21,
        ("invalid resumption quantity", message)
            if message.contains("lower bound") => 22,
        ("invalid resumption quantity", message)
            if message.contains("upper bound") => 20,
        ("duplicate associated binding", _) => 26,
        (_, _) if prefix.ends_with("where") => 23,
        (_, message) if message.contains("expected `{`") || message == "expected a block" => 9,
        ("expected a name", _) => 1,
        (title, message) => panic!(
            "unmapped bootstrap header diagnostic `{title}` / `{message}` at {span:?}"
        ),
    }
}

fn encode_bootstrap_header_error(
    output: &mut Vec<u8>,
    source: &str,
    error: &grandiose::diagnostic::Diagnostic,
) {
    output.push(3);
    push_u32(output, bootstrap_header_error_code(source, error));
    let span = error.span.unwrap();
    push_u64(output, span.start as u64);
    push_u64(output, span.end as u64);
}

fn encode_rust_headers(output: &mut Vec<u8>, source: &str) {
    let Ok(tokens) = grandiose::lexer::lex(source) else {
        output.push(1);
        return;
    };
    let program = match grandiose::parser::parse(tokens) {
        Ok(program) => program,
        Err(error) => {
            encode_bootstrap_header_error(output, source, &error);
            return;
        }
    };
    let mut callables = program.functions.iter().collect::<Vec<_>>();
    callables.sort_by_key(|declaration| declaration.span.start);

    let mut encoded = Vec::new();
    push_u32(&mut encoded, callables.len().try_into().unwrap());
    for callable in callables {
        if encode_callable(&mut encoded, source, &program, callable).is_err() {
            output.push(3);
            return;
        }
    }
    let mut effect_row_aliases = program.effect_row_aliases.iter().collect::<Vec<_>>();
    effect_row_aliases.sort_by_key(|declaration| declaration.span.start);
    push_u32(&mut encoded, effect_row_aliases.len().try_into().unwrap());
    for declaration in effect_row_aliases {
        if encode_effect_row_alias(&mut encoded, source, &program, declaration).is_err() {
            output.push(3);
            return;
        }
    }
    let mut effects = program.effects.iter().collect::<Vec<_>>();
    effects.sort_by_key(|declaration| declaration.span.start);
    push_u32(&mut encoded, effects.len().try_into().unwrap());
    for effect in effects {
        if encode_effect(&mut encoded, source, &program, effect).is_err() {
            output.push(3);
            return;
        }
    }
    let mut structs = program.structs.iter().collect::<Vec<_>>();
    structs.sort_by_key(|declaration| declaration.span.start);
    push_u32(&mut encoded, structs.len().try_into().unwrap());
    for declaration in structs {
        if encode_struct(&mut encoded, source, &program, declaration).is_err() {
            output.push(3);
            return;
        }
    }
    let mut drops = program.drops.iter().collect::<Vec<_>>();
    drops.sort_by_key(|declaration| declaration.span.start);
    push_u32(&mut encoded, drops.len().try_into().unwrap());
    for declaration in drops {
        encode_drop(&mut encoded, source, declaration);
    }
    let mut uses = program.uses.iter().collect::<Vec<_>>();
    uses.sort_by_key(|declaration| declaration.span.start);
    push_u32(&mut encoded, uses.len().try_into().unwrap());
    for declaration in uses {
        encode_use(&mut encoded, source, declaration);
    }
    output.push(0);
    output.extend(encoded);
}

fn encode_rust_trait_impl_interfaces(output: &mut Vec<u8>, source: &str) {
    let program = grandiose::parser::parse(grandiose::lexer::lex(source).unwrap()).unwrap();
    enum Item { Trait(usize), Struct(usize), Impl(usize), Function(usize) }
    let mut items = Vec::new();
    items.extend(program.traits.iter().enumerate().map(|(i, d)| (d.span.start, Item::Trait(i))));
    items.extend(program.structs.iter().enumerate().map(|(i, d)| (d.span.start, Item::Struct(i))));
    items.extend(program.impls.iter().enumerate().map(|(i, d)| (d.span.start, Item::Impl(i))));
    items.extend(program.functions.iter().enumerate().map(|(i, d)| (d.span.start, Item::Function(i))));
    items.sort_by_key(|(start, _)| *start);
    push_u32(output, items.len().try_into().unwrap());
    for (_, item) in items {
        match item {
            Item::Trait(index) => {
                output.push(15);
                let declaration = &program.traits[index];
                output.push(u8::from(program.visibility(declaration.span) == Visibility::Public));
                push_string(output, &declaration.name);
                if let Some(generics) = declaration.generics.as_ref() {
                    for parameter in &generics.params {
                        output.push(match parameter.kind {
                            GenericParamKind::Type => 1,
                            GenericParamKind::Lifetime => 2,
                            GenericParamKind::EffectRow => 3,
                            GenericParamKind::Const(_) => 0,
                        });
                        push_string(output, &parameter.name);
                    }
                }
                push_span(output, declaration.span);
            }
            Item::Struct(index) => {
                output.push(8);
                let declaration = &program.structs[index];
                output.push(u8::from(program.visibility(declaration.span) == Visibility::Public));
                push_string(output, &declaration.name);
                encode_generics(output, declaration.generics.as_ref()).unwrap();
                push_u32(output, declaration.fields.len().try_into().unwrap());
                for field in &declaration.fields {
                    output.push(u8::from(field.visibility == FieldVisibility::Public));
                    push_string(output, &field.name);
                    encode_type(output, source, &field.ty).unwrap();
                }
            }
            Item::Impl(index) => {
                output.push(16);
                let declaration = &program.impls[index];
                if let Some(generics) = declaration.generics.as_ref() {
                    for parameter in &generics.params {
                        output.push(match parameter.kind {
                            GenericParamKind::Type => 1,
                            GenericParamKind::Lifetime => 2,
                            GenericParamKind::EffectRow => 3,
                            GenericParamKind::Const(_) => 0,
                        });
                        push_string(output, &parameter.name);
                    }
                }
                push_u32(output, declaration.trait_ref.path.len().try_into().unwrap());
                for segment in &declaration.trait_ref.path { push_string(output, &segment.name); }
                push_span(output, declaration.self_ty.span);
                encode_type(output, source, &declaration.self_ty).unwrap();
                encode_where_contract(output, source, declaration.where_clause.as_ref());
                push_span(output, declaration.span);
            }
            Item::Function(index) => {
                output.push(12);
                encode_callable(output, source, &program, &program.functions[index]).unwrap();
            }
        }
    }
}

fn encode_rust_malformed_nested_type(output: &mut Vec<u8>, source: &str) {
    let tokens = grandiose::lexer::lex(source).unwrap();
    let error = grandiose::parser::parse(tokens).unwrap_err();
    encode_bootstrap_header_error(output, source, &error);
}

#[test]
fn self_host_header_malformed_nested_types_match_bootstrap() {
    // The focused protocol carries the bootstrap parser's first diagnostic.
    // Keep this acceptance at the component boundary.
    let sources = [
        "type Bad = Pair<>; main() -> { () }",
        "type Bad = Pair<i64, Text; main() -> { () }",
        "type Bad = (i64, Text; main() -> { () }",
        "main(value: &mut) -> { () }",
    ];
    let directory = tempfile::tempdir().unwrap();
    let mut inputs = Vec::new();
    let mut expected = Vec::new();
    push_u32(&mut expected, sources.len().try_into().unwrap());
    for (index, source) in sources.iter().enumerate() {
        let path = directory.path().join(format!("malformed-{index}.glorious"));
        fs::write(&path, source).unwrap();
        inputs.push(path);
        encode_rust_malformed_nested_type(&mut expected, source);
    }

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle("probe::headers::application"),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let output_path = directory.path().join("malformed.bin");
    let args = std::iter::once(output_path.clone().into_os_string())
        .chain(inputs.iter().map(|path| path.clone().into_os_string()))
        .collect::<Vec<OsString>>();
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(args),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    assert_eq!(fs::read(output_path).unwrap(), expected);
}

fn corpus(directory: &Path) -> Vec<PathBuf> {
    let focused = [
        "",
        "struct Vault { private secret: i64, visible: Text, private: i64 }",
        "noop() { () }",
        "identity<T>(value: T) -> T { value }",
        "pub consume(value: &mut Vec<u8>) { () }",
        "borrow<'a, T>(value: &'a T) -> &'a T { value }",
        "slice<'a, T>(value: &'a Vec<T>) -> pkg::Slice<'a, T> { unreachable() }",
        "tuples(unit: (), single: (u8,), trio: (u8, String, !)) -> (u8, u8) { (0, 0) }",
        "view<T>(value: pkg::View<(T, !)>) -> pkg::View<(T, !)> { value }",
        "type Alias = Result<&mut (i64, Option<&Text>), ()>; struct Record { value: &Map<Text, (i64, &mut Bytes)> } enum Event { Send(core::Packet<&Text>, ()), Empty } effect Query { ask(input: &mut Vec<(i64, Text)>) -> Option<&Text>; } run(arg: &Alias) -> Result<(i64, Text), &mut Error> { () }",
        "first<T>(value: Vec<T>) -> T { unreachable() } second(value: core::Pair<u8, u16>) { () }",
        "spaced<T,>(value: Vec< /* element */ T, >) -> Vec<T> { value }",
        "read<T, E: EffectRow>(value: T) -> pkg::Result<T, !> / {Console, Io<T> | E} { value }",
        "bounded<T>(value: T) -> T where T: Use<[0, *]> { value }",
        "trait Marker {} struct Box<T> { value: T } impl<U> Drop for Box<U> where U: Marker { drop(&mut self) -> { () } } impl<T> Use<[1, 2]> for Box<T> where T: Marker, T: Use<[0, 2]> {} main() -> { () }",
        "call<F, T>(function: F, value: T) -> T where F: Fn<(T), Output=T> { function(value) }",
        "write(value: String) / Console { () }",
        "bad(value u32) { () }",
        "bad(value: Vec<>) { () }",
        "bad(value: T) trailing { () }",
        "bad<T>(value: T) -> T where { value }",
        "pub effect Control<'a, T, E: EffectRow> where T: Marker { [0, infinity] choose<U>(input: &'a T, fallback: U) -> Result<T, U> where U: Marker; [2, 4] repeat(value: T) -> T; stop(reason: String) -> !; unit() ->; implicit() }",
        "effect Adjacent { first() second(value: u8) -> u8 third() -> ! }",
        "effect AdjacentWhere<T> { first(value: T) -> T where T: Marker second<U>(value: U) -> U }",
        "effect GenericWhere<T> { first<F, U>(value: T, function: F) -> U where Vec<Result<T, U>>: Marker, F: Fn<(T), Output=U> next<V>(value: V) -> V }",
        "effect BadQuantity { [0 1] choose() -> u8; }",
        "effect BadOperationWhere { choose() -> u8 where; }",
    ];
    let mut paths = Vec::new();
    for (index, source) in focused.into_iter().enumerate() {
        let path = directory.join(format!("focused-{index}.glorious"));
        fs::write(&path, source).unwrap();
        paths.push(path);
    }

    let mut deep = String::from("deep(value: ");
    for _ in 0..32 {
        deep.push_str("Vec<");
    }
    deep.push_str("u8");
    for _ in 0..32 {
        deep.push('>');
    }
    deep.push_str(") { () }");
    let path = directory.join("deep.glorious");
    fs::write(&path, deep).unwrap();
    paths.push(path);
    paths
}

#[test]
fn self_host_header_struct_visibility_matches_bootstrap() {
    self_hosted_headers_match_rust_in_vm_and_native_execution();
}

#[test]
fn self_host_unit_unit_and_never_results_are_retained() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = "effect Stop { stop() -> !; } main() -> { () }";
            let input = directory.path().join("unit-and-never.glorious");
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_output = directory.path().join("vm.bin");
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
            assert_wire_eq(
                &fs::read(&vm_output).unwrap(),
                &expected,
                "VM unit and never headers diverged",
            );

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            let native_output = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            assert_wire_eq(
                &fs::read(native_output).unwrap(),
                &expected,
                "native unit and never headers diverged",
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_unit_empty_marker_traits_and_positive_impls() {
    let directory = tempfile::tempdir().unwrap();
    let source = "trait Marker {} struct Box<T> { value: T } impl Marker for i64 {} impl<T> Marker for Box<T> where T: Marker {} main() -> { () }";
    let input = directory.path().join("marker.glorious");
    let output = directory.path().join("headers.bin");
    fs::write(&input, source).unwrap();
    let mut expected = Vec::new();
    push_u32(&mut expected, 1);
    expected.push(0);
    encode_rust_trait_impl_interfaces(&mut expected, source);

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle("probe::headers::interface_application"),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    ).unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    ).unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    assert_wire_eq(&fs::read(&output).unwrap(), &expected, "marker trait interfaces diverged");
}

#[test]
fn self_host_header_drop_and_use_declarations_match_bootstrap() {
    self_hosted_headers_match_rust_in_vm_and_native_execution();
}

#[test]
fn effect_where_unmatched_closers_are_rejected_before_header_parity() {
    for source in [
        "effect Bad { first<T>() where T: Marker) second() }",
        "effect Bad { first<T>() where T: Marker> second() }",
        "effect Bad { first<T>() where T: Marker] second() }",
    ] {
        let tokens = grandiose::lexer::lex(source).unwrap();
        assert!(
            grandiose::parser::parse(tokens).is_err(),
            "the bootstrap parser unexpectedly accepted `{source}`"
        );
    }
}

#[test]
fn self_hosted_headers_match_rust_in_vm_and_native_execution() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_HEADERS_CHECK_ONLY").is_some() {
                let phases = grandiose::compile_bundle_to_phases_with_options(
                    &self_host_bundle("probe::headers::application"),
                    CompileOptions {
                        optimization_level: OptimizationLevel::O0,
                    },
                )
                .unwrap();
                verify(phases.artifact).unwrap();
                return;
            }

            let directory = tempfile::tempdir().unwrap();
            let corpus = corpus(directory.path());
            let expected_path = directory.path().join("expected.bin");
            let vm_path = directory.path().join("vm.bin");
            let mut expected = Vec::new();
            push_u32(&mut expected, corpus.len().try_into().unwrap());
            for path in &corpus {
                encode_rust_headers(&mut expected, &fs::read_to_string(path).unwrap());
            }
            fs::write(&expected_path, &expected).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_args = std::iter::once(vm_path.clone().into_os_string())
                .chain(corpus.iter().map(|path| path.clone().into_os_string()))
                .collect::<Vec<OsString>>();
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            let vm_actual = fs::read(&vm_path).unwrap();
            if vm_actual != expected {
                for (index, path) in corpus.iter().enumerate() {
                    let focused_path = directory.path().join(format!("vm-{index}.bin"));
                    let focused = Vm::with_host(
                        verify(phases.artifact.clone()).unwrap(),
                        ["process.args", "fs.read", "fs.write", "diagnostic"],
                        SystemHost::new(vec![
                            focused_path.clone().into_os_string(),
                            path.clone().into_os_string(),
                        ]),
                    )
                    .unwrap();
                    assert_eq!(focused.run(entry, vec![]).unwrap(), Value::Unit);
                    let mut expected_one = Vec::new();
                    push_u32(&mut expected_one, 1);
                    encode_rust_headers(
                        &mut expected_one,
                        &fs::read_to_string(path).unwrap(),
                    );
                    assert_wire_eq(
                        &fs::read(&focused_path).unwrap(),
                        &expected_one,
                        &format!("VM headers diverged for input {index} ({})", path.display()),
                    );
                }
                assert_wire_eq(&vm_actual, &expected, "VM aggregate headers diverged");
            }

            let asan = std::env::var_os("G1_SELF_HOST_HEADERS_ASAN").is_some();
            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let debug_directory = repository_root().join("target/self-host-headers-debug");
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
                debug_directory.join("self-host-headers.ll")
            } else {
                directory.path().join("self-host-headers.ll")
            };
            let executable = if asan {
                debug_directory.join("self-host-headers")
            } else {
                directory.path().join("self-host-headers")
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
            assert_wire_eq(
                &fs::read(&native_all_path).unwrap(),
                &expected,
                "native whole-corpus headers diverged",
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
                encode_rust_headers(&mut expected_one, &fs::read_to_string(path).unwrap());
                assert_eq!(
                    fs::read(&native_path).unwrap(),
                    expected_one,
                    "native headers diverged for input {index} ({})",
                    path.display()
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_unit_associated_types_and_gats() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = "trait Family<C> { type Member<'a, T>; } struct Box<S>{value:S} struct Triple<A,B,C>{first:A,second:B,third:C} impl<S,C> Family<C> for Box<S> { type Member<'scope, T> = Triple<S,C,T>; } read(value:<Box<i64> as Family<Text>>::Member<'static, u16>)->u16 where Box<i64>: Family<Text, Member<'static, u16> = Triple<i64,Text,u16>> { 0 } main()->{()}";
            let input = directory.path().join("associated-types-and-gats.glorious");
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_output = directory.path().join("vm.bin");
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![vm_output.clone().into_os_string(), input.clone().into_os_string()]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_wire_eq(&fs::read(&vm_output).unwrap(), &expected, "VM associated GAT headers diverged");

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            assert!(clang.status.success(), "{}", String::from_utf8_lossy(&clang.stderr));
            let native_output = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(native.status.success(), "native status: {:?}\n{}", native.status, String::from_utf8_lossy(&native.stderr));
            assert_wire_eq(&fs::read(native_output).unwrap(), &expected, "native associated GAT headers diverged");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_header_reference_lifetimes_match_bootstrap() {
    // The component contract is exercised in both execution engines below.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = concat!(
                "forward<'long, 'short>(left: &'long i64, right: &'short mut i64) ",
                "-> &'short i64 where 'long: 'short { left } ",
                "main() -> { () }"
            );
            let input = directory.path().join("reference-lifetimes.glorious");
            fs::write(&input, source).unwrap();
            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_path = directory.path().join("vm.bin");
            let vm_args = vec![vm_path.clone().into_os_string(), input.clone().into_os_string()];
            let vm = Vm::with_host(
                verify(phases.artifact.clone()).unwrap(),
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vm_args),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            assert_eq!(fs::read(&vm_path).unwrap(), expected, "VM reference contract diverged");

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            let native_path = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_path)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            assert_eq!(fs::read(native_path).unwrap(), expected, "native contract diverged");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_header_mixed_nominal_arguments_match_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = "struct View<T, 'a> { value: &'a T } pass<'scope, U>(value: View<U, 'scope>) -> View<U, 'scope> { move value } main() -> { () }";
            let input = directory.path().join("mixed-nominal-arguments.glorious");
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_output = directory.path().join("vm.bin");
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
            assert_wire_eq(
                &fs::read(&vm_output).unwrap(),
                &expected,
                "VM mixed nominal headers diverged",
            );

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            let native_output = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            assert_wire_eq(
                &fs::read(native_output).unwrap(),
                &expected,
                "native mixed nominal headers diverged",
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_header_generic_where_effect_rows_match_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("focused.glorious");
            let vm_output = directory.path().join("vm.bin");
            let native_output = directory.path().join("native.bin");
            let source = "run<E, S, F, R>(body: F) -> R / {Ask, Trace<i32>} where F: Fn<(), Output = R>, F: RunsIn<E, (), After = S>, E: Use<[0, 0]> { body() }";
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
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
            assert_eq!(fs::read(&vm_output).unwrap(), expected, "VM headers diverged");

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            assert_eq!(fs::read(&native_output).unwrap(), expected, "native headers diverged");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_header_effect_row_aliases_match_bootstrap() {
    let directory = tempfile::tempdir().unwrap();
    let source = "cases Common = {Primary, Trace<i32> | Tail}; run<E: EffectRow>(value: i64) -> () / {Common | E} { () } main() -> { () }";
    let input = directory.path().join("effect-row-alias.glorious");
    let output = directory.path().join("headers.bin");
    fs::write(&input, source).unwrap();

    let mut expected = Vec::new();
    push_u32(&mut expected, 1);
    encode_rust_headers(&mut expected, source);

    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle("probe::headers::application"),
        CompileOptions { optimization_level: OptimizationLevel::O2 },
    )
    .unwrap();
    let entry = phases.artifact.entry_function.unwrap();
    let vm = Vm::with_host(
        verify(phases.artifact).unwrap(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
    )
    .unwrap();
    assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
    assert_eq!(fs::read(output).unwrap(), expected);
}

#[test]
fn self_host_header_higher_ranked_binders_match_bootstrap() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let source = concat!(
                "check() -> Text where ",
                "for<Item, 'scope> Text:Rel<Item, 'scope>, ",
                "for<'long, 'short> 'long: 'short { \"ok\" } ",
                "main() -> { () }"
            );
            let input = directory.path().join("higher-ranked-binders.glorious");
            fs::write(&input, source).unwrap();

            let mut expected = Vec::new();
            push_u32(&mut expected, 1);
            encode_rust_headers(&mut expected, source);

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::headers::application"),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let vm_output = directory.path().join("vm.bin");
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
            assert_wire_eq(
                &fs::read(&vm_output).unwrap(),
                &expected,
                "VM higher-ranked binder headers diverged",
            );

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-headers.ll");
            let executable = directory.path().join("self-host-headers");
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
            let native_output = directory.path().join("native.bin");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native status: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            assert_wire_eq(
                &fs::read(native_output).unwrap(),
                &expected,
                "native higher-ranked binder headers diverged",
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_host_header_nested_type_spans_match_bootstrap() {
    self_hosted_headers_match_rust_in_vm_and_native_execution();
}
