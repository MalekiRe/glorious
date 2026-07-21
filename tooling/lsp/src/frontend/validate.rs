use std::collections::{HashMap, HashSet};

use crate::frontend::{
    ast::{
        EffectDecl, EffectOperationDecl, Expr, ExprKind, GenericParamKind, PatternKind, Program,
        Stmt,
    },
    diagnostic::Diagnostic,
    span::Span,
};

pub fn validate(program: &Program) -> Result<(), Vec<Diagnostic>> {
    let mut errors = Vec::new();
    let mut type_declarations = program
        .type_aliases
        .iter()
        .map(|declaration| (declaration.name.as_str(), declaration.span))
        .chain(
            program
                .structs
                .iter()
                .map(|declaration| (declaration.name.as_str(), declaration.span)),
        )
        .chain(
            program
                .enums
                .iter()
                .map(|declaration| (declaration.name.as_str(), declaration.span)),
        )
        .collect::<Vec<_>>();
    type_declarations.sort_by_key(|(_, span)| span.start);
    let mut types = HashMap::<&str, Span>::new();
    for (name, span) in type_declarations {
        if name == "Quantity" {
            errors.push(
                Diagnostic::error(
                    "reserved const type name",
                    "`Quantity` is the frozen compiler-defined const parameter type",
                    span,
                )
                .with_code("G0007")
                .with_help("choose a different source type name"),
            );
        } else if let Some(original) = types.get(name).copied() {
            errors.push(
                Diagnostic::error(
                    "type declared more than once",
                    format!("`{name}` is redeclared here"),
                    span,
                )
                .with_code("G0007")
                .with_related(original, "the first declaration is here")
                .with_help(
                    "rename one declaration; aliases, structs, and enums share the type namespace",
                ),
            );
        } else {
            types.insert(name, span);
        }
    }
    let mut value_declarations = program
        .functions
        .iter()
        .map(|function| (None, function.name.as_str(), function.span, true))
        .chain(program.globals.iter().map(|binding| {
            (
                binding.owner.as_deref(),
                binding.name.as_str(),
                binding.span,
                false,
            )
        }))
        .collect::<Vec<_>>();
    value_declarations.sort_by_key(|(_, _, span, _)| span.start);
    let mut values = HashMap::<(Option<&str>, &str), (Span, bool)>::new();
    for (owner, name, span, callable) in value_declarations {
        if let Some(owner) = owner
            && !types.contains_key(owner)
        {
            errors.push(
                Diagnostic::error(
                    "unknown associated binding owner",
                    format!("`{owner}` is not a declared nominal type or type alias"),
                    span,
                )
                .with_code("G0006")
                .with_help("declare the type owner before adding a qualified value binding"),
            );
        }
        if let Some(owner) = owner
            && let Some(original) = program
                .enums
                .iter()
                .find(|declaration| declaration.name == owner)
                .and_then(|declaration| {
                    declaration
                        .variants
                        .iter()
                        .find(|variant| variant.name == name)
                })
                .map(|variant| variant.span)
        {
            errors.push(
                Diagnostic::error(
                    "value declared more than once",
                    format!("`{owner}::{name}` is already an enum constructor"),
                    span,
                )
                .with_code("G0006")
                .with_related(original, "the constructor is declared here")
                .with_help("choose a distinct associated binding name"),
            );
        }
        let key = (owner, name);
        if let Some((original, original_callable)) = values.get(&key).copied() {
            let duplicate_callables = callable && original_callable;
            let display = owner.map_or_else(|| name.to_owned(), |owner| format!("{owner}::{name}"));
            errors.push(
                Diagnostic::error(
                    if duplicate_callables {
                        "callable declared more than once"
                    } else {
                        "value declared more than once"
                    },
                    format!("`{display}` is redeclared here"),
                    span,
                )
                .with_code(if duplicate_callables {
                    "G0001"
                } else {
                    "G0006"
                })
                .with_related(original, "the first declaration is here")
                .with_help(if duplicate_callables {
                    "rename one declaration; callable names must be unique in a module"
                } else {
                    "rename one declaration; globals and callables share the value namespace"
                }),
            );
        } else {
            values.insert(key, (span, callable));
        }
    }

    let mut effect_declarations = program
        .effects
        .iter()
        .map(|effect| (effect.name.as_str(), effect.span))
        .chain(
            program
                .effect_row_aliases
                .iter()
                .map(|alias| (alias.name.as_str(), alias.span)),
        )
        .collect::<Vec<_>>();
    effect_declarations.sort_by_key(|(_, span)| span.start);
    let mut effect_names = HashMap::<&str, Span>::new();
    for (name, span) in effect_declarations {
        if let Some(original) = effect_names.get(name).copied() {
            errors.push(
                Diagnostic::error(
                    "effect name declared more than once",
                    format!("`{name}` is redeclared here"),
                    span,
                )
                .with_code("G0002")
                .with_related(original, "the first declaration is here")
                .with_help("effects and effect-row aliases share one namespace"),
            );
        } else {
            effect_names.insert(name, span);
        }
    }

    let mut effects = HashMap::<&str, (&EffectDecl, HashMap<&str, &EffectOperationDecl>)>::new();
    for effect in &program.effects {
        if effects.contains_key(effect.name.as_str()) {
            continue;
        }
        let mut operation_names = HashSet::new();
        let mut operations = HashMap::new();
        for operation in &effect.operations {
            if !operation_names.insert(operation.name.as_str()) {
                errors.push(
                    Diagnostic::error(
                        "duplicate effect operation",
                        format!(
                            "`{}::{}` is declared more than once",
                            effect.name, operation.name
                        ),
                        operation.span,
                    )
                    .with_code("G0003"),
                );
            }
            if operation.terminal && operation.has_resumption_quantity {
                errors.push(
                    Diagnostic::error(
                        "terminal operation cannot declare a resumption quantity",
                        format!(
                            "`{}::{}` returns `!` and has no continuation",
                            effect.name, operation.name
                        ),
                        operation.span,
                    )
                    .with_code("G0004")
                    .with_help("remove the `[lower, upper]` quantity"),
                );
            }
            if operation
                .resumption_upper
                .is_some_and(|upper| upper < operation.resumption_lower)
            {
                errors.push(
                    Diagnostic::error(
                        "invalid resumption quantity interval",
                        "the upper bound is smaller than the lower bound",
                        operation.span,
                    )
                    .with_code("G0005")
                    .with_help("increase the upper bound or decrease the lower bound"),
                );
            }
            operations.insert(operation.name.as_str(), operation);
        }
        effects.insert(&effect.name, (effect, operations));
    }

    for function in &program.functions {
        validate_expr(&function.body, &effects, &mut errors);
    }
    let effectful_functions = program
        .functions
        .iter()
        .filter(|function| {
            function.outward_effects.as_ref().is_some_and(|row| {
                effect_row_is_semantically_nonempty(
                    row,
                    &program
                        .effect_row_aliases
                        .iter()
                        .map(|alias| (alias.name.as_str(), alias))
                        .collect(),
                    &effects.keys().copied().collect(),
                    &mut HashSet::new(),
                )
            })
        })
        .map(|function| function.name.as_str())
        .collect::<HashSet<_>>();
    let nominal_types = program
        .structs
        .iter()
        .map(|declaration| declaration.name.as_str())
        .chain(
            program
                .enums
                .iter()
                .map(|declaration| declaration.name.as_str()),
        )
        .collect::<HashSet<_>>();
    let mut drop_targets = HashMap::<&str, Span>::new();
    for declaration in &program.drops {
        if !nominal_types.contains(declaration.target.as_str()) {
            errors.push(
                Diagnostic::error(
                    "Drop target is not nominal",
                    format!("`{}` is not a declared struct or enum", declaration.target),
                    declaration.span,
                )
                .with_code("G0200")
                .with_help("implement Drop for a nominal struct or enum declared in this module"),
            );
        }
        if let Some(original) = drop_targets.insert(&declaration.target, declaration.span) {
            errors.push(
                Diagnostic::error(
                    "Drop implemented more than once",
                    format!("`{}` already has a Drop hook", declaration.target),
                    declaration.span,
                )
                .with_code("G0201")
                .with_related(original, "the first implementation is here"),
            );
        }
        validate_expr(&declaration.body, &effects, &mut errors);
        if drop_body_has_forbidden_control(&declaration.body, &effectful_functions) {
            errors.push(
                Diagnostic::error(
                    "Drop hook can suspend or expose effects",
                    "Drop::drop must complete synchronously without outward effects",
                    declaration.body.span,
                )
                .with_code("G0202")
                .with_help("remove effectful calls, perform, resume, and cancel from this hook"),
            );
        }
    }
    for binding in &program.globals {
        validate_expr(&binding.value, &effects, &mut errors);
    }
    validate_source_lifetimes(program, &mut errors);
    validate_effect_row_binder_positions(program, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn validate_effect_row_binder_positions(program: &Program, errors: &mut Vec<Diagnostic>) {
    let mut reject = |generics: Option<&crate::frontend::ast::GenericParams>, context: &str| {
        for parameter in generics
            .into_iter()
            .flat_map(|generics| &generics.params)
            .filter(|parameter| parameter.kind == GenericParamKind::EffectRow)
        {
            errors.push(
                Diagnostic::error(
                    "effect-row binder outside callable",
                    format!("`EffectRow` binders are supported only on callable declarations, not {context}"),
                    parameter.span,
                )
                .with_code("G0009"),
            );
        }
    };
    for declaration in &program.type_aliases {
        reject(declaration.generics.as_ref(), "type aliases");
    }
    for declaration in &program.structs {
        reject(declaration.generics.as_ref(), "structs");
    }
    for declaration in &program.enums {
        reject(declaration.generics.as_ref(), "enums");
    }
    for declaration in &program.traits {
        reject(declaration.generics.as_ref(), "traits");
        for item in &declaration.associated_types {
            reject(item.generics.as_ref(), "associated types");
        }
    }
    for declaration in &program.impls {
        reject(declaration.generics.as_ref(), "trait implementations");
    }
    for declaration in &program.effects {
        reject(declaration.generics.as_ref(), "effect declarations");
    }
    for declaration in &program.drops {
        reject(declaration.generics.as_ref(), "Drop implementations");
    }
    for declaration in &program.uses {
        reject(declaration.generics.as_ref(), "Use declarations");
    }
}

fn validate_source_lifetimes(program: &Program, errors: &mut Vec<Diagnostic>) {
    for function in &program.functions {
        let lifetime_binders = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .filter(|parameter| parameter.kind == GenericParamKind::Lifetime)
            .map(|parameter| parameter.name.as_str())
            .collect::<HashSet<_>>();
        let non_lifetime_binders = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .filter(|parameter| parameter.kind != GenericParamKind::Lifetime)
            .map(|parameter| parameter.name.as_str())
            .collect::<HashSet<_>>();
        let known = |name: &str| name == "'static" || lifetime_binders.contains(name);
        for annotation in program.reference_lifetimes.iter().filter(|annotation| {
            function.span.start <= annotation.reference.start
                && annotation.reference.end <= function.span.end
        }) {
            let name = annotation.lifetime.name.as_str();
            if name == "'_" || known(name) {
                continue;
            }
            let detail = if non_lifetime_binders.contains(name) {
                format!("`{name}` is a type or const binder, not a lifetime binder")
            } else {
                format!(
                    "lifetime `{name}` is not bound by callable `{}`",
                    function.name
                )
            };
            errors.push(
                Diagnostic::error(
                    "unbound reference lifetime",
                    detail,
                    annotation.lifetime.span,
                )
                .with_code("G0008")
                .with_help("bind the lifetime in the callable's generic parameter list"),
            );
        }
        if let Some(where_clause) = &function.where_clause {
            for constraint in &where_clause.lifetime_outlives {
                for lifetime in [&constraint.longer, &constraint.shorter] {
                    if lifetime.name == "'_" {
                        errors.push(
                            Diagnostic::error(
                                "anonymous lifetime in outlives constraint",
                                "`'_` denotes a fresh inferred region and cannot name an outlives endpoint",
                                lifetime.span,
                            )
                            .with_code("G0008")
                            .with_help("use a named lifetime binder in this constraint"),
                        );
                    } else if !known(&lifetime.name) {
                        errors.push(
                            Diagnostic::error(
                                "unbound lifetime in outlives constraint",
                                format!(
                                    "lifetime `{}` is not bound by callable `{}`",
                                    lifetime.name, function.name
                                ),
                                lifetime.span,
                            )
                            .with_code("G0008"),
                        );
                    }
                }
                if constraint.shorter.name == "'static" && constraint.longer.name != "'static" {
                    errors.push(
                        Diagnostic::error(
                            "invalid static outlives constraint",
                            "only `'static` can be proven to outlive `'static`",
                            constraint.span,
                        )
                        .with_code("G0008"),
                    );
                }
            }
        }
    }

    for annotation in &program.reference_lifetimes {
        if program.functions.iter().any(|function| {
            function.span.start <= annotation.reference.start
                && annotation.reference.end <= function.span.end
        }) {
            continue;
        }
        if annotation.lifetime.name != "'static" {
            errors.push(
                Diagnostic::error(
                    "unsupported stored reference lifetime",
                    "named lifetimes in nominal fields require kinded nominal arguments and aggregate provenance",
                    annotation.lifetime.span,
                )
                .with_code("G0008")
                .with_help("this compiler slice supports named reference lifetimes at callable boundaries; use `'static` for stored references"),
            );
        }
    }
}

fn effect_row_is_semantically_nonempty(
    row: &crate::frontend::ast::EffectRowSyntax,
    aliases: &HashMap<&str, &crate::frontend::ast::EffectRowAliasDecl>,
    effects: &HashSet<&str>,
    visiting: &mut HashSet<String>,
) -> bool {
    row.effects.iter().any(|member| {
        let Some(name) = member.simple_name() else {
            return true;
        };
        if effects.contains(name) {
            return true;
        }
        let Some(alias) = aliases.get(name) else {
            return true;
        };
        if !visiting.insert(name.to_owned()) {
            return true;
        }
        let nonempty = effect_row_is_semantically_nonempty(&alias.row, aliases, effects, visiting);
        visiting.remove(name);
        nonempty
    })
}

fn drop_body_has_forbidden_control(expr: &Expr, effectful: &HashSet<&str>) -> bool {
    drop_body_has_outward_control(expr, effectful, &HashSet::new())
}

fn drop_body_has_outward_control(
    expr: &Expr,
    effectful: &HashSet<&str>,
    handled: &HashSet<(String, String)>,
) -> bool {
    match &expr.kind {
        ExprKind::Move(operand) => drop_body_has_outward_control(operand, effectful, handled),
        ExprKind::Perform {
            effect,
            operation,
            args,
        } => {
            !handled.contains(&(effect.to_string(), operation.to_string()))
                || args
                    .iter()
                    .any(|argument| drop_body_has_outward_control(argument, effectful, handled))
        }
        ExprKind::Call(callee, arguments) => {
            let forbidden_callee = matches!(
                &callee.kind,
                ExprKind::Variable(path)
                    if path.len() == 1
                        && (path[0].as_ref() == "resume"
                            || path[0].as_ref() == "cancel"
                            || effectful.contains(path[0].as_ref()))
            );
            forbidden_callee
                || drop_body_has_outward_control(callee, effectful, handled)
                || arguments
                    .iter()
                    .any(|argument| drop_body_has_outward_control(argument, effectful, handled))
        }
        ExprKind::List(values) | ExprKind::Tuple(values) => values
            .iter()
            .any(|value| drop_body_has_outward_control(value, effectful, handled)),
        ExprKind::Closure { body, .. } => drop_body_has_outward_control(body, effectful, handled),
        ExprKind::Struct { fields, .. } => fields
            .iter()
            .any(|(_, value)| drop_body_has_outward_control(value, effectful, handled)),
        ExprKind::Field(subject, _) => drop_body_has_outward_control(subject, effectful, handled),
        ExprKind::Block(statements) => statements.iter().any(|statement| match statement {
            Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                drop_body_has_outward_control(value, effectful, handled)
            }
        }),
        ExprKind::Handle {
            computation,
            clauses,
        } => {
            let mut computation_handled = handled.clone();
            for clause in clauses.iter() {
                if clause.patterns.iter().all(|pattern| {
                    matches!(
                        pattern.kind,
                        PatternKind::Wildcard | PatternKind::Binding(_)
                    )
                }) {
                    computation_handled.insert((clause.effect.clone(), clause.operation.clone()));
                }
            }
            drop_body_has_outward_control(computation, effectful, &computation_handled)
                || clauses
                    .iter()
                    .any(|clause| drop_body_has_outward_control(&clause.body, effectful, handled))
        }
        ExprKind::Unary { operand, .. } => {
            drop_body_has_outward_control(operand, effectful, handled)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            drop_body_has_outward_control(lhs, effectful, handled)
                || drop_body_has_outward_control(rhs, effectful, handled)
        }
        ExprKind::Unit | ExprKind::Int(_) | ExprKind::String(_) | ExprKind::Variable(_) => false,
    }
}

fn validate_expr(
    expr: &Expr,
    effects: &HashMap<&str, (&EffectDecl, HashMap<&str, &EffectOperationDecl>)>,
    errors: &mut Vec<Diagnostic>,
) {
    match &expr.kind {
        ExprKind::Move(operand) => validate_expr(operand, effects, errors),
        ExprKind::List(values) | ExprKind::Tuple(values) => values
            .iter()
            .for_each(|value| validate_expr(value, effects, errors)),
        ExprKind::Closure { body, .. } => validate_expr(body, effects, errors),
        ExprKind::Struct { fields, .. } => fields
            .iter()
            .for_each(|(_, value)| validate_expr(value, effects, errors)),
        ExprKind::Field(subject, _) => validate_expr(subject, effects, errors),
        ExprKind::Block(statements) => statements.iter().for_each(|statement| match statement {
            Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                validate_expr(value, effects, errors)
            }
        }),
        ExprKind::Call(callee, args) => {
            validate_expr(callee, effects, errors);
            args.iter()
                .for_each(|arg| validate_expr(arg, effects, errors));
        }
        ExprKind::Perform {
            effect,
            operation,
            args,
        } => {
            match effects.get(effect.as_ref()) {
                None => errors.push(
                    Diagnostic::error(
                        "unknown effect",
                        format!("`{effect}` has not been declared in this module"),
                        expr.span,
                    )
                    .with_code("G0100")
                    .with_help(format!("declare it with `effect {effect} {{ ... }}`")),
                ),
                Some((declaration, operations)) if !operations.contains_key(operation.as_ref()) => {
                    errors.push(
                        Diagnostic::error(
                            "unknown effect operation",
                            format!("effect `{effect}` has no operation named `{operation}`"),
                            expr.span,
                        )
                        .with_code("G0101")
                        .with_related(declaration.span, format!("`{effect}` is declared here"))
                        .with_help("use an operation declared by the effect interface"),
                    )
                }
                Some(_) => {}
            }
            args.iter()
                .for_each(|arg| validate_expr(arg, effects, errors));
        }
        ExprKind::Handle {
            computation,
            clauses,
        } => {
            validate_expr(computation, effects, errors);
            for clause in clauses.iter() {
                match effects
                    .get(clause.effect.as_str())
                    .and_then(|(_, operations)| operations.get(clause.operation.as_str()))
                {
                    None if !effects.contains_key(clause.effect.as_str()) => {
                        errors.push(
                            Diagnostic::error(
                                "unknown effect",
                                format!("`{}` has not been declared in this module", clause.effect),
                                clause.span,
                            )
                            .with_code("G0100")
                            .with_help(format!(
                                "declare it with `effect {} {{ ... }}`",
                                clause.effect
                            )),
                        );
                    }
                    None => {
                        let declaration = effects[clause.effect.as_str()].0;
                        errors.push(
                            Diagnostic::error(
                                "unknown effect operation",
                                format!(
                                    "effect `{}` has no operation named `{}`",
                                    clause.effect, clause.operation
                                ),
                                clause.span,
                            )
                            .with_code("G0101")
                            .with_related(
                                declaration.span,
                                format!("`{}` is declared here", clause.effect),
                            )
                            .with_help("use an operation declared by the effect interface"),
                        );
                    }
                    Some(operation) if operation.terminal && clause.resumption.is_some() => {
                        errors.push(
                            Diagnostic::error(
                                "terminal operation has no resumption",
                                format!(
                                    "`{}::{}` returns `!`, so this clause cannot bind a continuation",
                                    clause.effect, clause.operation
                                ),
                                clause.span,
                            )
                            .with_code("G0102")
                            .with_related(operation.span, "the terminal operation is declared here")
                            .with_help("remove the `with` resumption binding"),
                        );
                    }
                    Some(operation) if !operation.terminal && clause.resumption.is_none() => {
                        errors.push(
                            Diagnostic::error(
                                "resumptive handler must name its continuation",
                                format!(
                                    "`{}::{}` returns normally and captures the rest of the computation",
                                    clause.effect, clause.operation
                                ),
                                clause.span,
                            )
                            .with_code("G0103")
                            .with_related(operation.span, "the resumptive operation is declared here")
                            .with_help("write `with k => ...` and use `resume(k, value)` or `cancel(k)`"),
                        );
                    }
                    _ => {}
                }
                validate_expr(&clause.body, effects, errors);
            }
        }
        ExprKind::Unary { operand, .. } => validate_expr(operand, effects, errors),
        ExprKind::Binary { lhs, rhs, .. } => {
            validate_expr(lhs, effects, errors);
            validate_expr(rhs, effects, errors);
        }
        ExprKind::Unit | ExprKind::Int(_) | ExprKind::String(_) | ExprKind::Variable(_) => {}
    }
}
