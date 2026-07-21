use std::collections::{HashMap, HashSet};

use crate::{
    ast::{
        AssignmentPlaceKind, AssociatedBindingValue, EffectDecl, EffectOperationDecl, Expr,
        ExprKind, GenericParamKind, GoalArgument, PatternKind, Program, Stmt, TraitRefSyntax,
        TypeSyntax, TypeSyntaxKind, WhereClause,
    },
    diagnostic::Diagnostic,
    span::Span,
};

pub fn validate(program: &Program) -> Result<(), Vec<Diagnostic>> {
    let mut errors = Vec::new();
    // A declaration-only collection is syntactically valid; requiring an entry
    // callable is a program-level judgment, so it lives here, not in the parser.
    if program.functions.is_empty() {
        errors.push(Diagnostic::plain(
            "program has no callables; expected at least a `main() -> { ... }` declaration",
        ));
    }
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
            && !crate::compiler_traits::is_predefined(owner)
        {
            errors.push(
                Diagnostic::error(
                    "unknown associated binding owner",
                    format!(
                        "`{owner}` is not a declared type alias, nominal type, or predefined type"
                    ),
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
                    format!("`{name}` is declared more than once here"),
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
        let mut generic_names = HashMap::new();
        for parameter in effect.generics.iter().flat_map(|generics| &generics.params) {
            if let Some(original) = generic_names.insert(parameter.name.as_str(), parameter.span) {
                errors.push(
                    Diagnostic::error(
                        "effect parameter declared more than once",
                        format!("generic parameter `{}` is repeated", parameter.name),
                        parameter.span,
                    )
                    .with_code("G0113")
                    .with_related(original, "the first parameter is here"),
                );
            }
        }
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
        let generic_kinds = function
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .map(|parameter| (parameter.name.as_str(), parameter.kind))
            .collect();
        validate_expr(
            program,
            &function.body,
            &effects,
            &generic_kinds,
            &mut errors,
        );
        validate_label_scopes(&function.body, &mut errors);
    }
    validate_trait_methods(program, &effects, &mut errors);
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
    let type_aliases = program
        .type_aliases
        .iter()
        .map(|declaration| (declaration.name.as_str(), declaration))
        .collect::<HashMap<_, _>>();
    fn canonical_drop_target(
        name: &str,
        aliases: &HashMap<&str, &crate::ast::TypeAliasDecl>,
        nominals: &HashSet<&str>,
        visiting: &mut HashSet<String>,
    ) -> Option<String> {
        if nominals.contains(name) {
            return Some(name.to_owned());
        }
        let alias = aliases.get(name)?;
        if !visiting.insert(name.to_owned()) {
            return None;
        }
        let target = match &alias.target.kind {
            crate::ast::TypeSyntaxKind::Path(path) if path.len() == 1 => {
                canonical_drop_target(&path[0].name, aliases, nominals, visiting)
            }
            crate::ast::TypeSyntaxKind::Application { constructor, .. } => constructor
                .simple_name()
                .and_then(|target| canonical_drop_target(target, aliases, nominals, visiting)),
            _ => None,
        };
        visiting.remove(name);
        target
    }
    let mut drop_targets = HashMap::<String, Span>::new();
    for declaration in &program.drops {
        let canonical_target = canonical_drop_target(
            &declaration.target,
            &type_aliases,
            &nominal_types,
            &mut HashSet::new(),
        );
        if canonical_target.is_none() {
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
        if declaration.generics.is_none()
            && let Some(canonical_target) = canonical_target
            && let Some(original) = drop_targets.insert(canonical_target, declaration.span)
        {
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
        validate_expr(
            program,
            &declaration.body,
            &effects,
            &HashMap::new(),
            &mut errors,
        );
        validate_label_scopes(&declaration.body, &mut errors);
        if drop_body_has_forbidden_control(program, &declaration.body, &effectful_functions) {
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
        validate_expr(
            program,
            &binding.value,
            &effects,
            &HashMap::new(),
            &mut errors,
        );
        validate_label_scopes(&binding.value, &mut errors);
    }
    validate_source_lifetimes(program, &mut errors);
    validate_effect_row_binder_positions(program, &mut errors);
    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

fn validate_trait_methods(
    program: &Program,
    effects: &HashMap<&str, (&EffectDecl, HashMap<&str, &EffectOperationDecl>)>,
    errors: &mut Vec<Diagnostic>,
) {
    fn mapped_name<'a>(name: &'a str, binders: &'a HashMap<&str, &str>) -> &'a str {
        binders.get(name).copied().unwrap_or(name)
    }

    fn same_type(
        template: &TypeSyntax,
        actual: &TypeSyntax,
        self_ty: &TypeSyntax,
        binders: &HashMap<&str, &str>,
        trait_arguments: &HashMap<&str, &TypeSyntax>,
    ) -> bool {
        if template.simple_name() == Some("Self") {
            return same_type(self_ty, actual, self_ty, binders, trait_arguments);
        }
        if let Some(name) = template.simple_name() {
            if let Some(mapped) = binders.get(name) {
                return actual.simple_name() == Some(*mapped);
            }
            if let Some(argument) = trait_arguments.get(name) {
                return same_type(argument, actual, self_ty, binders, trait_arguments);
            }
        }
        match (&template.kind, &actual.kind) {
            (TypeSyntaxKind::Never, TypeSyntaxKind::Never) => true,
            (TypeSyntaxKind::Path(left), TypeSyntaxKind::Path(right)) => left
                .iter()
                .map(|segment| mapped_name(&segment.name, binders))
                .eq(right.iter().map(|segment| segment.name.as_str())),
            (TypeSyntaxKind::SharedReference(left), TypeSyntaxKind::SharedReference(right))
            | (TypeSyntaxKind::UniqueReference(left), TypeSyntaxKind::UniqueReference(right)) => {
                same_type(left, right, self_ty, binders, trait_arguments)
            }
            (TypeSyntaxKind::Tuple(left), TypeSyntaxKind::Tuple(right)) => {
                left.len() == right.len()
                    && left.iter().zip(right).all(|(left, right)| {
                        same_type(left, right, self_ty, binders, trait_arguments)
                    })
            }
            (
                TypeSyntaxKind::Application {
                    constructor: left_constructor,
                    arguments: left,
                    ..
                },
                TypeSyntaxKind::Application {
                    constructor: right_constructor,
                    arguments: right,
                    ..
                },
            ) => {
                same_type(
                    left_constructor,
                    right_constructor,
                    self_ty,
                    binders,
                    trait_arguments,
                ) && left.len() == right.len()
                    && left.iter().zip(right).all(|(left, right)| {
                        same_type(left, right, self_ty, binders, trait_arguments)
                    })
            }
            _ => false,
        }
    }

    fn same_trait_ref(
        template: &TraitRefSyntax,
        actual: &TraitRefSyntax,
        self_ty: &TypeSyntax,
        binders: &HashMap<&str, &str>,
        trait_arguments: &HashMap<&str, &TypeSyntax>,
    ) -> bool {
        template
            .path
            .iter()
            .map(|segment| segment.name.as_str())
            .eq(actual.path.iter().map(|segment| segment.name.as_str()))
            && template.arguments.len() == actual.arguments.len()
            && template
                .arguments
                .iter()
                .zip(&actual.arguments)
                .all(|(template, actual)| match (template, actual) {
                    (GoalArgument::Type(template), GoalArgument::Type(actual)) => {
                        same_type(template, actual, self_ty, binders, trait_arguments)
                    }
                    (
                        GoalArgument::Lifetime { name: template, .. },
                        GoalArgument::Lifetime { name: actual, .. },
                    ) => mapped_name(template, binders) == actual,
                    (GoalArgument::Quantity(template), GoalArgument::Quantity(actual)) => {
                        template.lower == actual.lower && template.upper == actual.upper
                    }
                    (
                        GoalArgument::U32 {
                            value: template, ..
                        },
                        GoalArgument::U32 { value: actual, .. },
                    ) => template == actual,
                    _ => false,
                })
            && template.bindings.len() == actual.bindings.len()
            && template
                .bindings
                .iter()
                .zip(&actual.bindings)
                .all(|(template, actual)| {
                    template.name == actual.name
                        && template.arguments.len() == actual.arguments.len()
                        && template.arguments.iter().zip(&actual.arguments).all(
                            |(template, actual)| match (template, actual) {
                                (
                                    crate::ast::AssociatedArgumentSyntax::Type(template),
                                    crate::ast::AssociatedArgumentSyntax::Type(actual),
                                ) => same_type(template, actual, self_ty, binders, trait_arguments),
                                (
                                    crate::ast::AssociatedArgumentSyntax::Lifetime {
                                        name: template,
                                        ..
                                    },
                                    crate::ast::AssociatedArgumentSyntax::Lifetime {
                                        name: actual,
                                        ..
                                    },
                                ) => mapped_name(template, binders) == actual,
                                _ => false,
                            },
                        )
                        && match (&template.value, &actual.value) {
                            (
                                AssociatedBindingValue::Type(template),
                                AssociatedBindingValue::Type(actual),
                            ) => same_type(template, actual, self_ty, binders, trait_arguments),
                            _ => false,
                        }
                })
    }

    fn same_where_clause(
        template: Option<&WhereClause>,
        actual: Option<&WhereClause>,
        self_ty: &TypeSyntax,
        binders: &HashMap<&str, &str>,
        trait_arguments: &HashMap<&str, &TypeSyntax>,
    ) -> bool {
        let empty_template = template
            .is_none_or(|clause| clause.goals.is_empty() && clause.lifetime_outlives.is_empty());
        let empty_actual = actual
            .is_none_or(|clause| clause.goals.is_empty() && clause.lifetime_outlives.is_empty());
        if empty_template || empty_actual {
            return empty_template == empty_actual;
        }
        let (Some(template), Some(actual)) = (template, actual) else {
            return false;
        };
        if template.goals.len() != actual.goals.len()
            || template.lifetime_outlives.len() != actual.lifetime_outlives.len()
        {
            return false;
        }
        let mut matched_goals = vec![false; actual.goals.len()];
        for template in &template.goals {
            let Some((index, _)) = actual.goals.iter().enumerate().find(|(index, actual)| {
                if matched_goals[*index]
                    || template.polarity != actual.polarity
                    || template.higher_ranked_lifetimes.len()
                        != actual.higher_ranked_lifetimes.len()
                    || !template
                        .higher_ranked_lifetimes
                        .iter()
                        .zip(&actual.higher_ranked_lifetimes)
                        .all(|(template, actual)| template.kind == actual.kind)
                {
                    return false;
                }
                let mut goal_binders = binders.clone();
                goal_binders.extend(
                    template
                        .higher_ranked_lifetimes
                        .iter()
                        .zip(&actual.higher_ranked_lifetimes)
                        .map(|(template, actual)| (template.name.as_str(), actual.name.as_str())),
                );
                same_type(
                    &template.subject,
                    &actual.subject,
                    self_ty,
                    &goal_binders,
                    trait_arguments,
                ) && same_trait_ref(
                    &template.relation,
                    &actual.relation,
                    self_ty,
                    &goal_binders,
                    trait_arguments,
                )
            }) else {
                return false;
            };
            matched_goals[index] = true;
        }
        let mut matched_outlives = vec![false; actual.lifetime_outlives.len()];
        for template in &template.lifetime_outlives {
            let Some((index, _)) =
                actual
                    .lifetime_outlives
                    .iter()
                    .enumerate()
                    .find(|(index, actual)| {
                        !matched_outlives[*index]
                            && mapped_name(&template.longer.name, binders) == actual.longer.name
                            && mapped_name(&template.shorter.name, binders) == actual.shorter.name
                    })
            else {
                return false;
            };
            matched_outlives[index] = true;
        }
        true
    }

    for implementation in &program.impls {
        let Some(trait_name) = implementation
            .trait_ref
            .path
            .first()
            .filter(|_| implementation.trait_ref.path.len() == 1)
            .map(|segment| segment.name.as_str())
        else {
            continue;
        };
        let Some(trait_decl) = program.traits.iter().find(|item| item.name == trait_name) else {
            continue;
        };
        let trait_arguments = trait_decl
            .generics
            .iter()
            .flat_map(|generics| &generics.params)
            .zip(&implementation.trait_ref.arguments)
            .filter_map(|(parameter, argument)| match argument {
                GoalArgument::Type(argument) if parameter.kind == GenericParamKind::Type => {
                    Some((parameter.name.as_str(), argument))
                }
                _ => None,
            })
            .collect::<HashMap<_, _>>();
        if implementation.polarity == crate::ast::GoalPolarity::Negative
            && !implementation.methods.is_empty()
        {
            errors.push(
                Diagnostic::error(
                    "negative implementation defines methods",
                    "negative trait implementations cannot contain method bodies",
                    implementation.span,
                )
                .with_code("G0140"),
            );
            // A negative impl has no value-level contract to compare. Keep
            // this as the single primary diagnostic instead of cascading
            // missing/unknown/signature errors for every enclosed body.
            continue;
        }
        for declared in &trait_decl.methods {
            let Some(defined) = implementation
                .methods
                .iter()
                .find(|method| method.name == declared.name)
            else {
                if implementation.polarity == crate::ast::GoalPolarity::Positive {
                    errors.push(
                        Diagnostic::error(
                            "missing trait method",
                            format!(
                                "implementation of `{trait_name}` is missing `{}`",
                                declared.name
                            ),
                            implementation.span,
                        )
                        .with_code("G0141")
                        .with_related(declared.span, "the method is declared here"),
                    );
                }
                continue;
            };
            let declared_generics = declared
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .collect::<Vec<_>>();
            let defined_generics = defined
                .generics
                .iter()
                .flat_map(|generics| &generics.params)
                .collect::<Vec<_>>();
            let same_binders = declared_generics.len() == defined_generics.len()
                && declared_generics
                    .iter()
                    .zip(&defined_generics)
                    .all(|(declared, defined)| declared.kind == defined.kind);
            let binders = declared_generics
                .iter()
                .zip(&defined_generics)
                .map(|(declared, defined)| (declared.name.as_str(), defined.name.as_str()))
                .collect::<HashMap<_, _>>();
            let same_params = declared.params.len() == defined.params.len()
                && declared
                    .params
                    .iter()
                    .zip(&defined.params)
                    .all(|(left, right)| {
                        same_type(
                            &left.ty,
                            &right.ty,
                            &implementation.self_ty,
                            &binders,
                            &trait_arguments,
                        )
                    });
            let same_result = match (&declared.return_type, &defined.return_type) {
                (None, None) => true,
                (Some(left), Some(right)) => same_type(
                    left,
                    right,
                    &implementation.self_ty,
                    &binders,
                    &trait_arguments,
                ),
                _ => false,
            };
            let same_effects = match (&declared.outward_effects, &defined.outward_effects) {
                (None, None) => true,
                (Some(declared), Some(defined)) => {
                    declared.effects.len() == defined.effects.len()
                        && declared.effects.iter().zip(&defined.effects).all(
                            |(declared, defined)| {
                                same_type(
                                    declared,
                                    defined,
                                    &implementation.self_ty,
                                    &binders,
                                    &trait_arguments,
                                )
                            },
                        )
                        && declared
                            .tail
                            .as_ref()
                            .map(|tail| mapped_name(&tail.name, &binders))
                            == defined.tail.as_ref().map(|tail| tail.name.as_str())
                }
                _ => false,
            };
            let same_where = same_where_clause(
                declared.where_clause.as_ref(),
                defined.where_clause.as_ref(),
                &implementation.self_ty,
                &binders,
                &trait_arguments,
            );
            if !same_binders || !same_params || !same_result || !same_effects || !same_where {
                errors.push(
                    Diagnostic::error(
                        "trait method signature mismatch",
                        format!(
                            "method `{}` does not match its declaration in `{trait_name}`",
                            defined.name
                        ),
                        defined.span,
                    )
                    .with_code("G0142")
                    .with_related(declared.span, "the required signature is declared here"),
                );
            }
        }
        for defined in &implementation.methods {
            if !trait_decl
                .methods
                .iter()
                .any(|method| method.name == defined.name)
            {
                errors.push(
                    Diagnostic::error(
                        "unknown trait method",
                        format!("trait `{trait_name}` has no method `{}`", defined.name),
                        defined.span,
                    )
                    .with_code("G0143"),
                );
            }
            if let Some(body) = &defined.body {
                let generic_kinds = implementation
                    .generics
                    .iter()
                    .flat_map(|generics| &generics.params)
                    .chain(
                        defined
                            .generics
                            .iter()
                            .flat_map(|generics| &generics.params),
                    )
                    .map(|parameter| (parameter.name.as_str(), parameter.kind))
                    .collect();
                validate_expr(program, body, effects, &generic_kinds, errors);
                validate_label_scopes(body, errors);
            }
        }
    }
}

#[derive(Clone, Copy)]
struct ActiveLabel<'a> {
    binder: Span,
    direct_destination: bool,
    destination: Option<&'a TypeSyntax>,
}

fn validate_label_scopes(expression: &Expr, errors: &mut Vec<Diagnostic>) {
    fn obvious_value_kind(value: Option<&Expr>) -> Option<&'static str> {
        match value.map(|value| &value.kind) {
            None | Some(ExprKind::Unit) => Some("Unit"),
            Some(ExprKind::Int(_)) => Some("integer"),
            Some(ExprKind::String(_)) => Some("Text"),
            Some(ExprKind::Char(_)) => Some("Char"),
            Some(ExprKind::Byte(_)) => Some("u8"),
            Some(ExprKind::ByteString(_)) => Some("Bytes"),
            _ => None,
        }
    }

    fn destination_accepts(ty: Option<&TypeSyntax>, value: Option<&Expr>) -> bool {
        let actual = obvious_value_kind(value);
        let Some(ty) = ty else {
            return actual == Some("Unit");
        };
        match (&ty.kind, actual) {
            (TypeSyntaxKind::Never, _) => false,
            (TypeSyntaxKind::Tuple(elements), Some("Unit")) => elements.is_empty(),
            (TypeSyntaxKind::Path(_), Some("integer")) => ty.simple_name().is_some_and(|name| {
                matches!(
                    name,
                    "i8" | "i16" | "i32" | "i64" | "i128" | "u8" | "u16" | "u32" | "u64" | "u128"
                )
            }),
            (TypeSyntaxKind::Path(_), Some(actual)) => ty.simple_name() == Some(actual),
            (_, None) => true,
            _ => false,
        }
    }

    fn visit<'a>(
        expression: &'a Expr,
        labels: &mut HashMap<String, ActiveLabel<'a>>,
        errors: &mut Vec<Diagnostic>,
    ) {
        let bind = |label: &'a crate::ast::LabelSyntax,
                    direct_destination: bool,
                    destination: Option<&'a TypeSyntax>,
                    body: &'a Expr,
                    labels: &mut HashMap<String, ActiveLabel<'a>>,
                    errors: &mut Vec<Diagnostic>| {
            if let Some(previous) = labels.get(label.name.as_ref()) {
                errors.push(
                    Diagnostic::error(
                        "duplicate active label",
                        format!("label `@{}` is already active in this lexical scope", label.name),
                        label.span,
                    )
                    .with_code("G0131")
                    .with_related(previous.binder, "the active label is introduced here")
                    .with_help("rename one label; label identities are generative and cannot shadow an active brand"),
                );
                visit(body, labels, errors);
                return;
            }
            labels.insert(
                label.name.to_string(),
                ActiveLabel {
                    binder: label.span,
                    direct_destination,
                    destination,
                },
            );
            visit(body, labels, errors);
            labels.remove(label.name.as_ref());
        };

        match &expression.kind {
            ExprKind::Labeled { label, body } => bind(label, false, None, body, labels, errors),
            ExprKind::LabelDestination { label, ty, body } => {
                bind(label, true, ty.as_deref(), body, labels, errors)
            }
            ExprKind::LabelReference(label) => {
                if !labels.contains_key(label.name.as_ref()) {
                    errors.push(
                        Diagnostic::error(
                            "unknown label",
                            format!("label `@{}` is not active here", label.name),
                            label.span,
                        )
                        .with_code("G0132")
                        .with_help("move this use inside the label body or introduce a label with that name"),
                    );
                }
            }
            ExprKind::Leave { label, value } => {
                match labels.get(label.name.as_ref()) {
                    None => errors.push(
                        Diagnostic::error(
                            "unknown leave destination",
                            format!("`leave@{}` has no active lexical destination", label.name),
                            label.span,
                        )
                        .with_code("G0132"),
                    ),
                    Some(active) if !active.direct_destination => errors.push(
                        Diagnostic::error(
                            "label is not a direct destination",
                            format!(
                                "`@{}` introduces a label brand but no `Destination` evidence",
                                label.name
                            ),
                            label.span,
                        )
                        .with_code("G0133")
                        .with_related(active.binder, "this generative label is introduced here")
                        .with_help(
                            "use `label @name: Type { ... }` for a direct typed destination",
                        ),
                    ),
                    Some(active) if !destination_accepts(active.destination, value.as_deref()) => {
                        errors.push(
                            Diagnostic::error(
                                "leave value does not match destination",
                                format!("`leave@{}` supplies an incompatible value", label.name),
                                value.as_deref().map_or(label.span, |value| value.span),
                            )
                            .with_code("G0134")
                            .with_related(
                                active.binder,
                                "the typed destination is introduced here",
                            ),
                        );
                    }
                    Some(_) => {}
                }
                if let Some(value) = value {
                    visit(value, labels, errors);
                }
            }
            ExprKind::Move(value)
            | ExprKind::Field(value, _)
            | ExprKind::Unary { operand: value, .. } => visit(value, labels, errors),
            ExprKind::Closure { body, .. } | ExprKind::TypedClosure { body, .. } => {
                visit(body, labels, errors)
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    visit(value, labels, errors);
                }
            }
            ExprKind::Struct { fields, .. } => {
                for (_, value) in fields.iter() {
                    visit(value, labels, errors);
                }
            }
            ExprKind::Block(statements) | ExprKind::ContextBlock(statements) => {
                for statement in statements.iter() {
                    match statement {
                        Stmt::Let { value, .. }
                        | Stmt::Deconstruct { value, .. }
                        | Stmt::Expr(value) => visit(value, labels, errors),
                        Stmt::Assign {
                            destination, value, ..
                        } => {
                            visit(value, labels, errors);
                            if let AssignmentPlaceKind::Dereference { reference, .. } =
                                &destination.kind
                            {
                                visit(reference, labels, errors);
                            }
                        }
                    }
                }
            }
            ExprKind::Call(callee, arguments) => {
                visit(callee, labels, errors);
                for argument in arguments.iter() {
                    visit(argument, labels, errors);
                }
            }
            ExprKind::Perform { args, .. } => {
                for argument in args.iter() {
                    visit(argument, labels, errors);
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                visit(computation, labels, errors);
                for clause in clauses.iter() {
                    visit(&clause.body, labels, errors);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                visit(lhs, labels, errors);
                visit(rhs, labels, errors);
            }
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                visit(resumption, labels, errors);
                if let Some(value) = value {
                    visit(value, labels, errors);
                }
            }
            ExprKind::Cancel { resumption } => visit(resumption, labels, errors),
            ExprKind::Is { subject, .. } => visit(subject, labels, errors),
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::Variable(_) => {}
        }
    }

    visit(expression, &mut HashMap::new(), errors);
}

fn validate_effect_row_binder_positions(program: &Program, errors: &mut Vec<Diagnostic>) {
    let mut reject = |generics: Option<&crate::ast::GenericParams>, context: &str| {
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
            if item.kind != crate::ast::AssociatedItemSyntaxKind::EffectRow {
                reject(item.generics.as_ref(), "associated types");
            }
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
    let nominal_generics = program
        .structs
        .iter()
        .map(|declaration| (declaration.name.as_str(), declaration.generics.as_ref()))
        .chain(
            program
                .enums
                .iter()
                .map(|declaration| (declaration.name.as_str(), declaration.generics.as_ref())),
        )
        .collect::<HashMap<_, _>>();

    fn validate_nominal_arguments(
        syntax: &TypeSyntax,
        scope: Option<&crate::ast::GenericParams>,
        nominals: &HashMap<&str, Option<&crate::ast::GenericParams>>,
        const_applications: &[crate::ast::TypeConstApplicationSyntax],
        errors: &mut Vec<Diagnostic>,
    ) {
        match &syntax.kind {
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                lifetime_arguments,
            } => {
                if let Some(name) = constructor.simple_name()
                    && let Some(Some(declared)) = nominals.get(name)
                {
                    let const_arguments = const_applications
                        .iter()
                        .find(|entry| entry.application == syntax.span)
                        .map_or(&[][..], |entry| entry.arguments.as_slice());
                    let supplied =
                        arguments.len() + lifetime_arguments.len() + const_arguments.len();
                    if supplied != declared.params.len() {
                        errors.push(
                            Diagnostic::error(
                                "wrong number of nominal arguments",
                                format!(
                                    "nominal `{name}` expects {} generic argument(s), but this application supplies {supplied}",
                                    declared.params.len()
                                ),
                                syntax.span,
                            )
                            .with_code("G0008")
                            .with_related(declared.span, "the generic binders are declared here"),
                        );
                    } else {
                        let lifetime_positions = lifetime_arguments
                            .iter()
                            .map(|argument| argument.position)
                            .collect::<HashSet<_>>();
                        let const_positions = const_arguments
                            .iter()
                            .map(|argument| argument.position)
                            .collect::<HashSet<_>>();
                        let scope_lifetimes = scope
                            .iter()
                            .flat_map(|generics| &generics.params)
                            .filter(|parameter| parameter.kind == GenericParamKind::Lifetime)
                            .map(|parameter| parameter.name.as_str())
                            .collect::<HashSet<_>>();
                        for argument in lifetime_arguments {
                            if declared
                                .params
                                .get(argument.position)
                                .is_none_or(|parameter| {
                                    parameter.kind != GenericParamKind::Lifetime
                                })
                            {
                                errors.push(
                                    Diagnostic::error(
                                        "nominal argument kind mismatch",
                                        format!(
                                            "lifetime `{}` is supplied for a non-lifetime binder of `{name}`",
                                            argument.lifetime.name
                                        ),
                                        argument.lifetime.span,
                                    )
                                    .with_code("G0008"),
                                );
                            }
                            if argument.lifetime.name != "'static"
                                && !scope_lifetimes.contains(argument.lifetime.name.as_str())
                            {
                                errors.push(
                                    Diagnostic::error(
                                        "unbound nominal lifetime argument",
                                        format!(
                                            "lifetime `{}` is not bound in this declaration",
                                            argument.lifetime.name
                                        ),
                                        argument.lifetime.span,
                                    )
                                    .with_code("G0008"),
                                );
                            }
                        }
                        for argument in const_arguments {
                            let Some(parameter) = declared.params.get(argument.position) else {
                                continue;
                            };
                            let actual_kind = match &argument.value {
                                crate::ast::ConstArgumentValueSyntax::Quantity(_) => {
                                    crate::ast::ConstKind::Quantity
                                }
                                crate::ast::ConstArgumentValueSyntax::U32 { value, span } => {
                                    if u32::try_from(*value).is_err() {
                                        errors.push(
                                            Diagnostic::error(
                                                "const argument exceeds its domain",
                                                "u32 const arguments must fit in 32 bits",
                                                *span,
                                            )
                                            .with_code("G0008"),
                                        );
                                    }
                                    crate::ast::ConstKind::U32
                                }
                            };
                            if parameter.kind != GenericParamKind::Const(actual_kind) {
                                errors.push(
                                    Diagnostic::error(
                                        "nominal argument kind mismatch",
                                        format!(
                                            "const argument has kind {actual_kind:?}, but binder `{}` of `{name}` has kind {:?}",
                                            parameter.name, parameter.kind
                                        ),
                                        argument.value.span(),
                                    )
                                    .with_code("G0008"),
                                );
                            }
                        }
                        let mut type_arguments = arguments.iter();
                        for (position, parameter) in declared.params.iter().enumerate() {
                            if lifetime_positions.contains(&position)
                                || const_positions.contains(&position)
                            {
                                continue;
                            }
                            let Some(argument) = type_arguments.next() else {
                                break;
                            };
                            match parameter.kind {
                                GenericParamKind::Type => {}
                                GenericParamKind::Const(expected_kind) => {
                                    let bound = argument.simple_name().and_then(|argument_name| {
                                        scope
                                            .iter()
                                            .flat_map(|scope| &scope.params)
                                            .find(|candidate| candidate.name == argument_name)
                                    });
                                    if bound.is_none_or(|bound| {
                                        bound.kind != GenericParamKind::Const(expected_kind)
                                    }) {
                                        errors.push(
                                            Diagnostic::error(
                                                "nominal const argument kind mismatch",
                                                format!(
                                                    "binder `{}` of `{name}` requires a {expected_kind:?} const literal or in-scope const parameter",
                                                    parameter.name
                                                ),
                                                argument.span,
                                            )
                                            .with_code("G0008"),
                                        );
                                    }
                                }
                                _ => {
                                    errors.push(
                                        Diagnostic::error(
                                            "nominal argument kind mismatch",
                                            format!(
                                                "type argument is supplied for non-type binder `{}` of `{name}`",
                                                parameter.name
                                            ),
                                            argument.span,
                                        )
                                        .with_code("G0008"),
                                    );
                                }
                            }
                        }
                    }
                }
                validate_nominal_arguments(
                    constructor,
                    scope,
                    nominals,
                    const_applications,
                    errors,
                );
                for argument in arguments {
                    validate_nominal_arguments(
                        argument,
                        scope,
                        nominals,
                        const_applications,
                        errors,
                    );
                }
            }
            TypeSyntaxKind::SharedReference(referent)
            | TypeSyntaxKind::UniqueReference(referent) => {
                validate_nominal_arguments(referent, scope, nominals, const_applications, errors)
            }
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    validate_nominal_arguments(
                        element,
                        scope,
                        nominals,
                        const_applications,
                        errors,
                    );
                }
            }
            TypeSyntaxKind::Projection {
                subject, arguments, ..
            } => {
                validate_nominal_arguments(subject, scope, nominals, const_applications, errors);
                for argument in arguments {
                    if let crate::ast::AssociatedArgumentSyntax::Type(argument) = argument {
                        validate_nominal_arguments(
                            argument,
                            scope,
                            nominals,
                            const_applications,
                            errors,
                        );
                    }
                }
            }
            TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        }
    }

    fn reject_const_binder_in_type_position(
        syntax: &TypeSyntax,
        scope: Option<&crate::ast::GenericParams>,
        nominals: &HashMap<&str, Option<&crate::ast::GenericParams>>,
        const_applications: &[crate::ast::TypeConstApplicationSyntax],
        errors: &mut Vec<Diagnostic>,
    ) {
        let const_binder = |name: &str| {
            scope
                .into_iter()
                .flat_map(|generics| &generics.params)
                .find(|parameter| {
                    parameter.name == name && matches!(parameter.kind, GenericParamKind::Const(_))
                })
        };
        match &syntax.kind {
            TypeSyntaxKind::Path(path) if path.len() == 1 => {
                if let Some(parameter) = const_binder(&path[0].name) {
                    errors.push(
                        Diagnostic::error(
                            "const parameter used as a runtime type",
                            format!(
                                "const parameter `{}` may only appear in a declared const argument position",
                                parameter.name
                            ),
                            syntax.span,
                        )
                        .with_code("G0008")
                        .with_related(parameter.span, "the const parameter is declared here"),
                    );
                }
            }
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                lifetime_arguments,
            } => {
                reject_const_binder_in_type_position(
                    constructor,
                    scope,
                    nominals,
                    const_applications,
                    errors,
                );
                let const_positions = const_applications
                    .iter()
                    .find(|entry| entry.application == syntax.span)
                    .map_or_else(HashSet::new, |entry| {
                        entry
                            .arguments
                            .iter()
                            .map(|argument| argument.position)
                            .collect()
                    });
                let lifetime_positions = lifetime_arguments
                    .iter()
                    .map(|argument| argument.position)
                    .collect::<HashSet<_>>();
                let declared = constructor
                    .simple_name()
                    .and_then(|name| nominals.get(name))
                    .copied()
                    .flatten();
                let mut source_arguments = arguments.iter();
                let total = arguments.len() + const_positions.len() + lifetime_positions.len();
                for position in 0..total {
                    if const_positions.contains(&position) || lifetime_positions.contains(&position)
                    {
                        continue;
                    }
                    let Some(argument) = source_arguments.next() else {
                        break;
                    };
                    if declared
                        .and_then(|generics| generics.params.get(position))
                        .is_some_and(|parameter| {
                            matches!(parameter.kind, GenericParamKind::Const(_))
                        })
                    {
                        continue;
                    }
                    reject_const_binder_in_type_position(
                        argument,
                        scope,
                        nominals,
                        const_applications,
                        errors,
                    );
                }
            }
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    reject_const_binder_in_type_position(
                        element,
                        scope,
                        nominals,
                        const_applications,
                        errors,
                    );
                }
            }
            TypeSyntaxKind::SharedReference(referent)
            | TypeSyntaxKind::UniqueReference(referent) => reject_const_binder_in_type_position(
                referent,
                scope,
                nominals,
                const_applications,
                errors,
            ),
            // Associated-type arguments are kind-checked against their GAT
            // schema during trait lowering, where const positions are known.
            TypeSyntaxKind::Projection { subject, .. } => reject_const_binder_in_type_position(
                subject,
                scope,
                nominals,
                const_applications,
                errors,
            ),
            TypeSyntaxKind::Path(_) | TypeSyntaxKind::Never => {}
        }
    }

    for function in &program.functions {
        for parameter in &function.params {
            validate_nominal_arguments(
                &parameter.ty,
                function.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
            reject_const_binder_in_type_position(
                &parameter.ty,
                function.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
        }
        if let Some(result) = &function.return_type {
            validate_nominal_arguments(
                result,
                function.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
            reject_const_binder_in_type_position(
                result,
                function.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
        }
    }
    for declaration in &program.structs {
        for field in &declaration.fields {
            validate_nominal_arguments(
                &field.ty,
                declaration.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
            reject_const_binder_in_type_position(
                &field.ty,
                declaration.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
        }
    }
    for declaration in &program.enums {
        for field in declaration
            .variants
            .iter()
            .flat_map(|variant| &variant.fields)
        {
            validate_nominal_arguments(
                field,
                declaration.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
            reject_const_binder_in_type_position(
                field,
                declaration.generics.as_ref(),
                &nominal_generics,
                &program.type_const_arguments,
                errors,
            );
        }
    }

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
        let containing_nominal = program
            .structs
            .iter()
            .map(|declaration| (declaration.span, declaration.generics.as_ref()))
            .chain(
                program
                    .enums
                    .iter()
                    .map(|declaration| (declaration.span, declaration.generics.as_ref())),
            )
            .find(|(span, _)| {
                span.start <= annotation.reference.start && annotation.reference.end <= span.end
            });
        let bound_by_nominal = containing_nominal.is_some_and(|(_, generics)| {
            generics.is_some_and(|generics| {
                generics.params.iter().any(|parameter| {
                    parameter.kind == GenericParamKind::Lifetime
                        && parameter.name == annotation.lifetime.name
                })
            })
        });
        if annotation.lifetime.name != "'static" && !bound_by_nominal {
            errors.push(
                Diagnostic::error(
                    "unbound stored reference lifetime",
                    format!(
                        "lifetime `{}` is not bound by the containing nominal declaration",
                        annotation.lifetime.name
                    ),
                    annotation.lifetime.span,
                )
                .with_code("G0008")
                .with_help("bind the lifetime on the struct or enum that stores this reference"),
            );
        }
    }

    // One Core origin can faithfully represent one stored loan. Reject layouts
    // with multiple independently usable reference fields until aggregate
    // provenance becomes a path-indexed origin map.
    for (name, span, fields) in program
        .structs
        .iter()
        .map(|declaration| {
            (
                declaration.name.as_str(),
                declaration.span,
                declaration
                    .fields
                    .iter()
                    .map(|field| &field.ty)
                    .collect::<Vec<_>>(),
            )
        })
        .chain(program.enums.iter().map(|declaration| {
            (
                declaration.name.as_str(),
                declaration.span,
                declaration
                    .variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .collect::<Vec<_>>(),
            )
        }))
    {
        let stored = fields
            .iter()
            .filter(|field| {
                matches!(
                    field.kind,
                    TypeSyntaxKind::SharedReference(_) | TypeSyntaxKind::UniqueReference(_)
                ) && program.reference_lifetime(field.span).is_some()
            })
            .count();
        if stored > 1 {
            errors.push(
                Diagnostic::error(
                    "multiple stored reference origins",
                    format!(
                        "nominal `{name}` stores {stored} independently projectable references; this requires path-indexed aggregate provenance"
                    ),
                    span,
                )
                .with_code("G0008"),
            );
        }
    }
}

fn effect_row_is_semantically_nonempty(
    row: &crate::ast::EffectRowSyntax,
    aliases: &HashMap<&str, &crate::ast::EffectRowAliasDecl>,
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

fn effect_instance_text(program: &Program, site: Span, fallback: &str) -> String {
    fn render(syntax: &TypeSyntax, output: &mut String) {
        match &syntax.kind {
            TypeSyntaxKind::Path(path) => {
                for (index, segment) in path.iter().enumerate() {
                    if index != 0 {
                        output.push_str("::");
                    }
                    output.push_str(&segment.name);
                }
            }
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } => {
                render(constructor, output);
                output.push('<');
                for (index, argument) in arguments.iter().enumerate() {
                    if index != 0 {
                        output.push(',');
                    }
                    render(argument, output);
                }
                output.push('>');
            }
            _ => output.push_str("<invalid-effect>"),
        }
    }

    let Some(syntax) = program.effect_path(site) else {
        return fallback.to_owned();
    };
    let mut output = String::new();
    render(syntax, &mut output);
    output
}

fn drop_body_has_forbidden_control(
    program: &Program,
    expr: &Expr,
    effectful: &HashSet<&str>,
) -> bool {
    drop_body_has_outward_control(program, expr, effectful, &HashSet::new())
}

fn drop_body_has_outward_control(
    program: &Program,
    expr: &Expr,
    effectful: &HashSet<&str>,
    handled: &HashSet<(String, String)>,
) -> bool {
    match &expr.kind {
        ExprKind::Move(operand) => {
            drop_body_has_outward_control(program, operand, effectful, handled)
        }
        ExprKind::Perform {
            effect,
            operation,
            args,
        } => {
            !handled.contains(&(
                effect_instance_text(program, expr.span, effect),
                operation.to_string(),
            )) || args.iter().any(|argument| {
                drop_body_has_outward_control(program, argument, effectful, handled)
            })
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
                || drop_body_has_outward_control(program, callee, effectful, handled)
                || arguments.iter().any(|argument| {
                    drop_body_has_outward_control(program, argument, effectful, handled)
                })
        }
        ExprKind::List(values) | ExprKind::Tuple(values) => values
            .iter()
            .any(|value| drop_body_has_outward_control(program, value, effectful, handled)),
        ExprKind::Closure { body, .. } => {
            drop_body_has_outward_control(program, body, effectful, handled)
        }
        ExprKind::Struct { fields, .. } => fields
            .iter()
            .any(|(_, value)| drop_body_has_outward_control(program, value, effectful, handled)),
        ExprKind::Field(subject, _) => {
            drop_body_has_outward_control(program, subject, effectful, handled)
        }
        ExprKind::Block(statements) => statements.iter().any(|statement| match statement {
            Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                drop_body_has_outward_control(program, value, effectful, handled)
            }
            Stmt::Assign {
                destination, value, ..
            } => {
                drop_body_has_outward_control(program, value, effectful, handled)
                    || match &destination.kind {
                        AssignmentPlaceKind::Local { .. } => false,
                        AssignmentPlaceKind::Dereference { reference, .. } => {
                            drop_body_has_outward_control(program, reference, effectful, handled)
                        }
                    }
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
                    computation_handled.insert((
                        effect_instance_text(program, clause.span, &clause.effect),
                        clause.operation.clone(),
                    ));
                }
            }
            drop_body_has_outward_control(program, computation, effectful, &computation_handled)
                || clauses.iter().any(|clause| {
                    drop_body_has_outward_control(program, &clause.body, effectful, handled)
                })
        }
        ExprKind::Unary { operand, .. } => {
            drop_body_has_outward_control(program, operand, effectful, handled)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            drop_body_has_outward_control(program, lhs, effectful, handled)
                || drop_body_has_outward_control(program, rhs, effectful, handled)
        }
        // Structural resumption operations and direct label transfers are
        // outward control, exactly like their legacy call spellings above.
        ExprKind::Resume { .. }
        | ExprKind::Cancel { .. }
        | ExprKind::TailResume { .. }
        | ExprKind::Leave { .. } => true,
        ExprKind::ContextBlock(statements) => statements.iter().any(|statement| match statement {
            Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                drop_body_has_outward_control(program, value, effectful, handled)
            }
            Stmt::Assign { value, .. } => {
                drop_body_has_outward_control(program, value, effectful, handled)
            }
        }),
        ExprKind::TypedClosure { body, .. }
        | ExprKind::Labeled { body, .. }
        | ExprKind::LabelDestination { body, .. } => {
            drop_body_has_outward_control(program, body, effectful, handled)
        }
        ExprKind::Is { subject, .. } => {
            drop_body_has_outward_control(program, subject, effectful, handled)
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::String(_)
        | ExprKind::Char(_)
        | ExprKind::Byte(_)
        | ExprKind::ByteString(_)
        | ExprKind::Variable(_)
        | ExprKind::LabelReference(_) => false,
    }
}

fn validate_effect_application<'a>(
    program: &'a Program,
    site: Span,
    fallback: &'a str,
    effects: &HashMap<&str, (&EffectDecl, HashMap<&str, &EffectOperationDecl>)>,
    generic_kinds: &HashMap<&str, GenericParamKind>,
    errors: &mut Vec<Diagnostic>,
) -> Option<&'a str> {
    let syntax = program.effect_path(site);
    let (name, arguments, application_span) = match syntax.map(|syntax| &syntax.kind) {
        None => (fallback, &[][..], site),
        Some(TypeSyntaxKind::Path(_)) => (syntax?.simple_name()?, &[][..], syntax?.span),
        Some(TypeSyntaxKind::Application {
            constructor,
            arguments,
            ..
        }) => {
            let Some(name) = constructor.simple_name() else {
                errors.push(
                    Diagnostic::error(
                        "invalid effect application",
                        "an effect application must name one declared effect",
                        constructor.span,
                    )
                    .with_code("G0110"),
                );
                return None;
            };
            (name, arguments.as_slice(), syntax?.span)
        }
        Some(_) => {
            errors.push(
                Diagnostic::error(
                    "invalid effect application",
                    "perform and handler paths require a named effect application",
                    syntax?.span,
                )
                .with_code("G0110"),
            );
            return None;
        }
    };
    let Some((declaration, _)) = effects.get(name) else {
        errors.push(
            Diagnostic::error(
                "unknown effect",
                format!("`{name}` has not been declared in this module"),
                application_span,
            )
            .with_code("G0100")
            .with_help(format!("declare it with `effect {name} {{ ... }}`")),
        );
        return None;
    };
    let parameters = declaration
        .generics
        .iter()
        .flat_map(|generics| &generics.params)
        .collect::<Vec<_>>();
    let const_arguments = syntax
        .map(|syntax| program.type_const_arguments(syntax.span))
        .unwrap_or(&[]);
    let lifetime_arguments = syntax
        .and_then(|syntax| match &syntax.kind {
            TypeSyntaxKind::Application {
                lifetime_arguments, ..
            } => Some(lifetime_arguments.as_slice()),
            _ => None,
        })
        .unwrap_or(&[]);
    let supplied_arguments = arguments.len() + const_arguments.len() + lifetime_arguments.len();
    if parameters.len() != supplied_arguments {
        errors.push(
            Diagnostic::error(
                "wrong number of effect arguments",
                format!(
                    "effect `{name}` expects {} generic argument(s), but this application supplies {}",
                    parameters.len(),
                    supplied_arguments
                ),
                application_span,
            )
            .with_code("G0111")
            .with_related(declaration.span, "the effect is declared here"),
        );
        return Some(name);
    }
    for (parameter, argument) in parameters
        .iter()
        .filter(|parameter| parameter.kind == GenericParamKind::Type)
        .zip(arguments)
    {
        // Effect applications currently use the ordinary type-argument grammar.
        // A named non-type binder must not silently cross this kind boundary.
        if parameter.kind != GenericParamKind::Type {
            errors.push(
                Diagnostic::error(
                    "unsupported effect parameter kind",
                    format!(
                        "effect parameter `{}` is not a type parameter and cannot be supplied by this application syntax",
                        parameter.name
                    ),
                    argument.span,
                )
                .with_code("G0112")
                .with_related(parameter.span, "the parameter kind is declared here"),
            );
        } else if let Some(argument_name) = argument.simple_name()
            && let Some(kind) = generic_kinds.get(argument_name)
            && *kind != GenericParamKind::Type
        {
            errors.push(
                Diagnostic::error(
                    "effect argument kind mismatch",
                    format!("`{argument_name}` is not a type parameter"),
                    argument.span,
                )
                .with_code("G0112")
                .with_related(parameter.span, "a type argument is required here"),
            );
        }
    }
    if parameters
        .iter()
        .filter(|parameter| matches!(parameter.kind, GenericParamKind::Const(_)))
        .count()
        != const_arguments.len()
        || parameters
            .iter()
            .filter(|parameter| parameter.kind == GenericParamKind::Lifetime)
            .count()
            != lifetime_arguments.len()
    {
        errors.push(
            Diagnostic::error(
                "effect argument kind mismatch",
                "effect type, const, and brand arguments must match their declared binder kinds",
                application_span,
            )
            .with_code("G0112")
            .with_related(
                declaration.span,
                "the effect binder kinds are declared here",
            ),
        );
    }
    Some(name)
}

fn validate_expr(
    program: &Program,
    expr: &Expr,
    effects: &HashMap<&str, (&EffectDecl, HashMap<&str, &EffectOperationDecl>)>,
    generic_kinds: &HashMap<&str, GenericParamKind>,
    errors: &mut Vec<Diagnostic>,
) {
    match &expr.kind {
        ExprKind::Move(operand) => validate_expr(program, operand, effects, generic_kinds, errors),
        ExprKind::List(values) | ExprKind::Tuple(values) => values
            .iter()
            .for_each(|value| validate_expr(program, value, effects, generic_kinds, errors)),
        ExprKind::Closure { body, .. } => {
            validate_expr(program, body, effects, generic_kinds, errors)
        }
        ExprKind::Struct { fields, .. } => fields
            .iter()
            .for_each(|(_, value)| validate_expr(program, value, effects, generic_kinds, errors)),
        ExprKind::Field(subject, _) => {
            validate_expr(program, subject, effects, generic_kinds, errors)
        }
        ExprKind::Block(statements) => statements.iter().for_each(|statement| match statement {
            Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                validate_expr(program, value, effects, generic_kinds, errors)
            }
            Stmt::Assign {
                destination, value, ..
            } => {
                validate_expr(program, value, effects, generic_kinds, errors);
                if let AssignmentPlaceKind::Dereference { reference, .. } = &destination.kind {
                    validate_expr(program, reference, effects, generic_kinds, errors);
                }
            }
        }),
        ExprKind::Call(callee, args) => {
            validate_expr(program, callee, effects, generic_kinds, errors);
            args.iter()
                .for_each(|arg| validate_expr(program, arg, effects, generic_kinds, errors));
        }
        ExprKind::Perform {
            effect,
            operation,
            args,
        } => {
            let declaration_name = validate_effect_application(
                program,
                expr.span,
                effect,
                effects,
                generic_kinds,
                errors,
            );
            match declaration_name.and_then(|name| effects.get(name)) {
                None => {}
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
                .for_each(|arg| validate_expr(program, arg, effects, generic_kinds, errors));
        }
        ExprKind::Handle {
            computation,
            clauses,
        } => {
            validate_expr(program, computation, effects, generic_kinds, errors);
            for clause in clauses.iter() {
                let declaration_name = validate_effect_application(
                    program,
                    clause.span,
                    &clause.effect,
                    effects,
                    generic_kinds,
                    errors,
                );
                match declaration_name
                    .and_then(|name| effects.get(name))
                    .and_then(|(_, operations)| operations.get(clause.operation.as_str()))
                {
                    None if declaration_name.is_none() => {}
                    None => {
                        let declaration = effects[declaration_name.unwrap()].0;
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
                clause
                    .patterns
                    .iter()
                    .for_each(|pattern| validate_pattern(program, pattern, errors));
                validate_expr(program, &clause.body, effects, generic_kinds, errors);
            }
        }
        ExprKind::Unary { operand, .. } => {
            validate_expr(program, operand, effects, generic_kinds, errors)
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            validate_expr(program, lhs, effects, generic_kinds, errors);
            validate_expr(program, rhs, effects, generic_kinds, errors);
        }
        // Structural resumption invocations are the normative encoding of the
        // legacy `resume`/`cancel` call spellings; the pipeline rewrites them
        // before lowering, so they are valid here.
        ExprKind::Resume { resumption, value } => {
            validate_expr(program, resumption, effects, generic_kinds, errors);
            if let Some(value) = value {
                validate_expr(program, value, effects, generic_kinds, errors);
            }
        }
        ExprKind::Cancel { resumption } => {
            validate_expr(program, resumption, effects, generic_kinds, errors)
        }
        ExprKind::ContextBlock(statements) => {
            statements.iter().for_each(|statement| match statement {
                Stmt::Let { value, .. } | Stmt::Deconstruct { value, .. } | Stmt::Expr(value) => {
                    validate_expr(program, value, effects, generic_kinds, errors)
                }
                Stmt::Assign {
                    destination, value, ..
                } => {
                    validate_expr(program, value, effects, generic_kinds, errors);
                    if let AssignmentPlaceKind::Dereference { reference, .. } = &destination.kind {
                        validate_expr(program, reference, effects, generic_kinds, errors);
                    }
                }
            })
        }
        ExprKind::TypedClosure {
            params,
            outward_effects,
            body,
            ..
        } => {
            let mut seen = HashMap::<&str, Span>::new();
            for param in params.iter() {
                if let Some(original) = seen.insert(param.name.as_str(), param.span) {
                    errors.push(
                        Diagnostic::error(
                            "duplicate typed closure parameter",
                            format!("parameter `{}` appears more than once", param.name),
                            param.span,
                        )
                        .with_code("G0130")
                        .with_related(original, "the first declaration is here")
                        .with_help("give every typed closure parameter a distinct name"),
                    );
                }
            }
            if let Some(row) = outward_effects {
                if let Some(tail) = &row.tail {
                    errors.push(
                        Diagnostic::error(
                            "open typed closure effect row",
                            "a typed anonymous callable must declare a closed effect row",
                            tail.span,
                        )
                        .with_code("G0130")
                        .with_help("list every outward effect instead of `| tail`"),
                    );
                }
                for member in &row.effects {
                    let name = match &member.kind {
                        TypeSyntaxKind::Application { constructor, .. } => {
                            constructor.simple_name()
                        }
                        _ => member.simple_name(),
                    };
                    let Some(name) = name else {
                        errors.push(
                            Diagnostic::error(
                                "invalid typed closure effect row",
                                "each row member must name one declared effect or effect-row alias",
                                member.span,
                            )
                            .with_code("G0130"),
                        );
                        continue;
                    };
                    if !effects.contains_key(name)
                        && !program
                            .effect_row_aliases
                            .iter()
                            .any(|alias| alias.name == name)
                    {
                        errors.push(
                            Diagnostic::error(
                                "unknown typed closure effect",
                                format!("`{name}` is not a declared effect or effect-row alias"),
                                member.span,
                            )
                            .with_code("G0130")
                            .with_help("declare the effect before naming it in a closure row"),
                        );
                    }
                }
            }
            validate_expr(program, body, effects, generic_kinds, errors);
        }
        ExprKind::Labeled { body, .. } | ExprKind::LabelDestination { body, .. } => {
            validate_expr(program, body, effects, generic_kinds, errors);
        }
        ExprKind::LabelReference(_) => {}
        ExprKind::Leave { value, .. } => {
            if let Some(value) = value {
                validate_expr(program, value, effects, generic_kinds, errors);
            }
        }
        ExprKind::TailResume { resumption, value } => {
            validate_expr(program, resumption, effects, generic_kinds, errors);
            if let Some(value) = value {
                validate_expr(program, value, effects, generic_kinds, errors);
            }
        }
        ExprKind::Is { subject, pattern } => {
            validate_expr(program, subject, effects, generic_kinds, errors);
            validate_pattern(program, pattern, errors);
        }
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Char(_)
        | ExprKind::Byte(_)
        | ExprKind::ByteString(_)
        | ExprKind::String(_)
        | ExprKind::Variable(_) => {}
    }
}

/// Handler clause patterns are structurally recursive; named-struct patterns
/// additionally resolve their field spellings against the declaration so the
/// recovery evaluator and the bytecode path reject the same shapes.
fn validate_pattern(
    program: &Program,
    pattern: &crate::ast::Pattern,
    errors: &mut Vec<Diagnostic>,
) {
    match &pattern.kind {
        PatternKind::Wildcard
        | PatternKind::Binding(_)
        | PatternKind::Unit
        | PatternKind::Int(_)
        | PatternKind::Float(_)
        | PatternKind::Char(_)
        | PatternKind::Byte(_)
        | PatternKind::String(_) => {}
        PatternKind::Variant { path, fields, .. } => {
            if let [enum_name, variant_name] = path.as_slice() {
                // Qualified value-subnamespace bindings may alias enum
                // constructors through type-alias owners. Their canonical
                // enum/variant and arity are checked by
                // `normalize_constructor_aliases`; validating the source
                // spelling as though its owner had to be a direct enum would
                // reject a supported alias before normalization can run.
                let declared_constructor_alias = program.globals.iter().any(|binding| {
                    binding.owner.as_deref() == Some(enum_name.as_str())
                        && binding.name == *variant_name
                });
                match program
                    .enums
                    .iter()
                    .find(|decl| decl.name == *enum_name)
                {
                    None if declared_constructor_alias => {}
                    None => errors.push(
                        Diagnostic::error(
                            "unknown enum pattern type",
                            format!("`{enum_name}` is not a declared enum"),
                            pattern.span,
                        )
                        .with_code("G0135"),
                    ),
                    Some(declaration) => match declaration
                        .variants
                        .iter()
                        .find(|variant| variant.name == *variant_name)
                    {
                        None => errors.push(
                            Diagnostic::error(
                                "unknown enum variant pattern",
                                format!("enum `{enum_name}` has no variant `{variant_name}`"),
                                pattern.span,
                            )
                            .with_code("G0135")
                            .with_related(declaration.span, "the enum is declared here"),
                        ),
                        Some(variant) if fields.len() > variant.fields.len() => errors.push(
                            Diagnostic::error(
                                "wrong enum pattern arity",
                                format!(
                                    "`{enum_name}::{variant_name}` has {} field(s), but this pattern supplies {} explicit field pattern(s)",
                                    variant.fields.len(),
                                    fields.len()
                                ),
                                pattern.span,
                            )
                            .with_code("G0136")
                            .with_related(variant.span, "the variant is declared here"),
                        ),
                        Some(_) => {}
                    },
                }
            } else {
                errors.push(
                    Diagnostic::error(
                        "invalid variant pattern path",
                        "variant patterns must name exactly `Enum::Variant`",
                        pattern.span,
                    )
                    .with_code("G0135"),
                );
            }
            fields
                .iter()
                .for_each(|field| validate_pattern(program, field, errors));
        }
        PatternKind::Tuple { elements, .. } => elements
            .iter()
            .for_each(|element| validate_pattern(program, element, errors)),
        PatternKind::Struct { name, fields, .. } => {
            if let Some(declaration) = program.structs.iter().find(|decl| decl.name == *name) {
                for field in fields {
                    if !declaration
                        .fields
                        .iter()
                        .any(|declared| declared.name == field.field)
                    {
                        errors.push(
                            Diagnostic::error(
                                "unknown struct pattern field",
                                format!("struct `{name}` has no field named `{}`", field.field),
                                field.span,
                            )
                            .with_code("G0129")
                            .with_related(declaration.span, format!("`{name}` is declared here")),
                        );
                    }
                }
            } else {
                errors.push(
                    Diagnostic::error(
                        "unknown struct pattern type",
                        format!("`{name}` is not a declared struct"),
                        pattern.span,
                    )
                    .with_code("G0135"),
                );
            }
            fields
                .iter()
                .for_each(|field| validate_pattern(program, &field.pattern, errors));
        }
    }
}
