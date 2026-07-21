//! Early declaration/interface resolution for tooling stop boundaries.
//!
//! This pass deliberately does not elaborate callable bodies, run ownership,
//! build Core/MIR, optimize, or emit bytecode. It validates the parsed source
//! surface and resolves every type, trait, and effect name exposed by a
//! declaration interface.

use std::collections::BTreeSet;

use crate::{
    ast::{
        AssignmentPlaceKind, AssociatedArgumentSyntax, AssociatedBindingValue, EffectRowSyntax,
        Expr, ExprKind, GenericParamKind, GenericParams, GoalArgument, Pattern, PatternKind,
        Program, Stmt, TraitMethod, TraitRefSyntax, TypeSyntax, TypeSyntaxKind, WhereClause,
    },
    diagnostic::Diagnostic,
    source_bundle::SourceBundle,
};

pub fn resolve_bundle(bundle: &SourceBundle) -> Result<(), Vec<Diagnostic>> {
    let program = crate::modules::parse_bundle(bundle)?;
    let program = crate::parser::normalize_for_legacy_consumers(program);
    let program = crate::modules::resolve_program(bundle, program)?.program;
    crate::validate::validate(&program)?;
    resolve_interfaces(&program)
}

fn resolve_interfaces(program: &Program) -> Result<(), Vec<Diagnostic>> {
    let types = program
        .type_aliases
        .iter()
        .map(|declaration| declaration.name.as_str())
        .chain(
            program
                .structs
                .iter()
                .map(|declaration| declaration.name.as_str()),
        )
        .chain(
            program
                .enums
                .iter()
                .map(|declaration| declaration.name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    let traits = program
        .traits
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<BTreeSet<_>>();
    let effects = program
        .effects
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<BTreeSet<_>>();
    let effect_aliases = program
        .effect_row_aliases
        .iter()
        .map(|declaration| declaration.name.as_str())
        .collect::<BTreeSet<_>>();
    let values = program
        .functions
        .iter()
        .map(|declaration| declaration.name.as_str())
        .chain(
            program
                .globals
                .iter()
                .filter(|declaration| declaration.owner.is_none())
                .map(|declaration| declaration.name.as_str()),
        )
        .collect::<BTreeSet<_>>();
    let qualified_values = program
        .globals
        .iter()
        .filter_map(|declaration| Some((declaration.owner.as_deref()?, declaration.name.as_str())))
        .chain(program.enums.iter().flat_map(|declaration| {
            declaration
                .variants
                .iter()
                .map(|variant| (declaration.name.as_str(), variant.name.as_str()))
        }))
        .chain(program.traits.iter().flat_map(|declaration| {
            declaration
                .methods
                .iter()
                .map(|method| (declaration.name.as_str(), method.name.as_str()))
        }))
        .collect::<BTreeSet<_>>();
    let context = Context {
        types,
        traits,
        effects,
        effect_aliases,
        values,
        qualified_values,
    };
    let mut errors = Vec::new();

    for declaration in &program.type_aliases {
        let scope = Scope::new(declaration.generics.as_ref());
        context.ty(&declaration.target, &scope, &mut errors);
    }
    for declaration in &program.structs {
        let scope = Scope::new(declaration.generics.as_ref());
        for field in &declaration.fields {
            context.ty(&field.ty, &scope, &mut errors);
        }
    }
    for declaration in &program.enums {
        let scope = Scope::new(declaration.generics.as_ref());
        for field in declaration
            .variants
            .iter()
            .flat_map(|variant| &variant.fields)
        {
            context.ty(field, &scope, &mut errors);
        }
    }
    for declaration in &program.effect_row_aliases {
        context.effect_row(&declaration.row, &Scope::default(), &mut errors);
    }
    for declaration in &program.effects {
        let scope = Scope::new(declaration.generics.as_ref());
        for operation in &declaration.operations {
            for parameter in &operation.params {
                context.ty(&parameter.ty, &scope, &mut errors);
            }
            if let Some(result) = &operation.return_type {
                context.ty(result, &scope, &mut errors);
            }
        }
    }
    for function in &program.functions {
        let scope = Scope::new(function.generics.as_ref());
        context.callable(
            &function.params,
            function.return_type.as_ref(),
            function.outward_effects.as_ref(),
            function.where_clause.as_ref(),
            &scope,
            &mut errors,
        );
        let mut locals = function
            .params
            .iter()
            .map(|parameter| parameter.name.clone())
            .collect();
        context.expression(&function.body, &mut locals, &mut errors);
    }
    for declaration in &program.traits {
        let scope = Scope::new(declaration.generics.as_ref());
        for supertrait in &declaration.supertraits {
            context.trait_ref(supertrait, &scope, &mut errors);
        }
        for method in &declaration.methods {
            context.method(method, &scope, &mut errors);
            if let Some(body) = &method.body {
                let mut locals = method
                    .params
                    .iter()
                    .map(|parameter| parameter.name.clone())
                    .collect::<BTreeSet<_>>();
                locals.insert("self".to_string());
                context.expression(body, &mut locals, &mut errors);
            }
        }
    }
    for declaration in &program.impls {
        let scope = Scope::new(declaration.generics.as_ref());
        context.ty(&declaration.self_ty, &scope, &mut errors);
        context.trait_ref(&declaration.trait_ref, &scope, &mut errors);
        context.where_clause(declaration.where_clause.as_ref(), &scope, &mut errors);
        for associated in &declaration.associated_types {
            let nested = scope.extended(associated.generics.as_ref());
            context.binding_value(&associated.value, &nested, &mut errors);
        }
        for method in &declaration.methods {
            context.method(method, &scope, &mut errors);
        }
    }
    for declaration in &program.uses {
        let scope = Scope::new(declaration.generics.as_ref());
        context.ty(&declaration.target, &scope, &mut errors);
        context.where_clause(declaration.where_clause.as_ref(), &scope, &mut errors);
    }
    for declaration in &program.drops {
        let scope = Scope::new(declaration.generics.as_ref());
        context.ty(&declaration.target_type, &scope, &mut errors);
        context.where_clause(declaration.where_clause.as_ref(), &scope, &mut errors);
        let mut locals = BTreeSet::from(["self".to_string()]);
        context.expression(&declaration.body, &mut locals, &mut errors);
    }
    for declaration in &program.globals {
        context.expression(&declaration.value, &mut BTreeSet::new(), &mut errors);
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

#[derive(Clone, Default)]
struct Scope<'a> {
    types: BTreeSet<&'a str>,
    effect_rows: BTreeSet<&'a str>,
}

impl<'a> Scope<'a> {
    fn new(generics: Option<&'a GenericParams>) -> Self {
        let mut scope = Self::default();
        scope.add(generics);
        scope
    }

    fn extended(&self, generics: Option<&'a GenericParams>) -> Self {
        let mut scope = self.clone();
        scope.add(generics);
        scope
    }

    fn add(&mut self, generics: Option<&'a GenericParams>) {
        for parameter in generics.into_iter().flat_map(|generics| &generics.params) {
            match parameter.kind {
                GenericParamKind::Type => {
                    self.types.insert(&parameter.name);
                }
                GenericParamKind::EffectRow => {
                    self.effect_rows.insert(&parameter.name);
                }
                GenericParamKind::Lifetime | GenericParamKind::Const(_) => {}
            }
        }
    }
}

struct Context<'a> {
    types: BTreeSet<&'a str>,
    traits: BTreeSet<&'a str>,
    effects: BTreeSet<&'a str>,
    effect_aliases: BTreeSet<&'a str>,
    values: BTreeSet<&'a str>,
    qualified_values: BTreeSet<(&'a str, &'a str)>,
}

impl Context<'_> {
    fn expression(
        &self,
        expression: &Expr,
        locals: &mut BTreeSet<String>,
        errors: &mut Vec<Diagnostic>,
    ) {
        match &expression.kind {
            ExprKind::Variable(path) => match path.as_ref() {
                [name]
                    if !locals.contains(name.as_ref())
                        && !self.values.contains(name.as_ref())
                        && !matches!(name.as_ref(), "resume" | "cancel" | "tail") =>
                {
                    errors.push(unknown("value", name, expression.span));
                }
                [owner, name]
                    if !self
                        .qualified_values
                        .contains(&(owner.as_ref(), name.as_ref())) =>
                {
                    errors.push(unknown(
                        "qualified value",
                        &format!("{owner}::{name}"),
                        expression.span,
                    ));
                }
                _ => {}
            },
            ExprKind::Move(value)
            | ExprKind::Unary { operand: value, .. }
            | ExprKind::Field(value, _)
            | ExprKind::Labeled { body: value, .. }
            | ExprKind::LabelDestination { body: value, .. }
            | ExprKind::Cancel { resumption: value } => self.expression(value, locals, errors),
            ExprKind::Closure { params, body } => {
                let mut nested = locals.clone();
                nested.extend(params.iter().map(|name| name.to_string()));
                self.expression(body, &mut nested, errors);
            }
            ExprKind::TypedClosure {
                params,
                return_type,
                outward_effects,
                body,
                ..
            } => {
                let scope = Scope::default();
                for parameter in params.iter() {
                    self.ty(&parameter.ty, &scope, errors);
                }
                if let Some(result) = return_type {
                    self.ty(result, &scope, errors);
                }
                if let Some(effects) = outward_effects {
                    self.effect_row(effects, &scope, errors);
                }
                let mut nested = locals.clone();
                nested.extend(params.iter().map(|parameter| parameter.name.clone()));
                self.expression(body, &mut nested, errors);
            }
            ExprKind::Leave { value, .. } => {
                if let Some(value) = value {
                    self.expression(value, locals, errors);
                }
            }
            ExprKind::Resume { resumption, value } | ExprKind::TailResume { resumption, value } => {
                self.expression(resumption, locals, errors);
                if let Some(value) = value {
                    self.expression(value, locals, errors);
                }
            }
            ExprKind::Is { subject, pattern } => {
                self.expression(subject, locals, errors);
                self.pattern(pattern, errors);
            }
            ExprKind::ContextBlock(statements) | ExprKind::Block(statements) => {
                let mut nested = locals.clone();
                self.statements(statements, &mut nested, errors);
            }
            ExprKind::List(values) | ExprKind::Tuple(values) => {
                for value in values.iter() {
                    self.expression(value, locals, errors);
                }
            }
            ExprKind::Struct { name, fields } => {
                if !self.types.contains(name.as_ref()) && !is_predefined(name) {
                    errors.push(unknown("type", name, expression.span));
                }
                for (_, value) in fields.iter() {
                    self.expression(value, locals, errors);
                }
            }
            ExprKind::Call(callee, arguments) => {
                if let ExprKind::Variable(else_path) = &callee.kind
                    && else_path.len() == 1
                    && else_path[0].as_ref() == "else"
                    && let [if_expression, negative] = arguments.as_slice()
                    && let ExprKind::Call(if_callee, if_arguments) = &if_expression.kind
                    && let ExprKind::Variable(if_path) = &if_callee.kind
                    && if_path.len() == 1
                    && if_path[0].as_ref() == "if"
                    && let [condition, positive] = if_arguments.as_slice()
                    && let ExprKind::Is { subject, pattern } = &condition.kind
                {
                    self.expression(callee, locals, errors);
                    self.expression(if_callee, locals, errors);
                    self.expression(subject, locals, errors);
                    self.pattern(pattern, errors);

                    let mut positive_locals = locals.clone();
                    self.pattern_bindings(pattern, &mut positive_locals);
                    self.expression(positive, &mut positive_locals, errors);
                    self.expression(negative, locals, errors);
                    return;
                }
                self.expression(callee, locals, errors);
                for argument in arguments.iter() {
                    self.expression(argument, locals, errors);
                }
            }
            ExprKind::Perform { args, .. } => {
                for argument in args.iter() {
                    self.expression(argument, locals, errors);
                }
            }
            ExprKind::Handle {
                computation,
                clauses,
            } => {
                self.expression(computation, locals, errors);
                for clause in clauses.iter() {
                    let mut nested = locals.clone();
                    for pattern in &clause.patterns {
                        self.pattern_bindings(pattern, &mut nested);
                    }
                    if let Some(resumption) = &clause.resumption {
                        nested.insert(resumption.clone());
                    }
                    self.expression(&clause.body, &mut nested, errors);
                }
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.expression(lhs, locals, errors);
                self.expression(rhs, locals, errors);
            }
            ExprKind::Unit
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::String(_)
            | ExprKind::Char(_)
            | ExprKind::Byte(_)
            | ExprKind::ByteString(_)
            | ExprKind::LabelReference(_) => {}
        }
    }

    fn statements(
        &self,
        statements: &[Stmt],
        locals: &mut BTreeSet<String>,
        errors: &mut Vec<Diagnostic>,
    ) {
        for statement in statements {
            match statement {
                Stmt::Let { name, value, .. } => {
                    self.expression(value, locals, errors);
                    locals.insert(name.clone());
                }
                Stmt::Deconstruct {
                    ty, fields, value, ..
                } => {
                    self.expression(value, locals, errors);
                    if let Some(name) = ty
                        && !self.types.contains(name.as_str())
                        && !is_predefined(name)
                    {
                        errors.push(unknown("type", name, value.span));
                    }
                    locals.extend(fields.iter().filter_map(|field| field.binding.clone()));
                }
                Stmt::Assign {
                    destination, value, ..
                } => {
                    self.expression(value, locals, errors);
                    match &destination.kind {
                        AssignmentPlaceKind::Local { name, .. } => {
                            if !locals.contains(name.as_ref()) {
                                errors.push(unknown("local value", name, destination.span));
                            }
                        }
                        AssignmentPlaceKind::Dereference { reference, .. } => {
                            self.expression(reference, locals, errors)
                        }
                    }
                }
                Stmt::Expr(expression) => self.expression(expression, locals, errors),
            }
        }
    }

    fn pattern(&self, pattern: &Pattern, errors: &mut Vec<Diagnostic>) {
        match &pattern.kind {
            PatternKind::Variant { path, fields, .. } => {
                if let [owner, name] = path.as_slice()
                    && !self
                        .qualified_values
                        .contains(&(owner.as_str(), name.as_str()))
                {
                    errors.push(unknown(
                        "enum constructor",
                        &format!("{owner}::{name}"),
                        pattern.span,
                    ));
                }
                for field in fields {
                    self.pattern(field, errors);
                }
            }
            PatternKind::Tuple { elements, .. } => {
                for element in elements {
                    self.pattern(element, errors);
                }
            }
            PatternKind::Struct { name, fields, .. } => {
                if !self.types.contains(name.as_str()) {
                    errors.push(unknown("type", name, pattern.span));
                }
                for field in fields {
                    self.pattern(&field.pattern, errors);
                }
            }
            PatternKind::Wildcard
            | PatternKind::Binding(_)
            | PatternKind::Unit
            | PatternKind::Int(_)
            | PatternKind::Float(_)
            | PatternKind::String(_)
            | PatternKind::Char(_)
            | PatternKind::Byte(_) => {}
        }
    }

    fn pattern_bindings(&self, pattern: &Pattern, locals: &mut BTreeSet<String>) {
        let mut stack = vec![pattern];
        while let Some(pattern) = stack.pop() {
            match &pattern.kind {
                PatternKind::Binding(name) => {
                    locals.insert(name.clone());
                }
                PatternKind::Variant { fields, .. } => stack.extend(fields),
                PatternKind::Tuple { elements, .. } => stack.extend(elements),
                PatternKind::Struct { fields, .. } => {
                    stack.extend(fields.iter().map(|field| &field.pattern));
                }
                _ => {}
            }
        }
    }

    fn callable(
        &self,
        params: &[crate::ast::Param],
        result: Option<&TypeSyntax>,
        effects: Option<&EffectRowSyntax>,
        where_clause: Option<&WhereClause>,
        scope: &Scope<'_>,
        errors: &mut Vec<Diagnostic>,
    ) {
        for parameter in params {
            self.ty(&parameter.ty, scope, errors);
        }
        if let Some(result) = result {
            self.ty(result, scope, errors);
        }
        if let Some(effects) = effects {
            self.effect_row(effects, scope, errors);
        }
        self.where_clause(where_clause, scope, errors);
    }

    fn method(&self, method: &TraitMethod, outer: &Scope<'_>, errors: &mut Vec<Diagnostic>) {
        let scope = outer.extended(method.generics.as_ref());
        self.callable(
            &method.params,
            method.return_type.as_ref(),
            method.outward_effects.as_ref(),
            method.where_clause.as_ref(),
            &scope,
            errors,
        );
    }

    fn ty(&self, syntax: &TypeSyntax, scope: &Scope<'_>, errors: &mut Vec<Diagnostic>) {
        match &syntax.kind {
            TypeSyntaxKind::Path(path) => {
                let Some(first) = path.first() else {
                    return;
                };
                if !self.types.contains(first.name.as_str())
                    && !scope.types.contains(first.name.as_str())
                    && !is_predefined(&first.name)
                {
                    errors.push(unknown("type", &first.name, first.span));
                }
            }
            TypeSyntaxKind::SharedReference(referent)
            | TypeSyntaxKind::UniqueReference(referent) => self.ty(referent, scope, errors),
            TypeSyntaxKind::Tuple(elements) => {
                for element in elements {
                    self.ty(element, scope, errors);
                }
            }
            TypeSyntaxKind::Application {
                constructor,
                arguments,
                ..
            } => {
                self.ty(constructor, scope, errors);
                for argument in arguments {
                    self.ty(argument, scope, errors);
                }
            }
            TypeSyntaxKind::Projection {
                subject,
                trait_ref,
                arguments,
                ..
            } => {
                self.ty(subject, scope, errors);
                self.trait_ref(trait_ref, scope, errors);
                for argument in arguments {
                    if let AssociatedArgumentSyntax::Type(argument) = argument {
                        self.ty(argument, scope, errors);
                    }
                }
            }
            TypeSyntaxKind::Never => {}
        }
    }

    fn trait_ref(
        &self,
        reference: &TraitRefSyntax,
        scope: &Scope<'_>,
        errors: &mut Vec<Diagnostic>,
    ) {
        if let Some(name) = reference.path.first()
            && !self.traits.contains(name.name.as_str())
            && !matches!(name.name.as_str(), "Use" | "Drop" | "Fn")
        {
            errors.push(unknown("trait", &name.name, name.span));
        }
        for argument in &reference.arguments {
            if let GoalArgument::Type(argument) = argument {
                self.ty(argument, scope, errors);
            }
        }
        for binding in &reference.bindings {
            for argument in &binding.arguments {
                if let AssociatedArgumentSyntax::Type(argument) = argument {
                    self.ty(argument, scope, errors);
                }
            }
            self.binding_value(&binding.value, scope, errors);
        }
    }

    fn effect_row(&self, row: &EffectRowSyntax, scope: &Scope<'_>, errors: &mut Vec<Diagnostic>) {
        for effect in &row.effects {
            let base = match &effect.kind {
                TypeSyntaxKind::Application { constructor, .. } => constructor.simple_name(),
                _ => effect.simple_name(),
            };
            if let Some(name) = base
                && !self.effects.contains(name)
                && !self.effect_aliases.contains(name)
                && !scope.effect_rows.contains(name)
            {
                errors.push(unknown("effect", name, effect.span));
            }
            if let TypeSyntaxKind::Application { arguments, .. } = &effect.kind {
                for argument in arguments {
                    self.ty(argument, scope, errors);
                }
            }
        }
        if let Some(tail) = &row.tail
            && !scope.effect_rows.contains(tail.name.as_str())
            && !self.effect_aliases.contains(tail.name.as_str())
        {
            errors.push(unknown("effect row", &tail.name, tail.span));
        }
    }

    fn where_clause(
        &self,
        clause: Option<&WhereClause>,
        scope: &Scope<'_>,
        errors: &mut Vec<Diagnostic>,
    ) {
        for goal in clause.into_iter().flat_map(|clause| &clause.goals) {
            self.ty(&goal.subject, scope, errors);
            self.trait_ref(&goal.relation, scope, errors);
        }
    }

    fn binding_value(
        &self,
        value: &AssociatedBindingValue,
        scope: &Scope<'_>,
        errors: &mut Vec<Diagnostic>,
    ) {
        match value {
            AssociatedBindingValue::Type(value) => self.ty(value, scope, errors),
            AssociatedBindingValue::EffectRow(value) => self.effect_row(value, scope, errors),
        }
    }
}

fn is_predefined(name: &str) -> bool {
    matches!(
        name,
        "Unit"
            | "Never"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "usize"
            | "isize"
            | "f32"
            | "f64"
            | "char"
            | "Char"
            | "Text"
            | "Bytes"
            | "Array"
            | "Self"
    )
}

fn unknown(kind: &str, name: &str, span: crate::span::Span) -> Diagnostic {
    Diagnostic::error(
        format!("unknown {kind}"),
        format!("`{name}` does not resolve to a declared {kind}"),
        span,
    )
    .with_code("G1R001")
}
