use grandiose::{
    ast::{
        AssociatedArgumentSyntax, ConstBinaryOp, ConstExprSyntaxKind, ConstKind, FieldVisibility,
        GenericParamKind, GoalArgument, GoalPolarity, TypeSyntax, TypeSyntaxKind,
    },
    lexer, parser,
};

#[test]
fn struct_fields_are_public_by_default_and_private_is_contextual() {
    let source =
        "struct Vault { private secret: i64, visible: Text, private: i64 } main() -> { () }";
    let program = parse(source);
    let fields = &program.structs[0].fields;
    assert_eq!(fields.len(), 3);
    assert_eq!(fields[0].name, "secret");
    assert_eq!(fields[0].visibility, FieldVisibility::Private);
    assert_eq!(&source[fields[0].span.range()], "private secret: i64");
    assert_eq!(fields[1].visibility, FieldVisibility::Public);
    assert_eq!(fields[2].name, "private");
    assert_eq!(fields[2].visibility, FieldVisibility::Public);
}

fn parse(source: &str) -> grandiose::ast::Program {
    parser::parse(lexer::lex(source).unwrap()).unwrap()
}

#[test]
fn retains_explicit_reference_lifetimes_and_named_outlives_constraints() {
    let source = "forward<'long, 'short>(left: &'long i64, right: &'short mut i64) -> &'short i64 where 'long: 'short { left } main() -> { () }";
    let program = parse(source);
    let function = &program.functions[0];
    let references = [
        &function.params[0].ty,
        &function.params[1].ty,
        function.return_type.as_ref().unwrap(),
    ];
    assert_eq!(
        references
            .iter()
            .map(|syntax| match &syntax.kind {
                TypeSyntaxKind::SharedReference {
                    lifetime: Some(lifetime),
                    ..
                }
                | TypeSyntaxKind::UniqueReference {
                    lifetime: Some(lifetime),
                    ..
                } => lifetime.name.as_str(),
                _ => panic!("expected an explicit reference lifetime"),
            })
            .collect::<Vec<_>>(),
        ["'long", "'short", "'short"]
    );
    assert_eq!(&source[references[1].span.range()], "&'short mut i64");
    let constraint = &function.where_clause.as_ref().unwrap().lifetime_outlives[0];
    assert!(constraint.higher_ranked_lifetimes.is_empty());
    assert_eq!(constraint.longer.name, "'long");
    assert_eq!(constraint.shorter.name, "'short");
    assert_eq!(&source[constraint.span.range()], "'long: 'short");
}

#[test]
fn higher_ranked_outlives_binders_are_preserved_on_the_constraint() {
    let source = "check() -> () where for<'long, 'short> 'long: 'short { () } main() -> { () }";
    let program = parse(source);
    let constraint = &program.functions[0]
        .where_clause
        .as_ref()
        .unwrap()
        .lifetime_outlives[0];
    assert_eq!(constraint.higher_ranked_lifetimes.len(), 2);
    assert_eq!(constraint.higher_ranked_lifetimes[0].name, "'long");
    assert_eq!(constraint.higher_ranked_lifetimes[1].name, "'short");
    assert_eq!(&source[constraint.span.range()], "'long: 'short");
}

#[test]
fn const_alias_defaults_expressions_and_fixed_arrays_are_preserved() {
    let source = "type Buffer<const N:u32 = 2 + 3 * 4> = [i64; N + 1]; struct Wrap<const N:u32>{value:Buffer<N + 2>} main()->{()}";
    let program = parse(source);

    let alias = &program.type_aliases[0];
    let parameter = &alias.generics.as_ref().unwrap().params[0];
    assert_eq!(parameter.kind, GenericParamKind::Const(ConstKind::U32));
    let default = parameter.const_default.as_ref().unwrap();
    let ConstExprSyntaxKind::Binary {
        op: ConstBinaryOp::Add,
        rhs,
        ..
    } = &default.kind
    else {
        panic!("expected additive default: {default:#?}");
    };
    assert!(matches!(
        rhs.kind,
        ConstExprSyntaxKind::Binary {
            op: ConstBinaryOp::Multiply,
            ..
        }
    ));

    let array = program.fixed_array(alias.target.span).unwrap();
    assert_eq!(array.element.simple_name(), Some("i64"));
    assert_eq!(&source[array.array.range()], "[i64; N + 1]");
    assert!(matches!(
        array.length.kind,
        ConstExprSyntaxKind::Binary {
            op: ConstBinaryOp::Add,
            ..
        }
    ));

    let field = &program.structs[0].fields[0].ty;
    let arguments = program.type_const_arguments(field.span);
    assert_eq!(arguments.len(), 1);
    assert!(matches!(
        arguments[0].value,
        grandiose::ast::ConstArgumentValueSyntax::Expression(_)
    ));
}

#[test]
fn mixed_nominal_arguments_retain_lifetime_positions_without_treating_regions_as_types() {
    let source = "struct View<'a, T> { value: &'a T } pass<'scope, U>(value: View<'scope, U>) -> View<'scope, U> { move value } main() -> { () }";
    let program = parse(source);
    let function = &program.functions[0];
    for syntax in [
        &function.params[0].ty,
        function.return_type.as_ref().unwrap(),
    ] {
        let TypeSyntaxKind::Application {
            constructor,
            arguments,
            lifetime_arguments,
        } = &syntax.kind
        else {
            panic!("expected a mixed nominal application: {syntax:#?}");
        };
        assert_eq!(constructor.simple_name(), Some("View"));
        assert_eq!(arguments.len(), 1);
        assert_eq!(arguments[0].simple_name(), Some("U"));
        assert_eq!(lifetime_arguments.len(), 1);
        assert_eq!(lifetime_arguments[0].position, 0);
        assert_eq!(lifetime_arguments[0].lifetime.name, "'scope");
        assert_eq!(
            &source[lifetime_arguments[0].lifetime.span.range()],
            "'scope"
        );
    }
}

#[test]
fn qualified_global_binding_retains_its_value_subnamespace_owner() {
    let source = "enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Ok; main() -> { () }";
    let program = parse(source);
    let binding = &program.globals[0];
    assert_eq!(binding.owner.as_deref(), Some("Option"));
    assert_eq!(binding.name, "Some");
    let grandiose::ast::ExprKind::Variable(target) = &binding.value.kind else {
        panic!("expected a constructor value reference")
    };
    assert_eq!(
        target.iter().map(AsRef::as_ref).collect::<Vec<&str>>(),
        ["Result", "Ok"]
    );
}

#[test]
fn qualified_callable_binding_retains_its_owner_and_unqualified_target() {
    let source = "struct Box<T> { value: T } alias_identity<T>(value:T)->T{value} let Box::identity = alias_identity; main()->{()}";
    let program = parse(source);
    let binding = &program.globals[0];
    assert_eq!(binding.owner.as_deref(), Some("Box"));
    assert_eq!(binding.name, "identity");
    let grandiose::ast::ExprKind::Variable(target) = &binding.value.kind else {
        panic!("expected an ordinary callable value reference")
    };
    assert_eq!(
        target.iter().map(AsRef::as_ref).collect::<Vec<&str>>(),
        ["alias_identity"]
    );
}

#[test]
fn preserves_generic_where_and_effect_row_structure_in_source_order() {
    let source = "run<E, S, F, R>(body: F) -> R / {Ask, Trace<i32>} where F: Fn<(), Output = R>, F: RunsIn<E, (), After = S>, E: Use<[0, 0]> { body() }";
    let program = parse(source);
    let function = &program.functions[0];
    let generics = function.generics.as_ref().unwrap();
    assert_eq!(
        generics
            .params
            .iter()
            .map(|param| param.name.as_str())
            .collect::<Vec<_>>(),
        ["E", "S", "F", "R"]
    );
    assert_eq!(&source[generics.span.range()], "<E, S, F, R>");
    let row = function.outward_effects.as_ref().unwrap();
    assert_eq!(row.effects.len(), 2);
    assert_eq!(row.effects[0].simple_name(), Some("Ask"));
    assert_eq!(&source[row.effects[1].span.range()], "Trace<i32>");
    let goals = &function.where_clause.as_ref().unwrap().goals;
    assert_eq!(
        goals
            .iter()
            .map(|goal| goal.relation.path[0].name.as_str())
            .collect::<Vec<_>>(),
        ["Fn", "RunsIn", "Use"]
    );
    assert_eq!(function.params[0].ty.simple_name(), Some("F"));
    assert!(
        matches!(goals[0].relation.arguments[0], GoalArgument::Type(TypeSyntax { kind: TypeSyntaxKind::Tuple(ref fields), .. }) if fields.is_empty())
    );
    assert_eq!(goals[0].relation.bindings[0].name, "Output");
    assert_eq!(
        goals[0].relation.bindings[0]
            .value
            .as_type()
            .and_then(TypeSyntax::simple_name),
        Some("R")
    );
    assert_eq!(goals[1].relation.bindings[0].name, "After");
    assert!(
        matches!(goals[2].relation.arguments[0], GoalArgument::Quantity(ref quantity) if quantity.lower == 0 && quantity.upper == Some(0))
    );
}

#[test]
fn retains_effect_row_aliases_and_their_exact_spans() {
    let source = "cases Common = {Primary, Trace<i32>}; main() -> { () }";
    let program = parse(source);
    let alias = &program.effect_row_aliases[0];
    assert_eq!(alias.name, "Common");
    assert_eq!(
        &source[alias.span.range()],
        "cases Common = {Primary, Trace<i32>};"
    );
    assert_eq!(alias.row.effects.len(), 2);
    assert_eq!(&source[alias.row.effects[1].span.range()], "Trace<i32>");
}

#[test]
fn preserves_generic_drop_target_binders_and_where_clause() {
    let source = "trait Marker {} struct Box<T> { value: T } impl<U> Drop for Box<U> where U: Marker { drop(&mut self) -> { self.value; () } } main() -> { () }";
    let program = parse(source);
    let declaration = &program.drops[0];
    assert_eq!(declaration.target, "Box");
    assert_eq!(declaration.generics.as_ref().unwrap().params[0].name, "U");
    assert_eq!(&source[declaration.target_type.span.range()], "Box<U>");
    assert_eq!(
        declaration.where_clause.as_ref().unwrap().goals[0]
            .relation
            .path[0]
            .name,
        "Marker"
    );
}

#[test]
fn preserves_intrinsic_use_quantity_and_exact_target() {
    let source =
        "struct Ticket { value: i64 } impl Use<[0, infinity]> for Ticket {} main() -> { () }";
    let program = parse(source);
    assert_eq!(program.uses.len(), 1);
    let declaration = &program.uses[0];
    assert_eq!(declaration.quantity.lower, 0);
    assert_eq!(declaration.quantity.upper, None);
    assert_eq!(declaration.target.simple_name(), Some("Ticket"));
    assert_eq!(
        &source[declaration.span.range()],
        "impl Use<[0, infinity]> for Ticket {}"
    );
    assert!(program.impls.is_empty());
}

#[test]
fn preserves_generic_marker_conditioned_use_declaration() {
    let source = "trait Marker {} struct Phantom<T> { marker: i64 } impl<T> Use<[1, 2]> for Phantom<T> where T: Marker {} main() -> { () }";
    let program = parse(source);
    assert_eq!(program.uses.len(), 1);
    assert!(program.impls.is_empty());
    let declaration = &program.uses[0];
    assert_eq!(declaration.generics.as_ref().unwrap().params[0].name, "T");
    assert_eq!(declaration.quantity.lower, 1);
    assert_eq!(declaration.quantity.upper, Some(2));
    assert_eq!(&source[declaration.target.span.range()], "Phantom<T>");
    let goal = &declaration.where_clause.as_ref().unwrap().goals[0];
    assert_eq!(goal.subject.simple_name(), Some("T"));
    assert_eq!(goal.relation.path[0].name, "Marker");
}

#[test]
fn preserves_mixed_marker_and_intrinsic_use_conditions() {
    let source = "trait Marker {} struct Phantom<T> { marker: i64 } impl<T> Use<[1, 1]> for Phantom<T> where T: Marker, T: Use<[0, 2]> {} main() -> { () }";
    let program = parse(source);
    let declaration = &program.uses[0];
    let where_clause = declaration.where_clause.as_ref().unwrap();
    assert_eq!(
        &source[where_clause.span.range()],
        "where T: Marker, T: Use<[0, 2]>"
    );
    assert_eq!(where_clause.goals.len(), 2);

    let marker = &where_clause.goals[0];
    assert_eq!(marker.subject.simple_name(), Some("T"));
    assert_eq!(marker.relation.path[0].name, "Marker");
    assert!(marker.relation.arguments.is_empty());
    assert_eq!(&source[marker.span.range()], "T: Marker");
    assert_eq!(&source[marker.relation.span.range()], "Marker");

    let intrinsic_use = &where_clause.goals[1];
    assert_eq!(intrinsic_use.subject.simple_name(), Some("T"));
    assert_eq!(intrinsic_use.relation.path[0].name, "Use");
    assert_eq!(&source[intrinsic_use.span.range()], "T: Use<[0, 2]>");
    assert_eq!(&source[intrinsic_use.relation.span.range()], "Use<[0, 2]>");
    let GoalArgument::Quantity(quantity) = &intrinsic_use.relation.arguments[0] else {
        panic!("expected intrinsic Use quantity argument");
    };
    assert_eq!(quantity.lower, 0);
    assert_eq!(quantity.upper, Some(2));
    assert_eq!(&source[quantity.span.range()], "[0, 2]");
}

#[test]
fn malformed_structural_constraints_are_diagnosed_without_skipping() {
    for (source, title) in [
        ("run<T, T>() -> { () }", "duplicate generic parameter"),
        (
            "run<F>(f: F) -> i64 where F: Fn<(), Output=i64, Output=i64> { f() }",
            "duplicate associated binding",
        ),
        (
            "run<F>(f: F) -> i64 where F: Use<[x, 0]> { 0 }",
            "invalid use quantity",
        ),
        // Structural const arguments are grammar; kind agreement against the
        // declared associated-item parameters is judged during trait lowering.
        (
            "trait Family { type Member<T>; } read(v:<Text as Family>::Member<1.5>)->Text{v} main()->{()}",
            "invalid const argument",
        ),
        (
            "trait Family { type Member<T>; } read<T>(v:T)->T where T:Family<Member<[1 1]>=Text>{v} main()->{()}",
            "unexpected syntax",
        ),
        ("run<const T>() -> { () }", "unexpected syntax"),
        ("run<for>() -> { () }", "unsupported generic binder"),
    ] {
        let error = parser::parse(lexer::lex(source).unwrap()).unwrap_err();
        assert_eq!(error.title, title, "source: {source}");
    }
}

#[test]
fn retains_kinded_open_effect_row_tails() {
    let source = "effect Ask { [1,1] ask() -> i64 } run<F, e: EffectRow>(body:F)->i64 where F:Fn<(),Output=i64,Effects={Ask | e}>{body()} main()->{()}";
    let program = parse(source);
    let function = &program.functions[0];
    let binders = &function.generics.as_ref().unwrap().params;
    assert_eq!(binders[1].kind, GenericParamKind::EffectRow);
    let grandiose::ast::AssociatedBindingValue::EffectRow(row) =
        &function.where_clause.as_ref().unwrap().goals[0]
            .relation
            .bindings[1]
            .value
    else {
        panic!("expected an effect-row binding")
    };
    assert_eq!(row.effects[0].simple_name(), Some("Ask"));
    assert_eq!(row.tail.as_ref().unwrap().name, "e");
    assert_eq!(&source[row.tail.as_ref().unwrap().span.range()], "e");

    for (bad, title) in [
        (
            "run<F,e>(f:F)->i64 where F:Fn<(),Output=i64,Effects={|e}>{f()} main()->{()}",
            "effect-row tail kind mismatch",
        ),
        (
            "run<F>(f:F)->i64 where F:Fn<(),Output=i64,Effects={|e}>{f()} main()->{()}",
            "unbound effect-row tail",
        ),
        (
            "cases Open={Ask|e}; main()->{()}",
            "unsupported open effect-row alias",
        ),
    ] {
        let error = parser::parse(lexer::lex(bad).unwrap()).unwrap_err();
        assert_eq!(error.title, title, "source: {bad}");
    }
}

#[test]
fn preserves_lifetime_binders_and_trait_arguments() {
    let source = "trait Rel<'a, T> {} struct Local { value: i64 } impl<'a> Rel<'a, Text> for Local {} main()->{()}";
    let program = parse(source);

    let trait_binders = program.traits[0].generics.as_ref().unwrap();
    assert_eq!(trait_binders.params[0].name, "'a");
    assert_eq!(trait_binders.params[0].kind, GenericParamKind::Lifetime);
    assert_eq!(trait_binders.params[1].kind, GenericParamKind::Type);

    let impl_binders = program.impls[0].generics.as_ref().unwrap();
    assert_eq!(impl_binders.params[0].name, "'a");
    assert_eq!(impl_binders.params[0].kind, GenericParamKind::Lifetime);
    let GoalArgument::Lifetime { name, span } = &program.impls[0].trait_ref.arguments[0] else {
        panic!("the first trait argument must remain a lifetime");
    };
    assert_eq!(name, "'a");
    assert_eq!(&source[span.range()], "'a");
}

#[test]
fn higher_ranked_where_type_and_lifetime_binders_are_preserved() {
    let program = parse(
        "trait Rel<T,'a>{} check()->Text where for<Item,'scope> Text:Rel<Item,'scope>{\"ok\"} main()->{()}",
    );
    let goal = &program.functions[0].where_clause.as_ref().unwrap().goals[0];
    assert_eq!(goal.higher_ranked_lifetimes.len(), 2);
    assert_eq!(goal.higher_ranked_lifetimes[0].name, "Item");
    assert_eq!(goal.higher_ranked_lifetimes[0].kind, GenericParamKind::Type);
    assert_eq!(goal.higher_ranked_lifetimes[1].name, "'scope");
    assert_eq!(
        goal.higher_ranked_lifetimes[1].kind,
        GenericParamKind::Lifetime
    );

    let error =
        parser::parse(lexer::lex("trait Rel<for<'a>> {} main()->{()}").unwrap()).unwrap_err();
    assert_eq!(error.title, "unsupported generic binder");
    assert!(error.message.contains("higher-ranked"));

    let const_program = parse(
        "trait Rel<const N:u32>{} check()->() where for<const N: u32> Text:Rel<N>{} main()->{()}",
    );
    let const_binder = &const_program.functions[0]
        .where_clause
        .as_ref()
        .unwrap()
        .goals[0]
        .higher_ranked_lifetimes[0];
    assert_eq!(const_binder.name, "N");
    assert_eq!(const_binder.kind, GenericParamKind::Const(ConstKind::U32));

    let effect_program = parse(
        "trait Rel<Row:EffectRow>{} check()->() where for<Row: EffectRow> Text:Rel<Row>{} main()->{()}",
    );
    let effect_binder = &effect_program.functions[0]
        .where_clause
        .as_ref()
        .unwrap()
        .goals[0]
        .higher_ranked_lifetimes[0];
    assert_eq!(effect_binder.name, "Row");
    assert_eq!(effect_binder.kind, GenericParamKind::EffectRow);
}

#[test]
fn preserves_empty_marker_traits_and_positive_implementations() {
    let source = "trait Marker {} struct Box<T> { value: T } impl Marker for i64 {} impl<T> Marker for Box<T> where T: Marker {} main() -> { () }";
    let program = parse(source);

    assert_eq!(program.traits.len(), 1);
    assert_eq!(program.traits[0].name, "Marker");
    assert!(program.traits[0].generics.is_none());
    assert_eq!(&source[program.traits[0].span.range()], "trait Marker {}");

    assert_eq!(program.impls.len(), 2);
    assert_eq!(program.impls[0].trait_ref.path[0].name, "Marker");
    assert_eq!(program.impls[0].self_ty.simple_name(), Some("i64"));
    assert!(program.impls[0].generics.is_none());
    assert!(program.impls[0].where_clause.is_none());
    assert_eq!(
        &source[program.impls[0].span.range()],
        "impl Marker for i64 {}"
    );

    let recursive = &program.impls[1];
    assert_eq!(recursive.generics.as_ref().unwrap().params[0].name, "T");
    assert_eq!(&source[recursive.self_ty.span.range()], "Box<T>");
    let goals = &recursive.where_clause.as_ref().unwrap().goals;
    assert_eq!(goals.len(), 1);
    assert_eq!(goals[0].subject.simple_name(), Some("T"));
    assert_eq!(goals[0].relation.path[0].name, "Marker");
}

#[test]
fn preserves_trait_and_impl_const_binders_and_ground_arguments() {
    let source = "trait Quota<const Q:Quantity>{} trait Index<const N:u32>{} struct Local{marker:i64} impl<const Q:Quantity> Quota<Q> for Local{} impl Index<7> for Local{} main()->{()}";
    let program = parse(source);

    assert_eq!(
        program.traits[0].generics.as_ref().unwrap().params[0].kind,
        GenericParamKind::Const(ConstKind::Quantity)
    );
    assert_eq!(
        program.traits[1].generics.as_ref().unwrap().params[0].kind,
        GenericParamKind::Const(ConstKind::U32)
    );
    assert_eq!(
        program.impls[0].generics.as_ref().unwrap().params[0].kind,
        GenericParamKind::Const(ConstKind::Quantity)
    );
    let GoalArgument::Type(bound) = &program.impls[0].trait_ref.arguments[0] else {
        panic!("bare const binder reference remains identifier syntax in the parser AST");
    };
    assert_eq!(bound.simple_name(), Some("Q"));
    let GoalArgument::U32 { value, span } = &program.impls[1].trait_ref.arguments[0] else {
        panic!("expected a ground u32 argument");
    };
    assert_eq!(*value, 7);
    assert_eq!(&source[span.range()], "7");
}

#[test]
fn ordinary_type_applications_preserve_structural_const_literal_positions() {
    let source = "struct Token<T>{marker:i64} inspect(a:Token<7>,b:Token<[1,infinity]>)->(){()} main()->{()}";
    let program = parse(source);
    assert_eq!(program.type_const_arguments.len(), 2);
    let first = &program.type_const_arguments[0];
    assert_eq!(first.arguments[0].position, 0);
    let grandiose::ast::ConstArgumentValueSyntax::U32 { value, span } = &first.arguments[0].value
    else {
        panic!("expected u32 const argument")
    };
    assert_eq!(*value, 7);
    assert_eq!(&source[span.range()], "7");
    let grandiose::ast::ConstArgumentValueSyntax::Quantity(quantity) =
        &program.type_const_arguments[1].arguments[0].value
    else {
        panic!("expected quantity const argument")
    };
    assert_eq!((quantity.lower, quantity.upper), (1, None));
    assert_eq!(&source[quantity.span.range()], "[1,infinity]");
}

#[test]
fn preserves_ordered_parameterized_marker_traits() {
    let program = parse("trait Rel<From, To> {} main() -> { () }");
    let generics = program.traits[0].generics.as_ref().unwrap();
    assert_eq!(
        generics
            .params
            .iter()
            .map(|parameter| parameter.name.as_str())
            .collect::<Vec<_>>(),
        ["From", "To"]
    );
}

#[test]
fn preserves_negative_implementations_and_where_goals() {
    let source = "trait Rel<To> {} struct Box<T> { value: T } impl<T> !Rel<i64> for Box<T> {} require<T>(value: T) -> T where T: !Rel<i64>, T: Rel<Text> { value } main() -> { () }";
    let program = parse(source);

    let implementation = &program.impls[0];
    assert_eq!(implementation.polarity, GoalPolarity::Negative);
    assert_eq!(
        &source[implementation.span.range()],
        "impl<T> !Rel<i64> for Box<T> {}"
    );
    assert_eq!(&source[implementation.trait_ref.span.range()], "Rel<i64>");

    let goals = &program.functions[0].where_clause.as_ref().unwrap().goals;
    assert_eq!(goals.len(), 2);
    assert_eq!(goals[0].polarity, GoalPolarity::Negative);
    assert_eq!(&source[goals[0].span.range()], "T: !Rel<i64>");
    assert_eq!(&source[goals[0].relation.span.range()], "Rel<i64>");
    assert_eq!(goals[1].polarity, GoalPolarity::Positive);
    assert_eq!(&source[goals[1].span.range()], "T: Rel<Text>");
}

#[test]
fn preserves_associated_type_declarations_definitions_and_projections() {
    let source = "trait Value<Context> { type Item; } struct Box<T> { value: T } impl<T> Value<Text> for Box<T> { type Item = (T, Text); } read(value: <Box<i64> as Value<Text>>::Item) -> <Box<Text> as Value<Text>>::Item where Box<Text>: Value<Text, Item=(Text, Text)> { value } main() -> { () }";
    let program = parse(source);

    let declaration = &program.traits[0].associated_types[0];
    assert_eq!(declaration.name, "Item");
    assert_eq!(&source[declaration.span.range()], "type Item;");

    let definition = &program.impls[0].associated_types[0];
    assert_eq!(definition.name, "Item");
    assert_eq!(&source[definition.span.range()], "type Item = (T, Text);");
    assert_eq!(&source[definition.value.span().range()], "(T, Text)");

    let TypeSyntaxKind::Projection {
        subject,
        trait_ref,
        item,
        arguments,
        ..
    } = &program.functions[0].params[0].ty.kind
    else {
        panic!("expected a fully qualified associated projection");
    };
    assert_eq!(&source[subject.span.range()], "Box<i64>");
    assert_eq!(&source[trait_ref.span.range()], "Value<Text>");
    assert_eq!(item.name, "Item");
    assert!(arguments.is_empty());
    assert_eq!(
        &source[program.functions[0].params[0].ty.span.range()],
        "<Box<i64> as Value<Text>>::Item"
    );

    let goal = &program.functions[0].where_clause.as_ref().unwrap().goals[0];
    assert_eq!(goal.relation.bindings[0].name, "Item");
    assert_eq!(
        &source[goal.relation.bindings[0].value.span().range()],
        "(Text, Text)"
    );
}

#[test]
fn preserves_gat_binders_projection_arguments_and_equalities() {
    let source = "trait Family<C> { type Member<'a, T>; } struct Box<S>{value:S} struct Triple<A,B,C>{first:A,second:B,third:C} impl<S,C> Family<C> for Box<S> { type Member<'scope, T> = Triple<S,C,T>; } read(value:<Box<i64> as Family<Text>>::Member<'static, u16>)->u16 where Box<i64>: Family<Text, Member<'static, u16> = Triple<i64,Text,u16>> { value.third } main()->{()}";
    let program = parse(source);

    let declaration = &program.traits[0].associated_types[0];
    let declaration_binders = declaration.generics.as_ref().unwrap();
    assert_eq!(declaration.name, "Member");
    assert_eq!(declaration_binders.params[0].name, "'a");
    assert_eq!(
        declaration_binders.params[0].kind,
        GenericParamKind::Lifetime
    );
    assert_eq!(declaration_binders.params[1].name, "T");
    assert_eq!(&source[declaration.span.range()], "type Member<'a, T>;");

    let definition = &program.impls[0].associated_types[0];
    let definition_binders = definition.generics.as_ref().unwrap();
    assert_eq!(definition.name, "Member");
    assert_eq!(definition_binders.params[0].name, "'scope");
    assert_eq!(
        definition_binders.params[0].kind,
        GenericParamKind::Lifetime
    );
    assert_eq!(definition_binders.params[1].name, "T");
    assert_eq!(
        &source[definition.span.range()],
        "type Member<'scope, T> = Triple<S,C,T>;"
    );

    let TypeSyntaxKind::Projection {
        subject,
        trait_ref,
        item,
        arguments,
        ..
    } = &program.functions[0].params[0].ty.kind
    else {
        panic!("expected a GAT projection");
    };
    assert_eq!(&source[subject.span.range()], "Box<i64>");
    assert_eq!(&source[trait_ref.span.range()], "Family<Text>");
    assert_eq!(item.name, "Member");
    assert_eq!(arguments.len(), 2);
    let AssociatedArgumentSyntax::Lifetime { name, span } = &arguments[0] else {
        panic!("the first GAT argument must remain a lifetime");
    };
    assert_eq!(name, "'static");
    assert_eq!(&source[span.range()], "'static");
    assert_eq!(
        arguments[1].as_type().and_then(TypeSyntax::simple_name),
        Some("u16")
    );

    let binding = &program.functions[0].where_clause.as_ref().unwrap().goals[0]
        .relation
        .bindings[0];
    assert_eq!(binding.name, "Member");
    assert_eq!(binding.arguments.len(), 2);
    let AssociatedArgumentSyntax::Lifetime { name, span } = &binding.arguments[0] else {
        panic!("the first associated equality argument must remain a lifetime");
    };
    assert_eq!(name, "'static");
    assert_eq!(&source[span.range()], "'static");
    assert_eq!(
        binding.arguments[1]
            .as_type()
            .and_then(TypeSyntax::simple_name),
        Some("u16")
    );
    assert_eq!(
        &source[binding.span.range()],
        "Member<'static, u16> = Triple<i64,Text,u16>"
    );
}

#[test]
fn preserves_distinct_lexical_trait_environments_on_generic_callables() {
    let source = "trait Mark {} trait Value { type Item; } positive<T>(value:T)->T where T: Mark { value } negative<T>(value:T)->T where T: !Mark { value } equal<T>(value:T)->T where T: Value<Item=Text>, T: Mark { value } main()->{()}";
    let program = parse(source);

    let positive = &program.functions[0].where_clause.as_ref().unwrap().goals;
    assert_eq!(positive.len(), 1);
    assert_eq!(positive[0].polarity, GoalPolarity::Positive);
    assert_eq!(&source[positive[0].span.range()], "T: Mark");

    let negative = &program.functions[1].where_clause.as_ref().unwrap().goals;
    assert_eq!(negative.len(), 1);
    assert_eq!(negative[0].polarity, GoalPolarity::Negative);
    assert_eq!(&source[negative[0].span.range()], "T: !Mark");

    let equal = &program.functions[2].where_clause.as_ref().unwrap().goals;
    assert_eq!(equal.len(), 2);
    assert_eq!(equal[0].polarity, GoalPolarity::Positive);
    assert_eq!(&source[equal[0].span.range()], "T: Value<Item=Text>");
    assert_eq!(equal[0].relation.bindings[0].name, "Item");
    assert_eq!(
        equal[0].relation.bindings[0]
            .value
            .as_type()
            .and_then(TypeSyntax::simple_name),
        Some("Text")
    );
    assert_eq!(&source[equal[1].span.range()], "T: Mark");
}

#[test]
fn rejects_marker_features_outside_the_parameterized_kernel() {
    for (source, title) in [
        (
            "trait Marker { check() -> { () } } main() -> { () }",
            "unexpected syntax",
        ),
        (
            "trait Marker<T> {} impl Marker<Item=i64> for i64 {} main() -> { () }",
            "unsupported implementation trait",
        ),
    ] {
        let error = parser::parse(lexer::lex(source).unwrap()).unwrap_err();
        assert_eq!(error.title, title, "source: {source}");
    }
}

fn source_text<'a>(source: &'a str, ty: &TypeSyntax) -> &'a str {
    &source[ty.span.range()]
}

#[test]
fn retains_nested_type_syntax_and_exact_spans_in_every_signature_position() {
    let source = "\
type Alias = Result<&mut (i64, Option<&Text>), ()>;
struct Record { value: &Map<Text, (i64, &mut Bytes)> }
enum Event { Send(core::Packet<&Text>, ()), Empty }
effect Query { ask(input: &mut Vec<(i64, Text)>) -> Option<&Text>; }
run(arg: &Alias) -> Result<(i64, Text), &mut Error> { () }
";
    let program = parse(source);

    let alias = &program.type_aliases[0].target;
    assert_eq!(
        source_text(source, alias),
        "Result<&mut (i64, Option<&Text>), ()>"
    );
    let TypeSyntaxKind::Application {
        constructor,
        arguments,
        ..
    } = &alias.kind
    else {
        panic!("expected generic application: {alias:#?}");
    };
    assert_eq!(constructor.simple_name(), Some("Result"));
    assert_eq!(arguments.len(), 2);
    assert!(matches!(
        arguments[0].kind,
        TypeSyntaxKind::UniqueReference { referent: _, .. }
    ));
    assert!(matches!(arguments[1].kind, TypeSyntaxKind::Tuple(ref fields) if fields.is_empty()));

    let field = &program.structs[0].fields[0].ty;
    assert_eq!(source_text(source, field), "&Map<Text, (i64, &mut Bytes)>");
    assert!(matches!(
        field.kind,
        TypeSyntaxKind::SharedReference { referent: _, .. }
    ));

    let payload = &program.enums[0].variants[0].fields[0];
    assert_eq!(source_text(source, payload), "core::Packet<&Text>");
    let TypeSyntaxKind::Application { constructor, .. } = &payload.kind else {
        panic!("expected application");
    };
    let TypeSyntaxKind::Path(segments) = &constructor.kind else {
        panic!("expected qualified path");
    };
    assert_eq!(
        segments
            .iter()
            .map(|part| part.name.as_str())
            .collect::<Vec<_>>(),
        ["core", "Packet"]
    );
    assert_eq!(&source[segments[0].span.range()], "core");
    assert_eq!(&source[segments[1].span.range()], "Packet");
    assert_eq!(constructor.simple_name(), None);

    let operation = &program.effects[0].operations[0];
    assert_eq!(
        source_text(source, &operation.params[0].ty),
        "&mut Vec<(i64, Text)>"
    );
    assert_eq!(
        source_text(source, operation.return_type.as_ref().unwrap()),
        "Option<&Text>"
    );

    let function = &program.functions[0];
    assert_eq!(source_text(source, &function.params[0].ty), "&Alias");
    assert_eq!(
        source_text(source, function.return_type.as_ref().unwrap()),
        "Result<(i64, Text), &mut Error>"
    );
}

#[test]
fn unit_and_never_results_are_retained_without_changing_empty_unit_syntax() {
    let program = parse("effect Stop { stop() -> !; } main() -> { () }");
    let result = program.effects[0].operations[0]
        .return_type
        .as_ref()
        .unwrap();
    assert!(matches!(result.kind, TypeSyntaxKind::Never));
    assert!(program.functions[0].return_type.is_none());
}

#[test]
fn malformed_nested_types_are_rejected_at_the_structural_error() {
    for source in [
        "type Bad = Pair<>; main() -> { () }",
        "type Bad = Pair<i64, Text; main() -> { () }",
        "type Bad = (i64, Text; main() -> { () }",
        "main(value: &mut) -> { () }",
    ] {
        let error = parser::parse(lexer::lex(source).unwrap()).unwrap_err();
        assert!(error.span.is_some(), "{error:#?}");
    }
}

#[test]
fn commas_inside_nested_types_do_not_split_outer_fields_or_parameters() {
    let program = parse(
        "struct S { first: Pair<(i64, Text), &mut Vec<Bytes>>, second: Unit } \
         f(value: Pair<(i64, Text), Vec<Unit>>, other: i64) -> Unit { () }",
    );
    assert_eq!(program.structs[0].fields.len(), 2);
    assert_eq!(program.functions[0].params.len(), 2);
    assert_eq!(program.structs[0].fields[0].ty.simple_name(), None);
    assert_eq!(program.structs[0].fields[1].ty.simple_name(), Some("Unit"));
}
