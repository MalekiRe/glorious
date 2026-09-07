use grandiose_stage0::{
    BindingMode, BodySyntax, DeclarationScan, DefinitionIndex, ElaboratedInterface, ExprKind,
    FileKey, GenericArgument, InterfaceSet, LexedFile, LogicalPath, PackageKey, PatternDecision,
    PatternGenericScope, ScalarType, Type, elaborate_pattern, elaborate_pattern_with_scope,
};
use std::collections::BTreeMap;

fn parsed(
    source: &str,
) -> (
    grandiose_stage0::PackageInterface,
    grandiose_stage0::ElaboratedInterface,
    BodySyntax,
) {
    let package = PackageKey("pattern@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, main.body.unwrap());
    (interface, signatures, body)
}

#[test]
fn empty_pattern_distinguishes_unit_from_nonempty_and_scalar_subjects() {
    let (interface, signatures, body) = parsed("pub fn main() -> () { () is () }");
    let ExprKind::Block(values) = &body.expression(body.root).kind else { panic!("block"); };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else { panic!("test"); };
    for (subject, accepted) in [
        (Type::Unit, true),
        (Type::Scalar(ScalarType::I64), false),
        (Type::Tuple(vec![Type::Unit]), false),
    ] {
        let result = elaborate_pattern(&body, pattern, subject.clone(),
            &DefinitionIndex::from_interface(&interface), &signatures, &interface.module);
        assert_eq!(!result.recovered, accepted, "{subject:?}: {:?}", result.diagnostics);
        if accepted {
            assert!(!result.plan.refutable);
            assert!(result.plan.bindings.is_empty());
            assert!(result.diagnostics.is_empty());
        } else {
            assert!(result.diagnostics.iter().any(|d| matches!(d.code, "G4202" | "G4203")));
        }
    }
}

#[test]
fn is_pattern_elaboration_rejects_duplicate_resolved_binders() {
    let source = "pub fn main() -> () { (1, 2) is (value, value) }";
    let (interface, signatures, body) = parsed(source);
    assert!(body.diagnostics.is_empty());
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let result = elaborate_pattern(
        &body,
        pattern,
        Type::Tuple(vec![Type::Scalar(ScalarType::I64); 2]),
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(result.recovered);
    assert!(result.diagnostics.iter().any(|diagnostic| diagnostic.code == "G4017"));
    assert_eq!(result.plan.bindings.len(), 1);
}

#[test]
fn enum_pattern_elaboration_uses_frozen_layouts_and_fresh_binder_keys() {
    let source = "pub enum Result { Ok(i64), Err(Text) } pub fn main(value: Result) -> () { value is Result::Ok(found) }";
    let (interface, signatures, body) = parsed(source);
    let enum_definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Result"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let plan = elaborate_pattern(
        &body,
        pattern,
        Type::Nominal {
            definition: enum_definition,
            arguments: vec![],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert!(plan.plan.refutable);
    assert!(matches!(
        plan.plan.decision,
        PatternDecision::Enum { definition, variant: 0, .. } if definition == enum_definition
    ));
    assert_eq!(plan.plan.bindings.len(), 1);
    assert_eq!(plan.plan.bindings[0].name, "found");
    assert_eq!(plan.plan.bindings[0].mode, BindingMode::Copy);
}

#[test]
fn record_pattern_tracks_implicit_discarded_fields_for_later_use_checking() {
    let source = "pub struct Pair { left: i64, right: Text } pub fn main(value: Pair) -> () { value is Pair { left: found } }";
    let (interface, signatures, body) = parsed(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Pair"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let plan = elaborate_pattern(
        &body,
        pattern,
        Type::Nominal {
            definition,
            arguments: vec![],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert_eq!(plan.plan.discarded.len(), 1);
    assert_eq!(plan.plan.bindings[0].name, "found");
}

#[test]
fn named_enum_payload_patterns_keep_selected_field_indices() {
    let source = "pub enum Result { Ok { code: i64, detail: Text } } pub fn main(value: Result) -> () { value is Result::Ok { code: found } }";
    let (interface, signatures, body) = parsed(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Result"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let plan = elaborate_pattern(
        &body,
        pattern,
        Type::Nominal {
            definition,
            arguments: vec![],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert!(matches!(
        plan.plan.decision,
        PatternDecision::Enum { ref fields, .. } if fields.len() == 1 && fields[0].0 == 0
    ));
    assert_eq!(plan.plan.discarded.len(), 1);
}

#[test]
fn explicit_nominal_pattern_arguments_must_match_the_subject_identity() {
    let source = "pub enum Result<T> { Ok(T) } pub fn main(value: Result<i64>) -> () { value is Result<Text>::Ok(_) }";
    let (interface, signatures, body) = parsed(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Result"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let plan = elaborate_pattern(
        &body,
        pattern,
        Type::Nominal {
            definition,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(
        plan.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4216"),
        "{:#?}",
        plan.diagnostics
    );
}

#[test]
fn explicit_generic_nominal_pattern_identity_accepts_the_matching_application() {
    let source = "pub enum Result<T> { Ok(T), Err } pub fn main(value: Result<i64>) -> () { value is Result<i64>::Ok(found) }";
    let (interface, signatures, body) = parsed(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Result"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let plan = elaborate_pattern(
        &body,
        pattern,
        Type::Nominal {
            definition,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert!(matches!(
        plan.plan.decision,
        PatternDecision::Enum { variant: 0, .. }
    ));
}

#[test]
fn generic_nominal_pattern_arguments_preserve_symbolic_associated_type_identity() {
    let source = "trait Element { type Item; } pub struct Boxed<T> { value: T } pub fn main<T>(value: Boxed<<T as Element>::Item>) -> Bool { value is Boxed<<T as Element>::Item> { value: _ } }";
    let (interface, signatures, body) = parsed(source);
    let boxed = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Boxed"))
        .unwrap()
        .key;
    let element = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Element"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let projection = Type::Projection {
        subject: Box::new(Type::Generic(0)),
        trait_definition: element,
        trait_arguments: vec![],
        name: "Item".into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let plan = elaborate_pattern_with_scope(
        &body,
        pattern,
        Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(projection)],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
        &PatternGenericScope {
            types: BTreeMap::from([("T".into(), 0)]),
            ..PatternGenericScope::default()
        },
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert!(
        matches!(plan.plan.decision, PatternDecision::Record { definition, .. } if definition == boxed)
    );
}

#[test]
fn generic_nominal_pattern_arguments_preserve_gat_item_arguments() {
    let source = "trait Apply { type Output<U>; } pub struct Boxed<T> { value: T } pub fn main<T>(value: Boxed<<T as Apply>::Output<i64>>) -> Bool { value is Boxed<<T as Apply>::Output<i64>> { value: _ } }";
    let (interface, signatures, body) = parsed(source);
    let boxed = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Boxed"))
        .unwrap()
        .key;
    let apply = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Apply"))
        .unwrap()
        .key;
    let ExprKind::Block(values) = &body.expression(body.root).kind else {
        panic!("expected body block");
    };
    let ExprKind::Is { pattern, .. } = body.expression(values[0]).kind else {
        panic!("expected structural test");
    };
    let projection = Type::Projection {
        subject: Box::new(Type::Generic(0)),
        trait_definition: apply,
        trait_arguments: vec![],
        name: "Output".into(),
        item_generic_kinds: vec![grandiose_stage0::GenericKind::Type],
        item_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    };
    let plan = elaborate_pattern_with_scope(
        &body,
        pattern,
        Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(projection)],
        },
        &DefinitionIndex::from_interface(&interface),
        &signatures,
        &interface.module,
        &PatternGenericScope {
            types: BTreeMap::from([("T".into(), 0)]),
            ..PatternGenericScope::default()
        },
    );
    assert!(plan.diagnostics.is_empty(), "{:#?}", plan.diagnostics);
    assert!(
        matches!(plan.plan.decision, PatternDecision::Record { definition, .. } if definition == boxed)
    );
}
