use grandiose_stage0::{
    BindingMode, BodySyntax, DeclarationScan, DefinitionIndex, ElaboratedInterface, ExprKind,
    FileKey, GenericArgument, InterfaceSet, LexedFile, LogicalPath, PackageKey, PatternDecision,
    ScalarType, Type, elaborate_pattern,
};

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
