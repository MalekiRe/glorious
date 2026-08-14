use grandiose_stage0::{
    BodySyntax, CaptureMode, CoreHandlerResumption, CoreKind, DeclarationScan, DefinitionIndex,
    ElaboratedInterface, FileKey, InterfaceSet, LexedFile, Lifetime, LogicalPath, MirInstruction,
    MirLowering, PackageKey, PlaceFlow, Type, TypedBody, implementation_method_key,
};

fn flow_for(package_name: &str, source: &str) -> PlaceFlow {
    let package = PackageKey(package_name.into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    PlaceFlow::analyze(&core)
}

#[test]
fn typed_core_elaborates_scoped_locals_and_flat_numeric_operator_chains() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; value + 2 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let root = core.expression(core.root);
    assert!(matches!(root.kind, CoreKind::Block(_)));
    assert!(
        core.expressions
            .iter()
            .any(|expression| matches!(expression.kind, CoreKind::Binary { .. }))
    );
}

#[test]
fn typed_core_checks_a_function_body_against_its_declared_result() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> Text { 1 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4110")
    );
}

#[test]
fn typed_core_uses_the_enclosing_callable_where_clause_as_bound_evidence() {
    let package = PackageKey("core-ambient-where-bound@0.1.0".into());
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } pub fn forwards_mark<T>(value: T) -> T where T: Mark { requires_mark(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("forwards_mark"))
        .expect("forwarding definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("forwarding body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_does_not_invent_callable_where_bound_evidence() {
    let package = PackageKey("core-missing-ambient-where-bound@0.1.0".into());
    let source = "trait Mark {} pub fn requires_mark<T>(value: T) -> T where T: Mark { value } pub fn forwards_without_mark<T>(value: T) -> T { requires_mark(value) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("forwards_without_mark"))
        .expect("forwarding definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("forwarding body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4143"),
        "missing unproven-bound diagnostic: {:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_normalizes_nested_concrete_associated_type_projections() {
    let package = PackageKey("core-nested-associated-projection@0.1.0".into());
    let source = "trait Source { type Item; } trait Wrapper { type Item; } struct Value {} impl Source for Value { type Item = i64; } impl Wrapper for Value { type Item = <Value as Source>::Item; } pub fn value() -> <Value as Wrapper>::Item { 1 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("value body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_reports_recursive_associated_type_projections() {
    let package = PackageKey("core-recursive-associated-projection@0.1.0".into());
    let source = "trait Loop { type Item; } struct Value {} impl Loop for Value { type Item = <Value as Loop>::Item; } pub fn value() -> <Value as Loop>::Item { 1 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("value body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4157"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_core_admits_calls_with_the_same_symbolic_effect_row_tail() {
    let package = PackageKey("core-symbolic-effect-tail@0.1.0".into());
    let source = "pub fn forward<e: EffectRow>() -> i64 / { | e } { 0 } pub fn relay<T, e: EffectRow>(value: T) -> i64 / { | e } { forward() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_instantiates_unconstrained_effect_row_tails_to_a_closed_caller() {
    let package = PackageKey("core-closed-effect-tail-instantiation@0.1.0".into());
    let source = "pub fn forward<e: EffectRow>() -> i64 / { | e } { 0 } pub fn closed() -> i64 { forward() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let closed = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("closed"))
        .expect("closed definition");
    let body = BodySyntax::parse(&lexed, source, closed.body.expect("closed body"));
    let core = TypedBody::elaborate(
        closed,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_core_retains_selected_trait_method_evidence() {
    let package = PackageKey("core-trait-method-evidence@0.1.0".into());
    let source = "trait Increment { fn increment(value: i64) -> i64; } impl Increment for i64 { fn increment(value: i64) -> i64 { value + 1 } } pub fn main() -> i64 { Increment::increment(41) }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, main.body.unwrap());
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.kind == grandiose_stage0::DeclarationKind::Implementation)
        .expect("implementation definition");
    assert!(core.expressions.iter().any(|expression| {
        matches!(
            expression.kind,
            CoreKind::TraitMethod { evidence, method }
                if evidence == implementation.key
                    && method == implementation_method_key(implementation.key, "increment")
        )
    }));
}

#[test]
fn placeflow_rejects_use_after_move_from_typed_core() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; move value; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001")
    );
}

#[test]
fn placeflow_rejects_read_while_a_unique_borrow_is_live() {
    let package = PackageKey("core-unique-borrow-read@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; let loan = &mut value; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a unique loan must exclude reads: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_tracks_a_field_borrow_back_to_its_root_local() {
    let package = PackageKey("core-projection-borrow@0.1.0".into());
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; move pair; 0 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5004"),
        "a projection loan must keep its root from moving: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_allows_disjoint_field_access_while_a_projection_loan_is_live() {
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &mut pair.left; pair.right = 3; pair.right }";
    let flow = flow_for("core-projection-disjoint@0.1.0", source);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
}

#[test]
fn placeflow_rejects_accesses_that_overlap_a_projection_loan() {
    let unique_read = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &mut pair.left; pair.left }";
    let flow = flow_for("core-projection-unique-read@0.1.0", unique_read);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5008"),
        "a unique field loan must exclude reads of that field: {:#?}",
        flow.diagnostics
    );

    let shared_write = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; pair.left = 3; pair.right }";
    let flow = flow_for("core-projection-shared-write@0.1.0", shared_write);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5007"),
        "a shared field loan must exclude writes to that field: {:#?}",
        flow.diagnostics
    );

    let whole_unique = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; let loan = &pair.left; let whole = &mut pair; 0 }";
    let flow = flow_for("core-projection-whole-conflict@0.1.0", whole_unique);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5006"),
        "a whole unique loan must conflict with a live field loan: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn placeflow_conservatively_consumes_a_root_after_a_projection_move() {
    let package = PackageKey("core-projection-move@0.1.0".into());
    let source = "pub struct Pair { left: i64, right: i64 } pub fn main() -> i64 { let pair = Pair { left: 1, right: 2 }; move pair.left; pair.right }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "a projection move must consume its root until partial moves are tracked: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn typed_core_and_placeflow_lower_to_validated_mir() {
    let package = PackageKey("core@0.1.0".into());
    let source = "pub fn main() -> i64 { let value = 1; value + 2 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    let lowered = MirLowering::lower(definition.key, &core, &flow);
    assert!(lowered.diagnostics.is_empty(), "{:#?}", lowered.diagnostics);
    let mir = lowered.function.unwrap();
    assert!(
        mir.entry_block()
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::AddI64 { .. }))
    );
    assert!(mir.validate().is_ok());
}

#[test]
fn typed_closures_become_callable_core_values_with_explicit_capture_modes() {
    let package = PackageKey("core-closure@0.1.0".into());
    let source =
        "pub fn main(value: i64) -> i64 { let add = (extra: i64) -> i64 { value + extra }; 1 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(CoreKind::Closure {
        parameters,
        captures,
        ..
    }) = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            closure @ CoreKind::Closure { .. } => Some(closure),
            _ => None,
        })
    else {
        panic!("typed closure was not elaborated")
    };
    assert_eq!(parameters[0].0, "extra");
    assert_eq!(captures.len(), 1);
    assert_eq!(captures[0].name, "value");
    assert_eq!(captures[0].mode, CaptureMode::SharedBorrow);
}

#[test]
fn typed_closures_preserve_enclosing_lifetime_binders() {
    let package = PackageKey("core-closure-lifetime@0.1.0".into());
    let source = "pub fn main<'a>(value: &'a i64) -> i64 { let identity = (item: &'a i64) -> &'a i64 { item }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find(|expression| matches!(expression.kind, CoreKind::Closure { .. }))
        .expect("typed closure");
    let Type::Callable {
        parameters, result, ..
    } = &closure.ty
    else {
        panic!("typed closure did not receive a callable type")
    };
    assert!(matches!(
        parameters.as_slice(),
        [Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }]
    ));
    assert!(matches!(
        result.as_ref(),
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
}

#[test]
fn typed_closures_reject_unbound_lifetime_annotations() {
    let package = PackageKey("core-closure-unbound-lifetime@0.1.0".into());
    let source = "pub fn main() -> i64 { let identity = (item: &'a i64) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4170"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closures_reject_lifetime_binders_in_type_position() {
    let package = PackageKey("core-closure-lifetime-type@0.1.0".into());
    let source = "pub fn main<'a>() -> i64 { let invalid = (item: 'a) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4172"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closures_reject_const_binders_in_type_position() {
    let package = PackageKey("core-closure-const-type@0.1.0".into());
    let source = "pub fn main<n: u32>() -> i64 { let invalid = (item: n) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4173"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_type_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-associated-projection@0.1.0".into());
    let source = "trait Iterator { type Item; } struct Range<T> {} impl<T> Iterator for Range<T> { type Item = T; } pub fn main() -> i64 { let identity = (value: <Range<Text> as Iterator>::Item) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn concrete_gat_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<T>; } struct Wrapper {} impl Apply for Wrapper { type Output<T> = T; } pub fn main() -> i64 { let identity = (value: <Wrapper as Apply>::Output<Text>) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn structural_const_associated_projections_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-const-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<n: u32>; } struct Wrapper {} impl Apply for Wrapper { type Output<n: u32> = Text; } pub fn main() -> i64 { let identity = (value: <Wrapper as Apply>::Output<7>) -> Text { value }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(body.diagnostics.is_empty(), "{body:#?}");
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        expression.kind,
        CoreKind::Closure { ref parameters, .. }
            if parameters[0].1 == grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)
    )));
}

#[test]
fn associated_effect_rows_are_rejected_by_the_type_projection_surface() {
    let package = PackageKey("core-associated-effect-row@0.1.0".into());
    let source = "trait HasEffects { type Effects: EffectRow; } struct Value {} impl HasEffects for Value { type Effects = {}; } pub fn main() -> i64 { let value = (input: <Value as HasEffects>::Effects) -> i64 { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4149"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_effect_rows_normalize_in_typed_closure_contracts() {
    let package = PackageKey("core-closure-associated-effect-row@0.1.0".into());
    let source = "effect Trace { note(); } trait Capability { type Effects: EffectRow; } struct Value {} impl Capability for Value { type Effects = {Trace}; } pub fn main() -> i64 { let worker = () -> i64 / { <Value as Capability>::Effects } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .expect("Trace definition")
        .key;
    let body = BodySyntax::parse(&lexed, source, main.body.expect("main body"));
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.effects.iter().any(|effect| effect.definition == trace)
    )));
}

#[test]
fn typed_closure_contracts_preserve_generic_effect_instances() {
    let package = PackageKey("core-closure-generic-effect@0.1.0".into());
    let source = "effect Trace<T> { note(value: T); } pub fn main() -> i64 { let worker = () -> i64 / { Trace<Text> } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let main = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .expect("Trace definition")
        .key;
    let body = BodySyntax::parse(&lexed, source, main.body.expect("main body"));
    let core = TypedBody::elaborate(
        main,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.effects.iter().any(|effect| effect.definition == trace
                && effect.arguments == [grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::Text)])
    )));
}

#[test]
fn typed_closure_contracts_preserve_enclosing_open_effect_row_tails() {
    let package = PackageKey("core-closure-open-effect-row@0.1.0".into());
    let source = "pub fn relay<e: EffectRow>() -> i64 / { | e } { let worker = () -> i64 / { | e } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(core.expressions.iter().any(|expression| matches!(
        &expression.ty,
        grandiose_stage0::Type::Callable { effects, .. }
            if effects.tail == Some(grandiose_stage0::EffectTail::Generic(0))
    )));
}

#[test]
fn typed_closure_rejects_ordinary_generic_as_effect_row_tail() {
    let package = PackageKey("core-closure-invalid-effect-row@0.1.0".into());
    let source = "pub fn relay<T>() -> i64 { let worker = () -> i64 / { | T } { 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let body = BodySyntax::parse(&lexed, source, relay.body.expect("relay body"));
    let core = TypedBody::elaborate(
        relay,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4115"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn typed_closure_body_checks_against_its_own_effect_contract() {
    let package = PackageKey("core-closure-effect-boundary@0.1.0".into());
    let source = "effect Trace { note(); } pub fn outer() -> i64 { let worker = () -> i64 / {Trace} { Trace::note(); 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let outer = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("outer"))
        .expect("outer definition");
    let body = BodySyntax::parse(&lexed, source, outer.body.expect("outer body"));
    let core = TypedBody::elaborate(
        outer,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn typed_closure_body_rejects_effects_missing_from_its_own_contract() {
    let package = PackageKey("core-closure-closed-effect-boundary@0.1.0".into());
    let source = "effect Trace { note(); } pub fn outer() -> i64 / {Trace} { let worker = () -> i64 { Trace::note(); 0 }; 0 }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let outer = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("outer"))
        .expect("outer definition");
    let body = BodySyntax::parse(&lexed, source, outer.body.expect("outer body"));
    let core = TypedBody::elaborate(
        outer,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "{:#?}",
        core.diagnostics
    );
}

#[test]
fn concrete_associated_effect_rows_normalize_at_call_boundaries() {
    let package = PackageKey("core-associated-effect-row-normalization@0.1.0".into());
    let source = "effect Trace { note(); } trait Capability { type Effects: EffectRow; } struct Value {} impl Capability for Value { type Effects = {Trace}; } pub fn worker() -> i64 / { <Value as Capability>::Effects } { 1 } pub fn main() -> i64 / { Trace } { worker() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn generic_associated_effect_rows_normalize_item_arguments() {
    let package = PackageKey("core-gat-effect-row-normalization@0.1.0".into());
    let source = "effect Trace<T> { note(value: T); } trait Capability { type Effects<T>: EffectRow; } struct Value {} impl Capability for Value { type Effects<T> = {Trace<T>}; } pub fn worker() -> i64 / { <Value as Capability>::Effects<Text> } { 1 } pub fn main() -> i64 / { Trace<Text> } { worker() }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
}

#[test]
fn placeflow_applies_a_closure_move_capture_when_the_closure_is_created() {
    let package = PackageKey("core-closure-move@0.1.0".into());
    let source = "pub fn main(value: i64) -> i64 { let consume = (extra: i64) -> i64 { move value + extra }; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = &interface.definitions[0];
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "{:#?}",
        flow.diagnostics
    );
}

#[test]
fn contextual_blocks_become_closures_only_under_callable_parameter_expectations() {
    let package = PackageKey("core-contextual@0.1.0".into());
    let source = "pub fn accept(block: () -> i64) -> () { } pub fn main() -> () { accept { 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    assert!(
        core.expressions
            .iter()
            .any(|value| matches!(value.kind, CoreKind::Closure { ref parameters, .. } if parameters.is_empty()))
    );
}

#[test]
fn typed_core_resolves_deep_handler_operations_payloads_and_resumptions() {
    let package = PackageKey("core-handler@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { handle Console::read(41) { Console::read(value) with resume => resume(value) } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let Some(CoreKind::Handle {
        computation,
        clauses,
    }) = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            handler @ CoreKind::Handle { .. } => Some(handler),
            _ => None,
        })
    else {
        panic!("handler syntax did not elaborate into Typed Core")
    };
    assert!(matches!(
        core.expression(*computation).kind,
        CoreKind::Perform {
            terminal: false,
            ..
        }
    ));
    assert_eq!(clauses.len(), 1);
    assert_eq!(
        clauses[0].payload_types,
        vec![grandiose_stage0::Type::Scalar(
            grandiose_stage0::ScalarType::I64
        )]
    );
    assert_eq!(clauses[0].bindings[0].0, "value");
    assert!(matches!(
        clauses[0].resumption,
        CoreHandlerResumption::Explicit { ref name, .. } if name == "resume"
    ));
}

#[test]
fn typed_core_interprets_with_wildcard_as_resumption_discard() {
    let package = PackageKey("core-handler-with-wildcard@0.1.0".into());
    let source = "effect Log { [0, 1] write(value: i64) -> i64; } pub fn main() -> i64 { handle Log::write(1) { Log::write(value) with _ => 0 } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clause = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first(),
            _ => None,
        })
        .expect("handler clause");
    assert!(matches!(
        clause.resumption,
        CoreHandlerResumption::Discard { .. }
    ));
}

#[test]
fn typed_core_rejects_a_continuation_that_shadows_a_payload_binder() {
    let package = PackageKey("core-handler-duplicate-continuation@0.1.0".into());
    let source = "effect Log { [1, 1] write(value: i64) -> i64; } pub fn main() -> i64 { handle Log::write(1) { Log::write(value) with value => value(0) } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(
        body.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4017"),
        "parser accepted duplicate handler binder: {:#?}",
        body.diagnostics
    );
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160"),
        "typed Core accepted duplicate handler binder: {:#?}",
        core.diagnostics
    );
}

#[test]
fn handler_coverage_tracks_direct_operations_but_calls_require_total_protocol_coverage() {
    let package = PackageKey("core-handler-coverage@0.1.0".into());
    let source = "effect Console { read() -> i64; write(value: i64) -> i64; } effect Stop { abort() -> !; } pub fn worker() -> i64 / Console { Console::write(0) } pub fn partial() -> i64 { handle Console::read() { Console::read() => 1 } } pub fn partial_call() -> i64 { handle worker() { Console::read() => 1 } } pub fn terminal() -> i64 { handle Stop::abort() { Stop::abort() with resume => 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let index = DefinitionIndex::from_interface(&interface);

    let partial = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("partial"))
        .unwrap();
    let partial_body = BodySyntax::parse(&lexed, source, partial.body.unwrap());
    let partial_core = TypedBody::elaborate(partial, &partial_body, &index, &signatures);
    assert!(
        partial_core.diagnostics.is_empty(),
        "{:#?}",
        partial_core.diagnostics
    );

    let partial_call = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("partial_call"))
        .unwrap();
    let partial_call_body = BodySyntax::parse(&lexed, source, partial_call.body.unwrap());
    let partial_call_core =
        TypedBody::elaborate(partial_call, &partial_call_body, &index, &signatures);
    assert!(
        partial_call_core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "partial handler unexpectedly discharged a whole-protocol callable: {:#?}",
        partial_call_core.diagnostics
    );

    let terminal = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("terminal"))
        .unwrap();
    let terminal_body = BodySyntax::parse(&lexed, source, terminal.body.unwrap());
    let terminal_core = TypedBody::elaborate(terminal, &terminal_body, &index, &signatures);
    assert!(
        terminal_core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160"),
        "terminal handler accepted a resumption: {:#?}",
        terminal_core.diagnostics
    );
}

#[test]
fn handler_payload_binders_capture_only_when_a_nested_closure_needs_them() {
    let package = PackageKey("core-handler-capture@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { handle Console::read(1) { Console::read(value) => { let delayed = (ignored: i64) -> i64 { value }; 1 } } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let closure = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. } => Some(captures),
            _ => None,
        })
        .expect("handler clause closure was not elaborated");
    assert_eq!(closure.len(), 1);
    assert_eq!(closure[0].name, "value");
}

#[test]
fn handler_resumption_cannot_escape_through_a_nested_closure_capture() {
    let package = PackageKey("core-handler-resumption-escape@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let delayed = (ignored: i64) -> i64 { let saved = k; 0 }; 0 } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4174"),
        "nested closure captured a handler continuation: {:#?}",
        core.diagnostics
    );
    let captures = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. } => Some(captures),
            _ => None,
        })
        .expect("nested closure");
    assert!(
        captures.iter().any(|capture| capture.name == "k"),
        "regression fixture did not capture the handler resumption: {captures:#?}"
    );
}

#[test]
fn handler_resumption_cannot_be_aliased_as_an_ordinary_value() {
    let package = PackageKey("core-handler-resumption-alias@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let saved = k; saved(42) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4175"),
        "resumption alias escaped Typed Core validation: {:#?}",
        core.diagnostics
    );
}

#[test]
fn nested_local_shadowing_does_not_turn_an_ordinary_value_into_a_resumption() {
    let package = PackageKey("core-handler-resumption-shadow@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let shadow = (k: i64) -> i64 { k }; let ignored = shadow(0); k(42) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| matches!(diagnostic.code, "G4174" | "G4175")),
        "a shadowing local was mistaken for the outer resumption: {:#?}",
        core.diagnostics
    );
}

#[test]
fn a_nested_handler_payload_can_shadow_an_outer_resumption_for_capture_analysis() {
    let package = PackageKey("core-handler-resumption-capture-shadow@0.1.0".into());
    let source = "effect Ask { [1, 1] ask() -> i64; } effect Inner { [1, 1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask() with k => { let inside = handle Inner::ask(1) { Inner::ask(k) => { let delayed = (ignored: i64) -> i64 { k }; 0 } }; k(42) } } }";
    let file = FileKey::new(&package, "src/main.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    assert!(body.diagnostics.is_empty(), "{:#?}", body.diagnostics);
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        !core
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4174"),
        "a closure captured the nested payload, not the outer resumption: {:#?}",
        core.diagnostics
    );
    let closure = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. }
                if captures.iter().any(|capture| capture.name == "k") =>
            {
                Some(captures)
            }
            _ => None,
        })
        .expect("nested payload closure");
    assert_eq!(closure[0].name, "k");
}

#[test]
fn handler_payload_binders_do_not_escape_into_the_enclosing_closure() {
    let package = PackageKey("core-handler-scope@0.1.0".into());
    let source = "effect Console { read(value: i64) -> i64; } pub fn main() -> i64 { let delayed = (ignored: i64) -> i64 { handle Console::read(1) { Console::read(value) => value } }; 0 }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let captures = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Closure { captures, .. } => Some(captures),
            _ => None,
        })
        .expect("enclosing closure was not elaborated");
    assert!(
        captures.is_empty(),
        "handler binder escaped its arm: {captures:#?}"
    );
}

#[test]
fn generic_effect_instances_are_resolved_as_distinct_handler_identities() {
    let package = PackageKey("core-handler-generic@0.1.0".into());
    let source = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<i64>::fail(error) => error } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let clause = core
        .expressions
        .iter()
        .find_map(|expression| match &expression.kind {
            CoreKind::Handle { clauses, .. } => clauses.first(),
            _ => None,
        })
        .expect("generic handler did not reach Core");
    assert_eq!(clause.effect.arguments.len(), 1);
    assert!(matches!(
        clause.effect.arguments[0],
        grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64)
    ));
    assert!(clause.terminal);

    let mismatched = "effect Fail<E> { fail(error: E) -> !; } pub fn main() -> i64 { handle Fail<i64>::fail(42) { Fail<Text>::fail(error) => 0 } }";
    let lexed = LexedFile::lex(file, mismatched);
    let scan = DeclarationScan::scan(&lexed, mismatched);
    let interface = InterfaceSet::collect(
        PackageKey("core-handler-generic-mismatch@0.1.0".into()),
        "crate",
        &lexed,
        mismatched,
        &scan,
    )
    .interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, mismatched, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4155"),
        "handler for a distinct generic protocol instance intercepted the operation: {:#?}",
        core.diagnostics
    );
}

#[test]
fn handler_effect_application_arity_is_diagnosed_as_an_operation_arm() {
    let source = "effect State<S> { get() -> S; } pub fn main() -> i64 { handle State<i64>::get() { State<i64, Text>::get() => 0 } }";
    let package = PackageKey("core-handler-effect-arity@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .expect("main definition");
    let body = BodySyntax::parse(&lexed, source, definition.body.expect("main body"));
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(
        core.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4163"),
        "misapplied handler protocol was not diagnosed as an operation arm: {:#?}",
        core.diagnostics
    );
}

#[test]
fn placeflow_joins_handler_arms_conservatively_after_dynamic_selection() {
    let package = PackageKey("core-handler-flow@0.1.0".into());
    let source = "effect Console { read() -> i64; } pub fn main() -> i64 { let value = 7; handle Console::read() { Console::read() => move value, Console::read() => 0 }; value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(
        flow.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5001"),
        "a move in one dynamic handler arm was not propagated: {:#?}",
        flow.diagnostics
    );
}

#[test]
fn exact_one_shot_tail_resumption_lowers_to_a_runtime_handler_frame() {
    let package = PackageKey("core-handler-runtime@0.1.0".into());
    let source = "effect Ask { [1,1] ask(seed: i64) -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(41); value + 1 } { Ask::ask(seed) => seed } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("one-shot tail handler lowers to MIR");
    let instructions = mir
        .blocks
        .iter()
        .flat_map(|block| &block.instructions)
        .collect::<Vec<_>>();
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::InstallHandler { .. }))
    );
    assert!(
        instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::Resume { .. }))
    );
}

#[test]
fn affine_discarded_resumption_lowers_to_a_runtime_handler_cancellation() {
    let package = PackageKey("core-handler-cancel@0.1.0".into());
    let source = "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle { let value = Ask::ask(); value + 1 } { Ask::ask(_) => 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("affine cancellation lowers to MIR");
    assert!(mir.blocks.iter().any(|block| {
        block
            .instructions
            .iter()
            .any(|instruction| matches!(instruction, MirInstruction::Cancel))
    }));
}

#[test]
fn generic_effect_handler_frame_retains_its_nominal_instance_arguments() {
    let package = PackageKey("core-handler-runtime-generic@0.1.0".into());
    let source = "effect State<T> { [1,1] get() -> T; } pub fn main() -> i64 { handle State<i64>::get() { State<i64>::get() => 42 } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let body = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(
        definition,
        &body,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
    let flow = PlaceFlow::analyze(&core);
    let mir = MirLowering::lower(definition.key, &core, &flow)
        .function
        .expect("generic one-shot handler lowers to MIR");
    assert!(mir.blocks.iter().flat_map(|block| &block.instructions).any(
        |instruction| matches!(
            instruction,
            MirInstruction::InstallHandler {
                effect_arguments,
                ..
            } if effect_arguments == &[grandiose_stage0::Type::Scalar(grandiose_stage0::ScalarType::I64)]
        )
    ));
}
