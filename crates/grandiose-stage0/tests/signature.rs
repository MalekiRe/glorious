use grandiose_stage0::{
    DeclarationScan, EffectTail, ElaboratedHeader, ElaboratedInterface, ElaboratedNominalLayout,
    FileKey, InterfaceSet, LexedFile, LogicalPath, PackageKey, Quantity, ScalarType, Type,
};

#[test]
fn interfaces_elaborate_generic_callable_signatures_without_bodies() {
    let package = PackageKey("signature@0.1.0".into());
    let source = "pub struct Box<T> {} pub fn wrap<T>(value: T) -> Box<T> { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
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
        .find(|definition| definition.name.as_deref() == Some("wrap"))
        .unwrap();
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.parameters, [Type::Generic(0)]);
    assert!(
        matches!(&signature.result, Type::Nominal { arguments, .. } if arguments == &vec![Type::Generic(0)])
    );
    assert_ne!(Type::Scalar(ScalarType::I64), signature.result);
}

#[test]
fn interface_validation_checks_associated_type_names_and_arities() {
    let package = PackageKey("signature-associated-items@0.1.0".into());
    let source = "trait Apply { type Output<T>; type Item; } impl Apply for i64 { type Output = i64; type Extra = Text; }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let codes = signatures
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G4114"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G4115"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G4116"), "{:#?}", signatures.diagnostics);
}

#[test]
fn interfaces_retain_trait_method_signatures_with_trait_and_method_generics() {
    let package = PackageKey("signature-trait-methods@0.1.0".into());
    let source = "trait Map<T> { fn apply<U>(value: T, replacement: U) -> (T, U); }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let trait_key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Map"))
        .unwrap()
        .key;
    let ElaboratedHeader::Trait(trait_header) = signatures.definitions.get(&trait_key).unwrap()
    else {
        panic!("expected trait signature")
    };
    let method = trait_header.methods.get("apply").expect("trait method");
    assert_eq!(method.generics, 1);
    assert_eq!(method.parameters, [Type::Generic(0), Type::Generic(1)]);
    assert_eq!(
        method.result,
        Type::Tuple(vec![Type::Generic(0), Type::Generic(1)])
    );
}

#[test]
fn interfaces_retain_implementation_method_signatures_and_validate_method_sets() {
    let package = PackageKey("signature-impl-methods@0.1.0".into());
    let source = "trait Convert { fn convert<T>(value: T) -> T; } impl Convert for i64 { fn convert<T>(value: T) -> T { value } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.name.is_none())
        .expect("implementation declaration");
    let ElaboratedHeader::Implementation(implementation) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected implementation signature")
    };
    let method = implementation.methods.get("convert").expect("impl method");
    assert_eq!(method.generics, 1);
    assert_eq!(method.parameters, [Type::Generic(0)]);
    assert_eq!(method.result, Type::Generic(0));
}

#[test]
fn implementation_methods_must_match_the_instantiated_trait_contract() {
    let package = PackageKey("signature-impl-method-contract@0.1.0".into());
    let source = r#"
        trait Transform<T> { fn transform<U>(value: T, replacement: U) -> (T, U); }
        impl Transform<i64> for i64 {
            fn transform<U>(value: i64, replacement: U) -> (i64, U) { (value, replacement) }
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface =
        InterfaceSet::collect(package.clone(), "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );

    let mismatched_source = r#"
        trait Convert { fn convert<T>(value: T) -> T; }
        impl Convert for i64 { fn convert<T>(value: T) -> i64 { 0 } }
    "#;
    let file = FileKey::new(&package, "src/mismatch.glorious");
    let lexed = LexedFile::lex(file, mismatched_source);
    let scan = DeclarationScan::scan(&lexed, mismatched_source);
    let interface =
        InterfaceSet::collect(package, "crate", &lexed, mismatched_source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4147"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn transparent_aliases_are_substituted_in_callable_contracts() {
    let package = PackageKey("signature-alias@0.1.0".into());
    let source = "type Count = i64; type Buffer<T> = Array<T>; pub fn count(value: Count) -> Count { ignored } pub fn bytes(value: Buffer<u8>) -> Buffer<u8> { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let callable = |name| {
        let key = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap()
            .key;
        let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&key).unwrap()
        else {
            panic!("expected callable")
        };
        signature
    };
    let count = callable("count");
    assert_eq!(count.parameters, [Type::Scalar(ScalarType::I64)]);
    assert_eq!(count.result, Type::Scalar(ScalarType::I64));
    let bytes = callable("bytes");
    assert_eq!(
        bytes.parameters,
        [Type::Array(Box::new(Type::Scalar(ScalarType::U8)))]
    );
    assert_eq!(
        bytes.result,
        Type::Array(Box::new(Type::Scalar(ScalarType::U8)))
    );
}

#[test]
fn cyclic_transparent_aliases_are_rejected_during_signature_freezing() {
    let package = PackageKey("signature-alias-cycle@0.1.0".into());
    let source = "type A = B; type B = A; pub fn cycle(value: A) -> B { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3307"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn nominal_and_alias_applications_require_their_declared_generic_arity() {
    let package = PackageKey("signature-nominal-arity@0.1.0".into());
    let source = "pub struct Brand<T> {} type Pair<T, U> = (T, U); pub fn bad_one(value: Brand) -> i64 { ignored } pub fn bad_two(value: Brand<i64, Bool>) -> i64 { ignored } pub fn bad_three(value: Pair<i64>) -> i64 { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let arity_errors = signatures
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == "G3305")
        .count();
    assert_eq!(arity_errors, 3, "{:#?}", signatures.diagnostics);
}

#[test]
fn nominal_layout_field_types_are_elaborated_and_alias_normalized() {
    let package = PackageKey("signature-nominal-layout@0.1.0".into());
    let source = "type Count = i64; pub struct Pair<T> { left: T, count: Count }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let pair = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Pair"))
        .unwrap();
    let Some(ElaboratedHeader::Nominal { layout, .. }) = signatures.definitions.get(&pair.key)
    else {
        panic!("expected elaborated nominal layout")
    };
    assert!(matches!(layout, ElaboratedNominalLayout::Struct(fields)
        if fields[0].ty == Type::Generic(0)
        && fields[1].ty == Type::Scalar(ScalarType::I64)));
}

#[test]
fn trait_impl_and_effect_contracts_elaborate_with_stable_declaration_identity() {
    let package = PackageKey("signature-protocols@0.1.0".into());
    let source = r#"
        trait Marker<T> {}
        trait Display<T>: Marker<T> { type Output; render(value: T) -> Text; }
        struct Box<T> { value: T }
        impl<T> Display<T> for Box<T> where T: Marker<T> { type Output = Text; fn render(value: T) -> Text { "rendered" } }
        effect Console<T> { write(value: T); [0, 1] read() -> T; stop() -> !; }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let lookup = |name: &str| {
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap()
            .key
    };
    let ElaboratedHeader::Trait(display) = signatures.definitions.get(&lookup("Display")).unwrap()
    else {
        panic!("expected elaborated trait")
    };
    assert_eq!(display.generics, 1);
    assert_eq!(display.supertraits[0].definition, lookup("Marker"));
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| {
            matches!(
                definition.kind,
                grandiose_stage0::DeclarationKind::Implementation
            )
        })
        .unwrap();
    let ElaboratedHeader::Implementation(value) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected elaborated implementation")
    };
    assert_eq!(value.relation.definition, lookup("Display"));
    assert_eq!(value.where_bounds.len(), 1);
    let ElaboratedHeader::Effect(console) = signatures.definitions.get(&lookup("Console")).unwrap()
    else {
        panic!("expected elaborated effect")
    };
    assert_eq!(console.operations[1].resumption, Quantity::AFFINE);
    assert!(console.operations[2].terminal);
    assert_eq!(console.operations[1].result, Type::Generic(0));
}

#[test]
fn generic_associated_type_projections_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-associated-projection@0.1.0".into());
    let source = "trait Iterator { type Item; } pub fn collect<T>(value: T) -> <T as Iterator>::Item { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let iterator = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Iterator"))
        .unwrap()
        .key;
    let collect = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("collect"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&collect).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } if **subject == Type::Generic(0)
            && *trait_definition == iterator
            && trait_arguments.is_empty()
            && name == "Item"
            && item_arguments.is_empty()
    ));
}

#[test]
fn generic_associated_item_arguments_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<T>; } pub fn project<S, T>(value: S) -> <S as Apply>::Output<T> { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let apply = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Apply"))
        .unwrap()
        .key;
    let project = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("project"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&project).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        } if **subject == Type::Generic(0)
            && *trait_definition == apply
            && trait_arguments.is_empty()
            && name == "Output"
            && item_arguments == &[Type::Generic(1)]
    ));
}

#[test]
fn associated_effect_row_projections_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-associated-effect-row@0.1.0".into());
    let source = "trait Capability { type Effects: EffectRow; } pub fn consume<T>(value: T) -> i64 / { <T as Capability>::Effects } { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let capability = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Capability"))
        .unwrap()
        .key;
    let consume = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("consume"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&consume).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(signature.effects.effects.is_empty());
    assert!(matches!(
        signature.effects.projections.as_slice(),
        [grandiose_stage0::EffectRowProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_arguments,
        }] if **subject == Type::Generic(0)
            && *trait_definition == capability
            && trait_arguments.is_empty()
            && name == "Effects"
            && item_arguments.is_empty()
    ));
}

#[test]
fn kinded_effect_row_binders_preserve_open_row_tails() {
    let package = PackageKey("signature-open-row@0.1.0".into());
    let source = "pub fn relay<e: EffectRow>() -> i64 / { | e } { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
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
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&relay).unwrap() else {
        panic!("expected callable")
    };
    assert_eq!(signature.effects.tail, Some(EffectTail::Generic(0)));
}

#[test]
fn generic_kinds_reject_crossing_type_and_effect_row_positions() {
    let package = PackageKey("signature-generic-kinds@0.1.0".into());
    let source = "pub fn invalid_tail<T>() -> i64 / { | T } { 0 } pub fn invalid_type<e: EffectRow>(value: e) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let codes = signatures
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G3311"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G3313"), "{:#?}", signatures.diagnostics);
}

#[test]
fn effect_row_binders_are_rejected_outside_callable_declarations() {
    let package = PackageKey("signature-effect-row-binder-context@0.1.0".into());
    let source = "struct Invalid<e: EffectRow> {} trait AlsoInvalid<e: EffectRow> {} type Alias<e: EffectRow> = i64;";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3314")
            .count(),
        3,
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn callable_effect_rows_resolve_effect_declaration_identities() {
    let package = PackageKey("signature-effect-row@0.1.0".into());
    let source = "effect Console { write() } effect Trace { note() } pub fn run() -> i64 / { Trace, Console } { 42 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let run = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("run"))
        .unwrap();
    let console = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Console"))
        .unwrap();
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .unwrap();
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&run.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.effects.effects.len(), 2);
    assert!(
        signature
            .effects
            .effects
            .iter()
            .any(|effect| effect.definition == console.key && effect.arguments.is_empty())
    );
    assert!(
        signature
            .effects
            .effects
            .iter()
            .any(|effect| effect.definition == trace.key && effect.arguments.is_empty())
    );
}

#[test]
fn generic_effect_rows_keep_protocol_arguments_in_their_identity() {
    let package = PackageKey("signature-generic-effect-row@0.1.0".into());
    let source = "effect State<T> { get() -> T } pub fn integers() -> i64 / State<i64> { 0 } pub fn text() -> Text / State<Text> { \"\" }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let state = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("State"))
        .unwrap()
        .key;
    let callable = |name| {
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap();
        let ElaboratedHeader::Callable(signature) =
            signatures.definitions.get(&definition.key).unwrap()
        else {
            panic!("expected callable")
        };
        signature
    };
    let integers = callable("integers").effects.effects.iter().next().unwrap();
    let text = callable("text").effects.effects.iter().next().unwrap();
    assert_eq!(integers.definition, state);
    assert_eq!(text.definition, state);
    assert_eq!(integers.arguments, [Type::Scalar(ScalarType::I64)]);
    assert_eq!(text.arguments, [Type::Scalar(ScalarType::Text)]);
    assert_ne!(integers, text);
}

#[test]
fn transparent_aliases_are_normalized_inside_callable_effect_identities() {
    let package = PackageKey("signature-effect-alias@0.1.0".into());
    let source = "type Message = Text; effect Log<T> { write(value: T) } pub fn run() -> i64 / Log<Message> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let run = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("run"))
        .expect("run declaration");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&run.key).unwrap()
    else {
        panic!("expected callable")
    };
    let effect = signature.effects.effects.iter().next().expect("Log effect");
    assert_eq!(effect.arguments, [Type::Scalar(ScalarType::Text)]);
}
