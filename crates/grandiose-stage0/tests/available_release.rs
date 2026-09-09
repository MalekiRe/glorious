use grandiose_stage0::{
    BodySyntax, CoreKind, DeclarationScan, DefinitionIndex, ElaboratedHeader,
    ElaboratedInterface, FileKey, InterfaceSet, LexedFile, PackageKey, PlaceFlow, Type, TypedBody,
};

fn fixture() -> (TypedBody, ElaboratedInterface, grandiose_stage0::CallableSignature) {
    let source = "fn release<'e,E>(available: Available<'e,E>) where E: Environment<'e>, E: Use<[0,1]> { available_to_unit(available) }";
    let package = PackageKey("available-release@0.1.0".into());
    let lexed = LexedFile::lex(FileKey::new(&package, "lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
    let definition = interface.definitions.iter().find(|d| d.name.as_deref() == Some("release")).unwrap();
    let ElaboratedHeader::Callable(contract) = &signatures.definitions[&definition.key] else { panic!(); };
    let contract = contract.clone();
    let syntax = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    let core = TypedBody::elaborate(definition, &syntax, &DefinitionIndex::from_interface(&interface), &signatures);
    assert!(core.diagnostics.is_empty(), "{:?}", core.diagnostics);
    (core, signatures, contract)
}

#[test]
fn frozen_release_retains_exact_lexical_erasure_requirements() {
    let (core, signatures, contract) = fixture();
    assert!(core.validate().is_empty());
    let flow = PlaceFlow::analyze_with_interface_and_bounds(&core, &signatures, &contract.where_bounds);
    assert!(flow.diagnostics.is_empty(), "{:?}", flow.diagnostics);
    for removed in 0..contract.where_bounds.len() {
        let mut detached = contract.where_bounds.clone();
        detached.remove(removed);
        let flow = PlaceFlow::analyze_with_interface_and_bounds(&core, &signatures, &detached);
        assert!(flow.diagnostics.iter().any(|d| d.code == "G4188"), "{:?}", flow.diagnostics);
    }
    // A plain discard is not the same operation, even with lawful bounds.
    let mut discarded = core.clone();
    let release = discarded.expressions.iter().position(|e| matches!(e.kind, CoreKind::ReleaseAvailable(_))).unwrap();
    let CoreKind::ReleaseAvailable(value) = discarded.expressions[release].kind else { unreachable!() };
    let unit = grandiose_stage0::CoreId(discarded.expressions.len() as u32);
    let mut expression = discarded.expressions[release].clone();
    expression.kind = CoreKind::Tuple(vec![]);
    discarded.expressions.push(expression);
    discarded.expressions[release].kind = CoreKind::Block(vec![value, unit]);
    assert_ne!(core.semantic_fingerprint(), discarded.semantic_fingerprint());
    let flow = PlaceFlow::analyze_with_interface_and_bounds(&discarded, &signatures, &contract.where_bounds);
    assert!(flow.diagnostics.iter().any(|d| d.code == "G5024"), "{:?}", flow.diagnostics);
}

#[test]
fn frozen_release_rejects_forged_witness_and_result_types() {
    let (core, _, _) = fixture();
    let release = core.expressions.iter().position(|e| matches!(e.kind, CoreKind::ReleaseAvailable(_))).unwrap();
    let CoreKind::ReleaseAvailable(value) = core.expressions[release].kind else { unreachable!() };
    for index in [release, value.0 as usize] {
        let mut forged = core.clone();
        forged.expressions[index].ty = if index == release { Type::Scalar(grandiose_stage0::ScalarType::I64) } else { Type::Unit };
        assert!(forged.validate().iter().any(|d| d.code == "G4188"));
    }
    let mut forged = core.clone();
    if let Type::Nominal { arguments, .. } = &mut forged.expressions[value.0 as usize].ty {
        arguments[1] = grandiose_stage0::GenericArgument::Type(Type::Unit);
    }
    assert!(forged.validate().iter().any(|d| d.code == "G4183"),
        "an availability occurrence must retain its declared environment identity");
}
