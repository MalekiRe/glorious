use super::*;

fn projection_fixture(count: usize) -> ElaboratedInterface {
    let mut source = String::from("trait Associated { type Item; } impl Associated for i64 { type Item = i64; }");
    for index in 0..32 {
        source.push_str(&format!("\ntrait Padding{index} {{}} impl Padding{index} for i64 {{}}"));
    }
    for index in 0..count {
        source.push_str(&format!("\nfn projected_{index}(value: <i64 as Associated>::Item) -> <i64 as Associated>::Item;"));
    }
    let package = crate::PackageKey("projection-validation-scaling@0.1.0".into());
    let lexed = crate::LexedFile::lex(crate::FileKey::new(&package, "src/lib.glorious"), &source);
    let scan = crate::DeclarationScan::scan(&lexed, &source);
    let interface = crate::InterfaceSet::collect(package, "crate", &lexed, &source, &scan).interface;
    let index = crate::DefinitionIndex::from_interface(&interface);
    let signatures = ElaboratedInterface::elaborate_with_index(&interface, &index);
    assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
    signatures
}

#[test]
fn projection_validation_reuses_one_immutable_solver_snapshot() {
    let validate = |count| {
        let mut signatures = projection_fixture(count);
        let before = crate::trait_solver::snapshot_builds();
        let start = std::time::Instant::now();
        signatures.validate_projection_obligations();
        let elapsed = start.elapsed();
        let snapshots = crate::trait_solver::snapshot_builds() - before;
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        eprintln!("projection validation: {count} signatures, {snapshots} snapshots, {elapsed:?}");
        snapshots
    };
    let small = validate(2);
    let large = validate(32);
    assert_eq!(large, small, "immutable solver construction must not scale with projection count");
}

#[test]
fn frozen_projection_validation_is_lazy_and_keeps_lexical_evidence_isolated() {
    let mut signatures = projection_fixture(0);
    let associated = signatures.definitions.iter().find_map(|(key, header)| match header {
        ElaboratedHeader::Trait(header) if header.associated_types.contains_key("Item") => Some(*key),
        _ => None,
    }).unwrap();
    let subject = Type::Scalar(crate::ScalarType::I64);
    let relation = ElaboratedTraitReference { definition: associated, arguments: vec![] };
    let projection = Type::Projection {
        subject: Box::new(subject.clone()), trait_definition: associated, trait_arguments: vec![],
        name: "Item".into(), item_generic_kinds: vec![], item_arguments: vec![],
    };
    let before = crate::trait_solver::snapshot_builds();
    assert!(signatures.projection_obligation_diagnostics(&vec![Type::Unit; 8], &[]).is_empty());
    assert_eq!(crate::trait_solver::snapshot_builds() - before, 0);

    let before = crate::trait_solver::snapshot_builds();
    assert!(signatures.projection_obligation_diagnostics(&vec![projection.clone(); 32], &[]).is_empty());
    assert_eq!(crate::trait_solver::snapshot_builds() - before, 1);

    signatures.definitions.retain(|_, header| !matches!(header,
        ElaboratedHeader::Implementation(implementation) if implementation.relation.definition == associated));
    let missing = signatures.projection_obligation_diagnostics(std::slice::from_ref(&projection), &[]);
    assert!(missing.iter().any(|diagnostic| diagnostic.code == "G4190"), "{missing:?}");
    let before = crate::trait_solver::snapshot_builds();
    assert!(signatures.projection_obligation_diagnostics(std::slice::from_ref(&projection), &[(subject, relation)]).is_empty());
    assert_eq!(crate::trait_solver::snapshot_builds() - before, 0);
    assert_eq!(signatures.projection_obligation_diagnostics(&[projection], &[]), missing,
        "lexical proof and an earlier interface snapshot cannot authorize another entry");
}
