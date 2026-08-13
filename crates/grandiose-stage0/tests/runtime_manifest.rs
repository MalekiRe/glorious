use grandiose_stage0::{
    DeclarationScan, ElaboratedInterface, FileKey, InterfaceSet, LexedFile, LogicalPath,
    ManifestError, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput,
};

fn interface(package: PackageKey, source: &str) -> grandiose_stage0::PackageInterface {
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface
}

fn manifest(standard_library: PackageKey) -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library,
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::BranchBool,
            module_path: "crate".into(),
            name: "branch_bool".into(),
        }],
    }
}

#[test]
fn primitive_authority_binds_only_the_exact_standard_library_declaration() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { ignored }";
    let standard_interface = interface(standard.clone(), source);
    let signatures = ElaboratedInterface::elaborate(&standard_interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let bound_manifest = manifest(standard.clone())
        .bind(vec![standard_interface.clone()], &signatures)
        .unwrap();
    let bound = bound_manifest.primitives[&PrimitiveRole::BranchBool];
    assert_eq!(bound_manifest.standard_library, standard);
    assert_eq!(
        bound, standard_interface.definitions[0].key,
        "the manifest binds a declaration identity, not its spelling"
    );

    let user = PackageKey("app@0.1.0".into());
    let user_interface = interface(user, source);
    let unchanged = manifest(standard)
        .bind(vec![standard_interface], &signatures)
        .unwrap();
    assert_ne!(bound, user_interface.definitions[0].key);
    assert_eq!(unchanged.primitives[&PrimitiveRole::BranchBool], bound);
}

#[test]
fn primitive_manifest_rejects_signature_mismatch_before_authority_freezes() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub fn branch_bool(condition: Bool) -> Bool { condition }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(matches!(
        manifest(standard).bind(vec![interface], &signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::BranchBool,
            ..
        })
    ));
}
