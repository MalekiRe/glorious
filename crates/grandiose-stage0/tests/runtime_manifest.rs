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
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::BranchBool,
                module_path: "crate".into(),
                name: "branch_bool".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextByteLen,
                module_path: "crate".into(),
                name: "__g1_text_byte_len".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextConcat,
                module_path: "crate".into(),
                name: "__g1_text_concat".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextEq,
                module_path: "crate".into(),
                name: "__g1_text_eq".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextFromUtf8Checked,
                module_path: "crate".into(),
                name: "__g1_text_from_utf8_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextAsBytes,
                module_path: "crate".into(),
                name: "__g1_text_as_bytes".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharFromU32Checked,
                module_path: "crate".into(),
                name: "__g1_char_from_u32_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharToU32,
                module_path: "crate".into(),
                name: "__g1_char_to_u32".into(),
            },
        ],
    }
}

#[test]
fn primitive_authority_binds_only_the_exact_standard_library_declaration() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { ignored } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }";
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
    let standard_branch = standard_interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("branch_bool"))
        .expect("fixture declares branch_bool")
        .key;
    assert_eq!(bound_manifest.standard_library, standard);
    assert_eq!(
        bound, standard_branch,
        "the manifest binds a declaration identity, not its spelling"
    );

    let user = PackageKey("app@0.1.0".into());
    let user_interface = interface(user, source);
    let unchanged = manifest(standard)
        .bind(vec![standard_interface], &signatures)
        .unwrap();
    assert_ne!(
        bound,
        user_interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("branch_bool"))
            .expect("fixture declares branch_bool")
            .key
    );
    assert_eq!(unchanged.primitives[&PrimitiveRole::BranchBool], bound);
}

#[test]
fn manifest_can_grant_a_strict_runtime_leaf_subset() {
    let standard = PackageKey("std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "fn __g1_text_byte_len(value: Text) -> usize { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    let manifest = RuntimeManifestInput {
        standard_library: standard,
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::TextByteLen,
            module_path: "crate".into(),
            name: "__g1_text_byte_len".into(),
        }],
    }
    .bind(vec![interface], &signatures)
    .expect("a standard-library revision may expose only the leaves it owns");
    assert_eq!(manifest.primitives.len(), 1);
    assert!(
        manifest
            .primitives
            .contains_key(&PrimitiveRole::TextByteLen)
    );
}

#[test]
fn primitive_manifest_rejects_signature_mismatch_before_authority_freezes() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub fn branch_bool(condition: Bool) -> Bool { condition } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
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

#[test]
fn text_byte_len_requires_its_exact_monomorphic_abi() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { ignored } pub fn __g1_text_byte_len(value: Text) -> i64 { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(matches!(
        manifest(standard).bind(vec![interface], &signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::TextByteLen,
            ..
        })
    ));
}
