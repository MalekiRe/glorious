use grandiose_stage0::{
    DeclarationScan, Digest, FileKey, InterfaceSet, LexedFile, LogicalPath, PackageKey,
};

fn collect(source: &str) -> InterfaceSet {
    let package = PackageKey("interface@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    InterfaceSet::collect(package, "crate", &lexed, source, &scan)
}

#[test]
fn named_definition_identity_and_public_interface_ignore_body_only_edits() {
    let first = collect("pub fn answer() -> i64 { 1 }");
    let second = collect("pub fn answer() -> i64 { 2 }");
    assert!(first.diagnostics.is_empty());
    assert_eq!(
        first.interface.definitions[0].key,
        second.interface.definitions[0].key
    );
    assert_eq!(
        first.interface.public_fingerprint,
        second.interface.public_fingerprint
    );
}

#[test]
fn duplicate_names_in_one_namespace_are_structured_interface_errors() {
    let interface = collect("pub fn answer() { () } fn answer() { () }");
    assert_eq!(interface.diagnostics.len(), 1);
    assert_eq!(interface.diagnostics[0].code, "G3001");
}

#[test]
fn public_fingerprint_changes_for_header_but_not_private_definition_changes() {
    let first = collect("pub fn answer() -> i64 { 1 } fn helper() { () }");
    let private_changed = collect("pub fn answer() -> i64 { 1 } fn other_helper() { () }");
    let public_changed = collect("pub fn answer() -> u64 { 1 } fn helper() { () }");
    assert_eq!(
        first.interface.public_fingerprint,
        private_changed.interface.public_fingerprint
    );
    assert_ne!(
        first.interface.public_fingerprint,
        public_changed.interface.public_fingerprint
    );
    assert_ne!(first.interface.public_fingerprint, Digest::of_bytes(b""));
}

#[test]
fn public_nominal_layout_changes_invalidate_the_exported_interface() {
    let package = PackageKey("interface-nominal-layout@0.1.0".into());
    let first = "pub struct Pair { left: i64, right: i64 }";
    let second = "pub struct Pair { left: i64, right: Bool }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let interface = |source: &str| {
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        InterfaceSet::collect(package.clone(), "crate", &lexed, source, &scan).interface
    };
    assert_ne!(
        interface(first).public_fingerprint,
        interface(second).public_fingerprint
    );
}

#[test]
fn constants_without_initializers_are_rejected_at_the_interface_boundary() {
    let package = PackageKey("interface-const@0.1.0".into());
    let source = "pub const answer: i64;";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
    assert!(
        interface
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3003"),
        "{:#?}",
        interface.diagnostics
    );
}

#[test]
fn public_constant_values_participate_in_interface_fingerprints() {
    let first = collect("pub const answer: i64 = 40;");
    let changed = collect("pub const answer: i64 = 42;");
    assert_ne!(
        first.interface.public_fingerprint,
        changed.interface.public_fingerprint
    );
}
