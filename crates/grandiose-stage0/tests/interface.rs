use grandiose_stage0::{
    DeclarationKind, DeclarationScan, Digest, FileKey, InterfaceSet, LexedFile, LogicalPath,
    PackageKey,
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
fn inherent_member_interfaces_exclude_bodies_and_private_members() {
    let first = collect(
        "pub struct Cell<T> { value: T } impl<T> Cell<T> { pub fn new(value: T) -> Self { first } fn helper() { a } }",
    );
    let body_changed = collect(
        "pub struct Cell<T> { value: T } impl<T> Cell<T> { pub fn new(value: T) -> Self { different_body } fn renamed() { b } }",
    );
    assert!(first.diagnostics.is_empty(), "{:#?}", first.diagnostics);
    assert!(
        body_changed.diagnostics.is_empty(),
        "{:#?}",
        body_changed.diagnostics
    );
    let member = |interface: &InterfaceSet| {
        interface
            .interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("Cell::new"))
            .unwrap()
            .key
    };
    assert_eq!(member(&first), member(&body_changed));
    assert_eq!(
        first.interface.public_fingerprint,
        body_changed.interface.public_fingerprint
    );
    let bounds_changed = collect(
        "pub struct Cell<T> { value: T } impl<T> Cell<T> where T: Allowed { pub fn new(value: T) -> Self { first } }",
    );
    assert_ne!(
        first.interface.public_fingerprint,
        bounds_changed.interface.public_fingerprint
    );
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
fn effect_family_and_operation_bounds_seal_public_contracts() {
    let base = collect("pub effect Gate<T> { gate<U>(U) -> U; }");
    let family = collect("pub effect Gate<T> where T: Mark { gate<U>(U) -> U; }");
    let operation = collect("pub effect Gate<T> { gate<U>(U) -> U where U: Mark; }");
    for changed in [&family, &operation] {
        assert!(changed.diagnostics.is_empty(), "{:?}", changed.diagnostics);
        assert_ne!(base.interface.public_fingerprint, changed.interface.public_fingerprint);
        // Named declaration identity is stable across revisions; its public
        // contract fingerprint, not its DefKey, invalidates old consumers.
        assert_eq!(base.interface.definitions[0].key, changed.interface.definitions[0].key);
    }
    assert_ne!(family.interface.public_fingerprint, operation.interface.public_fingerprint);
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
fn public_fingerprint_seals_effect_rows_inside_exported_callable_aliases() {
    let first = collect(
        "effect Read { read() -> i64; } effect Write { write() -> i64; } pub type Callback = () -> i64 / Read;",
    );
    let changed = collect(
        "effect Read { read() -> i64; } effect Write { write() -> i64; } pub type Callback = () -> i64 / Write;",
    );
    assert_ne!(
        first.interface.public_fingerprint, changed.interface.public_fingerprint,
        "a callable alias's outward authority is part of its public contract"
    );
}

#[test]
fn public_projection_obligations_participate_in_interface_fingerprints() {
    let unconstrained = collect(
        "pub trait Source { type Item; } pub fn project<T>(value: T) -> <T as Source>::Item { ignored }",
    );
    let constrained = collect(
        "pub trait Source { type Item; } pub fn project<T>(value: T) -> <T as Source>::Item where T: Source { ignored }",
    );
    assert_ne!(
        unconstrained.interface.public_fingerprint, constrained.interface.public_fingerprint,
        "adding the evidence that licenses a public associated projection must invalidate dependents"
    );
}

#[test]
fn exported_import_edges_participate_in_frozen_interface_identity() {
    let first = collect("pub use crate::api::answer;");
    let changed = collect("pub use crate::api::other;");
    let private_changed = collect("use crate::api::other;");

    assert_ne!(
        first.interface.public_fingerprint, changed.interface.public_fingerprint,
        "a dependent must be invalidated when an exported alias changes target"
    );
    assert_ne!(
        first.interface.public_fingerprint, private_changed.interface.public_fingerprint,
        "removing exported visibility changes the frozen interface"
    );
}

#[test]
fn equivalent_public_import_tree_order_has_one_canonical_interface_fingerprint() {
    let grouped = collect("pub use crate::api::{answer as result, helper};");
    let reordered = collect("pub use crate::api::helper; pub use crate::api::answer as result;");
    let duplicated = collect(
        "pub use crate::api::answer as result; pub use crate::api::helper; pub use crate::api::helper;",
    );

    assert_eq!(
        grouped.interface.public_fingerprint, reordered.interface.public_fingerprint,
        "source grouping and declaration order are not exported interface facts"
    );
    assert_eq!(
        grouped.interface.public_fingerprint, duplicated.interface.public_fingerprint,
        "duplicate equivalent re-export edges cannot churn dependent invalidation"
    );
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
fn implementation_identity_ignores_method_body_but_tracks_method_contracts() {
    let first = collect(
        "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> i64 { value } }",
    );
    let body_changed = collect(
        "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> i64 { value + 1 } }",
    );
    let contract_changed = collect(
        "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> Text { \"changed\" } }",
    );
    let implementation_key = |interface: &InterfaceSet| {
        interface
            .interface
            .definitions
            .iter()
            .find(|definition| definition.kind == DeclarationKind::Implementation)
            .expect("implementation definition")
            .key
    };
    assert_eq!(
        implementation_key(&first),
        implementation_key(&body_changed)
    );
    assert_ne!(
        implementation_key(&first),
        implementation_key(&contract_changed)
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

#[test]
fn public_evaluated_top_level_let_values_participate_in_interface_fingerprints() {
    let first = collect("pub let answer = add_one(40);");
    let changed = collect("pub let answer = add_one(41);");
    assert_ne!(
        first.interface.public_fingerprint,
        changed.interface.public_fingerprint
    );
}
