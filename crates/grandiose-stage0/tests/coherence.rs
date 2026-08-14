use grandiose_stage0::{
    CoherenceSet, DeclarationScan, DefinitionIndex, FileKey, InterfaceSet, LexedFile,
    PackageInterface, PackageKey,
};

fn collect(source: &str) -> CoherenceSet {
    let package = PackageKey("coherence@0.1.0".into());
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let index = DefinitionIndex::from_interface(&interface);
    CoherenceSet::collect([&interface], &index)
}

fn interface(package: &str, module: &str, source: &str) -> PackageInterface {
    let package = PackageKey(package.into());
    let file = FileKey::new(&package, &format!("{module}.glorious"));
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    let collected = InterfaceSet::collect(package, module, &lexed, source, &scan);
    assert!(
        collected.diagnostics.is_empty(),
        "{:#?}",
        collected.diagnostics
    );
    collected.interface
}

fn collect_linked(interfaces: &[PackageInterface]) -> CoherenceSet {
    let index = DefinitionIndex::from_interfaces(interfaces.iter());
    CoherenceSet::collect(interfaces.iter(), &index)
}

#[test]
fn coherence_rejects_unifiable_positive_and_negative_heads() {
    let positive = collect(
        "trait Marker<T> {} struct Box<T> {} impl<T> Marker<T> for Box<T> {} impl Marker<i64> for Box<i64> {}",
    );
    assert!(
        positive
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3404"),
        "{positive:#?}"
    );

    let mixed = collect(
        "trait Marker<T> {} struct Box<T> {} impl<T> Marker<T> for Box<T> {} impl !Marker<i64> for Box<i64> {}",
    );
    assert!(
        mixed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3406"),
        "{mixed:#?}"
    );
}

#[test]
fn coherence_accepts_disjoint_heads_and_rejects_unconstrained_negative_generics() {
    let disjoint = collect(
        "trait Marker {} struct Left {} struct Right {} impl Marker for Left {} impl Marker for Right {}",
    );
    assert!(disjoint.diagnostics.is_empty(), "{disjoint:#?}");

    let unconstrained = collect("trait Marker {} struct Left {} impl<T> !Marker for Left {}");
    assert!(
        unconstrained
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3407"),
        "{unconstrained:#?}"
    );
}

#[test]
fn coherence_counts_lifetime_binders_used_by_negative_impl_heads() {
    let constrained = collect("trait Marker {} impl<'a> !Marker for &'a i64 {}");
    assert!(
        constrained
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G3407"),
        "{constrained:#?}"
    );

    let unconstrained = collect("trait Marker {} impl<'a> !Marker for i64 {}");
    assert!(
        unconstrained
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3407"),
        "{unconstrained:#?}"
    );
}

#[test]
fn coherence_uses_solver_satisfiability_for_where_bound_overlap() {
    let disjoint = collect(
        "trait Left {} trait Right {} trait Render {} impl Left for i64 {} impl Right for Text {} impl<T> Render for T where T: Left {} impl<T> Render for T where T: Right {}",
    );
    assert!(
        disjoint
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G3404"),
        "disjoint bound domains must not overlap: {disjoint:#?}"
    );

    let overlapping = collect(
        "trait Left {} trait Right {} trait Render {} impl<T> Left for T {} impl<T> Right for T {} impl<T> Render for T where T: Left {} impl<T> Render for T where T: Right {}",
    );
    assert!(
        overlapping
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3404"),
        "jointly satisfiable bound domains must overlap: {overlapping:#?}"
    );
}

#[test]
fn coherence_treats_refuted_bounds_as_disjoint_from_positive_heads() {
    let coherence = collect(
        "trait Gate {} trait Render {} impl !Gate for i64 {} impl Render for i64 where i64: Gate {} impl Render for i64 {}",
    );
    assert!(
        coherence
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G3404" && diagnostic.code != "G3406"),
        "a refuted implementation bound cannot create an overlap: {coherence:#?}"
    );
}

#[test]
fn coherence_enforces_package_orphans_but_accepts_either_local_anchor() {
    let provider = interface(
        "provider@0.1.0",
        "crate",
        "pub trait ForeignTrait {} pub struct ForeignType {}",
    );
    let consumer = interface(
        "consumer@0.1.0",
        "crate",
        "use provider::ForeignTrait; use provider::ForeignType; trait LocalTrait {} struct LocalType {} struct OtherLocal {} impl LocalTrait for ForeignType {} impl ForeignTrait for LocalType {} impl !ForeignTrait for OtherLocal {} impl ForeignTrait for ForeignType {}",
    );
    let coherence = collect_linked(&[provider, consumer]);

    assert_eq!(
        coherence
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3407")
            .count(),
        1,
        "only the foreign-trait/foreign-self implementation may cross the orphan boundary: {coherence:#?}"
    );
    assert_eq!(coherence.implementations.len(), 3, "{coherence:#?}");
    assert!(
        coherence.implementations.values().any(|head| head.negative),
        "a constrained negative implementation with a local self type remains a valid coherence fact: {coherence:#?}"
    );
}

#[test]
fn coherence_treats_package_local_nominals_as_valid_anchors_across_modules() {
    let root = interface(
        "app@0.1.0",
        "crate",
        "pub mod model; trait Marker {} impl Marker for model::LocalType {}",
    );
    let model = interface("app@0.1.0", "crate::model", "pub struct LocalType {}");
    let coherence = collect_linked(&[root, model]);
    assert!(coherence.diagnostics.is_empty(), "{coherence:#?}");
    assert_eq!(coherence.implementations.len(), 1, "{coherence:#?}");
}

#[test]
fn negative_impls_obey_the_same_package_orphan_policy() {
    let provider = interface(
        "provider@0.1.0",
        "crate",
        "pub trait ForeignTrait {} pub struct ForeignType {}",
    );
    let consumer = interface(
        "consumer@0.1.0",
        "crate",
        "use provider::ForeignTrait; use provider::ForeignType; impl !ForeignTrait for ForeignType {}",
    );
    let coherence = collect_linked(&[provider, consumer]);
    assert_eq!(coherence.implementations.len(), 0, "{coherence:#?}");
    assert_eq!(coherence.diagnostics.len(), 1, "{coherence:#?}");
    assert_eq!(coherence.diagnostics[0].code, "G3407");
}

#[test]
fn coherence_preserves_dependency_module_visibility_for_trait_and_self_heads() {
    let provider_root = interface("provider@0.1.0", "crate", "pub mod hidden;");
    let provider_hidden = interface(
        "provider@0.1.0",
        "crate::hidden",
        "trait HiddenTrait {} struct HiddenType {}",
    );
    let consumer = interface(
        "consumer@0.1.0",
        "crate",
        "use provider::hidden::HiddenTrait; use provider::hidden::HiddenType; trait LocalTrait {} struct LocalType {} impl HiddenTrait for LocalType {} impl LocalTrait for HiddenType {}",
    );
    let coherence = collect_linked(&[provider_root, provider_hidden, consumer]);

    assert!(
        coherence
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3402"),
        "a dependency-private trait must be rejected during the interface coherence pass: {coherence:#?}"
    );
    assert!(
        coherence
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3409"),
        "a dependency-private self type must not be misdiagnosed as foreign: {coherence:#?}"
    );
    assert!(
        coherence
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G3407"),
        "privacy failures are distinct from the orphan rule: {coherence:#?}"
    );
}

#[test]
fn coherence_reports_linked_package_failures_in_deterministic_order() {
    let provider = interface(
        "provider@0.1.0",
        "crate",
        "pub trait ForeignTrait {} pub struct ForeignType {}",
    );
    let consumer = interface(
        "consumer@0.1.0",
        "crate",
        "use provider::ForeignTrait; use provider::ForeignType; impl ForeignTrait for ForeignType {}",
    );

    let forward = collect_linked(&[provider.clone(), consumer.clone()]);
    let reverse = collect_linked(&[consumer, provider]);
    assert_eq!(forward.diagnostics, reverse.diagnostics);
    assert_eq!(forward.diagnostics.len(), 1, "{forward:#?}");
    assert_eq!(forward.diagnostics[0].code, "G3407");
}
