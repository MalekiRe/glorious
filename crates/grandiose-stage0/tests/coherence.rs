use grandiose_stage0::{
    CoherenceSet, DeclarationScan, DefinitionIndex, FileKey, InterfaceSet, LexedFile, PackageKey,
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
