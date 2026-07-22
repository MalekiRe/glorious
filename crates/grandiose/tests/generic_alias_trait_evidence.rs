use grandiose::{compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn identity_generic_alias_impl_head_normalizes_associated_projection() {
    let source = r#"
        trait Value { type Item; }
        trait Accepted {}
        struct Local<T> { value: T }
        type First<X> = Local<X>;
        type Second<Y> = First<Y>;
        impl Accepted for Text {}
        impl<T> Value for Second<T> where T: Accepted { type Item = T; }
        make() -> <Local<Text> as Value>::Item { "projected" }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("alias-trait-evidence.glorious", source).unwrap();
    let repeated = compile_source_to_phases("alias-trait-evidence.glorious", source).unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    let make = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "make")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(phases.artifact).unwrap())
            .run(make, vec![])
            .unwrap(),
        Value::Text("projected".into())
    );
}

#[test]
fn generic_aliases_expand_through_every_projection_type_position() {
    let source = r#"
        trait Family<C> { type Member<T>; }
        struct Wrap<T> { value: T }
        type Alias<T> = Wrap<T>;
        impl<S, C> Family<C> for Wrap<S> { type Member<T> = T; }
        project_alias(
            value: <Alias<i64> as Family<Alias<Text>>>::Member<Alias<u16>>
        ) -> Alias<u16> { value }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("alias-projection-positions.glorious", source)
        .expect("aliases in projection subject and arguments should normalize structurally");
    assert!(
        phases
            .artifact
            .functions
            .iter()
            .any(|function| function.name == "project_alias")
    );
}

#[test]
fn alias_and_nominal_impl_heads_overlap_after_normalization() {
    let source = r#"
        trait Marker {}
        struct Local<T> { value: T }
        type Wrapped<X> = Local<X>;
        impl<T> Marker for Wrapped<T> {}
        impl<T> Marker for Local<T> {}
        main() -> { () }
    "#;
    let diagnostics = compile_source_to_bytecode("alias-overlap.glorious", source)
        .expect_err("alias spelling bypassed coherence");
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic
            .message
            .contains("overlapping implementations of `Marker`")
    }));
}

#[test]
fn non_identity_alias_impl_heads_remain_structured_errors() {
    let cases = [
        "struct Local<T>{value:T} type Fixed<X> = Local<Text>; trait Marker{} impl<T> Marker for Fixed<T>{} main()->{()}",
        "struct Pair<A,B>{left:A,right:B} type Swap<X,Y> = Pair<Y,X>; trait Marker{} impl<A,B> Marker for Swap<A,B>{} main()->{()}",
        "struct Pair<A,B>{left:A,right:B} type Duplicate<X,Y> = Pair<X,X>; trait Marker{} impl<A,B> Marker for Duplicate<A,B>{} main()->{()}",
    ];
    for source in cases {
        let diagnostics = compile_source_to_bytecode("nonidentity-alias-head.glorious", source)
            .expect_err("non-identity alias impl head was accepted");
        assert!(diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1TR001")
                && diagnostic
                    .message
                    .contains("identity-preserving ordered substitution")
                && diagnostic.span.is_some()
        }));
    }
}

#[test]
fn alias_trait_evidence_is_declaration_order_independent() {
    let first = r#"
        trait Value { type Item; }
        struct Local<T> { value: T }
        type Wrapped<X> = Local<X>;
        impl<T> Value for Wrapped<T> { type Item = T; }
        make() -> <Local<Text> as Value>::Item { "stable" }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        make() -> <Local<Text> as Value>::Item { "stable" }
        impl<T> Value for Wrapped<T> { type Item = T; }
        type Wrapped<X> = Local<X>;
        struct Local<T> { value: T }
        trait Value { type Item; }
    "#;
    let first = compile_source_to_phases("alias-order-first.glorious", first).unwrap();
    let reordered = compile_source_to_phases("alias-order-second.glorious", reordered).unwrap();
    assert_eq!(first.artifact.encode(), reordered.artifact.encode());
}
