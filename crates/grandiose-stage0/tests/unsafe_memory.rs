//! Raw-memory language contracts, independently of the Rust storage substrate.
//! Executable unsafe and VM/native ABI cases belong here as those layers land.

use std::collections::BTreeMap;

use grandiose_stage0::{
    BodySyntax, CoherenceSet, DeclarationScan, DefinitionIndex, ElaboratedHeader,
    ElaboratedInterface, ElaboratedTraitReference, EscapeFlow, FileKey, GenericArgument,
    InferContext, InterfaceSet, LexedFile, Lifetime, MirLowering, Mutability, PackageInterface,
    PackageKey, PlaceFlow, PointerMutability, Quantity, ScalarType, TraitAnswer, TraitGoal,
    TraitSolver, Type, TypeError, TypedBody, UseFlow,
};

fn pointer(mutability: PointerMutability, pointee: Type) -> Type {
    Type::RawPointer {
        mutability,
        pointee: Box::new(pointee),
    }
}

fn collect(source: &str) -> (LexedFile, PackageInterface, ElaboratedInterface) {
    let package = PackageKey("unsafe-memory@0.1.0".into());
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let collected = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
    assert!(collected.diagnostics.is_empty(), "{collected:#?}");
    let signatures = ElaboratedInterface::elaborate(&collected.interface);
    assert!(signatures.diagnostics.is_empty(), "{signatures:#?}");
    (lexed, collected.interface, signatures)
}

fn elaborate_main(source: &str) -> (TypedBody, ElaboratedInterface) {
    let (lexed, interface, signatures) = collect(source);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("main"))
        .unwrap();
    let syntax = BodySyntax::parse(&lexed, source, definition.body.unwrap());
    assert!(syntax.diagnostics.is_empty(), "{syntax:#?}");
    let core = TypedBody::elaborate(
        definition,
        &syntax,
        &DefinitionIndex::from_interface(&interface),
        &signatures,
    );
    (core, signatures)
}

#[test]
fn raw_pointer_inference_preserves_permission_and_checks_recursive_pointees() {
    let mut inference = InferContext::default();
    let hole = inference.fresh();
    let generic = pointer(PointerMutability::Mut, hole.clone());
    let concrete = pointer(PointerMutability::Mut, Type::Scalar(ScalarType::U8));
    inference.unify(generic.clone(), concrete.clone()).unwrap();
    assert_eq!(inference.zonk(generic).unwrap(), concrete);
    assert_eq!(inference.zonk(hole).unwrap(), Type::Scalar(ScalarType::U8));
    assert!(matches!(
        inference.unify(
            concrete.clone(),
            pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8)),
        ),
        Err(TypeError::Mismatch { .. })
    ));
    assert!(matches!(
        inference.unify(
            concrete,
            Type::Reference {
                mutability: Mutability::Unique,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Scalar(ScalarType::U8)),
            }
        ),
        Err(TypeError::Mismatch { .. })
    ));

    let recursive = inference.fresh();
    assert!(matches!(
        inference.unify(
            recursive.clone(),
            pointer(PointerMutability::Const, recursive),
        ),
        Err(TypeError::Occurs(_, _))
    ));
    let unresolved = inference.fresh();
    assert!(matches!(
        inference.type_fingerprint(pointer(PointerMutability::Mut, unresolved)),
        Err(TypeError::Unresolved(_))
    ));
}

#[test]
fn raw_pointer_fingerprints_keep_pointee_and_permission_identity() {
    let mut inference = InferContext::default();
    let values = [
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8)),
        pointer(PointerMutability::Mut, Type::Scalar(ScalarType::U8)),
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U64)),
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Elided,
            referent: Box::new(Type::Scalar(ScalarType::U8)),
        },
    ];
    let fingerprints = values
        .into_iter()
        .map(|value| inference.type_fingerprint(value).unwrap())
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(fingerprints.len(), 4);
}

#[test]
fn const_pointer_pointees_are_covariant_but_writable_pointees_are_invariant() {
    let (accepted, _) =
        elaborate_main("fn main<'a>(p: *const &'static i64) -> *const &'a i64 { p }");
    assert!(accepted.diagnostics.is_empty(), "{accepted:#?}");
    for source in [
        "fn main<'a>(p: *mut &'static i64) -> *mut &'a i64 { p }",
        "fn main<'a>(p: *const &'a i64) -> *const &'static i64 { p }",
        "fn main<'a>(p: *mut &'a i64) -> *mut &'static i64 { p }",
    ] {
        let (rejected, _) = elaborate_main(source);
        assert!(
            rejected
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5017"),
            "invalid pointer variance accepted: {source}\n{rejected:#?}"
        );
    }
}

#[test]
fn pointee_lifetimes_cannot_escape_higher_ranked_callable_binders() {
    let (valid, _) = elaborate_main(
        "fn main(f: for<'a> (*const &'a i64) -> *const &'a i64, p: *const &'static i64) -> *const &'static i64 { f(p) }",
    );
    assert!(valid.diagnostics.is_empty(), "{valid:#?}");
    let (escaping, _) =
        elaborate_main("fn main(f: for<'a> () -> *const &'a i64) -> i64 { f(); 0 }");
    assert!(
        escaping
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G5019"),
        "raw pointer hid escaping bound lifetime: {escaping:#?}"
    );
}

#[test]
fn raw_pointer_syntax_requires_an_explicit_permission_and_pointee() {
    for source in [
        "fn main(p: *i64) {}",
        "fn main(p: *mut) {}",
        "fn main(p: *const) {}",
    ] {
        let package = PackageKey("invalid-pointer@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan);
        assert!(
            !interface.diagnostics.is_empty(),
            "accepted malformed pointer: {source}"
        );
    }
}

#[test]
fn pointer_aliases_and_specialization_retain_nested_lifetime_and_type_arguments() {
    let (_, interface, signatures) =
        collect("type Ptr<'a, T> = *mut &'a T; fn keep<'a, T>(p: Ptr<'a, T>) -> Ptr<'a, T> { p }");
    let key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("keep"))
        .unwrap()
        .key;
    let instantiated = signatures
        .instantiate_callable_generic(
            key,
            &[
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::Type(Type::Scalar(ScalarType::U64)),
            ],
        )
        .unwrap();
    let expected = pointer(
        PointerMutability::Mut,
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Box::new(Type::Scalar(ScalarType::U64)),
        },
    );
    assert_eq!(instantiated.parameters, [expected.clone()]);
    assert_eq!(instantiated.result, expected);
}

#[test]
fn trait_projections_normalize_inside_raw_pointer_instances() {
    let (_, interface, signatures) = collect(
        "trait Element { type Item; } impl Element for i64 { type Item = u8; } fn keep<T>(p: *const <T as Element>::Item) -> *const <T as Element>::Item where T: Element { p }",
    );
    let key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("keep"))
        .unwrap()
        .key;
    let instantiated = signatures
        .instantiate_callable_generic(key, &[GenericArgument::Type(Type::Scalar(ScalarType::I64))])
        .unwrap();
    let result = TraitSolver::new(&signatures)
        .normalize_type(instantiated.result)
        .unwrap();
    assert_eq!(
        result,
        pointer(PointerMutability::Const, Type::Scalar(ScalarType::U8))
    );
}

#[test]
fn raw_pointer_copies_do_not_copy_or_borrow_the_pointee() {
    for source in [
        "struct Linear {} impl Use<[1,1]> for Linear {} fn main(p: *mut Linear) -> (*mut Linear, *mut Linear) { (p, p) }",
        "fn main<'a>(p: *const &'a mut i64) -> (*const &'a mut i64, *const &'a mut i64) { (p, p) }",
    ] {
        let (core, signatures) = elaborate_main(source);
        assert!(core.diagnostics.is_empty(), "{core:#?}");
        assert!(core.validate().is_empty(), "{:?}", core.validate());
        let flow = PlaceFlow::analyze(&core);
        assert!(flow.diagnostics.is_empty(), "{flow:#?}");
        let uses = UseFlow::analyze_with_interface(&core, &flow, &signatures);
        assert!(uses.diagnostics.is_empty(), "{uses:#?}");
        let escapes = EscapeFlow::analyze(&core, &flow);
        assert!(escapes.diagnostics.is_empty(), "{escapes:#?}");
        for expression in &core.expressions {
            if matches!(expression.ty, Type::RawPointer { .. }) {
                assert_eq!(
                    signatures.principal_use_interval(&expression.ty),
                    Some(Quantity::UNRESTRICTED)
                );
            }
        }
    }
}

#[test]
fn typed_closures_and_mir_preserve_raw_pointer_types() {
    let source =
        "fn main(p: *mut i64) -> *mut i64 { let f = (x: *mut i64) -> *mut i64 { x }; f(p) }";
    let (core, signatures) = elaborate_main(source);
    assert!(core.diagnostics.is_empty(), "{core:#?}");
    let flow = PlaceFlow::analyze(&core);
    assert!(flow.diagnostics.is_empty(), "{flow:#?}");
    let key = signatures
        .definitions
        .iter()
        .find_map(|(key, header)| matches!(header, ElaboratedHeader::Callable(_)).then_some(*key))
        .unwrap();
    let lowered = MirLowering::lower_with_bodies_and_signatures(
        key,
        &core,
        &flow,
        &BTreeMap::new(),
        Some(&signatures),
    );
    assert!(lowered.diagnostics.is_empty(), "{lowered:#?}");
    let function = lowered.function.unwrap();
    assert!(function.validate().is_ok(), "{function:#?}");
    assert_eq!(
        function.result,
        pointer(PointerMutability::Mut, Type::Scalar(ScalarType::I64))
    );
    assert!(
        grandiose_stage0::vm_backend::emit(&function).is_err(),
        "raw pointer was silently represented by an old-format VM value"
    );
}

#[test]
fn raw_pointer_mutability_is_not_a_safe_conversion_or_dereference() {
    for source in [
        "fn main(p: *const i64) -> *mut i64 { p }",
        "fn main(p: *mut i64) -> i64 { *p }",
        "fn main(p: *mut i64) -> &mut i64 { p }",
    ] {
        let (core, _) = elaborate_main(source);
        assert!(
            !core.diagnostics.is_empty(),
            "safe code unexpectedly accepted: {source}"
        );
    }
}

#[test]
fn pointer_indirection_breaks_owned_layout_recursion_without_deriving_auto_traits() {
    let (_, interface, signatures) =
        collect("auto trait Marker {} struct Node { next: *mut Node }");
    let marker = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Marker"))
        .unwrap()
        .key;
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(
        solver.solve(TraitGoal {
            subject: pointer(PointerMutability::Const, Type::Scalar(ScalarType::I64)),
            relation: ElaboratedTraitReference {
                definition: marker,
                arguments: vec![]
            },
        }),
        TraitAnswer::NoSolution
    );
}

#[test]
fn coherence_finds_pointer_head_overlap_and_distinguishes_permissions() {
    for (source, overlaps) in [
        (
            "trait Marker {} impl<T> Marker for *mut T {} impl Marker for *mut i64 {}",
            true,
        ),
        (
            "trait Marker {} impl<T> Marker for *mut T {} impl<T> Marker for *const T {}",
            false,
        ),
        (
            "trait Marker {} impl<'a, T> !Marker for *const &'a T {}",
            false,
        ),
    ] {
        let (_, interface, _) = collect(source);
        let coherence =
            CoherenceSet::collect([&interface], &DefinitionIndex::from_interface(&interface));
        assert_eq!(
            coherence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3404"),
            overlaps,
            "{coherence:#?}"
        );
        assert!(
            !coherence
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3407"),
            "{coherence:#?}"
        );
    }
}
