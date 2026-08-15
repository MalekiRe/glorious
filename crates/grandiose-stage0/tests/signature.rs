use std::collections::BTreeMap;

use grandiose_stage0::{
    CallableSignature, ConstKind, DeclarationScan, DefKey, DefinitionIndex, Digest, EffectRow,
    EffectTail, ElaboratedAssociatedTypeBinding, ElaboratedHeader, ElaboratedImplementation,
    ElaboratedInterface, ElaboratedNominalLayout, ElaboratedTraitReference, FileKey,
    GenericArgument, GenericKind, InstantiationError, InterfaceSet, LexedFile, Lifetime,
    LogicalPath, NominalField, PackageKey, Quantity, ScalarType, StructuralU32Expr, TraitSolver,
    Type, intrinsic_callable_trait_definition, intrinsic_label_trait_definition,
};

#[test]
fn callable_signatures_preserve_const_binder_kinds_and_reject_type_misuse() {
    let package = PackageKey("signature-const-generics@0.1.0".into());
    let source = "pub fn capacity<n: u32, budget: Quantity>() -> i64 { 0 } pub fn invalid<n: u32>(value: n) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("capacity"))
        .expect("capacity definition");
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(
        signature.generic_kinds,
        [
            GenericKind::Const(ConstKind::U32),
            GenericKind::Const(ConstKind::Quantity),
        ]
    );
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3317"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn frozen_public_signatures_retain_symbolic_associated_const_projection_identity() {
    let package = PackageKey("signature-associated-const-projection@0.1.0".into());
    let source = "trait Width { const Value: u32; } pub struct Chosen<n: u32> {} impl Width for i64 { const Value = 7; } pub fn retain<T>(value: Chosen<<T as Width>::Value>) -> Chosen<<T as Width>::Value> where T: Width { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let retain = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("retain"))
        .expect("retain definition");
    let width = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Width"))
        .expect("Width definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&retain.key).unwrap()
    else {
        panic!("expected callable signature")
    };
    let assert_projection = |ty: &Type| {
        assert!(matches!(
            ty,
            Type::Nominal { arguments, .. }
                if matches!(
                    arguments.as_slice(),
                    [GenericArgument::ConstProjection {
                        subject,
                        trait_definition,
                        trait_arguments,
                        name,
                        kind: ConstKind::U32,
                    }]
                    if **subject == Type::Generic(0)
                        && *trait_definition == width.key
                        && trait_arguments.is_empty()
                        && name == "Value"
                )
        ));
    };
    assert_projection(&signature.parameters[0]);
    assert_projection(&signature.result);

    let instantiated = signatures
        .instantiate_callable_generic(
            retain.key,
            &[GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .expect("the type binder accepts i64");
    let normalized = TraitSolver::new(&signatures)
        .normalize_type(instantiated.result)
        .expect("concrete associated const projection normalizes");
    assert!(matches!(
        normalized,
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstU32(7)]
    ));
}

#[test]
fn frozen_callable_signatures_retain_named_associated_item_equalities() {
    let package = PackageKey("signature-named-associated-bindings@0.1.0".into());
    let source = "trait Callable { type Output<T>; type Effects: EffectRow; } pub fn apply<F>() -> i64 where F: Callable<Output<i64> = i64, Effects = {}> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let callable = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("apply"))
        .expect("apply definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&callable.key).unwrap()
    else {
        panic!("expected callable signature")
    };
    assert_eq!(signature.where_associated_type_bindings.len(), 1);
    assert_eq!(signature.where_associated_effect_bindings.len(), 1);
    let output = &signature.where_associated_type_bindings[0];
    assert_eq!(output.name, "Output");
    assert_eq!(output.item_generic_kinds, vec![GenericKind::Type]);
    assert_eq!(
        output.item_arguments,
        vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))]
    );
    assert_eq!(output.value, Type::Scalar(ScalarType::I64));
    assert!(
        signature.where_associated_effect_bindings[0]
            .value
            .effects
            .is_empty()
    );
}

#[test]
fn frozen_interfaces_reject_forged_intrinsic_fn_output_contracts() {
    let intrinsic = intrinsic_callable_trait_definition();
    let callable = Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Scalar(ScalarType::I64)),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let relation = ElaboratedTraitReference {
        definition: intrinsic,
        arguments: vec![GenericArgument::Type(Type::Unit)],
    };
    let mut interface = ElaboratedInterface::default();
    interface.definitions.insert(
        DefKey(Digest::of_bytes(b"forged-intrinsic-fn-signature")),
        ElaboratedHeader::Callable(CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![],
            result: Type::Unit,
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![(callable.clone(), relation.clone())],
            where_associated_type_bindings: vec![ElaboratedAssociatedTypeBinding {
                subject: callable,
                relation,
                name: "Output".into(),
                item_generic_kinds: vec![],
                item_arguments: vec![],
                value: Type::Scalar(ScalarType::Bool),
            }],
            where_associated_effect_bindings: vec![],
        }),
    );
    interface.validate_projection_obligations();
    assert!(
        interface
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4167"),
        "{:#?}",
        interface.diagnostics
    );
}

#[test]
fn unresolved_source_fn_spelling_freezes_the_intrinsic_callable_identity() {
    let package = PackageKey("signature-intrinsic-fn@0.1.0".into());
    let source =
        "pub fn apply<F>(body: F) -> i64 where F: Fn<(), Output = i64, Effects = {}> { body() }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface.definitions.first().expect("apply definition");
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(
        signature.where_bounds[0].1.definition,
        intrinsic_callable_trait_definition()
    );
    assert_eq!(signature.where_associated_type_bindings[0].name, "Output");
    assert_eq!(
        signature.where_associated_effect_bindings[0].name,
        "Effects"
    );
}

#[test]
fn source_trait_named_runs_in_remains_a_source_trait() {
    let package = PackageKey("signature-source-runs-in@0.1.0".into());
    let source = "trait RunsIn {} pub fn apply<T>() -> i64 where T: RunsIn { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let declared_runs_in = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("RunsIn"))
        .expect("source RunsIn trait")
        .key;
    let apply = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("apply"))
        .expect("apply definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&apply.key).unwrap()
    else {
        panic!("expected callable signature")
    };
    assert_eq!(signature.where_bounds[0].1.definition, declared_runs_in);
    assert_ne!(
        signature.where_bounds[0].1.definition,
        grandiose_stage0::intrinsic_runs_in_trait_definition()
    );
}

#[test]
fn frozen_interfaces_reject_forged_intrinsic_runs_in_implementations() {
    let mut interface = ElaboratedInterface::default();
    interface.definitions.insert(
        DefKey(Digest::of_bytes(b"forged-intrinsic-runs-in-implementation")),
        ElaboratedHeader::Implementation(ElaboratedImplementation {
            generics: 0,
            generic_kinds: vec![],
            negative: false,
            relation: ElaboratedTraitReference {
                definition: grandiose_stage0::intrinsic_runs_in_trait_definition(),
                arguments: vec![],
            },
            self_ty: Type::Scalar(ScalarType::I64),
            where_bounds: vec![],
            associated_types: BTreeMap::new(),
            associated_effect_rows: BTreeMap::new(),
            associated_consts: BTreeMap::new(),
            methods: BTreeMap::new(),
        }),
    );
    interface.validate_projection_obligations();
    assert!(
        interface
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4173"),
        "forged intrinsic RunsIn implementation was accepted: {:#?}",
        interface.diagnostics
    );
}

#[test]
fn frozen_interfaces_reject_forged_intrinsic_label_contracts() {
    let intrinsic = intrinsic_label_trait_definition();
    let mut interface = ElaboratedInterface::default();
    interface.definitions.insert(
        DefKey(Digest::of_bytes(b"forged-intrinsic-label-signature")),
        ElaboratedHeader::Callable(CallableSignature {
            generics: 0,
            generic_kinds: vec![],
            parameters: vec![],
            result: Type::Unit,
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
            where_bounds: vec![(
                Type::Callable {
                    lifetime_binders: 0,
                    parameters: vec![Type::Scalar(ScalarType::I64)],
                    result: Box::new(Type::Scalar(ScalarType::I64)),
                    effects: EffectRow::empty(),
                    invocation: Quantity::ONCE,
                },
                ElaboratedTraitReference {
                    definition: intrinsic,
                    arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
                },
            )],
            where_associated_type_bindings: vec![],
            where_associated_effect_bindings: vec![],
        }),
    );
    interface.validate_projection_obligations();
    assert!(
        interface
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4171"),
        "{:#?}",
        interface.diagnostics
    );
}

#[test]
fn generic_instantiation_preserves_all_source_kinds_before_runtime_lowering() {
    let package = PackageKey("signature-generic-instantiation-boundary@0.1.0".into());
    let source = "pub fn typed<T>(value: T) -> T { value } pub fn region<'a>() -> i64 { 0 } pub fn row<e: EffectRow>() -> i64 { 0 } pub fn count<n: u32>() -> i64 { 0 } pub fn quota<q: Quantity>() -> Budget<q> { panic } pub struct Budget<q: Quantity> {} pub struct region_record<'a> {}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let definition = |name: &str| {
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap()
            .key
    };
    assert!(
        signatures
            .instantiate_callable_generic(
                definition("typed"),
                &[GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            )
            .is_ok()
    );
    for (name, argument) in [
        ("region", GenericArgument::Lifetime(Lifetime::Static)),
        ("row", GenericArgument::EffectRow(EffectRow::empty())),
        ("count", GenericArgument::ConstU32(3)),
        (
            "quota",
            GenericArgument::ConstQuantity(Quantity::new(1, Some(2)).unwrap()),
        ),
    ] {
        assert!(
            signatures
                .instantiate_callable_generic(definition(name), std::slice::from_ref(&argument))
                .is_ok(),
            "callable substitution lost source kind for `{name}`"
        );
    }
    let argument = GenericArgument::Lifetime(Lifetime::Static);
    assert!(
        signatures
            .instantiate_struct_fields_generic(
                definition("region_record"),
                std::slice::from_ref(&argument),
            )
            .is_ok(),
        "lifetime-parametric nominal layouts remain semantically meaningful until VM erasure"
    );
}

#[test]
fn signatures_canonicalize_higher_ranked_lifetimes_without_capturing_outer_binders() {
    let package = PackageKey("signature-hrtb@0.1.0".into());
    let source = "pub fn apply<'outer>(callback: for<'inner> (&'inner i64) -> &'inner i64, value: &'outer i64) -> &'outer i64 { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface.definitions.first().expect("apply definition");
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.parameters[0],
        Type::Callable { lifetime_binders: 1, parameters, result, .. }
            if matches!(parameters.as_slice(), [Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. }])
                && matches!(result.as_ref(), Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. })
    ));
    assert!(matches!(
        &signature.parameters[1],
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
}

#[test]
fn nested_higher_ranked_callable_scopes_use_debruijn_depths() {
    let package = PackageKey("signature-nested-hrtb@0.1.0".into());
    let source = "pub fn nested(callback: for<'a> (for<'b> (&'a i64, &'b i64) -> &'a i64) -> ()) { callback }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface.definitions.first().expect("nested definition");
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    let Type::Callable {
        parameters: outer_parameters,
        lifetime_binders: 1,
        ..
    } = &signature.parameters[0]
    else {
        panic!("expected outer HRTB")
    };
    let Type::Callable {
        parameters: inner_parameters,
        result,
        lifetime_binders: 1,
        ..
    } = &outer_parameters[0]
    else {
        panic!("expected nested HRTB")
    };
    assert!(matches!(
        inner_parameters.as_slice(),
        [
            Type::Reference {
                lifetime: Lifetime::Bound { depth: 1, index: 0 },
                ..
            },
            Type::Reference {
                lifetime: Lifetime::Bound { depth: 0, index: 0 },
                ..
            },
        ]
    ));
    assert!(matches!(
        result.as_ref(),
        Type::Reference {
            lifetime: Lifetime::Bound { depth: 1, index: 0 },
            ..
        }
    ));
}

#[test]
fn stacked_higher_ranked_binders_are_alpha_canonical() {
    let package = PackageKey("signature-stacked-hrtb@0.1.0".into());
    let source = "pub fn first(value: for<'a> for<'b> (&'a i64, &'b i64) -> &'a i64) { value } pub fn second(value: for<'x, 'y> (&'x i64, &'y i64) -> &'x i64) { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let parameter = |name: &str| {
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("callable definition");
        let ElaboratedHeader::Callable(signature) =
            signatures.definitions.get(&definition.key).unwrap()
        else {
            panic!("expected callable")
        };
        signature.parameters[0].clone()
    };
    let first = parameter("first");
    let second = parameter("second");
    assert_eq!(first, second);
    assert!(matches!(
        first,
        Type::Callable { lifetime_binders: 2, parameters, result, .. }
            if matches!(parameters.as_slice(), [
                Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. },
                Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 1 }, .. },
            ]) && matches!(result.as_ref(), Type::Reference { lifetime: Lifetime::Bound { depth: 0, index: 0 }, .. })
    ));
}

#[test]
fn declaration_index_retains_const_generic_kinds_for_future_argument_elaboration() {
    let package = PackageKey("signature-indexed-const-generics@0.1.0".into());
    let source = "pub struct Tag<T, n: u32, budget: Quantity> {}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let definition = interface.definitions.first().expect("Tag definition");
    let index = DefinitionIndex::from_interface(&interface);
    assert_eq!(
        index.type_generic_kinds(definition.key),
        Some(
            [
                GenericKind::Type,
                GenericKind::Const(ConstKind::U32),
                GenericKind::Const(ConstKind::Quantity),
            ]
            .as_slice()
        )
    );
}

#[test]
fn nominal_const_applications_preserve_literals_and_binder_identity() {
    let package = PackageKey("signature-const-generic-applications@0.1.0".into());
    let source = "pub struct Tag<n: u32> {} pub type Alias<n: u32> = Tag<n>; pub fn literal() -> Tag<7> { panic } pub fn inherited<n: u32>() -> Tag<n> { panic } pub fn through_alias() -> Alias<9> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let lookup = |name: &str| {
        let key = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("callable definition")
            .key;
        match signatures.definitions.get(&key).expect("signature") {
            ElaboratedHeader::Callable(signature) => signature.result.clone(),
            _ => panic!("expected callable"),
        }
    };
    assert!(matches!(
        lookup("literal"),
        Type::Nominal { arguments, .. } if arguments == vec![GenericArgument::ConstU32(7)]
    ));
    assert!(matches!(
        lookup("inherited"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstGeneric { index: 0, kind: ConstKind::U32 }]
    ));
    assert!(matches!(
        lookup("through_alias"),
        Type::Nominal { arguments, .. } if arguments == vec![GenericArgument::ConstU32(9)]
    ));
}

#[test]
fn nominal_const_applications_normalize_literal_arithmetic() {
    let package = PackageKey("signature-const-generic-arithmetic@0.1.0".into());
    let source = "pub struct Tag<n: u32> {} pub struct Budget<q: Quantity> {} pub fn tag() -> Tag<1 + 2 * 3> { panic } pub fn budget() -> Budget<[2 + 3, 3 * 4]> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let result = |name: &str| {
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("callable definition");
        let ElaboratedHeader::Callable(signature) = signatures
            .definitions
            .get(&definition.key)
            .expect("signature")
        else {
            panic!("expected callable")
        };
        signature.result.clone()
    };
    assert!(matches!(
        result("tag"),
        Type::Nominal { arguments, .. } if arguments == vec![GenericArgument::ConstU32(7)]
    ));
    assert!(matches!(
        result("budget"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstQuantity(Quantity::new(5, Some(12)).unwrap())]
    ));
}

#[test]
fn effect_quantity_arguments_and_resumption_bounds_preserve_kind_and_normal_form() {
    let package = PackageKey("signature-effect-quantity-contract@0.1.0".into());
    let source = "effect Retry<budget: Quantity> { [1 + 1, 3 * 2] retry() -> i64; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let retry = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Retry"))
        .expect("effect definition")
        .key;
    let budget = GenericArgument::ConstQuantity(Quantity::new(2, Some(4)).unwrap());
    let (index, operation) = signatures
        .instantiate_effect_operation_generic(retry, std::slice::from_ref(&budget), &[], "retry")
        .expect("quantity application must satisfy the effect kind contract");
    assert_eq!(index, 0);
    assert_eq!(operation.resumption, Quantity::new(2, Some(6)).unwrap());
    assert!(matches!(
        signatures.instantiate_effect_operation_generic(
            retry,
            &[GenericArgument::ConstU32(2)],
            &[],
            "retry"
        ),
        Err(InstantiationError::WrongKind { .. })
    ));
}

#[test]
fn nominal_quantity_const_applications_preserve_intervals_and_binder_identity() {
    let package = PackageKey("signature-quantity-const-generic-applications@0.1.0".into());
    let source = "pub struct Budget<q: Quantity> {} pub type Alias<q: Quantity> = Budget<q>; pub fn exact() -> Budget<[1, 1]> { panic } pub fn open() -> Budget<[2, *]> { panic } pub fn inherited<q: Quantity>() -> Budget<q> { panic } pub fn through_alias() -> Alias<[0, 1]> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let lookup = |name: &str| {
        let key = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .expect("callable definition")
            .key;
        match signatures.definitions.get(&key).expect("signature") {
            ElaboratedHeader::Callable(signature) => signature.result.clone(),
            _ => panic!("expected callable"),
        }
    };
    assert!(matches!(
        lookup("exact"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstQuantity(Quantity::ONCE)]
    ));
    assert!(matches!(
        lookup("open"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstQuantity(Quantity::new(2, None).unwrap())]
    ));
    assert!(matches!(
        lookup("inherited"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstGeneric { index: 0, kind: ConstKind::Quantity }]
    ));
    assert!(matches!(
        lookup("through_alias"),
        Type::Nominal { arguments, .. }
            if arguments == vec![GenericArgument::ConstQuantity(Quantity::AFFINE)]
    ));
}

#[test]
fn nominal_quantity_const_applications_reject_wrong_slot_kinds() {
    let package = PackageKey("signature-quantity-const-generic-slot-kinds@0.1.0".into());
    let source = "pub struct Budget<q: Quantity> {} pub struct Box<T> {} pub fn u32_in_quantity() -> Budget<7> { panic } pub fn quantity_in_type() -> Box<[0, 1]> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3318")
            .count(),
        2,
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn nominal_headers_preserve_mixed_kind_argument_identity() {
    let package = PackageKey("signature-mixed-nominal@0.1.0".into());
    let source = "effect Trace { note(); } pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} pub fn value() -> Mixed<'static, {Trace}, 7, [1, 2], i64> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let ElaboratedHeader::Callable(signature) = signatures
        .definitions
        .get(&definition.key)
        .expect("value signature")
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Nominal { arguments, .. }
            if matches!(arguments.as_slice(), [
                GenericArgument::Lifetime(Lifetime::Static),
                GenericArgument::EffectRow(row),
                GenericArgument::ConstU32(7),
                GenericArgument::ConstQuantity(quantity),
                GenericArgument::Type(Type::Scalar(ScalarType::I64)),
            ] if row.effects.len() == 1 && row.tail.is_none()
                && *quantity == Quantity::new(1, Some(2)).unwrap())
    ));
}

#[test]
fn generic_aliases_substitute_every_nominal_argument_kind() {
    let package = PackageKey("signature-mixed-nominal-alias@0.1.0".into());
    let source = "effect Trace { note(); } pub struct Mixed<'a, e: EffectRow, n: u32, q: Quantity, T> {} pub type Alias<'a, e: EffectRow, n: u32, q: Quantity, T> = Mixed<'a, e, n, q, T>; pub fn value<'a, e: EffectRow, n: u32, q: Quantity, T>() -> Alias<'a, e, n, q, T> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("value"))
        .expect("value definition");
    let ElaboratedHeader::Callable(signature) = signatures
        .definitions
        .get(&definition.key)
        .expect("value signature")
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Nominal { arguments, .. }
            if matches!(arguments.as_slice(), [
                GenericArgument::Lifetime(Lifetime::Generic(0)),
                GenericArgument::EffectRow(row),
                GenericArgument::ConstGeneric { index: 2, kind: ConstKind::U32 },
                GenericArgument::ConstGeneric { index: 3, kind: ConstKind::Quantity },
                GenericArgument::Type(Type::Generic(4)),
            ] if row.tail == Some(EffectTail::Generic(1)))
    ));
}

#[test]
fn nominal_const_applications_reject_wrong_slot_kinds() {
    let package = PackageKey("signature-const-generic-slot-kinds@0.1.0".into());
    let source = "pub struct Tag<n: u32> {} pub struct Box<T> {} pub fn type_in_const() -> Tag<i64> { panic } pub fn const_in_type() -> Box<7> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3318")
            .count(),
        2,
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn trait_references_elaborate_structural_const_arguments_by_declared_kind() {
    let package = PackageKey("signature-trait-const-generic-arguments@0.1.0".into());
    let source = "pub trait Capacity<n: u32> {} pub trait Marker<T> {} pub struct Tag<n: u32> {} pub impl<n: u32> Capacity<n> for Tag<n> {} pub fn inherited<n: u32>() where Tag<n>: Capacity<n> {} pub fn literal() where Tag<7>: Capacity<7> {} pub fn wrong<T>() where T: Marker<7> {}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let inherited = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("inherited"))
        .expect("inherited definition");
    let ElaboratedHeader::Callable(signature) = signatures
        .definitions
        .get(&inherited.key)
        .expect("inherited signature")
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        signature.where_bounds[0].1.arguments.as_slice(),
        [GenericArgument::ConstGeneric {
            index: 0,
            kind: ConstKind::U32
        }]
    ));
    let literal = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("literal"))
        .expect("literal definition");
    let ElaboratedHeader::Callable(signature) = signatures
        .definitions
        .get(&literal.key)
        .expect("literal signature")
    else {
        panic!("expected callable")
    };
    assert_eq!(
        signature.where_bounds[0].1.arguments,
        vec![GenericArgument::ConstU32(7)]
    );
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3318")
            .count(),
        1,
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn associated_type_projections_preserve_structural_const_item_arguments() {
    let package = PackageKey("signature-associated-const-projection@0.1.0".into());
    let source = "pub trait Family { type Out<n: u32>; } pub struct Tag {} pub impl Family for Tag { type Out<n: u32> = i64; } pub type Pick = <Tag as Family>::Out<7>;";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let pick = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Pick"))
        .expect("Pick alias");
    let ElaboratedHeader::Alias { target, .. } = signatures
        .definitions
        .get(&pick.key)
        .expect("Pick signature")
    else {
        panic!("expected alias")
    };
    assert!(matches!(
        target,
        Type::Projection { item_arguments, .. }
            if item_arguments == &vec![GenericArgument::ConstU32(7)]
    ));
}

#[test]
fn interfaces_preserve_declared_reference_lifetimes_without_type_slots() {
    let package = PackageKey("signature-reference-lifetimes@0.1.0".into());
    let source = "pub fn borrow<'a>(value: &'a i64, fallback: &i64) -> &'static i64 { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface.definitions.first().expect("borrow definition");
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.generics, 1);
    assert!(matches!(
        signature.parameters[0],
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
    assert!(matches!(
        signature.parameters[1],
        Type::Reference {
            lifetime: Lifetime::Elided,
            ..
        }
    ));
    assert!(matches!(
        signature.result,
        Type::Reference {
            lifetime: Lifetime::Static,
            ..
        }
    ));
}

#[test]
fn trait_and_implementation_lifetime_binders_are_frozen_with_their_kinds() {
    let package = PackageKey("signature-trait-implementation-lifetimes@0.1.0".into());
    let source = r#"
        trait View<'a> {
            fn view(value: &'a i64) -> &'a i64;
        }
        trait Marker {}
        impl<'a> Marker for &'a i64 {}
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );

    let view = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("View"))
        .expect("View definition");
    let ElaboratedHeader::Trait(view) = signatures.definitions.get(&view.key).unwrap() else {
        panic!("expected trait signature")
    };
    assert_eq!(view.generics, 1);
    assert_eq!(view.generic_kinds, [GenericKind::Lifetime]);
    let method = view.methods.get("view").expect("view method");
    assert!(matches!(
        method.parameters.as_slice(),
        [Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }]
    ));
    assert!(matches!(
        method.result,
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));

    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.name.is_none())
        .expect("implementation declaration");
    let ElaboratedHeader::Implementation(implementation) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected implementation signature")
    };
    assert_eq!(implementation.generics, 1);
    assert_eq!(implementation.generic_kinds, [GenericKind::Lifetime]);
    assert!(matches!(
        implementation.self_ty,
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
}

#[test]
fn trait_and_effect_references_elaborate_explicit_lifetime_arguments() {
    let package = PackageKey("signature-lifetime-generic-arguments@0.1.0".into());
    let source = r#"
        trait Marker<'a> {}
        effect Trace<'a> { emit() -> i64 }
        pub fn relay<'a, T>() -> i64 / Trace<'a> where T: Marker<'a> { 0 }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&relay.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(
        signature.where_bounds[0].1.arguments,
        vec![GenericArgument::Lifetime(Lifetime::Generic(0))]
    );
    let effect = signature
        .effects
        .effects
        .iter()
        .next()
        .expect("Trace effect");
    assert_eq!(
        effect.arguments,
        vec![GenericArgument::Lifetime(Lifetime::Generic(0))]
    );
}

#[test]
fn trait_and_effect_references_elaborate_explicit_effect_row_arguments() {
    let package = PackageKey("signature-effect-row-generic-arguments@0.1.0".into());
    let source = r#"
        trait Capability<e: EffectRow> {}
        effect Trace { note() }
        effect Relay<e: EffectRow> { emit() -> i64 }
        pub fn dispatch<e: EffectRow, T>() -> i64 / Relay<{ Trace, | e }>
            where T: Capability<{ Trace, | e }> { 0 }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let dispatch = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("dispatch"))
        .expect("dispatch definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&dispatch.key).unwrap()
    else {
        panic!("expected callable")
    };
    let expected = EffectRow {
        effects: [grandiose_stage0::EffectInstance {
            definition: interface
                .definitions
                .iter()
                .find(|definition| definition.name.as_deref() == Some("Trace"))
                .expect("Trace definition")
                .key,
            arguments: vec![],
        }]
        .into_iter()
        .collect(),
        projections: vec![],
        tail: Some(EffectTail::Generic(0)),
    };
    assert_eq!(
        signature.where_bounds[0].1.arguments,
        vec![GenericArgument::EffectRow(expected.clone())]
    );
    let effect = signature
        .effects
        .effects
        .iter()
        .next()
        .expect("Relay effect");
    assert_eq!(effect.arguments, vec![GenericArgument::EffectRow(expected)]);
}

#[test]
fn interfaces_reject_unbound_or_type_position_lifetimes() {
    let package = PackageKey("signature-invalid-lifetimes@0.1.0".into());
    let source =
        "pub fn missing(value: &'a i64) -> i64 { 0 } pub fn misuse<'a>(value: 'a) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let codes = signatures
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G3315"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G3316"), "{:#?}", signatures.diagnostics);
}

#[test]
fn aliases_can_bind_a_lifetime_without_turning_it_into_a_type_argument() {
    let package = PackageKey("signature-alias-lifetime@0.1.0".into());
    let source = "type Ref<'a> = &'a i64;";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface.definitions.first().expect("Ref definition");
    let ElaboratedHeader::Alias { generics, target } =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected alias")
    };
    assert_eq!(*generics, 1);
    assert!(matches!(
        target,
        Type::Reference {
            lifetime: Lifetime::Generic(0),
            ..
        }
    ));
}

#[test]
fn interfaces_elaborate_generic_callable_signatures_without_bodies() {
    let package = PackageKey("signature@0.1.0".into());
    let source = "pub struct Box<T> {} pub fn wrap<T>(value: T) -> Box<T> { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("wrap"))
        .unwrap();
    let ElaboratedHeader::Callable(signature) =
        signatures.definitions.get(&definition.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.parameters, [Type::Generic(0)]);
    assert!(
        matches!(&signature.result, Type::Nominal { arguments, .. } if arguments == &vec![GenericArgument::Type(Type::Generic(0))])
    );
    assert_ne!(Type::Scalar(ScalarType::I64), signature.result);
}

#[test]
fn interface_validation_checks_associated_type_names_and_arities() {
    let package = PackageKey("signature-associated-items@0.1.0".into());
    let source = "trait Apply { type Output<T>; type Item; } impl Apply for i64 { type Output = i64; type Extra = Text; }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let codes = signatures
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G4114"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G4115"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G4116"), "{:#?}", signatures.diagnostics);
}

#[test]
fn interfaces_retain_trait_method_signatures_with_trait_and_method_generics() {
    let package = PackageKey("signature-trait-methods@0.1.0".into());
    let source = "trait Map<T> { fn apply<U>(value: T, replacement: U) -> (T, U); }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let trait_key = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Map"))
        .unwrap()
        .key;
    let ElaboratedHeader::Trait(trait_header) = signatures.definitions.get(&trait_key).unwrap()
    else {
        panic!("expected trait signature")
    };
    let method = trait_header.methods.get("apply").expect("trait method");
    assert_eq!(method.generics, 1);
    assert_eq!(method.parameters, [Type::Generic(0), Type::Generic(1)]);
    assert_eq!(
        method.result,
        Type::Tuple(vec![Type::Generic(0), Type::Generic(1)])
    );
}

#[test]
fn interfaces_retain_implementation_method_signatures_and_validate_method_sets() {
    let package = PackageKey("signature-impl-methods@0.1.0".into());
    let source = "trait Convert { fn convert<T>(value: T) -> T; } impl Convert for i64 { fn convert<T>(value: T) -> T { value } }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.name.is_none())
        .expect("implementation declaration");
    let ElaboratedHeader::Implementation(implementation) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected implementation signature")
    };
    let method = implementation.methods.get("convert").expect("impl method");
    assert_eq!(method.generics, 1);
    assert_eq!(method.parameters, [Type::Generic(0)]);
    assert_eq!(method.result, Type::Generic(0));
}

#[test]
fn implementation_trait_methods_rebase_lifetime_binders_after_impl_generics() {
    let package = PackageKey("signature-trait-method-lifetime-rebase@0.1.0".into());
    let source = r#"
        struct Box<T> {}
        trait Inspect {
            fn inspect<'a, U>(value: &'a U) -> &'a U;
        }
        impl<T> Inspect for Box<T> {
            fn inspect<'b, V>(value: &'b V) -> &'b V { value }
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .all(|diagnostic| diagnostic.code != "G4147"),
        "{:#?}",
        signatures.diagnostics
    );
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.name.is_none())
        .expect("implementation declaration");
    let ElaboratedHeader::Implementation(implementation) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected implementation signature")
    };
    let method = implementation
        .methods
        .get("inspect")
        .expect("inspect method");
    assert!(matches!(
        method.parameters.as_slice(),
        [Type::Reference {
            lifetime: Lifetime::Generic(1),
            referent,
            ..
        }] if **referent == Type::Generic(2)
    ));
}

#[test]
fn implementation_methods_cannot_substitute_a_type_binder_for_a_lifetime_binder() {
    let package = PackageKey("signature-trait-method-lifetime-kind@0.1.0".into());
    let source = r#"
        trait Marker {
            fn mark<'a>() -> i64;
        }
        impl Marker for i64 {
            fn mark<T>() -> i64 { 0 }
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);

    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4119"
                && diagnostic.message.contains("<type>")
                && diagnostic.message.contains("<lifetime>")
        }),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn implementation_methods_must_match_the_instantiated_trait_contract() {
    let package = PackageKey("signature-impl-method-contract@0.1.0".into());
    let source = r#"
        trait Transform<T> { fn transform<U>(value: T, replacement: U) -> (T, U); }
        impl Transform<i64> for i64 {
            fn transform<U>(value: i64, replacement: U) -> (i64, U) { (value, replacement) }
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface =
        InterfaceSet::collect(package.clone(), "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );

    let mismatched_source = r#"
        trait Convert { fn convert<T>(value: T) -> T; }
        impl Convert for i64 { fn convert<T>(value: T) -> i64 { 0 } }
    "#;
    let file = FileKey::new(&package, "src/mismatch.glorious");
    let lexed = LexedFile::lex(file, mismatched_source);
    let scan = DeclarationScan::scan(&lexed, mismatched_source);
    let interface =
        InterfaceSet::collect(package, "crate", &lexed, mismatched_source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4147"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn transparent_aliases_are_substituted_in_callable_contracts() {
    let package = PackageKey("signature-alias@0.1.0".into());
    let source = "type Count = i64; type Buffer<T> = Array<T>; pub fn count(value: Count) -> Count { ignored } pub fn bytes(value: Buffer<u8>) -> Buffer<u8> { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let callable = |name| {
        let key = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap()
            .key;
        let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&key).unwrap()
        else {
            panic!("expected callable")
        };
        signature
    };
    let count = callable("count");
    assert_eq!(count.parameters, [Type::Scalar(ScalarType::I64)]);
    assert_eq!(count.result, Type::Scalar(ScalarType::I64));
    let bytes = callable("bytes");
    assert_eq!(
        bytes.parameters,
        [Type::Array(Box::new(Type::Scalar(ScalarType::U8)))]
    );
    assert_eq!(
        bytes.result,
        Type::Array(Box::new(Type::Scalar(ScalarType::U8)))
    );
}

#[test]
fn cyclic_transparent_aliases_are_rejected_during_signature_freezing() {
    let package = PackageKey("signature-alias-cycle@0.1.0".into());
    let source = "type A = B; type B = A; pub fn cycle(value: A) -> B { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3307"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn aliases_normalize_delayed_effect_projection_arguments_before_freezing_identity() {
    let package = PackageKey("signature-alias-delayed-effect-projection@0.1.0".into());
    let source = "type Count = i64; trait Capability<T> { type Effects: EffectRow; } struct Value {} impl Capability<i64> for Value { type Effects = {}; } struct Carrier<e: EffectRow> {} type Wrapped<e: EffectRow> = Carrier<e>; pub fn worker(value: Wrapped<{ <Value as Capability<Count>>::Effects }>) -> i64 { 0 } pub fn direct(value: Carrier<{ <Value as Capability<i64>>::Effects }>) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let worker = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("worker"))
        .expect("worker declaration");
    let ElaboratedHeader::Callable(signature) = signatures
        .definitions
        .get(&worker.key)
        .expect("worker signature")
    else {
        panic!("expected callable")
    };
    let Type::Nominal { arguments, .. } = &signature.parameters[0] else {
        panic!("transparent alias did not normalize to its carrier")
    };
    let [GenericArgument::EffectRow(row)] = arguments.as_slice() else {
        panic!("carrier did not retain its effect-row application")
    };
    let [projection] = row.projections.as_slice() else {
        panic!("delayed associated effect projection was lost")
    };
    assert_eq!(
        projection.trait_arguments,
        vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        "the alias-spelled trait argument must freeze as the canonical scalar identity"
    );
    let direct = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("direct"))
        .expect("direct declaration");
    let ElaboratedHeader::Callable(direct) = signatures
        .definitions
        .get(&direct.key)
        .expect("direct signature")
    else {
        panic!("expected callable")
    };
    assert_eq!(
        signature.parameters, direct.parameters,
        "alias-spelled and direct delayed-effect applications must share one frozen identity"
    );
}

#[test]
fn alias_cycles_reached_through_delayed_effect_projections_fail_closed() {
    let package = PackageKey("signature-alias-delayed-effect-cycle@0.1.0".into());
    let source = "trait Capability { type Effects: EffectRow; } struct Carrier<e: EffectRow> {} type First = Second; type Second = First; type Wrapped = Carrier<{ <First as Capability>::Effects }>; pub fn worker(value: Wrapped) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3307"),
        "a delayed associated-effect projection hid an alias cycle: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn nominal_and_alias_applications_require_their_declared_generic_arity() {
    let package = PackageKey("signature-nominal-arity@0.1.0".into());
    let source = "pub struct Brand<T> {} type Pair<T, U> = (T, U); pub fn bad_one(value: Brand) -> i64 { ignored } pub fn bad_two(value: Brand<i64, Bool>) -> i64 { ignored } pub fn bad_three(value: Pair<i64>) -> i64 { ignored }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let arity_errors = signatures
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == "G3305")
        .count();
    assert_eq!(arity_errors, 3, "{:#?}", signatures.diagnostics);
}

#[test]
fn polymorphic_enum_constructor_value_aliases_do_not_require_spurious_type_arguments() {
    let package = PackageKey("signature-polymorphic-constructor-alias@0.1.0".into());
    let source = "pub enum Result<T, E> { Ok(T), Err(E) } type Option<T> = Result<T, ()>; let Option::Some = Result::Ok; let None = Result::Err(()); pub fn references<'a, T, E>(value: Option<&'a T>) -> Result<!, E> { () }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        !signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3305"),
        "polymorphic constructor aliases were treated as missing nominal applications: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn nominal_layout_field_types_are_elaborated_and_alias_normalized() {
    let package = PackageKey("signature-nominal-layout@0.1.0".into());
    let source = "type Count = i64; pub struct Pair<T> { left: T, count: Count }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let pair = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Pair"))
        .unwrap();
    let Some(ElaboratedHeader::Nominal { layout, .. }) = signatures.definitions.get(&pair.key)
    else {
        panic!("expected elaborated nominal layout")
    };
    assert!(matches!(layout, ElaboratedNominalLayout::Struct(fields)
        if fields[0].ty == Type::Generic(0)
        && fields[1].ty == Type::Scalar(ScalarType::I64)));
}

#[test]
fn trait_impl_and_effect_contracts_elaborate_with_stable_declaration_identity() {
    let package = PackageKey("signature-protocols@0.1.0".into());
    let source = r#"
        trait Marker<T> {}
        trait Display<T>: Marker<T> { type Output; render(value: T) -> Text; }
        struct Box<T> { value: T }
        impl<T> Marker<T> for Box<T> {}
        impl<T> Display<T> for Box<T> where T: Marker<T> { type Output = Text; fn render(value: T) -> Text { "rendered" } }
        effect Console<T> { write(value: T); [0, 1] read() -> T; stop() -> !; }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let lookup = |name: &str| {
        interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap()
            .key
    };
    let ElaboratedHeader::Trait(display) = signatures.definitions.get(&lookup("Display")).unwrap()
    else {
        panic!("expected elaborated trait")
    };
    assert_eq!(display.generics, 1);
    assert_eq!(display.supertraits[0].definition, lookup("Marker"));
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| {
            matches!(
                definition.kind,
                grandiose_stage0::DeclarationKind::Implementation
            )
        })
        .unwrap();
    let ElaboratedHeader::Implementation(value) =
        signatures.definitions.get(&implementation.key).unwrap()
    else {
        panic!("expected elaborated implementation")
    };
    assert_eq!(value.relation.definition, lookup("Display"));
    assert_eq!(value.where_bounds.len(), 1);
    let ElaboratedHeader::Effect(console) = signatures.definitions.get(&lookup("Console")).unwrap()
    else {
        panic!("expected elaborated effect")
    };
    assert_eq!(console.operations[1].resumption, Quantity::AFFINE);
    assert!(console.operations[2].terminal);
    assert_eq!(console.operations[1].result, Type::Generic(0));
}

#[test]
fn positive_implementations_must_prove_instantiated_supertraits() {
    let package = PackageKey("signature-supertrait-obligations@0.1.0".into());
    let source = r#"
        trait Parent<T> {}
        trait Child<T>: Parent<T> {}
        struct Box<T> {}
        impl<T> Parent<T> for Box<T> {}
        impl<T> Child<T> for Box<T> {}
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn generic_subtrait_implementations_use_where_evidence_for_supertrait_implication() {
    // The parent candidate itself has a generic where-obligation. The child
    // implementation must be checked in the lexical `T: Gate` environment,
    // rather than as a global query for the unconstrained type parameter.
    let package = PackageKey("signature-generic-supertrait-where@0.1.0".into());
    let source = r#"
        trait Gate {}
        trait Parent {}
        trait Child: Parent {}
        struct Box<T> {}
        impl<T> Parent for Box<T> where T: Gate {}
        impl<T> Child for Box<T> where T: Gate {}
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn generic_subtrait_implementations_do_not_override_negative_parent_evidence() {
    let package = PackageKey("signature-generic-negative-supertrait@0.1.0".into());
    let source = r#"
        trait Gate {}
        trait Parent {}
        trait Child: Parent {}
        struct Box<T> {}
        impl<T> !Parent for Box<T> where T: Gate {}
        impl<T> Child for Box<T> where T: Gate {}
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4148" && diagnostic.message.contains("refuted")
        }),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn positive_implementations_reject_missing_or_negative_supertrait_evidence() {
    let package = PackageKey("signature-missing-supertrait@0.1.0".into());
    let source = r#"
        trait Parent<T> {}
        trait Child<T>: Parent<T> {}
        struct Box<T> {}
        impl<T> !Parent<T> for Box<T> {}
        impl<T> Child<T> for Box<T> {}
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4148" && diagnostic.message.contains("refuted")),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn negative_implementations_cannot_define_callable_or_associated_item_evidence() {
    let package = PackageKey("signature-negative-impl-items@0.1.0".into());
    let source = r#"
        trait Marker {
            type Item;
            type Trace: EffectRow;
            fn inspect(value: i64) -> i64;
        }
        impl !Marker for i64 {
            type Item = Text;
            type Trace = { Console };
            fn inspect(value: i64) -> i64 { value }
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4149"
                && diagnostic.message.contains("associated type `Item`")
                && diagnostic.message.contains("associated effect row `Trace`")
                && diagnostic.message.contains("method `inspect`")
        }),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn generic_associated_type_projections_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-associated-projection@0.1.0".into());
    let source = "trait Iterator { type Item; } pub fn collect<T>(value: T) -> <T as Iterator>::Item where T: Iterator { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let iterator = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Iterator"))
        .unwrap()
        .key;
    let collect = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("collect"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&collect).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } if **subject == Type::Generic(0)
            && *trait_definition == iterator
            && trait_arguments.is_empty()
            && name == "Item"
            && item_generic_kinds.is_empty()
            && item_arguments.is_empty()
    ));
}

#[test]
fn symbolic_associated_projections_require_explicit_or_inherited_trait_evidence() {
    let package = PackageKey("signature-projection-obligation@0.1.0".into());
    let source = r#"
        trait Parent { type Item; }
        trait Child: Parent {}
        pub fn inherited<T>(value: T) -> <T as Parent>::Item where T: Child { ignored }
        pub fn missing<T>(value: T) -> <T as Parent>::Item { ignored }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4190"
                && diagnostic
                    .message
                    .contains("associated type projection `Item`")
        }),
        "{:#?}",
        signatures.diagnostics
    );
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G4190")
            .count(),
        1,
        "the inherited Parent obligation must prove the other projection: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn type_effect_and_const_projection_contracts_share_the_same_required_evidence() {
    let package = PackageKey("signature-all-projection-obligations@0.1.0".into());
    let source = r#"
        trait Family {
            type Item;
            type Effects: EffectRow;
            const Width: u32;
        }
        pub struct Sized<n: u32> {}
        pub fn missing<T>(value: Sized<<T as Family>::Width>) -> <T as Family>::Item / { <T as Family>::Effects } { ignored }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let missing = signatures
        .diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.code == "G4190")
        .map(|diagnostic| diagnostic.message.as_str())
        .collect::<Vec<_>>();
    assert!(
        missing
            .iter()
            .any(|message| message.contains("associated type projection `Item`"))
            && missing
                .iter()
                .any(|message| message.contains("associated effect-row projection `Effects`"))
            && missing
                .iter()
                .any(|message| message.contains("associated const projection `Width`")),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn concrete_associated_projections_report_refuted_evidence_deterministically() {
    let package = PackageKey("signature-refuted-projection-obligation@0.1.0".into());
    let source = r#"
        trait Marker { type Item; }
        impl !Marker for i64 {}
        pub fn rejected(value: i64) -> <i64 as Marker>::Item { value }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4191" && diagnostic.message.contains("negative implementation")
        }),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn mixed_kind_trait_heads_are_preserved_in_associated_type_projections() {
    let package = PackageKey("signature-mixed-trait-projection@0.1.0".into());
    let source = "trait Select<'a, e: EffectRow, n: u32> { type Output; } pub fn project<'b, row: EffectRow, m: u32, T>(value: T) -> <T as Select<'b, row, m>>::Output where T: Select<'b, row, m> { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let select = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Select"))
        .unwrap()
        .key;
    let project = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("project"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&project).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection { subject, trait_definition, trait_arguments, name, .. }
            if **subject == Type::Generic(3)
                && *trait_definition == select
                && name == "Output"
                && trait_arguments == &[
                    GenericArgument::Lifetime(Lifetime::Generic(0)),
                    GenericArgument::EffectRow(grandiose_stage0::EffectRow {
                        effects: Default::default(), projections: vec![],
                        tail: Some(grandiose_stage0::EffectTail::Generic(1)),
                    }),
                    GenericArgument::ConstGeneric { index: 2, kind: ConstKind::U32 },
                ]
    ));
}

#[test]
fn generic_associated_item_arguments_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-gat-projection@0.1.0".into());
    let source = "trait Apply { type Output<T>; } pub fn project<S, T>(value: S) -> <S as Apply>::Output<T> where S: Apply { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let apply = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Apply"))
        .unwrap()
        .key;
    let project = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("project"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&project).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        } if **subject == Type::Generic(0)
            && *trait_definition == apply
            && trait_arguments.is_empty()
            && name == "Output"
            && item_generic_kinds == &[GenericKind::Type]
            && item_arguments == &[GenericArgument::Type(Type::Generic(1))]
    ));
}

#[test]
fn generic_associated_items_preserve_binder_kinds_and_reject_mismatched_impls() {
    let package = PackageKey("signature-gat-binder-kinds@0.1.0".into());
    let source = "trait Borrow { type View<'a, T, n: u32>; } impl Borrow for i64 { type View<'a, T, n: u32> = T; } trait Invalid { type View<'a>; } impl Invalid for i64 { type View<T> = T; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let borrow = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Borrow"))
        .expect("Borrow definition");
    let ElaboratedHeader::Trait(header) = signatures.definitions.get(&borrow.key).unwrap() else {
        panic!("expected trait")
    };
    assert_eq!(
        header.associated_types["View"].generic_kinds,
        [
            GenericKind::Lifetime,
            GenericKind::Type,
            GenericKind::Const(ConstKind::U32),
        ]
    );
    assert!(
        signatures.diagnostics.iter().any(|diagnostic| {
            diagnostic.code == "G4114" && diagnostic.message.contains("generic kinds")
        }),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn generic_associated_type_applications_preserve_lifetime_type_and_const_arguments() {
    let package = PackageKey("signature-gat-application-kinds@0.1.0".into());
    let source = "trait Borrow { type View<'a, T, n: u32>; } pub fn view<S, T>(value: S) -> <S as Borrow>::View<'static, T, 7> where S: Borrow { ignored }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let view = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("view"))
        .expect("view definition");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&view.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(matches!(
        &signature.result,
        Type::Projection { item_generic_kinds, item_arguments, .. }
            if item_generic_kinds == &[
                GenericKind::Lifetime,
                GenericKind::Type,
                GenericKind::Const(ConstKind::U32),
            ]
                && item_arguments == &[
                    GenericArgument::Lifetime(Lifetime::Static),
                    GenericArgument::Type(Type::Generic(1)),
                    GenericArgument::ConstU32(7),
                ]
    ));
}

#[test]
fn associated_effect_row_projections_are_preserved_in_frozen_signatures() {
    let package = PackageKey("signature-associated-effect-row@0.1.0".into());
    let source = "trait Capability { type Effects: EffectRow; } pub fn consume<T>(value: T) -> i64 / { <T as Capability>::Effects } where T: Capability { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let capability = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Capability"))
        .unwrap()
        .key;
    let consume = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("consume"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&consume).unwrap()
    else {
        panic!("expected callable")
    };
    assert!(signature.effects.effects.is_empty());
    assert!(matches!(
        signature.effects.projections.as_slice(),
        [grandiose_stage0::EffectRowProjection {
            subject,
            trait_definition,
            trait_arguments,
            name,
            item_generic_kinds,
            item_arguments,
        }] if **subject == Type::Generic(0)
            && *trait_definition == capability
            && trait_arguments.is_empty()
            && name == "Effects"
            && item_generic_kinds.is_empty()
            && item_arguments.is_empty()
    ));
}

#[test]
fn frozen_associated_effect_rows_are_canonical_sets() {
    let package = PackageKey("signature-associated-effect-row-canonical@0.1.0".into());
    let source = "trait First { type Effects: EffectRow; } trait Second { type Effects: EffectRow; } pub fn consume<T>(value: T) -> i64 / { <T as Second>::Effects, <T as First>::Effects, <T as First>::Effects } where T: First, T: Second { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let consume = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("consume"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&consume).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.effects.projections.len(), 2);
    assert!(
        signature
            .effects
            .projections
            .windows(2)
            .all(|pair| pair[0] != pair[1])
    );
    let mut inference = grandiose_stage0::InferContext::default();
    let first = inference
        .type_fingerprint(grandiose_stage0::Type::Callable {
            lifetime_binders: 0,
            parameters: signature.parameters.clone(),
            result: Box::new(signature.result.clone()),
            effects: signature.effects.clone(),
            invocation: signature.invocation,
        })
        .unwrap();
    let second = inference
        .type_fingerprint(grandiose_stage0::Type::Callable {
            lifetime_binders: 0,
            parameters: signature.parameters.clone(),
            result: Box::new(signature.result.clone()),
            effects: signature.effects.clone().canonicalized(),
            invocation: signature.invocation,
        })
        .unwrap();
    assert_eq!(first, second);
}

#[test]
fn kinded_effect_row_binders_preserve_open_row_tails() {
    let package = PackageKey("signature-open-row@0.1.0".into());
    let source = "pub fn relay<e: EffectRow>() -> i64 / { | e } { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .unwrap()
        .key;
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&relay).unwrap() else {
        panic!("expected callable")
    };
    assert_eq!(signature.effects.tail, Some(EffectTail::Generic(0)));
}

#[test]
fn generic_kinds_reject_crossing_type_and_effect_row_positions() {
    let package = PackageKey("signature-generic-kinds@0.1.0".into());
    let source = "pub fn invalid_tail<T>() -> i64 / { | T } { 0 } pub fn invalid_type<e: EffectRow>(value: e) -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let codes = signatures
        .diagnostics
        .iter()
        .map(|diagnostic| diagnostic.code)
        .collect::<Vec<_>>();
    assert!(codes.contains(&"G3311"), "{:#?}", signatures.diagnostics);
    assert!(codes.contains(&"G3313"), "{:#?}", signatures.diagnostics);
}

#[test]
fn effect_row_binders_are_preserved_for_nominals_and_aliases() {
    let package = PackageKey("signature-effect-row-binder-context@0.1.0".into());
    let source = "struct Invalid<e: EffectRow> {} trait AlsoInvalid<e: EffectRow> {} type Alias<e: EffectRow> = i64;";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3314")
            .count(),
        0,
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn callable_effect_rows_resolve_effect_declaration_identities() {
    let package = PackageKey("signature-effect-row@0.1.0".into());
    let source = "effect Console { write() } effect Trace { note() } pub fn run() -> i64 / { Trace, Console } { 42 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let run = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("run"))
        .unwrap();
    let console = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Console"))
        .unwrap();
    let trace = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Trace"))
        .unwrap();
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&run.key).unwrap()
    else {
        panic!("expected callable")
    };
    assert_eq!(signature.effects.effects.len(), 2);
    assert!(
        signature
            .effects
            .effects
            .iter()
            .any(|effect| effect.definition == console.key && effect.arguments.is_empty())
    );
    assert!(
        signature
            .effects
            .effects
            .iter()
            .any(|effect| effect.definition == trace.key && effect.arguments.is_empty())
    );
}

#[test]
fn generic_effect_rows_keep_protocol_arguments_in_their_identity() {
    let package = PackageKey("signature-generic-effect-row@0.1.0".into());
    let source = "effect State<T> { get() -> T } pub fn integers() -> i64 / State<i64> { 0 } pub fn text() -> Text / State<Text> { \"\" }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let state = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("State"))
        .unwrap()
        .key;
    let callable = |name| {
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some(name))
            .unwrap();
        let ElaboratedHeader::Callable(signature) =
            signatures.definitions.get(&definition.key).unwrap()
        else {
            panic!("expected callable")
        };
        signature
    };
    let integers = callable("integers").effects.effects.iter().next().unwrap();
    let text = callable("text").effects.effects.iter().next().unwrap();
    assert_eq!(integers.definition, state);
    assert_eq!(text.definition, state);
    assert_eq!(
        integers.arguments,
        [GenericArgument::Type(Type::Scalar(ScalarType::I64))]
    );
    assert_eq!(
        text.arguments,
        [GenericArgument::Type(Type::Scalar(ScalarType::Text))]
    );
    assert_ne!(integers, text);
}

#[test]
fn transparent_aliases_are_normalized_inside_callable_effect_identities() {
    let package = PackageKey("signature-effect-alias@0.1.0".into());
    let source = "type Message = Text; effect Log<T> { write(value: T) } pub fn run() -> i64 / Log<Message> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let run = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("run"))
        .expect("run declaration");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&run.key).unwrap()
    else {
        panic!("expected callable")
    };
    let effect = signature.effects.effects.iter().next().expect("Log effect");
    assert_eq!(
        effect.arguments,
        [GenericArgument::Type(Type::Scalar(ScalarType::Text))]
    );
}

#[test]
fn transparent_aliases_preserve_effectful_callable_contracts() {
    let package = PackageKey("signature-effectful-callable-alias@0.1.0".into());
    let source = "type Message = Text; effect Log<T> { write(value: T); } type Callback<T> = (T) -> T / Log<T>; pub fn relay(callback: Callback<Message>) -> Message / Log<Message> { panic }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let relay = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("relay"))
        .expect("relay declaration");
    let ElaboratedHeader::Callable(signature) = signatures.definitions.get(&relay.key).unwrap()
    else {
        panic!("expected callable")
    };
    let Type::Callable {
        parameters,
        result,
        effects,
        ..
    } = &signature.parameters[0]
    else {
        panic!("alias did not normalize to callable contract")
    };
    assert_eq!(parameters, &[Type::Scalar(ScalarType::Text)]);
    assert_eq!(result.as_ref(), &Type::Scalar(ScalarType::Text));
    let effect = effects.effects.iter().next().expect("Log effect");
    assert_eq!(
        effect.arguments,
        [GenericArgument::Type(Type::Scalar(ScalarType::Text))]
    );
    assert_eq!(effects, &signature.effects);
}

#[test]
fn trait_self_is_instantiated_for_method_contracts_and_impl_members() {
    let package = PackageKey("signature-trait-self@0.1.0".into());
    let source = "trait Identity { fn apply(value: Self) -> Self; } struct Box {} impl Identity for Box { fn apply(value: Self) -> Self { value } }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let box_definition = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Box"))
        .expect("Box definition")
        .key;
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| {
            matches!(
                definition.syntax.header,
                grandiose_stage0::ParsedHeader::Implementation(_)
            )
        })
        .expect("implementation definition");
    let ElaboratedHeader::Implementation(implementation) = signatures
        .definitions
        .get(&implementation.key)
        .expect("implementation signature")
    else {
        panic!("expected implementation signature")
    };
    let method = implementation.methods.get("apply").expect("apply method");
    let expected_self = Type::Nominal {
        definition: box_definition,
        arguments: vec![],
    };
    assert_eq!(method.parameters.len(), 1);
    assert_eq!(method.parameters[0], expected_self);
    assert_eq!(method.result, method.parameters[0]);
}

#[test]
fn trait_self_is_instantiated_in_supertrait_obligations() {
    let package = PackageKey("signature-trait-self-supertrait@0.1.0".into());
    let source = "trait Parent<T> {} trait Child: Parent<Self> {} impl Parent<i64> for i64 {} impl Child for i64 {}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn trait_supertrait_cycles_are_rejected_before_body_selection() {
    let package = PackageKey("signature-supertrait-cycle@0.1.0".into());
    let source = "trait First: Second {} trait Second: First {}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4175"),
        "{:#?}",
        signatures.diagnostics
    );
}

#[test]
fn associated_const_contracts_preserve_defaults_and_reject_missing_or_wrong_overrides() {
    let package = PackageKey("signature-associated-const@0.1.0".into());
    let source = "trait Shape { const Width: u32 = 4; const Demand: Quantity; } impl Shape for i64 { const Demand = [1, 2]; } impl Shape for Text { const Width = [1, 2]; const Demand = [1, 2]; const Extra = 9; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let shape = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Shape"))
        .expect("Shape trait");
    let ElaboratedHeader::Trait(shape) = signatures.definitions.get(&shape.key).unwrap() else {
        panic!("expected trait")
    };
    assert_eq!(shape.associated_consts["Width"].kind, ConstKind::U32);
    assert_eq!(
        shape.associated_consts["Width"].default,
        Some(GenericArgument::ConstU32(4))
    );
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4160")
    );
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G4161")
    );
}

#[test]
fn symbolic_u32_arithmetic_is_canonical_in_nominal_and_associated_const_contracts() {
    let package = PackageKey("signature-symbolic-structural-const@0.1.0".into());
    let source = "pub struct Tag<n: u32> {} pub fn advance<n: u32>(value: Tag<n + 1>) -> Tag<(1 + n)> { value } trait Sized<n: u32> { const Next: u32 = n + 1; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let advance = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("advance"))
        .expect("advance definition");
    let ElaboratedHeader::Callable(advance) = signatures.definitions.get(&advance.key).unwrap()
    else {
        panic!("expected callable")
    };
    let expected = GenericArgument::ConstU32Expr(StructuralU32Expr::Add(
        Box::new(StructuralU32Expr::Literal(1)),
        Box::new(StructuralU32Expr::Param(0)),
    ));
    let Type::Nominal { arguments, .. } = &advance.parameters[0] else {
        panic!("expected nominal parameter")
    };
    assert_eq!(arguments, &vec![expected.clone()]);
    let Type::Nominal { arguments, .. } = &advance.result else {
        panic!("expected nominal result")
    };
    assert_eq!(arguments, &vec![expected.clone()]);
    let sized = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("Sized"))
        .expect("trait definition");
    let ElaboratedHeader::Trait(sized) = signatures.definitions.get(&sized.key).unwrap() else {
        panic!("expected trait")
    };
    assert_eq!(sized.associated_consts["Next"].default, Some(expected));
}

#[test]
fn structural_u32_arithmetic_folds_closed_terms_and_rejects_checked_errors() {
    let package = PackageKey("signature-structural-const-errors@0.1.0".into());
    let source = "pub struct Fold<n: u32> {} pub fn folded(value: Fold<(2 + 3) * 4>) -> Fold<20> { value } pub fn invalid(value: Fold<1 / 0>) -> Fold<0> { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    let folded = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("folded"))
        .unwrap();
    let ElaboratedHeader::Callable(folded) = signatures.definitions.get(&folded.key).unwrap()
    else {
        panic!("expected callable")
    };
    let Type::Nominal { arguments, .. } = &folded.parameters[0] else {
        panic!("expected nominal")
    };
    assert_eq!(arguments, &vec![GenericArgument::ConstU32(20)]);
    let invalid = interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("invalid"))
        .unwrap();
    assert!(
        invalid
            .syntax
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3228"),
        "{:#?}",
        invalid.syntax.diagnostics
    );
}

#[test]
fn source_nominal_layouts_reject_owned_recursion_after_alias_normalization() {
    let package = PackageKey("signature-owned-layout-recursion@0.1.0".into());
    let source = "type Alias = Direct; pub struct Direct { next: Alias } pub struct Wrap<T> { value: T } pub struct ThroughGeneric { next: Wrap<ThroughGeneric> } pub struct Growing<T> { next: Growing<(T, T)> } pub enum ThroughVariant { Again(ThroughVariant), Done } pub struct Linked { next: &Linked }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert_eq!(
        signatures
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3320")
            .count(),
        4,
        "aliases, direct and growing generic fields, and enum payloads must all participate in owned-layout recursion checking: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn source_nominal_layouts_reject_recursion_hidden_by_associated_type_projections() {
    let package = PackageKey("signature-owned-layout-associated-cycle@0.1.0".into());
    let source = "trait Link { type Next; } pub struct Node { next: <Node as Link>::Next } impl Link for Node { type Next = Node; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3320"),
        "an associated type projection hid an infinitely-sized nominal layout: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn source_nominal_layouts_accept_distinct_finite_generic_instantiations() {
    let package = PackageKey("signature-owned-layout-instantiations@0.1.0".into());
    // The outer Result carries EffectRow, but EffectRow's Option alias expands
    // to a separate Result<Phantom<EffectRow>, ()>. Phantom erases its type
    // argument, so this distinct finite Result instantiation is not a
    // recursive owned layout.
    let source = "pub enum Result<T, E> { Ok(T), Err(E) } pub type Option<T> = Result<T, ()>; pub struct Phantom<T> { marker: usize } pub struct EffectRow { row_tail: Option<Phantom<EffectRow>> } pub struct Callable { effects: Result<EffectRow, ()> }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(
        !signatures
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3320"),
        "distinct finite generic applications must not be conflated into an owned-layout cycle: {:#?}",
        signatures.diagnostics
    );
}

#[test]
fn forged_interface_nominal_layout_cycle_is_rejected_before_core_or_mir() {
    let node = DefKey(Digest::of_bytes(b"forged-owned-layout-node"));
    let forged = ElaboratedInterface {
        definitions: BTreeMap::from([(
            node,
            ElaboratedHeader::Nominal {
                generics: 0,
                generic_kinds: vec![],
                layout: ElaboratedNominalLayout::Struct(vec![NominalField {
                    name: "next".into(),
                    ty: Type::Nominal {
                        definition: node,
                        arguments: vec![],
                    },
                    private_authority: None,
                }]),
            },
        )]),
        host_imports: BTreeMap::new(),
        diagnostics: vec![],
    };
    let checked = ElaboratedInterface::merge([forged]);
    assert!(
        checked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3320"),
        "a forged interface may not inject an infinite owned layout into Core or MIR"
    );
}
