use std::collections::BTreeSet;

use grandiose_stage0::{
    DefKey, Digest, EffectInstance, EffectRow, EffectRowProjection, GenericArgument, InferContext,
    Lifetime, Quantity, ScalarType, Type, TypeError,
};

#[test]
fn canonical_generic_arguments_keep_lifetimes_and_effect_rows_out_of_type_slots() {
    let lifetime = GenericArgument::Lifetime(Lifetime::Static);
    let row = GenericArgument::EffectRow(EffectRow::empty());
    let ty = GenericArgument::Type(Type::Unit);
    assert_ne!(lifetime, ty);
    assert_ne!(row, ty);
    assert_ne!(lifetime, row);
}

#[test]
fn unification_is_occurs_checked_and_zonks_body_local_uncertainty() {
    let mut inference = InferContext::default();
    let variable = inference.fresh();
    inference
        .unify(variable.clone(), Type::Scalar(ScalarType::I64))
        .unwrap();
    assert_eq!(
        inference.zonk(variable).unwrap(),
        Type::Scalar(ScalarType::I64)
    );

    let recursive = inference.fresh();
    let Type::Infer(variable) = recursive.clone() else {
        unreachable!()
    };
    let error = inference
        .unify(recursive, Type::Array(Box::new(Type::Infer(variable))))
        .unwrap_err();
    assert!(matches!(error, TypeError::Occurs(_, _)));
}

#[test]
fn callable_unification_requires_effect_and_invocation_agreement() {
    let callable = Type::Callable {
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Unit),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let mut inference = InferContext::default();
    assert_eq!(
        inference.unify(callable.clone(), callable.clone()).unwrap(),
        callable
    );
    let incompatible = Type::Callable {
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Unit),
        effects: EffectRow::empty(),
        invocation: Quantity::AFFINE,
    };
    assert!(matches!(
        inference.unify(callable, incompatible),
        Err(TypeError::Mismatch { .. })
    ));
}

#[test]
fn never_is_the_bottom_type_for_expected_result_positions() {
    let mut inference = InferContext::default();
    assert_eq!(
        inference
            .unify(Type::Scalar(ScalarType::I64), Type::Never)
            .unwrap(),
        Type::Scalar(ScalarType::I64)
    );
    assert_eq!(
        inference
            .unify(Type::Never, Type::Scalar(ScalarType::Text))
            .unwrap(),
        Type::Scalar(ScalarType::Text)
    );
}

#[test]
fn open_effect_rows_unify_without_becoming_type_holes() {
    let read = DefKey(Digest::of_bytes(b"Read"));
    let write = DefKey(Digest::of_bytes(b"Write"));
    let mut inference = InferContext::default();
    let mut left_effects = inference.fresh_effects();
    left_effects.effects.insert(EffectInstance {
        definition: read,
        arguments: vec![],
    });
    let mut right_effects = inference.fresh_effects();
    right_effects.effects.insert(EffectInstance {
        definition: write,
        arguments: vec![],
    });

    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    let unified = inference
        .unify(callable(left_effects), callable(right_effects))
        .unwrap();
    let closed = EffectRow::closed(BTreeSet::from([read, write]));
    let expected = callable(closed.clone());
    let unified = inference.unify(unified, expected).unwrap();
    assert_eq!(
        inference.zonk(unified).unwrap(),
        callable(closed),
        "the shared residual effect variable is solved by the closed context"
    );
}

#[test]
fn effect_rows_distinguish_instances_of_the_same_protocol_declaration() {
    let state = DefKey(Digest::of_bytes(b"State"));
    let integers = EffectRow::closed_instances([EffectInstance {
        definition: state,
        arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    }]);
    let text = EffectRow::closed_instances([EffectInstance {
        definition: state,
        arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
    }]);
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    assert_ne!(integers, text);
    assert!(matches!(
        InferContext::default().unify(callable(integers), callable(text)),
        Err(TypeError::EffectRow { .. })
    ));
}

#[test]
fn callable_fingerprints_include_associated_effect_row_projections() {
    let capability = DefKey(Digest::of_bytes(b"Capability"));
    let subject = Type::Scalar(ScalarType::I64);
    let callable = |name: &str| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: EffectRow {
            effects: BTreeSet::new(),
            projections: vec![EffectRowProjection {
                subject: Box::new(subject.clone()),
                trait_definition: capability,
                trait_arguments: vec![],
                name: name.into(),
                item_arguments: vec![],
            }],
            tail: None,
        },
        invocation: Quantity::ONCE,
    };
    let mut inference = InferContext::default();
    let first = inference.type_fingerprint(callable("First")).unwrap();
    let second = inference.type_fingerprint(callable("Second")).unwrap();
    assert_ne!(first, second);
}

#[test]
fn symbolic_effect_row_projections_are_sorted_deduplicated_and_fingerprinted_canonically() {
    let first = DefKey(Digest::of_bytes(b"FirstCapability"));
    let second = DefKey(Digest::of_bytes(b"SecondCapability"));
    let projection = |trait_definition, name: &str| EffectRowProjection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition,
        trait_arguments: vec![],
        name: name.into(),
        item_arguments: vec![],
    };
    let row = |projections| EffectRow {
        effects: BTreeSet::new(),
        projections,
        tail: None,
    };
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };

    let source_order = row(vec![
        projection(second, "Second"),
        projection(first, "First"),
        projection(first, "First"),
    ]);
    let canonical_order = row(vec![
        projection(first, "First"),
        projection(second, "Second"),
    ]);

    let mut inference = InferContext::default();
    let source_fingerprint = inference.type_fingerprint(callable(source_order)).unwrap();
    let canonical_fingerprint = inference
        .type_fingerprint(callable(canonical_order.clone()))
        .unwrap();
    assert_eq!(source_fingerprint, canonical_fingerprint);

    let zonked = inference
        .zonk(callable(row(vec![
            projection(second, "Second"),
            projection(first, "First"),
            projection(first, "First"),
        ])))
        .unwrap();
    let Type::Callable { effects, .. } = zonked else {
        panic!("expected callable");
    };
    assert_eq!(effects, canonical_order);
}

#[test]
fn matching_associated_effect_row_projections_unify_without_erasure() {
    let capability = DefKey(Digest::of_bytes(b"Capability"));
    let row = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: capability,
            trait_arguments: vec![],
            name: "Effects".into(),
            item_arguments: vec![],
        }],
        tail: None,
    };
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    let unified = InferContext::default()
        .unify(callable(row.clone()), callable(row.clone()))
        .unwrap();
    assert_eq!(unified, callable(row));
}

#[test]
fn associated_effect_row_projections_unify_their_subject_and_type_arguments() {
    let capability = DefKey(Digest::of_bytes(b"Capability"));
    let mut inference = InferContext::default();
    let left = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(inference.fresh()),
            trait_definition: capability,
            trait_arguments: vec![inference.fresh()],
            name: "Effects".into(),
            item_arguments: vec![inference.fresh()],
        }],
        tail: None,
    };
    let right = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: capability,
            trait_arguments: vec![Type::Scalar(ScalarType::Text)],
            name: "Effects".into(),
            item_arguments: vec![Type::Scalar(ScalarType::U8)],
        }],
        tail: None,
    };
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };

    let unified = inference
        .unify(callable(left), callable(right.clone()))
        .unwrap();
    assert_eq!(inference.zonk(unified).unwrap(), callable(right));
}

#[test]
fn associated_effect_row_projection_sets_unify_independently_of_source_order() {
    let first = DefKey(Digest::of_bytes(b"FirstCapability"));
    let second = DefKey(Digest::of_bytes(b"SecondCapability"));
    let projection = |trait_definition, name: &str| EffectRowProjection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition,
        trait_arguments: vec![],
        name: name.into(),
        item_arguments: vec![],
    };
    let left = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![projection(first, "First"), projection(second, "Second")],
        tail: None,
    };
    let right = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![projection(second, "Second"), projection(first, "First")],
        tail: None,
    };
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };

    assert_eq!(
        InferContext::default()
            .unify(callable(left.clone()), callable(right))
            .unwrap(),
        callable(left)
    );
}

#[test]
fn distinct_associated_effect_row_projections_do_not_unify() {
    let capability = DefKey(Digest::of_bytes(b"Capability"));
    let row = |name: &str| EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: capability,
            trait_arguments: vec![],
            name: name.into(),
            item_arguments: vec![],
        }],
        tail: None,
    };
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    assert!(matches!(
        InferContext::default().unify(callable(row("Left")), callable(row("Right"))),
        Err(TypeError::EffectRow { .. })
    ));
}

#[test]
fn effect_row_unification_solves_protocol_argument_inference() {
    let state = DefKey(Digest::of_bytes(b"State"));
    let mut inference = InferContext::default();
    let variable = inference.fresh();
    let generic = EffectRow::closed_instances([EffectInstance {
        definition: state,
        arguments: vec![GenericArgument::Type(variable)],
    }]);
    let concrete = EffectRow::closed_instances([EffectInstance {
        definition: state,
        arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    }]);
    let callable = |effects| Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    let unified = inference
        .unify(callable(generic), callable(concrete.clone()))
        .unwrap();
    assert_eq!(inference.zonk(unified).unwrap(), callable(concrete));
}

#[test]
fn type_fingerprints_are_canonical_and_reject_unresolved_semantics() {
    let definition = DefKey(Digest::of_bytes(b"Pair"));
    let value = Type::Nominal {
        definition,
        arguments: vec![GenericArgument::Type(Type::Tuple(vec![
            Type::Scalar(ScalarType::I64),
            Type::Unit,
        ]))],
    };
    let mut first = InferContext::default();
    let mut second = InferContext::default();
    assert_eq!(
        first.type_fingerprint(value.clone()).unwrap(),
        second.type_fingerprint(value).unwrap()
    );
    let unresolved = second.fresh();
    assert!(matches!(
        second.type_fingerprint(unresolved),
        Err(TypeError::Unresolved(_))
    ));
}

#[test]
fn nominal_identity_preserves_mixed_kind_generic_arguments() {
    let definition = DefKey(Digest::of_bytes(b"mixed-nominal"));
    let quantity = Quantity::new(1, Some(2)).unwrap();
    let mixed = Type::Nominal {
        definition,
        arguments: vec![
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::ConstU32(7),
            GenericArgument::ConstQuantity(quantity),
            GenericArgument::Type(Type::Scalar(ScalarType::I64)),
        ],
    };
    let distinct = Type::Nominal {
        definition,
        arguments: vec![
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::ConstU32(8),
            GenericArgument::ConstQuantity(quantity),
            GenericArgument::Type(Type::Scalar(ScalarType::I64)),
        ],
    };
    assert_ne!(mixed, distinct);
    let mut inference = InferContext::default();
    assert_ne!(
        inference.type_fingerprint(mixed).unwrap(),
        InferContext::default().type_fingerprint(distinct).unwrap()
    );
}

#[test]
fn effect_instance_ordering_is_total_during_error_recovery() {
    let definition = DefKey(Digest::of_bytes(b"recovery-effect"));
    let mut inference = InferContext::default();
    let mut instances = BTreeSet::new();
    instances.insert(EffectInstance {
        definition,
        arguments: vec![GenericArgument::Type(Type::Error)],
    });
    instances.insert(EffectInstance {
        definition,
        arguments: vec![GenericArgument::Type(inference.fresh())],
    });
    assert_eq!(instances.len(), 2);
}

#[test]
fn effect_instance_identity_preserves_generic_argument_kinds() {
    let definition = DefKey(Digest::of_bytes(b"kind-preserving-effect"));
    let type_encoded_const = EffectInstance {
        definition,
        arguments: vec![GenericArgument::Type(Type::ConstU32(1))],
    };
    let structural_const = EffectInstance {
        definition,
        arguments: vec![GenericArgument::ConstU32(1)],
    };
    assert_ne!(type_encoded_const, structural_const);

    let instances = BTreeSet::from([type_encoded_const, structural_const]);
    assert_eq!(
        instances.len(),
        2,
        "effect identity must not erase argument kinds"
    );
}
