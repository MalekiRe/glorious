use std::collections::BTreeSet;

use grandiose_stage0::{
    DefKey, Digest, EffectInstance, EffectRow, EffectRowProjection, EffectTail, GenericArgument,
    InferContext, Lifetime, Quantity, ScalarType, Type, TypeError,
};

#[test]
fn associated_row_subset_candidate_trials_do_not_leak_or_guess_bindings() {
    let projection = |subject: Type, argument: Type| EffectRowProjection {
        subject: Box::new(subject),
        trait_definition: DefKey(Digest::of_bytes(b"transactional-row-subset")),
        trait_arguments: vec![GenericArgument::Type(argument)],
        name: "Effects".into(), item_generic_kinds: vec![], item_arguments: vec![],
    };
    let row = |projections| EffectRow { effects: BTreeSet::new(), projections, tails: BTreeSet::new() };
    let i64_ty = Type::Scalar(ScalarType::I64);
    let u8_ty = Type::Scalar(ScalarType::U8);
    let mut inference = InferContext::default();
    let subject = inference.fresh();
    inference.constrain_effect_subset(
        row(vec![projection(subject.clone(), i64_ty.clone())]),
        row(vec![projection(u8_ty.clone(), u8_ty.clone()), projection(i64_ty.clone(), i64_ty.clone())]),
    ).unwrap();
    assert_eq!(inference.zonk(subject).unwrap(), i64_ty);

    let mut inference = InferContext::default();
    let subject = inference.fresh();
    assert!(inference.constrain_effect_subset(
        row(vec![projection(subject.clone(), i64_ty.clone())]),
        row(vec![projection(u8_ty, i64_ty.clone()), projection(i64_ty.clone(), i64_ty)]),
    ).is_err(), "an unknown subject cannot arbitrarily choose a union operand");
    assert!(matches!(inference.zonk(subject), Err(TypeError::Unresolved(_))));
}

fn row_callable(effects: EffectRow) -> Type {
    Type::Callable { contract: Default::default(), safety: grandiose_stage0::Safety::Safe, lifetime_binders: 0,
        parameters: vec![], result: Box::new(Type::Unit), effects, invocation: Quantity::ONCE }
}

#[test]
fn row_union_equations_wait_for_independent_operand_evidence() {
    let mut inference = InferContext::default();
    let first = inference.fresh_effects();
    let second = inference.fresh_effects();
    let mut union = first.clone(); union.extend(second.clone());
    let a = DefKey(Digest::of_bytes(b"row-union-a"));
    let b = DefKey(Digest::of_bytes(b"row-union-b"));
    inference.unify(row_callable(union.clone()), row_callable(EffectRow::closed([a,b]))).unwrap();
    inference.unify(row_callable(first.clone()), row_callable(EffectRow::closed([a]))).unwrap();
    inference.unify(row_callable(second.clone()), row_callable(EffectRow::closed([b]))).unwrap();
    assert_eq!(inference.zonk_effects(union).unwrap(), EffectRow::closed([a,b]));
    assert_eq!(inference.zonk_effects(first).unwrap(), EffectRow::closed([a]));
    assert_eq!(inference.zonk_effects(second).unwrap(), EffectRow::closed([b]));
}

#[test]
fn unresolved_nonempty_union_is_ambiguous_but_empty_union_is_unique() {
    for empty in [false, true] {
        let mut inference = InferContext::default();
        let first = inference.fresh_effects();
        let second = inference.fresh_effects();
        let mut union = first.clone(); union.extend(second.clone());
        let known = if empty { EffectRow::empty() } else { EffectRow::closed([DefKey(Digest::of_bytes(b"known"))]) };
        inference.unify(row_callable(union.clone()), row_callable(known)).unwrap();
        if empty {
            assert_eq!(inference.zonk_effects(first).unwrap(), EffectRow::empty());
            assert_eq!(inference.zonk_effects(second).unwrap(), EffectRow::empty());
        } else {
            assert!(matches!(inference.zonk_effects(union), Err(TypeError::AmbiguousEffectUnion { .. })));
        }
    }
}

#[test]
fn row_union_identity_is_unordered_but_never_discards_an_operand() {
    let row = |indices: &[u32]| EffectRow { effects: BTreeSet::new(), projections: vec![],
        tails: indices.iter().copied().map(EffectTail::Generic).collect() };
    let mut inference = InferContext::default();
    let fingerprint = inference.type_fingerprint(row_callable(row(&[1,0,1]))).unwrap();
    assert_eq!(fingerprint, inference.type_fingerprint(row_callable(row(&[0,1]))).unwrap());
    assert_ne!(fingerprint, inference.type_fingerprint(row_callable(row(&[0]))).unwrap());
}

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
fn lifetime_inference_is_local_kind_checked_and_cannot_rebind_declared_regions() {
    let carrier = DefKey(Digest::of_bytes(b"lifetime-inference-carrier"));
    let nominal = |lifetime| Type::Nominal {
        definition: carrier, arguments: vec![GenericArgument::Lifetime(lifetime)],
    };
    let mut inference = InferContext::default();
    let first = inference.fresh_lifetime();
    let second = inference.fresh_lifetime();
    let third = inference.fresh_lifetime();
    assert_ne!(first, second);
    assert_ne!(second, third);
    inference.unify(nominal(first), nominal(second)).unwrap();
    inference.unify(nominal(second), nominal(Lifetime::Generic(0))).unwrap();
    assert_eq!(inference.zonk(nominal(first)).unwrap(), nominal(Lifetime::Generic(0)));
    inference.unify(nominal(third), nominal(Lifetime::Static)).unwrap();
    assert_eq!(inference.zonk(nominal(third)).unwrap(), nominal(Lifetime::Static));
    assert!(matches!(inference.unify(nominal(first), nominal(Lifetime::Generic(1))),
        Err(TypeError::LifetimeMismatch { .. })));
    assert_eq!(inference.zonk(nominal(first)).unwrap(), nominal(Lifetime::Generic(0)));
    let fresh = inference.fresh_lifetime();
    assert!(inference.unify(nominal(fresh), Type::Nominal {
        definition: carrier, arguments: vec![GenericArgument::Type(Type::Unit)],
    }).is_err());
}

#[test]
fn unresolved_lifetimes_cannot_enter_frozen_types_or_fingerprints() {
    let mut inference = InferContext::default();
    let lifetime = inference.fresh_lifetime();
    let reference = Type::Reference {
        mutability: grandiose_stage0::Mutability::Shared, lifetime,
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    assert!(matches!(inference.zonk(reference.clone()), Err(TypeError::UnresolvedLifetime(_))));
    assert!(matches!(inference.type_fingerprint(reference.clone()), Err(TypeError::UnresolvedLifetime(_))));
    let resolved = Type::Reference {
        mutability: grandiose_stage0::Mutability::Shared, lifetime: Lifetime::Static,
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    inference.unify(reference.clone(), resolved.clone()).unwrap();
    assert_eq!(inference.zonk(reference.clone()).unwrap(), resolved);
    assert_eq!(inference.type_fingerprint(reference).unwrap(),
        InferContext::default().type_fingerprint(resolved).unwrap());
}

#[test]
fn const_generic_inference_is_kind_checked_occurs_checked_and_zonked() {
    let carrier = DefKey(Digest::of_bytes(b"const-inference-carrier"));
    let trait_definition = DefKey(Digest::of_bytes(b"const-inference-trait"));
    let mut inference = InferContext::default();
    let u32_hole = inference.fresh_const(grandiose_stage0::ConstKind::U32);
    let quantity_hole = inference.fresh_const(grandiose_stage0::ConstKind::Quantity);

    let inferred = inference
        .unify(
            Type::Nominal {
                definition: carrier,
                arguments: vec![u32_hole, quantity_hole],
            },
            Type::Nominal {
                definition: carrier,
                arguments: vec![
                    GenericArgument::ConstInteger(7u32.into()),
                    GenericArgument::ConstQuantity(Quantity::new(2, Some(4)).unwrap()),
                ],
            },
        )
        .expect("matching nominal arguments should solve each native const domain");
    assert_eq!(
        inference.zonk(inferred).unwrap(),
        Type::Nominal {
            definition: carrier,
            arguments: vec![
                GenericArgument::ConstInteger(7u32.into()),
                GenericArgument::ConstQuantity(Quantity::new(2, Some(4)).unwrap()),
            ],
        }
    );

    let u32_hole = inference.fresh_const(grandiose_stage0::ConstKind::U32);
    assert!(matches!(
        inference.unify(
            Type::Nominal {
                definition: carrier,
                arguments: vec![u32_hole],
            },
            Type::Nominal {
                definition: carrier,
                arguments: vec![GenericArgument::ConstQuantity(Quantity::ONCE)],
            },
        ),
        Err(TypeError::Mismatch { .. })
    ));

    let recursive = inference.fresh_const(grandiose_stage0::ConstKind::U32);
    let recursive_projection = GenericArgument::ConstProjection {
        subject: Box::new(Type::Unit),
        trait_definition,
        trait_arguments: vec![recursive.clone()],
        name: "Value".into(),
        kind: grandiose_stage0::ConstKind::U32,
    };
    assert!(matches!(
        inference.unify(
            Type::Nominal {
                definition: carrier,
                arguments: vec![recursive],
            },
            Type::Nominal {
                definition: carrier,
                arguments: vec![recursive_projection],
            },
        ),
        Err(TypeError::Mismatch { .. })
    ));
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
fn occurs_checks_cover_callable_effect_and_nominal_generic_edges() {
    let effect = DefKey(Digest::of_bytes(b"recursive-inference-effect"));
    let nominal = DefKey(Digest::of_bytes(b"recursive-inference-nominal"));

    let mut inference = InferContext::default();
    let recursive_callable = inference.fresh();
    let Type::Infer(callable_variable) = recursive_callable.clone() else {
        unreachable!()
    };
    let callable = Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: EffectRow::closed_instances([EffectInstance {
            definition: effect,
            arguments: vec![GenericArgument::Type(Type::Infer(callable_variable))],
        }]),
        invocation: Quantity::ONCE,
    };
    assert!(matches!(
        inference.unify(recursive_callable.clone(), callable),
        Err(TypeError::Occurs(_, _))
    ));
    assert!(matches!(
        inference.zonk(recursive_callable),
        Err(TypeError::Unresolved(_))
    ));

    let recursive_nominal = inference.fresh();
    let Type::Infer(nominal_variable) = recursive_nominal.clone() else {
        unreachable!()
    };
    let nominal_with_open_effect_argument = Type::Nominal {
        definition: nominal,
        arguments: vec![GenericArgument::EffectRow(EffectRow::closed_instances([
            EffectInstance {
                definition: effect,
                arguments: vec![GenericArgument::Type(Type::Infer(nominal_variable))],
            },
        ]))],
    };
    assert!(matches!(
        inference.unify(recursive_nominal.clone(), nominal_with_open_effect_argument),
        Err(TypeError::Occurs(_, _))
    ));
    assert!(matches!(
        inference.zonk(recursive_nominal),
        Err(TypeError::Unresolved(_))
    ));
}

#[test]
fn effect_occurs_checks_follow_nested_callable_effect_rows() {
    let effect = DefKey(Digest::of_bytes(b"recursive-effect-row"));
    let mut inference = InferContext::default();
    let open_effects = inference.fresh_effects();
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    let row_that_carries_its_own_open_tail = EffectRow::closed_instances([EffectInstance {
        definition: effect,
        arguments: vec![GenericArgument::Type(callable(open_effects.clone()))],
    }]);
    assert!(matches!(
        inference.unify(
            callable(open_effects.clone()),
            callable(row_that_carries_its_own_open_tail)
        ),
        Err(TypeError::EffectOccurs(_, _))
    ));
    assert!(matches!(
        inference.zonk_effects(open_effects),
        Err(TypeError::UnresolvedEffect(_))
    ));
}

#[test]
fn type_occurs_checks_follow_previously_bound_effect_tail_chains() {
    let effect = DefKey(Digest::of_bytes(b"bound-effect-tail-occurs"));
    let nominal = DefKey(Digest::of_bytes(b"bound-effect-tail-nominal"));
    let mut inference = InferContext::default();
    let type_variable = inference.fresh();
    let Type::Infer(variable) = type_variable.clone() else {
        unreachable!()
    };
    let open_effects = inference.fresh_effects();
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };

    // First solve the row tail. The later type constraint can only discover
    // its own variable by chasing this established effect-row binding.
    let bound_row = EffectRow::closed_instances([EffectInstance {
        definition: effect,
        arguments: vec![GenericArgument::Type(Type::Infer(variable))],
    }]);
    inference
        .unify(callable(open_effects.clone()), callable(bound_row))
        .expect("the row tail may be bound before the type constraint arrives");

    let type_that_reenters_the_bound_tail = Type::Nominal {
        definition: nominal,
        arguments: vec![GenericArgument::EffectRow(open_effects)],
    };
    assert!(matches!(
        inference.unify(type_variable.clone(), type_that_reenters_the_bound_tail),
        Err(TypeError::Occurs(_, _))
    ));
    assert!(matches!(
        inference.zonk(type_variable),
        Err(TypeError::Unresolved(_))
    ));
}

#[test]
fn callable_unification_requires_effect_and_invocation_agreement() {
    let callable = Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
    let incompatible = Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
fn never_does_not_bind_an_unresolved_expected_result() {
    for terminal_first in [false, true] {
        let mut inference = InferContext::default();
        let expected = inference.fresh();
        let result = if terminal_first {
            inference.unify(Type::Never, expected.clone())
        } else {
            inference.unify(expected.clone(), Type::Never)
        }.unwrap();
        assert_eq!(result, expected);
        inference.unify(expected.clone(), Type::Scalar(ScalarType::I64)).unwrap();
        assert_eq!(inference.zonk(expected).unwrap(), Type::Scalar(ScalarType::I64));
    }
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

    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
fn effect_row_subset_constraints_preserve_open_tail_remainders() {
    let trace = DefKey(Digest::of_bytes(b"Trace"));
    let log = DefKey(Digest::of_bytes(b"Log"));
    let mut inference = InferContext::default();
    let required_tail = inference.fresh_effects();
    let variable = required_tail.tails.first().copied();
    let mut required = required_tail;
    required.effects.insert(EffectInstance {
        definition: trace,
        arguments: vec![],
    });
    let allowed = EffectRow::closed([trace, log]);
    inference
        .constrain_effect_subset(required, allowed)
        .expect("open row must solve to the allowed remainder");
    let zonked = inference.zonk_effects(match variable {
        Some(EffectTail::Infer(variable)) => EffectRow {
            effects: BTreeSet::from([EffectInstance {
                definition: trace,
                arguments: vec![],
            }]),
            projections: vec![],
            tails: [EffectTail::Infer(variable)].into_iter().collect(),
        },
        _ => unreachable!(),
    });
    assert_eq!(zonked.unwrap(), EffectRow::closed([trace, log]));
}

#[test]
fn effect_row_subset_rejects_rigid_generic_tail_mismatches() {
    let trace = DefKey(Digest::of_bytes(b"Trace"));
    let required = EffectRow {
        effects: BTreeSet::from([EffectInstance {
            definition: trace,
            arguments: vec![],
        }]),
        projections: vec![],
        tails: [EffectTail::Generic(1)].into_iter().collect(),
    };
    let allowed = EffectRow {
        effects: BTreeSet::from([EffectInstance {
            definition: trace,
            arguments: vec![],
        }]),
        projections: vec![],
        tails: [EffectTail::Generic(2)].into_iter().collect(),
    };
    assert!(matches!(
        InferContext::default().constrain_effect_subset(required, allowed),
        Err(TypeError::EffectRow { .. })
    ));
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
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
    let callable = |name: &str| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
                item_generic_kinds: vec![],
                item_arguments: vec![],
            }],
            tails: Default::default(),
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
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let row = |projections| EffectRow {
        effects: BTreeSet::new(),
        projections,
        tails: Default::default(),
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
            item_generic_kinds: vec![],
            item_arguments: vec![],
        }],
        tails: Default::default(),
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
            trait_arguments: vec![GenericArgument::Type(inference.fresh())],
            name: "Effects".into(),
            item_generic_kinds: vec![grandiose_stage0::GenericKind::Type],
            item_arguments: vec![GenericArgument::Type(inference.fresh())],
        }],
        tails: Default::default(),
    };
    let right = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![EffectRowProjection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: capability,
            trait_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
            name: "Effects".into(),
            item_generic_kinds: vec![grandiose_stage0::GenericKind::Type],
            item_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::U8))],
        }],
        tails: Default::default(),
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let left = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![projection(first, "First"), projection(second, "Second")],
        tails: Default::default(),
    };
    let right = EffectRow {
        effects: BTreeSet::new(),
        projections: vec![projection(second, "Second"), projection(first, "First")],
        tails: Default::default(),
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
            item_generic_kinds: vec![],
            item_arguments: vec![],
        }],
        tails: Default::default(),
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
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
            GenericArgument::ConstInteger(7u32.into()),
            GenericArgument::ConstQuantity(quantity),
            GenericArgument::Type(Type::Scalar(ScalarType::I64)),
        ],
    };
    let distinct = Type::Nominal {
        definition,
        arguments: vec![
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::ConstInteger(8u32.into()),
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
fn nominal_effect_row_arguments_unify_and_solve_open_tails() {
    let wrapper = DefKey(Digest::of_bytes(b"row-generic-wrapper"));
    let trace = DefKey(Digest::of_bytes(b"row-generic-trace"));
    let mut inference = InferContext::default();
    let open = inference.fresh_effects();
    let left = Type::Nominal {
        definition: wrapper,
        arguments: vec![GenericArgument::EffectRow(open)],
    };
    let right = Type::Nominal {
        definition: wrapper,
        arguments: vec![GenericArgument::EffectRow(EffectRow::closed([trace]))],
    };

    let unified = inference.unify(left, right.clone()).unwrap();
    assert_eq!(inference.zonk(unified).unwrap(), right);
}

#[test]
fn effect_instance_row_arguments_participate_in_protocol_matching() {
    let carrier = DefKey(Digest::of_bytes(b"row-argument-carrier-effect"));
    let trace = DefKey(Digest::of_bytes(b"row-argument-trace"));
    let mut inference = InferContext::default();
    let open = inference.fresh_effects();
    let row = |argument| {
        EffectRow::closed_instances([EffectInstance {
            definition: carrier,
            arguments: vec![GenericArgument::EffectRow(argument)],
        }])
    };
    let callable = |effects| Type::Callable { contract: Default::default(),
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects,
        invocation: Quantity::ONCE,
    };
    let concrete = row(EffectRow::closed([trace]));

    let unified = inference
        .unify(callable(row(open)), callable(concrete.clone()))
        .unwrap();
    assert_eq!(inference.zonk(unified).unwrap(), callable(concrete));
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
        arguments: vec![GenericArgument::Type(Type::ConstInteger(1u32.into()))],
    };
    let structural_const = EffectInstance {
        definition,
        arguments: vec![GenericArgument::ConstInteger(1u32.into())],
    };
    assert_ne!(type_encoded_const, structural_const);

    let instances = BTreeSet::from([type_encoded_const, structural_const]);
    assert_eq!(
        instances.len(),
        2,
        "effect identity must not erase argument kinds"
    );
}

#[test]
fn result_generalization_defaults_numeric_variables_but_preserves_parametric_values() {
    let mut inference = InferContext::default();
    let number = inference.fresh();
    inference.constrain_numeric(number.clone(), false).unwrap();
    let arbitrary = inference.fresh();
    let (result, binders) = inference.generalize_result_type(Type::Tuple(vec![number, arbitrary])).unwrap();
    assert_eq!(result, Type::Tuple(vec![Type::Scalar(ScalarType::I64), Type::Generic(0)]));
    assert_eq!(binders, vec![grandiose_stage0::GenericKind::Type]);
}
