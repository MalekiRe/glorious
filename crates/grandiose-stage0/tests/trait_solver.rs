use grandiose_stage0::{
    DeclarationScan, DefKey, ElaboratedInterface, ElaboratedTraitReference, FileKey,
    GenericArgument, InterfaceSet, LexedFile, Lifetime, Mutability, PackageKey, ScalarType,
    TraitAnswer, TraitEffectRowProjectionAnswer, TraitGoal, TraitMethodAnswer,
    TraitProjectionAnswer, TraitSolver, Type, implementation_method_key,
};

fn signatures(source: &str) -> (grandiose_stage0::PackageInterface, ElaboratedInterface) {
    let package = PackageKey("trait-solver@0.1.0".into());
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
    (interface, signatures)
}

fn key(interface: &grandiose_stage0::PackageInterface, name: &str) -> DefKey {
    interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some(name))
        .unwrap()
        .key
}

#[test]
fn tabled_solver_proves_generic_impls_after_where_obligations() {
    let (interface, signatures) = signatures(
        "trait Copy {} trait Ready {} struct Box<T> {} impl Copy for i64 {} impl<T> Ready for Box<T> where T: Copy {}",
    );
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let mut solver = TraitSolver::new(&signatures);
    let answer = solver.solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![Type::Scalar(ScalarType::I64)],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn solver_matches_alpha_equivalent_hrtb_heads_but_rejects_outer_lifetime_leaks() {
    let (interface, signatures) = signatures(
        "trait CallableMarker {} impl CallableMarker for for<'a> (&'a i64) -> &'a i64 {}",
    );
    let marker = key(&interface, "CallableMarker");
    let hrtb = Type::Callable {
        lifetime_binders: 1,
        parameters: vec![Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        }],
        result: Box::new(Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        }),
        effects: grandiose_stage0::EffectRow::empty(),
        invocation: grandiose_stage0::Quantity::ONCE,
    };
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: marker,
            arguments: vec![],
        },
        subject: hrtb,
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");

    let leaked_outer = Type::Callable {
        lifetime_binders: 1,
        parameters: vec![Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Generic(77),
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        }],
        result: Box::new(Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Generic(77),
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        }),
        effects: grandiose_stage0::EffectRow::empty(),
        invocation: grandiose_stage0::Quantity::ONCE,
    };
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: marker,
            arguments: vec![],
        },
        subject: leaked_outer,
    });
    assert!(matches!(answer, TraitAnswer::NoSolution), "{answer:#?}");
}

#[test]
fn tabled_solver_normalizes_associated_projections_in_where_obligations() {
    let (interface, signatures) = signatures(
        "trait Source { type Item; } trait Consume<T> {} trait Ready {} struct Value {} impl Source for Value { type Item = i64; } impl Consume<i64> for Value {} impl Ready for Value where Value: Consume< <Value as Source>::Item > {}",
    );
    let ready = key(&interface, "Ready");
    let value = key(&interface, "Value");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: value,
            arguments: vec![],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn failed_projection_does_not_refute_the_outer_trait_goal() {
    let (interface, signatures) = signatures(
        "trait Source { type Item; } trait Consume<T> {} struct Value {} impl !Source for Value {}",
    );
    let source = key(&interface, "Source");
    let consume = key(&interface, "Consume");
    let value = key(&interface, "Value");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: consume,
            arguments: vec![GenericArgument::Type(Type::Projection {
                subject: Box::new(Type::Nominal {
                    definition: value,
                    arguments: vec![],
                }),
                trait_definition: source,
                trait_arguments: vec![],
                name: "Item".into(),
                item_arguments: vec![],
            })],
        },
        subject: Type::Nominal {
            definition: value,
            arguments: vec![],
        },
    });
    assert_eq!(answer, TraitAnswer::NoSolution);
}

#[test]
fn tabled_solver_binds_lifetime_parameters_in_implementation_heads() {
    let (interface, signatures) = signatures("trait Marker {} impl<'a> Marker for &'a i64 {}");
    let marker = key(&interface, "Marker");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: marker,
            arguments: vec![],
        },
        subject: Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn tabled_solver_substitutes_structural_const_impl_binders_into_where_obligations() {
    let (interface, signatures) = signatures(
        "trait Marker {} trait Ready {} struct Tag<n: u32> {} impl<n: u32> Marker for Tag<n> {} impl<n: u32> Ready for Tag<n> where Tag<n>: Marker {}",
    );
    let tag = key(&interface, "Tag");
    let ready = key(&interface, "Ready");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: tag,
            arguments: vec![Type::ConstU32(7)],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn tabled_solver_matches_structural_const_trait_arguments() {
    let (interface, signatures) = signatures(
        "trait Capacity<n: u32> {} struct Tag<n: u32> {} impl<n: u32> Capacity<n> for Tag<n> {}",
    );
    let capacity = key(&interface, "Capacity");
    let tag = key(&interface, "Tag");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: capacity,
            arguments: vec![GenericArgument::ConstU32(7)],
        },
        subject: Type::Nominal {
            definition: tag,
            arguments: vec![Type::ConstU32(7)],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn trait_solver_rejects_cross_kind_const_substitution() {
    let (interface, signatures) = signatures(
        "trait Capacity<n: u32> {} struct Tag<n: u32> {} impl<n: u32> Capacity<n> for Tag<n> {}",
    );
    let capacity = key(&interface, "Capacity");
    let tag = key(&interface, "Tag");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: capacity,
            // The spelling shares a numeric-looking value with the subject's
            // `u32` argument, but the argument kind is Quantity and may not
            // bind the implementation's `u32` trait slot.
            arguments: vec![GenericArgument::ConstQuantity(
                grandiose_stage0::Quantity::ONCE,
            )],
        },
        subject: Type::Nominal {
            definition: tag,
            arguments: vec![Type::ConstU32(1)],
        },
    });
    assert!(matches!(answer, TraitAnswer::NoSolution), "{answer:#?}");
}

#[test]
fn tabled_solver_does_not_bind_const_impl_binders_to_ordinary_types() {
    let (interface, signatures) =
        signatures("trait Ready {} struct Tag<n: u32> {} impl<n: u32> Ready for Tag<n> {}");
    let tag = key(&interface, "Tag");
    let ready = key(&interface, "Ready");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        // This cannot be produced by the elaborator, which rejects ordinary
        // types in const slots. Keep the solver defensive at its public API
        // boundary too.
        subject: Type::Nominal {
            definition: tag,
            arguments: vec![Type::Scalar(ScalarType::I64)],
        },
    });
    assert_eq!(answer, TraitAnswer::NoSolution);
}

#[test]
fn tabled_solver_distinguishes_negative_evidence_and_missing_evidence() {
    let (interface, signatures) =
        signatures("trait Ready {} struct Box<T> {} impl !Ready for Box<Text> {}");
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let mut solver = TraitSolver::new(&signatures);
    let relation = ElaboratedTraitReference {
        definition: ready,
        arguments: vec![],
    };
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: relation.clone(),
            subject: Type::Nominal {
                definition: boxed,
                arguments: vec![Type::Scalar(ScalarType::Text)],
            },
        }),
        TraitAnswer::Refuted { .. }
    ));
    assert_eq!(
        solver.solve(TraitGoal {
            relation,
            subject: Type::Nominal {
                definition: boxed,
                arguments: vec![Type::Scalar(ScalarType::I64)],
            },
        }),
        TraitAnswer::NoSolution
    );
}

#[test]
fn ordinary_recursive_goal_cycles_are_ambiguous_not_successful() {
    let (interface, signatures) = signatures("trait Loop {} impl<T> Loop for T where T: Loop {}");
    let loop_trait = key(&interface, "Loop");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: loop_trait,
            arguments: vec![],
        },
        subject: Type::Scalar(ScalarType::I64),
    });
    assert_eq!(answer, TraitAnswer::Ambiguous);
}

#[test]
fn negative_impls_must_prove_their_where_bounds_before_refuting_a_goal() {
    let (interface, signatures) = signatures(
        "trait Marker {} trait Ready {} struct Box<T> {} impl<T> !Ready for Box<T> where T: Marker {}",
    );
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![Type::Scalar(ScalarType::I64)],
        },
    };
    assert_eq!(
        TraitSolver::new(&signatures).solve(goal),
        TraitAnswer::NoSolution
    );
}

#[test]
fn associated_type_normalization_uses_the_selected_impl_substitution() {
    let (interface, signatures) = signatures(
        "trait Iterator { type Item; } struct Range<T> {} impl<T> Iterator for Range<T> { type Item = T; }",
    );
    let iterator = key(&interface, "Iterator");
    let range = key(&interface, "Range");
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: iterator,
                arguments: vec![],
            },
            subject: Type::Nominal {
                definition: range,
                arguments: vec![Type::Scalar(ScalarType::Text)],
            },
        },
        "Item",
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::Text),
            ..
        }
    ));
}
#[test]
fn associated_type_application_normalizes_item_generic_arguments() {
    let (interface, signatures) =
        signatures("trait Apply { type Output<T>; } impl Apply for i64 { type Output<T> = T; }");
    let apply = key(&interface, "Apply");
    let answer = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: apply,
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Output",
        &[Type::Scalar(ScalarType::Text)],
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::Text),
            ..
        }
    ));

    let wrong_arity = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: apply,
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Output",
    );
    assert!(matches!(
        wrong_arity,
        TraitProjectionAnswer::AssociatedTypeArity {
            expected: 1,
            found: 0,
            ..
        }
    ));
}

#[test]
fn associated_type_normalization_recurses_through_selected_projections() {
    let (interface, signatures) = signatures(
        "trait Source { type Item; } trait Wrapper { type Item; } struct Value {} impl Source for Value { type Item = Text; } impl Wrapper for Value { type Item = <Value as Source>::Item; }",
    );
    let wrapper = key(&interface, "Wrapper");
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: wrapper,
                arguments: vec![],
            },
            subject: Type::Nominal {
                definition: key(&interface, "Value"),
                arguments: vec![],
            },
        },
        "Item",
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::Text),
            ..
        }
    ));
}

#[test]
fn associated_type_normalization_reduces_projections_in_the_trait_head() {
    let (interface, signatures) = signatures(
        "trait Source { type Item; } trait Consume<T> { type Output; } struct Value {} impl Source for Value { type Item = i64; } impl Consume<i64> for Value { type Output = Text; }",
    );
    let source = key(&interface, "Source");
    let consume = key(&interface, "Consume");
    let value = key(&interface, "Value");
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: consume,
                arguments: vec![GenericArgument::Type(Type::Projection {
                    subject: Box::new(Type::Nominal {
                        definition: value,
                        arguments: vec![],
                    }),
                    trait_definition: source,
                    trait_arguments: vec![],
                    name: "Item".into(),
                    item_arguments: vec![],
                })],
            },
            subject: Type::Nominal {
                definition: value,
                arguments: vec![],
            },
        },
        "Output",
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::Text),
            ..
        }
    ));
}

#[test]
fn recursive_associated_type_normalization_is_rejected() {
    let (interface, signatures) = signatures(
        "trait Loop { type Item; } struct Value {} impl Loop for Value { type Item = <Value as Loop>::Item; }",
    );
    let loop_trait = key(&interface, "Loop");
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: loop_trait,
                arguments: vec![],
            },
            subject: Type::Nominal {
                definition: key(&interface, "Value"),
                arguments: vec![],
            },
        },
        "Item",
    );
    assert_eq!(answer, TraitProjectionAnswer::RecursiveProjection);
}

#[test]
fn associated_effect_row_normalization_recurses_through_selected_projections() {
    let (interface, signatures) = signatures(
        "effect Trace { note(); } trait Source { type Effects: EffectRow; } trait Wrapper { type Effects: EffectRow; } struct Value {} impl Source for Value { type Effects = {Trace}; } impl Wrapper for Value { type Effects = {<Value as Source>::Effects}; }",
    );
    let wrapper = key(&interface, "Wrapper");
    let value = key(&interface, "Value");
    let trace = key(&interface, "Trace");
    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: wrapper,
                arguments: vec![],
            },
            subject: Type::Nominal {
                definition: value,
                arguments: vec![],
            },
        },
        "Effects",
        &[],
    );
    assert!(matches!(
        answer,
        TraitEffectRowProjectionAnswer::Normalized { row, .. }
            if row == grandiose_stage0::EffectRow::closed([trace])
    ));
}

#[test]
fn recursive_associated_effect_row_normalization_is_rejected() {
    let (interface, signatures) = signatures(
        "trait Loop { type Effects: EffectRow; } struct Value {} impl Loop for Value { type Effects = {<Value as Loop>::Effects}; }",
    );
    let loop_trait = key(&interface, "Loop");
    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: loop_trait,
                arguments: vec![],
            },
            subject: Type::Nominal {
                definition: key(&interface, "Value"),
                arguments: vec![],
            },
        },
        "Effects",
        &[],
    );
    assert_eq!(answer, TraitEffectRowProjectionAnswer::RecursiveProjection,);
}

#[test]
fn method_selection_substitutes_impl_and_method_generic_arguments() {
    let (interface, signatures) = signatures(
        "trait Convert<T> { fn convert<U>(value: T, other: U) -> (T, U); } struct Box<T> {} impl<T> Convert<T> for Box<T> { fn convert<U>(value: T, other: U) -> (T, U) { (value, other) } }",
    );
    let convert = key(&interface, "Convert");
    let boxed = key(&interface, "Box");
    let answer = TraitSolver::new(&signatures).select_method(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: convert,
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            },
            subject: Type::Nominal {
                definition: boxed,
                arguments: vec![Type::Scalar(ScalarType::I64)],
            },
        },
        "convert",
        &[Type::Scalar(ScalarType::Text)],
    );
    let implementation = interface
        .definitions
        .iter()
        .find(|definition| definition.kind == grandiose_stage0::DeclarationKind::Implementation)
        .expect("implementation definition");
    assert!(matches!(
        answer,
        TraitMethodAnswer::Selected { method, ref signature, .. }
            if method == implementation_method_key(implementation.key, "convert")
                && signature.parameters == vec![Type::Scalar(ScalarType::I64), Type::Scalar(ScalarType::Text)]
                && signature.result == Type::Tuple(vec![Type::Scalar(ScalarType::I64), Type::Scalar(ScalarType::Text)])
    ));
}
