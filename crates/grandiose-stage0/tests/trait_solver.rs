use grandiose_stage0::{
    DeclarationScan, DefKey, ElaboratedInterface, ElaboratedTraitReference, FileKey, InterfaceSet,
    LexedFile, PackageKey, ScalarType, TraitAnswer, TraitGoal, TraitProjectionAnswer, TraitSolver,
    Type,
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
