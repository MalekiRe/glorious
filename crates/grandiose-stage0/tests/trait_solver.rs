use std::collections::BTreeSet;

use grandiose_stage0::{
    ConstKind, DeclarationScan, DefKey, DefinitionIndex, DefinitionNamespace, EffectRow,
    EffectTail, ElaboratedInterface, ElaboratedTraitReference, FileKey, GenericArgument,
    InterfaceSet, LexedFile, Lifetime, ModuleKey, Mutability, PackageInterface, PackageKey,
    Quantity, ResolutionState, ScalarType, TraitAnswer, TraitCandidateExplanation,
    TraitCandidateRejection, TraitConstProjectionAnswer, TraitCyclePolicy,
    TraitEffectRowProjectionAnswer, TraitExplanationTerminal, TraitGoal, TraitMethodAnswer,
    TraitProjectionAnswer, TraitSelectionExplanation, TraitSolver, TraitSolverLimits, Type,
    implementation_method_key, intrinsic_callable_trait_definition,
    intrinsic_label_trait_definition, intrinsic_runs_in_trait_definition,
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
fn associated_result_guarantees_are_available_to_generic_graph_consumers() {
    let (interface, signatures) = signatures("trait Eq {} trait Hash {} trait Graph { type Node: Eq + Hash + Use<[0,*]>; }");
    let owner = TraitGoal { subject: Type::Generic(0), relation: ElaboratedTraitReference { definition: key(&interface, "Graph"), arguments: vec![] } };
    let node = Type::Projection { subject: Box::new(owner.subject.clone()), trait_definition: owner.relation.definition,
        trait_arguments: vec![], name: "Node".into(), item_generic_kinds: vec![], item_arguments: vec![] };
    let solver = TraitSolver::new(&signatures);
    for name in ["Eq", "Hash"] {
        let goal = TraitGoal { subject: node.clone(), relation: ElaboratedTraitReference { definition: key(&interface, name), arguments: vec![] } };
        assert!(matches!(solver.solve_with_assumptions(goal.clone(), &[owner.clone()]), TraitAnswer::Proven { .. }));
        assert_eq!(solver.solve_with_assumptions(goal, &[]), TraitAnswer::NoSolution);
    }
    assert_eq!(solver.principal_use_with_assumptions(&node, &[owner]), Some(Quantity::UNRESTRICTED));
    assert_eq!(solver.principal_use_with_assumptions(&node, &[]), None);
}

#[test]
fn imported_defaulted_gat_domains_require_exact_outlives_evidence() {
    let library = linked_interface("library@0.1.0", "crate", r#"
        pub trait Family { type Item<'a> where Self: 'a = &'a Self; }
        pub struct Owner<'a> { pub value: &'a i64 }
        impl<'a> Family for Owner<'a> {}
    "#);
    let consumer = linked_interface("gat-domain-consumer@0.1.0", "crate", "use library::{Family,Owner}; fn lend<'a,'b>(value: &'b Owner<'a>) -> <Owner<'a> as Family>::Item<'b>; ");
    let (_, signatures) = linked_signatures(&[library.clone(), consumer]);
    let owner = Type::Nominal { definition: key(&library, "Owner"), arguments: vec![GenericArgument::Lifetime(Lifetime::Generic(0))] };
    let goal = TraitGoal { subject: owner.clone(), relation: ElaboratedTraitReference { definition: key(&library, "Family"), arguments: vec![] } };
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(solver.normalize_associated_type_application(goal.clone(), "Item", &[GenericArgument::Lifetime(Lifetime::Generic(1))]), TraitProjectionAnswer::NoSolution);
    solver.set_outlives_assumptions(vec![grandiose_stage0::OutlivesPredicate::Region { longer: Lifetime::Generic(0), shorter: Lifetime::Generic(1) }]);
    assert!(matches!(solver.normalize_associated_type_application(goal.clone(), "Item", &[GenericArgument::Lifetime(Lifetime::Generic(1))]),
        TraitProjectionAnswer::Normalized { ty: Type::Reference { lifetime: Lifetime::Generic(1), referent, .. }, .. } if *referent == owner));
    solver.set_outlives_assumptions(vec![]);
    assert_eq!(solver.normalize_associated_type_application(goal, "Item", &[GenericArgument::Lifetime(Lifetime::Generic(1))]), TraitProjectionAnswer::NoSolution);
}

#[test]
fn gat_item_lifetime_holes_are_substitutions_not_domain_evidence() {
    let (interface, signatures) = signatures(
        "trait View { type Item<'a>; type StaticItem<'a> where 'a: 'static; } impl View for i64 { type Item<'a> = &'a i64; type StaticItem<'a> = &'a i64 where 'a: 'static; }",
    );
    let goal = TraitGoal { subject: Type::Scalar(ScalarType::I64),
        relation: ElaboratedTraitReference { definition: key(&interface, "View"), arguments: vec![] } };
    let region = Lifetime::Infer(grandiose_stage0::types::LifetimeInferVar(0));
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(solver.normalize_associated_type_application_in_hrtb(
        goal.clone(), "Item", &[GenericArgument::Lifetime(region)], &[]),
        TraitProjectionAnswer::Normalized { ty: Type::Reference { lifetime, .. }, .. } if lifetime == region));
    assert_eq!(solver.normalize_associated_type_application_in_hrtb(
        goal.clone(), "StaticItem", &[GenericArgument::Lifetime(region)], &[]), TraitProjectionAnswer::NoSolution);
    assert!(matches!(solver.normalize_associated_type_application_in_hrtb(
        goal, "StaticItem", &[GenericArgument::Lifetime(Lifetime::Static)], &[]),
        TraitProjectionAnswer::Normalized { ty: Type::Reference { lifetime: Lifetime::Static, .. }, .. }));
}

#[test]
fn outlives_predicates_are_directional_transitive_and_kind_distinct() {
    use grandiose_stage0::OutlivesPredicate as P;
    let region = |index| Lifetime::Generic(index);
    let facts = vec![P::Region { longer: region(0), shorter: region(1) },
        P::Region { longer: region(1), shorter: region(2) }, P::Type { subject: Type::Generic(0), lifetime: region(0) }];
    assert!(P::Region { longer: region(0), shorter: region(2) }.proven_by(&facts));
    assert!(P::Type { subject: Type::Generic(0), lifetime: region(2) }.proven_by(&facts));
    assert!(!P::Region { longer: region(2), shorter: region(0) }.proven_by(&facts));
    assert!(!P::Type { subject: Type::Generic(1), lifetime: region(1) }.proven_by(&facts));
    assert!(!P::Region { longer: region(0), shorter: Lifetime::Static }.proven_by(&facts));
}

fn linked_interface(package: &str, module: &str, source: &str) -> PackageInterface {
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

fn linked_signatures(interfaces: &[PackageInterface]) -> (DefinitionIndex, ElaboratedInterface) {
    let index = DefinitionIndex::from_interfaces(interfaces.iter());
    let signatures = ElaboratedInterface::merge(
        interfaces
            .iter()
            .map(|interface| ElaboratedInterface::elaborate_with_index(interface, &index)),
    );
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    (index, signatures)
}

fn terminal(explanation: &TraitSelectionExplanation) -> Option<&TraitExplanationTerminal> {
    explanation.terminal.as_ref().or_else(|| {
        explanation.candidates.iter().find_map(|candidate| {
            let (TraitCandidateExplanation::Applicable { where_bounds, .. }
            | TraitCandidateExplanation::Structural {
                obligations: where_bounds,
                ..
            }
            | TraitCandidateExplanation::Rejected {
                reason:
                    TraitCandidateRejection::WhereBound {
                        outcomes: where_bounds,
                    },
                ..
            }) = candidate
            else {
                return None;
            };
            where_bounds
                .iter()
                .find_map(|bound| terminal(&bound.explanation))
        })
    })
}

#[test]
fn intrinsic_fn_evidence_is_tied_to_callable_shape_not_the_source_spelling() {
    let (interface, signatures) = signatures("trait Fn {}");
    let declared_fn = key(&interface, "Fn");
    let callable = Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Scalar(ScalarType::Bool)),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: intrinsic_callable_trait_definition(),
                arguments: vec![GenericArgument::Type(Type::Tuple(vec![Type::Scalar(
                    ScalarType::I64,
                )]))],
            },
            subject: callable.clone(),
        }),
        TraitAnswer::Proven { .. }
    ));
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: declared_fn,
                arguments: vec![],
            },
            subject: callable,
        }),
        TraitAnswer::NoSolution
    ));
}

#[test]
fn intrinsic_label_evidence_requires_an_escaping_callable_not_a_spelled_trait() {
    let (interface, signatures) = signatures("trait Label {}");
    let declared_label = key(&interface, "Label");
    let escape = Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Never),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: intrinsic_label_trait_definition(),
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            },
            subject: escape.clone(),
        }),
        TraitAnswer::Proven { .. }
    ));
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: declared_label,
                arguments: vec![],
            },
            subject: escape,
        }),
        TraitAnswer::NoSolution
    ));
}

#[test]
fn intrinsic_runs_in_requires_core_environment_evidence_not_a_source_trait_spelling() {
    let (interface, signatures) = signatures("trait RunsIn {}");
    let declared_runs_in = key(&interface, "RunsIn");
    let callable = Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Scalar(ScalarType::I64)),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: intrinsic_runs_in_trait_definition(),
                arguments: vec![],
            },
            subject: callable.clone(),
        }),
        TraitAnswer::NoSolution
    ));
    assert!(matches!(
        solver.solve(TraitGoal {
            relation: ElaboratedTraitReference {
                definition: declared_runs_in,
                arguments: vec![],
            },
            subject: callable,
        }),
        TraitAnswer::NoSolution
    ));
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
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn scoped_where_evidence_is_transitive_over_supertraits_without_leaking_globally() {
    let (interface, signatures) =
        signatures("trait Root {} trait Parent: Root {} struct Box<T> {}");
    let root = key(&interface, "Root");
    let parent = key(&interface, "Parent");
    let boxed = key(&interface, "Box");
    let subject = Type::Nominal {
        definition: boxed,
        arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    };
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: root,
            arguments: vec![],
        },
        subject: subject.clone(),
    };
    let assumption = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: parent,
            arguments: vec![],
        },
        subject,
    };
    let mut ordinary = TraitSolver::new(&signatures);
    assert!(matches!(
        ordinary.solve(goal.clone()),
        TraitAnswer::NoSolution
    ));
    let scoped = TraitSolver::new(&signatures).solve_with_assumptions(goal, &[assumption]);
    assert!(matches!(scoped, TraitAnswer::Proven { .. }), "{scoped:#?}");
}

#[test]
fn supertrait_method_and_associated_items_follow_canonical_instantiated_edges() {
    let (interface, signatures) = signatures(
        "trait Parent<T> { type Item; type Effects: EffectRow; const Width: u32; fn id(value: T) -> T; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { type Item = i64; type Effects = {}; const Width = 7; fn id(value: i64) -> i64 { value } } impl Child<i64> for i64 {}",
    );
    let child = key(&interface, "Child");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(
        solver.method_generic_kinds(&goal.relation, "id"),
        Some(vec![])
    );
    assert!(matches!(
        solver.select_method(goal.clone(), "id", &[]),
        TraitMethodAnswer::Selected { .. }
    ));
    assert!(matches!(
        solver.normalize_associated_type(goal.clone(), "Item"),
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::I64),
            ..
        }
    ));
    assert!(matches!(
        solver.normalize_associated_effect_row_application(goal.clone(), "Effects", &[]),
        TraitEffectRowProjectionAnswer::Normalized { ref row, .. } if row == &EffectRow::empty()
    ));
    assert!(matches!(
        solver.normalize_associated_const(goal, "Width", ConstKind::U32),
        TraitConstProjectionAnswer::Normalized {
            value: GenericArgument::ConstInteger(value),
            ..
        } if value.as_u32() == Some(7)
    ));
}

#[test]
fn inherited_method_selection_requires_the_requested_child_evidence() {
    let (interface, parent_only) = signatures(
        "trait Parent<T> { fn relay(value: i64) -> i64; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { fn relay(value: i64) -> i64 { value } }",
    );
    let child = key(&interface, "Child");
    let parent = key(&interface, "Parent");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    assert!(matches!(
        TraitSolver::new(&parent_only).select_method(goal.clone(), "relay", &[]),
        TraitMethodAnswer::NoSolution
    ));
    let parent_assumption = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: parent,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    assert!(matches!(
        TraitSolver::new(&parent_only).select_method_with_assumptions(
            goal,
            "relay",
            &[],
            &[parent_assumption],
        ),
        TraitMethodAnswer::NoSolution
    ));

    let (interface, negative_child) = signatures(
        "trait Parent<T> { fn relay(value: i64) -> i64; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { fn relay(value: i64) -> i64 { value } } impl !Child<i64> for i64 {}",
    );
    let child = key(&interface, "Child");
    let negative_goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    assert!(matches!(
        TraitSolver::new(&negative_child).select_method(negative_goal, "relay", &[]),
        TraitMethodAnswer::Refuted { .. }
    ));
}

#[test]
fn negative_child_trait_refutes_inherited_type_effect_and_const_projections() {
    let (interface, signatures) = signatures(
        "trait Parent<T> { type Item; type Effects: EffectRow; const Width: u32; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { type Item = i64; type Effects = {}; const Width = 7; } impl !Child<i64> for i64 {}",
    );
    let child = key(&interface, "Child");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.normalize_associated_type(goal.clone(), "Item"),
        TraitProjectionAnswer::Refuted { .. }
    ));
    assert!(matches!(
        solver.normalize_associated_effect_row_application(goal.clone(), "Effects", &[]),
        TraitEffectRowProjectionAnswer::Refuted { .. }
    ));
    assert!(matches!(
        solver.normalize_associated_const(goal, "Width", ConstKind::U32),
        TraitConstProjectionAnswer::Refuted { .. }
    ));
}

#[test]
fn parent_evidence_cannot_select_items_requested_through_an_unimplemented_child() {
    let (interface, signatures) = signatures(
        "trait Parent<T> { type Item; type Effects: EffectRow; const Width: u32; } trait Child<U>: Parent<U> {} impl Parent<i64> for i64 { type Item = i64; type Effects = {}; const Width = 7; }",
    );
    let child = key(&interface, "Child");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.normalize_associated_type(goal.clone(), "Item"),
        TraitProjectionAnswer::NoSolution
    ));
    assert!(matches!(
        solver.normalize_associated_effect_row_application(goal.clone(), "Effects", &[]),
        TraitEffectRowProjectionAnswer::NoSolution
    ));
    assert!(matches!(
        solver.normalize_associated_const(goal, "Width", ConstKind::U32),
        TraitConstProjectionAnswer::NoSolution
    ));
}

#[test]
fn parent_evidence_cannot_select_a_method_requested_through_an_unimplemented_child() {
    let (interface, signatures) = signatures(
        "trait Parent { fn identity(value: Self) -> Self; } trait Child: Parent {} impl Parent for i64 { fn identity(value: i64) -> i64 { value } }",
    );
    let child = key(&interface, "Child");
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(
        solver.select_method(
            TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: child,
                    arguments: vec![],
                },
                subject: Type::Scalar(ScalarType::I64),
            },
            "identity",
            &[],
        ),
        TraitMethodAnswer::NoSolution
    ));
}

#[test]
fn parent_lexical_evidence_cannot_select_an_inherited_child_method() {
    let (interface, signatures) = signatures(
        "trait Parent { fn identity(value: Self) -> Self; } trait Child: Parent {} impl Parent for i64 { fn identity(value: i64) -> i64 { value } }",
    );
    let parent = key(&interface, "Parent");
    let child = key(&interface, "Child");
    let subject = Type::Scalar(ScalarType::I64);
    let child_goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![],
        },
        subject: subject.clone(),
    };
    let parent_assumption = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: parent,
            arguments: vec![],
        },
        subject,
    };
    assert!(matches!(
        TraitSolver::new(&signatures).select_method_with_assumptions(
            child_goal,
            "identity",
            &[],
            &[parent_assumption],
        ),
        TraitMethodAnswer::NoSolution
    ));
}

#[test]
fn child_lexical_evidence_selects_an_inherited_blanket_method() {
    let (interface, signatures) = signatures(
        "trait Gate {} trait Parent<U> { fn relay(receiver: Self, value: i64) -> i64; } trait Child<U>: Parent<U> + Gate {} impl<T> Parent<i64> for T where T: Gate { fn relay(receiver: T, value: i64) -> i64 { value } }",
    );
    let child = key(&interface, "Child");
    let generic = Type::Generic(0);
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: child,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        subject: generic,
    };
    let answer = TraitSolver::new(&signatures).select_method_with_assumptions(
        goal.clone(),
        "relay",
        &[],
        &[goal],
    );
    assert!(matches!(answer, TraitMethodAnswer::Selected { .. }), "{answer:#?}");
}

#[test]
fn negative_child_evidence_refutes_an_inherited_method_request() {
    let (interface, signatures) = signatures(
        "trait Parent { fn identity(value: Self) -> Self; } trait Child: Parent {} impl Parent for i64 { fn identity(value: i64) -> i64 { value } } impl !Child for i64 {}",
    );
    let child = key(&interface, "Child");
    assert!(matches!(
        TraitSolver::new(&signatures).select_method(
            TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: child,
                    arguments: vec![],
                },
                subject: Type::Scalar(ScalarType::I64),
            },
            "identity",
            &[],
        ),
        TraitMethodAnswer::Refuted { .. }
    ));
}

#[test]
fn method_selection_uses_lexical_where_bounds_for_generic_impl_candidates() {
    let (interface, signatures) = signatures(
        "trait Gate {} trait Parent { fn identity(value: Self) -> Self; } impl<T> Parent for T where T: Gate { fn identity(value: T) -> T { value } }",
    );
    let parent = key(&interface, "Parent");
    let gate = key(&interface, "Gate");
    let generic = Type::Generic(0);
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: parent,
            arguments: vec![],
        },
        subject: generic.clone(),
    };
    let assumption = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: gate,
            arguments: vec![],
        },
        subject: generic,
    };
    assert!(matches!(
        TraitSolver::new(&signatures).select_method_with_assumptions(
            goal,
            "identity",
            &[],
            &[assumption],
        ),
        TraitMethodAnswer::Selected { .. }
    ));
}

#[test]
fn method_selection_preserves_supertrait_identity_through_cross_package_reexports() {
    let provider = linked_interface(
        "provider@0.1.0",
        "crate",
        "pub trait Parent { fn identity(value: i64) -> i64; } pub trait Child: Parent {} impl Parent for i64 { fn identity(value: i64) -> i64 { value } } impl Child for i64 {}",
    );
    let bridge = linked_interface("bridge@0.1.0", "crate", "pub use provider::Child;");
    let consumer = linked_interface("consumer@0.1.0", "crate", "use bridge::Child;");
    let (index, signatures) = linked_signatures(&[provider.clone(), bridge, consumer]);
    let child = key(&provider, "Child");
    let resolved = index.resolve_path(
        DefinitionNamespace::Trait,
        &ModuleKey {
            package: PackageKey("consumer@0.1.0".into()),
            path: "crate".into(),
        },
        &["bridge".into(), "Child".into()],
    );
    assert_eq!(resolved, ResolutionState::Resolved(child));
    assert!(matches!(
        TraitSolver::new(&signatures).select_method(
            TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: child,
                    arguments: vec![],
                },
                subject: Type::Scalar(ScalarType::I64),
            },
            "identity",
            &[],
        ),
        TraitMethodAnswer::Selected { .. }
    ));
}

#[test]
fn method_selection_fails_closed_for_assumption_only_method_evidence() {
    let (interface, signatures) = signatures("trait Parent { fn identity(value: Self) -> Self; }");
    let parent = key(&interface, "Parent");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: parent,
            arguments: vec![],
        },
        subject: Type::Generic(0),
    };
    assert_eq!(
        TraitSolver::new(&signatures).select_method_with_assumptions(
            goal.clone(),
            "identity",
            &[],
            &[goal],
        ),
        TraitMethodAnswer::NoSolution,
        "a forged lexical bound cannot become a codegen-capable implementation method"
    );
}

#[test]
fn method_selection_reports_ambiguous_duplicate_supertrait_methods() {
    let (interface, signatures) = signatures(
        "trait Left { fn identity(value: i64) -> i64; } trait Right { fn identity(value: i64) -> i64; } trait Child: Left + Right {} impl Left for i64 { fn identity(value: i64) -> i64 { value } } impl Right for i64 { fn identity(value: i64) -> i64 { value } } impl Child for i64 {}",
    );
    assert_eq!(
        TraitSolver::new(&signatures).select_method(
            TraitGoal {
                relation: ElaboratedTraitReference {
                    definition: key(&interface, "Child"),
                    arguments: vec![],
                },
                subject: Type::Scalar(ScalarType::I64),
            },
            "identity",
            &[],
        ),
        TraitMethodAnswer::Ambiguous
    );
}

#[test]
fn conflicting_inherited_items_remain_ambiguous() {
    let (interface, signatures) = signatures(
        "trait Left { type Item; } trait Right { type Item; } trait Child: Left + Right {} impl Left for i64 { type Item = i64; } impl Right for i64 { type Item = i64; } impl Child for i64 {}",
    );
    let child = key(&interface, "Child");
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: child,
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Item",
    );
    assert!(
        matches!(answer, TraitProjectionAnswer::Ambiguous),
        "{answer:?}"
    );
}

#[test]
fn solver_matches_alpha_equivalent_hrtb_heads_but_rejects_outer_lifetime_leaks() {
    let (interface, signatures) = signatures(
        "trait CallableMarker {} impl CallableMarker for for<'a> (&'a i64) -> &'a i64 {}",
    );
    let marker = key(&interface, "CallableMarker");
    let hrtb = Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
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
        safety: grandiose_stage0::Safety::Safe,
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
fn solver_instantiates_hrtb_heads_without_capturing_fresh_placeholders() {
    let (interface, signatures) = signatures(
        "trait CallableMarker {} impl<T> CallableMarker for for<'a> (&'a T) -> &'a T {}",
    );
    let marker = key(&interface, "CallableMarker");
    let callable = |referent: Type| Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 1,
        parameters: vec![Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(referent.clone()),
        }],
        result: Box::new(Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(referent),
        }),
        effects: grandiose_stage0::EffectRow::empty(),
        invocation: grandiose_stage0::Quantity::ONCE,
    };
    let goal = |subject| TraitGoal {
        relation: ElaboratedTraitReference {
            definition: marker,
            arguments: vec![],
        },
        subject,
    };
    let valid = TraitSolver::new(&signatures).solve(goal(callable(Type::Scalar(ScalarType::I64))));
    assert!(matches!(valid, TraitAnswer::Proven { .. }), "{valid:#?}");

    let escaped = Type::Reference {
        mutability: Mutability::Shared,
        lifetime: Lifetime::Bound { depth: 0, index: 0 },
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    let leaked = TraitSolver::new(&signatures).solve(goal(callable(escaped)));
    assert!(matches!(leaked, TraitAnswer::NoSolution), "{leaked:#?}");
}

#[test]
fn solver_rejects_hrtb_capture_hidden_in_nominal_and_associated_arguments() {
    let (interface, signatures) = signatures(
        "trait CallableMarker {} struct Wrap<T> {} impl<T> CallableMarker for for<'a> (&'a Wrap<T>) -> &'a Wrap<T> {} trait Apply { type Output<T>; } impl Apply for i64 { type Output<T> = T; }",
    );
    let marker = key(&interface, "CallableMarker");
    let wrap = key(&interface, "Wrap");
    let callable = |argument: Type| Type::Callable {
        safety: grandiose_stage0::Safety::Safe,
        lifetime_binders: 1,
        parameters: vec![Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Nominal {
                definition: wrap,
                arguments: vec![GenericArgument::Type(argument.clone())],
            }),
        }],
        result: Box::new(Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Nominal {
                definition: wrap,
                arguments: vec![GenericArgument::Type(argument)],
            }),
        }),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    let goal = |subject| TraitGoal {
        relation: ElaboratedTraitReference {
            definition: marker,
            arguments: vec![],
        },
        subject,
    };
    let valid = TraitSolver::new(&signatures).solve(goal(callable(Type::Scalar(ScalarType::I64))));
    assert!(matches!(valid, TraitAnswer::Proven { .. }), "{valid:#?}");

    let captured = Type::Reference {
        mutability: Mutability::Shared,
        lifetime: Lifetime::Bound { depth: 0, index: 0 },
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    let leaked = TraitSolver::new(&signatures).solve(goal(callable(captured.clone())));
    assert!(matches!(leaked, TraitAnswer::NoSolution), "{leaked:#?}");

    let apply = key(&interface, "Apply");
    let forged_item_argument = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: apply,
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Output",
        &[GenericArgument::Type(captured)],
    );
    assert_eq!(forged_item_argument, TraitProjectionAnswer::NoSolution);
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
                item_generic_kinds: vec![],
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
            arguments: vec![GenericArgument::ConstInteger(7u32.into())],
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
            arguments: vec![GenericArgument::ConstInteger(7u32.into())],
        },
        subject: Type::Nominal {
            definition: tag,
            arguments: vec![GenericArgument::ConstInteger(7u32.into())],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn tabled_solver_substitutes_quantity_binders_without_aliasing_intervals() {
    let (interface, signatures) = signatures(
        "trait Budget<q: Quantity> {} struct Packet<q: Quantity> {} impl<q: Quantity> Budget<q> for Packet<q> {}",
    );
    let budget = key(&interface, "Budget");
    let packet = key(&interface, "Packet");
    let accepted = Quantity::new(1, Some(2)).unwrap();
    let relation = |quantity| ElaboratedTraitReference {
        definition: budget,
        arguments: vec![GenericArgument::ConstQuantity(quantity)],
    };
    let subject = Type::Nominal {
        definition: packet,
        arguments: vec![GenericArgument::ConstQuantity(accepted)],
    };
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: relation(accepted),
        subject: subject.clone(),
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
    let rejected = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: relation(Quantity::new(1, Some(3)).unwrap()),
        subject,
    });
    assert_eq!(rejected, TraitAnswer::NoSolution);
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
            arguments: vec![GenericArgument::ConstInteger(1u32.into())],
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
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
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
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
            },
        }),
        TraitAnswer::Refuted { .. }
    ));
    assert_eq!(
        solver.solve(TraitGoal {
            relation,
            subject: Type::Nominal {
                definition: boxed,
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
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
fn recursive_where_bound_explanations_record_inductive_cycle_policy() {
    let (interface, signatures) = signatures(
        "trait Left {} trait Right {} impl<T> Left for T where T: Right {} impl<T> Right for T where T: Left {}",
    );
    let left = key(&interface, "Left");
    let explanation = TraitSolver::new(&signatures).explain(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: left,
            arguments: vec![],
        },
        subject: Type::Scalar(ScalarType::I64),
    });
    assert_eq!(
        explanation.answer,
        TraitAnswer::Ambiguous,
        "{explanation:#?}"
    );
    assert!(matches!(
        terminal(&explanation),
        Some(TraitExplanationTerminal::OrdinaryCycle {
            policy: TraitCyclePolicy::Inductive,
            ..
        })
    ));
}

#[test]
fn structurally_decreasing_recursive_where_bounds_remain_productive() {
    let (interface, signatures) = signatures(
        "trait Ready {} struct Box<T> {} impl Ready for i64 {} impl<T> Ready for Box<T> where T: Ready {}",
    );
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let subject = Type::Nominal {
        definition: boxed,
        arguments: vec![GenericArgument::Type(Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        })],
    };
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject,
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn expanding_recursive_where_bounds_propagate_depth_overflow_not_ambiguity() {
    let (interface, signatures) =
        signatures("trait Grow {} struct Box<T> {} impl<T> Grow for T where Box<T>: Grow {}");
    let grow = key(&interface, "Grow");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: grow,
            arguments: vec![],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    let limits = TraitSolverLimits {
        max_depth: 3,
        max_steps: 32,
    };
    let answer = TraitSolver::with_limits(&signatures, limits.clone()).solve(goal.clone());
    assert_eq!(answer, TraitAnswer::Overflow);
    let explanation = TraitSolver::with_limits(&signatures, limits).explain(goal);
    assert_eq!(
        explanation.answer,
        TraitAnswer::Overflow,
        "{explanation:#?}"
    );
    assert!(matches!(
        terminal(&explanation),
        Some(TraitExplanationTerminal::DepthLimit { limit: 3 })
    ));
}

#[test]
fn recursive_where_bounds_report_step_limit_deterministically() {
    let (interface, signatures) =
        signatures("trait Grow {} struct Box<T> {} impl<T> Grow for T where Box<T>: Grow {}");
    let grow = key(&interface, "Grow");
    let goal = TraitGoal {
        relation: ElaboratedTraitReference {
            definition: grow,
            arguments: vec![],
        },
        subject: Type::Scalar(ScalarType::I64),
    };
    let limits = TraitSolverLimits {
        max_depth: 32,
        max_steps: 2,
    };
    let explanation = TraitSolver::with_limits(&signatures, limits).explain(goal);
    assert_eq!(
        explanation.answer,
        TraitAnswer::Overflow,
        "{explanation:#?}"
    );
    assert!(matches!(
        terminal(&explanation),
        Some(TraitExplanationTerminal::StepLimit { limit: 2 })
    ));
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
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    };
    assert_eq!(
        TraitSolver::new(&signatures).solve(goal),
        TraitAnswer::NoSolution
    );
}

#[test]
fn selection_explanations_name_head_mismatches() {
    let (interface, signatures) =
        signatures("trait Ready {} struct Box<T> {} impl Ready for i64 {}");
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let explanation = TraitSolver::new(&signatures).explain(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    });
    assert_eq!(explanation.answer, TraitAnswer::NoSolution);
    assert!(matches!(
        explanation.candidates.as_slice(),
        [TraitCandidateExplanation::Rejected {
            reason: TraitCandidateRejection::HeadMismatch,
            ..
        }]
    ));
}

#[test]
fn selection_explanations_retain_refuted_and_ambiguous_where_bound_outcomes() {
    let (refuted_interface, refuted_signatures) = signatures(
        "trait Gate {} trait Ready {} struct Box<T> {} impl !Gate for i64 {} impl<T> Ready for Box<T> where T: Gate {}",
    );
    let ready = key(&refuted_interface, "Ready");
    let boxed = key(&refuted_interface, "Box");
    let refuted = TraitSolver::new(&refuted_signatures).explain(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    });
    let TraitCandidateExplanation::Rejected {
        reason: TraitCandidateRejection::WhereBound { outcomes },
        ..
    } = &refuted.candidates[0]
    else {
        panic!("expected a refuted where-bound explanation: {refuted:#?}");
    };
    assert!(matches!(
        outcomes.as_slice(),
        [grandiose_stage0::TraitWhereBoundExplanation {
            outcome: TraitAnswer::Refuted { .. },
            ..
        }]
    ));

    let (interface, signatures) = signatures(
        "trait Gate {} trait Ready {} struct Box<T> {} impl<T> Gate for T where T: Gate {} impl<T> Ready for Box<T> where T: Gate {}",
    );
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let ambiguous = TraitSolver::new(&signatures).explain(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    });
    let TraitCandidateExplanation::Rejected {
        reason: TraitCandidateRejection::WhereBound { outcomes },
        ..
    } = &ambiguous.candidates[0]
    else {
        panic!("expected an ambiguous where-bound explanation: {ambiguous:#?}");
    };
    assert!(matches!(
        outcomes.as_slice(),
        [grandiose_stage0::TraitWhereBoundExplanation {
            outcome: TraitAnswer::Ambiguous,
            ..
        }]
    ));
}

#[test]
fn selection_explanations_retain_recursive_overflow_where_bound_outcomes() {
    let (interface, signatures) = signatures(
        "trait Gate {} trait Ready {} struct Box<T> {} impl Gate for i64 {} impl<T> Ready for Box<T> where T: Gate {}",
    );
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let explanation = TraitSolver::with_limits(
        &signatures,
        TraitSolverLimits {
            max_depth: 1,
            max_steps: 32,
        },
    )
    .explain(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    });
    let TraitCandidateExplanation::Rejected {
        reason: TraitCandidateRejection::WhereBound { outcomes },
        ..
    } = &explanation.candidates[0]
    else {
        panic!("expected an overflow where-bound explanation: {explanation:#?}");
    };
    assert!(matches!(
        outcomes.as_slice(),
        [grandiose_stage0::TraitWhereBoundExplanation {
            outcome: TraitAnswer::Overflow,
            ..
        }]
    ));
}

#[test]
fn trait_goal_queries_distinguish_nested_mixed_kind_nominal_arguments() {
    let (interface, signatures) = signatures("trait Ready {} struct Box<T> {}");
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let solver = TraitSolver::new(&signatures);
    let nested_goal = |argument: GenericArgument| TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ready,
            arguments: vec![argument.clone()],
        },
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Nominal {
                definition: boxed,
                arguments: vec![argument],
            })],
        },
    };
    let arguments = vec![
        GenericArgument::Type(Type::Scalar(ScalarType::I64)),
        GenericArgument::Lifetime(Lifetime::Static),
        GenericArgument::Lifetime(Lifetime::Generic(7)),
        GenericArgument::EffectRow(EffectRow::empty()),
        GenericArgument::EffectRow(EffectRow {
            effects: BTreeSet::new(),
            projections: vec![],
            tails: [EffectTail::Generic(3)].into_iter().collect(),
        }),
        GenericArgument::ConstInteger(7u32.into()),
        GenericArgument::ConstQuantity(Quantity::new(2, Some(5)).unwrap()),
    ];
    let fingerprints = arguments
        .into_iter()
        .map(|argument| solver.query(&nested_goal(argument)).fingerprint)
        .collect::<BTreeSet<_>>();
    assert_eq!(fingerprints.len(), 7, "mixed-kind goals must never alias");
}

#[test]
fn trait_solver_tables_do_not_alias_nested_nominal_argument_kinds() {
    let (interface, signatures) =
        signatures("trait Ready {} struct Box<T> {} impl Ready for Box<i64> {}");
    let ready = key(&interface, "Ready");
    let boxed = key(&interface, "Box");
    let relation = ElaboratedTraitReference {
        definition: ready,
        arguments: vec![],
    };
    let matching = TraitGoal {
        relation: relation.clone(),
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    };
    let adversarial = TraitGoal {
        relation,
        subject: Type::Nominal {
            definition: boxed,
            arguments: vec![GenericArgument::ConstQuantity(Quantity::ONCE)],
        },
    };
    let mut solver = TraitSolver::new(&signatures);
    assert!(matches!(solver.solve(matching), TraitAnswer::Proven { .. }));
    assert_eq!(solver.solve(adversarial), TraitAnswer::NoSolution);
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
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
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
fn associated_type_defaults_normalize_when_a_positive_impl_omits_the_item() {
    let (interface, signatures) =
        signatures("trait Source { type Item = Text; } struct Value {} impl Source for Value {}");
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Source"),
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
fn generic_associated_type_defaults_substitute_trait_and_item_binders() {
    let (interface, signatures) = signatures(
        "trait Convert<T> { type Output<U> = (T, U); } struct Value {} impl Convert<i64> for Value {}",
    );
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let answer = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Convert"),
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            },
            subject: Type::Nominal {
                definition: key(&interface, "Value"),
                arguments: vec![],
            },
        },
        "Output",
        &[GenericArgument::Type(Type::Scalar(ScalarType::Text))],
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Tuple(values),
            ..
        } if values == vec![Type::Scalar(ScalarType::I64), Type::Scalar(ScalarType::Text)]
    ));
}

#[test]
fn explicit_associated_type_definitions_override_trait_defaults() {
    let (interface, signatures) = signatures(
        "trait Source { type Item = Text; } struct Value {} impl Source for Value { type Item = i64; }",
    );
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let answer = TraitSolver::new(&signatures).normalize_associated_type(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Source"),
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
            ty: Type::Scalar(ScalarType::I64),
            ..
        }
    ));
}

#[test]
fn associated_effect_row_defaults_normalize_when_a_positive_impl_omits_the_item() {
    let (interface, signatures) = signatures(
        "effect Trace { note(); } trait Capability { type Effects: EffectRow = { Trace }; } struct Value {} impl Capability for Value {}",
    );
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Capability"),
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
    assert!(matches!(
        answer,
        TraitEffectRowProjectionAnswer::Normalized { row, .. }
            if row.effects.iter().any(|effect| effect.definition == key(&interface, "Trace"))
    ));
}

#[test]
fn associated_effect_rows_compose_prefixed_defaults_and_specializations_with_mixed_arguments() {
    let default_source = "effect Prefix<'a, e: EffectRow, T, n: u32> { note(); } effect Tail { note(); } trait Capability<'a, e: EffectRow, T, n: u32> { type Effects<'b, row: EffectRow, U, m: u32>: EffectRow = { Prefix<'b, row, U, m>, | e }; } struct Value {} impl<'a, e: EffectRow, T, n: u32> Capability<'a, e, T, n> for Value {}";
    let (interface, default_signatures) = signatures(default_source);
    let prefix = key(&interface, "Prefix");
    let tail = key(&interface, "Tail");
    let capability = key(&interface, "Capability");
    let value = key(&interface, "Value");
    let caller_row = EffectRow::closed_instances([grandiose_stage0::EffectInstance {
        definition: tail,
        arguments: vec![],
    }]);
    let answer = TraitSolver::new(&default_signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: capability,
                arguments: vec![
                    GenericArgument::Lifetime(Lifetime::Static),
                    GenericArgument::EffectRow(caller_row.clone()),
                    GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                    GenericArgument::ConstInteger(7u32.into()),
                ],
            },
            subject: Type::Nominal {
                definition: value,
                arguments: vec![],
            },
        },
        "Effects",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::Type(Type::Scalar(ScalarType::I64)),
            GenericArgument::ConstInteger(8u32.into()),
        ],
    );
    assert!(matches!(
        answer,
        TraitEffectRowProjectionAnswer::Normalized { row, .. }
            if row.tails.is_empty()
                && row.effects.iter().any(|effect| {
                    effect.definition == tail && effect.arguments.is_empty()
                })
                && row.effects.iter().any(|effect| {
                    effect.definition == prefix
                        && effect.arguments
                            == vec![
                                GenericArgument::Lifetime(Lifetime::Static),
                                GenericArgument::EffectRow(EffectRow::empty()),
                                GenericArgument::Type(Type::Scalar(ScalarType::I64)),
                                GenericArgument::ConstInteger(8u32.into()),
                            ]
                })
    ));

    let specialization_source = "effect Prefix<'a, e: EffectRow, T, n: u32> { note(); } effect Tail { note(); } trait Capability<'a, e: EffectRow, T, n: u32> { type Effects<'b, row: EffectRow, U, m: u32>: EffectRow = {}; } struct Value {} impl<'a, e: EffectRow, T, n: u32> Capability<'a, e, T, n> for Value { type Effects<'b, row: EffectRow, U, m: u32> = { Prefix<'b, row, U, m>, | e }; }";
    let (interface, signatures) = signatures(specialization_source);
    let prefix = key(&interface, "Prefix");
    let tail = key(&interface, "Tail");
    let capability = key(&interface, "Capability");
    let value = key(&interface, "Value");
    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: capability,
                arguments: vec![
                    GenericArgument::Lifetime(Lifetime::Static),
                    GenericArgument::EffectRow(EffectRow::closed_instances([
                        grandiose_stage0::EffectInstance {
                            definition: tail,
                            arguments: vec![],
                        },
                    ])),
                    GenericArgument::Type(Type::Scalar(ScalarType::Text)),
                    GenericArgument::ConstInteger(7u32.into()),
                ],
            },
            subject: Type::Nominal {
                definition: value,
                arguments: vec![],
            },
        },
        "Effects",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::Type(Type::Scalar(ScalarType::I64)),
            GenericArgument::ConstInteger(8u32.into()),
        ],
    );
    assert!(matches!(
        answer,
        TraitEffectRowProjectionAnswer::Normalized { row, .. }
            if row.tails.is_empty()
                && row.effects.iter().any(|effect| effect.definition == tail)
                && row.effects.iter().any(|effect| effect.definition == prefix)
    ));
}

#[test]
fn mixed_gat_projections_normalize_inside_where_obligations() {
    let (interface, signatures) = signatures(
        "effect Tail { note(); } trait Source { type Output<'b, row: EffectRow, U, m: u32>; } trait Consume<T> {} trait Ready {} struct Value {} impl Source for Value { type Output<'b, row: EffectRow, U, m: u32> = U; } impl Consume<i64> for Value {} impl Ready for Value where Value: Consume<<Value as Source>::Output<'static, {Tail}, i64, 8>> {}",
    );
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: key(&interface, "Ready"),
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: key(&interface, "Value"),
            arguments: vec![],
        },
    });
    assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:#?}");
}

#[test]
fn forged_interface_cannot_specialize_an_associated_row_with_different_kinds() {
    let (interface, mut signatures) = signatures(
        "trait Capability { type Effects<'a, row: EffectRow, T, n: u32>: EffectRow; } impl Capability for i64 { type Effects<'a, row: EffectRow, T, n: u32> = {}; }",
    );
    let implementation = signatures
        .definitions
        .values_mut()
        .find_map(|header| match header {
            grandiose_stage0::ElaboratedHeader::Implementation(implementation) => {
                Some(implementation)
            }
            _ => None,
        })
        .expect("fixture must contain an implementation");
    // This cannot be produced by source elaboration: it changes only the
    // implementation's final GAT slot to `Quantity`, leaving the declaration
    // at `u32`. A dependency interface must not gain a new specialization
    // surface merely by forging that metadata.
    implementation
        .associated_effect_rows
        .get_mut("Effects")
        .expect("fixture must define the row")
        .generic_kinds[3] = grandiose_stage0::GenericKind::Const(ConstKind::Quantity);

    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Capability"),
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Effects",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::Type(Type::Scalar(ScalarType::Text)),
            GenericArgument::ConstQuantity(Quantity::ONCE),
        ],
    );
    assert_eq!(answer, TraitEffectRowProjectionAnswer::NoSolution);
}

#[test]
fn forged_interface_cannot_reclassify_a_defaulted_effect_row_as_a_value_type() {
    let (interface, mut signatures) =
        signatures("trait Capability { type Effects: EffectRow = {}; } impl Capability for i64 {}");
    let trait_header = signatures
        .definitions
        .get_mut(&key(&interface, "Capability"))
        .expect("fixture trait must be frozen");
    let grandiose_stage0::ElaboratedHeader::Trait(trait_header) = trait_header else {
        panic!("fixture key must name a trait");
    };
    trait_header
        .associated_types
        .get_mut("Effects")
        .expect("fixture must declare the row")
        .effect_row = false;

    let answer = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Capability"),
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Effects",
        &[],
    );
    assert_eq!(answer, TraitEffectRowProjectionAnswer::NoSolution);
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
        &[GenericArgument::Type(Type::Scalar(ScalarType::Text))],
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
fn associated_item_applications_preserve_mixed_generic_kinds() {
    let (interface, signatures) = signatures(
        "trait Borrow { type View<'a, T, n: u32>; } impl Borrow for i64 { type View<'a, T, n: u32> = T; } trait Source { type Effects<'a, n: u32>: EffectRow; } impl Source for i64 { type Effects<'a, n: u32> = {}; }",
    );
    let subject = Type::Scalar(ScalarType::I64);
    let borrow = key(&interface, "Borrow");
    let view = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: borrow,
                arguments: vec![],
            },
            subject: subject.clone(),
        },
        "View",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::Type(Type::Scalar(ScalarType::Text)),
            GenericArgument::ConstInteger(7u32.into()),
        ],
    );
    assert!(matches!(
        view,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::Text),
            ..
        }
    ));
    let wrong_kind = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: borrow,
                arguments: vec![],
            },
            subject: subject.clone(),
        },
        "View",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::Type(Type::Scalar(ScalarType::Text)),
            GenericArgument::ConstQuantity(Quantity::ONCE),
        ],
    );
    assert_eq!(wrong_kind, TraitProjectionAnswer::NoSolution);

    let source = key(&interface, "Source");
    let effects = TraitSolver::new(&signatures).normalize_associated_effect_row_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: source,
                arguments: vec![],
            },
            subject,
        },
        "Effects",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::ConstInteger(9u32.into()),
        ],
    );
    assert!(matches!(
        effects,
        TraitEffectRowProjectionAnswer::Normalized { row, .. } if row == EffectRow::empty()
    ));
}

#[test]
fn generic_trait_heads_normalize_gats_for_lifetime_and_effect_row_arguments() {
    let (interface, signatures) = signatures(
        "effect Trace { note(); } trait Select<'a, e: EffectRow> { type Output<'b, row: EffectRow>; } impl<'a, e: EffectRow> Select<'a, e> for i64 { type Output<'b, row: EffectRow> = i64; }",
    );
    let trace = key(&interface, "Trace");
    let select = key(&interface, "Select");
    let row = EffectRow {
        effects: std::collections::BTreeSet::from([grandiose_stage0::EffectInstance {
            definition: trace,
            arguments: vec![],
        }]),
        projections: vec![],
        tails: Default::default(),
    };
    let answer = TraitSolver::new(&signatures).normalize_associated_type_application(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: select,
                arguments: vec![
                    GenericArgument::Lifetime(Lifetime::Static),
                    GenericArgument::EffectRow(row.clone()),
                ],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Output",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(row),
        ],
    );
    assert!(matches!(
        answer,
        TraitProjectionAnswer::Normalized {
            ty: Type::Scalar(ScalarType::I64),
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
                    item_generic_kinds: vec![],
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

    // A hostile frozen impl head can carry the projection directly rather
    // than reaching it through the public associated-item query.  The
    // coherence normalizer uses this boundary, so it must fail closed too.
    assert!(matches!(
        TraitSolver::new(&signatures).normalize_type(Type::Projection {
            subject: Box::new(Type::Nominal {
                definition: key(&interface, "Value"),
                arguments: vec![],
            }),
            trait_definition: loop_trait,
            trait_arguments: vec![],
            name: "Item".into(),
            item_generic_kinds: vec![],
            item_arguments: vec![],
        }),
        Err(answer) if *answer == TraitProjectionAnswer::RecursiveProjection
    ));
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

    assert!(matches!(
        TraitSolver::new(&signatures).normalize_effect_row(EffectRow {
            effects: Default::default(),
            projections: vec![grandiose_stage0::EffectRowProjection {
                subject: Box::new(Type::Nominal {
                    definition: key(&interface, "Value"),
                    arguments: vec![],
                }),
                trait_definition: loop_trait,
                trait_arguments: vec![],
                name: "Effects".into(),
                item_generic_kinds: vec![],
                item_arguments: vec![],
            }],
            tails: Default::default(),
        }),
        Err(answer) if *answer == TraitEffectRowProjectionAnswer::RecursiveProjection
    ));
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
                arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
            },
        },
        "convert",
        &[GenericArgument::Type(Type::Scalar(ScalarType::Text))],
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

#[test]
fn method_selection_preserves_mixed_method_generic_argument_kinds() {
    let (interface, signatures) = signatures(
        "struct Token<'a, e: EffectRow, n: u32, q: Quantity> {} trait Relay { fn relay<'a, e: EffectRow, n: u32, q: Quantity>(value: Token<'a, e, n, q>) -> Token<'a, e, n, q> / {| e}; } impl Relay for i64 { fn relay<'a, e: EffectRow, n: u32, q: Quantity>(value: Token<'a, e, n, q>) -> Token<'a, e, n, q> / {| e} { value } }",
    );
    let answer = TraitSolver::new(&signatures).select_method(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: key(&interface, "Relay"),
                arguments: vec![],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "relay",
        &[
            GenericArgument::Lifetime(Lifetime::Static),
            GenericArgument::EffectRow(EffectRow::empty()),
            GenericArgument::ConstInteger(7u32.into()),
            GenericArgument::ConstQuantity(Quantity::ONCE),
        ],
    );
    let token = key(&interface, "Token");
    assert!(
        matches!(
            answer,
            TraitMethodAnswer::Selected { ref signature, .. }
                if signature.parameters == vec![Type::Nominal {
                    definition: token,
                    arguments: vec![
                        GenericArgument::Lifetime(Lifetime::Static),
                        GenericArgument::EffectRow(EffectRow::empty()),
                        GenericArgument::ConstInteger(7u32.into()),
                        GenericArgument::ConstQuantity(Quantity::ONCE),
                    ],
                }]
                    && signature.result == Type::Nominal {
                        definition: token,
                        arguments: vec![
                            GenericArgument::Lifetime(Lifetime::Static),
                            GenericArgument::EffectRow(EffectRow::empty()),
                            GenericArgument::ConstInteger(7u32.into()),
                            GenericArgument::ConstQuantity(Quantity::ONCE),
                        ],
                    }
                    && signature.effects == EffectRow::empty()
        ),
        "{answer:#?}"
    );
}

#[test]
fn associated_constants_normalize_overrides_defaults_and_const_generics() {
    let (interface, signatures) = signatures(
        "trait Width<n: u32> { const Value: u32 = n + 1; } struct Box<n: u32> {} impl<n: u32> Width<n> for Box<n> {} impl Width<9> for i64 { const Value = 12; }",
    );
    let width = key(&interface, "Width");
    let boxed = key(&interface, "Box");
    let mut solver = TraitSolver::new(&signatures);
    let default = solver.normalize_associated_const(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: width,
                arguments: vec![GenericArgument::ConstInteger(7u32.into())],
            },
            subject: Type::Nominal {
                definition: boxed,
                arguments: vec![GenericArgument::ConstInteger(7u32.into())],
            },
        },
        "Value",
        ConstKind::U32,
    );
    assert!(matches!(
        default,
        TraitConstProjectionAnswer::Normalized {
            value: GenericArgument::ConstInteger(value),
            ..
        } if value.as_u32() == Some(8)
    ));
    let override_value = solver.normalize_associated_const(
        TraitGoal {
            relation: ElaboratedTraitReference {
                definition: width,
                arguments: vec![GenericArgument::ConstInteger(9u32.into())],
            },
            subject: Type::Scalar(ScalarType::I64),
        },
        "Value",
        ConstKind::U32,
    );
    assert!(matches!(
        override_value,
        TraitConstProjectionAnswer::Normalized {
            value: GenericArgument::ConstInteger(value),
            ..
        } if value.as_u32() == Some(12)
    ));
}

#[test]
fn associated_constants_recursively_normalize_nested_projection_values_and_cycles() {
    let (interface, signatures) = signatures(
        "trait First { const Value: u32; } trait Second { const Value: u32; } struct Chosen<n: u32> {} impl Second for i64 { const Value = 7; } impl First for i64 { const Value = <i64 as Second>::Value; } trait Loop { const Value: u32; } impl Loop for i64 { const Value = <i64 as Loop>::Value; }",
    );
    let first = key(&interface, "First");
    let looping = key(&interface, "Loop");
    let chosen = key(&interface, "Chosen");
    let nested = |trait_definition| GenericArgument::ConstProjection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition,
        trait_arguments: vec![],
        name: "Value".into(),
        kind: ConstKind::U32,
    };
    let mut solver = TraitSolver::new(&signatures);
    assert_eq!(
        solver.normalize_type(Type::Nominal {
            definition: chosen,
            arguments: vec![nested(first)],
        }),
        Ok(Type::Nominal {
            definition: chosen,
            arguments: vec![GenericArgument::ConstInteger(7u32.into())],
        }),
        "a selected associated const must recursively reduce its own projection value"
    );
    assert!(
        matches!(
            solver.normalize_type(Type::Nominal {
                definition: chosen,
                arguments: vec![nested(looping)],
            }),
            Err(answer) if *answer == TraitProjectionAnswer::RecursiveProjection
        ),
        "recursive associated const definitions must not leak as VM-facing structural terms"
    );
}

#[test]
fn auto_traits_structurally_traverse_source_nominals_and_type_forms() {
    let (interface, signatures) = signatures(
        "auto trait Sendish {} struct Pair<T> { left: T, right: T } enum Choice<T> { Empty, One(T), Named { value: T } } impl !Sendish for Text {}",
    );
    let sendish = key(&interface, "Sendish");
    let pair = key(&interface, "Pair");
    let choice = key(&interface, "Choice");
    let relation = ElaboratedTraitReference {
        definition: sendish,
        arguments: vec![],
    };
    let mut solver = TraitSolver::new(&signatures);
    for subject in [
        Type::Tuple(vec![
            Type::Scalar(ScalarType::I64),
            Type::Array(Box::new(Type::Scalar(ScalarType::Bool))),
        ]),
        Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Static,
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        },
        Type::Callable {
            safety: grandiose_stage0::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![Type::Scalar(ScalarType::I64)],
            result: Box::new(Type::Scalar(ScalarType::Bool)),
            effects: EffectRow::empty(),
            invocation: Quantity::ONCE,
        },
        Type::Nominal {
            definition: pair,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
        Type::Nominal {
            definition: choice,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
        },
    ] {
        let answer = solver.solve(TraitGoal {
            relation: relation.clone(),
            subject,
        });
        assert!(matches!(answer, TraitAnswer::Proven { .. }), "{answer:?}");
    }
    let answer = solver.solve(TraitGoal {
        relation,
        subject: Type::Nominal {
            definition: pair,
            arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::Text))],
        },
    });
    assert!(matches!(answer, TraitAnswer::NoSolution), "{answer:?}");
}

#[test]
fn auto_trait_recursive_nominals_are_coinductive_but_explicit_negatives_win() {
    let (interface, signatures) = signatures(
        "auto trait Sendish {} struct Link { next: &Link } struct Denied {} impl !Sendish for Denied {}",
    );
    let sendish = key(&interface, "Sendish");
    let relation = ElaboratedTraitReference {
        definition: sendish,
        arguments: vec![],
    };
    let mut solver = TraitSolver::new(&signatures);
    let recursive = solver.explain(TraitGoal {
        relation: relation.clone(),
        subject: Type::Nominal {
            definition: key(&interface, "Link"),
            arguments: vec![],
        },
    });
    assert!(
        matches!(recursive.answer, TraitAnswer::Proven { .. }),
        "{recursive:#?}"
    );
    assert!(matches!(
        terminal(&recursive),
        Some(TraitExplanationTerminal::OrdinaryCycle {
            policy: TraitCyclePolicy::CoinductiveAuto,
            ..
        })
    ));
    let denied = solver.solve(TraitGoal {
        relation,
        subject: Type::Nominal {
            definition: key(&interface, "Denied"),
            arguments: vec![],
        },
    });
    assert!(matches!(denied, TraitAnswer::Refuted { .. }), "{denied:?}");
}

#[test]
fn ordinary_trait_cycles_remain_inductive() {
    let (interface, signatures) = signatures(
        "trait Ordinary {} struct Link { next: &Link } impl Ordinary for Link where Link: Ordinary {}",
    );
    let ordinary = key(&interface, "Ordinary");
    let answer = TraitSolver::new(&signatures).solve(TraitGoal {
        relation: ElaboratedTraitReference {
            definition: ordinary,
            arguments: vec![],
        },
        subject: Type::Nominal {
            definition: key(&interface, "Link"),
            arguments: vec![],
        },
    });
    assert!(matches!(answer, TraitAnswer::Ambiguous), "{answer:?}");
}
