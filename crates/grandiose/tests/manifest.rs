use grandiose::ast::ConstKind;
use grandiose::{
    AssociatedItemKind, GenericParameterKind, IntrinsicRole, ManifestAssociatedItem, ManifestTrait,
    TraitPolicy, TrustedTraitManifest, compile_source_to_bytecode,
    compile_source_to_bytecode_with_manifest, compile_source_to_phases_with_manifest,
};
use grandiose_vm::{Value, Vm, verify};

fn item(name: &str, kind: AssociatedItemKind) -> ManifestAssociatedItem {
    ManifestAssociatedItem {
        name: name.into(),
        parameters: vec![],
        kind,
    }
}

fn intrinsic(id: u64, display_name: &str, role: IntrinsicRole) -> ManifestTrait {
    use GenericParameterKind::{Const, Lifetime, Type};
    let (parameters, associated_items, policy) = match role {
        IntrinsicRole::Drop => (vec![], vec![], TraitPolicy::DedicatedDrop),
        IntrinsicRole::Use => (
            vec![Const(ConstKind::Quantity)],
            vec![],
            TraitPolicy::DedicatedUse,
        ),
        IntrinsicRole::Fn => (
            vec![Type],
            vec![
                item("Output", AssociatedItemKind::Type),
                item("Effects", AssociatedItemKind::EffectRow),
            ],
            TraitPolicy::CompilerSealed,
        ),
        IntrinsicRole::RunsIn => (
            vec![Type, Type],
            vec![item("After", AssociatedItemKind::Type)],
            TraitPolicy::CompilerSealed,
        ),
        IntrinsicRole::Label => (vec![Type], vec![], TraitPolicy::CompilerSealed),
        IntrinsicRole::Environment => (vec![Lifetime], vec![], TraitPolicy::CompilerSealed),
    };
    ManifestTrait {
        id,
        display_name: display_name.into(),
        parameters,
        associated_items,
        policy,
        role: Some(role),
    }
}

fn base_declarations() -> Vec<ManifestTrait> {
    vec![
        intrinsic(1, "Drop", IntrinsicRole::Drop),
        intrinsic(2, "Use", IntrinsicRole::Use),
        intrinsic(3, "Fn", IntrinsicRole::Fn),
        intrinsic(4, "RunsIn", IntrinsicRole::RunsIn),
        intrinsic(5, "Label", IntrinsicRole::Label),
        intrinsic(6, "Environment", IntrinsicRole::Environment),
    ]
}

fn external(
    id: u64,
    name: &str,
    parameters: Vec<GenericParameterKind>,
    associated_items: Vec<ManifestAssociatedItem>,
    policy: TraitPolicy,
) -> ManifestTrait {
    ManifestTrait {
        id,
        display_name: name.into(),
        parameters,
        associated_items,
        policy,
        role: None,
    }
}

fn manifest_with(entries: impl IntoIterator<Item = ManifestTrait>) -> TrustedTraitManifest {
    let mut declarations = base_declarations();
    declarations.extend(entries);
    TrustedTraitManifest::new(declarations).unwrap()
}

#[test]
fn sealed_manifest_traits_reject_both_polarities_and_reserved_redeclarations() {
    let manifest = manifest_with([external(
        100,
        "Sealed",
        vec![],
        vec![],
        TraitPolicy::CompilerSealed,
    )]);
    for source in [
        "struct Local{marker:i64} impl Sealed for Local{} main()->{()}",
        "struct Local{marker:i64} impl !Sealed for Local{} main()->{()}",
    ] {
        let errors = compile_source_to_bytecode_with_manifest("sealed.glorious", source, &manifest)
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
                    && error.message
                        == "source impls for sealed external trait `Sealed` are unsupported"
            }),
            "{errors:#?}"
        );
    }
    let errors = compile_source_to_bytecode_with_manifest(
        "reserved.glorious",
        "trait Sealed{} main()->{()}",
        &manifest,
    )
    .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.span.is_some()
                && error.message == "reserved external trait `Sealed` cannot be redeclared"
        }),
        "{errors:#?}"
    );
}

#[test]
fn manifest_and_source_order_preserve_diagnostic_identity() {
    let sealed = external(100, "Sealed", vec![], vec![], TraitPolicy::CompilerSealed);
    let foreign = external(101, "Foreign", vec![], vec![], TraitPolicy::ExternalOpen);
    let first_manifest = manifest_with([sealed.clone(), foreign.clone()]);
    let mut reversed_declarations = base_declarations();
    reversed_declarations.extend([foreign, sealed]);
    reversed_declarations.reverse();
    let reversed_manifest = TrustedTraitManifest::new(reversed_declarations).unwrap();
    let first = r#"
        struct Local{marker:i64}
        impl Sealed for Local{}
        impl Foreign for i64{}
        main()->{()}
    "#;
    let reordered = r#"
        main()->{()}
        impl Foreign for i64{}
        impl Sealed for Local{}
        struct Local{marker:i64}
    "#;
    let signature = |source: &str, manifest: &TrustedTraitManifest| {
        let mut errors =
            compile_source_to_bytecode_with_manifest("manifest-errors.glorious", source, manifest)
                .unwrap_err()
                .into_iter()
                .map(|error| {
                    assert!(error.span.is_some());
                    (error.code, error.title, error.message)
                })
                .collect::<Vec<_>>();
        errors.sort();
        errors
    };
    assert_eq!(
        signature(first, &first_manifest),
        signature(reordered, &reversed_manifest)
    );
}

#[test]
fn source_spelling_has_no_manifest_authority_and_contexts_do_not_leak_identity() {
    let trusted = TrustedTraitManifest::trusted_default();
    let local_spelling = r#"
        trait CompilerSealed<Arg> {}
        struct Local { marker:i64 }
        impl CompilerSealed<i64> for Local {}
        pass<T>(value:T)->T where T:CompilerSealed<i64>{value}
        answer(value:Local)->Local{pass(value)}
        main()->{()}
    "#;
    compile_source_to_bytecode_with_manifest("local-spelling.glorious", local_spelling, &trusted)
        .unwrap();

    let sealed = "struct Local{marker:i64} impl Fn<i64> for Local{} main()->{()}";
    let errors =
        compile_source_to_bytecode_with_manifest("fn.glorious", sealed, &trusted).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message == "source impls for sealed external trait `Fn` are unsupported"
        }),
        "{errors:#?}"
    );

    let external_context = manifest_with([external(
        100,
        "Contextual",
        vec![],
        vec![],
        TraitPolicy::CompilerSealed,
    )]);
    let source =
        "trait Contextual{} struct Local{marker:i64} impl Contextual for Local{} main()->{()}";
    assert!(
        compile_source_to_bytecode_with_manifest(
            "external-context.glorious",
            source,
            &external_context
        )
        .is_err()
    );
    compile_source_to_bytecode("local-context.glorious", source).unwrap();
}

#[test]
fn external_open_trait_for_local_generic_nominals_gates_all_consumers_deterministically() {
    let foreign = external(
        100,
        "Foreign",
        vec![GenericParameterKind::Type],
        vec![item("Item", AssociatedItemKind::Type)],
        TraitPolicy::ExternalOpen,
    );
    let unused = external(
        101,
        "UnusedExternal",
        vec![],
        vec![],
        TraitPolicy::ExternalOpen,
    );
    let manifest = manifest_with([foreign.clone(), unused.clone()]);
    let manifest_reordered = manifest_with([unused, foreign]);
    let source = r#"
        infixl 40 /;
        trait Marker {}
        struct Wrap<T>{value:T}
        struct Ticket<T>{marker:i64}
        struct Bomb<T>{value:T}
        impl Marker for i64 {}
        impl<T> Foreign<T> for Wrap<T> where T:Marker { type Item=T; }
        impl<T> Use<[0,1]> for Ticket<T>
            where Wrap<T>:Foreign<T,Item=T> {}
        impl<T> Drop for Bomb<T>
            where Wrap<T>:Foreign<T,Item=T> {
            drop(&mut self)->{self.value;1 / 0;()}
        }
        pass<T>(value:T)->T where Wrap<T>:Foreign<T,Item=T>{value}
        answer(value:i64)->i64{pass(value)}
        projected(value:<Wrap<i64> as Foreign<i64>>::Item)->i64{value}
        ticket_yes(value:Ticket<i64>)->Ticket<i64>{value}
        ticket_no(value:Ticket<Text>)->Ticket<Text>{value}
        bomb_yes(value:Bomb<i64>)->Bomb<i64>{value}
        bomb_no(value:Bomb<Text>)->Bomb<Text>{value}
        make_bomb()->Bomb<i64>{Bomb{value:1}}
        main()->{let bomb=make_bomb();()}
    "#;
    let reordered = r#"
        infixl 40 /;
        main()->{let bomb=make_bomb();()}
        make_bomb()->Bomb<i64>{Bomb{value:1}}
        bomb_no(value:Bomb<Text>)->Bomb<Text>{value}
        bomb_yes(value:Bomb<i64>)->Bomb<i64>{value}
        ticket_no(value:Ticket<Text>)->Ticket<Text>{value}
        ticket_yes(value:Ticket<i64>)->Ticket<i64>{value}
        projected(value:<Wrap<i64> as Foreign<i64>>::Item)->i64{value}
        answer(value:i64)->i64{pass(value)}
        pass<T>(value:T)->T where Wrap<T>:Foreign<T,Item=T>{value}
        impl<T> Drop for Bomb<T> where Wrap<T>:Foreign<T,Item=T>{drop(&mut self)->{self.value;1 / 0;()}}
        impl<T> Use<[0,1]> for Ticket<T> where Wrap<T>:Foreign<T,Item=T>{}
        impl<T> Foreign<T> for Wrap<T> where T:Marker{type Item=T;}
        impl Marker for i64{}
        struct Bomb<T>{value:T}
        struct Ticket<T>{marker:i64}
        struct Wrap<T>{value:T}
        trait Marker{}
    "#;
    let phases =
        compile_source_to_phases_with_manifest("foreign.glorious", source, &manifest).unwrap();
    let repeated =
        compile_source_to_phases_with_manifest("foreign.glorious", source, &manifest_reordered)
            .unwrap();
    let reordered_phases =
        compile_source_to_phases_with_manifest("foreign-reordered.glorious", reordered, &manifest)
            .unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());
    assert_eq!(phases.artifact.encode(), reordered_phases.artifact.encode());

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let yes = parameter("ticket_yes");
    let no = parameter("ticket_no");
    assert!(!phases.artifact.types[yes as usize].claimed_duplicable());
    assert!(phases.artifact.types[no as usize].claimed_duplicable());
    let bomb_yes = parameter("bomb_yes");
    let bomb_no = parameter("bomb_no");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_yes)
    );
    assert!(
        !phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_no)
    );
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$pass#"))
            .count(),
        1
    );
    let verified = verify(phases.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone())
            .run(answer, vec![Value::I64(42)])
            .unwrap(),
        Value::I64(42)
    );
    let error = Vm::new(verified)
        .run(repeated.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");
}

#[test]
fn orphan_rules_cover_predefined_alias_and_negative_parity() {
    let manifest = manifest_with([external(
        100,
        "Foreign",
        vec![],
        vec![],
        TraitPolicy::ExternalOpen,
    )]);
    for source in [
        "impl Foreign for i64{} main()->{()}",
        "impl Foreign for Text{} main()->{()}",
        "impl !Foreign for i64{} main()->{()}",
        "type Alias=i64; impl Foreign for Alias{} main()->{()}",
        "type Alias=Text; impl !Foreign for Alias{} main()->{()}",
    ] {
        let errors = compile_source_to_bytecode_with_manifest("orphan.glorious", source, &manifest)
            .unwrap_err();
        assert!(errors.iter().any(|error| {
            error.code.as_deref() == Some("G1TR001")
                && error.span.is_some()
                && error.message
                    == "orphan implementation of external trait `Foreign` requires a source-local outer nominal type"
        }), "source: {source}\n{errors:#?}");
    }

    let local = r#"
        trait Positive {}
        trait Negative {}
        impl Positive for i64 {}
        impl !Negative for Text {}
        positive<T>(value:T)->T where T:Positive{value}
        negative<T>(value:T)->T where T:!Negative{value}
        integer(value:i64)->i64{positive(value)}
        text(value:Text)->Text{negative(value)}
        main()->{()}
    "#;
    compile_source_to_bytecode_with_manifest("local-predefined.glorious", local, &manifest)
        .unwrap();
}

#[test]
fn chained_alias_to_local_nominal_preserves_external_impl_ownership_and_evidence() {
    let manifest = manifest_with([external(
        100,
        "Foreign",
        vec![],
        vec![],
        TraitPolicy::ExternalOpen,
    )]);
    let source = r#"
        struct Local{marker:i64}
        type Alias=Local;
        type Chained=Alias;
        impl Foreign for Chained{}
        pass<T>(value:T)->T where T:Foreign{value}
        answer(value:Local)->Local{pass(value)}
        main()->{()}
    "#;
    let phases =
        compile_source_to_phases_with_manifest("local-alias-orphan.glorious", source, &manifest)
            .unwrap();
    assert_eq!(
        phases
            .artifact
            .functions
            .iter()
            .filter(|function| function.name.starts_with("$specialization$pass#"))
            .count(),
        1
    );
    verify(phases.artifact).unwrap();
}

#[test]
fn external_schema_kinds_are_checked_and_effect_rows_are_source_definable() {
    let const_manifest = manifest_with([external(
        100,
        "ConstExternal",
        vec![GenericParameterKind::Const(ConstKind::U32)],
        vec![],
        TraitPolicy::ExternalOpen,
    )]);
    compile_source_to_bytecode_with_manifest(
        "const-manifest.glorious",
        "struct Local{marker:i64} impl ConstExternal<7> for Local{} main()->{()}",
        &const_manifest,
    )
    .unwrap();

    let const_gat_manifest = manifest_with([external(
        100,
        "ConstGat",
        vec![],
        vec![ManifestAssociatedItem {
            name: "Item".into(),
            parameters: vec![GenericParameterKind::Const(ConstKind::U32)],
            kind: AssociatedItemKind::Type,
        }],
        TraitPolicy::ExternalOpen,
    )]);
    // Const-kinded associated-type binders and arguments are complete in the
    // trait layer: an external const-GAT definition is ordinary source.
    compile_source_to_bytecode_with_manifest(
        "const-gat-definition.glorious",
        "struct Local{marker:i64} impl ConstGat for Local{type Item<const N:u32> = i64;} main()->{()}",
        &const_gat_manifest,
    )
    .unwrap();
    // Const arguments now remain attached through associated projection
    // normalization and bytecode signature lowering.
    compile_source_to_bytecode_with_manifest(
        "const-gat-projection.glorious",
        "struct Local{marker:i64} impl ConstGat for Local{type Item<const N:u32> = i64;} read(value:<Local as ConstGat>::Item<7>)->{()} main()->{()}",
        &const_gat_manifest,
    )
    .unwrap();

    let lifetime = external(
        100,
        "LifetimeExternal",
        vec![GenericParameterKind::Lifetime],
        vec![],
        TraitPolicy::ExternalOpen,
    );
    let lifetime_manifest = manifest_with([lifetime.clone()]);
    compile_source_to_bytecode_with_manifest(
        "rigid-lifetime-manifest.glorious",
        "struct Local{marker:i64} impl<'a> LifetimeExternal<'a> for Local{} main()->{()}",
        &lifetime_manifest,
    )
    .unwrap();
    let wrong_kind = compile_source_to_bytecode_with_manifest(
        "wrong-lifetime-kind.glorious",
        "struct Local{marker:i64} impl LifetimeExternal<i64> for Local{} main()->{()}",
        &lifetime_manifest,
    )
    .unwrap_err();
    assert!(wrong_kind.iter().any(|error| {
        error.code.as_deref() == Some("G1TR001")
            && error.span.is_some()
            && error.message == "trait generic argument has the wrong kind; expected a lifetime"
    }));

    let row_manifest = manifest_with([external(
        100,
        "RowExternal",
        vec![],
        vec![item("Effects", AssociatedItemKind::EffectRow)],
        TraitPolicy::ExternalOpen,
    )]);
    compile_source_to_bytecode_with_manifest(
        "external-row-manifest.glorious",
        "struct Local{marker:i64} impl RowExternal for Local{type Effects = {};} main()->{()}",
        &row_manifest,
    )
    .unwrap();
}

#[test]
fn malformed_manifests_report_canonical_structured_errors() {
    let messages = |declarations: Vec<ManifestTrait>| {
        let mut messages = TrustedTraitManifest::new(declarations)
            .unwrap_err()
            .into_iter()
            .map(|error| {
                assert!(error.span.is_none());
                assert_eq!(error.title, "error");
                error.message
            })
            .collect::<Vec<_>>();
        messages.sort();
        messages
    };

    let mut duplicate_id = base_declarations();
    duplicate_id.push(external(
        6,
        "Foreign",
        vec![],
        vec![],
        TraitPolicy::ExternalOpen,
    ));
    assert!(
        messages(duplicate_id).contains(&"trusted trait manifest contains duplicate id 6".into())
    );

    let mut duplicate_name = base_declarations();
    duplicate_name.push(external(
        100,
        "Fn",
        vec![],
        vec![],
        TraitPolicy::ExternalOpen,
    ));
    assert!(
        messages(duplicate_name).contains(
            &"trusted trait manifest contains duplicate or empty display name `Fn`".into()
        )
    );

    let mut duplicate_item = base_declarations();
    duplicate_item.push(external(
        100,
        "Foreign",
        vec![],
        vec![
            item("Item", AssociatedItemKind::Type),
            item("Item", AssociatedItemKind::Type),
        ],
        TraitPolicy::ExternalOpen,
    ));
    assert!(messages(duplicate_item).contains(
        &"trusted trait `Foreign` contains duplicate or empty associated item `Item`".into()
    ));

    let mut malformed_schema = base_declarations();
    malformed_schema[1].parameters.clear();
    assert!(
        messages(malformed_schema)
            .contains(&"trusted trait `Use` does not match the frozen Use intrinsic schema".into())
    );

    let mut wrong_policy = base_declarations();
    wrong_policy[2].policy = TraitPolicy::ExternalOpen;
    assert!(
        messages(wrong_policy)
            .contains(&"trusted trait `Fn` has a conflicting intrinsic role and policy".into())
    );

    let mut duplicate_role = base_declarations();
    duplicate_role.push(intrinsic(100, "OtherFn", IntrinsicRole::Fn));
    assert!(
        messages(duplicate_role)
            .contains(&"trusted trait manifest contains duplicate intrinsic role Fn".into())
    );

    let mut missing_role = base_declarations();
    missing_role.retain(|declaration| declaration.role != Some(IntrinsicRole::Label));
    assert!(
        messages(missing_role)
            .contains(&"trusted trait manifest is missing required intrinsic role Label".into())
    );
}
