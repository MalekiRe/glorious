use grandiose::ast::ConstKind;
use grandiose::{
    AssociatedItemKind, GenericParameterKind, IntrinsicRole, ManifestAssociatedItem, ManifestTrait,
    TraitPolicy, TrustedTraitManifest, compile_source_to_bytecode_with_manifest,
    compile_source_to_phases_with_manifest,
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

fn external(id: u64, name: &str, parameter: GenericParameterKind) -> ManifestTrait {
    ManifestTrait {
        id,
        display_name: name.into(),
        parameters: vec![parameter],
        associated_items: vec![],
        policy: TraitPolicy::ExternalOpen,
        role: None,
    }
}

fn manifest_with(entries: impl IntoIterator<Item = ManifestTrait>) -> TrustedTraitManifest {
    let mut declarations = vec![
        intrinsic(1, "Drop", IntrinsicRole::Drop),
        intrinsic(2, "Use", IntrinsicRole::Use),
        intrinsic(3, "Fn", IntrinsicRole::Fn),
        intrinsic(4, "RunsIn", IntrinsicRole::RunsIn),
        intrinsic(5, "Label", IntrinsicRole::Label),
        intrinsic(6, "Environment", IntrinsicRole::Environment),
    ];
    declarations.extend(entries);
    TrustedTraitManifest::new(declarations).unwrap()
}

fn structural_manifest() -> TrustedTraitManifest {
    manifest_with([
        external(
            100,
            "Quota",
            GenericParameterKind::Const(ConstKind::Quantity),
        ),
        external(101, "Index", GenericParameterKind::Const(ConstKind::U32)),
        external(102, "TypeRel", GenericParameterKind::Type),
    ])
}

fn reordered_structural_manifest() -> TrustedTraitManifest {
    manifest_with([
        external(102, "TypeRel", GenericParameterKind::Type),
        external(101, "Index", GenericParameterKind::Const(ConstKind::U32)),
        external(
            100,
            "Quota",
            GenericParameterKind::Const(ConstKind::Quantity),
        ),
    ])
}

#[test]
fn external_quantity_arguments_are_structural_and_forward_through_param_envs() {
    let source = r#"
        infixl 40 /;
        struct Token { marker:i64 }
        struct Infinite { marker:i64 }
        struct Missing { marker:i64 }
        struct Ticket<T> { marker:i64 }
        struct Bomb<T> { value:T }
        impl Quota<[0,1]> for Token {}
        impl Quota<[0,infinity]> for Infinite {}
        impl<T> Use<[0,1]> for Ticket<T> where T:Quota<[0,1]> {}
        impl<T> Drop for Bomb<T> where T:Quota<[0,1]> {
            drop(&mut self)->{self.value; 1 / 0; ()}
        }
        inner<T>(value:T)->T where T:Quota<[0,1]>{value}
        outer<T>(value:T)->T where T:Quota<[0,1]>{inner(value)}
        answer()->i64{outer(Token{marker:42}).marker}
        infinity<T>(value:T)->T where T:Quota<[0,infinity]>{value}
        infinity_answer(value:Infinite)->Infinite{infinity(value)}
        ticket_token(value:Ticket<Token>)->Ticket<Token>{value}
        ticket_missing(value:Ticket<Missing>)->Ticket<Missing>{value}
        bomb_token(value:Bomb<Token>)->Bomb<Token>{value}
        bomb_missing(value:Bomb<Missing>)->Bomb<Missing>{value}
        make_bomb()->Bomb<Token>{Bomb{value:Token{marker:1}}}
        main()->{let bomb=make_bomb();()}
    "#;
    let phases = compile_source_to_phases_with_manifest(
        "external-quantity.glorious",
        source,
        &structural_manifest(),
    )
    .unwrap();
    let repeated = compile_source_to_phases_with_manifest(
        "external-quantity.glorious",
        source,
        &reordered_structural_manifest(),
    )
    .unwrap();
    assert_eq!(phases.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(phases.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(phases.artifact.encode(), repeated.artifact.encode());

    let parameter = |name: &str| {
        phases
            .artifact
            .functions
            .iter()
            .find(|function| function.name == name)
            .unwrap()
            .params[0]
    };
    let ticket_token = parameter("ticket_token");
    let ticket_missing = parameter("ticket_missing");
    assert!(!phases.artifact.types[ticket_token as usize].claimed_duplicable());
    assert!(phases.artifact.types[ticket_missing as usize].claimed_duplicable());
    let bomb_token = parameter("bomb_token");
    let bomb_missing = parameter("bomb_missing");
    assert!(
        phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_token)
    );
    assert!(
        !phases
            .artifact
            .drop_glue
            .iter()
            .any(|glue| glue.ty == bomb_missing)
    );

    let verified = verify(phases.artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
    let error = Vm::new(verified)
        .run(repeated.artifact.entry_function.unwrap(), vec![])
        .unwrap_err();
    assert!(error.to_string().contains("division by zero"), "{error}");

    for (name, bound) in [
        ("different-finite", "[0,2]"),
        ("finite-versus-infinity", "[0,9]"),
    ] {
        let subject = if name == "different-finite" {
            "Token"
        } else {
            "Infinite"
        };
        let source = format!(
            "struct Token{{marker:i64}} struct Infinite{{marker:i64}} impl Quota<[0,1]> for Token{{}} impl Quota<[0,infinity]> for Infinite{{}} require_quota<T>(v:T)->T where T:Quota<{bound}>{{v}} bad(v:{subject})->{subject}{{require_quota(v)}} main()->{{()}}"
        );
        let errors =
            compile_source_to_bytecode_with_manifest(name, &source, &structural_manifest())
                .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && (error.message.contains("evidence")
                        || error.message.contains("matching implementation"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn explicit_negative_quantity_evidence_is_not_confused_with_absence() {
    let manifest = structural_manifest();
    let accepted = r#"
        struct No { marker:i64 }
        impl !Quota<[1,infinity]> for No {}
        reject<T>(value:T)->i64 where T:!Quota<[1,infinity]>{value;7}
        answer()->i64{reject(No{marker:7})}
        main()->{()}
    "#;
    compile_source_to_bytecode_with_manifest("negative-quantity.glorious", accepted, &manifest)
        .unwrap();

    let absent = r#"
        struct Missing { marker:i64 }
        reject<T>(value:T)->i64 where T:!Quota<[1,infinity]>{value;7}
        bad(value:Missing)->i64{reject(value)}
        main()->{()}
    "#;
    let errors =
        compile_source_to_bytecode_with_manifest("absent-negative.glorious", absent, &manifest)
            .unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.span.is_some()
                && (error.message.contains("negative evidence")
                    || error.message.contains("matching implementation"))
        }),
        "{errors:#?}"
    );
}

#[test]
fn source_const_binders_prove_ground_quantity_and_u32_goals() {
    let source = r#"
        trait Rel<const Q: Quantity> {}
        trait At<const N: u32> {}
        struct Any { marker:i64 }
        impl<const Q: Quantity> Rel<Q> for Any {}
        impl<const N: u32> At<N> for Any {}
        quantity<T>(value:T)->i64 where T:Rel<[2,infinity]>{value;20}
        index<T>(value:T)->i64 where T:At<4294967295>{value;22}
        answer()->i64{quantity(Any{marker:1}) + index(Any{marker:2})}
        main()->{()}
    "#;
    let artifact = grandiose::compile_source_to_bytecode("const-binders.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn const_kinds_and_numeric_domains_are_checked_structurally() {
    let cases = [
        (
            "quantity-got-type",
            "struct S{} impl Quota<i64> for S{} main()->{()}",
            "Quantity",
        ),
        (
            "quantity-got-u32",
            "struct S{} impl Quota<1> for S{} main()->{()}",
            "wrong kind",
        ),
        (
            "u32-got-quantity",
            "struct S{} impl Index<[0,1]> for S{} main()->{()}",
            "wrong kind",
        ),
        (
            "type-got-quantity",
            "struct S{} impl TypeRel<[0,1]> for S{} main()->{()}",
            "wrong kind",
        ),
        (
            "u32-overflow",
            "struct S{} impl Index<4294967296> for S{} main()->{()}",
            "u32",
        ),
        (
            "quantity-overflow",
            "struct S{} impl Quota<[4294967296,4294967296]> for S{} main()->{()}",
            "u32",
        ),
        (
            "quantity-order",
            "struct S{} impl Quota<[2,1]> for S{} main()->{()}",
            "lower",
        ),
    ];
    for (name, source, needle) in cases {
        let errors = compile_source_to_bytecode_with_manifest(name, source, &structural_manifest())
            .unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && error
                        .message
                        .to_ascii_lowercase()
                        .contains(&needle.to_ascii_lowercase())
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn structural_const_overlap_uses_const_identity() {
    let accepted = r#"
        trait Rel<const Q: Quantity> {}
        struct S { marker:i64 }
        impl Rel<[0,1]> for S {}
        impl Rel<[0,2]> for S {}
        main()->{()}
    "#;
    grandiose::compile_source_to_bytecode("disjoint-consts.glorious", accepted).unwrap();

    for (name, source) in [
        (
            "duplicate-ground",
            "trait Rel<const Q:Quantity>{} struct S{} impl Rel<[0,1]> for S{} impl Rel<[0,1]> for S{} main()->{()}",
        ),
        (
            "blanket-fixed",
            "trait Rel<const Q:Quantity>{} struct S{} impl<const Q:Quantity> Rel<Q> for S{} impl Rel<[0,1]> for S{} main()->{()}",
        ),
        (
            "polarity-conflict",
            "trait Rel<const Q:Quantity>{} struct S{} impl Rel<[0,1]> for S{} impl !Rel<[0,1]> for S{} main()->{()}",
        ),
    ] {
        let errors = grandiose::compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && (error.message.contains("overlap") || error.message.contains("conflict"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn const_binders_are_accepted_on_nominals_and_declaration_only_functions() {
    for (name, source) in [
        (
            "const-struct",
            "struct Bad<const Q:Quantity>{marker:i64} main()->{()}",
        ),
        ("const-enum", "enum Bad<const N:u32>{One} main()->{()}"),
        (
            "const-function",
            "bad<const Q:Quantity>()->{()} main()->{()}",
        ),
    ] {
        grandiose::compile_source_to_bytecode(name, source).unwrap();
    }
}

#[test]
fn frozen_const_kind_names_cannot_be_shadowed_by_source_types() {
    for (name, source) in [
        (
            "quantity-struct",
            "struct Quantity{marker:i64} main()->{()}",
        ),
        ("quantity-alias", "type Quantity=i64; main()->{()}"),
    ] {
        let errors = grandiose::compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.span.is_some()
                    && error.code.is_some()
                    && (error.message.contains("Quantity")
                        || error.message.contains("predefined")
                        || error.message.contains("reserved"))
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn external_const_orphan_rules_preserve_alias_and_polarity_parity() {
    let manifest = structural_manifest();
    let accepted =
        "struct Local{marker:i64} type Alias=Local; impl Quota<[0,1]> for Alias{} main()->{()}";
    compile_source_to_bytecode_with_manifest("local-alias-const.glorious", accepted, &manifest)
        .unwrap();

    for (name, source) in [
        (
            "foreign-positive",
            "impl Quota<[0,1]> for i64{} main()->{()}",
        ),
        (
            "foreign-negative",
            "impl !Quota<[0,1]> for i64{} main()->{()}",
        ),
        (
            "foreign-alias-negative",
            "type Alias=Text; impl !Quota<[0,1]> for Alias{} main()->{()}",
        ),
    ] {
        let errors = compile_source_to_bytecode_with_manifest(name, source, &manifest).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G1TR001")
                    && error.span.is_some()
                    && error.message.contains("orphan")
            }),
            "{name}: {errors:#?}"
        );
    }
}
