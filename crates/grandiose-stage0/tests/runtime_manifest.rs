use grandiose_stage0::{
    DeclarationScan, ElaboratedInterface, FileKey, HostImportSelector, InterfaceSet, LexedFile,
    LogicalPath, ManifestError, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput,
};

fn interface(package: PackageKey, source: &str) -> grandiose_stage0::PackageInterface {
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface
}

fn manifest(standard_library: PackageKey) -> RuntimeManifestInput {
    RuntimeManifestInput {
        standard_library,
        literal_views: vec![], host_imports: vec![],
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::TextByteLen,
                module_path: "crate".into(),
                name: "__g1_text_byte_len".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextConcat,
                module_path: "crate".into(),
                name: "__g1_text_concat".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextEq,
                module_path: "crate".into(),
                name: "__g1_text_eq".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextFromUtf8Checked,
                module_path: "crate".into(),
                name: "__g1_text_from_utf8_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::TextAsBytes,
                module_path: "crate".into(),
                name: "__g1_text_as_bytes".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharFromU32Checked,
                module_path: "crate".into(),
                name: "__g1_char_from_u32_checked".into(),
            },
            PrimitiveSelector {
                role: PrimitiveRole::CharToU32,
                module_path: "crate".into(),
                name: "__g1_char_to_u32".into(),
            },
        ],
    }
}

fn literal_manifest() -> (RuntimeManifestInput, grandiose_stage0::PackageInterface, ElaboratedInterface) {
    use grandiose_stage0::{DefinitionIndex, LiteralViewKind, LiteralViewSelector};
    let package = PackageKey("chosen-library@7".into());
    let interface = interface(package.clone(), r#"
        pub struct View<'a> { value: &'a i64 }
        fn materialize(value: __StaticData<Utf8Bytes>) -> View<'static> { () }
    "#);
    let index = DefinitionIndex::from_interface(&interface).with_runtime_library(Some(package.clone()));
    let signatures = ElaboratedInterface::elaborate_with_index(&interface, &index);
    assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
    (RuntimeManifestInput { standard_library: package, selectors: vec![], host_imports: vec![],
        literal_views: vec![LiteralViewSelector { kind: LiteralViewKind::Utf8, module_path: "crate".into(), name: "materialize".into() }],
    }, interface, signatures)
}

#[test]
fn literal_views_bind_private_ordinary_functions_in_the_selected_library() {
    use grandiose_stage0::LiteralViewKind;
    let (input, interface, signatures) = literal_manifest();
    let bound = input.bind([interface.clone()], &signatures).unwrap();
    let definition = interface.definitions.iter().find(|definition| definition.name.as_deref() == Some("materialize")).unwrap();
    assert_eq!(bound.literal_views[&LiteralViewKind::Utf8], definition.key);
    assert!(bound.primitives.is_empty() && bound.host_imports.is_empty());
    let mut empty = input.clone(); empty.literal_views.clear();
    assert_ne!(bound.digest, empty.bind([interface], &signatures).unwrap().digest);
}

#[test]
fn literal_view_bindings_reject_nonclosed_or_nonordinary_contracts() {
    use grandiose_stage0::{ElaboratedHeader, GenericKind, LiteralViewKind, ScalarType, Type};
    let (input, interface, signatures) = literal_manifest();
    let definition = input.bind([interface.clone()], &signatures).unwrap().literal_views[&LiteralViewKind::Utf8];
    for case in 0..12 {
        let mut invalid = signatures.clone();
        let ElaboratedHeader::Callable(signature) = invalid.definitions.get_mut(&definition).unwrap() else { unreachable!() };
        match case {
            0 => signature.safety = grandiose_stage0::Safety::Unsafe,
            1 => signature.parameters.clear(),
            2 => signature.parameters.push(signature.parameters[0].clone()),
            3 => signature.parameters = vec![Type::Scalar(ScalarType::Bytes)],
            4 => { let Type::StaticData { tag, .. } = &mut signature.parameters[0] else { unreachable!() }; *tag = 0x4752_414e_4449_4f53_455f_5241_5755_385f; }
            5 => { let Type::StaticData { alignment, .. } = &mut signature.parameters[0] else { unreachable!() }; *alignment = 8; }
            6 => { signature.generics = 1; signature.generic_kinds.push(GenericKind::Type); }
            7 => signature.result = Type::Scalar(ScalarType::Text),
            8 => signature.effects = grandiose_stage0::EffectRow::closed([definition]),
            9 => { let Type::Nominal { arguments, .. } = &mut signature.result else { unreachable!() }; arguments[0] = grandiose_stage0::GenericArgument::Lifetime(grandiose_stage0::Lifetime::Generic(0)); }
            10 => { let Type::Nominal { definition: target, .. } = &mut signature.result else { unreachable!() }; *target = definition; }
            _ => signature.where_outlives.push(grandiose_stage0::OutlivesPredicate::Region { longer: grandiose_stage0::Lifetime::Static, shorter: grandiose_stage0::Lifetime::Static }),
        }
        assert!(matches!(input.bind([interface.clone()], &invalid), Err(ManifestError::IncompatibleLiteralView { kind: LiteralViewKind::Utf8, .. })), "case {case}");
    }
    let mut host = input.clone();
    host.host_imports.push(HostImportSelector { module_path: "crate".into(), name: "materialize".into(), capability: "host.view".into(), symbol: "view".into() });
    assert!(matches!(host.bind([interface.clone()], &signatures), Err(ManifestError::ConflictingRuntimeBinding { .. })));
    let mut duplicate = input.clone(); duplicate.literal_views.push(input.literal_views[0].clone());
    assert_eq!(duplicate.canonicalize(), Err(ManifestError::DuplicateLiteralView(LiteralViewKind::Utf8)));
    assert!(matches!(duplicate.bind([interface.clone()], &signatures), Err(ManifestError::DuplicateLiteralView(LiteralViewKind::Utf8))));
    let mut missing = input; missing.literal_views[0].name = "not-present".into();
    assert!(matches!(missing.bind([interface], &signatures), Err(ManifestError::MissingDeclaration { .. })));
}

#[test]
fn primitive_authority_binds_only_the_exact_standard_library_declaration() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }";
    let standard_interface = interface(standard.clone(), source);
    let signatures = ElaboratedInterface::elaborate(&standard_interface);
    assert!(
        signatures.diagnostics.is_empty(),
        "{:#?}",
        signatures.diagnostics
    );
    let bound_manifest = manifest(standard.clone())
        .bind(vec![standard_interface.clone()], &signatures)
        .unwrap();
    let bound = bound_manifest.primitives[&PrimitiveRole::TextByteLen];
    let standard_leaf = standard_interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("__g1_text_byte_len"))
        .expect("fixture declares text_byte_len")
        .key;
    assert_eq!(bound_manifest.standard_library, standard);
    assert_eq!(
        bound, standard_leaf,
        "the manifest binds a declaration identity, not its spelling"
    );

    let user = PackageKey("app@0.1.0".into());
    let user_interface = interface(user, source);
    let unchanged = manifest(standard)
        .bind(vec![standard_interface], &signatures)
        .unwrap();
    assert_ne!(
        bound,
        user_interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("__g1_text_byte_len"))
            .expect("fixture declares text_byte_len")
            .key
    );
    assert_eq!(unchanged.primitives[&PrimitiveRole::TextByteLen], bound);
}

#[test]
fn manifest_can_grant_a_strict_runtime_leaf_subset() {
    let standard = PackageKey("std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "fn __g1_text_byte_len(value: Text) -> usize { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    let manifest = RuntimeManifestInput {
        standard_library: standard,
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::TextByteLen,
            module_path: "crate".into(),
            name: "__g1_text_byte_len".into(),
        }],
    }
    .bind(vec![interface], &signatures)
    .expect("a standard-library revision may expose only the leaves it owns");
    assert_eq!(manifest.primitives.len(), 1);
    assert!(
        manifest
            .primitives
            .contains_key(&PrimitiveRole::TextByteLen)
    );
}

#[test]
fn manifest_host_selector_cannot_replace_a_source_host_boundary() {
    let standard = PackageKey("std@0.1.0".into());
    let package_interface = interface(standard.clone(), "host clock fn now() -> i64;");
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    let input = RuntimeManifestInput {
        standard_library: standard,
        selectors: vec![],
        literal_views: vec![], host_imports: vec![HostImportSelector {
            module_path: "crate".into(),
            name: "now".into(),
            capability: "other_clock".into(),
            symbol: "replaced".into(),
        }],
    };

    assert!(matches!(
        input.bind(vec![package_interface], &signatures),
        Err(ManifestError::ConflictingRuntimeBinding { .. })
    ));
}

#[test]
fn bytes_runtime_leaves_bind_by_exact_identity_and_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn __g1_bytes_get(bytes: Bytes, index: usize) -> u8 { () }";
    let package_interface = interface(standard.clone(), source);
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::BytesGet,
            module_path: "crate".into(),
            name: "__g1_bytes_get".into(),
        }],
    };
    let manifest = input
        .bind(vec![package_interface], &signatures)
        .expect("the exact Bytes and usize to u8 ABI must bind");
    assert!(manifest.primitives.contains_key(&PrimitiveRole::BytesGet));

    let invalid_interface = interface(
        standard.clone(),
        "pub fn __g1_bytes_get(bytes: Bytes, index: usize) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::BytesGet,
            ..
        })
    ));
}

#[test]
fn u32_runtime_leaves_bind_by_exact_identity_and_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::U32CheckedAdd,
            module_path: "crate".into(),
            name: "__g1_u32_checked_add".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_u32_checked_add(left: u32, right: u32) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact checked u32 ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_u32_checked_add(left: u32, right: u32) -> usize { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::U32CheckedAdd,
            ..
        })
    ));
}

#[test]
fn generic_int_shr_requires_its_exact_mixed_generic_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntShr,
            module_path: "crate".into(),
            name: "__g1_int_shr".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_shr<T>(value: T, count: u32) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic int shift ABI must bind");
    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_shr<T>(value: T, count: i64) -> T { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntShr,
            ..
        })
    ));
}

#[test]
fn generic_int_bit_xor_requires_its_exact_generic_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntBitXor,
            module_path: "crate".into(),
            name: "__g1_int_bit_xor".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_bit_xor<T>(left: T, right: T) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic int bit-xor ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_bit_xor(left: i64, right: i64) -> i64 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntBitXor,
            ..
        })
    ));
}

#[test]
fn generic_int_bit_and_requires_its_exact_generic_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntBitAnd,
            module_path: "crate".into(),
            name: "__g1_int_bit_and".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_bit_and<T>(left: T, right: T) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic int bit-and ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_bit_and(left: i64, right: i64) -> i64 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntBitAnd,
            ..
        })
    ));
}

#[test]
fn generic_int_bit_or_requires_its_exact_generic_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntBitOr,
            module_path: "crate".into(),
            name: "__g1_int_bit_or".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_bit_or<T>(left: T, right: T) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic int bit-or ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_bit_or(left: i64, right: i64) -> i64 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntBitOr,
            ..
        })
    ));
}

#[test]
fn generic_int_bit_not_requires_its_exact_unary_generic_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntBitNot,
            module_path: "crate".into(),
            name: "__g1_int_bit_not".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_bit_not<T>(value: T) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact unary generic int bit-not ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_bit_not<T>(left: T, right: T) -> T { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntBitNot,
            ..
        })
    ));
}

#[test]
fn generic_int_shift_left_requires_its_exact_i64_u32_i64_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntShl,
            module_path: "crate".into(),
            name: "__g1_int_shl".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_shl<T>(value: T, count: u32) -> T { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64/u32/i64 shift-left ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_shl<T>(value: T, count: T) -> T { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntShl,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_u32_requires_its_exact_i64_to_u32_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToU32,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_u32".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_u32<T>(value: T) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-u32 wrapping ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_u32<T>(value: T) -> i64 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToU32,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_usize_requires_its_exact_i64_to_usize_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToUsize,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_usize".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_usize<T>(value: T) -> usize { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-usize wrapping ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_usize<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToUsize,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_u8_requires_its_exact_i64_to_u8_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToU8,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_u8".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_u8<T>(value: T) -> u8 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-u8 wrapping ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_u8<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToU8,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_u16_requires_its_exact_i64_to_u16_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToU16,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_u16".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_u16<T>(value: T) -> u16 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-u16 wrapping ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_u16<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToU16,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_i16_requires_its_exact_i64_to_i16_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToI16,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_i16".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_i16<T>(value: T) -> i16 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("exact i64-to-i16 ABI must bind");
    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_i16<T>(value: T) -> u16 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToI16,
            ..
        })
    ));
}

#[test]
fn generic_int_checked_to_i32_requires_its_exact_i64_to_i32_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertCheckedToI32,
            module_path: "crate".into(),
            name: "__g1_int_convert_checked_to_i32".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_checked_to_i32<T>(value: T) -> i32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("exact i64-to-i32 ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_checked_to_i32<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertCheckedToI32,
            ..
        })
    ));
}

#[test]
fn generic_int_wrapping_to_i32_requires_its_exact_i64_to_i32_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertWrappingToI32,
            module_path: "crate".into(),
            name: "__g1_int_convert_wrapping_to_i32".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_wrapping_to_i32<T>(value: T) -> i32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("exact i64-to-i32 ABI must bind");
    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_wrapping_to_i32<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertWrappingToI32,
            ..
        })
    ));
}

#[test]
fn generic_int_checked_to_usize_requires_its_exact_i64_to_usize_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertCheckedToUsize,
            module_path: "crate".into(),
            name: "__g1_int_convert_checked_to_usize".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_checked_to_usize<T>(value: T) -> usize { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-usize checked ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_checked_to_usize<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertCheckedToUsize,
            ..
        })
    ));
}

#[test]
fn generic_int_checked_to_u8_requires_its_exact_i64_to_u8_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertCheckedToU8,
            module_path: "crate".into(),
            name: "__g1_int_convert_checked_to_u8".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_checked_to_u8<T>(value: T) -> u8 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-u8 checked ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_checked_to_u8<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertCheckedToU8,
            ..
        })
    ));
}

#[test]
fn generic_int_checked_to_u16_requires_its_exact_i64_to_u16_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::IntConvertCheckedToU16,
            module_path: "crate".into(),
            name: "__g1_int_convert_checked_to_u16".into(),
        }],
    };
    let package_interface = interface(
        standard.clone(),
        "pub fn __g1_int_convert_checked_to_u16<T>(value: T) -> u16 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    input
        .bind(vec![package_interface], &signatures)
        .expect("the exact generic i64-to-u16 checked ABI must bind");

    let invalid_interface = interface(
        standard,
        "pub fn __g1_int_convert_checked_to_u16<T>(value: T) -> u32 { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid_interface);
    assert!(matches!(
        input.bind(vec![invalid_interface], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::IntConvertCheckedToU16,
            ..
        })
    ));
}

#[test]
fn primitive_manifest_rejects_signature_mismatch_before_authority_freezes() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub enum Bool { Yes, No } pub fn branch_bool(condition: Bool) -> Bool { condition } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(matches!(
        RuntimeManifestInput { standard_library: standard, literal_views: vec![], host_imports: vec![], selectors: vec![PrimitiveSelector { role: PrimitiveRole::BranchBool, module_path: "crate".into(), name: "branch_bool".into() }] }.bind(vec![interface], &signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::BranchBool,
            ..
        })
    ));
}

#[test]
fn text_byte_len_requires_its_exact_monomorphic_abi() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub fn __g1_text_byte_len(value: Text) -> i64 { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(matches!(
        manifest(standard).bind(vec![interface], &signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::TextByteLen,
            ..
        })
    ));
}

#[test]
fn implemented_generic_integer_roles_have_stable_selector_round_trips() {
    use PrimitiveRole::*;
    let roles = [
        IntCheckedAdd,
        IntCheckedDiv,
        IntWrappingAdd,
        IntWrappingSub,
        IntWrappingMul,
        IntWrappingNeg,
        IntEqual,
        IntLess,
        IntGreater,
        IntBitAnd,
        IntBitOr,
        IntBitXor,
        IntBitNot,
        IntShl,
        IntShr,
        IntConvertCheckedToI64,
        IntConvertWrappingToI64,
        IntConvertCheckedToU32,
        IntConvertWrappingToU32,
        IntConvertCheckedToUsize,
        IntConvertWrappingToUsize,
        IntConvertCheckedToU8,
        IntConvertWrappingToU8,
        IntConvertCheckedToU16,
        IntConvertWrappingToU16,
        IntConvertCheckedToI16,
        IntConvertWrappingToI16,
        IntConvertCheckedToI32,
        IntConvertWrappingToI32,
    ];
    for role in roles {
        assert_eq!(
            PrimitiveRole::parse_selector_name(role.selector_name()),
            Some(role)
        );
    }
}

#[test]
fn blake3_requires_the_exact_manifest_bound_bytes_abi() {
    let standard = PackageKey("compiler-support@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
        literal_views: vec![], host_imports: vec![],
        selectors: vec![PrimitiveSelector {
            role: PrimitiveRole::Blake3,
            module_path: "crate".into(),
            name: "__g1_blake3".into(),
        }],
    };
    let valid = interface(
        standard.clone(),
        "pub fn __g1_blake3(value: Bytes) -> Bytes { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&valid);
    input
        .bind(vec![valid], &signatures)
        .expect("the exact BLAKE3 bytes ABI must bind");

    let invalid = interface(
        standard,
        "pub fn __g1_blake3(value: Bytes) -> Text { () }",
    );
    let invalid_signatures = ElaboratedInterface::elaborate(&invalid);
    assert!(matches!(
        input.bind(vec![invalid], &invalid_signatures),
        Err(ManifestError::IncompatibleSignature {
            role: PrimitiveRole::Blake3,
            ..
        })
    ));
}
