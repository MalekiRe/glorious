use grandiose_stage0::{
    DeclarationScan, ElaboratedInterface, FileKey, InterfaceSet, LexedFile, LogicalPath,
    ManifestError, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput,
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
        selectors: vec![
            PrimitiveSelector {
                role: PrimitiveRole::BranchBool,
                module_path: "crate".into(),
                name: "branch_bool".into(),
            },
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

#[test]
fn primitive_authority_binds_only_the_exact_standard_library_declaration() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { ignored } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }";
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
    let bound = bound_manifest.primitives[&PrimitiveRole::BranchBool];
    let standard_branch = standard_interface
        .definitions
        .iter()
        .find(|definition| definition.name.as_deref() == Some("branch_bool"))
        .expect("fixture declares branch_bool")
        .key;
    assert_eq!(bound_manifest.standard_library, standard);
    assert_eq!(
        bound, standard_branch,
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
            .find(|definition| definition.name.as_deref() == Some("branch_bool"))
            .expect("fixture declares branch_bool")
            .key
    );
    assert_eq!(unchanged.primitives[&PrimitiveRole::BranchBool], bound);
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
fn bytes_runtime_leaves_bind_by_exact_identity_and_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let source = "pub fn __g1_bytes_get(bytes: Bytes, index: usize) -> u8 { () }";
    let package_interface = interface(standard.clone(), source);
    let signatures = ElaboratedInterface::elaborate(&package_interface);
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
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
fn generic_int_checked_to_usize_requires_its_exact_i64_to_usize_abi() {
    let standard = PackageKey("std@0.1.0".into());
    let input = RuntimeManifestInput {
        standard_library: standard.clone(),
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
fn primitive_manifest_rejects_signature_mismatch_before_authority_freezes() {
    let standard = PackageKey("bad-std@0.1.0".into());
    let interface = interface(
        standard.clone(),
        "pub fn branch_bool(condition: Bool) -> Bool { condition } pub fn __g1_text_byte_len(value: Text) -> usize { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
    );
    let signatures = ElaboratedInterface::elaborate(&interface);
    assert!(matches!(
        manifest(standard).bind(vec![interface], &signatures),
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
        "pub fn branch_bool<T>(condition: Bool, on_true: () -> T, on_false: () -> T) -> T { ignored } pub fn __g1_text_byte_len(value: Text) -> i64 { () } pub fn __g1_text_concat(left: Text, right: Text) -> Text { () } pub fn __g1_text_eq(left: Text, right: Text) -> u32 { () } pub fn __g1_text_from_utf8_checked(value: Bytes) -> Text { () } pub fn __g1_text_as_bytes(value: Text) -> Bytes { () } pub fn __g1_char_from_u32_checked(value: u32) -> char { () } pub fn __g1_char_to_u32(value: char) -> u32 { () }",
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
