use grandiose_stage0::types::integer_const::{
    IntegerConst as Value, IntegerConstError as Error, IntegerConstExpr as Expr,
    IntegerConstOp as Op,
};
use grandiose_stage0::types::{ScalarType, StructuralConstError, IntegerConstExpr};

#[test]
fn argument_substitution_preserves_mixed_slot_indices_and_integer_kinds() {
    use grandiose_stage0::{ConstKind, GenericArgument, Type};
    for scalar in (0..=12).filter_map(ConstKind::from_tag).filter_map(ConstKind::integer_scalar) {
        let expression = binary(Op::Add,
            Expr::Param { index: 1, scalar },
            Expr::Literal(value(scalar, 1)));
        assert_eq!(expression.substitute_arguments(&[
            GenericArgument::Type(Type::Scalar(ScalarType::Bool)),
            GenericArgument::ConstInteger(value(scalar, 41)),
        ]), Ok(Expr::Literal(value(scalar, 42))));
        assert!(expression.substitute_arguments(&[
            GenericArgument::ConstInteger(value(scalar, 41)),
            GenericArgument::Type(Type::Scalar(ScalarType::Bool)),
        ]).is_err());
        for other in (0..=12).filter_map(ConstKind::from_tag).filter_map(ConstKind::integer_scalar) {
            if other == scalar { continue }
            assert!(expression.substitute_arguments(&[
                GenericArgument::Type(Type::Scalar(ScalarType::Bool)),
                GenericArgument::ConstInteger(value(other, 41)),
            ]).is_err(), "{other:?} into {scalar:?}");
        }
    }
}

#[test]
fn a_known_zero_divisor_is_rejected_even_with_a_symbolic_numerator() {
    for scalar in (0..=12).filter_map(grandiose_stage0::ConstKind::from_tag)
        .filter_map(grandiose_stage0::ConstKind::integer_scalar)
    {
        for op in [Op::Div, Op::Rem] {
            let expression = binary(op, Expr::Param { index: 0, scalar }, Expr::Literal(value(scalar, 0)));
            assert_eq!(expression.normalized(), Err(Error::DivisionByZero));
        }
    }
}

#[test]
fn literal_elaboration_preserves_full_magnitudes_and_canonical_spellings() {
    for token in ["42", "4_2", "0b101010", "0o52", "0x2a", "0x_2A"] {
        for kind in (0..=12)
            .filter_map(grandiose_stage0::ConstKind::from_tag)
            .filter_map(|kind| kind.integer_scalar())
        {
            assert_eq!(Value::from_literal(kind, token, false, 64), Value::new(kind, false, 42, 64));
        }
    }
    for token in ["340282366920938463463374607431768211455", "0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff"] {
        assert_eq!(Value::from_literal(ScalarType::U128, token, false, 64).unwrap().magnitude(), u128::MAX);
        assert_eq!(Value::from_literal(ScalarType::I128, token, false, 64), Err(Error::Overflow));
    }
    for token in ["170141183460469231731687303715884105728", "0x80000000000000000000000000000000"] {
        assert_eq!(Value::from_literal(ScalarType::I128, token, true, 64), Value::new(ScalarType::I128, true, 1 << 127, 64));
        assert_eq!(Value::from_literal(ScalarType::I128, token, false, 64), Err(Error::Overflow));
    }
    assert_eq!(Value::from_literal(ScalarType::I8, "0x80", true, 64), Value::new(ScalarType::I8, true, 128, 64));
    assert_eq!(Value::from_literal(ScalarType::U8, "1", true, 64), Err(Error::Overflow));
    assert_eq!(Value::from_literal(ScalarType::I8, "0", true, 64), Value::new(ScalarType::I8, false, 0, 64));
}

#[test]
fn literal_elaboration_checks_target_width_and_rejects_invalid_spelling() {
    for token in ["", "_1", "1_", "1__0", "0x", "0x_", "0x__1", "0b2", "0o8", "0xg", "-1", "+1", "1u8", "1.0", "1e2", " 1", "1 ", "１２"] {
        assert_eq!(Value::from_literal(ScalarType::U128, token, false, 64), Err(Error::InvalidLiteral), "{token}");
    }
    for token in ["340282366920938463463374607431768211456", "0x100000000000000000000000000000000"] {
        assert_eq!(Value::from_literal(ScalarType::U128, token, false, 64), Err(Error::Overflow));
    }
    // Invalid syntax is still checked after magnitude overflow.
    assert_eq!(Value::from_literal(ScalarType::U128, "340282366920938463463374607431768211456_", false, 64), Err(Error::InvalidLiteral));
    assert_eq!(Value::from_literal(ScalarType::Usize, "4294967296", false, 32), Err(Error::Overflow));
    assert_eq!(Value::from_literal(ScalarType::Usize, "4294967296", false, 64).unwrap().magnitude(), 1 << 32);
    assert_eq!(Value::from_literal(ScalarType::Isize, "2147483648", true, 32).unwrap().magnitude(), 1 << 31);
    assert_eq!(Value::from_literal(ScalarType::Isize, "2147483648", false, 32), Err(Error::Overflow));
    assert_eq!(Value::from_literal(ScalarType::U32, "1", false, 16), Err(Error::InvalidTargetWidth));
    assert_eq!(Value::from_literal(ScalarType::F32, "1", false, 64), Err(Error::NonIntegerKind));
}

#[test]
fn const_kind_tags_and_names_are_exact_and_reject_unknown_domains() {
    use grandiose_stage0::{ConstKind, GenericKind};
    for tag in 0..=u8::MAX {
        let kind = ConstKind::from_tag(tag);
        assert_eq!(kind.is_some(), tag <= 12);
        if let Some(kind) = kind {
            assert_eq!(kind.tag(), tag);
            assert_eq!(
                GenericKind::from_tag(GenericKind::Const(kind).tag()),
                Some(GenericKind::Const(kind))
            );
            if kind != ConstKind::Quantity {
                assert_eq!(ConstKind::from_integer_name(kind.name()), Some(kind));
                assert!(kind.integer_scalar().is_some());
            }
        }
        assert_eq!(GenericKind::from_tag(tag).is_some(), tag <= 15);
    }
    for name in ["bool", "Bool", "f32", "f64", "char", "Text", "Quantity"] {
        assert_eq!(ConstKind::from_integer_name(name), None);
    }
}

#[test]
fn explicit_const_binders_retain_every_integer_kind_through_headers_and_signatures() {
    use grandiose_stage0::{
        ConstKind, DeclarationScan, ElaboratedHeader, ElaboratedInterface, FileKey,
        GenericArgument, GenericKind, HeaderParse, InterfaceSet, LexedFile, PackageKey,
        ParsedHeader, Type,
    };
    for kind in (0..=12).filter_map(ConstKind::from_tag) {
        let source = format!(
            "struct Tag<const N: {}>();
            fn carry<const N: {}>(value: Tag<N>) -> Tag<N> {{ value }}
            trait Width {{ const SIZE: {}; }}",
            kind.name(),
            kind.name(),
            kind.name()
        );
        let package = PackageKey("const-kind-header@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        assert!(scan.diagnostics.is_empty(), "{source}: {scan:?}");
        let parsed = HeaderParse::parse(&lexed, &source, &scan.declarations[1]);
        assert!(parsed.diagnostics.is_empty(), "{source}: {parsed:?}");
        let ParsedHeader::Function(header) = parsed.header else {
            panic!("callable header")
        };
        assert_eq!(header.generics.kinds(), vec![GenericKind::Const(kind)]);
        let interface = InterfaceSet::collect(package, "crate", &lexed, &source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        assert!(
            signatures.diagnostics.is_empty(),
            "{source}: {:?}",
            signatures.diagnostics
        );
        let key = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("carry"))
            .unwrap()
            .key;
        let ElaboratedHeader::Callable(signature) = &signatures.definitions[&key] else {
            panic!("callable signature")
        };
        assert_eq!(signature.generic_kinds, vec![GenericKind::Const(kind)]);
        assert!(
            matches!(&signature.parameters[0], Type::Nominal { arguments, .. }
            if arguments == &[GenericArgument::ConstGeneric { index: 0, kind }])
        );
        assert_eq!(signature.parameters[0], signature.result);
    }
}

#[test]
fn explicit_const_binders_reject_missing_or_nonconst_kinds() {
    use grandiose_stage0::{DeclarationScan, FileKey, HeaderParse, LexedFile, PackageKey};
    for binder in [
        "const N",
        "const N: EffectRow",
        "const 'a: usize",
        "const N: f64",
        "const N: bool",
    ] {
        let source = format!("fn carry<{binder}>() {{}}");
        let package = PackageKey("bad-const-kind@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        let parsed = HeaderParse::parse(&lexed, &source, &scan.declarations[0]);
        assert!(
            parsed
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3205"),
            "{source}: {parsed:?}"
        );
    }
}

#[test]
fn const_inference_and_frozen_identities_do_not_merge_different_integer_kinds() {
    use grandiose_stage0::{ConstKind, DefKey, Digest, GenericArgument, InferContext, Type};
    let definition = DefKey(Digest::of_bytes(b"integer-kind-identity"));
    let nominal = |argument| Type::Nominal {
        definition,
        arguments: vec![argument],
    };
    let mut identities = std::collections::BTreeSet::new();
    for kind in (0..=12).filter_map(ConstKind::from_tag) {
        let mut inference = InferContext::default();
        let variable = inference.fresh_const(kind);
        let expected = GenericArgument::ConstGeneric { index: 0, kind };
        for other in (0..=12)
            .filter_map(ConstKind::from_tag)
            .filter(|other| *other != kind)
        {
            assert!(
                inference
                    .unify(
                        nominal(variable.clone()),
                        nominal(GenericArgument::ConstGeneric {
                            index: 0,
                            kind: other
                        })
                    )
                    .is_err()
            );
        }
        inference
            .unify(nominal(variable.clone()), nominal(expected.clone()))
            .unwrap();
        assert_eq!(
            inference.zonk(nominal(variable)).unwrap(),
            nominal(expected.clone())
        );
        assert!(identities.insert(inference.type_fingerprint(nominal(expected)).unwrap()));
    }
}

fn value(kind: ScalarType, number: i128) -> Value {
    Value::new(kind, number < 0, number.unsigned_abs(), 64).unwrap()
}

fn binary(op: Op, left: Expr, right: Expr) -> Expr {
    Expr::Binary {
        op,
        left: Box::new(left),
        right: Box::new(right),
    }
}

#[test]
fn every_integer_kind_checks_its_own_signed_and_unsigned_limits() {
    use ScalarType::*;
    for (kind, bits, signed) in [
        (U8, 8, false),
        (U16, 16, false),
        (U32, 32, false),
        (U64, 64, false),
        (U128, 128, false),
        (I8, 8, true),
        (I16, 16, true),
        (I32, 32, true),
        (I64, 64, true),
        (I128, 128, true),
    ] {
        let maximum = if signed {
            (1u128 << (bits - 1)) - 1
        } else {
            u128::MAX >> (128 - bits)
        };
        let max = Value::new(kind, false, maximum, 64).unwrap();
        assert_eq!(max.magnitude(), maximum);
        assert_eq!(max.scalar(), kind);
        assert_eq!(
            max.checked(Op::Add, value(kind, 1), 64),
            Err(Error::Overflow)
        );
        if maximum != u128::MAX {
            assert_eq!(
                Value::new(kind, false, maximum + 1, 64),
                Err(Error::Overflow)
            );
        }
        if signed {
            let minimum = Value::new(kind, true, maximum + 1, 64).unwrap();
            assert_eq!(minimum.checked_neg(64), Err(Error::Overflow));
            assert_eq!(
                minimum.checked(Op::Sub, value(kind, 1), 64),
                Err(Error::Overflow)
            );
            for op in [Op::Div, Op::Rem] {
                assert_eq!(
                    minimum.checked(op, value(kind, -1), 64),
                    Err(Error::Overflow)
                );
            }
            assert_eq!(
                Value::new(kind, true, maximum + 2, 64),
                Err(Error::Overflow)
            );
        } else {
            assert_eq!(Value::new(kind, true, 1, 64), Err(Error::Overflow));
            assert_eq!(
                value(kind, 0).checked(Op::Sub, value(kind, 1), 64),
                Err(Error::Overflow)
            );
        }
        assert_eq!(Value::new(kind, true, 0, 64).unwrap(), value(kind, 0));
    }
}

#[test]
fn small_integer_arithmetic_matches_an_independent_wider_integer_oracle() {
    for signed in [false, true] {
        let (kind, minimum, maximum) = if signed {
            (ScalarType::I8, -128i32, 127i32)
        } else {
            (ScalarType::U8, 0i32, 255i32)
        };
        for left in minimum..=maximum {
            for right in minimum..=maximum {
                for op in [Op::Add, Op::Sub, Op::Mul, Op::Div, Op::Rem] {
                    let expected = if matches!(op, Op::Div | Op::Rem) && right == 0 {
                        Err(Error::DivisionByZero)
                    } else if signed
                        && left == minimum
                        && right == -1
                        && matches!(op, Op::Div | Op::Rem)
                    {
                        Err(Error::Overflow)
                    } else {
                        let result = match op {
                            Op::Add => left + right,
                            Op::Sub => left - right,
                            Op::Mul => left * right,
                            Op::Div => left / right,
                            Op::Rem => left % right,
                        };
                        if (minimum..=maximum).contains(&result) {
                            Ok(value(kind, result.into()))
                        } else {
                            Err(Error::Overflow)
                        }
                    };
                    assert_eq!(
                        value(kind, left.into()).checked(op, value(kind, right.into()), 64),
                        expected,
                        "{kind:?}: {left} {op:?} {right}"
                    );
                }
            }
        }
    }
}

#[test]
fn full_u128_and_i128_values_do_not_round_trip_through_host_usize_or_i64() {
    let high = Value::new(ScalarType::U128, false, u128::MAX, 64).unwrap();
    assert_eq!(
        high.checked(Op::Div, value(ScalarType::U128, 2), 64)
            .unwrap()
            .magnitude(),
        u128::MAX / 2
    );
    assert_eq!(
        high.checked(Op::Rem, value(ScalarType::U128, 2), 64),
        Ok(value(ScalarType::U128, 1))
    );
    let minimum = value(ScalarType::I128, i128::MIN);
    assert_eq!(
        minimum.checked(Op::Div, value(ScalarType::I128, 2), 64),
        Ok(value(ScalarType::I128, i128::MIN / 2))
    );
    assert_eq!(
        minimum.checked(Op::Add, value(ScalarType::I128, i128::MAX), 64),
        Ok(value(ScalarType::I128, -1))
    );
}

#[test]
fn target_sized_domains_depend_on_the_declared_target_not_the_host() {
    for bits in [32, 64] {
        let unsigned_max = (1u128 << bits) - 1;
        let signed_min = 1u128 << (bits - 1);
        assert!(Value::new(ScalarType::Usize, false, unsigned_max, bits).is_ok());
        assert_eq!(
            Value::new(ScalarType::Usize, false, unsigned_max + 1, bits),
            Err(Error::Overflow)
        );
        assert!(Value::new(ScalarType::Isize, true, signed_min, bits).is_ok());
        assert_eq!(
            Value::new(ScalarType::Isize, false, signed_min, bits),
            Err(Error::Overflow)
        );
    }
    let wide = Value::new(ScalarType::Usize, false, 1u128 << 32, 64).unwrap();
    assert_eq!(
        wide.checked(Op::Add, value(ScalarType::Usize, 0), 32),
        Err(Error::Overflow)
    );
    assert_eq!(
        Expr::Literal(wide).normalize(32, &mut 1),
        Err(Error::Overflow)
    );
    for width in [0, 16, 128, u32::MAX] {
        assert_eq!(
            Value::new(ScalarType::Usize, false, 0, width),
            Err(Error::InvalidTargetWidth)
        );
    }
}

#[test]
fn structural_values_do_not_coerce_between_integer_kinds_or_noninteger_domains() {
    assert_eq!(
        value(ScalarType::U32, 1).checked(Op::Add, value(ScalarType::Usize, 1), 64),
        Err(Error::KindMismatch)
    );
    assert_ne!(value(ScalarType::U32, 1), value(ScalarType::Usize, 1));
    for kind in [
        ScalarType::Bool,
        ScalarType::F32,
        ScalarType::F64,
        ScalarType::Char,
        ScalarType::Text,
        ScalarType::Bytes,
    ] {
        assert_eq!(Value::new(kind, false, 0, 64), Err(Error::NonIntegerKind));
        assert_eq!(
            Expr::Param {
                index: 0,
                scalar: kind
            }
            .normalize(64, &mut 1),
            Err(Error::NonIntegerKind)
        );
    }
}

#[test]
fn array_lengths_reject_negative_and_target_index_overflow() {
    assert_eq!(
        value(ScalarType::I128, -1).array_length(64),
        Err(Error::NegativeArrayLength)
    );
    assert_eq!(value(ScalarType::I128, 0).array_length(32), Ok(0));
    let boundary = Value::new(ScalarType::U128, false, u32::MAX.into(), 64).unwrap();
    assert_eq!(boundary.array_length(32), Ok(u32::MAX.into()));
    let wide = boundary
        .checked(Op::Add, value(ScalarType::U128, 1), 64)
        .unwrap();
    assert_eq!(wide.array_length(32), Err(Error::Overflow));
    assert_eq!(wide.array_length(64), Ok(1u64 << 32));
    assert_eq!(
        Value::new(ScalarType::U128, false, u64::MAX as u128 + 1, 64)
            .unwrap()
            .array_length(64),
        Err(Error::Overflow)
    );
}

#[test]
fn symbolic_normalization_retains_kinds_and_is_canonical_and_idempotent() {
    let parameter = Expr::Param {
        index: 0,
        scalar: ScalarType::Usize,
    };
    let one = Expr::Literal(value(ScalarType::Usize, 1));
    let first = binary(Op::Add, parameter.clone(), one.clone())
        .normalize(64, &mut 20)
        .unwrap();
    let reversed = binary(Op::Add, one, parameter)
        .normalize(64, &mut 20)
        .unwrap();
    assert_eq!(first, reversed);
    assert_eq!(first.normalize(64, &mut 20).unwrap(), first);
    assert_eq!(
        first.substitute(&[Expr::Literal(value(ScalarType::Usize, 41))], 64, &mut 20),
        Ok(Expr::Literal(value(ScalarType::Usize, 42)))
    );
    assert_eq!(
        first.substitute(&[Expr::Literal(value(ScalarType::U32, 41))], 64, &mut 20),
        Err(Error::KindMismatch)
    );
}

#[test]
fn substitution_is_simultaneous_and_does_not_capture_argument_binders() {
    let parameter = Expr::Param {
        index: 0,
        scalar: ScalarType::Usize,
    };
    let argument = Expr::Param {
        index: 1,
        scalar: ScalarType::Usize,
    };
    assert_eq!(
        parameter.substitute(
            &[
                argument.clone(),
                Expr::Literal(value(ScalarType::Usize, 42))
            ],
            64,
            &mut 5
        ),
        Ok(argument)
    );
    assert_eq!(parameter.substitute(&[], 64, &mut 1), Ok(parameter));
}

#[test]
fn symbolic_cancellation_cannot_hide_checked_overflow() {
    let parameter = Expr::Param {
        index: 0,
        scalar: ScalarType::U8,
    };
    let sum = binary(Op::Add, parameter, Expr::Literal(value(ScalarType::U8, 1)));
    let expression = binary(Op::Sub, sum.clone(), sum);
    assert!(matches!(
        expression.normalize(64, &mut 20),
        Ok(Expr::Binary { .. })
    ));
    assert_eq!(
        expression.substitute(&[Expr::Literal(value(ScalarType::U8, 255))], 64, &mut 20),
        Err(Error::Overflow)
    );
}

#[test]
fn proof_work_and_recursion_depth_are_bounded_with_explicit_failures() {
    let expression = binary(
        Op::Add,
        Expr::Literal(value(ScalarType::U32, 1)),
        Expr::Literal(value(ScalarType::U32, 2)),
    );
    assert_eq!(expression.normalize(64, &mut 2), Err(Error::ResourceLimit));
    let mut exact = 3;
    assert_eq!(
        expression.normalize(64, &mut exact),
        Ok(Expr::Literal(value(ScalarType::U32, 3)))
    );
    assert_eq!(exact, 0);
    let mut deep = Expr::Param {
        index: 0,
        scalar: ScalarType::I32,
    };
    for _ in 0..128 {
        deep = Expr::Neg(Box::new(deep));
    }
    assert_eq!(deep.normalize(64, &mut 1000), Err(Error::ResourceLimit));
    let parameter = Expr::Param {
        index: 0,
        scalar: ScalarType::U32,
    };
    assert_eq!(
        parameter.substitute(&[expression], 64, &mut 3),
        Err(Error::ResourceLimit)
    );
}

#[test]
fn existing_u32_const_pipeline_uses_the_checked_integer_kernel() {
    assert_eq!(
        IntegerConstExpr::binary(grandiose_stage0::types::integer_const::IntegerConstOp::Add,
            Box::new(IntegerConstExpr::Literal(41u32.into())),
            Box::new(IntegerConstExpr::Literal(1u32.into()))
        )
        .normalized(),
        Ok(IntegerConstExpr::Literal(42u32.into()))
    );
    assert_eq!(
        IntegerConstExpr::binary(grandiose_stage0::types::integer_const::IntegerConstOp::Add,
            Box::new(IntegerConstExpr::Literal(u32::MAX.into())),
            Box::new(IntegerConstExpr::Literal(1u32.into()))
        )
        .normalized(),
        Err(StructuralConstError::Overflow)
    );
    assert_eq!(
        IntegerConstExpr::binary(grandiose_stage0::types::integer_const::IntegerConstOp::Rem,
            Box::new(IntegerConstExpr::Literal(1u32.into())),
            Box::new(IntegerConstExpr::Literal(0u32.into()))
        )
        .normalized(),
        Err(StructuralConstError::DivisionByZero)
    );
}
