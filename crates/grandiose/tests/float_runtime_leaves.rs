use grandiose::{
    CompileOptions, ManifestPrimitiveLeaf, OptimizationLevel, TrustedRuntimeManifest,
    TrustedTraitManifest, compile_bundle_to_phases_with_manifest_and_options,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Primitive, Value, Vm, verify};

const INTEGERS: [&str; 12] = [
    "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize",
];

fn fixture() -> (SourceBundle, TrustedTraitManifest) {
    let mut source = String::new();
    let mut leaves = Vec::new();
    let mut id = 1_u64;
    let mut add_leaf = |name: String, primitive: Primitive, declaration: String| {
        source.push_str(&declaration);
        source.push('\n');
        leaves.push(ManifestPrimitiveLeaf {
            id,
            display_name: name,
            primitive,
        });
        id += 1;
    };

    for width in ["f32", "f64"] {
        for (operation, primitive) in [
            ("add", Primitive::FloatAdd),
            ("sub", Primitive::FloatSub),
            ("mul", Primitive::FloatMul),
            ("div", Primitive::FloatDiv),
            ("rem", Primitive::FloatRem),
        ] {
            let name = format!("__g1_{width}_{operation}");
            add_leaf(
                name.clone(),
                primitive,
                format!("{name}(left: {width}, right: {width}) -> {width} {{ () }}"),
            );
        }
        let name = format!("__g1_{width}_neg");
        add_leaf(
            name.clone(),
            Primitive::FloatNeg,
            format!("{name}(value: {width}) -> {width} {{ () }}"),
        );
        for (operation, primitive) in [
            ("eq", Primitive::FloatEq),
            ("ne", Primitive::FloatNe),
            ("lt", Primitive::FloatLt),
            ("le", Primitive::FloatLe),
            ("gt", Primitive::FloatGt),
            ("ge", Primitive::FloatGe),
        ] {
            let name = format!("__g1_{width}_{operation}");
            add_leaf(
                name.clone(),
                primitive,
                format!("{name}(left: {width}, right: {width}) -> u32 {{ () }}"),
            );
        }
    }
    for (name, source_ty, target_ty, primitive) in [
        ("__g1_f32_to_f64", "f32", "f64", Primitive::FloatConvert),
        ("__g1_f64_to_f32", "f64", "f32", Primitive::FloatConvert),
        ("__g1_f32_to_bits", "f32", "u32", Primitive::FloatToBits),
        ("__g1_f32_from_bits", "u32", "f32", Primitive::FloatFromBits),
        ("__g1_f64_to_bits", "f64", "u64", Primitive::FloatToBits),
        ("__g1_f64_from_bits", "u64", "f64", Primitive::FloatFromBits),
    ] {
        add_leaf(
            name.into(),
            primitive,
            format!("{name}(value: {source_ty}) -> {target_ty} {{ () }}"),
        );
    }
    for target in ["f32", "f64"] {
        for source_ty in INTEGERS {
            let name = format!("__g1_{source_ty}_to_{target}");
            add_leaf(
                name.clone(),
                Primitive::IntToFloat,
                format!("{name}(value: {source_ty}) -> {target} {{ () }}"),
            );
        }
    }
    for source_ty in ["f32", "f64"] {
        for target in INTEGERS {
            let name = format!("__g1_{source_ty}_to_{target}_checked");
            add_leaf(
                name.clone(),
                Primitive::FloatToIntChecked,
                format!("{name}(value: {source_ty}) -> {target} {{ () }}"),
            );
        }
    }

    for width in ["f32", "f64"] {
        let bits = if width == "f32" { "u32" } else { "u64" };
        for operation in ["add", "sub", "mul", "div", "rem"] {
            source.push_str(&format!(
                "case_{width}_{operation}() -> {bits} {{ __g1_{width}_to_bits(__g1_{width}_{operation}(7.5, 2.0)) }}\n"
            ));
        }
        source.push_str(&format!(
            "case_{width}_neg() -> {bits} {{ __g1_{width}_to_bits(__g1_{width}_neg(0.0)) }}\n"
        ));
        for operation in ["eq", "ne", "lt", "le", "gt", "ge"] {
            source.push_str(&format!(
                "case_{width}_{operation}() -> u32 {{ __g1_{width}_{operation}(1.0, 2.0) }}\n"
            ));
        }
    }
    source.push_str(
        "case_f32_to_f64() -> u64 { __g1_f64_to_bits(__g1_f32_to_f64(1.5)) }\n\
         case_f64_to_f32() -> u32 { __g1_f32_to_bits(__g1_f64_to_f32(1.5)) }\n\
         case_f32_nan() -> u32 { __g1_f32_to_bits(__g1_f32_from_bits(2143289345)) }\n\
         case_f64_nan() -> u64 { __g1_f64_to_bits(__g1_f64_from_bits(9221120237041090561)) }\n\
         case_f32_nan_div() -> u32 { __g1_f32_to_bits(__g1_f32_div(0.0, 0.0)) }\n\
         case_f64_nan_div() -> u64 { __g1_f64_to_bits(__g1_f64_div(0.0, 0.0)) }\n\
         case_f32_negative_zero() -> u32 { __g1_f32_to_bits(__g1_f32_from_bits(2147483648)) }\n\
         case_f64_negative_zero() -> u64 { __g1_f64_to_bits(__g1_f64_from_bits(9223372036854775808)) }\n",
    );
    for integer in INTEGERS {
        source.push_str(&format!(
            "case_{integer}_to_f32() -> u32 {{ __g1_f32_to_bits(__g1_{integer}_to_f32(7)) }}\n\
             case_{integer}_to_f64() -> u64 {{ __g1_f64_to_bits(__g1_{integer}_to_f64(7)) }}\n\
             case_f32_to_{integer}() -> {integer} {{ __g1_f32_to_{integer}_checked(7.75) }}\n\
             case_f64_to_{integer}() -> {integer} {{ __g1_f64_to_{integer}_checked(7.75) }}\n"
        ));
    }

    let runtime = TrustedRuntimeManifest::new(vec![], leaves).unwrap();
    let manifest = TrustedTraitManifest::trusted_default().with_runtime(runtime);
    let mut primary = String::from("main() -> () {\n");
    for line in source.lines() {
        let line = line.trim();
        let Some((name, _)) = line.split_once('(') else {
            continue;
        };
        if name.starts_with("case_") {
            primary.push_str(name);
            primary.push_str("();\n");
        }
    }
    primary.push_str("() }\n");
    let bundle = SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new("float-std.glorious", source),
        Segment::new("main.glorious", primary),
        [],
    );
    (bundle, manifest)
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

fn integer_value(ty: &str) -> Value {
    match ty {
        "u128" => Value::U128(7),
        "i128" => Value::I128(7),
        ty if ty.starts_with('u') => Value::U64(7),
        _ => Value::I64(7),
    }
}

#[test]
fn concrete_float_leaves_execute_at_every_optimization_level() {
    let (bundle, manifest) = fixture();
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_bundle_to_phases_with_manifest_and_options(
            &bundle,
            &manifest,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        let run = |name: &str| {
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, name), vec![])
                .unwrap()
        };
        for (width, to_bits) in [("f32", true), ("f64", false)] {
            let expected: [(&str, f64); 5] = [
                ("add", 9.5),
                ("sub", 5.5),
                ("mul", 15.0),
                ("div", 3.75),
                ("rem", 1.5),
            ];
            for (operation, expected) in expected {
                let expected = if to_bits {
                    Value::U64(u64::from((expected as f32).to_bits()))
                } else {
                    Value::U64(expected.to_bits())
                };
                assert_eq!(run(&format!("case_{width}_{operation}")), expected);
            }
            let negative_zero = if to_bits {
                Value::U64(u64::from((-0.0_f32).to_bits()))
            } else {
                Value::U64((-0.0_f64).to_bits())
            };
            assert_eq!(
                run(&format!("case_{width}_neg")),
                negative_zero,
                "{optimization_level:?} {width} negation must preserve signed zero"
            );
            for (operation, expected) in [
                ("eq", 0),
                ("ne", 1),
                ("lt", 1),
                ("le", 1),
                ("gt", 0),
                ("ge", 0),
            ] {
                assert_eq!(
                    run(&format!("case_{width}_{operation}")),
                    Value::U64(expected)
                );
            }
        }
        assert_eq!(run("case_f32_to_f64"), Value::U64(1.5_f64.to_bits()));
        assert_eq!(
            run("case_f64_to_f32"),
            Value::U64(u64::from(1.5_f32.to_bits()))
        );
        assert_eq!(run("case_f32_nan"), Value::U64(0x7fc0_0000));
        assert_eq!(run("case_f64_nan"), Value::U64(0x7ff8_0000_0000_0000));
        assert_eq!(run("case_f32_nan_div"), Value::U64(0x7fc0_0000));
        assert_eq!(run("case_f64_nan_div"), Value::U64(0x7ff8_0000_0000_0000));
        assert_eq!(run("case_f32_negative_zero"), Value::U64(0x8000_0000));
        assert_eq!(
            run("case_f64_negative_zero"),
            Value::U64(0x8000_0000_0000_0000)
        );
        for integer in INTEGERS {
            assert_eq!(
                run(&format!("case_{integer}_to_f32")),
                Value::U64(u64::from(7.0_f32.to_bits()))
            );
            assert_eq!(
                run(&format!("case_{integer}_to_f64")),
                Value::U64(7.0_f64.to_bits())
            );
            assert_eq!(
                run(&format!("case_f32_to_{integer}")),
                integer_value(integer)
            );
            assert_eq!(
                run(&format!("case_f64_to_{integer}")),
                integer_value(integer)
            );
        }
    }
}

#[test]
fn float_leaf_declarations_require_the_exact_concrete_signature() {
    let manifest = TrustedTraitManifest::trusted_default().with_runtime(
        TrustedRuntimeManifest::new(
            vec![],
            vec![ManifestPrimitiveLeaf {
                id: 1,
                display_name: "bad_add".into(),
                primitive: Primitive::FloatAdd,
            }],
        )
        .unwrap(),
    );
    let bundle = SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new(
            "bad-float-std.glorious",
            "bad_add(left: f32, right: f64) -> f32 { () }",
        ),
        Segment::new("main.glorious", "main() -> () { () }"),
        [],
    );
    let messages = compile_bundle_to_phases_with_manifest_and_options(
        &bundle,
        &manifest,
        CompileOptions::default(),
    )
    .unwrap_err()
    .into_iter()
    .map(|diagnostic| diagnostic.message)
    .collect::<Vec<_>>();
    assert!(
        messages
            .iter()
            .any(|message| message.contains("does not match the frozen FloatAdd signature")),
        "{messages:#?}"
    );
}
