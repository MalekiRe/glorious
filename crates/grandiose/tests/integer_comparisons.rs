use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

const SOURCE: &str = r#"
    struct Stats { n: usize }
    effect OrderedOperand { read(value: i64) -> i64 }

    signed_eq(a: i64, b: i64) -> Bool { a == b }
    signed_ne(a: i64, b: i64) -> Bool { a != b }
    signed_lt(a: i64, b: i64) -> Bool { a < b }
    signed_le(a: i64, b: i64) -> Bool { a <= b }
    signed_gt(a: i64, b: i64) -> Bool { a > b }
    signed_ge(a: i64, b: i64) -> Bool { a >= b }

    unsigned_eq(a: u128, b: u128) -> Bool { a == b }
    unsigned_ne(a: u128, b: u128) -> Bool { a != b }
    unsigned_lt(a: u128, b: u128) -> Bool { a < b }
    unsigned_le(a: u128, b: u128) -> Bool { a <= b }
    unsigned_gt(a: u128, b: u128) -> Bool { a > b }
    unsigned_ge(a: u128, b: u128) -> Bool { a >= b }

    size_eq(a: usize, b: usize) -> Bool { a == b }
    size_ne(a: usize, b: usize) -> Bool { a != b }
    size_lt(a: usize, b: usize) -> Bool { a < b }
    size_le(a: usize, b: usize) -> Bool { a <= b }
    size_gt(a: usize, b: usize) -> Bool { a > b }
    size_ge(a: usize, b: usize) -> Bool { a >= b }

    left() -> i64 / {OrderedOperand} { perform OrderedOperand::read(4) }
    right() -> i64 / {OrderedOperand} { perform OrderedOperand::read(9) }
    ordered() -> Bool / {OrderedOperand} { left() < right() }
    literal_left_size(size: usize) -> Bool { 0 < size }
    size(value: usize) -> usize { value }
    field_left() -> Bool {
        let stats = Stats { n: size(3) };
        0 < stats.n
    }
    field_right() -> Bool {
        let stats = Stats { n: size(3) };
        stats.n > 0
    }
    reference_field_left() -> Bool {
        let stats = Stats { n: size(3) };
        let reference = &stats;
        0 < reference.n
    }
    reference_field_right() -> Bool {
        let stats = Stats { n: size(3) };
        let reference = &stats;
        reference.n > 0
    }
    deref_left() -> Bool {
        let n = size(3);
        let reference = &n;
        0 < *reference
    }
    deref_right() -> Bool {
        let n = size(3);
        let reference = &n;
        *reference > 0
    }
    arithmetic_left() -> Bool {
        let stats = Stats { n: size(3) };
        0 < stats.n + 1
    }
    arithmetic_right() -> Bool {
        let stats = Stats { n: size(3) };
        stats.n + 1 > 0
    }
    block_left() -> Bool {
        let stats = Stats { n: size(3) };
        0 < { let projected = stats.n; projected }
    }
    block_right() -> Bool {
        let stats = Stats { n: size(3) };
        { let projected = stats.n; projected } > 0
    }
    constant_true() -> Bool { 2 < 3 }
    constant_false() -> Bool { 3 < 2 }
    main() -> () { () }
"#;

fn function(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function {name}")) as u32
}

fn code<'a>(
    artifact: &'a grandiose_vm::Artifact,
    function: &grandiose_vm::Function,
) -> &'a [Instruction] {
    &artifact.code[function.code_start as usize..(function.code_start + function.code_len) as usize]
}

fn expected_bool(ty: u32, value: bool) -> Value {
    Value::aggregate_with_variant(ty, Some(u32::from(!value)), [Value::Unit])
}

#[test]
fn integer_comparisons_lower_to_each_frozen_primitive_and_source_bool() {
    let operations = [
        ("eq", Primitive::IntEq),
        ("ne", Primitive::IntNe),
        ("lt", Primitive::IntLt),
        ("le", Primitive::IntLe),
        ("gt", Primitive::IntGt),
        ("ge", Primitive::IntGe),
    ];
    let signed_expected = [false, true, true, true, false, false];
    let positive_expected = [false, true, false, false, true, true];

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "integer-comparisons.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let verified = verify(artifact.clone()).unwrap();
        let vm = Vm::new(verified);

        for (name, expected) in [("constant_true", true), ("constant_false", false)] {
            let id = function(&artifact, name);
            let body = &artifact.functions[id as usize];
            assert_eq!(
                vm.run(id, vec![]).unwrap(),
                expected_bool(body.return_type, expected),
                "constant comparison produced the wrong Bool at {optimization_level:?}"
            );
        }
        let literal_left_size = function(&artifact, "literal_left_size");
        let literal_left_body = &artifact.functions[literal_left_size as usize];
        assert_eq!(
            vm.run(literal_left_size, vec![Value::U64(1)]).unwrap(),
            expected_bool(literal_left_body.return_type, true),
        );
        for name in [
            "field_left",
            "field_right",
            "reference_field_left",
            "reference_field_right",
            "deref_left",
            "deref_right",
            "arithmetic_left",
            "arithmetic_right",
            "block_left",
            "block_right",
        ] {
            let id = function(&artifact, name);
            let body = &artifact.functions[id as usize];
            assert_eq!(
                vm.run(id, vec![]).unwrap(),
                expected_bool(body.return_type, true),
                "typed comparison context failed for {name} at {optimization_level:?}"
            );
        }

        for (index, (suffix, primitive)) in operations.iter().enumerate() {
            for (prefix, arguments, expected) in [
                (
                    "signed",
                    vec![Value::I64(-7), Value::I64(3)],
                    signed_expected[index],
                ),
                (
                    "unsigned",
                    vec![Value::U128(7), Value::U128(3)],
                    positive_expected[index],
                ),
                (
                    "size",
                    vec![Value::U64(7), Value::U64(3)],
                    positive_expected[index],
                ),
            ] {
                let name = format!("{prefix}_{suffix}");
                let id = function(&artifact, &name);
                let body = &artifact.functions[id as usize];
                assert!(
                    code(&artifact, body).iter().any(|instruction| matches!(
                        instruction,
                        Instruction::Primitive { op, .. } if *op == *primitive
                    )),
                    "{name} at {optimization_level:?} did not retain {primitive:?}"
                );
                assert_eq!(
                    vm.run(id, arguments).unwrap(),
                    expected_bool(body.return_type, expected),
                    "wrong source Bool for {name} at {optimization_level:?}"
                );
            }
        }
    }
}

#[test]
fn comparison_operands_remain_left_to_right() {
    // The helpers perform an outward effect, so their calls are observable and
    // cannot be folded away before this test checks source operand order.
    let artifact = compile_source_to_bytecode_with_options(
        "ordered-comparison.glorious",
        SOURCE,
        CompileOptions {
            optimization_level: OptimizationLevel::O1,
        },
    )
    .unwrap();
    let ordered = &artifact.functions[function(&artifact, "ordered") as usize];
    let ordered_code = code(&artifact, ordered);
    let calls = ordered_code
        .iter()
        .filter_map(|instruction| match instruction {
            Instruction::Call { function, .. } => Some(*function),
            _ => None,
        })
        .collect::<Vec<_>>();
    assert_eq!(calls.len(), 2);
    assert_eq!(calls[0], function(&artifact, "left"));
    assert_eq!(calls[1], function(&artifact, "right"));
    let comparison = ordered_code
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                Instruction::Primitive {
                    op: Primitive::IntLt,
                    ..
                }
            )
        })
        .unwrap();
    let conversion_call = ordered_code
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                Instruction::TailCall { function: target, .. }
                    if *target == function(&artifact, "__g1_bool_from_u32")
            )
        })
        .unwrap();
    assert!(comparison < conversion_call);
}

#[test]
fn mixed_integer_types_are_rejected() {
    let diagnostics = compile_source_to_bytecode(
        "mixed-comparison.glorious",
        "bad(left: u8, right: u16) -> Bool { left == right } main() -> () { () }",
    )
    .unwrap_err();
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.message.contains("expected u8, found u16")
            || diagnostic.message.contains("same-typed integer operands")
    }));
}

#[test]
fn refinement_binders_shadow_function_items_only_in_the_positive_branch() {
    let source = r#"
        left() -> i64 { 99 }
        ok() -> Result<i64, ()> { Result::Ok(7) }
        err() -> Result<i64, ()> { Result::Err(()) }
        positive() -> i64 {
            let selected = ok();
            if(selected is Result::Ok(left)) { left } else { left() }
        }
        negative() -> i64 {
            let selected = err();
            if(selected is Result::Ok(left)) { left } else { left() }
        }
        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "refinement-function-item-shadowing.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(function(&artifact, "positive"), vec![]).unwrap(),
            Value::I64(7),
            "{optimization_level:?}"
        );
        assert_eq!(
            vm.run(function(&artifact, "negative"), vec![]).unwrap(),
            Value::I64(99),
            "{optimization_level:?}"
        );
    }

    let diagnostics = compile_source_to_bytecode(
        "negative-refinement-scope.glorious",
        r#"
        bad(selected: Result<i64, ()>) -> i64 {
            if(selected is Result::Ok(found)) { 0 } else { found }
        }
        main() -> () { () }
        "#,
    )
    .unwrap_err();
    assert!(
        diagnostics.iter().any(|diagnostic| {
            diagnostic.code.as_deref() == Some("G1BC001")
                && diagnostic.message.contains("`found`")
                && diagnostic
                    .message
                    .contains("not a parameter, local, or immutable global")
        }),
        "{diagnostics:#?}"
    );
}
