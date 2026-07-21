use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Instruction, Primitive, Value, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<InterpreterValue>,
        span: Span,
    ) -> Result<InterpreterValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected effect",
            "integer arithmetic must not perform host effects",
            span,
        ))
    }
}

const INTEGER_TYPES: [&str; 12] = [
    "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
];

fn arithmetic_source() -> String {
    let mut source = String::new();
    for ty in INTEGER_TYPES {
        for (name, operator) in [
            ("add", "+"),
            ("sub", "-"),
            ("mul", "*"),
            ("div", "/"),
            ("rem", "%"),
        ] {
            source.push_str(&format!(
                "{name}_{ty}(left: {ty}, right: {ty}) -> {ty} {{ left {operator} right }}\n"
            ));
        }
    }
    source.push_str("main() -> { () }");
    source
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

fn scalar(ty: &str, signed: i128, unsigned: u128) -> Value {
    match ty {
        "i128" => Value::I128(signed),
        "i8" | "i16" | "i32" | "i64" | "isize" => Value::I64(signed as i64),
        "u128" => Value::U128(unsigned),
        "u8" | "u16" | "u32" | "u64" | "usize" => Value::U64(unsigned as u64),
        _ => unreachable!("test integer type table is exhaustive"),
    }
}

fn bounds(ty: &str) -> (Value, Value) {
    match ty {
        "i8" => (Value::I64(i8::MIN.into()), Value::I64(i8::MAX.into())),
        "i16" => (Value::I64(i16::MIN.into()), Value::I64(i16::MAX.into())),
        "i32" => (Value::I64(i32::MIN.into()), Value::I64(i32::MAX.into())),
        "i64" | "isize" => (Value::I64(i64::MIN), Value::I64(i64::MAX)),
        "i128" => (Value::I128(i128::MIN), Value::I128(i128::MAX)),
        "u8" => (Value::U64(0), Value::U64(u8::MAX.into())),
        "u16" => (Value::U64(0), Value::U64(u16::MAX.into())),
        "u32" => (Value::U64(0), Value::U64(u32::MAX.into())),
        "u64" | "usize" => (Value::U64(0), Value::U64(u64::MAX)),
        "u128" => (Value::U128(0), Value::U128(u128::MAX)),
        _ => unreachable!("test integer type table is exhaustive"),
    }
}

#[test]
fn all_checked_integer_operators_execute_at_every_width_from_o0_through_o3() {
    let source = arithmetic_source();
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "all-integer-arithmetic.gr",
            &source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for ty in INTEGER_TYPES {
            let left = scalar(ty, 23, 23);
            let right = scalar(ty, 5, 5);
            for (name, expected) in [
                ("add", scalar(ty, 28, 28)),
                ("sub", scalar(ty, 18, 18)),
                ("mul", scalar(ty, 115, 115)),
                ("div", scalar(ty, 4, 4)),
                ("rem", scalar(ty, 3, 3)),
            ] {
                let result = Vm::new(verified.clone())
                    .run(
                        function_id(&phases.artifact, &format!("{name}_{ty}")),
                        vec![left.clone(), right.clone()],
                    )
                    .unwrap();
                assert_eq!(result, expected, "{level:?} {name} on {ty}");
            }
        }
    }
}

#[test]
fn long_left_associated_arithmetic_chains_do_not_use_the_host_call_stack() {
    let mut expression = String::from("1000");
    for _ in 0..32 {
        expression.push_str(" - 1");
    }
    let source = format!("answer() -> i64 {{ {expression} }} main() -> () {{ () }}");
    let phases = compile_source_to_phases_with_options(
        "long-arithmetic-chain.gr",
        &source,
        CompileOptions::default(),
    )
    .unwrap();
    let verified = verify(phases.artifact.clone()).unwrap();
    assert_eq!(
        Vm::new(verified)
            .run(function_id(&phases.artifact, "answer"), vec![])
            .unwrap(),
        Value::I64(968)
    );
}

#[test]
fn checked_boundaries_trap_for_signed_and_unsigned_types_at_every_level() {
    let source = arithmetic_source();
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "integer-boundaries.gr",
            &source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for ty in INTEGER_TYPES {
            let (minimum, maximum) = bounds(ty);
            let one = scalar(ty, 1, 1);
            let zero = scalar(ty, 0, 0);
            let add = function_id(&phases.artifact, &format!("add_{ty}"));
            let div = function_id(&phases.artifact, &format!("div_{ty}"));
            let rem = function_id(&phases.artifact, &format!("rem_{ty}"));

            let overflow = Vm::new(verified.clone())
                .run(add, vec![maximum, one.clone()])
                .unwrap_err()
                .to_string();
            assert!(
                overflow.contains("checked arithmetic overflow"),
                "{level:?} {ty}: {overflow}"
            );

            for function in [div, rem] {
                let error = Vm::new(verified.clone())
                    .run(function, vec![one.clone(), zero.clone()])
                    .unwrap_err()
                    .to_string();
                assert!(
                    error.contains("division by zero"),
                    "{level:?} {ty}: {error}"
                );
            }

            if ty.starts_with('i') {
                let negative_one = scalar(ty, -1, 0);
                for function in [div, rem] {
                    let error = Vm::new(verified.clone())
                        .run(function, vec![minimum.clone(), negative_one.clone()])
                        .unwrap_err()
                        .to_string();
                    assert!(
                        error.contains("checked arithmetic overflow"),
                        "{level:?} {ty}: {error}"
                    );
                }
            } else {
                let sub = function_id(&phases.artifact, &format!("sub_{ty}"));
                let error = Vm::new(verified.clone())
                    .run(sub, vec![minimum, one])
                    .unwrap_err()
                    .to_string();
                assert!(
                    error.contains("checked arithmetic overflow"),
                    "{level:?} {ty}: {error}"
                );
            }
        }
    }
}

#[test]
fn mixed_source_integer_types_are_rejected_for_every_arithmetic_operator() {
    for operator in ["+", "-", "*", "/", "%"] {
        let source = format!(
            "bad(left: u8, right: u16) -> u8 {{ left {operator} right }} main() -> {{ () }}"
        );
        let diagnostics = compile_source_to_phases_with_options(
            "mixed-integer-arithmetic.gr",
            &source,
            CompileOptions::default(),
        )
        .unwrap_err();
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.message.contains("type mismatch")
                    || diagnostic.message.contains("expected u8")
            }),
            "operator {operator}: {diagnostics:#?}"
        );
    }
}

#[test]
fn recovery_interpreter_preserves_typed_remainder_values_and_traps() {
    for ty in INTEGER_TYPES {
        let signed = ty.starts_with('i');
        let bits = match ty {
            "i8" | "u8" => 8,
            "i16" | "u16" => 16,
            "i32" | "u32" => 32,
            "i64" | "u64" | "isize" | "usize" => 64,
            "i128" | "u128" => 128,
            _ => unreachable!("integer type table is exhaustive"),
        };
        let dividend = if signed { -23 } else { 23 };
        let source = format!(
            "typed(value: {ty}) -> {ty} {{ value }} main() -> {ty} {{ typed({dividend}) % 5 }}"
        );
        let expected = if signed && bits == 64 {
            InterpreterValue::Int(-3)
        } else {
            let mask = if bits == 128 {
                u128::MAX
            } else {
                (1_u128 << bits) - 1
            };
            InterpreterValue::Integer {
                signed,
                bits,
                raw: if signed { (-3_i128) as u128 & mask } else { 3 },
            }
        };
        assert_eq!(
            run_source(
                &format!("recovery-{ty}-rem.gr"),
                &source,
                vec![],
                &mut NoHost
            )
            .unwrap(),
            expected,
            "recovery remainder must preserve {ty}"
        );
    }

    for ty in ["u8", "u16", "u32", "u64", "u128", "usize"] {
        let source = format!(
            "typed(value: {ty}) -> {ty} {{ value }} main() -> {ty} {{ typed(1) % typed(0) }}"
        );
        let diagnostics =
            run_source("recovery-rem-zero.gr", &source, vec![], &mut NoHost).unwrap_err();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("zero")),
            "recovery {ty} remainder by zero must trap"
        );
    }

    for (ty, minimum) in [
        ("i8", "-128"),
        ("i16", "-32768"),
        ("i32", "-2147483648"),
        ("i64", "typed(-9223372036854775807) - typed(1)"),
        ("isize", "typed(-9223372036854775807) - typed(1)"),
    ] {
        let source = format!(
            "typed(value: {ty}) -> {ty} {{ value }} main() -> {ty} {{ ({minimum}) % typed(-1) }}"
        );
        let diagnostics =
            run_source("recovery-rem-overflow.gr", &source, vec![], &mut NoHost).unwrap_err();
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.message.contains("overflow")),
            "recovery {ty} MIN % -1 must trap"
        );
    }
}

#[test]
fn remainder_evaluates_effectful_operands_once_in_left_to_right_order() {
    let source = r#"
        effect Probe { [1,1] value(marker: i64) -> i64 }
        calculate() -> i64 {
            handle {
                perform Probe::value(1) % perform Probe::value(2)
            } {
                Probe::value(marker) with continuation =>
                    resume(continuation, marker * 10 + 3),
            }
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "remainder-order.gr",
            source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap();
        let calculate = function_id(&phases.artifact, "calculate");
        assert_eq!(
            phases
                .artifact
                .code
                .iter()
                .filter(|instruction| matches!(
                    instruction,
                    Instruction::Primitive {
                        op: Primitive::IntCheckedRem,
                        ..
                    }
                ))
                .count(),
            1,
            "{level:?} must retain exactly one remainder operation"
        );
        assert_eq!(
            Vm::new(verify(phases.artifact).unwrap())
                .run(calculate, vec![])
                .unwrap(),
            Value::I64(13),
            "{level:?} must evaluate 13 % 23 in source order"
        );
    }
}
