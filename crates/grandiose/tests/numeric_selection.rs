use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

const TYPES: [&str; 8] = ["i8", "i64", "i128", "isize", "u8", "u64", "u128", "usize"];

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
            "numeric selection must not reach the host",
            span,
        ))
    }
}

fn source() -> String {
    let mut source = String::new();
    for ty in TYPES {
        source.push_str(&format!(
            "min_{ty}(left: {ty}, right: {ty}) -> {ty} {{ min(left, right) }}\n\
             max_{ty}(left: {ty}, right: {ty}) -> {ty} {{ max(left, right) }}\n\
             clamp_{ty}(value: {ty}, lower: {ty}, upper: {ty}) -> {ty} {{\
                 clamp(value, lower, upper)\
             }}\n"
        ));
    }
    source.push_str("main() -> { () }");
    source
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing function `{name}`")) as u32
}

fn vm_value(ty: &str, value: i64) -> Value {
    match ty {
        "i128" => Value::I128(value.into()),
        "i8" | "i64" | "isize" => Value::I64(value),
        "u128" => Value::U128(value as u128),
        "u8" | "u64" | "usize" => Value::U64(value as u64),
        _ => unreachable!("representative type table is exhaustive"),
    }
}

fn interpreter_value(ty: &str, value: i64) -> InterpreterValue {
    let signed = ty.starts_with('i');
    let bits = match ty {
        "i8" | "u8" => 8,
        "i64" | "u64" | "isize" | "usize" => 64,
        "i128" | "u128" => 128,
        _ => unreachable!("representative type table is exhaustive"),
    };
    if ty == "i64" || ty == "isize" {
        InterpreterValue::Int(value)
    } else {
        let raw = if bits == 128 {
            value as u128
        } else {
            value as u128 & ((1_u128 << bits) - 1)
        };
        InterpreterValue::Integer { signed, bits, raw }
    }
}

#[test]
fn public_numeric_selection_runs_at_o1_through_o3() {
    let source = source();
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "numeric-selection.glorious",
            &source,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();

        for ty in TYPES {
            let (low, middle, high) = if ty.starts_with('i') {
                (-7, 3, 11)
            } else {
                (2, 7, 13)
            };
            for (name, arguments, expected) in [
                ("min", vec![high, low], low),
                ("min", vec![low, high], low),
                ("max", vec![high, low], high),
                ("max", vec![low, high], high),
                ("clamp", vec![low - 1, low, high], low),
                ("clamp", vec![low, low, high], low),
                ("clamp", vec![middle, low, high], middle),
                ("clamp", vec![high, low, high], high),
                ("clamp", vec![high + 1, low, high], high),
            ] {
                let function = function_id(&phases.artifact, &format!("{name}_{ty}"));
                let arguments = arguments
                    .into_iter()
                    .map(|value| vm_value(ty, value))
                    .collect();
                let actual = Vm::new(verified.clone()).run(function, arguments).unwrap();
                assert_eq!(
                    actual,
                    vm_value(ty, expected),
                    "{optimization_level:?} {name} on {ty}"
                );
            }
        }
    }
}

#[test]
fn recovery_interpreter_agrees_on_widths_and_clamp_boundaries() {
    for ty in TYPES {
        let (low, middle, high) = if ty.starts_with('i') {
            (-7, 3, 11)
        } else {
            (2, 7, 13)
        };
        for (label, expression, expected) in [
            ("min", format!("min(typed({high}), typed({low}))"), low),
            ("max", format!("max(typed({low}), typed({high}))"), high),
            (
                "clamp-low",
                format!("clamp(typed({}), typed({low}), typed({high}))", low - 1),
                low,
            ),
            (
                "clamp-lower-boundary",
                format!("clamp(typed({low}), typed({low}), typed({high}))"),
                low,
            ),
            (
                "clamp-middle",
                format!("clamp(typed({middle}), typed({low}), typed({high}))"),
                middle,
            ),
            (
                "clamp-upper-boundary",
                format!("clamp(typed({high}), typed({low}), typed({high}))"),
                high,
            ),
            (
                "clamp-high",
                format!("clamp(typed({}), typed({low}), typed({high}))", high + 1),
                high,
            ),
        ] {
            let source =
                format!("typed(value: {ty}) -> {ty} {{ value }} main() -> {ty} {{ {expression} }}");
            assert_eq!(
                run_source(
                    &format!("recovery-{label}-{ty}.glorious"),
                    &source,
                    vec![],
                    &mut NoHost,
                )
                .unwrap(),
                interpreter_value(ty, expected),
                "recovery {label} on {ty}"
            );
        }
    }
}
