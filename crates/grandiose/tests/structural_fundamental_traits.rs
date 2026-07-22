use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options,
    eval::{Host, Value as RecoveryValue},
    run_source,
    span::Span,
};
use grandiose_vm::{Value, Vm, verify};

#[derive(Default)]
struct NoHost;

impl Host for NoHost {
    fn perform(
        &mut self,
        _effect: &str,
        _operation: &str,
        _args: Vec<RecoveryValue>,
        span: Span,
    ) -> Result<RecoveryValue, grandiose::diagnostic::Diagnostic> {
        Err(grandiose::diagnostic::Diagnostic::error(
            "unexpected effect",
            "structural trait execution performed a host effect",
            span,
        ))
    }
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing bytecode function `{name}`")) as u32
}

const SURFACE: &str = r#"
    effect Finished { inspect(value: Result<String, Utf8Error>) -> !; }

    hash_pair(value: &(i64, i64)) -> u64 {
        let state = Hasher::new();
        Hash::hash(value, &mut state);
        Hasher::finish(&state)
    }
    display_result(value: &Result<i64, i64>, formatter: &mut Formatter) -> () {
        Display::fmt(value, move formatter)
    }
    debug_result(value: &Result<i64, i64>, formatter: &mut Formatter) -> () {
        Debug::fmt(value, move formatter)
    }

    default_result() -> Result<i64, String> { Default::default() }
    default_option() -> Option<i64> { Default::default() }
    default_unit() -> () { Default::default() }
    default_one() -> (i64,) { Default::default() }
    default_two() -> (i64, i64) { Default::default() }
    default_three() -> (i64, i64, i64) { Default::default() }
    default_four() -> (i64, i64, i64, i64) { Default::default() }

    relations_score() -> u64 {
        let hash_left = (7, 9);
        let hash_right = (7, 9);
        hash_pair(&hash_left); hash_pair(&hash_right);
        6
    }

    score() -> u64 { relations_score() }

    render() -> String {
        let formatter = Formatter::new();
        let result = ok(7);
        let error = err(8);
        let separator = " ";
        display_result(&result, &mut formatter);
        Formatter::literal(&mut formatter, &separator);
        debug_result(&error, &mut formatter);
        Formatter::literal(&mut formatter, &separator);
        let four = (1, 2, 3, 4);
        Display::fmt(&four, &mut formatter);
        Formatter::literal(&mut formatter, &separator);
        let one = (5,);
        Debug::fmt(&one, &mut formatter);
        handle perform Finished::inspect(Formatter::finish(move formatter)) {
            Finished::inspect(Result::Ok(output)) => move output,
            Finished::inspect(Result::Err(_)) => "invalid"
        }
    }

    ok(value: i64) -> Result<i64, i64> { Result::Ok(value) }
    err(value: i64) -> Result<i64, i64> { Result::Err(value) }

    main() -> () { () }
"#;

#[test]
fn structural_fundamental_traits_execute_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "structural-fundamental-traits.glorious",
            SURFACE,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let vm = Vm::new(verify(artifact.clone()).unwrap());
        assert_eq!(
            vm.run(function_id(&artifact, "score"), vec![]).unwrap(),
            Value::U64(6),
            "{optimization_level:?}",
        );
        assert_eq!(
            vm.run(function_id(&artifact, "render"), vec![]).unwrap(),
            Value::Text("Ok(7) Err(8) (1, 2, 3, 4) (5,)".into()),
            "{optimization_level:?}",
        );
    }
}

#[test]
fn structural_fundamental_traits_have_recovery_parity() {
    let recovery_surface =
        SURFACE.replace("main() -> () { () }", "main() -> u64 { relations_score() }");
    assert_eq!(
        run_source(
            "structural-fundamental-traits-recovery.glorious",
            &recovery_surface,
            vec![],
            &mut NoHost,
        )
        .unwrap(),
        RecoveryValue::Integer {
            signed: false,
            bits: 64,
            raw: 6,
        },
    );
}
