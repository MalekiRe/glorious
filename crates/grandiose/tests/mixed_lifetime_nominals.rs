use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_bytecode_with_options};
use grandiose_vm::Type;

#[test]
fn mixed_lifetime_type_nominals_erase_regions_from_runtime_identity() {
    let source = r#"
        struct Brand<'a, T> { value: T }
        pass<'scope, U>(value: Brand<'scope, U>) -> Brand<'scope, U> {
            move value
        }
        make() -> Brand<'static, i64> { Brand { value: 42 } }
        answer() -> i64 {
            let branded = pass(make());
            let Brand { value } = move branded;
            value
        }
        main() -> () { () }
    "#;
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "mixed-lifetime-nominal.glorious",
            source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
        let brands = artifact
            .types
            .iter()
            .filter(|ty| {
                matches!(ty.representation(), Type::Struct { name, .. } if name.contains("Brand"))
            })
            .collect::<Vec<_>>();
        assert_eq!(brands.len(), 1, "{level:?}: {brands:#?}");
    }
}

#[test]
fn lifetime_only_nominal_can_be_nested_in_a_runtime_generic_result() {
    let source = r#"
        struct Session<'a> { value: &'a i64 }

        prepare<'a>(value: &'a i64) -> Result<Session<'a>, u8> {
            Result::Ok(Session { value: value })
        }

        answer() -> i64 {
            let value = 42;
            handle prepare(&value) {
                Result::Err(_) => 0,
                Result::Ok(session) => *session.value
            }
        }

        main() -> () { () }
    "#;
    for level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile_source_to_bytecode_with_options(
            "nested-lifetime-only-nominal.glorious",
            source,
            CompileOptions {
                optimization_level: level,
            },
        )
        .unwrap_or_else(|errors| panic!("{level:?}: {errors:#?}"));
    }
}

#[test]
fn mixed_nominal_arguments_enforce_binder_kinds_arity_and_lifetime_scope() {
    let cases = [
        (
            "wrong-kind.glorious",
            "struct Brand<'a,T>{value:T} bad<'scope>(value:Brand<i64,'scope>)->(){()} main()->(){()}",
            "supplied for a non-lifetime binder",
        ),
        (
            "wrong-arity.glorious",
            "struct Brand<'a,T>{value:T} bad(value:Brand<i64>)->(){()} main()->(){()}",
            "expects 2 generic argument",
        ),
        (
            "unbound-region.glorious",
            "struct Brand<'a,T>{value:T} bad(value:Brand<'missing,i64>)->(){()} main()->(){()}",
            "is not bound in this declaration",
        ),
    ];
    for (name, source, expected) in cases {
        let errors = grandiose::compile_source_to_bytecode(name, source)
            .expect_err("an ill-kinded mixed nominal application compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}
