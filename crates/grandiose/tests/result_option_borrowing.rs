use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_phases_with_options,
    diagnostic::Diagnostic,
    eval::{Host, Value as InterpreterValue},
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
        _args: Vec<InterpreterValue>,
        span: Span,
    ) -> Result<InterpreterValue, Diagnostic> {
        Err(Diagnostic::error(
            "unexpected effect",
            "borrowing projection reached the host",
            span,
        ))
    }
}

const SOURCE: &str = r#"
    ok(value:i64)->Result<i64,i64>{Result::Ok(value)}
    err(value:i64)->Result<i64,i64>{Result::Err(value)}
    some(value:i64)->Option<i64>{Option::Some(value)}
    none()->Option<i64>{None}

    result_shared(value:Result<i64,i64>)->i64 {
        let projected = Result::as_ref(&value);
        if(projected is Result::Ok(_)){*projected.0}else{*projected.0}
    }
    result_unique<'a>(value:&'a mut Result<i64,i64>)->Result<&'a mut i64,&'a mut i64>{Result::as_mut(value)}
    result_mutate(value:Result<i64,i64>)->i64 {
        let projected=Result::as_mut(&mut value);
        handle projected {
            Result::Ok(item) => {*item=42;()},
            Result::Err(item) => {*item=42;()}
        };
        if(value is Result::Ok(_)){value.0}else{value.0}
    }
    option_shared(value:Option<i64>)->i64 {
        let projected = Option::as_ref(&value);
        if(projected is Result::Ok(_)){*projected.0}else{42}
    }
    option_unique<'a>(value:&'a mut Option<i64>)->Option<&'a mut i64>{Option::as_mut(value)}
    option_mutate(value:Option<i64>)->i64 {
        let projected=Option::as_mut(&mut value);
        handle projected { Option::Some(item) => {*item=42;()}, None => () };
        if(value is Option::Some(_)){value.0}else{42}
    }
    ok_shared()->i64{result_shared(ok(42))}
    err_shared()->i64{result_shared(err(42))}
    ok_mutate()->i64{result_mutate(ok(1))}
    err_mutate()->i64{result_mutate(err(1))}
    some_shared()->i64{option_shared(some(42))}
    none_shared()->i64{option_shared(none())}
    some_mutate()->i64{option_mutate(some(1))}
    none_mutate()->i64{option_mutate(none())}
    answer()->i64{ok_shared() + err_shared() + some_shared() + none_shared()}
    main()->(){()}
"#;

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap() as u32
}

#[test]
fn borrowing_projections_preserve_variants_and_mutate_at_o1_through_o3() {
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "result-option-borrowing.glorious",
            SOURCE,
            CompileOptions { optimization_level },
        )
        .unwrap();
        let verified = verify(phases.artifact.clone()).unwrap();
        for name in [
            "ok_shared",
            "err_shared",
            "ok_mutate",
            "err_mutate",
            "some_shared",
            "none_shared",
            "some_mutate",
            "none_mutate",
        ] {
            assert_eq!(
                Vm::new(verified.clone())
                    .run(function_id(&phases.artifact, name), vec![])
                    .unwrap(),
                Value::I64(42),
                "{optimization_level:?} {name}"
            );
        }
        assert!(
            phases
                .artifact
                .functions
                .iter()
                .any(|function| function.name == "result_unique")
        );
        assert!(
            phases
                .artifact
                .functions
                .iter()
                .any(|function| function.name == "option_unique")
        );
    }
}

#[test]
fn recovery_interpreter_agrees_on_projection_behavior() {
    let source = r#"
        ok(value:i64)->Result<i64,i64>{Result::Ok(value)}
        main()->i64{
            let owner=ok(1);
            let projected=Result::as_mut(&mut owner);
            if(projected is Result::Ok(_)){*projected.0=42;()}else{()};
            if(owner is Result::Ok(_)){owner.0}else{0}
        }
    "#;
    assert_eq!(
        run_source(
            "result-option-borrowing-recovery.glorious",
            source,
            vec![],
            &mut NoHost
        )
        .unwrap(),
        InterpreterValue::Int(42)
    );
}

#[test]
fn projected_references_reject_conflicting_owner_access_and_escape() {
    for source in [
        "ok()->Result<i64,i64>{Result::Ok(1)}warm<'a>(value:&'a mut Result<i64,i64>)->Result<&'a i64,&'a i64>{Result::as_ref(value)}warm_mut<'a>(value:&'a mut Result<i64,i64>)->Result<&'a mut i64,&'a mut i64>{Result::as_mut(value)}bad(value:&mut Result<i64,i64>)->i64{let loan=warm(value);let unique=warm_mut(value);if(loan is Result::Ok(_)){*loan.0}else{0}}main()->(){let value=ok();warm(&mut value);bad(&mut value);()}",
        "ok()->Result<i64,i64>{Result::Ok(42)}warm<'a>(value:&'a Result<i64,i64>)->Result<&'a i64,&'a i64>{Result::as_ref(value)}bad()->Result<&'static i64,&'static i64>{let owner=ok();warm(&owner)}main()->(){let value=ok();warm(&value);bad();()}",
    ] {
        let errors = compile_source_to_phases_with_options(
            "projection-hostile.glorious",
            source,
            CompileOptions::default(),
        )
        .expect_err("invalid projected loan must fail");
        assert!(
            errors.iter().any(|error| error.message.contains("borrow")
                || error.message.contains("loan")
                || error.message.contains("lifetime")
                || error.message.contains("moved")
                || error.message.contains("escape")),
            "{errors:#?}"
        );
    }
}
