use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

fn run(source: &str, function: &str) -> Value {
    let artifact = compile_source_to_bytecode("surface-simplifications.glorious", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .position(|candidate| candidate.name == function)
        .unwrap() as u32;
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

#[test]
fn associated_callable_aliases_support_dot_call_and_auto_borrow() {
    let source = r#"
        struct Counter { value: i64 }
        bump(counter: &mut Counter, amount: i64) -> () {
            counter.value = counter.value + amount;
            ()
        }
        let Counter::bump = bump;
        answer() -> i64 {
            let counter = Counter { value: 40 };
            counter.bump(2);
            counter.value
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn calls_reborrow_unique_handles_and_demote_them_to_shared() {
    let source = r#"
        increment(value: &mut i64) -> () { *value = *value + 1; () }
        observe(value: &i64) -> i64 { *value }
        passthrough_test<T>(value: T) -> T { value }
        forward(value: &mut i64) -> i64 {
            increment(value);
            passthrough_test(observe(value))
        }
        answer() -> i64 {
            let value = 41;
            forward(&mut value)
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn owned_values_move_implicitly_without_surface_move_noise() {
    let source = r#"
        struct Token { value: i64 }
        unwrap(token: Token) -> i64 { token.value }
        answer() -> i64 {
            let token = Token { value: 42 };
            unwrap(token)
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn generic_case_inspects_an_instantiated_nominal_payload() {
    let source = r#"
        make() -> Result<i64, ()> { Result::Ok(42) }
        answer() -> i64 {
            let value = make();
            handle perform Case<Result<i64, ()>>::inspect(move value) {
                Result::Ok(answer) => answer,
                Result::Err(_) => 0
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn library_match_syntax_elaborates_to_source_defined_refinement_calls() {
    let source = r#"
        make() -> Result<i64, ()> { Result::Ok(42) }
        answer() -> i64 {
            match(make()) {
                Result::Ok(answer) => answer,
                Result::Err(_) => 0
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn owned_refinement_moves_noncopy_payloads_into_if_arms() {
    let source = r#"
        struct Token { value: i64 }
        impl Use<[0,1]> for Token {}
        enum Choice { Some(Token), None }
        make() -> Choice { Choice::Some(Token { value: 42 }) }
        answer() -> i64 {
            let choice = make();
            if(choice is Choice::Some(token)) {
                token.value
            } else {
                0
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn match_moves_noncopy_payloads_out_of_its_subject() {
    let source = r#"
        struct Token { value: i64 }
        impl Use<[0,1]> for Token {}
        enum Choice { Some(Token), None }
        make() -> Choice { Choice::Some(Token { value: 42 }) }
        answer() -> i64 {
            match(make()) {
                Choice::Some(token) => token.value,
                Choice::None => 0
            }
        }
        main() -> { () }
    "#;
    assert_eq!(run(source, "answer"), Value::I64(42));
}

#[test]
fn owned_refinement_consumes_the_scrutinee_across_the_join() {
    let source = r#"
        struct Token { value: i64 }
        impl Use<[0,1]> for Token {}
        enum Choice { Some(Token), None }
        bad(choice: Choice) -> i64 {
            let answer = if(choice is Choice::Some(token)) {
                token.value
            } else {
                0
            };
            choice;
            answer
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("surface-simplifications.glorious", source)
        .expect_err("the scrutinee must be consumed after the refinement joins");
    assert!(
        errors
            .iter()
            .any(|error| error.message.contains("already moved")),
        "{errors:#?}"
    );
}

#[test]
fn generic_case_resolves_module_local_nominals_in_its_payload() {
    let source = r#"
        mod app {
            enum Error { Failed }
            make() -> Result<i64, Error> { Result::Ok(42) }
            answer() -> i64 {
                let value = make();
                handle perform Case<Result<i64, Error>>::inspect(move value) {
                    Result::Ok(answer) => answer,
                    Result::Err(_) => 0
                }
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("surface-simplifications.glorious", source).unwrap();
}
