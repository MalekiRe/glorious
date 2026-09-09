use grandiose_stage0::*;
use std::collections::BTreeMap;

fn compile(source: &str) -> Result<CompilationOutcome, ServiceError> {
    compile_at(source, "0")
}

fn compile_at(source: &str, optimization: &str) -> Result<CompilationOutcome, ServiceError> {
    // These fixtures deliberately define their own truth/operator contracts.
    // Opt out of the distribution's prelude while keeping explicit std imports
    // available to the tests which exercise the real library boundary.
    let source = format!("#![no_implicit_prelude]\n{source}");
    let package = PackageKey("library-boundary@0.1.0".into());
    StageZeroCompiler::new().compile(CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"source-owned-operators")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::from([("optimization-level".into(), optimization.into())]),
        capability_manifest: vec![],
        runtime_manifest: None,
    })
}
fn run(source: &str) -> i64 {
    let mut result = None;
    for optimization in ["0", "2"] {
        let artifact = compile_at(source, optimization).unwrap().artifact.unwrap();
        let actual = artifact.run_i64().unwrap();
        assert_eq!(decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap(), actual);
        if let Some(expected) = result { assert_eq!(actual, expected, "O{optimization}"); }
        result = Some(actual);
    }
    result.unwrap()
}

#[test]
fn no_operator_has_an_implicit_fixity_or_scalar_implementation() {
    for source in [
        "pub fn main() -> i64 { 20 + 22 }",
        "pub infixl 30 +; pub fn main() -> i64 { 20 + 22 }",
        "pub prefix 50 !; pub fn main() -> i64 { !42 }",
    ] {
        assert!(compile(source).is_err(), "{source}");
    }
}

#[test]
fn a_source_trait_defines_scalar_addition_without_compiler_interception() {
    assert_eq!(
        run(
            "pub infixl 30 +; pub trait Pick { +(left: Self, right: Self) -> Self; } impl Pick for i64 { +(left: i64, right: i64) -> i64 { right } } pub fn main() -> i64 { 20 + 22 }"
        ),
        22
    );
}

#[test]
fn a_source_trait_defines_prefix_punctuation() {
    assert_eq!(
        run(
            "pub prefix 50 !; pub trait Change { !(value: Self) -> Self; } impl Change for i64 { !(value: i64) -> i64 { 42 } } pub fn main() -> i64 { !7 }"
        ),
        42
    );
}

#[test]
fn prefix_and_infix_contracts_for_one_spelling_have_distinct_identities() {
    assert_eq!(
        run(
            "pub prefix 50 +; pub infixl 30 +; pub trait Prefix { +(value: Self) -> Self; } pub trait Binary { +(left: Self, right: Self) -> Self; } impl Prefix for i64 { +(value: i64) -> i64 { value } } impl Binary for i64 { +(left: i64, right: i64) -> i64 { right } } pub fn main() -> i64 { +7 + 42 }"
        ),
        42
    );
}

#[test]
fn source_fixity_changes_the_grouping_of_source_calls() {
    for (fixity, expected) in [("infixl", 3), ("infixr", 2)] {
        let source = format!(
            "pub {fixity} 30 +; pub trait Difference {{ +(left: Self, right: Self) -> Self; }} impl Difference for i64 {{ +(left: i64, right: i64) -> i64 {{ handle left {{ 1 => 2; _ => right }} }} }} pub fn main() -> i64 {{ 1 + 2 + 3 }}"
        );
        assert_eq!(run(&source), expected);
    }
}

#[test]
fn prefix_precedence_and_parentheses_use_source_fixity() {
    for (precedence, expected) in [(10, 2), (50, 3)] {
        let source = format!(
            "pub prefix {precedence} change; pub infixl 30 choose; pub fn change(value: i64) -> i64 {{ handle value {{ 3 => 2; _ => 1 }} }} pub fn choose(left: i64, right: i64) -> i64 {{ right }} pub fn main() -> i64 {{ change 7 choose 3 }}"
        );
        assert_eq!(run(&source), expected);
    }
    assert_eq!(
        run(
            "pub prefix 10 change; pub infixl 30 choose; pub fn change(value: i64) -> i64 { 2 } pub fn choose(left: i64, right: i64) -> i64 { right } pub fn main() -> i64 { (change 7) choose 3 }"
        ),
        3
    );
}

#[test]
fn familiar_word_operators_have_only_their_source_defined_behavior() {
    assert_eq!(
        run(
            "pub infixl 3 and; pub fn and(left: i64, right: i64) -> i64 { right } pub fn main() -> i64 { 1 and 42 }"
        ),
        42
    );
    assert_eq!(
        run(
            "pub prefix 4 not; pub fn not(value: i64) -> i64 { value } pub fn main() -> i64 { not 42 }"
        ),
        42
    );
}

#[test]
fn arbitrary_word_fixities_are_parsed_from_source_declarations() {
    assert_eq!(
        run(
            "pub infixl 3 choose; pub prefix 4 identity; pub fn choose(left: i64, right: i64) -> i64 { right } pub fn identity(value: i64) -> i64 { value } pub fn main() -> i64 { 1 choose identity 42 }"
        ),
        42
    );
    assert_eq!(
        run(
            "pub infixl 3 else; pub fn else(left: i64, right: i64) -> i64 { left } pub fn main() -> i64 { 42 else 7 }"
        ),
        42
    );
}

#[test]
fn truth_spellings_are_ordinary_names_not_literals_or_builtin_types() {
    assert!(compile("pub fn main() -> i64 { true }").is_err());
    assert!(
        compile("pub fn missing(value: Bool) -> i64 { 42 } pub fn main() -> i64 { 42 }").is_err()
    );
    assert_eq!(
        run(
            "pub type Bool = i64; pub let true = 42; pub let false = 7; pub fn main() -> Bool { true }"
        ),
        42
    );
}

#[test]
fn structural_constant_patterns_follow_their_values_not_their_names() {
    assert_eq!(
        run(
            "pub enum Choice { Left(()), Right(()) } pub let true = Choice::Right(()); pub let false = Choice::Left(()); pub fn main() -> i64 { handle Choice::Right(()) { false => 7; true => 42 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "pub enum Choice { Left(()), Right(()) } pub let accepted = Choice::Right(()); pub let rejected = Choice::Left(()); pub fn main() -> i64 { handle Choice::Right(()) { rejected => 7; accepted => 42 } }"
        ),
        42
    );
}

#[test]
fn polymorphic_constant_patterns_supply_ordinary_type_constraints() {
    assert_eq!(
        run("use std::*; pub fn main() -> i64 { handle true { true => 42; false => 0 } }"),
        42
    );
    assert_eq!(
        run(
            "enum Choice<A, B> { Left(A), Right(B) } let accepted = Choice::Right(()); let rejected = Choice::Left(()); pub fn main() -> i64 { handle accepted { accepted => 42; rejected => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle std::true { std::true => 42; std::false => 0 } }"
        ),
        42
    );
}

#[test]
fn an_unconstrained_nested_block_is_eager() {
    assert_eq!(
        run("pub fn main() -> i64 { let mut count = 0; let pair = (1, { count = 42; 2 }); count }"),
        42
    );
}

#[test]
fn binding_a_projected_owner_separates_it_from_later_source_replacement() {
    assert_eq!(
        run(r#"
        struct Data { value: i64 }
        impl Use<[0, 1]> for Data {}
        enum State { Full(Data), Empty }
        struct Slot { state: State }
        pub fn main() -> i64 {
            let mut slot = Slot { state: State::Full(Data { value: 41 }) };
            let saved = slot.state;
            slot.state = State::Full(Data { value: 7 });
            handle saved { State::Full(data) => data.value, State::Empty => 0 }
        }
    "#),
        41
    );
}

#[test]
fn truth_constants_are_closed_but_none_and_constructors_remain_polymorphic() {
    // Language §4.3 closes both slots of Bool. Generic absence and success
    // remain available through None and ordinary Result constructors.
    for source in [
        "use std::*; enum Failure { Broken } fn succeed() -> Result<(), Failure> { true } fn empty() -> Option<i64> { false } pub fn main() -> i64 { 42 }",
        "use std::*; fn empty<T>() -> Option<T> { false } fn succeed<E>() -> Result<(), E> { true } pub fn main() -> i64 { 42 }",
    ] {
        let Err(ServiceError::Failed(diagnostics)) = compile(source) else {
            panic!("closed truth constants widened to other Result types");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4107"), "{diagnostics:#?}");
    }
    assert_eq!(
        run(
            "use std::*; enum Failure { Broken } fn succeed() -> Result<(), Failure> { Result::Ok(()) } fn empty() -> Option<i64> { None } pub fn main() -> i64 { handle succeed() { Result::Ok(_) => handle empty() { None => 42; Result::Ok(_) => 0 }; Result::Err(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; fn empty<T>() -> Option<T> { None } fn succeed<E>() -> Result<(), E> { Result::Ok(()) } pub fn main() -> i64 { handle empty<i64>() { None => handle succeed<i64>() { Result::Ok(_) => 42; Result::Err(_) => 0 }; Result::Ok(_) => 0 } }"
        ),
        42
    );
}

#[test]
fn false_is_a_unit_error_not_a_wildcard_error_pattern() {
    assert!(compile("use std::*; pub fn main() -> i64 { handle Result<(), i64>::Err(7) { false => 0; _ => 42 } }").is_err());
    assert!(
        compile("use std::*; fn fail() -> Result<(), i64> { false } pub fn main() -> i64 { 42 }")
            .is_err()
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle Result<(), i64>::Err(7) { Result::Err(_) => 42; Result::Ok(_) => 0 } }"
        ),
        42
    );
}

#[test]
fn generic_constants_receive_context_even_after_a_terminal_expression() {
    assert_eq!(
        run(
            "use std::*; enum Choice<A, B> { Left(A), Right(B) } let absent = Choice::Right(()); fn finish<L>(exit: L) -> Choice<i64, ()> where L: Label<i64> { exit(42); absent } pub fn main() -> i64 { @done: i64 { finish(@done); 0 } }"
        ),
        42
    );
}

#[test]
fn result_control_preserves_payloads_and_only_invokes_selected_operands() {
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { let mut calls = 0; let value = { let left = Result<i64, i64>::Err(42); let result = left and { calls = 1; Result::Ok(7) }; handle result { Result::Err(error) => error; Result::Ok(_) => 0 } }; value + calls }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { let mut calls = 0; let value = { let left = Result<i64, i64>::Ok(42); let result = left or { calls = 1; Result::Err(7) }; handle result { Result::Ok(value) => value; Result::Err(_) => 0 } }; value + calls }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle not Result<i64, i64>::Err(42) { Result::Ok(value) => value; Result::Err(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle not Result<i64, i64>::Ok(42) { Result::Err(value) => value; Result::Ok(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle Result<i64, i64>::Ok(7) and { Result::Ok(42) } { Result::Ok(value) => value; Result::Err(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { handle Result<i64, i64>::Err(7) or { Result<i64, i64>::Ok(42) } { Result::Ok(value) => value; Result::Err(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn main() -> i64 { let result = if(Result<i64, i64>::Err(42)) { 7 }; handle result { Result::Err(error) => error; Result::Ok(_) => 0 } }"
        ),
        42
    );
    assert_eq!(
        run("use std::*; pub fn main() -> i64 { Result<i64, i64>::Err(7) else { 42 } }"),
        42
    );
}

#[test]
fn temporary_callback_loans_live_through_arguments_but_not_a_scalar_result() {
    assert_eq!(
        run(
            "use std::*; fn apply<F>(body: F) -> i64 where F: Fn<(), Output = i64> { body() } pub fn main() -> i64 { let mut count = 0; apply(() -> i64 { count = 42; count }); count }"
        ),
        42
    );
    for source in [
        "use std::*; fn apply<F>(body: F, other: i64) -> i64 where F: Fn<(), Output = i64> { body() } pub fn main() -> i64 { let mut count = 0; apply(() -> i64 { count = 42; count }, count) }",
        "use std::*; fn identity<F>(body: F) -> F { body } pub fn main() -> i64 { let mut count = 0; let kept = identity(() -> i64 { count = 42; count }); let invalid = count; kept() }",
    ] {
        let Err(ServiceError::Failed(diagnostics)) = compile(source) else {
            panic!("capture loan was released too early");
        };
        assert!(
            diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G5008"),
            "{diagnostics:#?}"
        );
    }
}

#[test]
fn standard_operators_are_source_calls_to_manifest_machine_leaves() {
    assert_eq!(
        run("use std::*; pub fn main() -> i64 { handle 20 + 22 == 42 { true => 42; false => 0 } }"),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn check(value: u32, other: usize) -> i64 { handle 1 + value == 4 and { 2 * other == 14 } { true => 42; false => 0 } } pub fn main() -> i64 { check(3, 7) }"
        ),
        42
    );
    assert_eq!(
        run(
            "use std::*; pub fn check(value: f64) -> i64 { handle value * 7.0 == 42.0 { true => 42; false => 0 } } pub fn main() -> i64 { check(6.0) }"
        ),
        42
    );
}

#[test]
fn canonical_comparisons_use_structural_eq_and_ord_instances() {
    assert_eq!(run("use std::*; pub fn main() -> i64 { handle true == true and { true != false } and { true < false } and { false >= true } { true => 42, false => 0 } }"), 42);
    assert_eq!(run("use std::*; struct Item { value: i64 } impl Use<[1,1]> for Item {}
        impl PartialEq for Item { fn eq(left: &Self, right: &Self) -> Bool { left.value == right.value } }
        impl Eq for Item {}
        impl PartialOrd for Item { fn partial_cmp(left: &Self, right: &Self) -> Option<Ordering> { Some(Ord::cmp(left, right)) } }
        impl Ord for Item { fn cmp(left: &Self, right: &Self) -> Ordering { Ord::cmp(&left.value, &right.value) } }
        fn equal(left: i64, right: i64) -> Bool { false }
        pub fn main() -> i64 { let left = Item { value: 21 }; let right = Item { value: 21 };
            let answer = handle &left == &right and { &left <= &right } { true => 42, false => 0 };
            let Item { value: a } = left; let Item { value: b } = right; answer + a - b }"), 42);
}

#[test]
fn scalar_float_comparisons_follow_ieee_nan_and_signed_zero_policy() {
    for scalar in ["f32", "f64"] {
        let source = format!("use std::*; pub fn check(nan: {scalar}, negative_zero: {scalar}, zero: {scalar}, infinity: {scalar}) -> i64 {{
            handle nan != nan and {{ not(nan == zero) }} and {{ not(nan < zero) }}
                and {{ not(nan <= infinity) }} and {{ not(nan > zero) }} and {{ not(zero >= nan) }}
                and {{ negative_zero == zero }} and {{ not(negative_zero < zero) }}
                and {{ negative_zero <= zero }} and {{ infinity > zero }} {{ true => 42, false => 0 }}
        }} pub fn main() -> i64 {{ check(0.0 / 0.0, -0.0, 0.0, 1.0 / 0.0) }}");
        assert_eq!(run(&source), 42, "{scalar}");
    }
}

#[test]
fn float_partial_traits_do_not_grant_total_order_or_hash_key_evidence() {
    for scalar in ["f32", "f64"] {
        assert_eq!(run(&format!("use std::*; pub fn check(left: {scalar}, right: {scalar}) -> i64 {{
            handle PartialOrd::partial_cmp(&left, &right) {{ None => handle PartialEq::eq(&left, &right) {{ false => 42, true => 0 }}, Some(_) => 0 }}
        }} pub fn main() -> i64 {{ check(0.0 / 0.0, 0.0) }}")), 42);
        for bound in ["Eq", "Ord", "Hash"] {
            let source = format!("use std::*; fn require<T>(value: T) -> T where T: {bound} {{ value }}
                pub fn check(value: {scalar}) -> i64 {{ require(value); 42 }} pub fn main() -> i64 {{ check(1.0) }}");
            for optimization in ["0", "2"] {
                let error = compile_at(&source, optimization).expect_err("IEEE floats do not satisfy total or hash-key traits");
                assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4143"), "{bound}: {error:#?}");
            }
        }
    }
}

#[test]
fn structural_partial_comparisons_propagate_unordered_payloads() {
    for scalar in ["f32", "f64"] {
        assert_eq!(run(&format!("use std::*;
            pub fn check(nan: {scalar}, zero: {scalar}, negative_zero: {scalar}) -> i64 {{
                let unordered: Option<{scalar}> = Some(nan);
                let positive: Option<{scalar}> = Some(zero);
                let negative: Option<{scalar}> = Some(negative_zero);
                handle unordered != unordered and {{ not(unordered < positive) }}
                    and {{ not(unordered <= positive) }} and {{ not(unordered > positive) }}
                    and {{ not(unordered >= positive) }} and {{ positive == negative }} {{
                    true => handle PartialOrd::partial_cmp(&unordered, &positive) {{ None => 42, Some(_) => 0 }},
                    false => 0,
                }}
            }} pub fn main() -> i64 {{ check(0.0 / 0.0, 0.0, -0.0) }}")), 42);
    }
}

#[test]
fn immutable_function_aliases_preserve_direct_calls() {
    assert_eq!(
        run(
            "fn answer() -> i64 { 42 } pub fn main() -> i64 { let first = answer; let second = first; second() }"
        ),
        42
    );
}

#[test]
fn constructor_alias_patterns_preserve_nested_payload_and_nominal_identity() {
    let source = "#![no_std]\nenum Inner { A, B } enum Choice<T> { Value(T), Empty }
        let Selected = Choice::Value; let Alias = Selected; let Nothing = Choice::Empty;
        fn read(value: Choice<Inner>) -> i64 { handle value { Alias(Inner::A) => 42, Alias(Inner::B) => 0, Nothing => 0 } }
        pub fn main() -> i64 { read(Selected(Inner::A)) }";
    assert_eq!(run(source), 42);
    let wrong = "#![no_std]\nenum First { Value(i64) } enum Second { Value(i64) }
        let Selected = First::Value;
        pub fn main() -> i64 { handle Second::Value(42) { Selected(value) => value } }";
    let error = compile(wrong).expect_err("a constructor alias cannot match an unrelated same-shaped enum");
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4212"), "{error:#?}");
}

#[test]
fn plus_where_bounds_enforce_every_relation_and_authorize_affine_disposal() {
    let declarations = "#![no_std]\ntrait First {} trait Second {} impl First for i64 {}
        fn keep<T>(value: T) -> T where T: First + Second { value }";
    let bad = format!("{declarations} pub fn main() -> i64 {{ keep(42) }}");
    let error = compile(&bad).expect_err("the second conjunct is a required caller obligation");
    assert!(error.diagnostics().iter().any(|diagnostic| diagnostic.code == "G4143"), "{error:#?}");
    assert_eq!(run(&format!("{declarations} impl Second for i64 {{}} pub fn main() -> i64 {{ keep(42) }}")), 42);
    assert_eq!(run("#![no_std]\ntrait Observe { fn read(value: &Self) -> i64; }
        struct Owner {} impl Use<[0,1]> for Owner {} impl Observe for Owner { fn read(value: &Self) -> i64 { 42 } }
        fn observe<T>(value: T) -> i64 where T: Observe + Use<[0,1]> { Observe::read(&value) }
        pub fn main() -> i64 { observe(Owner {}) }"), 42);
}

#[test]
fn arbitrary_function_callback_chains_use_ordinary_inference() {
    for count in [2, 8] {
        let chain = format!("1{}", (2..=count)
            .map(|value| format!(" follow {{ {value} }}"))
            .collect::<String>());
        let source = format!("pub infixl 3 follow; fn follow<A, B, F>(value: A, next: F) -> B where A: Use<[0, 1]>, F: Fn<(), Output = B> {{ next() }} pub fn main() -> i64 {{ {chain} }}");
        assert_eq!(run(&source), count);
    }
}

#[test]
fn library_and_rejects_a_value_where_its_callback_is_required() {
    for expression in ["1 == 1 and 2 == 2", "and(true, false)"] {
        let source = format!("use std::*; pub fn main() -> i64 {{ handle {expression} {{ true => 42; false => 0 }} }}");
        let Err(ServiceError::Failed(diagnostics)) = compile(&source) else {
            panic!("noncallable argument was accepted: {source}");
        };
        assert!(diagnostics.iter().any(|diagnostic| diagnostic.code == "G4105"),
            "{diagnostics:#?}");
    }
}

#[test]
fn distinct_normal_completion_observes_inner_handler_clause_results() {
    assert_eq!(run("use std::*; effect Stop { stop() -> !; } pub fn main() -> i64 { handle { handle Stop::stop() { Stop::stop() => 42 } } { value => value + 100 } }"), 142);
    assert_eq!(run("use std::*; effect Stop { stop() -> !; } pub fn main() -> i64 { handle Stop::stop() { value => value + 100, Stop::stop() => 42 } }"), 42);
    assert_eq!(run("effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { label done { handle Ask::ask() { value => transfer done value, Ask::ask(_) => 42 } } }"), 42);
}

#[test]
fn reassigned_function_aliases_call_the_current_value() {
    assert_eq!(
        run(
            "fn initial() -> i64 { 7 } fn answer() -> i64 { 42 } pub fn main() -> i64 { let mut selected = initial; selected = answer; selected() }"
        ),
        42
    );
}
