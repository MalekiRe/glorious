use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_bytecode_with_options,
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
            "const recovery test performed a host effect",
            span,
        ))
    }
}

#[test]
fn phantom_u32_const_nominals_specialize_and_execute() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        three() -> Tag<3> { Tag { marker: 3 } }
        read<const N: u32>(value: Tag<N>) -> i64 { value.marker }
        answer() -> i64 { read(three()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-nominal-u32.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(3)
    );
}

#[test]
fn ground_const_arithmetic_normalizes_into_nominal_identity() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        make() -> Tag<2 + 3 * 4> { Tag { marker: 14 } }
        read(value: Tag<14>) -> i64 { value.marker }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-arithmetic.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(14)
    );
}

#[test]
fn ground_const_arithmetic_rejects_invalid_domains() {
    for (name, expression, expected) in [
        ("divide-zero", "4 / 0", "division by zero"),
        ("overflow", "4294967295 + 1", "overflows the u32 domain"),
        ("negative", "-1", "negative value"),
    ] {
        let source = format!(
            "struct Tag<const N:u32>{{marker:i64}} bad()->Tag<{expression}>{{Tag{{marker:0}}}} main()->(){{()}}"
        );
        let errors = compile_source_to_bytecode(&format!("const-{name}.glorious"), &source)
            .expect_err("invalid const arithmetic compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn const_generic_aliases_preserve_nominal_identity() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        type Alias<const N: u32> = Tag<N>;
        three() -> Alias<3> { Tag { marker: 3 } }
        read<const N: u32>(value: Alias<N>) -> i64 { value.marker }
        answer() -> i64 { read(three()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-alias-u32.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(3)
    );
}

#[test]
fn const_generic_aliases_reorder_mixed_arguments_structurally() {
    let source = r#"
        struct Pair<T, const N: u32> { value: T }
        type Reordered<const N: u32, T> = Pair<T, N>;
        make() -> Reordered<3, i64> { Pair { value: 9 } }
        read(value: Pair<i64, 3>) -> i64 { value.value }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-alias-reorder.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(9)
    );
}

#[test]
fn const_generic_alias_defaults_fill_trailing_arguments() {
    let source = r#"
        struct Pair<T, const N: u32> { value: T }
        type Defaulted<T, const N: u32 = 2 + 1> = Pair<T, N>;
        make() -> Defaulted<i64> { Pair { value: 9 } }
        read(value: Pair<i64, 3>) -> i64 { value.value }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-alias-default.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(9)
    );
}

#[test]
fn nominal_const_defaults_fill_trailing_arguments() {
    let source = r#"
        struct Pair<T, const N: u32 = 2 + 1> { value: T }
        make() -> Pair<i64> { Pair { value: 9 } }
        read(value: Pair<i64, 3>) -> i64 { value.value }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-nominal-default.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(9)
    );
}

#[test]
fn nominal_const_defaults_can_reference_earlier_const_arguments() {
    let source = r#"
        struct Window<const Start: u32, const End: u32 = Start + 1> { marker: i64 }
        make() -> Window<3> { Window { marker: 4 } }
        read(value: Window<3, 4>) -> i64 { value.marker }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-dependent-default.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(4)
    );
}

#[test]
fn alias_expansion_materializes_dependent_nominal_const_defaults() {
    let source = r#"
        struct Window<const Start: u32, const End: u32 = Start + 1> { marker: i64 }
        type StartWindow<const Start: u32> = Window<Start>;
        make() -> StartWindow<3> { Window { marker: 4 } }
        read(value: Window<3, 4>) -> i64 { value.marker }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-alias-dependent-default.glorious", source)
        .unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(4)
    );
}

#[test]
fn symbolic_const_expressions_fold_after_specialization() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        three() -> Tag<3> { Tag { marker: 3 } }
        bump_tag<const N: u32>(value: Tag<N>) -> Tag<N + 1> {
            Tag { marker: value.marker + 1 }
        }
        read_four(value: Tag<4>) -> i64 { value.marker }
        answer() -> i64 { read_four(bump_tag(three())) }
        main() -> () { () }
    "#;
    let artifact =
        compile_source_to_bytecode("const-symbolic-expression.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(4)
    );
}

#[test]
fn ground_fixed_arrays_lower_to_fixed_tuple_layouts() {
    let source = r#"
        sum(value: [i64; 2]) -> i64 { value.0 + value.1 }
        answer() -> i64 { sum((20, 22)) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("fixed-array-layout.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn fixed_array_lengths_are_bounded_and_ground() {
    for (name, length, expected) in [
        ("too-large", "1025", "at most 1024 elements"),
        ("unresolved", "N", "unresolved parameter or path"),
    ] {
        let source = format!("bad<const N:u32>(value:[i64;{length}])->(){{()}} main()->(){{()}}");
        let errors = compile_source_to_bytecode(&format!("fixed-array-{name}.glorious"), &source)
            .expect_err("invalid fixed-array length compiled");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn const_defaults_symbolic_arithmetic_and_fixed_layouts_execute_at_all_levels() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        struct Boxed<T, const N: u32 = 3> { value: T }
        type Alias<T, const N: u32 = 3> = Boxed<T, N>;
        make() -> Tag<3> { Tag { marker: 3 } }
        bump<const N: u32>(value: Tag<N>) -> Tag<N + 1> {
            Tag { marker: value.marker + 1 }
        }
        boxed() -> Alias<i64> { Boxed { value: 38 } }
        combine(values: [i64; 2], tag: Tag<4>, value: Boxed<i64, 3>) -> i64 {
            values.0 + values.1 + tag.marker + value.value
        }
        answer() -> i64 { combine((0, 0), bump(make()), boxed()) }
        main() -> () { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let artifact = compile_source_to_bytecode_with_options(
            "const-combined-all-levels.glorious",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(artifact).unwrap();
        let answer = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified).run(answer, vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn const_defaults_symbolic_arithmetic_and_fixed_layouts_have_recovery_parity() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        struct Boxed<T, const N: u32 = 3> { value: T }
        type Alias<T, const N: u32 = 3> = Boxed<T, N>;
        make() -> Tag<3> { Tag { marker: 3 } }
        bump<const N: u32>(value: Tag<N>) -> Tag<N + 1> {
            Tag { marker: value.marker + 1 }
        }
        boxed() -> Alias<i64> { Boxed { value: 38 } }
        combine(values: [i64; 2], tag: Tag<4>, value: Boxed<i64, 3>) -> i64 {
            values.0 + values.1 + tag.marker + value.value
        }
        main() -> i64 { combine((0, 0), bump(make()), boxed()) }
    "#;
    let result = run_source("const-recovery.glorious", source, vec![], &mut NoHost).unwrap();
    assert_eq!(result, RecoveryValue::Int(42));
}

#[test]
fn phantom_quantity_const_nominals_specialize_and_execute() {
    let source = r#"
        struct Quota<const Q: Quantity> { marker: i64 }
        open() -> Quota<[1, infinity]> { Quota { marker: 7 } }
        read<const Q: Quantity>(value: Quota<Q>) -> i64 { value.marker }
        answer() -> i64 { read(open()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-nominal-quantity.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(7)
    );
}

#[test]
fn distinct_const_nominal_identities_do_not_unify() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        three() -> Tag<3> { Tag { marker: 3 } }
        read_four(value: Tag<4>) -> i64 { value.marker }
        answer() -> i64 { read_four(three()) }
        main() -> () { () }
    "#;
    let errors = compile_source_to_bytecode("const-nominal-mismatch.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G1BC002")
                && error.message == "expected Tag<4>, found Tag<3>"
                && error.span.is_some()
        }),
        "{errors:#?}"
    );
}

#[test]
fn const_nominal_specialization_is_declaration_order_deterministic() {
    let first = r#"
        struct Tag<const N: u32> { marker: i64 }
        three() -> Tag<3> { Tag { marker: 3 } }
        read<const N: u32>(value: Tag<N>) -> i64 { value.marker }
        answer() -> i64 { read(three()) }
        main() -> () { () }
    "#;
    let reordered = r#"
        main() -> () { () }
        answer() -> i64 { read(three()) }
        read<const N: u32>(value: Tag<N>) -> i64 { value.marker }
        three() -> Tag<3> { Tag { marker: 3 } }
        struct Tag<const N: u32> { marker: i64 }
    "#;
    let first = compile_source_to_bytecode("const-order-a.glorious", first).unwrap();
    let reordered = compile_source_to_bytecode("const-order-b.glorious", reordered).unwrap();
    assert_eq!(first.encode(), reordered.encode());
}

#[test]
fn const_nominal_literal_kinds_and_domains_have_exact_diagnostics() {
    for (name, source, title, message) in [
        (
            "const-u32-overflow.glorious",
            "struct Tag<const N:u32>{marker:i64} bad()->Tag<4294967296>{Tag{marker:0}} main()->(){()}",
            "const argument exceeds its domain",
            "u32 const arguments must fit in 32 bits",
        ),
        (
            "const-u32-kind.glorious",
            "struct Tag<const N:u32>{marker:i64} bad()->Tag<[1,2]>{Tag{marker:0}} main()->(){()}",
            "nominal argument kind mismatch",
            "const argument has kind Quantity, but binder `N` of `Tag` has kind Const(U32)",
        ),
        (
            "const-quantity-kind.glorious",
            "struct Tag<const Q:Quantity>{marker:i64} bad()->Tag<7>{Tag{marker:0}} main()->(){()}",
            "nominal argument kind mismatch",
            "const argument has kind U32, but binder `Q` of `Tag` has kind Const(Quantity)",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.code.as_deref() == Some("G0008")
                    && error.title == title
                    && error.message == message
                    && error.span.is_some()
            }),
            "{name}: {errors:#?}"
        );
    }
}

#[test]
fn local_gat_const_arguments_normalize_into_runtime_signatures() {
    let source = r#"
        trait Family<const N: u32> { type Member<const M: u32>; }
        struct S { marker: i64 }
        impl<const K: u32> Family<K> for S {
            type Member<const M: u32> = i64;
        }
        gat_value(value: <S as Family<7>>::Member<9>) -> i64 { value }
        answer() -> i64 { gat_value(42) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-gat-runtime.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn const_binders_cannot_be_used_as_runtime_field_types() {
    let source = "struct Bad<const N:u32>{value:N} main()->(){()}";
    let errors = compile_source_to_bytecode("const-runtime-field.glorious", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some("G0008")
                && error.title == "const parameter used as a runtime type"
                && error.message
                    == "const parameter `N` may only appear in a declared const argument position"
                && error.span.map(|span| &source[span.range()]) == Some("N")
        }),
        "{errors:#?}"
    );
}

#[test]
fn lifetime_const_and_type_nominal_arguments_keep_source_positions() {
    let source = r#"
        struct Stamp<'a, const N:u32, T> { value:T }
        make() -> Stamp<'static, 3, i64> { Stamp { value:9 } }
        read(value:Stamp<'static, 3, i64>) -> i64 { value.value }
        answer() -> i64 { read(make()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("mixed-const-nominal.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(9)
    );
}

#[test]
fn inferred_function_consts_substitute_into_marker_evidence() {
    let source = r#"
        trait Index<const N:u32> {}
        struct Tag<const N:u32> { marker:i64 }
        struct Token { marker:i64 }
        impl Index<3> for Token {}
        make() -> Tag<3> { Tag { marker:0 } }
        select<const N:u32, T>(tag:Tag<N>, value:T) -> T where T:Index<N> { value }
        answer() -> i64 { select(make(), Token { marker:11 }).marker }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-function-evidence.glorious", source).unwrap();
    let verified = verify(artifact).unwrap();
    let answer = verified
        .artifact()
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verified).run(answer, vec![]).unwrap(),
        Value::I64(11)
    );
}
