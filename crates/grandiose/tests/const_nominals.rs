use grandiose::compile_source_to_bytecode;
use grandiose_vm::{Value, Vm, verify};

#[test]
fn phantom_u32_const_nominals_specialize_and_execute() {
    let source = r#"
        struct Tag<const N: u32> { marker: i64 }
        three() -> Tag<3> { Tag { marker: 3 } }
        read<const N: u32>(value: Tag<N>) -> i64 { value.marker }
        answer() -> i64 { read(three()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-nominal-u32.gr", source).unwrap();
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
fn phantom_quantity_const_nominals_specialize_and_execute() {
    let source = r#"
        struct Quota<const Q: Quantity> { marker: i64 }
        open() -> Quota<[1, infinity]> { Quota { marker: 7 } }
        read<const Q: Quantity>(value: Quota<Q>) -> i64 { value.marker }
        answer() -> i64 { read(open()) }
        main() -> () { () }
    "#;
    let artifact = compile_source_to_bytecode("const-nominal-quantity.gr", source).unwrap();
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
    let errors = compile_source_to_bytecode("const-nominal-mismatch.gr", source).unwrap_err();
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
    let first = compile_source_to_bytecode("const-order-a.gr", first).unwrap();
    let reordered = compile_source_to_bytecode("const-order-b.gr", reordered).unwrap();
    assert_eq!(first.encode(), reordered.encode());
}

#[test]
fn const_nominal_literal_kinds_and_domains_have_exact_diagnostics() {
    for (name, source, title, message) in [
        (
            "const-u32-overflow.gr",
            "struct Tag<const N:u32>{marker:i64} bad()->Tag<4294967296>{Tag{marker:0}} main()->(){()}",
            "const argument exceeds its domain",
            "u32 const arguments must fit in 32 bits",
        ),
        (
            "const-u32-kind.gr",
            "struct Tag<const N:u32>{marker:i64} bad()->Tag<[1,2]>{Tag{marker:0}} main()->(){()}",
            "nominal argument kind mismatch",
            "const argument has kind Quantity, but binder `N` of `Tag` has kind Const(U32)",
        ),
        (
            "const-quantity-kind.gr",
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
    let artifact = compile_source_to_bytecode("const-gat-runtime.gr", source).unwrap();
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
    let errors = compile_source_to_bytecode("const-runtime-field.gr", source).unwrap_err();
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
    let artifact = compile_source_to_bytecode("mixed-const-nominal.gr", source).unwrap();
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
    let artifact = compile_source_to_bytecode("const-function-evidence.gr", source).unwrap();
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
