use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn nested_generic_nominal_fields_construct_and_forward_at_every_optimization_level() {
    let source = r#"
        struct Slot<T> { value: T }
        struct Ring<T> { slots: Vec<Slot<T>> }
        struct ArrayRing<T> { slots: Array<Slot<T>> }

        impl<T> Use<[0,1]> for Slot<T> where T: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Ring<T> where Vec<Slot<T>>: Use<[0,1]> {}
        impl<T> Use<[0,1]> for ArrayRing<T> where Array<Slot<T>>: Use<[0,1]> {}

        empty_ring<T>() -> Ring<T> { Ring { slots: Vec::new() } }
        forward_ring(value: Ring<i64>) -> Ring<i64> { value }
        wrap_array<T>(slots: Array<Slot<T>>) -> ArrayRing<T> {
            ArrayRing { slots: move slots }
        }
        forward_array(value: Array<Slot<i64>>) -> ArrayRing<i64> {
            wrap_array(move value)
        }
        answer() -> usize {
            let ring = forward_ring(empty_ring());
            Vec::len(&ring.slots)
        }
        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "nested-generic-fields.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let answer = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified).run(answer, vec![]).unwrap(),
            Value::U64(0)
        );
    }
}

#[test]
fn nested_generic_field_use_requires_exact_evidence() {
    let source = r#"
        struct Ticket { serial: i64 }
        struct Slot<T> { value: T }
        struct Ring<T> { slots: Vec<Slot<T>> }
        impl Use<[1,1]> for Ticket {}
        impl<T> Use<[0,1]> for Slot<T> where T: Use<[0,1]> {}
        impl<T> Use<[1,1]> for Ring<T> where T: Use<[1,1]> {}
        bad(value: Ring<Ticket>) -> () { () }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("nested-generic-use.gr", source)
        .expect_err("the nested Vec<Slot<T>> field lacks exact Use<[1,1]> evidence");
    assert!(
        errors.iter().any(|error| {
            error.message.contains("Use")
                || error.message.contains("uncovered generic Use field")
                || error.message.contains("matching implementation")
        }),
        "{errors:#?}"
    );
}

#[test]
fn nested_generic_applications_cannot_hide_owned_cycles_or_growth() {
    for (source, expected) in [
        (
            r#"
                struct Loop<T> { next: Vec<Loop<T>> }
                expose(value: Loop<i64>) -> Loop<i64> { value }
                main() -> () { () }
            "#,
            "cycles through",
        ),
        (
            r#"
                struct Grow<T> { next: Vec<Grow<(T, T)>> }
                expose(value: Grow<i64>) -> Grow<i64> { value }
                main() -> () { () }
            "#,
            "expands infinitely",
        ),
    ] {
        let errors = grandiose::compile_source_to_bytecode("nested-generic-cycle.gr", source)
            .expect_err("owned nested generic recursion must remain finite");
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "{errors:#?}"
        );
    }
}

#[test]
fn nested_generic_field_emission_is_declaration_order_independent() {
    let first = r#"
        struct Slot<T> { value: T }
        struct Ring<T> { slots: Vec<Slot<T>> }
        struct ArrayRing<T> { slots: Array<Slot<T>> }
        forward(value: Ring<i64>) -> Ring<i64> { value }
        forward_array(value: ArrayRing<i64>) -> ArrayRing<i64> { value }
        main() -> () { () }
    "#;
    let reordered = r#"
        main() -> () { () }
        forward_array(value: ArrayRing<i64>) -> ArrayRing<i64> { value }
        forward(value: Ring<i64>) -> Ring<i64> { value }
        struct ArrayRing<T> { slots: Array<Slot<T>> }
        struct Ring<T> { slots: Vec<Slot<T>> }
        struct Slot<T> { value: T }
    "#;
    assert_eq!(
        grandiose::compile_source_to_bytecode("nested-order-a.gr", first)
            .unwrap()
            .encode(),
        grandiose::compile_source_to_bytecode("nested-order-b.gr", reordered)
            .unwrap()
            .encode()
    );
}
