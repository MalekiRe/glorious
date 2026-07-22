use grandiose::{CompileOptions, OptimizationLevel, compile_source_to_phases_with_options};
use grandiose_vm::{Value, Vm, verify};

#[test]
fn nested_generic_nominal_fields_construct_and_forward_at_every_optimization_level() {
    let source = r#"
        struct NestedSlot<T> { value: T }
        struct Ring<T> { slots: Vec<NestedSlot<T>> }
        struct ArrayRing<T> { slots: Array<NestedSlot<T>> }

        impl<T> Use<[0,1]> for NestedSlot<T> where T: Use<[0,1]> {}
        impl<T> Use<[0,1]> for Ring<T> where Vec<NestedSlot<T>>: Use<[0,1]> {}
        impl<T> Use<[0,1]> for ArrayRing<T> where Array<NestedSlot<T>>: Use<[0,1]> {}

        empty_ring<T>() -> Ring<T> { Ring { slots: Vec::new() } }
        forward_ring(value: Ring<i64>) -> Ring<i64> { value }
        wrap_array<T>(slots: Array<NestedSlot<T>>) -> ArrayRing<T> {
            ArrayRing { slots: move slots }
        }
        forward_array(value: Array<NestedSlot<i64>>) -> ArrayRing<i64> {
            wrap_array(move value)
        }
        answer() -> usize {
            let ring = forward_ring(empty_ring());
            Vec::len(&ring.slots)
        }
        main() -> () { () }
    "#;

    for optimization_level in [
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "nested-generic-fields.glorious",
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
        struct NestedSlot<T> { value: T }
        struct Ring<T> { slots: Vec<NestedSlot<T>> }
        impl Use<[1,1]> for Ticket {}
        impl<T> Use<[0,1]> for NestedSlot<T> where T: Use<[0,1]> {}
        impl<T> Use<[1,1]> for Ring<T> where T: Use<[1,1]> {}
        bad(value: Ring<Ticket>) -> () { () }
        main() -> () { () }
    "#;
    let errors = grandiose::compile_source_to_bytecode("nested-generic-use.glorious", source)
        .expect_err("the nested Vec<NestedSlot<T>> field lacks exact Use<[1,1]> evidence");
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
        let errors = grandiose::compile_source_to_bytecode("nested-generic-cycle.glorious", source)
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
        struct NestedSlot<T> { value: T }
        struct Ring<T> { slots: Vec<NestedSlot<T>> }
        struct ArrayRing<T> { slots: Array<NestedSlot<T>> }
        forward(value: Ring<i64>) -> Ring<i64> { value }
        forward_array(value: ArrayRing<i64>) -> ArrayRing<i64> { value }
        main() -> () { () }
    "#;
    let reordered = r#"
        main() -> () { () }
        forward_array(value: ArrayRing<i64>) -> ArrayRing<i64> { value }
        forward(value: Ring<i64>) -> Ring<i64> { value }
        struct ArrayRing<T> { slots: Array<NestedSlot<T>> }
        struct Ring<T> { slots: Vec<NestedSlot<T>> }
        struct NestedSlot<T> { value: T }
    "#;
    assert_eq!(
        grandiose::compile_source_to_bytecode("nested-order-a.glorious", first)
            .unwrap()
            .encode(),
        grandiose::compile_source_to_bytecode("nested-order-b.glorious", reordered)
            .unwrap()
            .encode()
    );
}
