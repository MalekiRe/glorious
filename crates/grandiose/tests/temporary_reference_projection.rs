use grandiose_vm::{Value, Vm, verify};

#[test]
fn call_returned_reference_supports_direct_field_projection() {
    let source = r#"
        struct Inner { value: i64 }
        struct Outer { inner: Inner }

        relay<'a>(value: &'a Outer) -> &'a Outer { value }

        selected() -> i64 {
            let value = Outer { inner: Inner { value: 42 } };
            relay(&value).inner.value
        }

        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("temporary-reference-projection.glorious", source)
            .unwrap();
    let selected = artifact
        .functions
        .iter()
        .position(|function| function.name == "selected")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(selected, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn comparison_uses_the_known_operand_when_handler_binding_is_opaque() {
    let source = r#"
        struct Search { count: u32 }

        u32_value(value: u32) -> u32 { value }

        selected(value: Result<Search, ()>) -> Bool {
            handle value {
                Result::Ok(found) => found.count == u32_value(0),
                Result::Err(_) => false
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("opaque-handler-comparison.glorious", source).unwrap();
}

#[test]
fn generic_option_handler_binding_types_field_projection_for_operator_selection() {
    let source = r#"
        struct TypeId { index: u32 }
        struct CallableHeader { result: Option<TypeId> }

        result_index_plus_one(value: &CallableHeader) -> u32 {
            handle Option::as_ref(&value.result) {
                Result::Err(_) => 0,
                Result::Ok(result) => result.index + wrapping_convert_to_u32(1)
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("generic-option-handler-projection.glorious", source)
        .unwrap();
}

#[test]
fn structural_call_results_flow_through_nested_operators_and_projection() {
    let source = r#"
        struct Entry { value: u32 }

        usize_value<T>(value: T) -> usize { wrapping_convert_to_usize(value) }
        usize_from_u32(value: u32) -> usize { wrapping_convert_to_usize(value) }
        u32_value<T>(value: T) -> u32 { wrapping_convert_to_u32(value) }

        projected(values: &Vec<Entry>, index: usize) -> u32 {
            Vec::index(values, index * usize_value(4) + usize_value(1)).value
        }

        before(values: &Vec<Entry>, shell: u32) -> Bool {
            usize_from_u32(shell) < Vec::len(values)
        }

        equal(found: u32) -> Bool {
            found == u32_value(0)
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("nested-structural-call-results.glorious", source)
        .unwrap();
}

#[test]
fn inferred_handler_result_types_flow_to_following_operators() {
    let source = r#"
        u8_value(value: u8) -> u8 { value }

        selected(flag: Bool) -> Bool {
            let kind = handle flag {
                Result::Err(_) => u8_value(0),
                Result::Ok(_) => u8_value(1)
            };
            kind == u8_value(0)
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("inferred-handler-result.glorious", source).unwrap();
}

#[test]
fn public_generic_associated_call_remains_callable_inside_comparison() {
    let source = r#"
        fill_zeroes(value: &mut Vec<u32>, count: usize) -> Bool {
            Vec::len(value) < count
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("public-generic-associated-comparison.glorious", source)
        .unwrap();
}

#[test]
fn generic_array_len_wrapper_remains_manifest_lowered() {
    let source = r#"
        generic_len<T>(value: &Vec<T>) -> usize {
            Vec::len(value)
        }

        len(value: &Vec<u32>) -> usize {
            generic_len(value)
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("late-generic-array-len.glorious", source).unwrap();
}

#[test]
fn byte_view_wrapper_agrees_with_manifest_bytes_slice_lowering() {
    let source = r#"
        copy(value: &ByteView) -> Bytes {
            ByteView::to_bytes(value)
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("late-byte-view-bytes-slice.glorious", source).unwrap();
}

#[test]
fn character_iteration_keeps_manifest_bytes_get_index_as_usize() {
    let source = r#"
        next(value: &mut Chars) -> Option<char> {
            Chars::next(value)
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("late-bytes-get-index-type.glorious", source).unwrap();
}

#[test]
fn assignment_accepts_temporary_unique_reference_from_generic_associated_call() {
    let source = r#"
        struct Values { items: Vec<u32> }

        write(value: &mut Values) -> () {
            *Vec::index_mut(&mut value.items, wrapping_convert_to_usize(0)) =
                wrapping_convert_to_u32(42);
            ()
        }

        write_on_one_branch(value: &mut Values, flag: Bool) -> () {
            handle flag {
                Result::Ok(_) => {
                    *Vec::index_mut(&mut value.items, wrapping_convert_to_usize(0)) =
                        wrapping_convert_to_u32(42);
                    ()
                },
                Result::Err(_) => ()
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode(
        "generic-associated-unique-reference-assignment.glorious",
        source,
    )
    .unwrap();
}

#[test]
fn borrowed_enum_scrutinee_supports_non_consuming_variant_patterns() {
    let source = r#"
        enum NumberBase { Binary, Octal, Decimal, Hex }

        number_base(value: &NumberBase) -> u32 {
            handle value {
                NumberBase::Binary => 2,
                NumberBase::Octal => 8,
                NumberBase::Decimal => 10,
                NumberBase::Hex => 16
            }
        }

        main() -> () { () }
    "#;
    grandiose::compile_source_to_bytecode("borrowed-enum-handler.glorious", source).unwrap();
}

#[test]
fn reference_carrier_pattern_binding_preserves_its_origin() {
    let source = r#"
        struct ProbeRange { count: u32 }
        struct ProbeCallable { parameters: ProbeRange }

        find<'a>(values: &'a Vec<ProbeCallable>) -> Option<&'a ProbeCallable> {
            Vec::get(values, 0)
        }

        parameters<'a>(callable: &'a ProbeCallable) -> &'a ProbeRange {
            &callable.parameters
        }

        read(value: Option<&ProbeCallable>) -> u32 {
            handle value {
                Result::Err(_) => 0,
                Result::Ok(callable) => parameters(callable).count
            }
        }

        selected(values: &Vec<ProbeCallable>) -> u32 {
            read(find(values))
        }

        some() -> u32 {
            let callable = ProbeCallable { parameters: ProbeRange { count: 42 } };
            read(Result::Ok(&callable))
        }

        none() -> u32 {
            read(Result::Err(()))
        }

        main() -> () { () }
    "#;
    let artifact =
        grandiose::compile_source_to_bytecode("reference-carrier-pattern.glorious", source)
            .unwrap();
    let some = artifact
        .functions
        .iter()
        .position(|function| function.name == "some")
        .unwrap() as u32;
    let none = artifact
        .functions
        .iter()
        .position(|function| function.name == "none")
        .unwrap() as u32;
    let verified = verify(artifact).unwrap();
    assert_eq!(
        Vm::new(verified.clone()).run(some, vec![]).unwrap(),
        Value::U64(42)
    );
    assert_eq!(Vm::new(verified).run(none, vec![]).unwrap(), Value::U64(0));
}
