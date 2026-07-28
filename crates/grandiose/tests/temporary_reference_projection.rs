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
