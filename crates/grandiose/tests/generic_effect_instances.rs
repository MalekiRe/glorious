use grandiose::compile_source_to_bytecode;
use grandiose_vm::{I64, TEXT, Type, Value, Vm, verify};

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("missing `{name}`")) as u32
}

fn run(artifact: grandiose_vm::Artifact, name: &str) -> Value {
    let function = function_id(&artifact, name);
    Vm::new(verify(artifact).unwrap())
        .run(function, vec![])
        .unwrap()
}

#[test]
fn distinct_fail_instantiations_have_distinct_runtime_protocol_identities() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        i64_scope() -> / {Fail<i64>} { () }
        text_scope() -> / {Fail<Text>} { () }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("distinct-fail-instances.gr", source).unwrap();
    let fail = artifact
        .protocols
        .iter()
        .filter(|protocol| protocol.display_name == "Fail")
        .collect::<Vec<_>>();
    assert_eq!(fail.len(), 2);
    assert!(fail.iter().any(|protocol| protocol.type_arguments == [I64]));
    assert!(
        fail.iter()
            .any(|protocol| protocol.type_arguments == [TEXT])
    );
    assert_ne!(fail[0].type_arguments, fail[1].type_arguments);
}

#[test]
fn instantiated_text_perform_and_handler_execute_with_substituted_payload_type() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        selected() -> Text {
            handle perform Fail<Text>::fail("typed") {
                Fail<Text>::fail(error) => error
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("handled-fail-text.gr", source).unwrap();
    assert_eq!(run(artifact, "selected"), Value::Text("typed".into()));
}

#[test]
fn one_generic_effect_source_site_uses_each_ground_specialization() {
    let source = r#"
        enum Parcel<T> { Wrapped(T) }
        effect Inspect<T> { inspect(value: Parcel<T>) -> ! }
        unpack<T>(value: Parcel<T>) -> T {
            handle perform Inspect<T>::inspect(value) {
                Inspect<T>::inspect(Parcel::Wrapped(item)) => item
            }
        }
        integer() -> i64 { unpack(Parcel::Wrapped(42)) }
        text() -> Text { unpack(Parcel::Wrapped("typed")) }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("generic-effect-source-site.gr", source).unwrap();
    let inspect = artifact
        .protocols
        .iter()
        .filter(|protocol| protocol.display_name == "Inspect")
        .collect::<Vec<_>>();
    assert_eq!(inspect.len(), 2);
    assert!(
        inspect
            .iter()
            .any(|protocol| protocol.type_arguments == [I64])
    );
    assert!(
        inspect
            .iter()
            .any(|protocol| protocol.type_arguments == [TEXT])
    );
    assert_eq!(run(artifact.clone(), "integer"), Value::I64(42));
    assert_eq!(run(artifact, "text"), Value::Text("typed".into()));
}

#[test]
fn generic_callable_forwards_its_instantiated_effect_parameter_and_row() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        invoke<E, F>(error: E, body: F) -> ! / {Fail<E>}
            where F: Fn<(E), Output=!, Effects={Fail<E>}> {
            body(error)
        }
        selected() -> i64 {
            handle { invoke(42, { error => perform Fail<i64>::fail(error) }) } {
                Fail<i64>::fail(error) => error
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("forwarded-generic-fail.gr", source).unwrap();
    assert_eq!(run(artifact, "selected"), Value::I64(42));
}

#[test]
fn nearest_matching_instantiated_handler_wins() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        selected() -> i64 {
            handle {
                handle perform Fail<i64>::fail(41) {
                    Fail<i64>::fail(error) => error + 1
                }
            } {
                Fail<i64>::fail(error) => 0
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("nearest-generic-fail.gr", source).unwrap();
    assert_eq!(run(artifact, "selected"), Value::I64(42));
}

#[test]
fn wrong_type_instance_is_not_intercepted_and_reaches_matching_outer_handler() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        selected() -> i64 {
            handle {
                handle perform Fail<i64>::fail(42) {
                    Fail<Text>::fail(error) => 0
                }
            } {
                Fail<i64>::fail(error) => error
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("nonmatching-generic-fail.gr", source).unwrap();
    assert_eq!(run(artifact, "selected"), Value::I64(42));
}

#[test]
fn instantiated_protocol_artifact_is_stable_across_declaration_reordering() {
    let first = r#"
        effect Fail<E> { fail(error: E) -> ! }
        integer() -> / {Fail<i64>} { () }
        text() -> / {Fail<Text>} { () }
        main() -> { () }
    "#;
    let reordered = r#"
        main() -> { () }
        text() -> / {Fail<Text>} { () }
        integer() -> / {Fail<i64>} { () }
        effect Fail<E> { fail(error: E) -> ! }
    "#;
    let first = compile_source_to_bytecode("generic-effect-order-a.gr", first)
        .unwrap()
        .encode();
    let reordered = compile_source_to_bytecode("generic-effect-order-b.gr", reordered)
        .unwrap()
        .encode();
    assert_eq!(first, reordered);
}

#[test]
fn malformed_or_open_effect_instances_have_structured_diagnostics() {
    for (name, source, needle) in [
        (
            "wrong-arity.gr",
            "effect Fail<E> { fail(error:E) -> ! } bad() -> / {Fail<i64, Text>} { () } main() -> { () }",
            "argument",
        ),
        (
            "wrong-kind.gr",
            "effect Fail<E> { fail(error:E) -> ! } bad<e: EffectRow>() -> / {Fail<e>} { () } main() -> { () }",
            "type",
        ),
        (
            "unresolved-effect-binder.gr",
            "effect Fail<E> { fail(error:E) -> ! } bad() -> / {Fail<E>} { () } main() -> { () }",
            "E",
        ),
    ] {
        let diagnostics = compile_source_to_bytecode(name, source)
            .expect_err("an invalid effect instance reached bytecode emission");
        assert!(
            diagnostics
                .iter()
                .all(|diagnostic| diagnostic.code.is_some())
        );
        assert!(
            diagnostics.iter().any(|diagnostic| {
                diagnostic.span.is_some()
                    && (diagnostic.title.contains(needle) || diagnostic.message.contains(needle))
            }),
            "missing structured `{needle}` diagnostic: {diagnostics:#?}"
        );
    }
}

#[test]
fn effect_row_aliases_may_contain_instantiated_protocols() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        cases Failures = {Fail<i64>, Fail<Text>};
        scope() -> / {Failures} { () }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("instantiated-effect-row-alias.gr", source).unwrap();
    let fail = artifact
        .protocols
        .iter()
        .enumerate()
        .filter(|(_, protocol)| protocol.display_name == "Fail")
        .collect::<Vec<_>>();
    assert_eq!(fail.len(), 2);
    let scope = artifact
        .functions
        .iter()
        .find(|function| function.name == "scope")
        .unwrap();
    assert_eq!(scope.outward_protocols.len(), 2);
    assert!(
        fail.iter()
            .all(|(id, _)| scope.outward_protocols.contains(&(*id as u32)))
    );
}

#[test]
fn repeated_use_of_one_instance_dedupes_and_duplicate_display_names_are_rejected() {
    let deduped = r#"
        effect Fail<E> { fail(error: E) -> ! }
        first() -> / {Fail<i64>, Fail<i64>} { () }
        second() -> / {Fail<i64>} { () }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("deduped-effect-instance.gr", deduped).unwrap();
    assert_eq!(
        artifact
            .protocols
            .iter()
            .filter(|protocol| protocol.display_name == "Fail")
            .count(),
        1
    );
    for function in artifact
        .functions
        .iter()
        .filter(|function| function.name == "first" || function.name == "second")
    {
        assert_eq!(function.outward_protocols.len(), 1);
    }

    let duplicate = r#"
        effect Fail<E> { fail(error: E) -> ! }
        effect Fail<E> { fail(error: E) -> ! }
        main() -> { () }
    "#;
    let diagnostics = compile_source_to_bytecode("duplicate-effect-display-name.gr", duplicate)
        .expect_err("duplicate effect display names were accepted");
    assert!(diagnostics.iter().any(|diagnostic| {
        diagnostic.code.as_deref() == Some("G0002")
            && diagnostic.message.contains("declared more than once")
    }));
}

#[test]
fn generic_resumptions_have_distinct_identity_per_instance_and_handler_site() {
    let source = r#"
        effect Ask<E> { [1,1] ask(value: E) -> E }
        integer_first() -> i64 {
            handle perform Ask<i64>::ask(1) {
                Ask<i64>::ask(value) with continuation => resume(continuation, value)
            }
        }
        integer_second() -> i64 {
            handle perform Ask<i64>::ask(2) {
                Ask<i64>::ask(value) with continuation => resume(continuation, value)
            }
        }
        text() -> Text {
            handle perform Ask<Text>::ask("typed") {
                Ask<Text>::ask(value) with continuation => resume(continuation, value)
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("generic-resumption-identities.gr", source).unwrap();
    let ask_protocols = artifact
        .protocols
        .iter()
        .enumerate()
        .filter_map(|(id, protocol)| (protocol.display_name == "Ask").then_some(id as u32))
        .collect::<std::collections::BTreeSet<_>>();
    let ask_handlers = artifact
        .handler_defs
        .iter()
        .filter(|handler| {
            handler
                .clauses
                .iter()
                .any(|clause| ask_protocols.contains(&clause.protocol))
        })
        .collect::<Vec<_>>();
    assert_eq!(ask_handlers.len(), 3);
    let resumptions = artifact
        .handler_defs
        .iter()
        .filter(|handler| {
            handler
                .clauses
                .iter()
                .any(|clause| ask_protocols.contains(&clause.protocol))
        })
        .map(|handler| handler.clauses[0].resumption_type.unwrap())
        .collect::<Vec<_>>();
    assert_eq!(
        resumptions
            .iter()
            .copied()
            .collect::<std::collections::BTreeSet<_>>()
            .len(),
        3,
        "each handler site requires a distinct K identity, including sibling instances"
    );
    let identities = resumptions
        .iter()
        .map(|ty| match artifact.types[*ty as usize].representation() {
            Type::Resumption { identity_name, .. } => identity_name.as_str(),
            other => panic!("expected resumption type, found {other:?}"),
        })
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(identities.len(), 3);
    assert_eq!(run(artifact.clone(), "integer_first"), Value::I64(1));
    assert_eq!(run(artifact.clone(), "integer_second"), Value::I64(2));
    assert_eq!(run(artifact, "text"), Value::Text("typed".into()));
}

#[test]
fn handling_one_instance_leaves_its_sibling_instance_outward() {
    let source = r#"
        effect Fail<E> { fail(error: E) -> ! }
        both() -> i64 / {Fail<i64>, Fail<Text>} {
            perform Fail<i64>::fail(1)
        }
        forward_text() -> i64 / {Fail<Text>} {
            handle { both() } {
                Fail<i64>::fail(error) => error
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("generic-effect-sibling-outward.gr", source).unwrap();
    let integer = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Fail" && protocol.type_arguments == [I64])
        .unwrap() as u32;
    let text = artifact
        .protocols
        .iter()
        .position(|protocol| protocol.display_name == "Fail" && protocol.type_arguments == [TEXT])
        .unwrap() as u32;
    let both = artifact
        .functions
        .iter()
        .find(|function| function.name == "both")
        .unwrap();
    let forward = artifact
        .functions
        .iter()
        .find(|function| function.name == "forward_text")
        .unwrap();
    assert_eq!(both.outward_protocols, [integer, text]);
    assert_eq!(forward.outward_protocols, [text]);
}
