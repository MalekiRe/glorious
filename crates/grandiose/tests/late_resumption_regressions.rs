use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{compile_bundle_to_bytecode, compile_source_to_bytecode, compile_source_to_phases};
use grandiose_vm::{Type, Value, Vm, verify};

#[test]
fn late_resumption_round_trips_through_nested_tuple_and_generic_wrappers() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Wrap<T> { value: T }
        struct Outer<T> { payload: (i64, (Wrap<T>,)) }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let wrapped = Wrap { value: move k };
                    let outer = Outer { payload: (7, (move wrapped,)) };
                    let Outer { payload } = move outer;
                    let (marker, nested) = move payload;
                    let (wrapped,) = move nested;
                    let Wrap { value } = move wrapped;
                    resume(move value, marker + 35)
                }
            }
        }
        main() -> { () }
    "#;

    let artifact = compile_source_to_bytecode("nested-late-wrapper.gr", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn late_resumption_closure_identity_survives_declaration_reordering() {
    let before = r#"
        unrelated() -> i64 { 9 }
        effect Ask { [1,1] ask() -> i64 }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let finish = { => resume(move k, 42) };
                    finish()
                }
            }
        }
        main() -> { () }
    "#;
    let after = r#"
        effect Ask { [1,1] ask() -> i64 }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let finish = { => resume(move k, 42) };
                    finish()
                }
            }
        }
        unrelated() -> i64 { 9 }
        main() -> { () }
    "#;

    let first = compile_source_to_phases("late-closure-order.gr", before).unwrap();
    let repeated = compile_source_to_phases("late-closure-order.gr", before).unwrap();
    let reordered = compile_source_to_phases("late-closure-order.gr", after).unwrap();
    assert_eq!(first.core_fingerprint(), repeated.core_fingerprint());
    assert_eq!(first.mir_fingerprint(), repeated.mir_fingerprint());
    assert_eq!(first.artifact.encode(), reordered.artifact.encode());
}

#[test]
fn different_handler_sites_get_distinct_late_box_identities() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Box<T> { value: T }
        first() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let boxed = Box { value: move k };
                    let Box { value } = move boxed;
                    resume(move value, 41)
                }
            }
        }
        second() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let boxed = Box { value: move k };
                    let Box { value } = move boxed;
                    resume(move value, 42)
                }
            }
        }
        main() -> { () }
    "#;

    let artifact = compile_source_to_bytecode("distinct-late-boxes.gr", source).unwrap();
    let mut boxes = artifact
        .types
        .iter()
        .filter_map(|ty| match ty.representation() {
            Type::Struct { name, .. } if name.starts_with("Box<") => Some(name.as_str()),
            _ => None,
        })
        .collect::<Vec<_>>();
    boxes.sort_unstable();
    boxes.dedup();
    assert_eq!(
        boxes.len(),
        2,
        "expected one distinct Box identity per handler site"
    );

    let verified = verify(artifact).unwrap();
    for (name, expected) in [("first", 41), ("second", 42)] {
        let function = verified
            .artifact()
            .functions
            .iter()
            .position(|function| function.name == name)
            .unwrap() as u32;
        assert_eq!(
            Vm::new(verified.clone()).run(function, vec![]).unwrap(),
            Value::I64(expected)
        );
    }
}

#[test]
fn late_resumption_instantiates_a_generic_wrapper_over_a_tuple() {
    let source = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Wrap<T> { value: T }
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let wrapped = Wrap { value: (move k,) };
                    let Wrap { value } = move wrapped;
                    let (restored,) = move value;
                    resume(move restored, 42)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("late-tuple-wrapper.gr", source).unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );
}

#[test]
fn late_resumption_specializes_a_private_generic_sealing_function() {
    let owner = r#"
        effect Ask { [1,1] ask() -> i64 }
        struct Secret<T> { private value: T }
        seal<T>(value: T) -> Secret<T> { Secret { value: move value } }
        unseal<T>(secret: Secret<T>) -> T {
            let Secret { value } = move secret;
            move value
        }
    "#;
    let caller = r#"
        answer() -> i64 {
            handle perform Ask::ask() {
                Ask::ask() with k => {
                    let secret = seal(move k);
                    let value = unseal(move secret);
                    resume(move value, 42)
                }
            }
        }
        main() -> { () }
    "#;
    let artifact = compile_bundle_to_bytecode(&SourceBundle::new(
        Segment::new("owner.gr", owner),
        Segment::new("caller.gr", caller),
        [],
    ))
    .unwrap();
    let answer = artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    assert_eq!(
        Vm::new(verify(artifact).unwrap())
            .run(answer, vec![])
            .unwrap(),
        Value::I64(42)
    );

    let rejected = compile_bundle_to_bytecode(&SourceBundle::new(
        Segment::new(
            "owner.gr",
            r#"
                effect Ask { [1,1] ask() -> i64 }
                struct Secret<T> { private value: T }
                seal<T>(value: T) -> Secret<T> { Secret { value: move value } }
            "#,
        ),
        Segment::new(
            "caller.gr",
            r#"
                bad() -> i64 {
                    handle perform Ask::ask() {
                        Ask::ask() with k => {
                            let secret = seal(move k);
                            let Secret { value } = move secret;
                            resume(move value, 42)
                        }
                    }
                }
                main() -> { () }
            "#,
        ),
        [],
    ))
    .unwrap_err();
    assert!(
        rejected.iter().any(|diagnostic| {
            diagnostic
                .message
                .contains("private fields of struct `Secret`")
                && diagnostic.message.contains("defining source segment")
        }),
        "{rejected:#?}"
    );
}
