use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode, compile_source_to_phases,
    compile_source_to_phases_with_options,
};
use grandiose_vm::{Instruction, Type, Value, Vm, verify};

fn run_i64_at_all_levels(source_name: &str, source: &str, function: &str, expected: i64) {
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            source_name,
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        let function = phases
            .artifact
            .functions
            .iter()
            .position(|candidate| candidate.name == function)
            .unwrap() as u32;
        let verified = verify(phases.artifact).unwrap();
        assert_eq!(
            Vm::new(verified).run(function, vec![]).unwrap(),
            Value::I64(expected),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn exhaustive_deconstruction_releases_empty_and_nonempty_exact_linear_structs() {
    let source = r#"
        struct Empty {}
        struct Parcel { value: i64 }
        impl Use<[1,1]> for Empty {}
        impl Use<[1,1]> for Parcel {}

        answer() -> i64 {
            let empty = Empty {};
            let Empty {} = empty;
            let parcel = Parcel { value: 42 };
            let Parcel { value: renamed } = parcel;
            renamed
        }
        main() -> { answer(); () }
    "#;

    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "deconstruct.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(phases.core.canonical_text().contains("deconstruct"));
        assert!(phases.mir.canonical_text().contains("ProjectMove"));
        let answer = phases
            .artifact
            .functions
            .iter()
            .position(|function| function.name == "answer")
            .unwrap() as u32;
        let answer_function = &phases.artifact.functions[answer as usize];
        assert_eq!(
            phases.artifact.code[answer_function.code_start as usize
                ..(answer_function.code_start + answer_function.code_len) as usize]
                .iter()
                .filter(|instruction| matches!(instruction, Instruction::Deconstruct { .. }))
                .count(),
            2,
            "{optimization_level:?}"
        );

        let verified = verify(phases.artifact).unwrap();
        assert_eq!(
            Vm::new(verified).run(answer, vec![]).unwrap(),
            Value::I64(42),
            "{optimization_level:?}"
        );
    }
}

#[test]
fn deconstruction_rejects_duplicate_and_unknown_fields() {
    let cases = [
        (
            "duplicate",
            "struct Pair { left: i64, right: i64 } bad(value: Pair) -> i64 { let Pair { left, left: again, right } = value; left + again + right } main() -> { () }",
            "more than once",
        ),
        (
            "unknown",
            "struct Pair { left: i64, right: i64 } bad(value: Pair) -> i64 { let Pair { left, right, third } = value; left + right + third } main() -> { () }",
            "no field",
        ),
    ];

    for (name, source, expected) in cases {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "expected `{expected}` diagnostic, got {errors:#?}"
        );
    }
}

#[test]
fn deconstructed_positive_lower_field_remains_a_checked_owner() {
    let source = r#"
        struct Token { marker: i64 }
        struct Envelope { token: Token }
        impl Use<[1,1]> for Token {}
        impl Use<[1,1]> for Envelope {}
        bad(value: Envelope) -> {
            let Envelope { token } = value;
            let moved = token;
            ()
        }
        main() -> { () }
    "#;

    let errors = compile_source_to_bytecode("deconstruct-discard.gr", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("actual Use count 0")
                && error.message.contains("outside principal interval [1,1]")
        }),
        "got {errors:#?}"
    );
}

#[test]
fn deconstruction_discharges_the_shells_complete_residual_quantity() {
    let source = r#"
        struct ExactlyTwo { value: i64 }
        impl Use<[2,2]> for ExactlyTwo {}
        unwrap(owner: ExactlyTwo) -> i64 {
            let ExactlyTwo { value } = owner;
            value
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("deconstruct-residual-use.gr", source).unwrap();
    verify(artifact).unwrap();
}

#[test]
fn custom_drop_structs_cannot_be_deconstructed() {
    let source = r#"
        struct Guard { marker: i64 }
        impl Drop for Guard { drop(&mut self) -> { self.marker; () } }
        bad(value: Guard) -> i64 {
            let Guard { marker } = value;
            marker
        }
        main() -> { () }
    "#;

    let errors = compile_source_to_bytecode("deconstruct-drop.gr", source).unwrap_err();
    assert!(errors.iter().any(|error| {
        error.message.contains("custom Drop") && error.message.contains("deconstruct")
    }));
}

#[test]
fn deconstruction_transfers_reference_field_origins() {
    let reference = r#"
        struct Borrowed { value: &mut i64 }
        unpack_borrowed(value: Borrowed) -> i64 {
            let Borrowed { value } = value;
            *value
        }
        answer() -> i64 {
            let number = 42;
            unpack_borrowed(Borrowed { value: &mut number })
        }
        main() -> { () }
    "#;
    run_i64_at_all_levels("deconstruct-reference.gr", reference, "answer", 42);
}

#[test]
fn deconstruction_rejects_erased_fields_before_owner_creation() {
    let erased = r#"
        struct Erased {}
        struct Envelope { erased: Erased }
        impl Use<[0,0]> for Erased {}
        bad(value: Envelope) -> {
            let Envelope { erased } = value;
            ()
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("deconstruct-erased.gr", erased).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("compiler-erased deconstruction field")
                && error.message.contains("[0,0]")
                && error.code.as_deref() == Some("G1BC001")
        }),
        "got {errors:#?}"
    );
}

#[test]
fn deconstruction_bindings_may_shadow_outer_locals() {
    let source = r#"
        struct Parcel { value: i64 }
        impl Use<[1,1]> for Parcel {}
        answer() -> i64 {
            let value = 1;
            let parcel = Parcel { value: 42 };
            let Parcel { value } = parcel;
            value
        }
        main() -> { answer(); () }
    "#;

    let artifact = compile_source_to_bytecode("deconstruct-shadow.gr", source).unwrap();
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
fn exhaustive_tuple_deconstruction_lowers_through_core_mir_and_vm() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}

        answer() -> i64 {
            let pair = (Token { marker: 40 }, 2);
            let (token, amount) = pair;
            let Token { marker } = token;
            marker + amount
        }
        singleton() -> i64 {
            let value = (7,);
            let (element,) = value;
            element
        }
        main() -> { answer(); singleton(); () }
    "#;

    let phases = compile_source_to_phases("tuple-deconstruct.gr", source).unwrap();
    assert!(phases.core.canonical_text().contains("deconstruct"));
    assert!(phases.mir.canonical_text().contains("ProjectMove"));
    assert!(
        phases
            .artifact
            .code
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Deconstruct { .. }))
            .count()
            >= 3
    );
    let answer = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "answer")
        .unwrap() as u32;
    let singleton = phases
        .artifact
        .functions
        .iter()
        .position(|function| function.name == "singleton")
        .unwrap() as u32;
    let verified = verify(phases.artifact).unwrap();
    let vm = Vm::new(verified);
    assert_eq!(vm.run(answer, vec![]).unwrap(), Value::I64(42));
    assert_eq!(vm.run(singleton, vec![]).unwrap(), Value::I64(7));
}

#[test]
fn tuple_deconstruction_rejects_excess_arity_and_duplicate_bindings() {
    let cases = [
        (
            "extra",
            "bad(value: (i64, i64)) -> i64 { let (a, b, c) = value; a + b + c } main() -> { () }",
            "no element at index",
        ),
        (
            "duplicate-binding",
            "bad(value: (i64, i64)) -> i64 { let (same, same) = value; same } main() -> { () }",
            "binding `same` appears more than once",
        ),
    ];

    for (name, source, expected) in cases {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "expected `{expected}` diagnostic, got {errors:#?}"
        );
    }

    let invalid_singleton =
        "bad(value: (i64,)) -> i64 { let (element) = value; element } main() -> { () }";
    let errors =
        compile_source_to_bytecode("singleton-without-comma", invalid_singleton).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.title.contains("singleton tuple deconstruction")
                && error.message.contains("trailing comma")
        }),
        "got {errors:#?}"
    );

    let unit = "bad(value: ()) -> { let () = value; () } main() -> { () }";
    let errors = compile_source_to_bytecode("unit-pattern", unit).unwrap_err();
    assert!(
        errors.iter().any(|error| error
            .message
            .contains("tuple deconstruction expects a tuple")),
        "the unit pattern must not be mistaken for an aggregate tuple: {errors:#?}"
    );
}

#[test]
fn wildcard_rest_and_omitted_fields_are_zero_use_disposals() {
    let source = r#"
        struct Pair { left: i64, right: i64 }

        struct Affine { marker: i64 }
        impl Use<[0,1]> for Affine {}
        struct Envelope { first: Affine, second: Affine, third: Affine }

        struct_only_left(value: Pair) -> i64 {
            let Pair { left } = value;
            left
        }
        struct_wildcard(value: Pair) -> i64 {
            let Pair { left, right: _ } = value;
            left
        }
        struct_rest(value: Pair) -> i64 {
            let Pair { left, .. } = value;
            left
        }
        tuple_middle_rest(value: (i64, i64, i64)) -> i64 {
            let (first, .., last) = value;
            first + last
        }
        tuple_wildcard(value: (i64, i64)) -> i64 {
            let (_, last) = value;
            last
        }
        tuple_omission(value: (i64, i64)) -> i64 {
            let (first,) = value;
            first
        }
        dispose_affine(value: Envelope) -> {
            let Envelope { first: _, .. } = value;
            ()
        }
        main() -> {
            struct_only_left(Pair { left: 10, right: 90 });
            struct_wildcard(Pair { left: 20, right: 80 });
            struct_rest(Pair { left: 30, right: 70 });
            tuple_middle_rest((1, 100, 2));
            tuple_wildcard((100, 4));
            tuple_omission((5, 100));
            ()
        }
    "#;

    let phases = compile_source_to_phases("zero-use-patterns.gr", source).unwrap();
    let text = phases.core.canonical_text();
    assert!(text.contains("destroy:t10"));
    assert!(
        phases
            .artifact
            .code
            .iter()
            .any(|instruction| { matches!(instruction, Instruction::Drop { .. }) })
    );
    verify(phases.artifact).unwrap();
}

#[test]
fn discarded_fields_reject_positive_use_and_malformed_remainders() {
    let positive_cases = [
        (
            "wildcard",
            "struct Token {} impl Use<[1,1]> for Token {} struct Boxed { token: Token } bad(value: Boxed) -> { let Boxed { token: _ } = value; () } main() -> { () }",
        ),
        (
            "omitted",
            "struct Token {} impl Use<[1,1]> for Token {} struct Boxed { token: Token } bad(value: Boxed) -> { let Boxed {} = value; () } main() -> { () }",
        ),
        (
            "rest",
            "struct Token {} impl Use<[1,1]> for Token {} bad(value: (i64, Token)) -> i64 { let (first, ..) = value; first } main() -> { () }",
        ),
    ];
    for (name, source) in positive_cases {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| {
                error.message.contains("does not permit zero-use disposal")
                    && error.message.contains("[1,1]")
            }),
            "got {errors:#?}"
        );
    }

    for (name, source, expected) in [
        (
            "two-tuple-rests",
            "bad(value: (i64, i64)) -> { let (.., ..) = value; () } main() -> { () }",
            "only one `..`",
        ),
        (
            "two-struct-rests",
            "struct Pair { x: i64 } bad(value: Pair) -> { let Pair { .., .. } = value; () } main() -> { () }",
            "only one `..`",
        ),
        (
            "overlapping-rest",
            "bad(value: (i64,)) -> i64 { let (first, .., last) = value; first + last } main() -> { () }",
            "more than once",
        ),
    ] {
        let errors = compile_source_to_bytecode(name, source).unwrap_err();
        assert!(
            errors.iter().any(|error| error.message.contains(expected)),
            "got {errors:#?}"
        );
    }
}

#[test]
fn exact_zero_discard_is_erased_from_aggregate_layout_and_code() {
    let source = r#"
        struct Erased {}
        impl Use<[0,0]> for Erased {}
        struct Envelope { proof: Erased }
        struct_discard(value: Envelope) -> {
            let Envelope {} = value;
            ()
        }
        main() -> { () }
    "#;
    let phases = compile_source_to_phases("erased-discard.gr", source).unwrap();
    assert!(phases.core.canonical_text().contains("destroy-erased"));

    let envelope = phases
        .artifact
        .types
        .iter()
        .find_map(|ty| match ty.representation() {
            Type::Struct { name, fields, .. } if name == "Envelope" => Some(fields),
            _ => None,
        })
        .unwrap();
    assert!(matches!(
        phases.artifact.types[envelope[0].ty as usize],
        Type::Available { .. }
    ));

    let function = phases
        .artifact
        .functions
        .iter()
        .find(|function| function.name == "struct_discard")
        .unwrap();
    let code = &phases.artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    assert!(matches!(
        code,
        [Instruction::Deconstruct { .. }, Instruction::Return { .. }]
    ));
    verify(phases.artifact).unwrap();
}

#[test]
fn exact_zero_field_with_observable_drop_keeps_its_runtime_slot() {
    let source = r#"
        struct Proof { marker: i64 }
        impl Use<[0,0]> for Proof {}
        impl Drop for Proof { drop(&mut self) -> { self.marker; () } }
        struct Envelope { proof: Proof }
        discard(value: Envelope) -> {
            let Envelope {} = value;
            ()
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("observable-zero-drop.gr", source).unwrap();
    let envelope = artifact
        .types
        .iter()
        .find_map(|ty| match ty.representation() {
            Type::Struct { name, fields, .. } if name == "Envelope" => Some(fields),
            _ => None,
        })
        .unwrap();
    assert!(!matches!(
        artifact.types[envelope[0].ty as usize],
        Type::Available { .. }
    ));
    let function = artifact
        .functions
        .iter()
        .find(|function| function.name == "discard")
        .unwrap();
    let code = &artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    assert!(matches!(
        code,
        [
            Instruction::ProjectMove { field: 0, .. },
            Instruction::Drop { .. },
            Instruction::Deconstruct { .. },
            Instruction::Return { .. }
        ]
    ));
    verify(artifact).unwrap();
}

#[test]
fn discarded_runtime_fields_drop_in_reverse_declaration_order() {
    let source = r#"
        struct Child { marker: i64 }
        impl Use<[0,0]> for Child {}
        impl Drop for Child { drop(&mut self) -> { self.marker; () } }
        struct Bundle { first: Child, second: Child }
        discard(value: Bundle) -> {
            let Bundle {} = value;
            ()
        }
        main() -> { () }
    "#;
    let artifact = compile_source_to_bytecode("reverse-discard.gr", source).unwrap();
    let function = artifact
        .functions
        .iter()
        .find(|function| function.name == "discard")
        .unwrap();
    let code = &artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    assert!(
        matches!(
            code,
            [
                Instruction::ProjectMove {
                    dst: 2,
                    field: 0,
                    ..
                },
                Instruction::ProjectMove {
                    dst: 3,
                    field: 1,
                    ..
                },
                Instruction::Drop { register: 3 },
                Instruction::Drop { register: 2 },
                Instruction::Deconstruct { .. },
                Instruction::Return { .. }
            ]
        ),
        "unexpected disposal order: {code:#?}"
    );
    verify(artifact).unwrap();
}

#[test]
fn tuple_deconstruction_rejects_borrowed_and_partially_moved_sources() {
    let borrowed = r#"
        bad(value: (i64, i64)) -> i64 {
            let loan = &value;
            let (left, right) = value;
            loan.0 + left + right
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("tuple-deconstruct-borrowed.gr", borrowed).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("cannot be deconstructed") && error.message.contains("borrowed")
        }),
        "got {errors:#?}"
    );

    let partially_moved = r#"
        struct Once { marker: i64 }
        impl Use<[0,1]> for Once {}
        bad(value: (Once, i64)) -> i64 {
            let first = value.0;
            let (again, number) = value;
            number
        }
        main() -> { () }
    "#;
    let errors =
        compile_source_to_bytecode("tuple-deconstruct-partial.gr", partially_moved).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("already moved or partially moved")
                && error.message.contains("cannot be deconstructed")
        }),
        "got {errors:#?}"
    );
}

#[test]
fn tuple_deconstructed_positive_lower_elements_remain_checked_owners() {
    let source = r#"
        struct Token { marker: i64 }
        impl Use<[1,1]> for Token {}
        bad(value: (Token, i64)) -> {
            let (token, number) = value;
            let moved = token;
            number;
            ()
        }
        main() -> { () }
    "#;

    let errors = compile_source_to_bytecode("tuple-deconstruct-discard.gr", source).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("actual Use count 0")
                && error.message.contains("outside principal interval [1,1]")
        }),
        "got {errors:#?}"
    );
}

#[test]
fn tuple_deconstruction_transfers_reference_element_origins() {
    let reference = r#"
        unpack_borrowed_tuple(value: (&mut i64, i64)) -> i64 {
            let (borrowed, number) = value;
            *borrowed + number
        }
        answer() -> i64 {
            let number = 40;
            unpack_borrowed_tuple((&mut number, 2))
        }
        main() -> { () }
    "#;
    run_i64_at_all_levels("tuple-deconstruct-reference.gr", reference, "answer", 42);
}

#[test]
fn tuple_deconstruction_rejects_erased_elements() {
    let erased = r#"
        struct Erased {}
        impl Use<[0,0]> for Erased {}
        bad(value: (Erased, i64)) -> {
            let (erased, number) = value;
            number;
            ()
        }
        main() -> { () }
    "#;
    let errors = compile_source_to_bytecode("tuple-deconstruct-erased.gr", erased).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error
                .message
                .contains("compiler-erased deconstruction field")
                && error.message.contains("[0,0]")
                && error.code.as_deref() == Some("G1BC001")
        }),
        "got {errors:#?}"
    );
}
