use grandiose::{
    CompileOptions, OptimizationLevel, compile_source_to_bytecode,
    compile_source_to_phases_with_options,
    compiler_mir::{CleanupAction, CleanupEdge},
    lexer, parser, validate,
};
use grandiose_vm::{Value, Vm, verify};

fn validate_source(source: &str) -> Result<(), Vec<grandiose::diagnostic::Diagnostic>> {
    let tokens = lexer::lex(source).map_err(|error| vec![error])?;
    let (program, parse_errors) = parser::parse_recovering(tokens);
    if !parse_errors.is_empty() {
        return Err(parse_errors);
    }
    validate::validate(&program)
}

fn assert_label_error(source: &str, code: &str, message: &str) {
    let errors = validate_source(source).expect_err("invalid label program validated");
    assert!(
        errors.iter().any(|error| {
            error.code.as_deref() == Some(code) && error.message.contains(message)
        }),
        "expected {code} containing {message:?}, got {errors:#?}"
    );
    assert!(
        errors
            .iter()
            .all(|error| error.code.as_deref() != Some("G0124"))
    );
}

#[test]
fn nested_typed_destinations_and_unit_destinations_validate_lexically() {
    validate_source(
        r#"
            answer() -> i64 {
                label @outer: i64 {
                    label @inner: {
                        leave@inner();
                        leave@outer(42)
                    }
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn generative_labeled_blocks_expose_their_brand_only_inside_the_body() {
    validate_source(
        r#"
            answer() -> {
                @scope: {
                    @scope;
                    ()
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn labeled_trailing_application_and_loop_syntax_share_lexical_brand_rules() {
    validate_source(
        r#"
            loop<L>(body: L) -> { () }
            answer() -> {
                loop @outer: {
                    @outer;
                    ()
                }
            }
            main() -> { () }
        "#,
    )
    .unwrap();
}

#[test]
fn unknown_and_out_of_scope_labels_are_rejected() {
    assert_label_error(
        r#"
            answer() -> { @missing }
            main() -> { () }
        "#,
        "G0132",
        "not active",
    );
    assert_label_error(
        r#"
            answer() -> {
                label @done: { () };
                leave@done()
            }
            main() -> { () }
        "#,
        "G0132",
        "no active lexical destination",
    );
}

#[test]
fn an_active_label_name_cannot_be_shadowed_by_another_brand() {
    assert_label_error(
        r#"
            answer() -> {
                @scope: {
                    label @scope: { () }
                }
            }
            main() -> { () }
        "#,
        "G0131",
        "already active",
    );
}

#[test]
fn generative_labels_do_not_grant_direct_destination_evidence() {
    assert_label_error(
        r#"
            answer() -> i64 {
                @scope: { leave@scope(42) }
            }
            main() -> { () }
        "#,
        "G0133",
        "no `Destination` evidence",
    );
}

#[test]
fn obvious_leave_value_mismatches_are_source_diagnostics() {
    assert_label_error(
        r#"
            answer() -> i64 {
                label @done: i64 { leave@done("wrong") }
            }
            main() -> { () }
        "#,
        "G0134",
        "incompatible value",
    );
    assert_label_error(
        r#"
            answer() -> i64 {
                label @done: i64 { leave@done() }
            }
            main() -> { () }
        "#,
        "G0134",
        "incompatible value",
    );
}

#[test]
fn nested_leave_executes_the_outer_typed_destination() {
    let source = r#"
        answer() -> i64 {
            label @outer: i64 {
                label @inner: i64 {
                    leave@outer(42)
                }
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("nested-leave.gr", source).unwrap();
}

#[test]
fn leave_cleans_intervening_linear_owners_without_bypassing_use() {
    let source = r#"
        struct Ticket { value: i64 }
        impl Use<[1,1]> for Ticket {}
        consume(ticket: Ticket) -> { let Ticket { value: _ } = move ticket; () }
        answer() -> i64 {
            label @done: i64 {
                let ticket = Ticket { value: 1 };
                consume(move ticket);
                leave@done(42)
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-cleanup.gr", source).unwrap();
}

#[test]
fn reference_result_provenance_crosses_leave_but_cannot_escape_its_referent() {
    let source = r#"
        select<'a>(value: &'a i64) -> &'a i64 {
            label @done: &'a i64 { leave@done(value) }
        }
        answer() -> i64 {
            let value = 42;
            let selected = select(&value);
            *selected
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-reference-result.gr", source).unwrap();
}

#[test]
fn leave_does_not_bypass_private_deconstruction_authority() {
    let source = r#"
        struct Secret { private value: i64 }
        answer(secret: Secret) -> i64 {
            label @done: i64 {
                let Secret { value } = move secret;
                leave@done(value)
            }
        }
        main() -> { () }
    "#;
    compile_source_to_bytecode("leave-private-field.gr", source).unwrap();
}

#[test]
fn nested_leave_cleans_partial_owners_and_loans_at_all_optimization_levels() {
    let source = r#"
        struct Resource { value: i64 }
        impl Use<[0,1]> for Resource {}
        struct Parcel { left: Resource, right: Resource }
        observe(value: &Resource) -> { () }
        answer() -> i64 {
            label @outer: i64 {
                let parcel = Parcel {
                    left: Resource { value: 1 },
                    right: Resource { value: 2 },
                };
                let left = parcel.left;
                let right = &parcel.right;
                observe(right);
                label @inner: i64 {
                    let scratch = Resource { value: 3 };
                    leave@outer(42)
                }
            }
        }
        main() -> { () }
    "#;
    for optimization_level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile_source_to_phases_with_options(
            "nested-leave-cleanup.gr",
            source,
            CompileOptions { optimization_level },
        )
        .unwrap_or_else(|errors| panic!("{optimization_level:?}: {errors:#?}"));
        assert!(
            phases.mir.functions.iter().any(|function| {
                function.flow.cleanup_plans.iter().any(|plan| {
                    matches!(plan.edge, CleanupEdge::Leave { .. })
                        && plan.actions.iter().any(|action| {
                            matches!(
                                action,
                                CleanupAction::DestroyResidual {
                                    initialized_fields,
                                    ..
                                } if initialized_fields == &[false, true]
                            )
                        })
                }) || {
                    let partial_owners = function
                        .blocks
                        .iter()
                        .flat_map(|block| &block.statements)
                        .filter_map(|statement| {
                            let grandiose::compiler_mir::InstructionKind::ProjectMove {
                                src, ..
                            } = &statement.kind
                            else {
                                return None;
                            };
                            Some(src.register)
                        })
                        .collect::<std::collections::BTreeSet<_>>();
                    function.blocks.iter().any(|block| {
                        let grandiose::compiler_mir::Terminator::Leave { .. } = &block.terminator
                        else {
                            return false;
                        };
                        block.statements.iter().any(|statement| {
                            matches!(
                                &statement.kind,
                                grandiose::compiler_mir::InstructionKind::Drop { owner: dropped }
                                    if partial_owners.contains(&dropped.register)
                            )
                        })
                    })
                }
            }),
            "{optimization_level:?}: nested leave lost exact cleanup\n{}",
            phases.mir.canonical_text()
        );
        let verified = verify(phases.artifact).unwrap();
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
