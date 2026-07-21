use grandiose::{
    OptimizationLevel,
    ast::{AssignmentPlaceKind, ExprKind, Stmt},
    compile_bundle_to_bytecode, compile_source_to_phases_with_options, lexer, parser,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{
    I64, Instruction, Primitive, Value, Vm,
    value::{ArenaObject, ArrayValue, ReferenceTarget},
    verify,
};

fn external_i64(value: i64) -> ArenaObject<ArrayValue> {
    ArenaObject::new(ArrayValue {
        element_type: I64,
        slots: vec![Some(Value::I64(value))],
        logical_capacity: 1,
    })
}

fn external_i64_reference(storage: &ArenaObject<ArrayValue>) -> Value {
    Value::Reference {
        referent_type: I64,
        unique: true,
        target: ReferenceTarget::ArrayElement {
            array: storage.clone(),
            index: 0,
        },
    }
}

fn external_i64_value(storage: &ArenaObject<ArrayValue>) -> Option<Value> {
    storage.borrow().slots[0].clone()
}

fn compile(source: &str, level: OptimizationLevel) -> Result<grandiose::CompiledPhases, String> {
    compile_source_to_phases_with_options(
        "assignment.gr",
        source,
        grandiose::CompileOptions {
            optimization_level: level,
        },
    )
    .map_err(|errors| {
        errors
            .into_iter()
            .map(|error| error.message)
            .collect::<Vec<_>>()
            .join("\n")
    })
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap() as u32
}

#[test]
fn parser_keeps_assignment_statement_only_and_preserves_static_places() {
    let program = parser::parse(
        lexer::lex(
            "update(local: i64, pointer: &mut i64) -> { local = 1; *pointer = 2; local } main() -> { () }",
        )
        .unwrap(),
    )
    .unwrap();
    let ExprKind::Block(statements) = &program.functions[0].body.kind else {
        panic!("function body must be a block")
    };
    assert!(matches!(
        &statements[0],
        Stmt::Assign {
            destination: grandiose::ast::AssignmentPlace {
                kind: AssignmentPlaceKind::Local { name, fields },
                ..
            },
            ..
        } if name.as_ref() == "local" && fields.is_empty()
    ));
    assert!(matches!(
        &statements[1],
        Stmt::Assign {
            destination: grandiose::ast::AssignmentPlace {
                kind: AssignmentPlaceKind::Dereference { fields, .. },
                ..
            },
            ..
        } if fields.is_empty()
    ));

    for bad in [
        "bad() -> { make() = 1; () } make() -> i64 { 0 } main() -> { () }",
        "bad() -> { let x = 0; x = 1 } main() -> { () }",
        "bad() -> { let x = 0; let y = 1; x = y = 2; () } main() -> { () }",
    ] {
        assert!(parser::parse(lexer::lex(bad).unwrap()).is_err(), "{bad}");
    }
}

#[test]
fn assignment_typechecks_at_o0_through_o3_for_local_field_and_unique_deref() {
    let source = r#"
        struct Pair { left: i64, right: i64 }
        struct Inner { number: i64 }
        struct Outer { inner: Inner }
        local(value: i64) -> i64 { value = 7; value }
        field(value: Pair) -> i64 { value.left = 8; value.left }
        nested(value: Outer) -> i64 { value.inner.number = 12; value.inner.number }
        indirect(value: &mut i64) -> i64 { *value = 9; *value }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(verified.clone())
                .run(function_id(&phases.artifact, "local"), vec![Value::I64(1)])
                .unwrap(),
            Value::I64(7)
        );
        let field_id = function_id(&phases.artifact, "field");
        let pair = phases.artifact.functions[field_id as usize].params[0];
        assert_eq!(
            Vm::new(verified.clone())
                .run(
                    field_id,
                    vec![Value::aggregate(pair, [Value::I64(1), Value::I64(2)])],
                )
                .unwrap(),
            Value::I64(8)
        );
        let nested_id = function_id(&phases.artifact, "nested");
        let outer = phases.artifact.functions[nested_id as usize].params[0];
        let inner = match phases.artifact.types[outer as usize].representation() {
            grandiose_vm::Type::Struct { fields, .. } => fields[0].ty,
            other => panic!("Outer is not a struct: {other:?}"),
        };
        assert_eq!(
            Vm::new(verified.clone())
                .run(
                    nested_id,
                    vec![Value::aggregate(
                        outer,
                        [Value::aggregate(inner, [Value::I64(4)])],
                    )],
                )
                .unwrap(),
            Value::I64(12)
        );
        let storage = external_i64(3);
        let reference = external_i64_reference(&storage);
        assert_eq!(
            Vm::new(verified)
                .run(function_id(&phases.artifact, "indirect"), vec![reference],)
                .unwrap(),
            Value::I64(9)
        );
        assert_eq!(external_i64_value(&storage), Some(Value::I64(9)));
    }
}

#[test]
fn rhs_trap_precedes_deref_move_destroy_and_store() {
    let source = r#"
        replace_for_trap_test(target: &mut i64, divisor: i64) -> i64 {
            *target = 10 / divisor;
            *target
        }
        main() -> { () }
    "#;
    let phases = compile(source, OptimizationLevel::O0).unwrap();
    let function =
        &phases.artifact.functions[function_id(&phases.artifact, "replace_for_trap_test") as usize];
    let code = &phases.artifact.code
        [function.code_start as usize..(function.code_start + function.code_len) as usize];
    let division = code
        .iter()
        .position(|instruction| {
            matches!(
                instruction,
                Instruction::Primitive {
                    op: Primitive::IntCheckedDiv,
                    ..
                }
            )
        })
        .unwrap();
    let move_old = code
        .iter()
        .position(|instruction| matches!(instruction, Instruction::DerefMove { .. }))
        .unwrap();
    let store = code
        .iter()
        .position(|instruction| matches!(instruction, Instruction::DerefStore { .. }))
        .unwrap();
    assert!(division < move_old && move_old < store, "{code:#?}");

    let storage = external_i64(41);
    let reference = external_i64_reference(&storage);
    let verified = verify(phases.artifact.clone()).unwrap();
    assert!(
        Vm::new(verified)
            .run(
                function_id(&phases.artifact, "replace_for_trap_test"),
                vec![reference, Value::I64(0)],
            )
            .is_err()
    );
    assert_eq!(external_i64_value(&storage), Some(Value::I64(41)));
}

#[test]
fn assignment_obeys_live_alias_conflicts_and_nll_release() {
    let conflict = r#"
        bad(owner: i64) -> i64 {
            let alias = &owner;
            owner = 2;
            *alias
        }
        main() -> { () }
    "#;
    let error = compile(conflict, OptimizationLevel::O0).unwrap_err();
    assert!(error.contains("live shared or unique loan"), "{error}");

    let released = r#"
        good(owner: i64) -> i64 {
            let alias = &owner;
            let observed = *alias;
            owner = 2;
            observed + owner
        }
        main() -> { () }
    "#;
    compile(released, OptimizationLevel::O0).unwrap();
}

#[test]
fn private_fields_cannot_be_assignment_destinations_across_segments() {
    let bundle = SourceBundle::new(
        Segment::new(
            "vault.glorious",
            "struct Vault { private secret: i64 } make() -> Vault { Vault { secret: 1 } }",
        ),
        Segment::new(
            "caller.glorious",
            "change(value: Vault) -> Vault { value.secret = 2; move value } main() -> { change(make()); () }",
        ),
        [],
    );
    let errors = compile_bundle_to_bytecode(&bundle).unwrap_err();
    assert!(
        errors.iter().any(|error| {
            error.message.contains("private field `secret`")
                && error.message.contains("defining source segment")
        }),
        "{errors:#?}"
    );
}

#[test]
fn initialized_must_move_values_cannot_be_destroyed_by_assignment() {
    let source = r#"
        struct Ticket {}
        impl Use<[1,1]> for Ticket {}
        bad(ticket: Ticket) -> Ticket { ticket = Ticket {}; move ticket }
        main() -> { () }
    "#;
    let error = compile(source, OptimizationLevel::O0).unwrap_err();
    assert!(
        error.contains("assignment would destroy an initialized subtree"),
        "{error}"
    );
    assert!(error.contains("[1,1]"), "{error}");
}

#[test]
fn whole_local_reinitialization_after_move_does_not_destroy_the_old_owner() {
    let source = r#"
        struct Ticket {}
        impl Use<[1,1]> for Ticket {}
        replace_local_ticket(ticket: Ticket, replacement: Ticket) -> (Ticket, Ticket) {
            let old = move ticket;
            ticket = move replacement;
            (move old, move ticket)
        }
        main() -> { () }
    "#;
    compile(source, OptimizationLevel::O0).unwrap();
}

#[test]
fn exact_moved_field_can_be_reinitialized_without_destroying_it_again() {
    let source = r#"
        struct Ticket {}
        impl Use<[1,infinity]> for Ticket {}
        struct TicketSlot { ticket: Ticket, marker: i64 }
        replace_slot_field(slot: TicketSlot, replacement: Ticket) -> (Ticket, TicketSlot) {
            let old = move slot.ticket;
            slot.ticket = move replacement;
            (move old, move slot)
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap();
        let text = phases.core.canonical_text();
        assert!(text.contains("assign"), "{text}");
        assert!(text.contains("destroy-old=false"), "{text}");
    }
}

#[test]
fn nested_moved_leaf_rebuilds_every_parent_at_o0_through_o3() {
    let source = r#"
        struct Inner { left: i64, right: i64 }
        struct Outer { inner: Inner, marker: i64 }
        rebuild(value: Outer, replacement: i64) -> i64 {
            let old = move value.inner.left;
            value.inner.left = move replacement;
            old + value.inner.left + value.inner.right + value.marker
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let function = function_id(&phases.artifact, "rebuild");
        let outer = phases.artifact.functions[function as usize].params[0];
        let inner = match phases.artifact.types[outer as usize].representation() {
            grandiose_vm::Type::Struct { fields, .. } => fields[0].ty,
            other => panic!("Outer is not a struct: {other:?}"),
        };
        let result = Vm::new(verified)
            .run(
                function,
                vec![
                    Value::aggregate(
                        outer,
                        [
                            Value::aggregate(inner, [Value::I64(2), Value::I64(3)]),
                            Value::I64(5),
                        ],
                    ),
                    Value::I64(7),
                ],
            )
            .unwrap();
        assert_eq!(result, Value::I64(17), "{level:?}");
    }
}

#[test]
fn assigning_children_below_moved_parent_reconstructs_parent_at_o0_through_o3() {
    let source = r#"
        struct Inner { left: i64, right: i64 }
        struct Outer { inner: Inner, marker: i64 }
        rebuild(value: Outer, left: i64, right: i64) -> i64 {
            let old = move value.inner;
            value.inner.left = move left;
            value.inner.right = move right;
            old.left + old.right + value.inner.left + value.inner.right + value.marker
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let function = function_id(&phases.artifact, "rebuild");
        let outer = phases.artifact.functions[function as usize].params[0];
        let inner = match phases.artifact.types[outer as usize].representation() {
            grandiose_vm::Type::Struct { fields, .. } => fields[0].ty,
            other => panic!("Outer is not a struct: {other:?}"),
        };
        let result = Vm::new(verified)
            .run(
                function,
                vec![
                    Value::aggregate(
                        outer,
                        [
                            Value::aggregate(inner, [Value::I64(2), Value::I64(3)]),
                            Value::I64(5),
                        ],
                    ),
                    Value::I64(7),
                    Value::I64(11),
                ],
            )
            .unwrap();
        assert_eq!(result, Value::I64(28), "{level:?}");
    }
}

#[test]
fn assigning_all_leaves_after_whole_owner_move_reconstructs_root_at_o0_through_o3() {
    let source = r#"
        struct Inner { left: i64, right: i64 }
        struct Outer { inner: Inner, marker: i64 }
        rebuild(value: Outer, left: i64, right: i64, marker: i64) -> i64 {
            let old = move value;
            value.inner.left = move left;
            value.inner.right = move right;
            value.marker = move marker;
            old.inner.left + value.inner.left + value.inner.right + value.marker
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let function = function_id(&phases.artifact, "rebuild");
        let outer = phases.artifact.functions[function as usize].params[0];
        let inner = match phases.artifact.types[outer as usize].representation() {
            grandiose_vm::Type::Struct { fields, .. } => fields[0].ty,
            other => panic!("Outer is not a struct: {other:?}"),
        };
        let result = Vm::new(verified)
            .run(
                function,
                vec![
                    Value::aggregate(
                        outer,
                        [
                            Value::aggregate(inner, [Value::I64(2), Value::I64(3)]),
                            Value::I64(5),
                        ],
                    ),
                    Value::I64(7),
                    Value::I64(11),
                    Value::I64(13),
                ],
            )
            .unwrap();
        assert_eq!(result, Value::I64(33), "{level:?}");
    }
}

#[test]
fn nested_projection_moves_preserve_double_move_and_custom_drop_rejections() {
    let double_move = r#"
        struct Inner { value: i64, marker: i64 }
        struct Outer { inner: Inner }
        bad(value: Outer) -> i64 {
            let first = move value.inner.value;
            first + move value.inner.value
        }
        main() -> { () }
    "#;
    let error = compile(double_move, OptimizationLevel::O0).unwrap_err();
    assert!(error.contains("already moved"), "{error}");

    let custom_drop = r#"
        struct Inner { value: i64, marker: i64 }
        impl Drop for Inner { drop(&mut self) -> { self.marker; () } }
        struct Outer { inner: Inner }
        bad(value: Outer) -> i64 { move value.inner.value }
        main() -> { () }
    "#;
    let error = compile(custom_drop, OptimizationLevel::O0).unwrap_err();
    assert!(error.contains("custom Drop hook"), "{error}");
}

#[test]
fn proven_enum_payload_assignment_replaces_and_reinitializes_at_all_levels() {
    let source = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        enum Choice { Some(Resource), None }
        update_choice(choice: Choice) -> i64 {
            if(choice is Choice::Some(_)) {
                choice.0 = Resource { marker: 42 };
                42
            } else {
                0
            }
        }
        selected() -> i64 { update_choice(Choice::Some(Resource { marker: 1 })) }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        assert_eq!(
            Vm::new(verified)
                .run(function_id(&phases.artifact, "selected"), vec![])
                .unwrap(),
            Value::I64(42),
            "{level:?}"
        );
    }
}

#[test]
fn enum_payload_assignment_requires_a_variant_proof_and_safe_replacement() {
    let unproved = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        enum Choice { Some(Resource), None }
        bad(value: Choice) -> () {
            value.0 = Resource { marker: 1 };
            ()
        }
        main() -> { () }
    "#;
    let error = compile(unproved, OptimizationLevel::O0).unwrap_err();
    assert!(error.contains("variant proof"), "{error}");

    let positive = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        enum Choice { Some(Ticket), None }
        bad(value: Choice, replacement: Ticket) -> () {
            if(value is Choice::Some(_)) {
                value.0 = move replacement;
                ()
            } else {
                ()
            }
        }
        main() -> { () }
    "#;
    let error = compile(positive, OptimizationLevel::O0).unwrap_err();
    assert!(
        error.contains("assignment would destroy an initialized subtree"),
        "{error}"
    );

    let custom_drop = r#"
        struct Resource { marker: i64 }
        impl Use<[0,1]> for Resource {}
        enum Choice { Some(Resource), None }
        impl Drop for Choice { drop(&mut self) -> { () } }
        bad(value: Choice) -> () {
            if(value is Choice::Some(_)) {
                value.0 = Resource { marker: 1 };
                ()
            } else {
                ()
            }
        }
        main() -> { () }
    "#;
    let error = compile(custom_drop, OptimizationLevel::O0).unwrap_err();
    assert!(error.contains("custom Drop hook"), "{error}");
}

#[test]
fn nested_restoration_transfers_exact_use_obligations_to_old_and_replacement() {
    let source = r#"
        struct Ticket { serial: i64 }
        impl Use<[1,1]> for Ticket {}
        struct Inner { ticket: Ticket, marker: i64 }
        struct Outer { inner: Inner }
        restore_ticket(value: Outer, replacement: Ticket) -> (Ticket, Outer) {
            let old = move value.inner.ticket;
            value.inner.ticket = move replacement;
            (move old, move value)
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
    }

    let whole_owner = r#"
        struct Owner { left: i64, right: i64 }
        impl Use<[1,1]> for Owner {}
        restore_owner(value: Owner, left: i64, right: i64) -> (Owner, Owner) {
            let old = move value;
            value.left = move left;
            value.right = move right;
            (move old, move value)
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        compile(whole_owner, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
    }
}

#[test]
fn assignment_rejects_shared_deref_unknown_places_and_type_mismatch() {
    let cases = [
        (
            "bad(value: &i64) -> { *value = 1; () } main() -> { () }",
            "unique reference",
        ),
        (
            "bad() -> { missing = 1; () } main() -> { () }",
            "not an addressable local",
        ),
        (
            "bad(value: i64) -> { value = \"text\"; () } main() -> { () }",
            "expected i64, found Text",
        ),
    ];
    for (source, expected) in cases {
        let error = compile(source, OptimizationLevel::O0).unwrap_err();
        assert!(
            error.contains(expected),
            "expected {expected:?} in {error:?}"
        );
    }
}

#[test]
fn move_through_unique_reference_reinitializes_at_o0_through_o3() {
    let source = r#"
        replace_i64(target: &mut i64, incoming: i64) -> i64 {
            replace(target, move incoming)
        }
        swap_i64(left: &mut i64, right: &mut i64) -> () {
            swap(left, right)
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        let verified = verify(phases.artifact.clone()).unwrap();
        let storage = external_i64(3);
        let reference = external_i64_reference(&storage);
        assert_eq!(
            Vm::new(verified.clone())
                .run(
                    function_id(&phases.artifact, "replace_i64"),
                    vec![reference, Value::I64(9)],
                )
                .unwrap(),
            Value::I64(3)
        );
        assert_eq!(external_i64_value(&storage), Some(Value::I64(9)));

        let left = external_i64(4);
        let right = external_i64(7);
        Vm::new(verified)
            .run(
                function_id(&phases.artifact, "swap_i64"),
                vec![
                    external_i64_reference(&left),
                    external_i64_reference(&right),
                ],
            )
            .unwrap();
        assert_eq!(external_i64_value(&left), Some(Value::I64(7)));
        assert_eq!(external_i64_value(&right), Some(Value::I64(4)));
        assert!(phases.core.canonical_text().contains("deref-move"));
        assert!(phases.core.canonical_text().contains("destroy-old=false"));
    }
}

#[test]
fn move_through_unique_reference_preserves_exact_linear_values() {
    let source = r#"
        struct Ticket { id: i64 }
        impl Use<[1,1]> for Ticket {}
        replace_ticket(target: &mut Ticket, incoming: Ticket) -> Ticket {
            replace(target, move incoming)
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        verify(phases.artifact).unwrap();
    }
}

#[test]
fn empty_unique_referents_reject_access_transfer_and_normal_exit() {
    let cases = [
        (
            "bad(target: &mut i64) -> i64 { let old = move *target; move *target } main() -> { () }",
            "already moved",
        ),
        (
            "bad(target: &mut i64) -> i64 { let old = move *target; *target } main() -> { () }",
            "uninitialized after `move *`",
        ),
        (
            "sink(value: &mut i64) -> { () } bad(target: &mut i64) -> i64 { let old = move *target; sink(target); old } main() -> { () }",
            "cannot be used, transferred, called, or dropped",
        ),
        (
            "bad(target: &mut i64) -> { let old = move *target; () } main() -> { () }",
            "uninitialized on a normal exit",
        ),
        (
            "bad(target: &i64) -> i64 { move *target } main() -> { () }",
            "requires a unique reference",
        ),
    ];
    for (source, expected) in cases {
        let error = compile(source, OptimizationLevel::O0).unwrap_err();
        assert!(
            error.contains(expected),
            "expected {expected:?} in {error:?}"
        );
    }
}

#[test]
fn pure_unrelated_call_is_allowed_while_unique_referent_is_empty() {
    let source = r#"
        unrelated() -> { () }
        good(target: &mut i64, incoming: i64) -> i64 {
            let previous = move *target;
            unrelated();
            *target = move incoming;
            previous
        }
        main() -> { () }
    "#;
    compile(source, OptimizationLevel::O0).unwrap();
}

#[test]
fn projected_assignment_in_handler_preserves_named_unique_root_at_join() {
    let source = r#"
        struct Cell { value: i64 }
        effect Branch { inspect(value: Bool) -> !; }
        update(cell: &mut Cell) -> i64 {
            handle perform Branch::inspect(true) {
                Branch::inspect(Result::Ok(_)) => {
                    (*cell).value = 9;
                    (*cell).value
                },
                Branch::inspect(Result::Err(_)) => (*cell).value
            }
        }
        main() -> { () }
    "#;
    for level in [
        OptimizationLevel::O0,
        OptimizationLevel::O1,
        OptimizationLevel::O2,
        OptimizationLevel::O3,
    ] {
        let phases = compile(source, level).unwrap_or_else(|error| panic!("{level:?}: {error}"));
        verify(phases.artifact).unwrap();
    }
}
