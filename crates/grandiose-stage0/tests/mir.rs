use std::collections::{BTreeMap, BTreeSet};

use grandiose_stage0::{
    CallableId, CaptureMode, ConstKind, CoreId, DefKey, Digest, EffectInstance, EffectRow,
    EffectRowProjection, EnvironmentBrand, GenericArgument, GenericKind, InferVar, InstanceKey,
    Lifetime, LoanFact, MirBlock, MirBlockId, MirCapture, MirCaptureEnvironment, MirCleanupPlan,
    MirContinuationPolicy, MirEditor, MirFunction, MirInstance, MirInstruction, MirLocal,
    MirLocalDecl, MirPattern, MirPatternField, MirProgram, MirTerminator, MoveFact, Mutability,
    Quantity, ScalarType, Type, VmArtifactError, emit_vm, emit_vm_program, optimize_mir, verify_vm,
};

fn local(ty: Type) -> MirLocalDecl {
    MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    }
}

#[test]
fn mir_rejects_a_forged_nonfinite_replay_budget() {
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-replay-budget")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(Type::Scalar(ScalarType::I64))],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::InstallHandler {
                    effect: DefKey(Digest::of_bytes(b"forged-mir-replay-effect")),
                    effect_arguments: vec![],
                    operation: 0,
                    payload_destinations: vec![],
                    resume_type: Type::Scalar(ScalarType::I64),
                    continuation: MirContinuationPolicy::Replay { uses: 1 },
                    target: MirBlockId(1),
                }],
                terminator: MirTerminator::Unreachable,
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            },
        ],
    };
    assert!(function.validate().is_err());
}

#[test]
fn mir_rejects_one_label_brand_with_contradictory_destinations() {
    let owner = DefKey(Digest::of_bytes(b"forged-mir-label-contract-owner"));
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-label-contract")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::Bool)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
        ],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(0),
                    value: true,
                }],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![],
                    else_target: MirBlockId(2),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(1),
                    value: 1,
                }],
                terminator: MirTerminator::Leave {
                    brand: grandiose_stage0::LabelBrand { owner, label: 0 },
                    target: MirBlockId(3),
                    arguments: vec![MirLocal(1)],
                    cleanup: MirCleanupPlan {
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(2),
                    value: 2,
                }],
                terminator: MirTerminator::Leave {
                    brand: grandiose_stage0::LabelBrand { owner, label: 0 },
                    target: MirBlockId(4),
                    arguments: vec![MirLocal(2)],
                    cleanup: MirCleanupPlan {
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
            MirBlock {
                parameters: vec![MirLocal(2)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(2) },
            },
        ],
    };
    assert!(
        function
            .validate()
            .expect_err("one label brand cannot authorize two destinations")
            .contains("contradictory destination or payload layout")
    );
}

#[test]
fn mir_rejects_a_forged_payload_distinct_nan_constant() {
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-nan-payload")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(Type::Scalar(ScalarType::F64))],
        result: Type::Scalar(ScalarType::F64),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::ConstF64 {
                dst: MirLocal(0),
                bits: 0x7ff8_0000_0000_0001,
            }],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("non-canonical NaN payload"))
    );
}

#[test]
fn mir_rejects_a_literal_pattern_that_violates_the_lossless_lexer_contract() {
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-malformed-text-pattern")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::Text)),
            local(Type::Scalar(ScalarType::Bool)),
        ],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::ConstText {
                    dst: MirLocal(0),
                    value: "A".into(),
                },
                MirInstruction::PatternTest {
                    dst: MirLocal(1),
                    subject: MirLocal(0),
                    pattern: MirPattern::Literal(r#""\u{41"#.into()),
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("literal pattern"))
    );
}

#[test]
fn mir_rejects_overlapping_or_live_loan_cleanup_paths() {
    let leave = |cleanup| MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-cleanup")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(Type::Scalar(ScalarType::I64))],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Leave {
                    brand: grandiose_stage0::LabelBrand {
                        owner: DefKey(Digest::of_bytes(b"forged-mir-cleanup-owner")),
                        label: 0,
                    },
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(0)],
                    cleanup,
                },
            },
            MirBlock {
                parameters: vec![MirLocal(0)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(0) },
            },
        ],
    };
    let overlapping_moves = MirCleanupPlan {
        moved_places: vec![
            MoveFact {
                root: "pair".into(),
                fields: vec![],
            },
            MoveFact {
                root: "pair".into(),
                fields: vec![0],
            },
        ],
        active_loans: vec![],
    };
    assert!(
        leave(overlapping_moves)
            .validate()
            .is_err_and(|error| error.contains("overlapping moved places"))
    );

    let moved_live_loan = MirCleanupPlan {
        moved_places: vec![MoveFact {
            root: "pair".into(),
            fields: vec![0],
        }],
        active_loans: vec![LoanFact {
            owner: Some("loan".into()),
            root: "pair".into(),
            fields: vec![],
            unique: false,
        }],
    };
    assert!(
        leave(moved_live_loan)
            .validate()
            .is_err_and(|error| error.contains("live loan"))
    );
}

fn graph() -> MirFunction {
    MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-cfg")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::Bool)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
        ],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![MirLocal(1)],
                    else_target: MirBlockId(2),
                    else_arguments: vec![MirLocal(2)],
                },
            },
            MirBlock {
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
            MirBlock {
                parameters: vec![MirLocal(4)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(4) },
            },
        ],
    }
}

#[test]
fn cfg_validation_checks_typed_block_edges_and_returns() {
    assert!(graph().validate().is_ok());
    let mut invalid = graph();
    let MirTerminator::SwitchBool { then_arguments, .. } = &mut invalid.blocks[0].terminator else {
        panic!("fixture entry must be a switch")
    };
    *then_arguments = vec![MirLocal(0)];
    assert!(invalid.validate().is_err());
}

#[test]
fn mir_validation_rejects_unresolved_associated_const_projection_identity() {
    let nominal = Type::Nominal {
        definition: DefKey(Digest::of_bytes(b"mir-associated-const-carrier")),
        arguments: vec![GenericArgument::ConstProjection {
            subject: Box::new(Type::Generic(0)),
            trait_definition: DefKey(Digest::of_bytes(b"mir-associated-const-trait")),
            trait_arguments: vec![],
            name: "Width".into(),
            kind: ConstKind::U32,
        }],
    };
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-associated-const-function")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(nominal.clone())],
        result: nominal,
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    assert!(function.validate().is_err_and(|error| {
        error.contains("unresolved associated structural-constant projection")
    }));
}

#[test]
fn mir_validation_rejects_nominal_pattern_fields_outside_frozen_arity() {
    let definition = DefKey(Digest::of_bytes(b"mir-pattern-arity"));
    let nominal = Type::Nominal {
        definition,
        arguments: vec![],
    };
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-pattern-arity-function")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(nominal), local(Type::Scalar(ScalarType::Bool))],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::PatternTest {
                dst: MirLocal(1),
                subject: MirLocal(0),
                pattern: MirPattern::Record {
                    definition,
                    field_types: vec![Type::Scalar(ScalarType::I64)],
                    field_count: 1,
                    fields: vec![MirPatternField {
                        index: 1,
                        ty: Type::Scalar(ScalarType::I64),
                        pattern: MirPattern::Any,
                    }],
                },
            }],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };

    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("outside its structural arity")),
        "forged nominal field projections must not become executable MIR"
    );
}

#[test]
fn mir_validation_rejects_nominal_pattern_field_type_forgery() {
    let definition = DefKey(Digest::of_bytes(b"mir-pattern-layout"));
    let nominal = Type::Nominal {
        definition,
        arguments: vec![],
    };
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-pattern-layout-function")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(nominal), local(Type::Scalar(ScalarType::Bool))],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::PatternTest {
                dst: MirLocal(1),
                subject: MirLocal(0),
                pattern: MirPattern::Record {
                    definition,
                    field_types: vec![Type::Scalar(ScalarType::I64)],
                    field_count: 1,
                    fields: vec![MirPatternField {
                        index: 0,
                        ty: Type::Scalar(ScalarType::Bool),
                        pattern: MirPattern::Any,
                    }],
                },
            }],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };

    let validation = function.validate();
    assert!(
        validation
            .as_ref()
            .is_err_and(|error| error.contains("disagrees with its frozen layout")),
        "validation result: {validation:?}; MIR must reject an in-range field with forged type metadata"
    );
}

#[test]
fn mir_validation_rejects_forged_reborrow_capability_and_referent() {
    let i64 = Type::Scalar(ScalarType::I64);
    let shared_i64 = Type::Reference {
        mutability: Mutability::Shared,
        lifetime: Lifetime::Elided,
        referent: Box::new(i64.clone()),
    };
    let unique_i64 = Type::Reference {
        mutability: Mutability::Unique,
        lifetime: Lifetime::Elided,
        referent: Box::new(i64.clone()),
    };
    let forged_capability = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-shared-to-unique-reborrow")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(i64.clone()), local(shared_i64), local(unique_i64)],
        result: i64.clone(),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 1,
                },
                MirInstruction::Borrow {
                    dst: MirLocal(1),
                    src: MirLocal(0),
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
                MirInstruction::Borrow {
                    dst: MirLocal(2),
                    src: MirLocal(1),
                    fields: vec![],
                    unique: true,
                    reborrow: true,
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    assert!(
        forged_capability
            .validate()
            .is_err_and(|error| error.contains("shared parent")),
        "forged shared-to-unique reborrow reached executable MIR"
    );

    let forged_referent = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-whole-borrow-referent")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64.clone()),
            local(Type::Reference {
                mutability: Mutability::Shared,
                lifetime: Lifetime::Elided,
                referent: Box::new(Type::Scalar(ScalarType::Text)),
            }),
        ],
        result: i64.clone(),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 1,
                },
                MirInstruction::Borrow {
                    dst: MirLocal(1),
                    src: MirLocal(0),
                    fields: vec![],
                    unique: false,
                    reborrow: false,
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    assert!(
        forged_referent
            .validate()
            .is_err_and(|error| error.contains("referent does not match")),
        "forged whole-place borrow changed its referent type"
    );
}

#[test]
fn mir_validation_rejects_forged_array_pattern_and_projection_element_types() {
    let array = Type::Array(Box::new(Type::Scalar(ScalarType::I64)));
    let pattern = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-array-pattern-forgery")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(array.clone()), local(Type::Scalar(ScalarType::Bool))],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::PatternTest {
                dst: MirLocal(1),
                subject: MirLocal(0),
                pattern: MirPattern::Array {
                    element: Type::Scalar(ScalarType::Bool),
                    elements: vec![MirPattern::Any],
                },
            }],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };
    assert!(
        pattern
            .validate()
            .is_err_and(|error| error.contains("array pattern has an incompatible subject type"))
    );

    let projection = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-array-projection-forgery")),
        captures: 0,
        parameters: vec![],
        locals: vec![local(array), local(Type::Scalar(ScalarType::Bool))],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![MirInstruction::ProjectArray {
                dst: MirLocal(1),
                base: MirLocal(0),
                index: 0,
                field_count: 1,
                element_type: Type::Scalar(ScalarType::Bool),
            }],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };
    assert!(projection.validate().is_err_and(|error| {
        error.contains("array projection has inconsistent structural metadata")
    }));
}

#[test]
fn emitted_mir_cannot_resume_past_an_active_nested_handler_frame() {
    let outer = DefKey(Digest::of_bytes(b"forged-mir-nested-outer"));
    let inner = DefKey(Digest::of_bytes(b"forged-mir-nested-inner"));
    let forged = MirFunction {
        definition: DefKey(Digest::of_bytes(b"forged-mir-nested-resume")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Scalar(ScalarType::I64)),
        ],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![
                    MirInstruction::InstallHandler {
                        effect: outer,
                        effect_arguments: vec![],
                        operation: 0,
                        payload_destinations: vec![],
                        resume_type: Type::Scalar(ScalarType::I64),
                        continuation: MirContinuationPolicy::Consume,
                        target: MirBlockId(1),
                    },
                    MirInstruction::Perform {
                        dst: MirLocal(0),
                        effect: outer,
                        effect_arguments: vec![],
                        operation: 0,
                        arguments: vec![],
                    },
                    MirInstruction::UninstallHandler,
                ],
                terminator: MirTerminator::Return { value: MirLocal(0) },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![
                    MirInstruction::InstallHandler {
                        effect: inner,
                        effect_arguments: vec![],
                        operation: 0,
                        payload_destinations: vec![],
                        resume_type: Type::Scalar(ScalarType::I64),
                        continuation: MirContinuationPolicy::Consume,
                        target: MirBlockId(2),
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 41,
                    },
                    // The topmost frame is the unsuspended inner frame, so
                    // this forged outer-resume edge has no valid target.
                    MirInstruction::Resume { value: MirLocal(1) },
                ],
                terminator: MirTerminator::Unreachable,
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Unreachable,
            },
        ],
    };
    let artifact = emit_vm(&forged).expect("well-formed structural MIR emits");
    assert!(matches!(
        verify_vm(artifact),
        Err(VmArtifactError::HandlerResumeUnavailable)
    ));
}

#[test]
fn mir_validation_rejects_nested_unresolved_type_metadata_and_unscoped_lifetimes() {
    let mut nested_local = graph();
    nested_local.locals[1].ty = Type::Array(Box::new(Type::Tuple(vec![Type::Infer(InferVar(9))])));
    assert!(
        nested_local
            .validate()
            .is_err_and(|error| error.contains("unresolved inference")),
        "nested local inference must not become executable MIR"
    );

    let mut unscoped_lifetime = graph();
    unscoped_lifetime.locals[1].ty = Type::Reference {
        mutability: grandiose_stage0::Mutability::Shared,
        lifetime: Lifetime::Bound { depth: 0, index: 0 },
        referent: Box::new(Type::Scalar(ScalarType::I64)),
    };
    assert!(
        unscoped_lifetime
            .validate()
            .is_err_and(|error| error.contains("absent higher-ranked binder")),
        "a bound lifetime outside a callable binder must be rejected"
    );

    let mut gat_item_argument = graph();
    gat_item_argument.locals[1].ty = Type::Projection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"mir-forged-gat-trait")),
        trait_arguments: vec![],
        name: "Output".into(),
        item_generic_kinds: vec![grandiose_stage0::GenericKind::Type],
        item_arguments: vec![GenericArgument::Type(Type::Reference {
            mutability: grandiose_stage0::Mutability::Shared,
            lifetime: Lifetime::Bound { depth: 0, index: 0 },
            referent: Box::new(Type::Scalar(ScalarType::I64)),
        })],
    };
    assert!(
        gat_item_argument
            .validate()
            .is_err_and(|error| error.contains("absent higher-ranked binder")),
        "a forged GAT item argument must not smuggle an unscoped bound lifetime into MIR"
    );

    let mut wrong_gat_kind = graph();
    wrong_gat_kind.locals[1].ty = Type::Projection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"mir-forged-gat-kind")),
        trait_arguments: vec![],
        name: "Output".into(),
        item_generic_kinds: vec![grandiose_stage0::GenericKind::Const(
            grandiose_stage0::ConstKind::U32,
        )],
        item_arguments: vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    };
    assert!(
        wrong_gat_kind
            .validate()
            .is_err_and(|error| error.contains("invalid item generic arguments")),
        "MIR must reject a forged associated-item argument whose identity kind disagrees with its declaration"
    );

    let mut scoped_hrtb_gat = graph();
    let scoped_hrtb_gat_type = Type::Callable {
        lifetime_binders: 1,
        parameters: vec![],
        result: Box::new(Type::Projection {
            subject: Box::new(Type::Scalar(ScalarType::I64)),
            trait_definition: DefKey(Digest::of_bytes(b"mir-hrtb-gat-row")),
            trait_arguments: vec![],
            name: "Output".into(),
            item_generic_kinds: vec![
                grandiose_stage0::GenericKind::Lifetime,
                grandiose_stage0::GenericKind::EffectRow,
            ],
            item_arguments: vec![
                GenericArgument::Lifetime(Lifetime::Bound { depth: 0, index: 0 }),
                GenericArgument::EffectRow(EffectRow {
                    effects: BTreeSet::new(),
                    projections: vec![],
                    tail: Some(grandiose_stage0::EffectTail::Generic(5)),
                }),
            ],
        }),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    };
    for local in &mut scoped_hrtb_gat.locals[1..] {
        local.ty = scoped_hrtb_gat_type.clone();
    }
    scoped_hrtb_gat.result = scoped_hrtb_gat_type;
    assert!(
        scoped_hrtb_gat.validate().is_ok(),
        "MIR must retain scoped HRTB lifetimes and open effect rows in GAT arguments: {:#?}",
        scoped_hrtb_gat.validate()
    );

    let mut generic_metadata = graph();
    generic_metadata.blocks[0]
        .instructions
        .push(MirInstruction::Call {
            dst: MirLocal(1),
            callee: DefKey(Digest::of_bytes(b"generic-target")),
            generic_arguments: vec![GenericArgument::Type(Type::Nominal {
                definition: DefKey(Digest::of_bytes(b"nested-generic")),
                arguments: vec![GenericArgument::Type(Type::Infer(InferVar(4)))],
            })],
            trait_instance: None,
            arguments: vec![],
        });
    let entry = generic_metadata.definition;
    let program = MirProgram {
        entry,
        functions: BTreeMap::from([(entry, generic_metadata)]),
        instances: BTreeMap::new(),
    };
    assert!(
        program
            .validate()
            .is_err_and(|error| error.contains("unresolved inference")),
        "nested generic call metadata must not bypass MIR program validation"
    );

    let mut escaped_effect_lifetime = graph();
    escaped_effect_lifetime.blocks[0]
        .instructions
        .push(MirInstruction::Perform {
            dst: MirLocal(1),
            effect: DefKey(Digest::of_bytes(b"mir-escaped-hrtb-effect")),
            effect_arguments: vec![GenericArgument::Lifetime(Lifetime::Bound {
                depth: 0,
                index: 0,
            })],
            operation: 0,
            arguments: vec![],
        });
    assert!(
        escaped_effect_lifetime
            .validate()
            .is_err_and(|error| error.contains("absent higher-ranked binder")),
        "MIR effect metadata must reject an HRTB placeholder before VM erases binder scopes"
    );
}

#[test]
fn mir_program_rejects_forged_instance_identity_before_vm_emission() {
    let key = InstanceKey::new(
        DefKey(Digest::of_bytes(b"forged-instance-template")),
        &[GenericKind::Type],
        vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))],
    )
    .expect("closed instance key");
    let executable = DefKey(Digest::of_bytes(b"retargeted-instance-body"));
    let mut function = graph();
    function.definition = executable;
    let forged = MirProgram {
        entry: executable,
        functions: BTreeMap::from([(executable, function)]),
        instances: BTreeMap::from([(executable, MirInstance { key, executable })]),
    };
    assert!(
        forged
            .validate()
            .is_err_and(|error| error.contains("canonical substitution identity")),
        "forged instance metadata must not reach VM emission"
    );
}

#[test]
fn mir_program_accepts_a_canonical_zero_generic_instance_at_vm_boundary() {
    let key = InstanceKey::new(
        DefKey(Digest::of_bytes(b"zero-generic-instance-template")),
        &[],
        vec![],
    )
    .expect("zero-generic instance key is canonical");
    let executable = DefKey(key.fingerprint());
    let mut function = graph();
    function.definition = executable;
    let program = MirProgram {
        entry: executable,
        functions: BTreeMap::from([(executable, function)]),
        instances: BTreeMap::from([(executable, MirInstance { key, executable })]),
    };
    assert!(program.validate().is_ok(), "{:#?}", program.validate());
    assert!(
        emit_vm_program(&program).is_ok(),
        "a canonical zero-generic instance must be able to reach VM emission"
    );
}

#[test]
fn mir_validation_rejects_noncanonical_nested_effect_row_identity() {
    let projection = |name: &str| EffectRowProjection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"mir-canonical-row-trait")),
        trait_arguments: vec![],
        name: name.into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    let mut function = graph();
    function.locals[1].ty = Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: EffectRow {
            effects: BTreeSet::new(),
            projections: vec![projection("Z"), projection("A")],
            tail: None,
        },
        invocation: Quantity::ONCE,
    };
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("non-canonical identity")),
        "forged MIR must not bypass the canonical type-identity boundary"
    );
}

#[test]
fn mir_validation_rejects_inference_in_enclosing_mixed_trait_heads() {
    let mut function = graph();
    function.locals[1].ty = Type::Projection {
        subject: Box::new(Type::Scalar(ScalarType::I64)),
        trait_definition: DefKey(Digest::of_bytes(b"mir-mixed-trait-head")),
        trait_arguments: vec![GenericArgument::EffectRow(EffectRow::closed_instances([
            EffectInstance {
                definition: DefKey(Digest::of_bytes(b"mir-mixed-trait-head-effect")),
                arguments: vec![GenericArgument::Type(Type::Infer(InferVar(91)))],
            },
        ]))],
        name: "Output".into(),
        item_generic_kinds: vec![],
        item_arguments: vec![],
    };
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("unresolved inference")),
        "MIR must walk enclosing trait arguments instead of treating them as a type-only shell"
    );
}

#[test]
fn mir_validation_rejects_inference_nested_in_callable_effect_arguments() {
    let mut function = graph();
    function.locals.push(local(Type::Callable {
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: EffectRow::closed_instances([EffectInstance {
            definition: DefKey(Digest::of_bytes(b"mir-hidden-inference-effect")),
            arguments: vec![GenericArgument::Type(Type::Infer(InferVar(23)))],
        }]),
        invocation: Quantity::ONCE,
    }));
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("unresolved inference")),
        "MIR must reject inference hidden inside callable effect metadata"
    );
}

#[test]
fn mir_validation_preserves_never_and_rejects_nested_recovery_types() {
    let mut function = graph();
    function
        .locals
        .push(local(Type::Array(Box::new(Type::Never))));
    assert!(
        function.validate().is_ok(),
        "MIR must preserve the VM's zero-sized bottom representation"
    );

    function.locals.pop();
    function
        .locals
        .push(local(Type::Array(Box::new(Type::Error))));
    assert!(
        function
            .validate()
            .is_err_and(|error| error.contains("recovered error poison")),
        "MIR must not provide a VM layout for recovered error poison"
    );
}

#[test]
fn checked_mir_editor_rolls_back_an_invalid_cfg_edit() {
    let function = graph();
    let mut editor = MirEditor::open(function.clone()).unwrap();
    assert!(
        editor
            .replace_terminator(
                MirBlockId(0),
                MirTerminator::Goto {
                    target: MirBlockId(99),
                    arguments: vec![],
                },
            )
            .is_err()
    );
    assert_eq!(editor.finish(), function);
}

#[test]
fn optimizer_folds_checked_scalar_constants_and_eliminates_known_branches() {
    let mut function = graph();
    function.blocks[0].instructions = vec![MirInstruction::ConstBool {
        dst: MirLocal(0),
        value: true,
    }];
    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.eliminated_branches, 1);
    assert!(matches!(
        optimized.blocks[0].terminator,
        MirTerminator::Goto {
            target: MirBlockId(1),
            ..
        }
    ));

    let i64_ty = Type::Scalar(ScalarType::I64);
    let arithmetic = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-optimizer")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 40,
                },
                MirInstruction::ConstI64 {
                    dst: MirLocal(1),
                    value: 2,
                },
                MirInstruction::AddI64 {
                    dst: MirLocal(2),
                    left: MirLocal(0),
                    right: MirLocal(1),
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(2) },
        }],
    };
    let (optimized, report) = optimize_mir(arithmetic).unwrap();
    assert_eq!(report.constant_folds, 1);
    assert!(matches!(
        optimized.blocks[0].instructions[2],
        MirInstruction::ConstI64 { value: 42, .. }
    ));
}

#[test]
fn optimizer_folds_reflexive_integer_and_boolean_comparisons_without_constants() {
    let bool_ty = Type::Scalar(ScalarType::Bool);
    let i64_ty = Type::Scalar(ScalarType::I64);
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-reflexive-comparisons")),
        captures: 0,
        parameters: vec![MirLocal(0), MirLocal(1)],
        locals: vec![
            local(i64_ty),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty),
        ],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::LtI64 {
                    dst: MirLocal(2),
                    left: MirLocal(0),
                    right: MirLocal(0),
                },
                MirInstruction::EqBool {
                    dst: MirLocal(3),
                    left: MirLocal(1),
                    right: MirLocal(1),
                },
                MirInstruction::NeBool {
                    dst: MirLocal(4),
                    left: MirLocal(1),
                    right: MirLocal(1),
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(3) },
        }],
    };

    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.constant_folds, 3);
    assert!(matches!(
        optimized.blocks[0].instructions.as_slice(),
        [
            MirInstruction::ConstBool { value: false, .. },
            MirInstruction::ConstBool { value: true, .. },
            MirInstruction::ConstBool { value: false, .. },
        ]
    ));
}

#[test]
fn optimizer_folds_known_and_irrefutable_structural_pattern_tests() {
    let bool_ty = Type::Scalar(ScalarType::Bool);
    let i64_ty = Type::Scalar(ScalarType::I64);
    let f64_ty = Type::Scalar(ScalarType::F64);
    let char_ty = Type::Scalar(ScalarType::Char);
    let text_ty = Type::Scalar(ScalarType::Text);
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-pattern-constants")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64_ty),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(f64_ty),
            local(bool_ty.clone()),
            local(char_ty),
            local(bool_ty.clone()),
            local(text_ty),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty),
        ],
        result: Type::Scalar(ScalarType::Bool),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 41,
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(1),
                        subject: MirLocal(0),
                        pattern: MirPattern::Literal("0x29".into()),
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(2),
                        subject: MirLocal(0),
                        pattern: MirPattern::Literal("42".into()),
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(3),
                        subject: MirLocal(0),
                        pattern: MirPattern::Any,
                    },
                    MirInstruction::ConstF64 {
                        dst: MirLocal(4),
                        bits: (-0.0f64).to_bits(),
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(5),
                        subject: MirLocal(4),
                        pattern: MirPattern::Literal("0.0".into()),
                    },
                    MirInstruction::ConstChar {
                        dst: MirLocal(6),
                        value: '\n' as u32,
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(7),
                        subject: MirLocal(6),
                        pattern: MirPattern::Literal("'\\n'".into()),
                    },
                    MirInstruction::ConstText {
                        dst: MirLocal(8),
                        value: "line\nbreak".into(),
                    },
                    MirInstruction::PatternTest {
                        dst: MirLocal(9),
                        subject: MirLocal(8),
                        pattern: MirPattern::Literal("\"line\\nbreak\"".into()),
                    },
                ],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(2),
                    then_target: MirBlockId(1),
                    then_arguments: vec![],
                    else_target: MirBlockId(2),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(10),
                    value: true,
                }],
                terminator: MirTerminator::Return {
                    value: MirLocal(10),
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(11),
                    value: false,
                }],
                terminator: MirTerminator::Return {
                    value: MirLocal(11),
                },
            },
        ],
    };

    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.constant_folds, 6);
    assert_eq!(report.eliminated_branches, 1);
    assert!(matches!(
        optimized.blocks[0].instructions[1],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].instructions[2],
        MirInstruction::ConstBool { value: false, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].instructions[3],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].instructions[5],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].instructions[7],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].instructions[9],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[0].terminator,
        MirTerminator::Goto {
            target: MirBlockId(2),
            ..
        }
    ));
}

#[test]
fn optimizer_propagates_constants_through_typed_block_arguments() {
    let i64_ty = Type::Scalar(ScalarType::I64);
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-cross-block-constants")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 40,
                }],
                terminator: MirTerminator::Goto {
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(0)],
                },
            },
            MirBlock {
                parameters: vec![MirLocal(1)],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(2),
                        value: 2,
                    },
                    MirInstruction::AddI64 {
                        dst: MirLocal(3),
                        left: MirLocal(1),
                        right: MirLocal(2),
                    },
                ],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
        ],
    };

    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.constant_folds, 1);
    assert!(matches!(
        optimized.blocks[1].instructions[1],
        MirInstruction::ConstI64 { value: 42, .. }
    ));
}

#[test]
fn optimizer_requires_joined_block_arguments_to_agree() {
    let bool_ty = Type::Scalar(ScalarType::Bool);
    let i64_ty = Type::Scalar(ScalarType::I64);
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-constant-join")),
        captures: 0,
        parameters: vec![MirLocal(0)],
        locals: vec![
            local(bool_ty),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(0),
                    then_target: MirBlockId(1),
                    then_arguments: vec![],
                    else_target: MirBlockId(2),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(1),
                    value: 40,
                }],
                terminator: MirTerminator::Goto {
                    target: MirBlockId(3),
                    arguments: vec![MirLocal(1)],
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(2),
                    value: 41,
                }],
                terminator: MirTerminator::Goto {
                    target: MirBlockId(3),
                    arguments: vec![MirLocal(2)],
                },
            },
            MirBlock {
                parameters: vec![MirLocal(3)],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(4),
                        value: 2,
                    },
                    MirInstruction::AddI64 {
                        dst: MirLocal(5),
                        left: MirLocal(3),
                        right: MirLocal(4),
                    },
                ],
                terminator: MirTerminator::Return { value: MirLocal(5) },
            },
        ],
    };

    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.constant_folds, 0);
    assert!(matches!(
        optimized.blocks[3].instructions[1],
        MirInstruction::AddI64 { .. }
    ));
}

#[test]
fn optimizer_folds_comparisons_and_carries_them_to_a_successor_branch() {
    let bool_ty = Type::Scalar(ScalarType::Bool);
    let i64_ty = Type::Scalar(ScalarType::I64);
    let function = MirFunction {
        definition: DefKey(Digest::of_bytes(b"mir-comparison-constants")),
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64_ty.clone()),
            local(i64_ty),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
            local(bool_ty.clone()),
        ],
        result: bool_ty,
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 40,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 42,
                    },
                    MirInstruction::LtI64 {
                        dst: MirLocal(2),
                        left: MirLocal(0),
                        right: MirLocal(1),
                    },
                ],
                terminator: MirTerminator::Goto {
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(2)],
                },
            },
            MirBlock {
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::SwitchBool {
                    condition: MirLocal(3),
                    then_target: MirBlockId(2),
                    then_arguments: vec![],
                    else_target: MirBlockId(3),
                    else_arguments: vec![],
                },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(4),
                    value: true,
                }],
                terminator: MirTerminator::Return { value: MirLocal(4) },
            },
            MirBlock {
                parameters: vec![],
                instructions: vec![MirInstruction::ConstBool {
                    dst: MirLocal(5),
                    value: false,
                }],
                terminator: MirTerminator::Return { value: MirLocal(5) },
            },
        ],
    };

    let (optimized, report) = optimize_mir(function).unwrap();
    assert_eq!(report.constant_folds, 1);
    assert_eq!(report.eliminated_branches, 1);
    assert!(matches!(
        optimized.blocks[0].instructions[2],
        MirInstruction::ConstBool { value: true, .. }
    ));
    assert!(matches!(
        optimized.blocks[1].terminator,
        MirTerminator::Goto {
            target: MirBlockId(2),
            ..
        }
    ));
}

#[test]
fn mir_rejects_forged_callable_environment_brand_count_and_type() {
    let owner = DefKey(Digest::of_bytes(b"mir-callable-environment-owner"));
    let brand = EnvironmentBrand {
        owner,
        callable: CallableId(3),
    };
    let callable_index = brand.callable.0.to_le_bytes();
    let callee = DefKey(Digest::of_parts([
        b"grandiose-stage0-lifted-callable".as_slice(),
        owner.0.as_bytes().as_slice(),
        callable_index.as_slice(),
    ]));
    let entry = DefKey(Digest::of_bytes(b"mir-callable-environment-entry"));
    let layout = MirCaptureEnvironment {
        brand,
        captures: vec![MirCapture {
            mode: CaptureMode::Move,
            ty: Type::Scalar(ScalarType::I64),
        }],
    };
    let target = MirFunction {
        definition: callee,
        captures: 1,
        parameters: vec![MirLocal(0)],
        locals: vec![local(Type::Scalar(ScalarType::I64))],
        result: Type::Scalar(ScalarType::I64),
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![],
            terminator: MirTerminator::Return { value: MirLocal(0) },
        }],
    };
    let entry_function = |environment: Option<MirCaptureEnvironment>| MirFunction {
        definition: entry,
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(Type::Scalar(ScalarType::I64)),
            local(Type::Callable {
                parameters: vec![],
                result: Box::new(Type::Scalar(ScalarType::I64)),
                effects: EffectRow::empty(),
                lifetime_binders: 0,
                invocation: Quantity::ONCE,
            }),
        ],
        result: Type::Callable {
            parameters: vec![],
            result: Box::new(Type::Scalar(ScalarType::I64)),
            effects: EffectRow::empty(),
            lifetime_binders: 0,
            invocation: Quantity::ONCE,
        },
        entry: MirBlockId(0),
        blocks: vec![MirBlock {
            parameters: vec![],
            instructions: vec![
                MirInstruction::ConstI64 {
                    dst: MirLocal(0),
                    value: 42,
                },
                MirInstruction::MakeCallable {
                    dst: MirLocal(1),
                    callee,
                    captures: vec![MirLocal(0)],
                    generic_arguments: vec![],
                    trait_instance: None,
                    environment,
                },
            ],
            terminator: MirTerminator::Return { value: MirLocal(1) },
        }],
    };
    let valid = MirProgram {
        entry,
        functions: BTreeMap::from([
            (entry, entry_function(Some(layout.clone()))),
            (callee, target),
        ]),
        instances: BTreeMap::new(),
    };
    assert!(valid.validate().is_ok());

    let mut forged_brand = layout.clone();
    forged_brand.brand.callable = CallableId(4);
    assert!(entry_function(Some(forged_brand)).validate().is_err());
    let mut forged_count = layout.clone();
    forged_count.captures.clear();
    assert!(entry_function(Some(forged_count)).validate().is_err());
    let mut forged_type = layout;
    forged_type.captures[0].ty = Type::Scalar(ScalarType::Bool);
    assert!(entry_function(Some(forged_type)).validate().is_err());
    assert!(entry_function(None).validate().is_err());
}
