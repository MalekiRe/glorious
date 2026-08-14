use grandiose_stage0::{
    CoreId, DefKey, Digest, MirBlock, MirBlockId, MirEditor, MirFunction, MirInstruction, MirLocal,
    MirLocalDecl, MirTerminator, ScalarType, Type, optimize_mir,
};

fn local(ty: Type) -> MirLocalDecl {
    MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    }
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
