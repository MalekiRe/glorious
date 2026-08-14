use std::collections::BTreeMap;

use grandiose_stage0::{
    CoreId, DefKey, Digest, GenericArgument, InferVar, Lifetime, MirBlock, MirBlockId, MirEditor,
    MirFunction, MirInstruction, MirLocal, MirLocalDecl, MirPattern, MirProgram, MirTerminator,
    ScalarType, Type, optimize_mir,
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
