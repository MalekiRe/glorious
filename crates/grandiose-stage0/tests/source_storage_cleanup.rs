//! Deliberately-red conformance contracts for the source-storage MIR slice.
//!
//! These fixtures use the already-public raw MIR boundary so the eventual
//! storage representation is tested at the same hostile-input boundary as the
//! rest of `mir.rs`.  They intentionally fail until MIR owns executable
//! storage state and ordered cleanup actions rather than treating every local
//! as an always-live SSA register.

use grandiose_stage0::{
    emit_vm, CoreId, DefKey, Digest, EffectRow, LabelBrand, Lifetime, MirBlock, MirBlockId,
    MirCleanupPlan, MirControlTables, MirFunction, MirInstruction, MirLocal, MirLocalDecl,
    MirScopeId, MirTerminator, Mutability, Quantity, ScalarType, Type,
};

fn local(ty: Type) -> MirLocalDecl {
    MirLocalDecl {
        ty,
        source: CoreId(u32::MAX),
    }
}

fn label_type() -> Type {
    Type::Callable {
        lifetime_binders: 0,
        parameters: vec![Type::Scalar(ScalarType::I64)],
        result: Box::new(Type::Never),
        effects: EffectRow::empty(),
        invocation: Quantity::ONCE,
    }
}

/// A lexical leave abandons an initialized source slot in an inner label
/// scope.  Cleanup elaboration must generate an ordered plan: newest storage
/// first, `EndBorrow` before `Destroy`, then `StorageDead`; the value carried
/// to the target is protected and must not appear in that plan.
///
/// The pre-storage MIR only sees ordinary locals and accepts this empty plan,
/// which is exactly the gap this composite fixture keeps red.  Once storage
/// metadata/actions exist, this one example also proves reverse destruction,
/// nested scope exit, and protected payload exclusion together.
#[test]
fn mir_requires_ordered_source_storage_cleanup_on_nested_lexical_leave() {
    let owner = DefKey(Digest::of_bytes(b"source-storage-cleanup-nested-leave"));
    let function = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: owner,
        captures: 0,
        parameters: vec![],
        locals: vec![
            // An initialized inner-scope owner which is not transferred to
            // the label target and therefore must be destroyed before exit.
            local(Type::Scalar(ScalarType::I64)),
            // The protected label payload survives cleanup.
            local(Type::Scalar(ScalarType::I64)),
            local(label_type()),
            local(Type::Scalar(ScalarType::I64)),
        ],
        result: Type::Scalar(ScalarType::I64),
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 10,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(1),
                        value: 42,
                    },
                    MirInstruction::MakeLabel {
                        label: grandiose_stage0::MirLabelId::UNASSIGNED,
                        dst: MirLocal(2),
                        brand: LabelBrand { owner, label: 0 },
                        target: MirBlockId(1),
                        destination: MirLocal(3),
                    },
                ],
                terminator: MirTerminator::Leave {
                    label: grandiose_stage0::MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(1)],
                    cleanup: MirCleanupPlan {
                        moved_paths: vec![],
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(3)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(3) },
            },
        ],
    }
    .with_frozen_control_tables();

    assert!(
        function.validate().is_err(),
        "an exit from nested source storage cannot omit reverse cleanup or \
         destroy its protected label payload"
    );
    assert!(
        emit_vm(&function).is_err(),
        "VM lowering must reject an unelaborated nested source-storage exit"
    );
}

/// Storage death is not permitted while a loan of that storage is live.  The
/// required cleanup ordering ends the loan before destroying/releasing the
/// source slot.  The old representation has neither a storage lifecycle nor
/// ordered cleanup actions, so this forged leave currently reaches the VM.
#[test]
fn mir_requires_end_borrow_before_source_storage_cleanup() {
    let owner = DefKey(Digest::of_bytes(b"source-storage-cleanup-live-loan"));
    let i64_ty = Type::Scalar(ScalarType::I64);
    let shared_i64 = Type::Reference {
        mutability: Mutability::Shared,
        lifetime: Lifetime::Elided,
        referent: Box::new(i64_ty.clone()),
    };
    let function = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: owner,
        captures: 0,
        parameters: vec![],
        locals: vec![
            local(i64_ty.clone()),
            local(shared_i64),
            local(i64_ty.clone()),
            local(label_type()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![
                    MirInstruction::ConstI64 {
                        dst: MirLocal(0),
                        value: 10,
                    },
                    MirInstruction::Borrow {
                        dst: MirLocal(1),
                        src: MirLocal(0),
                        fields: vec![],
                        unique: false,
                        reborrow: false,
                    },
                    MirInstruction::ConstI64 {
                        dst: MirLocal(2),
                        value: 42,
                    },
                    MirInstruction::MakeLabel {
                        label: grandiose_stage0::MirLabelId::UNASSIGNED,
                        dst: MirLocal(3),
                        brand: LabelBrand { owner, label: 0 },
                        target: MirBlockId(1),
                        destination: MirLocal(4),
                    },
                ],
                terminator: MirTerminator::Leave {
                    label: grandiose_stage0::MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(1),
                    arguments: vec![MirLocal(2)],
                    cleanup: MirCleanupPlan {
                        moved_paths: vec![],
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(4)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(4) },
            },
        ],
    }
    .with_frozen_control_tables();

    assert!(
        function.validate().is_err(),
        "source-storage cleanup must end the live loan before it can destroy \
         or release the borrowed owner"
    );
}

/// A source slot initialized on only one predecessor needs a compiler-created
/// drop flag before both paths can leave its lexical scope.  The `true` edge
/// must destroy/release the owner and clear the flag; the `false` edge must
/// skip it.  No drop-flag operation survives bytecode emission, but verified
/// VM cleanup has to preserve precisely those two outcomes.
///
/// This is deliberately expressed as one branch/leave fixture instead of a
/// synthetic flag API: frontend-emitted flags are not represented yet, and
/// the important contract is that malformed raw MIR cannot evade the required
/// transition and its VM erasure proof.
#[test]
fn mir_requires_drop_flag_for_divergent_source_storage_initialization() {
    let owner = DefKey(Digest::of_bytes(b"source-storage-cleanup-drop-flag"));
    let i64_ty = Type::Scalar(ScalarType::I64);
    let function = MirFunction {
        nominal_copy_descriptors: vec![],
        definition: owner,
        captures: 0,
        parameters: vec![MirLocal(0), MirLocal(1)],
        locals: vec![
            local(Type::Scalar(ScalarType::Bool)),
            // This is the protected payload carried through either leave.
            local(i64_ty.clone()),
            // Only the true predecessor initializes this source slot.
            local(i64_ty.clone()),
            local(label_type()),
            local(i64_ty.clone()),
        ],
        result: i64_ty,
        control: MirControlTables::default(),
        entry: MirBlockId(0),
        blocks: vec![
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::MakeLabel {
                    label: grandiose_stage0::MirLabelId::UNASSIGNED,
                    dst: MirLocal(3),
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(3),
                    destination: MirLocal(4),
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
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![MirInstruction::ConstI64 {
                    dst: MirLocal(2),
                    value: 10,
                }],
                terminator: MirTerminator::Leave {
                    label: grandiose_stage0::MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(3),
                    arguments: vec![MirLocal(1)],
                    cleanup: MirCleanupPlan {
                        moved_paths: vec![],
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![],
                instructions: vec![],
                terminator: MirTerminator::Leave {
                    label: grandiose_stage0::MirLabelId::UNASSIGNED,
                    brand: LabelBrand { owner, label: 0 },
                    target: MirBlockId(3),
                    arguments: vec![MirLocal(1)],
                    cleanup: MirCleanupPlan {
                        moved_paths: vec![],
                        moved_places: vec![],
                        active_loans: vec![],
                    },
                },
            },
            MirBlock {
                scope: MirScopeId::ROOT,
                parameters: vec![MirLocal(4)],
                instructions: vec![],
                terminator: MirTerminator::Return { value: MirLocal(4) },
            },
        ],
    }
    .with_frozen_control_tables();

    assert!(
        function.validate().is_err(),
        "a divergent source-storage initialization must carry a checked drop \
         flag transition rather than silently omitting cleanup"
    );
    assert!(
        emit_vm(&function).is_err(),
        "the VM must not erase an unproven source-storage drop-flag transition"
    );
}
