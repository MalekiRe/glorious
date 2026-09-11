use super::*;

fn fixture(source: &str) -> VmLirProgram {
    let runtime = crate::runtime_mir::tests::fixture(source);
    let function = lower::lower_function(&runtime).unwrap();
    let mut program = VmLirProgram {
        entry: function.definition,
        functions: BTreeMap::from([(function.definition, function)]),
        callable_environments: BTreeMap::new(),
    };
    program.infer_returns().unwrap();
    program.validate().unwrap();
    program
}

#[test]
fn lir_uses_only_claimed_consuming_effect_payloads() {
    let program = fixture("effect Ask { [0, 1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(42) { Ask::ask(value) with _ => value } }");
    let function = &program.functions[&program.entry];
    let instructions = function.blocks.iter().flat_map(|block| &block.instructions).collect::<Vec<_>>();
    assert!(instructions.iter().any(|instruction| matches!(instruction, VmInstruction::PerformOwned { .. })));
    assert!(instructions.iter().any(|instruction| matches!(instruction, VmInstruction::InstallHandlerOwned { .. })));
    assert!(instructions.iter().any(|instruction| matches!(instruction, VmInstruction::ClaimEffectPayloads { .. })));
    let bytes = crate::vm_backend::encode_program(&program.emit().unwrap());
    assert_eq!(crate::vm_backend::decode_and_verify_program(&bytes).unwrap().run_i64().unwrap(), 42);
    let mut forged = program;
    let perform = forged.functions.get_mut(&forged.entry).unwrap().blocks.iter_mut()
        .flat_map(|block| &mut block.instructions).find(|instruction| matches!(instruction, VmInstruction::PerformOwned { .. })).unwrap();
    let VmInstruction::PerformOwned { dst, effect, effect_arguments, operation, arguments } = perform.clone() else { panic!() };
    *perform = VmInstruction::Perform { dst, effect, effect_arguments, operation, arguments };
    assert!(forged.validate().is_err());
}

#[test]
fn lir_relocates_and_round_trips_without_a_mir_body() {
    let program = fixture("pub fn main() -> i64 { 42 }");
    let first = program.emit().unwrap();
    assert_eq!(first, program.emit().unwrap());
    let bytes = crate::vm_backend::encode_program(&first);
    let executable = crate::vm_backend::decode_and_verify_program(&bytes).unwrap();
    assert_eq!(executable.run_i64().unwrap(), 42);
}

#[test]
fn lir_rejects_generic_register_metadata_accepted_by_legacy_artifacts() {
    for ty in [
        VmType::Generic(0),
        VmType::Array(Box::new(VmType::Generic(0))),
        VmType::Nominal {
            definition: DefKey(Digest::of_bytes(b"generic-lir-nominal")),
            arguments: vec![crate::vm_backend::VmGenericArgument::ConstGeneric {
                index: 0,
                kind: crate::ConstKind::U32,
            }],
        },
    ] {
        let mut program = fixture("pub fn main() -> i64 { 42 }");
        program
            .functions
            .get_mut(&program.entry)
            .unwrap()
            .registers
            .push(ty);
        // Unused generic registers are legal in the compatibility schema,
        // so this rejection must be the independent production LIR boundary.
        crate::vm_backend::verify_program(program.emit().unwrap()).unwrap();
        assert!(matches!(
            program.validate(),
            Err(VmArtifactError::MalformedEncoding { message })
                if matches!(message, "VM LIR retains a non-concrete type or const"
                    | "VM LIR retains a non-concrete generic argument")
        ));
    }
}

#[test]
fn lir_rejects_open_effect_rows_inside_callable_metadata() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    program
        .functions
        .get_mut(&program.entry)
        .unwrap()
        .registers
        .push(VmType::Callable { shared_receiver: false, unique_receiver: false,
            safety: Safety::Safe,
            parameters: vec![],
            result: Box::new(VmType::I64),
            effects: Box::new(crate::vm_backend::VmEffectRow {
                tails: [crate::EffectTail::Generic(0)].into_iter().collect(),
                ..Default::default()
            }),
        });
    crate::vm_backend::verify_program(program.emit().unwrap()).unwrap();
    assert!(matches!(
        program.validate(),
        Err(VmArtifactError::MalformedEncoding {
            message: "VM LIR retains an open or projected effect row"
        })
    ));
}

#[test]
fn lir_checks_protocol_arguments_even_in_unreachable_machine_leaves() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    program
        .functions
        .get_mut(&program.entry)
        .unwrap()
        .blocks
        .push(VmLirBlock {
            instructions: vec![VmInstruction::Perform {
                dst: 0,
                effect: program.entry,
                operation: 0,
                arguments: vec![],
                effect_arguments: vec![crate::vm_backend::VmGenericArgument::ConstGeneric {
                    index: 0,
                    kind: crate::ConstKind::U32,
                }],
            }],
            terminator: VmLirTerminator::Trap,
        });
    assert!(matches!(
        program.validate(),
        Err(VmArtifactError::MalformedEncoding {
            message: "VM LIR retains a non-concrete generic argument"
        })
    ));
}

#[test]
fn lir_checks_layout_and_environment_metadata_without_reachability_shortcuts() {
    let original = fixture("pub fn main() -> i64 { 42 }");
    let mut layout = original.clone();
    layout
        .functions
        .get_mut(&layout.entry)
        .unwrap()
        .nominal_copy_descriptors
        .push(VmNominalCopyDescriptor {
            definition: layout.entry,
            source_contract: Digest::of_bytes(b"layout"),
            is_enum: false,
            arguments: vec![],
            variants: vec![vec![VmType::Generic(0)]],
        });
    assert!(layout.validate_closed_metadata().is_err());
    let mut environment = original;
    environment.callable_environments.insert(
        environment.entry,
        VmCaptureEnvironment {
            owner: environment.entry,
            callable: 0,
            instance: None,
            destructor: None,
            captures: vec![crate::vm_backend::VmCapture {
                mode: crate::vm_backend::VmCaptureMode::Move,
                ty: VmType::Generic(0),
            }],
        },
    );
    assert!(environment.validate_closed_metadata().is_err());
}

#[test]
fn lir_branch_edges_are_blocks_and_missing_symbols_fail() {
    let mut program = fixture("pub fn main() -> i64 { handle 0 { 0 => 41; _ => 42 } }");
    assert_eq!(
        crate::vm_backend::verify_program(program.emit().unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        41
    );
    let function = program.functions.get_mut(&program.entry).unwrap();
    let missing = VmLirBlockId(function.blocks.len() as u32);
    let branch = function
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, VmLirTerminator::Branch { .. }))
        .unwrap();
    let VmLirTerminator::Branch { then_target, .. } = &mut branch.terminator else {
        unreachable!()
    };
    *then_target = missing;
    assert!(program.validate().is_err());
}

#[test]
fn lir_independently_rejects_a_forged_register() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    let function = program.functions.get_mut(&program.entry).unwrap();
    let missing = function.registers.len() as u32;
    let block = function
        .blocks
        .iter_mut()
        .find(|block| matches!(block.terminator, VmLirTerminator::Return(_)))
        .unwrap();
    block.terminator = VmLirTerminator::Return(missing);
    assert!(program.validate().is_err());
}

#[test]
fn lir_rejects_legacy_call_fallbacks() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    let function = program.functions.get_mut(&program.entry).unwrap();
    function.blocks[0].instructions.push(VmInstruction::Call {
        dst: 0,
        callee: function.definition,
        arguments: vec![],
    });
    assert!(program.validate().is_err());
}

#[test]
fn lir_rejects_control_hidden_in_machine_leaves() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    program.functions.get_mut(&program.entry).unwrap().blocks[0]
        .instructions
        .push(VmInstruction::Jump { target: 0 });
    assert!(program.validate().is_err());
}

#[test]
fn lir_independently_rejects_a_forged_result_abi() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    program.functions.get_mut(&program.entry).unwrap().result = VmType::Bool;
    assert!(program.validate().is_err());
    let candidate = program.emit().unwrap();
    assert!(
        crate::vm_backend::decode_and_verify_program(&crate::vm_backend::encode_program(
            &candidate
        ))
        .is_err()
    );
}

#[test]
fn lir_return_flag_is_checked_on_an_uncalled_entrypoint() {
    let mut program = fixture("pub fn main() -> i64 { 42 }");
    program.functions.get_mut(&program.entry).unwrap().returns = false;
    assert!(program.validate().is_err());
}

#[test]
fn lir_handler_cancellation_contributes_to_the_normal_return_abi() {
    let program = fixture(
        "effect Ask { [0,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle Ask::ask(20) { Ask::ask(_) with _ => 42 } }",
    );
    assert!(program.functions[&program.entry].returns);
    let bytes = crate::vm_backend::encode_program(&program.emit().unwrap());
    assert_eq!(
        crate::vm_backend::decode_and_verify_program(&bytes)
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn lir_lexical_leave_retains_its_enclosing_handler() {
    let program = fixture(
        "effect Ask { [0,1] ask(value: i64) -> i64; } pub fn main() -> i64 { handle label done { transfer done 42 } { Ask::ask(_) with _ => 0 } }",
    );
    assert!(
        program.functions[&program.entry]
            .blocks
            .iter()
            .any(|block| matches!(
                block.terminator,
                VmLirTerminator::Leave {
                    ref retained_handlers,
                    ref exited_handlers,
                    ..
                } if retained_handlers.len() == 1 && exited_handlers.is_empty()
            ))
    );
    assert_eq!(
        crate::vm_backend::verify_program(program.emit().unwrap())
            .unwrap()
            .run_i64()
            .unwrap(),
        42
    );
}

#[test]
fn lir_leave_rejects_invalid_handler_relocations() {
    let original = fixture("effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle label done { transfer done 42 } { Ask::ask() with _ => 0 } }");
    let body = &original.functions[&original.entry];
    let nonhandler = body.blocks.iter().enumerate().find_map(|(block, data)|
        data.instructions.iter().position(|instruction| !matches!(instruction, VmInstruction::InstallHandlerOwned { .. }))
            .map(|offset| (VmLirBlockId(block as u32), offset as u32))).unwrap();
    for location in [(VmLirBlockId(u32::MAX), 0), (VmLirBlockId(0), u32::MAX), nonhandler] {
        let mut forged = original.clone();
        let prefix = forged.functions.get_mut(&forged.entry).unwrap().blocks.iter_mut().find_map(|block|
            match &mut block.terminator { VmLirTerminator::Leave { retained_handlers, .. } => Some(retained_handlers), _ => None }).unwrap();
        prefix[0] = location;
        assert!(forged.emit().is_err());
    }
}
