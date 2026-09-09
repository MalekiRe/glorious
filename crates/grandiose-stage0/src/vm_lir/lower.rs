use super::*;
use crate::runtime_mir::{RuntimeMir, RuntimeOperation, RuntimeProgram, RuntimeTerminator};
use crate::vm_backend::{
    emit_parallel_moves, lower_instruction, vm_nominal_copy_descriptor,
    vm_nominal_copy_descriptor_key, vm_type,
};

impl VmLirProgram {
    pub fn lower(source: &RuntimeProgram) -> Result<Self, VmArtifactError> {
        source.validate().map_err(|error| {
            eprintln!("Runtime to VM LIR validation: {}", error.0);
            invalid("VM LIR input failed Runtime validation")
        })?;
        let owners = specialized_lifted_owners(source)?;
        let reachable = source.reachable_function_keys();
        let mut functions = source
            .functions()
            .iter()
            .filter(|(key, _)| reachable.contains(key))
            .map(|(key, body)| Ok((*key, lower_function(body)?)))
            .collect::<Result<BTreeMap<_, _>, VmArtifactError>>()?;
        let mut callable_environments = BTreeMap::new();
        for function in functions.values_mut() {
            for instruction in function
                .blocks
                .iter_mut()
                .flat_map(|block| &mut block.instructions)
            {
                if let VmInstruction::MakeCallable {
                    callee,
                    environment: Some(environment),
                    ..
                } = instruction
                {
                    environment.instance = owners.get(callee).map(|owner| owner.fingerprint());
                    if let Some(previous) =
                        callable_environments.insert(*callee, environment.clone())
                        && previous != *environment
                    {
                        return Err(invalid("VM LIR callable has conflicting environments"));
                    }
                }
            }
        }
        let program = Self {
            entry: source.entry(),
            functions,
            callable_environments,
        };
        program.validate()?;
        Ok(program)
    }
}

/// Instance identity is a link-time proof, not a source specialization retry.
/// Walk already-materialized Runtime bodies and seal the same identity into
/// the VM environment registry consumed by independent artifact verification.
fn specialized_lifted_owners(
    source: &RuntimeProgram,
) -> Result<BTreeMap<DefKey, crate::InstanceKey>, VmArtifactError> {
    let mut owners = BTreeMap::new();
    let mut pending = source
        .instances()
        .values()
        .filter(|instance| !instance.key.arguments().is_empty())
        .map(|instance| (instance.executable, instance.key.clone()))
        .collect::<std::collections::VecDeque<_>>();
    while let Some((definition, instance)) = pending.pop_front() {
        let function = source
            .functions()
            .get(&definition)
            .ok_or_else(|| invalid("VM LIR instance has no executable body"))?;
        for operation in function
            .blocks()
            .iter()
            .flat_map(|block| &block.instructions)
        {
            let RuntimeOperation::MakeCallable {
                callee,
                environment: Some(environment),
                ..
            } = operation
            else {
                continue;
            };
            let lexical = crate::mir::lifted_callable_definition(environment.brand);
            let target = crate::mir::materialized_lifted_callable_definition(&instance, lexical);
            if *callee != target {
                return Err(invalid(
                    "VM LIR specialized callable identity is not canonical",
                ));
            }
            match owners.get(&target) {
                Some(owner) if owner != &instance => {
                    return Err(invalid("VM LIR callable has contradictory instance owners"));
                }
                Some(_) => {}
                None => {
                    owners.insert(target, instance.clone());
                    pending.push_back((target, instance.clone()));
                }
            }
        }
    }
    Ok(owners)
}

pub(super) fn lower_function(source: &RuntimeMir) -> Result<VmLirFunction, VmArtifactError> {
    let mut registers = source
        .locals
        .iter()
        .enumerate()
        .map(|(index, local)| {
            vm_type(&local.ty).map_err(|ty| VmArtifactError::UnsupportedType {
                local: index as u32,
                ty,
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    let result = vm_type(&source.result).map_err(|ty| VmArtifactError::UnsupportedType {
        local: u32::MAX,
        ty,
    })?;
    let mut descriptors = source
        .nominal_copy_descriptors
        .iter()
        .map(vm_nominal_copy_descriptor)
        .collect::<Result<Vec<_>, _>>()?;
    descriptors.sort_by_key(vm_nominal_copy_descriptor_key);
    let mut nominal_copy_descriptors: Vec<VmNominalCopyDescriptor> = Vec::new();
    for descriptor in descriptors {
        if let Some(previous) = nominal_copy_descriptors.last()
            && previous.definition == descriptor.definition
            && previous.arguments == descriptor.arguments
        {
            if *previous != descriptor {
                return Err(invalid("VM LIR lifetime-erased nominal layouts disagree"));
            }
            continue;
        }
        nominal_copy_descriptors.push(descriptor);
    }
    // Machine leaf conversion maps source block IDs to symbolic LIR IDs. It
    // never sees PCs, a source interface, or a reconstructed MIR function.
    let labels = (0..source.blocks.len())
        .map(|index| {
            u32::try_from(index).map_err(|_| invalid("VM LIR block arena exceeds address space"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let transfers = source
        .frame
        .transfers
        .iter()
        .map(|transfer| {
            (
                (transfer.block.0 as usize, transfer.instruction as usize),
                transfer,
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut blocks = Vec::with_capacity(source.blocks.len());
    let mut edges = Vec::new();
    for (index, block) in source.blocks.iter().enumerate() {
        let mut instructions = block
            .instructions
            .iter()
            .enumerate()
            .map(|(offset, operation)| {
                let leaf = crate::runtime_mir::emission::emit_operation(
                    operation,
                    transfers.get(&(index, offset)).copied(),
                );
                let mut instruction = lower_instruction(&leaf, &labels)?.with_owned_effect_payloads();
                if let RuntimeOperation::Store { dst, src } = operation {
                    instruction = VmInstruction::StoreOwned { dst: dst.0, src: src.0 };
                }
                if matches!(operation, RuntimeOperation::MakeTuple { .. } | RuntimeOperation::MakeArray { .. }
                    | RuntimeOperation::MakeRecord { .. } | RuntimeOperation::MakeEnum { .. }) {
                    instruction = instruction.with_owned_aggregate();
                }
                if let (RuntimeOperation::InstallHandler { replay_owned, .. },
                    VmInstruction::InstallHandlerOwned { replay_owned: machine, .. }) = (operation, &mut instruction)
                {
                    *machine = replay_owned.iter().map(|local| local.0).collect();
                }
                Ok(instruction)
            })
            .collect::<Result<Vec<_>, _>>()?;
        // Runtime's explicit Abort leaf ends execution before any nominal
        // block suffix. In LIR it occupies the dedicated terminator slot.
        let abort = instructions
            .iter()
            .position(|instruction| matches!(instruction, VmInstruction::Trap));
        let terminator = if let Some(offset) = abort {
            instructions.truncate(offset);
            VmLirTerminator::Trap
        } else {
            match &block.terminator {
                RuntimeTerminator::Goto { target, arguments } => {
                    emit_parallel_moves(
                        arguments,
                        &source.blocks[target.0 as usize].parameters,
                        &mut registers,
                        &mut instructions,
                    );
                    VmLirTerminator::Jump(VmLirBlockId(target.0))
                }
                RuntimeTerminator::SwitchBool {
                    condition,
                    then_target,
                    then_arguments,
                    else_target,
                    else_arguments,
                } => {
                    let mut edge =
                        |target: crate::mir::MirBlockId, arguments: &[crate::mir::MirLocal]| {
                            let id = u32::try_from(source.blocks.len() + edges.len())
                                .map_err(|_| invalid("VM LIR edge arena exceeds address space"))?;
                            let mut instructions = Vec::new();
                            emit_parallel_moves(
                                arguments,
                                &source.blocks[target.0 as usize].parameters,
                                &mut registers,
                                &mut instructions,
                            );
                            edges.push(VmLirBlock {
                                instructions,
                                terminator: VmLirTerminator::Jump(VmLirBlockId(target.0)),
                            });
                            Ok::<_, VmArtifactError>(VmLirBlockId(id))
                        };
                    VmLirTerminator::Branch {
                        condition: condition.0,
                        then_target: edge(*then_target, then_arguments)?,
                        else_target: edge(*else_target, else_arguments)?,
                    }
                }
                RuntimeTerminator::Return { .. } => VmLirTerminator::Return(
                    transfers[&(index, block.instructions.len())].arguments[0]
                        .local
                        .0,
                ),
                RuntimeTerminator::TailCall { callee, arguments } => VmLirTerminator::TailCall {
                    callee: *callee, arguments: arguments.iter().map(|argument| argument.0).collect(),
                },
                RuntimeTerminator::Leave {
                    brand,
                    target,
                    cleanup,
                    ..
                } => VmLirTerminator::Leave {
                    brand_owner: brand.owner,
                    brand_label: brand.label,
                    handler_depth: source
                        .control
                        .leave_handler_depths
                        .get(&crate::mir::MirBlockId(index as u32))
                        .copied()
                        .ok_or_else(|| {
                            invalid("VM LIR leave is missing its checked handler depth")
                        })?,
                    target: VmLirBlockId(target.0),
                    arguments: transfers[&(index, block.instructions.len())]
                        .arguments
                        .iter()
                        .map(|arg| arg.local.0)
                        .collect(),
                    destinations: source.blocks[target.0 as usize]
                        .parameters
                        .iter()
                        .map(|local| local.0)
                        .collect(),
                    cleanup: VmCleanupProof::from_mir(
                        cleanup,
                        &source.control.move_paths,
                        &source.control.source_storage,
                    )?,
                },
                RuntimeTerminator::Unreachable => VmLirTerminator::Trap,
            }
        };
        blocks.push(VmLirBlock {
            instructions,
            terminator,
        });
    }
    blocks.extend(edges);
    let mut function = VmLirFunction {
        definition: source.definition,
        safety: source.safety,
        unsafe_execution: source.unsafe_execution,
        nominal_copy_descriptors,
        captures: source.frame.capture_parameters.len() as u32,
        parameters: (source.frame.capture_parameters.len()
            + source.frame.invocation_parameters.len()) as u32,
        registers,
        result,
        returns: false,
        frame_cleanup: source
            .frame
            .abandonment
            .iter()
            .map(|action| VmFrameDrop {
                owner: action.owner.0,
                destructor: action.destructor,
            })
            .collect(),
        entry: VmLirBlockId(source.entry.0),
        blocks,
    };
    function.returns = crate::vm_backend::infer_function_returns(&function.emit()?)?
        || (source.result != crate::Type::Never && function.blocks.iter().any(|block|
            matches!(block.terminator, VmLirTerminator::TailCall { .. })));
    Ok(function)
}
