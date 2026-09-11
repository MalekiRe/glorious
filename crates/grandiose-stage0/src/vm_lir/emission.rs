use super::*;

impl VmLirFunction {
    /// Handler entry PCs must follow every installing PC. Ordinary loops do
    /// not constrain layout. Stable topological ordering preserves this ABI
    /// even when Cleanup introduced later-numbered installation blocks.
    fn layout(&self) -> Result<Vec<usize>, VmArtifactError> {
        if self.blocks.is_empty() || self.entry.0 != 0 {
            return Err(invalid("VM LIR has no canonical entry block"));
        }
        let mut successors = vec![BTreeSet::new(); self.blocks.len()];
        let mut predecessors = vec![0usize; self.blocks.len()];
        for (index, block) in self.blocks.iter().enumerate() {
            for instruction in &block.instructions {
                match instruction {
                    VmInstruction::InstallHandlerOwned { target, .. } => {
                        let target = *target as usize;
                        if target >= self.blocks.len() {
                            return Err(invalid("VM LIR handler target is missing"));
                        }
                        if successors[index].insert(target) {
                            predecessors[target] += 1;
                        }
                    }
                    VmInstruction::MakeLabel { target, .. }
                        if *target as usize >= self.blocks.len() =>
                    {
                        return Err(invalid("VM LIR label target is missing"));
                    }
                    VmInstruction::Jump { .. }
                    | VmInstruction::BranchBool { .. }
                    | VmInstruction::Return { .. }
                    | VmInstruction::Leave { .. }
                    | VmInstruction::Trap
                    | VmInstruction::DeclareResult { .. }
                    | VmInstruction::DeclareFrameCleanup { .. } => {
                        return Err(invalid(
                            "VM LIR control instruction is not in its dedicated slot",
                        ));
                    }
                    // Production calls always consume their outgoing carriers.
                    VmInstruction::Call { .. }
                    | VmInstruction::CallIndirect { .. }
                    | VmInstruction::HostCall { .. } => {
                        return Err(invalid("VM LIR contains a legacy non-consuming call"));
                    }
                    VmInstruction::Perform { .. } | VmInstruction::InstallHandler { .. } => {
                        return Err(invalid("VM LIR contains a legacy effect payload protocol"));
                    }
                    _ => {}
                }
            }
            let targets = match &block.terminator {
                VmLirTerminator::Jump(target) | VmLirTerminator::Leave { target, .. } => {
                    vec![*target]
                }
                VmLirTerminator::Branch {
                    then_target,
                    else_target,
                    ..
                } => vec![*then_target, *else_target],
                _ => vec![],
            };
            if targets
                .iter()
                .any(|target| target.0 as usize >= self.blocks.len())
            {
                return Err(invalid("VM LIR terminator target is missing"));
            }
        }
        let mut ready = predecessors
            .iter()
            .enumerate()
            .filter_map(|(index, count)| (*count == 0).then_some(index))
            .collect::<BTreeSet<_>>();
        let mut order = Vec::with_capacity(self.blocks.len());
        while let Some(index) = ready.pop_first() {
            order.push(index);
            for target in &successors[index] {
                predecessors[*target] -= 1;
                if predecessors[*target] == 0 {
                    ready.insert(*target);
                }
            }
        }
        if order.len() != self.blocks.len() || order.first() != Some(&0) {
            return Err(invalid(
                "VM LIR handler layout dependencies are cyclic or precede entry",
            ));
        }
        Ok(order)
    }

    pub(super) fn emit(&self) -> Result<VmFunction, VmArtifactError> {
        let order = self.layout()?;
        let mut starts = vec![0u32; self.blocks.len()];
        let mut next = 1u32 + u32::from(!self.frame_cleanup.is_empty());
        for index in &order {
            starts[*index] = next;
            let length = u32::try_from(self.blocks[*index].instructions.len())
                .map_err(|_| invalid("VM LIR block exceeds address space"))?;
            next = next
                .checked_add(length)
                .and_then(|next| next.checked_add(1))
                .ok_or_else(|| invalid("VM LIR function exceeds address space"))?;
        }
        let mut instructions = Vec::with_capacity(next as usize);
        instructions.push(VmInstruction::DeclareResult {
            result: self.result.clone(),
            returns: self.returns,
        });
        if !self.frame_cleanup.is_empty() {
            instructions.push(VmInstruction::DeclareFrameCleanup {
                actions: self.frame_cleanup.clone(),
            });
        }
        let handler_pc = |(block, offset): &(VmLirBlockId, u32)| -> Result<u32, VmArtifactError> {
            let data = self.blocks.get(block.0 as usize).ok_or_else(|| invalid("VM LIR leave names an absent handler block"))?;
            if !matches!(data.instructions.get(*offset as usize), Some(VmInstruction::InstallHandlerOwned { .. })) {
                return Err(invalid("VM LIR leave does not name a handler installation"));
            }
            starts[block.0 as usize].checked_add(*offset).ok_or_else(|| invalid("VM LIR handler PC overflows"))
        };
        for index in order {
            let block = &self.blocks[index];
            for instruction in &block.instructions {
                let mut instruction = instruction.clone();
                match &mut instruction {
                    VmInstruction::InstallHandlerOwned { target, .. }
                    | VmInstruction::MakeLabel { target, .. } => {
                        *target = starts[*target as usize];
                    }
                    _ => {}
                }
                instructions.push(instruction);
            }
            instructions.push(match &block.terminator {
                VmLirTerminator::Jump(target) => VmInstruction::Jump {
                    target: starts[target.0 as usize],
                },
                VmLirTerminator::Branch {
                    condition,
                    then_target,
                    else_target,
                } => VmInstruction::BranchBool {
                    condition: *condition,
                    then_target: starts[then_target.0 as usize],
                    else_target: starts[else_target.0 as usize],
                },
                VmLirTerminator::Return(value) => VmInstruction::Return { value: *value },
                VmLirTerminator::TailCall { callee, arguments } => VmInstruction::TailCallOwned {
                    callee: *callee, arguments: arguments.clone(),
                },
                VmLirTerminator::Leave {
                    brand_owner,
                    brand_label,
                    retained_handlers,
                    exited_handlers,
                    target,
                    arguments,
                    destinations,
                    cleanup,
                } => VmInstruction::Leave {
                    brand_owner: *brand_owner,
                    brand_label: *brand_label,
                    retained_handlers: retained_handlers.iter().map(handler_pc).collect::<Result<_, _>>()?,
                    exited_handlers: exited_handlers.iter().map(handler_pc).collect::<Result<_, _>>()?,
                    target: starts[target.0 as usize],
                    arguments: arguments.clone(),
                    destinations: destinations.clone(),
                    cleanup: cleanup.clone(),
                },
                VmLirTerminator::Trap => VmInstruction::Trap,
            });
        }
        Ok(VmFunction {
            definition: self.definition,
            safety: self.safety,
            unsafe_execution: self.unsafe_execution,
            nominal_copy_descriptors: self.nominal_copy_descriptors.clone(),
            captures: self.captures,
            parameters: self.parameters,
            registers: self.registers.clone(),
            instructions,
        })
    }
}
