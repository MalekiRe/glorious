//! Generated segments over the ordinary execution runtime's resident frames.
//! No native body is replaced by bytecode or a synthetic host-call wrapper.
//! Scalars have private spill slots; addressable residents and their masks
//! stay in the same NativeHome through calls, suspension and engine switches.

use super::{LlvmError, LlvmExecutionProfile, LlvmNativeModule, NativeContext};
use crate::vm_backend::{
    DefKey, ExecutionBudget, RuntimeRegisters, VmArtifactError, VmExecutionLimits,
    VmFunction, VmInstruction, VmType, VmValue, VmAuthoringProfile,
    native_memory::NativeShape, native_storage::{NativeFramePlan, NativeScalarSpills},
};
use std::sync::Arc;

fn error(message: &'static str) -> VmArtifactError { VmArtifactError::NativeAbi { message } }

fn runtime_error(failure: LlvmError) -> VmArtifactError {
    match failure {
        LlvmError::Runtime(failure) | LlvmError::VerifiedCode(failure) => failure,
        _ => error("generated segment violated its bound execution contract"),
    }
}

impl LlvmNativeModule {
    pub(in crate::vm_backend) fn is_native(&self, definition: DefKey) -> bool {
        !self.plan().vm_functions.contains(&definition)
    }

    pub(in crate::vm_backend) fn extend_resident_plan(&self, function: &VmFunction, plan: &mut NativeFramePlan) {
        let index = self.plan().functions.binary_search(&function.definition).expect("bound native graph");
        let frame = &self.plan().frame_layouts[index];
        for (slot, layout) in frame.layouts.iter().enumerate() {
            // Even a VM-selected producer establishes an aggregate's native
            // home before it crosses an engine boundary. Private scalar
            // registers need no additional source storage identity.
            if !matches!(layout.shape, NativeShape::Scalar) {
                plan.layouts[slot] = Some(layout.clone());
            }
        }
        plan.results = function.instructions.iter().map(|instruction|
            crate::vm_backend::native_storage::instruction_result(instruction)
                .filter(|slot| plan.layouts[*slot as usize].is_some() || *slot < function.captures)).collect();
        plan.read_projections.fill(None);
    }

    pub(in crate::vm_backend) fn execute_segment(&self, function: &VmFunction, pc: usize,
        registers: &mut RuntimeRegisters, budget: &mut ExecutionBudget,
    ) -> Result<usize, VmArtifactError> {
        let index = self.plan().functions.binary_search(&function.definition)
            .map_err(|_| error("native frame does not belong to its bound graph"))?;
        let frame = &self.plan().frame_layouts[index];
        let spills = NativeScalarSpills::acquire(frame.scalar_spill_layout, frame.scratch_bytes, budget)?;
        let _scratch = budget.native_memory.reserve_control(frame.scratch_bytes, budget.limits)?;
        let mut homes = Vec::with_capacity(frame.layouts.len());
        let mut flags = Vec::with_capacity(frame.layouts.len());
        let mut slots = Vec::with_capacity(2 * frame.layouts.len());
        for (slot, layout) in frame.layouts.iter().enumerate() {
            let local = slot as u32;
            let resident = registers.wants_native(local);
            let observed_entry = if resident && registers.values[slot].is_some() {
                budget.native_memory.measurements.as_ref().map(|measurements| (measurements.clone(), measurements.snapshot()))
            } else { None };
            let (home, pointer) = if resident {
                let home = registers.native_home(local, budget)?;
                if let Some(value) = &registers.values[slot] {
                    home.store(&[], value, budget)?;
                } else { home.clear(&[]); }
                flags.push(frame.paths[slot].iter().map(|path| u8::from(home.is_initialized(path))).collect::<Vec<_>>());
                let pointer = home.pointer();
                (Some(home), pointer)
            } else {
                if frame.paths[slot].len() != 1 || !frame.paths[slot][0].is_empty() {
                    return Err(error("private scalar spill has a non-scalar initialization contract"));
                }
                let offset = frame.scalar_spill_offsets[slot]
                    .ok_or_else(|| error("private native register has no scalar spill layout"))?;
                flags.push(vec![u8::from(spills.store(offset, layout, registers.values[slot].as_ref(), budget)?)]);
                (None, spills.slot(offset, layout)?)
            };
            if let Some((measurements, before)) = observed_entry { measurements.resident_entry(before); }
            slots.extend([pointer.cast_const(), flags.last().unwrap().as_ptr()]);
            homes.push(home);
        }
        let mut loans = Vec::with_capacity(homes.len());
        for (slot, home) in homes.iter().enumerate() {
            // The generated code writes the actual active initialization view,
            // not a shadow mask interpreted after the computation has run.
            if let Some(home) = home {
                loans.push(unsafe { home.lend_native(flags[slot].as_mut_ptr(), frame.paths[slot].clone(), budget)? });
            }
        }
        let mut context = NativeContext::new(budget.limits);
        context.instructions = budget.instructions;
        let mut allocation = super::memory::AllocationContext::new(&mut budget.native_memory, budget.limits.max_native_bytes);
        let callables = super::callables::CallableContext::new(self, budget);
        unsafe { allocation.install(&mut context); callables.install(&mut context); }
        let mut stopped = u32::try_from(pc).map_err(|_| error("native resume location overflow"))?;
        let status = unsafe { self.invoke_segment(index, &mut context, slots.as_ptr(), &mut stopped) };
        for loan in loans.into_iter().rev() { loan.finish()?; }
        budget.instructions = context.instructions;
        if let Some(failure) = allocation.failure { return Err(failure); }
        if let Some(failure) = callables.failure.borrow_mut().take() { return Err(failure); }
        context.result(status).map_err(runtime_error)?;
        let stopped = stopped as usize;
        if !function.instructions.get(stopped).is_some_and(crate::vm_backend::execution::is_frame_transition) {
            return Err(error("native segment returned without a verified frame transition"));
        }
        for (slot, home) in homes.into_iter().enumerate() {
            registers.values[slot] = if let Some(home) = home {
                if home.is_initialized(&[]) { Some(VmValue::Resident(home)) } else { None }
            } else {
                // The successfully completed verified segment supplies the
                // current scalar mask, never bytes retained from another entry.
                unsafe { spills.load(frame.scalar_spill_offsets[slot].expect("checked scalar spill"),
                    &frame.layouts[slot], flags[slot][0], budget)? }
            };
        }
        spills.release(budget);
        Ok(stopped)
    }

    pub(super) fn run_shared(&self, limits: VmExecutionLimits, measure_memory: bool) -> Result<(i64, LlvmExecutionProfile), LlvmError> {
        self.plan().validate_abi(self.abi())?;
        let program = &self.plan().program.program;
        let entry = &program.functions[&program.entry];
        if entry.parameters != 0 || !matches!(entry.instructions.first(), Some(VmInstruction::DeclareResult { result: VmType::I64, .. })) {
            return Err(LlvmError::AbiMismatch("native i64 runner requires a zero-argument i64 entry"));
        }
        let mut budget = ExecutionBudget {
            native_memory: if measure_memory { crate::vm_backend::native_memory::NativeMemory::profiled() } else { Default::default() },
            unsafe_execution: true, limits,
            instructions: 0, allocated_elements: 0,
        };
        budget.native_memory.generated = Some(Arc::new(self.clone()));
        let mut profile = VmAuthoringProfile::default();
        let value = crate::vm_backend::execute_program_profiled(program, program.entry, &[], 0,
            &mut budget, &mut None, Some(&mut profile), false, None, None).map_err(LlvmError::Runtime)?;
        let result = crate::vm_backend::expect_i64(value).map_err(LlvmError::Runtime)?;
        let native_memory = budget.native_memory.measurements.as_ref().map(|measurements| measurements.snapshot()).unwrap_or_default();
        Ok((result, LlvmExecutionProfile { instructions: budget.instructions,
            peak_call_depth: profile.peak_call_depth, recycled_tail_calls: profile.recycled_tail_calls, native_memory }))
    }
}
