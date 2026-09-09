//! Closed generated-code bindings over the existing shared native bridge.
//!
//! Unlike user-provided native imports these wrappers cannot bind arbitrary
//! implementations: the selected entries and VM callback bodies belong to one
//! immutable source/code/partition witness. This module is nested under
//! `native_bridge` so private runtime carriers do not become a public ABI.

use super::*;
use crate::vm_backend::llvm::{
    LLVM_NATIVE_STACK_BYTES, LlvmError, LlvmNativeModule, NativeContext,
};
use std::mem::MaybeUninit;

const GENERATED_CAPABILITY: &str = "grandiose.compiler.generated.llvm";
const GENERATED_REENTRY_LIMIT: u32 = 8;

#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct ScalarSlot([MaybeUninit<u8>; 16]);
impl ScalarSlot {
    fn new() -> Self {
        Self([MaybeUninit::uninit(); 16])
    }
    fn pointer(&mut self) -> *mut u8 {
        self.0.as_mut_ptr().cast()
    }
}

fn runtime_error(error: LlvmError) -> VmArtifactError {
    match error {
        LlvmError::Runtime(error) | LlvmError::VerifiedCode(error) => error,
        _ => super::error("generated native execution did not satisfy its linked ABI"),
    }
}

fn resident_types(
    parameters: &[VmType],
    result: &VmType,
    descriptors: &[VmNominalCopyDescriptor],
) -> Result<Vec<VmType>, VmArtifactError> {
    let mut pending = parameters.to_vec();
    pending.push(result.clone());
    let mut seen = BTreeSet::new();
    let mut residents = BTreeMap::new();
    while let Some(ty) = pending.pop() {
        let key = nominal_key(&ty);
        if !seen.insert(key.clone()) {
            continue;
        }
        if owned_resident(&ty) {
            residents.insert(key, ty.clone());
        }
        match ty {
            VmType::Tuple(fields) => pending.extend(fields),
            VmType::Reference { referent, .. }
            | VmType::RawPointer {
                pointee: referent, ..
            }
            | VmType::Array(referent)
            | VmType::FixedArray {
                element: referent, ..
            }
            | VmType::StaticData {
                element: referent, ..
            } => pending.push(*referent),
            VmType::Nominal {
                definition,
                arguments,
            } => {
                let descriptor = descriptors
                    .iter()
                    .find(|item| item.definition == definition && item.arguments == arguments)
                    .ok_or_else(|| {
                        super::error("generated native resident has no source layout descriptor")
                    })?;
                pending.extend(descriptor.variants.iter().flatten().cloned());
                pending.extend(arguments.into_iter().filter_map(|argument| match argument {
                    super::super::VmGenericArgument::Type(ty) => Some(ty),
                    _ => None,
                }));
            }
            VmType::Callable { .. } => {
                return Err(super::error(
                    "generated native callable slot ABI is not implemented",
                ));
            }
            _ => {}
        }
    }
    Ok(residents.into_values().collect())
}

/// Private execution representation, not portable verified bytecode. Replaced
/// bodies execute LLVM compiled from these exact original verified bodies;
/// unknown user host imports cannot supply their semantic transfer summaries.
fn vm_wrappers(
    plan: &crate::vm_backend::llvm::LlvmIrProgram,
) -> Result<CandidateVmProgram, VmArtifactError> {
    let mut program = plan.program.program.clone();
    // A generated wrapper is an explicit native authority boundary, even
    // when the original source signature was safe. Public safe admission is
    // checked against the unchanged original source graph, never this adapter.
    for function in program.functions.values_mut() {
        function.unsafe_execution = true;
    }
    for (definition, function) in &mut program.functions {
        if plan.vm_functions.contains(definition) {
            continue;
        }
        let Some(VmInstruction::DeclareResult { result, returns }) =
            function.instructions.first().cloned()
        else {
            return Err(super::error(
                "generated native wrapper has no source result contract",
            ));
        };
        let parameters = function.registers[..function.parameters as usize].to_vec();
        let mut contract = b"grandiose-compiler-owned-native-binding-v1".to_vec();
        contract.extend_from_slice(&plan.abi().fingerprint().as_bytes());
        contract.extend_from_slice(&definition.0.as_bytes());
        let source_contract = Digest::of_bytes(&contract);
        let mut resident_operations =
            resident_types(&parameters, &result, &function.nominal_copy_descriptors)?
                .into_iter()
                .map(|ty| {
                    let mut source = contract.clone();
                    encode_type(&ty, &mut source);
                    // Body ownership/destruction is executed by this exact source
                    // function, whose complete code is bound above. No unrelated
                    // external destructor implementation can be installed here.
                    VmNativeResident {
                        ty,
                        source_type: Digest::of_bytes(&source),
                        destructor: None,
                    }
                })
                .collect::<Vec<_>>();
        resident_operations.sort_by_key(|resident| resident.source_type);
        let dst = function.parameters;
        function.registers = parameters.clone();
        function.registers.push(result.clone());
        function.instructions = vec![
            VmInstruction::DeclareResult {
                result: result.clone(),
                returns,
            },
            VmInstruction::HostCallOwned {
                dst,
                capability: GENERATED_CAPABILITY.into(),
                symbol: definition.0.to_string(),
                source_contract,
                parameters,
                result,
                resident_operations,
                arguments: (0..dst).collect(),
            },
            if returns {
                VmInstruction::Return { value: dst }
            } else {
                VmInstruction::Trap
            },
        ];
    }
    // Only ordinary source edges are hidden behind these local wrappers.
    // The private linker below includes the originally checked complete graph
    // as callback roots; no unused external host capability is introduced.
    program.host_capabilities =
        super::super::reachable_host_capabilities(program.entry, &program.functions);
    program.fingerprint = program.computed_fingerprint();
    // Check every ordinary graph/ABI/control invariant of the adapter. Only
    // the semantic body summaries come from the unchanged source graph: a
    // generated HostCall is this same checked source function, not an unknown
    // external implementation. Keep the original VerifiedVmProgram intact;
    // the adapted bytecode is never exposed or serialized as verified code.
    super::super::validate_program(&program, Some(&plan.program))?;
    Ok(program)
}

struct GeneratedPlans {
    callbacks: BTreeMap<DefKey, Arc<CallbackPlan>>,
    initialization: BTreeMap<DefKey, Vec<Vec<Vec<u32>>>>,
    parameters: BTreeMap<DefKey, Vec<Arc<NativeLayout>>>,
}

impl GeneratedPlans {
    fn new(module: &LlvmNativeModule) -> Result<Self, VmArtifactError> {
        let mut callbacks = BTreeMap::new();
        let mut initialization = BTreeMap::new();
        let mut parameter_plans = BTreeMap::new();
        for definition in &module.plan().functions {
            let function = &module.plan().program.program.functions[definition];
            let descriptors = function.nominal_copy_descriptors.clone().into();
            let parameters = function.registers[..function.parameters as usize]
                .iter()
                .map(|ty| value_plan(ty, &descriptors))
                .collect::<Result<Vec<_>, _>>()?;
            initialization.insert(
                *definition,
                parameters
                    .iter()
                    .map(|layout| {
                        crate::vm_backend::llvm::initialization_paths(layout).map_err(runtime_error)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            );
            parameter_plans.insert(*definition, parameters.clone());
            if !module.plan().vm_functions.contains(definition) {
                continue;
            }
            let result = super::super::return_type(function)?;
            callbacks.insert(
                *definition,
                Arc::new(CallbackPlan {
                    parameters,
                    result: value_plan(&result, &descriptors)?,
                }),
            );
        }
        Ok(Self {
            callbacks,
            initialization,
            parameters: parameter_plans,
        })
    }
}

pub(in crate::vm_backend) unsafe fn run(
    module: LlvmNativeModule,
    limits: VmExecutionLimits,
) -> Result<i64, LlvmError> {
    module.plan().validate_abi(module.abi())?;
    // VM/native re-entry uses real native frames. This zero-argument closed
    // graph starts its own allocation domain on a known-size worker stack;
    // no borrowed host pointer or thread-bound VM carrier crosses the spawn.
    let worker = std::thread::Builder::new()
        .name("grandiose-generated-native".into())
        .stack_size(16 * 1024 * 1024)
        .spawn(move || unsafe { run_local(module, limits) })?;
    worker
        .join()
        .map_err(|_| LlvmError::Runtime(super::error("generated native worker panicked")))?
}

unsafe fn run_local(module: LlvmNativeModule, limits: VmExecutionLimits) -> Result<i64, LlvmError> {
    let environment = crate::vm_backend::float_env::FloatEnvironment::enter().map_err(LlvmError::Runtime)?;
    let result = unsafe { run_local_with_float_environment(module, limits) };
    environment.restore().map_err(LlvmError::Runtime)?;
    result
}

unsafe fn run_local_with_float_environment(module: LlvmNativeModule, limits: VmExecutionLimits) -> Result<i64, LlvmError> {
    let program = vm_wrappers(module.plan())?;
    let plans = Arc::new(GeneratedPlans::new(&module)?);
    let contracts = imports_from_roots(&program, program.functions.keys().copied().collect())?;
    let mut imports = VmNativeImports::default();
    for contract in &contracts {
        if contract.capability != GENERATED_CAPABILITY {
            return Err(LlvmError::AbiMismatch(
                "mixed graph contains an external native import",
            ));
        }
        let index = module
            .plan()
            .functions
            .iter()
            .position(|definition| definition.0.to_string() == contract.symbol)
            .ok_or(LlvmError::AbiMismatch(
                "generated native binding is absent from the checked graph",
            ))?;
        let selected = module.clone();
        let selected_plans = plans.clone();
        // SAFETY: the implementation is our generated code for this exact
        // source/ABI witness, not a user closure selected by symbol spelling.
        unsafe {
            imports.insert(contract.clone(), move |call| {
                invoke_native(call, &selected, &selected_plans, index)
            })?;
        }
        // Not serialized, not selected by capability spelling, and not
        // exposed by public native registration. Only this exact generated
        // implementation understands the sealed initialization sidecar ABI.
        imports
            .bindings
            .get_mut(&(contract.capability.clone(), contract.symbol.clone()))
            .expect("just installed compiler-owned binding")
            .initialization_sidecars = true;
    }
    let linked = imports.link_contracts(contracts)?;
    let mut native_memory = NativeMemory::default();
    native_memory.imports = Some(linked);
    let mut budget = ExecutionBudget {
        native_memory,
        unsafe_execution: true,
        limits,
        instructions: 0,
        allocated_elements: 0,
    };
    let result = execute_with_arguments(&program, program.entry, &[], 0, &mut budget)
        .map_err(LlvmError::Runtime)?;
    expect_i64(result).map_err(LlvmError::Runtime)
}

struct MixedInvocation<'a, 'vm> {
    call: &'a mut VmNativeCall<'vm>,
    module: &'a LlvmNativeModule,
    plans: &'a GeneratedPlans,
    failure: Option<VmArtifactError>,
}

fn invoke_native(
    call: &mut VmNativeCall<'_>,
    module: &LlvmNativeModule,
    plans: &GeneratedPlans,
    index: usize,
) -> Result<(), VmArtifactError> {
    let count = call.binding.parameters.len();
    let initialization = &plans.initialization[&module.plan().functions[index]];
    let flag_bytes = call
        .binding
        .parameters
        .iter()
        .enumerate()
        .filter(|(_, plan)| matches!(plan, ArgumentPlan::Owned(_)))
        .map(|(index, _)| initialization[index].len())
        .sum::<usize>();
    let transport_bytes = count
        .checked_mul(
            std::mem::size_of::<ScalarSlot>()
                + 2 * std::mem::size_of::<*const u8>()
                + std::mem::size_of::<Vec<u8>>(),
        )
        .and_then(|bytes| bytes.checked_add(flag_bytes))
        .and_then(|bytes| bytes.checked_add(std::mem::size_of::<ScalarSlot>()))
        .ok_or_else(|| super::error("generated native slot table size overflow"))?
        as u64;
    if transport_bytes > call.budget.limits.max_native_allocation_bytes {
        return Err(super::error(
            "generated native slot table exceeds the allocation limit",
        ));
    }
    call.budget
        .reserve_value("generated native argument slots", count)?;
    call.budget
        .reserve_value("generated initialization sidecars", flag_bytes)?;
    let mut context = NativeContext::new(call.budget.limits);
    context.instructions = call.budget.instructions;
    context.byte_limit = call
        .budget
        .limits
        .max_native_bytes
        .saturating_sub(call.budget.native_memory.live_native_bytes() as u64)
        .min(LLVM_NATIVE_STACK_BYTES);
    context.live_bytes = transport_bytes;
    if context.live_bytes > context.byte_limit {
        return Err(super::error(
            "generated native ABI slots exceed the memory budget",
        ));
    }
    context.depth_limit = call
        .budget
        .limits
        .max_call_depth
        .saturating_sub(call.depth.saturating_add(1));
    let mut values = vec![ScalarSlot::new(); count];
    let mut flags = vec![Vec::<u8>::new(); count];
    let mut arguments = Vec::with_capacity(2 * count);
    for (index, slot) in values.iter_mut().enumerate() {
        let pointer = match &call.binding.parameters[index] {
            ArgumentPlan::Owned(layout) => {
                let register = call.arguments[index];
                let Some(VmValue::Resident(home)) = call.registers[register as usize].as_ref()
                else {
                    return Err(super::error(
                        "generated owned argument has no resident home",
                    ));
                };
                if home.ty() != &layout.ty || !home.is_initialized(&[]) {
                    return Err(super::error(
                        "generated owned argument has invalid root initialization",
                    ));
                }
                flags[index].reserve(initialization[index].len());
                for path in &initialization[index] {
                    call.budget.tick()?;
                    flags[index].push(u8::from(home.is_initialized(path)));
                }
                home.expose_address();
                let pointer = home.project(&[])?.0;
                call.registers[register as usize] = None;
                pointer
            }
            ArgumentPlan::Value(_) => {
                let pointer = slot.pointer();
                unsafe {
                    call.write_argument(index, pointer)?;
                }
                pointer
            }
            ArgumentPlan::Callback(_) => {
                return Err(super::error(
                    "generated native callable parameter ABI is not implemented",
                ));
            }
        };
        arguments.push(pointer.cast_const());
        arguments.push(if flags[index].is_empty() {
            std::ptr::null()
        } else {
            flags[index].as_ptr()
        });
    }
    let owned_result = call.result_home.is_some();
    let mut scalar_result = ScalarSlot::new();
    let result = if owned_result {
        unsafe { call.result_pointer()? }
    } else {
        scalar_result.pointer()
    };
    let mut invocation = MixedInvocation {
        call,
        module,
        plans,
        failure: None,
    };
    context.mixed_context = (&mut invocation as *mut MixedInvocation<'_, '_>).cast();
    context.invoke_vm = Some(invoke_vm);
    context.instructions = invocation.call.budget.instructions;
    let mut allocation = crate::vm_backend::llvm::memory::AllocationContext::new(
        &mut invocation.call.budget.native_memory,
        invocation.call.budget.limits.max_native_bytes,
    );
    // SAFETY: the shared domain and this binding remain at stable addresses
    // throughout this synchronous native call and all VM callbacks.
    unsafe {
        allocation.install(&mut context);
    }
    // SAFETY: every argument/result has been prepared using the exact linked
    // slot plan, with owned arguments retaining their original backing address.
    let status = unsafe { module.invoke_native(index, &mut context, arguments.as_ptr(), result) };
    invocation.call.budget.instructions = context.instructions;
    if let Some(error) = allocation.failure {
        return Err(error);
    }
    if let Some(failure) = invocation.failure {
        return Err(failure);
    }
    context
        .result(status)
        .map_err(|error| match runtime_error(error) {
            VmArtifactError::CallDepthLimit { .. } => VmArtifactError::CallDepthLimit {
                limit: invocation.call.budget.limits.max_call_depth,
            },
            error => error,
        })?;
    if context.depth != 0 || context.live_bytes != transport_bytes {
        return Err(super::error(
            "generated native call did not release its activation accounting",
        ));
    }
    if owned_result {
        unsafe { invocation.call.finish_result() }
    } else {
        unsafe { invocation.call.set_result_from(result) }
    }
}

unsafe extern "C" fn invoke_vm(
    context: *mut NativeContext,
    index: u32,
    slots: *const *const u8,
    result: *mut u8,
    tail_slots: *mut *const u8,
    tail_storage: *mut u8,
    tail_next: *mut u32,
) -> u32 {
    // SAFETY: generated code calls only with its current synchronous context.
    let context = unsafe { &mut *context };
    let invocation = unsafe { &mut *context.mixed_context.cast::<MixedInvocation<'_, '_>>() };
    if invocation.failure.is_some() {
        return 1;
    }
    invocation.call.budget.instructions = context.instructions;
    let outcome = crate::vm_backend::float_env::with_profile(|| {
        catch_unwind(AssertUnwindSafe(|| unsafe {
            invoke_vm_checked(
                invocation,
                context,
                index,
                slots,
                result,
                tail_slots,
                tail_storage,
                tail_next,
            )
        }))
        .unwrap_or_else(|_| Err(super::error("generated native VM callback panicked")))
    });
    context.instructions = invocation.call.budget.instructions;
    match outcome {
        Ok(tail) => {
            if tail {
                2
            } else {
                0
            }
        }
        Err(error) => {
            invocation.failure = Some(error);
            1
        }
    }
}

unsafe fn invoke_vm_checked(
    invocation: &mut MixedInvocation<'_, '_>,
    context: &mut NativeContext,
    index: u32,
    slots: *const *const u8,
    result: *mut u8,
    tail_slots: *mut *const u8,
    tail_storage: *mut u8,
    tail_next: *mut u32,
) -> Result<bool, VmArtifactError> {
    let definition = invocation
        .module
        .plan()
        .functions
        .get(index as usize)
        .ok_or_else(|| super::error("generated callback has an invalid function index"))?;
    let plan = invocation
        .plans
        .callbacks
        .get(definition)
        .ok_or_else(|| super::error("generated callback target is not in the VM partition"))?
        .clone();
    let paths = &invocation.plans.initialization[definition];
    invocation
        .call
        .budget
        .reserve_value("generated callback slot pairs", 2 * plan.parameters.len())?;
    let mut arguments = Vec::with_capacity(plan.parameters.len());
    let mut holes = Vec::with_capacity(plan.parameters.len());
    for (index, paths) in paths.iter().enumerate() {
        arguments.push(unsafe { slots.add(2 * index).read() });
        let flags = unsafe { slots.add(2 * index + 1).read() };
        holes.push(unsafe { read_initialization(flags, paths, invocation.call.budget)? });
    }
    if invocation.call.budget.native_memory.callback_depth >= GENERATED_REENTRY_LIMIT {
        return Err(super::error("generated mixed-engine re-entry limit"));
    }
    let native_limit = invocation.call.budget.limits.max_native_bytes;
    // VM allocations and further native calls see the still-live generated
    // frames as unavailable bytes in this same allocation domain.
    invocation.call.budget.limits.max_native_bytes =
        native_limit
            .checked_sub(context.live_bytes)
            .ok_or_else(|| super::error("generated callback exceeds the shared memory budget"))?;
    let mut callback = CallbackContext {
        call: invocation.call,
        callee: *definition,
        captures: RuntimeCaptureEnvironment::new(vec![]),
        plan: plan.clone(),
        additional_depth: context.depth,
        argument_holes: Some(&holes),
    };
    let mut boundary = GeneratedTailBoundary {
        module: invocation.module,
        plans: invocation.plans,
        slots: tail_slots,
        storage: tail_storage,
        next: tail_next,
    };
    let outcome = unsafe {
        callback.invoke_with_tail_boundary(
            arguments.as_ptr(),
            plan.parameters.len(),
            result,
            Some(&mut boundary),
        )
    };
    invocation.call.budget.limits.max_native_bytes = native_limit;
    context.instructions = invocation.call.budget.instructions;
    context.byte_limit = native_limit
        .saturating_sub(invocation.call.budget.native_memory.live_native_bytes() as u64)
        .min(LLVM_NATIVE_STACK_BYTES);
    let tail = outcome?;
    if context.live_bytes > context.byte_limit {
        return Err(super::error(
            "generated callback exceeded its shared memory budget",
        ));
    }
    Ok(tail)
}

/// Only generated thunks construct this boundary, using dispatcher-owned
/// packets sized by the same immutable plan that emitted the machine code.
/// It never invokes the next engine while the ending VM activation is live.
struct GeneratedTailBoundary<'a> {
    module: &'a LlvmNativeModule,
    plans: &'a GeneratedPlans,
    slots: *mut *const u8,
    storage: *mut u8,
    next: *mut u32,
}

impl super::super::RuntimeTailBoundary for GeneratedTailBoundary<'_> {
    fn transfer(
        &mut self,
        callee: DefKey,
        registers: &mut RuntimeRegisters,
        arguments: &[u32],
        budget: &mut ExecutionBudget,
    ) -> Result<bool, VmArtifactError> {
        let plan = self.module.plan();
        if plan.vm_functions.contains(&callee) {
            return Ok(false);
        }
        let index = plan
            .functions
            .iter()
            .position(|key| *key == callee)
            .ok_or_else(|| super::error("generated tail target is absent from its code witness"))?;
        let function = &plan.program.program.functions[&callee];
        if arguments.len() != function.parameters as usize {
            return Err(super::error("generated tail argument arity mismatch"));
        }
        let packet = &plan.tail_packets[index];
        let paths = &self.plans.initialization[&callee];
        for (index, argument) in arguments.iter().enumerate() {
            budget.tick()?;
            let layout = &self.plans.parameters[&callee][index];
            let value =
                registers[*argument as usize]
                    .as_ref()
                    .ok_or(VmArtifactError::ReadBeforeWrite {
                        register: *argument,
                    })?;
            let data = unsafe { self.storage.add(packet.data_offsets[index]) };
            let flags = unsafe { self.storage.add(packet.initialization_offsets[index]) };
            check_slot(&layout, data)?;
            if let VmValue::Resident(home) = value {
                if home.ty() != &layout.ty || !home.is_initialized(&[]) {
                    return Err(super::error(
                        "generated tail resident has an invalid layout or root",
                    ));
                }
                for (offset, path) in paths[index].iter().enumerate() {
                    budget.tick()?;
                    unsafe {
                        flags.add(offset).write(u8::from(home.is_initialized(path)));
                    }
                }
                unsafe {
                    home.write_bytes_with_sidecar(data)?;
                }
            } else {
                // Scalar/reference slots retain real pointer values. This
                // rejects any unmaterialized frame-relative reference rather
                // than serializing a register coordinate as native authority.
                unsafe {
                    layout.write(data, value.clone(), budget)?;
                }
                for offset in 0..paths[index].len() {
                    budget.tick()?;
                    unsafe {
                        flags.add(offset).write(1);
                    }
                }
            }
            unsafe {
                self.slots.add(2 * index).write(data.cast_const());
                self.slots.add(2 * index + 1).write(flags.cast_const());
            }
        }
        unsafe {
            self.next.write(index as u32);
        }
        Ok(true)
    }
}

unsafe fn read_initialization(
    flags: *const u8,
    paths: &[Vec<u32>],
    budget: &mut ExecutionBudget,
) -> Result<BTreeSet<Vec<u32>>, VmArtifactError> {
    if flags.is_null() {
        return Ok(BTreeSet::new());
    }
    budget.reserve_value("generated callback initialization", paths.len())?;
    let flags = unsafe { std::slice::from_raw_parts(flags, paths.len()) };
    let mut holes = BTreeSet::new();
    for (path, flag) in paths.iter().zip(flags) {
        budget.tick()?;
        match *flag {
            0 if !path.is_empty() => {
                holes.insert(path.clone());
            }
            1 if !(0..path.len()).any(|length| holes.contains(&path[..length])) => {}
            _ => {
                return Err(super::error(
                    "generated argument has invalid initialization sidecar",
                ));
            }
        }
    }
    Ok(holes)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_adapter_uses_exact_source_semantics_without_certifying_portable_host_code() {
        use crate::{
            CompilationMode, CompilationRequest, CompilerBuildIdentity, LogicalPath, PackageKey,
            SourceInput, StageZeroCompiler,
        };
        let package = PackageKey("native-tail-proof@0.1.0".into());
        let source = "fn pure(value: i64) -> i64 { value - 1 }
            fn native_end(value: &mut i64) -> i64 { *value }
            fn vm_relay(value: &mut i64) -> i64 {
                let marker = 41001; let ignored = pure(1); tail native_end(value)
            }
            pub fn main() -> i64 { let mut value = 42; vm_relay(&mut value) }";
        let input = CompilationRequest {
            build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"native-tail-proof")),
            mode: CompilationMode::Build,
            root_package: package.clone(),
            sources: vec![SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            )],
            target: "stage0-vm".into(),
            semantic_options: Default::default(),
            codegen_options: Default::default(),
            capability_manifest: vec![],
            runtime_manifest: None,
        };
        let ir = StageZeroCompiler::new()
            .compile_llvm_partitioned(
                input,
                crate::vm_backend::llvm::LlvmTarget::host().unwrap(),
                |function| {
                    function.instructions.iter().any(|instruction| {
                        matches!(instruction, VmInstruction::ConstI64 { value: 41001, .. })
                    })
                },
            )
            .unwrap();
        let original = ir.vm_program().canonical_bytes();
        let mut adapter = vm_wrappers(&ir).unwrap();
        assert!(matches!(
            super::super::super::verify_program(adapter.clone()),
            Err(VmArtifactError::UnprovenTailCarrier { .. })
        ));
        assert_eq!(ir.vm_program().canonical_bytes(), original);
        assert_eq!(ir.vm_program().run_i64().unwrap(), 42);

        // Source-derived semantics do not waive a single adapter ABI check.
        let function = adapter
            .functions
            .values_mut()
            .find(|function| {
                function
                    .instructions
                    .iter()
                    .any(|instruction| matches!(instruction, VmInstruction::HostCallOwned { .. }))
            })
            .unwrap();
        let instruction = function
            .instructions
            .iter_mut()
            .find(|instruction| matches!(instruction, VmInstruction::HostCallOwned { .. }))
            .unwrap();
        let VmInstruction::HostCallOwned { result, .. } = instruction else {
            unreachable!()
        };
        *result = VmType::Tuple(vec![VmType::Bool, VmType::Bool]);
        adapter.fingerprint = adapter.computed_fingerprint();
        assert!(super::super::super::validate_program(&adapter, Some(&ir.program)).is_err());
    }

    fn budget() -> ExecutionBudget {
        ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: Default::default(),
            instructions: 0,
            allocated_elements: 0,
        }
    }

    #[test]
    fn generated_initialization_sidecars_validate_roots_bits_and_dead_parents() {
        let paths = vec![vec![], vec![0], vec![0, 0], vec![1]];
        for flags in [[0, 0, 0, 0], [1, 2, 1, 1], [1, 0, 1, 1]] {
            assert!(
                unsafe { read_initialization(flags.as_ptr(), &paths, &mut budget()) }.is_err(),
                "{flags:?}"
            );
        }
        assert_eq!(
            unsafe { read_initialization([1, 0, 0, 1].as_ptr(), &paths, &mut budget()) }.unwrap(),
            BTreeSet::from([vec![0], vec![0, 0]])
        );
        assert!(
            unsafe { read_initialization(std::ptr::null(), &paths, &mut budget()) }
                .unwrap()
                .is_empty()
        );
        let mut limited = budget();
        limited.limits.max_instructions = 0;
        assert!(matches!(
            unsafe { read_initialization([1, 1, 1, 1].as_ptr(), &paths, &mut limited) },
            Err(VmArtifactError::InstructionLimit { limit: 0 })
        ));
    }

    #[test]
    fn public_native_registration_cannot_enable_partial_owner_transport_by_name() {
        let contract = VmNativeImport {
            abi: VmNativeAbi::current(),
            capability: GENERATED_CAPABILITY.into(),
            symbol: "spoofed-generated-entry".into(),
            source_contract: Digest::of_bytes(b"unrelated source"),
            parameters: vec![],
            result: VmType::Unit,
            nominals: vec![],
            residents: vec![],
        };
        let mut imports = VmNativeImports::default();
        unsafe { imports.insert(contract.clone(), |_| Ok(())) }.unwrap();
        let linked = imports.link_contracts(vec![contract]).unwrap();
        assert!(
            !linked.imports[GENERATED_CAPABILITY]["spoofed-generated-entry"]
                .initialization_sidecars
        );
    }
}
