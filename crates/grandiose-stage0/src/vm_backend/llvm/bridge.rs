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

fn vm_wrappers(module: &LlvmNativeModule) -> Result<VerifiedVmProgram, VmArtifactError> {
    let plan = module.plan();
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
        contract.extend_from_slice(&module.abi().fingerprint().as_bytes());
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
    super::super::verify_program(program)
}

struct GeneratedPlans {
    callbacks: BTreeMap<DefKey, Arc<CallbackPlan>>,
}

impl GeneratedPlans {
    fn new(module: &LlvmNativeModule) -> Result<Self, VmArtifactError> {
        let mut callbacks = BTreeMap::new();
        for definition in &module.plan().vm_functions {
            let function = &module.plan().program.program.functions[definition];
            let descriptors = function.nominal_copy_descriptors.clone().into();
            let result = super::super::return_type(function)?;
            callbacks.insert(
                *definition,
                Arc::new(CallbackPlan {
                    parameters: function.registers[..function.parameters as usize]
                        .iter()
                        .map(|ty| value_plan(ty, &descriptors))
                        .collect::<Result<_, _>>()?,
                    result: value_plan(&result, &descriptors)?,
                }),
            );
        }
        Ok(Self { callbacks })
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
    let program = vm_wrappers(&module)?;
    let plans = Arc::new(GeneratedPlans::new(&module)?);
    let contracts = imports_from_roots(
        &program.program,
        program.program.functions.keys().copied().collect(),
    )?;
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
    let result =
        execute_with_arguments(&program.program, program.program.entry, &[], 0, &mut budget)
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
    let transport_bytes = count
        .checked_mul(std::mem::size_of::<ScalarSlot>() + std::mem::size_of::<*const u8>())
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
    let mut arguments = Vec::with_capacity(count);
    for (index, slot) in values.iter_mut().enumerate() {
        let pointer = match call.binding.parameters[index] {
            ArgumentPlan::Owned(_) => unsafe { call.take_argument(index)? },
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
) -> u32 {
    // SAFETY: generated code calls only with its current synchronous context.
    let context = unsafe { &mut *context };
    let invocation = unsafe { &mut *context.mixed_context.cast::<MixedInvocation<'_, '_>>() };
    if invocation.failure.is_some() {
        return 1;
    }
    let outcome = catch_unwind(AssertUnwindSafe(|| unsafe {
        invoke_vm_checked(invocation, context, index, slots, result)
    }))
    .unwrap_or_else(|_| Err(super::error("generated native VM callback panicked")));
    match outcome {
        Ok(()) => 0,
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
) -> Result<(), VmArtifactError> {
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
    if invocation.call.budget.native_memory.callback_depth >= GENERATED_REENTRY_LIMIT {
        return Err(super::error("generated mixed-engine re-entry limit"));
    }
    invocation.call.budget.instructions = context.instructions;
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
    };
    let outcome = unsafe { callback.invoke(slots, plan.parameters.len(), result) };
    invocation.call.budget.limits.max_native_bytes = native_limit;
    context.instructions = invocation.call.budget.instructions;
    context.byte_limit = native_limit
        .saturating_sub(invocation.call.budget.native_memory.live_native_bytes() as u64)
        .min(LLVM_NATIVE_STACK_BYTES);
    outcome?;
    if context.live_bytes > context.byte_limit {
        return Err(super::error(
            "generated callback exceeded its shared memory budget",
        ));
    }
    Ok(())
}
