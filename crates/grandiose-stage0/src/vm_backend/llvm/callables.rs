//! Authenticated callable residents for generated code. Construction, source
//! Copy and capture loans use the VM's existing resident/environment domain;
//! invocation and destruction dispatch to the selected generated machine code.
//! No bytecode interpreter or process code pointer is stored in a callable.

use super::{LlvmNativeModule, NativeContext};
use crate::vm_backend::{
    ExecutionBudget, RuntimeCaptureEnvironment, VmArtifactError, VmCaptureMode, VmInstruction as I,
    VmType, VmValue, copy_owned_value, native_memory::NativeLayout, native_storage::NativeHome,
};
use std::{
    cell::RefCell,
    collections::BTreeSet,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::Arc,
};

pub(in crate::vm_backend) struct CallableContext<'a> {
    module: &'a LlvmNativeModule,
    budget: *mut ExecutionBudget,
    pub(in crate::vm_backend) failure: RefCell<Option<VmArtifactError>>,
    scopes: RefCell<Vec<Vec<(usize, usize)>>>,
}

fn invalid(message: &'static str) -> VmArtifactError {
    VmArtifactError::NativeAbi { message }
}

impl<'a> CallableContext<'a> {
    pub(in crate::vm_backend) fn new(
        module: &'a LlvmNativeModule,
        budget: &mut ExecutionBudget,
    ) -> Self {
        Self {
            module,
            budget,
            failure: RefCell::new(None),
            scopes: RefCell::new(vec![]),
        }
    }

    /// The domain, module and budget remain live at stable addresses for the
    /// complete synchronous invocation, including recursive generated calls.
    pub(in crate::vm_backend) unsafe fn install(&self, context: &mut NativeContext) {
        context.callable_context = (self as *const Self).cast_mut().cast();
        context.callable = Some(action);
        context.residents = Some(transport);
    }

    unsafe fn budget_scope<'ctx>(
        &self,
        context: &'ctx mut NativeContext,
    ) -> Result<NativeBudget<'ctx>, VmArtifactError> {
        let budget = unsafe { &mut *self.budget };
        let limit = budget.limits.max_native_bytes;
        budget.limits.max_native_bytes = limit
            .checked_sub(context.live_bytes)
            .ok_or_else(|| invalid("native callable runtime exceeds the shared byte budget"))?;
        budget.instructions = context.instructions;
        Ok(NativeBudget {
            budget: self.budget,
            context,
            limit,
        })
    }

    fn layout(&self, function: u32, register: u32) -> Result<Arc<NativeLayout>, VmArtifactError> {
        self.module
            .plan()
            .frame_layouts
            .get(function as usize)
            .and_then(|frame| frame.layouts.get(register as usize))
            .cloned()
            .ok_or_else(|| invalid("unknown native callable slot"))
    }

    unsafe fn slots(&self, slots: *const *const u8, index: usize) -> (*mut u8, *const u8) {
        unsafe {
            (
                (*slots.add(2 * index)).cast_mut(),
                *slots.add(2 * index + 1),
            )
        }
    }

    unsafe fn holes(
        &self,
        paths: &[Vec<u32>],
        flags: *const u8,
    ) -> Result<BTreeSet<Vec<u32>>, VmArtifactError> {
        if flags.is_null() {
            return Ok(BTreeSet::new());
        }
        let mut holes = BTreeSet::new();
        for (index, path) in paths.iter().enumerate() {
            match unsafe { *flags.add(index) } {
                0 => {
                    holes.insert(path.clone());
                }
                1 => {}
                _ => return Err(invalid("invalid capture initialization flag")),
            }
        }
        Ok(holes)
    }

    unsafe fn construct(
        &self,
        context: &mut NativeContext,
        function: u32,
        pc: u32,
        slots: *const *const u8,
        result: *mut u8,
    ) -> Result<(), VmArtifactError> {
        let plan = self.module.plan();
        let key = plan
            .functions
            .get(function as usize)
            .ok_or_else(|| invalid("unknown callable constructor body"))?;
        let body = &plan.program.program.functions[key];
        let Some(I::MakeCallable {
            dst,
            callee,
            captures,
            environment,
        }) = body.instructions.get(pc as usize)
        else {
            return Err(invalid(
                "native callable constructor is not a checked construction",
            ));
        };
        let _accounting = unsafe { self.budget_scope(context)? };
        let budget = unsafe { &mut *self.budget };
        budget.reserve_value("native callable captures", captures.len())?;
        let mut values = Vec::with_capacity(captures.len());
        let mut owned = Vec::with_capacity(captures.len());
        for (index, register) in captures.iter().enumerate() {
            let layout = self.layout(function, *register)?;
            let (pointer, flags) = unsafe { self.slots(slots, index) };
            let holes = unsafe {
                self.holes(
                    &plan.frame_layouts[function as usize].paths[*register as usize],
                    flags,
                )?
            };
            let source = unsafe {
                NativeHome::external_argument_with_holes(
                    layout.clone(),
                    pointer,
                    budget,
                    Some(&holes),
                )?
            };
            let destination = NativeHome::new(layout, budget)?;
            destination.store(&[], &VmValue::Resident(source), budget)?;
            values.push(VmValue::Resident(destination));
            owned.push(environment.as_ref().is_some_and(|environment| {
                matches!(
                    environment.captures[index].mode,
                    VmCaptureMode::Copy | VmCaptureMode::Move
                )
            }));
        }
        let value = VmValue::Callable {
            callee: *callee,
            captures: RuntimeCaptureEnvironment::with_ownership(values, owned),
            signature: body.registers[*dst as usize].clone(),
        };
        unsafe {
            budget.native_memory.callables.write(result, value)?;
        }
        Ok(())
    }

    unsafe fn invoke(
        &self,
        context: &mut NativeContext,
        function: u32,
        pc: u32,
        slots: *const *const u8,
        result: *mut u8,
        destroy: bool,
    ) -> Result<(), VmArtifactError> {
        let plan = self.module.plan();
        let key = plan
            .functions
            .get(function as usize)
            .ok_or_else(|| invalid("unknown callable invocation body"))?;
        let body = &plan.program.program.functions[key];
        let (register, arguments) = match body.instructions.get(pc as usize) {
            Some(
                I::CallIndirect {
                    callee, arguments, ..
                }
                | I::CallIndirectOwned {
                    callee, arguments, ..
                },
            ) if !destroy => (*callee, arguments.len()),
            Some(I::DestroyCallable { value, .. }) if destroy => (*value, 0),
            _ => {
                return Err(invalid(
                    "native callable operation is not a checked invocation",
                ));
            }
        };
        let (mut pointer, flags) = unsafe { self.slots(slots, 0) };
        if !flags.is_null() && unsafe { *flags } != 1 {
            return Err(invalid("native callable receiver was moved out"));
        }
        let mut ty = &body.registers[register as usize];
        if let VmType::Reference { referent, .. } = ty {
            pointer = unsafe { pointer.cast::<*mut u8>().read() };
            ty = referent;
        }
        if pointer.is_null() {
            return Err(invalid("null native callable receiver"));
        }
        let callable = unsafe { (&*self.budget).native_memory.callables.read(pointer, ty)? };
        let VmValue::Callable {
            callee, captures, ..
        } = callable
        else {
            unreachable!()
        };
        let target = if destroy {
            captures.live.set(false);
            plan.program
                .program
                .callable_environments
                .get(&callee)
                .and_then(|environment| environment.destructor)
        } else {
            Some(callee)
        };
        let Some(target) = target else {
            captures.take();
            return Ok(());
        };
        let target_index = plan
            .functions
            .binary_search(&target)
            .ok()
            .ok_or_else(|| invalid("native callable target is outside its sealed graph"))?;
        let callee_body = &plan.program.program.functions[&target];
        if callee_body.parameters as usize != captures.len() + arguments {
            return Err(invalid(
                "native callable environment does not match its target ABI",
            ));
        }
        let sidecars = plan.frame_layouts[target_index]
            .paths
            .iter()
            .take(captures.len())
            .map(Vec::len)
            .sum::<usize>();
        // Re-entry has real Rust/native stack frames as well as slot vectors.
        // Charge their finite bridge ceiling to the same activation budget.
        let transport_bytes = 16 * 1024
            + sidecars as u64
            + captures.len() as u64
                * (std::mem::size_of::<VmValue>() + std::mem::size_of::<Vec<u8>>()) as u64
            + callee_body.parameters as u64 * 2 * std::mem::size_of::<*const u8>() as u64;
        let activation =
            unsafe { NativeActivation::enter(context, self.budget, transport_bytes)? };
        let context = &mut *activation.context;
        let mut loan = CaptureLoan {
            environment: captures.clone(),
            values: captures.lend_to_invocation(),
            restore: !destroy,
        };
        let mut flags = Vec::with_capacity(loan.values.len());
        let mut incoming = Vec::with_capacity(2 * callee_body.parameters as usize);
        // Native and VM-created callables share the same homes. A scalar VM
        // capture is materialized once into that domain before lending it.
        {
            let _accounting = unsafe { self.budget_scope(context)? };
            let budget = unsafe { &mut *self.budget };
            budget.reserve_value("native capture loan", callee_body.parameters as usize)?;
            for (index, value) in loan.values.iter_mut().enumerate() {
                let layout = self.layout(target_index as u32, index as u32)?;
                if !matches!(value, VmValue::Resident(_)) {
                    let home = NativeHome::new(layout.clone(), budget)?;
                    home.store(&[], value, budget)?;
                    *value = VmValue::Resident(home);
                }
                let VmValue::Resident(home) = value else {
                    unreachable!()
                };
                let paths = &plan.frame_layouts[target_index].paths[index];
                budget.reserve_value("native capture initialization", paths.len())?;
                flags.push(
                    paths
                        .iter()
                        .map(|path| u8::from(home.is_initialized(path)))
                        .collect::<Vec<_>>(),
                );
                incoming.push(home.pointer().cast_const());
                incoming.push(flags.last().unwrap().as_ptr());
            }
            for index in 0..arguments {
                let (pointer, flags) = unsafe { self.slots(slots, index + 1) };
                incoming.extend([pointer.cast_const(), flags]);
            }
        }
        // No mutable Rust reference to the shared budget crosses re-entry.
        // Source instructions, including the destructor, execute in LLVM.
        let status = unsafe {
            self.module
                .invoke_native(target_index, context, incoming.as_ptr(), result)
        };
        let _accounting = unsafe { self.budget_scope(context)? };
        let budget = unsafe { &mut *self.budget };
        if !destroy {
            for (index, (value, flags)) in loan.values.iter().zip(&flags).enumerate() {
                let VmValue::Resident(home) = value else {
                    unreachable!()
                };
                let holes = unsafe {
                    self.holes(
                        &plan.frame_layouts[target_index].paths[index],
                        flags.as_ptr(),
                    )?
                };
                unsafe {
                    home.initialize_native_with_holes(budget, Some(&holes))?;
                }
            }
        }
        if status != 0 {
            return Err(invalid("generated callable invocation failed"));
        }
        Ok(())
    }
}

/// Temporarily reserve the still-live generated stack against the same heap
/// budget. The raw pointers are used only synchronously, never over re-entry.
struct NativeBudget<'a> {
    budget: *mut ExecutionBudget,
    context: &'a mut NativeContext,
    limit: u64,
}
impl Drop for NativeBudget<'_> {
    fn drop(&mut self) {
        let budget = unsafe { &mut *self.budget };
        let context = &mut *self.context;
        budget.limits.max_native_bytes = self.limit;
        context.instructions = budget.instructions;
        context.byte_limit = self
            .limit
            .saturating_sub(budget.native_memory.live_native_bytes() as u64)
            .min(super::LLVM_NATIVE_STACK_BYTES);
    }
}

struct NativeActivation<'a> {
    context: &'a mut NativeContext,
    budget: *mut ExecutionBudget,
    bytes: u64,
}
impl<'a> NativeActivation<'a> {
    unsafe fn enter(
        context: &'a mut NativeContext,
        budget: *mut ExecutionBudget,
        bytes: u64,
    ) -> Result<Self, VmArtifactError> {
        let total = context
            .live_bytes
            .checked_add(bytes)
            .filter(|total| *total <= context.byte_limit)
            .ok_or_else(|| {
                invalid("native callable activation exceeds the shared stack/byte budget")
            })?;
        context.live_bytes = total;
        Ok(Self {
            context,
            budget,
            bytes,
        })
    }
}
impl Drop for NativeActivation<'_> {
    fn drop(&mut self) {
        let context = &mut *self.context;
        let budget = unsafe { &*self.budget };
        context.live_bytes -= self.bytes;
        context.byte_limit = budget
            .limits
            .max_native_bytes
            .saturating_sub(budget.native_memory.live_native_bytes() as u64)
            .min(super::LLVM_NATIVE_STACK_BYTES);
    }
}

struct CaptureLoan {
    environment: Arc<RuntimeCaptureEnvironment>,
    values: Vec<VmValue>,
    restore: bool,
}
impl Drop for CaptureLoan {
    fn drop(&mut self) {
        if self.restore {
            *self.environment.values.borrow_mut() = std::mem::take(&mut self.values);
        }
    }
}

unsafe extern "C" fn action(
    context: *mut NativeContext,
    operation: u32,
    function: u32,
    pc: u32,
    register: u32,
    slots: *const *const u8,
    result: *mut u8,
) -> u32 {
    let context = unsafe { &mut *context };
    let domain = unsafe { &*context.callable_context.cast::<CallableContext<'_>>() };
    if domain.failure.borrow().is_some() {
        return 1;
    }
    let outcome = crate::vm_backend::float_env::with_profile(|| {
        catch_unwind(AssertUnwindSafe(|| unsafe {
            match operation {
                0 => domain.construct(context, function, pc, slots, result),
                1 | 2 => domain.invoke(context, function, pc, slots, result, operation == 2),
                3 => {
                    let layout = domain.layout(function, register)?;
                    let (source, flags) = domain.slots(slots, 0);
                    let paths = &domain.module.plan().frame_layouts[function as usize].paths
                        [register as usize];
                    if !domain.holes(paths, flags)?.is_empty() {
                        return Err(invalid(
                            "native source Copy requires an initialized callable value",
                        ));
                    }
                    let _accounting = domain.budget_scope(context)?;
                    let budget = &mut *domain.budget;
                    let value = layout.read(source, budget)?;
                    let value = copy_owned_value(&value, budget)?;
                    layout.write(result, value, budget)?;
                    Ok(())
                }
                _ => Err(invalid("unknown generated callable operation")),
            }
        }))
        .unwrap_or_else(|_| Err(invalid("generated callable runtime panicked")))
    });
    let budget = unsafe { &*domain.budget };
    context.byte_limit = budget
        .limits
        .max_native_bytes
        .saturating_sub(budget.native_memory.live_native_bytes() as u64)
        .min(super::LLVM_NATIVE_STACK_BYTES);
    match outcome {
        Ok(()) => 0,
        Err(error) => {
            if domain.failure.borrow().is_none() {
                *domain.failure.borrow_mut() = Some(error);
            }
            1
        }
    }
}

/// Byte transport maintains leases, never source Copy or source destruction.
/// Scope records contain only compiler-owned stack regions; cleanup never reads
/// expired stack bytes and never releases an unrelated backing allocation.
unsafe extern "C" fn transport(
    context: *mut NativeContext,
    operation: u32,
    destination: *mut u8,
    source: *const u8,
    bytes: u64,
) {
    let context = unsafe { &mut *context };
    let domain = unsafe { &*context.callable_context.cast::<CallableContext<'_>>() };
    let residents = unsafe { &(*domain.budget).native_memory.callables };
    match operation {
        0 => residents.copy(source.addr(), destination.addr(), bytes as usize),
        1 => residents.clear(destination.addr(), bytes as usize),
        2 => domain.scopes.borrow_mut().push(vec![]),
        3 => {
            let regions = domain
                .scopes
                .borrow_mut()
                .pop()
                .expect("generated resident scope");
            for (address, bytes) in regions {
                residents.clear(address, bytes);
            }
        }
        4 => domain
            .scopes
            .borrow_mut()
            .last_mut()
            .expect("generated resident scope")
            .push((destination.addr(), bytes as usize)),
        _ => unreachable!("checked native transport operation"),
    }
    let budget = unsafe { &*domain.budget };
    context.byte_limit = budget
        .limits
        .max_native_bytes
        .saturating_sub(budget.native_memory.live_native_bytes() as u64)
        .min(super::LLVM_NATIVE_STACK_BYTES);
}
