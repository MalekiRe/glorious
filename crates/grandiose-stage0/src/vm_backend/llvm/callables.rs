//! Authenticated resident operations within generated segments. Source Copy,
//! borrowing and byte transport use the shared resident/environment domain.
//! Construction, invocation and destruction are common runtime transitions.
//! No process code pointer is stored in a callable.

use super::{LlvmNativeModule, NativeContext};
use crate::vm_backend::{
    ExecutionBudget, VmArtifactError, VmInstruction as I,
    VmType, VmValue, copy_owned_value, native_memory::NativeLayout, native_storage::NativeHome,
    native_residents::ResidentScope,
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
    scopes: RefCell<Vec<ResidentScope>>,
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
            scopes: RefCell::new(vec![budget.native_memory.residents.scope()]),
        }
    }

    /// The domain, module and budget remain live at stable addresses for the
    /// complete generated segment. No Glorious call retains this native scope.
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

    unsafe fn reference(&self, function: u32, register: u32, slots: *const *const u8)
        -> Result<VmValue, VmArtifactError>
    {
        let layout = self.layout(function, register)?;
        let VmType::Reference { referent, unique, .. } = &layout.ty else {
            return Err(invalid("generated reference action has a non-reference slot"));
        };
        let (pointer, flags) = unsafe { self.slots(slots, 0) };
        if flags.is_null() || unsafe { *flags } != 1 {
            return Err(invalid("generated reference handle was moved out"));
        }
        unsafe { (&*self.budget).native_memory.residents.read_reference(pointer, referent, *unique)? }
            .ok_or_else(|| invalid("generated reference handle has no backing storage contract"))
    }

    /// These actions operate on the checked storage contract only. Payload
    /// loads and transfers remain generated machine instructions.
    unsafe fn reference_action(&self, context: &mut NativeContext, operation: u32, function: u32,
        pc: u32, slots: *const *const u8, result: *mut u8,
    ) -> Result<(), VmArtifactError> {
        let plan = self.module.plan();
        let key = plan.functions.get(function as usize).ok_or_else(|| invalid("unknown reference body"))?;
        let body = &plan.program.program.functions[key];
        let instruction = body.instructions.get(pc as usize).ok_or_else(|| invalid("unknown reference instruction"))?;
        let _accounting = unsafe { self.budget_scope(context)? };
        match (operation, instruction) {
            (4, I::Borrow { dst, src, fields, reborrow, .. }) => {
                let VmType::Reference { referent, unique, .. } = &body.registers[*dst as usize] else {
                    return Err(invalid("generated borrow has a non-reference result"));
                };
                let carrier = if *reborrow {
                    unsafe { self.reference(function, *src, slots)? }
                } else {
                    let (pointer, flags) = unsafe { self.slots(slots, 0) };
                    let layout = self.layout(function, *src)?;
                    let home = NativeHome::capture_loan(layout, pointer, flags, unsafe { &*self.budget })?;
                    VmValue::Resident(home)
                };
                // Formation is not a value read. Unique handles can restore an
                // absent resident; shared handles require its shell, not every
                // descendant. The shared origin producer checks this view
                // against the actual backing layout and initialization; a
                // reborrow can retain a previously weakened shared view.
                let value = crate::vm_backend::borrow_value(&[], &[], *src, &carrier,
                    fields, *unique, *reborrow, referent)?;
                unsafe { (&*self.budget).native_memory.residents.write_reference(result, &value, false, false)?; }
                Ok(())
            }
            (5 | 6, I::DerefCopy { dst, reference } | I::DerefMove { dst, reference }) => {
                let VmValue::Reference { target, fields, unique, referent } =
                    (unsafe { self.reference(function, *reference, slots)? }) else { unreachable!() };
                let moving = matches!(instruction, I::DerefMove { .. });
                if (moving && !unique) || (!moving && operation == 6) || referent != body.registers[*dst as usize] {
                    return Err(invalid("generated dereference has a different type or authority"));
                }
                if !target.native_initialized(&fields, false) {
                    return Err(invalid("generated dereference names a moved-out referent"));
                }
                if operation == 5 {
                    let (_, flags) = unsafe { self.slots(slots, 1) };
                    if flags.is_null() { return Err(invalid("generated dereference result lacks initialization flags")); }
                    for (index, path) in plan.frame_layouts[function as usize].paths[*dst as usize].iter().enumerate() {
                        let path = fields.iter().chain(path).copied().collect::<Vec<_>>();
                        unsafe { *flags.cast_mut().add(index) = u8::from(target.native_initialized(&path, false)); }
                    }
                } else {
                    let (pointer, layout) = target.native_project(&fields)?;
                    unsafe { &*self.budget }.native_memory.residents.clear(pointer.addr(), layout.memory.size());
                    target.replace_native_initialization(&fields, &BTreeSet::from([vec![]]))?;
                }
                Ok(())
            }
            (7, I::DerefStore { reference, src }) => {
                let VmValue::Reference { target, fields, unique, referent } =
                    (unsafe { self.reference(function, *reference, slots)? }) else { unreachable!() };
                if !unique || referent != body.registers[*src as usize] {
                    return Err(invalid("generated reference store has a different type or authority"));
                }
                let (_, flags) = unsafe { self.slots(slots, 1) };
                if flags.is_null() { return Err(invalid("generated reference store lacks source initialization flags")); }
                let holes = unsafe { self.holes(&plan.frame_layouts[function as usize].paths[*src as usize], flags)? };
                target.replace_native_initialization(&fields, &holes)
            }
            _ => Err(invalid("generated reference action does not match its checked instruction")),
        }
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
                4..=7 => domain.reference_action(context, operation, function, pc, slots, result),
                8 => {
                    let key = domain.module.plan().functions.get(function as usize).ok_or_else(|| invalid("unknown raw reference body"))?;
                    let body = &domain.module.plan().program.program.functions[key];
                    let Some(I::MemoryIntrinsic { primitive, .. }) = body.instructions.get(pc as usize) else {
                        return Err(invalid("raw reference action requires its unsafe instruction"));
                    };
                    if !matches!(primitive, crate::vm_backend::MemoryPrimitive::BorrowShared | crate::vm_backend::MemoryPrimitive::BorrowUnique) {
                        return Err(invalid("raw reference action requires an explicit raw borrow"));
                    }
                    let layout = domain.layout(function, register)?;
                    let crate::vm_backend::native_memory::NativeShape::Reference { referent, descriptors, unique } = &layout.shape else {
                        return Err(invalid("raw borrow result lacks a reference layout"));
                    };
                    let target = super::layout::concrete_layout(referent, descriptors).map_err(|_| invalid("raw borrow lacks a concrete referent"))?;
                    let (source, _) = domain.slots(slots, 0);
                    let pointer = source.cast::<*mut u8>().read();
                    let reference = (&*domain.budget).native_memory.raw_reference(pointer, target, *unique)?;
                    (&*domain.budget).native_memory.residents.write_reference(result, &reference, true, true)
                }
                9 => {
                    let frame = domain.module.plan().frame_layouts.get(function as usize).ok_or_else(|| invalid("unknown borrowed pattern frame"))?;
                    let plan = frame.pattern_references.get(register as usize).ok_or_else(|| invalid("unknown borrowed pattern layout"))?;
                    let VmType::Reference { unique, referent } = &plan.handle.ty else { unreachable!() };
                    let (pointer, _) = domain.slots(slots, 0);
                    let VmValue::Reference { target, fields, .. } = (&*domain.budget).native_memory.residents
                        .read_reference(pointer, referent, *unique)?.ok_or_else(|| invalid("borrowed pattern lacks a checked referent"))? else { unreachable!() };
                    for (index, path) in plan.paths.iter().enumerate() {
                        let path = fields.iter().chain(path).copied().collect::<Vec<_>>();
                        *result.add(index) = u8::from(target.native_initialized(&path, false));
                    }
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
    let residents = unsafe { &(*domain.budget).native_memory.residents };
    match operation {
        0 => residents.copy(source.addr(), destination.addr(), bytes as usize),
        1 => residents.clear(destination.addr(), bytes as usize),
        2 => domain.scopes.borrow_mut().push(residents.scope()),
        3 => {
            let scope = domain
                .scopes
                .borrow_mut()
                .pop()
                .expect("generated resident scope");
            drop(scope);
        }
        4 => domain
            .scopes
            .borrow_mut()
            .last_mut()
            .expect("generated resident scope")
            .track(destination.addr(), bytes as usize),
        _ => unreachable!("checked native transport operation"),
    }
    let budget = unsafe { &*domain.budget };
    context.byte_limit = budget
        .limits
        .max_native_bytes
        .saturating_sub(budget.native_memory.live_native_bytes() as u64)
        .min(super::LLVM_NATIVE_STACK_BYTES);
}
