//! Allocation-domain runtime calls for generated code. This is an allocator
//! binding, not execution of VM memory instructions or private VM values.

use super::{LLVM_NATIVE_STACK_BYTES, NativeContext};
use crate::vm_backend::{
    VmArtifactError,
    native_memory::{NativeMemory, memory_error},
};
use grandiose_runtime::memory::MemoryLayout;
use std::{
    ffi::c_void,
    panic::{AssertUnwindSafe, catch_unwind},
};

pub(in crate::vm_backend) struct AllocationContext {
    memory: *mut NativeMemory,
    total_limit: u64,
    pub(in crate::vm_backend) failure: Option<VmArtifactError>,
}

impl AllocationContext {
    /// The raw pointer avoids retaining a Rust reference while a synchronous
    /// VM callback temporarily accesses this same allocation domain. It is
    /// dereferenced only during the allocator call, never concurrently.
    pub(in crate::vm_backend) fn new(memory: &mut NativeMemory, total_limit: u64) -> Self {
        Self {
            memory,
            total_limit,
            failure: None,
        }
    }

    /// # Safety
    /// This context and its memory domain must remain at stable addresses until
    /// all synchronous generated calls using `context` have returned.
    pub(in crate::vm_backend) unsafe fn install(&mut self, context: &mut NativeContext) {
        context.allocation_context = (self as *mut Self).cast::<c_void>();
        context.allocate = Some(allocate);
    }
}

unsafe extern "C" fn allocate(
    context: *mut NativeContext,
    operation: u32,
    pointer: *mut u8,
    old_size: u64,
    alignment: u64,
    size: u64,
    result: *mut *mut u8,
) -> u32 {
    // SAFETY: only our ABI-checked generated code supplies this current context.
    let context = unsafe { &mut *context };
    let domain = unsafe { &mut *context.allocation_context.cast::<AllocationContext>() };
    if domain.failure.is_some() {
        return 1;
    }
    let outcome = crate::vm_backend::float_env::with_profile(|| {
        catch_unwind(AssertUnwindSafe(|| unsafe {
            allocate_checked(
                domain, context, operation, pointer, old_size, alignment, size, result,
            )
        }))
        .unwrap_or_else(|_| {
            Err(VmArtifactError::NativeMemory {
                message: "generated allocator panicked",
            })
        })
    });
    match outcome {
        Ok(()) => 0,
        Err(error) => {
            domain.failure = Some(error);
            1
        }
    }
}

unsafe fn allocate_checked(
    domain: &mut AllocationContext,
    context: &mut NativeContext,
    operation: u32,
    pointer: *mut u8,
    old_size: u64,
    alignment: u64,
    size: u64,
    result: *mut *mut u8,
) -> Result<(), VmArtifactError> {
    let invalid = || VmArtifactError::NativeMemory {
        message: "invalid generated allocator ABI",
    };
    let count = |value: u64| usize::try_from(value).map_err(|_| invalid());
    let memory = unsafe { &mut *domain.memory };
    let total_limit = domain
        .total_limit
        .checked_sub(context.live_bytes)
        .ok_or_else(invalid)?;
    let block_limit = count(context.allocation_limit)?;
    let total_limit = count(total_limit)?;
    let alignment = count(alignment)?;
    let output = match operation {
        0 => memory.allocate(
            MemoryLayout::new(count(size)?, alignment).map_err(memory_error)?,
            block_limit,
            total_limit,
        )?,
        1 => unsafe {
            memory.reallocate(
                pointer,
                MemoryLayout::new(count(old_size)?, alignment).map_err(memory_error)?,
                count(size)?,
                block_limit,
                total_limit,
            )?
        },
        2 => {
            memory.deallocate(
                pointer,
                MemoryLayout::new(count(old_size)?, alignment).map_err(memory_error)?,
            )?;
            std::ptr::null_mut()
        }
        _ => return Err(invalid()),
    };
    if !result.is_null() {
        unsafe {
            result.write(output);
        }
    }
    context.byte_limit = domain
        .total_limit
        .saturating_sub(memory.live_native_bytes() as u64)
        .min(LLVM_NATIVE_STACK_BYTES);
    if context.live_bytes > context.byte_limit {
        return Err(VmArtifactError::NativeMemory {
            message: "generated allocator exceeded the shared native byte limit",
        });
    }
    Ok(())
}
