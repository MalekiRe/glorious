//! Shared-storage substrate checks, NOT an interpreter/native ABI certificate.
//! No guest instructions or trusted-export admission are implemented here.

use grandiose_vm::runtime::memory::{MemoryLayout, RawAllocation};

#[repr(C)]
struct NativePair {
    first: u64,
    second: u64,
}

// This is a trusted test implementation with the exact same host-target type,
// not arbitrary foreign code admitted through a matching size/alignment.
unsafe extern "C" fn update_pair(pointer: *mut NativePair) -> *mut NativePair {
    // SAFETY: the caller lends one initialized, aligned, exclusively accessible
    // NativePair. No reference or ownership is retained beyond this call.
    unsafe {
        (*pointer).first += 1;
        (*pointer).second += 2;
    }
    pointer
}

#[test]
fn native_call_borrows_the_same_allocation_without_element_reconstruction() {
    let owner = RawAllocation::new(MemoryLayout::of::<NativePair>(), 16).unwrap();
    let pointer = owner.as_ptr().cast::<NativePair>().as_ptr();
    // SAFETY: initialize before passing to native code, no simultaneous alias,
    // and move the sole resident out before releasing its backing allocation.
    unsafe {
        pointer.write(NativePair {
            first: 19,
            second: 20,
        });
        assert_eq!(update_pair(pointer), pointer);
        assert_eq!(owner.as_ptr().cast::<NativePair>().as_ptr(), pointer);
        let value = pointer.read();
        assert_eq!(value.first + value.second, 42);
    }
}

#[test]
fn native_ownership_handoff_keeps_the_address_and_allocator_domain() {
    let owner = RawAllocation::new(MemoryLayout::of::<NativePair>(), 16).unwrap();
    let original = owner.as_ptr();
    // SAFETY: allocated uninitialized storage is correctly sized/aligned.
    unsafe {
        original.cast::<NativePair>().as_ptr().write(NativePair {
            first: 1,
            second: 2,
        });
    }
    let (pointer, layout) = owner.into_raw_parts();
    // SAFETY: unchanged pointer/layout from this runtime's sole-owner transfer,
    // not a foreign allocation, integer address, or a second adopted owner.
    let returned = unsafe { RawAllocation::from_raw_parts(pointer, layout) };
    assert_eq!(returned.as_ptr(), original);
    // SAFETY: resident remained initialized; move it out before deallocation.
    let value = unsafe { returned.as_ptr().cast::<NativePair>().as_ptr().read() };
    assert_eq!((value.first, value.second), (1, 2));
}
