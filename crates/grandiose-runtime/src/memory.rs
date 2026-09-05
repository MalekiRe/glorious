//! Uninitialized, aligned storage with explicit ownership handoff.
//!
//! There is no resident type, initialized length, growth factor, copy/drop
//! callback, or vector operation here. Trusted library code owns those
//! invariants. The per-block byte limit is not a replacement for a VM's total
//! memory accounting, execution budget, or safe-only admission checks.
//!
//! Layouts and pointers refer to the current host target. A future linker must
//! establish target, concrete type, allocator, ownership and calling-convention
//! compatibility before these addresses can cross a Glorious VM/native call.

use std::{
    alloc::{Layout, alloc, dealloc, realloc},
    error::Error,
    fmt,
    mem::ManuallyDrop,
    num::NonZeroUsize,
    ptr::NonNull,
};

/// A validated byte extent and alignment, not a language type identity.
///
/// Construction checks the allocator's addressable-size bound, including
/// alignment padding. The private representation is not a serialized ABI.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MemoryLayout(Layout);

impl MemoryLayout {
    pub fn new(size: usize, alignment: usize) -> Result<Self, MemoryError> {
        Layout::from_size_align(size, alignment)
            .map(Self)
            .map_err(|_| MemoryError::InvalidLayout { size, alignment })
    }

    pub const fn of<T>() -> Self {
        Self(Layout::new::<T>())
    }

    /// Repeat an element layout, including its trailing alignment padding.
    /// Even zero-sized elements keep their alignment; element obligations are
    /// not represented by the resulting byte extent.
    pub fn repeat(self, count: usize) -> Result<Self, MemoryError> {
        let stride = self.0.pad_to_align().size();
        let size = stride.checked_mul(count).ok_or(MemoryError::SizeOverflow)?;
        Self::new(size, self.alignment()).map_err(|_| MemoryError::SizeOverflow)
    }

    pub const fn size(self) -> usize {
        self.0.size()
    }

    pub const fn alignment(self) -> usize {
        self.0.align()
    }

    /// Append one naturally aligned field. Field order and enum policy belong
    /// to the caller's concrete ABI, not the allocator.
    pub fn extend(self, field: Self) -> Result<(Self, usize), MemoryError> {
        self.0.extend(field.0).map(|(layout, offset)| (Self(layout), offset))
            .map_err(|_| MemoryError::SizeOverflow)
    }

    /// Include trailing padding so adjacent residents retain their alignment.
    pub fn pad_to_alignment(self) -> Self {
        Self(self.0.pad_to_align())
    }

    fn dangling(self) -> NonNull<u8> {
        // The nonzero alignment is guaranteed by Layout. This address has no
        // allocation provenance and must never be dereferenced for bytes.
        NonNull::without_provenance(NonZeroUsize::new(self.alignment()).unwrap())
    }

    fn check_limit(self, limit: usize) -> Result<(), MemoryError> {
        if self.size() > limit {
            Err(MemoryError::LimitExceeded {
                requested: self.size(),
                limit,
            })
        } else {
            Ok(())
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MemoryError {
    InvalidLayout { size: usize, alignment: usize },
    SizeOverflow,
    LimitExceeded { requested: usize, limit: usize },
    AllocationFailed { size: usize, alignment: usize },
}

impl fmt::Display for MemoryError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLayout { size, alignment } => write!(
                formatter,
                "invalid memory layout: size {size}, alignment {alignment}"
            ),
            Self::SizeOverflow => write!(formatter, "memory layout size overflow"),
            Self::LimitExceeded { requested, limit } => write!(
                formatter,
                "memory request {requested} exceeds block limit {limit}"
            ),
            Self::AllocationFailed { size, alignment } => write!(
                formatter,
                "allocation failed: size {size}, alignment {alignment}"
            ),
        }
    }
}

impl Error for MemoryError {}

/// Sole ownership of a raw byte allocation in this runtime's allocation domain.
///
/// Memory is initially uninitialized. There is deliberately no safe byte slice
/// or typed reference constructor. Safe code may manage or pass the owner;
/// accessing its residents requires an unsafe operation and its contract.
///
/// Dropping this owner releases bytes, **not resident values**. Unsafe clients
/// must arrange all required resident destruction/ownership transfers and end
/// all references before release. This is not a Glorious zero-use capability
/// for an allocation containing linear residents. The source library and its
/// checked public API must establish that contract before guest admission.
///
/// This owner is neither Clone nor implicitly Send/Sync. It contains no guest
/// authority token and must not be constructed from an untrusted numeric address.
#[derive(Debug)]
pub struct RawAllocation {
    pointer: NonNull<u8>,
    layout: MemoryLayout,
}

impl RawAllocation {
    pub fn new(layout: MemoryLayout, byte_limit: usize) -> Result<Self, MemoryError> {
        layout.check_limit(byte_limit)?;
        let pointer = if layout.size() == 0 {
            layout.dangling()
        } else {
            // SAFETY: layout is valid and nonzero. The result, if non-null,
            // is uniquely owned here and freed using this exact layout.
            let raw = unsafe { allocate(layout.0) };
            NonNull::new(raw).ok_or(MemoryError::AllocationFailed {
                size: layout.size(),
                alignment: layout.alignment(),
            })?
        };
        Ok(Self { pointer, layout })
    }

    /// Non-null and aligned, but not necessarily initialized or dereferenceable.
    /// A zero-byte owner carries a dangling pointer with the requested alignment.
    pub const fn as_ptr(&self) -> NonNull<u8> {
        self.pointer
    }

    pub const fn layout(&self) -> MemoryLayout {
        self.layout
    }

    /// Change the byte extent, retaining the existing alignment. Successful
    /// relocation preserves the first min(old_size, new_size) bytes, including
    /// uninitialized bytes. An error leaves the owner and its contents unchanged.
    /// There is no implicit capacity rounding or resident initialization policy.
    ///
    /// # Safety
    ///
    /// No references or accesses may remain live across relocation. The caller
    /// must discharge obligations for truncated residents, permit byte relocation
    /// of retained residents, and repair any permitted internal addresses before
    /// using them. Old pointers must not be used after successful relocation.
    pub unsafe fn resize(&mut self, new_size: usize, byte_limit: usize) -> Result<(), MemoryError> {
        let next = MemoryLayout::new(new_size, self.layout.alignment())?;
        next.check_limit(byte_limit)?;
        if next == self.layout {
            return Ok(());
        }
        if self.layout.size() == 0 || next.size() == 0 {
            // Allocate before replacing: failure retains the old owner.
            *self = Self::new(next, byte_limit)?;
            return Ok(());
        }
        // SAFETY: both extents are nonzero valid layouts with equal alignment;
        // self owns the old allocation. On failure realloc retains it. Caller
        // supplies the resident relocation and reference-invalidation contract.
        let raw = unsafe { reallocate(self.pointer.as_ptr(), self.layout.0, next.size()) };
        let pointer = NonNull::new(raw).ok_or(MemoryError::AllocationFailed {
            size: next.size(),
            alignment: next.alignment(),
        })?;
        self.pointer = pointer;
        self.layout = next;
        Ok(())
    }

    /// Transfer byte ownership without copying, reallocating, or releasing it.
    /// The recipient must eventually return it through `from_raw_parts` or the
    /// exact matching allocation-domain release mechanism. Losing it leaks.
    pub fn into_raw_parts(self) -> (NonNull<u8>, MemoryLayout) {
        let owner = ManuallyDrop::new(self);
        (owner.pointer, owner.layout)
    }

    /// Recover a transferred byte allocation. This is an embedding boundary,
    /// not an import certificate or a guest-callable pointer validation routine.
    ///
    /// # Safety
    ///
    /// For nonzero size, pointer/layout must describe the exact live allocation
    /// transferred by this runtime, with no other owner, matching allocation
    /// domain, and unchanged layout. For zero size the pointer must be non-null
    /// and aligned. The caller transfers resident and outstanding-reference
    /// obligations to this owner; they must be discharged before resize/drop.
    /// Arbitrary foreign pointers or serialized addresses are not admissible.
    pub unsafe fn from_raw_parts(pointer: NonNull<u8>, layout: MemoryLayout) -> Self {
        Self { pointer, layout }
    }
}

impl Drop for RawAllocation {
    fn drop(&mut self) {
        if self.layout.size() != 0 {
            // SAFETY: constructors/resize maintain sole ownership and the
            // exact allocation layout. Unsafe clients must not free it early.
            unsafe { dealloc(self.pointer.as_ptr(), self.layout.0) };
        }
    }
}

unsafe fn allocate(layout: Layout) -> *mut u8 {
    #[cfg(test)]
    if tests::allocation_failure_enabled() {
        return std::ptr::null_mut();
    }
    // SAFETY: caller supplies a valid nonzero layout.
    unsafe { alloc(layout) }
}

unsafe fn reallocate(pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
    #[cfg(test)]
    if tests::allocation_failure_enabled() {
        return std::ptr::null_mut();
    }
    // SAFETY: caller owns pointer under layout and supplies a valid nonzero
    // replacement size for that same alignment.
    unsafe { realloc(pointer, layout, new_size) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{cell::Cell, rc::Rc};

    thread_local! {
        static FAIL_ALLOCATIONS: Cell<bool> = const { Cell::new(false) };
    }

    pub(super) fn allocation_failure_enabled() -> bool {
        FAIL_ALLOCATIONS.with(Cell::get)
    }

    fn failing_allocations<T>(body: impl FnOnce() -> T) -> T {
        struct Reset(bool);
        impl Drop for Reset {
            fn drop(&mut self) {
                FAIL_ALLOCATIONS.with(|flag| flag.set(self.0));
            }
        }
        let _reset = Reset(FAIL_ALLOCATIONS.with(|flag| flag.replace(true)));
        body()
    }

    #[test]
    fn layouts_reject_invalid_alignment_and_address_overflow() {
        for alignment in [0, 3, 6] {
            assert_eq!(
                MemoryLayout::new(8, alignment),
                Err(MemoryError::InvalidLayout { size: 8, alignment })
            );
        }
        assert!(MemoryLayout::new(usize::MAX, 1).is_err());
        assert!(MemoryLayout::new(isize::MAX as usize, 2).is_err());
        assert!(MemoryLayout::new(isize::MAX as usize, 1).is_ok());
    }

    #[test]
    fn repeated_layouts_include_padding_and_check_both_overflow_bounds() {
        let padded = MemoryLayout::new(3, 8).unwrap();
        assert_eq!(padded.repeat(3).unwrap(), MemoryLayout::new(24, 8).unwrap());
        assert_eq!(padded.repeat(usize::MAX), Err(MemoryError::SizeOverflow));
        assert_eq!(
            MemoryLayout::of::<u8>().repeat(usize::MAX),
            Err(MemoryError::SizeOverflow)
        );
        assert_eq!(padded.repeat(0).unwrap(), MemoryLayout::new(0, 8).unwrap());
    }

    #[test]
    fn extended_layouts_preserve_field_padding_and_trailing_stride() {
        let (layout, first) = MemoryLayout::of::<()>().extend(MemoryLayout::of::<u8>()).unwrap();
        let (layout, second) = layout.extend(MemoryLayout::of::<u64>()).unwrap();
        let (layout, third) = layout.extend(MemoryLayout::of::<u8>()).unwrap();
        assert_eq!((first, second, third), (0, 8, 16));
        assert_eq!(layout.size(), 17);
        assert_eq!(layout.pad_to_alignment(), MemoryLayout::new(24, 8).unwrap());
        assert_eq!(layout.repeat(2).unwrap(), MemoryLayout::new(48, 8).unwrap());
        let huge = MemoryLayout::new(isize::MAX as usize, 1).unwrap();
        assert_eq!(huge.extend(MemoryLayout::of::<u64>()), Err(MemoryError::SizeOverflow));
    }

    #[test]
    fn zero_byte_owners_retain_alignment_without_allocating() {
        let layout = MemoryLayout::new(0, 4096)
            .unwrap()
            .repeat(usize::MAX)
            .unwrap();
        let owner = failing_allocations(|| RawAllocation::new(layout, 0)).unwrap();
        assert_eq!(owner.layout(), layout);
        assert_eq!(owner.as_ptr().as_ptr().addr() % 4096, 0);
        let (pointer, layout) = owner.into_raw_parts();
        // SAFETY: exact untouched ownership handoff, including zero layout.
        drop(unsafe { RawAllocation::from_raw_parts(pointer, layout) });
    }

    #[test]
    fn byte_limits_are_checked_before_allocation_including_zero_budget() {
        let layout = MemoryLayout::of::<u64>();
        assert_eq!(
            failing_allocations(|| RawAllocation::new(layout, 0)).unwrap_err(),
            MemoryError::LimitExceeded {
                requested: 8,
                limit: 0
            }
        );
        assert_eq!(
            failing_allocations(|| RawAllocation::new(layout, 8)).unwrap_err(),
            MemoryError::AllocationFailed {
                size: 8,
                alignment: layout.alignment()
            }
        );
        assert!(RawAllocation::new(layout, 8).is_ok());
    }

    #[test]
    fn raw_storage_is_aligned_and_typed_residents_are_explicitly_initialized() {
        #[repr(C, align(256))]
        struct Aligned {
            word: u64,
        }
        let owner = RawAllocation::new(MemoryLayout::of::<Aligned>(), 256).unwrap();
        let pointer = owner.as_ptr().cast::<Aligned>();
        assert_eq!(pointer.as_ptr().addr() % 256, 0);
        // SAFETY: aligned allocated storage, initialized once then moved out;
        // no references or residents remain when the owner is dropped.
        unsafe {
            pointer.as_ptr().write(Aligned { word: 42 });
            assert_eq!(pointer.as_ptr().read().word, 42);
        }
    }

    #[test]
    fn resizing_preserves_the_retained_initialized_prefix() {
        let mut owner =
            RawAllocation::new(MemoryLayout::of::<u64>().repeat(2).unwrap(), 64).unwrap();
        // SAFETY: every read is initialized and within the current allocation;
        // raw addresses are reacquired after each resize, no live references.
        unsafe {
            owner.as_ptr().cast::<u64>().as_ptr().write(11);
            owner.as_ptr().cast::<u64>().as_ptr().add(1).write(22);
            owner.resize(64, 64).unwrap();
            assert_eq!(owner.layout().size(), 64);
            assert_eq!(owner.as_ptr().cast::<u64>().as_ptr().read(), 11);
            assert_eq!(owner.as_ptr().cast::<u64>().as_ptr().add(1).read(), 22);
            owner.resize(8, 64).unwrap();
            assert_eq!(owner.as_ptr().cast::<u64>().as_ptr().read(), 11);
            owner.resize(0, 0).unwrap();
            assert_eq!(owner.layout().size(), 0);
            owner.resize(8, 8).unwrap();
            owner.as_ptr().cast::<u64>().as_ptr().write(33);
            assert_eq!(owner.as_ptr().cast::<u64>().as_ptr().read(), 33);
        }
    }

    #[test]
    fn rejected_resizes_preserve_pointer_layout_and_contents() {
        let mut owner = RawAllocation::new(MemoryLayout::of::<u64>(), 8).unwrap();
        let before = owner.as_ptr();
        let layout = owner.layout();
        // SAFETY: the only resident is a u64, no reference survives mutation.
        unsafe {
            before.cast::<u64>().as_ptr().write(42);
            assert_eq!(
                owner.resize(16, 8),
                Err(MemoryError::LimitExceeded {
                    requested: 16,
                    limit: 8
                })
            );
            assert!(owner.resize(usize::MAX, usize::MAX).is_err());
            assert_eq!(
                failing_allocations(|| owner.resize(16, 16)),
                Err(MemoryError::AllocationFailed {
                    size: 16,
                    alignment: layout.alignment()
                })
            );
            assert_eq!(owner.as_ptr(), before);
            assert_eq!(owner.layout(), layout);
            assert_eq!(owner.as_ptr().cast::<u64>().as_ptr().read(), 42);
        }
    }

    #[test]
    fn same_size_resize_does_not_allocate_but_still_checks_the_limit() {
        let mut owner = RawAllocation::new(MemoryLayout::of::<u64>(), 8).unwrap();
        let pointer = owner.as_ptr();
        // SAFETY: there are no initialized residents or live references.
        unsafe {
            failing_allocations(|| owner.resize(8, 8)).unwrap();
            assert_eq!(owner.as_ptr(), pointer);
            assert_eq!(
                owner.resize(8, 7),
                Err(MemoryError::LimitExceeded {
                    requested: 8,
                    limit: 7
                })
            );
        }
    }

    #[test]
    fn zero_to_nonzero_allocation_failure_retains_the_empty_owner() {
        let mut owner = RawAllocation::new(MemoryLayout::new(0, 64).unwrap(), 0).unwrap();
        let pointer = owner.as_ptr();
        // SAFETY: zero-byte storage has no residents or references.
        unsafe {
            assert_eq!(
                failing_allocations(|| owner.resize(128, 128)),
                Err(MemoryError::AllocationFailed {
                    size: 128,
                    alignment: 64
                })
            );
        }
        assert_eq!(owner.as_ptr(), pointer);
        assert_eq!(owner.layout(), MemoryLayout::new(0, 64).unwrap());
    }

    #[test]
    fn relocation_retains_overalignment_and_initialized_bytes() {
        let mut owner = RawAllocation::new(MemoryLayout::new(256, 256).unwrap(), 1024).unwrap();
        // SAFETY: only this first byte is read, after initialization. No
        // references survive resizing; the new raw address is reacquired.
        unsafe {
            owner.as_ptr().as_ptr().write(42);
            for size in [512, 128, 1024] {
                owner.resize(size, 1024).unwrap();
                assert_eq!(owner.as_ptr().as_ptr().addr() % 256, 0);
                assert_eq!(owner.as_ptr().as_ptr().read(), 42);
            }
        }
    }

    #[test]
    fn zero_size_resident_obligations_do_not_disappear_with_zero_byte_storage() {
        thread_local! { static DROPS: Cell<usize> = const { Cell::new(0) }; }
        #[repr(align(64))]
        struct Resident;
        impl Drop for Resident {
            fn drop(&mut self) {
                DROPS.with(|count| count.set(count.get() + 1));
            }
        }
        DROPS.with(|count| count.set(0));
        let owner =
            failing_allocations(|| RawAllocation::new(MemoryLayout::of::<Resident>(), 0)).unwrap();
        assert_eq!(owner.layout().size(), 0);
        // SAFETY: zero-sized access still has a non-null aligned pointer. The
        // library tracks one initialization and one move independently of size.
        unsafe {
            owner.as_ptr().cast::<Resident>().as_ptr().write(Resident);
            let resident = owner.as_ptr().cast::<Resident>().as_ptr().read();
            drop(owner);
            assert_eq!(DROPS.with(Cell::get), 0);
            drop(resident);
        }
        assert_eq!(DROPS.with(Cell::get), 1);
    }

    #[test]
    fn ownership_handoff_and_relocation_do_not_duplicate_or_drop_residents() {
        struct Resident(Rc<Cell<usize>>);
        impl Drop for Resident {
            fn drop(&mut self) {
                self.0.set(self.0.get() + 1);
            }
        }
        let drops = Rc::new(Cell::new(0));
        let layout = MemoryLayout::of::<Resident>();
        let owner = RawAllocation::new(layout, 1024).unwrap();
        // SAFETY: initialize one resident in suitably aligned storage.
        unsafe {
            owner
                .as_ptr()
                .cast::<Resident>()
                .as_ptr()
                .write(Resident(drops.clone()));
        }
        let original = owner.as_ptr();
        let (pointer, layout) = owner.into_raw_parts();
        assert_eq!(pointer, original);
        assert_eq!(drops.get(), 0);
        // SAFETY: exact sole-owner handoff; Resident is movable and has no
        // interior address into the block. Move it out before releasing bytes.
        unsafe {
            let mut owner = RawAllocation::from_raw_parts(pointer, layout);
            owner
                .resize(layout.repeat(2).unwrap().size(), 1024)
                .unwrap();
            assert_eq!(drops.get(), 0);
            let resident = owner.as_ptr().cast::<Resident>().as_ptr().read();
            drop(owner);
            assert_eq!(drops.get(), 0);
            drop(resident);
        }
        assert_eq!(drops.get(), 1);
        assert_eq!(Rc::strong_count(&drops), 1);
    }
}
