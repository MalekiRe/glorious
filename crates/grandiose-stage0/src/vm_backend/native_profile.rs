//! Opt-in measurements of VM-owned native backing extents and explicit bulk
//! copies. Allocation owners report events; instruction-boundary sampling can
//! miss temporary peaks and is deliberately not used here.

use grandiose_runtime::memory::{MemoryError, MemoryLayout, RawAllocation};
use std::{cell::Cell, ptr::NonNull, rc::Rc};

/// Native backing-storage measurements at the end of execution, before the
/// runner destroys its remaining allocation domain. Live bytes therefore do
/// not hide source buffers left outstanding for that final teardown.
///
/// Bytes are requested native layouts, not allocator usable sizes or RSS.
/// Raw reallocations replace their old extent atomically in this observation;
/// allocator-internal overlap/relocation costs are not measured. Rust metadata,
/// static data, and externally owned native arguments are outside this scope.
/// Zero-byte dangling allocations do not count as backing allocations.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct VmNativeMemoryProfile {
    /// Peak simultaneous raw + home bytes, not the sum of independent peaks.
    pub peak_live_bytes: u64,
    pub raw_live_bytes: u64,
    pub raw_peak_bytes: u64,
    pub raw_allocations: u64,
    /// Successful nonzero-to-nonzero extent changes; same-size calls are no-ops.
    pub raw_reallocations: u64,
    pub raw_deallocations: u64,
    /// Resident-home and private scalar-spill backing, including idle pooled
    /// spill bytes until they are reused or reclaimed for another allocation.
    pub home_live_bytes: u64,
    pub home_peak_bytes: u64,
    pub home_allocations: u64,
    pub home_deallocations: u64,
    /// Bytes passed through the explicit raw copy/copy-nonoverlapping leaves.
    pub raw_bulk_copy_bytes: u64,
    /// Bytes passed through native-home bulk moves, copies, and exports.
    /// Scalar loads/stores and allocator-internal relocation are not included.
    pub home_bulk_copy_bytes: u64,
    /// Already-present addressable residents lent to generated segments.
    /// Private scalar spills and empty future frame slots are not shared objects.
    pub generated_resident_entries: u64,
    /// Backing allocations/copies while admitting those existing residents at
    /// machine entry. Source value production, ownership transfer and replay
    /// run in the common runtime and are not boundary adapters.
    pub generated_resident_entry_allocations: u64,
    pub generated_resident_entry_copy_bytes: u64,
    /// Cumulative operation/copy counters saturate rather than wrap. If set,
    /// those counters are lower bounds, not exact measurements.
    pub counters_saturated: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AllocationKind { Raw, Home }

#[derive(Debug, Default)]
pub(super) struct NativeMemoryMeasurements {
    value: Cell<VmNativeMemoryProfile>,
}

fn accumulate(value: &mut u64, amount: u64, saturated: &mut bool) {
    if let Some(next) = value.checked_add(amount) {
        *value = next;
    } else {
        *value = u64::MAX;
        *saturated = true;
    }
}

fn peaks(value: &mut VmNativeMemoryProfile) {
    value.raw_peak_bytes = value.raw_peak_bytes.max(value.raw_live_bytes);
    value.home_peak_bytes = value.home_peak_bytes.max(value.home_live_bytes);
    // The existing native byte-budget admission bounds these actual extents.
    let total = value.raw_live_bytes.checked_add(value.home_live_bytes)
        .expect("admitted native backing extents fit their byte budget");
    value.peak_live_bytes = value.peak_live_bytes.max(total);
}

impl NativeMemoryMeasurements {
    pub(super) fn snapshot(&self) -> VmNativeMemoryProfile { self.value.get() }

    /// This interval contains only storage admission, never generated or guest
    /// computation. Measure the allocation owners' actual events, not an
    /// assumption derived from a type or an engine selection.
    pub(super) fn resident_entry(&self, before: VmNativeMemoryProfile) {
        let mut value = self.value.get();
        let allocations = value.home_allocations.saturating_sub(before.home_allocations);
        let copies = value.home_bulk_copy_bytes.saturating_sub(before.home_bulk_copy_bytes);
        accumulate(&mut value.generated_resident_entries, 1, &mut value.counters_saturated);
        accumulate(&mut value.generated_resident_entry_allocations, allocations, &mut value.counters_saturated);
        accumulate(&mut value.generated_resident_entry_copy_bytes, copies, &mut value.counters_saturated);
        self.value.set(value);
    }

    fn acquired(&self, kind: AllocationKind, bytes: usize) {
        if bytes == 0 { return; }
        let mut value = self.value.get();
        let (live, operations) = match kind {
            AllocationKind::Raw => (&mut value.raw_live_bytes, &mut value.raw_allocations),
            AllocationKind::Home => (&mut value.home_live_bytes, &mut value.home_allocations),
        };
        *live = live.checked_add(bytes as u64).expect("admitted native extent fits");
        accumulate(operations, 1, &mut value.counters_saturated);
        peaks(&mut value);
        self.value.set(value);
    }

    fn released(&self, kind: AllocationKind, bytes: usize) {
        if bytes == 0 { return; }
        let mut value = self.value.get();
        let (live, operations) = match kind {
            AllocationKind::Raw => (&mut value.raw_live_bytes, &mut value.raw_deallocations),
            AllocationKind::Home => (&mut value.home_live_bytes, &mut value.home_deallocations),
        };
        *live = live.checked_sub(bytes as u64).expect("native extent released once");
        accumulate(operations, 1, &mut value.counters_saturated);
        self.value.set(value);
    }

    fn resized(&self, old: usize, new: usize) {
        if old == new { return; }
        if old == 0 { self.acquired(AllocationKind::Raw, new); return; }
        if new == 0 { self.released(AllocationKind::Raw, old); return; }
        let mut value = self.value.get();
        value.raw_live_bytes = value.raw_live_bytes.checked_sub(old as u64)
            .and_then(|live| live.checked_add(new as u64))
            .expect("successful raw resize retains an admitted extent");
        accumulate(&mut value.raw_reallocations, 1, &mut value.counters_saturated);
        peaks(&mut value);
        self.value.set(value);
    }

    pub(super) fn copied(&self, kind: AllocationKind, bytes: usize) {
        let mut value = self.value.get();
        let count = match kind {
            AllocationKind::Raw => &mut value.raw_bulk_copy_bytes,
            AllocationKind::Home => &mut value.home_bulk_copy_bytes,
        };
        accumulate(count, bytes as u64, &mut value.counters_saturated);
        self.value.set(value);
    }
}

/// Measurement follows the actual allocation owner, including temporary homes
/// rejected by a later logical-budget check. This changes no byte admission or
/// allocator policy and does not run guest resident destruction.
#[derive(Debug)]
pub(super) struct NativeAllocation {
    allocation: Option<RawAllocation>,
    measurements: Option<Rc<NativeMemoryMeasurements>>,
    kind: AllocationKind,
}

impl NativeAllocation {
    pub(super) fn new(
        allocation: RawAllocation,
        measurements: Option<Rc<NativeMemoryMeasurements>>,
        kind: AllocationKind,
    ) -> Self {
        if let Some(measurements) = &measurements {
            measurements.acquired(kind, allocation.layout().size());
        }
        Self { allocation: Some(allocation), measurements, kind }
    }

    pub(super) fn as_ptr(&self) -> NonNull<u8> {
        self.allocation.as_ref().expect("live native allocation").as_ptr()
    }

    pub(super) fn layout(&self) -> MemoryLayout {
        self.allocation.as_ref().expect("live native allocation").layout()
    }

    /// # Safety
    /// The caller supplies RawAllocation::resize's resident/loan obligations.
    pub(super) unsafe fn resize_raw(&mut self, size: usize, limit: usize) -> Result<(), MemoryError> {
        debug_assert_eq!(self.kind, AllocationKind::Raw);
        let allocation = self.allocation.as_mut().expect("live native allocation");
        let old = allocation.layout().size();
        // SAFETY: unchanged obligations forwarded from the machine leaf.
        unsafe { allocation.resize(size, limit)?; }
        if let Some(measurements) = &self.measurements {
            measurements.resized(old, size);
        }
        Ok(())
    }
}

impl Drop for NativeAllocation {
    fn drop(&mut self) {
        if let Some(allocation) = self.allocation.take() {
            let bytes = allocation.layout().size();
            drop(allocation);
            if let Some(measurements) = &self.measurements {
                measurements.released(self.kind, bytes);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resident_entry_counts_actual_backing_events_only_inside_its_interval() {
        let measurements = NativeMemoryMeasurements::default();
        measurements.acquired(AllocationKind::Home, 16);
        measurements.copied(AllocationKind::Home, 16);
        let unchanged = measurements.snapshot();
        measurements.resident_entry(unchanged);
        let before = measurements.snapshot();
        measurements.acquired(AllocationKind::Home, 8);
        measurements.copied(AllocationKind::Home, 8);
        measurements.resident_entry(before);
        measurements.copied(AllocationKind::Home, 4);
        let result = measurements.snapshot();
        assert_eq!(result.generated_resident_entries, 2);
        assert_eq!(result.generated_resident_entry_allocations, 1);
        assert_eq!(result.generated_resident_entry_copy_bytes, 8);
        assert_eq!(result.home_bulk_copy_bytes, 28);
        assert!(!result.counters_saturated);
    }

    #[test]
    fn native_profile_cumulative_counters_saturate_explicitly_without_corrupting_live_bytes() {
        let measurements = NativeMemoryMeasurements::default();
        measurements.value.set(VmNativeMemoryProfile {
            raw_allocations: u64::MAX,
            raw_bulk_copy_bytes: u64::MAX - 1,
            ..Default::default()
        });
        measurements.acquired(AllocationKind::Raw, 8);
        measurements.copied(AllocationKind::Raw, 2);
        measurements.released(AllocationKind::Raw, 8);
        let result = measurements.snapshot();
        assert!(result.counters_saturated);
        assert_eq!(result.raw_allocations, u64::MAX);
        assert_eq!(result.raw_bulk_copy_bytes, u64::MAX);
        assert_eq!((result.raw_live_bytes, result.raw_peak_bytes, result.raw_deallocations), (0, 8, 1));
    }
}
