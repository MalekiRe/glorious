//! Physical authoring-runtime measurements. Compilation and verification are
//! outside the meter; the runtime executes synchronously on the metered thread.
//! Requested bytes include repeated allocations/reallocations, not allocator
//! metadata, peak resident memory, or allocations on other threads.

use std::alloc::{GlobalAlloc, Layout, System};
use std::cell::Cell;
use std::collections::BTreeMap;

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, VerifiedVmProgram, VmExecutionLimits,
};

#[derive(Clone, Copy, Debug, Default)]
struct AllocationCounts {
    allocations: u64,
    reallocations: u64,
    requested_bytes: u64,
}

thread_local! {
    // Constant, non-allocating TLS avoids allocator recursion. Disabled by
    // default so parallel compilation and test reporting are not counted.
    static COUNTS: Cell<Option<AllocationCounts>> = const { Cell::new(None) };
}

struct MeteredSystem;

fn count_request(bytes: usize, reallocation: bool) {
    let _ = COUNTS.try_with(|cell| {
        if let Some(mut counts) = cell.get() {
            counts.allocations += u64::from(!reallocation);
            counts.reallocations += u64::from(reallocation);
            counts.requested_bytes += bytes as u64;
            cell.set(Some(counts));
        }
    });
}

// SAFETY: every operation forwards the original pointer/layout unchanged to
// System. Instrumentation uses only non-allocating thread-local integer state.
unsafe impl GlobalAlloc for MeteredSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let result = unsafe { System.alloc(layout) };
        if !result.is_null() {
            count_request(layout.size(), false);
        }
        result
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let result = unsafe { System.alloc_zeroed(layout) };
        if !result.is_null() {
            count_request(layout.size(), false);
        }
        result
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) }
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        let result = unsafe { System.realloc(pointer, layout, new_size) };
        if !result.is_null() {
            count_request(new_size, true);
        }
        result
    }
}

#[global_allocator]
static ALLOCATOR: MeteredSystem = MeteredSystem;

struct Meter;

impl Drop for Meter {
    fn drop(&mut self) {
        COUNTS.with(|cell| cell.set(None));
    }
}

fn measured<T>(run: impl FnOnce() -> T) -> (T, AllocationCounts) {
    COUNTS.with(|cell| {
        assert!(cell.get().is_none(), "allocation meters cannot nest");
        cell.set(Some(AllocationCounts::default()));
    });
    let guard = Meter;
    let value = run();
    let counts = COUNTS.with(|cell| cell.replace(None).unwrap());
    drop(guard);
    (value, counts)
}

fn program(size: usize, read: bool) -> VerifiedVmProgram {
    let source = include_str!("fixtures/hash_indexing_profile.glorious")
        .replace("@SIZE@", &size.to_string())
        .replace("@READ@", if read { "1" } else { "0" });
    let app = PackageKey("app@0.1.0".into());
    let standard = PackageKey("std@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"runtime-storage-profile")),
        mode: CompilationMode::Build,
        root_package: app.clone(),
        sources: vec![
            SourceInput::new(
                app,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            ),
            SourceInput::new(
                standard,
                LogicalPath::parse("src/lib.glorious").unwrap(),
                include_bytes!("../../../stdlib/src/lib.glorious").as_slice(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };
    let outcome = StageZeroCompiler::new().compile(request).unwrap();
    let bytes = outcome.artifact.unwrap().canonical_bytes();
    grandiose_stage0::decode_and_verify_program(&bytes).unwrap()
}

#[test]
fn allocation_meter_is_thread_local_and_counts_only_its_scope() {
    let worker = std::thread::spawn(|| measured(|| std::hint::black_box(vec![0_u8; 8192])));
    let (value, counts) = measured(|| {
        let mut value = std::hint::black_box(vec![0_u8; 257]);
        value.reserve_exact(1024);
        std::hint::black_box(value)
    });
    assert_eq!(value.len(), 257);
    assert!(counts.allocations >= 1);
    assert!(counts.reallocations >= 1);
    assert!(counts.requested_bytes >= 257 + 1281);
    // The worker's allocation cannot have been charged to this thread.
    assert!(counts.requested_bytes < 8192);
    let (worker_value, worker_counts) = worker.join().unwrap();
    assert_eq!(worker_value.len(), 8192);
    assert_eq!(worker_counts.requested_bytes, 8192);
    assert!(COUNTS.with(|cell| cell.get().is_none()));
}

#[test]
fn hash_table_physical_allocation_requests_are_measured_separately_from_vm_work() {
    let mut lookup_work = Vec::new();
    let mut lookup_bytes = Vec::new();
    for size in [8, 64] {
        let mut runs = Vec::new();
        for read in [false, true] {
            let program = program(size, read);
            let (result, allocation) = measured(|| {
                program.run_i64_for_authoring(VmExecutionLimits {
                    max_call_depth: 64,
                    ..Default::default()
                })
            });
            let (value, profile) = result.unwrap();
            assert_eq!(value, 42);
            assert!(allocation.allocations > 0);
            assert!(allocation.requested_bytes > 0);
            assert!(profile.peak_call_depth < 64);
            eprintln!("physical hash table size={size}, read={read}: {allocation:?}; {profile:?}");
            runs.push((allocation, profile));
        }
        let added_work = runs[1]
            .1
            .work_ticks
            .checked_sub(runs[0].1.work_ticks)
            .unwrap();
        // Preserve size-independent lookup transfer, not today's absolute
        // allocation count. Runtime improvements may reduce these costs.
        let added_bytes =
            i128::from(runs[1].0.requested_bytes) - i128::from(runs[0].0.requested_bytes);
        eprintln!(
            "hash table size={size}, sixteen reads: work={added_work}, additional allocator-request bytes={added_bytes}"
        );
        lookup_work.push(added_work);
        lookup_bytes.push(added_bytes);
    }
    assert_eq!(lookup_work[0], lookup_work[1]);
    assert!(lookup_bytes[0] > 0);
    assert_eq!(
        lookup_bytes[0], lookup_bytes[1],
        "lookup must not copy the table backing"
    );
}
