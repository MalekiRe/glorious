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
    let fixture = include_str!("fixtures/hash_indexing_profile.glorious");
    assert_eq!(fixture.matches("    fill(&mut map, 0);").count(), 1);
    assert_eq!(fixture.matches("=> 42").count(), 2);
    // Warm one checked lookup in both executions. Native layout descriptors
    // are cached on first use, and large-table construction can already have
    // populated them. The delta must measure the same sixteen warm lookups,
    // not that size-dependent first-use history. The warmup remains metered
    // and charged, and the result is checked in both branches.
    let source = fixture
        .replace("    fill(&mut map, 0);", "    fill(&mut map, 0);\n    let warm = probe(&map, HashMap::len(&map) - 1);")
        .replace("=> 42", "=> 42 * warm")
        .replace("@SIZE@", &size.to_string())
        .replace("@READ@", if read { "1" } else { "0" });
    compile_source(&source)
}

fn compile_source(source: &str) -> VerifiedVmProgram {
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
fn projected_array_updates_do_not_copy_unique_backing_as_arrays_grow() {
    let mut added_bytes = Vec::new();
    for size in [8, 64, 512] {
        let mut runs = Vec::new();
        for update in [false, true] {
            let source = include_str!("fixtures/array_update_profile.glorious")
                .replace("@SIZE@", &size.to_string())
                .replace("@UPDATE@", if update { "1" } else { "0" });
            let program = compile_source(&source);
            let digest = Digest::of_bytes(&program.canonical_bytes());
            // SAFETY: compile_source compiles the local fixture and trusted
            // pointer-backed stdlib, then independently decodes/verifies it.
            let (result, allocation) = measured(|| unsafe {
                program.run_i64_for_authoring_with_unsafe(VmExecutionLimits {
                    max_call_depth: 64,
                    ..Default::default()
                })
            });
            let (value, profile) = result.unwrap();
            assert_eq!(value, 42);
            eprintln!("physical array size={size}, update={update}, artifact={digest:?}: {allocation:?}; {profile:?}");
            runs.push((allocation, profile));
        }
        let bytes = i128::from(runs[1].0.requested_bytes) - i128::from(runs[0].0.requested_bytes);
        eprintln!("array size={size}, sixteen writes: additional allocator-request bytes={bytes}");
        added_bytes.push(bytes);
    }
    assert!(added_bytes[0] > 0);
    assert!(added_bytes.windows(2).all(|pair| pair[0] == pair[1]),
        "updating one element must not copy the array backing: {added_bytes:?}");
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
fn source_vec_pushes_with_capacity_do_not_materialize_growth_only_registers() {
    let mut profiles = Vec::new();
    for count in [64, 256, 1024] {
        let source = format!(
            r#"
            use std::*;
            fn fill(values: &mut Vec<usize>, index: usize) -> () {{
                handle index == {count} {{
                    true => (),
                    false => {{ Vec::push(&mut *values, index); fill(values, index + 1) }},
                }}
            }}
            pub fn main() -> i64 {{
                let mut values = Vec<usize>::with_capacity(1024);
                fill(&mut values, 0);
                handle Vec::len(&values) == {count} {{
                    false => 0,
                    true => handle Vec::capacity(&values) == 1024 {{
                        false => 0, true => handle *Vec::get_unchecked(&values, as<usize>({count}) - 1) == as<usize>({count}) - 1 {{ true => 42, false => 0 }},
                    }},
                }}
            }}
        "#
        );
        let program = compile_source(&source);
        // SAFETY: freshly compiled source plus the trusted stdlib, under one
        // execution domain and the same finite instruction/allocation limits.
        let (result, allocation) = measured(|| unsafe {
            program.run_i64_for_authoring_with_unsafe(VmExecutionLimits {
                max_call_depth: 64,
                ..Default::default()
            })
        });
        let (value, profile) = result.unwrap();
        assert_eq!(value, 42);
        assert!(profile.peak_call_depth < 64);
        eprintln!("physical preallocated Vec pushes={count}: {allocation:?}; {profile:?}");
        profiles.push((count, allocation, profile));
    }
    // Once capacity is available, pushes plus the final source destruction
    // stay linear. Drop consumes bounded chunks, so an exact per-resident
    // slope can be fractional; compare rational slopes without rounding.
    let slopes: Vec<_> = profiles
        .windows(2)
        .map(|pair| {
            let count = (pair[1].0 - pair[0].0) as u64;
            let bytes = pair[1].1.requested_bytes - pair[0].1.requested_bytes;
            let elements =
                pair[1].2.charged_allocation_elements - pair[0].2.charged_allocation_elements;
            (bytes, elements, count)
        })
        .collect();
    assert_eq!(slopes[0].0 * slopes[1].2, slopes[1].0 * slopes[0].2,
        "physical requests must have an exact steady-state slope: {slopes:?}");
    assert_eq!(slopes[0].1 * slopes[1].2, slopes[1].1 * slopes[0].2,
        "logical charges must have an exact steady-state slope: {slopes:?}");
    // The old reserve routine materialized 129 registers even when it did
    // nothing, taking this whole source path above 170 charged elements/push.
    // Keep the same ceiling, now including actual resident destruction.
    assert!(
        slopes[0].1 < 100 * slopes[0].2,
        "growth-only temporaries reached the steady-state path: {slopes:?}"
    );
    eprintln!(
        "preallocated Vec per-resident (physical numerator, charged numerator, denominator): {:?}",
        slopes[0]
    );
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
                // SAFETY: this is the same locally compiled/verified source
                // path as the projected-update probe, not external bytecode.
                unsafe {
                    program.run_i64_for_authoring_with_unsafe(VmExecutionLimits {
                        max_call_depth: 64,
                        ..Default::default()
                    })
                }
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
