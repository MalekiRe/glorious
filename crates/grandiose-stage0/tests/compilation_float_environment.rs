//! Compilation, not only execution, is isolated from the embedding thread's
//! floating-point controls and sticky exception status.
#![cfg(all(target_arch = "x86_64", target_os = "linux"))]

use grandiose_stage0::vm_backend::llvm::LlvmTarget;
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    PersistentArtifactCache, SourceInput, StageZeroCompiler, decode_and_verify_program,
};

#[derive(Debug, Eq, PartialEq)]
struct Controls {
    mxcsr: u32,
    x87_control: u16,
    x87_status: u16,
}

impl Controls {
    fn read() -> Self {
        let mut value = Self {
            mxcsr: 0,
            x87_control: 0,
            x87_status: 0,
        };
        // SAFETY: these non-mutating stores use appropriately sized storage.
        unsafe {
            std::arch::asm!("stmxcsr [{p}]", p = in(reg) &mut value.mxcsr, options(nostack));
            std::arch::asm!("fnstcw [{p}]", p = in(reg) &mut value.x87_control, options(nostack));
            std::arch::asm!("fnstsw [{p}]", p = in(reg) &mut value.x87_status, options(nostack));
        }
        value
    }
}

#[repr(C, align(64))]
struct Saved([u8; 512]);
unsafe extern "C" {
    fn grandiose_float_env_capture(storage: *mut Saved) -> std::ffi::c_int;
    fn grandiose_float_env_default() -> std::ffi::c_int;
    fn grandiose_float_env_restore(storage: *const Saved) -> std::ffi::c_int;
    fn feraiseexcept(exceptions: std::ffi::c_int) -> std::ffi::c_int;
}
impl Drop for Saved {
    fn drop(&mut self) {
        // SAFETY: restore the same thread's captured opaque environment.
        assert_eq!(unsafe { grandiose_float_env_restore(self) }, 0);
    }
}

fn profile<T>(rounding: u32, denormals: u32, flags: Option<u32>, body: impl FnOnce() -> T) -> T {
    let mut saved = Saved([0; 512]);
    // SAFETY: the bridge checks opaque storage against the target's fenv_t.
    unsafe {
        assert_eq!(grandiose_float_env_capture(&mut saved), 0);
        assert_eq!(grandiose_float_env_default(), 0);
        if let Some(flags) = flags {
            // FE_* exception bits on this gated target (excluding the
            // architecture's nonstandard denormal-operand flag).
            assert_eq!(feraiseexcept((flags & 0x3d) as std::ffi::c_int), 0);
        }
        let mxcsr = flags.map_or(0, |flags| 0x1f80 | flags) | rounding | denormals;
        let x87 = if flags.is_some() { 0x037f } else { 0x0340 } | ((rounding >> 3) as u16);
        std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &mxcsr, options(nostack));
        std::arch::asm!("fldcw [{p}]", p = in(reg) &x87, options(nostack));
    }
    let before = Controls::read();
    let result = body();
    let after = Controls::read();
    // Restore before assertions/formatting, including in trap-enabled probes.
    drop(saved);
    assert_eq!(
        after, before,
        "compiler changed caller controls or exception status"
    );
    result
}

fn request(source: &str, optimization: &str) -> CompilationRequest {
    let package = PackageKey("compilation-float-environment@0.1.0".into());
    let library = grandiose_stage0::service::STANDARD_LIBRARY_FRAGMENTS
        .iter()
        .filter(|(path, _)| {
            matches!(
                *path,
                "src/lib.glorious" | "src/foundation.glorious" | "src/float.glorious"
            )
        })
        .map(|(_, source)| *source)
        .collect::<Vec<_>>()
        .join("\n");
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"compilation-float-environment")),
        mode: CompilationMode::Build,
        root_package: package.clone(),
        sources: vec![
            SourceInput::new(
                package,
                LogicalPath::parse("src/main.glorious").unwrap(),
                source.as_bytes(),
            ),
            SourceInput::new(
                PackageKey("std@0.1.0".into()),
                LogicalPath::parse("src/lib.glorious").unwrap(),
                library.as_bytes(),
            ),
        ],
        target: "stage0-vm".into(),
        semantic_options: Default::default(),
        codegen_options: [("optimization-level".into(), optimization.into())].into(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

// Arithmetic and conversions pass through both optimization levels. The
// current optimizer folds checked integers/patterns and propagates float
// bit patterns; it deliberately does not fold floating-point arithmetic.
const SOURCE: &str = r#"
    use std::*;
    fn folded_pattern() -> i64 { handle 0.1 { 0.1 => 11, _ => 0 } }
    pub fn main() -> [i64; 20] {
        let decimal: f64 = 0.1;
        let limit32: f32 = 3.4028234663852886e38;
        let limit64: f64 = 1.7976931348623157e308;
        let tiny32: f32 = 1e-45;
        let tiny64: f64 = 5e-324;
        let zero32: f32 = 1e-9999;
        let zero64: f64 = 1e-9999;
        let tie32: f32 = 1.000000059604644775390625;
        let above32: f32 = 1.000000059604644775390625000001;
        let tie64: f64 = 1.00000000000000011102230246251565404236316680908203125;
        let above64: f64 = 1.000000000000000111022302462515654042363166809082031251;
        let add32 = f32_add(1.0, 0.000000059604644775390625);
        let add64 = f64_add(1.0, 0.00000000000000011102230246251565404236316680908203125);
        let integer32: u32 = 4294967295;
        let integer64: u64 = 9007199254740995;
        [as<i64>(f64::to_bits(decimal)),
         as<i64>(f32::to_bits(limit32)), as<i64>(f64::to_bits(limit64)),
         as<i64>(f32::to_bits(tiny32)), as<i64>(f64::to_bits(tiny64)),
         as<i64>(f32::to_bits(zero32)), as<i64>(f64::to_bits(zero64)),
         as<i64>(f32::to_bits(tie32)), as<i64>(f32::to_bits(above32)),
         as<i64>(f64::to_bits(tie64)), as<i64>(f64::to_bits(above64)),
         as<i64>(f32::to_bits(add32)), as<i64>(f64::to_bits(add64)),
         as<i64>(f32::to_bits(f32_add(tiny32, tiny32))),
         as<i64>(f64::to_bits(f64_add(tiny64, tiny64))),
         as<i64>(f32::to_bits(as<f32>(integer32))),
         as<i64>(f64::to_bits(as<f64>(integer64))),
         as<i64>(-1.75), (5 + 7) * 3, folded_pattern()]
    }
"#;
const EXPECTED: [i64; 20] = [
    0x3fb999999999999a,
    0x7f7fffff,
    0x7fefffffffffffff,
    1,
    1,
    0,
    0,
    0x3f800000,
    0x3f800001,
    0x3ff0000000000000,
    0x3ff0000000000001,
    0x3f800000,
    0x3ff0000000000000,
    2,
    2,
    0x4f800000,
    0x4340000000000002,
    -1,
    36,
    11,
];

fn compilation_matrix(unmasked: bool) {
    for optimization in ["0", "2"] {
        let input = request(SOURCE, optimization);
        let baseline = profile(0, 0, Some(0), || {
            StageZeroCompiler::new().compile(input.clone())
        })
        .unwrap()
        .artifact
        .unwrap();
        assert_eq!(baseline.run_array_i64().unwrap(), EXPECTED);
        let bytes = baseline.canonical_bytes();
        for (r, rounding) in [0, 0x2000, 0x4000, 0x6000].into_iter().enumerate() {
            for (d, denormals) in [0, 0x40, 0x8000, 0x8040].into_iter().enumerate() {
                let flags = (!unmasked).then_some([0, 0x15, 0x2a, 0x3f][(r + d) % 4]);
                let compiler = StageZeroCompiler::new();
                let result = profile(rounding, denormals, flags, || match (r + d) % 4 {
                    0 => compiler.compile(input.clone()),
                    1 => compiler.compile_with_parent(input.clone(), None),
                    2 => {
                        let revision = compiler.import_revision(input.clone(), None).unwrap();
                        compiler.compile_revision(revision)
                    }
                    _ => {
                        let revision = compiler.import_revision(input.clone(), None).unwrap();
                        let session = compiler.open_session(revision).unwrap();
                        compiler.compile_session(&session)
                    }
                })
                .unwrap();
                let program = result.artifact.unwrap();
                assert_eq!(
                    program.canonical_bytes(),
                    bytes,
                    "O{optimization}, RC={rounding:x}, denormals={denormals:x}"
                );
                assert_eq!(program.run_array_i64().unwrap(), EXPECTED);
                assert_eq!(
                    decode_and_verify_program(&program.canonical_bytes())
                        .unwrap()
                        .run_array_i64()
                        .unwrap(),
                    EXPECTED
                );
            }
        }
    }
}

#[test]
fn compilation_is_deterministic_and_preserves_caller_environment() {
    compilation_matrix(false);
}

#[test]
fn compilation_masks_host_traps_without_changing_host_masks() {
    const CHILD: &str = "GRANDIOSE_COMPILATION_FLOAT_TRAP_CHILD";
    if std::env::var_os(CHILD).is_none() {
        let outcome = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                "compilation_masks_host_traps_without_changing_host_masks",
                "--nocapture",
            ])
            .env(CHILD, "1")
            .output()
            .unwrap();
        assert!(
            outcome.status.success(),
            "trap-enabled compiler child {:?}: {}{}",
            outcome.status,
            String::from_utf8_lossy(&outcome.stdout),
            String::from_utf8_lossy(&outcome.stderr)
        );
        return;
    }
    compilation_matrix(true);
    compilation_errors(true);
    compilation_policy_unwind(true);
}

#[test]
fn compilation_restores_environment_and_diagnostics_after_source_errors() {
    compilation_errors(false);
}

fn compilation_errors(unmasked: bool) {
    for source in [
        "pub fn main() -> f32 { 1e39 }",
        "pub fn main() -> f64 { 1e9999 }",
        "pub fn main() -> f64 { missing(0.1) }",
    ] {
        for optimization in ["0", "2"] {
            let input = request(source, optimization);
            let baseline = profile(0, 0, Some(0), || {
                StageZeroCompiler::new().compile(input.clone())
            })
            .unwrap_err()
            .diagnostics();
            for rounding in [0, 0x2000, 0x4000, 0x6000] {
                for denormals in [0, 0x40, 0x8000, 0x8040] {
                    let error = profile(rounding, denormals, (!unmasked).then_some(0x15), || {
                        StageZeroCompiler::new().compile(input.clone())
                    })
                    .unwrap_err()
                    .diagnostics();
                    assert_eq!(error, baseline);
                }
            }
        }
    }
}

#[test]
fn compilation_restores_environment_on_native_partition_policy_unwind() {
    compilation_policy_unwind(false);
}

fn mutating_compilation_policy(panic: bool) -> bool {
    let controls = Controls::read();
    assert_eq!(controls.mxcsr & !0x3f, 0x1f80);
    assert_eq!(controls.x87_control, 0x037f);
    let altered = 0xffd5u32;
    let x87 = 0x0f7fu16;
    // SAFETY: known architectural controls, exceptions masked.
    unsafe {
        std::arch::asm!("ldmxcsr [{p}]", p = in(reg) &altered, options(nostack));
        std::arch::asm!("fldcw [{p}]", p = in(reg) &x87, options(nostack));
    }
    assert!(!panic, "deliberate compilation policy unwind");
    false
}

fn compilation_policy_unwind(unmasked: bool) {
    let input = request("pub fn main() -> f64 { 0.1 }", "2");
    let target = LlvmTarget::host().unwrap();
    let baseline = profile(0, 0, Some(0), || {
        StageZeroCompiler::new().compile_llvm(input.clone(), target.clone())
    })
    .unwrap();
    for rounding in [0, 0x2000, 0x4000, 0x6000] {
        for denormals in [0, 0x40, 0x8000, 0x8040] {
            for panic in [false, true] {
                let result = profile(rounding, denormals, (!unmasked).then_some(0x15), || {
                    std::panic::catch_unwind(|| {
                        StageZeroCompiler::new().compile_llvm_partitioned(
                            input.clone(),
                            target.clone(),
                            |_| mutating_compilation_policy(panic),
                        )
                    })
                });
                if panic {
                    assert!(result.is_err());
                } else {
                    let program = result.unwrap().unwrap();
                    assert_eq!(program.ir(), baseline.ir());
                    assert_eq!(program.abi(), baseline.abi());
                    assert_eq!(
                        program.vm_program().canonical_bytes(),
                        baseline.vm_program().canonical_bytes()
                    );
                }
            }
        }
    }
}

#[test]
fn compilation_cache_miss_and_hit_preserve_the_caller_environment() {
    let directory = std::env::temp_dir().join(format!(
        "grandiose-compilation-float-cache-{}",
        std::process::id()
    ));
    // A new private test directory, never an existing host cache.
    std::fs::create_dir(&directory).unwrap();
    let cache = PersistentArtifactCache::new(&directory);
    for optimization in ["0", "2"] {
        let input = request("pub fn main() -> f64 { 0.1 }", optimization);
        let baseline = profile(0, 0, Some(0), || {
            StageZeroCompiler::new().compile(input.clone())
        })
        .unwrap()
        .artifact
        .unwrap()
        .canonical_bytes();
        for rounding in [0x2000, 0x4000] {
            let artifact = profile(rounding, 0x8040, Some(0x15), || {
                StageZeroCompiler::new().compile_artifact_with_cache(input.clone(), &cache)
            })
            .unwrap()
            .unwrap();
            assert_eq!(artifact.canonical_bytes(), baseline);
            assert_eq!(artifact.run_f64().unwrap().to_bits(), 0x3fb999999999999a);
        }
    }
    assert_eq!(cache.stats().misses, 2);
    assert_eq!(cache.stats().hits, 2);
    std::fs::remove_dir_all(directory).unwrap();
}
