use std::{
    fs,
    path::{Path, PathBuf},
    time::Instant,
};

use grandiose::{CompileOptions, OptimizationLevel, source_bundle::{Segment, SourceBundle}};
use grandiose_vm::{SystemHost, Value, Vm, verify};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).parent().unwrap().parent().unwrap().to_owned()
}

fn self_host_bundle(application: &str) -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("main.glorious").to_string_lossy(),
        format!("mod frontend;\nmod probe;\n\nmain() {{ run_compiler_host({application}) }}\n"),
    );
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("probe/probe.glorious"),
        root.join("probe/headers/headers.glorious"),
        root.join("probe/bodies/bodies.glorious"),
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let mut source = fs::read_to_string(&path)
                .unwrap()
                .replace("pub mod lossless;\n", "")
                .replace("pub mod resolution;\n", "")
                .replace("pub mod elaboration;\n", "");
            if path.ends_with("probe/probe.glorious") {
                source = source
                    .replace("pub mod lexer;\n", "")
                    .replace("pub mod scanner;\n", "");
            }
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

// A representative, moderately-heavy body-parser corpus entry.
const REP_INPUT: &str = "infixl 10 op; proxy(a: i64, b: i64) -> i64 { combine(a op b, c) } \
    effect Signal<T> { inspect(value: T) -> ! } \
    enum Result<T, E> { Ok(T), Err(E) } \
    pick(value: Result<i64, ()>) -> i64 { \
        handle perform Signal<Result<i64, ()>>::inspect(value) { \
            Result::Ok(answer) => answer, Result::Err(_) => 0 \
        } \
    } \
    probe_while() { while { true } } \
    probe_loop() { loop { () } { () } } \
    probe_nested() { let x = { let y = make(); y }; combine(x, 2) }";

/// VM-execution benchmark for the self-host body-parser workload. The compiled
/// G1 artifact is cached on disk (G1_VM_PERF_CACHE) so VM-internal changes can
/// be measured without recompiling the self-host bundle on every run.
#[test]
#[ignore = "manual perf benchmark"]
fn vm_body_bench_cached() {
    let repeats: usize = std::env::var("G1_PERF_REPEATS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(1);
    let mut cache_path = std::env::var("G1_VM_PERF_CACHE").ok();
    if cache_path.as_deref() == Some("") {
        cache_path = None;
    }

    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let t0 = Instant::now();
            let (verified, functions) = match cache_path.as_deref() {
                Some(path) if Path::new(path).exists() => {
                    let bytes = fs::read(path).unwrap();
                    let verified = grandiose_vm::load_verified(&bytes).unwrap();
                    let functions = verified.clone().into_inner().functions.len();
                    (verified, functions)
                }
                _ => {
                    let phases = grandiose::compile_bundle_to_phases_with_options(
                        &self_host_bundle("probe::bodies::application"),
                        CompileOptions { optimization_level: OptimizationLevel::O2 },
                    )
                    .unwrap();
                    let functions = phases.artifact.functions.len();
                    let bytes = phases.artifact.encode();
                    if let Some(path) = cache_path.as_deref() {
                        fs::write(path, &bytes).unwrap();
                        eprintln!("VM_BENCH_CACHE_WRITTEN={path}");
                    }
                    (verify(phases.artifact).unwrap(), functions)
                }
            };
            let compile_secs = t0.elapsed().as_secs_f64();
            eprintln!("VM_BENCH_COMPILE_SECS={compile_secs:.3}");
            eprintln!("VM_BENCH_FUNCTIONS={functions}");

            let entry = verified.entry_function().unwrap();
            let dir = tempfile::tempdir().unwrap();
            let output = dir.path().join("out.bin");
            let mut args: Vec<std::ffi::OsString> = vec![output.clone().into_os_string()];
            for i in 0..repeats {
                let p = dir.path().join(format!("in-{i}.glorious"));
                fs::write(&p, REP_INPUT).unwrap();
                args.push(p.into_os_string());
            }
            let vm = Vm::with_host(
                verified,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(args),
            ).unwrap();
            let t1 = Instant::now();
            let r = vm.run(entry, vec![]).unwrap();
            let run_secs = t1.elapsed().as_secs_f64();
            assert_eq!(r, Value::Unit);
            eprintln!("VM_BENCH_RUN_SECS={run_secs:.3}");
            eprintln!("VM_BENCH_INPUTS={repeats}");
            eprintln!("VM_BENCH_SECS_PER_INPUT={:.4}", run_secs / repeats.max(1) as f64);
            eprintln!("VM_BENCH_TOTAL_SECS={:.3}", t0.elapsed().as_secs_f64());
        })
        .unwrap()
        .join()
        .unwrap();
}
