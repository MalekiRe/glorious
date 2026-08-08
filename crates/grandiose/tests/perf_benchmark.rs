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

#[test]
#[ignore = "manual perf benchmark"]
fn self_host_body_benchmark() {
    let repeats: usize = std::env::var("G1_PERF_REPEATS")
        .ok().and_then(|v| v.parse().ok()).unwrap_or(1);

    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let t0 = Instant::now();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::bodies::application"),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let compile_secs = t0.elapsed().as_secs_f64();
            eprintln!("PERF_COMPILE_SECS={compile_secs:.3}");
            eprintln!("PERF_FUNCTIONS={}", phases.artifact.functions.len());
            eprintln!("PERF_INSTRUCTIONS={}", phases.artifact.code.len());

            let entry = phases.artifact.entry_function.unwrap();
            let verified = verify(phases.artifact.clone()).unwrap();
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
            eprintln!("PERF_RUN_SECS={run_secs:.3}");
            eprintln!("PERF_INPUTS={repeats}");
            eprintln!("PERF_SECS_PER_INPUT={:.3}", run_secs / repeats.max(1) as f64);
            eprintln!("PERF_TOTAL_SECS={:.3}", t0.elapsed().as_secs_f64());
        })
        .unwrap()
        .join()
        .unwrap();
}


fn self_host_module_paths(root: &Path) -> [PathBuf; 17] {
    [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/lossless/lossless.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
        root.join("backend/backend.glorious"),
        root.join("backend/artifact/artifact.glorious"),
        root.join("backend/lowering/lowering.glorious"),
        root.join("backend/emission/emission.glorious"),
        root.join("compiler/compiler.glorious"),
        root.join("diagnostics/diagnostics.glorious"),
        root.join("diagnostics/model/model.glorious"),
        root.join("diagnostics/source_errors/source_errors.glorious"),
        root.join("diagnostics/backend_errors/backend_errors.glorious"),
    ]
}

fn self_host_compiler_pipeline_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_source = [
        r#"
            mod frontend;
            mod backend;
            mod compiler;
            mod diagnostics;

            use compiler::CompileError;
            use compiler::InterfaceNameKind;
            use frontend::bodies::BodyError;
            use frontend::headers::HeaderError;
            use frontend::scanner::ScanError;
            use frontend::resolution::ResolutionError;
            use frontend::elaboration::ElaborationError;
            use backend::lowering::LoweringError;
            use backend::emission::EmissionError;

            classify_compile_error(source: String) -> u8 {
                handle compiler::compile_source(&source) {
                    Result::Ok(_) => 0,
                    Result::Err(error) => handle error {
                        CompileError::Lex(_) => 1,
                        CompileError::Scan(_) => 2,
                        CompileError::Headers(_) => 3,
                        CompileError::ResolutionIndex(_) => 4,
                        CompileError::InterfaceCollection(_) => 5,
                        CompileError::DeclarationName(_) => 6,
                        CompileError::BodyParse(_, _) => 7,
                        CompileError::BodyResolution(_, _) => 8,
                        CompileError::BodyElaboration(_, _) => 9,
                        CompileError::Lowering(_, _) => 10,
                        CompileError::InterfaceName(_, _) => 11,
                        CompileError::UnsupportedInterfaceType(_) => 12,
                        CompileError::Emission(_) => 13
                    }
                }
            }

            main() { run_compiler_host(diagnostics::application) }
        "#,
    ]
    .concat();
    let primary = Segment::new(root.join("main.glorious").to_string_lossy(), primary_source);
    SourceBundle::distributed(
        primary,
        self_host_module_paths(&root).into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

#[test]
#[ignore = "manual perf benchmark"]
fn self_host_full_pipeline_benchmark() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let t0 = Instant::now();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_compiler_pipeline_bundle(),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let compile_secs = t0.elapsed().as_secs_f64();
            eprintln!("FULL_COMPILE_SECS={compile_secs:.3}");
            eprintln!("FULL_FUNCTIONS={}", phases.artifact.functions.len());
            eprintln!("FULL_INSTRUCTIONS={}", phases.artifact.code.len());
            let classify = phases.artifact.functions.iter()
                .position(|f| f.name == "classify_compile_error").unwrap() as u32;
            let verified = verify(phases.artifact.clone()).unwrap();
            let vm = Vm::with_host(
                verified, ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(Vec::<std::ffi::OsString>::new()),
            ).unwrap();
            let source = "pipeline_identity(value: i64) -> i64 { value } main() { () }";
            let t1 = Instant::now();
            let Value::U64(class) = vm.run(classify, vec![Value::Text(source.to_owned().into())]).unwrap() else { panic!() };
            let run_secs = t1.elapsed().as_secs_f64();
            eprintln!("FULL_RUN_SECS={run_secs:.3}");
            eprintln!("FULL_CLASS={class}");
            eprintln!("FULL_TOTAL_SECS={:.3}", t0.elapsed().as_secs_f64());
        })
        .unwrap()
        .join()
        .unwrap();
}
