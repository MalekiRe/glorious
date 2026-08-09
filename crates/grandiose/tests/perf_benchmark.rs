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


use grandiose_vm::bytecode::Instruction as Insn;
use grandiose_vm::bytecode::Register;

fn reg_of_insn(ins: &Insn) -> Option<(Register, Register)> {
    match ins {
        Insn::Move { dst, src } => Some((*dst, *src)),
        Insn::Copy { dst, src } => Some((*dst, *src)),
        Insn::DerefMove { dst, src } => Some((*dst, *src)),
        Insn::DerefCopy { dst, src } => Some((*dst, *src)),
        _ => None,
    }
}

fn insn_writes(ins: &Insn) -> Vec<Register> {
    match ins {
        Insn::Const { dst, .. } => vec![*dst],
        Insn::Move { dst, .. } => vec![*dst],
        Insn::Copy { dst, .. } => vec![*dst],
        Insn::BorrowShared { dst, .. } => vec![*dst],
        Insn::BorrowUnique { dst, .. } => vec![*dst],
        Insn::ReborrowShared { dst, .. } => vec![*dst],
        Insn::ReborrowUnique { dst, .. } => vec![*dst],
        Insn::DerefCopy { dst, .. } => vec![*dst],
        Insn::DerefReborrowShared { dst, .. } => vec![*dst],
        Insn::DerefReborrowUnique { dst, .. } => vec![*dst],
        Insn::DerefMove { dst, .. } => vec![*dst],
        Insn::Construct { dst, .. } => vec![*dst],
        Insn::ProjectMove { dst, .. } => vec![*dst],
        Insn::ProjectCopy { dst, .. } => vec![*dst],
        Insn::ProjectBorrowShared { dst, .. } => vec![*dst],
        Insn::ProjectBorrowUnique { dst, .. } => vec![*dst],
        Insn::EnumTag { dst, .. } => vec![*dst],
        Insn::Primitive { dst, .. } => vec![*dst],
        _ => vec![],
    }
}

fn insn_reads(ins: &Insn) -> Vec<Register> {
    match ins {
        Insn::Move { src, .. } => vec![*src],
        Insn::Copy { src, .. } => vec![*src],
        Insn::BorrowShared { src, .. } => vec![*src],
        Insn::BorrowUnique { src, .. } => vec![*src],
        Insn::ReborrowShared { src, .. } => vec![*src],
        Insn::ReborrowUnique { src, .. } => vec![*src],
        Insn::DerefCopy { src, .. } => vec![*src],
        Insn::DerefReborrowShared { src, .. } => vec![*src],
        Insn::DerefReborrowUnique { src, .. } => vec![*src],
        Insn::DerefMove { src, .. } => vec![*src],
        Insn::DerefStore { src, .. } => vec![*src],
        Insn::EndBorrow { reference } => vec![*reference],
        Insn::Construct { fields, .. } => fields.clone(),
        Insn::ProjectMove { src, .. } => vec![*src],
        Insn::ProjectCopy { src, .. } => vec![*src],
        Insn::ProjectBorrowShared { src, .. } => vec![*src],
        Insn::ProjectBorrowUnique { src, .. } => vec![*src],
        Insn::EnumTag { src, .. } => vec![*src],
        Insn::Deconstruct { src } => vec![*src],
        Insn::Drop { register } => vec![*register],
        Insn::Primitive { args, .. } => args.clone(),
        Insn::Switch { discr, cases, .. } => {
            let mut v = vec![*discr];
            for (_, t) in cases { v.push(*t); }
            v
        }
        Insn::Call { args, .. } => args.clone(),
        Insn::TailCall { args, .. } => args.clone(),
        Insn::CallSelf { args, .. } => args.clone(),
        Insn::TailCallSelf { args, .. } => args.clone(),
        Insn::CallKnownReceiver { receiver, args, .. } => {
            let mut v = vec![*receiver]; v.extend(args.clone()); v
        }
        Insn::TailCallKnownReceiver { receiver, args, .. } => {
            let mut v = vec![*receiver]; v.extend(args.clone()); v
        }
        Insn::MakeCallable { captures, .. } => captures.clone(),
        Insn::MakeHandler { clauses, .. } => clauses.clone(),
        Insn::MakeHandlerShared { captures, .. } => captures.clone(),
        Insn::MakeBindingPack { payloads, .. } => payloads.clone(),
        Insn::CallIndirect { callable, args, .. } => {
            let mut v = vec![*callable]; v.extend(args.clone()); v
        }
        Insn::TailCallIndirect { callable, args, .. } => {
            let mut v = vec![*callable]; v.extend(args.clone()); v
        }
        Insn::Handle { handler, body, args, .. } => {
            let mut v = vec![*handler, *body]; v.extend(args.clone()); v
        }
        Insn::Perform { payloads, .. } => payloads.clone(),
        Insn::Resume { resumption, value, .. } => vec![*resumption, *value],
        Insn::TailResume { resumption, value, .. } => vec![*resumption, *value],
        Insn::Cancel { resumption, .. } => vec![*resumption],
        Insn::HostCall { args, .. } => args.clone(),
        Insn::LabelPush { result_register, .. } => vec![*result_register],
        Insn::Return { src } => { if let Some(s) = src { vec![*s] } else { vec![] } }
        _ => vec![],
    }
}

fn insn_succs(pc: usize, ins: &Insn, code_len: usize) -> Vec<usize> {
    match ins {
        Insn::Jump { target } => vec![*target as usize],
        Insn::Switch { cases, otherwise, .. } => {
            let mut v = cases.iter().map(|(_, t)| *t as usize).collect::<Vec<_>>();
            v.push(*otherwise as usize);
            v
        }
        Insn::Return { .. } | Insn::Unreachable | Insn::Abort { .. } | Insn::TailCall { .. }
        | Insn::TailCallSelf { .. } | Insn::TailCallKnownReceiver { .. } | Insn::TailCallIndirect { .. }
        | Insn::TailResume { .. } | Insn::Leave { .. } => vec![],
        _ => {
            if pc + 1 < code_len { vec![pc + 1] } else { vec![] }
        }
    }
}

#[test]
#[ignore = "manual perf instrumentation"]
fn self_host_body_instrument() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::bodies::application"),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let code = &phases.artifact.code;
            let mut hist: std::collections::BTreeMap<String, usize> = Default::default();
            for ins in code {
                let name = format!("{:?}", ins).split('{').next().unwrap_or("?").to_string();
                *hist.entry(name).or_default() += 1;
            }
            eprintln!("=== OPCODE HISTOGRAM ===");
            for (name, count) in &hist {
                eprintln!("{name}: {count}");
            }
            let names: Vec<&str> = phases.artifact.functions.iter().map(|f| f.name.as_str()).collect();
            let hot = [1657usize, 2359, 954, 1876, 113, 1998, 955, 974, 196];
            eprintln!("=== HOT FUNCTION NAMES ===");
            for idx in hot {
                if let Some(name) = names.get(idx) {
                    eprintln!("f{idx}: {} (len {})", name, phases.artifact.functions[idx].code_len);
                }
            }
            let mut dead_moves = 0usize;
            let mut dead_copies = 0usize;
            let mut self_moves = 0usize;
            let mut dead_drops = 0usize;
            let mut total_moves_copies = 0usize;
            let mut all_drops = 0usize;
            let analyzed = code.len();
            for f in &phases.artifact.functions {
                let start = f.code_start as usize;
                let end = start + f.code_len as usize;
                let n = end - start;
                if n == 0 { continue; }
                let mut live_out: Vec<Vec<Register>> = vec![vec![]; n];
                let mut live_in: Vec<Vec<Register>> = vec![vec![]; n];
                loop {
                    let mut changed = false;
                    for i in (0..n).rev() {
                        let succs = insn_succs(i, &code[start + i], n);
                        let mut lo: Vec<Register> = Vec::new();
                        for s in &succs {
                            if *s < n { lo.extend(live_in[*s].iter().copied()); }
                        }
                        lo.sort_unstable(); lo.dedup();
                        if lo != live_out[i] { live_out[i] = lo; changed = true; }
                        let writes = insn_writes(&code[start + i]);
                        let reads = insn_reads(&code[start + i]);
                        let mut li = reads.clone();
                        li.extend(live_out[i].iter().copied());
                        li.retain(|r| !writes.contains(r));
                        li.sort_unstable(); li.dedup();
                        if li != live_in[i] { live_in[i] = li; changed = true; }
                    }
                    if !changed { break; }
                }
                for i in 0..n {
                    let ins = &code[start + i];
                    if let Some((dst, src)) = reg_of_insn(ins) {
                        total_moves_copies += 1;
                        if dst == src {
                            self_moves += 1;
                        } else if !live_out[i].contains(&dst) {
                            match ins {
                                Insn::Move { .. } => dead_moves += 1,
                                _ => dead_copies += 1,
                            }
                        }
                    }
                    if let Insn::Drop { .. } = ins {
                        all_drops += 1;
                        // drop whose register is not read (incl. not dropped again)
                        if !live_out[i].contains(&register_of_drop(ins)) {
                            dead_drops += 1;
                        }
                    }
                }
            }
            eprintln!("TOTAL_INSNS={analyzed}");
            eprintln!("TOTAL_MOVES_COPIES={total_moves_copies}");
            eprintln!("SELF_MOVES={self_moves}");
            eprintln!("DEAD_MOVES={dead_moves}");
            eprintln!("DEAD_COPIES={dead_copies}");
            eprintln!("ALL_DROPS={all_drops}");
            eprintln!("DEAD_DROPS={dead_drops}");
        })
        .unwrap()
        .join()
        .unwrap();
}

fn register_of_drop(ins: &Insn) -> Register {
    match ins {
        Insn::Drop { register } => *register,
        _ => unreachable!(),
    }
}


#[test]
#[ignore = "manual perf instrumentation"]
fn self_host_body_dump_artifact() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle("probe::bodies::application"),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            )
            .unwrap();
            let mut out = String::new();
            out.push_str(&format!("TOTAL {}\n", phases.artifact.code.len()));
            for (i, f) in phases.artifact.functions.iter().enumerate() {
                out.push_str(&format!("FUNC {i} {} start={} len={} regs={:?}\n", f.name, f.code_start, f.code_len, f.register_types));
            }
            out.push_str(&format!("TYPES {}\n", types_pretty(&phases.artifact.types)));
            out.push_str(&format!("CONSTS {:?}\n", phases.artifact.constants));
            out.push_str(&format!("GLUE {:?}\n", phases.artifact.drop_glue));
            for (pc, ins) in phases.artifact.code.iter().enumerate() {
                out.push_str(&format!("{pc} {:?}\n", ins));
            }
            std::fs::write("/tmp/g24_body_artifact.txt", out).unwrap();
        })
        .unwrap()
        .join()
        .unwrap();
}

fn types_pretty(types: &[grandiose_vm::bytecode::Type]) -> String {
    let mut s = String::new();
    for (i, t) in types.iter().enumerate() {
        s.push_str(&format!("{i}: {:?}\n", t));
    }
    s
}
