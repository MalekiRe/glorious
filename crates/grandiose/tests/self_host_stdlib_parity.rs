// Self-host standard-library parity survey + supported-subset gate.
//
// The self-host compiler is a partial reimplementation. This file answers, for
// the standard_library native corpus, two distinct questions with one harness:
//
//   1. SUPPORTED SUBSET (asserted): the standard-library surface the self-host
//      compiler already accepts and that agrees with the Rust bootstrap oracle.
//      Today this is the injected `Result` nominal (construction + `handle`
//      dispatch); asserting it keeps genuine parity green and flags regressions.
//
//   2. FRONTIER (reported): a program drawn from each of the remaining
//      standard_library families that the Rust oracle ACCEPTS but the self-host
//      compiler still rejects. Each is printed with the self-host failing
//      compiler phase, so the ledger rows they back stay `unported` until the
//      self-host frontend/lowerer grows the corresponding surface. This is a
//      live roadmap, not a false claim of coverage.
//
// Both arms run the SAME self-host compiler bundle (compiled by the Rust
// bootstrap) inside the VM, feeding each source through the full frontend ->
// emission pipeline. 0 means accepted; 1..13 is the failing phase index.

use std::{
    fs,
    path::{Path, PathBuf},
};

use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode_with_options,
    compile_source_to_bytecode_with_options,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Artifact, SystemHost, Value, Vm, verify};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
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

fn bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_source = r#"
        mod frontend; mod backend; mod compiler; mod diagnostics;
        use compiler::CompileError; use compiler::InterfaceNameKind;
        use frontend::bodies::BodyError; use frontend::headers::HeaderError;
        use frontend::scanner::ScanError; use frontend::resolution::ResolutionError;
        use frontend::elaboration::ElaborationError; use backend::lowering::LoweringError; use backend::emission::EmissionError;
        classify_compile_error(source: String) -> u8 {
            handle compiler::compile_source(&source) {
                Result::Ok(_) => 0,
                Result::Err(error) => handle error {
                    CompileError::Lex(_) => 1, CompileError::Scan(_) => 2, CompileError::Headers(_) => 3,
                    CompileError::ResolutionIndex(_) => 4, CompileError::InterfaceCollection(_) => 5,
                    CompileError::DeclarationName(_) => 6, CompileError::BodyParse(_, _) => 7,
                    CompileError::BodyResolution(_, _) => 8, CompileError::BodyElaboration(_, _) => 9,
                    CompileError::Lowering(_, _) => 10, CompileError::InterfaceName(_, _) => 11,
                    CompileError::UnsupportedInterfaceType(_) => 12, CompileError::Emission(_) => 13
                }
            }
        }
        main() { run_compiler_host(diagnostics::application) }
    "#;
    let primary = Segment::new(root.join("main.glorious").to_string_lossy(), primary_source);
    SourceBundle::distributed(
        primary,
        self_host_module_paths(&root).into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("self-hosted artifact is missing `{name}`")) as u32
}

const PHASES: [&str; 14] = [
    "accepted",
    "lex", "scan", "headers", "resolution-index", "interface-collection",
    "declaration-name", "body-parse", "body-resolution", "body-elaboration",
    "lowering", "interface-name", "unsupported-interface-type", "emission",
];

// The supported subset: programs the self-host compiler accepts AND that the
// Rust oracle also accepts (real parity, asserted). This now includes the
// injected scalar standard-library mirror (wrapping_*/bit_*/shift_*) whose
// generic wrappers resolve through the appended scalar prelude and lower to
// their bytecode primitives, matching the native distributed standard surface.
const SUPPORTED: [(&str, &str); 12] = [
    ("result_constructor_and_dispatch", "ok(v: i64) -> Result<i64, i64> { Result::Ok(v) } pick() -> i64 { handle ok(5) { Result::Ok(x) => x, Result::Err(_) => 0 } } main() { () }"), ("result_err_and_dispatch", "bad(v: i64) -> Result<i64, i64> { Result::Err(v) } pick() -> i64 { handle bad(9) { Result::Ok(_) => 0, Result::Err(e) => e } } main() { () }"), ("scalar_wrapping_add_i64", "add(a: i64, b: i64) -> i64 { wrapping_add(move a, move b) } main() { () }"), ("scalar_wrapping_add_u8", "add(a: u8, b: u8) -> u8 { wrapping_add(move a, move b) } main() { () }"), ("scalar_wrapping_sub_i64", "sub(a: i64, b: i64) -> i64 { wrapping_sub(move a, move b) } main() { () }"), ("scalar_wrapping_mul_u64", "mul(a: u64, b: u64) -> u64 { wrapping_mul(move a, move b) } main() { () }"), ("scalar_bit_and_u64", "w(a: u64, b: u64) -> u64 { bit_and(move a, move b) } main() { () }"), ("scalar_bit_or_u64", "w(a: u64, b: u64) -> u64 { bit_or(move a, move b) } main() { () }"), ("scalar_bit_xor_i64", "w(a: i64, b: i64) -> i64 { bit_xor(move a, move b) } main() { () }"), ("scalar_bit_not_i64", "w(a: i64) -> i64 { bit_not(move a) } main() { () }"), ("scalar_shift_left_i64", "w(v: i64, c: u32) -> i64 { shift_left(move v, move c) } main() { () }"), ("scalar_shift_right_u64", "w(v: u64, c: u32) -> u64 { shift_right(move v, move c) } main() { () }"),
];

// The frontier: programs the Rust oracle accepts that the self-host compiler
// does not yet accept (blocker phase printed). These keep ledger rows unported.
const FRONTIER: [(&str, &str); 12] = [
    ("collection_extended_surface", "empty() -> Vec<i64> { Vec::new() } main() { () }"), ("collection_foundations", "empty() -> Vec<u64> { Vec::new() } main() { () }"), ("hash_collections", "m() -> HashMap<u64, u64> { HashMap::new() } main() { () }"), ("index_vec_traversal", "v() -> IndexVec<u8, i64> { IndexVec::new() } main() { () }"), ("range_helpers", "r(start: usize, end: usize) -> Range<usize> { Range { start: move start, end: move end } } main() { () }"), ("option_surface", "some(v: i64) -> Option<i64> { Option::Some(v) } main() { () }"), ("slot_surface", "s() -> Slot<i64> { slot_empty() } main() { () }"), ("toolkit_foundations", "b() -> StepBudget { StepBudget::new(5) } main() { () }"), ("vec_copying_growth", "e() -> Vec<i64> { Vec::new() } main() { () }"), ("vec_deque", "dq() -> VecDeque<i64> { VecDeque::new() } main() { () }"), ("vec_destructive_shrink", "e() -> Vec<u64> { Vec::new() } main() { () }"), ("vec_into_iter", "e() -> Vec<i64> { Vec::new() } main() { () }"),
];

#[test]
fn self_host_stdlib_parity_supported_subset_and_frontier() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let artifact = compile_bundle_to_bytecode_with_options(
                &bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let classify = function_id(&artifact, "classify_compile_error");
            let verified = verify(artifact).unwrap();

            // Supported subset: genuine accept parity (both accept).
            for (name, source) in SUPPORTED {
                let oracle =
                    compile_source_to_bytecode_with_options(name, source, CompileOptions::default())
                        .is_ok();
                assert!(
                    oracle,
                    "bootstrap oracle should accept supported std-lib case {name:?}: {source:?}"
                );
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(Vec::<std::ffi::OsString>::new()),
                )
                .unwrap();
                let Value::U64(class) = vm
                    .run(classify, vec![Value::Text(source.to_owned().into())])
                    .unwrap()
                else {
                    panic!("no class for {name:?}");
                };
                assert_eq!(
                    class, 0,
                    "self-host regressed on supported std-lib case {name:?}: phase {class} ({})",
                    PHASES[class as usize]
                );
                eprintln!("STDLIB-PARITY supported {} => accepted (parity)", name);
            }

            // Frontier: reported, not asserted. Oracle accepts; self-host rejects
            // at the printed phase. Future work turns each of these green.
            for (name, source) in FRONTIER {
                let oracle =
                    compile_source_to_bytecode_with_options(name, source, CompileOptions::default())
                        .is_ok();
                assert!(
                    oracle,
                    "frontier case {name:?} is not oracle-valid (fix the corpus): {source:?}"
                );
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(Vec::<std::ffi::OsString>::new()),
                )
                .unwrap();
                let Value::U64(class) = vm
                    .run(classify, vec![Value::Text(source.to_owned().into())])
                    .unwrap()
                else {
                    panic!("no class for frontier {name:?}");
                };
                eprintln!(
                    "STDLIB-PARITY frontier {} => oracle=accepted self-host={} ({})",
                    name, class, PHASES[class as usize]
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}


// Genuine semantic parity for the injected scalar surface: the self-hosted
// compiler must not merely ACCEPT wrapping_add but lower it to the wrapping-add
// primitive truthfully (matching the Rust-oracle result). One program exercising
// each lowering surface is compiled by BOTH compilers and its observable result
// compared.
#[test]
fn self_host_stdlib_scalar_semantics_match_native() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let cases: [(&str, &str); 4] = [
                ("wrapping_add", "add(a: i64, b: i64) -> i64 { wrapping_add(move a, move b) } compute() -> i64 { add(20, 22) } main() { () }"),
                ("wrapping_sub", "sub(a: i64, b: i64) -> i64 { wrapping_sub(move a, move b) } compute() -> i64 { sub(50, 8) } main() { () }"),
                ("wrapping_mul", "mul(a: u64, b: u64) -> u64 { wrapping_mul(move a, move b) } compute() -> u64 { mul(6, 7) } main() { () }"),
                ("bit_xor", "x(a: i64, b: i64) -> i64 { bit_xor(move a, move b) } compute() -> i64 { x(12, 10) } main() { () }"),
            ];
            let oracle_results: Vec<Value> = cases.iter().map(|(name, src)| {
                let artifact = compile_source_to_bytecode_with_options(
                    name, src, CompileOptions::default()).unwrap();
                let fid = function_id(&artifact, "compute");
                let vm = Vm::with_host(verify(artifact).unwrap(),
                    ["process.args","fs.read","fs.write","diagnostic"], SystemHost::new(Vec::new())).unwrap();
                vm.run(fid, vec![]).unwrap()
            }).collect();
            let artifact = compile_bundle_to_bytecode_with_options(
                &bundle(),
                CompileOptions { optimization_level: OptimizationLevel::O2 },
            ).unwrap();
            let main_entry = artifact.entry_function.expect("self-host compiler entry");
            let verified = verify(artifact).unwrap();
            let dir = tempfile::tempdir().unwrap();
            for (i, (name, src)) in cases.iter().enumerate() {
                let input = dir.path().join(format!("in{i}.glorious"));
                let output = dir.path().join(format!("out{i}.grbc"));
                fs::write(&input, src).unwrap();
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        output.clone().into_os_string(),
                        input.clone().into_os_string(),
                    ]),
                ).unwrap();
                assert_eq!(vm.run(main_entry, vec![]).unwrap(), Value::Unit);
                let bytes = fs::read(&output).unwrap();
                let decoded = Artifact::decode(&bytes).expect("self-host GRBC must decode");
                let fid = decoded.functions.iter().position(|f| f.name == "compute")
                    .unwrap_or_else(|| panic!("{name}: self-host artifact missing compute")) as u32;
                let rvm = Vm::with_host(
                    grandiose_vm::verify::load_verified(&bytes).unwrap(),
                    ["process.args","fs.read","fs.write","diagnostic"], SystemHost::new(Vec::new())).unwrap();
                let res = rvm.run(fid, vec![]).unwrap();
                assert_eq!(
                    res, oracle_results[i],
                    "scalar semantics diverged for {name}: native={:?} self-host={:?}",
                    oracle_results[i], res
                );
                eprintln!("STDLIB-PARITY scalar semantics {name} => native={:?} self-host={:?} (match)", oracle_results[i], res);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

