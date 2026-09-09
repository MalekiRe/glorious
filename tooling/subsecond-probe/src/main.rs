//! Disposable compiler requests across a Subsecond boundary; no compiler state survives a tick.
use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};
use std::{collections::BTreeMap, time::Duration};

fn main() {
    dioxus_devtools::connect_subsecond();
    subsecond::register_handler(std::sync::Arc::new(|| println!("PROBE_PATCH_APPLIED")));
    println!("PROBE_START pid={}", std::process::id());
    let mut tick = 0_u64;
    loop {
        tick += 1;
        // Pass a zero-sized function item and separate arguments. In Subsecond 0.7.6,
        // a pointer-sized capturing closure takes the non-detoured pointer path.
        subsecond::HotFn::current(compile_once).call((tick,));
        std::thread::sleep(Duration::from_secs(2));
    }
}

fn compile_once(tick: u64) {
    // Edit this marker while dx is serving to distinguish patching from a restart.
    let marker = "probe-v1";
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"subsecond-probe")),
        mode: CompilationMode::Build,
        root_package: PackageKey("app@0.1.0".into()),
        sources: vec![SourceInput::new(
            PackageKey("app@0.1.0".into()),
            LogicalPath::parse("src/main.glorious").unwrap(),
            b"pub fn main() -> i64 { 42 }".as_slice(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    };
    let result = StageZeroCompiler::new().compile(request).unwrap();
    assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
    let artifact = result.artifact.unwrap();
    let value = decode_and_verify_program(&artifact.canonical_bytes()).unwrap().run_i64().unwrap();
    assert_eq!(value, 42);
    println!("PROBE_TICK pid={} tick={tick} marker={marker} value={value} library_digest={:?}",
        std::process::id(), Digest::of_bytes(b"subsecond-library-probe"));
}
