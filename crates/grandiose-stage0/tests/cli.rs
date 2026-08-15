use std::{
    collections::BTreeMap,
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use grandiose_stage0::{
    BootstrapLimits, BootstrapManifest, BootstrapStage, CompilationMode, CompilationRequest,
    CompilerBuildIdentity, Digest, LogicalPath, PackageKey, SourceInput, StageZeroCompiler,
    decode_and_verify_program,
};

static NEXT_TEMPORARY: AtomicU64 = AtomicU64::new(0);

fn temporary_directory() -> std::path::PathBuf {
    let ordinal = NEXT_TEMPORARY.fetch_add(1, Ordering::Relaxed);
    let directory = std::env::temp_dir().join(format!(
        "grandiose-stage0-cli-{}-{ordinal}",
        std::process::id()
    ));
    fs::create_dir(&directory).expect("create isolated CLI test directory");
    directory
}

fn staging_files(directory: &std::path::Path) -> Vec<std::path::PathBuf> {
    fs::read_dir(directory)
        .unwrap()
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|extension| extension == "tmp"))
        .collect()
}

#[test]
fn cli_emits_verifies_and_runs_verified_vm_programs() {
    let directory = temporary_directory();
    let source = directory.join("main.glorious");
    let program = directory.join("main.g0vp");
    fs::write(&source, "pub fn main() -> Text { \"glorious\" }").unwrap();
    let compiler = env!("CARGO_BIN_EXE_grc-stage0");

    let emitted = Command::new(compiler)
        .args([
            "emit-vm",
            source.to_str().unwrap(),
            program.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        emitted.status.success(),
        "emit-vm failed: {}",
        String::from_utf8_lossy(&emitted.stderr)
    );
    assert!(fs::metadata(&program).unwrap().len() > 0);

    let verified = Command::new(compiler)
        .args(["verify-vm", program.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        verified.status.success(),
        "verify-vm failed: {}",
        String::from_utf8_lossy(&verified.stderr)
    );
    assert_eq!(String::from_utf8(verified.stdout).unwrap().trim().len(), 64);

    let run = Command::new(compiler)
        .args(["run", source.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "run failed: {}",
        String::from_utf8_lossy(&run.stderr)
    );
    assert_eq!(String::from_utf8(run.stdout).unwrap(), "\"glorious\"\n");

    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_failed_output_publication_preserves_existing_target_state() {
    let directory = temporary_directory();
    let source = directory.join("main.glorious");
    let output_directory = directory.join("program.g0vp");
    fs::write(&source, "pub fn main() -> i64 { 42 }").unwrap();
    fs::create_dir(&output_directory).unwrap();
    let sentinel = output_directory.join("previous-output");
    fs::write(&sentinel, b"visible before failed publication").unwrap();

    let emitted = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "emit-vm",
            source.to_str().unwrap(),
            output_directory.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(!emitted.status.success());
    assert_eq!(
        fs::read(sentinel).unwrap(),
        b"visible before failed publication"
    );
    assert!(staging_files(&directory).is_empty());
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_emits_stage_one_artifact_with_bound_bootstrap_manifest() {
    let directory = temporary_directory();
    let source = directory.join("main.glorious");
    let program = directory.join("stage1.g0vp");
    let manifest = directory.join("stage1.g0bm");
    fs::write(&source, "pub fn main() -> i64 { 42 }").unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "emit-bootstrap-vm",
            source.to_str().unwrap(),
            program.to_str().unwrap(),
            manifest.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "stage-one emission failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let program = decode_and_verify_program(&fs::read(&program).unwrap()).unwrap();
    let manifest = BootstrapManifest::decode(&fs::read(&manifest).unwrap()).unwrap();
    assert_eq!(manifest.stage.ordinal, 1);
    manifest.validate_verified_artifact(&program).unwrap();
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_verifies_adjacent_independently_bound_bootstrap_stages() {
    let directory = temporary_directory();
    let source = "pub fn main() -> i64 { 42 }";
    let compiler = StageZeroCompiler::new();
    let seed = Digest::of_bytes(b"cli-bootstrap-seed");
    let first = compiler
        .compile(bootstrap_request(source, seed, 1, None))
        .unwrap();
    let first_artifact = first.artifact.unwrap();
    let first_manifest = first.bootstrap_manifest.unwrap();
    let second = compiler
        .compile(bootstrap_request(
            source,
            first_manifest.artifact,
            2,
            Some(first_manifest.artifact),
        ))
        .unwrap();
    let second_artifact = second.artifact.unwrap();
    let second_manifest = second.bootstrap_manifest.unwrap();

    let first_program_path = directory.join("stage1.g0vp");
    let first_manifest_path = directory.join("stage1.g0bm");
    let second_program_path = directory.join("stage2.g0vp");
    let second_manifest_path = directory.join("stage2.g0bm");
    fs::write(&first_program_path, first_artifact.canonical_bytes()).unwrap();
    fs::write(&first_manifest_path, first_manifest.encode().unwrap()).unwrap();
    fs::write(&second_program_path, second_artifact.canonical_bytes()).unwrap();
    fs::write(&second_manifest_path, second_manifest.encode().unwrap()).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "verify-bootstrap",
            first_program_path.to_str().unwrap(),
            first_manifest_path.to_str().unwrap(),
            second_program_path.to_str().unwrap(),
            second_manifest_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "bootstrap verification failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap().trim().len(), 64);
    fs::remove_dir_all(directory).unwrap();
}

fn bootstrap_request(
    source: &str,
    compiler: Digest,
    ordinal: u32,
    expected_artifact: Option<Digest>,
) -> CompilationRequest {
    let package = PackageKey("app@0.1.0".into());
    CompilationRequest {
        build: CompilerBuildIdentity::stage0(compiler),
        mode: CompilationMode::Bootstrap(BootstrapStage {
            ordinal,
            producer: compiler,
            optimization_level: 0,
            limits: BootstrapLimits::new(4, 16 * 1024),
            expected_artifact,
        }),
        root_package: package.clone(),
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").unwrap(),
            source.as_bytes(),
        )],
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest: None,
    }
}

#[test]
fn cli_binds_private_runtime_leaves_only_from_explicit_host_manifest() {
    let directory = temporary_directory();
    let source = directory.join("runtime.glorious");
    fs::write(
        &source,
        "fn __g1_text_byte_len(value: Text) -> usize { () } pub fn main() -> usize { __g1_text_byte_len(\"a🦀\") }",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "--runtime-standard-library",
            "command@0.1.0",
            "--runtime-leaf",
            "text-byte-len",
            "crate",
            "__g1_text_byte_len",
            "run",
            source.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "runtime-manifest run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "5\n");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_binds_a_private_generic_int_leaf_from_an_explicit_manifest() {
    let directory = temporary_directory();
    let source = directory.join("runtime.glorious");
    fs::write(
        &source,
        "fn __g1_int_greater<T>(left: T, right: T) -> u32 { () } pub fn main() -> u32 { __g1_int_greater<i64>(0, -1) }",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "--runtime-standard-library",
            "command@0.1.0",
            "--runtime-leaf",
            "int-greater",
            "crate",
            "__g1_int_greater",
            "run",
            source.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "runtime-manifest run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "1\n");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_forwards_an_explicit_host_capability_to_the_request_world() {
    let directory = temporary_directory();
    let source = directory.join("host.glorious");
    fs::write(
        &source,
        "host clock fn now() -> i64; pub fn main() -> i64 { now() }",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args(["--capability", "clock", "check", source.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "capability request failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_binds_a_private_standard_library_leaf_from_an_explicit_package_source() {
    let directory = temporary_directory();
    let root = directory.join("main.glorious");
    let standard = directory.join("std.glorious");
    fs::write(
        &root,
        "use std::byte_len; pub fn main() -> usize { byte_len(\"a🦀\") }",
    )
    .unwrap();
    fs::write(
        &standard,
        "fn __g1_text_byte_len(value: Text) -> usize { () } pub fn byte_len(value: Text) -> usize { __g1_text_byte_len(value) }",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args([
            "--root-package",
            "app@0.1.0",
            "--source",
            "std@0.1.0",
            "src/lib.glorious",
            standard.to_str().unwrap(),
            "--runtime-standard-library",
            "std@0.1.0",
            "--runtime-leaf",
            "text-byte-len",
            "crate",
            "__g1_text_byte_len",
            "run",
            root.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "package runtime-manifest run failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "5\n");
    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_renders_invalid_request_failures_as_stable_diagnostics() {
    let directory = temporary_directory();
    let source = directory.join("invalid-utf8.glorious");
    fs::write(&source, [0xff]).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args(["check", source.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("G7018: source"), "{stderr}");
    assert!(
        !stderr.contains("Revision(Input") && !stderr.contains("ServiceError"),
        "CLI must not expose implementation enum formatting: {stderr}"
    );

    fs::remove_dir_all(directory).unwrap();
}

#[test]
fn cli_emits_structured_json_lines_for_compiler_diagnostics() {
    let directory = temporary_directory();
    let source = directory.join("invalid-utf8.glorious");
    fs::write(&source, [0xff]).unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_grc-stage0"))
        .args(["--diagnostics", "json", "check", source.to_str().unwrap()])
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert_eq!(
        stderr.lines().count(),
        1,
        "expected exactly one JSON line: {stderr}"
    );
    assert!(
        stderr.starts_with(
            "{\"code\":\"G7018\",\"class\":\"input_corruption\",\"severity\":\"error\","
        ),
        "{stderr}"
    );
    assert!(stderr.contains("\"primary\":null"), "{stderr}");
    assert!(stderr.contains("\"input_fingerprint\":null"), "{stderr}");
    assert!(!stderr.contains("grc-stage0:"), "{stderr}");

    fs::remove_dir_all(directory).unwrap();
}
