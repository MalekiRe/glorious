use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
};

use grandiose_stage0::{BootstrapManifest, decode_and_verify_program};

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
