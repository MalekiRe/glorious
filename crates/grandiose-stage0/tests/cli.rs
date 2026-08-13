use std::{
    fs,
    process::Command,
    sync::atomic::{AtomicU64, Ordering},
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
