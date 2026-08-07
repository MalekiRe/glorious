use std::{fs, path::PathBuf, process::Command};

use grandiose_vm::{
    ACCEPTED_SEED_IDENTITIES, Artifact, Constant, Function, Instruction, RELEASED_SEED_IDENTITY,
    SEED_IDENTITY_VERSION, TEXT, Type, UNIT,
    bytecode::{Import, Signature},
    verify::with_generated_cleanup_plans,
    vm::MAX_PRIMITIVE_ALLOCATION_BYTES,
};

struct TempArtifact(PathBuf);

impl Drop for TempArtifact {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn unit_program() -> TempArtifact {
    let path = std::env::temp_dir().join(format!(
        "grandiose-vm-cli-{}-{}.grbc",
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    let artifact = Artifact {
        required_features: 1,
        entry_function: Some(0),
        types: Type::predefined(),
        constants: vec![Constant::Unit],
        imports: vec![],
        protocols: vec![],
        handler_defs: vec![],
        cleanups: vec![],
        exports: vec![],
        drop_glue: vec![],
        reference_return_contracts: vec![],
        functions: vec![Function {
            flags: 0,
            name: "main".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, UNIT],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        }],
        code: vec![
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
    };
    fs::write(
        &path,
        with_generated_cleanup_plans(artifact).unwrap().encode(),
    )
    .unwrap();
    TempArtifact(path)
}

fn process_args_program() -> TempArtifact {
    let path = std::env::temp_dir().join(format!(
        "grandiose-vm-cli-{}-process-args.grbc",
        std::process::id()
    ));
    let mut types = Type::predefined();
    types.push(Type::Array { element: TEXT }.restricted(false, true));
    let artifact = Artifact {
        required_features: 1 | (1 << 5),
        entry_function: Some(0),
        types,
        constants: vec![Constant::Unit],
        imports: vec![Import {
            capability: "process.args".into(),
            symbol: "get".into(),
            signature: Signature {
                params: vec![],
                result: 19,
                outward_protocols: vec![],
            },
            may_trap: true,
        }],
        protocols: vec![],
        handler_defs: vec![],
        cleanups: vec![],
        exports: vec![],
        drop_glue: vec![],
        reference_return_contracts: vec![],
        functions: vec![Function {
            flags: 0,
            name: "main".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, 19, UNIT],
            code_start: 0,
            code_len: 4,
            label_slot_count: 0,
        }],
        code: vec![
            Instruction::HostCall {
                dst: Some(1),
                import: 0,
                args: vec![],
            },
            Instruction::Drop { register: 1 },
            Instruction::Const {
                dst: 2,
                constant: 0,
            },
            Instruction::Return { src: Some(2) },
        ],
    };
    fs::write(
        &path,
        with_generated_cleanup_plans(artifact).unwrap().encode(),
    )
    .unwrap();
    TempArtifact(path)
}

fn allocation_limit_program() -> TempArtifact {
    let path = std::env::temp_dir().join(format!(
        "grandiose-vm-cli-{}-allocation-limit.grbc",
        std::process::id()
    ));
    let mut types = Type::predefined();
    let array = types.len() as u32;
    types.push(Type::Array { element: UNIT }.restricted(false, true));
    let mut artifact = Artifact {
        required_features: 1,
        entry_function: Some(0),
        types,
        constants: vec![Constant::Usize(MAX_PRIMITIVE_ALLOCATION_BYTES as u64 + 1), Constant::Unit],
        functions: vec![Function {
            flags: 0,
            name: "main".into(),
            params: vec![],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, grandiose_vm::USIZE, UNIT, array, UNIT],
            code_start: 0,
            code_len: 6,
            label_slot_count: 0,
        }],
        code: vec![
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Const {
                dst: 2,
                constant: 1,
            },
            Instruction::Primitive {
                dst: 3,
                op: grandiose_vm::Primitive::ArrayNew,
                args: vec![1, 2],
            },
            Instruction::Drop { register: 3 },
            Instruction::Const {
                dst: 4,
                constant: 1,
            },
            Instruction::Return { src: Some(4) },
        ],
        ..Artifact::default()
    };
    artifact.canonicalize_constants();
    fs::write(
        &path,
        with_generated_cleanup_plans(artifact).unwrap().encode(),
    )
    .unwrap();
    TempArtifact(path)
}

#[test]
fn reports_the_versioned_vm_and_artifact_compatibility_contract() {
    let output = Command::new(env!("CARGO_BIN_EXE_grvm"))
        .arg("--capabilities")
        .output()
        .unwrap();
    assert!(output.status.success());
    let capabilities = String::from_utf8(output.stdout).unwrap();
    assert!(capabilities.contains(r#""contract":1"#));
    assert!(capabilities.contains(r#""contract-min":1"#));
    assert!(capabilities.contains(r#""contract-max":1"#));
    assert!(capabilities.contains(r#""artifact-major":1"#));
    assert!(capabilities.contains(r#""artifact-minor-min":0"#));
    assert!(capabilities.contains(r#""artifact-minor-max":0"#));
    assert!(
        capabilities.contains(&format!(
            r#""seed-identity-version":{SEED_IDENTITY_VERSION}"#
        )),
        "{capabilities}"
    );
    for identity in ACCEPTED_SEED_IDENTITIES {
        assert!(capabilities.contains(identity), "{capabilities}");
    }

    assert!(
        !Command::new(env!("CARGO_BIN_EXE_grvm"))
            .args(["--capabilities", "extra"])
            .status()
            .unwrap()
            .success()
    );
}

#[test]
fn released_seed_identity_is_checked_before_loading_or_execution() {
    let grvm = env!("CARGO_BIN_EXE_grvm");
    let mismatch = Command::new(grvm)
        .args([
            "run",
            "--seed-identity",
            "incompatible-seed",
            "does-not-exist.grbc",
        ])
        .output()
        .unwrap();
    assert_eq!(mismatch.status.code(), Some(1));
    let stderr = String::from_utf8(mismatch.stderr).unwrap();
    assert!(
        stderr.contains("incompatible released-seed identity"),
        "{stderr}"
    );
    assert!(!stderr.contains("does-not-exist"), "{stderr}");

    let artifact = unit_program();
    assert!(
        Command::new(grvm)
            .args(["run", "--seed-identity", RELEASED_SEED_IDENTITY])
            .arg(&artifact.0)
            .status()
            .unwrap()
            .success()
    );
    for identity in ACCEPTED_SEED_IDENTITIES {
        assert!(
            Command::new(grvm)
                .args(["run", "--seed-identity", identity])
                .arg(&artifact.0)
                .status()
                .unwrap()
                .success()
        );
    }
}

#[test]
fn supervised_allocation_limit_is_distinct_from_an_internal_fault() {
    let artifact = allocation_limit_program();
    let output = Command::new(env!("CARGO_BIN_EXE_grvm"))
        .args(["run", "--memory-limit", "4096MiB"])
        .arg(&artifact.0)
        .output()
        .unwrap();
    assert_eq!(output.status.code(), Some(125));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("memory-limit"), "{stderr}");
    assert!(!stderr.contains("internal"), "{stderr}");
}

#[test]
fn verifies_and_runs_normative_executable_directly_and_supervised() {
    let artifact = unit_program();
    let grvm = env!("CARGO_BIN_EXE_grvm");

    assert!(
        Command::new(grvm)
            .arg("verify")
            .arg(&artifact.0)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(grvm)
            .arg("run")
            .arg(&artifact.0)
            .status()
            .unwrap()
            .success()
    );
    assert!(
        Command::new(grvm)
            .args(["run", "--time-limit", "5s", "--memory-limit", "1024MiB"])
            .arg(&artifact.0)
            .status()
            .unwrap()
            .success()
    );
}

#[test]
fn passes_owned_program_arguments_to_the_granted_process_host() {
    let artifact = process_args_program();
    let grvm = env!("CARGO_BIN_EXE_grvm");

    assert!(
        Command::new(grvm)
            .args(["run", "--allow", "process.args"])
            .arg(&artifact.0)
            .args(["--", "one", "two"])
            .status()
            .unwrap()
            .success()
    );
    assert!(
        !Command::new(grvm)
            .arg("run")
            .arg(&artifact.0)
            .args(["--", "one"])
            .status()
            .unwrap()
            .success()
    );
}

#[cfg(unix)]
#[test]
fn unused_non_utf8_program_arguments_do_not_fault() {
    use std::{ffi::OsString, os::unix::ffi::OsStringExt};

    let artifact = unit_program();
    assert!(
        Command::new(env!("CARGO_BIN_EXE_grvm"))
            .arg("run")
            .arg(&artifact.0)
            .arg("--")
            .arg(OsString::from_vec(vec![0xff]))
            .status()
            .unwrap()
            .success()
    );
}
