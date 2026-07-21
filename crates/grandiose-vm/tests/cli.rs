use std::{fs, path::PathBuf, process::Command};

use grandiose_vm::{
    Artifact, Constant, Function, Instruction, TEXT, Type, UNIT,
    bytecode::{Import, Signature},
    verify::with_generated_cleanup_plans,
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
