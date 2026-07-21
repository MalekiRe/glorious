//! Explicit maintainer tool for regenerating the checked-in G1 compatibility
//! fixtures. Run only when an intentional bytecode-format change has followed
//! the release discipline in `docs/bytecode.md`.

use std::{fs, path::PathBuf};

use grandiose_vm::{
    Artifact, Constant, Function, I64, Instruction, UNIT, verify::with_generated_cleanup_plans,
};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let output = std::env::args_os()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("tests/fixtures"));
    fs::create_dir_all(&output)?;
    fs::write(
        output.join("g1-unit-return.grbc"),
        canonical(unit_program()),
    )?;
    fs::write(output.join("g1-i64-return.grbc"), canonical(i64_program()))?;
    Ok(())
}

fn canonical(artifact: Artifact) -> Vec<u8> {
    with_generated_cleanup_plans(artifact).unwrap().encode()
}

fn function(return_type: u32, register_types: Vec<u32>, code_len: u32) -> Function {
    Function {
        name: "main".into(),
        flags: 0,
        params: vec![],
        return_type,
        outward_protocols: vec![],
        receiver_mode: None,
        register_types,
        code_start: 0,
        code_len,
        label_slot_count: 0,
    }
}

fn unit_program() -> Artifact {
    Artifact {
        entry_function: Some(0),
        functions: vec![function(UNIT, vec![UNIT], 1)],
        code: vec![Instruction::Return { src: None }],
        ..Artifact::default()
    }
}

fn i64_program() -> Artifact {
    Artifact {
        constants: vec![Constant::I64(42)],
        functions: vec![function(I64, vec![UNIT, I64], 2)],
        code: vec![
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    }
}
