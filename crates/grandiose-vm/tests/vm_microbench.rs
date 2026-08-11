//! Release-only VM throughput microbenchmarks.
//!
//! Run with:
//! `tooling/ram-gate.sh cargo test --release -p grandiose-vm --test vm_microbench -- --ignored --nocapture`

use std::time::Instant;

use grandiose_vm::{
    verify, verify::with_generated_cleanup_plans, Artifact, Constant, Function, Instruction,
    Primitive, Value, Vm, I64, UNIT,
};

const ITERS: usize = 20_000;
/// Every generated artifact executes this many target operations in one VM
/// entry. Keeping it unrolled avoids measuring the loop-control mechanism in
/// the arithmetic, call, and frame-setup cases.
const INNER_OPS: usize = 128;

fn function(
    name: &str,
    params: Vec<u32>,
    result: u32,
    registers: Vec<u32>,
    start: u32,
    len: u32,
) -> Function {
    Function {
        name: name.into(),
        flags: 0,
        params,
        return_type: result,
        outward_protocols: vec![],
        receiver_mode: None,
        register_types: registers,
        code_start: start,
        code_len: len,
        label_slot_count: 0,
    }
}

fn measure(name: &str, artifact: Artifact, expected: Value) {
    let artifact = verify(with_generated_cleanup_plans(artifact).unwrap()).unwrap();
    let vm = Vm::new(artifact);
    assert_eq!(
        vm.run(0, vec![])
            .unwrap_or_else(|error| panic!("{name}: {error:?}")),
        expected
    );
    let started = Instant::now();
    for _ in 0..ITERS {
        assert_eq!(vm.run(0, vec![]).unwrap(), expected);
    }
    let elapsed = started.elapsed();
    eprintln!(
        "g1-vm-microbench name={name} iterations={ITERS} ns_per_run={}",
        elapsed.as_nanos() / ITERS as u128
    );
}

/// Sustained arithmetic and register movement in a single VM entry.
fn arithmetic_register_program() -> Artifact {
    let mut code = vec![Instruction::Const {
        dst: 1,
        constant: 0,
    }];
    for _ in 0..INNER_OPS {
        code.extend([
            Instruction::Const {
                dst: 2,
                constant: 1,
            },
            Instruction::Move { dst: 3, src: 1 },
            Instruction::Primitive {
                dst: 1,
                op: Primitive::IntCheckedAdd,
                args: vec![3, 2],
            },
        ]);
    }
    code.push(Instruction::Return { src: Some(1) });
    Artifact {
        constants: vec![Constant::I64(0), Constant::I64(1)],
        functions: vec![function(
            "main",
            vec![],
            I64,
            vec![UNIT, I64, I64, I64],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Sustained signed comparison. This is deliberately separate from branch
/// dispatch: it measures the scalar primitive path that compiler comparison
/// helpers use before their result becomes a control-flow condition.
fn signed_comparison_program() -> Artifact {
    let mut code = Vec::with_capacity(INNER_OPS * 3 + 1);
    for index in 0..INNER_OPS {
        code.extend([
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
                op: Primitive::IntLt,
                args: vec![1, 2],
            },
        ]);
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 3 });
        }
    }
    code.push(Instruction::Return { src: Some(3) });
    Artifact {
        constants: vec![Constant::I64(-1), Constant::I64(1)],
        functions: vec![function(
            "main",
            vec![],
            grandiose_vm::U32,
            vec![UNIT, I64, I64, grandiose_vm::U32],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Each jump is taken and skips a bytecode slot; the target is computed while
/// building the artifact so the measurement contains no source compiler work.
fn branch_jump_program() -> Artifact {
    let mut code = vec![Instruction::Const {
        dst: 1,
        constant: 0,
    }];
    for _ in 0..INNER_OPS {
        let target = code.len() as u32 + 2;
        code.push(Instruction::Jump { target });
        code.push(Instruction::Nop);
    }
    code.push(Instruction::Return { src: Some(1) });
    Artifact {
        constants: vec![Constant::I64(7)],
        functions: vec![function(
            "main",
            vec![],
            I64,
            vec![UNIT, I64],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Call a zero-argument leaf at every generated position. This isolates
/// repeated direct-call frame construction without rebuilding the VM.
fn direct_call_program() -> Artifact {
    let mut code = Vec::with_capacity(INNER_OPS * 2 + 2);
    for index in 0..INNER_OPS {
        code.push(Instruction::Call {
            dst: Some(1),
            function: 1,
            args: vec![],
        });
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 1 });
        }
    }
    code.push(Instruction::Return { src: Some(1) });
    let leaf_start = code.len() as u32;
    code.extend([
        Instruction::Const {
            dst: 1,
            constant: 0,
        },
        Instruction::Return { src: Some(1) },
    ]);
    Artifact {
        constants: vec![Constant::I64(1)],
        functions: vec![
            function("main", vec![], I64, vec![UNIT, I64], 0, leaf_start),
            function("leaf", vec![], I64, vec![UNIT, I64], leaf_start, 2),
        ],
        code,
        ..Artifact::default()
    }
}

/// Repeatedly relocates two arguments into a direct callee frame. Keeping the
/// result as the loop output verifies the final callee result as well.
fn frame_argument_setup_program() -> Artifact {
    let mut code = Vec::with_capacity(INNER_OPS * 4 + 2);
    for index in 0..INNER_OPS {
        code.extend([
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Const {
                dst: 2,
                constant: 0,
            },
            Instruction::Call {
                dst: Some(3),
                function: 1,
                args: vec![1, 2],
            },
        ]);
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 3 });
        }
    }
    code.push(Instruction::Return { src: Some(3) });
    let add_start = code.len() as u32;
    code.extend([
        Instruction::Primitive {
            dst: 3,
            op: Primitive::IntCheckedAdd,
            args: vec![1, 2],
        },
        Instruction::Return { src: Some(3) },
    ]);
    Artifact {
        constants: vec![Constant::I64(1)],
        functions: vec![
            function("main", vec![], I64, vec![UNIT, I64, I64, I64], 0, add_start),
            function(
                "add",
                vec![I64, I64],
                I64,
                vec![UNIT, I64, I64, I64],
                add_start,
                2,
            ),
        ],
        code,
        ..Artifact::default()
    }
}

#[test]
#[ignore = "run explicitly in release mode; reports VM run throughput"]
fn vm_execution_microbenchmarks() {
    measure(
        "arithmetic_register",
        arithmetic_register_program(),
        Value::I64(INNER_OPS as i64),
    );
    measure("signed_comparison", signed_comparison_program(), Value::U64(1));
    measure("branch_jump", branch_jump_program(), Value::I64(7));
    measure("direct_call", direct_call_program(), Value::I64(1));
    measure(
        "frame_argument_setup",
        frame_argument_setup_program(),
        Value::I64(2),
    );
}
