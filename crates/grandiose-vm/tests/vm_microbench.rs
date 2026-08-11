//! Release-only VM throughput microbenchmarks.
//!
//! Run with:
//! `tooling/ram-gate.sh cargo test --release -p grandiose-vm --test vm_microbench -- --ignored --nocapture`

use std::time::Instant;

use grandiose_vm::{Artifact, Constant, Function, I64, Instruction, UNIT, Value, Vm, verify, verify::with_generated_cleanup_plans};

const ITERS: usize = 1_000_000;

fn function(name: &str, params: Vec<u32>, result: u32, registers: Vec<u32>, start: u32, len: u32) -> Function {
    Function { name: name.into(), flags: 0, params, return_type: result, outward_protocols: vec![], receiver_mode: None, register_types: registers, code_start: start, code_len: len, label_slot_count: 0 }
}

fn measure(name: &str, artifact: Artifact, expected: Value) {
    let artifact = verify(with_generated_cleanup_plans(artifact).unwrap()).unwrap();
    let vm = Vm::new(artifact);
    assert_eq!(vm.run(0, vec![]).unwrap(), expected);
    let started = Instant::now();
    for _ in 0..ITERS { assert_eq!(vm.run(0, vec![]).unwrap(), expected); }
    let elapsed = started.elapsed();
    eprintln!("g1-vm-microbench name={name} iterations={ITERS} ns_per_run={}", elapsed.as_nanos() / ITERS as u128);
}

#[test]
#[ignore = "run explicitly in release mode; reports VM run throughput"]
fn vm_execution_microbenchmarks() {
    // Register/arithmetic-shaped: a dense const/move/return path.
    measure("arithmetic_register", Artifact { constants: vec![Constant::I64(7)], functions: vec![function("main", vec![], I64, vec![UNIT,I64,I64], 0, 3)], code: vec![Instruction::Const{dst:1,constant:0}, Instruction::Move{dst:2,src:1}, Instruction::Return{src:Some(2)}], ..Artifact::default() }, Value::I64(7));
    // Branch/jump-shaped: an unconditional bytecode branch before return.
    measure("branch_jump", Artifact { constants: vec![Constant::I64(7)], functions: vec![function("main", vec![], I64, vec![UNIT,I64], 0, 3)], code: vec![Instruction::Jump{target:1}, Instruction::Const{dst:1,constant:0}, Instruction::Return{src:Some(1)}], ..Artifact::default() }, Value::I64(7));
    // Direct-call frame construction with no arguments.
    measure("direct_call", Artifact { constants: vec![Constant::I64(7)], functions: vec![function("main",vec![],I64,vec![UNIT,I64],0,2), function("callee",vec![],I64,vec![UNIT,I64],2,2)], code: vec![Instruction::Call{dst:Some(1),function:1,args:vec![]},Instruction::Return{src:Some(1)},Instruction::Const{dst:1,constant:0},Instruction::Return{src:Some(1)}], ..Artifact::default() }, Value::I64(7));
    // Direct call with one relocated argument isolates argument-frame setup.
    measure("frame_argument_setup", Artifact { constants: vec![Constant::I64(7)], functions: vec![function("main",vec![],I64,vec![UNIT,I64,I64],0,3), function("id",vec![I64],I64,vec![UNIT,I64],3,1)], code: vec![Instruction::Const{dst:1,constant:0},Instruction::Call{dst:Some(2),function:1,args:vec![1]},Instruction::Return{src:Some(2)},Instruction::Return{src:Some(1)}], ..Artifact::default() }, Value::I64(7));
}
