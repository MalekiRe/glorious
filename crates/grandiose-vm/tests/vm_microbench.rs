//! Release-only VM throughput microbenchmarks.
//!
//! Run with:
//! `tooling/ram-gate.sh cargo test --release -p grandiose-vm --test vm_microbench -- --ignored --nocapture`

use std::time::Instant;

use grandiose_vm::{
    verify, verify::with_generated_cleanup_plans, Artifact, Constant, Function, Instruction,
    Primitive, Type, Value, Vm, BYTES, I64, TEXT, U32, UNIT, USIZE,
};
use grandiose_vm::bytecode::Signature;

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

fn measure_with_args(name: &str, artifact: Artifact, args: Vec<Value>, expected: Value) {
    let artifact = verify(with_generated_cleanup_plans(artifact).unwrap()).unwrap();
    let vm = Vm::new(artifact);
    assert_eq!(
        vm.run(0, args.clone())
            .unwrap_or_else(|error| panic!("{name}: {error:?}")),
        expected
    );
    let started = Instant::now();
    for _ in 0..ITERS {
        assert_eq!(vm.run(0, args.clone()).unwrap(), expected);
    }
    let elapsed = started.elapsed();
    eprintln!(
        "g1-vm-microbench name={name} iterations={ITERS} ns_per_run={}",
        elapsed.as_nanos() / ITERS as u128
    );
}

fn measure(name: &str, artifact: Artifact, expected: Value) {
    measure_with_args(name, artifact, vec![], expected);
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

/// Compiler data structures are predominantly small product values. Exercise
/// constructing a two-field tuple, moving out both fields, and deconstructing
/// the emptied shell repeatedly in one verified VM entry.
fn tuple_construct_project_program() -> Artifact {
    let mut types = Type::predefined();
    let pair = types.len() as u32;
    types.push(Type::Tuple {
        fields: vec![I64, I64],
        copy: false,
    });
    let mut code = Vec::with_capacity(INNER_OPS * 7 + 1);
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
            Instruction::Construct {
                dst: 3,
                ty: pair,
                variant: None,
                fields: vec![1, 2],
            },
            Instruction::ProjectMove {
                dst: 1,
                src: 3,
                field: 0,
            },
            Instruction::ProjectMove {
                dst: 2,
                src: 3,
                field: 1,
            },
            Instruction::Deconstruct { src: 3 },
        ]);
        if index + 1 != INNER_OPS {
            code.extend([
                Instruction::Drop { register: 1 },
                Instruction::Drop { register: 2 },
            ]);
        }
    }
    code.push(Instruction::Return { src: Some(1) });
    Artifact {
        types,
        constants: vec![Constant::I64(1), Constant::I64(2)],
        functions: vec![function(
            "main",
            vec![],
            I64,
            vec![UNIT, I64, I64, pair],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Repeatedly builds and destroys a two-field refinement binding pack.  The
/// self-host compiler uses these records to carry inferred local bindings, so
/// this isolates operand-list iteration and aggregate field materialization.
fn binding_pack_program() -> Artifact {
    let mut types = Type::predefined();
    types.push(
        Type::Tuple {
            fields: vec![I64, I64],
            copy: false,
        }
        .restricted(false, true),
    );
    types.push(
        Type::BindingPack {
            payload_type: 19,
            identity_name: "microbench bindings".into(),
            copy: false,
        }
        .restricted(false, true),
    );
    let mut code = Vec::with_capacity(INNER_OPS * 4 + 2);
    for _ in 0..INNER_OPS {
        code.extend([
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Const {
                dst: 2,
                constant: 1,
            },
            Instruction::MakeBindingPack {
                dst: 3,
                binding_type: 20,
                payloads: vec![1, 2],
            },
            Instruction::Drop { register: 3 },
        ]);
    }
    code.extend([
        Instruction::Const {
            dst: 4,
            constant: 2,
        },
        Instruction::Return { src: Some(4) },
    ]);
    Artifact {
        types,
        constants: vec![Constant::I64(1), Constant::I64(2), Constant::Unit],
        functions: vec![function(
            "main",
            vec![],
            UNIT,
            vec![UNIT, I64, I64, 20, UNIT],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Repeatedly invoke one captureless shared closure. The closure value remains
/// live across calls, matching compiler visitors and callback-heavy passes.
fn shared_closure_call_program() -> Artifact {
    let mut types = Type::predefined();
    let shared_unit = types.len() as u32;
    types.push(Type::RefShared { referent: UNIT });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 0,
        identity_name: "shared microbench closure".into(),
        copy: true,
        zero_use_allowed: true,
    });
    let mut code = vec![Instruction::MakeCallable {
        dst: 1,
        callable_type: callable,
        function: 1,
        captures: vec![],
    }];
    for index in 0..INNER_OPS {
        code.push(Instruction::CallIndirect {
            dst: Some(2),
            callable: 1,
            receiver_mode: 0,
            args: vec![],
        });
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 2 });
        }
    }
    code.push(Instruction::Drop { register: 1 });
    code.push(Instruction::Return { src: Some(2) });
    let body_start = code.len() as u32;
    code.extend([
        Instruction::Const {
            dst: 1,
            constant: 0,
        },
        Instruction::Return { src: Some(1) },
    ]);
    Artifact {
        required_features: 1 | (1 << 1),
        types,
        constants: vec![Constant::I64(1)],
        functions: vec![
            function(
                "main",
                vec![],
                I64,
                vec![UNIT, callable, I64],
                0,
                body_start,
            ),
            Function {
                name: "closure_body".into(),
                flags: 0,
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_unit, I64],
                code_start: body_start,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code,
        ..Artifact::default()
    }
}

/// Parser and symbol-table paths commonly compare a copied immutable spelling
/// against itself.  This keeps the source text large enough for content
/// comparison to be visible while retaining the VM's normal Copy semantics.
fn shared_text_equality_program() -> Artifact {
    let text = "identifier_segment_".repeat(16);
    let mut code = Vec::with_capacity(INNER_OPS * 4 + 1);
    for index in 0..INNER_OPS {
        code.extend([
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Primitive {
                dst: 3,
                op: Primitive::TextEq,
                args: vec![1, 2],
            },
        ]);
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 3 });
        }
    }
    code.push(Instruction::Return { src: Some(3) });
    Artifact {
        constants: vec![Constant::Text(text)],
        functions: vec![function(
            "main",
            vec![],
            U32,
            vec![UNIT, TEXT, TEXT, U32],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Concatenating an empty suffix occurs in parser and diagnostic assembly.
/// The source is an argument so the benchmark measures the primitive's output
/// ownership rather than re-materializing a large text constant per opcode.
fn text_concat_empty_program() -> Artifact {
    let mut code = Vec::with_capacity(INNER_OPS * 4 + 1);
    for index in 0..INNER_OPS {
        code.extend([
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Const {
                dst: 3,
                constant: 0,
            },
            Instruction::Primitive {
                dst: 4,
                op: Primitive::TextConcat,
                args: vec![2, 3],
            },
        ]);
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 4 });
        }
    }
    code.push(Instruction::Return { src: Some(4) });
    Artifact {
        constants: vec![Constant::Text(String::new())],
        functions: vec![function(
            "main",
            vec![TEXT],
            TEXT,
            vec![UNIT, TEXT, TEXT, TEXT, TEXT],
            0,
            code.len() as u32,
        )],
        code,
        ..Artifact::default()
    }
}

/// Whole-input slices are common when a compiler tracks a byte span that
/// happens to cover the current buffer. This measures the immutable identity
/// case without charging construction of the input to each bytecode opcode.
fn bytes_full_slice_program(length: usize) -> Artifact {
    let mut code = Vec::with_capacity(INNER_OPS * 5 + 1);
    for index in 0..INNER_OPS {
        code.extend([
            Instruction::Copy { dst: 2, src: 1 },
            Instruction::Const {
                dst: 3,
                constant: 0,
            },
            Instruction::Const {
                dst: 4,
                constant: 1,
            },
            Instruction::Primitive {
                dst: 5,
                op: Primitive::BytesSlice,
                args: vec![2, 3, 4],
            },
        ]);
        if index + 1 != INNER_OPS {
            code.push(Instruction::Drop { register: 5 });
        }
    }
    code.push(Instruction::Return { src: Some(5) });
    Artifact {
        constants: vec![Constant::Usize(0), Constant::Usize(length as u64)],
        functions: vec![function(
            "main",
            vec![BYTES],
            BYTES,
            vec![UNIT, BYTES, BYTES, USIZE, USIZE, BYTES],
            0,
            code.len() as u32,
        )],
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
    measure(
        "signed_comparison",
        signed_comparison_program(),
        Value::U64(1),
    );
    measure("branch_jump", branch_jump_program(), Value::I64(7));
    measure("direct_call", direct_call_program(), Value::I64(1));
    measure(
        "frame_argument_setup",
        frame_argument_setup_program(),
        Value::I64(2),
    );
    measure(
        "tuple_construct_project",
        tuple_construct_project_program(),
        Value::I64(1),
    );
    measure("binding_pack", binding_pack_program(), Value::Unit);
    measure(
        "shared_closure_call",
        shared_closure_call_program(),
        Value::I64(1),
    );
    measure(
        "shared_text_equality",
        shared_text_equality_program(),
        Value::U64(1),
    );
    let text = "parser_identifier_segment_".repeat(128);
    measure_with_args(
        "text_concat_empty",
        text_concat_empty_program(),
        vec![Value::Text(text.clone().into())],
        Value::Text(text.into()),
    );
    let bytes = vec![0x5a; 4096];
    measure_with_args(
        "bytes_full_slice",
        bytes_full_slice_program(bytes.len()),
        vec![Value::Bytes(bytes.clone().into())],
        Value::Bytes(bytes.into()),
    );
}
