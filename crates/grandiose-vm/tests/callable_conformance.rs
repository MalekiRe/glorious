use grandiose_vm::bytecode::{CleanupPlan, Field, NEVER, Operation, Protocol, Signature};
use grandiose_vm::verify::with_generated_cleanup_plans;
use grandiose_vm::{
    Artifact, Constant, Function, I64, Instruction, NO_RETURN, Primitive, RuntimeError, Type, UNIT,
    Value, VerifyError, Vm, verify,
};

fn two_nominal_callables() -> (Artifact, u32, u32) {
    let mut types = Type::predefined();
    let first_callable = types.len() as u32;
    let signature = Signature {
        params: vec![],
        result: I64,
        outward_protocols: vec![],
    };
    types.push(Type::Callable {
        signature: signature.clone(),
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "first closure identity".into(),
        copy: false,
        zero_use_allowed: true,
    });
    let second_callable = types.len() as u32;
    types.push(Type::Callable {
        signature,
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "second closure identity".into(),
        copy: false,
        zero_use_allowed: true,
    });

    let artifact = Artifact {
        types,
        constants: vec![Constant::I64(20), Constant::I64(22)],
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, first_callable, second_callable, I64, I64, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "first body".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, I64],
                code_start: 6,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "second body".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, I64],
                code_start: 8,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type: first_callable,
                function: 1,
                captures: vec![],
            },
            Instruction::MakeCallable {
                dst: 2,
                callable_type: second_callable,
                function: 2,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(3),
                callable: 1,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 2,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Primitive {
                dst: 5,
                op: Primitive::IntCheckedAdd,
                args: vec![3, 4],
            },
            Instruction::Return { src: Some(5) },
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
            Instruction::Const {
                dst: 1,
                constant: 1,
            },
            Instruction::Return { src: Some(1) },
        ],
        cleanups: vec![
            CleanupPlan {
                function: 0,
                first_instruction: 0,
                end_instruction: 1,
                registers: vec![],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 1,
                end_instruction: 2,
                registers: vec![1],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 2,
                end_instruction: 3,
                registers: vec![2, 1],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 3,
                end_instruction: 4,
                registers: vec![3, 2],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 4,
                end_instruction: 5,
                registers: vec![4, 3],
            },
            CleanupPlan {
                function: 0,
                first_instruction: 5,
                end_instruction: 6,
                registers: vec![5],
            },
            CleanupPlan {
                function: 1,
                first_instruction: 0,
                end_instruction: 1,
                registers: vec![0],
            },
            CleanupPlan {
                function: 1,
                first_instruction: 1,
                end_instruction: 2,
                registers: vec![1, 0],
            },
            CleanupPlan {
                function: 2,
                first_instruction: 0,
                end_instruction: 1,
                registers: vec![0],
            },
            CleanupPlan {
                function: 2,
                first_instruction: 1,
                end_instruction: 2,
                registers: vec![1, 0],
            },
        ],
        ..Artifact::default()
    };
    (artifact, first_callable, second_callable)
}

#[test]
fn nominal_callable_identity_and_explicit_type_survive_roundtrip() {
    let (artifact, first_callable, second_callable) = two_nominal_callables();
    let decoded = Artifact::decode(&artifact.encode()).unwrap();
    assert_eq!(
        decoded.types[first_callable as usize],
        artifact.types[first_callable as usize]
    );
    assert_eq!(
        decoded.types[second_callable as usize],
        artifact.types[second_callable as usize]
    );
    assert_ne!(
        decoded.types[first_callable as usize],
        decoded.types[second_callable as usize]
    );
    assert!(matches!(
        decoded.code[0],
        Instruction::MakeCallable { callable_type, .. } if callable_type == first_callable
    ));
    assert!(matches!(
        decoded.code[1],
        Instruction::MakeCallable { callable_type, .. } if callable_type == second_callable
    ));
    assert_eq!(
        Vm::new(verify(decoded).unwrap()).run(0, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn verifier_rejects_callable_descriptor_producer_and_call_mode_mismatches() {
    let (artifact, first_callable, second_callable) = two_nominal_callables();

    let mut wrong_descriptor_mode = artifact.clone();
    let Type::Callable { receiver_mode, .. } =
        &mut wrong_descriptor_mode.types[first_callable as usize]
    else {
        unreachable!()
    };
    *receiver_mode = 0;
    assert_eq!(
        verify(wrong_descriptor_mode).unwrap_err(),
        VerifyError::InvalidFunction(1)
    );

    let mut wrong_instruction_mode = artifact.clone();
    let Instruction::CallIndirect { receiver_mode, .. } = &mut wrong_instruction_mode.code[2]
    else {
        unreachable!()
    };
    *receiver_mode = 3;
    assert_eq!(
        verify(wrong_instruction_mode).unwrap_err(),
        VerifyError::InvalidFunction(0)
    );

    let mut wrong_nominal_type = artifact;
    let Instruction::MakeCallable { callable_type, .. } = &mut wrong_nominal_type.code[0] else {
        unreachable!()
    };
    *callable_type = second_callable;
    assert_eq!(
        verify(wrong_nominal_type).unwrap_err(),
        VerifyError::InvalidFunction(1)
    );
}

#[test]
fn indirect_call_effect_rows_are_checked_at_the_calling_boundary() {
    let (mut artifact, first_callable, second_callable) = two_nominal_callables();
    artifact.protocols.push(Protocol {
        display_name: "DeclaredEffect".into(),
        type_arguments: vec![],
        operations: vec![],
    });
    artifact.required_features |= 1 << 3;
    for callable in [first_callable, second_callable] {
        let Type::Callable { signature, .. } = &mut artifact.types[callable as usize] else {
            unreachable!()
        };
        signature.outward_protocols = vec![0];
    }
    artifact.functions[1].outward_protocols = vec![0];
    artifact.functions[2].outward_protocols = vec![0];

    assert!(
        verify(artifact.clone()).is_err(),
        "a caller may not erase an indirect target's outward effect row"
    );

    artifact.functions[0].outward_protocols = vec![0];
    assert!(verify(artifact).is_ok());
}

#[test]
fn callable_values_roundtrip_through_aggregate_storage_and_move_projection() {
    let mut types = Type::predefined();
    let callable_type = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "stored closure identity".into(),
        copy: false,
        zero_use_allowed: true,
    });
    let tuple_type = types.len() as u32;
    types.push(Type::Tuple {
        fields: vec![callable_type],
        copy: false,
    });
    let artifact = Artifact {
        types,
        constants: vec![Constant::I64(42)],
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable_type, tuple_type, callable_type, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "stored body".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, I64],
                code_start: 6,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type,
                function: 1,
                captures: vec![],
            },
            Instruction::Construct {
                dst: 2,
                ty: tuple_type,
                variant: None,
                fields: vec![1],
            },
            Instruction::ProjectMove {
                dst: 3,
                src: 2,
                field: 0,
            },
            Instruction::Deconstruct { src: 2 },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 3,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    let decoded = Artifact::decode(&artifact.encode()).unwrap();
    assert_eq!(
        Vm::new(verify(decoded).unwrap()).run(0, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn copyable_callable_with_a_relevant_capture_cannot_be_abandoned() {
    let mut types = Type::predefined();
    let relevant = types.len() as u32;
    types.push(Type::I64.restricted(true, false));
    let environment = types.len() as u32;
    types.push(Type::Tuple {
        fields: vec![relevant],
        copy: true,
    });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: relevant,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 2,
        identity_name: "copyable but relevant closure".into(),
        copy: true,
        zero_use_allowed: false,
    });
    let artifact = Artifact {
        types,
        functions: vec![
            Function {
                flags: 0,
                name: "abandons closure".into(),
                params: vec![relevant],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, relevant, callable],
                code_start: 0,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "returns relevant capture".into(),
                params: vec![],
                return_type: relevant,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![environment, relevant],
                code_start: 2,
                code_len: 3,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 2,
                callable_type: callable,
                function: 1,
                captures: vec![1],
            },
            Instruction::Return { src: None },
            Instruction::ProjectMove {
                dst: 1,
                src: 0,
                field: 0,
            },
            Instruction::Deconstruct { src: 0 },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    let error = with_generated_cleanup_plans(artifact).unwrap_err();
    assert!(
        matches!(
            error,
            VerifyError::LiveValueAtExit {
                function: 0,
                register: 2,
                ..
            }
        ),
        "{error:?}"
    );
}

#[test]
fn captureless_zero_use_callable_supports_repeated_shared_calls_and_cleanup() {
    let mut types = Type::predefined();
    let shared_unit = types.len() as u32;
    types.push(Type::RefShared { referent: UNIT });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 0,
        identity_name: "reusable captureless closure".into(),
        copy: true,
        zero_use_allowed: true,
    });
    let artifact = Artifact {
        required_features: 1 | (1 << 1),
        types,
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "shared body".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_unit],
                code_start: 5,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type: callable,
                function: 1,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: None,
                callable: 1,
                receiver_mode: 0,
                args: vec![],
            },
            Instruction::CallIndirect {
                dst: None,
                callable: 1,
                receiver_mode: 0,
                args: vec![],
            },
            Instruction::Drop { register: 1 },
            Instruction::Return { src: None },
            Instruction::EndBorrow { reference: 0 },
            Instruction::Return { src: None },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(0, vec![]).unwrap(),
        Value::Unit
    );
}

#[test]
fn noncopy_zero_use_environment_makes_the_callable_droppable_but_not_copyable() {
    let mut types = Type::predefined();
    let environment = types.len() as u32;
    types.push(
        Type::Tuple {
            fields: vec![I64],
            copy: false,
        }
        .restricted(false, true),
    );
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 2,
        identity_name: "droppable noncopy closure".into(),
        copy: false,
        zero_use_allowed: true,
    });
    let artifact = Artifact {
        types,
        constants: vec![Constant::I64(42)],
        functions: vec![
            Function {
                flags: 0,
                name: "drops closure".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, I64, callable],
                code_start: 0,
                code_len: 4,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "moves capture".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![environment, I64],
                code_start: 4,
                code_len: 3,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::MakeCallable {
                dst: 2,
                callable_type: callable,
                function: 1,
                captures: vec![1],
            },
            Instruction::Drop { register: 2 },
            Instruction::Return { src: None },
            Instruction::ProjectMove {
                dst: 1,
                src: 0,
                field: 0,
            },
            Instruction::Deconstruct { src: 0 },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    assert!(!artifact.types[callable as usize].claimed_duplicable());
    assert!(artifact.types[callable as usize].claimed_zero_use_allowed());
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(0, vec![]).unwrap(),
        Value::Unit
    );
}

fn owned_exact_callable(invocations: usize) -> Artifact {
    let mut types = Type::predefined();
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "exact owned closure".into(),
        copy: false,
        zero_use_allowed: false,
    });
    let mut code = vec![Instruction::MakeCallable {
        dst: 1,
        callable_type: callable,
        function: 1,
        captures: vec![],
    }];
    code.extend((0..invocations).map(|_| Instruction::CallIndirect {
        dst: None,
        callable: 1,
        receiver_mode: 2,
        args: vec![],
    }));
    code.push(Instruction::Return { src: None });
    let body_start = code.len() as u32;
    code.push(Instruction::Return { src: None });
    Artifact {
        types,
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable],
                code_start: 0,
                code_len: body_start,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "owned body".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT],
                code_start: body_start,
                code_len: 1,
                label_slot_count: 0,
            },
        ],
        code,
        ..Artifact::default()
    }
}

#[test]
fn owned_receiver_with_exact_use_must_be_invoked_once() {
    let once = with_generated_cleanup_plans(owned_exact_callable(1)).unwrap();
    assert_eq!(
        Vm::new(verify(once).unwrap()).run(0, vec![]).unwrap(),
        Value::Unit
    );
    assert!(matches!(
        with_generated_cleanup_plans(owned_exact_callable(0)),
        Err(VerifyError::LiveValueAtExit {
            function: 0,
            register: 1,
            ..
        })
    ));
    assert!(matches!(
        with_generated_cleanup_plans(owned_exact_callable(2)),
        Err(VerifyError::UseOfEmpty {
            function: 0,
            register: 1,
            ..
        })
    ));
}

#[test]
fn callable_value_can_cross_an_ordinary_function_return_boundary() {
    let mut types = Type::predefined();
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "returned closure".into(),
        copy: false,
        zero_use_allowed: false,
    });
    let artifact = Artifact {
        types,
        constants: vec![Constant::I64(42)],
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable, I64],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "factory".into(),
                params: vec![],
                return_type: callable,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable],
                code_start: 3,
                code_len: 2,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "returned body".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, I64],
                code_start: 5,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::Call {
                dst: Some(1),
                function: 1,
                args: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(2),
                callable: 1,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Return { src: Some(2) },
            Instruction::MakeCallable {
                dst: 1,
                callable_type: callable,
                function: 2,
                captures: vec![],
            },
            Instruction::Return { src: Some(1) },
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    let mut hostile_return = artifact.clone();
    hostile_return.functions[1].return_type = UNIT;
    assert!(verify(hostile_return).is_err());

    let decoded = Artifact::decode(&artifact.encode()).unwrap();
    assert_eq!(
        Vm::new(verify(decoded).unwrap()).run(0, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn callable_value_roundtrips_through_a_nominal_aggregate() {
    let mut types = Type::predefined();
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: I64,
            outward_protocols: vec![],
        },
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "nominally stored closure".into(),
        copy: false,
        zero_use_allowed: false,
    });
    let holder = types.len() as u32;
    types.push(Type::Struct {
        name: "ClosureHolder".into(),
        fields: vec![Field {
            name: "body".into(),
            ty: callable,
        }],
        copy: false,
    });
    let artifact = Artifact {
        types,
        constants: vec![Constant::I64(42)],
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, callable, holder, callable, I64],
                code_start: 0,
                code_len: 6,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "nominal body".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(2),
                register_types: vec![UNIT, I64],
                code_start: 6,
                code_len: 2,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type: callable,
                function: 1,
                captures: vec![],
            },
            Instruction::Construct {
                dst: 2,
                ty: holder,
                variant: None,
                fields: vec![1],
            },
            Instruction::ProjectMove {
                dst: 3,
                src: 2,
                field: 0,
            },
            Instruction::Deconstruct { src: 2 },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 3,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Return { src: Some(4) },
            Instruction::Const {
                dst: 1,
                constant: 0,
            },
            Instruction::Return { src: Some(1) },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    let mut hostile_storage = artifact.clone();
    let Type::Struct { fields, .. } = &mut hostile_storage.types[holder as usize] else {
        unreachable!()
    };
    fields[0].ty = I64;
    assert!(verify(hostile_storage).is_err());

    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(0, vec![]).unwrap(),
        Value::I64(42)
    );
}

#[test]
fn outward_effectful_indirect_invocation_reaches_the_runtime_effect_boundary() {
    let mut types = Type::predefined();
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: NEVER,
            outward_protocols: vec![0],
        },
        capture_type: UNIT,
        receiver_mode: 2,
        identity_name: "outward effectful closure".into(),
        copy: false,
        zero_use_allowed: false,
    });
    let artifact = Artifact {
        required_features: 1 | (1 << 3),
        types,
        protocols: vec![Protocol {
            display_name: "Stop".into(),
            type_arguments: vec![],
            operations: vec![Operation {
                name: "stop".into(),
                payload_signature: Signature {
                    params: vec![],
                    result: NEVER,
                    outward_protocols: vec![],
                },
                result_type: NEVER,
                resumption_lower: 0,
                resumption_upper: Some(0),
                terminal: true,
            }],
        }],
        functions: vec![
            Function {
                flags: NO_RETURN,
                name: "main".into(),
                params: vec![],
                return_type: NEVER,
                outward_protocols: vec![0],
                receiver_mode: None,
                register_types: vec![UNIT, callable],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            },
            Function {
                flags: NO_RETURN,
                name: "effectful body".into(),
                params: vec![],
                return_type: NEVER,
                outward_protocols: vec![0],
                receiver_mode: Some(2),
                register_types: vec![UNIT],
                code_start: 3,
                code_len: 1,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 1,
                callable_type: callable,
                function: 1,
                captures: vec![],
            },
            Instruction::CallIndirect {
                dst: None,
                callable: 1,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Unreachable,
            Instruction::Perform {
                dst: None,
                protocol: 0,
                operation: 0,
                payloads: vec![],
            },
        ],
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    assert_eq!(
        Vm::new(verify(artifact).unwrap()).run(0, vec![]),
        Err(RuntimeError::UnhandledEffect {
            protocol: 0,
            operation: 0,
        })
    );
}

#[test]
fn relevant_copy_callable_supports_shared_observation_then_owned_final_call() {
    let mut types = Type::predefined();
    let relevant = types.len() as u32;
    types.push(Type::I64.restricted(true, false));
    let environment = types.len() as u32;
    types.push(
        Type::Tuple {
            fields: vec![relevant],
            copy: true,
        }
        .restricted(true, false),
    );
    let shared_environment = types.len() as u32;
    types.push(Type::RefShared {
        referent: environment,
    });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: relevant,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 0,
        identity_name: "relevant observing closure".into(),
        copy: true,
        zero_use_allowed: false,
    });
    let result_tuple = types.len() as u32;
    types.push(
        Type::Tuple {
            fields: vec![relevant, relevant],
            copy: true,
        }
        .restricted(true, false),
    );
    let artifact = Artifact {
        types,
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![relevant],
                return_type: result_tuple,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, relevant, callable, relevant, relevant, result_tuple],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "observe".into(),
                params: vec![],
                return_type: relevant,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_environment, relevant],
                code_start: 5,
                code_len: 3,
                label_slot_count: 0,
            },
        ],
        code: vec![
            Instruction::MakeCallable {
                dst: 2,
                callable_type: callable,
                function: 1,
                captures: vec![1],
            },
            Instruction::CallIndirect {
                dst: Some(3),
                callable: 2,
                receiver_mode: 0,
                args: vec![],
            },
            Instruction::CallIndirect {
                dst: Some(4),
                callable: 2,
                receiver_mode: 2,
                args: vec![],
            },
            Instruction::Construct {
                dst: 5,
                ty: result_tuple,
                variant: None,
                fields: vec![3, 4],
            },
            Instruction::Return { src: Some(5) },
            Instruction::ProjectCopy {
                dst: 1,
                src: 0,
                field: 0,
            },
            Instruction::EndBorrow { reference: 0 },
            Instruction::Return { src: Some(1) },
        ],
        required_features: 1 | (1 << 1),
        ..Artifact::default()
    };
    let artifact = with_generated_cleanup_plans(artifact).unwrap();
    assert_eq!(
        Vm::new(verify(artifact.clone()).unwrap())
            .run(0, vec![Value::I64(6)])
            .unwrap(),
        Value::aggregate(result_tuple, vec![Value::I64(6), Value::I64(6)])
    );

    let mut unique = artifact;
    let unique_environment = unique.types.len() as u32;
    unique.types.push(Type::RefUnique {
        referent: environment,
    });
    let Type::Callable {
        receiver_mode,
        copy,
        ..
    } = &mut unique.types[callable as usize]
    else {
        unreachable!()
    };
    *receiver_mode = 1;
    *copy = false;
    unique.functions[1].receiver_mode = Some(1);
    unique.functions[1].register_types[0] = unique_environment;
    let Instruction::CallIndirect { receiver_mode, .. } = &mut unique.code[1] else {
        unreachable!()
    };
    *receiver_mode = 1;
    assert_eq!(
        Vm::new(verify(unique.clone()).unwrap())
            .run(0, vec![Value::I64(6)])
            .unwrap(),
        Value::aggregate(result_tuple, vec![Value::I64(6), Value::I64(6)])
    );

    let mut weaker = unique;
    let Instruction::CallIndirect { receiver_mode, .. } = &mut weaker.code[1] else {
        unreachable!()
    };
    *receiver_mode = 0;
    assert!(
        verify(weaker).is_err(),
        "a shared request is weaker than a unique body"
    );
}
