//! Hand-built verifier coverage for callable-bearing environment graphs.
//! These artifacts deliberately do not depend on compiler emission.

use grandiose_vm::bytecode::Signature;
use grandiose_vm::verify::with_generated_cleanup_plans;
use grandiose_vm::{
    Artifact, Constant, Function, I64, Instruction, Type, UNIT, Value, VerifyError, Vm, verify,
};

fn recursive_callable_types(copy: bool, zero_use_allowed: bool) -> (Vec<Type>, u32, u32) {
    let mut types = Type::predefined();
    let environment = types.len() as u32;
    let callable = environment + 1;
    types.push(Type::Tuple {
        fields: vec![callable],
        copy,
    });
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 2,
        identity_name: "recursive callable identity".into(),
        copy,
        zero_use_allowed,
    });
    (types, environment, callable)
}

#[test]
fn recursive_callable_environment_identity_verifies_without_unbounded_type_walks() {
    let (types, _, _) = recursive_callable_types(true, false);
    let artifact = Artifact {
        types,
        ..Artifact::default()
    };
    let verification = verify(artifact.clone());
    assert!(verification.is_ok(), "{verification:?}");
    assert!(verify(Artifact::decode(&artifact.encode()).unwrap()).is_ok());
}

#[test]
fn recursive_environment_cannot_claim_copy_when_its_callable_leaf_is_noncopy() {
    let (mut types, environment, callable) = recursive_callable_types(false, true);
    let Type::Tuple { copy, .. } = &mut types[environment as usize] else {
        unreachable!()
    };
    *copy = true;
    let artifact = Artifact {
        types,
        ..Artifact::default()
    };
    assert_eq!(
        verify(artifact).unwrap_err(),
        VerifyError::InvalidType(environment)
    );

    // The failure is caused by the nested callable's declared capability, not
    // merely by the cycle itself.
    assert_ne!(environment, callable);
}

#[test]
fn callable_aggregate_cannot_launder_an_exact_resumption_into_copyability() {
    let mut types = Type::predefined();
    let resumption = types.len() as u32;
    types.push(Type::Resumption {
        input_type: UNIT,
        output_type: UNIT,
        effect_signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        lower_uses: 1,
        upper_uses: Some(1),
        identity_name: "exact captured resumption".into(),
        copy: false,
    });
    let environment = types.len() as u32;
    types.push(Type::Tuple {
        fields: vec![resumption],
        copy: false,
    });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 2,
        identity_name: "exact resumption closure".into(),
        copy: false,
        zero_use_allowed: false,
    });
    let valid = Artifact {
        types,
        required_features: 1 | (1 << 3),
        ..Artifact::default()
    };
    assert!(verify(valid.clone()).is_ok());
    assert!(verify(Artifact::decode(&valid.encode()).unwrap()).is_ok());

    let mut malformed = valid;
    let Type::Tuple { copy, .. } = &mut malformed.types[environment as usize] else {
        unreachable!()
    };
    *copy = true;
    let Type::Callable { copy, .. } = &mut malformed.types[callable as usize] else {
        unreachable!()
    };
    *copy = true;
    assert_eq!(
        verify(malformed).unwrap_err(),
        VerifyError::InvalidType(environment)
    );
    assert_ne!(callable, environment);
}

fn one_capture_callable() -> (Artifact, u32, u32) {
    let mut types = Type::predefined();
    let environment = types.len() as u32;
    types.push(
        Type::Tuple {
            fields: vec![UNIT],
            copy: true,
        }
        .restricted(true, true),
    );
    let shared_environment = types.len() as u32;
    types.push(Type::RefShared {
        referent: environment,
    });
    let callable = types.len() as u32;
    types.push(Type::Callable {
        signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        capture_type: environment,
        receiver_mode: 0,
        identity_name: "shared receiver closure".into(),
        copy: true,
        zero_use_allowed: true,
    });
    let artifact = Artifact {
        types,
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![UNIT],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, UNIT, callable],
                code_start: 0,
                code_len: 3,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "body".into(),
                params: vec![],
                return_type: UNIT,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_environment],
                code_start: 3,
                code_len: 2,
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
                dst: None,
                callable: 2,
                receiver_mode: 0,
                args: vec![],
            },
            Instruction::Return { src: None },
            Instruction::EndBorrow { reference: 0 },
            Instruction::Return { src: None },
        ],
        required_features: 1 | (1 << 1),
        ..Artifact::default()
    };
    (
        with_generated_cleanup_plans(artifact).unwrap(),
        environment,
        callable,
    )
}

#[test]
fn malformed_capture_layout_and_weaker_indirect_receiver_are_rejected() {
    let (artifact, environment, callable) = one_capture_callable();
    let verification = verify(artifact.clone());
    assert!(verification.is_ok(), "{verification:?}");

    let mut wrong_capture_type = artifact.clone();
    wrong_capture_type.functions[0].register_types[1] = environment;
    assert!(verify(wrong_capture_type).is_err());

    let mut missing_capture = artifact.clone();
    let Instruction::MakeCallable { captures, .. } = &mut missing_capture.code[0] else {
        unreachable!()
    };
    captures.clear();
    assert!(verify(missing_capture).is_err());

    let mut unique_body = artifact;
    let unique_environment = unique_body.types.len() as u32;
    unique_body.types.push(Type::RefUnique {
        referent: environment,
    });
    let Type::Callable { receiver_mode, .. } = &mut unique_body.types[callable as usize] else {
        unreachable!()
    };
    *receiver_mode = 1;
    unique_body.functions[1].receiver_mode = Some(1);
    unique_body.functions[1].register_types[0] = unique_environment;
    assert!(verify(unique_body).is_err());
}

fn known_shared_receiver_artifact(tail: bool) -> Artifact {
    let mut types = Type::predefined();
    let shared_unit = types.len() as u32;
    types.push(Type::RefShared { referent: UNIT });
    let clause = if tail {
        vec![Instruction::TailCallKnownReceiver {
            function: 2,
            receiver: 1,
            args: vec![2],
        }]
    } else {
        vec![
            Instruction::CallKnownReceiver {
                dst: Some(3),
                function: 2,
                receiver: 1,
                args: vec![2],
            },
            Instruction::Return { src: Some(3) },
        ]
    };
    let target_start = 5 + clause.len() as u32;
    let mut code = vec![
        Instruction::Const {
            dst: 1,
            constant: 0,
        },
        Instruction::BorrowShared { dst: 2, src: 1 },
        Instruction::Const {
            dst: 3,
            constant: 1,
        },
        Instruction::Call {
            dst: Some(4),
            function: 1,
            args: vec![2, 3],
        },
        Instruction::Return { src: Some(4) },
    ];
    code.extend(clause);
    code.push(Instruction::Return { src: Some(1) });
    let artifact = Artifact {
        types,
        constants: vec![Constant::Unit, Constant::I64(42)],
        functions: vec![
            Function {
                flags: 0,
                name: "main".into(),
                params: vec![],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: vec![UNIT, UNIT, shared_unit, I64, I64],
                code_start: 0,
                code_len: 5,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "synthetic clause".into(),
                params: vec![shared_unit, I64],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: None,
                register_types: if tail {
                    vec![UNIT, shared_unit, I64]
                } else {
                    vec![UNIT, shared_unit, I64, I64]
                },
                code_start: 5,
                code_len: target_start - 5,
                label_slot_count: 0,
            },
            Function {
                flags: 0,
                name: "lexical closure target".into(),
                params: vec![I64],
                return_type: I64,
                outward_protocols: vec![],
                receiver_mode: Some(0),
                register_types: vec![shared_unit, I64],
                code_start: target_start,
                code_len: 1,
                label_slot_count: 0,
            },
        ],
        code,
        required_features: 1 | (1 << 1),
        ..Artifact::default()
    };
    with_generated_cleanup_plans(artifact).unwrap()
}

#[test]
fn explicit_known_shared_receiver_tail_call_verifies_roundtrips_and_executes() {
    for tail in [false, true] {
        let artifact = known_shared_receiver_artifact(tail);
        let decoded = Artifact::decode(&artifact.encode()).unwrap();
        assert_eq!(decoded, artifact);
        let verified = verify(decoded).unwrap();
        assert_eq!(Vm::new(verified).run(0, vec![]).unwrap(), Value::I64(42));
    }
}

#[test]
fn known_receiver_calls_reject_nonshared_targets_and_wrong_receiver_types() {
    let artifact = known_shared_receiver_artifact(true);

    let mut unique_target = artifact.clone();
    unique_target.functions[2].receiver_mode = Some(1);
    assert!(verify(unique_target).is_err());

    let mut wrong_receiver = artifact;
    wrong_receiver.functions[1].register_types[1] = UNIT;
    assert!(verify(wrong_receiver).is_err());
}
