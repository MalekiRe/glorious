use grandiose_vm::bytecode::{HandlerClause, HandlerDef, NEVER, Operation, Protocol, Signature};
use grandiose_vm::verify::with_generated_cleanup_plans;
use grandiose_vm::{Artifact, Function, I64, Instruction, Type, UNIT, verify};

fn identity_artifact() -> (Artifact, u32, u32) {
    let mut types = Type::predefined();
    let first = types.len() as u32;
    for identity_name in ["handler A continuation", "handler B continuation"] {
        types.push(Type::Resumption {
            input_type: I64,
            output_type: UNIT,
            effect_signature: Signature {
                params: vec![],
                result: UNIT,
                outward_protocols: vec![],
            },
            lower_uses: 1,
            upper_uses: Some(1),
            identity_name: identity_name.into(),
            copy: false,
        });
    }
    let second = first + 1;
    let operation = Operation {
        name: "yield".into(),
        payload_signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![],
        },
        result_type: I64,
        resumption_lower: 1,
        resumption_upper: Some(1),
        terminal: false,
    };
    let definition = |resumption_type| HandlerDef {
        result_type: UNIT,
        clauses: vec![HandlerClause {
            protocol: 0,
            operation: 0,
            resumption_type: Some(resumption_type),
            callable_signature: Signature {
                params: vec![resumption_type],
                result: UNIT,
                outward_protocols: vec![],
            },
        }],
        partial: false,
    };
    (
        Artifact {
            required_features: 1 | (1 << 3),
            types,
            protocols: vec![Protocol {
                display_name: "Yield".into(),
                type_arguments: vec![],
                operations: vec![operation],
            }],
            handler_defs: vec![definition(first), definition(second)],
            ..Artifact::default()
        },
        first,
        second,
    )
}

#[test]
fn handler_specific_resumption_identities_roundtrip_and_verify() {
    let (artifact, first, second) = identity_artifact();
    let decoded = Artifact::decode(&artifact.encode()).unwrap();
    assert_eq!(decoded, artifact);
    assert_eq!(
        decoded.handler_defs[0].clauses[0].resumption_type,
        Some(first)
    );
    assert_eq!(
        decoded.handler_defs[1].clauses[0].resumption_type,
        Some(second)
    );
    assert!(verify(decoded).is_ok());
}

#[test]
fn clause_signature_and_quantity_cannot_forge_another_handler_identity() {
    let (artifact, first, _) = identity_artifact();

    let mut wrong_signature = artifact.clone();
    wrong_signature.handler_defs[1].clauses[0].resumption_type = Some(first);
    assert!(verify(wrong_signature).is_err());

    let mut aliased_identity = artifact.clone();
    aliased_identity.handler_defs[1].clauses[0].resumption_type = Some(first);
    aliased_identity.handler_defs[1].clauses[0]
        .callable_signature
        .params[0] = first;
    assert!(verify(aliased_identity).is_err());

    let mut wrong_quantity = artifact.clone();
    let Type::Resumption { upper_uses, .. } = &mut wrong_quantity.types[first as usize] else {
        unreachable!()
    };
    *upper_uses = Some(2);
    assert!(verify(wrong_quantity).is_err());

    let mut wrong_effect_result = artifact;
    let Type::Resumption {
        effect_signature, ..
    } = &mut wrong_effect_result.types[first as usize]
    else {
        unreachable!()
    };
    effect_signature.result = I64;
    assert!(verify(wrong_effect_result).is_err());

    let (mut malformed_handler_layout, _, _) = identity_artifact();
    let capture_tuple = malformed_handler_layout.types.len() as u32;
    malformed_handler_layout.types.push(Type::Tuple {
        fields: vec![I64],
        copy: true,
    });
    malformed_handler_layout.types.push(Type::Handler {
        handler_def: 0,
        capture_type: capture_tuple,
        identity_name: "forged handler layout".into(),
    });
    assert!(verify(malformed_handler_layout).is_err());
}

#[test]
fn resume_requires_its_concrete_effect_row_at_the_call_site() {
    let mut types = Type::predefined();
    let resumption = types.len() as u32;
    types.push(Type::Resumption {
        input_type: UNIT,
        output_type: UNIT,
        effect_signature: Signature {
            params: vec![],
            result: UNIT,
            outward_protocols: vec![0],
        },
        lower_uses: 1,
        upper_uses: Some(1),
        identity_name: "effectful concrete continuation".into(),
        copy: false,
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
                    result: UNIT,
                    outward_protocols: vec![],
                },
                result_type: NEVER,
                resumption_lower: 0,
                resumption_upper: Some(0),
                terminal: true,
            }],
        }],
        functions: vec![Function {
            flags: 0,
            name: "missing continuation effect".into(),
            params: vec![resumption, UNIT],
            return_type: UNIT,
            outward_protocols: vec![],
            receiver_mode: None,
            register_types: vec![UNIT, resumption, UNIT, UNIT],
            code_start: 0,
            code_len: 2,
            label_slot_count: 0,
        }],
        code: vec![
            Instruction::Resume {
                dst: 3,
                resumption: 1,
                receiver_mode: 2,
                value: 2,
            },
            Instruction::Return { src: Some(3) },
        ],
        ..Artifact::default()
    };
    assert!(with_generated_cleanup_plans(artifact).is_err());
}
