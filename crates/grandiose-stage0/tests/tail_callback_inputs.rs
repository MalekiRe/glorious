use grandiose_stage0::{
    CandidateVmProgram, DefKey, Digest, Safety, VmArtifactError, VmFunction, VmInstruction as I,
    VmType, decode_and_verify_program, encode_program, verify_vm_program,
};
use std::collections::BTreeMap;

fn key(name: &str) -> DefKey {
    DefKey(Digest::of_bytes(name.as_bytes()))
}

fn candidate(
    forwarded: bool,
    unknown_callback: bool,
    second_caller: bool,
    address_taken: bool,
) -> CandidateVmProgram {
    let entry = key("callback-input-entry");
    let relay = key("callback-input-relay");
    let forward = key("callback-input-forward");
    let finish = key("callback-input-finish");
    let pure = key("callback-input-pure");
    let opaque = key("callback-input-opaque");
    let callback = VmType::Callable {
        shared_receiver: true,
        unique_receiver: true,
        safety: Safety::Safe,
        parameters: vec![],
        result: Box::new(VmType::Unit),
        effects: Default::default(),
    };
    let reference = VmType::Reference {
        unique: false,
        referent: Box::new(VmType::I64),
    };
    let receiver = VmType::Reference {
        unique: true,
        referent: Box::new(callback.clone()),
    };
    let relay_callable = VmType::Callable {
        shared_receiver: true,
        unique_receiver: true,
        safety: Safety::Safe,
        parameters: vec![reference.clone(), receiver.clone()],
        result: Box::new(VmType::I64),
        effects: Default::default(),
    };
    let function = |definition, parameters, registers, instructions| VmFunction {
        definition,
        parameters,
        registers,
        instructions,
        safety: Safety::Safe,
        unsafe_execution: false,
        nominal_copy_descriptors: vec![],
        captures: 0,
    };
    let mut instructions = vec![
        I::DeclareResult {
            result: VmType::I64,
            returns: true,
        },
        I::MakeCallable {
            dst: 0,
            callee: if unknown_callback { opaque } else { pure },
            captures: vec![],
            environment: None,
        },
        I::Borrow {
            dst: 1,
            src: 0,
            fields: vec![],
            unique: true,
            reborrow: false,
        },
        I::ConstI64 { dst: 2, value: 42 },
        I::Borrow {
            dst: 3,
            src: 2,
            fields: vec![],
            unique: false,
            reborrow: false,
        },
        I::CallOwned {
            dst: 4,
            callee: if forwarded { forward } else { relay },
            arguments: vec![3, 1],
        },
    ];
    if second_caller {
        instructions.extend([
            I::MakeCallable {
                dst: 7,
                callee: opaque,
                captures: vec![],
                environment: None,
            },
            I::Borrow {
                dst: 8,
                src: 7,
                fields: vec![],
                unique: true,
                reborrow: false,
            },
            I::Borrow {
                dst: 9,
                src: 2,
                fields: vec![],
                unique: false,
                reborrow: false,
            },
            I::CallOwned {
                dst: 10,
                callee: relay,
                arguments: vec![9, 8],
            },
        ]);
    }
    if address_taken {
        instructions.push(I::MakeCallable {
            dst: 6,
            callee: relay,
            captures: vec![],
            environment: None,
        });
    }
    instructions.push(I::Return { value: 4 });
    let mut functions = BTreeMap::from([
        (
            entry,
            function(
                entry,
                0,
                vec![
                    callback.clone(),
                    receiver.clone(),
                    VmType::I64,
                    reference.clone(),
                    VmType::I64,
                    VmType::I64,
                    relay_callable,
                    callback,
                    receiver.clone(),
                    reference.clone(),
                    VmType::I64,
                ],
                instructions,
            ),
        ),
        (
            relay,
            function(
                relay,
                2,
                vec![reference.clone(), receiver.clone(), VmType::Unit],
                vec![
                    I::DeclareResult {
                        result: VmType::I64,
                        returns: true,
                    },
                    I::CallIndirectOwned {
                        dst: 2,
                        callee: 1,
                        arguments: vec![],
                    },
                    I::TailCallOwned {
                        callee: finish,
                        arguments: vec![0],
                    },
                ],
            ),
        ),
        (
            forward,
            function(
                forward,
                2,
                vec![reference.clone(), receiver, VmType::I64],
                vec![
                    I::DeclareResult {
                        result: VmType::I64,
                        returns: true,
                    },
                    I::CallOwned {
                        dst: 2,
                        callee: relay,
                        arguments: vec![0, 1],
                    },
                    I::Return { value: 2 },
                ],
            ),
        ),
        (
            finish,
            function(
                finish,
                1,
                vec![reference, VmType::I64],
                vec![
                    I::DeclareResult {
                        result: VmType::I64,
                        returns: true,
                    },
                    I::DerefCopy {
                        dst: 1,
                        reference: 0,
                    },
                    I::Return { value: 1 },
                ],
            ),
        ),
        (
            pure,
            function(
                pure,
                0,
                vec![VmType::Unit],
                vec![
                    I::DeclareResult {
                        result: VmType::Unit,
                        returns: true,
                    },
                    I::ConstUnit { dst: 0 },
                    I::Return { value: 0 },
                ],
            ),
        ),
    ]);
    let external = unknown_callback || second_caller;
    if external {
        functions.insert(
            opaque,
            function(
                opaque,
                0,
                vec![VmType::Unit],
                vec![
                    I::DeclareResult {
                        result: VmType::Unit,
                        returns: true,
                    },
                    I::HostCallOwned {
                        dst: 0,
                        capability: "test.callback".into(),
                        symbol: "opaque".into(),
                        source_contract: Digest::of_bytes(b"opaque-callback-contract"),
                        parameters: vec![],
                        result: VmType::Unit,
                        resident_operations: vec![],
                        arguments: vec![],
                    },
                    I::Return { value: 0 },
                ],
            ),
        );
    }
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        entry,
        functions,
        callable_environments: BTreeMap::new(),
        host_capabilities: if external {
            vec!["test.callback".into()]
        } else {
            vec![]
        },
        fingerprint: Digest::of_bytes(b"unsealed-callback-input"),
    };
    program.fingerprint = program.computed_fingerprint();
    program
}

#[test]
fn callback_entry_proofs_follow_all_direct_and_transitive_callers() {
    for forwarded in [false, true] {
        for unknown in [false, true] {
            let candidate = candidate(forwarded, unknown, false, false);
            for result in [
                verify_vm_program(candidate.clone()),
                decode_and_verify_program(&encode_program(&candidate)),
            ] {
                if unknown {
                    assert!(
                        matches!(result, Err(VmArtifactError::UnprovenTailCarrier { function, register: 0, .. })
                        if function == key("callback-input-relay")),
                        "{result:?}"
                    );
                } else {
                    assert_eq!(result.unwrap().run_i64().unwrap(), 42);
                }
            }
        }
    }
}

#[test]
fn one_proven_caller_cannot_certify_other_or_first_class_entry_paths() {
    for (second_caller, address_taken) in [(true, false), (false, true)] {
        let candidate = candidate(false, false, second_caller, address_taken);
        for result in [
            verify_vm_program(candidate.clone()),
            decode_and_verify_program(&encode_program(&candidate)),
        ] {
            assert!(
                matches!(result, Err(VmArtifactError::UnprovenTailCarrier { function, register: 0, .. })
                if function == key("callback-input-relay")),
                "{result:?}"
            );
        }
    }
}

#[test]
fn initial_cleanup_does_not_anticipate_a_future_borrow() {
    for exposure in 0..3 {
        let mut candidate = candidate(false, false, false, false);
        let entry = candidate.functions.get_mut(&candidate.entry).unwrap();
        entry.registers.extend([
            VmType::Bool,
            VmType::Unit,
            entry.registers[0].clone(),
            VmType::Bool,
        ]);
        let mut instructions = vec![
            I::DeclareResult {
                result: VmType::I64,
                returns: true,
            },
            I::StorageLive {
                binding: 0,
                local: 7,
            },
        ];
        if exposure != 0 {
            instructions.push(I::MakeCallable {
                dst: 7,
                callee: key("callback-input-pure"),
                captures: vec![],
                environment: None,
            });
            if exposure == 2 {
                instructions.push(I::ConstBool {
                    dst: 14,
                    value: false,
                });
                let branch = instructions.len() as u32;
                instructions.push(I::BranchBool {
                    condition: 14,
                    then_target: branch + 1,
                    else_target: branch + 2,
                });
            }
            instructions.push(I::Borrow {
                dst: 8,
                src: 7,
                fields: vec![],
                unique: true,
                reborrow: false,
            });
            instructions.push(I::Move { dst: 13, src: 7 });
        }
        instructions.push(I::MakeCallable {
            dst: 0,
            callee: key("callback-input-pure"),
            captures: vec![],
            environment: None,
        });
        let probe = instructions.len() as u32;
        instructions.extend([
            I::IsInitialized {
                dst: 11,
                base: 7,
                fields: vec![],
            },
            I::BranchBool {
                condition: 11,
                then_target: probe + 2,
                else_target: probe + 4,
            },
            I::DestroyCallable { dst: 12, value: 7 },
            I::Jump { target: probe + 4 },
            I::StoreOwned { dst: 7, src: 0 },
            I::Borrow {
                dst: 1,
                src: 7,
                fields: vec![],
                unique: true,
                reborrow: false,
            },
            I::ConstI64 { dst: 2, value: 42 },
            I::Borrow {
                dst: 3,
                src: 2,
                fields: vec![],
                unique: false,
                reborrow: false,
            },
            I::CallOwned {
                dst: 4,
                callee: key("callback-input-relay"),
                arguments: vec![3, 1],
            },
            I::Return { value: 4 },
        ]);
        entry.instructions = instructions;
        candidate.fingerprint = candidate.computed_fingerprint();
        for result in [
            verify_vm_program(candidate.clone()),
            decode_and_verify_program(&encode_program(&candidate)),
        ] {
            if exposure != 0 {
                // Readability alone cannot prove an exposed slot absent:
                // retaining that conservative branch must not certify an
                // unknown destructor as harmless to the live callback.
                assert!(
                    matches!(result, Err(VmArtifactError::UnprovenTailCarrier { .. })),
                    "{result:?}"
                );
            } else {
                assert_eq!(result.unwrap().run_i64().unwrap(), 42);
            }
        }
    }
}
