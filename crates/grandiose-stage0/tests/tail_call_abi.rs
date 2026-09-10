use grandiose_stage0::{
    CandidateVmProgram, DefKey, Digest, Safety, VmArtifactError, VmEffectInstance, VmFunction,
    VmGenericArgument, VmInstruction, VmType, decode_and_verify_program, encode_program,
    verify_vm_program,
};
use std::collections::BTreeMap;

fn key(name: &str) -> DefKey {
    DefKey(Digest::of_bytes(name.as_bytes()))
}

fn callable(shared: bool, unique: bool) -> VmType {
    VmType::Callable {
        shared_receiver: shared,
        unique_receiver: unique,
        safety: Safety::Safe,
        parameters: vec![],
        result: Box::new(VmType::I64),
        effects: Default::default(),
    }
}

fn reference(value: VmType, unique: bool) -> VmType {
    VmType::Reference {
        unique,
        referent: Box::new(value),
    }
}

fn wrapper(parameter: VmType) -> VmType {
    let mut value = callable(false, false);
    if let VmType::Callable { parameters, .. } = &mut value {
        parameters.push(parameter);
    }
    value
}

/// Independently authored open entry ABI: no source contracts, closure
/// annotations or producer-issued compatibility witnesses are trusted here.
/// Trap keeps the callee's implementation neutral while its declared ABI is
/// checked. Source execution regressions separately exercise actual payloads.
fn program(
    actual: Vec<VmType>,
    expected: Vec<VmType>,
    source_result: (VmType, bool),
    target_result: (VmType, bool),
    tail: bool,
) -> CandidateVmProgram {
    let entry = key("call-abi-entry");
    let target = key("call-abi-target");
    let arguments = (0..actual.len() as u32).collect::<Vec<_>>();
    let result = actual.len() as u32;
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
    let mut registers = actual;
    registers.push(source_result.0.clone());
    let mut instructions = vec![VmInstruction::DeclareResult {
        result: source_result.0,
        returns: source_result.1,
    }];
    if tail {
        instructions.push(VmInstruction::TailCallOwned {
            callee: target,
            arguments,
        });
    } else {
        instructions.push(VmInstruction::CallOwned {
            dst: result,
            callee: target,
            arguments,
        });
        instructions.push(VmInstruction::Return { value: result });
    }
    let mut program = CandidateVmProgram {
        schema: grandiose_stage0::STAGE0_VM_SCHEMA,
        runtime_manifest: None,
        entry,
        fingerprint: Digest::of_bytes(b"unsealed-call-abi"),
        host_capabilities: vec![],
        callable_environments: BTreeMap::new(),
        functions: BTreeMap::from([
            (entry, function(entry, result, registers, instructions)),
            (
                target,
                function(
                    target,
                    expected.len() as u32,
                    expected,
                    vec![
                        VmInstruction::DeclareResult {
                            result: target_result.0,
                            returns: target_result.1,
                        },
                        VmInstruction::Trap,
                    ],
                ),
            ),
        ]),
    };
    program.fingerprint = program.computed_fingerprint();
    program
}

fn check(program: CandidateVmProgram, valid: bool) {
    for result in [
        verify_vm_program(program.clone()),
        decode_and_verify_program(&encode_program(&program)),
    ] {
        if valid {
            result.unwrap();
        } else {
            assert!(
                matches!(
                    result,
                    Err(VmArtifactError::TypeMismatch { .. })
                        | Err(VmArtifactError::CallArity { .. })
                        | Err(VmArtifactError::MalformedEncoding {
                            message: "mandatory tail target has an incompatible activation-transfer ABI",
                        })
                ),
                "wrong rejection: {result:?}"
            );
        }
    }
}

#[test]
fn ordinary_and_tail_arguments_share_directional_callable_abi() {
    let weak = callable(false, false);
    let strong = callable(true, true);
    let unique = callable(false, true);
    let mut unsafe_callback = weak.clone();
    if let VmType::Callable { safety, .. } = &mut unsafe_callback {
        *safety = Safety::Unsafe;
    }
    let mut effectful = weak.clone();
    if let VmType::Callable { effects, .. } = &mut effectful {
        effects.effects.push(VmEffectInstance {
            definition: key("callback-effect"),
            arguments: vec![],
        });
    }
    let mut other_result = weak.clone();
    if let VmType::Callable { result, .. } = &mut other_result {
        **result = VmType::Bool;
    }
    let cases = [
        (strong.clone(), weak.clone(), true),
        (unique.clone(), weak.clone(), true),
        (strong.clone(), unique.clone(), true),
        (weak.clone(), strong.clone(), false),
        (unique, strong.clone(), false),
        (
            VmType::Tuple(vec![strong.clone()]),
            VmType::Tuple(vec![weak.clone()]),
            true,
        ),
        (
            VmType::Tuple(vec![weak.clone()]),
            VmType::Tuple(vec![strong.clone()]),
            false,
        ),
        (
            reference(strong.clone(), false),
            reference(weak.clone(), false),
            true,
        ),
        (
            reference(weak.clone(), false),
            reference(strong.clone(), false),
            false,
        ),
        (
            reference(strong.clone(), true),
            reference(weak.clone(), true),
            false,
        ),
        (
            reference(weak.clone(), true),
            reference(strong.clone(), true),
            false,
        ),
        // Higher-order inputs reverse capability variance.
        (wrapper(weak.clone()), wrapper(strong.clone()), true),
        (wrapper(strong.clone()), wrapper(weak.clone()), false),
        (unsafe_callback, weak.clone(), false),
        (effectful, weak.clone(), false),
        (other_result, weak.clone(), false),
        (wrapper(VmType::I64), weak, false),
    ];
    for tail in [false, true] {
        for (actual, expected, valid) in &cases {
            check(
                program(
                    vec![actual.clone()],
                    vec![expected.clone()],
                    (VmType::I64, true),
                    (VmType::I64, true),
                    tail,
                ),
                *valid,
            );
        }
    }
}

#[test]
fn ordinary_and_tail_results_share_covariant_callable_abi() {
    let weak = callable(false, false);
    let strong = callable(true, true);
    for tail in [false, true] {
        for (actual, expected, valid) in [
            (strong.clone(), weak.clone(), true),
            (weak.clone(), strong.clone(), false),
            (
                VmType::Tuple(vec![strong.clone()]),
                VmType::Tuple(vec![weak.clone()]),
                true,
            ),
            (
                reference(strong.clone(), false),
                reference(weak.clone(), false),
                true,
            ),
            (
                reference(strong.clone(), true),
                reference(weak.clone(), true),
                false,
            ),
            (wrapper(weak.clone()), wrapper(strong.clone()), true),
            (wrapper(strong.clone()), wrapper(weak.clone()), false),
        ] {
            check(
                program(vec![], vec![], (expected, true), (actual, true), tail),
                valid,
            );
        }
    }
}

#[test]
fn ordinary_and_tail_calls_share_one_target_local_generic_substitution() {
    for tail in [false, true] {
        for (actual, expected, source, target, valid) in [
            (
                vec![VmType::I64],
                vec![VmType::Generic(0)],
                VmType::I64,
                VmType::Generic(0),
                true,
            ),
            (
                vec![VmType::I64],
                vec![VmType::Generic(0)],
                VmType::Bool,
                VmType::Generic(0),
                false,
            ),
            (
                vec![VmType::I64, VmType::Bool],
                vec![VmType::Generic(0); 2],
                VmType::I64,
                VmType::Generic(0),
                false,
            ),
            (vec![], vec![], VmType::I64, VmType::Generic(0), true),
            // The caller's binder 0 is not the target's binder 0.
            (
                vec![VmType::Generic(0)],
                vec![VmType::Generic(1)],
                VmType::Generic(0),
                VmType::Generic(1),
                true,
            ),
            (vec![VmType::I64], vec![], VmType::I64, VmType::I64, false),
        ] {
            check(
                program(actual, expected, (source, true), (target, true), tail),
                valid,
            );
        }
    }
}

#[test]
fn tail_call_retains_terminal_and_unsafe_activation_requirements() {
    check(
        program(
            vec![],
            vec![],
            (VmType::I64, true),
            (VmType::Unit, false),
            true,
        ),
        true,
    );
    check(
        program(
            vec![],
            vec![],
            (VmType::Unit, false),
            (VmType::Unit, false),
            true,
        ),
        true,
    );
    check(
        program(
            vec![],
            vec![],
            (VmType::Unit, false),
            (VmType::Unit, true),
            true,
        ),
        false,
    );
    let mut unsafe_target = program(
        vec![],
        vec![],
        (VmType::I64, true),
        (VmType::I64, true),
        true,
    );
    unsafe_target
        .functions
        .get_mut(&key("call-abi-target"))
        .unwrap()
        .safety = Safety::Unsafe;
    unsafe_target.fingerprint = unsafe_target.computed_fingerprint();
    check(unsafe_target, false);
}

#[test]
fn tail_call_checks_the_same_generic_effect_specialization_as_an_ordinary_call() {
    for tail in [false, true] {
        for specialized in [false, true] {
            let ty = if specialized {
                VmType::I64
            } else {
                VmType::Generic(0)
            };
            let mut candidate = program(
                vec![VmType::I64],
                vec![ty.clone()],
                (VmType::I64, true),
                (ty.clone(), true),
                tail,
            );
            candidate.runtime_manifest = Some(Digest::of_bytes(b"tail-call-effect-manifest"));
            let target = candidate
                .functions
                .get_mut(&key("call-abi-target"))
                .unwrap();
            target.registers.push(ty.clone());
            target.instructions.pop();
            target.instructions.extend([
                VmInstruction::Perform {
                    dst: 1,
                    effect: key("tail-call-generic-effect"),
                    effect_arguments: vec![VmGenericArgument::Type(ty)],
                    operation: 0,
                    arguments: vec![0],
                },
                VmInstruction::Return { value: 1 },
            ]);
            candidate.fingerprint = candidate.computed_fingerprint();
            for result in [
                verify_vm_program(candidate.clone()),
                decode_and_verify_program(&encode_program(&candidate)),
            ] {
                if specialized {
                    result.unwrap();
                } else {
                    assert!(
                        matches!(
                            result,
                            Err(VmArtifactError::MalformedEncoding {
                                message: "generic effect operation ABI was not specialized for call",
                            })
                        ),
                        "{result:?}"
                    );
                }
            }
        }
    }
}
