use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel, modules,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{
    Artifact, Constant, RuntimeError, SystemHost, Type, Value, Vm,
    bytecode::{I64, Instruction, U64},
    verify::{VerifiedArtifact, load_verified},
};

const FIXTURE: &str = r#"
    struct Pair {
        first: i64,
        second: i64
    }

    enum Choice {
        Empty,
        Number(i64),
        Pair(i64, u64)
    }

    enum TestBool { False, True }
    enum Outer { Wrap(i64), Empty }
    enum Inner { One(i64), None }
    enum ScalarBranch { Select(u32) }

    __g1_bool_from_u32(value: u32) -> TestBool { TestBool::True }
    let test_true = TestBool::True;

    infixl 20 <=;
    infixl 30 +;
    infixl 30 -;
    infixl 40 *;
    infixl 40 /;
    infixl 40 %;

    identity(value: i64) -> i64 { value }
    answer() -> i64 {
        let value = 7;
        identity(value)
    }
    first() -> i64 {
        let pair = (7, 9);
        pair.0
    }
    struct_answer() -> i64 {
        let value = 11;
        let pair = Pair { second: value, first: value };
        pair.first
    }
    empty_choice() -> Choice { Choice::Empty }
    number_choice() -> Choice { Choice::Number(13) }
    pair_choice() -> Choice { Choice::Pair(7, 9) }
    inspect_choice(choice: Choice) -> i64 {
        handle choice {
            Choice::Empty => 3,
            Choice::Number(value) => value,
            Choice::Pair(first, _) => first
        }
    }
    inspect_choice_tail(choice: Choice) -> u64 {
        handle choice {
            Choice::Empty => 3,
            Choice::Number(_) => 13,
            Choice::Pair(_, second) => second
        }
    }
    branch_final(choice: Choice) -> i64 {
        let value = 17;
        handle choice {
            Choice::Empty => identity(value),
            Choice::Number(_) => identity(value),
            Choice::Pair(_, _) => identity(value)
        }
    }
    diverge() -> ! { diverge() }
    never_last(choice: Choice) {
        handle choice {
            Choice::Empty => (),
            Choice::Number(_) => (),
            Choice::Pair(_, _) => diverge()
        }
    }
    never_first(choice: Choice) {
        handle choice {
            Choice::Empty => diverge(),
            Choice::Number(_) => (),
            Choice::Pair(_, _) => ()
        }
    }
    integer_arithmetic(value: i64) -> i64 {
        (value + 2) * 3 - 4 / 2 % 5
    }
    integer_compare(value: u32) -> TestBool {
        value <= 7
    }
    literal_left_compare(value: u8) -> TestBool {
        128 <= value
    }
    alias_expression() -> TestBool { test_true }
    inspect_scalar_branch(branch: ScalarBranch) -> i64 {
        handle branch {
            ScalarBranch::Select(0) => 31,
            ScalarBranch::Select(_) => 37
        }
    }
    matched_scalar_zero() -> i64 {
        inspect_scalar_branch(ScalarBranch::Select(0))
    }
    matched_scalar_other() -> i64 {
        inspect_scalar_branch(ScalarBranch::Select(9))
    }
    nested_handle_binders(outer: Outer, inner: Inner) -> i64 {
        handle outer {
            Outer::Wrap(value) => handle inner {
                Inner::One(_) => value,
                Inner::None => value
            },
            Outer::Empty => 0
        }
    }
    matched_empty() -> i64 { inspect_choice(Choice::Empty) }
    matched_number() -> i64 { inspect_choice(Choice::Number(13)) }
    matched_pair() -> i64 { inspect_choice(Choice::Pair(7, 9)) }
    matched_pair_tail() -> u64 { inspect_choice_tail(Choice::Pair(7, 9)) }
    branch_final_empty() -> i64 { branch_final(Choice::Empty) }
    branch_final_number() -> i64 { branch_final(Choice::Number(1)) }
    branch_final_pair() -> i64 { branch_final(Choice::Pair(1, 2)) }
    main() { () }
"#;

const DIAGNOSTIC_PROBES: &str = r#"
    diagnostic_fingerprint(source: String) -> u64 {
        handle diagnostics::compile_source(&source) {
            Result::Ok(_) => 0,
            Result::Err(value) =>
                wrapping_convert_to_u64(
                    diagnostics::diagnostic_phase_code(&value)
                ) * 1000000000
                + wrapping_convert_to_u64(
                    diagnostics::diagnostic_class_code(&value)
                ) * 100000000
                + wrapping_convert_to_u64(
                    diagnostics::diagnostic_code(&value)
                ) * 1000
                + wrapping_convert_to_u64(
                    diagnostics::diagnostic_primary_space_code(&value)
                ) * 10
                + wrapping_convert_to_u64(
                    diagnostics::diagnostic_owner_space_code(&value)
                )
        }
    }

    resource_limit_fingerprint() -> u64 {
        let error = CompileError::Scan(
            ScanError::DeclarationIdExhausted(3, 4)
        );
        let value = diagnostics::compile_error_diagnostic(&error);
        wrapping_convert_to_u64(
            diagnostics::diagnostic_class_code(&value)
        ) * 10000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_code(&value)
            )
    }

    resource_limit_render() -> String {
        let error = CompileError::Scan(
            ScanError::DeclarationIdExhausted(3, 4)
        );
        let value = diagnostics::compile_error_diagnostic(&error);
        diagnostics::render_diagnostic(&value)
    }

    lowering_fingerprint() -> u64 {
        let error = CompileError::Lowering(
            Id::from_u32(2),
            LoweringError::ConstructionFieldCount(
                Id::from_u32(4),
                2,
                3
            )
        );
        let value = diagnostics::compile_error_diagnostic(&error);
        wrapping_convert_to_u64(
            diagnostics::diagnostic_code(&value)
        ) * 100000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_primary_space_code(&value)
            ) * 1000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_owner_space_code(&value)
            ) * 10000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_expected(&value)
            ) * 100
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_found(&value)
            )
    }

    emission_code() -> u32 {
        let error = CompileError::Emission(
            EmissionError::StructFieldNameCount(
                Id::from_u32(1),
                2,
                3
            )
        );
        let value = diagnostics::compile_error_diagnostic(&error);
        diagnostics::diagnostic_code(&value)
    }

    site_fingerprint(error: CompileError) -> u64 {
        let value = diagnostics::compile_error_diagnostic(&error);
        wrapping_convert_to_u64(
            diagnostics::diagnostic_class_code(&value)
        ) * 100000000000000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_code(&value)
            ) * 10000000000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_primary_space_code(&value)
            ) * 100000000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_primary_start(&value)
            ) * 1000000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_related_space_code(&value)
            ) * 10000000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_related_start(&value)
            ) * 100000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_owner_space_code(&value)
            ) * 1000
            + wrapping_convert_to_u64(
                diagnostics::diagnostic_owner_start(&value)
            )
    }

    body_internal_site() -> u64 {
        site_fingerprint(CompileError::BodyParse(
            Id::from_u32(2),
            BodyError::MissingBodyShell(Id::from_u32(8))
        ))
    }

    resolution_ambiguous_site() -> u64 {
        site_fingerprint(CompileError::BodyResolution(
            Id::from_u32(2),
            ResolutionError::AmbiguousFunction(
                9,
                Id::from_u32(4)
            )
        ))
    }

    elaboration_internal_site() -> u64 {
        site_fingerprint(CompileError::BodyElaboration(
            Id::from_u32(2),
            ElaborationError::InvalidResolvedExpression(5, 7)
        ))
    }

    typed_space_contract() -> u32 {
        let field_name = diagnostics::compile_error_diagnostic(
            &CompileError::InterfaceName(
                InterfaceNameKind::Field,
                4
            )
        );
        let variant_name = diagnostics::compile_error_diagnostic(
            &CompileError::InterfaceName(
                InterfaceNameKind::Variant,
                5
            )
        );
        let alias_header = diagnostics::compile_error_diagnostic(
            &CompileError::BodyElaboration(
                Id::from_u32(2),
                ElaborationError::MissingAliasHeader(6)
            )
        );
        let field_header = diagnostics::compile_error_diagnostic(
            &CompileError::BodyElaboration(
                Id::from_u32(2),
                ElaborationError::MissingFieldHeader(7)
            )
        );
        let variant_header = diagnostics::compile_error_diagnostic(
            &CompileError::ResolutionIndex(
                ResolutionError::MissingVariantHeader(8, 9)
            )
        );
        let switch_case = diagnostics::compile_error_diagnostic(
            &CompileError::Emission(
                EmissionError::MissingSwitchConstant(
                    Id::from_u32(10),
                    11
                )
            )
        );
        if(
            diagnostics::diagnostic_primary_space_code(&field_name) == 18
            and {
                diagnostics::diagnostic_primary_space_code(&variant_name) == 17
            }
            and {
                diagnostics::diagnostic_primary_space_code(&alias_header) == 2
            }
            and {
                diagnostics::diagnostic_primary_space_code(&field_header) == 18
            }
            and {
                diagnostics::diagnostic_related_space_code(&variant_header) == 17
            }
            and {
                diagnostics::diagnostic_related_space_code(&switch_case) == 20
            }
        ) { 1 } else { 0 }
    }

    diagnostic_codes_preserve_variant_identity() -> u32 {
        let header_a = diagnostics::compile_error_diagnostic(
            &CompileError::Headers(
                HeaderError::ExpectedRightBrace(1, 2)
            )
        );
        let header_b = diagnostics::compile_error_diagnostic(
            &CompileError::Headers(
                HeaderError::ExpectedSemicolon(1, 2)
            )
        );
        let body_a = diagnostics::compile_error_diagnostic(
            &CompileError::BodyParse(
                Id::from_u32(0),
                BodyError::ExpectedGroupingClose(1, 2)
            )
        );
        let body_b = diagnostics::compile_error_diagnostic(
            &CompileError::BodyParse(
                Id::from_u32(0),
                BodyError::DuplicatePatternBinder(1, 2)
            )
        );
        let resolution_a = diagnostics::compile_error_diagnostic(
            &CompileError::ResolutionIndex(
                ResolutionError::UnknownFunction(1)
            )
        );
        let resolution_b = diagnostics::compile_error_diagnostic(
            &CompileError::ResolutionIndex(
                ResolutionError::UnknownStruct(1)
            )
        );
        let elaboration_a = diagnostics::compile_error_diagnostic(
            &CompileError::InterfaceCollection(
                ElaborationError::MissingAliasHeader(1)
            )
        );
        let elaboration_b = diagnostics::compile_error_diagnostic(
            &CompileError::InterfaceCollection(
                ElaborationError::MissingDeclarationShell(1)
            )
        );
        if(
            diagnostics::diagnostic_code(&header_a)
                != diagnostics::diagnostic_code(&header_b)
            and {
                diagnostics::diagnostic_code(&body_a)
                    != diagnostics::diagnostic_code(&body_b)
            }
            and {
                diagnostics::diagnostic_code(&resolution_a)
                    != diagnostics::diagnostic_code(&resolution_b)
            }
            and {
                diagnostics::diagnostic_code(&elaboration_a)
                    != diagnostics::diagnostic_code(&elaboration_b)
            }
        ) { 1 } else { 0 }
    }

    zero_argument_render() -> String {
        let value = diagnostics::compile_error_diagnostic(
            &CompileError::Lowering(
                Id::from_u32(2),
                LoweringError::UnexpectedVariant(
                    Id::from_u32(4),
                    0
                )
            )
        );
        diagnostics::render_diagnostic(&value)
    }

    zero_argument_contract() -> u32 {
        let value = diagnostics::compile_error_diagnostic(
            &CompileError::Lowering(
                Id::from_u32(2),
                LoweringError::UnexpectedVariant(
                    Id::from_u32(4),
                    0
                )
            )
        );
        if(
            diagnostics::diagnostic_has_arguments(&value)
            and {
                diagnostics::diagnostic_class_code(&value) == 7
            }
        ) { 1 } else { 0 }
    }

    diagnostic_matrix() -> u64 {
        diagnostic_fingerprint("\"")
            + diagnostic_fingerprint("}") * 17
            + diagnostic_fingerprint("struct Broken { field }") * 289
            + diagnostic_fingerprint("main() { let value = ; }") * 4913
            + diagnostic_fingerprint("main() { missing() }") * 83521
            + diagnostic_fingerprint("main() -> i64 { () }") * 1419857
            + resource_limit_fingerprint() * 1771561
            + lowering_fingerprint()
            + wrapping_convert_to_u64(emission_code()) * 19487171
    }
"#;

const EFFECT_BACKEND_PROBES: &str = r#"
    effect_backend_terminal_artifact() -> Bytes {
        let protocols = backend::lowering::mir_protocols();
        let operations = Vec::new();
        Vec::push(&mut operations, backend::lowering::mir_operation(
            "stop",
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(0),
                Vec::new()
            ),
            backend::lowering::artifact_type_id(1),
            0,
            Option::Some(0),
            true
        ));
        let protocol = handle Arena::alloc(
            &mut protocols,
            backend::lowering::mir_protocol(
                "Probe",
                Vec::new(),
                operations
            )
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(found) => found
        };
        let outward_protocols = Vec::new();
        Vec::push(&mut outward_protocols, 0);
        let function = backend::lowering::new_mir_function(
            "terminal_probe",
            Vec::new(),
            backend::lowering::artifact_type_id(1),
            outward_protocols,
            1
        );
        let payloads = backend::lowering::alloc_mir_register_pack(
            &mut function,
            Vec::new()
        );
        backend::lowering::push_mir_instruction(
            &mut function,
            backend::lowering::MirInstruction::Perform(
                None,
                protocol,
                0,
                payloads
            )
        );
        backend::lowering::push_mir_cleanup(
            &mut function,
            0,
            1,
            Vec::new()
        );
        let functions = Arena::new();
        handle Arena::alloc(&mut functions, function) {
            Result::Err(_) => unreachable(),
            Result::Ok(_) => ()
        };
        let program = backend::lowering::finish_effect_program(
            functions,
            backend::lowering::mir_types(),
            Vec::new(),
            protocols,
            backend::lowering::mir_handler_definitions()
        );
        handle backend::emission::encode(&program, None) {
            Result::Err(_) => unreachable(),
            Result::Ok(bytes) => bytes
        }
    }

    effect_backend_invalid_terminal_reason() -> u32 {
        let protocols = backend::lowering::mir_protocols();
        let operations = Vec::new();
        Vec::push(&mut operations, backend::lowering::mir_operation(
            "bad",
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(0),
                Vec::new()
            ),
            backend::lowering::artifact_type_id(0),
            0,
            Option::Some(0),
            true
        ));
        handle Arena::alloc(
            &mut protocols,
            backend::lowering::mir_protocol("Bad", Vec::new(), operations)
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(_) => ()
        };
        let program = backend::lowering::finish_effect_program(
            Arena::new(),
            backend::lowering::mir_types(),
            Vec::new(),
            protocols,
            backend::lowering::mir_handler_definitions()
        );
        handle backend::emission::encode(&program, None) {
            Result::Err(error) => handle error {
                backend::emission::EmissionError::InvalidProtocol(
                    _, reason
                ) => handle reason {
                    backend::emission::ProtocolValidationError::TerminalContract => 4,
                    _ => 998
                },
                _ => 999
            },
            Result::Ok(_) => 997
        }
    }

    effect_backend_nonterminal_artifact() -> Bytes {
        let protocols = backend::lowering::mir_protocols();
        let operations = Vec::new();
        Vec::push(&mut operations, backend::lowering::mir_operation(
            "ask",
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(0),
                Vec::new()
            ),
            backend::lowering::artifact_type_id(4),
            1,
            Option::Some(1),
            false
        ));
        let protocol = handle Arena::alloc(
            &mut protocols,
            backend::lowering::mir_protocol("Ask", Vec::new(), operations)
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(found) => found
        };
        let type_names = Vec::new();
        Vec::push(&mut type_names, "probe one-shot resumption");
        Vec::push(&mut type_names, "probe unbounded resumption");
        let types = backend::lowering::mir_types();
        let resumption_mir = backend::lowering::push_resumption_type(
            &mut types,
            0,
            backend::lowering::artifact_type_id(4),
            backend::lowering::artifact_type_id(4),
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(4),
                Vec::new()
            ),
            1,
            Option::Some(1),
            0
        );
        let resumption = backend::lowering::mir_type_artifact_id(
            resumption_mir
        );
        backend::lowering::push_resumption_type(
            &mut types,
            1,
            backend::lowering::artifact_type_id(0),
            backend::lowering::artifact_type_id(0),
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(0),
                Vec::new()
            ),
            0,
            None,
            1
        );
        let clauses = Vec::new();
        let parameters = Vec::new();
        Vec::push(&mut parameters, resumption);
        Vec::push(&mut clauses, backend::lowering::mir_handler_clause(
            protocol,
            0,
            backend::lowering::mir_signature(
                parameters,
                backend::lowering::artifact_type_id(4),
                Vec::new()
            ),
            Option::Some(resumption)
        ));
        let definitions = backend::lowering::mir_handler_definitions();
        handle Arena::alloc(
            &mut definitions,
            backend::lowering::mir_handler_definition(
                backend::lowering::artifact_type_id(4),
                clauses,
                false
            )
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(_) => ()
        };
        let program = backend::lowering::finish_effect_program(
            Arena::new(),
            types,
            type_names,
            protocols,
            definitions
        );
        handle backend::emission::encode(&program, None) {
            Result::Err(_) => unreachable(),
            Result::Ok(bytes) => bytes
        }
    }

    effect_backend_invalid_resumption_reason(kind: u32) -> u32 {
        let type_names = Vec::new();
        Vec::push(&mut type_names, "malformed resumption");
        let input = if(kind == 0) {
            backend::lowering::artifact_type_id(4294967295)
        } else { backend::lowering::artifact_type_id(4) };
        let output = if(kind == 1) {
            backend::lowering::artifact_type_id(4294967295)
        } else { backend::lowering::artifact_type_id(4) };
        let outward = Vec::new();
        if(kind == 2) { Vec::push(&mut outward, 0) } else { () };
        let lower = if(kind == 3) { 2 } else { 1 };
        let upper = Option::Some(1);
        let copy_flag = if(kind == 4) { 1 } else { 0 };
        let types = backend::lowering::mir_types();
        backend::lowering::push_resumption_type(
            &mut types,
            0,
            input,
            output,
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(4),
                outward
            ),
            lower,
            upper,
            copy_flag
        );
        let program = backend::lowering::finish_effect_program(
            Arena::new(),
            types,
            type_names,
            backend::lowering::mir_protocols(),
            backend::lowering::mir_handler_definitions()
        );
        handle backend::emission::encode(&program, None) {
            Result::Err(error) => handle error {
                backend::emission::EmissionError::InvalidResumptionType(
                    _, reason
                ) => handle reason {
                    backend::emission::ResumptionTypeValidationError::InputType => 1,
                    backend::emission::ResumptionTypeValidationError::OutputType => 2,
                    backend::emission::ResumptionTypeValidationError::EffectSignature => 3,
                    backend::emission::ResumptionTypeValidationError::Quantity => 4,
                    backend::emission::ResumptionTypeValidationError::CopyContract => 5
                },
                _ => 999
            },
            Result::Ok(_) => 997
        }
    }

    effect_backend_invalid_handler_resumption_reason() -> u32 {
        let protocols = backend::lowering::mir_protocols();
        let operations = Vec::new();
        Vec::push(&mut operations, backend::lowering::mir_operation(
            "ask",
            backend::lowering::mir_signature(
                Vec::new(),
                backend::lowering::artifact_type_id(0),
                Vec::new()
            ),
            backend::lowering::artifact_type_id(4),
            1,
            Option::Some(1),
            false
        ));
        let protocol = handle Arena::alloc(
            &mut protocols,
            backend::lowering::mir_protocol(
                "Mismatch", Vec::new(), operations
            )
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(found) => found
        };
        let type_names = Vec::new();
        Vec::push(&mut type_names, "mismatched resumption");
        let types = backend::lowering::mir_types();
        let resumption = backend::lowering::mir_type_artifact_id(
            backend::lowering::push_resumption_type(
                &mut types,
                0,
                backend::lowering::artifact_type_id(5),
                backend::lowering::artifact_type_id(4),
                backend::lowering::mir_signature(
                    Vec::new(),
                    backend::lowering::artifact_type_id(4),
                    Vec::new()
                ),
                1,
                Option::Some(1),
                0
            )
        );
        let parameters = Vec::new();
        Vec::push(&mut parameters, resumption);
        let clauses = Vec::new();
        Vec::push(&mut clauses, backend::lowering::mir_handler_clause(
            protocol,
            0,
            backend::lowering::mir_signature(
                parameters,
                backend::lowering::artifact_type_id(4),
                Vec::new()
            ),
            Option::Some(resumption)
        ));
        let definitions = backend::lowering::mir_handler_definitions();
        handle Arena::alloc(
            &mut definitions,
            backend::lowering::mir_handler_definition(
                backend::lowering::artifact_type_id(4),
                clauses,
                false
            )
        ) {
            Result::Err(_) => unreachable(),
            Result::Ok(_) => ()
        };
        let program = backend::lowering::finish_effect_program(
            Arena::new(), types, type_names, protocols, definitions
        );
        handle backend::emission::encode(&program, None) {
            Result::Err(error) => handle error {
                backend::emission::EmissionError::InvalidHandlerDefinition(
                    _, reason
                ) => handle reason {
                    backend::emission::HandlerValidationError::ResumptionDescriptor => 6,
                    _ => 998
                },
                _ => 999
            },
            Result::Ok(_) => 997
        }
    }

    effect_backend_invalid_resumption_reasons() -> u32 {
        effect_backend_invalid_resumption_reason(0)
            + effect_backend_invalid_resumption_reason(1) * 10
            + effect_backend_invalid_resumption_reason(2) * 100
            + effect_backend_invalid_resumption_reason(3) * 1000
            + effect_backend_invalid_resumption_reason(4) * 10000
            + effect_backend_invalid_handler_resumption_reason() * 100000
    }

    callable_backend_direct_mir_artifact() -> Bytes {
        let types = backend::lowering::mir_types();
        let type_names = Vec::new();
        Vec::push(&mut type_names, "direct callable");
        let callable = backend::lowering::push_callable_type(
            &mut types,
            0,
            backend::lowering::artifact_type_id(0),
            backend::lowering::mir_signature(
                Vec::new(), backend::lowering::artifact_type_id(0), Vec::new()
            ),
            2,
            0,
            false
        );
        let callable_type = backend::lowering::mir_type_artifact_id(callable);
        let target = backend::lowering::new_mir_callable_function(
            "direct_callable_target", Vec::new(),
            backend::lowering::artifact_type_id(0), Vec::new(), 2,
            backend::lowering::artifact_type_id(0), 1
        );
        backend::lowering::push_mir_instruction(
            &mut target, backend::lowering::MirInstruction::Return(None)
        );
        let receiver_cleanup = Vec::new();
        Vec::push(&mut receiver_cleanup, Id::from_u32(0));
        backend::lowering::push_mir_cleanup(
            &mut target, 0, 1, receiver_cleanup
        );
        let caller = backend::lowering::new_mir_function(
            "direct_callable_entry", Vec::new(),
            backend::lowering::artifact_type_id(0), Vec::new(), 2
        );
        let captures = backend::lowering::alloc_mir_register_pack(
            &mut caller, Vec::new()
        );
        backend::lowering::push_mir_instruction(&mut caller,
            backend::lowering::MirInstruction::MakeCallable(
                Id::from_u32(1), callable_type, Id::from_u32(1), captures
            ));
        let arguments = backend::lowering::alloc_mir_register_pack(
            &mut caller, Vec::new()
        );
        backend::lowering::push_mir_instruction(&mut caller,
            backend::lowering::MirInstruction::CallIndirect(
                None, Id::from_u32(1), 2, arguments
            ));
        backend::lowering::push_mir_instruction(
            &mut caller, backend::lowering::MirInstruction::Return(None)
        );
        backend::lowering::push_mir_cleanup(&mut caller, 0, 1, Vec::new());
        let callable_cleanup = Vec::new();
        Vec::push(&mut callable_cleanup, Id::from_u32(1));
        backend::lowering::push_mir_cleanup(
            &mut caller, 1, 2, callable_cleanup
        );
        backend::lowering::push_mir_cleanup(&mut caller, 2, 3, Vec::new());
        let functions = Arena::new();
        handle Arena::alloc(&mut functions, caller) {
            Result::Err(_) => unreachable(), Result::Ok(_) => ()
        };
        handle Arena::alloc(&mut functions, target) {
            Result::Err(_) => unreachable(), Result::Ok(_) => ()
        };
        let program = backend::lowering::finish_program(
            functions, types, type_names
        );
        handle backend::emission::encode(&program, Option::Some(Id::from_u32(0))) {
            Result::Err(_) => unreachable(), Result::Ok(bytes) => bytes
        }
    }
"#;

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn self_host_module_paths(root: &Path) -> [PathBuf; 17] {
    [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/lossless/lossless.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
        root.join("backend/backend.glorious"),
        root.join("backend/artifact/artifact.glorious"),
        root.join("backend/lowering/lowering.glorious"),
        root.join("backend/emission/emission.glorious"),
        root.join("compiler/compiler.glorious"),
        root.join("diagnostics/diagnostics.glorious"),
        root.join("diagnostics/model/model.glorious"),
        root.join("diagnostics/source_errors/source_errors.glorious"),
        root.join("diagnostics/backend_errors/backend_errors.glorious"),
    ]
}

fn production_self_host_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_path = root.join("main.glorious");
    let primary = Segment::new(
        primary_path.to_string_lossy(),
        fs::read_to_string(&primary_path).unwrap(),
    );
    SourceBundle::distributed(
        primary,
        self_host_module_paths(&root).into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

/// Keep the expensive complete-bundle artifact available when decoding or
/// verification fails.  This is deliberately integration-test-only: the
/// production decoder remains fail-closed and unchanged, while a failing RAM
/// gate leaves an exact `.grbc` input for `grvm`/`G1_VERIFY_TRACE` diagnosis.
struct RetainedSelfHostArtifact {
    directory: PathBuf,
    artifact: PathBuf,
    keep: bool,
}

impl RetainedSelfHostArtifact {
    fn write(bytes: &[u8]) -> Self {
        let root = std::env::var_os("G1_SELF_HOST_ARTIFACT_TRACE_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(|| repository_root().join("target/self-host-artifact-traces"));
        Self::write_in(&root, bytes)
    }

    fn write_in(root: &Path, bytes: &[u8]) -> Self {
        static NEXT_TRACE: AtomicUsize = AtomicUsize::new(0);

        let ordinal = NEXT_TRACE.fetch_add(1, Ordering::Relaxed);
        let directory = root.join(format!(
            "full-bundle-{}-{}",
            std::process::id(),
            ordinal,
        ));
        fs::create_dir_all(&directory).unwrap_or_else(|error| {
            panic!(
                "failed to create retained self-host artifact directory {}: {error}",
                directory.display()
            )
        });
        let artifact = directory.join("full-self-host.grbc");
        fs::write(&artifact, bytes).unwrap_or_else(|error| {
            panic!(
                "failed to retain complete self-host artifact {}: {error}",
                artifact.display()
            )
        });
        Self {
            directory,
            artifact,
            keep: false,
        }
    }

    fn preserve(&mut self, phase: &str, error: impl std::fmt::Debug) -> ! {
        self.keep = true;
        eprintln!(
            "self-host artifact trace: {phase} failed: {error:?}; retained {}\n\
             rerun with `G1_VERIFY_TRACE=1 cargo test --release -p grandiose \\\n+             --test self_host_bytecode full_self_host_bundle_compiles_to_a_verified_artifact_in_release \\\n+             -- --ignored --nocapture` for the decoder's concise function/register trace",
            self.artifact.display(),
        );
        panic!("complete self-host artifact {phase} failed; retained {}", self.artifact.display());
    }

    fn discard(mut self) {
        self.keep = false;
        let _ = fs::remove_dir_all(&self.directory);
    }
}

impl Drop for RetainedSelfHostArtifact {
    fn drop(&mut self) {
        if !self.keep {
            let _ = fs::remove_dir_all(&self.directory);
        }
    }
}

fn decode_and_verify_full_self_host_artifact(bytes: &[u8]) {
    let mut trace = RetainedSelfHostArtifact::write(bytes);
    let decoded = match Artifact::decode(bytes) {
        Ok(decoded) => decoded,
        Err(error) => trace.preserve("decode", error),
    };
    assert_eq!(decoded.encode(), bytes, "the self-host artifact must be canonical");
    match load_verified(bytes) {
        Ok(_) => {}
        Err(errors) => trace.preserve("verification", errors),
    }
    trace.discard();
}

#[test]
fn retained_self_host_artifact_keeps_only_failed_gate_inputs() {
    let directory = tempfile::tempdir().expect("trace scratch directory");
    let success = RetainedSelfHostArtifact::write_in(directory.path(), b"success");
    let success_path = success.artifact.clone();
    let success_directory = success.directory.clone();
    assert_eq!(fs::read(&success_path).unwrap(), b"success");
    success.discard();
    assert!(!success_directory.exists(), "successful gate input must be removed");

    let mut failure = RetainedSelfHostArtifact::write_in(directory.path(), b"failure");
    let failure_path = failure.artifact.clone();
    let failure_directory = failure.directory.clone();
    failure.keep = true;
    drop(failure);
    assert_eq!(fs::read(&failure_path).unwrap(), b"failure");
    assert!(failure_directory.exists(), "failed gate input must be retained");
}

fn self_host_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_source = [
        r#"
            mod frontend;
            mod backend;
            mod compiler;
            mod diagnostics;

            use compiler::CompileError;
            use compiler::InterfaceNameKind;
            use frontend::bodies::BodyError;
            use frontend::headers::HeaderError;
            use frontend::scanner::ScanError;
            use frontend::resolution::ResolutionError;
            use frontend::elaboration::ElaborationError;
            use backend::lowering::LoweringError;
            use backend::emission::EmissionError;

            classify_compile_error(source: String) -> u8 {
                handle compiler::compile_source(&source) {
                    Result::Ok(_) => 0,
                    Result::Err(error) => handle error {
                        CompileError::Lex(_) => 1,
                        CompileError::Scan(_) => 2,
                        CompileError::Headers(_) => 3,
                        CompileError::ResolutionIndex(_) => 4,
                        CompileError::InterfaceCollection(_) => 5,
                        CompileError::DeclarationName(_) => 6,
                        CompileError::BodyParse(_, _) => 7,
                        CompileError::BodyResolution(_, _) => 8,
                        CompileError::BodyElaboration(_, _) => 9,
                        CompileError::Lowering(_, _) => 10,
                        CompileError::InterfaceName(_, _) => 11,
                        CompileError::UnsupportedInterfaceType(_) => 12,
                        CompileError::Emission(_) => 13
                    }
                }
            }
        "#,
        DIAGNOSTIC_PROBES,
        r#"
            main() { run_compiler_host(diagnostics::application) }
        "#,
    ]
    .concat();
    let primary = Segment::new(root.join("main.glorious").to_string_lossy(), primary_source);
    SourceBundle::distributed(
        primary,
        self_host_module_paths(&root).into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

// The effect-backend probes construct MIR directly.  Lowering still names the
// Core data types, so retain its frontend dependency closure, but avoid loading
// compiler/diagnostic modules and frontend phases (lossless/header parsing)
// that no probe can reach.  This keeps the test's backend wire-format coverage
// while preventing unrelated self-host compiler graphs from sharing its peak.
fn self_host_effect_backend_module_paths(root: &Path) -> Vec<PathBuf> {
    vec![
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
        root.join("frontend/lossless/lossless.glorious"),
        root.join("frontend/scanner/scanner.glorious"),
        root.join("frontend/headers/headers.glorious"),
        root.join("frontend/bodies/bodies.glorious"),
        root.join("frontend/resolution/resolution.glorious"),
        root.join("frontend/elaboration/elaboration.glorious"),
        root.join("backend/backend.glorious"),
        root.join("backend/artifact/artifact.glorious"),
        root.join("backend/lowering/lowering.glorious"),
        root.join("backend/emission/emission.glorious"),
    ]
}

fn self_host_effect_backend_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary_source = [
        r#"
            mod frontend;
            mod backend;
        "#,
        EFFECT_BACKEND_PROBES,
        r#"
            main() { () }
        "#,
    ]
    .concat();
    let primary = Segment::new(root.join("main.glorious").to_string_lossy(), primary_source);
    SourceBundle::distributed(
        primary,
        self_host_effect_backend_module_paths(&root)
            .into_iter()
            .map(|path| Segment::new(path.to_string_lossy(), fs::read_to_string(&path).unwrap())),
    )
}

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("self-hosted artifact is missing `{name}`")) as u32
}

fn bootstrap_self_host_release_vm() -> (VerifiedArtifact, u32, u32) {
    let phases = grandiose::compile_bundle_to_phases_with_options(
        &self_host_bundle(),
        CompileOptions {
            optimization_level: OptimizationLevel::O2,
        },
    )
    .unwrap();
    let classify = function_id(&phases.artifact, "classify_compile_error");
    let diagnostic = function_id(&phases.artifact, "diagnostic_fingerprint");
    let bytes = phases.artifact.encode();
    drop(phases);
    (load_verified(&bytes).unwrap(), classify, diagnostic)
}

fn run_self_host_source_probe(compiler: &VerifiedArtifact, function: u32, source: &str) -> Value {
    Vm::with_host(
        compiler.clone(),
        ["process.args", "fs.read", "fs.write", "diagnostic"],
        SystemHost::new(vec![]),
    )
    .unwrap()
    .run(function, vec![Value::Text(source.into())])
    .unwrap()
}

fn assert_diagnostic_contracts(mut run: impl FnMut(&str, Vec<Value>) -> Value) {
    let frontend = [
        (1_u64, 1_u64, 1016_u64, 1_u64, 0_u64),
        (2, 1, 2001, 2, 0),
        (3, 1, 3007, 2, 0),
        (7, 1, 7001, 2, 3),
        (8, 2, 8001, 2, 3),
        (9, 3, 9003, 2, 3),
    ];
    let fingerprint = |(phase, class, code, space, owner)| {
        phase * 1_000_000_000 + class * 100_000_000 + code * 1_000 + space * 10 + owner
    };
    let weights = [1_u64, 17, 289, 4_913, 83_521, 1_419_857];
    let mut expected = frontend
        .into_iter()
        .zip(weights)
        .map(|(value, weight)| fingerprint(value) * weight)
        .sum::<u64>();
    expected += (5_u64 * 10_000 + 2_007) * 1_771_561;
    expected += 10_007_u64 * 100_000_000 + 5 * 1_000_000 + 3 * 10_000 + 2 * 100 + 3;
    expected += 12_006_u64 * 19_487_171;

    assert_eq!(run("diagnostic_matrix", vec![]), Value::U64(expected));
    assert_eq!(
        run("resource_limit_render", vec![]),
        Value::Text(
            "[G2007] self-host compiler: declaration scanning failed (token 3); related token 4"
                .into()
        )
    );
    assert_eq!(
        run("body_internal_site", vec![]),
        Value::U64(770_070_308_000_003_002)
    );
    assert_eq!(
        run("resolution_ambiguous_site", vec![]),
        Value::U64(280_020_209_030_403_002)
    );
    assert_eq!(
        run("elaboration_internal_site", vec![]),
        Value::U64(790_250_605_070_703_002)
    );
    assert_eq!(run("typed_space_contract", vec![]), Value::U64(1));
    assert_eq!(
        run("diagnostic_codes_preserve_variant_identity", vec![]),
        Value::U64(1)
    );
    assert_eq!(run("zero_argument_contract", vec![]), Value::U64(1));
    assert_eq!(
        run("zero_argument_render", vec![]),
        Value::Text(
            "[G10008] self-host compiler: an unexpected enum variant reached lowering (type 4); related variant 0; owner declaration 2; expected 0, found 0"
                .into()
        )
    );
}

fn assert_compiled_artifact(bytes: &[u8]) {
    let decoded = Artifact::decode(bytes).expect("self-hosted GRBC must decode");
    assert_eq!(
        decoded.encode(),
        bytes,
        "self-hosted GRBC must already be canonical"
    );
    let answer = function_id(&decoded, "answer");
    let first = function_id(&decoded, "first");
    let struct_answer = function_id(&decoded, "struct_answer");
    let empty_choice = function_id(&decoded, "empty_choice");
    let number_choice = function_id(&decoded, "number_choice");
    let pair_choice = function_id(&decoded, "pair_choice");
    let matched_empty = function_id(&decoded, "matched_empty");
    let matched_number = function_id(&decoded, "matched_number");
    let matched_pair = function_id(&decoded, "matched_pair");
    let matched_pair_tail = function_id(&decoded, "matched_pair_tail");
    let branch_final = function_id(&decoded, "branch_final");
    let branch_final_empty = function_id(&decoded, "branch_final_empty");
    let branch_final_number = function_id(&decoded, "branch_final_number");
    let branch_final_pair = function_id(&decoded, "branch_final_pair");
    let matched_scalar_zero = function_id(&decoded, "matched_scalar_zero");
    let matched_scalar_other = function_id(&decoded, "matched_scalar_other");
    let main = function_id(&decoded, "main");
    assert!(decoded.types.iter().any(|ty| matches!(
        ty.representation(),
        Type::Struct { name, fields, .. }
            if name == "Pair"
                && fields.len() == 2
                && fields[0].name == "first"
                && fields[1].name == "second"
    )));
    let choice = decoded
        .types
        .iter()
        .position(|ty| {
            matches!(
                ty.representation(),
                Type::Enum { name, .. } if name == "Choice"
            )
        })
        .expect("self-hosted artifact must contain Choice") as u32;
    let Type::Enum { variants, .. } = decoded.types[choice as usize].representation() else {
        unreachable!()
    };
    assert_eq!(
        variants
            .iter()
            .map(|variant| variant.name.as_str())
            .collect::<Vec<_>>(),
        ["Empty", "Number", "Pair"]
    );
    assert!(variants[0].fields.is_empty());
    assert_eq!(variants[1].fields.len(), 1);
    assert_eq!(variants[1].fields[0].name, "0");
    assert_eq!(variants[1].fields[0].ty, I64);
    assert_eq!(variants[2].fields.len(), 2);
    assert_eq!(variants[2].fields[0].name, "0");
    assert_eq!(variants[2].fields[0].ty, I64);
    assert_eq!(variants[2].fields[1].name, "1");
    assert_eq!(variants[2].fields[1].ty, U64);
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::EnumTag { .. })),
        "enum handles must inspect the subject tag"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Switch { .. })),
        "enum handles must branch on the subject tag"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::ProjectMove { .. })),
        "enum handles must move payload fields into arm bindings"
    );
    assert!(
        decoded
            .code
            .iter()
            .any(|instruction| matches!(instruction, Instruction::Deconstruct { .. })),
        "enum handles must consume the matched aggregate shell"
    );
    let branch = &decoded.functions[branch_final as usize];
    let branch_code =
        &decoded.code[branch.code_start as usize..(branch.code_start + branch.code_len) as usize];
    assert!(
        branch_code
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Move { .. }))
            .count()
            >= 7,
        "CFG-final uses in the subject and every arm must lower as moves"
    );
    drop(decoded);
    let verified = load_verified(bytes).expect("self-hosted GRBC must verify");
    assert_eq!(
        Vm::new(verified.clone()).run(answer, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(first, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(struct_answer, vec![])
            .unwrap(),
        Value::I64(11)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(empty_choice, vec![]).unwrap(),
        Value::aggregate_with_variant(choice, Some(0), [])
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(number_choice, vec![])
            .unwrap(),
        Value::aggregate_with_variant(choice, Some(1), [Value::I64(13)])
    );
    assert_eq!(
        Vm::new(verified.clone()).run(pair_choice, vec![]).unwrap(),
        Value::aggregate_with_variant(choice, Some(2), [Value::I64(7), Value::U64(9)])
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_empty, vec![])
            .unwrap(),
        Value::I64(3)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_number, vec![])
            .unwrap(),
        Value::I64(13)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(matched_pair, vec![]).unwrap(),
        Value::I64(7)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_pair_tail, vec![])
            .unwrap(),
        Value::U64(9)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(branch_final_empty, vec![])
            .unwrap(),
        Value::I64(17)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(branch_final_number, vec![])
            .unwrap(),
        Value::I64(17)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(branch_final_pair, vec![])
            .unwrap(),
        Value::I64(17)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_scalar_zero, vec![])
            .unwrap(),
        Value::I64(31)
    );
    assert_eq!(
        Vm::new(verified.clone())
            .run(matched_scalar_other, vec![])
            .unwrap(),
        Value::I64(37)
    );
    assert_eq!(Vm::new(verified).run(main, vec![]).unwrap(), Value::Unit);
}

#[test]
// Release-only profiling harness for substantial generated bootstrap bytecode.
//
// Run without the self-host stage replay, for example:
// `G1_VM_OPCODE_PROFILE=1 tooling/ram-gate.sh cargo test --release -p grandiose
// --test self_host_bytecode self_host_callable_backend_direct_mir_emits_vm_callable_wire_format
// -- --exact --nocapture`
// The VM prints `g1-vm-opcode-profile` with exact executed instruction and
// opcode-category counts. Combine it with `G1_VM_HOT_FUNCTION_SAMPLE_STEPS`
// when selecting the next interpreter optimization target.
fn self_host_callable_backend_direct_mir_emits_vm_callable_wire_format() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let bundle = self_host_effect_backend_bundle();
            let artifact = grandiose::compile_bundle_to_bytecode_with_options(
                &bundle,
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap_or_else(|errors| {
                for error in &errors {
                    if let Some(span) = error.span
                        && let Some(segment) = bundle.segment_at(span.start)
                    {
                        let base = segment.global_range().start;
                        eprintln!(
                            "{}:{}..{}: {}",
                            segment.name(),
                            span.start - base,
                            span.end - base,
                            error.message
                        );
                    }
                }
                panic!("{errors:#?}")
            });
            let terminal_artifact = function_id(&artifact, "effect_backend_terminal_artifact");
            let nonterminal_artifact =
                function_id(&artifact, "effect_backend_nonterminal_artifact");
            let invalid_terminal = function_id(&artifact, "effect_backend_invalid_terminal_reason");
            let invalid_resumption =
                function_id(&artifact, "effect_backend_invalid_resumption_reasons");
            let callable_artifact =
                function_id(&artifact, "callable_backend_direct_mir_artifact");
            let compiler_bytes = artifact.encode();
            drop(artifact);
            let compiler = load_verified(&compiler_bytes).unwrap();
            drop(compiler_bytes);
            let run = |name: &str| {
                let function = match name {
                    "effect_backend_terminal_artifact" => terminal_artifact,
                    "effect_backend_nonterminal_artifact" => nonterminal_artifact,
                    "effect_backend_invalid_terminal_reason" => invalid_terminal,
                    "effect_backend_invalid_resumption_reasons" => invalid_resumption,
                    "callable_backend_direct_mir_artifact" => callable_artifact,
                    _ => unreachable!("unknown effect-backend probe {name}"),
                };
                Vm::new(compiler.clone()).run(function, vec![]).unwrap()
            };

            let Value::Bytes(bytes) = run("effect_backend_terminal_artifact") else {
                panic!("terminal backend probe did not return artifact bytes")
            };
            let decoded =
                Artifact::decode(bytes.as_ref()).expect("terminal effect artifact must decode");
            assert_eq!(
                decoded.encode(),
                bytes.as_ref(),
                "bootstrap and self-host encoders must agree"
            );
            assert_eq!(decoded.required_features, 1 | (1 << 3));
            assert_eq!(decoded.protocols.len(), 1);
            assert_eq!(decoded.protocols[0].display_name, "Probe");
            assert_eq!(decoded.protocols[0].operations.len(), 1);
            let operation = &decoded.protocols[0].operations[0];
            assert_eq!(operation.name, "stop");
            assert!(operation.payload_signature.params.is_empty());
            assert_eq!(operation.payload_signature.result, grandiose_vm::UNIT);
            assert!(operation.payload_signature.outward_protocols.is_empty());
            assert!(operation.terminal);
            assert_eq!(operation.result_type, grandiose_vm::bytecode::NEVER);
            assert_eq!(
                (operation.resumption_lower, operation.resumption_upper),
                (0, Some(0))
            );
            assert!(matches!(
                decoded.code.as_slice(),
                [Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 0,
                    payloads,
                }] if payloads.is_empty()
            ));
            load_verified(bytes.as_ref()).expect("terminal effect artifact must verify");

            let Value::Bytes(bytes) = run("effect_backend_nonterminal_artifact") else {
                panic!("nonterminal backend probe did not return artifact bytes")
            };
            let decoded =
                Artifact::decode(bytes.as_ref()).expect("nonterminal effect artifact must decode");
            assert_eq!(
                decoded.encode(),
                bytes.as_ref(),
                "bootstrap and self-host resumption encoders must agree"
            );
            assert_eq!(decoded.required_features, 1 | (1 << 3) | (1 << 4));
            assert_eq!(decoded.protocols.len(), 1);
            assert_eq!(decoded.protocols[0].display_name, "Ask");
            assert_eq!(decoded.protocols[0].operations.len(), 1);
            let operation = &decoded.protocols[0].operations[0];
            assert_eq!(operation.name, "ask");
            assert!(operation.payload_signature.params.is_empty());
            assert_eq!(operation.payload_signature.result, grandiose_vm::UNIT);
            assert!(operation.payload_signature.outward_protocols.is_empty());
            assert_eq!(operation.result_type, grandiose_vm::U32);
            assert_eq!(
                (operation.resumption_lower, operation.resumption_upper),
                (1, Some(1))
            );
            assert!(!operation.terminal);
            assert_eq!(decoded.handler_defs.len(), 1);
            assert_eq!(decoded.handler_defs[0].result_type, grandiose_vm::U32);
            assert!(!decoded.handler_defs[0].partial);
            assert_eq!(decoded.handler_defs[0].clauses.len(), 1);
            assert_eq!(decoded.handler_defs[0].clauses[0].protocol, 0);
            assert_eq!(decoded.handler_defs[0].clauses[0].operation, 0);
            let resumption = decoded.handler_defs[0].clauses[0]
                .resumption_type
                .expect("nonterminal clause must name its resumption type");
            assert!(matches!(
                decoded.types[resumption as usize].representation(),
                grandiose_vm::Type::Resumption {
                    input_type: grandiose_vm::U32,
                    output_type: grandiose_vm::U32,
                    effect_signature,
                    lower_uses: 1,
                    upper_uses: Some(1),
                    identity_name,
                    copy: false,
                } if effect_signature.params.is_empty()
                    && effect_signature.result == grandiose_vm::U32
                    && effect_signature.outward_protocols.is_empty()
                    && identity_name == "probe one-shot resumption"
            ));
            assert!(!decoded.types[resumption as usize].claimed_duplicable());
            assert!(!decoded.types[resumption as usize].claimed_zero_use_allowed());
            let unbounded = decoded
                .types
                .iter()
                .find(|ty| {
                    matches!(
                        ty.representation(),
                        grandiose_vm::Type::Resumption { identity_name, .. }
                            if identity_name == "probe unbounded resumption"
                    )
                })
                .expect("unbounded resumption type must be present");
            assert!(matches!(
                unbounded.representation(),
                grandiose_vm::Type::Resumption {
                    input_type: grandiose_vm::UNIT,
                    output_type: grandiose_vm::UNIT,
                    effect_signature,
                    lower_uses: 0,
                    upper_uses: None,
                    identity_name,
                    copy: true,
                } if effect_signature.params.is_empty()
                    && effect_signature.result == grandiose_vm::UNIT
                    && effect_signature.outward_protocols.is_empty()
                    && identity_name == "probe unbounded resumption"
            ));
            assert!(unbounded.claimed_duplicable());
            assert!(unbounded.claimed_zero_use_allowed());
            assert_eq!(
                decoded.handler_defs[0].clauses[0].callable_signature.params,
                [resumption]
            );
            assert_eq!(
                decoded.handler_defs[0].clauses[0].callable_signature.result,
                grandiose_vm::U32
            );
            assert!(
                decoded.handler_defs[0].clauses[0]
                    .callable_signature
                    .outward_protocols
                    .is_empty()
            );
            load_verified(bytes.as_ref()).expect("nonterminal effect artifact must verify");

            let Value::Bytes(bytes) = run("callable_backend_direct_mir_artifact") else {
                panic!("callable backend probe did not return artifact bytes")
            };
            let decoded = Artifact::decode(bytes.as_ref())
                .expect("callable MIR artifact must decode");
            assert_eq!(decoded.encode(), bytes.as_ref(),
                "bootstrap and self-host callable encoders must agree");
            assert!(matches!(decoded.types[19].representation(),
                Type::Callable {
                    signature, capture_type: grandiose_vm::UNIT,
                    receiver_mode: 2, identity_name, copy: false,
                    zero_use_allowed: false,
                } if signature.params.is_empty()
                    && signature.result == grandiose_vm::UNIT
                    && signature.outward_protocols.is_empty()
                    && identity_name == "direct callable"
            ));
            assert!(matches!(decoded.code.as_slice(), [
                Instruction::MakeCallable { callable_type: 19, function: 1,
                    captures, .. },
                Instruction::CallIndirect { dst: None, callable: 1,
                    receiver_mode: 2, args },
                Instruction::Return { src: None },
                Instruction::Return { src: None },
            ] if captures.is_empty() && args.is_empty()));
            let verified = load_verified(bytes.as_ref())
                .expect("callable MIR artifact must verify");
            assert_eq!(Vm::new(verified).run(0, vec![]).unwrap(), Value::Unit);

            assert_eq!(
                run("effect_backend_invalid_terminal_reason"),
                Value::U64(4),
                "terminal metadata must require NEVER and [0,0]"
            );
            assert_eq!(
                run("effect_backend_invalid_resumption_reasons"),
                Value::U64(654_321),
                "malformed resumption descriptors must preserve typed reasons"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_hosted_frontend_emits_canonical_executable_bytecode_in_vm_and_native() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_BYTECODE_CHECK_ONLY").is_some() {
                let bundle = self_host_bundle();
                if let Some(offset) = std::env::var("G1_SPAN_TRACE")
                    .ok()
                    .and_then(|offset| offset.parse::<usize>().ok())
                    && let Some(segment) = bundle.segment_at(offset)
                {
                    eprintln!(
                        "trace span: {}:{}",
                        segment.name(),
                        offset - segment.global_range().start
                    );
                }
                let phases = grandiose::compile_bundle_to_phases_with_options(
                    &bundle,
                    CompileOptions {
                        optimization_level: OptimizationLevel::O3,
                    },
                )
                .unwrap_or_else(|errors| {
                    for error in &errors {
                        if let Some(span) = error.span
                            && let Some(segment) = bundle.segment_at(span.start)
                        {
                            let base = segment.global_range().start;
                            eprintln!(
                                "{}:{}..{}: {}",
                                segment.name(),
                                span.start - base,
                                span.end - base,
                                error.message
                            );
                        }
                    }
                    panic!("{errors:#?}")
                });
                let encoded = phases.artifact.encode();
                load_verified(&encoded).unwrap();
                return;
            }
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("input.glorious");
            fs::write(&input, FIXTURE).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O3,
                },
            )
            .unwrap();
            let compiler_entry = phases.artifact.entry_function.unwrap();
            let compiler_bytes = phases.artifact.encode();
            if let Some(directory) = std::env::var_os("G1_SELF_HOST_REPLAY_DIR") {
                let directory = PathBuf::from(directory);
                fs::create_dir_all(&directory).unwrap();
                fs::write(directory.join("fixture-stage1.grbc"), &compiler_bytes).unwrap();
                fs::write(directory.join("fixture-input.glorious"), FIXTURE).unwrap();
            }
            let compiler = load_verified(&compiler_bytes).unwrap();

            assert_diagnostic_contracts(|name, args| {
                Vm::with_host(
                    compiler.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![]),
                )
                .unwrap()
                .run(function_id(&phases.artifact, name), args)
                .unwrap()
            });

            let classify = function_id(&phases.artifact, "classify_compile_error");
            for (source, expected) in [("\"", 1), ("}", 2), ("struct Broken { field }", 3)] {
                assert_eq!(
                    Vm::with_host(
                        compiler.clone(),
                        ["process.args", "fs.read", "fs.write", "diagnostic"],
                        SystemHost::new(vec![]),
                    )
                    .unwrap()
                    .run(classify, vec![Value::Text(source.into())])
                    .unwrap(),
                    Value::U64(expected),
                    "{source:?}"
                );
            }

            // The VM-only measurement never emits LLVM IR from `phases`, so once
            // the frontend probes have read their function IDs and the GRBC has
            // been decoded into the VM image, neither the bootstrap
            // compile-phase graph (`phases` holds the whole artifact, core, MIR,
            // and provisional buffer) nor the encoded byte buffer is needed
            // again. Release both *before* starting the VM so the VM-only peak
            // does not retain large compile-phase / encoded-byte data
            // simultaneously with the running VM image. This branch always
            // returns, so the full (LLVM/native) path below still sees `phases`
            // as live.
            let vm_only = std::env::var_os("G1_SELF_HOST_BYTECODE_VM_ONLY").is_some();
            if vm_only {
                drop(phases);
                drop(compiler_bytes);
                let vm_output = directory.path().join("vm.grbc");
                let vm = Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        vm_output.clone().into_os_string(),
                        input.clone().into_os_string(),
                    ]),
                )
                .unwrap();
                assert_eq!(vm.run(compiler_entry, vec![]).unwrap(), Value::Unit);
                let vm_bytes = fs::read(&vm_output).unwrap();
                assert_compiled_artifact(&vm_bytes);
                return;
            }

            let vm_output = directory.path().join("vm.grbc");
            let vm = Vm::with_host(
                compiler,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![
                    vm_output.clone().into_os_string(),
                    input.clone().into_os_string(),
                ]),
            )
            .unwrap();
            assert_eq!(vm.run(compiler_entry, vec![]).unwrap(), Value::Unit);
            let vm_bytes = fs::read(&vm_output).unwrap();
            assert_compiled_artifact(&vm_bytes);

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-bytecode.ll");
            let executable = directory.path().join("self-host-bytecode");
            fs::write(&llvm, module.ir).unwrap();
            drop(phases);
            let clang = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O3")
                .arg("-o")
                .arg(&executable)
                .output()
                .unwrap();
            assert!(
                clang.status.success(),
                "{}",
                String::from_utf8_lossy(&clang.stderr)
            );

            let native_output = directory.path().join("native.grbc");
            let native = Command::new(&executable)
                .arg(&native_output)
                .arg(&input)
                .output()
                .unwrap();
            assert!(
                native.status.success(),
                "native self-host compiler failed: {:?}\n{}",
                native.status,
                String::from_utf8_lossy(&native.stderr)
            );
            let native_bytes = fs::read(&native_output).unwrap();
            assert_eq!(native_bytes, vm_bytes, "VM and LLVM hosts must agree");
            assert_compiled_artifact(&native_bytes);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release VM diagnostic gate"]
fn self_hosted_effect_elaboration_diagnostic_returns_without_abort() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("invalid-terminal-effect.glorious");
            let output = directory.path().join("unexpected-output.grbc");
            fs::write(
                &input,
                // A terminal operation may not declare a resumption quantity.
                // Header elaboration reports this as local diagnostic code 64
                // during InterfaceCollection (G5064). Before the exhaustive
                // mapping this same ElaborationError reached `unreachable()`.
                "effect Stop { [1,1] stop() -> ! } main() { () }",
            )
            .unwrap();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let bytes = phases.artifact.encode();
            drop(phases);
            let compiler = load_verified(&bytes).unwrap();
            drop(bytes);
            let vm = Vm::with_host(
                compiler,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![output.into_os_string(), input.into_os_string()]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release VM terminal-perform gate"]
fn self_hosted_terminal_text_perform_emits_vm_effect_and_is_unhandled() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("terminal-perform.glorious");
            let output = directory.path().join("terminal-perform.grbc");
            fs::write(
                &input,
                // `Template` is a declaration template, not a runtime
                // protocol until a ground instance is requested. Keep it next
                // to a real terminal perform so the decoded artifact proves
                // that the self-host compiler does not serialize an empty
                // declaration-shaped placeholder.
                "effect Template<T> { discard(value: T) -> ! } \
                 effect Stop { stop(message: Text) -> ! } \
                 trigger() -> ! / {Stop} { perform Stop::stop(\"terminal\") } \
                 main() { () }",
            )
            .unwrap();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let compiler_bytes = phases.artifact.encode();
            drop(phases);
            let compiler = load_verified(&compiler_bytes).unwrap();
            drop(compiler_bytes);
            let vm = Vm::with_host(
                compiler,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![output.clone().into_os_string(), input.into_os_string()]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);

            let bytes = fs::read(&output).unwrap();
            let artifact = Artifact::decode(&bytes).unwrap();
            assert_eq!(artifact.protocols.len(), 1);
            let operation = &artifact.protocols[0].operations[0];
            assert_eq!(operation.name, "stop");
            assert_eq!(operation.payload_signature.params.len(), 1);
            assert_eq!(operation.payload_signature.result, grandiose_vm::UNIT);
            assert!(operation.terminal);
            let trigger = function_id(&artifact, "trigger");
            assert_eq!(artifact.functions[trigger as usize].outward_protocols, [0]);
            assert!(artifact.code.iter().any(|instruction| matches!(
                instruction,
                Instruction::Perform {
                    dst: None,
                    protocol: 0,
                    operation: 0,
                    payloads,
                } if payloads.len() == 1
            )));
            let verified = load_verified(&bytes).unwrap();
            assert_eq!(
                Vm::new(verified).run(trigger, vec![]),
                Err(RuntimeError::UnhandledEffect {
                    protocol: 0,
                    operation: 0,
                })
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release VM gate"]
fn self_hosted_terminal_bool_handler_classifier_reaches_variant_dispatch() {
    std::thread::Builder::new().stack_size(64 * 1024 * 1024).spawn(|| {
        let source = "effect Branch { select(condition: Bool) -> ! } \
            choose(value: Bool) -> u32 { \
                handle Branch::select(value) { \
                    Branch::select(true) => 10, \
                    Branch::select(false) => 20 \
                } \
            } main() { () }";
        let phases = grandiose::compile_bundle_to_phases_with_options(
            &self_host_bundle(), CompileOptions { optimization_level: OptimizationLevel::O2 }
        ).unwrap();
        let classify = function_id(&phases.artifact, "classify_compile_error");
        let compiler = load_verified(&phases.artifact.encode()).unwrap();
        assert_eq!(Vm::with_host(compiler, ["process.args", "fs.read", "fs.write", "diagnostic"],
            SystemHost::new(vec![])).unwrap().run(classify, vec![Value::Text(source.into())]).unwrap(), Value::U64(0));
    }).unwrap().join().unwrap();
}

#[test]
#[ignore = "expensive release VM source-capability batch"]
fn self_hosted_source_capabilities_in_release_vm() {
    #[derive(Clone, Copy)]
    enum Probe {
        Classify,
        Diagnostic,
    }

    struct Case {
        name: &'static str,
        probe: Probe,
        source: &'static str,
        expected: u64,
    }

    let cases = [
        Case {
            // One terminal operation, one u32 payload, literal tests followed
            // by a wildcard, and one common scalar result.
            name: "terminal u32 handler scalar dispatch",
            probe: Probe::Classify,
            source: "effect Stop { stop(value: u32) -> ! } \
                selected() -> u32 { \
                    handle Stop::stop(2) { \
                        Stop::stop(0) => 10, \
                        Stop::stop(2) => 20, \
                        Stop::stop(_) => 30 \
                    } \
                } \
                main() { () }",
            expected: 0,
        },
        Case {
            name: "terminal Bool handler variant dispatch",
            probe: Probe::Classify,
            source: "effect Branch { select(condition: Bool) -> ! } \
                choose(value: Bool) -> u32 { \
                    handle Branch::select(value) { \
                        Branch::select(true) => 10, \
                        Branch::select(false) => 20 \
                    } \
                } main() { () }",
            expected: 0,
        },
        Case {
            // Abstract trait and generic-impl callables must defer, while the
            // concrete implementation members remain seedable and lowerable.
            name: "abstract trait and generic impl callable deferral",
            probe: Probe::Classify,
            source: "trait Measure { measure(self: &Self) -> i64; } \
                struct Wrapper<T> { value: T } \
                impl<T> Measure for Wrapper<T> { \
                    measure(self: &Self) -> i64 { 1 } \
                } \
                trait Entry { main() -> (); } \
                impl Entry for i64 { main() -> () { () } } \
                trait Route { first(value: i64) -> i64; second(other: i64) -> i64; } \
                impl Route for i64 { \
                    first(value: i64) -> i64 { value } \
                    second(other: i64) -> i64 { other } \
                } \
                main() { () }",
            expected: 0,
        },
        Case {
            // Effect MIR is intentionally not implemented, but its structured
            // lowering diagnostic must return rather than aborting.
            name: "residual effect control lowering diagnostic",
            probe: Probe::Diagnostic,
            source: "effect Ask { [1,1] ask(value: i64) -> i64 } \
                answer(value: i64) -> i64 / {Ask} { perform Ask::ask(value) }",
            expected: 10_710_026_103,
        },
    ];

    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let (compiler, classify, diagnostic) = bootstrap_self_host_release_vm();
            for case in cases {
                let function = match case.probe {
                    Probe::Classify => classify,
                    Probe::Diagnostic => diagnostic,
                };
                assert_eq!(
                    run_self_host_source_probe(&compiler, function, case.source),
                    Value::U64(case.expected),
                    "{}",
                    case.name
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release VM literal-lowering gate"]
fn self_hosted_compiler_lowers_text_and_bytes_literals_in_release_vm() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = "text_value() -> Text { \"hello\" } \
                bytes_value() -> Bytes { b\"\\x00\\xff\" } \
                main() { () }";
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("literal-input.glorious");
            let output = directory.path().join("literal-output.grbc");
            fs::write(&input, source).unwrap();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let compiler = load_verified(&phases.artifact.encode()).unwrap();
            assert_eq!(
                Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        output.clone().into_os_string(),
                        input.into_os_string(),
                    ]),
                )
                .unwrap()
                .run(entry, vec![])
                .unwrap(),
                Value::Unit,
                "self-host compiler must emit literal bytecode"
            );
            let bytes = fs::read(output).unwrap();
            let artifact = Artifact::decode(&bytes)
                .expect("text and bytes constants must use GRBC wire payloads");
            assert!(artifact.constants.iter().any(
                |constant| matches!(constant, Constant::Text(text) if text == "hello")
            ));
            assert!(artifact.constants.iter().any(
                |constant| matches!(constant, Constant::Bytes(bytes) if bytes == &[0, 0xff])
            ));
            load_verified(&bytes)
                .expect("literal artifact must pass VM bytecode verification");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release VM label-control gate"]
fn self_hosted_compiler_executes_protected_labels_and_nested_leave_in_release_vm() {
    // Keep this an end-to-end VM check.  The source program deliberately uses
    // both protected-region exits: `normal_label` reaches its join through
    // LabelPop, while `nested_leave` skips the inner region and reaches the
    // outer typed destination through Leave.  This is the executable core of
    // the bootstrap labels_leave.rs regressions, including lexical shadowing
    // of the active destination stack.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = r#"
                normal_label() -> i64 {
                    @done: i64 { 7 }
                }
                nested_leave() -> i64 {
                    @outer: i64 {
                        @inner: i64 {
                            @outer(42)
                        }
                    }
                }
                bool_dispatch_to_outer(value: Bool) -> i64 {
                    @outer: i64 {
                        @inner: i64 {
                            match(value) {
                                true => @outer(11),
                                false => @outer(22)
                            }
                        }
                    }
                }
                integer_dispatch_to_outer(value: u64) -> i64 {
                    @outer: i64 {
                        @inner: i64 {
                            match(value) {
                                0 => @outer(33),
                                _ => @outer(44)
                            }
                        }
                    }
                }
                bool_dispatch_returns(value: Bool) -> i64 {
                    match(value) { true => 55, false => 66 }
                }
                // Keep one normal arm alongside an outer transfer.  The
                // lowering must allocate a join result for the normal arm,
                // while retaining the direct Leave for the terminal one.
                bool_dispatch_mixed(value: Bool) -> i64 {
                    @outer: i64 {
                        match(value) {
                            true => @outer(101),
                            false => 102
                        }
                    }
                }
                // Construct Bool values in source: the production prelude
                // represents Bool as a nominal Result alias, not a VM scalar.
                bool_dispatch_to_outer_true() -> i64 {
                    bool_dispatch_to_outer(true)
                }
                bool_dispatch_to_outer_false() -> i64 {
                    bool_dispatch_to_outer(false)
                }
                bool_dispatch_returns_false() -> i64 {
                    bool_dispatch_returns(false)
                }
                bool_dispatch_mixed_true() -> i64 {
                    bool_dispatch_mixed(true)
                }
                bool_dispatch_mixed_false() -> i64 {
                    bool_dispatch_mixed(false)
                }
                integer_dispatch_returns(value: u64) -> i64 {
                    match(value) { 0 => 77, _ => 88 }
                }
                integer_dispatch_mixed(value: u64) -> i64 {
                    @outer: i64 {
                        match(value) {
                            0 => @outer(103),
                            _ => 104
                        }
                    }
                }
                main() { () }
            "#;
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("labels-input.glorious");
            let output = directory.path().join("labels-output.grbc");
            fs::write(&input, source).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let entry = phases.artifact.entry_function.unwrap();
            let compiler = load_verified(&phases.artifact.encode()).unwrap();
            drop(phases);

            assert_eq!(
                Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        output.clone().into_os_string(),
                        input.into_os_string(),
                    ]),
                )
                .unwrap()
                .run(entry, vec![])
                .unwrap(),
                Value::Unit,
                "the self-host compiler must emit a label program"
            );

            let bytes = fs::read(output).unwrap();
            let artifact = Artifact::decode(&bytes).expect("label artifact must decode");
            load_verified(&bytes).expect("label artifact must pass VM verification");
            assert!(
                artifact
                    .code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::LabelPush { .. })),
                "the emitted program must preserve protected label entry"
            );
            assert!(
                artifact
                    .code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::LabelPop { .. })),
                "the normal label edge must pop its protected destination"
            );
            assert!(
                artifact
                    .code
                    .iter()
                    .any(|instruction| matches!(instruction, Instruction::Leave { .. })),
                "the nested outer transfer must remain a VM Leave"
            );

            let verified = load_verified(&bytes).unwrap();
            assert_eq!(
                Vm::new(verified.clone())
                    .run(function_id(&artifact, "normal_label"), vec![])
                    .unwrap(),
                Value::I64(7)
            );
            assert_eq!(
                Vm::new(verified.clone())
                    .run(function_id(&artifact, "nested_leave"), vec![])
                    .unwrap(),
                Value::I64(42)
            );
            assert_eq!(
                Vm::new(verified.clone())
                    .run(
                        function_id(&artifact, "bool_dispatch_to_outer_true"),
                        vec![]
                    )
                    .unwrap(),
                Value::I64(11)
            );
            assert_eq!(
                Vm::new(verified.clone())
                    .run(
                        function_id(&artifact, "bool_dispatch_to_outer_false"),
                        vec![]
                    )
                    .unwrap(),
                Value::I64(22)
            );
            assert_eq!(
                Vm::new(verified.clone())
                    .run(
                        function_id(&artifact, "integer_dispatch_to_outer"),
                        vec![Value::U64(0)]
                    )
                    .unwrap(),
                Value::I64(33)
            );
            assert_eq!(
                Vm::new(verified)
                    .run(
                        function_id(&artifact, "integer_dispatch_to_outer"),
                        vec![Value::U64(9)]
                    )
                    .unwrap(),
                Value::I64(44)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "bool_dispatch_returns_false"),
                        vec![]
                    )
                    .unwrap(),
                Value::I64(66)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "integer_dispatch_returns"),
                        vec![Value::U64(0)]
                    )
                    .unwrap(),
                Value::I64(77)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "integer_dispatch_returns"),
                        vec![Value::U64(9)]
                    )
                    .unwrap(),
                Value::I64(88)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "bool_dispatch_mixed_true"),
                        vec![]
                    )
                    .unwrap(),
                Value::I64(101)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "bool_dispatch_mixed_false"),
                        vec![]
                    )
                    .unwrap(),
                Value::I64(102)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "integer_dispatch_mixed"),
                        vec![Value::U64(0)]
                    )
                    .unwrap(),
                Value::I64(103)
            );
            assert_eq!(
                Vm::new(load_verified(&bytes).unwrap())
                    .run(
                        function_id(&artifact, "integer_dispatch_mixed"),
                        vec![Value::U64(9)]
                    )
                    .unwrap(),
                Value::I64(104)
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn bootstrap_self_host_bytecode_prunes_dead_constants_in_release_vm() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let mut used = vec![false; phases.artifact.constants.len()];
            for instruction in &phases.artifact.code {
                match instruction {
                    Instruction::Const { constant, .. } => used[*constant as usize] = true,
                    Instruction::Switch { cases, .. } => {
                        for (constant, _) in cases {
                            used[*constant as usize] = true;
                        }
                    }
                    _ => {}
                }
            }
            assert!(
                used.into_iter().all(|used| used),
                "O2 bootstrap bytecode must not retain constants removed by peepholes"
            );

            let classify = function_id(&phases.artifact, "classify_compile_error");
            let compiler = load_verified(&phases.artifact.encode()).unwrap();
            assert_eq!(
                Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![]),
                )
                .unwrap()
                .run(classify, vec![Value::Text("\"".into())])
                .unwrap(),
                Value::U64(1),
                "the compacted bootstrap artifact must execute in the VM"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_hosted_prelude_bool_alias_resolves_before_literal_fallback_in_release_vm() {
    // The production prelude models Bool as Result<(), ()> and then exports
    // `true` as a global factory alias. Resolution must use that alias when
    // present; otherwise elaboration treats the identifier as the focused
    // probe's private scalar Bool and rejects the declared result type.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = "enum Result<T, E> { Ok(T), Err(E) } \
                type Option<T> = Result<T, ()>; \
                type Bool = Option<()>; \
                make_true() -> Bool { Result::Ok(()) } \
                let true = make_true(); \
                use_true() -> Bool { true }";
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let classify = function_id(&phases.artifact, "classify_compile_error");
            let compiler = load_verified(&phases.artifact.encode()).unwrap();
            assert_eq!(
                Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![]),
                )
                .unwrap()
                .run(classify, vec![Value::Text(source.into())])
                .unwrap(),
                Value::U64(0),
                "a source Bool factory alias must override bare-literal fallback"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn self_hosted_generic_alias_enum_construction_reaches_backend_in_release_vm() {
    // A constructor through nested aliases must adopt the expected nominal
    // application.  This is the small form of the compiler prelude's Bool
    // constructors (`Bool = Option<()> = Result<(), ()>`).
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source = "enum Result<T, E> { Ok(T), Err(E) } \
                type Option<T> = Result<T, ()>; \
                type Bool = Option<()>; \
                make_true() -> Bool { Result::Ok(()) }";
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let classify = function_id(&phases.artifact, "classify_compile_error");
            let compiler = load_verified(&phases.artifact.encode()).unwrap();
            assert_eq!(
                Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![]),
                )
                .unwrap()
                .run(classify, vec![Value::Text(source.into())])
                .unwrap(),
                Value::U64(0),
                "generic enum construction through a nested alias must compile"
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release regression gate: compile and verify the complete production self-host bundle"]
fn full_self_host_bundle_compiles_to_a_verified_artifact_in_release() {
    // Keep this deliberately before executing stage one: this is the smallest
    // gate for lowering regressions in the production self-host compiler.  In
    // particular, all-terminal nested dispatches must not leave untyped dead
    // registers behind in the encoded artifact.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &production_self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O3,
                },
            )
            .unwrap_or_else(|errors| panic!("bootstrap compilation failed: {errors:#?}"));
            let bytes = phases.artifact.encode();
            decode_and_verify_full_self_host_artifact(&bytes);
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "expensive release differential: native Stage1 must compile the production monolith exactly as the VM does"]
fn production_stage1_native_matches_vm_on_canonical_monolith_in_release() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let bundle = production_self_host_bundle();
            let program = modules::parse_bundle(&bundle).expect("production bundle must parse");
            let resolved = modules::resolve_program(&bundle, program)
                .expect("production bundle must resolve");
            let source = modules::monolithic_source(&bundle, &resolved.resolution)
                .expect("production bundle must have one canonical source");
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &bundle,
                CompileOptions { optimization_level: OptimizationLevel::O3 },
            ).expect("bootstrap must compile production Stage1");
            let entry = phases.artifact.entry_function.expect("Stage1 entry");
            let bytes = phases.artifact.encode();
            let vm_stage1 = load_verified(&bytes).expect("Stage1 must verify");
            let llvm_options = LlvmOptions {
                native_allocation_limit: 536_870_912,
                ..LlvmOptions::default()
            };
            let module = grandiose::emit_llvm_ir(&phases, &llvm_options)
                .expect("Stage1 LLVM emission must succeed");
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("canonical.glorious");
            let vm_output = directory.path().join("vm-stage2.grbc");
            let native_output = directory.path().join("native-stage2.grbc");
            let llvm = directory.path().join("stage1.ll");
            let executable = directory.path().join("stage1-native");
            fs::write(&input, source.as_bytes()).unwrap();
            let vm = Vm::with_host(
                vm_stage1,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![vm_output.clone().into_os_string(), input.clone().into_os_string()]),
            ).unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            let vm_bytes = fs::read(&vm_output).expect("VM Stage1 must emit Stage2");
            fs::write(&llvm, module.ir).unwrap();
            let linked = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .args(["-O3", "--ld-path=wild", "-o"])
                .arg(&executable)
                .output().unwrap();
            assert!(linked.status.success(), "{}", String::from_utf8_lossy(&linked.stderr));
            let native = Command::new(&executable).arg(&native_output).arg(&input).output().unwrap();
            assert!(native.status.success(), "native Stage1 diagnostic:\n{}", String::from_utf8_lossy(&native.stderr));
            assert_eq!(fs::read(&native_output).unwrap(), vm_bytes, "native and VM Stage2 must be byte-identical");
        }).unwrap().join().unwrap();
}

#[test]
#[ignore = "expensive release gate: bootstrap and run two complete self-compilation stages"]
fn self_hosted_compiler_compiles_itself_to_a_byte_identical_fixed_point() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let source_bundle = production_self_host_bundle();
            let source_program = modules::parse_bundle(&source_bundle)
                .unwrap_or_else(|errors| panic!("self-host source did not parse: {errors:#?}"));
            let source_resolution = modules::resolve_program(&source_bundle, source_program)
                .unwrap_or_else(|errors| panic!("self-host source did not resolve: {errors:#?}"));
            let monolithic_source =
                modules::monolithic_source(&source_bundle, &source_resolution.resolution)
                    .expect("the self-host module graph must have a canonical one-file form");
            let source = monolithic_source.as_bytes();
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &source_bundle,
                CompileOptions {
                    optimization_level: OptimizationLevel::O3,
                },
            )
            .unwrap_or_else(|errors| panic!("bootstrap compilation failed: {errors:#?}"));
            let stage1_bytes = phases.artifact.encode();
            if let Some(directory) = std::env::var_os("G1_SELF_HOST_REPLAY_DIR") {
                let directory = PathBuf::from(directory);
                fs::create_dir_all(&directory).unwrap_or_else(|error| {
                    panic!(
                        "failed to create self-host replay directory {}: {error}",
                        directory.display()
                    )
                });
                fs::write(directory.join("stage1.grbc"), &stage1_bytes).unwrap();
                fs::write(directory.join("input.glorious"), source).unwrap();
            }
            let stage1 = load_verified(&stage1_bytes)
                .expect("the Rust-bootstrap compiler artifact must verify");
            let stage1_entry = phases
                .artifact
                .entry_function
                .expect("the bootstrap compiler must have an entry function");
            drop(phases);

            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("self-host-bundle.glorious");
            let stage2_path = directory.path().join("stage2.grbc");
            let stage3_path = directory.path().join("stage3.grbc");
            fs::write(&input, source).unwrap();

            let run_stage = |compiler, entry, output: &Path| {
                let vm = Vm::with_host(
                    compiler,
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(vec![
                        output.as_os_str().to_owned(),
                        input.as_os_str().to_owned(),
                    ]),
                )
                .unwrap();
                assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
                fs::read(output).unwrap_or_else(|error| {
                    panic!(
                        "the self-hosted compiler did not emit {}: {error}",
                        output.display()
                    )
                })
            };

            let stage2 = run_stage(stage1, stage1_entry, &stage2_path);
            let decoded_stage2 = Artifact::decode(&stage2).expect("stage 2 must decode");
            assert_eq!(decoded_stage2.encode(), stage2, "stage 2 must be canonical");
            let stage2_entry = decoded_stage2
                .entry_function
                .expect("stage 2 must have an entry function");
            let verified_stage2 = load_verified(&stage2).expect("stage 2 must verify");

            let stage3 = run_stage(verified_stage2, stage2_entry, &stage3_path);
            load_verified(&stage3).expect("stage 3 must verify");
            assert_eq!(stage2, stage3, "stage 2 and stage 3 must be byte-identical");
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
#[ignore = "diagnostic release gate: replay a captured stage-one compiler in the VM"]
fn self_hosted_stage_one_replay_emits_stage_two_in_release_vm() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let stage_one = PathBuf::from(
                std::env::var_os("G1_SELF_HOST_REPLAY_STAGE1")
                    .expect("G1_SELF_HOST_REPLAY_STAGE1 must name a stage-one artifact"),
            );
            let input = PathBuf::from(
                std::env::var_os("G1_SELF_HOST_REPLAY_INPUT")
                    .expect("G1_SELF_HOST_REPLAY_INPUT must name self-host source"),
            );
            let compiler = load_verified(&fs::read(&stage_one).unwrap())
                .expect("the captured stage-one artifact must verify");
            let entry = compiler
                .entry_function()
                .expect("the captured stage-one artifact must have an entry function");
            let directory = tempfile::tempdir().unwrap();
            let output = directory.path().join("stage2-replay.grbc");
            let vm = Vm::with_host(
                compiler,
                ["process.args", "fs.read", "fs.write", "diagnostic"],
                SystemHost::new(vec![
                    output.as_os_str().to_owned(),
                    input.into_os_string(),
                ]),
            )
            .unwrap();
            assert_eq!(vm.run(entry, vec![]).unwrap(), Value::Unit);
            let bytes = fs::read(output).expect("stage one must emit a stage-two artifact");
            load_verified(&bytes).expect("the replayed stage-two artifact must verify");
        })
        .unwrap()
        .join()
        .unwrap();
}
