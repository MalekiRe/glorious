use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

use grandiose::{
    CompileOptions, LlvmOptions, OptimizationLevel,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{
    Artifact, SystemHost, Type, Value, Vm,
    bytecode::{I64, Instruction, U64},
    verify::load_verified,
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

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
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
    let paths = [
        root.join("frontend/frontend.glorious"),
        root.join("frontend/lexer/lexer.glorious"),
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
    ];
    SourceBundle::distributed(
        primary,
        paths.into_iter().map(|path| {
            let source = fs::read_to_string(&path).unwrap();
            Segment::new(path.to_string_lossy(), source)
        }),
    )
}

fn function_id(artifact: &Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("self-hosted artifact is missing `{name}`")) as u32
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
    let branch_code = &decoded.code
        [branch.code_start as usize..(branch.code_start + branch.code_len) as usize];
    assert!(
        branch_code
            .iter()
            .filter(|instruction| matches!(instruction, Instruction::Move { .. }))
            .count()
            >= 7,
        "CFG-final uses in the subject and every arm must lower as moves"
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
        Vm::new(verified.clone()).run(branch_final_empty, vec![]).unwrap(),
        Value::I64(17)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(branch_final_number, vec![]).unwrap(),
        Value::I64(17)
    );
    assert_eq!(
        Vm::new(verified.clone()).run(branch_final_pair, vec![]).unwrap(),
        Value::I64(17)
    );
    assert_eq!(Vm::new(verified).run(main, vec![]).unwrap(), Value::Unit);
}

#[test]
fn self_hosted_frontend_emits_canonical_executable_bytecode_in_vm_and_native() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            if std::env::var_os("G1_SELF_HOST_BYTECODE_CHECK_ONLY").is_some() {
                let bundle = self_host_bundle();
                let phases = grandiose::compile_bundle_to_phases_with_options(
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
                load_verified(&phases.artifact.encode()).unwrap();
                return;
            }
            let directory = tempfile::tempdir().unwrap();
            let input = directory.path().join("input.glorious");
            fs::write(&input, FIXTURE).unwrap();

            let phases = grandiose::compile_bundle_to_phases_with_options(
                &self_host_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let compiler_entry = phases.artifact.entry_function.unwrap();
            let compiler = load_verified(&phases.artifact.encode()).unwrap();

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

            if std::env::var_os("G1_SELF_HOST_BYTECODE_VM_ONLY").is_some() {
                return;
            }

            let module = grandiose::emit_llvm_ir(&phases, &LlvmOptions::default()).unwrap();
            let llvm = directory.path().join("self-host-bytecode.ll");
            let executable = directory.path().join("self-host-bytecode");
            fs::write(&llvm, module.ir).unwrap();
            let clang = Command::new("clang")
                .arg(&llvm)
                .arg(repository_root().join("crates/grandiose/src/native_runtime.c"))
                .arg(repository_root().join("crates/grandiose/src/native_host_runtime.c"))
                .arg("-O2")
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
