use std::{
    fs,
    path::{Path, PathBuf},
};

use grandiose::{
    CompileOptions, OptimizationLevel,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{Artifact, Value, Vm, verify::load_verified};

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_owned()
}

fn diagnostic_bundle() -> SourceBundle {
    let root = repository_root().join("self-host/src");
    let primary = Segment::new(
        root.join("diagnostic-test.glorious").to_string_lossy(),
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

            site_fingerprint(
                error: CompileError
            ) -> u64 {
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

            main() { () }
        "#,
    );
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
        .unwrap_or_else(|| panic!("self-host diagnostic artifact is missing `{name}`")) as u32
}

fn run(artifact: &Artifact, name: &str, args: Vec<Value>) -> Value {
    let verified = load_verified(&artifact.encode()).unwrap();
    Vm::new(verified)
        .run(function_id(artifact, name), args)
        .unwrap()
}

#[test]
fn self_host_diagnostics_normalize_frontend_and_backend_failures() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let phases = grandiose::compile_bundle_to_phases_with_options(
                &diagnostic_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let artifact = phases.artifact;

            let frontend = [
                (1_u64, 1_u64, 1016_u64, 1_u64, 0_u64),
                (2, 1, 2004, 2, 0),
                (3, 1, 3007, 2, 0),
                (7, 1, 7001, 2, 3),
                (8, 2, 8001, 2, 3),
                (9, 3, 9003, 2, 3),
            ];
            let fingerprint = |(phase, class, code, space, owner)| {
                phase * 1_000_000_000
                    + class * 100_000_000
                    + code * 1_000
                    + space * 10
                    + owner
            };
            let weights = [1_u64, 17, 289, 4_913, 83_521, 1_419_857];
            let mut expected = frontend
                .into_iter()
                .zip(weights)
                .map(|(value, weight)| fingerprint(value) * weight)
                .sum::<u64>();
            expected += (5_u64 * 10_000 + 2_007) * 1_771_561;
            expected += 10_007_u64 * 100_000_000
                + 5 * 1_000_000
                + 3 * 10_000
                + 2 * 100
                + 3;
            expected += 12_006_u64 * 19_487_171;

            assert_eq!(
                run(&artifact, "diagnostic_matrix", vec![]),
                Value::U64(expected)
            );
            assert_eq!(
                run(&artifact, "resource_limit_render", vec![]),
                Value::Text(
                    "[G2007] self-host compiler: declaration scanning failed (token 3); related token 4"
                        .into()
                )
            );
            assert_eq!(
                run(&artifact, "body_internal_site", vec![]),
                Value::U64(770_070_308_000_003_002)
            );
            assert_eq!(
                run(&artifact, "resolution_ambiguous_site", vec![]),
                Value::U64(280_020_209_030_403_002)
            );
            assert_eq!(
                run(&artifact, "elaboration_internal_site", vec![]),
                Value::U64(790_250_605_070_703_002)
            );
            assert_eq!(
                run(&artifact, "typed_space_contract", vec![]),
                Value::U64(1)
            );
            assert_eq!(
                run(&artifact, "diagnostic_codes_preserve_variant_identity", vec![]),
                Value::U64(1)
            );
            assert_eq!(
                run(&artifact, "zero_argument_contract", vec![]),
                Value::U64(1)
            );
            assert_eq!(
                run(&artifact, "zero_argument_render", vec![]),
                Value::Text(
                    "[G10008] self-host compiler: an unexpected enum variant reached lowering (type 4); related variant 0; owner declaration 2; expected 0, found 0"
                        .into()
                )
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
