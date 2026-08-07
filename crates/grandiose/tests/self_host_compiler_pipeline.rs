// Self-host compiler-pipeline parity: the self-hosted full pipeline
// (frontend -> ownership lowering -> emission) must agree with the Rust
// bootstrap compiler's accept/reject outcome on every focused case drawn from
// the modules_cli_sessions / compiler_pipeline suites.
//
// This is a focused subset parity gate. It compares whether each corpus source
// is accepted or rejected, and (on rejection) which compiler phase observes the
// failure. It deliberately exercises only programs the self-hosted pipeline
// already lowers, so a mismatch here is a real oracle divergence rather than a
// missing later-layer feature. Native execution of this same bundle is covered
// by the self_host_bytecode suite, so this file runs the comparison inside the
// VM and keeps the fixture focused.

use std::{
    fs,
    path::{Path, PathBuf},
};

use grandiose::{
    CompileOptions, OptimizationLevel, compile_bundle_to_bytecode_with_options,
    source_bundle::{Segment, SourceBundle},
};
use grandiose_vm::{SystemHost, Value, Vm, verify};

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

// The self-host compiler is compiled by the Rust bootstrap, then the probe
// below classifies each corpus source by running the self-hosted pipeline
// end-to-end. 0 means accepted; otherwise the failing phase index (the
// CompileError variant) is returned so the test can report where the two
// compilers diverge.
fn self_host_compiler_pipeline_bundle() -> SourceBundle {
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

fn function_id(artifact: &grandiose_vm::Artifact, name: &str) -> u32 {
    artifact
        .functions
        .iter()
        .position(|function| function.name == name)
        .unwrap_or_else(|| panic!("self-hosted artifact is missing `{name}`")) as u32
}

// A focused corpus drawn from the modules_cli_sessions/compiler_pipeline
// suites. Positive cases reuse function bodies the self-hosted pipeline is
// already known to lower (struct/enum construction and projection, locals,
// tuples, `handle` dispatch), so an accept/reject disagreement here is a real
// oracle divergence. Negative cases exercise frontend-phase rejections that the
// Rust bootstrap and self-host compiler must both report.
fn corpus() -> Vec<&'static str> {
    vec![
        // Accepted by both compilers: ordinary callable pipeline.  These names
        // deliberately avoid declarations injected by the bootstrap standard library.
        "pipeline_identity(value: i64) -> i64 { value } main() { () }",
        // Accepted by both: local bindings and struct construction/projection.
        "struct PipelinePair { first: i64, second: i64 } \
         pipeline_struct_answer() -> i64 { \
             let value = 11; \
             let pair = PipelinePair { second: value, first: value }; \
             pair.first \
         } \
         main() { () }",
        // Accepted by both: enum variants and `handle` dispatch.
        "enum PipelineChoice { Empty, Number(i64), Pair(i64, u64) } \
         pipeline_inspect_choice(choice: PipelineChoice) -> i64 { \
             handle choice { \
                 PipelineChoice::Empty => 3, \
                 PipelineChoice::Number(value) => value, \
                 PipelineChoice::Pair(first, _) => first \
             } \
         } \
         pipeline_matched_number() -> i64 { pipeline_inspect_choice(PipelineChoice::Number(13)) } \
         main() { () }",
        // Accepted by both: tuple construction and projection.
        "pipeline_first() -> i64 { let pair = (7, 9); pair.0 } main() { () }",
        // Accepted by both: an arm binder precedes a let in the same lexical
        // body. This ensures elaboration retains resolver-assigned local IDs.
        "enum PipelineBindingChoice { Number(i64) } \
         pipeline_extract_binding(choice: PipelineBindingChoice) -> i64 { \
             handle choice { PipelineBindingChoice::Number(value) => { let copy = value; copy } } \
         } main() { () }",
        // Public qualified aliases remain visible outside their defining module.
        "mod pipeline_aliases { pub type Public = i64; } \
         pipeline_public_alias(value: pipeline_aliases::Public) -> pipeline_aliases::Public { value } \
         main() { () }",
        // Rejected by both: a qualified private alias cannot escape its module.
        "mod pipeline_aliases { type Private = i64; } \
         pipeline_private_alias(value: pipeline_aliases::Private) -> pipeline_aliases::Private { value } \
         main() { () }",
        // Rejected by both: lexical analysis failure.
        "\"",
        // Rejected by both: declaration scanning failure.
        "}",
        // Rejected by both: malformed struct field (missing type).
        "struct Broken { field }",
        // Rejected by both: parameter is missing its `:` and type.
        "bad(value u32) { () }",
        // Rejected by both: empty generic type application.
        "type Bad = Pair<>; main() { () }",
        // Rejected by both: empty generic application on a parameter type.
        "bad(value: Vec<>) { () }",
        // Rejected by both: malformed effect resumption quantity.
        "effect Bad { [0 1] choose() -> u8; } main() { () }",
    ]
}

#[test]
#[ignore = "baseline-blocked: the full self-host compiler bundle is not yet green under the RAM gate; kept as a future compiler-pipeline parity gate"]
fn self_hosted_compiler_pipeline_accept_reject_matches_rust_in_vm() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let artifact = compile_bundle_to_bytecode_with_options(
                &self_host_compiler_pipeline_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let classify = function_id(&artifact, "classify_compile_error");
            let verified = verify(artifact).unwrap();

            for (index, source) in corpus().into_iter().enumerate() {
                let oracle_accepted =
                    grandiose::compile_source_to_bytecode("compiler-pipeline.glorious", source)
                        .is_ok();
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(Vec::<std::ffi::OsString>::new()),
                )
                .unwrap();
                let Value::U64(self_host_class) = vm
                    .run(classify, vec![Value::Text(source.to_owned().into())])
                    .unwrap()
                else {
                    panic!("classify_compile_error did not return u8 for case {index}");
                };
                let self_host_accepted = self_host_class == 0;

                assert_eq!(
                    oracle_accepted,
                    self_host_accepted,
                    "accept/reject divergence for corpus case {index}: {source:?} \
                     (Rust oracle accepted: {oracle_accepted}, self-host phase: {self_host_class})"
                );
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

// This is intentionally separate from the broader corpus: it is the smallest
// oracle for the temporary compiler-source prelude slice.  `Result` must have
// the same source-level availability as the bootstrap's distributed bundle,
// while an arbitrary missing nominal must still be rejected.
#[test]
#[ignore = "baseline-blocked: run through the full self-host compiler RAM gate"]
fn self_hosted_compiler_pipeline_result_prelude_does_not_mask_unknown_names() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let artifact = compile_bundle_to_bytecode_with_options(
                &self_host_compiler_pipeline_bundle(),
                CompileOptions {
                    optimization_level: OptimizationLevel::O2,
                },
            )
            .unwrap();
            let classify = function_id(&artifact, "classify_compile_error");
            let verified = verify(artifact).unwrap();
            let corpus = [
                (
                    "result() -> Result<i64, i64> { Result::Ok(7) } main() { () }",
                    true,
                ),
                ("unknown() -> DefinitelyMissing { () } main() { () }", false),
            ];

            for (source, expected) in corpus {
                let oracle =
                    grandiose::compile_source_to_bytecode("compiler-prelude.glorious", source)
                        .is_ok();
                assert_eq!(oracle, expected, "bootstrap oracle: {source:?}");
                let vm = Vm::with_host(
                    verified.clone(),
                    ["process.args", "fs.read", "fs.write", "diagnostic"],
                    SystemHost::new(Vec::<std::ffi::OsString>::new()),
                )
                .unwrap();
                let Value::U64(actual) = vm
                    .run(classify, vec![Value::Text(source.to_owned().into())])
                    .unwrap()
                else {
                    panic!("classify_compile_error did not return u8");
                };
                assert_eq!(actual == 0, oracle, "prelude parity: {source:?}");
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
