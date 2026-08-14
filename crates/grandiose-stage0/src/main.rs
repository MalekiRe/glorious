//! Thin host adapter for the independent stage-zero compiler service.

use std::{collections::BTreeMap, env, fs, process::ExitCode};

use grandiose_stage0::{
    BootstrapLimits, BootstrapManifest, BootstrapStage, CompilationMode, CompilationRequest,
    CompileDiagnostic, CompilerBuildIdentity, Digest, LogicalPath, PackageKey, PrimitiveRole,
    PrimitiveSelector, RuntimeManifestInput, SourceInput, StageZeroCompiler,
    decode_and_verify_program,
};

#[derive(Clone, Copy, Eq, PartialEq)]
enum DiagnosticFormat {
    Text,
    Json,
}

struct CliSource {
    package: PackageKey,
    logical_path: LogicalPath,
    file: String,
}

struct CliOptions {
    diagnostic_format: DiagnosticFormat,
    runtime_manifest: Option<RuntimeManifestInput>,
    root_package: PackageKey,
    additional_sources: Vec<CliSource>,
    positional: Vec<String>,
}

fn main() -> ExitCode {
    let CliOptions {
        diagnostic_format,
        runtime_manifest,
        root_package,
        additional_sources,
        positional: arguments,
    } = match split_cli_options(env::args().skip(1)) {
        Ok(arguments) => arguments,
        Err(message) => {
            eprintln!("grc-stage0: {message}");
            usage();
            return ExitCode::from(2);
        }
    };
    let mut arguments = arguments.into_iter();
    let Some(command) = arguments.next() else {
        usage();
        return ExitCode::from(2);
    };
    if command == "verify-vm" {
        let Some(path) = arguments.next() else {
            eprintln!("grc-stage0: verify-vm requires a PROGRAM file");
            return ExitCode::from(2);
        };
        if arguments.next().is_some() {
            usage();
            return ExitCode::from(2);
        }
        return verify_program(&path);
    }
    if command == "verify-bootstrap" {
        let Some(earlier_program) = arguments.next() else {
            eprintln!(
                "grc-stage0: verify-bootstrap requires EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST"
            );
            return ExitCode::from(2);
        };
        let Some(earlier_manifest) = arguments.next() else {
            eprintln!(
                "grc-stage0: verify-bootstrap requires EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST"
            );
            return ExitCode::from(2);
        };
        let Some(later_program) = arguments.next() else {
            eprintln!(
                "grc-stage0: verify-bootstrap requires EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST"
            );
            return ExitCode::from(2);
        };
        let Some(later_manifest) = arguments.next() else {
            eprintln!(
                "grc-stage0: verify-bootstrap requires EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST"
            );
            return ExitCode::from(2);
        };
        if arguments.next().is_some() {
            usage();
            return ExitCode::from(2);
        }
        return verify_bootstrap(
            &earlier_program,
            &earlier_manifest,
            &later_program,
            &later_manifest,
        );
    }
    let Some(path) = arguments.next() else {
        eprintln!("grc-stage0: {command} requires a source FILE");
        return ExitCode::from(2);
    };
    let output = if matches!(command.as_str(), "emit-vm" | "emit-bootstrap-vm") {
        let Some(output) = arguments.next() else {
            eprintln!("grc-stage0: {command} requires an OUTPUT file");
            return ExitCode::from(2);
        };
        Some(output)
    } else {
        None
    };
    let bootstrap_manifest_output = if command == "emit-bootstrap-vm" {
        let Some(manifest) = arguments.next() else {
            eprintln!("grc-stage0: emit-bootstrap-vm requires a MANIFEST file");
            return ExitCode::from(2);
        };
        Some(manifest)
    } else {
        None
    };
    if arguments.next().is_some()
        || !matches!(
            command.as_str(),
            "check" | "run" | "emit-vm" | "emit-bootstrap-vm"
        )
    {
        usage();
        return ExitCode::from(2);
    }
    let bytes = match fs::read(&path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("grc-stage0: cannot read {path}: {error}");
            return ExitCode::from(1);
        }
    };
    let mut sources = vec![SourceInput::new(
        root_package.clone(),
        LogicalPath::parse("src/main.glorious").expect("static logical path is valid"),
        bytes,
    )];
    for additional in additional_sources {
        let bytes = match fs::read(&additional.file) {
            Ok(bytes) => bytes,
            Err(error) => {
                eprintln!("grc-stage0: cannot read {}: {error}", additional.file);
                return ExitCode::from(1);
            }
        };
        sources.push(SourceInput::new(
            additional.package,
            additional.logical_path,
            bytes,
        ));
    }
    let build = CompilerBuildIdentity::stage0(Digest::of_bytes(b"grandiose-stage0-command-v6"));
    let mode = match command.as_str() {
        "run" | "emit-vm" => CompilationMode::Build,
        "emit-bootstrap-vm" => CompilationMode::Bootstrap(BootstrapStage {
            ordinal: 1,
            producer: build.compiler,
            optimization_level: 0,
            limits: BootstrapLimits::new(65_536, 4 * 1024 * 1024 * 1024),
            expected_artifact: None,
        }),
        "check" => CompilationMode::Check,
        _ => unreachable!("command was validated before request construction"),
    };
    let request = CompilationRequest {
        build,
        mode,
        root_package,
        // The CLI owns all host paths and maps them into an explicit logical
        // source world. Semantic phases receive only immutable package/path
        // identities and source bytes.
        sources,
        target: "stage0-vm".into(),
        semantic_options: BTreeMap::new(),
        codegen_options: BTreeMap::new(),
        capability_manifest: vec![],
        runtime_manifest,
    };
    match StageZeroCompiler::new().compile(request) {
        Ok(outcome) => {
            render_diagnostics(&outcome.diagnostics, diagnostic_format);
            if command == "run" {
                match outcome
                    .artifact
                    .expect("successful build has verified artifact")
                    .run_display()
                {
                    Ok(value) => println!("{value}"),
                    Err(error) => {
                        eprintln!("grc-stage0: verified VM execution failed: {error:?}");
                        return ExitCode::from(1);
                    }
                }
            } else if let Some(output) = output {
                let artifact = outcome
                    .artifact
                    .expect("successful build has verified artifact");
                if let Err(error) = fs::write(&output, artifact.canonical_bytes()) {
                    eprintln!("grc-stage0: cannot write {output}: {error}");
                    return ExitCode::from(1);
                }
                if let Some(manifest_output) = bootstrap_manifest_output {
                    let manifest = outcome
                        .bootstrap_manifest
                        .expect("successful bootstrap build has a manifest");
                    let bytes = match manifest.encode() {
                        Ok(bytes) => bytes,
                        Err(error) => {
                            eprintln!("grc-stage0: cannot encode bootstrap manifest: {error:?}");
                            return ExitCode::from(1);
                        }
                    };
                    if let Err(error) = fs::write(&manifest_output, bytes) {
                        eprintln!("grc-stage0: cannot write {manifest_output}: {error}");
                        return ExitCode::from(1);
                    }
                }
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            render_diagnostics(&error.diagnostics(), diagnostic_format);
            ExitCode::from(1)
        }
    }
}

fn split_cli_options(arguments: impl IntoIterator<Item = String>) -> Result<CliOptions, String> {
    let mut format = DiagnosticFormat::Text;
    let mut seen_format = false;
    let mut standard_library = None;
    let mut selectors = Vec::new();
    let mut root_package = None;
    let mut additional_sources = Vec::new();
    let mut positional = Vec::new();
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if argument != "--diagnostics" {
            if argument == "--runtime-standard-library" {
                if standard_library.is_some() {
                    return Err("--runtime-standard-library may be specified at most once".into());
                }
                let Some(package) = arguments.next() else {
                    return Err("--runtime-standard-library requires a PACKAGE".into());
                };
                standard_library = Some(PackageKey(package));
                continue;
            }
            if argument == "--runtime-leaf" {
                let Some(role) = arguments.next() else {
                    return Err("--runtime-leaf requires ROLE MODULE NAME".into());
                };
                let Some(module_path) = arguments.next() else {
                    return Err("--runtime-leaf requires ROLE MODULE NAME".into());
                };
                let Some(name) = arguments.next() else {
                    return Err("--runtime-leaf requires ROLE MODULE NAME".into());
                };
                let Some(role) = PrimitiveRole::parse_selector_name(&role) else {
                    return Err(format!(
                        "unknown runtime leaf role `{role}` (expected {})",
                        [
                            PrimitiveRole::BranchBool,
                            PrimitiveRole::TextByteLen,
                            PrimitiveRole::TextConcat,
                            PrimitiveRole::TextEq,
                            PrimitiveRole::TextFromUtf8Checked,
                            PrimitiveRole::TextAsBytes,
                            PrimitiveRole::IntCheckedAdd,
                            PrimitiveRole::IntWrappingAdd,
                            PrimitiveRole::IntWrappingSub,
                            PrimitiveRole::IntWrappingMul,
                            PrimitiveRole::IntEqual,
                            PrimitiveRole::IntLess,
                            PrimitiveRole::IntGreater,
                            PrimitiveRole::IntBitAnd,
                            PrimitiveRole::IntBitOr,
                            PrimitiveRole::IntBitXor,
                            PrimitiveRole::IntBitNot,
                            PrimitiveRole::IntConvertCheckedToI64,
                            PrimitiveRole::IntConvertWrappingToI64,
                            PrimitiveRole::IntConvertCheckedToU32,
                            PrimitiveRole::IntConvertCheckedToUsize,
                            PrimitiveRole::IntConvertCheckedToU8,
                            PrimitiveRole::IntConvertCheckedToU16,
                            PrimitiveRole::IntConvertCheckedToI16,
                            PrimitiveRole::IntConvertCheckedToI32,
                            PrimitiveRole::IntConvertWrappingToI32,
                            PrimitiveRole::IntConvertCheckedToI8,
                            PrimitiveRole::IntConvertWrappingToI8,
                            PrimitiveRole::IntConvertCheckedToU64,
                            PrimitiveRole::IntShr,
                        ]
                        .map(PrimitiveRole::selector_name)
                        .join(", ")
                    ));
                };
                selectors.push(PrimitiveSelector {
                    role,
                    module_path,
                    name,
                });
                continue;
            }
            if argument == "--root-package" {
                if root_package.is_some() {
                    return Err("--root-package may be specified at most once".into());
                }
                let Some(package) = arguments.next() else {
                    return Err("--root-package requires a PACKAGE".into());
                };
                root_package = Some(PackageKey(package));
                continue;
            }
            if argument == "--source" {
                let Some(package) = arguments.next() else {
                    return Err("--source requires PACKAGE LOGICAL_PATH FILE".into());
                };
                let Some(logical_path) = arguments.next() else {
                    return Err("--source requires PACKAGE LOGICAL_PATH FILE".into());
                };
                let Some(file) = arguments.next() else {
                    return Err("--source requires PACKAGE LOGICAL_PATH FILE".into());
                };
                let logical_path = LogicalPath::parse(logical_path)
                    .map_err(|error| format!("--source has invalid LOGICAL_PATH: {error}"))?;
                additional_sources.push(CliSource {
                    package: PackageKey(package),
                    logical_path,
                    file,
                });
                continue;
            }
            positional.push(argument);
            continue;
        }
        if seen_format {
            return Err("--diagnostics may be specified at most once".into());
        }
        let Some(value) = arguments.next() else {
            return Err("--diagnostics requires `text` or `json`".into());
        };
        format = match value.as_str() {
            "text" => DiagnosticFormat::Text,
            "json" => DiagnosticFormat::Json,
            _ => return Err("--diagnostics requires `text` or `json`".into()),
        };
        seen_format = true;
    }
    let runtime_manifest = match standard_library {
        Some(standard_library) => Some(RuntimeManifestInput {
            standard_library,
            selectors,
        }),
        None if selectors.is_empty() => None,
        None => return Err("--runtime-leaf requires --runtime-standard-library PACKAGE".into()),
    };
    Ok(CliOptions {
        diagnostic_format: format,
        runtime_manifest,
        root_package: root_package.unwrap_or_else(|| PackageKey("command@0.1.0".into())),
        additional_sources,
        positional,
    })
}

fn render_diagnostics(diagnostics: &[CompileDiagnostic], format: DiagnosticFormat) {
    for diagnostic in diagnostics {
        match format {
            DiagnosticFormat::Text => {
                for line in diagnostic.text_lines() {
                    eprintln!("{line}");
                }
            }
            DiagnosticFormat::Json => eprintln!("{}", diagnostic.to_json_line()),
        }
    }
}

fn verify_program(path: &str) -> ExitCode {
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) => {
            eprintln!("grc-stage0: cannot read {path}: {error}");
            return ExitCode::from(1);
        }
    };
    match decode_and_verify_program(&bytes) {
        Ok(program) => {
            println!("{}", program.fingerprint());
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("grc-stage0: program verification failed: {error:?}");
            ExitCode::from(1)
        }
    }
}

fn verify_bootstrap(
    earlier_program_path: &str,
    earlier_manifest_path: &str,
    later_program_path: &str,
    later_manifest_path: &str,
) -> ExitCode {
    let load_program = |path: &str| match fs::read(path) {
        Ok(bytes) => decode_and_verify_program(&bytes)
            .map_err(|error| format!("program verification failed: {error:?}")),
        Err(error) => Err(format!("cannot read {path}: {error}")),
    };
    let load_manifest = |path: &str| match fs::read(path) {
        Ok(bytes) => BootstrapManifest::decode(&bytes)
            .map_err(|error| format!("bootstrap manifest is invalid: {error:?}")),
        Err(error) => Err(format!("cannot read {path}: {error}")),
    };
    let earlier_program = match load_program(earlier_program_path) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("grc-stage0: {error}");
            return ExitCode::from(1);
        }
    };
    let earlier_manifest = match load_manifest(earlier_manifest_path) {
        Ok(manifest) => manifest,
        Err(error) => {
            eprintln!("grc-stage0: {error}");
            return ExitCode::from(1);
        }
    };
    let later_program = match load_program(later_program_path) {
        Ok(program) => program,
        Err(error) => {
            eprintln!("grc-stage0: {error}");
            return ExitCode::from(1);
        }
    };
    let later_manifest = match load_manifest(later_manifest_path) {
        Ok(manifest) => manifest,
        Err(error) => {
            eprintln!("grc-stage0: {error}");
            return ExitCode::from(1);
        }
    };
    if let Err(error) = earlier_manifest.validate_verified_artifact(&earlier_program) {
        eprintln!("grc-stage0: earlier bootstrap manifest does not match its program: {error:?}");
        return ExitCode::from(1);
    }
    if let Err(error) = later_manifest.validate_verified_artifact(&later_program) {
        eprintln!("grc-stage0: later bootstrap manifest does not match its program: {error:?}");
        return ExitCode::from(1);
    }
    if let Err(error) = earlier_manifest.compare_convergence(&later_manifest) {
        eprintln!("grc-stage0: bootstrap convergence failed: {error:?}");
        return ExitCode::from(1);
    }
    println!("{}", later_program.fingerprint());
    ExitCode::SUCCESS
}

fn usage() {
    eprintln!("usage: grc-stage0 [--diagnostics text|json] [RUNTIME] <check|run> FILE");
    eprintln!("       grc-stage0 [--diagnostics text|json] [RUNTIME] emit-vm SOURCE OUTPUT");
    eprintln!(
        "       grc-stage0 [--diagnostics text|json] [RUNTIME] emit-bootstrap-vm SOURCE OUTPUT MANIFEST"
    );
    eprintln!("       grc-stage0 [--diagnostics text|json] verify-vm PROGRAM");
    eprintln!(
        "       grc-stage0 [--diagnostics text|json] verify-bootstrap EARLIER_PROGRAM EARLIER_MANIFEST LATER_PROGRAM LATER_MANIFEST"
    );
    eprintln!("RUNTIME: --runtime-standard-library PACKAGE");
    eprintln!("         --runtime-leaf ROLE MODULE NAME  (repeatable)");
    eprintln!("SOURCES: --root-package PACKAGE");
    eprintln!("         --source PACKAGE LOGICAL_PATH FILE  (repeatable)");
}
