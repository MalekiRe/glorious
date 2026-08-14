//! Thin host adapter for the independent stage-zero compiler service.

use std::{collections::BTreeMap, env, fs, process::ExitCode};

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompileDiagnostic, CompilerBuildIdentity, Digest,
    LogicalPath, PackageKey, PrimitiveRole, PrimitiveSelector, RuntimeManifestInput, SourceInput,
    StageZeroCompiler, decode_and_verify_program,
};

#[derive(Clone, Copy, Eq, PartialEq)]
enum DiagnosticFormat {
    Text,
    Json,
}

fn main() -> ExitCode {
    let (diagnostic_format, runtime_manifest, arguments) =
        match split_cli_options(env::args().skip(1)) {
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
    let Some(path) = arguments.next() else {
        eprintln!("grc-stage0: {command} requires a source FILE");
        return ExitCode::from(2);
    };
    let output = if command == "emit-vm" {
        let Some(output) = arguments.next() else {
            eprintln!("grc-stage0: emit-vm requires an OUTPUT file");
            return ExitCode::from(2);
        };
        Some(output)
    } else {
        None
    };
    if arguments.next().is_some() || !matches!(command.as_str(), "check" | "run" | "emit-vm") {
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
    let package = PackageKey("command@0.1.0".into());
    let request = CompilationRequest {
        build: CompilerBuildIdentity::stage0(Digest::of_bytes(b"grandiose-stage0-command-v6")),
        mode: if matches!(command.as_str(), "run" | "emit-vm") {
            CompilationMode::Build
        } else {
            CompilationMode::Check
        },
        root_package: package.clone(),
        // The CLI is a host adapter. It maps its one explicit file input into
        // the compiler's logical source universe; semantic phases see no path.
        sources: vec![SourceInput::new(
            package,
            LogicalPath::parse("src/main.glorious").expect("static logical path is valid"),
            bytes,
        )],
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
            }
            ExitCode::SUCCESS
        }
        Err(error) => {
            render_diagnostics(&error.diagnostics(), diagnostic_format);
            ExitCode::from(1)
        }
    }
}

fn split_cli_options(
    arguments: impl IntoIterator<Item = String>,
) -> Result<(DiagnosticFormat, Option<RuntimeManifestInput>, Vec<String>), String> {
    let mut format = DiagnosticFormat::Text;
    let mut seen_format = false;
    let mut standard_library = None;
    let mut selectors = Vec::new();
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
    Ok((format, runtime_manifest, positional))
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

fn usage() {
    eprintln!("usage: grc-stage0 [--diagnostics text|json] [RUNTIME] <check|run> FILE");
    eprintln!("       grc-stage0 [--diagnostics text|json] [RUNTIME] emit-vm SOURCE OUTPUT");
    eprintln!("       grc-stage0 [--diagnostics text|json] verify-vm PROGRAM");
    eprintln!("RUNTIME: --runtime-standard-library PACKAGE");
    eprintln!("         --runtime-leaf ROLE MODULE NAME  (repeatable)");
}
