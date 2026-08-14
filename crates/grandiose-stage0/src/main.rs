//! Thin host adapter for the independent stage-zero compiler service.

use std::{collections::BTreeMap, env, fs, process::ExitCode};

use grandiose_stage0::{
    CompilationMode, CompilationRequest, CompilerBuildIdentity, Digest, LogicalPath, PackageKey,
    SourceInput, StageZeroCompiler, decode_and_verify_program,
};

fn main() -> ExitCode {
    let mut arguments = env::args().skip(1);
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
        runtime_manifest: None,
    };
    match StageZeroCompiler::new().compile(request) {
        Ok(outcome) => {
            for diagnostic in outcome.diagnostics {
                eprintln!("{}: {}", diagnostic.code, diagnostic.message);
            }
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
            for diagnostic in error.diagnostics() {
                eprintln!("{}: {}", diagnostic.code, diagnostic.message);
            }
            ExitCode::from(1)
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
    eprintln!("usage: grc-stage0 <check|run> FILE");
    eprintln!("       grc-stage0 emit-vm SOURCE OUTPUT");
    eprintln!("       grc-stage0 verify-vm PROGRAM");
}
