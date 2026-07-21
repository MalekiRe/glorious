use std::{env, path::PathBuf, process::ExitCode};

use grandiose::{eval::SystemHost, run_source};

fn main() -> ExitCode {
    let mut cli: Vec<String> = env::args().skip(1).collect();
    if cli.first().map(String::as_str) == Some("run") {
        cli.remove(0);
    }
    let Some(file) = cli.first().cloned() else {
        eprintln!("usage: grandiose [run] <program.gr> [-- <arguments>...]");
        return ExitCode::from(2);
    };
    cli.remove(0);
    if cli.first().map(String::as_str) == Some("--") {
        cli.remove(0);
    }
    let path = PathBuf::from(&file);
    let source = match std::fs::read_to_string(&path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("error: could not read {}: {error}", path.display());
            return ExitCode::FAILURE;
        }
    };
    let mut host = SystemHost::default();
    match run_source(&path.display().to_string(), &source, cli, &mut host) {
        Ok(_) => ExitCode::SUCCESS,
        Err(diagnostics) => {
            for diagnostic in diagnostics {
                let _ = diagnostic
                    .with_source(path.display().to_string())
                    .write(&source, std::io::stderr());
            }
            ExitCode::FAILURE
        }
    }
}
