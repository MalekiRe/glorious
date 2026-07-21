use std::{env, process::ExitCode};

#[path = "../cli.rs"]
mod cli;

fn main() -> ExitCode {
    ExitCode::from(cli::execute(env::args_os().skip(1)))
}
