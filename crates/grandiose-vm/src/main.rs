mod supervisor;

use std::{
    env,
    ffi::OsString,
    fmt, fs,
    path::{Path, PathBuf},
    process::ExitCode,
    time::Duration,
};

use grandiose_vm::{
    Artifact, DecodeError, HostLinkError, RuntimeError, RuntimeFaultCategory, SystemHost, Value,
    VerifyError, Vm, verify,
};
use supervisor::{SupervisorError, SupervisorLimits, WorkerTermination, run_worker};

const USAGE: &str = "usage:\n  grvm verify FILE\n  grvm run [--time-limit 120s] [--memory-limit 4096MiB] [--allow CAPABILITY]... FILE [-- args...]";
const DEFAULT_WALL_TIME: Duration = Duration::from_secs(120);
const DEFAULT_ADDRESS_SPACE_BYTES: u64 = 4096 * 1024 * 1024;

fn main() -> ExitCode {
    match parse(env::args_os().skip(1).collect()) {
        Ok(command) => ExitCode::from(dispatch(command)),
        Err(error) => {
            eprintln!("grvm: usage: {error}\n{USAGE}");
            ExitCode::from(2)
        }
    }
}

#[derive(Debug, Eq, PartialEq)]
enum Cli {
    Verify(PathBuf),
    Run {
        file: PathBuf,
        args: Vec<OsString>,
        grants: Vec<String>,
        limits: SupervisorLimits,
    },
    Worker {
        file: PathBuf,
        args: Vec<OsString>,
        grants: Vec<String>,
    },
}

fn parse(mut args: Vec<OsString>) -> Result<Cli, String> {
    if args.is_empty() {
        return Err("missing command".into());
    }
    let command = args.remove(0);
    match command.to_str() {
        Some("verify") => {
            if args.len() != 1 {
                return Err("verify expects exactly one bytecode file".into());
            }
            Ok(Cli::Verify(PathBuf::from(args.remove(0))))
        }
        Some("run") => parse_run(args),
        Some("__worker") => parse_worker(args),
        Some(command) => Err(format!("unknown command `{command}`")),
        None => Err("command is not valid UTF-8".into()),
    }
}

fn parse_run(args: Vec<OsString>) -> Result<Cli, String> {
    let mut it = args.into_iter();
    let mut wall_time = Some(DEFAULT_WALL_TIME);
    let mut address_space_bytes = Some(DEFAULT_ADDRESS_SPACE_BYTES);
    let mut saw_time_limit = false;
    let mut saw_memory_limit = false;
    let mut grants = Vec::new();
    let file = loop {
        let arg = it.next().ok_or("run requires a bytecode file")?;
        match arg.to_str() {
            Some("--time-limit") => {
                if saw_time_limit {
                    return Err("--time-limit may only be specified once".into());
                }
                saw_time_limit = true;
                let seconds = positive_quantity(it.next(), "--time-limit", "s")?;
                wall_time = Some(Duration::from_secs(seconds));
            }
            Some("--memory-limit") => {
                if saw_memory_limit {
                    return Err("--memory-limit may only be specified once".into());
                }
                saw_memory_limit = true;
                let mib = positive_quantity(it.next(), "--memory-limit", "MiB")?;
                address_space_bytes = Some(
                    mib.checked_mul(1024 * 1024)
                        .ok_or("--memory-limit is too large")?,
                );
            }
            Some("--allow") => {
                let grant = capability_grant(it.next(), "--allow")?;
                insert_grant(&mut grants, grant)?;
            }
            Some(option) if option.starts_with('-') => {
                return Err(format!("unknown run option `{option}`"));
            }
            _ => break PathBuf::from(arg),
        }
    };
    let rest: Vec<_> = it.collect();
    let args = trailing_args(rest)?;
    Ok(Cli::Run {
        file,
        args,
        grants,
        limits: SupervisorLimits::new(wall_time, address_space_bytes),
    })
}

fn parse_worker(args: Vec<OsString>) -> Result<Cli, String> {
    let mut it = args.into_iter();
    let mut grants = Vec::new();
    let file = loop {
        let arg = it.next().ok_or("__worker requires a bytecode file")?;
        match arg.to_str() {
            Some("--allow") => {
                let grant = capability_grant(it.next(), "--allow")?;
                insert_grant(&mut grants, grant)?;
            }
            Some(option) if option.starts_with('-') => {
                return Err(format!("unknown __worker option `{option}`"));
            }
            _ => break PathBuf::from(arg),
        }
    };
    let args = trailing_args(it.collect())?;
    Ok(Cli::Worker { file, args, grants })
}

fn capability_grant(value: Option<OsString>, option: &str) -> Result<String, String> {
    let value = value.ok_or_else(|| format!("{option} requires a capability"))?;
    let value = value
        .into_string()
        .map_err(|_| format!("{option} capability is not valid UTF-8"))?;
    if value.is_empty() {
        Err(format!("{option} capability must not be empty"))
    } else {
        Ok(value)
    }
}

fn insert_grant(grants: &mut Vec<String>, grant: String) -> Result<(), String> {
    if grants.contains(&grant) {
        return Err(format!("capability `{grant}` may only be granted once"));
    }
    grants.push(grant);
    Ok(())
}

fn positive_quantity(value: Option<OsString>, option: &str, unit: &str) -> Result<u64, String> {
    let value = value.ok_or_else(|| format!("{option} requires a value ending in `{unit}`"))?;
    let text = value
        .to_str()
        .ok_or_else(|| format!("{option} value is not valid UTF-8"))?;
    let digits = text
        .strip_suffix(unit)
        .ok_or_else(|| format!("invalid {option} value `{text}`; expected a `{unit}` suffix"))?;
    let number = digits
        .parse::<u64>()
        .map_err(|_| format!("invalid {option} value `{text}`"))?;
    if number == 0 {
        Err(format!("{option} must be nonzero"))
    } else {
        Ok(number)
    }
}

fn trailing_args(mut args: Vec<OsString>) -> Result<Vec<OsString>, String> {
    if args.is_empty() {
        return Ok(args);
    }
    if args.remove(0) != "--" {
        return Err("program arguments must follow `--`".into());
    }
    Ok(args)
}

fn dispatch(command: Cli) -> u8 {
    match command {
        Cli::Verify(file) => report(verify_file(&file)),
        Cli::Worker { file, args, grants } => report(run_file(&file, args, grants)),
        Cli::Run {
            file,
            args,
            grants,
            limits,
        } => supervise(file, args, grants, limits),
    }
}

fn supervise(
    file: PathBuf,
    args: Vec<OsString>,
    grants: Vec<String>,
    limits: SupervisorLimits,
) -> u8 {
    let exe = match env::current_exe() {
        Ok(exe) => exe,
        Err(error) => return report(Err(AppError::SupervisorExecutable(error))),
    };
    let mut worker_args = vec![OsString::from("__worker")];
    for grant in grants {
        worker_args.push(OsString::from("--allow"));
        worker_args.push(grant.into());
    }
    worker_args.push(file.into_os_string());
    if !args.is_empty() {
        worker_args.push(OsString::from("--"));
        worker_args.extend(args);
    }
    match run_worker(exe.as_os_str(), worker_args, limits) {
        Ok(outcome) => match outcome.termination {
            WorkerTermination::Exited { code } => code as u8,
            WorkerTermination::InternalSignal { signal, .. } => {
                eprintln!("grvm: internal: worker terminated unexpectedly by signal {signal}");
                126
            }
            WorkerTermination::TimedOut => {
                eprintln!("grvm: timeout: worker exceeded its wall-time limit");
                124
            }
        },
        Err(error) => report(Err(AppError::Supervisor(error))),
    }
}

fn verify_file(path: &Path) -> Result<u8, AppError> {
    verify(load(path)?).map_err(AppError::Verify)?;
    Ok(0)
}

fn run_file(path: &Path, args: Vec<OsString>, grants: Vec<String>) -> Result<u8, AppError> {
    let artifact = load(path)?;
    let entry = artifact.entry_function.ok_or(AppError::MissingEntry)?;
    let vm = Vm::with_host(
        verify(artifact).map_err(AppError::Verify)?,
        grants,
        SystemHost::new(args),
    )
    .map_err(AppError::HostLink)?;
    match vm.run(entry, vec![]).map_err(AppError::Runtime)? {
        Value::Unit => Ok(0),
        value => Err(AppError::InvalidResult(value)),
    }
}

fn load(path: &Path) -> Result<Artifact, AppError> {
    let bytes = fs::read(path).map_err(|source| AppError::Read {
        path: path.to_owned(),
        source,
    })?;
    Artifact::decode(&bytes).map_err(AppError::Decode)
}

fn report(result: Result<u8, AppError>) -> u8 {
    match result {
        Ok(code) => code,
        Err(error) => {
            eprintln!("grvm: {}: {error}", error.kind());
            1
        }
    }
}

#[derive(Debug)]
enum AppError {
    Read {
        path: PathBuf,
        source: std::io::Error,
    },
    Decode(DecodeError),
    Verify(VerifyError),
    Runtime(RuntimeError),
    HostLink(HostLinkError),
    MissingEntry,
    InvalidResult(Value),
    SupervisorExecutable(std::io::Error),
    Supervisor(SupervisorError),
}

impl AppError {
    fn kind(&self) -> &'static str {
        match self {
            Self::Read { .. } => "input",
            Self::Decode(
                DecodeError::UnsupportedMajor(_)
                | DecodeError::UnsupportedFeatures { .. }
                | DecodeError::UnknownCriticalSection(_)
                | DecodeError::UnsupportedType(_),
            ) => "compatibility",
            // Unknown instructions cannot be retained in a decoded Artifact,
            // but G1 classifies their rejection as verification rather than a
            // compatibility failure.
            Self::Decode(
                DecodeError::UnsupportedOpcode { .. } | DecodeError::UnsupportedPrimitive(_),
            ) => "verify",
            Self::Decode(_) => "malformed",
            Self::Verify(_) => "verify",
            Self::Runtime(error) => match error.category() {
                RuntimeFaultCategory::Verification => "verification",
                RuntimeFaultCategory::UnhandledEffect => "unhandled-effect",
                RuntimeFaultCategory::PrimitiveTrap => "primitive-trap",
                RuntimeFaultCategory::HostFault => "host-fault",
                RuntimeFaultCategory::ExplicitAbort => "explicit-abort",
                RuntimeFaultCategory::Internal => "internal",
            },
            Self::HostLink(_) => "host-link",
            Self::MissingEntry => "entry",
            Self::InvalidResult(_) => "result",
            Self::SupervisorExecutable(_) | Self::Supervisor(_) => "supervisor",
        }
    }
}

impl fmt::Display for AppError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Read { path, source } => write!(f, "could not read {}: {source}", path.display()),
            Self::Decode(error) => error.fmt(f),
            Self::Verify(error) => error.fmt(f),
            Self::Runtime(error) => error.fmt(f),
            Self::HostLink(error) => error.fmt(f),
            Self::MissingEntry => f.write_str("artifact is a library and has no entry function"),
            Self::InvalidResult(value) => write!(
                f,
                "entry function returned {value:?}; generation-1 executable entries must return unit"
            ),
            Self::SupervisorExecutable(error) => {
                write!(f, "could not locate the grvm executable: {error}")
            }
            Self::Supervisor(error) => error.fmt(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn strings(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }

    #[test]
    fn unknown_instruction_ids_are_verification_failures() {
        assert_eq!(
            AppError::Decode(DecodeError::UnsupportedOpcode {
                at: 0,
                opcode: 0x7ff,
            })
            .kind(),
            "verify"
        );
        assert_eq!(
            AppError::Decode(DecodeError::UnsupportedPrimitive(0xffff)).kind(),
            "verify"
        );
    }

    #[test]
    fn parses_verify() {
        assert_eq!(
            parse(strings(&["verify", "program.grbc"])),
            Ok(Cli::Verify("program.grbc".into()))
        );
    }

    #[test]
    fn parses_limited_run_and_program_args() {
        assert_eq!(
            parse(strings(&[
                "run",
                "--time-limit",
                "120s",
                "--memory-limit",
                "4096MiB",
                "program.grbc",
                "--",
                "one",
                "two",
            ])),
            Ok(Cli::Run {
                file: "program.grbc".into(),
                args: strings(&["one", "two"]),
                grants: vec![],
                limits: SupervisorLimits::new(
                    Some(Duration::from_secs(120)),
                    Some(4096 * 1024 * 1024),
                ),
            })
        );
    }

    #[test]
    fn run_uses_normative_supervisor_defaults() {
        assert_eq!(
            parse(strings(&["run", "program.grbc"])),
            Ok(Cli::Run {
                file: "program.grbc".into(),
                args: vec![],
                grants: vec![],
                limits: SupervisorLimits::new(
                    Some(DEFAULT_WALL_TIME),
                    Some(DEFAULT_ADDRESS_SPACE_BYTES),
                ),
            })
        );
    }

    #[test]
    fn parses_repeated_capability_grants_before_the_file() {
        assert_eq!(
            parse(strings(&[
                "run",
                "--allow",
                "process.args",
                "--time-limit",
                "1s",
                "--allow",
                "fs.read",
                "program.grbc",
            ])),
            Ok(Cli::Run {
                file: "program.grbc".into(),
                args: vec![],
                grants: vec!["process.args".into(), "fs.read".into()],
                limits: SupervisorLimits::new(
                    Some(Duration::from_secs(1)),
                    Some(DEFAULT_ADDRESS_SPACE_BYTES),
                ),
            })
        );
    }

    #[test]
    fn rejects_missing_empty_and_duplicate_capability_grants() {
        assert_eq!(
            parse(strings(&["run", "--allow"])),
            Err("--allow requires a capability".into())
        );
        assert_eq!(
            parse(strings(&["run", "--allow", "", "x"])),
            Err("--allow capability must not be empty".into())
        );
        assert_eq!(
            parse(strings(&[
                "run", "--allow", "fs.read", "--allow", "fs.read", "x",
            ])),
            Err("capability `fs.read` may only be granted once".into())
        );
    }

    #[test]
    fn rejects_zero_duplicate_and_unseparated_arguments() {
        assert!(parse(strings(&["run", "--time-limit", "0s", "x"])).is_err());
        assert!(
            parse(strings(&[
                "run",
                "--memory-limit",
                "1MiB",
                "--memory-limit",
                "2MiB",
                "x",
            ]))
            .is_err()
        );
        assert!(parse(strings(&["run", "x", "argument"])).is_err());
        assert!(parse(strings(&["run", "--time-limit", "1", "x"])).is_err());
        assert!(parse(strings(&["run", "--memory-limit", "1", "x"])).is_err());
    }

    #[test]
    fn parses_worker_without_accepting_limits() {
        assert_eq!(
            parse(strings(&["__worker", "x", "--", "arg"])),
            Ok(Cli::Worker {
                file: "x".into(),
                args: strings(&["arg"]),
                grants: vec![],
            })
        );
        assert!(parse(strings(&["__worker", "--time-limit", "1", "x"])).is_err());
    }

    #[test]
    fn worker_receives_capability_grants() {
        assert_eq!(
            parse(strings(&[
                "__worker",
                "--allow",
                "diagnostic",
                "--allow",
                "fs.write",
                "x",
            ])),
            Ok(Cli::Worker {
                file: "x".into(),
                args: vec![],
                grants: vec!["diagnostic".into(), "fs.write".into()],
            })
        );
        assert_eq!(
            parse(strings(&[
                "__worker",
                "--allow",
                "diagnostic",
                "--allow",
                "diagnostic",
                "x",
            ])),
            Err("capability `diagnostic` may only be granted once".into())
        );
    }
}
