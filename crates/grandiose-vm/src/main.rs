mod supervisor;

use std::{
    alloc::{GlobalAlloc, Layout, System},
    env,
    ffi::OsString,
    fmt, fs,
    path::{Path, PathBuf},
    process::ExitCode,
    sync::atomic::{AtomicI32, Ordering},
    time::Duration,
};

use grandiose_vm::{
    DecodeError, HostLinkError, LoadError, RuntimeError, RuntimeFaultCategory, SystemHost, Value,
    VerifiedArtifact, VerifyError, Vm, load_verified,
};
use supervisor::{
    MEMORY_REPORT_FD_ENV, SupervisorError, SupervisorLimits, WorkerTermination, run_worker,
};

const USAGE: &str = "usage:\n  grvm --capabilities\n  grvm verify FILE\n  grvm run [--seed-identity ID] [--time-limit 120s] [--memory-limit 4096MiB] [--allow CAPABILITY]... FILE [-- args...]";
const DEFAULT_WALL_TIME: Duration = Duration::from_secs(120);
const DEFAULT_ADDRESS_SPACE_BYTES: u64 = 4096 * 1024 * 1024;

struct ReportingAllocator;

#[global_allocator]
static ALLOCATOR: ReportingAllocator = ReportingAllocator;
static MEMORY_REPORT_FD: AtomicI32 = AtomicI32::new(-1);

unsafe impl GlobalAlloc for ReportingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc(layout) };
        if pointer.is_null() {
            report_memory_limit();
        }
        pointer
    }

    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let pointer = unsafe { System.alloc_zeroed(layout) };
        if pointer.is_null() {
            report_memory_limit();
        }
        pointer
    }

    unsafe fn dealloc(&self, pointer: *mut u8, layout: Layout) {
        unsafe { System.dealloc(pointer, layout) };
    }

    unsafe fn realloc(&self, pointer: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let pointer = unsafe { System.realloc(pointer, layout, size) };
        if pointer.is_null() {
            report_memory_limit();
        }
        pointer
    }
}

fn configure_memory_reporting() {
    let Some(descriptor) = env::var_os(MEMORY_REPORT_FD_ENV)
        .and_then(|value| value.to_str().and_then(|value| value.parse::<i32>().ok()))
    else {
        return;
    };
    if descriptor >= 0 {
        MEMORY_REPORT_FD.store(descriptor, Ordering::Relaxed);
        unsafe { fcntl(descriptor, F_SETFD, FD_CLOEXEC) };
    }
}

fn report_memory_limit() {
    let descriptor = memory_report_descriptor();
    if descriptor >= 0 {
        let marker = b'M';
        unsafe {
            write(
                descriptor,
                (&raw const marker).cast::<std::ffi::c_void>(),
                1,
            );
        }
    }
}

/// Resolve the inherited reporter without allocating. The global allocator can
/// fail before `main` has had a chance to call `configure_memory_reporting`,
/// while the worker is already under its address-space limit. `getenv` and the
/// bounded decimal scan keep that startup path observable without recursively
/// entering the allocator.
fn memory_report_descriptor() -> i32 {
    let cached = MEMORY_REPORT_FD.load(Ordering::Relaxed);
    if cached != -1 {
        return cached;
    }
    let descriptor = unsafe {
        parse_memory_report_descriptor(getenv(c"GRANDIOSE_SUPERVISOR_MEMORY_FD".as_ptr()))
    };
    MEMORY_REPORT_FD.store(descriptor, Ordering::Relaxed);
    descriptor
}

unsafe fn parse_memory_report_descriptor(mut value: *const std::ffi::c_char) -> i32 {
    if value.is_null() {
        return -2;
    }
    let mut result = 0_u32;
    let mut digits = 0_u8;
    loop {
        let byte = unsafe { *value }.cast_unsigned();
        if byte == 0 {
            break;
        }
        if !byte.is_ascii_digit() || digits == 10 {
            return -2;
        }
        result = match result
            .checked_mul(10)
            .and_then(|result| result.checked_add(u32::from(byte - b'0')))
        {
            Some(result) => result,
            None => return -2,
        };
        digits += 1;
        value = unsafe { value.add(1) };
    }
    if digits == 0 || result > i32::MAX as u32 {
        -2
    } else {
        result as i32
    }
}

fn main() -> ExitCode {
    configure_memory_reporting();
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
    Capabilities,
    Verify(PathBuf),
    Run {
        file: PathBuf,
        args: Vec<OsString>,
        grants: Vec<String>,
        limits: SupervisorLimits,
        seed_identity: Option<String>,
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
        Some("--capabilities") => {
            if !args.is_empty() {
                return Err("--capabilities does not accept other arguments".into());
            }
            Ok(Cli::Capabilities)
        }
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
    let mut seed_identity = None;
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
            Some("--seed-identity") => {
                let identity = it
                    .next()
                    .ok_or("--seed-identity requires an identity")?
                    .into_string()
                    .map_err(|_| "--seed-identity must be valid UTF-8")?;
                if identity.is_empty() {
                    return Err("--seed-identity must not be empty".into());
                }
                if seed_identity.replace(identity).is_some() {
                    return Err("--seed-identity may only be specified once".into());
                }
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
        seed_identity,
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
        Cli::Capabilities => {
            let accepted_seed_identities = grandiose_vm::ACCEPTED_SEED_IDENTITIES
                .iter()
                .map(|identity| format!("\"{identity}\""))
                .collect::<Vec<_>>()
                .join(",");
            println!(
                "{{\"grvm\":\"{}\",\"contract\":1,\"contract-min\":1,\"contract-max\":1,\"artifact-major\":1,\"artifact-minor-min\":0,\"artifact-minor-max\":0,\"seed-identity-version\":{},\"accepted-seed-identities\":[{}]}}",
                env!("CARGO_PKG_VERSION"),
                grandiose_vm::SEED_IDENTITY_VERSION,
                accepted_seed_identities,
            );
            0
        }
        Cli::Verify(file) => report(verify_file(&file)),
        Cli::Worker { file, args, grants } => report(run_file(&file, args, grants)),
        Cli::Run {
            file,
            args,
            grants,
            limits,
            seed_identity,
        } => {
            if let Some(identity) = seed_identity
                && !grandiose_vm::ACCEPTED_SEED_IDENTITIES.contains(&identity.as_str())
            {
                eprintln!("grvm: seed-identity: incompatible released-seed identity `{identity}`");
                return 1;
            }
            supervise(file, args, grants, limits)
        }
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
            WorkerTermination::MemoryLimit => {
                eprintln!("grvm: memory-limit: worker exceeded its allocation or memory limit");
                125
            }
        },
        Err(error) => report(Err(AppError::Supervisor(error))),
    }
}

fn verify_file(path: &Path) -> Result<u8, AppError> {
    load(path)?;
    Ok(0)
}

fn run_file(path: &Path, args: Vec<OsString>, grants: Vec<String>) -> Result<u8, AppError> {
    let artifact = load(path)?;
    let entry = artifact.entry_function().ok_or(AppError::MissingEntry)?;
    let vm = Vm::with_host(artifact, grants, SystemHost::new(args)).map_err(AppError::HostLink)?;
    match vm.run(entry, vec![]).map_err(AppError::Runtime)? {
        Value::Unit => Ok(0),
        value => Err(AppError::InvalidResult(value)),
    }
}

fn load(path: &Path) -> Result<VerifiedArtifact, AppError> {
    let bytes = fs::read(path).map_err(|source| AppError::Read {
        path: path.to_owned(),
        source,
    })?;
    load_verified(&bytes).map_err(|error| match error {
        LoadError::Decode(error) => AppError::Decode(error),
        LoadError::Verify(error) => AppError::Verify(error),
    })
}

fn report(result: Result<u8, AppError>) -> u8 {
    match result {
        Ok(code) => code,
        Err(error) => {
            if matches!(
                error,
                AppError::Runtime(ref runtime)
                    if runtime.category() == RuntimeFaultCategory::MemoryLimit
            ) {
                report_memory_limit();
            }
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
                RuntimeFaultCategory::MemoryLimit => "memory-limit",
                RuntimeFaultCategory::Internal => "internal",
            },
            Self::HostLink(_) => "host-link",
            Self::MissingEntry => "entry",
            Self::InvalidResult(_) => "result",
            Self::SupervisorExecutable(_) | Self::Supervisor(_) => "supervisor",
        }
    }
}

const F_SETFD: i32 = 2;
const FD_CLOEXEC: i32 = 1;

unsafe extern "C" {
    fn fcntl(descriptor: i32, command: i32, argument: i32) -> i32;
    fn getenv(name: *const std::ffi::c_char) -> *mut std::ffi::c_char;
    fn write(descriptor: i32, buffer: *const std::ffi::c_void, count: usize) -> isize;
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

    fn parsed_report_descriptor(value: &[u8]) -> i32 {
        assert_eq!(value.last(), Some(&0));
        unsafe { parse_memory_report_descriptor(value.as_ptr().cast()) }
    }

    #[test]
    fn allocation_report_descriptor_is_parsed_without_allocation() {
        assert_eq!(parsed_report_descriptor(b"0\0"), 0);
        assert_eq!(parsed_report_descriptor(b"198\0"), 198);
        assert_eq!(parsed_report_descriptor(b"2147483647\0"), i32::MAX);
        for invalid in [
            b"\0".as_slice(),
            b"-1\0",
            b"12x\0",
            b"2147483648\0",
            b"00000000001\0",
        ] {
            assert_eq!(parsed_report_descriptor(invalid), -2, "{invalid:?}");
        }
        assert_eq!(
            unsafe { parse_memory_report_descriptor(std::ptr::null()) },
            -2
        );
    }

    fn strings(values: &[&str]) -> Vec<OsString> {
        values.iter().map(OsString::from).collect()
    }

    #[test]
    fn capabilities_is_a_standalone_machine_command() {
        assert_eq!(parse(strings(&["--capabilities"])), Ok(Cli::Capabilities));
        assert!(parse(strings(&["--capabilities", "extra"])).is_err());
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
                seed_identity: None,
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
                seed_identity: None,
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
                seed_identity: None,
                limits: SupervisorLimits::new(
                    Some(Duration::from_secs(1)),
                    Some(DEFAULT_ADDRESS_SPACE_BYTES),
                ),
            })
        );
    }

    #[test]
    fn parses_and_validates_seed_identity_option() {
        assert_eq!(
            parse(strings(&[
                "run",
                "--seed-identity",
                grandiose_vm::RELEASED_SEED_IDENTITY,
                "program.grbc",
            ])),
            Ok(Cli::Run {
                file: "program.grbc".into(),
                args: vec![],
                grants: vec![],
                seed_identity: Some(grandiose_vm::RELEASED_SEED_IDENTITY.into()),
                limits: SupervisorLimits::new(
                    Some(DEFAULT_WALL_TIME),
                    Some(DEFAULT_ADDRESS_SPACE_BYTES),
                ),
            })
        );
        assert_eq!(
            parse(strings(&["run", "--seed-identity"])),
            Err("--seed-identity requires an identity".into())
        );
        assert_eq!(
            parse(strings(&["run", "--seed-identity", "", "program.grbc"])),
            Err("--seed-identity must not be empty".into())
        );
        assert_eq!(
            parse(strings(&[
                "run",
                "--seed-identity",
                "first",
                "--seed-identity",
                "second",
                "program.grbc",
            ])),
            Err("--seed-identity may only be specified once".into())
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
