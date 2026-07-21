//! Small, Linux-oriented worker-process supervisor.
//!
//! The caller is responsible for adding its worker-mode argument and ensuring
//! that worker mode does not recursively invoke [`run_worker`]. Each worker is
//! placed in a fresh process group so a timeout also kills any children it
//! starts.

use std::{
    error::Error,
    ffi::OsStr,
    fmt, io,
    os::unix::{process::CommandExt, process::ExitStatusExt},
    process::{Child, Command, ExitStatus},
    thread,
    time::{Duration, Instant},
};

/// Operating-system limits applied to a worker.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct SupervisorLimits {
    /// Maximum elapsed wall-clock time. `None` means unlimited.
    pub wall_time: Option<Duration>,
    /// Maximum virtual address space in bytes. `None` means unlimited.
    pub address_space_bytes: Option<u64>,
}

impl SupervisorLimits {
    pub const fn new(wall_time: Option<Duration>, address_space_bytes: Option<u64>) -> Self {
        Self {
            wall_time,
            address_space_bytes,
        }
    }

    fn validate(self) -> Result<Self, SupervisorError> {
        if self.wall_time == Some(Duration::ZERO) {
            return Err(SupervisorError::InvalidLimit("wall time must be nonzero"));
        }
        if self.address_space_bytes == Some(0) {
            return Err(SupervisorError::InvalidLimit(
                "address-space limit must be nonzero",
            ));
        }
        if let Some(bytes) = self.address_space_bytes {
            usize::try_from(bytes).map_err(|_| {
                SupervisorError::InvalidLimit("address-space limit is too large for this host")
            })?;
        }
        Ok(self)
    }
}

/// Why a supervised worker stopped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WorkerTermination {
    Exited { code: i32 },
    InternalSignal { signal: i32, core_dumped: bool },
    TimedOut,
}

/// Completed worker result. Output streams are inherited from the supervisor.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct WorkerOutcome {
    pub termination: WorkerTermination,
    pub elapsed: Duration,
}

#[derive(Debug)]
pub enum SupervisorError {
    InvalidExecutable,
    InvalidLimit(&'static str),
    Spawn(io::Error),
    Wait(io::Error),
    Terminate(io::Error),
}

impl fmt::Display for SupervisorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidExecutable => f.write_str("worker executable must not be empty"),
            Self::InvalidLimit(reason) => write!(f, "invalid supervisor limit: {reason}"),
            Self::Spawn(error) => write!(f, "could not start worker: {error}"),
            Self::Wait(error) => write!(f, "could not wait for worker: {error}"),
            Self::Terminate(error) => write!(f, "could not terminate worker group: {error}"),
        }
    }
}

impl Error for SupervisorError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Spawn(error) | Self::Wait(error) | Self::Terminate(error) => Some(error),
            _ => None,
        }
    }
}

/// Relaunch `exe` as a supervised worker, inheriting stdio and environment.
///
/// On Linux, the address-space limit is installed after `fork` and before
/// `exec`. A wall timeout kills the fresh worker process group with `SIGKILL`.
pub fn run_worker<I, S>(
    exe: impl AsRef<OsStr>,
    args: I,
    limits: SupervisorLimits,
) -> Result<WorkerOutcome, SupervisorError>
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let exe = exe.as_ref();
    if exe.is_empty() {
        return Err(SupervisorError::InvalidExecutable);
    }
    let limits = limits.validate()?;
    let address_space = limits.address_space_bytes.map(|n| n as usize);
    let mut command = Command::new(exe);
    command.args(args);

    // Only async-signal-safe libc calls are made between fork and exec.
    unsafe {
        command.pre_exec(move || {
            if setpgid(0, 0) != 0 {
                return Err(io::Error::last_os_error());
            }
            if let Some(bytes) = address_space {
                let limit = RLimit {
                    current: bytes,
                    maximum: bytes,
                };
                if setrlimit(RLIMIT_AS, &limit) != 0 {
                    return Err(io::Error::last_os_error());
                }
            }
            Ok(())
        });
    }

    let started = Instant::now();
    let mut child = command.spawn().map_err(SupervisorError::Spawn)?;
    let termination = match limits.wall_time {
        None => classify(
            wait_or_terminate(&mut child)?,
            limits.address_space_bytes.is_some(),
        ),
        Some(timeout) => wait_until(
            &mut child,
            started,
            timeout,
            limits.address_space_bytes.is_some(),
        )?,
    };
    Ok(WorkerOutcome {
        termination,
        elapsed: started.elapsed(),
    })
}

fn wait_until(
    child: &mut Child,
    started: Instant,
    timeout: Duration,
    memory_limit_installed: bool,
) -> Result<WorkerTermination, SupervisorError> {
    const POLL: Duration = Duration::from_millis(5);
    loop {
        let status = match child.try_wait() {
            Ok(status) => status,
            Err(error) => return Err(terminate_after_wait_error(child, error)),
        };
        if let Some(status) = status {
            return Ok(classify(status, memory_limit_installed));
        }
        let elapsed = started.elapsed();
        if elapsed >= timeout {
            terminate_group(child)?;
            wait_or_terminate(child)?;
            return Ok(WorkerTermination::TimedOut);
        }
        thread::sleep(POLL.min(timeout - elapsed));
    }
}

fn wait_or_terminate(child: &mut Child) -> Result<ExitStatus, SupervisorError> {
    child
        .wait()
        .map_err(|error| terminate_after_wait_error(child, error))
}

fn terminate_after_wait_error(child: &mut Child, error: io::Error) -> SupervisorError {
    // Once spawn succeeds, no supervisor error may leave the worker running.
    // Preserve the original wait error after best-effort group termination and
    // reaping; there is no useful way to report both failures through this API.
    let _ = terminate_group(child);
    let _ = child.wait();
    SupervisorError::Wait(error)
}

fn classify(status: ExitStatus, _memory_limit_installed: bool) -> WorkerTermination {
    if let Some(signal) = status.signal() {
        // RLIMIT_AS does not say whether a later signal was caused by the
        // address-space ceiling. Treating every SIGABRT/SIGSEGV/SIGILL as a
        // memory limit would hide VM bugs. Primitive allocation preflights use
        // an explicit error path; ambiguous signals are Internal.
        WorkerTermination::InternalSignal {
            signal,
            core_dumped: status.core_dumped(),
        }
    } else {
        WorkerTermination::Exited {
            code: status.code().unwrap_or(1),
        }
    }
}

fn terminate_group(child: &mut Child) -> Result<(), SupervisorError> {
    let pid = child.id() as i32;
    // Negative pid addresses the process group created in pre_exec.
    if unsafe { kill(-pid, SIGKILL) } == 0 {
        return Ok(());
    }
    let error = io::Error::last_os_error();
    // ESRCH is a harmless exit racing the timeout. For other failures, make a
    // best effort to kill the direct child before returning the original error.
    if error.raw_os_error() == Some(ESRCH) {
        Ok(())
    } else {
        let _ = child.kill();
        let _ = child.wait();
        Err(SupervisorError::Terminate(error))
    }
}

#[repr(C)]
struct RLimit {
    current: usize,
    maximum: usize,
}

const RLIMIT_AS: i32 = 9;
const SIGKILL: i32 = 9;
const ESRCH: i32 = 3;

unsafe extern "C" {
    fn setrlimit(resource: i32, limit: *const RLimit) -> i32;
    fn setpgid(pid: i32, pgid: i32) -> i32;
    fn kill(pid: i32, signal: i32) -> i32;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_empty_executable() {
        assert!(matches!(
            run_worker("", std::iter::empty::<&str>(), SupervisorLimits::default()),
            Err(SupervisorError::InvalidExecutable)
        ));
    }

    #[test]
    fn rejects_zero_limits_before_spawning() {
        let zero_time = SupervisorLimits::new(Some(Duration::ZERO), None);
        assert!(matches!(
            run_worker("missing-worker", std::iter::empty::<&str>(), zero_time),
            Err(SupervisorError::InvalidLimit(_))
        ));

        let zero_space = SupervisorLimits::new(None, Some(0));
        assert!(matches!(
            run_worker("missing-worker", std::iter::empty::<&str>(), zero_space),
            Err(SupervisorError::InvalidLimit(_))
        ));
    }

    #[test]
    fn distinguishes_exit_and_signal() {
        let exited = run_worker("/bin/sh", ["-c", "exit 7"], SupervisorLimits::default()).unwrap();
        assert_eq!(exited.termination, WorkerTermination::Exited { code: 7 });

        let signaled = run_worker(
            "/bin/sh",
            ["-c", "kill -TERM $$"],
            SupervisorLimits::default(),
        )
        .unwrap();
        assert_eq!(
            signaled.termination,
            WorkerTermination::InternalSignal {
                signal: 15,
                core_dumped: false
            }
        );
    }

    #[test]
    fn does_not_hide_an_ambiguous_signal_as_a_memory_limit() {
        let outcome = run_worker(
            "/bin/sh",
            ["-c", "kill -TERM $$"],
            SupervisorLimits::new(None, Some(4096 * 1024 * 1024)),
        )
        .unwrap();
        assert_eq!(
            outcome.termination,
            WorkerTermination::InternalSignal {
                signal: 15,
                core_dumped: false
            }
        );
    }

    #[test]
    fn reports_wall_timeout() {
        let outcome = run_worker(
            "/bin/sh",
            ["-c", "while :; do :; done"],
            SupervisorLimits::new(Some(Duration::from_millis(20)), None),
        )
        .unwrap();
        assert_eq!(outcome.termination, WorkerTermination::TimedOut);
    }
}
