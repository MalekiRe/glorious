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
    MemoryLimit,
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
    let mut memory_reporter = MemoryReporter::new().map_err(SupervisorError::Spawn)?;
    let mut command = Command::new(exe);
    command.args(args);
    if let Some(write_fd) = memory_reporter.write_fd() {
        command.env(MEMORY_REPORT_FD_ENV, write_fd.to_string());
    }
    let child_read_fd = memory_reporter.read_fd;
    let child_write_fd = memory_reporter.write_fd;

    // Only async-signal-safe libc calls are made between fork and exec.
    unsafe {
        command.pre_exec(move || {
            MemoryReporter::prepare_child_fds(child_read_fd, child_write_fd)?;
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
    memory_reporter.prepare_parent();
    let termination = match limits.wall_time {
        None => classify(wait_or_terminate(&mut child)?, memory_reporter.reported()),
        Some(timeout) => wait_until(&mut child, started, timeout, &memory_reporter)?,
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
    memory_reporter: &MemoryReporter,
) -> Result<WorkerTermination, SupervisorError> {
    const POLL: Duration = Duration::from_millis(5);
    loop {
        let status = match child.try_wait() {
            Ok(status) => status,
            Err(error) => return Err(terminate_after_wait_error(child, error)),
        };
        if let Some(status) = status {
            return Ok(classify(status, memory_reporter.reported()));
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

fn classify(status: ExitStatus, memory_limit_reported: bool) -> WorkerTermination {
    if memory_limit_reported {
        return WorkerTermination::MemoryLimit;
    }
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

pub const MEMORY_REPORT_FD_ENV: &str = "GRANDIOSE_SUPERVISOR_MEMORY_FD";

struct MemoryReporter {
    read_fd: Option<i32>,
    write_fd: Option<i32>,
}

impl MemoryReporter {
    fn new() -> io::Result<Self> {
        #[cfg(target_os = "linux")]
        {
            let mut descriptors = [-1; 2];
            if unsafe { pipe2(descriptors.as_mut_ptr(), O_CLOEXEC | O_NONBLOCK) } != 0 {
                return Err(io::Error::last_os_error());
            }
            Ok(Self {
                read_fd: Some(descriptors[0]),
                write_fd: Some(descriptors[1]),
            })
        }
        #[cfg(not(target_os = "linux"))]
        {
            Ok(Self {
                read_fd: None,
                write_fd: None,
            })
        }
    }

    fn write_fd(&self) -> Option<i32> {
        self.write_fd
    }

    fn prepare_child_fds(read_fd: Option<i32>, write_fd: Option<i32>) -> io::Result<()> {
        if let Some(read_fd) = read_fd {
            unsafe { close(read_fd) };
        }
        if let Some(write_fd) = write_fd
            && unsafe { fcntl(write_fd, F_SETFD, 0) } != 0
        {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }

    fn prepare_parent(&mut self) {
        if let Some(write_fd) = self.write_fd.take() {
            unsafe { close(write_fd) };
        }
    }

    fn reported(&self) -> bool {
        let Some(read_fd) = self.read_fd else {
            return false;
        };
        let mut marker = 0u8;
        unsafe { read(read_fd, (&raw mut marker).cast(), 1) == 1 }
    }
}

impl Drop for MemoryReporter {
    fn drop(&mut self) {
        if let Some(read_fd) = self.read_fd.take() {
            unsafe { close(read_fd) };
        }
        if let Some(write_fd) = self.write_fd.take() {
            unsafe { close(write_fd) };
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
const F_SETFD: i32 = 2;
const O_NONBLOCK: i32 = 0o4000;
const O_CLOEXEC: i32 = 0o2000000;

unsafe extern "C" {
    fn setrlimit(resource: i32, limit: *const RLimit) -> i32;
    fn setpgid(pid: i32, pgid: i32) -> i32;
    fn kill(pid: i32, signal: i32) -> i32;
    fn pipe2(descriptors: *mut i32, flags: i32) -> i32;
    fn fcntl(descriptor: i32, command: i32, argument: i32) -> i32;
    fn close(descriptor: i32) -> i32;
    fn read(descriptor: i32, buffer: *mut std::ffi::c_void, count: usize) -> isize;
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

    #[cfg(target_os = "linux")]
    #[test]
    fn explicit_allocator_marker_distinguishes_memory_limit_from_same_signal() {
        let memory = run_worker(
            "/bin/sh",
            [
                "-c",
                "eval \"printf M >&$GRANDIOSE_SUPERVISOR_MEMORY_FD\"; kill -ABRT $$",
            ],
            SupervisorLimits::new(None, Some(4096 * 1024 * 1024)),
        )
        .unwrap();
        assert_eq!(memory.termination, WorkerTermination::MemoryLimit);

        let internal = run_worker(
            "/bin/sh",
            ["-c", "kill -ABRT $$"],
            SupervisorLimits::new(None, Some(4096 * 1024 * 1024)),
        )
        .unwrap();
        assert!(matches!(
            internal.termination,
            WorkerTermination::InternalSignal { signal: 6, .. }
        ));
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

    #[cfg(target_os = "linux")]
    #[test]
    fn timeout_kills_the_entire_descendant_process_group() {
        let directory = tempfile::tempdir().unwrap();
        let child_pid = directory.path().join("child.pid");
        let args = vec![
            std::ffi::OsString::from("-c"),
            std::ffi::OsString::from("sleep 30 & echo \"$!\" > \"$1\"; wait"),
            std::ffi::OsString::from("grandiose-supervisor-test"),
            child_pid.clone().into_os_string(),
        ];
        let outcome = run_worker(
            "/bin/sh",
            args,
            SupervisorLimits::new(Some(Duration::from_millis(200)), None),
        )
        .unwrap();
        assert_eq!(outcome.termination, WorkerTermination::TimedOut);

        let pid = std::fs::read_to_string(&child_pid)
            .expect("the worker must start its descendant before the timeout")
            .trim()
            .parse::<i32>()
            .unwrap();
        let reaped = (0..100).any(|_| {
            if unsafe { kill(pid, 0) } != 0
                && io::Error::last_os_error().raw_os_error() == Some(ESRCH)
            {
                true
            } else {
                thread::sleep(Duration::from_millis(10));
                false
            }
        });
        assert!(reaped, "descendant {pid} survived the worker-group timeout");
    }
}
