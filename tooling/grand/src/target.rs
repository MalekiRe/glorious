use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{Context, Result, bail};

/// A verified Grandiose bytecode artifact executed by the canonical VM.
pub struct Artifact {
    payload: PathBuf,
    vm: PathBuf,
    seed_identity: Option<String>,
}

impl Artifact {
    pub fn bytecode(payload: PathBuf, vm: PathBuf, seed_identity: Option<String>) -> Self {
        Self {
            payload,
            vm,
            seed_identity,
        }
    }

    pub fn path(&self) -> &Path {
        &self.payload
    }

    /// Execute bytecode with a 4 GiB address-space ceiling.
    pub fn execute(&self, arguments: &[String], capabilities: &[String]) -> Result<i32> {
        let mut command = Command::new(&self.vm);
        command.arg("run");
        if let Some(identity) = &self.seed_identity {
            command.args(["--seed-identity", identity]);
        }
        for capability in capabilities {
            command.args(["--allow", capability]);
        }
        command.arg(&self.payload);
        if !arguments.is_empty() {
            command.arg("--").args(arguments);
        }
        limit_address_space(&mut command, 4 << 30);
        let status = command
            .status()
            .with_context(|| format!("failed to launch {}", self.vm.display()))?;
        match status.code() {
            Some(code) => Ok(code),
            None => {
                #[cfg(unix)]
                {
                    use std::os::unix::process::ExitStatusExt;
                    if let Some(signal) = status.signal() {
                        let name = match signal {
                            libc::SIGSEGV => " (SIGSEGV — segmentation fault)",
                            libc::SIGABRT => " (SIGABRT)",
                            libc::SIGKILL => " (SIGKILL — possibly the 4 GiB memory ceiling)",
                            libc::SIGILL => " (SIGILL)",
                            libc::SIGBUS => " (SIGBUS)",
                            _ => "",
                        };
                        bail!(
                            "{} terminated by signal {signal}{name}",
                            self.payload.display()
                        );
                    }
                }
                bail!("{} terminated abnormally", self.payload.display())
            }
        }
    }
}

#[cfg(unix)]
fn limit_address_space(command: &mut Command, bytes: u64) {
    use std::os::unix::process::CommandExt;
    // SAFETY: setrlimit is async-signal-safe; nothing else runs in the child yet.
    unsafe {
        command.pre_exec(move || {
            let limit = libc::rlimit {
                rlim_cur: bytes,
                rlim_max: bytes,
            };
            if libc::setrlimit(libc::RLIMIT_AS, &limit) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            Ok(())
        });
    }
}

#[cfg(not(unix))]
fn limit_address_space(_command: &mut Command, _bytes: u64) {}
