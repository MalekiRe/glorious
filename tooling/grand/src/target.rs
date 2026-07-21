use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

use crate::util::run_command;

/// How a compiled `.ll` becomes something that runs.
///
/// `Interp` is the working path today: assemble to bitcode and execute under
/// `lli` with the dlopen'd C runtime. `Native` is where the toolchain is
/// headed: link a real executable with clang. Both implement the same
/// materialize/execute pair so the rest of grand is target-agnostic.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    /// Select the G1 VM for `.grbc`, otherwise the legacy LLVM interpreter.
    Auto,
    Vm,
    Interp,
    Native,
}

impl Target {
    pub fn parse(name: &str) -> Result<Target> {
        match name {
            "auto" => Ok(Target::Auto),
            "vm" => Ok(Target::Vm),
            "interp" => Ok(Target::Interp),
            "native" => Ok(Target::Native),
            other => {
                bail!("unknown target `{other}` (expected `auto`, `vm`, `interp`, or `native`)")
            }
        }
    }
}

pub struct Artifact {
    runner: Runner,
    /// VM: the `.grbc`; native: the executable; interp: the `.bc` file.
    payload: PathBuf,
}

enum Runner {
    Vm {
        executable: PathBuf,
        seed_identity: Option<String>,
    },
    Interp(PathBuf),
    Native,
}

/// Turn textual IR into a runnable artifact inside `out_dir`.
pub fn materialize(
    target: Target,
    ir: &Path,
    runtime_c: &Path,
    out_dir: &Path,
    stem: &str,
) -> Result<Artifact> {
    std::fs::create_dir_all(out_dir)?;
    match target {
        Target::Auto | Target::Interp => {
            let bitcode = out_dir.join(format!("{stem}.bc"));
            if needs_rebuild(&bitcode, ir)? {
                let mut llvm_as = Command::new("llvm-as");
                llvm_as.arg(ir).arg("-o").arg(&bitcode);
                run_command(llvm_as, "llvm-as")?;
            }
            let shared = ensure_runtime(runtime_c, out_dir)?;
            Ok(Artifact {
                runner: Runner::Interp(shared),
                payload: bitcode,
            })
        }
        Target::Native => {
            let executable = out_dir.join(stem);
            if needs_rebuild(&executable, ir)? || needs_rebuild(&executable, runtime_c)? {
                let mut clang = Command::new("clang");
                clang
                    .args(["-O2", "-o"])
                    .arg(&executable)
                    .arg(ir)
                    .arg(runtime_c);
                run_command(clang, "clang (link)")?;
            }
            Ok(Artifact {
                runner: Runner::Native,
                payload: executable,
            })
        }
        Target::Vm => {
            bail!("the selected compiler emitted LLVM IR; use `--target auto` or `interp`")
        }
    }
}

impl Artifact {
    pub fn bytecode(
        target: Target,
        payload: PathBuf,
        vm: PathBuf,
        seed_identity: Option<String>,
    ) -> Result<Self> {
        match target {
            Target::Auto | Target::Vm => Ok(Self {
                runner: Runner::Vm {
                    executable: vm,
                    seed_identity,
                },
                payload,
            }),
            Target::Interp | Target::Native => {
                bail!("the selected compiler emits G1 bytecode; use `--target auto` or `vm`")
            }
        }
    }

    pub fn path(&self) -> &Path {
        &self.payload
    }

    /// Run the artifact with a 4 GiB address-space ceiling (project policy:
    /// generated code is untrusted until the toolchain settles) and return
    /// its exit code.
    pub fn execute(&self, arguments: &[String]) -> Result<i32> {
        let mut command = match &self.runner {
            Runner::Vm {
                executable,
                seed_identity,
            } => {
                let mut grvm = Command::new(executable);
                grvm.arg("run");
                if let Some(identity) = seed_identity {
                    grvm.args(["--seed-identity", identity]);
                }
                grvm.arg(&self.payload);
                if !arguments.is_empty() {
                    grvm.arg("--");
                }
                grvm
            }
            Runner::Interp(runtime) => {
                let mut lli = Command::new("lli");
                lli.arg(format!("--dlopen={}", runtime.display()))
                    .arg(&self.payload);
                lli
            }
            Runner::Native => Command::new(&self.payload),
        };
        command.args(arguments);
        limit_address_space(&mut command, 4 << 30);
        let status = command
            .status()
            .with_context(|| format!("failed to launch {}", self.payload.display()))?;
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

/// Enforce `[backend] minimum-version` against the installed clang major
/// version (queried once per process). Unparseable output is a warning, not
/// an error — unusual toolchains shouldn't hard-block builds.
pub fn check_toolchain(minimum: u64) -> Result<()> {
    static CLANG_MAJOR: std::sync::OnceLock<Option<u64>> = std::sync::OnceLock::new();
    let major = CLANG_MAJOR.get_or_init(|| {
        let output = Command::new("clang").arg("--version").output().ok()?;
        let text = String::from_utf8_lossy(&output.stdout);
        let after = text.split("version ").nth(1)?;
        after
            .split(|c: char| !c.is_ascii_digit())
            .next()?
            .parse()
            .ok()
    });
    match major {
        Some(major) if *major < minimum => bail!(
            "clang {major} is older than the manifest's [backend] minimum-version = {minimum}"
        ),
        Some(_) => Ok(()),
        None => {
            eprintln!(
                "warning: could not determine clang version to check minimum-version = {minimum}"
            );
            Ok(())
        }
    }
}

/// Compile the shared C runtime once per build dir (mtime-cached). Public so
/// `grand test` can pre-build it before parallel materializations.
pub fn ensure_runtime(runtime_c: &Path, out_dir: &Path) -> Result<PathBuf> {
    std::fs::create_dir_all(out_dir)?;
    let shared = out_dir.join("libgrandiose-runtime.so");
    if needs_rebuild(&shared, runtime_c)? {
        let mut clang = Command::new("clang");
        clang
            .args(["-shared", "-fPIC", "-O2", "-o"])
            .arg(&shared)
            .arg(runtime_c);
        run_command(clang, "clang (runtime)")?;
    }
    Ok(shared)
}

fn needs_rebuild(artifact: &Path, source: &Path) -> Result<bool> {
    let Ok(artifact_meta) = artifact.metadata() else {
        return Ok(true);
    };
    Ok(source.metadata()?.modified()? > artifact_meta.modified()?)
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
fn limit_address_space(_command: &mut Command, _bytes: u64) {
    // No portable address-space rlimit off unix; the supervisor limit is
    // best-effort there.
}
