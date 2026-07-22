use std::{
    ffi::OsString,
    io::{BufRead, BufReader, Write},
    path::{Path, PathBuf},
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    sync::Mutex,
};

use anyhow::{Context, Result, bail};
use serde::{Deserialize, Serialize};

use crate::contract::{Capabilities, Declaration, Diagnostic, parse_stderr};
use crate::util::find_upwards;

const SUPPORTED_CONTRACT: u32 = 1;
const SUPPORTED_ARTIFACT_MAJOR: u16 = 1;
const SUPPORTED_ARTIFACT_MINOR: u16 = 0;

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "kebab-case")]
struct VmCapabilities {
    grvm: String,
    contract: u32,
    contract_min: u32,
    contract_max: u32,
    artifact_major: u16,
    artifact_minor_min: u16,
    artifact_minor_max: u16,
    #[serde(default)]
    seed_identity_version: Option<u32>,
    #[serde(default)]
    accepted_seed_identities: Vec<String>,
}

/// A probed VM selected as part of one compiler/VM toolchain. Bytecode builds
/// never run an unversioned VM: compatibility is established before invoking
/// the compiler, and this identity participates in the build fingerprint.
pub struct VmToolchain {
    path: PathBuf,
    identity: String,
    seed_identity_version: Option<u32>,
    accepted_seed_identities: Vec<String>,
}

impl VmToolchain {
    pub fn path(&self) -> &Path {
        &self.path
    }

    pub fn identity(&self) -> &str {
        &self.identity
    }

    pub fn seed_identity_version(&self) -> Option<u32> {
        self.seed_identity_version
    }

    pub fn accepts_seed_identity(&self, identity: &str) -> bool {
        self.accepted_seed_identities
            .iter()
            .any(|accepted| accepted == identity)
    }
}

/// A Grandiose compiler behind the versioned contract in [`crate::contract`].
pub struct Compiler {
    path: PathBuf,
    pub caps: Capabilities,
    sessions: Mutex<SessionPool>,
}

#[derive(Default)]
struct SessionPool {
    idle: Vec<CompilerSession>,
    disabled: bool,
}

struct CompilerSession {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
    next_id: u64,
    generation: u64,
}

#[derive(Serialize)]
struct SessionRequest<'a> {
    protocol: u32,
    id: u64,
    method: &'a str,
    arguments: &'a [String],
}

#[derive(Deserialize)]
struct SessionResponse {
    protocol: u32,
    id: Option<u64>,
    status: u8,
    stdout: String,
    stderr: String,
    generation: u64,
    transaction: String,
}

pub struct CompileReport {
    pub success: bool,
    pub diagnostics: Vec<Diagnostic>,
    /// Non-diagnostic compiler stderr, verbatim.
    pub passthrough: String,
}

impl CompilerSession {
    fn spawn(path: &Path) -> Result<Self> {
        let mut child = Command::new(path)
            .arg("--serve")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .with_context(|| format!("failed to launch compiler session {}", path.display()))?;
        let input = child
            .stdin
            .take()
            .context("compiler session did not expose stdin")?;
        let output = child
            .stdout
            .take()
            .context("compiler session did not expose stdout")?;
        Ok(Self {
            child,
            input,
            output: BufReader::new(output),
            next_id: 1,
            generation: 0,
        })
    }

    fn serialized_request_size(&self, arguments: &[String]) -> Result<usize> {
        let request = SessionRequest {
            protocol: 1,
            id: self.next_id,
            method: "compile",
            arguments,
        };
        Ok(serde_json::to_vec(&request)
            .context("serializing compiler session request")?
            .len()
            + 1)
    }

    fn compile(&mut self, arguments: &[String]) -> Result<SessionResponse> {
        let id = self.next_id;
        self.next_id = self
            .next_id
            .checked_add(1)
            .context("session id exhausted")?;
        serde_json::to_writer(
            &mut self.input,
            &SessionRequest {
                protocol: 1,
                id,
                method: "compile",
                arguments,
            },
        )
        .context("writing compiler session request")?;
        self.input.write_all(b"\n")?;
        self.input.flush()?;

        let mut line = String::new();
        if self.output.read_line(&mut line)? == 0 {
            bail!("compiler session closed before responding");
        }
        let response: SessionResponse =
            serde_json::from_str(&line).context("invalid compiler session response")?;
        if response.protocol != 1 || response.id != Some(id) {
            bail!("compiler session response did not match request {id}");
        }
        if response.status > 2 {
            bail!(
                "compiler session returned invalid status {}",
                response.status
            );
        }
        let valid_transaction = match response.status {
            0 => matches!(response.transaction.as_str(), "committed" | "unchanged"),
            _ => response.transaction == "retained",
        };
        if !valid_transaction || response.generation < self.generation {
            bail!("compiler session returned an invalid transaction state");
        }
        if response.status == 2 {
            bail!(
                "compiler rejected a valid session request: {}",
                response.stderr
            );
        }
        self.generation = response.generation;
        Ok(response)
    }
}

impl Drop for CompilerSession {
    fn drop(&mut self) {
        // Never let cleanup wait on a wedged compiler. Closing a pooled session
        // is an implementation detail, so killing the owned child is safe.
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

impl Compiler {
    pub fn seed_identity(&self) -> Option<&str> {
        self.caps.seed_identity.as_deref()
    }

    /// Discovery order: an explicitly selected `GRAND_COMPILER`, the release
    /// compiler in this checkout, then `grc` on PATH. Normal project commands
    /// deliberately never discover `target/debug/grc`: the compiler performs
    /// substantial whole-program analysis, and its debug build is suitable
    /// for compiler debugging rather than real package builds.
    pub fn discover(project_root: &Path) -> Result<Compiler> {
        if let Ok(setting) = std::env::var("GRAND_COMPILER") {
            let path = PathBuf::from(&setting);
            if !path.is_file() {
                bail!("GRAND_COMPILER points to {setting}, which does not exist");
            }
            return Compiler::probe(path);
        }
        if let Some(grc) = find_checkout_release_tool(project_root, "grc") {
            return Compiler::probe(grc);
        }
        if let Ok(path) = which("grc") {
            return Compiler::probe(path);
        }
        bail!(
            "no Grandiose compiler found: set GRAND_COMPILER, build grc in release mode in this checkout, \
             or put `grc` on PATH"
        );
    }

    /// Stable identity for build fingerprinting: which compiler, which build
    /// of it, which contract. Changing compilers invalidates the cache.
    pub fn identity(&self) -> String {
        let digest = executable_digest(&self.path)
            .unwrap_or_else(|error| format!("unreadable:{:?}", error.kind()));
        format!(
            "{}:{digest}:{}:{}:{:?}:{:?}:{:?}:{:?}:{:?}",
            self.path.display(),
            self.caps.grc.as_deref().unwrap_or("unknown"),
            self.caps.contract,
            self.caps.artifact_major,
            self.caps.artifact_minor,
            self.caps.seed_identity_version,
            self.caps.seed_identity,
            self.caps.serve,
        )
    }

    fn probe(path: PathBuf) -> Result<Compiler> {
        let output = Command::new(&path)
            .arg("--capabilities")
            .output()
            .with_context(|| format!("failed to probe compiler {}", path.display()))?;
        if !output.status.success() {
            bail!(
                "compiler {} does not implement the required --capabilities contract",
                path.display()
            );
        }
        let caps: Capabilities = serde_json::from_slice(&output.stdout)
            .with_context(|| format!("invalid --capabilities response from {}", path.display()))?;
        let minimum = caps.contract_min.unwrap_or(caps.contract);
        let maximum = caps.contract_max.unwrap_or(caps.contract);
        if minimum > SUPPORTED_CONTRACT
            || maximum < SUPPORTED_CONTRACT
            || caps.contract != SUPPORTED_CONTRACT
        {
            bail!(
                "compiler contract {} (supported range {minimum}..={maximum}) is incompatible with grand contract {SUPPORTED_CONTRACT}",
                caps.contract
            );
        }
        if !caps.multi_file
            || !caps.modules
            || !caps.has_phase("check")
            || !caps.diagnostics_json
            || !caps.can_emit("interfaces-json")
            || !caps.can_emit("std-interfaces-json")
        {
            bail!("compiler lacks required modules, check, JSON-diagnostics, or interface support");
        }
        if !(caps.can_emit("bytecode") || caps.can_emit("grbc"))
            || caps.artifact_major != Some(SUPPORTED_ARTIFACT_MAJOR)
            || caps.artifact_minor != Some(SUPPORTED_ARTIFACT_MINOR)
        {
            bail!(
                "compiler does not emit supported Grandiose bytecode {}.{}",
                SUPPORTED_ARTIFACT_MAJOR,
                SUPPORTED_ARTIFACT_MINOR
            );
        }
        match (&caps.seed_identity_version, &caps.seed_identity) {
            (None, None) => {}
            (Some(version), Some(identity)) if *version > 0 && !identity.is_empty() => {}
            _ => bail!(
                "compiler seed identity metadata is incomplete; version and identity must be advertised together"
            ),
        }
        if let Some(serve) = &caps.serve {
            if serve.protocol != 1
                || serve.transport != "json-lines"
                || serve.max_request_bytes == 0
                || serve.max_arguments == 0
                || serve.max_inputs == 0
                || serve.max_source_bytes == 0
            {
                bail!(
                    "compiler advertises an incompatible or unbounded persistent-session contract"
                );
            }
        }
        Ok(Compiler {
            path,
            caps,
            sessions: Mutex::new(SessionPool::default()),
        })
    }

    /// Compile canonical crate roots. `None` requests check-only.
    pub fn compile(
        &self,
        inputs: &[PathBuf],
        dependency_roots: &[(String, PathBuf)],
        output: Option<&Path>,
        opt: Option<u8>,
    ) -> Result<CompileReport> {
        let mut arguments = vec![OsString::from("--diagnostics"), OsString::from("json")];
        if let Some(level) = opt {
            arguments.push(OsString::from(format!("-O{level}")));
        }
        match output {
            Some(path) => {
                arguments.extend([OsString::from("--emit"), OsString::from("bytecode")]);
                arguments.push(OsString::from("-o"));
                arguments.push(path.as_os_str().to_owned());
            }
            None => arguments.extend([OsString::from("--phase"), OsString::from("check")]),
        }
        arguments.extend(inputs.iter().map(|path| path.as_os_str().to_owned()));
        for (name, path) in dependency_roots {
            let mut specification = OsString::from(name);
            specification.push("=");
            specification.push(path);
            arguments.push(OsString::from("--dependency"));
            arguments.push(specification);
        }

        if let Some(response) = self.request_session(&arguments)? {
            if response.status != 0
                && [
                    "session input limit exceeded",
                    "session source-byte limit exceeded",
                    "declared module closure exceeds input-count limit",
                ]
                .iter()
                .any(|message| response.stderr.contains(message))
            {
                return self.compile_batch(&arguments);
            }
            let (diagnostics, passthrough) = parse_stderr(&response.stderr);
            return Ok(CompileReport {
                success: response.status == 0,
                diagnostics,
                passthrough,
            });
        }
        self.compile_batch(&arguments)
    }

    fn compile_batch(&self, arguments: &[OsString]) -> Result<CompileReport> {
        let out = Command::new(&self.path)
            .args(arguments)
            .output()
            .with_context(|| format!("failed to launch compiler {}", self.path.display()))?;
        let stderr = String::from_utf8_lossy(&out.stderr);
        let (diagnostics, passthrough) = parse_stderr(&stderr);
        Ok(CompileReport {
            success: out.status.success(),
            diagnostics,
            passthrough,
        })
    }

    /// Route a compile through an idle persistent compiler, spawning another
    /// one when all existing sessions are busy. The mutex only protects the
    /// idle list, so parallel test compilation remains parallel.
    ///
    /// `None` requests a batch fallback. This covers compilers without the
    /// optional protocol, non-UTF-8 paths (which JSON cannot represent), and
    /// requests exceeding the compiler's advertised transport bounds.
    fn request_session(&self, arguments: &[OsString]) -> Result<Option<SessionResponse>> {
        let Some(capabilities) = self.caps.serve.as_ref() else {
            return Ok(None);
        };
        let Some(arguments) = arguments
            .iter()
            .map(|argument| argument.clone().into_string().ok())
            .collect::<Option<Vec<_>>>()
        else {
            return Ok(None);
        };
        if arguments.len() > capabilities.max_arguments {
            return Ok(None);
        }

        let mut session = {
            let mut pool = self
                .sessions
                .lock()
                .unwrap_or_else(|error| error.into_inner());
            if pool.disabled {
                return Ok(None);
            }
            pool.idle.pop()
        };
        if session.is_none() {
            match CompilerSession::spawn(&self.path) {
                Ok(created) => session = Some(created),
                Err(_) => {
                    self.disable_sessions();
                    return Ok(None);
                }
            }
        }
        let mut session = session.expect("session was reused or created");
        let request_size = session.serialized_request_size(&arguments)?;
        if request_size > capabilities.max_request_bytes {
            self.return_session(session);
            return Ok(None);
        }
        match session.compile(&arguments) {
            Ok(response) => {
                self.return_session(session);
                Ok(Some(response))
            }
            Err(_) => {
                // A broken transaction is safe to retry in batch: compilation
                // has no external effect other than deterministically replacing
                // the requested output artifact.
                self.disable_sessions();
                Ok(None)
            }
        }
    }

    fn return_session(&self, session: CompilerSession) {
        let mut pool = self
            .sessions
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        if !pool.disabled {
            pool.idle.push(session);
        }
    }

    fn disable_sessions(&self) {
        let mut pool = self
            .sessions
            .lock()
            .unwrap_or_else(|error| error.into_inner());
        pool.disabled = true;
        pool.idle.clear();
    }

    /// Run the compiler's early resolver boundary when it is advertised.
    /// `None` means the selected compiler does not implement that phase; it is
    /// never silently substituted with a full check because callers use this
    /// boundary specifically to avoid body ownership and lowering work.
    pub fn resolve(&self, inputs: &[PathBuf]) -> Result<Option<CompileReport>> {
        if !self.caps.has_phase("resolve") {
            return Ok(None);
        }
        let mut arguments = vec![
            OsString::from("--diagnostics"),
            OsString::from("json"),
            OsString::from("--phase"),
            OsString::from("resolve"),
        ];
        arguments.extend(inputs.iter().map(|path| path.as_os_str().to_owned()));
        if let Some(response) = self.request_session(&arguments)? {
            let (diagnostics, passthrough) = parse_stderr(&response.stderr);
            return Ok(Some(CompileReport {
                success: response.status == 0,
                diagnostics,
                passthrough,
            }));
        }
        {
            let mut command = Command::new(&self.path);
            if self.caps.diagnostics_json {
                command.args(["--diagnostics", "json"]);
            }
            command.args(["--phase", "resolve"]).args(inputs);
            let out = command
                .output()
                .with_context(|| format!("failed to launch compiler {}", self.path.display()))?;
            let stderr = String::from_utf8_lossy(&out.stderr);
            let (diagnostics, passthrough) = if self.caps.diagnostics_json {
                parse_stderr(&stderr)
            } else {
                (Vec::new(), stderr.into_owned())
            };
            Ok(Some(CompileReport {
                success: out.status.success(),
                diagnostics,
                passthrough,
            }))
        }
    }

    /// Establish the compiler/released-seed/VM compatibility tuple before a
    /// bytecode build can consult freshness or execute an existing artifact.
    /// Compiler+VM pairs may both omit seed metadata; asymmetric omission
    /// cannot prove compatibility.
    pub fn ensure_seed_compatible(&self, vm: &VmToolchain) -> Result<()> {
        match (
            self.caps.seed_identity_version,
            self.caps.seed_identity.as_deref(),
            vm.seed_identity_version(),
        ) {
            (None, None, None) if vm.accepted_seed_identities.is_empty() => Ok(()),
            (Some(compiler_version), Some(identity), Some(vm_version)) => {
                if compiler_version != vm_version {
                    bail!(
                        "compiler seed identity protocol {compiler_version} is incompatible with VM protocol {vm_version}"
                    );
                }
                if !vm.accepts_seed_identity(identity) {
                    bail!("VM does not accept compiler released-seed identity `{identity}`");
                }
                Ok(())
            }
            _ => bail!(
                "compiler and VM must both advertise released-seed identity metadata, or both omit it"
            ),
        }
    }

    /// Authoritative compiler-owned interface scan.
    pub fn interfaces(&self, inputs: &[PathBuf]) -> Result<Vec<Declaration>> {
        match self.caps.can_emit("interfaces-json") {
            true => {
                let mut arguments =
                    vec![OsString::from("--emit"), OsString::from("interfaces-json")];
                arguments.extend(inputs.iter().map(|path| path.as_os_str().to_owned()));
                if let Some(response) = self.request_session(&arguments)? {
                    if response.status != 0 {
                        bail!("compiler interface scan failed: {}", response.stderr.trim());
                    }
                    return serde_json::from_str(&response.stdout)
                        .context("parsing interfaces-json");
                }
                let mut command = Command::new(&self.path);
                command.args(["--emit", "interfaces-json"]).args(inputs);
                let stdout = crate::util::run_command(command, "compiler interface scan")?;
                serde_json::from_str(&stdout).context("parsing interfaces-json")
            }
            false => bail!("compiler lacks required interfaces-json emission"),
        }
    }

    /// Declarations of the implicit prelude, if the compiler can report them.
    pub fn std_interfaces(&self) -> Result<Vec<Declaration>> {
        match self.caps.can_emit("std-interfaces-json") {
            true => {
                let arguments = [
                    OsString::from("--emit"),
                    OsString::from("std-interfaces-json"),
                ];
                if let Some(response) = self.request_session(&arguments)? {
                    if response.status != 0 {
                        bail!(
                            "compiler standard interface scan failed: {}",
                            response.stderr.trim()
                        );
                    }
                    return serde_json::from_str(&response.stdout)
                        .context("parsing std-interfaces-json");
                }
                let mut command = Command::new(&self.path);
                command.args(["--emit", "std-interfaces-json"]);
                let stdout = crate::util::run_command(command, "compiler std interface scan")?;
                serde_json::from_str(&stdout).context("parsing std-interfaces-json")
            }
            false => Ok(Vec::new()),
        }
    }
}

/// Locate the canonical generation-1 VM. The explicit environment override
/// is useful for hermetic toolchains; the repository-local release binary is
/// preferred over PATH so a checkout uses its matching VM. As with `grc`, a
/// debug binary is used only when the caller selects it explicitly.
pub fn discover_vm(project_root: &Path) -> Result<VmToolchain> {
    let path = discover_vm_path(project_root)?;
    probe_vm(path)
}

fn discover_vm_path(project_root: &Path) -> Result<PathBuf> {
    if let Ok(setting) = std::env::var("GRAND_VM") {
        let path = PathBuf::from(&setting);
        if !path.is_file() {
            bail!("GRAND_VM points to {setting}, which does not exist");
        }
        return Ok(path);
    }
    if let Some(path) = find_checkout_release_tool(project_root, "grvm") {
        return Ok(path);
    }
    if let Ok(path) = which("grvm") {
        return Ok(path);
    }
    bail!(
        "no Grandiose VM found: set GRAND_VM, build grvm in release mode in this checkout, \
         or put `grvm` on PATH"
    )
}

fn probe_vm(path: PathBuf) -> Result<VmToolchain> {
    let output = Command::new(&path)
        .arg("--capabilities")
        .output()
        .with_context(|| format!("failed to probe Grandiose VM {}", path.display()))?;
    if !output.status.success() {
        bail!(
            "Grandiose VM {} does not implement the required --capabilities contract",
            path.display()
        );
    }
    let capabilities: VmCapabilities = serde_json::from_slice(&output.stdout)
        .with_context(|| format!("invalid --capabilities response from {}", path.display()))?;
    if capabilities.contract != 1 || capabilities.contract_min > 1 || capabilities.contract_max < 1
    {
        bail!(
            "VM contract {} (supported range {}..={}) is incompatible with grand VM contract 1",
            capabilities.contract,
            capabilities.contract_min,
            capabilities.contract_max
        );
    }
    if capabilities.artifact_major != SUPPORTED_ARTIFACT_MAJOR
        || !(capabilities.artifact_minor_min..=capabilities.artifact_minor_max)
            .contains(&SUPPORTED_ARTIFACT_MINOR)
    {
        bail!(
            "VM artifact range {}.{}..={} is incompatible with compiler artifact {}.{}",
            capabilities.artifact_major,
            capabilities.artifact_minor_min,
            capabilities.artifact_minor_max,
            SUPPORTED_ARTIFACT_MAJOR,
            SUPPORTED_ARTIFACT_MINOR
        );
    }
    match capabilities.seed_identity_version {
        None if capabilities.accepted_seed_identities.is_empty() => {}
        Some(version)
            if version > 0
                && !capabilities.accepted_seed_identities.is_empty()
                && capabilities
                    .accepted_seed_identities
                    .iter()
                    .all(|identity| !identity.is_empty())
                && capabilities
                    .accepted_seed_identities
                    .windows(2)
                    .all(|pair| pair[0] < pair[1]) => {}
        _ => bail!(
            "VM seed identity metadata is incomplete or noncanonical; version and a sorted unique nonempty acceptance set are required together"
        ),
    }
    let digest = executable_digest(&path)
        .with_context(|| format!("failed to fingerprint Grandiose VM {}", path.display()))?;
    let identity = format!(
        "{}:{digest}:{}:{}:{}:{}:{}:{:?}:{:?}",
        path.display(),
        capabilities.grvm,
        capabilities.contract,
        capabilities.artifact_major,
        capabilities.artifact_minor_min,
        capabilities.artifact_minor_max,
        capabilities.seed_identity_version,
        capabilities.accepted_seed_identities,
    );
    Ok(VmToolchain {
        path,
        identity,
        seed_identity_version: capabilities.seed_identity_version,
        accepted_seed_identities: capabilities.accepted_seed_identities,
    })
}

fn executable_digest(path: &Path) -> std::io::Result<String> {
    std::fs::read(path).map(|bytes| blake3::hash(&bytes).to_hex().to_string())
}

fn find_checkout_release_tool(project_root: &Path, name: &str) -> Option<PathBuf> {
    find_upwards(project_root, &format!("target/release/{name}"))
}

fn which(name: &str) -> Result<PathBuf> {
    let path = std::env::var("PATH").unwrap_or_default();
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
        .with_context(|| format!("`{name}` not found on PATH"))
}

#[cfg(test)]
mod tests {
    use super::{Compiler, executable_digest, find_checkout_release_tool};

    #[cfg(unix)]
    fn session_compiler(directory: &std::path::Path) -> (Compiler, std::path::PathBuf) {
        use std::os::unix::fs::PermissionsExt;

        let executable = directory.join("grc-session");
        let log = directory.join("session.log");
        std::fs::write(
            &executable,
            format!(
                r##"#!/bin/sh
if [ "$1" = --capabilities ]; then
  echo '{{"grc":"test","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"modules":true,"phases":["check"],"emit":["bytecode","interfaces-json","std-interfaces-json"],"diagnostics-json":true,"serve":{{"protocol":1,"transport":"json-lines","max-request-bytes":1048576,"max-arguments":256,"max-inputs":256,"max-source-bytes":1048576}}}}'
  exit 0
fi
if [ "$1" = --serve ]; then
  echo serve >> "{}"
  id=1
  generation=0
  while IFS= read -r request; do
    generation=$((generation + 1))
    sleep 0.05
    echo "{{\"protocol\":1,\"id\":$id,\"status\":0,\"stdout\":\"\",\"stderr\":\"\",\"generation\":$generation,\"transaction\":\"committed\"}}"
    id=$((id + 1))
  done
  exit 0
fi
echo batch >> "{}"
exit 0
"##,
                log.display(),
                log.display(),
            ),
        )
        .unwrap();
        let mut permissions = std::fs::metadata(&executable).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&executable, permissions).unwrap();
        (Compiler::probe(executable).unwrap(), log)
    }

    #[test]
    fn executable_identity_hashes_content_not_only_metadata() {
        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("tool");
        std::fs::write(&executable, b"first-build").unwrap();
        let first = executable_digest(&executable).unwrap();
        std::fs::write(&executable, b"other-build").unwrap();
        let second = executable_digest(&executable).unwrap();
        assert_eq!(b"first-build".len(), b"other-build".len());
        assert_ne!(first, second);
    }

    #[test]
    fn checkout_discovery_ignores_debug_toolchains() {
        let directory = tempfile::tempdir().unwrap();
        let nested = directory.path().join("project/src");
        let debug = directory.path().join("target/debug/grc");
        std::fs::create_dir_all(&nested).unwrap();
        std::fs::create_dir_all(debug.parent().unwrap()).unwrap();
        std::fs::write(&debug, b"debug compiler").unwrap();
        assert_eq!(find_checkout_release_tool(&nested, "grc"), None);

        let release = directory.path().join("target/release/grc");
        std::fs::create_dir_all(release.parent().unwrap()).unwrap();
        std::fs::write(&release, b"release compiler").unwrap();
        assert_eq!(find_checkout_release_tool(&nested, "grc"), Some(release));
    }

    #[cfg(unix)]
    #[test]
    fn compile_reuses_persistent_session_for_sequential_requests() {
        let directory = tempfile::tempdir().unwrap();
        let (compiler, log) = session_compiler(directory.path());
        let input = directory.path().join("input.glorious");
        std::fs::write(&input, "main() -> () { () }").unwrap();

        assert!(
            compiler
                .compile(std::slice::from_ref(&input), &[], None, None)
                .unwrap()
                .success
        );
        assert!(
            compiler
                .compile(std::slice::from_ref(&input), &[], None, None)
                .unwrap()
                .success
        );

        assert_eq!(std::fs::read_to_string(log).unwrap(), "serve\n");
    }

    #[cfg(unix)]
    #[test]
    fn non_utf8_arguments_fall_back_without_starting_a_session() {
        use std::os::unix::ffi::OsStringExt;

        let directory = tempfile::tempdir().unwrap();
        let (compiler, log) = session_compiler(directory.path());
        let input = std::path::PathBuf::from(std::ffi::OsString::from_vec(vec![0xff]));

        assert!(compiler.compile(&[input], &[], None, None).unwrap().success);
        assert_eq!(std::fs::read_to_string(log).unwrap(), "batch\n");
    }

    #[cfg(unix)]
    #[test]
    fn busy_sessions_do_not_serialize_parallel_compiles() {
        let directory = tempfile::tempdir().unwrap();
        let (compiler, log) = session_compiler(directory.path());
        let input = directory.path().join("input.glorious");
        std::fs::write(&input, "main() -> () { () }").unwrap();
        let barrier = std::sync::Barrier::new(3);

        std::thread::scope(|scope| {
            for _ in 0..2 {
                scope.spawn(|| {
                    barrier.wait();
                    assert!(
                        compiler
                            .compile(std::slice::from_ref(&input), &[], None, None)
                            .unwrap()
                            .success
                    );
                });
            }
            barrier.wait();
        });

        assert_eq!(std::fs::read_to_string(log).unwrap(), "serve\nserve\n");
    }

    #[cfg(unix)]
    #[test]
    fn resolve_phase_is_capability_gated_and_preserves_json_diagnostics() {
        use std::os::unix::fs::PermissionsExt;

        let directory = tempfile::tempdir().unwrap();
        let executable = directory.path().join("grc");
        let log = directory.path().join("args.log");
        let input = directory.path().join("input.glorious");
        std::fs::write(&input, "main() -> () { () }").unwrap();
        std::fs::write(
            &executable,
            format!(
                "#!/bin/sh\nif [ \"$1\" = --capabilities ]; then echo '{{\"grc\":\"test\",\"contract\":1,\"contract-min\":1,\"contract-max\":1,\"artifact-major\":1,\"artifact-minor\":0,\"multi-file\":true,\"modules\":true,\"phases\":[\"resolve\",\"check\"],\"emit\":[\"bytecode\",\"interfaces-json\",\"std-interfaces-json\"],\"diagnostics-json\":true}}'; exit 0; fi\nprintf '%s\\n' \"$*\" > '{}'\necho '{{\"severity\":\"error\",\"code\":\"G1R001\",\"title\":\"unknown type\",\"labels\":[{{\"file\":\"{}\",\"line\":1}}]}}' >&2\nexit 1\n",
                log.display(),
                input.display(),
            ),
        )
        .unwrap();
        let mut permissions = std::fs::metadata(&executable).unwrap().permissions();
        permissions.set_mode(0o755);
        std::fs::set_permissions(&executable, permissions).unwrap();

        let compiler = Compiler::probe(executable).unwrap();
        let report = compiler
            .resolve(std::slice::from_ref(&input))
            .unwrap()
            .unwrap();
        assert!(!report.success);
        assert_eq!(report.diagnostics.len(), 1);
        assert_eq!(report.diagnostics[0].code.as_deref(), Some("G1R001"));
        let args = std::fs::read_to_string(&log).unwrap();
        assert!(
            args.contains("--diagnostics json --phase resolve"),
            "{args}"
        );
    }
}
