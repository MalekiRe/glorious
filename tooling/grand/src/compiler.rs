use std::process::Command;
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
};

use anyhow::{bail, Context, Result};
use serde::Deserialize;

use crate::contract::{parse_stderr, Capabilities, Declaration, Diagnostic};
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
}

pub struct CompileReport {
    pub success: bool,
    pub diagnostics: Vec<Diagnostic>,
    /// Non-diagnostic compiler stderr, verbatim.
    pub passthrough: String,
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
        Ok(Compiler { path, caps })
    }

    /// Compile canonical crate roots. `None` requests check-only.
    pub fn compile(
        &self,
        inputs: &[PathBuf],
        dependency_roots: &[(String, PathBuf)],
        output: Option<&Path>,
        opt: Option<u8>,
    ) -> Result<CompileReport> {
        {
            let mut command = Command::new(&self.path);
            command.args(["--diagnostics", "json"]);
            if let Some(level) = opt {
                command.arg(format!("-O{level}"));
            }
            match output {
                Some(path) => {
                    command.args(["--emit", "bytecode"]);
                    command.arg("-o").arg(path);
                }
                None => {
                    command.args(["--phase", "check"]);
                }
            }
            command.args(inputs);
            for (name, path) in dependency_roots {
                let mut specification = OsString::from(name);
                specification.push("=");
                specification.push(path);
                command.arg("--dependency").arg(specification);
            }
            let out = command
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
    }

    /// Run the compiler's early resolver boundary when it is advertised.
    /// `None` means the selected compiler does not implement that phase; it is
    /// never silently substituted with a full check because callers use this
    /// boundary specifically to avoid body ownership and lowering work.
    pub fn resolve(&self, inputs: &[PathBuf]) -> Result<Option<CompileReport>> {
        if !self.caps.has_phase("resolve") {
            return Ok(None);
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
                    bail!(
                        "VM does not accept compiler released-seed identity `{identity}`"
                    );
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
                    .all(|pair| pair[0] < pair[1]) =>
        {
        }
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
    use super::{executable_digest, find_checkout_release_tool, Compiler};

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
