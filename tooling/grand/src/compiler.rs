use std::process::Command;
use std::{
    ffi::OsString,
    path::{Path, PathBuf},
};

use anyhow::{bail, Context, Result};
use serde::Deserialize;

use crate::contract::{
    parse_stderr, Capabilities, Declaration, DeclarationKind, Diagnostic, Label, Severity,
};
use crate::scan;
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
///
/// Capabilities are probed once at discovery (`grc --capabilities`); legacy
/// unversioned legacy compilers fail the probe and are driven through the
/// original `grc <input.gr> <output.ll>` interface. Every future code path
/// (multi-file, check phase, structured diagnostics, interface scans) is
/// gated on a capability, so the real compiler lights them up by simply
/// implementing the probe.
pub struct Compiler {
    kind: Kind,
    pub caps: Capabilities,
}

enum Kind {
    Executable(PathBuf),
    /// In-process stand-in (`GRAND_COMPILER=fake`): emits exit-0 modules,
    /// fails on `FAKE_ERROR` markers, scans interfaces in-process.
    /// `GRAND_FAKE_CAPS=multi-file,resolve,check,diagnostics,interfaces,std` selects
    /// which future capabilities it advertises (default: none = legacy).
    Fake,
}

pub struct CompileReport {
    pub success: bool,
    pub diagnostics: Vec<Diagnostic>,
    /// Non-JSON compiler stderr (the legacy renderer's output), verbatim.
    pub passthrough: String,
}

impl Compiler {
    /// Whether this compiler emits verified G1 bytecode rather than legacy
    /// textual LLVM IR.
    pub fn emits_bytecode(&self) -> bool {
        self.caps.can_emit("bytecode") || self.caps.can_emit("grbc")
    }

    pub fn seed_identity(&self) -> Option<&str> {
        self.caps.seed_identity.as_deref()
    }

    /// Discovery order: `GRAND_COMPILER` (path or `fake`), then `compiler/grc`
    /// walking up from the project root (this repository's layout), then
    /// `grc` on PATH.
    pub fn discover(project_root: &Path) -> Result<Compiler> {
        if let Ok(setting) = std::env::var("GRAND_COMPILER") {
            if setting == "fake" {
                return Ok(Compiler {
                    kind: Kind::Fake,
                    caps: fake_capabilities(),
                });
            }
            let path = PathBuf::from(&setting);
            if !path.is_file() {
                bail!("GRAND_COMPILER points to {setting}, which does not exist");
            }
            return Compiler::probe(path);
        }
        if let Some(grc) = find_upwards(project_root, "compiler/grc") {
            return Compiler::probe(grc);
        }
        if let Ok(path) = which("grc") {
            return Compiler::probe(path);
        }
        bail!(
            "no Grandiose compiler found: set GRAND_COMPILER, or run inside a checkout \
             containing compiler/grc, or put `grc` on PATH"
        );
    }

    /// Stable identity for build fingerprinting: which compiler, which build
    /// of it, which contract. Changing compilers invalidates the cache.
    pub fn identity(&self) -> String {
        match &self.kind {
            Kind::Fake => format!(
                "fake:{}:{:?}:{:?}:{:?}:{:?}:{:?}:{:?}:{:?}:{}:{}:{:?}:{:?}:{}",
                self.caps.contract,
                self.caps.contract_min,
                self.caps.contract_max,
                self.caps.artifact_major,
                self.caps.artifact_minor,
                self.caps.seed_identity_version,
                self.caps.seed_identity,
                self.caps.serve,
                self.caps.multi_file,
                self.caps.modules,
                self.caps.phases,
                self.caps.emit,
                self.caps.diagnostics_json
            ),
            Kind::Executable(path) => {
                let digest = executable_digest(path)
                    .unwrap_or_else(|error| format!("unreadable:{:?}", error.kind()));
                format!(
                    "{}:{digest}:{}:{}:{:?}:{:?}:{:?}:{:?}:{:?}",
                    path.display(),
                    self.caps.grc.as_deref().unwrap_or("legacy"),
                    self.caps.contract,
                    self.caps.artifact_major,
                    self.caps.artifact_minor,
                    self.caps.seed_identity_version,
                    self.caps.seed_identity,
                    self.caps.serve,
                )
            }
        }
    }

    fn probe(path: PathBuf) -> Result<Compiler> {
        let caps = Command::new(&path)
            .arg("--capabilities")
            .output()
            .ok()
            .filter(|output| output.status.success())
            .and_then(|output| serde_json::from_slice(&output.stdout).ok())
            .unwrap_or_else(Capabilities::legacy);
        if caps.contract != 0 {
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
            let bytecode = caps.can_emit("bytecode") || caps.can_emit("grbc");
            if bytecode
                && (caps.artifact_major != Some(SUPPORTED_ARTIFACT_MAJOR)
                    || caps.artifact_minor != Some(SUPPORTED_ARTIFACT_MINOR))
            {
                bail!(
                    "compiler advertises bytecode but artifact version {:?}.{:?} is incompatible with supported {}.{}",
                    caps.artifact_major,
                    caps.artifact_minor,
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
        }
        Ok(Compiler {
            kind: Kind::Executable(path),
            caps,
        })
    }

    /// Compile `inputs` (already a single bundle unless `caps.multi_file`).
    /// `output` is the IR path; `None` requests check-only (caller must have
    /// verified `caps.has_phase("check")`). `opt` forwards `-O<n>` to
    /// contract-aware compilers.
    pub fn compile(
        &self,
        inputs: &[PathBuf],
        dependency_roots: &[(String, PathBuf)],
        output: Option<&Path>,
        opt: Option<u8>,
    ) -> Result<CompileReport> {
        match &self.kind {
            Kind::Fake => fake_compile(inputs, output),
            Kind::Executable(grc) => {
                let mut command = Command::new(grc);
                if self.caps.contract > 0 {
                    if self.caps.diagnostics_json {
                        command.args(["--diagnostics", "json"]);
                    }
                    if let Some(level) = opt {
                        command.arg(format!("-O{level}"));
                    }
                    match output {
                        Some(path) => {
                            if self.emits_bytecode() {
                                command.args(["--emit", "bytecode"]);
                            }
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
                } else {
                    let [input] = inputs else {
                        bail!(
                            "legacy compiler accepts exactly one input (grand should have bundled)"
                        )
                    };
                    command
                        .arg(input)
                        .arg(output.context("legacy compiler cannot check-only")?);
                }
                let out = command
                    .output()
                    .with_context(|| format!("failed to launch compiler {}", grc.display()))?;
                let stderr = String::from_utf8_lossy(&out.stderr);
                let (diagnostics, passthrough) = if self.caps.diagnostics_json {
                    parse_stderr(&stderr)
                } else {
                    (Vec::new(), stderr.into_owned())
                };
                Ok(CompileReport {
                    success: out.status.success(),
                    diagnostics,
                    passthrough,
                })
            }
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
        match &self.kind {
            Kind::Fake => fake_compile(inputs, None).map(Some),
            Kind::Executable(grc) => {
                let mut command = Command::new(grc);
                if self.caps.diagnostics_json {
                    command.args(["--diagnostics", "json"]);
                }
                command.args(["--phase", "resolve"]).args(inputs);
                let out = command
                    .output()
                    .with_context(|| format!("failed to launch compiler {}", grc.display()))?;
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
    }

    /// Establish the compiler/released-seed/VM compatibility tuple before a
    /// bytecode build can consult freshness or execute an existing artifact.
    /// Pre-negotiation compiler+VM pairs remain supported only when both sides
    /// omit seed metadata; asymmetric omission cannot prove compatibility.
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
                "compiler and VM must both advertise released-seed identity metadata, or both use the legacy contract"
            ),
        }
    }

    /// Authoritative interface scan, if the compiler offers one; `None` tells
    /// the caller to fall back to the in-process compiler scanner (warnings
    /// only for compatibility with an external legacy compiler).
    pub fn interfaces(&self, inputs: &[PathBuf]) -> Result<Option<Vec<Declaration>>> {
        match &self.kind {
            Kind::Fake if self.caps.can_emit("interfaces-json") => Ok(Some(scan_files(inputs)?)),
            Kind::Executable(grc) if self.caps.can_emit("interfaces-json") => {
                let mut command = Command::new(grc);
                command.args(["--emit", "interfaces-json"]).args(inputs);
                let stdout = crate::util::run_command(command, "compiler interface scan")?;
                Ok(Some(
                    serde_json::from_str(&stdout).context("parsing interfaces-json")?,
                ))
            }
            _ => Ok(None),
        }
    }

    /// Declarations of the implicit prelude, if the compiler can report them.
    pub fn std_interfaces(&self) -> Result<Vec<Declaration>> {
        match &self.kind {
            Kind::Fake if self.caps.can_emit("std-interfaces-json") => Ok(fake_std_interfaces()),
            Kind::Executable(grc) if self.caps.can_emit("std-interfaces-json") => {
                let mut command = Command::new(grc);
                command.args(["--emit", "std-interfaces-json"]);
                let stdout = crate::util::run_command(command, "compiler std interface scan")?;
                serde_json::from_str(&stdout).context("parsing std-interfaces-json")
            }
            _ => Ok(Vec::new()),
        }
    }
}

fn fake_capabilities() -> Capabilities {
    let selected = std::env::var("GRAND_FAKE_CAPS").unwrap_or_default();
    let has = |name: &str| selected.split(',').any(|token| token.trim() == name);
    Capabilities {
        grc: Some("fake".into()),
        contract: 1,
        contract_min: Some(1),
        contract_max: Some(1),
        artifact_major: None,
        artifact_minor: None,
        seed_identity_version: None,
        seed_identity: None,
        serve: None,
        multi_file: has("multi-file"),
        modules: has("modules"),
        phases: [
            has("resolve").then(|| "resolve".to_string()),
            has("check").then(|| "check".to_string()),
        ]
        .into_iter()
        .flatten()
        .collect(),
        emit: [
            has("interfaces").then(|| "interfaces-json".to_string()),
            has("std").then(|| "std-interfaces-json".to_string()),
        ]
        .into_iter()
        .flatten()
        .collect(),
        diagnostics_json: has("diagnostics"),
    }
}

/// The fake accepts anything except sources containing a `FAKE_ERROR` marker,
/// which produce a structured diagnostic at the marker (this is how tests
/// exercise failure paths, including bundle-to-source remapping).
fn fake_compile(inputs: &[PathBuf], output: Option<&Path>) -> Result<CompileReport> {
    let mut diagnostics = Vec::new();
    for input in inputs {
        let text = std::fs::read_to_string(input)
            .with_context(|| format!("reading {}", input.display()))?;
        for (index, line) in text.lines().enumerate() {
            if line.contains("FAKE_ERROR") {
                diagnostics.push(Diagnostic {
                    severity: Severity::Error,
                    code: Some("GRC9999".into()),
                    title: "fake error marker".into(),
                    labels: vec![Label {
                        file: input.clone(),
                        line: Some(index + 1),
                        col: None,
                        start_byte: None,
                        end_byte: None,
                        message: Some("marker found here".into()),
                    }],
                    note: None,
                    help: None,
                    fix: None,
                });
            }
            if let Some(col) = line.find("FAKE_FIXME") {
                let line_start: usize = text.lines().take(index).map(|l| l.len() + 1).sum();
                diagnostics.push(Diagnostic {
                    severity: Severity::Warning,
                    code: Some("GRC8888".into()),
                    title: "fixable marker".into(),
                    labels: vec![Label {
                        file: input.clone(),
                        line: Some(index + 1),
                        col: Some(col + 1),
                        start_byte: Some(line_start + col),
                        end_byte: Some(line_start + col + "FAKE_FIXME".len()),
                        message: Some("remove this marker".into()),
                    }],
                    note: None,
                    help: Some("run `grand fix` to apply".into()),
                    fix: Some(crate::contract::Fix {
                        file: input.clone(),
                        start_byte: line_start + col,
                        end_byte: line_start + col + "FAKE_FIXME".len(),
                        replacement: String::new(),
                    }),
                });
            }
        }
    }
    let success = diagnostics.iter().all(|d| d.severity != Severity::Error);
    if success {
        if let Some(output) = output {
            std::fs::write(output, "define i32 @main() {\nentry:\n  ret i32 0\n}\n")
                .with_context(|| format!("writing {}", output.display()))?;
        }
    }
    Ok(CompileReport {
        success,
        diagnostics,
        passthrough: String::new(),
    })
}

fn scan_files(inputs: &[PathBuf]) -> Result<Vec<Declaration>> {
    let mut declarations = Vec::new();
    for input in inputs {
        let text = std::fs::read_to_string(input)
            .with_context(|| format!("reading {}", input.display()))?;
        declarations.extend(scan::scan(input, &text));
    }
    Ok(declarations)
}

fn fake_std_interfaces() -> Vec<Declaration> {
    ["if", "else", "and", "or", "not", "Result", "Option", "Bool"]
        .into_iter()
        .map(|name| Declaration {
            identity: None,
            name: name.into(),
            kind: if name.chars().next().is_some_and(char::is_uppercase) {
                DeclarationKind::Type
            } else {
                DeclarationKind::Callable
            },
            module: None,
            visibility: None,
            file: PathBuf::from("«std»"),
            line: 0,
            signature: None,
            docs: None,
        })
        .collect()
}

/// Locate the C runtime source the generated IR links against.
/// Order: `GRAND_RUNTIME`, then `compiler/runtime/native_entry.c` upward.
pub fn discover_runtime(project_root: &Path) -> Result<PathBuf> {
    if let Ok(setting) = std::env::var("GRAND_RUNTIME") {
        let path = PathBuf::from(&setting);
        if !path.is_file() {
            bail!("GRAND_RUNTIME points to {setting}, which does not exist");
        }
        return Ok(path);
    }
    find_upwards(project_root, "compiler/runtime/native_entry.c").context(
        "no Grandiose C runtime found: set GRAND_RUNTIME or run inside a checkout \
         containing compiler/runtime/native_entry.c",
    )
}

/// Locate the canonical generation-1 VM. The explicit environment override
/// is useful for hermetic toolchains; repository-local release/debug binaries
/// are preferred over PATH so a checkout uses its matching VM.
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
    for relative in ["target/release/grvm", "target/debug/grvm"] {
        if let Some(path) = find_upwards(project_root, relative) {
            return Ok(path);
        }
    }
    if let Ok(path) = which("grvm") {
        return Ok(path);
    }
    bail!("no Grandiose VM found: set GRAND_VM, build grvm in this checkout, or put `grvm` on PATH")
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

fn which(name: &str) -> Result<PathBuf> {
    let path = std::env::var("PATH").unwrap_or_default();
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
        .with_context(|| format!("`{name}` not found on PATH"))
}

#[cfg(test)]
mod tests {
    use super::{executable_digest, Compiler};

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
                "#!/bin/sh\nif [ \"$1\" = --capabilities ]; then echo '{{\"grc\":\"test\",\"contract\":1,\"contract-min\":1,\"contract-max\":1,\"multi-file\":true,\"phases\":[\"resolve\",\"check\"],\"emit\":[],\"diagnostics-json\":true}}'; exit 0; fi\nprintf '%s\\n' \"$*\" > '{}'\necho '{{\"severity\":\"error\",\"code\":\"G1R001\",\"title\":\"unknown type\",\"labels\":[{{\"file\":\"{}\",\"line\":1}}]}}' >&2\nexit 1\n",
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

        let unadvertised = Compiler {
            kind: super::Kind::Fake,
            caps: crate::contract::Capabilities {
                phases: vec!["check".into()],
                ..crate::contract::Capabilities::default()
            },
        };
        assert!(unadvertised.resolve(&[input]).unwrap().is_none());
    }
}
