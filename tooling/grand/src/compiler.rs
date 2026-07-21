use std::path::{Path, PathBuf};
use std::process::Command;

use anyhow::{bail, Context, Result};

use crate::contract::{parse_stderr, Capabilities, Declaration, DeclarationKind, Diagnostic, Label, Severity};
use crate::scan;
use crate::util::find_upwards;

/// A Grandiose compiler behind the versioned contract in [`crate::contract`].
///
/// Capabilities are probed once at discovery (`grc --capabilities`); legacy
/// compilers — today's `grc` — fail the probe and are driven through the
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
    /// fails on `FAKE_ERROR` markers, scans interfaces heuristically.
    /// `GRAND_FAKE_CAPS=multi-file,check,diagnostics,interfaces,std` selects
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
    /// Discovery order: `GRAND_COMPILER` (path or `fake`), then `compiler/grc`
    /// walking up from the project root (this repository's layout), then
    /// `grc` on PATH.
    pub fn discover(project_root: &Path) -> Result<Compiler> {
        if let Ok(setting) = std::env::var("GRAND_COMPILER") {
            if setting == "fake" {
                return Ok(Compiler { kind: Kind::Fake, caps: fake_capabilities() });
            }
            let path = PathBuf::from(&setting);
            if !path.is_file() {
                bail!("GRAND_COMPILER points to {setting}, which does not exist");
            }
            return Ok(Compiler::probe(path));
        }
        if let Some(grc) = find_upwards(project_root, "compiler/grc") {
            return Ok(Compiler::probe(grc));
        }
        if let Ok(path) = which("grc") {
            return Ok(Compiler::probe(path));
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
                "fake:{}:{}:{:?}:{:?}:{}",
                self.caps.contract,
                self.caps.multi_file,
                self.caps.phases,
                self.caps.emit,
                self.caps.diagnostics_json
            ),
            Kind::Executable(path) => {
                let meta = path.metadata().ok();
                let mtime = meta
                    .as_ref()
                    .and_then(|m| m.modified().ok())
                    .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                    .map(|d| d.as_nanos())
                    .unwrap_or(0);
                let length = meta.map(|m| m.len()).unwrap_or(0);
                format!(
                    "{}:{mtime}:{length}:{}",
                    path.display(),
                    self.caps.grc.as_deref().unwrap_or("legacy")
                )
            }
        }
    }

    fn probe(path: PathBuf) -> Compiler {
        let caps = Command::new(&path)
            .arg("--capabilities")
            .output()
            .ok()
            .filter(|output| output.status.success())
            .and_then(|output| serde_json::from_slice(&output.stdout).ok())
            .unwrap_or_else(Capabilities::legacy);
        Compiler { kind: Kind::Executable(path), caps }
    }

    /// Compile `inputs` (already a single bundle unless `caps.multi_file`).
    /// `output` is the IR path; `None` requests check-only (caller must have
    /// verified `caps.has_phase("check")`). `opt` forwards `-O<n>` to
    /// contract-aware compilers.
    pub fn compile(
        &self,
        inputs: &[PathBuf],
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
                        Some(path) => { command.arg("-o").arg(path); }
                        None => { command.args(["--phase", "check"]); }
                    }
                    command.args(inputs);
                } else {
                    let [input] = inputs else {
                        bail!("legacy compiler accepts exactly one input (grand should have bundled)")
                    };
                    command.arg(input).arg(output.context("legacy compiler cannot check-only")?);
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
                Ok(CompileReport { success: out.status.success(), diagnostics, passthrough })
            }
        }
    }

    /// Authoritative interface scan, if the compiler offers one; `None` tells
    /// the caller to fall back to the heuristic scanner (warnings only).
    pub fn interfaces(&self, inputs: &[PathBuf]) -> Result<Option<Vec<Declaration>>> {
        match &self.kind {
            Kind::Fake if self.caps.can_emit("interfaces-json") => {
                Ok(Some(scan_files(inputs)?))
            }
            Kind::Executable(grc) if self.caps.can_emit("interfaces-json") => {
                let mut command = Command::new(grc);
                command.args(["--emit", "interfaces-json"]).args(inputs);
                let stdout = crate::util::run_command(command, "compiler interface scan")?;
                Ok(Some(serde_json::from_str(&stdout).context("parsing interfaces-json")?))
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
        multi_file: has("multi-file"),
        phases: has("check").then(|| vec!["check".into()]).unwrap_or_default(),
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
    Ok(CompileReport { success, diagnostics, passthrough: String::new() })
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
            name: name.into(),
            kind: if name.chars().next().is_some_and(char::is_uppercase) {
                DeclarationKind::Type
            } else {
                DeclarationKind::Callable
            },
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

fn which(name: &str) -> Result<PathBuf> {
    let path = std::env::var("PATH").unwrap_or_default();
    std::env::split_paths(&path)
        .map(|dir| dir.join(name))
        .find(|candidate| candidate.is_file())
        .with_context(|| format!("`{name}` not found on PATH"))
}
