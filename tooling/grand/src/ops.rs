use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{bail, Context, Result};

use crate::bundle::{assemble, input_files, package_sources};
use crate::compiler::{discover_runtime, Compiler};
use crate::contract::{Declaration, DeclarationKind, Diagnostic, Fix, Severity};
use crate::lock::{Lockfile, LOCK_NAME};
use crate::manifest::{Manifest, MANIFEST_NAME};
use crate::resolve::{resolve, Resolution, ResolveOptions};
use crate::target::{materialize, Artifact, Target};
use crate::util::{copy_dir, valid_package_name};

pub struct Project {
    pub root: PathBuf,
    pub manifest: Manifest,
    /// Where the shared lockfile lives: the workspace root when this package
    /// is a workspace member, else the package root.
    pub lock_root: PathBuf,
}

/// `-p/--package` selection (set once from the CLI before dispatch).
static SELECTED_PACKAGE: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();

pub fn select_package(name: Option<String>) {
    let _ = SELECTED_PACKAGE.set(name);
}

impl Project {
    pub fn locate() -> Result<Project> {
        let cwd = std::env::current_dir()?;
        let select = SELECTED_PACKAGE.get().and_then(|s| s.as_deref());
        let (root, manifest, lock_root) =
            crate::manifest::find_project_in_workspace(&cwd, select)?;
        Ok(Project { root, manifest, lock_root })
    }

    pub fn build_dir(&self) -> PathBuf {
        self.root.join("target").join("grand")
    }
}

fn env_flag(name: &str) -> bool {
    std::env::var(name).is_ok_and(|v| v == "1" || v == "true")
}

/// Load the project, resolve dependencies, and reconcile the lockfile.
/// `update`: None trusts existing pins; see [`ResolveOptions::update`].
pub fn load_and_resolve(update: Option<Vec<String>>) -> Result<(Project, Resolution)> {
    let project = Project::locate()?;
    let lock_path = project.lock_root.join(LOCK_NAME);
    let previous = Lockfile::load(&lock_path)?;
    let options = ResolveOptions {
        locked: env_flag("GRAND_LOCKED"),
        update,
        offline: env_flag("GRAND_OFFLINE"),
    };
    let resolution = resolve(&project.root, &project.manifest, previous.as_ref(), &options)?;
    let fresh = resolution.to_lockfile();
    let changed = previous.as_ref().map(|p| p.packages != fresh.packages).unwrap_or(true);
    if changed {
        if options.locked {
            bail!("{LOCK_NAME} is out of date and GRAND_LOCKED is set; run `grand lock` locally");
        }
        if !fresh.packages.is_empty() || lock_path.exists() {
            fresh.save(&lock_path)?;
            eprintln!("    Updated {LOCK_NAME}");
        }
    }
    Ok((project, resolution))
}

// ---------------------------------------------------------------------------
// Lint levels

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LintLevel {
    Allow,
    Warn,
    Deny,
}

impl LintLevel {
    fn parse(value: &str) -> Result<LintLevel> {
        match value {
            "allow" => Ok(LintLevel::Allow),
            "warn" => Ok(LintLevel::Warn),
            "deny" => Ok(LintLevel::Deny),
            other => bail!("unknown lint level `{other}` (expected allow, warn, deny)"),
        }
    }
}

/// Effective diagnostic-level table: manifest `[lints]` overridden by CLI
/// flags (`--allow/--warn/--deny CODE|warnings`). Errors from the compiler
/// are never downgraded; warnings/advice can be silenced or escalated.
struct Lints(BTreeMap<String, LintLevel>);

impl Lints {
    fn new(manifest: &Manifest, cli: &[(String, LintLevel)]) -> Result<Lints> {
        let mut table = BTreeMap::new();
        for (code, value) in &manifest.lints {
            table.insert(code.clone(), LintLevel::parse(value)?);
        }
        for (code, level) in cli {
            table.insert(code.clone(), *level);
        }
        Ok(Lints(table))
    }

    fn apply(&self, diagnostics: &mut Vec<Diagnostic>) {
        diagnostics.retain_mut(|diagnostic| {
            if diagnostic.severity == Severity::Error {
                return true;
            }
            let level = diagnostic
                .code
                .as_ref()
                .and_then(|code| self.0.get(code))
                .or_else(|| self.0.get("warnings"));
            match level {
                Some(LintLevel::Allow) => false,
                Some(LintLevel::Deny) => {
                    diagnostic.severity = Severity::Error;
                    true
                }
                Some(LintLevel::Warn) | None => true,
            }
        });
    }
}

// ---------------------------------------------------------------------------
// Compilation pipeline

pub struct Compiled {
    pub ir: Option<PathBuf>,
    pub diagnostics: Vec<Diagnostic>,
    pub passthrough: String,
    pub success: bool,
}

#[derive(Clone, Copy)]
pub struct CompileOptions<'a> {
    pub entry: Option<&'a Path>,
    pub stem: &'a str,
    pub want_ir: bool,
    /// Suppress progress + diagnostic printing; the caller consumes the
    /// returned data (compile-fail golden tests).
    pub quiet: bool,
    /// Optimization level, forwarded as `-O<n>` to contract-aware compilers
    /// (legacy compilers have no such flag; it is ignored there).
    pub opt: Option<u8>,
}

/// Compile the resolved project. `entry` substitutes the root entry file
/// (used by `grand test`); `stem` names the outputs; `want_ir = false` lets a
/// check-capable compiler skip emission. Renders diagnostics (lint-adjusted,
/// remapped out of the bundle when concatenation was used) but does NOT bail
/// on compilation failure — `grand fix` needs the diagnostics; use
/// [`compile_ok`] elsewhere.
fn compile(
    project: &Project,
    resolution: &Resolution,
    compiler: &Compiler,
    opts: CompileOptions,
    cli_lints: &[(String, LintLevel)],
) -> Result<Compiled> {
    let CompileOptions { entry, stem, want_ir, quiet, opt } = opts;
    macro_rules! progress {
        ($($arg:tt)*) => { if !quiet { eprintln!($($arg)*); } };
    }
    let lints = Lints::new(&project.manifest, cli_lints)?;
    if let Some(version) = &compiler.caps.grc {
        progress!("      Using grc {version} (contract {})", compiler.caps.contract);
    }
    let files = input_files(resolution, entry)?;
    let mut diagnostics = preflight(compiler, &files)?;
    progress!("  Collected {} file(s), {} package(s)", files.len(), resolution.packages.len());

    let build_dir = project.build_dir();
    std::fs::create_dir_all(&build_dir)?;
    let ir_path = build_dir.join(format!("{stem}.ll"));
    let output = (want_ir || !compiler.caps.has_phase("check")).then_some(ir_path);
    let (inputs, bundle) = if compiler.caps.multi_file {
        (files.iter().map(|(_, file)| file.clone()).collect::<Vec<_>>(), None)
    } else {
        let bundle = assemble(&files)?;
        let path = bundle.write(&build_dir, stem)?;
        (vec![path], Some(bundle))
    };

    // Freshness: skip the compiler when inputs + compiler identity are
    // unchanged since the last clean (zero-diagnostic) run. Preflight and
    // lints still run every time — they are cheap and their findings must
    // replay.
    let fingerprint = {
        let mut hasher = blake3::Hasher::new();
        match &bundle {
            Some(bundle) => { hasher.update(bundle.text.as_bytes()); }
            None => {
                for input in &inputs {
                    hasher.update(input.to_string_lossy().as_bytes());
                    hasher.update(&std::fs::read(input).unwrap_or_default());
                }
            }
        }
        hasher.update(compiler.identity().as_bytes());
        hasher.update(&[u8::from(output.is_some()), opt.unwrap_or(u8::MAX)]);
        hasher.finalize().to_hex().to_string()
    };
    let fingerprint_path = build_dir.join(format!("{stem}.fingerprint"));
    let outputs_present = output.as_deref().map(|o| o.is_file()).unwrap_or(true);
    if outputs_present
        && std::fs::read_to_string(&fingerprint_path).ok().as_deref() == Some(&fingerprint)
    {
        lints.apply(&mut diagnostics);
        if !quiet {
            for diagnostic in &diagnostics {
                eprintln!("{}", diagnostic.render());
            }
        }
        let success = diagnostics.iter().all(|d| d.severity != Severity::Error);
        progress!("      Fresh {stem}");
        return Ok(Compiled { ir: output, diagnostics, passthrough: String::new(), success });
    }

    progress!("  Compiling {}", project.manifest.project.name);
    let mut report = compiler.compile(&inputs, output.as_deref(), opt)?;
    if report.success && report.diagnostics.is_empty() {
        let _ = std::fs::write(&fingerprint_path, &fingerprint);
    } else {
        let _ = std::fs::remove_file(&fingerprint_path);
    }
    if let (Some(bundle), Some(bundle_path)) = (&bundle, inputs.first()) {
        for diagnostic in &mut report.diagnostics {
            diagnostic.remap(bundle_path, &bundle.segments);
        }
    }
    diagnostics.append(&mut report.diagnostics);
    lints.apply(&mut diagnostics);

    if !quiet {
        for diagnostic in &diagnostics {
            eprintln!("{}", diagnostic.render());
        }
        if !report.passthrough.is_empty() {
            eprint!("{}", report.passthrough);
        }
    }
    let success = report.success && diagnostics.iter().all(|d| d.severity != Severity::Error);
    if !success && bundle.is_some() && diagnostics.is_empty() {
        // The legacy renderer printed spans into the concatenation.
        progress!(
            "note: diagnostics reference the assembled bundle; consult {}/{stem}.map.json \
             to map its lines back to the original files",
            build_dir.display()
        );
    }
    Ok(Compiled { ir: output, diagnostics, passthrough: report.passthrough, success })
}

fn compile_ok(
    project: &Project,
    resolution: &Resolution,
    compiler: &Compiler,
    opts: CompileOptions,
    cli_lints: &[(String, LintLevel)],
) -> Result<Option<PathBuf>> {
    let compiled = compile(project, resolution, compiler, opts, cli_lints)?;
    if !compiled.success {
        bail!("compilation failed");
    }
    Ok(compiled.ir)
}

/// Cross-package name-collision preflight over the flat namespace, returned
/// as diagnostics (lint-adjustable). Findings from the compiler's own
/// interface scan are errors (GRAND001); findings from the heuristic scanner
/// are warnings only, because it can misclassify. Shadowing the standard
/// library warns (GRAND002).
fn preflight(compiler: &Compiler, files: &[(String, PathBuf)]) -> Result<Vec<Diagnostic>> {
    let mut groups: Vec<(String, Vec<PathBuf>)> = Vec::new();
    for (package, file) in files {
        match groups.last_mut() {
            Some((name, paths)) if name == package => paths.push(file.clone()),
            _ => groups.push((package.clone(), vec![file.clone()])),
        }
    }
    let std_declarations = compiler.std_interfaces()?;
    if groups.len() < 2 && std_declarations.is_empty() {
        return Ok(Vec::new());
    }

    let mut authoritative = true;
    let mut seen: std::collections::HashMap<String, (String, Declaration)> = Default::default();
    let mut findings = Vec::new();
    for (package, paths) in &groups {
        let declarations = match compiler.interfaces(paths)? {
            Some(declarations) => declarations,
            None => {
                authoritative = false;
                let mut declarations = Vec::new();
                for path in paths {
                    let text = std::fs::read_to_string(path)
                        .with_context(|| format!("reading {}", path.display()))?;
                    declarations.extend(crate::scan::scan(path, &text));
                }
                declarations
            }
        };
        for declaration in declarations {
            if declaration.kind == DeclarationKind::Fixity {
                continue;
            }
            if std_declarations.iter().any(|s| s.name == declaration.name) {
                findings.push(diagnostic(
                    Severity::Warning,
                    "GRAND002",
                    format!("`{}` shadows a standard-library name", declaration.name),
                    &[(&declaration, "shadowing declaration")],
                ));
            }
            match seen.get(&declaration.name) {
                Some((other_package, other)) if other_package != package => {
                    let severity = if authoritative { Severity::Error } else { Severity::Warning };
                    findings.push(diagnostic(
                        severity,
                        "GRAND001",
                        format!(
                            "`{}` is defined by both `{other_package}` and `{package}`",
                            declaration.name
                        ),
                        &[(other, "first defined here"), (&declaration, "also defined here")],
                    ));
                }
                Some(_) => {} // same-package duplicates are the compiler's to report
                None => {
                    seen.insert(declaration.name.clone(), (package.clone(), declaration));
                }
            }
        }
    }
    Ok(findings)
}

fn diagnostic(
    severity: Severity,
    code: &str,
    title: String,
    sites: &[(&Declaration, &str)],
) -> Diagnostic {
    Diagnostic {
        severity,
        code: Some(code.into()),
        title,
        labels: sites
            .iter()
            .map(|(declaration, message)| crate::contract::Label {
                file: declaration.file.clone(),
                line: Some(declaration.line),
                col: None,
                start_byte: None,
                end_byte: None,
                message: Some((*message).into()),
            })
            .collect(),
        note: Some("the flat namespace requires unique top-level names".into()),
        help: None,
        fix: None,
    }
}

fn build_artifact(
    project: &Project,
    resolution: &Resolution,
    compiler: &Compiler,
    target: Target,
    entry: Option<&Path>,
    stem: &str,
    opt: Option<u8>,
    cli_lints: &[(String, LintLevel)],
) -> Result<Artifact> {
    if let Some(minimum) = project.manifest.backend.as_ref().and_then(|b| b.minimum_version) {
        crate::target::check_toolchain(minimum)?;
    }
    let opts = CompileOptions { entry, stem, want_ir: true, quiet: false, opt };
    let ir = compile_ok(project, resolution, compiler, opts, cli_lints)?
        .expect("want_ir always yields an output path");
    let runtime = discover_runtime(&project.root)?;
    let artifact = materialize(target, &ir, &runtime, &project.build_dir(), stem)?;
    eprintln!("   Finished {} -> {}", stem, artifact.path().display());
    Ok(artifact)
}

// ---------------------------------------------------------------------------
// Commands

pub fn build(target: Target, opt: Option<u8>, cli_lints: &[(String, LintLevel)]) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let stem = project.manifest.project.name.clone();
    build_artifact(&project, &resolution, &compiler, target, None, &stem, opt, cli_lints)?;
    Ok(())
}

pub fn check(cli_lints: &[(String, LintLevel)]) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    // Uses `--phase check` when the compiler supports it; legacy compilers
    // compile to IR which is simply discarded.
    let opts = CompileOptions { entry: None, stem: "check", want_ir: false, quiet: false, opt: None };
    compile_ok(&project, &resolution, &compiler, opts, cli_lints)?;
    eprintln!("    Checked {}", project.manifest.project.name);
    Ok(())
}

pub fn run(
    target: Target,
    arguments: Vec<String>,
    opt: Option<u8>,
    cli_lints: &[(String, LintLevel)],
) -> Result<i32> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let stem = project.manifest.project.name.clone();
    let artifact =
        build_artifact(&project, &resolution, &compiler, target, None, &stem, opt, cli_lints)?;
    artifact.execute(&arguments)
}

fn discover_tests(dir: &Path, filter: Option<&str>) -> Result<Vec<PathBuf>> {
    let mut tests = Vec::new();
    if dir.is_dir() {
        for entry in walkdir::WalkDir::new(dir).sort_by_file_name() {
            let entry = entry?;
            let path = entry.path();
            if !entry.file_type().is_file() || path.extension().is_none_or(|e| e != "gr") {
                continue;
            }
            let name = path.file_stem().unwrap_or_default().to_string_lossy();
            if filter.is_none_or(|f| name.contains(f)) {
                tests.push(entry.into_path());
            }
        }
    }
    Ok(tests)
}

/// Run tests. Each `tests/*.gr` is its own executable (package sources minus
/// the root entry + the test file providing `main`; exit 0 passes), built and
/// run in parallel. `tests/compile-fail/*.gr` must FAIL to compile and their
/// rendered diagnostics must match a sibling `.stderr` golden file
/// (`--bless` rewrites the goldens). `filter` selects tests by substring.
pub fn test(
    target: Target,
    filter: Option<&str>,
    bless: bool,
    cli_lints: &[(String, LintLevel)],
) -> Result<i32> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let tests_dir = project.root.join("tests");
    let compile_fail_dir = tests_dir.join("compile-fail");
    let mut run_tests = discover_tests(&tests_dir, filter)?;
    run_tests.retain(|t| !t.starts_with(&compile_fail_dir));
    let fail_tests = discover_tests(&compile_fail_dir, filter)?;
    if run_tests.is_empty() && fail_tests.is_empty() {
        eprintln!("no tests found under {}", tests_dir.display());
        return Ok(0);
    }

    // Pre-build the shared runtime once: parallel materializations must not
    // race on compiling libgrandiose-runtime.so.
    if !run_tests.is_empty() {
        let runtime = discover_runtime(&project.root)?;
        crate::target::ensure_runtime(&runtime, &project.build_dir())?;
    }

    let failures = std::sync::atomic::AtomicUsize::new(0);
    let queue = std::sync::Mutex::new(run_tests.iter().cloned().collect::<Vec<_>>());
    let workers = std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4).min(8);
    std::thread::scope(|scope| {
        for _ in 0..workers.min(run_tests.len().max(1)) {
            scope.spawn(|| loop {
                let Some(test) = queue.lock().unwrap().pop() else { break };
                let name = test.file_stem().unwrap().to_string_lossy().to_string();
                let stem = format!("test-{name}");
                let outcome = build_artifact(
                    &project, &resolution, &compiler, target, Some(&test), &stem, None, cli_lints,
                )
                .and_then(|artifact| artifact.execute(&[]));
                match outcome {
                    Ok(0) => eprintln!("test {name} ... ok"),
                    Ok(code) => {
                        eprintln!("test {name} ... FAILED (exit code {code})");
                        failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                    Err(error) => {
                        eprintln!("test {name} ... FAILED ({error:#})");
                        failures.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                    }
                }
            });
        }
    });
    let mut failed = failures.into_inner();

    for test in &fail_tests {
        let name = test.file_stem().unwrap().to_string_lossy();
        let stem = format!("cf-{name}");
        let opts = CompileOptions { entry: Some(test), stem: &stem, want_ir: false, quiet: true, opt: None };
        let compiled = compile(&project, &resolution, &compiler, opts, cli_lints)?;
        if compiled.success {
            eprintln!("test compile-fail/{name} ... FAILED (compiled successfully)");
            failed += 1;
            continue;
        }
        let mut rendered = compiled
            .diagnostics
            .iter()
            .map(|d| d.render())
            .collect::<Vec<_>>()
            .join("\n");
        if !compiled.passthrough.is_empty() {
            rendered.push_str(&compiled.passthrough);
        }
        rendered.push('\n');
        // Normalize machine-specific paths so goldens are portable.
        let rendered = rendered.replace(&project.root.display().to_string(), "$ROOT");
        let golden_path = test.with_extension("stderr");
        if bless {
            std::fs::write(&golden_path, &rendered)?;
            eprintln!("test compile-fail/{name} ... blessed");
            continue;
        }
        let golden = std::fs::read_to_string(&golden_path).unwrap_or_default();
        if golden.trim_end() == rendered.trim_end() {
            eprintln!("test compile-fail/{name} ... ok");
        } else {
            eprintln!(
                "test compile-fail/{name} ... FAILED (diagnostics differ; \
                 run `grand test --bless` to update)\n--- expected\n{golden}\n--- actual\n{rendered}"
            );
            failed += 1;
        }
    }

    let total = run_tests.len() + fail_tests.len();
    eprintln!("{} passed, {failed} failed", total - failed);
    Ok(if failed == 0 { 0 } else { 1 })
}

/// Apply machine-applicable fixes from diagnostics (`Diagnostic.fix` in the
/// compiler contract), most-recent-first per file so byte offsets stay valid,
/// then re-check to confirm the project still compiles.
pub fn fix(cli_lints: &[(String, LintLevel)]) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let opts = CompileOptions { entry: None, stem: "fix", want_ir: false, quiet: false, opt: None };
    let compiled = compile(&project, &resolution, &compiler, opts, cli_lints)?;
    let mut by_file: BTreeMap<PathBuf, Vec<Fix>> = BTreeMap::new();
    for fix in compiled.diagnostics.iter().filter_map(|d| d.fix.clone()) {
        by_file.entry(fix.file.clone()).or_default().push(fix);
    }
    if by_file.is_empty() {
        eprintln!("nothing to fix");
        return if compiled.success { Ok(()) } else { bail!("compilation failed") };
    }
    let mut applied = 0;
    for (file, mut fixes) in by_file {
        fixes.sort_by(|a, b| b.start_byte.cmp(&a.start_byte));
        let mut text = std::fs::read_to_string(&file)
            .with_context(|| format!("reading {}", file.display()))?;
        let mut previous_start = usize::MAX;
        for fix in fixes {
            if fix.end_byte > previous_start || fix.end_byte > text.len() {
                eprintln!("warning: skipping overlapping fix in {}", file.display());
                continue;
            }
            text.replace_range(fix.start_byte..fix.end_byte, &fix.replacement);
            previous_start = fix.start_byte;
            applied += 1;
        }
        std::fs::write(&file, text)?;
        eprintln!("      Fixed {}", file.display());
    }
    eprintln!("    Applied {applied} fix(es)");
    let after = compile(&project, &resolution, &compiler, opts, cli_lints)?;
    if !after.success {
        bail!("fixes applied, but the project still fails to compile");
    }
    Ok(())
}

/// Generate API documentation from interface scans (the compiler's when
/// available, the heuristic scanner otherwise) into target/grand/doc.
pub fn doc(open: bool) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let mut html = String::from(
        "<!doctype html><meta charset=\"utf-8\"><title>grandiose docs</title><style>\
         body{font:15px/1.5 system-ui;max-width:60rem;margin:2rem auto;padding:0 1rem}\
         h1{border-bottom:1px solid #ccc}kbd{background:#eee;border-radius:3px;padding:0 .3rem;\
         font-size:.8em}pre{background:#f6f6f6;padding:.5rem;border-radius:4px}\
         p.docs{margin:.2rem 0 1rem;color:#333}</style>\n",
    );
    for package in &resolution.packages {
        let mut paths = package_sources(package)?;
        if let Some(entry) = &package.manifest.project.entry {
            paths.push(package.root.join(entry));
        }
        let declarations = match compiler.interfaces(&paths)? {
            Some(declarations) => declarations,
            None => {
                let mut declarations = Vec::new();
                for path in &paths {
                    let text = std::fs::read_to_string(path)
                        .with_context(|| format!("reading {}", path.display()))?;
                    declarations.extend(crate::scan::scan(path, &text));
                }
                declarations
            }
        };
        html.push_str(&format!("<h1>{}</h1>\n", escape(&package.name)));
        for declaration in declarations {
            if declaration.kind == DeclarationKind::Fixity {
                continue;
            }
            html.push_str(&format!(
                "<h3>{} <kbd>{:?}</kbd></h3>\n",
                escape(&declaration.name),
                declaration.kind
            ));
            if let Some(signature) = &declaration.signature {
                html.push_str(&format!("<pre>{}</pre>\n", escape(signature)));
            }
            if let Some(docs) = &declaration.docs {
                html.push_str(&format!("<p class=\"docs\">{}</p>\n", escape(docs)));
            }
        }
    }
    let doc_dir = project.build_dir().join("doc");
    std::fs::create_dir_all(&doc_dir)?;
    let index = doc_dir.join("index.html");
    std::fs::write(&index, html)?;
    eprintln!(" Documented {} -> {}", project.manifest.project.name, index.display());
    if open {
        let _ = std::process::Command::new("xdg-open").arg(&index).spawn();
    }
    Ok(())
}

/// Format the root package's sources (src + entry + tests), or explicit
/// paths. `check` reports instead of rewriting (exit via Err). Dependencies
/// are never formatted — their formatting is their author's business.
pub fn fmt(check: bool, paths: Vec<PathBuf>) -> Result<()> {
    let files = if paths.is_empty() {
        let project = Project::locate()?;
        let (_, manifest) = (&project.root, &project.manifest);
        let mut files = Vec::new();
        let mut roots: Vec<PathBuf> = manifest
            .project
            .sources
            .clone()
            .unwrap_or_else(|| vec!["src".into()])
            .iter()
            .map(|s| project.root.join(s))
            .collect();
        roots.push(project.root.join("tests"));
        for root in roots {
            if root.is_file() {
                files.push(root);
                continue;
            }
            if !root.is_dir() {
                continue;
            }
            for entry in walkdir::WalkDir::new(&root).sort_by_file_name() {
                let entry = entry?;
                if entry.file_type().is_file() && entry.path().extension().is_some_and(|e| e == "gr") {
                    files.push(entry.into_path());
                }
            }
        }
        if let Some(entry) = &manifest.project.entry {
            files.push(project.root.join(entry));
        }
        files.sort();
        files.dedup();
        files
    } else {
        paths
    };

    let mut dirty = Vec::new();
    for file in &files {
        let source = std::fs::read_to_string(file)
            .with_context(|| format!("reading {}", file.display()))?;
        let formatted = match grandfmt::format(&source) {
            Ok(formatted) => formatted,
            Err(error) => {
                eprintln!("warning: skipping {}: {error}", file.display());
                continue;
            }
        };
        if formatted != source {
            if check {
                eprintln!("would reformat {}", file.display());
            } else {
                std::fs::write(file, formatted)?;
                eprintln!("  Formatted {}", file.display());
            }
            dirty.push(file.clone());
        }
    }
    if check && !dirty.is_empty() {
        bail!("{} file(s) need formatting", dirty.len());
    }
    if dirty.is_empty() {
        eprintln!("{} file(s) already formatted", files.len());
    }
    Ok(())
}

/// Format stdin to stdout (editor integration).
pub fn fmt_stdin() -> Result<()> {
    let mut source = String::new();
    std::io::Read::read_to_string(&mut std::io::stdin(), &mut source)?;
    let formatted = grandfmt::format(&source).map_err(|e| anyhow::anyhow!("{e}"))?;
    print!("{formatted}");
    Ok(())
}

fn escape(text: &str) -> String {
    text.replace('&', "&amp;").replace('<', "&lt;").replace('>', "&gt;")
}

pub fn new(name: &str) -> Result<()> {
    if !valid_package_name(name) {
        bail!("`{name}` is not a valid package name (expected [a-z][a-z0-9-]*)");
    }
    let root = PathBuf::from(name);
    if root.exists() {
        bail!("{} already exists", root.display());
    }
    std::fs::create_dir_all(root.join("src"))?;
    scaffold(&root, name)?;
    eprintln!("    Created `{name}`");
    Ok(())
}

pub fn init() -> Result<()> {
    let cwd = std::env::current_dir()?;
    if cwd.join(MANIFEST_NAME).exists() {
        bail!("{MANIFEST_NAME} already exists here");
    }
    let name = cwd
        .file_name()
        .map(|n| n.to_string_lossy().to_lowercase().replace('_', "-"))
        .filter(|n| valid_package_name(n))
        .context("directory name is not a usable package name; use `grand new <name>` instead")?;
    std::fs::create_dir_all(cwd.join("src"))?;
    scaffold(&cwd, &name)?;
    eprintln!("    Created `{name}`");
    Ok(())
}

fn scaffold(root: &Path, name: &str) -> Result<()> {
    std::fs::write(
        root.join(MANIFEST_NAME),
        format!(
            "[project]\nname = \"{name}\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n\n\
             [backend]\nkind = \"llvm\"\nminimum-version = 18\n"
        ),
    )?;
    let main = root.join("src").join("main.gr");
    if !main.exists() {
        std::fs::write(main, "main() -> i64 {\n    0\n}\n")?;
    }
    let gitignore = root.join(".gitignore");
    if !gitignore.exists() {
        std::fs::write(gitignore, "/target\n")?;
    }
    Ok(())
}

pub struct AddSpec {
    pub name: String,
    pub path: Option<String>,
    pub git: Option<String>,
    pub github: Option<String>,
    pub tag: Option<String>,
    pub rev: Option<String>,
    pub branch: Option<String>,
}

/// Add or replace a `[dependencies]` entry, preserving manifest formatting,
/// then re-resolve so the lockfile picks it up (and roll back on failure).
pub fn add(spec: AddSpec) -> Result<()> {
    let project = Project::locate()?;
    let manifest_path = project.root.join(MANIFEST_NAME);
    let original = std::fs::read_to_string(&manifest_path)?;
    let mut document: toml_edit::DocumentMut = original.parse().context("parsing grandiose.toml")?;

    let mut entry = toml_edit::InlineTable::new();
    let mut set = |key: &str, value: &Option<String>| {
        if let Some(value) = value {
            entry.insert(key, value.as_str().into());
        }
    };
    set("path", &spec.path);
    set("git", &spec.git);
    set("github", &spec.github);
    set("tag", &spec.tag);
    set("rev", &spec.rev);
    set("branch", &spec.branch);
    document
        .entry("dependencies")
        .or_insert(toml_edit::table())
        .as_table_mut()
        .context("[dependencies] is not a table")?
        .insert(&spec.name, toml_edit::value(entry));
    std::fs::write(&manifest_path, document.to_string())?;

    match load_and_resolve(None) {
        Ok(_) => {
            eprintln!("      Added `{}`", spec.name);
            Ok(())
        }
        Err(error) => {
            std::fs::write(&manifest_path, original)?;
            Err(error.context(format!("could not add `{}`; manifest restored", spec.name)))
        }
    }
}

pub fn update(packages: Vec<String>) -> Result<()> {
    load_and_resolve(Some(packages))?;
    eprintln!("    Resolved dependencies");
    Ok(())
}

pub fn lock() -> Result<()> {
    load_and_resolve(None)?;
    eprintln!("    {LOCK_NAME} is up to date");
    Ok(())
}

/// Copy resolved git dependencies into ./vendor for offline, hermetic builds.
/// Vendored copies take precedence over the cache on the next resolution.
pub fn vendor() -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let vendor_dir = project.root.join("vendor");
    let mut count = 0;
    for package in &resolution.packages {
        if package.commit.is_none() {
            continue; // root and path deps stay where they are
        }
        let destination = vendor_dir.join(&package.name);
        let _ = std::fs::remove_dir_all(&destination);
        copy_dir(&package.root, &destination)?;
        eprintln!("   Vendored {} ({})", package.name, destination.display());
        count += 1;
    }
    if count == 0 {
        eprintln!("nothing to vendor (no git dependencies)");
    }
    Ok(())
}

pub fn clean(cache: bool) -> Result<()> {
    let project = Project::locate()?;
    let build_dir = project.build_dir();
    if build_dir.exists() {
        std::fs::remove_dir_all(&build_dir)?;
        eprintln!("     Removed {}", build_dir.display());
    }
    if cache {
        let cache_dir = crate::util::cache_root()?;
        if cache_dir.exists() {
            std::fs::remove_dir_all(&cache_dir)?;
            eprintln!("     Removed {}", cache_dir.display());
        }
    }
    Ok(())
}
