use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use anyhow::{Context, Result, bail};

use crate::bundle::{input_files, module_input_files, package_sources};
use crate::compiler::{Compiler, discover_vm};
use crate::contract::{Declaration, DeclarationKind, Diagnostic, Fix, Severity};
use crate::lock::{LOCK_NAME, Lockfile};
use crate::manifest::{MANIFEST_NAME, Manifest};
use crate::resolve::{Resolution, ResolveOptions, resolve};
use crate::target::Artifact;
use crate::util::{copy_dir, is_source_path, valid_package_name};

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
        let (root, manifest, lock_root) = crate::manifest::find_project_in_workspace(&cwd, select)?;
        Ok(Project {
            root,
            manifest,
            lock_root,
        })
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
    let resolution = resolve(
        &project.root,
        &project.manifest,
        previous.as_ref(),
        &options,
    )?;
    let fresh = resolution.to_lockfile();
    let changed = previous
        .as_ref()
        .map(|p| p.packages != fresh.packages)
        .unwrap_or(true);
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
    /// Optimization level, forwarded as `-O<n>`.
    pub opt: Option<u8>,
    /// Identity of the selected execution backend, when artifact emission and
    /// execution must be negotiated as one atomic toolchain.
    pub runtime_identity: Option<&'a str>,
}

/// Compile the resolved project. `entry` substitutes the root entry file
/// (used by `grand test`); `stem` names the outputs; `want_ir = false` lets a
/// check-capable compiler skip emission. Renders diagnostics (lint-adjusted,
/// but does NOT bail
/// on compilation failure — `grand fix` needs the diagnostics; use
/// [`compile_ok`] elsewhere.
fn compile(
    project: &Project,
    resolution: &Resolution,
    compiler: &Compiler,
    opts: CompileOptions,
    cli_lints: &[(String, LintLevel)],
) -> Result<Compiled> {
    let CompileOptions {
        entry,
        stem,
        want_ir,
        quiet,
        opt,
        runtime_identity,
    } = opts;
    macro_rules! progress {
        ($($arg:tt)*) => { if !quiet { eprintln!($($arg)*); } };
    }
    let lints = Lints::new(&project.manifest, cli_lints)?;
    if let Some(version) = &compiler.caps.grc {
        progress!(
            "      Using grc {version} (contract {})",
            compiler.caps.contract
        );
    }
    let watched_files = input_files(resolution, entry)?;
    let files = module_input_files(resolution, entry)?;
    let mut diagnostics = preflight(compiler, &files)?;
    progress!(
        "  Collected {} file(s), {} package(s)",
        files.len(),
        resolution.packages.len()
    );

    let build_dir = project.build_dir();
    std::fs::create_dir_all(&build_dir)?;
    let compiler_output = build_dir.join(format!("{stem}.grbc"));
    let output = want_ir.then_some(compiler_output);
    let primary = files
        .first()
        .map(|(_, file)| file.clone())
        .into_iter()
        .collect::<Vec<_>>();
    let dependencies = files
        .iter()
        .skip(1)
        .map(|(name, file)| (name.clone(), file.clone()))
        .collect::<Vec<_>>();
    let (inputs, dependency_roots) = (primary, dependencies);

    // Freshness: skip the compiler when inputs + compiler identity are
    // unchanged since the last clean (zero-diagnostic) run. Preflight and
    // lints still run every time — they are cheap and their findings must
    // replay.
    let fingerprint = {
        let mut hasher = blake3::Hasher::new();
        for (_, input) in &watched_files {
            hasher.update(input.to_string_lossy().as_bytes());
            hasher.update(&std::fs::read(input).unwrap_or_default());
        }
        hasher.update(compiler.identity().as_bytes());
        if let Some(identity) = runtime_identity {
            hasher.update(identity.as_bytes());
        }
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
        return Ok(Compiled {
            ir: output,
            diagnostics,
            passthrough: String::new(),
            success,
        });
    }

    progress!("  Compiling {}", project.manifest.project.name);
    let mut report = compiler.compile(&inputs, &dependency_roots, output.as_deref(), opt)?;
    if report.success && report.diagnostics.is_empty() {
        let _ = std::fs::write(&fingerprint_path, &fingerprint);
    } else {
        let _ = std::fs::remove_file(&fingerprint_path);
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
    Ok(Compiled {
        ir: output,
        diagnostics,
        passthrough: report.passthrough,
        success,
    })
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
/// interface scan are errors (GRAND001). Shadowing the standard library warns
/// (GRAND002).
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

    let mut seen: std::collections::HashMap<String, (String, Declaration)> = Default::default();
    let mut findings = Vec::new();
    for (package, paths) in &groups {
        let declarations = compiler.interfaces(paths)?;
        for declaration in declarations {
            if matches!(
                declaration.kind,
                DeclarationKind::Fixity | DeclarationKind::Impl
            ) {
                continue;
            }
            if declaration.visibility.as_deref() == Some("private") {
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
            let identity = declaration
                .identity
                .clone()
                .unwrap_or_else(|| declaration.name.clone());
            match seen.get(&identity) {
                Some((other_package, other)) if other_package != package => {
                    findings.push(diagnostic(
                        Severity::Error,
                        "GRAND001",
                        format!(
                            "`{}` is defined by both `{other_package}` and `{package}`",
                            declaration.name
                        ),
                        &[
                            (other, "first defined here"),
                            (&declaration, "also defined here"),
                        ],
                    ));
                }
                Some(_) => {} // same-package duplicates are the compiler's to report
                None => {
                    seen.insert(identity, (package.clone(), declaration));
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
        message: None,
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
        note: Some("a qualified exported identity must be unique across packages".into()),
        help: None,
        fix: None,
    }
}

struct BuildOptions<'a> {
    entry: Option<&'a Path>,
    stem: &'a str,
    opt: Option<u8>,
    cli_lints: &'a [(String, LintLevel)],
}

fn build_artifact(
    project: &Project,
    resolution: &Resolution,
    compiler: &Compiler,
    options: BuildOptions<'_>,
) -> Result<Artifact> {
    let BuildOptions {
        entry,
        stem,
        opt,
        cli_lints,
    } = options;
    let vm = discover_vm(&project.root)?;
    compiler.ensure_seed_compatible(&vm)?;
    let opts = CompileOptions {
        entry,
        stem,
        want_ir: true,
        quiet: false,
        opt,
        runtime_identity: Some(vm.identity()),
    };
    let compiler_output = compile_ok(project, resolution, compiler, opts, cli_lints)?
        .expect("want_ir always yields an output path");
    let artifact = Artifact::bytecode(
        compiler_output,
        vm.path().to_owned(),
        compiler.seed_identity().map(str::to_owned),
    );
    eprintln!("   Finished {} -> {}", stem, artifact.path().display());
    Ok(artifact)
}

// ---------------------------------------------------------------------------
// Commands

pub fn build(opt: Option<u8>, cli_lints: &[(String, LintLevel)]) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let stem = project.manifest.project.name.clone();
    build_artifact(
        &project,
        &resolution,
        &compiler,
        BuildOptions {
            entry: None,
            stem: &stem,
            opt,
            cli_lints,
        },
    )?;
    Ok(())
}

pub fn check(cli_lints: &[(String, LintLevel)]) -> Result<()> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let opts = CompileOptions {
        entry: None,
        stem: "check",
        want_ir: false,
        quiet: false,
        opt: None,
        runtime_identity: None,
    };
    compile_ok(&project, &resolution, &compiler, opts, cli_lints)?;
    eprintln!("    Checked {}", project.manifest.project.name);
    Ok(())
}

pub fn run(
    arguments: Vec<String>,
    opt: Option<u8>,
    cli_lints: &[(String, LintLevel)],
) -> Result<i32> {
    let (project, resolution) = load_and_resolve(None)?;
    let compiler = Compiler::discover(&project.root)?;
    let stem = project.manifest.project.name.clone();
    let artifact = build_artifact(
        &project,
        &resolution,
        &compiler,
        BuildOptions {
            entry: None,
            stem: &stem,
            opt,
            cli_lints,
        },
    )?;
    artifact.execute(&arguments, &project.manifest.runtime.capabilities)
}

fn discover_tests(dir: &Path, filter: Option<&str>) -> Result<Vec<PathBuf>> {
    let mut tests = Vec::new();
    if dir.is_dir() {
        for entry in walkdir::WalkDir::new(dir).sort_by_file_name() {
            let entry = entry?;
            let path = entry.path();
            if !entry.file_type().is_file() || !is_source_path(path) {
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

/// Run tests. Each `tests/*.glorious` is its own executable
/// (package sources minus
/// the root entry + the test file providing `main`; exit 0 passes), built and
/// run in parallel. `tests/compile-fail/*.{glorious,gr}` must FAIL to compile and their
/// rendered diagnostics must match a sibling `.stderr` golden file
/// (`--bless` rewrites the goldens). `filter` selects tests by substring.
pub fn test(filter: Option<&str>, bless: bool, cli_lints: &[(String, LintLevel)]) -> Result<i32> {
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

    let failures = std::sync::atomic::AtomicUsize::new(0);
    let queue = std::sync::Mutex::new(run_tests.to_vec());
    let workers = std::thread::available_parallelism()
        .map(|n| n.get())
        .unwrap_or(4)
        .min(8);
    std::thread::scope(|scope| {
        for _ in 0..workers.min(run_tests.len().max(1)) {
            scope.spawn(|| {
                loop {
                    let Some(test) = queue.lock().unwrap().pop() else {
                        break;
                    };
                    let name = test.file_stem().unwrap().to_string_lossy().to_string();
                    let stem = format!("test-{name}");
                    let outcome = build_artifact(
                        &project,
                        &resolution,
                        &compiler,
                        BuildOptions {
                            entry: Some(&test),
                            stem: &stem,
                            opt: None,
                            cli_lints,
                        },
                    )
                    .and_then(|artifact| {
                        artifact.execute(&[], &project.manifest.runtime.capabilities)
                    });
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
                }
            });
        }
    });
    let mut failed = failures.into_inner();

    for test in &fail_tests {
        let name = test.file_stem().unwrap().to_string_lossy();
        let stem = format!("cf-{name}");
        let opts = CompileOptions {
            entry: Some(test),
            stem: &stem,
            want_ir: false,
            quiet: true,
            opt: None,
            runtime_identity: None,
        };
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
    let opts = CompileOptions {
        entry: None,
        stem: "fix",
        want_ir: false,
        quiet: false,
        opt: None,
        runtime_identity: None,
    };
    let compiled = compile(&project, &resolution, &compiler, opts, cli_lints)?;
    let mut by_file: BTreeMap<PathBuf, Vec<Fix>> = BTreeMap::new();
    for fix in compiled.diagnostics.iter().filter_map(|d| d.fix.clone()) {
        by_file.entry(fix.file.clone()).or_default().push(fix);
    }
    if by_file.is_empty() {
        eprintln!("nothing to fix");
        return if compiled.success {
            Ok(())
        } else {
            bail!("compilation failed")
        };
    }
    let mut applied = 0;
    for (file, mut fixes) in by_file {
        fixes.sort_by_key(|fix| std::cmp::Reverse(fix.start_byte));
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

/// Generate API documentation from compiler interface scans into
/// target/grand/doc.
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
        let declarations = compiler.interfaces(&paths)?;
        html.push_str(&format!("<h1>{}</h1>\n", escape(&package.name)));
        for declaration in declarations {
            if matches!(
                declaration.kind,
                DeclarationKind::Fixity | DeclarationKind::Impl
            ) {
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
    eprintln!(
        " Documented {} -> {}",
        project.manifest.project.name,
        index.display()
    );
    if open {
        let _ = std::process::Command::new("xdg-open").arg(&index).spawn();
    }
    Ok(())
}

/// Format the root package's sources (src + entry + tests), or explicit
/// paths. `check` reports instead of rewriting (exit via Err). Dependencies
/// are never formatted — their formatting is their author's business.
pub fn fmt(check: bool, paths: Vec<PathBuf>) -> Result<()> {
    let package_mode = paths.is_empty();
    let mut package_sources = Vec::new();
    let mut package_entry = None;
    let files = if package_mode {
        let project = Project::locate()?;
        let (_, manifest) = (&project.root, &project.manifest);
        let mut files = Vec::new();
        let roots: Vec<PathBuf> = manifest
            .project
            .sources
            .clone()
            .unwrap_or_else(|| vec!["src".into()])
            .iter()
            .map(|s| project.root.join(s))
            .collect();
        for root in roots {
            if root.is_file() {
                package_sources.push(root);
                continue;
            }
            if !root.is_dir() {
                continue;
            }
            for entry in walkdir::WalkDir::new(&root).sort_by_file_name() {
                let entry = entry?;
                if entry.file_type().is_file() && is_source_path(entry.path()) {
                    package_sources.push(entry.into_path());
                }
            }
        }
        if let Some(entry) = &manifest.project.entry {
            let entry = project.root.join(entry);
            package_sources.push(entry.clone());
            package_entry = Some(entry);
        }
        package_sources.sort();
        package_sources.dedup();
        if package_entry.is_none() {
            let library_roots = package_sources
                .iter()
                .filter(|path| path.file_name().is_some_and(|name| name == "lib.glorious"))
                .cloned()
                .collect::<Vec<_>>();
            package_entry = match (package_sources.as_slice(), library_roots.as_slice()) {
                ([only], _) => Some(only.clone()),
                (_, [library]) => Some(library.clone()),
                _ => None,
            };
        }
        files.extend(package_sources.iter().cloned());

        let tests = project.root.join("tests");
        if tests.is_dir() {
            for entry in walkdir::WalkDir::new(&tests).sort_by_file_name() {
                let entry = entry?;
                if entry.file_type().is_file() && is_source_path(entry.path()) {
                    files.push(entry.into_path());
                }
            }
        }
        files.sort();
        files.dedup();
        files
    } else {
        paths
    };

    let sources = files
        .iter()
        .map(|file| {
            std::fs::read_to_string(file)
                .with_context(|| format!("reading {}", file.display()))
                .map(|source| (file.clone(), source))
        })
        .collect::<Result<Vec<_>>>()?;
    // Parse and lay out every file before writing any of them. A malformed
    // member therefore refuses the whole operation transactionally. Package
    // source files share their module context, while each tests/*.glorious
    // file is an independent executable root and never sees sibling test
    // roots as modules.
    let mut rendered = Vec::with_capacity(sources.len());
    for (index, (file, source)) in sources.iter().enumerate() {
        let is_package_source = package_mode && package_sources.contains(file);
        let context_sources = sources
            .iter()
            .enumerate()
            .filter(|(other, (other_file, _))| {
                if *other == index || !package_mode {
                    return false;
                }
                is_package_source && package_entry.is_some() && package_sources.contains(other_file)
            })
            .filter(|(_, (other_file, _))| {
                !is_package_source || package_entry.as_ref() != Some(other_file)
            })
            .map(|(_, (path, source))| (path.to_string_lossy().into_owned(), source.as_str()))
            .collect::<Vec<_>>();
        let borrowed_context = context_sources
            .iter()
            .map(|(path, source)| (path.as_str(), *source))
            .collect::<Vec<_>>();
        let source_name = file.to_string_lossy();
        let crate_root = is_package_source
            .then_some(package_entry.as_ref())
            .flatten()
            .filter(|entry| *entry != file)
            .and_then(|entry| {
                sources
                    .iter()
                    .find(|(path, _)| path == entry)
                    .map(|(path, source)| (path.to_string_lossy().into_owned(), source.as_str()))
            });
        let formatted = grandfmt::format_with_context(
            source,
            grandfmt::Context {
                source_name: &source_name,
                crate_root: crate_root
                    .as_ref()
                    .map(|(path, source)| (path.as_str(), *source)),
                sources: &borrowed_context,
                ..grandfmt::Context::default()
            },
        )
        .with_context(|| format!("refusing to format {}", file.display()))?;
        rendered.push((file, source, formatted));
    }

    let mut dirty = Vec::new();
    for (file, source, formatted) in rendered {
        if formatted != source.as_str() {
            if check {
                eprintln!("would reformat {}", file.display());
            } else {
                std::fs::write(file, &formatted)?;
                eprintln!("  Formatted {}", file.display());
            }
            dirty.push(file.to_path_buf());
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
    text.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
}

pub fn new(name: &str, requested_root: Option<&Path>) -> Result<()> {
    if !valid_package_name(name) {
        bail!("`{name}` is not a valid package name (expected [a-z][a-z0-9-]*)");
    }
    let default_root = PathBuf::from(name);
    let root = requested_root.unwrap_or(&default_root);
    match std::fs::symlink_metadata(root) {
        Ok(_) => bail!(
            "destination `{}` already exists; use `grand init` to initialize an existing directory",
            root.display()
        ),
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(error)
                .with_context(|| format!("checking destination `{}`", root.display()));
        }
    }
    let parent = root
        .parent()
        .filter(|parent| !parent.as_os_str().is_empty());
    if let Some(parent) = parent {
        std::fs::create_dir_all(parent)
            .with_context(|| format!("creating parent directory `{}`", parent.display()))?;
    }
    // `create_dir`, rather than `create_dir_all`, makes the final existence
    // check atomic and prevents a racing process from having files overwritten.
    std::fs::create_dir(root)
        .with_context(|| format!("creating destination `{}`", root.display()))?;
    let result = (|| {
        std::fs::create_dir(root.join("src"))?;
        scaffold(root, name)
    })();
    if let Err(error) = result {
        // Remove only the deterministic entries this invocation may have
        // created. If another process added anything, the non-recursive final
        // removals fail closed and leave that data intact.
        let _ = std::fs::remove_file(root.join(MANIFEST_NAME));
        let _ = std::fs::remove_file(root.join("src").join("main.glorious"));
        let _ = std::fs::remove_file(root.join(".gitignore"));
        let _ = std::fs::remove_dir(root.join("src"));
        let _ = std::fs::remove_dir(root);
        return Err(error).context("creating package scaffold");
    }
    eprintln!("    Created `{name}` at {}", root.display());
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
            "[project]\nname = \"{name}\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n"
        ),
    )?;
    let main = root.join("src").join("main.glorious");
    if !main.exists() {
        std::fs::write(main, "main() -> () {\n    ()\n}\n")?;
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
    let mut document: toml_edit::DocumentMut =
        original.parse().context("parsing grandiose.toml")?;

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
