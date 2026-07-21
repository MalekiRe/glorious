//! Tests for the future-compiler contract paths: capability probing,
//! multi-file input, check-only phase, structured diagnostics (including
//! bundle-to-source remapping), interface scans, and collision preflight.
//! The "compiler" is either a bash mock implementing the subprocess protocol
//! (tests the real wire format) or the in-process fake with GRAND_FAKE_CAPS.

use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

struct Sandbox {
    dir: TempDir,
    root: PathBuf,
}

impl Sandbox {
    fn new() -> Sandbox {
        let dir = TempDir::new().unwrap();
        let root = dir.path().join("work");
        std::fs::create_dir_all(&root).unwrap();
        Sandbox { dir, root }
    }

    /// Install a bash mock of the future grc advertising `caps` (JSON).
    /// Every invocation is appended to `args.log`; sources containing
    /// `MOCK_FAIL` produce a structured diagnostic at the marker line.
    fn install_mock_grc(&self, caps: &str) -> PathBuf {
        let dir = self.dir.path();
        std::fs::write(dir.join("caps.json"), caps).unwrap();
        let script = dir.join("mock-grc");
        std::fs::write(
            &script,
            r#"#!/usr/bin/env bash
dir="$(cd "$(dirname "$0")" && pwd)"
echo "$@" >> "$dir/args.log"
if [ "$1" = --capabilities ]; then cat "$dir/caps.json"; exit 0; fi
if [ "$1" = --emit ] && [ "$2" = std-interfaces-json ]; then echo '[]'; exit 0; fi
out=""; inputs=()
while [ $# -gt 0 ]; do
  case "$1" in
    --diagnostics|--phase|--emit) shift;;
    -o) out="$2"; shift;;
    *) inputs+=("$1");;
  esac
  shift
done
for f in "${inputs[@]}"; do
  n="$(grep -n MOCK_FAIL "$f" | head -1 | cut -d: -f1)"
  if [ -n "$n" ]; then
    printf '{"severity":"error","code":"GRC0001","title":"mock failure","labels":[{"file":"%s","line":%s,"message":"here"}]}\n' "$f" "$n" >&2
    exit 1
  fi
done
if [ -n "$out" ]; then printf 'define i32 @main() {\nentry:\n  ret i32 0\n}\n' > "$out"; fi
exit 0
"#,
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
    }

    fn args_log(&self) -> String {
        std::fs::read_to_string(self.dir.path().join("args.log")).unwrap_or_default()
    }

    fn grand(&self, cwd: &Path, compiler: &str, caps: &str, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .args(args)
            .current_dir(cwd)
            .env("GRAND_COMPILER", compiler)
            .env("GRAND_FAKE_CAPS", caps)
            .env("GRAND_CACHE_DIR", self.dir.path().join("cache"))
            .output()
            .unwrap()
    }

    fn app(&self) -> PathBuf {
        let output = self.grand(&self.root, "fake", "", &["new", "app"]);
        assert!(output.status.success());
        self.root.join("app")
    }
}

fn write(path: &Path, content: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, content).unwrap();
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

fn add_path_dep(app: &Path, name: &str, body: &str) {
    let dep = app.parent().unwrap().join(name);
    write(
        &dep.join("grandiose.toml"),
        &format!("[project]\nname = \"{name}\"\nversion = \"0.1.0\"\n"),
    );
    write(&dep.join("src/lib.gr"), body);
    write(
        &app.join("grandiose.toml"),
        &format!(
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n\n\
             [dependencies]\n{name} = {{ path = \"../{name}\" }}\n"
        ),
    );
}

#[test]
fn mock_grc_multi_file_and_check_phase() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"9.9.9","contract":1,"multi-file":true,"phases":["check"],"emit":[],"diagnostics-json":true}"#,
    );
    let app = sandbox.app();
    add_path_dep(&app, "util", "util_value() -> i64 { 3 }\n");
    let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let log = stderr(&output);
    assert!(output.status.success(), "check failed: {log}");
    assert!(log.contains("Using grc 9.9.9 (contract 1)"), "no version line: {log}");
    // Multi-file: both real source files passed, --phase check used, no bundle.
    let args = sandbox.args_log();
    let compile_line = args.lines().last().unwrap();
    assert!(compile_line.contains("--phase check"), "no check phase: {compile_line}");
    assert!(
        compile_line.contains("lib.gr") && compile_line.contains("main.gr"),
        "sources not passed individually: {compile_line}"
    );
    assert!(!app.join("target/grand/check.gr").exists(), "bundle written despite multi-file");
}

#[test]
fn mock_grc_diagnostics_remap_through_bundle() {
    let sandbox = Sandbox::new();
    // No multi-file: grand must bundle, then remap diagnostics back out.
    let grc = sandbox.install_mock_grc(r#"{"grc":"9.9.9","contract":1,"diagnostics-json":true}"#);
    let app = sandbox.app();
    add_path_dep(&app, "util", "util_value() -> i64 { 3 }\n");
    write(&app.join("src/main.gr"), "main() -> i64 {\n    MOCK_FAIL\n}\n");
    let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    // The mock reported bundle line 3 (util's line + main's line 2); grand
    // must render the original file and line, not the bundle.
    assert!(log.contains("error[GRC0001]: mock failure"), "diagnostic not rendered: {log}");
    assert!(
        log.contains("src/main.gr:2"),
        "diagnostic not remapped to the original file/line: {log}"
    );
    assert!(!log.contains("check.gr"), "diagnostic still points into the bundle: {log}");
}

#[test]
fn fake_structured_diagnostics_remap() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("src/helpers.gr"), "helper() -> i64 { 1 }\n");
    write(&app.join("src/main.gr"), "main() -> i64 {\n    FAKE_ERROR\n}\n");
    let output = sandbox.grand(&app, "fake", "diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("error[GRC9999]: fake error marker"), "unexpected: {log}");
    assert!(log.contains("src/main.gr:2"), "not remapped: {log}");
}

#[test]
fn fake_multi_file_points_at_real_files_directly() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("src/main.gr"), "main() -> i64 {\n    FAKE_ERROR\n}\n");
    let output = sandbox.grand(&app, "fake", "multi-file,check,diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("src/main.gr:2"), "unexpected: {log}");
    assert!(!app.join("target/grand/check.gr").exists(), "bundle written despite multi-file");
}

#[test]
fn collision_preflight_warns_heuristically_and_errors_authoritatively() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "shared() -> i64 { 3 }\n");
    write(&app.join("src/helpers.gr"), "shared() -> i64 { 4 }\n");

    // Heuristic scanner (no interfaces capability): warning, build proceeds.
    let output = sandbox.grand(&app, "fake", "", &["check"]);
    let log = stderr(&output);
    assert!(output.status.success(), "heuristic finding must not block: {log}");
    assert!(
        log.contains("warning[GRAND001]: `shared` is defined by both `util` and `app`"),
        "missing heuristic collision warning: {log}"
    );

    // Authoritative interface scan: hard error before compiling.
    let output = sandbox.grand(&app, "fake", "interfaces", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success(), "authoritative collision must fail: {log}");
    assert!(log.contains("error[GRAND001]: `shared` is defined by both"), "unexpected: {log}");
    assert!(log.contains("first defined here"), "labels missing: {log}");
}

#[test]
fn lint_levels_allow_and_deny() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "shared() -> i64 { 3 }\n");
    write(&app.join("src/helpers.gr"), "shared() -> i64 { 4 }\n");

    // Deny escalates the heuristic collision warning to a build-stopping error.
    let output = sandbox.grand(&app, "fake", "", &["check", "--deny", "GRAND001"]);
    assert!(!output.status.success(), "deny must fail: {}", stderr(&output));
    assert!(stderr(&output).contains("error[GRAND001]"), "unexpected: {}", stderr(&output));

    // --deny warnings catches it too; --allow silences it entirely.
    let output = sandbox.grand(&app, "fake", "", &["check", "--deny", "warnings"]);
    assert!(!output.status.success());
    let output = sandbox.grand(&app, "fake", "", &["check", "--allow", "GRAND001"]);
    let log = stderr(&output);
    assert!(output.status.success() && !log.contains("GRAND001"), "allow failed: {log}");

    // Manifest [lints] works without CLI flags.
    let manifest = std::fs::read_to_string(app.join("grandiose.toml")).unwrap();
    write(&app.join("grandiose.toml"), &format!("{manifest}\n[lints]\nGRAND001 = \"deny\"\n"));
    let output = sandbox.grand(&app, "fake", "", &["check"]);
    assert!(!output.status.success(), "manifest deny ignored: {}", stderr(&output));
    // CLI overrides the manifest.
    let output = sandbox.grand(&app, "fake", "", &["check", "--allow", "GRAND001"]);
    assert!(output.status.success(), "CLI override failed: {}", stderr(&output));
}

#[test]
fn fix_applies_machine_fixes_and_reverifies() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.gr"),
        "main() -> i64 {\n    FAKE_FIXME0\n}\n".replace("FAKE_FIXME0", "FAKE_FIXME 0").as_str(),
    );
    let output = sandbox.grand(&app, "fake", "diagnostics", &["fix"]);
    let log = stderr(&output);
    assert!(output.status.success(), "fix failed: {log}");
    assert!(log.contains("Applied 1 fix(es)"), "unexpected: {log}");
    let fixed = std::fs::read_to_string(app.join("src/main.gr")).unwrap();
    assert!(!fixed.contains("FAKE_FIXME"), "marker survived: {fixed}");
    assert!(fixed.contains("main() -> i64"), "file mangled: {fixed}");

    // Nothing left to fix on the second run.
    let output = sandbox.grand(&app, "fake", "diagnostics", &["fix"]);
    assert!(stderr(&output).contains("nothing to fix"));
}

#[test]
fn doc_renders_declarations_and_doc_comments() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "// Adds one to a value.\nadd_one(value: i64) -> i64 { value }\n");
    let output = sandbox.grand(&app, "fake", "", &["doc"]);
    assert!(output.status.success(), "doc failed: {}", stderr(&output));
    let html = std::fs::read_to_string(app.join("target/grand/doc/index.html")).unwrap();
    assert!(html.contains("<h1>util</h1>"), "package section missing");
    assert!(html.contains("add_one"), "declaration missing");
    assert!(html.contains("add_one(value: i64) -&gt; i64"), "signature missing/unescaped: {html}");
    assert!(html.contains("Adds one to a value."), "doc comment missing");
    assert!(html.contains("<h1>app</h1>") && html.contains("main"), "root entry missing");
}

#[test]
fn std_shadowing_warns() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("src/helpers.gr"), "not(value: i64) -> i64 { value }\n");
    let output = sandbox.grand(&app, "fake", "std", &["check"]);
    let log = stderr(&output);
    assert!(output.status.success(), "shadowing is a warning, not an error: {log}");
    assert!(log.contains("`not`") && log.contains("shadows a standard-library name"), "unexpected: {log}");
}
