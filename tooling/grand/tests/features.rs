//! Tests for build caching, workspaces, `grand fmt`, and the test runner
//! (filter + compile-fail goldens), all against executable contract fixtures.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

struct Sandbox {
    dir: TempDir,
    root: PathBuf,
    compiler: PathBuf,
    vm: PathBuf,
}

impl Sandbox {
    fn new() -> Sandbox {
        let dir = TempDir::new().unwrap();
        let root = dir.path().join("work");
        std::fs::create_dir_all(&root).unwrap();
        let compiler = super_install_compiler(dir.path());
        let vm = super_install_vm(dir.path());
        Sandbox {
            dir,
            root,
            compiler,
            vm,
        }
    }

    fn grand(&self, cwd: &Path, _caps: &str, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .args(args)
            .current_dir(cwd)
            .env("GRAND_COMPILER", &self.compiler)
            .env("GRAND_VM", &self.vm)
            .env("GRAND_CACHE_DIR", self.dir.path().join("cache"))
            .output()
            .unwrap()
    }

    fn ok(&self, cwd: &Path, caps: &str, args: &[&str]) -> String {
        let output = self.grand(cwd, caps, args);
        assert!(
            output.status.success(),
            "grand {args:?} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stderr).into_owned()
    }

    fn app(&self) -> PathBuf {
        assert!(self.grand(&self.root, "", &["new", "app"]).status.success());
        self.root.join("app")
    }
}

fn super_install_compiler(dir: &Path) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join("grc");
    std::fs::write(&path, r#"#!/usr/bin/env bash
if [ "$1" = --capabilities ]; then echo '{"grc":"test","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"modules":true,"phases":["resolve","check"],"emit":["bytecode","interfaces-json","std-interfaces-json"],"diagnostics-json":true}'; exit 0; fi
if [ "$1" = --emit ] && [[ "$2" = *interfaces-json ]]; then echo '[]'; exit 0; fi
out=""; inputs=(); while [ $# -gt 0 ]; do case "$1" in --diagnostics|--phase|--emit|--dependency) shift;; -o) out="$2"; shift;; *) inputs+=("$1");; esac; shift; done
for f in "${inputs[@]}"; do n="$(grep -n FAKE_ERROR "$f" | head -1 | cut -d: -f1)"; if [ -n "$n" ]; then printf '{"severity":"error","code":"GRC9999","title":"test error marker","labels":[{"file":"%s","line":%s}]}\n' "$f" "$n" >&2; exit 1; fi; done
if [ -n "$out" ]; then printf 'GRBC' > "$out"; fi
"#).unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    path
}

fn super_install_vm(dir: &Path) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join("grvm");
    std::fs::write(&path, "#!/usr/bin/env bash\nif [ \"$1\" = --capabilities ]; then echo '{\"grvm\":\"test\",\"contract\":1,\"contract-min\":1,\"contract-max\":1,\"artifact-major\":1,\"artifact-minor-min\":0,\"artifact-minor-max\":0}'; fi\nexit 0\n").unwrap();
    std::fs::set_permissions(&path, std::fs::Permissions::from_mode(0o755)).unwrap();
    path
}

fn write(path: &Path, content: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, content).unwrap();
}

fn stderr(output: &Output) -> String {
    String::from_utf8_lossy(&output.stderr).into_owned()
}

#[test]
fn second_build_is_fresh_and_edits_invalidate() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    let first = sandbox.ok(&app, "", &["check"]);
    assert!(first.contains("Compiling"), "{first}");
    let second = sandbox.ok(&app, "", &["check"]);
    assert!(
        second.contains("Fresh check"),
        "second build not cached: {second}"
    );
    assert!(!second.contains("Compiling"), "{second}");
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    1\n}\n",
    );
    let third = sandbox.ok(&app, "", &["check"]);
    assert!(
        third.contains("Compiling"),
        "edit did not invalidate: {third}"
    );
}

#[test]
fn workspaces_share_a_lockfile_and_select_members() {
    let sandbox = Sandbox::new();
    let ws = sandbox.root.join("ws");
    write(
        &ws.join("grandiose.toml"),
        "[workspace]\nmembers = [\"app\", \"util\"]\n",
    );
    write(
        &ws.join("util/grandiose.toml"),
        "[project]\nname = \"util\"\nversion = \"0.1.0\"\n",
    );
    write(
        &ws.join("util/src/lib.glorious"),
        "util_value() -> i64 { 3 }\n",
    );
    write(
        &ws.join("app/grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
         [dependencies]\nutil = { path = \"../util\" }\n",
    );
    write(
        &ws.join("app/src/main.glorious"),
        "main() -> i64 {\n    util_value()\n}\n",
    );

    // Member selection from the workspace root; lockfile lands at the root.
    sandbox.ok(&ws, "", &["-p", "app", "check"]);
    assert!(
        ws.join("grandiose.lock").is_file(),
        "lockfile not at workspace root"
    );
    assert!(
        !ws.join("app/grandiose.lock").exists(),
        "member got its own lockfile"
    );

    // From inside a member the workspace root is still found for the lock.
    sandbox.ok(&ws.join("app"), "", &["check"]);
    // Selecting an unknown member fails with the member list.
    let output = sandbox.grand(&ws, "", &["-p", "nope", "check"]);
    assert!(!output.status.success());
    assert!(
        stderr(&output).contains("members: app, util"),
        "{}",
        stderr(&output)
    );
    // A bare workspace root without -p names the members.
    let output = sandbox.grand(&ws, "", &["check"]);
    assert!(!output.status.success());
    assert!(
        stderr(&output).contains("select a member with -p"),
        "{}",
        stderr(&output)
    );
}

#[test]
fn fmt_normalizes_and_check_reports() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main( ) -> i64 {\n  let x=1 ;\n        finish (x , 2)\n}\n",
    );
    let output = sandbox.grand(&app, "", &["fmt", "--check"]);
    assert!(!output.status.success(), "dirty file passed --check");
    assert!(
        stderr(&output).contains("would reformat"),
        "{}",
        stderr(&output)
    );

    sandbox.ok(&app, "", &["fmt"]);
    let formatted = std::fs::read_to_string(app.join("src/main.glorious")).unwrap();
    assert_eq!(
        formatted,
        "main() -> i64 {\n    let x = 1;\n    finish(x, 2)\n}\n"
    );
    let output = sandbox.grand(&app, "", &["fmt", "--check"]);
    assert!(
        output.status.success(),
        "clean file failed --check: {}",
        stderr(&output)
    );
}

#[test]
fn fmt_refuses_a_malformed_package_transactionally() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    let clean = app.join("src/main.glorious");
    let malformed = app.join("src/other.glorious");
    let original = "main( ) -> i64 { 0 }\n";
    write(&clean, original);
    write(&malformed, "helper( -> i64 { 1 }\n");

    let output = sandbox.grand(&app, "", &["fmt"]);
    assert!(!output.status.success(), "malformed package was formatted");
    assert!(
        stderr(&output).contains("refusing to format"),
        "{}",
        stderr(&output)
    );
    assert_eq!(
        std::fs::read_to_string(clean).unwrap(),
        original,
        "a valid file was modified before the malformed sibling was rejected"
    );
}

#[test]
fn fmt_treats_test_sources_as_independent_executable_roots() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    let alpha = app.join("tests/alpha.glorious");
    let beta = app.join("tests/beta.glorious");
    write(&alpha, "main( )->(){()}\n");
    write(&beta, "main( )->(){()}\n");

    sandbox.ok(&app, "", &["fmt"]);
    assert_eq!(
        std::fs::read_to_string(&alpha).unwrap(),
        "main() -> { () }\n"
    );
    assert_eq!(
        std::fs::read_to_string(&beta).unwrap(),
        "main() -> { () }\n"
    );
    sandbox.ok(&app, "", &["fmt", "--check"]);
}

#[test]
fn fmt_keeps_package_modules_in_the_declared_crate_root_context() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    let main = app.join("src/main.glorious");
    let helper = app.join("src/helper/helper.glorious");
    write(
        &main,
        "mod helper;\nmain( )->i64{crate::helper::answer()}\n",
    );
    write(&helper, "pub answer( )->i64{42}\n");

    sandbox.ok(&app, "", &["fmt"]);
    assert!(
        std::fs::read_to_string(&main)
            .unwrap()
            .contains("crate::helper::answer()")
    );
    assert!(
        std::fs::read_to_string(&helper)
            .unwrap()
            .contains("answer()")
    );
    sandbox.ok(&app, "", &["fmt", "--check"]);
}

#[test]
fn test_runner_filters_and_compile_fail_goldens() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("tests/alpha.glorious"), "main() -> i64 { 0 }\n");
    write(&app.join("tests/beta.glorious"), "main() -> i64 { 0 }\n");
    write(
        &app.join("tests/compile-fail/bad.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );

    // Bless the compile-fail case, then verify it.
    let blessed = sandbox.ok(&app, "diagnostics", &["test", "bad", "--bless"]);
    assert!(
        blessed.contains("compile-fail/bad ... blessed"),
        "{blessed}"
    );
    let golden = std::fs::read_to_string(app.join("tests/compile-fail/bad.stderr")).unwrap();
    assert!(
        golden.contains("test error marker"),
        "golden missing diagnostic: {golden}"
    );
    assert!(
        golden.contains("$ROOT"),
        "golden not path-normalized: {golden}"
    );
    let log = sandbox.ok(&app, "diagnostics", &["test", "bad"]);
    assert!(log.contains("compile-fail/bad ... ok"), "{log}");
    // A drifted golden fails with a diff hint.
    std::fs::write(
        app.join("tests/compile-fail/bad.stderr"),
        "something else\n",
    )
    .unwrap();
    let output = sandbox.grand(&app, "diagnostics", &["test", "bad"]);
    assert!(!output.status.success());
    assert!(stderr(&output).contains("--bless"), "{}", stderr(&output));

    // Restore the golden we deliberately broke above before running unfiltered.
    sandbox.ok(&app, "diagnostics", &["test", "bad", "--bless"]);
    let log = sandbox.ok(&app, "", &["test", "alpha"]);
    assert!(log.contains("test alpha ... ok"), "{log}");
    assert!(!log.contains("beta"), "filter leaked: {log}");
    let log = sandbox.ok(&app, "diagnostics", &["test"]);
    assert!(
        log.contains("test alpha ... ok") && log.contains("test beta ... ok"),
        "{log}"
    );
    assert!(log.contains("compile-fail/bad ... ok"), "{log}");
}

#[test]
fn diagnostics_render_source_snippets() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );
    let output = sandbox.grand(&app, "diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(
        log.contains("    2 |     FAKE_ERROR"),
        "no source snippet: {log}"
    );
    assert!(log.contains("^"), "no caret: {log}");
}
