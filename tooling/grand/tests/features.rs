//! Tests for build caching, workspaces, `grand fmt`, and the test runner
//! (filter + compile-fail goldens), all against the in-process fake compiler.

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
        std::fs::write(dir.path().join("runtime.c"), "").unwrap();
        Sandbox { dir, root }
    }

    fn grand(&self, cwd: &Path, caps: &str, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .args(args)
            .current_dir(cwd)
            .env("GRAND_COMPILER", "fake")
            .env("GRAND_FAKE_CAPS", caps)
            .env("GRAND_CACHE_DIR", self.dir.path().join("cache"))
            .env("GRAND_RUNTIME", self.dir.path().join("runtime.c"))
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
fn test_runner_filters_and_compile_fail_goldens() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("tests/alpha.glorious"), "main() -> i64 { 0 }\n");
    write(&app.join("tests/beta.glorious"), "main() -> i64 { 0 }\n");
    write(
        &app.join("tests/compile-fail/bad.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );

    // Compile-fail path first (no LLVM toolchain needed): bless, then verify.
    let blessed = sandbox.ok(&app, "diagnostics", &["test", "bad", "--bless"]);
    assert!(
        blessed.contains("compile-fail/bad ... blessed"),
        "{blessed}"
    );
    let golden = std::fs::read_to_string(app.join("tests/compile-fail/bad.stderr")).unwrap();
    assert!(
        golden.contains("fake error marker"),
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

    // Runnable tests need the LLVM toolchain; skip quietly if absent.
    if !["llvm-as", "lli", "clang"].iter().all(|tool| {
        Command::new(tool)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    }) {
        eprintln!("skipping runnable-test half: llvm toolchain missing");
        return;
    }
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
