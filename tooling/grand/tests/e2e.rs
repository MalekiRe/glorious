//! End-to-end tests over the grand binary. The compiler is faked
//! (`GRAND_COMPILER=fake`) so these exercise everything grand owns —
//! scaffolding, resolution, git fetching, lockfiles, bundling — without
//! depending on the in-progress Grandiose compiler or the LLVM toolchain.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tempfile::TempDir;

struct Sandbox {
    _dir: TempDir,
    root: PathBuf,
    cache: PathBuf,
}

impl Sandbox {
    fn new() -> Sandbox {
        let dir = TempDir::new().unwrap();
        let root = dir.path().join("work");
        let cache = dir.path().join("cache");
        std::fs::create_dir_all(&root).unwrap();
        // Empty stand-in for compiler/runtime/native_entry.c: the fake
        // compiler's modules need no runtime symbols.
        std::fs::write(dir.path().join("runtime.c"), "").unwrap();
        Sandbox { _dir: dir, root, cache }
    }

    fn grand_in(&self, cwd: &Path, args: &[&str]) -> Output {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .args(args)
            .current_dir(cwd)
            .env("GRAND_COMPILER", "fake")
            .env("GRAND_CACHE_DIR", &self.cache)
            .env("GRAND_RUNTIME", self._dir.path().join("runtime.c"))
            .output()
            .unwrap()
    }

    fn ok_in(&self, cwd: &Path, args: &[&str]) -> String {
        let output = self.grand_in(cwd, args);
        assert!(
            output.status.success(),
            "grand {args:?} failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
        String::from_utf8_lossy(&output.stderr).into_owned()
    }

    fn fail_in(&self, cwd: &Path, args: &[&str]) -> String {
        let output = self.grand_in(cwd, args);
        assert!(!output.status.success(), "grand {args:?} unexpectedly succeeded");
        String::from_utf8_lossy(&output.stderr).into_owned()
    }
}

fn write(path: &Path, content: &str) {
    std::fs::create_dir_all(path.parent().unwrap()).unwrap();
    std::fs::write(path, content).unwrap();
}

fn lib_package(dir: &Path, name: &str, body: &str) {
    write(
        &dir.join("grandiose.toml"),
        &format!("[project]\nname = \"{name}\"\nversion = \"0.1.0\"\n"),
    );
    write(&dir.join("src").join("lib.gr"), body);
}

fn git(dir: &Path, args: &[&str]) -> String {
    let output = Command::new("git")
        .args(args)
        .current_dir(dir)
        .env("GIT_AUTHOR_NAME", "t")
        .env("GIT_AUTHOR_EMAIL", "t@t")
        .env("GIT_COMMITTER_NAME", "t")
        .env("GIT_COMMITTER_EMAIL", "t@t")
        .output()
        .unwrap();
    assert!(output.status.success(), "git {args:?}: {}", String::from_utf8_lossy(&output.stderr));
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}

fn git_package(sandbox: &Sandbox, name: &str, body: &str) -> PathBuf {
    let repo = sandbox.root.join(format!("{name}-repo"));
    lib_package(&repo, name, body);
    git(&repo, &["init", "-q", "-b", "main"]);
    git(&repo, &["add", "."]);
    git(&repo, &["commit", "-qm", "init"]);
    git(&repo, &["tag", "v1"]);
    repo
}

#[test]
fn scaffold_and_check() {
    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    assert!(app.join("src/main.gr").is_file());
    let log = sandbox.ok_in(&app, &["check"]);
    assert!(log.contains("Checked app"), "unexpected log: {log}");
    // Library-only packages cannot be checked as executables.
    let lib = sandbox.root.join("lib");
    lib_package(&lib, "lib", "helper() -> i64 { 1 }\n");
    let log = sandbox.fail_in(&lib, &["check"]);
    assert!(log.contains("no entry point"), "unexpected log: {log}");
}

#[test]
fn path_dependencies_bundle_in_topological_order() {
    let sandbox = Sandbox::new();
    let deep = sandbox.root.join("deep");
    lib_package(&deep, "deep", "deep_value() -> i64 { 1 }\n");
    let mid = sandbox.root.join("mid");
    lib_package(&mid, "mid", "mid_value() -> i64 { 2 }\n");
    write(
        &mid.join("grandiose.toml"),
        "[project]\nname = \"mid\"\nversion = \"0.1.0\"\n\n[dependencies]\ndeep = { path = \"../deep\" }\n",
    );
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(
        &app.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n\n[dependencies]\nmid = { path = \"../mid\" }\n",
    );
    sandbox.ok_in(&app, &["check"]);

    let bundle = std::fs::read_to_string(app.join("target/grand/check.gr")).unwrap();
    let deep_at = bundle.find("deep_value").unwrap();
    let mid_at = bundle.find("mid_value").unwrap();
    let main_at = bundle.find("main()").unwrap();
    assert!(deep_at < mid_at && mid_at < main_at, "bundle order wrong:\n{bundle}");
    let map = std::fs::read_to_string(app.join("target/grand/check.map.json")).unwrap();
    assert!(map.contains("\"package\": \"deep\""), "segment map missing packages: {map}");
    // Path dependencies do not appear pinned in the lockfile, but exist in it.
    let lock = std::fs::read_to_string(app.join("grandiose.lock")).unwrap();
    assert!(lock.contains("name = \"mid\"") && lock.contains("name = \"deep\""));
    assert!(!lock.contains("commit = "), "path deps must not be pinned: {lock}");
}

#[test]
fn git_dependencies_pin_lock_and_stay_reproducible() {
    let sandbox = Sandbox::new();
    let repo = git_package(&sandbox, "util", "util_value() -> i64 { 3 }\n");
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    let repo_url = repo.display().to_string();
    sandbox.ok_in(&app, &["add", "util", "--git", &repo_url, "--tag", "v1"]);

    let lock = std::fs::read_to_string(app.join("grandiose.lock")).unwrap();
    assert!(lock.contains("tag=v1") && lock.contains("commit = "), "lock not pinned: {lock}");
    assert!(lock.contains("content-hash = \"blake3:"), "lock missing content hash: {lock}");

    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.gr")).unwrap();
    assert!(bundle.contains("util_value"), "git dep missing from bundle:\n{bundle}");

    // Moving the tag upstream must not affect a locked project…
    write(&repo.join("src").join("lib.gr"), "util_value() -> i64 { 4 }\nextra() -> i64 { 5 }\n");
    git(&repo, &["commit", "-qam", "update"]);
    git(&repo, &["tag", "-f", "v1"]);
    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.gr")).unwrap();
    assert!(!bundle.contains("extra"), "locked build picked up unpinned changes");

    // …until an explicit update re-resolves it.
    sandbox.ok_in(&app, &["update", "util"]);
    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.gr")).unwrap();
    assert!(bundle.contains("extra"), "update did not move the pin");
}

#[test]
fn locked_mode_refuses_lockfile_changes() {
    let sandbox = Sandbox::new();
    let repo = git_package(&sandbox, "util", "util_value() -> i64 { 3 }\n");
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(
        &app.join("grandiose.toml"),
        &format!(
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n\n\
             [dependencies]\nutil = {{ git = \"{}\", tag = \"v1\" }}\n",
            repo.display()
        ),
    );
    let output = Command::new(env!("CARGO_BIN_EXE_grand"))
        .args(["check"])
        .current_dir(&app)
        .env("GRAND_COMPILER", "fake")
        .env("GRAND_CACHE_DIR", &sandbox.cache)
        .env("GRAND_LOCKED", "1")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("GRAND_LOCKED"), "unexpected error: {stderr}");
}

#[test]
fn conflicting_sources_and_cycles_are_rejected() {
    let sandbox = Sandbox::new();
    // Two packages that each vendor a different `shared`.
    let shared_a = sandbox.root.join("shared-a");
    lib_package(&shared_a, "shared", "a() -> i64 { 1 }\n");
    let shared_b = sandbox.root.join("shared-b");
    lib_package(&shared_b, "shared", "b() -> i64 { 2 }\n");
    let left = sandbox.root.join("left");
    lib_package(&left, "left", "l() -> i64 { 1 }\n");
    write(
        &left.join("grandiose.toml"),
        "[project]\nname = \"left\"\nversion = \"0.1.0\"\n\n[dependencies]\nshared = { path = \"../shared-a\" }\n",
    );
    let right = sandbox.root.join("right");
    lib_package(&right, "right", "r() -> i64 { 1 }\n");
    write(
        &right.join("grandiose.toml"),
        "[project]\nname = \"right\"\nversion = \"0.1.0\"\n\n[dependencies]\nshared = { path = \"../shared-b\" }\n",
    );
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(
        &app.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n\n\
         [dependencies]\nleft = { path = \"../left\" }\nright = { path = \"../right\" }\n",
    );
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(log.contains("two different sources"), "unexpected error: {log}");

    // A self-cycle through path deps.
    let ouro = sandbox.root.join("ouro");
    lib_package(&ouro, "ouro", "o() -> i64 { 1 }\n");
    write(
        &ouro.join("grandiose.toml"),
        "[project]\nname = \"ouro\"\nversion = \"0.1.0\"\nentry = \"src/lib.gr\"\n\n[dependencies]\nouro2 = { path = \".\" }\n",
    );
    let log = sandbox.fail_in(&ouro, &["check"]);
    assert!(log.contains("cycle") || log.contains("calls itself"), "unexpected error: {log}");
}

#[test]
fn vendored_dependencies_take_precedence() {
    let sandbox = Sandbox::new();
    let repo = git_package(&sandbox, "util", "util_value() -> i64 { 3 }\n");
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    let repo_url = repo.display().to_string();
    sandbox.ok_in(&app, &["add", "util", "--git", &repo_url, "--tag", "v1"]);
    sandbox.ok_in(&app, &["vendor"]);
    assert!(app.join("vendor/util/grandiose.toml").is_file());

    // Wipe the shared cache: the vendored copy must be enough.
    std::fs::remove_dir_all(&sandbox.cache).unwrap();
    let log = sandbox.ok_in(&app, &["check"]);
    assert!(log.contains("vendored"), "vendor copy not used: {log}");
}

#[test]
fn tests_run_as_independent_executables() {
    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(&app.join("tests").join("smoke.gr"), "main() -> i64 { 0 }\n");
    // The fake compiler ignores input and emits an exit-0 module, so this
    // exercises discovery, per-test bundling, materialization, and execution.
    if !has_llvm_toolchain() {
        eprintln!("skipping: llvm-as/lli/clang not available");
        return;
    }
    let log = sandbox.ok_in(&app, &["test"]);
    assert!(log.contains("test smoke ... ok"), "unexpected log: {log}");
    // The test bundle must contain the test file, not the root entry.
    let bundle = std::fs::read_to_string(app.join("target/grand/test-smoke.gr")).unwrap();
    assert_eq!(bundle.matches("main()").count(), 1, "root entry leaked into test bundle");
}

fn has_llvm_toolchain() -> bool {
    ["llvm-as", "lli", "clang"].iter().all(|tool| {
        Command::new(tool)
            .arg("--version")
            .output()
            .map(|o| o.status.success())
            .unwrap_or(false)
    })
}
