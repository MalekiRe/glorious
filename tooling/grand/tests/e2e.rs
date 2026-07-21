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
        Sandbox {
            _dir: dir,
            root,
            cache,
        }
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
        assert!(
            !output.status.success(),
            "grand {args:?} unexpectedly succeeded"
        );
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
    write(&dir.join("src").join("lib.glorious"), body);
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
    assert!(
        output.status.success(),
        "git {args:?}: {}",
        String::from_utf8_lossy(&output.stderr)
    );
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
    assert!(app.join("src/main.glorious").is_file());
    let log = sandbox.ok_in(&app, &["check"]);
    assert!(log.contains("Checked app"), "unexpected log: {log}");
    // Library-only packages cannot be checked as executables.
    let lib = sandbox.root.join("lib");
    lib_package(&lib, "lib", "helper() -> i64 { 1 }\n");
    let log = sandbox.fail_in(&lib, &["check"]);
    assert!(log.contains("no entry point"), "unexpected log: {log}");
}

#[test]
fn new_accepts_an_optional_destination_path_without_overwriting() {
    let sandbox = Sandbox::new();
    let destination = sandbox.root.join("nested").join("custom-directory");
    let destination_arg = destination.to_str().unwrap();
    sandbox.ok_in(&sandbox.root, &["new", "my-app", "--path", destination_arg]);

    assert_eq!(
        std::fs::read_to_string(destination.join("grandiose.toml")).unwrap(),
        "[project]\nname = \"my-app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
         [backend]\nkind = \"vm\"\n"
    );
    assert_eq!(
        std::fs::read_to_string(destination.join("src/main.glorious")).unwrap(),
        "main() -> () {\n    ()\n}\n"
    );
    assert_eq!(
        std::fs::read_to_string(destination.join(".gitignore")).unwrap(),
        "/target\n"
    );

    let existing = sandbox.root.join("existing");
    std::fs::create_dir(&existing).unwrap();
    write(&existing.join("keep.txt"), "do not replace\n");
    let log = sandbox.fail_in(
        &sandbox.root,
        &["new", "renamed", "--path", existing.to_str().unwrap()],
    );
    assert!(log.contains("already exists"), "unexpected log: {log}");
    assert_eq!(
        std::fs::read_to_string(existing.join("keep.txt")).unwrap(),
        "do not replace\n"
    );
    assert!(!existing.join("grandiose.toml").exists());

    let default_path = sandbox.root.join("default-name");
    sandbox.ok_in(&sandbox.root, &["new", "default-name"]);
    let manifest = std::fs::read_to_string(default_path.join("grandiose.toml")).unwrap();
    assert!(manifest.contains("name = \"default-name\""));
}

#[test]
fn new_rejects_invalid_names_before_creating_the_target() {
    let sandbox = Sandbox::new();
    let invalid = sandbox.root.join("otherwise-valid");
    let log = sandbox.fail_in(
        &sandbox.root,
        &["new", "Bad_Name", "--path", invalid.to_str().unwrap()],
    );
    assert!(
        log.contains("not a valid package name"),
        "unexpected log: {log}"
    );
    assert!(!invalid.exists());
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
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n[dependencies]\nmid = { path = \"../mid\" }\n",
    );
    sandbox.ok_in(&app, &["check"]);

    let bundle = std::fs::read_to_string(app.join("target/grand/check.glorious")).unwrap();
    let deep_at = bundle.find("deep_value").unwrap();
    let mid_at = bundle.find("mid_value").unwrap();
    let main_at = bundle.find("main()").unwrap();
    assert!(
        deep_at < mid_at && mid_at < main_at,
        "bundle order wrong:\n{bundle}"
    );
    let map = std::fs::read_to_string(app.join("target/grand/check.map.json")).unwrap();
    assert!(
        map.contains("\"package\": \"deep\""),
        "segment map missing packages: {map}"
    );
    // Path dependencies do not appear pinned in the lockfile, but exist in it.
    let lock = std::fs::read_to_string(app.join("grandiose.lock")).unwrap();
    assert!(lock.contains("name = \"mid\"") && lock.contains("name = \"deep\""));
    assert!(
        !lock.contains("commit = "),
        "path deps must not be pinned: {lock}"
    );
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
    assert!(
        lock.contains("tag=v1") && lock.contains("commit = "),
        "lock not pinned: {lock}"
    );
    assert!(
        lock.contains("content-hash = \"blake3:"),
        "lock missing content hash: {lock}"
    );

    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.glorious")).unwrap();
    assert!(
        bundle.contains("util_value"),
        "git dep missing from bundle:\n{bundle}"
    );

    // Moving the tag upstream must not affect a locked project…
    write(
        &repo.join("src").join("lib.glorious"),
        "util_value() -> i64 { 4 }\nextra() -> i64 { 5 }\n",
    );
    git(&repo, &["commit", "-qam", "update"]);
    git(&repo, &["tag", "-f", "v1"]);
    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.glorious")).unwrap();
    assert!(
        !bundle.contains("extra"),
        "locked build picked up unpinned changes"
    );

    // …until an explicit update re-resolves it.
    sandbox.ok_in(&app, &["update", "util"]);
    sandbox.ok_in(&app, &["check"]);
    let bundle = std::fs::read_to_string(app.join("target/grand/check.glorious")).unwrap();
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
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
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
    assert!(
        stderr.contains("GRAND_LOCKED"),
        "unexpected error: {stderr}"
    );
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
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
         [dependencies]\nleft = { path = \"../left\" }\nright = { path = \"../right\" }\n",
    );
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("two different sources"),
        "unexpected error: {log}"
    );

    // A self-cycle through path deps.
    let ouro = sandbox.root.join("ouro");
    lib_package(&ouro, "ouro", "o() -> i64 { 1 }\n");
    write(
        &ouro.join("grandiose.toml"),
        "[project]\nname = \"ouro\"\nversion = \"0.1.0\"\nentry = \"src/lib.glorious\"\n\n[dependencies]\nouro2 = { path = \".\" }\n",
    );
    let log = sandbox.fail_in(&ouro, &["check"]);
    assert!(
        log.contains("cycle") || log.contains("calls itself"),
        "unexpected error: {log}"
    );
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
fn source_and_workspace_paths_cannot_escape_their_roots() {
    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    let outside = sandbox.root.join("outside.glorious");
    write(&outside, "outside() -> i64 { 9 }\n");
    write(
        &app.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"../outside.glorious\"\n",
    );
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("escapes the package root"),
        "unexpected error: {log}"
    );

    let workspace = sandbox.root.join("workspace");
    write(
        &workspace.join("grandiose.toml"),
        "[workspace]\nmembers = [\"../external\"]\n",
    );
    lib_package(
        &sandbox.root.join("external"),
        "external",
        "value() -> i64 { 1 }\n",
    );
    let log = sandbox.fail_in(&workspace, &["-p", "external", "check"]);
    assert!(
        log.contains("escapes the workspace root"),
        "unexpected error: {log}"
    );
}

#[cfg(unix)]
#[test]
fn symlinked_source_escape_is_rejected() {
    use std::os::unix::fs::symlink;

    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    let outside = sandbox.root.join("outside.glorious");
    write(&outside, "outside() -> i64 { 9 }\n");
    std::fs::remove_file(app.join("src/main.glorious")).unwrap();
    symlink(&outside, app.join("src/main.glorious")).unwrap();
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("escapes the package root"),
        "unexpected error: {log}"
    );
}

#[cfg(unix)]
#[test]
fn dependency_cycles_through_symlink_aliases_are_rejected() {
    use std::os::unix::fs::symlink;

    let sandbox = Sandbox::new();
    let a = sandbox.root.join("a");
    let b = sandbox.root.join("b");
    lib_package(&a, "a", "a_value() -> i64 { 1 }\n");
    lib_package(&b, "b", "b_value() -> i64 { 2 }\n");
    symlink(&a, sandbox.root.join("a-alias")).unwrap();
    symlink(&b, sandbox.root.join("b-alias")).unwrap();
    write(
        &a.join("grandiose.toml"),
        "[project]\nname = \"a\"\nversion = \"0.1.0\"\nentry = \"src/lib.glorious\"\n\n\
         [dependencies]\nb = { path = \"../b-alias\" }\n",
    );
    write(
        &b.join("grandiose.toml"),
        "[project]\nname = \"b\"\nversion = \"0.1.0\"\n\n\
         [dependencies]\na = { path = \"../a-alias\" }\n",
    );
    let log = sandbox.fail_in(&a, &["check"]);
    assert!(log.contains("dependency cycle"), "unexpected error: {log}");
}

#[test]
fn dependency_names_cannot_be_used_as_vendor_path_traversal() {
    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(
        &app.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
         [dependencies.\"../escape\"]\npath = \".\"\n",
    );
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("dependency name") && log.contains("invalid"),
        "unexpected error: {log}"
    );
}

#[test]
fn malformed_lock_pins_and_modified_checkouts_are_rejected() {
    let sandbox = Sandbox::new();
    let repo = git_package(&sandbox, "util", "util_value() -> i64 { 3 }\n");
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    let repo_url = repo.display().to_string();
    write(
        &app.join("grandiose.toml"),
        &format!(
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
             [dependencies]\nutil = {{ git = \"{repo_url}\", tag = \"v1\" }}\n"
        ),
    );
    write(
        &app.join("grandiose.lock"),
        &format!(
            "version = 1\n\n[[package]]\nname = \"util\"\nsource = \"git+{repo_url}?tag=v1\"\n\
             commit = \"../../escape\"\ncontent-hash = \"blake3:{}\"\ndeps = []\n",
            "0".repeat(64)
        ),
    );
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(log.contains("invalid commit"), "unexpected error: {log}");

    std::fs::remove_file(app.join("grandiose.lock")).unwrap();
    sandbox.ok_in(&app, &["check"]);
    let valid_lock = std::fs::read_to_string(app.join("grandiose.lock")).unwrap();
    let tampered_lock = valid_lock
        .lines()
        .map(|line| {
            if line.starts_with("content-hash = ") {
                format!("content-hash = \"blake3:{}\"", "0".repeat(64))
            } else {
                line.to_owned()
            }
        })
        .collect::<Vec<_>>()
        .join("\n")
        + "\n";
    write(&app.join("grandiose.lock"), &tampered_lock);
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("content hash mismatch"),
        "unexpected error: {log}"
    );
    write(&app.join("grandiose.lock"), &valid_lock);

    let checkout_source = walkdir::WalkDir::new(sandbox.cache.join("checkouts"))
        .into_iter()
        .filter_map(Result::ok)
        .map(|entry| entry.into_path())
        .find(|path| path.ends_with("src/lib.glorious"))
        .expect("cached checkout source");
    let injected = checkout_source.parent().unwrap().join("injected.glorious");
    write(&injected, "injected() -> i64 { 666 }\n");
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("untracked package inputs"),
        "unexpected error: {log}"
    );
    std::fs::remove_file(injected).unwrap();

    write(&checkout_source, "util_value() -> i64 { 999 }\n");
    let log = sandbox.fail_in(&app, &["check"]);
    assert!(
        log.contains("modified tracked files"),
        "unexpected error: {log}"
    );
}

#[test]
fn resolution_order_and_git_cache_identity_are_deterministic() {
    let sandbox = Sandbox::new();
    let first_repo = git_package(&sandbox, "first", "which() -> i64 { 1 }\n");
    let second_repo = git_package(&sandbox, "second", "which() -> i64 { 2 }\n");

    for (app_name, repo, dependency_name) in [
        ("app-a", &first_repo, "first"),
        ("app-b", &second_repo, "second"),
    ] {
        sandbox.ok_in(&sandbox.root, &["new", app_name]);
        let app = sandbox.root.join(app_name);
        write(
            &app.join("grandiose.toml"),
            &format!(
                "[project]\nname = \"{app_name}\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
                 [dependencies]\n{dependency_name} = {{ git = \"{}\", tag = \"v1\" }}\n",
                repo.display()
            ),
        );
        sandbox.ok_in(&app, &["check"]);
        let first = std::fs::read(app.join("grandiose.lock")).unwrap();
        sandbox.ok_in(&app, &["check"]);
        assert_eq!(std::fs::read(app.join("grandiose.lock")).unwrap(), first);
        let bundle = std::fs::read_to_string(app.join("target/grand/check.glorious")).unwrap();
        let expected = if dependency_name == "first" {
            "{ 1 }"
        } else {
            "{ 2 }"
        };
        assert!(
            bundle.contains(expected),
            "cache contents crossed repositories: {bundle}"
        );
    }

    let checkout_roots = std::fs::read_dir(sandbox.cache.join("checkouts"))
        .unwrap()
        .count();
    assert_eq!(
        checkout_roots, 2,
        "distinct repository URLs shared a cache identity"
    );

    let alpha = sandbox.root.join("alpha");
    let zulu = sandbox.root.join("zulu");
    lib_package(&alpha, "alpha", "alpha_value() -> i64 { 1 }\n");
    lib_package(&zulu, "zulu", "zulu_value() -> i64 { 2 }\n");
    sandbox.ok_in(&sandbox.root, &["new", "ordered"]);
    let ordered = sandbox.root.join("ordered");
    write(
        &ordered.join("grandiose.toml"),
        "[project]\nname = \"ordered\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
         [dependencies]\nzulu = { path = \"../zulu\" }\nalpha = { path = \"../alpha\" }\n",
    );
    sandbox.ok_in(&ordered, &["check"]);
    let lock = std::fs::read_to_string(ordered.join("grandiose.lock")).unwrap();
    assert!(lock.find("name = \"alpha\"").unwrap() < lock.find("name = \"zulu\"").unwrap());
    let bundle = std::fs::read_to_string(ordered.join("target/grand/check.glorious")).unwrap();
    assert!(bundle.find("alpha_value").unwrap() < bundle.find("zulu_value").unwrap());
}

#[test]
fn tests_run_as_independent_executables() {
    let sandbox = Sandbox::new();
    sandbox.ok_in(&sandbox.root, &["new", "app"]);
    let app = sandbox.root.join("app");
    write(
        &app.join("tests").join("smoke.glorious"),
        "main() -> i64 { 0 }\n",
    );
    // The fake compiler ignores input and emits an exit-0 module, so this
    // exercises discovery, per-test bundling, materialization, and execution.
    if !has_llvm_toolchain() {
        eprintln!("skipping: llvm-as/lli/clang not available");
        return;
    }
    let log = sandbox.ok_in(&app, &["test"]);
    assert!(log.contains("test smoke ... ok"), "unexpected log: {log}");
    // The test bundle must contain the test file, not the root entry.
    let bundle = std::fs::read_to_string(app.join("target/grand/test-smoke.glorious")).unwrap();
    assert_eq!(
        bundle.matches("main()").count(),
        1,
        "root entry leaked into test bundle"
    );
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
