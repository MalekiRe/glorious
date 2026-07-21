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

    fn install_mock_vm(&self) -> PathBuf {
        self.install_mock_vm_with_caps(
            r#"{"grvm":"9.9.9","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
        )
    }

    fn install_mock_vm_with_caps(&self, capabilities: &str) -> PathBuf {
        let script = self.dir.path().join("mock-grvm");
        std::fs::write(self.dir.path().join("vm-caps.json"), capabilities).unwrap();
        std::fs::write(
            &script,
            "#!/usr/bin/env bash\ndir=\"$(cd \"$(dirname \"$0\")\" && pwd)\"\necho \"$@\" >> \"$dir/vm.log\"\nif [ \"$1\" = --capabilities ]; then cat \"$dir/vm-caps.json\"; fi\nexit 0\n",
        )
        .unwrap();
        std::fs::set_permissions(&script, std::fs::Permissions::from_mode(0o755)).unwrap();
        script
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
    write(&dep.join("src/lib.glorious"), body);
    write(
        &app.join("grandiose.toml"),
        &format!(
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n\
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
    assert!(
        log.contains("Using grc 9.9.9 (contract 1)"),
        "no version line: {log}"
    );
    // Multi-file: both real source files passed, --phase check used, no bundle.
    let args = sandbox.args_log();
    let compile_line = args.lines().last().unwrap();
    assert!(
        compile_line.contains("--phase check"),
        "no check phase: {compile_line}"
    );
    assert!(
        compile_line.contains("lib.glorious") && compile_line.contains("main.glorious"),
        "sources not passed individually: {compile_line}"
    );
    assert!(
        !app.join("target/grand/check.glorious").exists(),
        "bundle written despite multi-file"
    );
}

#[test]
fn module_aware_grc_receives_only_ordered_crate_roots_and_watches_children() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"9.9.9","contract":1,"multi-file":true,"modules":true,"phases":["check"],"emit":[],"diagnostics-json":true}"#,
    );
    let app = sandbox.app();
    add_path_dep(&app, "util", "mod detail;\nutil_value() -> i64 { 3 }\n");
    write(
        &app.join("src/main.glorious"),
        "mod helper;\nmain() -> i64 { helper_value() }\n",
    );
    write(
        &app.join("src/helper.glorious"),
        "helper_value() -> i64 { 1 }\n",
    );
    write(
        &app.parent().unwrap().join("util/src/detail.glorious"),
        "detail_value() -> i64 { 2 }\n",
    );

    let run = || sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let first = run();
    assert!(first.status.success(), "{}", stderr(&first));
    let log = sandbox.args_log();
    let compile = log.lines().last().unwrap();
    let main = compile.find("main.glorious").unwrap();
    let library = compile.find("lib.glorious").unwrap();
    assert!(main < library, "root entry was not first: {compile}");
    assert!(
        compile.contains("--dependency util="),
        "dependency root metadata was not explicit: {compile}"
    );
    assert!(!compile.contains("helper.glorious"), "{compile}");
    assert!(!compile.contains("detail.glorious"), "{compile}");

    assert!(run().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        3,
        "fresh check recompiled"
    );
    write(
        &app.join("src/helper.glorious"),
        "helper_value() -> i64 { 9 }\n",
    );
    assert!(run().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        5,
        "child module edit did not invalidate the fingerprint"
    );
}

#[test]
fn module_aware_dependency_root_ambiguity_is_diagnosed() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"9.9.9","contract":1,"multi-file":true,"modules":true,"phases":["check"],"emit":[],"diagnostics-json":true}"#,
    );
    let app = sandbox.app();
    add_path_dep(&app, "util", "util_value() -> i64 { 3 }\n");
    write(
        &app.parent().unwrap().join("util/src/lib.gr"),
        "other() -> i64 { 4 }\n",
    );
    let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success(), "ambiguous roots were accepted");
    assert!(
        log.contains("dependency `util` has ambiguous crate roots"),
        "{log}"
    );
    assert!(log.contains("set `[project].entry` explicitly"), "{log}");
}

#[test]
fn bytecode_capability_switches_build_output_and_runtime_to_g1() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"9.9.9","contract":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"phases":["check"],"emit":["bytecode"],"diagnostics-json":true}"#,
    );
    let grvm = sandbox.install_mock_vm();
    let app = sandbox.app();
    let output = Command::new(env!("CARGO_BIN_EXE_grand"))
        .arg("build")
        .current_dir(&app)
        .env("GRAND_COMPILER", &grc)
        .env("GRAND_VM", &grvm)
        .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
        .output()
        .unwrap();
    let log = stderr(&output);
    assert!(output.status.success(), "bytecode build failed: {log}");
    assert!(
        app.join("target/grand/app.grbc").is_file(),
        "missing .grbc output"
    );
    assert!(
        !app.join("target/grand/app.ll").exists(),
        "legacy .ll output was requested"
    );
    let compile_line = sandbox.args_log().lines().last().unwrap().to_string();
    assert!(compile_line.contains("--emit bytecode"), "{compile_line}");
    assert!(compile_line.contains("app.grbc"), "{compile_line}");

    let run = Command::new(env!("CARGO_BIN_EXE_grand"))
        .args(["run", "--", "hello"])
        .current_dir(&app)
        .env("GRAND_COMPILER", &grc)
        .env("GRAND_VM", &grvm)
        .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
        .output()
        .unwrap();
    assert!(
        run.status.success(),
        "bytecode run failed: {}",
        stderr(&run)
    );
    let vm_args = std::fs::read_to_string(sandbox.dir.path().join("vm.log")).unwrap();
    assert!(
        vm_args.contains("run") && vm_args.contains("app.grbc -- hello"),
        "{vm_args}"
    );
    assert!(
        !vm_args.contains("--seed-identity"),
        "legacy compiler/VM pairs must remain runnable without seed negotiation: {vm_args}"
    );
}

#[test]
fn matching_released_seed_identity_is_forwarded_to_the_selected_vm() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","multi-file":true,"phases":["check"],"emit":["bytecode"],"diagnostics-json":true}"#,
    );
    let grvm = sandbox.install_mock_vm_with_caps(
        r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1,"accepted-seed-identities":["seed-a"]}"#,
    );
    let app = sandbox.app();
    let output = Command::new(env!("CARGO_BIN_EXE_grand"))
        .args(["run", "--", "hello"])
        .current_dir(&app)
        .env("GRAND_COMPILER", &grc)
        .env("GRAND_VM", &grvm)
        .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
        .output()
        .unwrap();
    assert!(output.status.success(), "{}", stderr(&output));
    let vm_log = std::fs::read_to_string(sandbox.dir.path().join("vm.log")).unwrap();
    assert!(
        vm_log.contains("run --seed-identity seed-a") && vm_log.contains("app.grbc -- hello"),
        "{vm_log}"
    );
}

#[test]
fn missing_mismatched_and_malformed_seed_contracts_fail_before_compilation() {
    let cases = [
        (
            r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","emit":["bytecode"]}"#,
            r#"{"grvm":"legacy","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
            "must both advertise released-seed identity metadata",
        ),
        (
            r#"{"grc":"legacy","contract":1,"artifact-major":1,"artifact-minor":0,"emit":["bytecode"]}"#,
            r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1,"accepted-seed-identities":["seed-a"]}"#,
            "must both advertise released-seed identity metadata",
        ),
        (
            r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","emit":["bytecode"]}"#,
            r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":2,"accepted-seed-identities":["seed-a"]}"#,
            "seed identity protocol 1 is incompatible with VM protocol 2",
        ),
        (
            r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","emit":["bytecode"]}"#,
            r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1,"accepted-seed-identities":["seed-b"]}"#,
            "does not accept compiler released-seed identity `seed-a`",
        ),
        (
            r#"{"grc":"partial","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"emit":["bytecode"]}"#,
            r#"{"grvm":"legacy","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
            "compiler seed identity metadata is incomplete",
        ),
        (
            r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","emit":["bytecode"]}"#,
            r#"{"grvm":"partial","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1}"#,
            "VM seed identity metadata is incomplete or noncanonical",
        ),
    ];

    for (compiler_caps, vm_caps, expected) in cases {
        let sandbox = Sandbox::new();
        let grc = sandbox.install_mock_grc(compiler_caps);
        let grvm = sandbox.install_mock_vm_with_caps(vm_caps);
        let app = sandbox.app();
        let output = Command::new(env!("CARGO_BIN_EXE_grand"))
            .arg("build")
            .current_dir(&app)
            .env("GRAND_COMPILER", &grc)
            .env("GRAND_VM", &grvm)
            .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
            .output()
            .unwrap();
        let log = stderr(&output);
        assert!(
            !output.status.success(),
            "incompatible seed contract was accepted"
        );
        assert!(log.contains(expected), "expected `{expected}` in {log}");
        assert_eq!(
            sandbox.args_log().lines().count(),
            1,
            "compiler ran after incompatible seed negotiation"
        );
    }
}

#[test]
fn incompatible_seed_identity_rejects_an_existing_cached_artifact() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","multi-file":true,"phases":["check"],"emit":["bytecode"],"diagnostics-json":true}"#,
    );
    let grvm = sandbox.install_mock_vm_with_caps(
        r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1,"accepted-seed-identities":["seed-a"]}"#,
    );
    let app = sandbox.app();
    let build = || {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .arg("build")
            .current_dir(&app)
            .env("GRAND_COMPILER", &grc)
            .env("GRAND_VM", &grvm)
            .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
            .output()
            .unwrap()
    };

    assert!(build().status.success());
    assert_eq!(sandbox.args_log().lines().count(), 2, "probe + compile");
    assert!(app.join("target/grand/app.grbc").is_file());

    std::fs::write(
        sandbox.dir.path().join("vm-caps.json"),
        r#"{"grvm":"seeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0,"seed-identity-version":1,"accepted-seed-identities":["seed-b"]}"#,
    )
    .unwrap();
    let rejected = build();
    assert!(!rejected.status.success());
    assert!(
        stderr(&rejected).contains("does not accept compiler released-seed identity `seed-a`"),
        "{}",
        stderr(&rejected)
    );
    assert_eq!(
        sandbox.args_log().lines().count(),
        3,
        "cached output was recompiled or reused before compatibility rejection"
    );
}

#[test]
fn incompatible_contract_and_artifact_versions_fail_before_compilation() {
    for (caps, expected) in [
        (
            r#"{"grc":"future","contract":2,"multi-file":true}"#,
            "incompatible with grand contract 1",
        ),
        (
            r#"{"grc":"missing-version","contract":1,"emit":["bytecode"]}"#,
            "artifact version",
        ),
        (
            r#"{"grc":"future-artifact","contract":1,"artifact-major":2,"artifact-minor":0,"emit":["bytecode"]}"#,
            "incompatible with supported 1.0",
        ),
        (
            r#"{"grc":"bad-session","contract":1,"serve":{"protocol":2,"transport":"json-lines","max-request-bytes":1,"max-arguments":1,"max-inputs":1,"max-source-bytes":1}}"#,
            "incompatible or unbounded persistent-session contract",
        ),
    ] {
        let sandbox = Sandbox::new();
        let grc = sandbox.install_mock_grc(caps);
        let app = sandbox.app();
        let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
        let log = stderr(&output);
        assert!(
            !output.status.success(),
            "incompatible compiler was accepted"
        );
        assert!(log.contains(expected), "{log}");
        assert_eq!(
            sandbox.args_log().lines().count(),
            1,
            "compiler ran after probe"
        );
    }
}

#[test]
fn incompatible_or_unversioned_vm_fails_before_bytecode_compilation() {
    for (caps, expected) in [
        (
            r#"{"grvm":"future","contract":2,"contract-min":2,"contract-max":2,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
            "incompatible with grand VM contract 1",
        ),
        (
            r#"{"grvm":"future-artifact","contract":1,"contract-min":1,"contract-max":1,"artifact-major":2,"artifact-minor-min":0,"artifact-minor-max":0}"#,
            "incompatible with compiler artifact 1.0",
        ),
        (
            r#"{"grvm":"future-minor","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":1,"artifact-minor-max":3}"#,
            "incompatible with compiler artifact 1.0",
        ),
    ] {
        let sandbox = Sandbox::new();
        let grc = sandbox.install_mock_grc(
            r#"{"grc":"9.9.9","contract":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"phases":["check"],"emit":["bytecode"],"diagnostics-json":true}"#,
        );
        let grvm = sandbox.install_mock_vm_with_caps(caps);
        let app = sandbox.app();
        let output = Command::new(env!("CARGO_BIN_EXE_grand"))
            .arg("build")
            .current_dir(&app)
            .env("GRAND_COMPILER", &grc)
            .env("GRAND_VM", &grvm)
            .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
            .output()
            .unwrap();
        let log = stderr(&output);
        assert!(!output.status.success(), "incompatible VM was accepted");
        assert!(log.contains(expected), "{log}");
        assert_eq!(
            sandbox.args_log().lines().count(),
            1,
            "compiler ran after incompatible VM probe"
        );
    }
}

#[test]
fn selected_vm_identity_is_part_of_the_atomic_bytecode_fingerprint() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(
        r#"{"grc":"9.9.9","contract":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"phases":["check"],"emit":["bytecode"],"diagnostics-json":true}"#,
    );
    let grvm = sandbox.install_mock_vm();
    let app = sandbox.app();
    let run_build = || {
        Command::new(env!("CARGO_BIN_EXE_grand"))
            .arg("build")
            .current_dir(&app)
            .env("GRAND_COMPILER", &grc)
            .env("GRAND_VM", &grvm)
            .env("GRAND_CACHE_DIR", sandbox.dir.path().join("cache"))
            .output()
            .unwrap()
    };

    assert!(run_build().status.success());
    assert_eq!(sandbox.args_log().lines().count(), 2, "probe + compile");
    assert!(run_build().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        3,
        "an unchanged VM must preserve the fresh compiler output"
    );

    std::fs::write(
        sandbox.dir.path().join("vm-caps.json"),
        r#"{"grvm":"9.9.10","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
    )
    .unwrap();
    assert!(run_build().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        5,
        "changing the selected compatible VM must force recompilation"
    );
}

#[test]
fn mock_grc_diagnostics_remap_through_bundle() {
    let sandbox = Sandbox::new();
    // No multi-file: grand must bundle, then remap diagnostics back out.
    let grc = sandbox.install_mock_grc(r#"{"grc":"9.9.9","contract":1,"diagnostics-json":true}"#);
    let app = sandbox.app();
    add_path_dep(&app, "util", "util_value() -> i64 { 3 }\n");
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    MOCK_FAIL\n}\n",
    );
    let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    // The mock reported bundle line 3 (util's line + main's line 2); grand
    // must render the original file and line, not the bundle.
    assert!(
        log.contains("error[GRC0001]: mock failure"),
        "diagnostic not rendered: {log}"
    );
    assert!(
        log.contains("src/main.glorious:2"),
        "diagnostic not remapped to the original file/line: {log}"
    );
    assert!(
        !log.contains("check.glorious"),
        "diagnostic still points into the bundle: {log}"
    );
}

#[test]
fn fake_structured_diagnostics_remap() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("src/helpers.glorious"), "helper() -> i64 { 1 }\n");
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );
    let output = sandbox.grand(&app, "fake", "diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(
        log.contains("error[GRC9999]: fake error marker"),
        "unexpected: {log}"
    );
    assert!(log.contains("src/main.glorious:2"), "not remapped: {log}");
}

#[test]
fn fake_multi_file_points_at_real_files_directly() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );
    let output = sandbox.grand(&app, "fake", "multi-file,check,diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("src/main.glorious:2"), "unexpected: {log}");
    assert!(
        !app.join("target/grand/check.glorious").exists(),
        "bundle written despite multi-file"
    );
}

#[test]
fn fake_modules_capability_keeps_recursive_compatibility_inputs() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/helpers.glorious"),
        "helper() -> i64 { FAKE_ERROR }\n",
    );
    let output = sandbox.grand(
        &app,
        "fake",
        "multi-file,modules,check,diagnostics",
        &["check"],
    );
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("src/helpers.glorious:1"), "{log}");
}

#[test]
fn collision_preflight_warns_for_legacy_and_errors_authoritatively() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "shared() -> i64 { 3 }\n");
    write(&app.join("src/helpers.glorious"), "shared() -> i64 { 4 }\n");

    // Legacy fallback (no interfaces capability): warning, build proceeds.
    let output = sandbox.grand(&app, "fake", "", &["check"]);
    let log = stderr(&output);
    assert!(
        output.status.success(),
        "legacy fallback finding must not block: {log}"
    );
    assert!(
        log.contains("warning[GRAND001]: `shared` is defined by both `util` and `app`"),
        "missing legacy collision warning: {log}"
    );

    // Authoritative interface scan: hard error before compiling.
    let output = sandbox.grand(&app, "fake", "interfaces", &["check"]);
    let log = stderr(&output);
    assert!(
        !output.status.success(),
        "authoritative collision must fail: {log}"
    );
    assert!(
        log.contains("error[GRAND001]: `shared` is defined by both"),
        "unexpected: {log}"
    );
    assert!(log.contains("first defined here"), "labels missing: {log}");
}

#[test]
fn lint_levels_allow_and_deny() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "shared() -> i64 { 3 }\n");
    write(&app.join("src/helpers.glorious"), "shared() -> i64 { 4 }\n");

    // Deny escalates the legacy collision warning to a build-stopping error.
    let output = sandbox.grand(&app, "fake", "", &["check", "--deny", "GRAND001"]);
    assert!(
        !output.status.success(),
        "deny must fail: {}",
        stderr(&output)
    );
    assert!(
        stderr(&output).contains("error[GRAND001]"),
        "unexpected: {}",
        stderr(&output)
    );

    // --deny warnings catches it too; --allow silences it entirely.
    let output = sandbox.grand(&app, "fake", "", &["check", "--deny", "warnings"]);
    assert!(!output.status.success());
    let output = sandbox.grand(&app, "fake", "", &["check", "--allow", "GRAND001"]);
    let log = stderr(&output);
    assert!(
        output.status.success() && !log.contains("GRAND001"),
        "allow failed: {log}"
    );

    // Manifest [lints] works without CLI flags.
    let manifest = std::fs::read_to_string(app.join("grandiose.toml")).unwrap();
    write(
        &app.join("grandiose.toml"),
        &format!("{manifest}\n[lints]\nGRAND001 = \"deny\"\n"),
    );
    let output = sandbox.grand(&app, "fake", "", &["check"]);
    assert!(
        !output.status.success(),
        "manifest deny ignored: {}",
        stderr(&output)
    );
    // CLI overrides the manifest.
    let output = sandbox.grand(&app, "fake", "", &["check", "--allow", "GRAND001"]);
    assert!(
        output.status.success(),
        "CLI override failed: {}",
        stderr(&output)
    );
}

#[test]
fn fix_applies_machine_fixes_and_reverifies() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_FIXME0\n}\n"
            .replace("FAKE_FIXME0", "FAKE_FIXME 0")
            .as_str(),
    );
    let output = sandbox.grand(&app, "fake", "diagnostics", &["fix"]);
    let log = stderr(&output);
    assert!(output.status.success(), "fix failed: {log}");
    assert!(log.contains("Applied 1 fix(es)"), "unexpected: {log}");
    let fixed = std::fs::read_to_string(app.join("src/main.glorious")).unwrap();
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
    add_path_dep(
        &app,
        "util",
        "// Adds one to a value.\nadd_one(value: i64) -> i64 { value }\n",
    );
    let output = sandbox.grand(&app, "fake", "", &["doc"]);
    assert!(output.status.success(), "doc failed: {}", stderr(&output));
    let html = std::fs::read_to_string(app.join("target/grand/doc/index.html")).unwrap();
    assert!(html.contains("<h1>util</h1>"), "package section missing");
    assert!(html.contains("add_one"), "declaration missing");
    assert!(
        html.contains("add_one(value: i64) -&gt; i64"),
        "signature missing/unescaped: {html}"
    );
    assert!(html.contains("Adds one to a value."), "doc comment missing");
    assert!(
        html.contains("<h1>app</h1>") && html.contains("main"),
        "root entry missing"
    );
}

#[test]
fn std_shadowing_warns() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/helpers.glorious"),
        "not(value: i64) -> i64 { value }\n",
    );
    let output = sandbox.grand(&app, "fake", "std", &["check"]);
    let log = stderr(&output);
    assert!(
        output.status.success(),
        "shadowing is a warning, not an error: {log}"
    );
    assert!(
        log.contains("`not`") && log.contains("shadows a standard-library name"),
        "unexpected: {log}"
    );
}
