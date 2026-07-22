//! Tests for the compiler contract: capability probing, module roots,
//! check-only compilation, structured diagnostics, interface scans, and
//! collision preflight.
//! The "compiler" is either a bash mock implementing the subprocess protocol
//! Tests use executable fixtures that implement the real wire format.

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

    /// Install a bash mock of grc advertising `caps` (JSON).
    /// Every invocation is appended to `args.log`; sources containing
    /// `MOCK_FAIL` produce a structured diagnostic at the marker line.
    fn install_mock_grc(&self, caps: &str) -> PathBuf {
        let dir = self.dir.path();
        let mut caps: serde_json::Value = serde_json::from_str(caps).unwrap();
        let object = caps.as_object_mut().unwrap();
        object
            .entry("artifact-major")
            .or_insert(serde_json::json!(1));
        object
            .entry("artifact-minor")
            .or_insert(serde_json::json!(0));
        object
            .entry("multi-file")
            .or_insert(serde_json::json!(true));
        object.entry("modules").or_insert(serde_json::json!(true));
        object
            .entry("phases")
            .or_insert(serde_json::json!(["check"]));
        let emit = object
            .entry("emit")
            .or_insert_with(|| serde_json::json!([]))
            .as_array_mut()
            .unwrap();
        for capability in ["bytecode", "interfaces-json", "std-interfaces-json"] {
            if !emit.iter().any(|entry| entry == capability) {
                emit.push(serde_json::json!(capability));
            }
        }
        object
            .entry("diagnostics-json")
            .or_insert(serde_json::json!(true));
        std::fs::write(dir.join("caps.json"), serde_json::to_vec(&caps).unwrap()).unwrap();
        let script = dir.join("mock-grc");
        std::fs::write(
            &script,
            r#"#!/usr/bin/env bash
dir="$(cd "$(dirname "$0")" && pwd)"
echo "$@" >> "$dir/args.log"
if [ "$1" = --capabilities ]; then cat "$dir/caps.json"; exit 0; fi
if [ "$1" = --emit ] && [ "$2" = std-interfaces-json ]; then echo '[{"name":"if","kind":"callable","file":"«std»","line":0},{"name":"not","kind":"callable","file":"«std»","line":0}]'; exit 0; fi
if [ "$1" = --emit ] && [ "$2" = interfaces-json ]; then
  shift 2
  python3 - "$@" <<'PY'
import json,pathlib,re,sys
out=[]
paths=[]
for root in sys.argv[1:]:
  candidate=pathlib.Path(root)
  paths.extend(candidate.parent.rglob('*.glorious'))
for path in sorted(set(paths)):
  try: lines=open(path).read().splitlines()
  except OSError: continue
  docs=[]
  for n,line in enumerate(lines,1):
    if line.lstrip().startswith('//'): docs.append(line.lstrip()[2:].lstrip('/').strip()); continue
    m=re.match(r'\s*(?:pub\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*\(',line)
    if m: out.append({'name':m.group(1),'kind':'callable','file':str(path),'line':n,'signature':line.strip(),'docs':'\n'.join(docs) or None})
    docs=[]
print(json.dumps(out))
PY
  exit 0
fi
out=""; inputs=()
while [ $# -gt 0 ]; do
  case "$1" in
    --diagnostics|--phase|--emit|--dependency) shift;;
    -o) out="$2"; shift;;
    *) inputs+=("$1");;
  esac
  shift
done
expanded=()
for root in "${inputs[@]}"; do while IFS= read -r f; do expanded+=("$f"); done < <(find "$(dirname "$root")" -name '*.glorious' -type f); done
for f in "${expanded[@]}"; do
  n="$(grep -n -E 'MOCK_FAIL|FAKE_ERROR' "$f" | head -1 | cut -d: -f1)"
  if [ -n "$n" ]; then
    printf '{"severity":"error","code":"GRC0001","title":"mock failure","labels":[{"file":"%s","line":%s,"message":"here"}]}\n' "$f" "$n" >&2
    exit 1
  fi
  python3 - "$f" <<'PY' >&2
import json,sys
p=sys.argv[1]; s=open(p).read(); marker='FAKE_FIXME'; start=s.find(marker)
if start >= 0:
 print(json.dumps({'severity':'warning','code':'GRC8888','title':'fixable marker','labels':[{'file':p,'start_byte':start,'end_byte':start+len(marker)}],'fix':{'file':p,'start_byte':start,'end_byte':start+len(marker),'replacement':''}}))
PY
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

    fn grand(&self, cwd: &Path, compiler: &str, _caps: &str, args: &[&str]) -> Output {
        let fixture = compiler == "fixture";
        let selected_compiler = if fixture {
            self.install_mock_grc(
                r#"{"grc":"test","contract":1,"artifact-major":1,"artifact-minor":0,"multi-file":true,"modules":true,"phases":["resolve","check"],"emit":["bytecode","interfaces-json","std-interfaces-json"],"diagnostics-json":true}"#,
            )
        } else {
            PathBuf::from(compiler)
        };
        let mut command = Command::new(env!("CARGO_BIN_EXE_grand"));
        command
            .args(args)
            .current_dir(cwd)
            .env("GRAND_COMPILER", selected_compiler)
            .env("GRAND_CACHE_DIR", self.dir.path().join("cache"));
        if fixture {
            command.env("GRAND_VM", self.install_mock_vm());
        }
        command.output().unwrap()
    }

    fn app(&self) -> PathBuf {
        let output = Command::new(env!("CARGO_BIN_EXE_grand"))
            .args(["new", "app"])
            .current_dir(&self.root)
            .output()
            .unwrap();
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
    // The root and dependency crate root are passed through the canonical API.
    let args = sandbox.args_log();
    let compile_line = args.lines().last().unwrap();
    assert!(
        compile_line.contains("--phase check"),
        "no check phase: {compile_line}"
    );
    assert!(
        compile_line.contains("main.glorious") && compile_line.contains("--dependency util="),
        "crate roots not passed: {compile_line}"
    );
    assert!(
        !app.join("target/grand/check.glorious").exists(),
        "unexpected synthetic source file"
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
        9,
        "fresh check recompiled"
    );
    write(
        &app.join("src/helper.glorious"),
        "helper_value() -> i64 { 9 }\n",
    );
    assert!(run().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        14,
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
        &app.parent().unwrap().join("util/grandiose.toml"),
        "[project]\nname = \"util\"\nversion = \"0.1.0\"\nsources = [\"src/lib.glorious\", \"src/other.glorious\"]\n",
    );
    write(
        &app.parent().unwrap().join("util/src/other.glorious"),
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
    let compile_line = sandbox.args_log().lines().last().unwrap().to_string();
    assert!(compile_line.contains("--emit bytecode"), "{compile_line}");
    assert!(compile_line.contains("app.grbc"), "{compile_line}");

    let manifest_path = app.join("grandiose.toml");
    let mut manifest = std::fs::read_to_string(&manifest_path).unwrap();
    manifest
        .push_str("\n[runtime]\ncapabilities = [\"process.args\", \"fs.read\", \"diagnostic\"]\n");
    std::fs::write(&manifest_path, manifest).unwrap();

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
        vm_args.contains("run --allow process.args --allow fs.read --allow diagnostic")
            && vm_args.contains("app.grbc -- hello"),
        "{vm_args}"
    );
    assert!(
        !vm_args.contains("--seed-identity"),
        "compiler/VM pairs without seed metadata must remain runnable: {vm_args}"
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
    assert!(
        !vm_log.contains("--allow"),
        "runtime capabilities must default to none: {vm_log}"
    );
}

#[test]
fn missing_mismatched_and_malformed_seed_contracts_fail_before_compilation() {
    let cases = [
        (
            r#"{"grc":"seeded","contract":1,"artifact-major":1,"artifact-minor":0,"seed-identity-version":1,"seed-identity":"seed-a","emit":["bytecode"]}"#,
            r#"{"grvm":"unseeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
            "must both advertise released-seed identity metadata",
        ),
        (
            r#"{"grc":"unseeded","contract":1,"artifact-major":1,"artifact-minor":0,"emit":["bytecode"]}"#,
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
            r#"{"grvm":"unseeded","contract":1,"contract-min":1,"contract-max":1,"artifact-major":1,"artifact-minor-min":0,"artifact-minor-max":0}"#,
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
    assert_eq!(
        sandbox.args_log().lines().count(),
        4,
        "probe + scans + compile"
    );
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
        5,
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
            r#"{"grc":"missing-version","contract":1,"artifact-major":null,"artifact-minor":null,"emit":["bytecode"]}"#,
            "does not emit supported Grandiose bytecode",
        ),
        (
            r#"{"grc":"future-artifact","contract":1,"artifact-major":2,"artifact-minor":0,"emit":["bytecode"]}"#,
            "does not emit supported Grandiose bytecode",
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
    assert_eq!(
        sandbox.args_log().lines().count(),
        4,
        "probe + scans + compile"
    );
    assert!(run_build().status.success());
    assert_eq!(
        sandbox.args_log().lines().count(),
        7,
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
        11,
        "changing the selected compatible VM must force recompilation"
    );
}

#[test]
fn mock_grc_renders_structured_diagnostics_at_source_locations() {
    let sandbox = Sandbox::new();
    let grc = sandbox.install_mock_grc(r#"{"grc":"9.9.9","contract":1,"diagnostics-json":true}"#);
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    MOCK_FAIL\n}\n",
    );
    let output = sandbox.grand(&app, grc.to_str().unwrap(), "", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(
        log.contains("error[GRC0001]: mock failure"),
        "diagnostic not rendered: {log}"
    );
    assert!(
        log.contains("src/main.glorious:2"),
        "diagnostic does not identify the original file/line: {log}"
    );
}

#[test]
fn fixture_structured_diagnostics_remap() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(&app.join("src/helpers.glorious"), "helper() -> i64 { 1 }\n");
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );
    let output = sandbox.grand(&app, "fixture", "diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(
        log.contains("error[GRC0001]: mock failure"),
        "unexpected: {log}"
    );
    assert!(log.contains("src/main.glorious:2"), "not remapped: {log}");
}

#[test]
fn fixture_multi_file_points_at_real_files_directly() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/main.glorious"),
        "main() -> i64 {\n    FAKE_ERROR\n}\n",
    );
    let output = sandbox.grand(&app, "fixture", "multi-file,check,diagnostics", &["check"]);
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("src/main.glorious:2"), "unexpected: {log}");
    assert!(
        !app.join("target/grand/check.glorious").exists(),
        "unexpected synthetic source file"
    );
}

#[test]
fn fixture_modules_capability_keeps_recursive_compatibility_inputs() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    write(
        &app.join("src/helpers.glorious"),
        "helper() -> i64 { FAKE_ERROR }\n",
    );
    let output = sandbox.grand(
        &app,
        "fixture",
        "multi-file,modules,check,diagnostics",
        &["check"],
    );
    let log = stderr(&output);
    assert!(!output.status.success());
    assert!(log.contains("src/helpers.glorious:1"), "{log}");
}

#[test]
fn collision_preflight_is_authoritative() {
    let sandbox = Sandbox::new();
    let app = sandbox.app();
    add_path_dep(&app, "util", "shared() -> i64 { 3 }\n");
    write(&app.join("src/helpers.glorious"), "shared() -> i64 { 4 }\n");

    let output = sandbox.grand(&app, "fixture", "", &["check"]);
    let log = stderr(&output);
    assert!(
        !output.status.success(),
        "cross-package collision must block: {log}"
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
    write(&app.join("src/helpers.glorious"), "if() -> i64 { 4 }\n");

    let output = sandbox.grand(&app, "fixture", "std", &["check", "--deny", "GRAND002"]);
    assert!(
        !output.status.success(),
        "deny must fail: {}",
        stderr(&output)
    );
    assert!(
        stderr(&output).contains("error[GRAND002]"),
        "unexpected: {}",
        stderr(&output)
    );

    // --deny warnings catches it too; --allow silences it entirely.
    let output = sandbox.grand(&app, "fixture", "std", &["check", "--deny", "warnings"]);
    assert!(!output.status.success());
    let output = sandbox.grand(&app, "fixture", "std", &["check", "--allow", "GRAND002"]);
    let log = stderr(&output);
    assert!(
        output.status.success() && !log.contains("GRAND002"),
        "allow failed: {log}"
    );

    // Manifest [lints] works without CLI flags.
    let manifest = std::fs::read_to_string(app.join("grandiose.toml")).unwrap();
    write(
        &app.join("grandiose.toml"),
        &format!("{manifest}\n[lints]\nGRAND002 = \"deny\"\n"),
    );
    let output = sandbox.grand(&app, "fixture", "std", &["check"]);
    assert!(
        !output.status.success(),
        "manifest deny ignored: {}",
        stderr(&output)
    );
    // CLI overrides the manifest.
    let output = sandbox.grand(&app, "fixture", "std", &["check", "--allow", "GRAND002"]);
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
    let output = sandbox.grand(&app, "fixture", "diagnostics", &["fix"]);
    let log = stderr(&output);
    assert!(output.status.success(), "fix failed: {log}");
    assert!(log.contains("Applied 1 fix(es)"), "unexpected: {log}");
    let fixed = std::fs::read_to_string(app.join("src/main.glorious")).unwrap();
    assert!(!fixed.contains("FAKE_FIXME"), "marker survived: {fixed}");
    assert!(fixed.contains("main() -> i64"), "file mangled: {fixed}");

    // Nothing left to fix on the second run.
    let output = sandbox.grand(&app, "fixture", "diagnostics", &["fix"]);
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
    let output = sandbox.grand(&app, "fixture", "", &["doc"]);
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
    let output = sandbox.grand(&app, "fixture", "std", &["check"]);
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
