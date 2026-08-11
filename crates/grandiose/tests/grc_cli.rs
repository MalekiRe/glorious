use std::{
    fs,
    io::{BufRead, BufReader, Write},
    path::Path,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
};

use grandiose_vm::{Artifact, verify};
use tempfile::tempdir;

fn write(path: &Path, source: &str) {
    fs::write(path, source).unwrap();
}

fn grc() -> Command {
    Command::new(env!("CARGO_BIN_EXE_grc"))
}

struct Session {
    child: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl Session {
    fn start() -> Self {
        let mut child = grc()
            .arg("--serve")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        let input = child.stdin.take().unwrap();
        let output = BufReader::new(child.stdout.take().unwrap());
        Self {
            child,
            input,
            output,
        }
    }

    fn raw(&mut self, request: &str) -> serde_json::Value {
        writeln!(self.input, "{request}").unwrap();
        self.input.flush().unwrap();
        let mut response = String::new();
        self.output.read_line(&mut response).unwrap();
        assert!(!response.is_empty(), "session exited without a response");
        serde_json::from_str(&response).unwrap()
    }

    fn request(&mut self, request: serde_json::Value) -> serde_json::Value {
        self.raw(&request.to_string())
    }

    fn kill_and_wait(&mut self) {
        self.child.kill().unwrap();
        self.child.wait().unwrap();
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        if self.child.try_wait().ok().flatten().is_none() {
            let _ = self.child.kill();
            let _ = self.child.wait();
        }
    }
}

#[test]
fn persistent_serve_reuses_llvm_ir_and_invalidates_after_a_body_edit() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("cache.glorious");
    let output = directory.path().join("cache.ll");
    write(
        &input,
        "value() -> i64 { 1 } main() -> { let marker = value(); () }",
    );
    let arguments = || {
        serde_json::json!([
            "-O0",
            "--emit",
            "llvm-ir",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    let mut session = Session::start();

    let first = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": arguments(),
    }));
    assert_eq!(first["status"], 0, "{first}");
    assert_eq!(first["llvm_ir_cache"], "miss", "{first}");
    let first_ir = fs::read(&output).unwrap();

    let second = session.request(serde_json::json!({
        "protocol": 1,
        "id": 2,
        "method": "compile",
        "arguments": arguments(),
    }));
    assert_eq!(second["status"], 0, "{second}");
    assert_eq!(second["llvm_ir_cache"], "hit", "{second}");
    assert_eq!(fs::read(&output).unwrap(), first_ir);

    write(
        &input,
        "value() -> i64 { 2 } main() -> { let marker = value(); () }",
    );
    let edited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 3,
        "method": "compile",
        "arguments": arguments(),
    }));
    assert_eq!(edited["status"], 0, "{edited}");
    assert_eq!(edited["llvm_ir_cache"], "miss", "{edited}");
    assert_ne!(
        fs::read(&output).unwrap(),
        first_ir,
        "an edited body reused stale LLVM IR"
    );
}

/// A deterministic release-mode measurement harness for the real JSON-line
/// server. Run with:
/// `tooling/ram-gate.sh cargo test --release -p grandiose --test grc_cli \
/// release_warm_llvm_serve_iteration_records_cache_evidence -- --ignored --exact`
///
/// It records cache work rather than imposing unstable wall-clock budgets.
#[test]
#[ignore = "release-only warm iteration measurement harness"]
fn release_warm_llvm_serve_iteration_records_cache_evidence() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("warm.glorious");
    let output = directory.path().join("warm.ll");
    let arguments = || {
        serde_json::json!([
            "-O0",
            "--emit",
            "llvm-ir",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    let request = |session: &mut Session, id, arguments: serde_json::Value| {
        session.request(serde_json::json!({
            "protocol": 1,
            "id": id,
            "method": "compile",
            "arguments": arguments,
        }))
    };
    let mut session = Session::start();

    write(
        &input,
        "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
    );
    let cold = request(&mut session, 1, arguments());
    assert_eq!(cold["status"], 0, "{cold}");
    assert_eq!(cold["llvm_ir_cache"], "miss", "{cold}");
    assert_eq!(cold["cache_stats"]["llvm_ir_reused"], 0, "{cold}");
    assert_eq!(cold["cache_stats"]["llvm_fragments_reused"], 0, "{cold}");
    let cold_ir = fs::read(&output).unwrap();

    let warm = request(&mut session, 2, arguments());
    assert_eq!(warm["status"], 0, "{warm}");
    assert_eq!(warm["llvm_ir_cache"], "hit", "{warm}");
    assert_eq!(warm["cache_stats"]["llvm_ir_reused"], 1, "{warm}");
    assert_eq!(warm["cache_stats"]["llvm_fragments_reused"], 0, "{warm}");
    assert_eq!(fs::read(&output).unwrap(), cold_ir);

    write(
        &input,
        "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
    );
    let body_only = request(&mut session, 3, arguments());
    assert_eq!(body_only["status"], 0, "{body_only}");
    assert_eq!(body_only["llvm_ir_cache"], "miss", "{body_only}");
    assert_eq!(body_only["cache_stats"]["llvm_ir_reused"], 0, "{body_only}");
    assert_eq!(
        body_only["cache_stats"]["llvm_fragments_reused"], 2,
        "a leaf implementation edit must retain caller and entry fragments: {body_only}"
    );
    assert_ne!(fs::read(&output).unwrap(), cold_ir);

    write(
        &input,
        "leaf(argument: ()) -> i64 { 2 } caller() -> i64 { leaf(()) } main() -> () { caller(); () }",
    );
    let interface_changed = request(&mut session, 4, arguments());
    assert_eq!(interface_changed["status"], 0, "{interface_changed}");
    assert_eq!(interface_changed["llvm_ir_cache"], "miss", "{interface_changed}");
    assert_eq!(interface_changed["cache_stats"]["llvm_ir_reused"], 0);
    assert_eq!(
        interface_changed["cache_stats"]["llvm_fragments_reused"], 0,
        "the current runtime-ABI guard conservatively invalidates every fragment after a leaf ABI edit: {interface_changed}"
    );
}

#[test]
fn persistent_serve_reports_process_local_function_incremental_evidence() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("incremental.glorious");
    let output = directory.path().join("incremental.ll");
    let arguments = || {
        serde_json::json!([
            "-O0",
            "--emit",
            "llvm-ir",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    write(
        &input,
        "leaf() -> i64 { 1 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
    );
    let mut session = Session::start();
    let cold = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": arguments(),
    }));
    assert_eq!(cold["status"], 0, "{cold}");
    assert_eq!(cold["native_incremental"]["cache_scope"], "serve-process");
    assert_eq!(cold["native_incremental"]["llvm_fragments_reused"], 0);
    assert_eq!(cold["native_incremental"]["llvm_fragments_emitted"], 3);
    assert_eq!(cold["native_incremental"]["native_objects_reused"], 0);
    assert_eq!(cold["native_incremental"]["native_objects_emitted"], 0);
    assert_eq!(cold["native_incremental"]["wild_relink"], false);

    write(
        &input,
        "leaf() -> i64 { 2 } caller() -> i64 { leaf() } main() -> () { caller(); () }",
    );
    let edited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 2,
        "method": "compile",
        "arguments": arguments(),
    }));
    assert_eq!(edited["status"], 0, "{edited}");
    assert_eq!(edited["native_incremental"]["cache_scope"], "serve-process");
    assert_eq!(edited["native_incremental"]["llvm_fragments_reused"], 2);
    assert_eq!(edited["native_incremental"]["llvm_fragments_emitted"], 1);
    assert_eq!(edited["native_incremental"]["wild_relink"], false);
}

#[test]
fn persistent_serve_reuses_exact_llvm_object_bytes_at_the_current_output_path() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("cache.glorious");
    let first_output = directory.path().join("first.o");
    let second_output = directory.path().join("second.o");
    write(&input, "main() -> () { () }");
    let arguments = |output: &Path| {
        serde_json::json!([
            "-O0",
            "--emit",
            "llvm-object",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    let mut session = Session::start();

    let first = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": arguments(&first_output),
    }));
    assert_eq!(first["status"], 0, "{first}");
    assert_eq!(first["native_object_cache"], "miss", "{first}");
    let first_object = fs::read(&first_output).unwrap();

    let second = session.request(serde_json::json!({
        "protocol": 1,
        "id": 2,
        "method": "compile",
        "arguments": arguments(&second_output),
    }));
    assert_eq!(second["status"], 0, "{second}");
    assert_eq!(second["llvm_ir_cache"], "hit", "{second}");
    assert_eq!(second["native_object_cache"], "hit", "{second}");
    assert_eq!(fs::read(&second_output).unwrap(), first_object);

    write(&input, "main() -> () { let marker = (); marker }");
    let edited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 3,
        "method": "compile",
        "arguments": arguments(&second_output),
    }));
    assert_eq!(edited["status"], 0, "{edited}");
    assert_eq!(edited["native_object_cache"], "miss", "{edited}");
    assert_ne!(fs::read(&second_output).unwrap(), first_object);
}

#[test]
fn persistent_serve_reuses_partitioned_o3_objects_after_body_edit_and_wild_relinks() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("partitioned.glorious");
    let first_executable = directory.path().join("partitioned-native-first");
    let second_executable = directory.path().join("partitioned-native-second");
    let observed = directory.path().join("observed.bin");
    let observed_path = serde_json::to_string(observed.to_str().unwrap()).unwrap();
    let source = |value| {
        format!(
            r#"
                value() -> i64 {{ {value} }}
                main() -> () {{
                    let current = value();
                    if current == 1 {{
                        __g1_fs_write({observed_path}, String::as_bytes(&"one"));
                    }} else {{
                        __g1_fs_write({observed_path}, String::as_bytes(&"two"));
                    }};
                    ()
                }}
            "#
        )
    };
    let arguments = |output: &Path| {
        serde_json::json!([
            "-O3",
            "--emit",
            "executable",
            "--native-incremental",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    write(&input, &source(1));
    let mut session = Session::start();
    let cold = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": arguments(&first_executable),
    }));
    assert_eq!(cold["status"], 0, "{cold}");
    assert_eq!(cold["native_incremental"]["wild_relink"], true, "{cold}");
    assert_eq!(cold["native_incremental"]["strategy"], "partitioned-function-objects", "{cold}");
    assert_eq!(cold["native_incremental"]["native_objects_reused"], 0, "{cold}");
    assert!(cold["native_incremental"]["native_objects_emitted"].as_u64().unwrap() >= 3, "{cold}");
    assert!(first_executable.is_file());
    assert!(Command::new(&first_executable).status().unwrap().success());
    assert_eq!(fs::read(&observed).unwrap(), b"one");

    write(&input, &source(2));
    let edited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 2,
        "method": "compile",
        "arguments": arguments(&second_executable),
    }));
    assert_eq!(edited["status"], 0, "{edited}");
    assert_eq!(edited["native_incremental"]["wild_relink"], true, "{edited}");
    assert_eq!(edited["native_incremental"]["strategy"], "partitioned-function-objects", "{edited}");
    assert!(edited["native_incremental"]["function_objects_reused"].as_u64().unwrap() >= 1, "{edited}");
    // The edited leaf must be recompiled; the unchanged entry object is
    // retained. Shared runtime bytes may be independently re-emitted only
    // when generated globals change.
    assert!(edited["native_incremental"]["function_objects_compiled"].as_u64().unwrap() >= 1, "{edited}");
    assert!(second_executable.is_file());
    assert!(Command::new(&second_executable).status().unwrap().success());
    assert_eq!(fs::read(&observed).unwrap(), b"two");
}

#[test]
fn persistent_serve_separates_native_object_cache_entries_by_optimization_level() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("cache.glorious");
    let o0_output = directory.path().join("o0.o");
    let o3_output = directory.path().join("o3.o");
    let warm_o3_output = directory.path().join("warm-o3.o");
    write(
        &input,
        "leaf(value: i64) -> i64 { value + 1 } main() -> () { leaf(41); () }",
    );
    let arguments = |optimization: &str, output: &Path| {
        serde_json::json!([
            optimization,
            "--emit",
            "llvm-object",
            "-o",
            output.display().to_string(),
            input.display().to_string(),
        ])
    };
    let mut session = Session::start();

    let cold_o0 = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": arguments("-O0", &o0_output),
    }));
    assert_eq!(cold_o0["status"], 0, "{cold_o0}");
    assert_eq!(cold_o0["native_object_cache"], "miss", "{cold_o0}");

    let cold_o3 = session.request(serde_json::json!({
        "protocol": 1,
        "id": 2,
        "method": "compile",
        "arguments": arguments("-O3", &o3_output),
    }));
    assert_eq!(cold_o3["status"], 0, "{cold_o3}");
    assert_eq!(cold_o3["llvm_ir_cache"], "miss", "{cold_o3}");
    assert_eq!(cold_o3["native_object_cache"], "miss", "{cold_o3}");

    let warm_o3 = session.request(serde_json::json!({
        "protocol": 1,
        "id": 3,
        "method": "compile",
        "arguments": arguments("-O3", &warm_o3_output),
    }));
    assert_eq!(warm_o3["status"], 0, "{warm_o3}");
    assert_eq!(warm_o3["llvm_ir_cache"], "hit", "{warm_o3}");
    assert_eq!(warm_o3["native_object_cache"], "hit", "{warm_o3}");
    assert_eq!(fs::read(&warm_o3_output).unwrap(), fs::read(&o3_output).unwrap());
}

#[test]
fn multiple_inputs_compile_in_argument_order_at_every_optimization_level() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let additional = directory.path().join("helper.glorious");
    write(&primary, "answer() -> i64 { helper() } main() -> () { () }");
    write(&additional, "helper() -> i64 { 42 }");

    for level in ["-O0", "-O1", "-O2", "-O3"] {
        let output = directory.path().join(format!("answer-{level}.grbc"));
        let result = grc()
            .args([level, "--emit", "grbc", "-o"])
            .arg(&output)
            .arg(&primary)
            .arg(&additional)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{level}: {}",
            String::from_utf8_lossy(&result.stderr)
        );
        let artifact = Artifact::decode(&fs::read(output).unwrap()).unwrap();
        verify(artifact).unwrap();
    }
}

#[test]
fn crate_root_recursively_discovers_declared_hybrid_modules() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("app.glorious");
    let math_directory = directory.path().join("math");
    let nested_directory = math_directory.join("nested");
    fs::create_dir_all(&nested_directory).unwrap();
    write(
        &primary,
        "mod math; use crate::math::answer; probe() -> i64 { answer() } main() -> () { () }",
    );
    write(
        &math_directory.join("math.glorious"),
        "pub mod nested; pub answer() -> i64 { nested::value() }",
    );
    write(
        &nested_directory.join("nested.glorious"),
        "pub value() -> i64 { 42 }",
    );

    let output = directory.path().join("app.grbc");
    let result = grc()
        .args(["--emit", "grbc", "-o"])
        .arg(&output)
        .arg(&primary)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    verify(Artifact::decode(&fs::read(output).unwrap()).unwrap()).unwrap();

    let mut session = Session::start();
    let checked = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": ["--phase", "check", primary.display().to_string()]
    }));
    assert_eq!(checked["status"], 0, "{checked}");
    assert_eq!(checked["transaction"], "committed");
}

#[test]
fn named_dependency_roots_are_isolated_and_discover_their_own_modules() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("app.glorious");
    let dependency = directory.path().join("math-lib");
    let child = dependency.join("values");
    fs::create_dir_all(&child).unwrap();
    let dependency_root = dependency.join("lib.glorious");
    write(
        &primary,
        "use math_lib::answer; probe() -> i64 { answer() } main() -> () { () }",
    );
    write(
        &dependency_root,
        "pub mod values; pub answer() -> i64 { crate::values::answer() }",
    );
    write(&child.join("values.glorious"), "pub answer() -> i64 { 42 }");

    let checked = grc()
        .args(["--phase", "check", "--dependency"])
        .arg(format!("math-lib={}", dependency_root.display()))
        .arg(&primary)
        .output()
        .unwrap();
    assert!(
        checked.status.success(),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );

    let mut session = Session::start();
    let checked = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": [
            "--phase",
            "check",
            "--dependency",
            format!("math-lib={}", dependency_root.display()),
            primary.display().to_string()
        ]
    }));
    assert_eq!(checked["status"], 0, "{checked}");
    assert_eq!(checked["transaction"], "committed");
}

#[test]
fn check_only_writes_no_default_artifact() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("checked.glorious");
    write(&input, "main() -> () { () }");

    let result = grc().arg("--check").arg(&input).output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert!(!input.with_extension("grbc").exists());
}

#[test]
fn unreachable_handler_rows_are_successful_localized_warnings() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("warning.glorious");
    write(
        &input,
        r#"
            enum State { Hot, Cold }
            effect Pick { pick(value: State) -> ! }
            selected() -> i64 {
                handle perform Pick::pick(State::Hot) {
                    Pick::pick(_) => 42,
                    Pick::pick(State::Hot) => 0
                }
            }
            main() -> { selected(); () }
        "#,
    );

    let human = grc().arg("--check").arg(&input).output().unwrap();
    assert!(
        human.status.success(),
        "{}",
        String::from_utf8_lossy(&human.stderr)
    );
    let human_stderr = String::from_utf8_lossy(&human.stderr);
    assert!(human_stderr.contains("G1PW001"), "{human_stderr}");
    assert!(
        human_stderr.contains("unreachable handler pattern"),
        "{human_stderr}"
    );

    let json = grc()
        .args(["--check", "--diagnostics", "json"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        json.status.success(),
        "{}",
        String::from_utf8_lossy(&json.stderr)
    );
    let diagnostic: serde_json::Value =
        serde_json::from_slice(json.stderr.split(|byte| *byte == b'\n').next().unwrap()).unwrap();
    assert_eq!(diagnostic["severity"], "warning");
    assert_eq!(diagnostic["code"], "G1PW001");
    assert_eq!(diagnostic["labels"][0]["file"], input.display().to_string());
    assert!(!input.with_extension("grbc").exists());
}

#[test]
fn early_stop_phases_do_not_run_later_semantic_work_or_write_artifacts() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("phase.glorious");
    write(&input, "main() -> {");

    let lexed = grc().args(["--phase", "lex"]).arg(&input).output().unwrap();
    assert!(
        lexed.status.success(),
        "{}",
        String::from_utf8_lossy(&lexed.stderr)
    );
    assert!(!input.with_extension("grbc").exists());

    let malformed_scan = grc()
        .args(["--phase", "scan"])
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(malformed_scan.status.code(), Some(1));

    write(
        &input,
        "helper() -> i64 { unknown_name } main() -> () { () }",
    );
    let scanned = grc()
        .args(["--phase", "scan"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        scanned.status.success(),
        "{}",
        String::from_utf8_lossy(&scanned.stderr)
    );

    let checked = grc()
        .args(["--phase", "check"])
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(checked.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&checked.stderr).contains("unknown_name"),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );
}

#[test]
fn resolve_is_between_interface_scan_and_body_ownership_with_localized_json() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let library = directory.path().join("library.glorious");
    write(&primary, "main() -> () { () }");
    write(&library, "helper(value: MissingType) -> () { () }");

    let scanned = grc()
        .args(["--phase", "scan"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert!(
        scanned.status.success(),
        "{}",
        String::from_utf8_lossy(&scanned.stderr)
    );

    let resolved = grc()
        .args(["--diagnostics", "json", "--phase", "resolve"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert_eq!(resolved.status.code(), Some(1));
    let diagnostic: serde_json::Value =
        serde_json::from_slice(resolved.stderr.split(|byte| *byte == b'\n').next().unwrap())
            .unwrap();
    assert_eq!(diagnostic["code"], "G1R001");
    assert_eq!(
        diagnostic["labels"][0]["file"],
        library.display().to_string(),
        "{}",
        String::from_utf8_lossy(&resolved.stderr)
    );
    assert_eq!(diagnostic["labels"][0]["line"], 1);
    assert!(!primary.with_extension("grbc").exists());

    write(&library, "helper() -> i64 { missing_value }");
    let resolved_name = grc()
        .args(["--diagnostics", "json", "--phase", "resolve"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert_eq!(resolved_name.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&resolved_name.stderr).contains("missing_value"),
        "{}",
        String::from_utf8_lossy(&resolved_name.stderr)
    );

    write(
        &library,
        "struct Token {}\nimpl Use<[1,1]> for Token {}\nignore(value: Token) -> () { () }\n",
    );
    let resolved = grc()
        .args(["--phase", "resolve"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert!(
        resolved.status.success(),
        "{}",
        String::from_utf8_lossy(&resolved.stderr)
    );
    assert!(!primary.with_extension("grbc").exists());

    let checked = grc()
        .args(["--phase", "check"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert_eq!(checked.status.code(), Some(1));
    assert!(
        String::from_utf8_lossy(&checked.stderr).contains("Use count 0"),
        "{}",
        String::from_utf8_lossy(&checked.stderr)
    );

    write(
        &library,
        "relay<T, L>(value: T, destination: L) -> ! where L: Label<T> { destination(value) }",
    );
    let resolved_label = grc()
        .args(["--phase", "resolve"])
        .args([&primary, &library])
        .output()
        .unwrap();
    assert!(
        resolved_label.status.success(),
        "{}",
        String::from_utf8_lossy(&resolved_label.stderr)
    );
}

#[test]
fn resolve_scopes_is_pattern_binders_to_only_the_positive_branch() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("main.glorious");

    write(
        &input,
        "probe(value: Result<i64, i64>) -> i64 { if(value is Result::Ok(found)) { found } else { 0 } } main() -> () { () }",
    );
    let positive = grc()
        .args(["--phase", "resolve"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        positive.status.success(),
        "{}",
        String::from_utf8_lossy(&positive.stderr)
    );

    for source in [
        "probe(value: Result<i64, i64>) -> i64 { if(value is Result::Ok(found)) { 1 } else { found } } main() -> () { () }",
        "probe(value: Result<i64, i64>) -> i64 { let selected = if(value is Result::Ok(found)) { found } else { 0 }; found } main() -> () { () }",
    ] {
        write(&input, source);
        let invalid = grc()
            .args(["--diagnostics", "json", "--phase", "resolve"])
            .arg(&input)
            .output()
            .unwrap();
        assert_eq!(invalid.status.code(), Some(1));
        let diagnostic: serde_json::Value =
            serde_json::from_slice(invalid.stderr.split(|byte| *byte == b'\n').next().unwrap())
                .unwrap();
        assert_eq!(diagnostic["code"], "G1R001", "{diagnostic}");
        assert!(
            String::from_utf8_lossy(&invalid.stderr).contains("found"),
            "{diagnostic}"
        );
    }
}

#[test]
fn textual_phase_outputs_are_deterministic_and_use_kind_aware_defaults() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("phases.glorious");
    write(&input, "main() -> () { () }");

    for (kind, extension, marker) in [
        ("mir", "mir", "fn#"),
        ("core", "core", "fn#"),
        ("provisional", "provisional", "main"),
    ] {
        let first = grc().args(["--emit", kind]).arg(&input).output().unwrap();
        assert!(
            first.status.success(),
            "{kind}: {}",
            String::from_utf8_lossy(&first.stderr)
        );
        let path = input.with_extension(extension);
        let expected = fs::read(&path).unwrap();
        assert!(!expected.is_empty(), "{kind} output was empty");
        assert!(
            String::from_utf8_lossy(&expected).contains(marker),
            "{kind} output did not contain `{marker}`"
        );

        fs::remove_file(&path).unwrap();
        let second = grc()
            .arg(format!("--emit={kind}"))
            .arg(&input)
            .output()
            .unwrap();
        assert!(second.status.success());
        assert_eq!(fs::read(path).unwrap(), expected, "{kind} was unstable");
    }
}

#[test]
fn control_plan_emission_is_deterministic_and_reports_fusion_residuals() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("control.glorious");
    write(
        &input,
        r#"
            custom_walk<L, F>(index: usize, limit: usize, exit: L, body: F)
            where L: Label<usize>, F: Fn<(usize, L), Output = ()> {
                handle index == limit {
                    true => (),
                    false => {
                        body(index, exit);
                        custom_walk(index + 1, limit, exit, body)
                    }
                }
            }
            answer() -> usize {
                @done: usize {
                    custom_walk(0, 2, @done, { index, done =>
                        if(index == 1) { done(7) } else { () }
                    });
                    90
                }
            }
            main() -> () { () }
        "#,
    );

    let first = grc()
        .args(["--emit", "control-plan"])
        .arg(&input)
        .output()
        .unwrap();
    assert!(
        first.status.success(),
        "{}",
        String::from_utf8_lossy(&first.stderr)
    );
    let output = input.with_extension("control-plan");
    let expected = fs::read_to_string(&output).unwrap();
    assert!(expected.contains("helper: custom_walk"), "{expected}");
    assert!(expected.contains("tail-recursive cycle: yes"), "{expected}");
    assert!(
        expected.contains("formed control loop: control#"),
        "{expected}"
    );
    assert!(
        expected.contains("residual callable allocation: no"),
        "{expected}"
    );
    assert!(
        expected.contains("residual effect handler: no"),
        "{expected}"
    );
    assert!(expected.contains("failure reason: —"), "{expected}");

    fs::remove_file(&output).unwrap();
    let second = grc()
        .arg("--emit=control-plan")
        .arg(&input)
        .output()
        .unwrap();
    assert!(second.status.success());
    assert_eq!(fs::read_to_string(output).unwrap(), expected);
}

#[test]
fn diagnostics_are_mapped_to_the_failing_additional_input() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let additional = directory.path().join("broken.glorious");
    write(&primary, "main() -> () { () }");
    write(&additional, "broken() -> i64 { unknown_name }");

    let result = grc()
        .arg("--check")
        .arg(&primary)
        .arg(&additional)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    let stderr = String::from_utf8_lossy(&result.stderr);
    assert!(
        stderr.contains(&additional.display().to_string()),
        "{stderr}"
    );
    assert!(stderr.contains("unknown_name"), "{stderr}");
}

#[test]
fn usage_errors_have_exit_status_two() {
    let result = grc().arg("--not-an-option").output().unwrap();
    assert_eq!(result.status.code(), Some(2));
    assert!(String::from_utf8_lossy(&result.stderr).contains("unknown compiler option"));
}

#[test]
fn capabilities_advertise_only_the_implemented_contract() {
    let result = grc().arg("--capabilities").output().unwrap();
    assert!(result.status.success());
    let stdout = String::from_utf8(result.stdout).unwrap();
    assert!(stdout.contains("\"contract\":1"), "{stdout}");
    assert!(stdout.contains("\"contract-min\":1"), "{stdout}");
    assert!(stdout.contains("\"contract-max\":1"), "{stdout}");
    assert!(stdout.contains("\"artifact-major\":1"), "{stdout}");
    assert!(stdout.contains("\"artifact-minor\":0"), "{stdout}");
    assert!(
        stdout.contains(&format!(
            "\"seed-identity-version\":{}",
            grandiose_vm::SEED_IDENTITY_VERSION
        )),
        "{stdout}"
    );
    assert!(
        stdout.contains(&format!(
            "\"seed-identity\":\"{}\"",
            grandiose_vm::RELEASED_SEED_IDENTITY
        )),
        "{stdout}"
    );
    assert!(stdout.contains("\"multi-file\":true"), "{stdout}");
    assert!(stdout.contains("\"modules\":true"), "{stdout}");
    assert!(
        stdout.contains("\"phases\":[\"lex\",\"scan\",\"resolve\",\"check\"]"),
        "{stdout}"
    );
    assert!(stdout.contains("\"mir\""), "{stdout}");
    assert!(stdout.contains("\"interfaces-json\""), "{stdout}");
    assert!(stdout.contains("\"diagnostics-json\":true"), "{stdout}");
    let capabilities: serde_json::Value = serde_json::from_str(&stdout).unwrap();
    assert_eq!(capabilities["serve"]["protocol"], 1);
    assert_eq!(capabilities["serve"]["transport"], "json-lines");
    assert_eq!(capabilities["serve"]["max-request-bytes"], 1024 * 1024);
    assert_eq!(capabilities["serve"]["max-inputs"], 64);
    assert_eq!(capabilities["serve"]["max-source-bytes"], 16 * 1024 * 1024);
}

#[test]
fn session_resolve_check_and_compile_match_one_shot_and_commit_transactionally() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("session.glorious");
    let one_shot_artifact = directory.path().join("one-shot.grbc");
    let session_artifact = directory.path().join("session.grbc");
    write(&input, "main() -> () { () }");

    let one_shot = grc()
        .args(["--emit", "bytecode", "-o"])
        .arg(&one_shot_artifact)
        .arg(&input)
        .output()
        .unwrap();
    assert!(one_shot.status.success());

    let mut session = Session::start();
    let compiled = session.request(serde_json::json!({
        "protocol": 1,
        "id": 1,
        "method": "compile",
        "arguments": [
            "--emit", "bytecode", "-o",
            session_artifact.display().to_string(),
            input.display().to_string()
        ]
    }));
    assert_eq!(compiled["status"], 0, "{compiled}");
    assert_eq!(compiled["transaction"], "committed");
    assert_eq!(compiled["generation"], 1);
    assert_eq!(
        fs::read(&session_artifact).unwrap(),
        fs::read(&one_shot_artifact).unwrap()
    );

    for (id, phase) in [(2, "resolve"), (3, "check")] {
        let response = session.request(serde_json::json!({
            "protocol": 1,
            "id": id,
            "method": "compile",
            "arguments": ["--diagnostics", "json", "--phase", phase, input.display().to_string()]
        }));
        assert_eq!(response["status"], 0, "{response}");
        assert_eq!(response["transaction"], "committed");
        assert_eq!(response["generation"], id);
    }

    let unchanged = session.request(serde_json::json!({
        "protocol": 1,
        "id": 4,
        "method": "compile",
        "arguments": ["--diagnostics", "json", "--phase", "check", input.display().to_string()]
    }));
    assert_eq!(unchanged["status"], 0);
    assert_eq!(unchanged["transaction"], "unchanged");
    assert_eq!(unchanged["generation"], 3);

    write(&input, "main() -> () { missing_name }");
    let one_shot_failure = grc()
        .args(["--diagnostics", "json", "--phase", "check"])
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(one_shot_failure.status.code(), Some(1));
    let failed = session.request(serde_json::json!({
        "protocol": 1,
        "id": 5,
        "method": "compile",
        "arguments": ["--diagnostics", "json", "--phase", "check", input.display().to_string()]
    }));
    assert_eq!(failed["status"], 1, "{failed}");
    assert_eq!(failed["transaction"], "retained");
    assert_eq!(failed["generation"], 3);
    assert_eq!(
        failed["stderr"],
        String::from_utf8(one_shot_failure.stderr).unwrap()
    );
    assert_ne!(
        failed["source_fingerprint"], unchanged["source_fingerprint"],
        "an edited bundle was served from stale state"
    );

    write(&input, "main() -> () { () }");
    let recovered = session.request(serde_json::json!({
        "protocol": 1,
        "id": 6,
        "method": "compile",
        "arguments": ["--diagnostics", "json", "--phase", "check", input.display().to_string()]
    }));
    assert_eq!(recovered["status"], 0, "{recovered}");
    assert_eq!(recovered["transaction"], "unchanged");
    assert_eq!(recovered["generation"], 3);

    let shutdown = session.request(serde_json::json!({
        "protocol": 1,
        "id": 7,
        "method": "shutdown"
    }));
    assert_eq!(shutdown["status"], 0);
    assert!(session.child.wait().unwrap().success());
}

#[test]
fn session_protocol_errors_and_resource_limits_do_not_poison_the_process() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("healthy.glorious");
    write(&input, "main() -> () { () }");
    let mut session = Session::start();

    let malformed = session.raw("{not-json");
    assert_eq!(malformed["status"], 2);
    assert_eq!(malformed["id"], serde_json::Value::Null);
    let wrong_version = session.request(serde_json::json!({
        "protocol": 2,
        "id": 2,
        "method": "compile",
        "arguments": ["--phase", "check", input.display().to_string()]
    }));
    assert_eq!(wrong_version["status"], 2);
    assert!(
        wrong_version["stderr"]
            .as_str()
            .unwrap()
            .contains("incompatible")
    );
    let unknown = session.request(serde_json::json!({
        "protocol": 1,
        "id": 3,
        "method": "unknown"
    }));
    assert_eq!(unknown["status"], 2);

    let arguments = vec!["ignored"; 129];
    let limited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 4,
        "method": "compile",
        "arguments": arguments
    }));
    assert_eq!(limited["status"], 2);
    assert!(
        limited["stderr"]
            .as_str()
            .unwrap()
            .contains("argument-count")
    );

    let oversized = session.raw(&"x".repeat(1024 * 1024 + 1));
    assert_eq!(oversized["status"], 2);
    assert!(
        oversized["stderr"]
            .as_str()
            .unwrap()
            .contains("request exceeds session byte limit")
    );

    let oversized_source = directory.path().join("oversized.glorious");
    fs::File::create(&oversized_source)
        .unwrap()
        .set_len(16 * 1024 * 1024 + 1)
        .unwrap();
    let source_limited = session.request(serde_json::json!({
        "protocol": 1,
        "id": 5,
        "method": "compile",
        "arguments": ["--phase", "lex", oversized_source.display().to_string()]
    }));
    assert_eq!(source_limited["status"], 1);
    assert!(
        source_limited["stderr"]
            .as_str()
            .unwrap()
            .contains("source-byte limit exceeded")
    );

    let healthy = session.request(serde_json::json!({
        "protocol": 1,
        "id": 6,
        "method": "compile",
        "arguments": ["--phase", "check", input.display().to_string()]
    }));
    assert_eq!(healthy["status"], 0, "{healthy}");
    assert_eq!(healthy["generation"], 1);
}

#[test]
fn session_invalidates_when_any_source_bundle_segment_changes() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let helper = directory.path().join("helper.glorious");
    write(&primary, "main() -> () { helper() }");
    write(&helper, "helper() -> () { () }");
    let mut session = Session::start();
    let request = |id| {
        serde_json::json!({
            "protocol": 1,
            "id": id,
            "method": "compile",
            "arguments": [
                "--diagnostics", "json", "--phase", "check",
                primary.display().to_string(), helper.display().to_string()
            ]
        })
    };
    let initial = session.request(request(1));
    assert_eq!(initial["status"], 0, "{initial}");
    assert_eq!(initial["generation"], 1);

    write(&helper, "helper() -> () { missing_name }");
    let invalidated = session.request(request(2));
    assert_eq!(invalidated["status"], 1, "{invalidated}");
    assert_eq!(invalidated["generation"], 1);
    assert_eq!(invalidated["transaction"], "retained");
    assert_ne!(
        invalidated["source_fingerprint"],
        initial["source_fingerprint"]
    );

    write(&helper, "helper() -> () { () }");
    let restored = session.request(request(3));
    assert_eq!(restored["status"], 0, "{restored}");
    assert_eq!(restored["transaction"], "unchanged");
    assert_eq!(restored["generation"], 1);
}

#[test]
fn crashed_session_restart_never_reuses_stale_last_good_sources() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("restart.glorious");
    write(&input, "main() -> () { () }");
    let request = |id| {
        serde_json::json!({
            "protocol": 1,
            "id": id,
            "method": "compile",
            "arguments": ["--diagnostics", "json", "--phase", "check", input.display().to_string()]
        })
    };

    let mut first = Session::start();
    let committed = first.request(request(1));
    assert_eq!(committed["status"], 0);
    assert_eq!(committed["generation"], 1);
    first.kill_and_wait();

    write(&input, "main() -> () { missing_name }");
    let mut restarted = Session::start();
    let failed = restarted.request(request(2));
    assert_eq!(failed["status"], 1, "{failed}");
    assert_eq!(failed["transaction"], "retained");
    assert_eq!(failed["generation"], 0);

    write(&input, "main() -> () { () }");
    let recovered = restarted.request(request(3));
    assert_eq!(recovered["status"], 0, "{recovered}");
    assert_eq!(recovered["generation"], 1);
}

#[test]
fn interface_emission_uses_parser_spans_and_separates_the_standard_library() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let additional = directory.path().join("library.glorious");
    write(&primary, "// Entry.\nmain() -> () { () }");
    write(
        &additional,
        "// Public helper.\nhelper(value: i64) -> i64 { value }",
    );

    let result = grc()
        .args(["--emit", "interfaces-json"])
        .arg(&primary)
        .arg(&additional)
        .output()
        .unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    let declarations: serde_json::Value = serde_json::from_slice(&result.stdout).unwrap();
    let declarations = declarations.as_array().unwrap();
    assert!(declarations.iter().any(|declaration| {
        declaration["name"] == "helper"
            && declaration["identity"] == "user:value:helper"
            && declaration["file"] == additional.display().to_string()
            && declaration["line"] == 2
            && declaration["docs"] == "Public helper."
            && declaration["declaration_start_byte"] == 18
            && declaration["name_start_byte"] == 18
            && declaration["name_end_byte"] == 24
    }));
    assert!(
        !declarations
            .iter()
            .any(|declaration| declaration["file"] == "<grandiose:std>")
    );

    let standard = grc()
        .args(["--emit", "std-interfaces-json"])
        .output()
        .unwrap();
    assert!(standard.status.success());
    let declarations: serde_json::Value = serde_json::from_slice(&standard.stdout).unwrap();
    assert!(
        declarations
            .as_array()
            .unwrap()
            .iter()
            .all(|declaration| declaration["file"] == "<grandiose:std>")
    );
}

#[test]
fn json_diagnostics_use_local_files_and_byte_offsets() {
    let directory = tempdir().unwrap();
    let primary = directory.path().join("main.glorious");
    let additional = directory.path().join("broken.glorious");
    write(&primary, "main() -> () { () }");
    write(&additional, "broken() -> i64 { unknown_name }");

    let result = grc()
        .args(["--diagnostics", "json", "--phase", "check"])
        .arg(&primary)
        .arg(&additional)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(1));
    let lines = String::from_utf8(result.stderr).unwrap();
    let diagnostic: serde_json::Value = serde_json::from_str(lines.trim()).unwrap();
    assert_eq!(diagnostic["severity"], "error");
    assert_eq!(
        diagnostic["labels"][0]["file"],
        additional.display().to_string()
    );
    assert_eq!(diagnostic["labels"][0]["start_byte"], 18);
    assert_eq!(diagnostic["labels"][0]["end_byte"], 30);
}

#[test]
fn source_evaluator_command_is_not_exposed() {
    let directory = tempdir().unwrap();
    let input = directory.path().join("runner.glorious");
    write(&input, "main() -> () { () }");
    let result = Command::new(env!("CARGO_BIN_EXE_grandiose"))
        .arg("run")
        .arg(&input)
        .output()
        .unwrap();
    assert_eq!(result.status.code(), Some(2));
    let stderr = String::from_utf8(result.stderr).unwrap();
    assert!(stderr.contains("must use the `.glorious` extension"));
    assert!(!stderr.contains("grandiose run <program"));
}
