//! Scripted end-to-end LSP session against the real binary over stdio.

use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};
use std::time::{Duration, Instant};

use serde_json::{Value, json};
use tempfile::TempDir;

struct Session {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    next_id: i64,
}

impl Session {
    fn start(cwd: &Path) -> Session {
        Self::start_with_delay(cwd, None)
    }

    fn start_with_delay(cwd: &Path, delay_ms: Option<u64>) -> Session {
        let mut command = Command::new(env!("CARGO_BIN_EXE_grand-lsp"));
        command
            .current_dir(cwd)
            .env("GRAND_CACHE_DIR", cwd.join(".grand-cache"))
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null());
        if let Some(delay_ms) = delay_ms {
            command.env("GRAND_LSP_TEST_ANALYSIS_DELAY_MS", delay_ms.to_string());
        }
        let mut child = command.spawn().unwrap();
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Session {
            child,
            stdin,
            stdout,
            next_id: 0,
        }
    }

    fn send(&mut self, message: Value) {
        let body = serde_json::to_vec(&message).unwrap();
        write!(self.stdin, "Content-Length: {}\r\n\r\n", body.len()).unwrap();
        self.stdin.write_all(&body).unwrap();
        self.stdin.flush().unwrap();
    }

    fn notify(&mut self, method: &str, params: Value) {
        self.send(json!({"jsonrpc": "2.0", "method": method, "params": params}));
    }

    /// Send a request and pump messages until its response arrives; interleaved
    /// notifications are returned too so tests can inspect them.
    fn request(&mut self, method: &str, params: Value) -> (Value, Vec<Value>) {
        self.next_id += 1;
        let id = self.next_id;
        self.send(json!({"jsonrpc": "2.0", "id": id, "method": method, "params": params}));
        let mut notifications = Vec::new();
        loop {
            let message = self.receive();
            if message["id"].as_i64() == Some(id) {
                return (message["result"].clone(), notifications);
            }
            notifications.push(message);
        }
    }

    fn receive(&mut self) -> Value {
        let mut length = None;
        loop {
            let mut line = String::new();
            assert!(
                self.stdout.read_line(&mut line).unwrap() > 0,
                "server closed stdout"
            );
            let line = line.trim_end();
            if line.is_empty() {
                break;
            }
            if let Some(value) = line.strip_prefix("Content-Length:") {
                length = Some(value.trim().parse::<usize>().unwrap());
            }
        }
        let mut body = vec![0u8; length.unwrap()];
        self.stdout.read_exact(&mut body).unwrap();
        serde_json::from_slice(&body).unwrap()
    }

    /// Pump notifications until a publishDiagnostics for `suffix` arrives.
    fn diagnostics_for(&mut self, suffix: &str) -> Vec<Value> {
        for _ in 0..50 {
            let message = self.receive();
            if message["method"] == "textDocument/publishDiagnostics"
                && message["params"]["uri"]
                    .as_str()
                    .unwrap_or_default()
                    .ends_with(suffix)
            {
                return message["params"]["diagnostics"].as_array().unwrap().clone();
            }
        }
        panic!("no publishDiagnostics for {suffix}");
    }
}

#[test]
fn superseded_background_analysis_neither_blocks_requests_nor_publishes() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    let main = project(&root, "app", "main() -> () { () }");
    let mut session = Session::start_with_delay(&root, Some(700));
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));

    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1,
            "text": "main() -> () { () }"
        }}),
    );
    assert!(session.diagnostics_for("main.glorious").is_empty());
    let started = Instant::now();
    session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main)},
               "position": {"line": 0, "character": 0}}),
    );
    assert!(
        started.elapsed() < Duration::from_millis(400),
        "request after matching diagnostics triggered a second analysis"
    );
    let started = Instant::now();
    session.request(
        "textDocument/inlayHint",
        json!({"textDocument": {"uri": uri(&main)},
        "range": {
            "start": {"line": 0, "character": 0},
            "end": {"line": 0, "character": 24}
        }}),
    );
    assert!(
        started.elapsed() < Duration::from_millis(400),
        "inlay hints after matching diagnostics triggered a second analysis"
    );
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 2},
               "contentChanges": [{"text": "main( -> () {"}]}),
    );
    // Let the debounce expire so the broken generation is genuinely running, then
    // supersede it while the artificial slow analysis is in flight.
    std::thread::sleep(Duration::from_millis(250));
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 3},
               "contentChanges": [{"text": "main() -> () { () }"}]}),
    );

    let started = Instant::now();
    let (_hover, notifications) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main)},
               "position": {"line": 0, "character": 1}}),
    );
    assert!(
        started.elapsed() < Duration::from_millis(400),
        "semantic request waited for stale background compilation"
    );
    assert!(
        notifications
            .iter()
            .all(|message| { message["method"] != "textDocument/publishDiagnostics" })
    );

    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "superseded broken generation was published: {diagnostics:?}"
    );
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
    }
}

fn project(root: &Path, name: &str, source: &str) -> std::path::PathBuf {
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        format!(
            "[project]\nname = \"{name}\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n"
        ),
    )
    .unwrap();
    let main = root.join("src/main.glorious");
    std::fs::write(&main, source).unwrap();
    main
}

fn uri(path: &Path) -> String {
    format!("file://{}", path.display())
}

fn decoded_semantic_tokens(value: &Value) -> Vec<(u32, u32, u32, u32)> {
    let data = value["data"].as_array().unwrap();
    let mut line = 0;
    let mut start = 0;
    data.chunks_exact(5)
        .map(|token| {
            let delta_line = token[0].as_u64().unwrap() as u32;
            let delta_start = token[1].as_u64().unwrap() as u32;
            line += delta_line;
            start = if delta_line == 0 {
                start + delta_start
            } else {
                delta_start
            };
            (
                line,
                start,
                token[2].as_u64().unwrap() as u32,
                token[3].as_u64().unwrap() as u32,
            )
        })
        .collect()
}

#[test]
fn full_session() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/helpers.glorious"),
        "// Consumes a value, allegedly.\nhelper(value: i64) -> () { () }\n",
    )
    .unwrap();
    let main_path = root.join("src/main.glorious");
    std::fs::write(&main_path, "main() -> () {\n    helper(0)\n}\n").unwrap();

    let mut session = Session::start(&root);
    let (result, _) = session.request("initialize", json!({"rootUri": uri(&root)}));
    assert_eq!(result["capabilities"]["textDocumentSync"], 1);
    assert_eq!(result["capabilities"]["inlayHintProvider"], true);
    assert_eq!(result["serverInfo"]["name"], "grand-lsp");
    session.notify("initialized", json!({}));

    // Open a broken revision: expect an error diagnostic on main.glorious.
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main_path), "languageId": "grandiose", "version": 1,
            "text": "main( -> () {\n",
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(!diagnostics.is_empty(), "expected a parse error");
    assert_eq!(
        diagnostics[0]["severity"], 1,
        "expected error severity: {diagnostics:?}"
    );
    assert_eq!(diagnostics[0]["source"], "grandiose");

    // Fix the file: diagnostics clear.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 2},
               "contentChanges": [{"text": "main() -> () {\n    helper(0)\n}\n"}]}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "diagnostics did not clear: {diagnostics:?}"
    );

    // Document symbols for main.glorious.
    let (symbols, _) = session.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri(&main_path)}}),
    );
    let names: Vec<&str> = symbols
        .as_array()
        .unwrap()
        .iter()
        .map(|s| s["name"].as_str().unwrap())
        .collect();
    assert_eq!(names, vec!["main"], "unexpected symbols: {names:?}");

    // Go-to-definition on `helper` inside main.glorious lands in helpers.glorious.
    let (definition, _) = session.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    assert!(
        definition["uri"]
            .as_str()
            .unwrap()
            .ends_with("helpers.glorious"),
        "definition wrong: {definition}"
    );
    assert_eq!(definition["range"]["start"]["line"], 1); // below the doc comment

    // Hover shows the signature and the doc comment.
    let (hover, _) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    let markdown = hover["contents"]["value"].as_str().unwrap();
    assert!(
        markdown.contains("helper(value: i64) -> ()"),
        "hover: {markdown}"
    );
    assert!(
        markdown.contains("Consumes a value"),
        "hover missing docs: {markdown}"
    );

    // Completion offers workspace declarations and keywords.
    let (completions, _) = session.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    let labels: Vec<&str> = completions
        .as_array()
        .unwrap()
        .iter()
        .map(|c| c["label"].as_str().unwrap())
        .collect();
    assert!(
        labels.contains(&"helper") && labels.contains(&"main"),
        "completions: {labels:?}"
    );
    assert!(labels.contains(&"handle"), "keywords missing: {labels:?}");

    // Resilient parsing: two broken declarations produce two diagnostics.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 3},
               "contentChanges": [{"text":
            "first( -> i64 {\n    1\n}\nsecond( -> i64 {\n    2\n}\nvalid() -> i64 { helper(1) }\n"}]}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.len() >= 2,
        "resilient parser should report multiple errors: {diagnostics:?}"
    );

    // Locals: definition/hover of a `let` binding and completion including it.
    let body = "main() -> () {\n    let first = helper(1)\n    first\n}\n";
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 4},
               "contentChanges": [{"text": body}]}),
    );
    // line 2 is `    first` — resolve the usage back to the let binding.
    let (definition, _) = session.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 2, "character": 5}}),
    );
    assert!(
        definition["uri"]
            .as_str()
            .unwrap()
            .ends_with("main.glorious"),
        "{definition}"
    );
    assert_eq!(
        definition["range"]["start"]["line"], 1,
        "local def wrong: {definition}"
    );
    let (hover, _) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 2, "character": 5}}),
    );
    assert!(
        hover["contents"]["value"].as_str().unwrap().contains("()"),
        "local hover: {hover}"
    );

    // References: `helper` appears in helpers.glorious (definition) and main.glorious (call).
    let (references, _) = session.request(
        "textDocument/references",
        json!({"textDocument": {"uri": uri(&main_path)},
               "position": {"line": 1, "character": 17},
               "context": {"includeDeclaration": true}}),
    );
    let reference_files: Vec<&str> = references
        .as_array()
        .unwrap()
        .iter()
        .map(|l| l["uri"].as_str().unwrap())
        .collect();
    assert!(
        reference_files
            .iter()
            .any(|u| u.ends_with("helpers.glorious"))
            && reference_files.iter().any(|u| u.ends_with("main.glorious")),
        "references incomplete: {reference_files:?}"
    );

    // Rename edits every occurrence across both files.
    let (rename, _) = session.request(
        "textDocument/rename",
        json!({"textDocument": {"uri": uri(&main_path)},
               "position": {"line": 1, "character": 17},
               "newName": "assist"}),
    );
    let changes = rename["changes"].as_object().unwrap();
    assert_eq!(
        changes.len(),
        2,
        "rename should touch both files: {changes:?}"
    );

    // Std prelude names appear in completion.
    let (completions, _) = session.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 2, "character": 5}}),
    );
    let labels: Vec<&str> = completions
        .as_array()
        .unwrap()
        .iter()
        .map(|c| c["label"].as_str().unwrap())
        .collect();
    assert!(labels.contains(&"if"), "std completion missing: {labels:?}");
    assert!(
        labels.contains(&"first"),
        "local completion missing: {labels:?}"
    );

    // Formatting normalizes a sloppy buffer.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 5},
               "contentChanges": [{"text": "main( ) -> () {\n  helper (1)\n}\n"}]}),
    );
    let (edits, _) = session.request(
        "textDocument/formatting",
        json!({"textDocument": {"uri": uri(&main_path)},
               "options": {"tabSize": 4, "insertSpaces": true}}),
    );
    let new_text = edits[0]["newText"].as_str().unwrap();
    assert_eq!(new_text, "main() -> { helper(1) }\n");

    let (shutdown, _) = session.request("shutdown", json!(null));
    assert!(shutdown.is_null());
    session.notify("exit", json!(null));
    let status = session.child.wait().unwrap();
    assert!(status.success());
}

#[test]
fn standard_library_definition_opens_materialized_read_only_file() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    let source = concat!(
        "condition() -> Result<(), ()> { Result::Ok(()) }\n",
        "choose() -> Result<(), ()> {\n",
        "    if(condition()) { () }\n",
        "}\n",
        "main() -> () { () }\n",
    );
    let main = project(&root, "app", source);

    let mut session = Session::start(&root);
    let (initialize, _) = session.request("initialize", json!({"rootUri": uri(&root)}));
    let standard_library = &initialize["capabilities"]["experimental"]["standardLibrary"];
    assert_eq!(standard_library["readOnly"], true);
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics: {diagnostics:?}"
    );

    let (definition, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 2, "character": 5}
        }),
    );
    let std_uri = definition["uri"].as_str().unwrap();
    assert!(std_uri.starts_with("file://"), "{definition}");
    assert_eq!(standard_library["uri"], std_uri);
    let std_path = std::path::PathBuf::from(std_uri.strip_prefix("file://").unwrap());
    assert!(
        std_path.starts_with(root.join(".grand-cache/lsp/stdlib")),
        "{}",
        std_path.display()
    );
    let contents = std::fs::read_to_string(&std_path).unwrap();
    assert_eq!(
        contents,
        grandiose::source_bundle::DISTRIBUTED_STANDARD_LIBRARY_SOURCE
    );
    assert!(
        std::fs::metadata(&std_path)
            .unwrap()
            .permissions()
            .readonly()
    );
    let start = &definition["range"]["start"];
    let end = &definition["range"]["end"];
    assert_eq!(start["line"], end["line"]);
    let line = contents
        .lines()
        .nth(start["line"].as_u64().unwrap() as usize)
        .unwrap();
    let start_character = start["character"].as_u64().unwrap() as usize;
    let end_character = end["character"].as_u64().unwrap() as usize;
    assert_eq!(&line[start_character..end_character], "if");
}

#[test]
fn initial_late_compile_error_keeps_unique_top_level_definition_navigation() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
    )
    .unwrap();
    let helper = root.join("src/helper.glorious");
    std::fs::write(&helper, "helper() -> () { () }\n").unwrap();
    let main = root.join("src/main.glorious");
    // Name/module resolution succeeds, but the bad return type prevents the
    // compiler from ever producing an initial semantic snapshot.
    let source = concat!(
        "broken() -> Text { 1 }\n",
        "main() -> () {\n",
        "    helper();\n",
        "    assert(true)\n",
        "}\n",
    );
    std::fs::write(&main, source).unwrap();

    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());

    let (project_definition, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 2, "character": 7}
        }),
    );
    assert_eq!(
        project_definition["uri"],
        uri(&helper),
        "{project_definition}"
    );

    let (standard_definition, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 3, "character": 7}
        }),
    );
    assert!(
        standard_definition["uri"]
            .as_str()
            .is_some_and(|uri| uri.contains("/lsp/stdlib/") && uri.starts_with("file://")),
        "{standard_definition}"
    );
}

#[test]
fn initial_error_definition_fallback_does_not_capture_shadowing_local() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    let source = concat!(
        "helper() -> () { () }\n",
        "broken() -> Text { 1 }\n",
        "main() -> i64 {\n",
        "    let helper = 1;\n",
        "    helper\n",
        "}\n",
    );
    let main = project(&root, "app", source);
    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());
    let (definition, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 4, "character": 7}
        }),
    );
    assert!(
        definition.is_null(),
        "shadowed local must fail closed: {definition}"
    );
}

#[test]
fn cancellation_stale_versions_and_malformed_edits_do_not_replace_live_state() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    let main = project(&root, "app", "main() -> () { () } // 😀\n");
    let live = "main() -> () { () } // 😀\n";
    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {"uri": uri(&main), "languageId": "grandiose", "version": 10, "text": live}}),
    );
    let initial_diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        initial_diagnostics.is_empty(),
        "unexpected diagnostics: {initial_diagnostics:?}"
    );

    // A UTF-16 position in the middle of the emoji's surrogate pair clamps
    // safely and the server remains responsive.
    let (hover, _) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main)}, "position": {"line": 0, "character": 24}}),
    );
    assert!(hover.is_null());

    // The reader records cancellation before dispatch, so a queued request is
    // rejected and cannot force publication of the pending broken revision.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 11}, "contentChanges": [{"text": "main( -> Text {"}]}),
    );
    let cancelled_id = 7001;
    session.notify("$/cancelRequest", json!({"id": cancelled_id}));
    session.send(json!({
        "jsonrpc": "2.0", "id": cancelled_id,
        "method": "textDocument/completion",
        "params": {"textDocument": {"uri": uri(&main)}, "position": {"line": 0, "character": 22}}
    }));
    loop {
        let message = session.receive();
        if message["id"].as_i64() == Some(cancelled_id) {
            assert_eq!(message["error"]["code"], -32800);
            break;
        }
        assert_ne!(message["method"], "textDocument/publishDiagnostics");
    }
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 12}, "contentChanges": [{"text": live}]}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics: {diagnostics:?}"
    );

    // Full synchronization was advertised. A ranged fragment and an older
    // full version must both be ignored rather than corrupting the overlay.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 13}, "contentChanges": [{
            "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}},
            "text": "broken"
        }]}),
    );
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 9}, "contentChanges": [{"text": "broken( {"}]}),
    );
    let (symbols, notifications) = session.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri(&main)}}),
    );
    assert!(
        notifications.is_empty(),
        "ignored edits published stale diagnostics"
    );
    assert_eq!(symbols[0]["name"], "main");

    // Rapid revisions are debounced to the newest text. The broken version is
    // never published once a newer valid version is already queued.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 14}, "contentChanges": [{"text": "main( -> Text {"}]}),
    );
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 15}, "contentChanges": [{"text": live}]}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
}

#[test]
fn workspace_folders_isolate_completion_and_reference_search() {
    let temporary = TempDir::new().unwrap();
    let first = temporary.path().join("first");
    let second = temporary.path().join("second");
    let first_main = project(
        &first,
        "first",
        "shared() -> () { () }\nonly_first() -> () { shared() }\nmain() -> () { shared() }\n",
    );
    let second_main = project(
        &second,
        "second",
        "shared() -> () { () }\nonly_second() -> () { shared() }\nmain() -> () { shared() }\n",
    );
    let mut session = Session::start(temporary.path());
    let (initialize, _) = session.request(
        "initialize",
        json!({
            "workspaceFolders": [
                {"uri": uri(&first), "name": "first"},
                {"uri": uri(&second), "name": "second"}
            ]
        }),
    );
    assert_eq!(
        initialize["capabilities"]["workspace"]["workspaceFolders"]["supported"],
        true
    );
    session.notify("initialized", json!({}));

    let (completion, _) = session.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri(&first_main)}, "position": {"line": 2, "character": 15}}),
    );
    let labels = completion
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|item| item["label"].as_str())
        .collect::<Vec<_>>();
    assert!(labels.contains(&"only_first"));
    assert!(!labels.contains(&"only_second"));

    let (references, _) = session.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri(&first_main)},
            "position": {"line": 2, "character": 17},
            "context": {"includeDeclaration": true}
        }),
    );
    assert!(
        references
            .as_array()
            .unwrap()
            .iter()
            .all(|location| !location["uri"].as_str().unwrap().contains("second"))
    );
    assert!(second_main.is_file());
}

#[test]
fn malformed_revision_keeps_last_good_semantic_identities_transactionally() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
    )
    .unwrap();
    let helper = root.join("src/helper.glorious");
    std::fs::write(&helper, "helper() -> () { () }\n").unwrap();
    let main = root.join("src/main.glorious");
    let valid = "main() -> () {\n    helper()\n}\n";
    std::fs::write(&main, valid).unwrap();

    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": valid
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics: {diagnostics:?}"
    );

    let definition_request = || {
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 1, "character": 7}
        })
    };
    let (definition, _) = session.request("textDocument/definition", definition_request());
    assert!(
        definition["uri"]
            .as_str()
            .unwrap()
            .ends_with("helper.glorious")
    );

    // Keep every previously checked occurrence at the same byte position but
    // make the new tail unparsable. Diagnostics come from this revision while
    // symbols, definitions, references, and rename retain the old snapshot.
    let malformed = format!("{valid}broken( -> () {{\n");
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 2},
               "contentChanges": [{"text": malformed}]}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());

    let (definition, _) = session.request("textDocument/definition", definition_request());
    assert!(
        definition["uri"]
            .as_str()
            .unwrap()
            .ends_with("helper.glorious")
    );
    let (symbols, _) = session.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri(&main)}}),
    );
    assert_eq!(symbols.as_array().unwrap().len(), 1);
    assert_eq!(symbols[0]["name"], "main");
    let (references, _) = session.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 1, "character": 7},
            "context": {"includeDeclaration": true}
        }),
    );
    assert_eq!(references.as_array().unwrap().len(), 2);
    let (rename, _) = session.request(
        "textDocument/rename",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 1, "character": 7},
            "newName": "replacement"
        }),
    );
    assert_eq!(rename["changes"].as_object().unwrap().len(), 2);
}

#[test]
fn compiler_local_tables_preserve_shadowing_utf16_and_last_good_rename() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    let source = "selected(seed: i64) -> i64 {\n    let chosen = seed;\n    {\n        /* 😀 */ let chosen = 2;\n        /* 😀 */ chosen\n    }\n}\nmain() -> () { () }\n";
    let main = project(&root, "app", source);
    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    assert!(session.diagnostics_for("main.glorious").is_empty());

    let use_line = "        /* 😀 */ chosen";
    let use_character = use_line[..use_line.find("chosen").unwrap()]
        .encode_utf16()
        .count()
        + 2;
    let request = || {
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 4, "character": use_character}
        })
    };
    let (definition, _) = session.request("textDocument/definition", request());
    assert_eq!(definition["range"]["start"]["line"], 3, "{definition}");
    let (hover, _) = session.request("textDocument/hover", request());
    assert!(
        hover["contents"]["value"].as_str().unwrap().contains("i64"),
        "{hover}"
    );
    let (hints, _) = session.request(
        "textDocument/inlayHint",
        json!({
            "textDocument": {"uri": uri(&main)},
            "range": {
                "start": {"line": 0, "character": 0},
                "end": {"line": 7, "character": 0}
            }
        }),
    );
    let inner_hint = hints
        .as_array()
        .unwrap()
        .iter()
        .find(|hint| hint["position"]["line"] == 3)
        .expect("inner binding type hint");
    assert_eq!(inner_hint["label"], ": i64");
    let definition_line = "        /* 😀 */ let chosen = 2;";
    let expected_hint_character = definition_line[..definition_line.find("chosen").unwrap()]
        .encode_utf16()
        .count()
        + "chosen".len();
    assert_eq!(inner_hint["position"]["character"], expected_hint_character);
    let (references, _) = session.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 4, "character": use_character},
            "context": {"includeDeclaration": true}
        }),
    );
    assert_eq!(references.as_array().unwrap().len(), 2, "{references}");
    let (uses_only, _) = session.request(
        "textDocument/references",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 4, "character": use_character},
            "context": {"includeDeclaration": false}
        }),
    );
    assert_eq!(uses_only.as_array().unwrap().len(), 1, "{uses_only}");
    let (rename, _) = session.request(
        "textDocument/rename",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 4, "character": use_character},
            "newName": "inner"
        }),
    );
    let edits = rename["changes"][uri(&main)].as_array().unwrap();
    assert_eq!(edits.len(), 2, "outer shadow must not be renamed: {rename}");

    let malformed = format!("{source}broken( -> i64 {{\n");
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 2},
               "contentChanges": [{"text": malformed}]}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());
    let (definition, _) = session.request("textDocument/definition", request());
    assert_eq!(definition["range"]["start"]["line"], 3, "{definition}");

    let shifted = format!("broken( -> i64 {{\n{source}");
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 3},
               "contentChanges": [{"text": shifted}]}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());
    let (stale, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 5, "character": use_character}
        }),
    );
    assert!(
        stale.is_null(),
        "shifted stale offsets must fail closed: {stale}"
    );
}

#[test]
fn dependency_navigation_uses_compiler_package_identities() {
    let temporary = TempDir::new().unwrap();
    let app = temporary.path().join("app");
    let dependency = temporary.path().join("math-lib");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::create_dir_all(dependency.join("src/values")).unwrap();
    std::fs::write(
        app.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n[dependencies]\nmath-lib = { path = \"../math-lib\" }\n",
    )
    .unwrap();
    std::fs::write(
        dependency.join("grandiose.toml"),
        "[project]\nname = \"math-lib\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let source = "use math_lib::answer;\nprobe() -> i64 {\n    answer()\n}\nmain() -> () { () }\n";
    let main = app.join("src/main.glorious");
    std::fs::write(&main, source).unwrap();
    let dependency_root = dependency.join("src/lib.glorious");
    std::fs::write(
        &dependency_root,
        "pub mod values; pub answer() -> i64 { crate::values::answer() }",
    )
    .unwrap();
    std::fs::write(
        dependency.join("src/values/values.glorious"),
        "pub answer() -> i64 { 42 }",
    )
    .unwrap();

    let mut session = Session::start(&app);
    session.request("initialize", json!({"rootUri": uri(&app)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    assert!(session.diagnostics_for("main.glorious").is_empty());
    let request = json!({
        "textDocument": {"uri": uri(&main)},
        "position": {"line": 2, "character": 6}
    });
    let (definition, _) = session.request("textDocument/definition", request.clone());
    assert_eq!(definition["uri"], uri(&dependency_root), "{definition}");
    let (hover, _) = session.request("textDocument/hover", request.clone());
    assert!(
        hover["contents"]["value"]
            .as_str()
            .unwrap()
            .contains("answer() -> i64"),
        "{hover}"
    );
    let (references, _) = session.request(
        "textDocument/references",
        json!({
            "textDocument": request["textDocument"],
            "position": request["position"],
            "context": {"includeDeclaration": true}
        }),
    );
    assert!(
        references
            .as_array()
            .unwrap()
            .iter()
            .any(|location| location["uri"] == uri(&dependency_root)),
        "{references}"
    );
}

#[test]
fn signature_help_and_semantic_tokens_are_utf16_multifile_and_transactional() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
    )
    .unwrap();
    let helper = root.join("src/helper.glorious");
    std::fs::write(
        &helper,
        "// 😀 helper docs\nhelper(left: i64, right: i64) -> i64 { left }\n",
    )
    .unwrap();
    let main = root.join("src/main.glorious");
    let valid = "main() -> () {\n    // 😀\n    helper(1, 2); ()\n}\n";
    std::fs::write(&main, valid).unwrap();

    let mut session = Session::start(&root);
    let (initialize, _) = session.request("initialize", json!({"rootUri": uri(&root)}));
    assert_eq!(
        initialize["capabilities"]["signatureHelpProvider"]["triggerCharacters"],
        json!(["(", ","])
    );
    assert_eq!(
        initialize["capabilities"]["semanticTokensProvider"]["full"],
        true
    );
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": valid
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics: {diagnostics:?}"
    );

    let signature_request = || {
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 2, "character": 14},
            "context": {"triggerKind": 2, "triggerCharacter": ","}
        })
    };
    let (signature, _) = session.request("textDocument/signatureHelp", signature_request());
    assert_eq!(signature["activeSignature"], 0);
    assert_eq!(signature["activeParameter"], 1);
    assert_eq!(
        signature["signatures"][0]["label"],
        "helper(left: i64, right: i64) -> i64"
    );
    assert_eq!(
        signature["signatures"][0]["parameters"][1]["label"],
        "right: i64"
    );

    let (main_tokens, _) = session.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri(&main)}}),
    );
    let main_tokens = decoded_semantic_tokens(&main_tokens);
    assert!(
        main_tokens.contains(&(1, 4, 5, 8)),
        "UTF-16 comment token: {main_tokens:?}"
    );
    assert!(
        main_tokens.contains(&(2, 4, 6, 6)),
        "cross-file callable token: {main_tokens:?}"
    );
    assert!(
        main_tokens.contains(&(2, 11, 1, 10)),
        "numeric token: {main_tokens:?}"
    );

    let (helper_tokens, _) = session.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri(&helper)}}),
    );
    let helper_tokens = decoded_semantic_tokens(&helper_tokens);
    assert!(
        helper_tokens.contains(&(0, 0, 17, 8)),
        "UTF-16 docs token: {helper_tokens:?}"
    );
    assert!(
        helper_tokens.contains(&(1, 0, 6, 6)),
        "definition token: {helper_tokens:?}"
    );

    // Diagnostics follow the broken overlay, while semantic binding and
    // signature metadata remain the atomically retained last-good snapshot.
    let malformed = format!("{valid}broken( -> i64 {{\n");
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main), "version": 2},
               "contentChanges": [{"text": malformed}]}),
    );
    assert!(!session.diagnostics_for("main.glorious").is_empty());
    let (signature, _) = session.request("textDocument/signatureHelp", signature_request());
    assert_eq!(signature["activeParameter"], 1);
    assert_eq!(
        signature["signatures"][0]["label"],
        "helper(left: i64, right: i64) -> i64"
    );
    let (tokens, _) = session.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri(&main)}}),
    );
    assert!(
        decoded_semantic_tokens(&tokens).contains(&(2, 4, 6, 6)),
        "last-good callable identity disappeared"
    );
}

#[test]
fn qualified_effect_and_operation_definitions_are_exact() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    let source = concat!(
        "effect ParseCase { inspect(value: i64) -> ! }\n",
        "effect OtherCase { inspect(value: i64) -> ! }\n",
        "inspect() -> i64 { 99 }\n",
        "parse() -> i64 {\n",
        "    handle perform ParseCase::inspect(7) {\n",
        "        ParseCase::inspect(value) => value\n",
        "    }\n",
        "}\n",
        "other() -> i64 {\n",
        "    handle perform OtherCase::inspect(8) {\n",
        "        OtherCase::inspect(value) => value\n",
        "    }\n",
        "}\n",
        "main() -> () { () }\n",
    );
    let main = project(&root, "app", source);
    let mut session = Session::start(&root);
    session.request("initialize", json!({"rootUri": uri(&root)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    assert!(session.diagnostics_for("main.glorious").is_empty());

    let definition = |session: &mut Session, line, character| {
        session
            .request(
                "textDocument/definition",
                json!({
                    "textDocument": {"uri": uri(&main)},
                    "position": {"line": line, "character": character}
                }),
            )
            .0
    };
    let parse_effect = definition(&mut session, 4, 20);
    assert_eq!(parse_effect["range"]["start"]["line"], 0, "{parse_effect}");
    assert_eq!(
        parse_effect["range"]["start"]["character"], 7,
        "{parse_effect}"
    );

    for (line, character) in [(4, 31), (5, 21)] {
        let operation = definition(&mut session, line, character);
        assert_eq!(operation["range"]["start"]["line"], 0, "{operation}");
        assert_eq!(operation["range"]["start"]["character"], 19, "{operation}");
    }
    let other_operation = definition(&mut session, 9, 31);
    assert_eq!(
        other_operation["range"]["start"]["line"], 1,
        "{other_operation}"
    );
    let ordinary_function = definition(&mut session, 2, 2);
    assert_eq!(
        ordinary_function["range"]["start"]["line"], 2,
        "{ordinary_function}"
    );
}

#[test]
fn workspace_root_discovers_nested_project_and_its_dependency() {
    let temporary = TempDir::new().unwrap();
    let workspace = temporary.path().join("workspace");
    let app = workspace.join("tutorial/app");
    let dependency = app.join("library");
    std::fs::create_dir_all(app.join("src")).unwrap();
    std::fs::create_dir_all(dependency.join("src")).unwrap();
    std::fs::write(
        app.join("grandiose.toml"),
        "[project]\nname = \"nested-app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n\n[dependencies]\ncore-lib = { path = \"library\" }\n",
    )
    .unwrap();
    std::fs::write(
        dependency.join("grandiose.toml"),
        "[project]\nname = \"core-lib\"\nversion = \"0.1.0\"\n",
    )
    .unwrap();
    let source = "use core_lib::answer;\nprobe() -> i64 { answer() }\nmain() -> () { let ignored = probe(); () }\n";
    let main = app.join("src/main.glorious");
    std::fs::write(&main, source).unwrap();
    let library = dependency.join("src/lib.glorious");
    std::fs::write(&library, "pub answer() -> i64 { 42 }\n").unwrap();

    let mut session = Session::start(&workspace);
    session.request("initialize", json!({"rootUri": uri(&workspace)}));
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(diagnostics.is_empty(), "{diagnostics:#?}");
    let (definition, _) = session.request(
        "textDocument/definition",
        json!({
            "textDocument": {"uri": uri(&main)},
            "position": {"line": 1, "character": 18}
        }),
    );
    assert_eq!(definition["uri"], uri(&library), "{definition}");
}

#[test]
fn semantic_tokens_distinguish_effect_operations_enum_variants_and_functions() {
    let temporary = TempDir::new().unwrap();
    let root = temporary.path().join("app");
    let source = concat!(
        "effect Stop { stop(value: i64) -> ! }\n",
        "ordinary() -> () { () }\n",
        "result() -> Result<(), ()> { Result::Ok(()) }\n",
        "test() -> i64 {\n",
        "    ordinary();\n",
        "    handle perform Stop::stop(42) {\n",
        "        Stop::stop(value) => value\n",
        "    }\n",
        "}\n",
        "main() -> () { () }\n",
    );
    let main = project(&root, "app", source);
    let mut session = Session::start(&root);
    let (initialize, _) = session.request("initialize", json!({"rootUri": uri(&root)}));
    assert_eq!(
        initialize["capabilities"]["semanticTokensProvider"]["legend"]["tokenTypes"][12],
        "enumMember"
    );
    session.notify("initialized", json!({}));
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main), "languageId": "grandiose", "version": 1, "text": source
        }}),
    );
    let diagnostics = session.diagnostics_for("main.glorious");
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics: {diagnostics:?}"
    );

    let (tokens, _) = session.request(
        "textDocument/semanticTokens/full",
        json!({"textDocument": {"uri": uri(&main)}}),
    );
    let tokens = decoded_semantic_tokens(&tokens);
    assert!(
        tokens.contains(&(4, 4, 8, 6)),
        "ordinary function: {tokens:?}"
    );
    assert!(tokens.contains(&(5, 19, 4, 5)), "effect prefix: {tokens:?}");
    assert!(
        tokens.contains(&(5, 25, 4, 12)),
        "effect operation: {tokens:?}"
    );
    assert!(
        tokens.contains(&(6, 8, 4, 5)),
        "handler effect prefix: {tokens:?}"
    );
    assert!(
        tokens.contains(&(6, 14, 4, 12)),
        "handler operation: {tokens:?}"
    );

    let result_line = "result() -> Result<(), ()> { Result::Ok(()) }";
    let result_constructor = result_line.rfind("Result").unwrap() as u32;
    let ok = result_line.find("::Ok").unwrap() as u32 + 2;
    assert!(
        tokens.contains(&(2, result_constructor, 6, 1)),
        "enum prefix: {tokens:?}"
    );
    assert!(tokens.contains(&(2, ok, 2, 12)), "enum variant: {tokens:?}");
}
