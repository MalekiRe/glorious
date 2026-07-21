//! Scripted end-to-end LSP session against the real binary over stdio.

use std::io::{BufRead, BufReader, Read, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, ChildStdout, Command, Stdio};

use serde_json::{json, Value};
use tempfile::TempDir;

struct Session {
    child: Child,
    stdin: ChildStdin,
    stdout: BufReader<ChildStdout>,
    next_id: i64,
}

impl Session {
    fn start(cwd: &Path) -> Session {
        let mut child = Command::new(env!("CARGO_BIN_EXE_grand-lsp"))
            .current_dir(cwd)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        let stdin = child.stdin.take().unwrap();
        let stdout = BufReader::new(child.stdout.take().unwrap());
        Session { child, stdin, stdout, next_id: 0 }
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
            assert!(self.stdout.read_line(&mut line).unwrap() > 0, "server closed stdout");
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
                && message["params"]["uri"].as_str().unwrap_or_default().ends_with(suffix)
            {
                return message["params"]["diagnostics"].as_array().unwrap().clone();
            }
        }
        panic!("no publishDiagnostics for {suffix}");
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        let _ = self.child.kill();
    }
}

fn uri(path: &Path) -> String {
    format!("file://{}", path.display())
}

#[test]
fn full_session() {
    let dir = TempDir::new().unwrap();
    let root = dir.path().join("app");
    std::fs::create_dir_all(root.join("src")).unwrap();
    std::fs::write(
        root.join("grandiose.toml"),
        "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n",
    )
    .unwrap();
    std::fs::write(
        root.join("src/helpers.gr"),
        "// Doubles a value, allegedly.\nhelper(value: i64) -> i64 { value }\n",
    )
    .unwrap();
    let main_path = root.join("src/main.gr");
    std::fs::write(&main_path, "main() -> i64 {\n    helper(0)\n}\n").unwrap();

    let mut session = Session::start(&root);
    let (result, _) = session.request("initialize", json!({"rootUri": uri(&root)}));
    assert_eq!(result["capabilities"]["textDocumentSync"], 1);
    assert_eq!(result["serverInfo"]["name"], "grand-lsp");
    session.notify("initialized", json!({}));

    // Open a broken revision: expect an error diagnostic on main.gr.
    session.notify(
        "textDocument/didOpen",
        json!({"textDocument": {
            "uri": uri(&main_path), "languageId": "grandiose", "version": 1,
            "text": "main( -> i64 {\n",
        }}),
    );
    let diagnostics = session.diagnostics_for("main.gr");
    assert!(!diagnostics.is_empty(), "expected a parse error");
    assert_eq!(diagnostics[0]["severity"], 1, "expected error severity: {diagnostics:?}");
    assert_eq!(diagnostics[0]["source"], "grandiose");

    // Fix the file: diagnostics clear.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 2},
               "contentChanges": [{"text": "main() -> i64 {\n    helper(0)\n}\n"}]}),
    );
    let diagnostics = session.diagnostics_for("main.gr");
    assert!(diagnostics.is_empty(), "diagnostics did not clear: {diagnostics:?}");

    // Document symbols for main.gr.
    let (symbols, _) = session.request(
        "textDocument/documentSymbol",
        json!({"textDocument": {"uri": uri(&main_path)}}),
    );
    let names: Vec<&str> = symbols.as_array().unwrap().iter().map(|s| s["name"].as_str().unwrap()).collect();
    assert_eq!(names, vec!["main"], "unexpected symbols: {names:?}");

    // Go-to-definition on `helper` inside main.gr lands in helpers.gr.
    let (definition, _) = session.request(
        "textDocument/definition",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    assert!(
        definition["uri"].as_str().unwrap().ends_with("helpers.gr"),
        "definition wrong: {definition}"
    );
    assert_eq!(definition["range"]["start"]["line"], 1); // below the doc comment

    // Hover shows the signature and the doc comment.
    let (hover, _) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    let markdown = hover["contents"]["value"].as_str().unwrap();
    assert!(markdown.contains("helper(value: i64) -> i64"), "hover: {markdown}");
    assert!(markdown.contains("Doubles a value"), "hover missing docs: {markdown}");

    // Completion offers workspace declarations and keywords.
    let (completions, _) = session.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 1, "character": 6}}),
    );
    let labels: Vec<&str> =
        completions.as_array().unwrap().iter().map(|c| c["label"].as_str().unwrap()).collect();
    assert!(labels.contains(&"helper") && labels.contains(&"main"), "completions: {labels:?}");
    assert!(labels.contains(&"handle"), "keywords missing: {labels:?}");

    // Resilient parsing: two broken declarations produce two diagnostics.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 3},
               "contentChanges": [{"text":
            "first( -> i64 {\n    1\n}\nsecond( -> i64 {\n    2\n}\nvalid() -> i64 { helper(1) }\n"}]}),
    );
    let diagnostics = session.diagnostics_for("main.gr");
    assert!(
        diagnostics.len() >= 2,
        "resilient parser should report multiple errors: {diagnostics:?}"
    );

    // Locals: definition/hover of a `let` binding and completion including it.
    let body = "main() -> i64 {\n    let first = helper(1)\n    first\n}\n";
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
    assert!(definition["uri"].as_str().unwrap().ends_with("main.gr"), "{definition}");
    assert_eq!(definition["range"]["start"]["line"], 1, "local def wrong: {definition}");
    let (hover, _) = session.request(
        "textDocument/hover",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 2, "character": 5}}),
    );
    assert!(
        hover["contents"]["value"].as_str().unwrap().contains("let binding"),
        "local hover: {hover}"
    );

    // References: `helper` appears in helpers.gr (definition) and main.gr (call).
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
        reference_files.iter().any(|u| u.ends_with("helpers.gr"))
            && reference_files.iter().any(|u| u.ends_with("main.gr")),
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
    assert_eq!(changes.len(), 2, "rename should touch both files: {changes:?}");

    // Std prelude names appear in completion.
    let (completions, _) = session.request(
        "textDocument/completion",
        json!({"textDocument": {"uri": uri(&main_path)}, "position": {"line": 2, "character": 5}}),
    );
    let labels: Vec<&str> =
        completions.as_array().unwrap().iter().map(|c| c["label"].as_str().unwrap()).collect();
    assert!(labels.contains(&"if"), "std completion missing: {labels:?}");
    assert!(labels.contains(&"first"), "local completion missing: {labels:?}");

    // Formatting normalizes a sloppy buffer.
    session.notify(
        "textDocument/didChange",
        json!({"textDocument": {"uri": uri(&main_path), "version": 5},
               "contentChanges": [{"text": "main( ) -> i64 {\n  helper (1)\n}\n"}]}),
    );
    let (edits, _) = session.request(
        "textDocument/formatting",
        json!({"textDocument": {"uri": uri(&main_path)},
               "options": {"tabSize": 4, "insertSpaces": true}}),
    );
    let new_text = edits[0]["newText"].as_str().unwrap();
    assert_eq!(new_text, "main() -> i64 {\n    helper(1)\n}\n");

    let (shutdown, _) = session.request("shutdown", json!(null));
    assert!(shutdown.is_null());
    session.notify("exit", json!(null));
    let status = session.child.wait().unwrap();
    assert!(status.success());
}
