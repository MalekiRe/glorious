mod analysis;
mod frontend;
mod position;
mod rpc;

use std::io::{BufReader, Stdout};
use std::path::PathBuf;
use std::sync::mpsc;
use std::time::Duration;

use anyhow::Result;
use grand::contract::{Declaration, DeclarationKind};
use serde_json::{json, Value};

use crate::analysis::{identifiers, locals_at, Local, Workspace};
use crate::frontend::diagnostic::Severity;
use crate::position::LineIndex;
use crate::rpc::{path_to_uri, read_message, uri_to_path, write_message};

/// didChange publishes are debounced by this much; requests flush eagerly.
const DEBOUNCE: Duration = Duration::from_millis(120);

struct Server {
    workspace: Workspace,
    output: Stdout,
    published: std::collections::BTreeSet<PathBuf>,
    /// A didChange happened and diagnostics have not been re-published yet.
    dirty: bool,
}

/// What the cursor resolves to, in scope order: local, workspace declaration,
/// std declaration.
enum Target {
    Local(PathBuf, Local),
    Decl(Declaration),
    Std(Declaration),
}

fn main() -> Result<()> {
    // Reader thread feeds a channel so the main loop can debounce with
    // recv_timeout while staying single-threaded for state.
    let (sender, receiver) = mpsc::channel::<Value>();
    std::thread::spawn(move || {
        let mut input = BufReader::new(std::io::stdin());
        while let Ok(Some(message)) = read_message(&mut input) {
            if sender.send(message).is_err() {
                break;
            }
        }
    });

    let mut server = Server {
        workspace: Workspace::new(std::env::current_dir()?),
        output: std::io::stdout(),
        published: Default::default(),
        dirty: false,
    };
    loop {
        let message = match receiver.recv_timeout(DEBOUNCE) {
            Ok(message) => message,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                if server.dirty {
                    server.dirty = false;
                    server.publish()?;
                }
                continue;
            }
            Err(mpsc::RecvTimeoutError::Disconnected) => break,
        };
        if !server.handle(message)? {
            break;
        }
    }
    Ok(())
}

impl Server {
    /// Returns false on `exit`.
    fn handle(&mut self, message: Value) -> Result<bool> {
        let method = message["method"].as_str().unwrap_or_default().to_string();
        let id = message["id"].clone();
        let params = message["params"].clone();
        // Any request observes up-to-date diagnostics/state.
        if !id.is_null() && self.dirty {
            self.dirty = false;
            self.publish()?;
        }
        match method.as_str() {
            "initialize" => {
                if let Some(root) = params["rootUri"].as_str().and_then(|u| uri_to_path(u).ok()) {
                    self.workspace = Workspace::new(root);
                }
                self.respond(&id, json!({
                    "capabilities": {
                        "textDocumentSync": 1, // full
                        "documentSymbolProvider": true,
                        "definitionProvider": true,
                        "hoverProvider": true,
                        "completionProvider": {},
                        "documentFormattingProvider": true,
                        "referencesProvider": true,
                        "renameProvider": true,
                    },
                    "serverInfo": {"name": "grand-lsp", "version": env!("CARGO_PKG_VERSION")},
                }))?;
            }
            "shutdown" => self.respond(&id, Value::Null)?,
            "exit" => return Ok(false),
            "textDocument/didOpen" => {
                let path = doc_path(&params)?;
                let text = params["textDocument"]["text"].as_str().unwrap_or_default();
                self.workspace.open(path, text.to_string());
                self.publish()?;
            }
            "textDocument/didChange" => {
                let path = doc_path(&params)?;
                if let Some(text) = params["contentChanges"][0]["text"].as_str() {
                    self.workspace.open(path, text.to_string());
                }
                self.dirty = true; // debounced publish
            }
            "textDocument/didSave" => {
                self.workspace.invalidate();
                self.publish()?;
            }
            "textDocument/didClose" => {
                let path = doc_path(&params)?;
                self.workspace.close(&path);
                self.publish()?;
            }
            "textDocument/documentSymbol" => {
                let path = doc_path(&params)?;
                let analysis = self.workspace.analyze();
                let text = self.workspace.text(&path).unwrap_or_default();
                let index = LineIndex::new(&text);
                let symbols: Vec<Value> = analysis
                    .declarations
                    .iter()
                    .filter(|d| d.file == path)
                    .map(|d| {
                        let range = line_range(&index, &text, d.line);
                        json!({
                            "name": d.name,
                            "kind": symbol_kind(d.kind),
                            "range": range,
                            "selectionRange": range,
                            "detail": d.signature,
                        })
                    })
                    .collect();
                self.respond(&id, json!(symbols))?;
            }
            "textDocument/definition" => {
                let result = match self.lookup(&params)? {
                    Some(Target::Local(path, local)) => {
                        let text = self.workspace.text(&path).unwrap_or_default();
                        let index = LineIndex::new(&text);
                        let (line, col) = index.position(&text, local.def_offset);
                        let (end_line, end_col) =
                            index.position(&text, local.def_offset + local.name.len());
                        json!({
                            "uri": path_to_uri(&path),
                            "range": {
                                "start": {"line": line, "character": col},
                                "end": {"line": end_line, "character": end_col},
                            },
                        })
                    }
                    Some(Target::Decl(declaration)) => {
                        let text = self.workspace.text(&declaration.file).unwrap_or_default();
                        let index = LineIndex::new(&text);
                        json!({
                            "uri": path_to_uri(&declaration.file),
                            "range": line_range(&index, &text, declaration.line),
                        })
                    }
                    // Std names have no navigable file.
                    Some(Target::Std(_)) | None => Value::Null,
                };
                self.respond(&id, result)?;
            }
            "textDocument/hover" => {
                let result = match self.lookup(&params)? {
                    Some(Target::Local(_, local)) => json!({"contents": {
                        "kind": "markdown",
                        "value": format!("`{}` — {}", local.name, local.detail),
                    }}),
                    Some(Target::Decl(declaration)) => hover_markdown(&declaration, false),
                    Some(Target::Std(declaration)) => hover_markdown(&declaration, true),
                    None => Value::Null,
                };
                self.respond(&id, result)?;
            }
            "textDocument/references" => {
                let locations = match self.word_under_cursor(&params)? {
                    Some(word) => json!(self.find_references(&word)),
                    None => json!([]),
                };
                self.respond(&id, locations)?;
            }
            "textDocument/rename" => {
                let new_name = params["newName"].as_str().unwrap_or_default().to_string();
                let valid = !new_name.is_empty()
                    && new_name.chars().next().is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && new_name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
                if !valid {
                    self.reply(json!({
                        "jsonrpc": "2.0", "id": id,
                        "error": {"code": -32602, "message": format!("`{new_name}` is not a valid identifier")},
                    }))?;
                    return Ok(true);
                }
                let result = match self.word_under_cursor(&params)? {
                    Some(word) => {
                        let mut changes: serde_json::Map<String, Value> = Default::default();
                        for location in self.find_references(&word) {
                            let uri = location["uri"].as_str().unwrap().to_string();
                            let edit = json!({"range": location["range"], "newText": new_name});
                            changes
                                .entry(uri)
                                .or_insert_with(|| json!([]))
                                .as_array_mut()
                                .unwrap()
                                .push(edit);
                        }
                        json!({"changes": changes})
                    }
                    None => Value::Null,
                };
                self.respond(&id, result)?;
            }
            "textDocument/formatting" => {
                let path = doc_path(&params)?;
                let result = match self.workspace.text(&path) {
                    Some(text) => match grandfmt::format(&text) {
                        Ok(formatted) if formatted != text => {
                            let index = LineIndex::new(&text);
                            let (end_line, end_col) = index.position(&text, text.len());
                            json!([{
                                "range": {
                                    "start": {"line": 0, "character": 0},
                                    "end": {"line": end_line, "character": end_col},
                                },
                                "newText": formatted,
                            }])
                        }
                        _ => json!([]),
                    },
                    None => Value::Null,
                };
                self.respond(&id, result)?;
            }
            "textDocument/completion" => {
                let analysis = self.workspace.analyze();
                let mut items: Vec<Value> = Vec::new();
                if let Ok(path) = doc_path(&params) {
                    if let Some(text) = self.workspace.text(&path) {
                        let offset = cursor_offset(&params, &text);
                        for local in locals_at(&text, offset) {
                            items.push(json!({
                                "label": local.name,
                                "kind": 6, // Variable
                                "detail": local.detail,
                            }));
                        }
                    }
                }
                for d in analysis.declarations.iter() {
                    items.push(json!({
                        "label": d.name,
                        "kind": completion_kind(d.kind),
                        "detail": d.signature,
                        "documentation": d.docs,
                    }));
                }
                for d in analysis.std_declarations.iter() {
                    items.push(json!({
                        "label": d.name,
                        "kind": completion_kind(d.kind),
                        "detail": d.signature.clone().unwrap_or_else(|| "std".into()),
                    }));
                }
                for keyword in [
                    "let", "struct", "enum", "trait", "impl", "effect", "where", "handle",
                    "perform", "resume", "cancel", "type", "infixl", "infixr", "prefix",
                ] {
                    items.push(json!({"label": keyword, "kind": 14})); // Keyword
                }
                self.respond(&id, json!(items))?;
            }
            // Notifications we deliberately ignore.
            _ if id.is_null() => {}
            // Unknown request: per spec, MethodNotFound.
            _ => self.reply(json!({
                "jsonrpc": "2.0", "id": id,
                "error": {"code": -32601, "message": format!("unhandled method {method}")},
            }))?,
        }
        Ok(true)
    }

    fn reply(&mut self, message: Value) -> Result<()> {
        write_message(&mut self.output, &message)
    }

    fn respond(&mut self, id: &Value, result: Value) -> Result<()> {
        self.reply(json!({"jsonrpc": "2.0", "id": id, "result": result}))
    }

    /// Re-analyze the workspace and publish diagnostics for every file that
    /// has any (plus empty sets to clear files that no longer do).
    fn publish(&mut self) -> Result<()> {
        let analysis = self.workspace.analyze();
        let mut current = std::collections::BTreeSet::new();
        for (file, diagnostics) in &analysis.diagnostics {
            current.insert(file.clone());
            let text = self.workspace.text(file).unwrap_or_default();
            let index = LineIndex::new(&text);
            let payload: Vec<Value> = diagnostics
                .iter()
                .map(|d| {
                    let (start_line, start_col) = index.position(&text, d.start_byte);
                    let (end_line, end_col) = index.position(&text, d.end_byte);
                    json!({
                        "range": {
                            "start": {"line": start_line, "character": start_col},
                            "end": {"line": end_line, "character": end_col},
                        },
                        "severity": match d.severity {
                            Severity::Error => 1,
                            Severity::Warning => 2,
                            Severity::Advice => 3,
                        },
                        "code": d.code,
                        "source": "grandiose",
                        "message": d.message,
                    })
                })
                .collect();
            self.reply(json!({
                "jsonrpc": "2.0",
                "method": "textDocument/publishDiagnostics",
                "params": {"uri": path_to_uri(file), "diagnostics": payload},
            }))?;
        }
        for stale in self.published.difference(&current).cloned().collect::<Vec<_>>() {
            self.reply(json!({
                "jsonrpc": "2.0",
                "method": "textDocument/publishDiagnostics",
                "params": {"uri": path_to_uri(&stale), "diagnostics": []},
            }))?;
        }
        self.published = current;
        Ok(())
    }

    fn word_under_cursor(&self, params: &Value) -> Result<Option<String>> {
        let path = doc_path(params)?;
        let Some(text) = self.workspace.text(&path) else { return Ok(None) };
        let offset = cursor_offset(params, &text);
        Ok(word_at(&text, offset).map(str::to_string))
    }

    /// Resolve the identifier under the cursor: locals of the enclosing
    /// callable shadow workspace declarations, which shadow std.
    fn lookup(&self, params: &Value) -> Result<Option<Target>> {
        let path = doc_path(params)?;
        let Some(text) = self.workspace.text(&path) else { return Ok(None) };
        let offset = cursor_offset(params, &text);
        let Some(word) = word_at(&text, offset) else { return Ok(None) };
        if let Some(local) = locals_at(&text, offset).into_iter().find(|l| l.name == word) {
            return Ok(Some(Target::Local(path, local)));
        }
        let analysis = self.workspace.analyze();
        if let Some(declaration) = analysis.declarations.iter().find(|d| d.name == word) {
            return Ok(Some(Target::Decl(declaration.clone())));
        }
        if let Some(declaration) = analysis.std_declarations.iter().find(|d| d.name == word) {
            return Ok(Some(Target::Std(declaration.clone())));
        }
        Ok(None)
    }

    /// Every word-boundary occurrence of `name` across the workspace
    /// (comment/string-aware), as LSP Locations.
    fn find_references(&self, name: &str) -> Vec<Value> {
        let analysis = self.workspace.analyze();
        let mut locations = Vec::new();
        for file in &analysis.files {
            let Some(text) = self.workspace.text(file) else { continue };
            let index = LineIndex::new(&text);
            for (word, offset) in identifiers(&text) {
                if word != name {
                    continue;
                }
                let (line, col) = index.position(&text, offset);
                let (end_line, end_col) = index.position(&text, offset + word.len());
                locations.push(json!({
                    "uri": path_to_uri(file),
                    "range": {
                        "start": {"line": line, "character": col},
                        "end": {"line": end_line, "character": end_col},
                    },
                }));
            }
        }
        locations
    }
}

fn doc_path(params: &Value) -> Result<PathBuf> {
    uri_to_path(params["textDocument"]["uri"].as_str().unwrap_or_default())
}

fn cursor_offset(params: &Value, text: &str) -> usize {
    let line = params["position"]["line"].as_u64().unwrap_or(0) as u32;
    let character = params["position"]["character"].as_u64().unwrap_or(0) as u32;
    LineIndex::new(text).offset(text, line, character)
}

fn hover_markdown(declaration: &Declaration, std: bool) -> Value {
    let mut markdown = String::new();
    if let Some(signature) = &declaration.signature {
        markdown.push_str(&format!("```grandiose\n{signature}\n```\n"));
    } else {
        markdown.push_str(&format!(
            "`{}` ({})\n",
            declaration.name,
            kind_name(declaration.kind)
        ));
    }
    if std {
        markdown.push_str("\n*standard library*");
    }
    if let Some(docs) = &declaration.docs {
        markdown.push('\n');
        markdown.push_str(docs);
    }
    json!({"contents": {"kind": "markdown", "value": markdown}})
}

fn word_at(text: &str, offset: usize) -> Option<&str> {
    let is_ident = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let bytes = text.as_bytes();
    let offset = offset.min(text.len());
    let mut start = offset;
    while start > 0 && is_ident(bytes[start - 1]) {
        start -= 1;
    }
    let mut end = offset;
    while end < bytes.len() && is_ident(bytes[end]) {
        end += 1;
    }
    (start < end).then(|| &text[start..end])
}

fn line_range(index: &LineIndex, text: &str, line_1based: usize) -> Value {
    let line = line_1based.saturating_sub(1) as u32;
    let start = index.offset(text, line, 0);
    let end = text[start..].find('\n').map(|n| start + n).unwrap_or(text.len());
    let (end_line, end_col) = index.position(text, end);
    json!({
        "start": {"line": line, "character": 0},
        "end": {"line": end_line, "character": end_col},
    })
}

fn symbol_kind(kind: DeclarationKind) -> u32 {
    match kind {
        DeclarationKind::Callable => 12, // Function
        DeclarationKind::Struct => 23,
        DeclarationKind::Enum => 10,
        DeclarationKind::Type => 5,      // Class (alias)
        DeclarationKind::Effect => 24,   // Event
        DeclarationKind::Trait => 11,    // Interface
        DeclarationKind::Global => 14,   // Constant
        DeclarationKind::Fixity => 24,
    }
}

fn completion_kind(kind: DeclarationKind) -> u32 {
    match kind {
        DeclarationKind::Callable => 3, // Function
        DeclarationKind::Struct | DeclarationKind::Enum | DeclarationKind::Type => 7, // Class
        DeclarationKind::Effect | DeclarationKind::Trait => 8, // Interface
        DeclarationKind::Global => 21,  // Constant
        DeclarationKind::Fixity => 24,  // Operator
    }
}

fn kind_name(kind: DeclarationKind) -> &'static str {
    match kind {
        DeclarationKind::Callable => "callable",
        DeclarationKind::Struct => "struct",
        DeclarationKind::Enum => "enum",
        DeclarationKind::Type => "type alias",
        DeclarationKind::Effect => "effect",
        DeclarationKind::Trait => "trait",
        DeclarationKind::Global => "global",
        DeclarationKind::Fixity => "fixity",
    }
}
