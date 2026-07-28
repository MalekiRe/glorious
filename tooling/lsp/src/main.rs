mod analysis;
mod position;
mod rpc;

use std::io::{BufReader, Stdout, Write};
use std::path::PathBuf;
use std::sync::{
    Arc, Mutex,
    atomic::{AtomicU64, Ordering},
    mpsc,
};
use std::time::Duration;

use anyhow::{Context, Result, bail};
use grandiose::diagnostic::Severity;
use grandiose::interface::DeclarationKind;
use grandiose::lossless::{LosslessKind, lex_lossless};
use serde_json::{Value, json};

use crate::analysis::{Analysis, Local, SemanticDeclaration, Workspace};
use crate::position::LineIndex;
use crate::rpc::{path_to_uri, read_message, uri_to_path, write_message};

/// didChange publishes are debounced by this much; requests flush eagerly.
const DEBOUNCE: Duration = Duration::from_millis(120);
struct Server {
    workspace: Workspace,
    analysis: std::rc::Rc<Analysis>,
    analysis_sender: mpsc::Sender<AnalysisCommand>,
    analysis_receiver: mpsc::Receiver<AnalysisResult>,
    analysis_generation: Option<u64>,
    analysis_in_flight: Option<u64>,
    pending_requests: Vec<Value>,
    standard_library_path: PathBuf,
    output: Stdout,
    published: std::collections::BTreeSet<PathBuf>,
    /// A didChange happened and diagnostics have not been re-published yet.
    dirty: bool,
    cancellation: Arc<Mutex<std::collections::BTreeSet<String>>>,
    document_versions: std::collections::BTreeMap<PathBuf, i64>,
    input_generation: Arc<AtomicU64>,
    applied_generation: u64,
}

enum AnalysisCommand {
    SetRoots(Vec<PathBuf>),
    Open(PathBuf, String),
    Save(PathBuf, Option<String>),
    Close(PathBuf),
    Analyze(u64),
}

struct AnalysisResult {
    generation: u64,
    analysis: Analysis,
}

/// What the cursor resolves to, in scope order: local, workspace declaration,
/// std declaration.
enum Target {
    Local(Local),
    Decl(SemanticDeclaration),
    Std(SemanticDeclaration),
}

/// Materialize the compiler-embedded standard library under grand's normal
/// content-addressed cache. Definition results can then use an ordinary
/// `file://` URI that every LSP client knows how to open. The immutable digest
/// directory also prevents one server version from changing the document
/// underneath another running editor.
fn materialize_standard_library() -> Result<PathBuf> {
    let source = grandiose::source_bundle::DISTRIBUTED_STANDARD_LIBRARY_SOURCE;
    let digest = grand::util::blake3_hex(source.as_bytes());
    let directory = grand::util::cache_root()?
        .join("lsp")
        .join("stdlib")
        .join(digest);
    let path = directory.join("distributed_std.glorious");

    if path.exists() {
        let existing = std::fs::read_to_string(&path)
            .with_context(|| format!("read cached standard library `{}`", path.display()))?;
        if existing == source {
            mark_readonly(&path)?;
            return Ok(path);
        }
        bail!(
            "cached standard library `{}` does not match its content address",
            path.display()
        );
    }

    std::fs::create_dir_all(&directory)
        .with_context(|| format!("create standard-library cache `{}`", directory.display()))?;
    let temporary = directory.join(format!(
        ".distributed_std.glorious.{}.tmp",
        std::process::id()
    ));
    let mut file = std::fs::OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(&temporary)
        .with_context(|| format!("create `{}`", temporary.display()))?;
    file.write_all(source.as_bytes())?;
    file.sync_all()?;
    drop(file);

    if let Err(error) = std::fs::rename(&temporary, &path) {
        // Another language-server process can win the same content-addressed
        // write. Accept its identical complete file and discard ours.
        let _ = std::fs::remove_file(&temporary);
        if std::fs::read_to_string(&path).ok().as_deref() != Some(source) {
            return Err(error)
                .with_context(|| format!("install cached standard library `{}`", path.display()));
        }
    }
    mark_readonly(&path)?;
    Ok(path)
}

fn mark_readonly(path: &std::path::Path) -> Result<()> {
    let mut permissions = std::fs::metadata(path)?.permissions();
    if !permissions.readonly() {
        permissions.set_readonly(true);
        std::fs::set_permissions(path, permissions)?;
    }
    Ok(())
}

fn main() -> Result<()> {
    // Reader thread feeds a channel so the main loop can debounce with
    // recv_timeout while staying single-threaded for state.
    let (sender, receiver) = mpsc::channel::<Value>();
    let cancellation = Arc::new(Mutex::new(std::collections::BTreeSet::new()));
    let reader_cancellation = Arc::clone(&cancellation);
    let input_generation = Arc::new(AtomicU64::new(0));
    let reader_generation = Arc::clone(&input_generation);
    std::thread::spawn(move || {
        let mut input = BufReader::new(std::io::stdin());
        while let Ok(Some(mut message)) = read_message(&mut input) {
            if matches!(
                message["method"].as_str(),
                Some(
                    "textDocument/didOpen"
                        | "textDocument/didChange"
                        | "textDocument/didSave"
                        | "textDocument/didClose"
                )
            ) {
                let generation = reader_generation.fetch_add(1, Ordering::AcqRel) + 1;
                if let Some(object) = message.as_object_mut() {
                    object.insert("__grandiose_generation".into(), json!(generation));
                }
            }
            if message["method"] == "$/cancelRequest"
                && let Some(key) = request_key(&message["params"]["id"])
            {
                let mut cancelled = reader_cancellation.lock().unwrap();
                if cancelled.len() >= 4096 {
                    cancelled.pop_first();
                }
                cancelled.insert(key);
            }
            if sender.send(message).is_err() {
                break;
            }
        }
    });

    let initial_root = std::env::current_dir()?;
    let standard_library_path = materialize_standard_library()?;
    let (analysis_sender, analysis_commands) = mpsc::channel();
    let (analysis_results, analysis_receiver) = mpsc::channel();
    let worker_root = initial_root.clone();
    let worker_standard_library_path = standard_library_path.clone();
    std::thread::Builder::new()
        .name("grandiose-lsp-analysis".into())
        .stack_size(32 * 1024 * 1024)
        .spawn(move || {
            let mut workspace = Workspace::new(worker_root);
            workspace.exclude_from_analysis(worker_standard_library_path);
            while let Ok(command) = analysis_commands.recv() {
                match command {
                    AnalysisCommand::SetRoots(roots) => workspace.set_roots(roots),
                    AnalysisCommand::Open(path, text) => {
                        workspace.open(path, text);
                    }
                    AnalysisCommand::Save(path, text) => {
                        workspace.save(&path, text.as_deref());
                    }
                    AnalysisCommand::Close(path) => {
                        workspace.close(&path);
                    }
                    AnalysisCommand::Analyze(generation) => {
                        let analysis = (*workspace.analyze()).clone();
                        if analysis_results
                            .send(AnalysisResult {
                                generation,
                                analysis,
                            })
                            .is_err()
                        {
                            break;
                        }
                    }
                }
            }
        })
        .context("spawn LSP analysis worker")?;

    let mut server = Server {
        workspace: {
            let mut workspace = Workspace::new(initial_root);
            workspace.exclude_from_analysis(standard_library_path.clone());
            workspace
        },
        analysis: std::rc::Rc::new(Analysis::default()),
        analysis_sender,
        analysis_receiver,
        analysis_generation: None,
        analysis_in_flight: None,
        pending_requests: Vec::new(),
        standard_library_path,
        output: std::io::stdout(),
        published: Default::default(),
        dirty: false,
        cancellation,
        document_versions: Default::default(),
        input_generation,
        applied_generation: 0,
    };
    loop {
        server.accept_analysis()?;
        let message = match receiver.recv_timeout(DEBOUNCE) {
            Ok(message) => message,
            Err(mpsc::RecvTimeoutError::Timeout) => {
                server.accept_analysis()?;
                server.schedule_analysis();
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
        if let Some(generation) = message["__grandiose_generation"].as_u64() {
            self.applied_generation = self.applied_generation.max(generation);
        }
        let id = message["id"].clone();
        let params = message["params"].clone();
        if method == "$/cancelRequest" {
            let cancelled = params["id"].clone();
            if let Some(key) = request_key(&cancelled) {
                let before = self.pending_requests.len();
                self.pending_requests
                    .retain(|request| request_key(&request["id"]).as_deref() != Some(&key));
                if self.pending_requests.len() != before {
                    self.respond(&cancelled, Value::Null)?;
                }
            }
            return Ok(true);
        }
        if !id.is_null() && self.is_cancelled(&id) {
            self.respond(&id, Value::Null)?;
            return Ok(true);
        }
        if !id.is_null()
            && method != "initialize"
            && method != "shutdown"
            && self.dirty
            && !(self.analysis_generation.is_some()
                && self
                    .analysis_in_flight
                    .is_some_and(|generation| generation != self.applied_generation))
        {
            self.pending_requests.push(message);
            self.schedule_analysis();
            return Ok(true);
        }
        match method.as_str() {
            "initialize" => {
                let roots = params["workspaceFolders"]
                    .as_array()
                    .into_iter()
                    .flatten()
                    .filter_map(|folder| folder["uri"].as_str())
                    .filter_map(|uri| uri_to_path(uri).ok())
                    .collect::<Vec<_>>();
                if let Some(root) = roots.first().cloned().or_else(|| {
                    params["rootUri"]
                        .as_str()
                        .and_then(|uri| uri_to_path(uri).ok())
                }) {
                    self.workspace = Workspace::new(root);
                    self.workspace
                        .exclude_from_analysis(self.standard_library_path.clone());
                    self.workspace.set_roots(roots);
                }
                self.analysis_sender
                    .send(AnalysisCommand::SetRoots(self.workspace.roots().to_vec()))
                    .ok();
                self.dirty = true;
                self.respond(
                    &id,
                    json!({
                        "capabilities": {
                            "textDocumentSync": 1, // full
                            "documentSymbolProvider": true,
                            "definitionProvider": true,
                            "hoverProvider": true,
                            "inlayHintProvider": true,
                            "completionProvider": {},
                            "signatureHelpProvider": {"triggerCharacters": ["(", ","]},
                            "semanticTokensProvider": {
                                "legend": {
                                    "tokenTypes": [
                                        "type", "enum", "interface", "struct", "variable",
                                        "event", "function", "keyword", "comment", "string",
                                        "number", "operator", "enumMember", "label"
                                    ],
                                    "tokenModifiers": []
                                },
                                "full": true
                            },
                            "documentFormattingProvider": true,
                            "referencesProvider": true,
                            "renameProvider": true,
                            "workspace": {"workspaceFolders": {"supported": true, "changeNotifications": false}},
                            "experimental": {
                                "standardLibrary": {
                                    "uri": path_to_uri(&self.standard_library_path),
                                    "readOnly": true,
                                }
                            },
                        },
                        "serverInfo": {"name": "grand-lsp", "version": env!("CARGO_PKG_VERSION")},
                    }),
                )?;
            }
            "shutdown" => self.respond(&id, Value::Null)?,
            "exit" => return Ok(false),
            "textDocument/didOpen" => {
                let path = doc_path(&params)?;
                let text = params["textDocument"]["text"].as_str().unwrap_or_default();
                if let Some(version) = params["textDocument"]["version"].as_i64() {
                    self.document_versions.insert(path.clone(), version);
                }
                let text = text.to_string();
                let changed = self.workspace.open(path.clone(), text.clone());
                self.analysis_sender
                    .send(AnalysisCommand::Open(path, text))
                    .ok();
                self.dirty |= changed || self.analysis.diagnostics.is_empty();
            }
            "textDocument/didChange" => {
                let path = doc_path(&params)?;
                let version = params["textDocument"]["version"].as_i64();
                if version.is_some_and(|incoming| {
                    self.document_versions
                        .get(&path)
                        .is_some_and(|current| incoming <= *current)
                }) {
                    return Ok(true);
                }
                let changes = params["contentChanges"].as_array();
                let full_text = changes
                    .filter(|changes| changes.len() == 1)
                    .and_then(|changes| changes.first())
                    .filter(|change| change.get("range").is_none())
                    .and_then(|change| change["text"].as_str());
                let Some(text) = full_text else {
                    // The server advertises full synchronization. Reject
                    // malformed/ranged sequences instead of interpreting a
                    // fragment as the complete document.
                    return Ok(true);
                };
                if let Some(version) = version {
                    self.document_versions.insert(path.clone(), version);
                }
                let text = text.to_string();
                let changed = self.workspace.open(path.clone(), text.clone());
                self.analysis_sender
                    .send(AnalysisCommand::Open(path, text))
                    .ok();
                if changed {
                    self.dirty = true; // debounced publish
                }
            }
            "textDocument/didSave" => {
                let path = doc_path(&params)?;
                let text = params.get("text").and_then(Value::as_str);
                let changed = self.workspace.save(&path, text);
                self.analysis_sender
                    .send(AnalysisCommand::Save(path, text.map(ToOwned::to_owned)))
                    .ok();
                self.dirty |= changed;
            }
            "textDocument/didClose" => {
                let path = doc_path(&params)?;
                self.document_versions.remove(&path);
                let changed = self.workspace.close(&path);
                self.analysis_sender.send(AnalysisCommand::Close(path)).ok();
                self.dirty |= changed;
            }
            "textDocument/documentSymbol" => {
                let path = doc_path(&params)?;
                let analysis = std::rc::Rc::clone(&self.analysis);
                let text = self.workspace.text(&path).unwrap_or_default();
                let index = LineIndex::new(&text);
                let symbols: Vec<Value> = analysis
                    .declarations
                    .iter()
                    .filter(|d| d.file == path)
                    .map(|d| {
                        let range = byte_range(
                            &index,
                            &text,
                            d.declaration_start_byte,
                            d.declaration_end_byte,
                        );
                        let selection_range =
                            byte_range(&index, &text, d.name_start_byte, d.name_end_byte);
                        json!({
                            "name": d.name,
                            "kind": symbol_kind(d.kind),
                            "range": range,
                            "selectionRange": selection_range,
                            "detail": d.signature,
                        })
                    })
                    .collect();
                self.respond(&id, json!(symbols))?;
            }
            "textDocument/definition" => {
                let result = match self.lookup(&params)? {
                    Some(Target::Local(local)) => {
                        let path = local.file.clone();
                        let text = self.workspace.text(&path).unwrap_or_default();
                        let index = LineIndex::new(&text);
                        let (line, col) = index.position(&text, local.definition_start_byte);
                        let (end_line, end_col) = index.position(&text, local.definition_end_byte);
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
                            "range": byte_range(
                                &index,
                                &text,
                                declaration.name_start_byte,
                                declaration.name_end_byte,
                            ),
                        })
                    }
                    Some(Target::Std(declaration)) => {
                        let text = grandiose::source_bundle::DISTRIBUTED_STANDARD_LIBRARY_SOURCE;
                        let index = LineIndex::new(text);
                        json!({
                            "uri": path_to_uri(&self.standard_library_path),
                            "range": byte_range(
                                &index,
                                text,
                                declaration.name_start_byte,
                                declaration.name_end_byte,
                            ),
                        })
                    }
                    None => Value::Null,
                };
                self.respond(&id, result)?;
            }
            "textDocument/hover" => {
                let result = match self.lookup(&params)? {
                    Some(Target::Local(local)) => json!({"contents": {
                        "kind": "markdown",
                        "value": format!("`{}`: `{}`", local.name, local.inferred_type),
                    }}),
                    Some(Target::Decl(declaration)) => hover_markdown(&declaration, false),
                    Some(Target::Std(declaration)) => hover_markdown(&declaration, true),
                    None => {
                        let path = doc_path(&params)?;
                        let text = self.workspace.text(&path).unwrap_or_default();
                        let offset = cursor_offset(&params, &text);
                        self.analysis.expression_at(&path, offset).map_or(
                            Value::Null,
                            |expression| {
                                json!({"contents": {
                                    "kind": "markdown",
                                    "value": format!("`{}`", expression.inferred_type),
                                }})
                            },
                        )
                    }
                };
                self.respond(&id, result)?;
            }
            "textDocument/signatureHelp" => {
                let path = doc_path(&params)?;
                let result = self
                    .workspace
                    .text(&path)
                    .and_then(|text| {
                        signature_help(&self.analysis, &path, &text, cursor_offset(&params, &text))
                    })
                    .unwrap_or(Value::Null);
                self.respond(&id, result)?;
            }
            "textDocument/semanticTokens/full" => {
                let path = doc_path(&params)?;
                let result = self.workspace.text(&path).map_or(Value::Null, |text| {
                    semantic_tokens(&self.analysis, &path, &text)
                });
                self.respond(&id, result)?;
            }
            "textDocument/inlayHint" => {
                let path = doc_path(&params)?;
                let result = self.workspace.text(&path).map_or(Value::Null, |text| {
                    let index = LineIndex::new(&text);
                    let start = params["range"]["start"]["line"].as_u64().map_or(0, |line| {
                        index.offset(
                            &text,
                            line as u32,
                            params["range"]["start"]["character"].as_u64().unwrap_or(0) as u32,
                        )
                    });
                    let end = params["range"]["end"]["line"]
                        .as_u64()
                        .map_or(text.len(), |line| {
                            index.offset(
                                &text,
                                line as u32,
                                params["range"]["end"]["character"].as_u64().unwrap_or(0) as u32,
                            )
                        });
                    let hints = self
                        .analysis
                        .inlay_locals(&path, start, end)
                        .into_iter()
                        .filter(|local| {
                            !text[local.definition_end_byte.min(text.len())..]
                                .trim_start()
                                .starts_with(':')
                        })
                        .map(|local| {
                            let (line, character) =
                                index.position(&text, local.definition_end_byte);
                            json!({
                                "position": {"line": line, "character": character},
                                "label": format!(": {}", local.inferred_type),
                                "kind": 1,
                                "paddingRight": true,
                            })
                        })
                        .collect::<Vec<_>>();
                    json!(hints)
                });
                self.respond(&id, result)?;
            }
            "textDocument/references" => {
                let path = doc_path(&params)?;
                let include_declaration = params["context"]["includeDeclaration"]
                    .as_bool()
                    .unwrap_or(true);
                let locations = match self.lookup(&params)? {
                    Some(Target::Decl(declaration)) => {
                        json!(self.find_references(
                            &declaration.identity,
                            &path,
                            include_declaration,
                        ))
                    }
                    Some(Target::Std(declaration)) => {
                        json!(self.find_references(
                            &declaration.identity,
                            &path,
                            include_declaration,
                        ))
                    }
                    Some(Target::Local(local)) => {
                        json!(self.find_local_references(&local, &path, include_declaration,))
                    }
                    None => json!([]),
                };
                self.respond(&id, locations)?;
            }
            "textDocument/rename" => {
                let new_name = params["newName"].as_str().unwrap_or_default().to_string();
                let valid = !new_name.is_empty()
                    && new_name
                        .chars()
                        .next()
                        .is_some_and(|c| c.is_ascii_alphabetic() || c == '_')
                    && new_name
                        .chars()
                        .all(|c| c.is_ascii_alphanumeric() || c == '_');
                if !valid {
                    self.reply(json!({
                        "jsonrpc": "2.0", "id": id,
                        "error": {"code": -32602, "message": format!("`{new_name}` is not a valid identifier")},
                    }))?;
                    return Ok(true);
                }
                let result = match self.lookup(&params)? {
                    Some(Target::Decl(declaration)) | Some(Target::Std(declaration)) => {
                        let mut changes: serde_json::Map<String, Value> = Default::default();
                        let path = doc_path(&params)?;
                        for location in self.find_references(&declaration.identity, &path, true) {
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
                    Some(Target::Local(local)) => {
                        let mut changes: serde_json::Map<String, Value> = Default::default();
                        let path = doc_path(&params)?;
                        for location in self.find_local_references(&local, &path, true) {
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
                let analysis = std::rc::Rc::clone(&self.analysis);
                let mut items: Vec<Value> = Vec::new();
                let request_path = doc_path(&params).ok();
                if let Some(path) = request_path.as_ref()
                    && let Some(text) = self.workspace.text(path)
                {
                    let offset = cursor_offset(&params, &text);
                    for local in analysis.locals_at(path, offset) {
                        items.push(json!({
                            "label": local.name,
                            "kind": 6, // Variable
                            "detail": local.inferred_type,
                        }));
                    }
                }
                for d in analysis.declarations.iter().filter(|declaration| {
                    request_path
                        .as_ref()
                        .is_none_or(|path| analysis.same_root(path, &declaration.file))
                }) {
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
        if self.take_cancelled(id) {
            return self.reply(json!({
                "jsonrpc": "2.0", "id": id,
                "error": {"code": -32800, "message": "request cancelled"},
            }));
        }
        self.reply(json!({"jsonrpc": "2.0", "id": id, "result": result}))
    }

    fn is_cancelled(&self, id: &Value) -> bool {
        request_key(id).is_some_and(|key| self.cancellation.lock().unwrap().contains(&key))
    }

    fn take_cancelled(&self, id: &Value) -> bool {
        request_key(id).is_some_and(|key| self.cancellation.lock().unwrap().remove(&key))
    }

    fn schedule_analysis(&mut self) {
        if !self.dirty
            || self.analysis_in_flight.is_some()
            || self.input_generation.load(Ordering::Acquire) != self.applied_generation
        {
            return;
        }
        if self
            .analysis_sender
            .send(AnalysisCommand::Analyze(self.applied_generation))
            .is_ok()
        {
            self.analysis_in_flight = Some(self.applied_generation);
        }
    }

    fn accept_analysis(&mut self) -> Result<()> {
        while let Ok(result) = self.analysis_receiver.try_recv() {
            self.analysis_in_flight = None;
            if result.generation != self.applied_generation
                || self.input_generation.load(Ordering::Acquire) != result.generation
            {
                // The worker may finish an old, expensive request after newer
                // input arrives. Keep it as an internal compiler-session step,
                // but never expose its diagnostics or semantic snapshot.
                self.dirty = true;
                continue;
            }
            self.analysis = std::rc::Rc::new(result.analysis);
            self.analysis_generation = Some(result.generation);
            self.publish_analysis()?;
            self.dirty = false;
            let pending = std::mem::take(&mut self.pending_requests);
            for request in pending {
                if !self.handle(request)? {
                    break;
                }
            }
        }
        Ok(())
    }

    /// Publish one generation already completed by the background worker.
    fn publish_analysis(&mut self) -> Result<()> {
        let analysis = std::rc::Rc::clone(&self.analysis);
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
        for stale in self
            .published
            .difference(&current)
            .cloned()
            .collect::<Vec<_>>()
        {
            self.reply(json!({
                "jsonrpc": "2.0",
                "method": "textDocument/publishDiagnostics",
                "params": {"uri": path_to_uri(&stale), "diagnostics": []},
            }))?;
        }
        self.published = current;
        Ok(())
    }

    /// Resolve the identifier under the cursor: locals of the enclosing
    /// callable shadow workspace declarations, which shadow std.
    fn lookup(&self, params: &Value) -> Result<Option<Target>> {
        let path = doc_path(params)?;
        let Some(text) = self.workspace.text(&path) else {
            return Ok(None);
        };
        let offset = cursor_offset(params, &text);
        let analysis = std::rc::Rc::clone(&self.analysis);
        if let Some(occurrence) = analysis.local_occurrence_at(&path, offset)
            && let Some(local) = analysis.local(&occurrence.identity)
        {
            return Ok(Some(Target::Local(local.clone())));
        }
        if let Some(occurrence) = analysis.occurrence_at(&path, offset)
            && let Some(declaration) = analysis.declaration(&occurrence.identity)
        {
            if declaration.interface.identity.starts_with("std:") {
                return Ok(Some(Target::Std(declaration.clone())));
            }
            if analysis.same_root(&path, &declaration.file) {
                return Ok(Some(Target::Decl(declaration.clone())));
            }
        }
        // On an initial late compiler failure there is no last-good semantic
        // snapshot yet. The analysis layer may still have an exact, uniquely
        // resolved top-level interface occurrence from the current source.
        // This branch is intentionally after normal semantic/local lookup and
        // is used only for definition navigation.
        if let Some(declaration) = analysis.initial_error_declaration_at(&path, offset) {
            if declaration.identity.starts_with("std:") {
                return Ok(Some(Target::Std(declaration.clone())));
            }
            return Ok(Some(Target::Decl(declaration.clone())));
        }
        Ok(None)
    }

    /// Every compiler-bound occurrence of one declaration identity within the
    /// originating compilation root.
    fn find_references(
        &self,
        identity: &str,
        origin: &std::path::Path,
        include_declaration: bool,
    ) -> Vec<Value> {
        let analysis = std::rc::Rc::clone(&self.analysis);
        let mut locations = Vec::new();
        for occurrence in analysis.references(identity) {
            if occurrence.definition && !include_declaration {
                continue;
            }
            if !analysis.same_root(origin, &occurrence.file) {
                continue;
            }
            let Some(text) = self.workspace.text(&occurrence.file) else {
                continue;
            };
            let index = LineIndex::new(&text);
            locations.push(json!({
                "uri": path_to_uri(&occurrence.file),
                "range": byte_range(
                    &index,
                    &text,
                    occurrence.start_byte,
                    occurrence.end_byte,
                ),
            }));
        }
        locations
    }

    fn find_local_references(
        &self,
        target: &Local,
        path: &std::path::Path,
        include_declaration: bool,
    ) -> Vec<Value> {
        let analysis = std::rc::Rc::clone(&self.analysis);
        analysis
            .local_references(&target.identity)
            .filter_map(|occurrence| {
                if occurrence.definition && !include_declaration {
                    return None;
                }
                if !analysis.same_root(path, &occurrence.file) {
                    return None;
                }
                let text = self.workspace.text(&occurrence.file)?;
                let index = LineIndex::new(&text);
                Some(json!({
                    "uri": path_to_uri(&occurrence.file),
                    "range": byte_range(
                        &index,
                        &text,
                        occurrence.start_byte,
                        occurrence.end_byte,
                    ),
                }))
            })
            .collect()
    }
}

fn request_key(id: &Value) -> Option<String> {
    match id {
        Value::String(value) => Some(format!("s:{value}")),
        Value::Number(value) => Some(format!("n:{value}")),
        _ => None,
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

#[derive(Clone, Copy)]
enum Delimiter {
    Call {
        callee_start: usize,
        callee_end: usize,
        active_parameter: usize,
    },
    Other(char),
}

fn signature_help(
    analysis: &analysis::Analysis,
    path: &std::path::Path,
    text: &str,
    offset: usize,
) -> Option<Value> {
    let tokens = lex_lossless(text).ok()?;
    let significant = tokens
        .iter()
        .copied()
        .filter(|token| !token.kind.is_trivia() && token.span.start < offset)
        .collect::<Vec<_>>();
    let mut stack = Vec::new();
    let mut previous = None;
    for token in significant {
        let spelling = token.text(text);
        if token.kind == LosslessKind::Punctuation {
            match spelling {
                "(" => {
                    let call = previous
                        .filter(|previous: &grandiose::lossless::LosslessToken| {
                            previous.kind == LosslessKind::Identifier
                        })
                        .map_or(Delimiter::Other('('), |callee| Delimiter::Call {
                            callee_start: callee.span.start,
                            callee_end: callee.span.end,
                            active_parameter: 0,
                        });
                    stack.push(call);
                }
                "[" | "{" => stack.push(Delimiter::Other(spelling.chars().next()?)),
                ")" => {
                    if matches!(
                        stack.last(),
                        Some(Delimiter::Call { .. } | Delimiter::Other('('))
                    ) {
                        stack.pop();
                    }
                }
                "]" => {
                    if matches!(stack.last(), Some(Delimiter::Other('['))) {
                        stack.pop();
                    }
                }
                "}" => {
                    if matches!(stack.last(), Some(Delimiter::Other('{'))) {
                        stack.pop();
                    }
                }
                "," => {
                    if let Some(Delimiter::Call {
                        active_parameter, ..
                    }) = stack.last_mut()
                    {
                        *active_parameter += 1;
                    }
                }
                _ => {}
            }
        }
        previous = Some(token);
    }
    let (callee_start, callee_end, active_parameter) = stack.iter().rev().find_map(|frame| {
        let Delimiter::Call {
            callee_start,
            callee_end,
            active_parameter,
        } = frame
        else {
            return None;
        };
        Some((*callee_start, *callee_end, *active_parameter))
    })?;
    let occurrence = analysis.occurrences.iter().find(|occurrence| {
        occurrence.file == path
            && occurrence.start_byte == callee_start
            && occurrence.end_byte == callee_end
    })?;
    let declaration = analysis.declaration(&occurrence.identity)?;
    if declaration.kind != DeclarationKind::Callable {
        return None;
    }
    let signature = declaration.signature.as_ref()?;
    let parameters = signature_parameters(signature);
    let active_parameter = if parameters.is_empty() {
        0
    } else {
        active_parameter.min(parameters.len() - 1)
    };
    let parameter_payload = parameters
        .iter()
        .map(|label| json!({"label": label}))
        .collect::<Vec<_>>();
    Some(json!({
        "signatures": [{
            "label": signature,
            "documentation": declaration.docs,
            "parameters": parameter_payload,
        }],
        "activeSignature": 0,
        "activeParameter": active_parameter,
    }))
}

fn signature_parameters(signature: &str) -> Vec<String> {
    let Some(open) = signature.find('(') else {
        return Vec::new();
    };
    let mut depth = 0usize;
    let mut start = open + 1;
    let mut parameters = Vec::new();
    for (relative, character) in signature[open + 1..].char_indices() {
        let index = open + 1 + relative;
        match character {
            '(' | '[' | '{' | '<' => depth += 1,
            ')' if depth == 0 => {
                let parameter = signature[start..index].trim();
                if !parameter.is_empty() {
                    parameters.push(parameter.to_string());
                }
                break;
            }
            ')' | ']' | '}' | '>' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                let parameter = signature[start..index].trim();
                if !parameter.is_empty() {
                    parameters.push(parameter.to_string());
                }
                start = index + character.len_utf8();
            }
            _ => {}
        }
    }
    parameters
}

fn semantic_tokens(analysis: &analysis::Analysis, path: &std::path::Path, text: &str) -> Value {
    let mut spans = std::collections::BTreeMap::<(usize, usize), u32>::new();
    let lossless_tokens = lex_lossless(text).ok();
    if let Some(tokens) = &lossless_tokens {
        for token in tokens {
            let token_type = match token.kind {
                LosslessKind::LineComment | LosslessKind::BlockComment => Some(8),
                LosslessKind::String
                | LosslessKind::Character
                | LosslessKind::ByteString
                | LosslessKind::ByteCharacter => Some(9),
                LosslessKind::Number => Some(10),
                LosslessKind::Label => Some(13),
                LosslessKind::Identifier if is_keyword(token.text(text)) => Some(7),
                LosslessKind::Punctuation if is_operator(token.text(text)) => Some(11),
                _ => None,
            };
            if let Some(token_type) = token_type {
                insert_single_line_spans(
                    &mut spans,
                    text,
                    token.span.start,
                    token.span.end,
                    token_type,
                );
            }
        }
    }
    for occurrence in analysis
        .occurrences
        .iter()
        .filter(|occurrence| occurrence.file == path)
    {
        let Some(declaration) = analysis.declaration(&occurrence.identity) else {
            continue;
        };
        let Some(spelling) = text.get(occurrence.start_byte..occurrence.end_byte) else {
            continue;
        };
        if declaration.name.rsplit("::").next() != Some(spelling) {
            continue;
        }
        let token_type = match declaration.kind {
            DeclarationKind::Callable
                if declaration
                    .signature
                    .as_deref()
                    .is_some_and(|signature| signature.contains("-> !")) =>
            {
                13
            }
            DeclarationKind::Callable => 6,
            DeclarationKind::Struct => 3,
            DeclarationKind::Enum => 1,
            DeclarationKind::Type => 0,
            DeclarationKind::Effect => 5,
            DeclarationKind::Trait | DeclarationKind::Impl => 2,
            DeclarationKind::Global => 4,
            DeclarationKind::Fixity => 11,
        };
        spans.insert((occurrence.start_byte, occurrence.end_byte), token_type);

        // An enum/effect path names two different semantic roles. Keep the
        // resolved prefix colored as the nominal declaration, but color the
        // variant/operation after `::` as an enum member. In particular this
        // prevents LSP semantic highlighting from flattening handler clauses
        // such as `BrainIo::read(...)` into one effect-colored path.
        if matches!(
            declaration.kind,
            DeclarationKind::Enum | DeclarationKind::Effect
        ) && let Some(tokens) = &lossless_tokens
            && let Some((member_start, member_end)) =
                qualified_member_after(tokens, text, occurrence.end_byte)
        {
            spans.insert((member_start, member_end), 12);
        }
    }
    for occurrence in analysis
        .local_occurrences
        .iter()
        .filter(|occurrence| occurrence.file == path)
    {
        if analysis
            .local(&occurrence.identity)
            .is_some_and(|local| local.inferred_type.contains("$label$"))
        {
            spans.insert((occurrence.start_byte, occurrence.end_byte), 13);
        }
    }

    // Constructors are resolved in the compiler's type/pattern namespaces and
    // are not always emitted as top-level value occurrences. Recover their
    // two-token role only from a unique nominal declaration visible to this
    // compilation root, and only while the compiler snapshot still owns the
    // complete path span. Ambiguous equal names deliberately receive no
    // semantic override, leaving syntax highlighting intact.
    if let Some(tokens) = &lossless_tokens {
        let significant = tokens
            .iter()
            .filter(|token| !token.kind.is_trivia())
            .collect::<Vec<_>>();
        for window in significant.windows(3) {
            let [prefix, separator, member] = window else {
                continue;
            };
            if prefix.kind != LosslessKind::Identifier
                || separator.kind != LosslessKind::Punctuation
                || separator.text(text) != "::"
                || member.kind != LosslessKind::Identifier
                || !analysis.semantic_span_is_current(path, member.span.end)
            {
                continue;
            }
            let name = prefix.text(text);
            let mut candidates = analysis
                .declarations
                .iter()
                .chain(&analysis.std_declarations)
                .filter(|declaration| {
                    declaration.name == name
                        && matches!(
                            declaration.kind,
                            DeclarationKind::Enum | DeclarationKind::Effect
                        )
                        && (declaration.identity.starts_with("std:")
                            || analysis.same_root(path, &declaration.file))
                });
            let Some(declaration) = candidates.next() else {
                continue;
            };
            if candidates.any(|candidate| candidate.identity != declaration.identity) {
                continue;
            }
            let prefix_type = match declaration.kind {
                DeclarationKind::Enum => 1,
                DeclarationKind::Effect => 5,
                _ => unreachable!(),
            };
            spans.insert((prefix.span.start, prefix.span.end), prefix_type);
            spans.insert((member.span.start, member.span.end), 12);
        }

    }

    let index = LineIndex::new(text);
    let mut data = Vec::<u32>::new();
    let mut previous_line = 0;
    let mut previous_start = 0;
    for ((start, end), token_type) in spans {
        if start >= end || end > text.len() {
            continue;
        }
        let (line, start_character) = index.position(text, start);
        let (end_line, end_character) = index.position(text, end);
        if line != end_line || end_character <= start_character {
            continue;
        }
        let delta_line = line - previous_line;
        let delta_start = if delta_line == 0 {
            start_character - previous_start
        } else {
            start_character
        };
        data.extend([
            delta_line,
            delta_start,
            end_character - start_character,
            token_type,
            0,
        ]);
        previous_line = line;
        previous_start = start_character;
    }
    json!({"data": data})
}

fn qualified_member_after(
    tokens: &[grandiose::lossless::LosslessToken],
    text: &str,
    prefix_end: usize,
) -> Option<(usize, usize)> {
    let mut following = tokens
        .iter()
        .filter(|token| !token.kind.is_trivia() && token.span.start >= prefix_end);
    let separator = following.next()?;
    if separator.kind != LosslessKind::Punctuation || separator.text(text) != "::" {
        return None;
    }
    let member = following.next()?;
    (member.kind == LosslessKind::Identifier).then_some((member.span.start, member.span.end))
}

fn insert_single_line_spans(
    spans: &mut std::collections::BTreeMap<(usize, usize), u32>,
    text: &str,
    start: usize,
    end: usize,
    token_type: u32,
) {
    let mut line_start = start;
    for (relative, character) in text[start..end].char_indices() {
        if character == '\n' {
            let line_end = start + relative;
            if line_start < line_end {
                spans.insert((line_start, line_end), token_type);
            }
            line_start = line_end + 1;
        }
    }
    if line_start < end {
        spans.insert((line_start, end), token_type);
    }
}

fn is_keyword(spelling: &str) -> bool {
    matches!(
        spelling,
        "let"
            | "struct"
            | "enum"
            | "trait"
            | "impl"
            | "effect"
            | "where"
            | "handle"
            | "perform"
            | "resume"
            | "cancel"
            | "tail"
            | "label"
            | "leave"
            | "is"
            | "type"
            | "infix"
            | "infixl"
            | "infixr"
            | "prefix"
    )
}

fn is_operator(spelling: &str) -> bool {
    !matches!(
        spelling,
        "(" | ")" | "[" | "]" | "{" | "}" | "," | ";" | ":" | "." | "::"
    )
}

fn hover_markdown(declaration: &SemanticDeclaration, std: bool) -> Value {
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

fn byte_range(index: &LineIndex, text: &str, start: usize, end: usize) -> Value {
    let (start_line, start_col) = index.position(text, start.min(text.len()));
    let (end_line, end_col) = index.position(text, end.min(text.len()));
    json!({
        "start": {"line": start_line, "character": start_col},
        "end": {"line": end_line, "character": end_col},
    })
}

fn symbol_kind(kind: DeclarationKind) -> u32 {
    match kind {
        DeclarationKind::Callable => 12, // Function
        DeclarationKind::Struct => 23,
        DeclarationKind::Enum => 10,
        DeclarationKind::Type => 5,    // Class (alias)
        DeclarationKind::Effect => 24, // Event
        DeclarationKind::Trait => 11,  // Interface
        DeclarationKind::Impl => 11,   // Interface implementation
        DeclarationKind::Global => 14, // Constant
        DeclarationKind::Fixity => 24,
    }
}

fn completion_kind(kind: DeclarationKind) -> u32 {
    match kind {
        DeclarationKind::Callable => 3, // Function
        DeclarationKind::Struct | DeclarationKind::Enum | DeclarationKind::Type => 7, // Class
        DeclarationKind::Effect | DeclarationKind::Trait | DeclarationKind::Impl => 8, // Interface
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
        DeclarationKind::Impl => "impl",
        DeclarationKind::Global => "global",
        DeclarationKind::Fixity => "fixity",
    }
}
