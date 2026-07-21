//! Whole-workspace analysis: builds the concatenated source bundle exactly
//! the way the compiler does (embedded std + dependency sources + root, using
//! grand's resolver), runs the vendored frontend (lex -> resilient parse ->
//! validate), and maps diagnostics back through the bundle's segment table to
//! per-file byte ranges. Also maintains the declaration index (grand's
//! heuristic scanner, overlay-aware, plus the embedded std) powering
//! symbols/definition/hover/completion/references.
//!
//! Analysis is cached per overlay revision: every mutation bumps `revision`,
//! and `analyze()` recomputes only when the cached snapshot is stale.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use anyhow::Result;
use grand::contract::Declaration;

use crate::frontend::diagnostic::{Diagnostic, Severity};
use crate::frontend::source_bundle::{
    Segment, SourceBundle, DISTRIBUTED_STANDARD_LIBRARY_SOURCE,
};
use crate::frontend::{lexer, parser, validate};

pub struct Workspace {
    root: PathBuf,
    overlays: HashMap<PathBuf, String>,
    revision: u64,
    cache: RefCell<Option<(u64, Rc<Analysis>)>>,
}

#[derive(Debug, Clone)]
pub struct FileDiagnostic {
    pub start_byte: usize,
    pub end_byte: usize,
    pub severity: Severity,
    pub message: String,
    pub code: Option<String>,
}

pub struct Analysis {
    /// Every analyzed file has an entry (possibly empty) so stale diagnostics
    /// get cleared on publish.
    pub diagnostics: BTreeMap<PathBuf, Vec<FileDiagnostic>>,
    /// Workspace declarations (heuristic scan, overlay-aware).
    pub declarations: Vec<Declaration>,
    /// Prelude declarations from the embedded standard library. Separate from
    /// `declarations` so go-to-definition can skip them (no real file) while
    /// hover/completion include them.
    pub std_declarations: &'static [Declaration],
    /// The analyzed files, in bundle order (used for reference search).
    pub files: Vec<PathBuf>,
}

fn std_declarations() -> &'static [Declaration] {
    static STD: std::sync::OnceLock<Vec<Declaration>> = std::sync::OnceLock::new();
    STD.get_or_init(|| {
        let std_file = Path::new("\u{ab}std\u{bb}");
        let mut declarations =
            grand::scan::scan(std_file, DISTRIBUTED_STANDARD_LIBRARY_SOURCE);
        // The distributed bundle is currently a stub — the prelude lives in
        // the interpreter. Backfill the documented names it provides; real
        // scan results take precedence as the bundle grows.
        for (name, kind) in [
            ("if", grand::contract::DeclarationKind::Callable),
            ("else", grand::contract::DeclarationKind::Callable),
            ("and", grand::contract::DeclarationKind::Callable),
            ("or", grand::contract::DeclarationKind::Callable),
            ("not", grand::contract::DeclarationKind::Callable),
            ("resume", grand::contract::DeclarationKind::Callable),
            ("Result", grand::contract::DeclarationKind::Enum),
            ("Option", grand::contract::DeclarationKind::Type),
            ("Bool", grand::contract::DeclarationKind::Type),
        ] {
            if !declarations.iter().any(|d| d.name == name) {
                declarations.push(Declaration {
                    name: name.into(),
                    kind,
                    file: std_file.to_path_buf(),
                    line: 0,
                    signature: None,
                    docs: None,
                });
            }
        }
        declarations
    })
}

impl Workspace {
    pub fn new(root: PathBuf) -> Workspace {
        Workspace { root, overlays: HashMap::new(), revision: 0, cache: RefCell::new(None) }
    }

    pub fn open(&mut self, path: PathBuf, text: String) {
        self.overlays.insert(path, text);
        self.revision += 1;
    }

    pub fn close(&mut self, path: &Path) {
        self.overlays.remove(path);
        self.revision += 1;
    }

    /// Files on disk can change behind our back; a publish after save should
    /// recompute even if no overlay changed.
    pub fn invalidate(&mut self) {
        self.revision += 1;
    }

    pub fn text(&self, path: &Path) -> Option<String> {
        if let Some(text) = self.overlays.get(path) {
            return Some(text.clone());
        }
        std::fs::read_to_string(path).ok()
    }

    /// Ordered compilation inputs. Uses grand's project discovery + resolver
    /// (offline: an editor session must never hit the network); when there is
    /// no manifest or resolution fails, degrades to the open overlays so
    /// single-file editing still works.
    fn project_files(&self) -> Vec<PathBuf> {
        match self.resolve_project() {
            Ok(files) if !files.is_empty() => files,
            _ => {
                let mut files: Vec<PathBuf> = self.overlays.keys().cloned().collect();
                files.sort();
                files
            }
        }
    }

    fn resolve_project(&self) -> Result<Vec<PathBuf>> {
        let (project_root, manifest) = grand::manifest::find_project(&self.root)?;
        let lock = grand::lock::Lockfile::load(&project_root.join(grand::lock::LOCK_NAME))?;
        let options = grand::resolve::ResolveOptions { locked: false, update: None, offline: true };
        let resolution = grand::resolve::resolve(&project_root, &manifest, lock.as_ref(), &options)?;
        let mut files = Vec::new();
        for package in &resolution.packages {
            files.extend(grand::bundle::package_sources(package)?);
            // Unlike a build, analysis includes entry files wherever they are
            // (a library root has none; that's fine).
            if let Some(entry) = &package.manifest.project.entry {
                let entry = package.root.join(entry);
                if entry.is_file() {
                    files.push(entry);
                }
            }
        }
        Ok(files)
    }

    /// Cached per revision; cheap to call from every request handler.
    pub fn analyze(&self) -> Rc<Analysis> {
        if let Some((revision, analysis)) = self.cache.borrow().as_ref() {
            if *revision == self.revision {
                return Rc::clone(analysis);
            }
        }
        let analysis = Rc::new(self.compute());
        *self.cache.borrow_mut() = Some((self.revision, Rc::clone(&analysis)));
        analysis
    }

    fn compute(&self) -> Analysis {
        let files = self.project_files();
        let mut diagnostics: BTreeMap<PathBuf, Vec<FileDiagnostic>> =
            files.iter().map(|f| (f.clone(), Vec::new())).collect();
        let mut declarations = Vec::new();

        let mut segments = Vec::new();
        for file in &files {
            let Some(text) = self.text(file) else { continue };
            declarations.extend(grand::scan::scan(file, &text));
            segments.push(Segment::new(file.display().to_string(), text));
        }
        let Some(primary) = segments.first().cloned() else {
            return Analysis {
                diagnostics,
                declarations,
                std_declarations: std_declarations(),
                files,
            };
        };
        let bundle = SourceBundle::distributed(primary, segments.into_iter().skip(1));

        let found = check(&bundle);
        let fallback = files.first().cloned().unwrap_or_default();
        for diagnostic in found {
            let (file, start, end) = match diagnostic.span.and_then(|s| bundle.map_span(s)) {
                Some(mapped) => {
                    let file = PathBuf::from(mapped.segment.name());
                    // Diagnostics inside the embedded std segment (its name is
                    // not a workspace file) surface on the primary file.
                    if diagnostics.contains_key(&file) {
                        (file, mapped.span.range().start, mapped.span.range().end)
                    } else {
                        (fallback.clone(), 0, 0)
                    }
                }
                None => (fallback.clone(), 0, 0),
            };
            diagnostics.entry(file).or_default().push(FileDiagnostic {
                start_byte: start,
                end_byte: end.max(start),
                severity: diagnostic.severity,
                message: if diagnostic.message.is_empty() {
                    diagnostic.title.clone()
                } else {
                    format!("{}: {}", diagnostic.title, diagnostic.message)
                },
                code: diagnostic.code.clone(),
            });
        }
        Analysis { diagnostics, declarations, std_declarations: std_declarations(), files }
    }
}

/// The frontend's static pipeline. The resilient parser reports every
/// declaration-level error and still yields a partial program; validation
/// only runs on a fully parsed program (partial programs would produce
/// misleading unknown-name errors for the broken declarations).
fn check(bundle: &SourceBundle) -> Vec<Diagnostic> {
    let tokens = match lexer::lex(bundle.source()) {
        Ok(tokens) => tokens,
        Err(error) => return vec![error],
    };
    let (program, parse_errors) = parser::parse_resilient(tokens);
    if !parse_errors.is_empty() {
        return parse_errors;
    }
    match validate::validate(&program) {
        Ok(()) => Vec::new(),
        Err(errors) => errors,
    }
}

// ---------------------------------------------------------------------------
// Locals: a scope-aware, token-light view of the callable under the cursor.

pub struct Local {
    pub name: String,
    /// Byte offset of the defining occurrence in the same file.
    pub def_offset: usize,
    pub detail: String,
}

/// Parameters and `let` bindings of the callable enclosing `offset`,
/// text-derived so it works on broken files. Bindings after the cursor are
/// excluded (they are not in scope yet).
pub fn locals_at(text: &str, offset: usize) -> Vec<Local> {
    let Some((header_start, body_start, body_end)) = enclosing_callable(text, offset) else {
        return Vec::new();
    };
    let mut locals = Vec::new();
    // Parameters: identifiers directly followed by `:` inside the header's
    // parameter parentheses.
    if let Some(open) = text[header_start..body_start].find('(') {
        let params_start = header_start + open + 1;
        let close = matching_paren(text, params_start - 1).unwrap_or(body_start);
        for (name, position) in identifiers(&text[params_start..close]) {
            let after = text[params_start + position + name.len()..close.min(text.len())]
                .trim_start()
                .starts_with(':');
            if after {
                locals.push(Local {
                    name: name.to_string(),
                    def_offset: params_start + position,
                    detail: "parameter".into(),
                });
            }
        }
    }
    // `let name` bindings before the cursor inside the body.
    let scope_end = offset.clamp(body_start, body_end);
    let body = &text[body_start..scope_end];
    for (word, position) in identifiers(body) {
        if word == "let" {
            let rest = &body[position + 3..];
            let trimmed = rest.trim_start();
            let name: String = trimmed
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            if !name.is_empty() && !name.chars().next().unwrap().is_ascii_digit() {
                let name_offset =
                    body_start + position + 3 + (rest.len() - trimmed.len());
                locals.push(Local { name, def_offset: name_offset, detail: "let binding".into() });
            }
        }
    }
    locals
}

/// (header start, body `{` offset + 1, body end) of the callable containing
/// `offset`, found by scanning top-level declarations heuristically.
fn enclosing_callable(text: &str, offset: usize) -> Option<(usize, usize, usize)> {
    let mut line_start = 0usize;
    let mut depth = 0i64;
    let mut candidate: Option<(usize, usize, usize)> = None;
    for line in text.split_inclusive('\n') {
        if depth == 0 {
            let trimmed = line.trim_start();
            let head: String = trimmed
                .chars()
                .take_while(|c| c.is_ascii_alphanumeric() || *c == '_')
                .collect();
            let is_callable = !head.is_empty()
                && !matches!(
                    head.as_str(),
                    "let" | "type" | "struct" | "enum" | "trait" | "impl" | "effect" | "cases"
                        | "infixl" | "infixr" | "prefix"
                )
                && trimmed[head.len()..].trim_start().starts_with(['(', '<']);
            if is_callable {
                if let Some(open) = text[line_start..].find('{') {
                    let body_open = line_start + open;
                    let body_end = matching_brace(text, body_open).unwrap_or(text.len());
                    candidate = Some((line_start, body_open + 1, body_end));
                }
            }
        }
        for byte in line.bytes() {
            match byte {
                b'{' | b'(' | b'[' => depth += 1,
                b'}' | b')' | b']' => depth -= 1,
                _ => {}
            }
        }
        line_start += line.len();
        if line_start > offset {
            break;
        }
    }
    candidate.filter(|(start, _, end)| (*start..=*end).contains(&offset))
}

fn matching_brace(text: &str, open: usize) -> Option<usize> {
    matching(text, open, b'{', b'}')
}

fn matching_paren(text: &str, open: usize) -> Option<usize> {
    matching(text, open, b'(', b')')
}

fn matching(text: &str, open: usize, open_byte: u8, close_byte: u8) -> Option<usize> {
    let mut depth = 0i64;
    for (index, byte) in text.bytes().enumerate().skip(open) {
        if byte == open_byte {
            depth += 1;
        } else if byte == close_byte {
            depth -= 1;
            if depth == 0 {
                return Some(index);
            }
        }
    }
    None
}

/// Word-boundary identifier occurrences (name, byte offset) in `text`,
/// skipping line comments and string literals.
pub fn identifiers(text: &str) -> Vec<(&str, usize)> {
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        match bytes[i] {
            b'"' => {
                i += 1;
                while i < bytes.len() && bytes[i] != b'"' {
                    i += if bytes[i] == b'\\' { 2 } else { 1 };
                }
                i += 1;
            }
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b if b.is_ascii_alphabetic() || b == b'_' => {
                let start = i;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                out.push((&text[start..i], start));
            }
            b if b.is_ascii_digit() => {
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
            }
            _ => i += 1,
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn locals_see_params_and_earlier_lets() {
        let text = "helper(seed: i64) -> i64 { seed }\n\
                    main(count: i64) -> i64 {\n    let first = 1\n    let second = 2\n    first\n}\n";
        let cursor = text.rfind("first").unwrap();
        let locals = locals_at(text, cursor);
        let names: Vec<&str> = locals.iter().map(|l| l.name.as_str()).collect();
        assert_eq!(names, vec!["count", "first", "second"]);
        // From inside `helper`, only helper's scope is visible.
        let cursor = text.find("seed }").unwrap();
        let names: Vec<String> = locals_at(text, cursor).into_iter().map(|l| l.name).collect();
        assert_eq!(names, vec!["seed"]);
    }

    #[test]
    fn std_index_contains_prelude_names() {
        let names: Vec<&str> = std_declarations().iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"if"), "std scan missing `if`: {names:?}");
    }
}
