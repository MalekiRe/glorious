//! Persistent whole-workspace compiler sessions for the language server.
//!
//! Each root is assembled with the compiler's real [`SourceBundle`], checked
//! by the real compiler pipeline, and scanned by the compiler-owned interface
//! pass. A successful check atomically replaces that root's declaration and
//! definition snapshot. A failed edit publishes diagnostics for the new text
//! while navigation continues to use the last successful snapshot; no partial
//! parse or declaration scan can leak into semantic requests.

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use anyhow::Result;
use grandiose::diagnostic::Severity;
use grandiose::interface::{InterfaceDeclaration, InterfaceSelection, scan_interfaces};
use grandiose::lossless::{LosslessKind, lex_lossless};
use grandiose::source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_NAME, Segment, SourceBundle};
use grandiose::{CompileOptions, OptimizationLevel, compile_bundle_to_phases_with_options};

pub struct Workspace {
    roots: Vec<PathBuf>,
    overlays: HashMap<PathBuf, String>,
    revision: u64,
    cache: RefCell<Option<(u64, Rc<Analysis>)>>,
    /// Successfully checked semantic state, independently transactional per
    /// workspace root.
    last_good: RefCell<BTreeMap<PathBuf, RootSnapshot>>,
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
    /// Compiler-owned declarations from the most recent successful root
    /// transaction.
    pub declarations: Vec<SemanticDeclaration>,
    /// Compiler-owned standard-library interface.
    pub std_declarations: Vec<SemanticDeclaration>,
    /// Definition-bound occurrences. References and rename query this by
    /// semantic identity rather than searching for equal token spellings.
    pub occurrences: Vec<SemanticOccurrence>,
    pub file_roots: BTreeMap<PathBuf, PathBuf>,
}

#[derive(Debug, Clone)]
pub struct SemanticDeclaration {
    pub interface: InterfaceDeclaration,
    pub file: PathBuf,
}

impl std::ops::Deref for SemanticDeclaration {
    type Target = InterfaceDeclaration;

    fn deref(&self) -> &Self::Target {
        &self.interface
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SemanticOccurrence {
    pub identity: String,
    pub file: PathBuf,
    pub start_byte: usize,
    pub end_byte: usize,
    pub definition: bool,
}

#[derive(Debug, Clone, Default)]
struct RootSnapshot {
    declarations: Vec<SemanticDeclaration>,
    std_declarations: Vec<SemanticDeclaration>,
    occurrences: Vec<SemanticOccurrence>,
}

impl Analysis {
    pub fn same_root(&self, left: &Path, right: &Path) -> bool {
        self.file_roots.get(left) == self.file_roots.get(right)
    }

    pub fn declaration(&self, identity: &str) -> Option<&SemanticDeclaration> {
        self.declarations
            .iter()
            .chain(&self.std_declarations)
            .find(|declaration| declaration.interface.identity == identity)
    }

    pub fn occurrence_at(&self, file: &Path, offset: usize) -> Option<&SemanticOccurrence> {
        self.occurrences.iter().find(|occurrence| {
            occurrence.file == file
                && (occurrence.start_byte..=occurrence.end_byte).contains(&offset)
        })
    }

    pub fn references(&self, identity: &str) -> impl Iterator<Item = &SemanticOccurrence> {
        self.occurrences
            .iter()
            .filter(move |occurrence| occurrence.identity == identity)
    }
}

impl Workspace {
    pub fn new(root: PathBuf) -> Workspace {
        Workspace {
            roots: vec![root],
            overlays: HashMap::new(),
            revision: 0,
            cache: RefCell::new(None),
            last_good: RefCell::new(BTreeMap::new()),
        }
    }

    pub fn set_roots(&mut self, mut roots: Vec<PathBuf>) {
        roots.sort();
        roots.dedup();
        if !roots.is_empty() && roots != self.roots {
            self.roots = roots;
            self.invalidate();
        }
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
    fn project_groups(&self) -> Vec<(PathBuf, Vec<PathBuf>)> {
        let mut groups = Vec::new();
        let mut assigned = BTreeSet::new();
        for root in &self.roots {
            let mut files = match self.resolve_project(root) {
                Ok(files) if !files.is_empty() => files,
                _ => self
                    .overlays
                    .keys()
                    .filter(|path| path.starts_with(root))
                    .cloned()
                    .collect(),
            };
            files.sort();
            files.dedup();
            files.retain(|file| assigned.insert(file.clone()));
            groups.push((root.clone(), files));
        }
        for file in self
            .overlays
            .keys()
            .filter(|file| !assigned.contains(*file))
        {
            let root = file.parent().unwrap_or(file).to_path_buf();
            groups.push((root, vec![file.clone()]));
        }
        groups
    }

    fn resolve_project(&self, root: &Path) -> Result<Vec<PathBuf>> {
        let (project_root, manifest) = grand::manifest::find_project(root)?;
        let lock = grand::lock::Lockfile::load(&project_root.join(grand::lock::LOCK_NAME))?;
        let options = grand::resolve::ResolveOptions {
            locked: false,
            update: None,
            offline: true,
        };
        let resolution =
            grand::resolve::resolve(&project_root, &manifest, lock.as_ref(), &options)?;
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
        if let Some((revision, analysis)) = self.cache.borrow().as_ref()
            && *revision == self.revision
        {
            return Rc::clone(analysis);
        }
        let analysis = Rc::new(self.compute());
        *self.cache.borrow_mut() = Some((self.revision, Rc::clone(&analysis)));
        analysis
    }

    fn compute(&self) -> Analysis {
        let groups = self.project_groups();
        let mut diagnostics: BTreeMap<PathBuf, Vec<FileDiagnostic>> = BTreeMap::new();
        let mut declarations = Vec::new();
        let mut std_declarations = Vec::new();
        let mut occurrences = Vec::new();
        let mut file_roots = BTreeMap::new();

        for (root, group_files) in &groups {
            let mut segments = Vec::new();
            for file in group_files {
                diagnostics.entry(file.clone()).or_default();
                file_roots.insert(file.clone(), root.clone());
                let Some(text) = self.text(file) else {
                    continue;
                };
                segments.push(Segment::new(file.display().to_string(), text));
            }
            let Some(primary) = segments.first().cloned() else {
                continue;
            };
            let bundle = SourceBundle::distributed(primary, segments.into_iter().skip(1));
            let fallback = group_files.first().cloned().unwrap_or_default();
            let checked = compile_bundle_to_phases_with_options(
                &bundle,
                CompileOptions {
                    optimization_level: OptimizationLevel::O0,
                },
            );
            let compiler_diagnostics = match &checked {
                Ok(_) => &[][..],
                Err(diagnostics) => diagnostics.as_slice(),
            };
            for diagnostic in compiler_diagnostics {
                let (file, start, end) = match diagnostic.span.and_then(|s| bundle.map_span(s)) {
                    Some(mapped) => {
                        let file = PathBuf::from(mapped.segment.name());
                        if group_files.contains(&file) {
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

            // Both compiler checking and interface extraction must succeed
            // before the new side tables become visible. This is the semantic
            // transaction boundary for one workspace root.
            let user_interfaces = scan_interfaces(&bundle, InterfaceSelection::User);
            let standard_interfaces = scan_interfaces(&bundle, InterfaceSelection::StandardLibrary);
            if checked.is_ok()
                && let (Ok(user), Ok(standard)) = (user_interfaces, standard_interfaces)
            {
                let snapshot = semantic_snapshot(&bundle, user, standard);
                self.last_good.borrow_mut().insert(root.clone(), snapshot);
            }
            if let Some(snapshot) = self.last_good.borrow().get(root) {
                declarations.extend(snapshot.declarations.iter().cloned());
                std_declarations.extend(snapshot.std_declarations.iter().cloned());
                occurrences.extend(snapshot.occurrences.iter().cloned());
            }
        }
        std_declarations.sort_by(|left, right| left.identity.cmp(&right.identity));
        std_declarations.dedup_by(|left, right| left.identity == right.identity);
        Analysis {
            diagnostics,
            declarations,
            std_declarations,
            occurrences,
            file_roots,
        }
    }
}

fn semantic_snapshot(
    bundle: &SourceBundle,
    user: Vec<InterfaceDeclaration>,
    standard: Vec<InterfaceDeclaration>,
) -> RootSnapshot {
    let convert = |interface: InterfaceDeclaration| SemanticDeclaration {
        file: PathBuf::from(&interface.file),
        interface,
    };
    let declarations = user.into_iter().map(convert).collect::<Vec<_>>();
    let std_declarations = standard.into_iter().map(convert).collect::<Vec<_>>();
    let mut occurrences = declarations
        .iter()
        .map(|declaration| SemanticOccurrence {
            identity: declaration.interface.identity.clone(),
            file: declaration.file.clone(),
            start_byte: declaration.interface.name_start_byte,
            end_byte: declaration.interface.name_end_byte,
            definition: true,
        })
        .collect::<Vec<_>>();

    // A successfully compiled flat namespace has one authoritative identity
    // for an unambiguous spelling. Ambiguous cross-namespace spellings are
    // deliberately omitted until the compiler exports its typed occurrence
    // table; guessing would make rename unsound.
    let mut identities = BTreeMap::<String, Vec<String>>::new();
    for declaration in declarations.iter().chain(&std_declarations) {
        identities
            .entry(declaration.interface.name.clone())
            .or_default()
            .push(declaration.interface.identity.clone());
    }
    for segment in bundle.segments() {
        if segment.name() == DISTRIBUTED_STANDARD_LIBRARY_NAME {
            continue;
        }
        let file = PathBuf::from(segment.name());
        let Ok(tokens) = lex_lossless(segment.source()) else {
            continue;
        };
        let tokens = tokens
            .into_iter()
            .filter(|token| !token.kind.is_trivia())
            .collect::<Vec<_>>();
        for (index, token) in tokens.iter().copied().enumerate() {
            if token.kind != LosslessKind::Identifier {
                continue;
            }
            let name = token.text(segment.source());
            let Some(identity) = identities
                .get(name)
                .filter(|candidates| candidates.len() == 1)
                .and_then(|candidates| candidates.first())
            else {
                continue;
            };
            // Locals shadow the flat value namespace. Do not attach a global
            // identity to a compiler-accepted local use just because its
            // spelling is equal.
            if locals_at(segment.source(), token.span.start)
                .iter()
                .any(|local| local.name == name)
            {
                continue;
            }
            let previous = index
                .checked_sub(1)
                .and_then(|index| tokens.get(index))
                .map(|token| token.text(segment.source()));
            let next = tokens
                .get(index + 1)
                .map(|token| token.text(segment.source()));
            if matches!(previous, Some("let" | ".")) || matches!(next, Some(":" | "=")) {
                continue;
            }
            if occurrences.iter().any(|occurrence| {
                occurrence.file == file
                    && occurrence.start_byte == token.span.start
                    && occurrence.end_byte == token.span.end
            }) {
                continue;
            }
            occurrences.push(SemanticOccurrence {
                identity: identity.clone(),
                file: file.clone(),
                start_byte: token.span.start,
                end_byte: token.span.end,
                definition: false,
            });
        }
    }
    occurrences.sort_by(|left, right| {
        (&left.file, left.start_byte, left.end_byte).cmp(&(
            &right.file,
            right.start_byte,
            right.end_byte,
        ))
    });
    RootSnapshot {
        declarations,
        std_declarations,
        occurrences,
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
                let name_offset = body_start + position + 3 + (rest.len() - trimmed.len());
                locals.push(Local {
                    name,
                    def_offset: name_offset,
                    detail: "let binding".into(),
                });
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
                    "let"
                        | "type"
                        | "struct"
                        | "enum"
                        | "trait"
                        | "impl"
                        | "effect"
                        | "cases"
                        | "infixl"
                        | "infixr"
                        | "prefix"
                )
                && trimmed[head.len()..].trim_start().starts_with(['(', '<']);
            if is_callable && let Some(open) = text[line_start..].find('{') {
                let body_open = line_start + open;
                let body_end = matching_brace(text, body_open).unwrap_or(text.len());
                candidate = Some((line_start, body_open + 1, body_end));
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
    let tokens = match lex_lossless(text) {
        Ok(tokens) => tokens,
        Err(error) => {
            let prefix_end = error.span.map_or(0, |span| span.start);
            lex_lossless(&text[..prefix_end]).unwrap_or_default()
        }
    };
    tokens
        .into_iter()
        .filter_map(|token| match token.kind {
            LosslessKind::Identifier => Some((token.text(text), token.span.start)),
            LosslessKind::Label | LosslessKind::Lifetime => Some((
                &text[token.span.start + 1..token.span.end],
                token.span.start + 1,
            )),
            _ => None,
        })
        .collect()
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
        let names: Vec<String> = locals_at(text, cursor)
            .into_iter()
            .map(|l| l.name)
            .collect();
        assert_eq!(names, vec!["seed"]);
    }

    #[test]
    fn std_index_contains_prelude_names() {
        let bundle =
            SourceBundle::distributed(Segment::new("main.glorious", "main() -> i64 { 0 }"), []);
        let standard = scan_interfaces(&bundle, InterfaceSelection::StandardLibrary).unwrap();
        let names: Vec<&str> = standard.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"if"), "std scan missing `if`: {names:?}");
    }

    #[test]
    fn identifiers_skip_nested_comments_literals_and_keep_byte_offsets() {
        let text = "before /* hidden /* nested */ end */ \"also_hidden\" 😀 after";
        let after = text.find("after").unwrap();
        assert_eq!(identifiers(text), vec![("before", 0), ("after", after)]);
        assert_ne!(after, text[..after].encode_utf16().count());
    }

    #[test]
    fn identifiers_before_malformed_trivia_remain_available() {
        assert_eq!(identifiers("visible /* never closed"), vec![("visible", 0)]);
    }

    #[test]
    fn semantic_occurrences_do_not_capture_shadowing_locals() {
        let bundle = SourceBundle::distributed(
            Segment::new(
                "main.glorious",
                "helper() -> () { () }\nmain() -> () {\n    let helper = ()\n    helper\n}",
            ),
            [],
        );
        let user = scan_interfaces(&bundle, InterfaceSelection::User).unwrap();
        let standard = scan_interfaces(&bundle, InterfaceSelection::StandardLibrary).unwrap();
        let snapshot = semantic_snapshot(&bundle, user, standard);
        let helper_occurrences = snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == "user:value:helper")
            .collect::<Vec<_>>();
        assert_eq!(helper_occurrences.len(), 1);
        assert!(helper_occurrences[0].definition);
    }

    #[test]
    fn workspace_roots_are_checked_as_independent_bundles() {
        let temporary = tempfile::TempDir::new().unwrap();
        let first = temporary.path().join("first");
        let second = temporary.path().join("second");
        for root in [&first, &second] {
            std::fs::create_dir_all(root.join("src")).unwrap();
            std::fs::write(
                root.join("grandiose.toml"),
                format!(
                    "[project]\nname = \"{}\"\nversion = \"0.1.0\"\nentry = \"src/main.gr\"\n",
                    root.file_name().unwrap().to_string_lossy()
                ),
            )
            .unwrap();
        }
        let first_main = first.join("src/main.gr");
        let second_main = second.join("src/main.gr");
        std::fs::write(
            &first_main,
            "shared() -> () { () }\nmain() -> () { shared() }\n",
        )
        .unwrap();
        std::fs::write(
            &second_main,
            "shared() -> () { () }\nmain() -> () { shared() }\n",
        )
        .unwrap();

        let mut workspace = Workspace::new(first.clone());
        workspace.set_roots(vec![first, second]);
        let analysis = workspace.analyze();
        assert!(!analysis.same_root(&first_main, &second_main));
        assert!(analysis.diagnostics[&first_main].is_empty());
        assert!(analysis.diagnostics[&second_main].is_empty());
    }
}
