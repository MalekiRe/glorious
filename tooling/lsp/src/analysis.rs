//! Persistent whole-workspace compiler sessions for the language server.
//!
//! Each root is assembled with the compiler's real [`SourceBundle`], checked
//! by the real compiler pipeline, and scanned by the compiler-owned interface
//! pass. A successful check atomically replaces that root's declaration and
//! definition snapshot. A failed edit publishes diagnostics for the new text
//! while navigation continues to use the last successful snapshot; no partial
//! parse or declaration scan can leak into semantic requests.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::hash::{Hash, Hasher};
use std::path::{Path, PathBuf};
use std::rc::Rc;

use anyhow::Result;
use grandiose::compiler_session::CompilationDriver;
use grandiose::diagnostic::Severity;
use grandiose::interface::{
    DeclarationKind, InterfaceDeclaration, InterfaceOccurrence, InterfaceSnapshot,
    scan_interface_bundle,
};
#[cfg(test)]
use grandiose::interface::{InterfaceSelection, scan_interface_snapshot};
use grandiose::lossless::{LosslessKind, lex_lossless};
use grandiose::semantic::SemanticSnapshot as CompilerSemanticSnapshot;
use grandiose::source_bundle::{Segment, SourceBundle};
use grandiose::{CompileOptions, OptimizationLevel};

pub struct Workspace {
    roots: Vec<PathBuf>,
    overlays: HashMap<PathBuf, String>,
    analysis_exclusions: BTreeSet<PathBuf>,
    revision: u64,
    cache: RefCell<Option<(u64, Rc<Analysis>)>>,
    root_cache: RefCell<BTreeMap<PathBuf, CachedRootAnalysis>>,
    /// Successfully checked semantic state, independently transactional per
    /// workspace root.
    last_good: RefCell<BTreeMap<PathBuf, RootSnapshot>>,
    next_body_arena: Cell<u64>,
    compiler_sessions: RefCell<BTreeMap<PathBuf, CompilationDriver>>,
    #[cfg(test)]
    root_analysis_runs: Cell<u64>,
}

#[derive(Clone)]
struct CachedRootAnalysis {
    fingerprint: u64,
    diagnostics: BTreeMap<PathBuf, Vec<FileDiagnostic>>,
    initial_error_declarations: Vec<SemanticDeclaration>,
    initial_error_occurrences: Vec<SemanticOccurrence>,
}

#[derive(Debug, Clone)]
pub struct FileDiagnostic {
    pub start_byte: usize,
    pub end_byte: usize,
    pub severity: Severity,
    pub message: String,
    pub code: Option<String>,
}

#[derive(Clone, Default)]
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
    /// Compiler-elaborated local definitions and references.
    pub locals: Vec<Local>,
    pub local_occurrences: Vec<SemanticOccurrence>,
    pub expression_types: Vec<SemanticExpression>,
    /// Exactly resolved top-level names from the current source when the
    /// compiler has never produced a successful snapshot for this root. This
    /// is deliberately definition-only: references, rename, hover, and local
    /// lookup continue to require compiler-owned semantic state.
    initial_error_declarations: Vec<SemanticDeclaration>,
    initial_error_occurrences: Vec<SemanticOccurrence>,
    /// Byte prefix unchanged from the successful snapshot that owns semantic
    /// spans. Requests outside it must not apply stale offsets to a broken edit.
    semantic_prefixes: BTreeMap<PathBuf, usize>,
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
    locals: Vec<Local>,
    local_occurrences: Vec<SemanticOccurrence>,
    expression_types: Vec<SemanticExpression>,
    sources: BTreeMap<PathBuf, String>,
    body_arenas: BTreeMap<String, BodyArena>,
}

#[derive(Debug, Clone)]
struct BodyArena {
    generation: u64,
    semantic: Rc<grandiose::semantic::SemanticBodySnapshot>,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct Local {
    pub identity: String,
    pub name: String,
    pub file: PathBuf,
    pub definition_start_byte: usize,
    pub definition_end_byte: usize,
    pub scope_start_byte: usize,
    pub scope_end_byte: usize,
    pub inferred_type: String,
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub struct SemanticExpression {
    pub file: PathBuf,
    pub start_byte: usize,
    pub end_byte: usize,
    pub inferred_type: String,
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
                && (occurrence.start_byte..occurrence.end_byte).contains(&offset)
                && self.span_is_current(file, occurrence.end_byte)
        })
    }

    pub fn references(&self, identity: &str) -> impl Iterator<Item = &SemanticOccurrence> {
        self.occurrences.iter().filter(move |occurrence| {
            occurrence.identity == identity
                && self.span_is_current(&occurrence.file, occurrence.end_byte)
        })
    }

    pub fn local(&self, identity: &str) -> Option<&Local> {
        self.locals.iter().find(|local| local.identity == identity)
    }

    pub fn local_occurrence_at(&self, file: &Path, offset: usize) -> Option<&SemanticOccurrence> {
        self.local_occurrences.iter().find(|occurrence| {
            occurrence.file == file
                && (occurrence.start_byte..occurrence.end_byte).contains(&offset)
                && self.span_is_current(file, occurrence.end_byte)
        })
    }

    pub fn local_references(&self, identity: &str) -> impl Iterator<Item = &SemanticOccurrence> {
        self.local_occurrences.iter().filter(move |occurrence| {
            occurrence.identity == identity
                && self.span_is_current(&occurrence.file, occurrence.end_byte)
        })
    }

    pub fn expression_at(&self, file: &Path, offset: usize) -> Option<&SemanticExpression> {
        self.expression_types
            .iter()
            .filter(|expression| {
                expression.file == file
                    && (expression.start_byte..expression.end_byte).contains(&offset)
                    && self.span_is_current(file, expression.end_byte)
            })
            .min_by_key(|expression| expression.end_byte.saturating_sub(expression.start_byte))
    }

    /// Resolve a top-level name from the current, module-resolved interface
    /// when initial compilation failed after parsing/name resolution. The
    /// caller must try compiler-owned locals and declarations first.
    ///
    /// Both the occurrence identity and its definition must be unique in the
    /// originating root. This makes the fallback fail closed under ambiguity
    /// and prevents equal names in sibling workspace roots from cross-linking.
    pub fn initial_error_declaration_at(
        &self,
        file: &Path,
        offset: usize,
    ) -> Option<&SemanticDeclaration> {
        let mut identities = self
            .initial_error_occurrences
            .iter()
            .filter(|occurrence| {
                occurrence.file == file
                    && (occurrence.start_byte..occurrence.end_byte).contains(&offset)
            })
            .map(|occurrence| occurrence.identity.as_str());
        let identity = identities.next()?;
        if identities.any(|candidate| candidate != identity) {
            return None;
        }

        let mut declarations = self
            .initial_error_declarations
            .iter()
            .filter(|declaration| {
                declaration.identity == identity
                    && (identity.starts_with("std:") || self.same_root(file, &declaration.file))
            });
        let declaration = declarations.next()?;
        if declarations.any(|candidate| candidate.file != declaration.file) {
            return None;
        }
        Some(declaration)
    }

    pub fn locals_at(&self, file: &Path, offset: usize) -> Vec<&Local> {
        let mut by_name = BTreeMap::new();
        for local in self.locals.iter().filter(|local| {
            local.file == file
                && local.definition_start_byte <= offset
                && (local.scope_start_byte..=local.scope_end_byte).contains(&offset)
                && self.span_is_current(file, local.definition_end_byte)
        }) {
            by_name.insert(local.name.as_str(), local);
        }
        by_name.into_values().collect()
    }

    pub fn inlay_locals(&self, file: &Path, start: usize, end: usize) -> Vec<&Local> {
        self.locals
            .iter()
            .filter(|local| {
                local.file == file
                    && (start..end).contains(&local.definition_end_byte)
                    && self.span_is_current(file, local.definition_end_byte)
            })
            .collect()
    }

    pub fn semantic_span_is_current(&self, file: &Path, end: usize) -> bool {
        self.span_is_current(file, end)
    }

    fn span_is_current(&self, file: &Path, end: usize) -> bool {
        self.semantic_prefixes
            .get(file)
            .is_some_and(|prefix| end <= *prefix)
    }
}

impl Workspace {
    pub fn new(root: PathBuf) -> Workspace {
        Workspace {
            roots: vec![root],
            overlays: HashMap::new(),
            analysis_exclusions: BTreeSet::new(),
            revision: 0,
            cache: RefCell::new(None),
            root_cache: RefCell::new(BTreeMap::new()),
            last_good: RefCell::new(BTreeMap::new()),
            next_body_arena: Cell::new(0),
            compiler_sessions: RefCell::new(BTreeMap::new()),
            #[cfg(test)]
            root_analysis_runs: Cell::new(0),
        }
    }

    /// Keep generated source documents available to editor requests without
    /// compiling them as user segments. The embedded standard library is one
    /// such document: `SourceBundle::distributed` already includes it.
    pub fn exclude_from_analysis(&mut self, path: PathBuf) {
        if self.analysis_exclusions.insert(path) {
            self.invalidate();
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

    pub fn roots(&self) -> &[PathBuf] {
        &self.roots
    }

    /// Install a full-document overlay, invalidating analysis only when the
    /// effective source bytes actually change.
    pub fn open(&mut self, path: PathBuf, text: String) -> bool {
        let changed = self.text(&path).as_deref() != Some(text.as_str());
        self.overlays.insert(path, text);
        if changed {
            self.revision += 1;
        }
        changed
    }

    pub fn close(&mut self, path: &Path) -> bool {
        let previous = self.overlays.remove(path);
        let changed = previous.as_deref().is_some_and(|previous| {
            std::fs::read_to_string(path).ok().as_deref() != Some(previous)
        });
        if changed {
            self.revision += 1;
        }
        changed
    }

    /// Apply optional text carried by didSave. An open full-text overlay is
    /// already authoritative, so a save without text does not invalidate it.
    pub fn save(&mut self, path: &Path, text: Option<&str>) -> bool {
        if let Some(text) = text {
            return self.open(path.to_path_buf(), text.to_string());
        }
        if self.overlays.contains_key(path) {
            return false;
        }
        self.revision += 1;
        true
    }

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
    fn project_groups(&self) -> Vec<(PathBuf, Vec<PathBuf>, BTreeMap<PathBuf, String>)> {
        let mut groups = Vec::new();
        let mut assigned = BTreeSet::new();
        // A workspace folder may contain several Grandiose projects (the
        // repository tutorial is one such layout). Resolve the nearest
        // manifest for every open source instead of assuming the workspace
        // folder itself is a package root.
        let mut project_roots = BTreeSet::new();
        for candidate in self
            .roots
            .iter()
            .chain(self.overlays.keys())
            .filter(|candidate| !self.analysis_exclusions.contains(*candidate))
        {
            if let Ok((project_root, _)) = grand::manifest::find_project(candidate) {
                project_roots.insert(project_root);
            }
        }
        for root in project_roots {
            let Ok((mut files, mut dependency_roots)) = self.resolve_project(&root) else {
                continue;
            };
            if files.is_empty() {
                continue;
            }
            files.sort();
            files.dedup();
            // A crate root is semantic, not lexicographic. Keep the manifest
            // entry first so SourceBundle's primary segment receives the root
            // module exception (`src/main.glorious` need not live in
            // `main/main.glorious`). Declared child modules remain sorted.
            if let Ok((project_root, manifest)) = grand::manifest::find_project(&root)
                && let Some(entry) = manifest.project.entry
                && let entry = project_root.join(entry)
                && let Some(index) = files.iter().position(|file| *file == entry)
            {
                let primary = files.remove(index);
                files.insert(0, primary);
            }
            for overlay in self
                .overlays
                .keys()
                .filter(|overlay| files.contains(overlay))
            {
                assigned.insert(overlay.clone());
            }
            dependency_roots.retain(|file, _| files.contains(file));
            groups.push((root, files, dependency_roots));
        }
        for file in self
            .overlays
            .keys()
            .filter(|file| {
                !assigned.contains(*file) && !self.analysis_exclusions.contains(*file)
            })
        {
            let root = file.parent().unwrap_or(file).to_path_buf();
            groups.push((root, vec![file.clone()], BTreeMap::new()));
        }
        groups
    }

    fn resolve_project(&self, root: &Path) -> Result<(Vec<PathBuf>, BTreeMap<PathBuf, String>)> {
        let (project_root, manifest) = grand::manifest::find_project(root)?;
        let lock = grand::lock::Lockfile::load(&project_root.join(grand::lock::LOCK_NAME))?;
        let options = grand::resolve::ResolveOptions {
            locked: false,
            update: None,
            offline: true,
        };
        let resolution =
            grand::resolve::resolve(&project_root, &manifest, lock.as_ref(), &options)?;
        let semantic_roots = grand::bundle::module_input_files(&resolution, None)?;
        let dependency_roots = semantic_roots
            .into_iter()
            .skip(1)
            .map(|(name, path)| (path, name))
            .collect::<BTreeMap<_, _>>();
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
        Ok((files, dependency_roots))
    }

    /// Cached per revision; cheap to call from every request handler.
    pub fn analyze(&self) -> Rc<Analysis> {
        if let Some((revision, analysis)) = self.cache.borrow().as_ref()
            && *revision == self.revision
        {
            return Rc::clone(analysis);
        }
        if let Some(delay) = std::env::var_os("GRAND_LSP_TEST_ANALYSIS_DELAY_MS")
            .and_then(|value| value.to_string_lossy().parse::<u64>().ok())
        {
            std::thread::sleep(std::time::Duration::from_millis(delay.min(5_000)));
        }
        let analysis = Rc::new(self.compute());
        *self.cache.borrow_mut() = Some((self.revision, Rc::clone(&analysis)));
        analysis
    }

    fn compute(&self) -> Analysis {
        let groups = self.project_groups();
        let active_roots = groups
            .iter()
            .map(|(root, _, _)| root.clone())
            .collect::<BTreeSet<_>>();
        self.root_cache
            .borrow_mut()
            .retain(|root, _| active_roots.contains(root));
        self.compiler_sessions
            .borrow_mut()
            .retain(|root, _| active_roots.contains(root));
        self.last_good
            .borrow_mut()
            .retain(|root, _| active_roots.contains(root));
        let mut diagnostics = self
            .overlays
            .keys()
            .filter(|file| self.analysis_exclusions.contains(*file))
            .cloned()
            .map(|file| (file, Vec::new()))
            .collect::<BTreeMap<PathBuf, Vec<FileDiagnostic>>>();
        let mut declarations = Vec::new();
        let mut std_declarations = Vec::new();
        let mut occurrences = Vec::new();
        let mut locals = Vec::new();
        let mut local_occurrences = Vec::new();
        let mut expression_types = Vec::new();
        let mut initial_error_declarations = Vec::new();
        let mut initial_error_occurrences = Vec::new();
        let mut semantic_prefixes = BTreeMap::new();
        let mut file_roots = BTreeMap::new();

        for (root, group_files, dependency_roots) in &groups {
            let mut segments = Vec::new();
            let mut group_sources = BTreeMap::new();
            for file in group_files {
                diagnostics.entry(file.clone()).or_default();
                file_roots.insert(file.clone(), root.clone());
                let Some(text) = self.text(file) else {
                    continue;
                };
                group_sources.insert(file.clone(), text.clone());
                let segment = Segment::new(file.display().to_string(), text);
                segments.push(if let Some(name) = dependency_roots.get(file) {
                    segment.with_package_root(name.clone())
                } else {
                    segment
                });
            }
            let Some(primary) = segments.first().cloned() else {
                continue;
            };
            let bundle = SourceBundle::distributed(primary, segments.into_iter().skip(1));
            let fallback = group_files.first().cloned().unwrap_or_default();
            let fingerprint = root_fingerprint(&group_sources, dependency_roots);
            let cached = self
                .root_cache
                .borrow()
                .get(root)
                .filter(|cached| cached.fingerprint == fingerprint)
                .cloned();
            if let Some(cached) = cached {
                diagnostics.extend(cached.diagnostics);
                initial_error_declarations.extend(cached.initial_error_declarations);
                initial_error_occurrences.extend(cached.initial_error_occurrences);
                if let Some(snapshot) = self.last_good.borrow().get(root) {
                    declarations.extend(snapshot.declarations.iter().cloned());
                    std_declarations.extend(snapshot.std_declarations.iter().cloned());
                    occurrences.extend(snapshot.occurrences.iter().cloned());
                    locals.extend(snapshot.locals.iter().cloned());
                    local_occurrences.extend(snapshot.local_occurrences.iter().cloned());
                    expression_types.extend(snapshot.expression_types.iter().cloned());
                    for (file, previous) in &snapshot.sources {
                        let current = group_sources.get(file).map(String::as_str).unwrap_or("");
                        semantic_prefixes
                            .insert(file.clone(), common_prefix_len(previous, current));
                    }
                }
                continue;
            }
            #[cfg(test)]
            self.root_analysis_runs
                .set(self.root_analysis_runs.get().saturating_add(1));
            let mut root_diagnostics = group_files
                .iter()
                .cloned()
                .map(|file| (file, Vec::new()))
                .collect::<BTreeMap<_, _>>();
            let mut root_initial_declarations = Vec::new();
            let mut root_initial_occurrences = Vec::new();
            let checked = self
                .compiler_sessions
                .borrow_mut()
                .entry(root.clone())
                .or_default()
                .compile_bundle_with_interfaces(
                    &bundle,
                    CompileOptions {
                        optimization_level: OptimizationLevel::O2,
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
                root_diagnostics
                    .entry(file)
                    .or_default()
                    .push(FileDiagnostic {
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
            let interfaces = match &checked {
                Ok(snapshot) => Ok(snapshot.interfaces.clone()),
                Err(_) => scan_interface_bundle(&bundle),
            }
            .map(|mut interfaces| {
                augment_effect_operations(
                    &bundle,
                    &interfaces.program,
                    &mut interfaces.user,
                    &mut interfaces.standard_library,
                );
                interfaces
            });
            if let Ok(compilation) = &checked
                && let Ok(interfaces) = &interfaces
            {
                let compiler = grandiose::semantic::semantic_snapshot(&bundle, &compilation.phases);
                let previous = self.last_good.borrow().get(root).cloned();
                let mut snapshot = semantic_snapshot(
                    interfaces.user.clone(),
                    interfaces.standard_library.clone(),
                    compiler,
                    previous.as_ref(),
                    &self.next_body_arena,
                );
                snapshot.sources = group_sources.clone();
                self.last_good.borrow_mut().insert(root.clone(), snapshot);
            }
            // Late compiler failures (for example unsupported bytecode
            // specialization) need not disable declaration navigation on the
            // very first editor load. Interface scanning uses the real parser
            // and module resolver, so its occurrences already exclude locals
            // and unresolved/ambiguous names. Never replace a last-good
            // semantic transaction with this narrower current-source view.
            if checked.is_err()
                && !self.last_good.borrow().contains_key(root)
                && let Ok(interfaces) = interfaces
            {
                let fallback = interface_snapshot(interfaces.user, interfaces.standard_library);
                root_initial_declarations.extend(fallback.declarations);
                root_initial_declarations.extend(fallback.std_declarations);
                root_initial_occurrences.extend(fallback.occurrences);
            }
            diagnostics.extend(root_diagnostics.clone());
            initial_error_declarations.extend(root_initial_declarations.iter().cloned());
            initial_error_occurrences.extend(root_initial_occurrences.iter().cloned());
            self.root_cache.borrow_mut().insert(
                root.clone(),
                CachedRootAnalysis {
                    fingerprint,
                    diagnostics: root_diagnostics,
                    initial_error_declarations: root_initial_declarations,
                    initial_error_occurrences: root_initial_occurrences,
                },
            );
            if let Some(snapshot) = self.last_good.borrow().get(root) {
                declarations.extend(snapshot.declarations.iter().cloned());
                std_declarations.extend(snapshot.std_declarations.iter().cloned());
                occurrences.extend(snapshot.occurrences.iter().cloned());
                locals.extend(snapshot.locals.iter().cloned());
                local_occurrences.extend(snapshot.local_occurrences.iter().cloned());
                expression_types.extend(snapshot.expression_types.iter().cloned());
                for (file, previous) in &snapshot.sources {
                    let current = group_sources.get(file).map(String::as_str).unwrap_or("");
                    semantic_prefixes.insert(file.clone(), common_prefix_len(previous, current));
                }
            }
        }
        std_declarations.sort_by(|left, right| left.identity.cmp(&right.identity));
        std_declarations.dedup_by(|left, right| left.identity == right.identity);
        initial_error_declarations.sort_by(|left, right| {
            (&left.identity, &left.file).cmp(&(&right.identity, &right.file))
        });
        initial_error_declarations
            .dedup_by(|left, right| left.identity == right.identity && left.file == right.file);
        Analysis {
            diagnostics,
            declarations,
            std_declarations,
            occurrences,
            locals,
            local_occurrences,
            expression_types,
            initial_error_declarations,
            initial_error_occurrences,
            semantic_prefixes,
            file_roots,
        }
    }
}

fn root_fingerprint(
    sources: &BTreeMap<PathBuf, String>,
    dependency_roots: &BTreeMap<PathBuf, String>,
) -> u64 {
    let mut fingerprint = std::collections::hash_map::DefaultHasher::new();
    for (path, source) in sources {
        path.hash(&mut fingerprint);
        source.hash(&mut fingerprint);
        dependency_roots.get(path).hash(&mut fingerprint);
    }
    fingerprint.finish()
}

/// Add effect operations to the editor interface without weakening the
/// compiler-owned effect identity. The compiler interface intentionally lists
/// top-level effects only; an operation is namespaced by that exact identity,
/// so equal operation spellings in different effects (or ordinary functions)
/// can never collide.
fn augment_effect_operations(
    bundle: &SourceBundle,
    program: &grandiose::ast::Program,
    user: &mut InterfaceSnapshot,
    standard: &mut InterfaceSnapshot,
) {
    let effects = user
        .declarations
        .iter()
        .chain(&standard.declarations)
        .filter(|declaration| declaration.kind == DeclarationKind::Effect)
        .cloned()
        .collect::<Vec<_>>();

    for effect in &program.effects {
        let Some(mapped) = bundle.map_span(effect.span) else {
            continue;
        };
        let Some(parent) = effects.iter().find(|declaration| {
            declaration.file == mapped.segment.name()
                && declaration.declaration_start_byte == mapped.span.start
                && declaration.name == effect.name
        }) else {
            continue;
        };
        let target = if parent.identity.starts_with("std:") {
            &mut *standard
        } else {
            &mut *user
        };
        for operation in &effect.operations {
            let Some(operation_mapped) = bundle.map_span(operation.span) else {
                continue;
            };
            let source = operation_mapped.segment.source();
            let start = operation_mapped.span.start.min(source.len());
            let end = operation_mapped.span.end.min(source.len());
            let name_range = lex_lossless(source.get(start..end).unwrap_or_default())
                .ok()
                .and_then(|tokens| {
                    tokens.into_iter().find(|token| {
                        token.kind == LosslessKind::Identifier
                            && token.text(&source[start..end]) == operation.name
                    })
                })
                .map_or((start, start), |token| {
                    (start + token.span.start, start + token.span.end)
                });
            let signature = source.get(start..end).unwrap_or_default().trim();
            target.declarations.push(InterfaceDeclaration {
                identity: format!("{}::operation:{}", parent.identity, operation.name),
                name: operation.name.clone(),
                kind: DeclarationKind::Callable,
                module: parent.module.clone(),
                visibility: parent.visibility.clone(),
                file: operation_mapped.segment.name().to_string(),
                line: source[..start]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1,
                declaration_start_byte: start,
                declaration_end_byte: end,
                name_start_byte: name_range.0,
                name_end_byte: name_range.1,
                signature: (!signature.is_empty()).then(|| signature.to_string()),
                docs: None,
            });
        }
    }

    let effect_identity = |file: &str, start: usize, end: usize| {
        user.occurrences
            .iter()
            .chain(&standard.occurrences)
            .find(|occurrence| {
                occurrence.file == file
                    && occurrence.start_byte == start
                    && occurrence.end_byte == end
            })
            .map(|occurrence| occurrence.identity.clone())
    };
    let mut operation_occurrences = Vec::new();
    for path in &program.effect_paths {
        let effect_span = match &path.effect.kind {
            grandiose::ast::TypeSyntaxKind::Path(segments) => segments
                .first()
                .zip(segments.last())
                .map(|(first, last)| first.span.join(last.span)),
            grandiose::ast::TypeSyntaxKind::Application { constructor, .. } => {
                match &constructor.kind {
                    grandiose::ast::TypeSyntaxKind::Path(segments) => segments
                        .first()
                        .zip(segments.last())
                        .map(|(first, last)| first.span.join(last.span)),
                    _ => None,
                }
            }
            _ => None,
        };
        let (Some(effect_mapped), Some(site_mapped)) = (
            effect_span.and_then(|span| bundle.map_span(span)),
            bundle.map_span(path.site),
        ) else {
            continue;
        };
        if effect_mapped.segment.name() != site_mapped.segment.name() {
            continue;
        }
        let Some(parent_identity) = effect_identity(
            effect_mapped.segment.name(),
            effect_mapped.span.start,
            effect_mapped.span.end,
        ) else {
            continue;
        };
        let source = site_mapped.segment.source();
        let tail_start = effect_mapped.span.end.min(source.len());
        let tail_end = site_mapped.span.end.min(source.len());
        let tail = source.get(tail_start..tail_end).unwrap_or_default();
        let Some(operation) = lex_lossless(tail).ok().and_then(|tokens| {
            let mut after_separator = false;
            tokens.into_iter().find(|token| {
                if token.kind == LosslessKind::Punctuation && token.text(tail) == "::" {
                    after_separator = true;
                    return false;
                }
                after_separator && token.kind == LosslessKind::Identifier
            })
        }) else {
            continue;
        };
        let name = operation.text(tail);
        let identity = format!("{parent_identity}::operation:{name}");
        let occurrence = InterfaceOccurrence {
            identity: identity.clone(),
            file: site_mapped.segment.name().to_string(),
            start_byte: tail_start + operation.span.start,
            end_byte: tail_start + operation.span.end,
        };
        operation_occurrences.push((parent_identity.starts_with("std:"), occurrence));
    }
    for (is_standard, occurrence) in operation_occurrences {
        if is_standard {
            standard.occurrences.push(occurrence);
        } else {
            user.occurrences.push(occurrence);
        }
    }
}

fn interface_snapshot(user: InterfaceSnapshot, standard: InterfaceSnapshot) -> RootSnapshot {
    let convert = |interface: InterfaceDeclaration| SemanticDeclaration {
        file: PathBuf::from(&interface.file),
        interface,
    };
    let declarations = user
        .declarations
        .into_iter()
        .map(convert)
        .collect::<Vec<_>>();
    let std_declarations = standard
        .declarations
        .into_iter()
        .map(convert)
        .collect::<Vec<_>>();
    let mut occurrences = declarations
        .iter()
        .map(|declaration| SemanticOccurrence {
            identity: declaration.identity.clone(),
            file: declaration.file.clone(),
            start_byte: declaration.name_start_byte,
            end_byte: declaration.name_end_byte,
            definition: true,
        })
        .collect::<Vec<_>>();
    occurrences.extend(
        user.occurrences
            .into_iter()
            .chain(standard.occurrences)
            .map(|occurrence| SemanticOccurrence {
                identity: occurrence.identity,
                file: occurrence.file.into(),
                start_byte: occurrence.start_byte,
                end_byte: occurrence.end_byte,
                definition: false,
            }),
    );
    RootSnapshot {
        declarations,
        std_declarations,
        occurrences,
        ..RootSnapshot::default()
    }
}

fn common_prefix_len(left: &str, right: &str) -> usize {
    left.bytes()
        .zip(right.bytes())
        .take_while(|(left, right)| left == right)
        .count()
}

fn semantic_snapshot(
    user: InterfaceSnapshot,
    standard: InterfaceSnapshot,
    compiler: CompilerSemanticSnapshot,
    previous: Option<&RootSnapshot>,
    next_body_arena: &Cell<u64>,
) -> RootSnapshot {
    let body_arenas = retain_body_arenas(&compiler, previous, next_body_arena);
    let interface = interface_snapshot(user, standard);
    let declarations = interface.declarations;
    let std_declarations = interface.std_declarations;
    let mut occurrences = interface.occurrences;
    occurrences.sort_by(|left, right| {
        (&left.file, left.start_byte, left.end_byte).cmp(&(
            &right.file,
            right.start_byte,
            right.end_byte,
        ))
    });
    let locals = compiler
        .locals
        .into_iter()
        .map(|local| Local {
            identity: local.identity,
            name: local.name,
            file: local.file.into(),
            definition_start_byte: local.definition_start_byte,
            definition_end_byte: local.definition_end_byte,
            scope_start_byte: local.scope_start_byte,
            scope_end_byte: local.scope_end_byte,
            inferred_type: local.inferred_type,
        })
        .collect();
    let local_occurrences = compiler
        .occurrences
        .into_iter()
        .map(|occurrence| SemanticOccurrence {
            identity: occurrence.identity,
            file: occurrence.file.into(),
            start_byte: occurrence.start_byte,
            end_byte: occurrence.end_byte,
            definition: occurrence.definition,
        })
        .collect();
    let expression_types = compiler
        .expressions
        .into_iter()
        .map(|expression| SemanticExpression {
            file: expression.file.into(),
            start_byte: expression.start_byte,
            end_byte: expression.end_byte,
            inferred_type: expression.inferred_type,
        })
        .collect();
    RootSnapshot {
        declarations,
        std_declarations,
        occurrences,
        locals,
        local_occurrences,
        expression_types,
        sources: BTreeMap::new(),
        body_arenas,
    }
}

fn retain_body_arenas(
    compiler: &CompilerSemanticSnapshot,
    previous: Option<&RootSnapshot>,
    next_body_arena: &Cell<u64>,
) -> BTreeMap<String, BodyArena> {
    compiler
        .bodies
        .iter()
        .map(|body| {
            let retained = previous
                .and_then(|snapshot| snapshot.body_arenas.get(&body.identity))
                .filter(|arena| arena.semantic.source_fingerprint == body.source_fingerprint);
            if let Some(arena) = retained
                && arena.semantic.file == body.file
                && arena.semantic.start_byte == body.start_byte
                && arena.semantic.end_byte == body.end_byte
            {
                return (body.identity.clone(), arena.clone());
            }
            let generation = retained.map_or_else(
                || {
                    let generation = next_body_arena.get();
                    next_body_arena.set(generation.saturating_add(1));
                    generation
                },
                |arena| arena.generation,
            );
            (
                body.identity.clone(),
                BodyArena {
                    generation,
                    semantic: Rc::new(body.clone()),
                },
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn compiler_body(identity: &str, fingerprint: u64, start: usize) -> CompilerSemanticSnapshot {
        CompilerSemanticSnapshot {
            bodies: vec![grandiose::semantic::SemanticBodySnapshot {
                identity: identity.into(),
                file: "main.glorious".into(),
                start_byte: start,
                end_byte: start + 10,
                source_fingerprint: fingerprint,
                locals: vec![],
                occurrences: vec![],
                expressions: vec![],
            }],
            ..CompilerSemanticSnapshot::default()
        }
    }

    #[test]
    fn body_arenas_reuse_unchanged_inference_rebase_spans_and_invalidate_changes() {
        let next = Cell::new(0);
        let first = retain_body_arenas(&compiler_body("body:main", 7, 10), None, &next);
        let first_generation = first["body:main"].generation;
        let previous = RootSnapshot {
            body_arenas: first,
            ..RootSnapshot::default()
        };
        let unchanged =
            retain_body_arenas(&compiler_body("body:main", 7, 10), Some(&previous), &next);
        assert!(Rc::ptr_eq(
            &unchanged["body:main"].semantic,
            &previous.body_arenas["body:main"].semantic,
        ));
        let shifted =
            retain_body_arenas(&compiler_body("body:main", 7, 40), Some(&previous), &next);
        assert_eq!(shifted["body:main"].generation, first_generation);
        assert_eq!(shifted["body:main"].semantic.start_byte, 40);
        let previous = RootSnapshot {
            body_arenas: shifted,
            ..RootSnapshot::default()
        };
        let changed =
            retain_body_arenas(&compiler_body("body:main", 8, 40), Some(&previous), &next);
        assert_ne!(changed["body:main"].generation, first_generation);
    }

    #[test]
    fn std_index_contains_prelude_names() {
        let bundle =
            SourceBundle::distributed(Segment::new("main.glorious", "main() -> i64 { 0 }"), []);
        let standard =
            grandiose::interface::scan_interfaces(&bundle, InterfaceSelection::StandardLibrary)
                .unwrap();
        let names: Vec<&str> = standard.iter().map(|d| d.name.as_str()).collect();
        assert!(names.contains(&"if"), "std scan missing `if`: {names:?}");
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
        let user = scan_interface_snapshot(&bundle, InterfaceSelection::User).unwrap();
        let standard =
            scan_interface_snapshot(&bundle, InterfaceSelection::StandardLibrary).unwrap();
        let snapshot = semantic_snapshot(
            user,
            standard,
            CompilerSemanticSnapshot::default(),
            None,
            &Cell::new(0),
        );
        let helper_occurrences = snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == "user:value:helper")
            .collect::<Vec<_>>();
        assert_eq!(helper_occurrences.len(), 1);
        assert!(helper_occurrences[0].definition);
    }

    #[test]
    fn compiler_occurrences_distinguish_equal_names_in_sibling_modules() {
        let root = "mod left; mod right;\n\
                    use crate::left::answer as left_answer;\n\
                    use crate::right::answer as right_answer;\n\
                    probe() -> i64 { left_answer() + right_answer() }\n\
                    main() -> { () }";
        let bundle = SourceBundle::distributed(
            Segment::new("/work/src/main.glorious", root),
            [
                Segment::new("/work/src/left/left.glorious", "pub answer() -> i64 { 20 }"),
                Segment::new(
                    "/work/src/right/right.glorious",
                    "pub answer() -> i64 { 22 }",
                ),
            ],
        );
        let user = scan_interface_snapshot(&bundle, InterfaceSelection::User).unwrap();
        let standard =
            scan_interface_snapshot(&bundle, InterfaceSelection::StandardLibrary).unwrap();
        let snapshot = semantic_snapshot(
            user,
            standard,
            CompilerSemanticSnapshot::default(),
            None,
            &Cell::new(0),
        );
        let left = snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == "user:value:left::answer")
            .collect::<Vec<_>>();
        let right = snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == "user:value:right::answer")
            .collect::<Vec<_>>();
        assert!(!left.is_empty(), "{:#?}", snapshot.occurrences);
        assert!(!right.is_empty(), "{:#?}", snapshot.occurrences);
        assert!(left.iter().any(|occurrence| {
            !occurrence.definition && occurrence.file.ends_with("main.glorious")
        }));
        assert!(right.iter().any(|occurrence| {
            !occurrence.definition && occurrence.file.ends_with("main.glorious")
        }));
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
                    "[project]\nname = \"{}\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
                    root.file_name().unwrap().to_string_lossy()
                ),
            )
            .unwrap();
        }
        let first_main = first.join("src/main.glorious");
        let second_main = second.join("src/main.glorious");
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
        assert_eq!(workspace.root_analysis_runs.get(), 2);

        let original = std::fs::read_to_string(&first_main).unwrap();
        assert!(!workspace.open(first_main.clone(), original));
        assert!(!workspace.save(&first_main, None));
        assert_eq!(workspace.root_analysis_runs.get(), 2);

        assert!(workspace.open(
            first_main.clone(),
            "shared() -> () { () }\nmain() -> () {\n    shared()\n}\n".into(),
        ));
        let analysis = workspace.analyze();
        assert!(analysis.diagnostics[&first_main].is_empty());
        assert_eq!(
            workspace.root_analysis_runs.get(),
            3,
            "editing one root must not recompile its sibling"
        );
    }

    #[test]
    fn manifest_entry_precedes_lexically_earlier_module_files() {
        let temporary = tempfile::TempDir::new().unwrap();
        let root = temporary.path().join("app");
        std::fs::create_dir_all(root.join("src/aaa")).unwrap();
        std::fs::write(
            root.join("grandiose.toml"),
            "[project]\nname = \"app\"\nversion = \"0.1.0\"\nentry = \"src/main.glorious\"\n",
        )
        .unwrap();
        let main = root.join("src/main.glorious");
        let module = root.join("src/aaa/aaa.glorious");
        std::fs::write(&main, "mod aaa; main() -> () { () }").unwrap();
        std::fs::write(&module, "pub helper() -> () { () }").unwrap();

        let workspace = Workspace::new(root);
        let groups = workspace.project_groups();
        assert_eq!(groups[0].1[0], main);
        assert!(groups[0].1.contains(&module));
    }

    #[test]
    fn materialized_standard_library_is_not_compiled_twice() {
        let temporary = tempfile::TempDir::new().unwrap();
        let standard_library = temporary.path().join("distributed_std.glorious");
        let source = grandiose::source_bundle::DISTRIBUTED_STANDARD_LIBRARY_SOURCE;
        std::fs::write(&standard_library, source).unwrap();

        let mut workspace = Workspace::new(temporary.path().to_path_buf());
        workspace.exclude_from_analysis(standard_library.clone());
        workspace.open(standard_library.clone(), source.to_string());

        assert!(workspace.project_groups().is_empty());
        let analysis = workspace.analyze();
        assert!(
            analysis
                .diagnostics
                .get(&standard_library)
                .is_some_and(Vec::is_empty)
        );
    }

    #[test]
    fn manifest_dependencies_are_marked_as_package_roots_for_navigation() {
        let temporary = tempfile::TempDir::new().unwrap();
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
        let main = app.join("src/main.glorious");
        std::fs::write(
            &main,
            "use math_lib::answer; probe() -> i64 { answer() } main() -> () { () }",
        )
        .unwrap();
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

        let workspace = Workspace::new(app);
        let analysis = workspace.analyze();
        assert!(
            analysis.diagnostics[&main].is_empty(),
            "{:#?}",
            analysis.diagnostics
        );
        let declaration = analysis
            .declarations
            .iter()
            .find(|declaration| declaration.file == dependency_root && declaration.name == "answer")
            .expect("dependency declaration missing");
        assert!(
            analysis
                .references(&declaration.identity)
                .any(|occurrence| occurrence.file == main && !occurrence.definition)
        );
    }
}
