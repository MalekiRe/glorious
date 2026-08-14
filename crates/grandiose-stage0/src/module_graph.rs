//! Package/module graph construction over immutable supplied source blobs.
//!
//! The compiler receives a source universe from `grand`/the request host. An
//! external `mod name;` declaration selects a logical file from that universe;
//! it never causes the semantic compiler to read a host path.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    identity::{FileKey, ModuleKey, PackageKey},
    interface::{
        InterfaceCache, InterfaceCacheInput, InterfaceCacheTransaction, InterfaceCollector,
        InterfaceSet,
    },
    request::{NormalizedInputWorld, SourceInput},
    scanner::{DeclarationKind, DeclarationScan},
    source::{LexedFile, Span},
};

#[derive(Clone, Debug)]
pub struct ModuleNode {
    pub key: ModuleKey,
    pub file: FileKey,
    pub logical_path: String,
    pub interface: InterfaceSet,
    pub children: Vec<ModuleKey>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ModuleDiagnostic {
    pub code: &'static str,
    pub span: Option<Span>,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct ModuleGraph {
    pub package: PackageKey,
    pub root: ModuleKey,
    pub modules: BTreeMap<ModuleKey, ModuleNode>,
    pub diagnostics: Vec<ModuleDiagnostic>,
}

impl ModuleGraph {
    pub fn build(world: &NormalizedInputWorld, package: &PackageKey) -> Self {
        let cache = InterfaceCache::default();
        Self::build_with_interface_cache(world, package, &cache)
    }

    /// Build this revision's exact module topology while validating every
    /// frozen module interface through the database-owned cache.  The graph is
    /// never reused wholesale: a revision may add/remove module declarations
    /// even when several individual source blobs remain unchanged.
    pub fn build_with_interface_cache(
        world: &NormalizedInputWorld,
        package: &PackageKey,
        cache: &InterfaceCache,
    ) -> Self {
        let mut transaction = cache.transaction();
        let graph = Self::build_with_interface_transaction(world, package, &mut transaction);
        transaction.commit();
        graph
    }

    /// Build a graph with request-local frozen-interface staging. The caller
    /// owns publication: dropping the transaction abandons all newly collected
    /// interfaces along with the rest of a failed request.
    pub(crate) fn build_with_interface_transaction(
        world: &NormalizedInputWorld,
        package: &PackageKey,
        cache: &mut InterfaceCacheTransaction<'_>,
    ) -> Self {
        Self::build_with_interface_collector(world, package, cache)
    }

    fn build_with_interface_collector<C: InterfaceCollector>(
        world: &NormalizedInputWorld,
        package: &PackageKey,
        cache: &mut C,
    ) -> Self {
        let supplied = world
            .sources
            .iter()
            .filter(|source| &source.package == package)
            .map(|source| (source.logical_path.as_str().to_owned(), source))
            .collect::<BTreeMap<_, _>>();
        let root = ModuleKey {
            package: package.clone(),
            path: "crate".into(),
        };
        let mut graph = Self {
            package: package.clone(),
            root: root.clone(),
            modules: BTreeMap::new(),
            diagnostics: vec![],
        };
        let mut claimed = BTreeSet::new();
        let mut visiting = BTreeSet::new();
        let roots = supplied
            .iter()
            .filter(|(path, _)| is_root_path(path))
            .map(|(path, _)| path.clone())
            .collect::<Vec<_>>();
        match roots.as_slice() {
            [] => graph.diagnostics.push(ModuleDiagnostic {
                code: "G3101",
                span: None,
                message: format!(
                    "package `{package:?}` has no `src/main.glorious` or `src/lib.glorious` root"
                ),
            }),
            [root_path] => graph.visit(
                world,
                cache,
                root_path,
                &root,
                &supplied,
                &mut claimed,
                &mut visiting,
            ),
            _ => graph.diagnostics.push(ModuleDiagnostic {
                code: "G3102",
                span: None,
                message: "package provides more than one root module".into(),
            }),
        }
        for (path, source) in &supplied {
            if !claimed.contains(path) {
                graph.diagnostics.push(ModuleDiagnostic {
                    code: "G3103",
                    span: None,
                    message: format!(
                        "supplied source `{path}` is not claimed by any external module declaration (file {:?})",
                        source.key
                    ),
                });
            }
        }
        graph.diagnostics.sort_by(|left, right| {
            (
                left.code,
                left.span.map(|span| (span.file, span.start, span.end)),
                &left.message,
            )
                .cmp(&(
                    right.code,
                    right.span.map(|span| (span.file, span.start, span.end)),
                    &right.message,
                ))
        });
        graph
    }

    #[allow(clippy::too_many_arguments)]
    fn visit<C: InterfaceCollector>(
        &mut self,
        world: &NormalizedInputWorld,
        cache: &mut C,
        path: &str,
        key: &ModuleKey,
        supplied: &BTreeMap<String, &SourceInput>,
        claimed: &mut BTreeSet<String>,
        visiting: &mut BTreeSet<ModuleKey>,
    ) {
        if self.modules.contains_key(key) {
            return;
        }
        if !visiting.insert(key.clone()) {
            self.diagnostics.push(ModuleDiagnostic {
                code: "G3106",
                span: None,
                message: format!("cyclic external module dependency reaches `{}`", key.path),
            });
            return;
        }
        let Some(source) = supplied.get(path).copied() else {
            self.diagnostics.push(ModuleDiagnostic {
                code: "G3104",
                span: None,
                message: format!("module `{}` requires unsupplied source `{path}`", key.path),
            });
            visiting.remove(key);
            return;
        };
        claimed.insert(path.to_owned());
        let text = std::str::from_utf8(&source.bytes).expect("normalized source is UTF-8");
        let lexed = LexedFile::lex(source.key, text);
        // Source products are authoritative.  Structural scanning can recover
        // around an invalid token, but a release compilation must still retain
        // the exact lexical failure rather than silently accepting the later
        // recovered outline.
        self.diagnostics
            .extend(lexed.diagnostics.iter().map(|diagnostic| ModuleDiagnostic {
                code: diagnostic.code,
                span: Some(diagnostic.span),
                message: diagnostic.message.into(),
            }));
        self.diagnostics
            .extend(
                lexed
                    .delimiters
                    .diagnostics
                    .iter()
                    .map(|diagnostic| ModuleDiagnostic {
                        code: diagnostic.code,
                        span: Some(diagnostic.span),
                        message: diagnostic.message.into(),
                    }),
            );
        let scan = DeclarationScan::scan(&lexed, text);
        let interface = cache.collect(InterfaceCacheInput {
            build: &world.build,
            package: &self.package,
            module_path: &key.path,
            file: source.key,
            source_digest: source.digest,
            lexed: &lexed,
            source: text,
            scan: &scan,
        });
        let external_modules = scan
            .declarations
            .iter()
            .filter(|shell| shell.kind == DeclarationKind::Module && shell.body.is_none())
            .collect::<Vec<_>>();
        let mut children = vec![];
        for declaration in external_modules {
            let Some(name) = &declaration.name else {
                self.diagnostics.push(ModuleDiagnostic {
                    code: "G3105",
                    span: Some(declaration.span),
                    message: "external module declaration has no name".into(),
                });
                continue;
            };
            let child_path = external_module_path(key, name);
            let child_key = ModuleKey {
                package: self.package.clone(),
                path: module_child_path(&key.path, name),
            };
            children.push(child_key.clone());
            self.visit(
                world,
                cache,
                &child_path,
                &child_key,
                supplied,
                claimed,
                visiting,
            );
        }
        let inline_modules = scan
            .declarations
            .iter()
            .filter(|shell| shell.kind == DeclarationKind::Module && shell.body.is_some())
            .collect::<Vec<_>>();
        for declaration in inline_modules {
            let Some(name) = &declaration.name else {
                self.diagnostics.push(ModuleDiagnostic {
                    code: "G3105",
                    span: Some(declaration.span),
                    message: "inline module declaration has no name".into(),
                });
                continue;
            };
            let body = declaration
                .body
                .expect("filtered inline modules have bodies");
            let child_key = ModuleKey {
                package: self.package.clone(),
                path: module_child_path(&key.path, name),
            };
            children.push(child_key.clone());
            let nested = DeclarationScan::scan_range(
                &lexed,
                text,
                crate::TokenRange {
                    start: body.start + 1,
                    end: body.end.saturating_sub(1),
                },
            );
            self.visit_inline(
                world, cache, path, &child_key, source, &lexed, text, nested, supplied, claimed,
                visiting,
            );
        }
        children.sort();
        children.dedup();
        self.modules.insert(
            key.clone(),
            ModuleNode {
                key: key.clone(),
                file: source.key,
                logical_path: path.to_owned(),
                interface,
                children,
            },
        );
        visiting.remove(key);
    }

    #[allow(clippy::too_many_arguments)]
    fn visit_inline<C: InterfaceCollector>(
        &mut self,
        world: &NormalizedInputWorld,
        cache: &mut C,
        path: &str,
        key: &ModuleKey,
        source: &SourceInput,
        lexed: &LexedFile,
        text: &str,
        scan: DeclarationScan,
        supplied: &BTreeMap<String, &SourceInput>,
        claimed: &mut BTreeSet<String>,
        visiting: &mut BTreeSet<ModuleKey>,
    ) {
        if self.modules.contains_key(key) {
            return;
        }
        if !visiting.insert(key.clone()) {
            self.diagnostics.push(ModuleDiagnostic {
                code: "G3106",
                span: None,
                message: format!("cyclic inline module dependency reaches `{}`", key.path),
            });
            return;
        }
        let interface = cache.collect(InterfaceCacheInput {
            build: &world.build,
            package: &self.package,
            module_path: &key.path,
            file: source.key,
            source_digest: source.digest,
            lexed,
            source: text,
            scan: &scan,
        });
        let mut children = vec![];
        for declaration in scan
            .declarations
            .iter()
            .filter(|shell| shell.kind == DeclarationKind::Module && shell.body.is_none())
        {
            let Some(name) = &declaration.name else {
                self.diagnostics.push(ModuleDiagnostic {
                    code: "G3105",
                    span: Some(declaration.span),
                    message: "external module declaration has no name".into(),
                });
                continue;
            };
            let child_key = ModuleKey {
                package: self.package.clone(),
                path: module_child_path(&key.path, name),
            };
            children.push(child_key.clone());
            self.visit(
                world,
                cache,
                &external_module_path(key, name),
                &child_key,
                supplied,
                claimed,
                visiting,
            );
        }
        for declaration in scan
            .declarations
            .iter()
            .filter(|shell| shell.kind == DeclarationKind::Module && shell.body.is_some())
        {
            let Some(name) = &declaration.name else {
                self.diagnostics.push(ModuleDiagnostic {
                    code: "G3105",
                    span: Some(declaration.span),
                    message: "inline module declaration has no name".into(),
                });
                continue;
            };
            let body = declaration
                .body
                .expect("filtered inline modules have bodies");
            let child_key = ModuleKey {
                package: self.package.clone(),
                path: module_child_path(&key.path, name),
            };
            children.push(child_key.clone());
            let nested = DeclarationScan::scan_range(
                lexed,
                text,
                crate::TokenRange {
                    start: body.start + 1,
                    end: body.end.saturating_sub(1),
                },
            );
            self.visit_inline(
                world, cache, path, &child_key, source, lexed, text, nested, supplied, claimed,
                visiting,
            );
        }
        children.sort();
        children.dedup();
        self.modules.insert(
            key.clone(),
            ModuleNode {
                key: key.clone(),
                file: source.key,
                logical_path: path.to_owned(),
                interface,
                children,
            },
        );
        visiting.remove(key);
    }
}

fn is_root_path(path: &str) -> bool {
    matches!(path, "src/main.glorious" | "src/lib.glorious")
}

fn external_module_path(parent: &ModuleKey, name: &str) -> String {
    let mut path = String::from("src");
    for segment in parent.path.split("::").skip(1) {
        path.push('/');
        path.push_str(segment);
    }
    format!("{path}/{name}/{name}.glorious")
}

fn module_child_path(parent: &str, child: &str) -> String {
    if parent == "crate" {
        format!("crate::{child}")
    } else {
        format!("{parent}::{child}")
    }
}
