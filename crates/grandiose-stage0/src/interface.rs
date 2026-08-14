//! Canonical declaration interfaces.
//!
//! This is the boundary between structural source knowledge and body-demand
//! work. It indexes all declarations, captures namespace/visibility identity,
//! rejects ambiguities deterministically, and fingerprints only header facts.
//! A body edit can therefore retain the same public interface and leave a
//! downstream package green once query invalidation is connected.

use std::{
    collections::{BTreeMap, HashMap},
    sync::Mutex,
};

use crate::{
    header::{HeaderParse, ParsedHeader},
    identity::{DefKey, Digest, FileKey, ModuleKey, PackageKey},
    request::CompilerBuildIdentity,
    scanner::{DeclarationKind, DeclarationScan, TokenRange},
    source::{LexedFile, Span},
};

#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum DefinitionNamespace {
    Type,
    Value,
    Trait,
    Effect,
    Module,
    Operator,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub key: DefKey,
    pub kind: DeclarationKind,
    pub namespace: Option<DefinitionNamespace>,
    pub name: Option<String>,
    pub public: bool,
    pub module: ModuleKey,
    pub span: Span,
    pub header: TokenRange,
    pub body: Option<TokenRange>,
    /// Frozen request capability for a host import, if this definition is
    /// imported from the embedding host rather than defined by source.
    pub host_capability: Option<String>,
    pub header_fingerprint: Digest,
    /// Function bodies do not affect public interface identity, but a public
    /// constant's initializer is an exported semantic value and must.
    pub constant_value_fingerprint: Option<Digest>,
    /// Structured header syntax is frozen with the declaration interface.
    /// This lets later semantic queries elaborate the same signatures without
    /// reparsing source or touching a function body.
    pub syntax: HeaderParse,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InterfaceDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug)]
pub struct PackageInterface {
    pub package: PackageKey,
    pub module: ModuleKey,
    pub definitions: Vec<Definition>,
    /// Only exported facts participate in this fingerprint. Private body and
    /// private declaration changes do not cause a dependent package rebuild.
    pub public_fingerprint: Digest,
}

#[derive(Clone, Debug)]
pub struct InterfaceSet {
    pub interface: PackageInterface,
    pub diagnostics: Vec<InterfaceDiagnostic>,
}

/// A content-validated database-lifetime cache for frozen declaration
/// interfaces.  This is deliberately narrower than a module graph cache: a
/// child revision must still rescan its supplied source world to discover the
/// exact module topology, while an unchanged source/module input may reuse its
/// immutable header product.
///
/// The key contains every identity which makes source headers meaningful. In
/// particular, a stable logical file name alone is never sufficient: replacing
/// its bytes, changing its owning module path (as with an inline module), or
/// changing the compiler's interface schema all force recollection.
#[derive(Debug, Default)]
pub struct InterfaceCache {
    entries: Mutex<HashMap<InterfaceCacheKey, InterfaceSet>>,
    stats: Mutex<InterfaceCacheStats>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct InterfaceCacheStats {
    pub hits: u64,
    pub misses: u64,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct InterfaceCacheKey {
    file: FileKey,
    source: Digest,
    package: PackageKey,
    module_path: String,
    interface_context: Digest,
}

/// All immutable inputs observed by frozen interface collection. Grouping
/// these facts makes the cache boundary auditable: adding a new header input
/// requires adding it here and to `InterfaceCacheKey` rather than quietly
/// reaching into a revision from cache code.
pub(crate) struct InterfaceCacheInput<'a> {
    pub build: &'a CompilerBuildIdentity,
    pub package: &'a PackageKey,
    pub module_path: &'a str,
    pub file: FileKey,
    pub source_digest: Digest,
    pub lexed: &'a LexedFile,
    pub source: &'a str,
    pub scan: &'a DeclarationScan,
}

/// The narrow interface-collection authority consumed by module graph
/// construction. A direct cache commits each complete interface immediately;
/// a request transaction stages them until the enclosing request outcome is
/// known to be publishable.
pub(crate) trait InterfaceCollector {
    fn collect(&mut self, input: InterfaceCacheInput<'_>) -> InterfaceSet;
}

/// Request-local staging for frozen interface cache entries. Dropping this
/// value abandons every cache miss collected during the request, making a
/// failed/cancelled compilation unable to publish a partial cache fact.
#[derive(Debug)]
pub(crate) struct InterfaceCacheTransaction<'a> {
    cache: &'a InterfaceCache,
    staged: HashMap<InterfaceCacheKey, InterfaceSet>,
    hits: u64,
    misses: u64,
}

impl InterfaceCache {
    pub fn stats(&self) -> InterfaceCacheStats {
        *self
            .stats
            .lock()
            .expect("interface cache stats mutex poisoned")
    }

    pub(crate) fn transaction(&self) -> InterfaceCacheTransaction<'_> {
        InterfaceCacheTransaction {
            cache: self,
            staged: HashMap::new(),
            hits: 0,
            misses: 0,
        }
    }

    fn cache_key(input: &InterfaceCacheInput<'_>) -> InterfaceCacheKey {
        InterfaceCacheKey {
            file: input.file,
            source: input.source_digest,
            package: input.package.clone(),
            module_path: input.module_path.to_owned(),
            interface_context: interface_context_fingerprint(input.build),
        }
    }

    pub(crate) fn collect(&self, input: InterfaceCacheInput<'_>) -> InterfaceSet {
        let mut transaction = self.transaction();
        let interface = transaction.collect(input);
        transaction.commit();
        interface
    }
}

impl InterfaceCollector for InterfaceCache {
    fn collect(&mut self, input: InterfaceCacheInput<'_>) -> InterfaceSet {
        InterfaceCache::collect(self, input)
    }
}

impl InterfaceCacheTransaction<'_> {
    pub(crate) fn commit(self) {
        let mut entries = self
            .cache
            .entries
            .lock()
            .expect("interface cache mutex poisoned");
        let mut stats = self
            .cache
            .stats
            .lock()
            .expect("interface cache stats mutex poisoned");
        for (key, interface) in self.staged {
            entries.entry(key).or_insert(interface);
        }
        stats.hits += self.hits;
        stats.misses += self.misses;
    }
}

impl InterfaceCollector for InterfaceCacheTransaction<'_> {
    fn collect(&mut self, input: InterfaceCacheInput<'_>) -> InterfaceSet {
        let key = InterfaceCache::cache_key(&input);
        if let Some(interface) = self.staged.get(&key) {
            return interface.clone();
        }
        if let Some(interface) = self
            .cache
            .entries
            .lock()
            .expect("interface cache mutex poisoned")
            .get(&key)
            .cloned()
        {
            self.hits += 1;
            return interface;
        }
        let interface = InterfaceSet::collect(
            input.package.clone(),
            input.module_path,
            input.lexed,
            input.source,
            input.scan,
        );
        self.staged.insert(key, interface.clone());
        self.misses += 1;
        interface
    }
}

fn interface_context_fingerprint(build: &CompilerBuildIdentity) -> Digest {
    Digest::of_parts([
        b"grandiose-stage0-interface-cache-v1".as_slice(),
        build.compiler.as_bytes().as_slice(),
        &build.language_generation.to_le_bytes(),
        &build.query_generation.to_le_bytes(),
        &build.interface_generation.to_le_bytes(),
        &build.cache_generation.to_le_bytes(),
    ])
}

impl InterfaceSet {
    pub fn collect(
        package: PackageKey,
        module_path: impl Into<String>,
        lexed: &LexedFile,
        source: &str,
        scan: &DeclarationScan,
    ) -> Self {
        let module = ModuleKey {
            package: package.clone(),
            path: module_path.into(),
        };
        let mut definitions = vec![];
        let mut diagnostics = vec![];
        let mut occupied = BTreeMap::<(DefinitionNamespace, String), Span>::new();

        for (ordinal, shell) in scan.declarations.iter().enumerate() {
            let namespace = namespace(shell.kind);
            let name = shell.name.clone();
            if let (Some(namespace), Some(name)) = (namespace, &name)
                && namespace != DefinitionNamespace::Operator
                && let Some(previous) = occupied.insert((namespace, name.clone()), shell.span)
            {
                diagnostics.push(InterfaceDiagnostic {
                    code: "G3001",
                    span: shell.span,
                    message: format!(
                        "duplicate {namespace:?} definition `{name}`; the first declaration starts at byte {}",
                        previous.start
                    ),
                });
            }
            let fingerprint_range = match shell.kind {
                DeclarationKind::Struct
                | DeclarationKind::Enum
                | DeclarationKind::Trait
                | DeclarationKind::Effect
                | DeclarationKind::Implementation => {
                    shell.body.map_or(shell.header, |body| TokenRange {
                        start: shell.header.start,
                        end: body.end,
                    })
                }
                _ => shell.header,
            };
            let syntax = HeaderParse::parse(lexed, source, shell);
            let header_digest = match &syntax.header {
                ParsedHeader::Implementation(implementation) => implementation_header_fingerprint(
                    lexed,
                    source,
                    fingerprint_range,
                    implementation,
                ),
                _ => header_fingerprint(lexed, source, fingerprint_range),
            };
            let constant_value_fingerprint = (shell.kind == DeclarationKind::Constant)
                .then(|| {
                    shell
                        .body
                        .map(|range| header_fingerprint(lexed, source, range))
                })
                .flatten();
            diagnostics.extend(
                syntax
                    .diagnostics
                    .iter()
                    .map(|diagnostic| InterfaceDiagnostic {
                        code: diagnostic.code,
                        span: diagnostic.span,
                        message: diagnostic.message.to_owned(),
                    }),
            );
            if shell.kind == DeclarationKind::Constant && shell.body.is_none() {
                diagnostics.push(InterfaceDiagnostic {
                    code: "G3003",
                    span: shell.span,
                    message: "constant declaration has no initializer".into(),
                });
            }
            let key = definition_key(&module, shell.kind, name.as_deref(), header_digest, ordinal);
            definitions.push(Definition {
                key,
                kind: shell.kind,
                namespace,
                name,
                public: shell.visibility_public,
                module: module.clone(),
                span: shell.span,
                header: shell.header,
                body: shell.body,
                host_capability: shell.host_capability.clone(),
                header_fingerprint: header_digest,
                constant_value_fingerprint,
                syntax,
            });
        }
        let mut fixities = BTreeMap::new();
        for definition in &definitions {
            let ParsedHeader::Fixity(fixity) = &definition.syntax.header else {
                continue;
            };
            let key = (fixity.form.is_prefix(), fixity.operator.clone());
            if let Some(previous) = fixities.insert(key, definition.span) {
                diagnostics.push(InterfaceDiagnostic {
                    code: "G3002",
                    span: definition.span,
                    message: format!(
                        "conflicting fixity declaration for `{}`; the first declaration starts at byte {}",
                        fixity.operator, previous.start
                    ),
                });
            }
        }
        definitions.sort_by_key(|definition| {
            (
                definition.namespace,
                definition.name.clone(),
                definition.key,
            )
        });
        diagnostics.sort_by_key(|diagnostic| diagnostic.span.start);
        let public_fingerprint = public_fingerprint(&module, &definitions);
        Self {
            interface: PackageInterface {
                package,
                module,
                definitions,
                public_fingerprint,
            },
            diagnostics,
        }
    }
}

impl Definition {
    /// A callable signature is available without loading or parsing its body.
    pub fn callable_header(&self) -> Option<&crate::header::CallableHeader> {
        match &self.syntax.header {
            ParsedHeader::Function(header) => Some(header),
            _ => None,
        }
    }
}

fn namespace(kind: DeclarationKind) -> Option<DefinitionNamespace> {
    Some(match kind {
        DeclarationKind::Function | DeclarationKind::HostImport | DeclarationKind::Constant => {
            DefinitionNamespace::Value
        }
        DeclarationKind::Struct | DeclarationKind::Enum | DeclarationKind::TypeAlias => {
            DefinitionNamespace::Type
        }
        DeclarationKind::Trait => DefinitionNamespace::Trait,
        DeclarationKind::Effect => DefinitionNamespace::Effect,
        DeclarationKind::Module => DefinitionNamespace::Module,
        DeclarationKind::Fixity => DefinitionNamespace::Operator,
        DeclarationKind::Implementation | DeclarationKind::Import => return None,
    })
}

fn header_fingerprint(lexed: &LexedFile, source: &str, range: TokenRange) -> Digest {
    if range.start >= range.end {
        return Digest::of_bytes(b"");
    }
    let start = lexed.tokens[range.start].start as usize;
    let end = lexed.tokens[range.end - 1].end as usize;
    Digest::of_bytes(&source.as_bytes()[start..end])
}

/// An implementation's contract includes its head, associated definitions,
/// and method signatures, but never a method's executable body.  The body
/// ranges are retained for demand-driven compilation; excluding them here
/// prevents a private implementation-body edit from churning coherence
/// evidence, selected method identities, or downstream query keys.
fn implementation_header_fingerprint(
    lexed: &LexedFile,
    source: &str,
    range: TokenRange,
    implementation: &crate::header::ImplementationHeader,
) -> Digest {
    if range.start >= range.end {
        return Digest::of_bytes(b"");
    }
    let start = lexed.tokens[range.start].start as usize;
    let end = lexed.tokens[range.end - 1].end as usize;
    let mut cursor = start;
    let mut bytes = Vec::new();
    for body in implementation
        .methods
        .iter()
        .filter_map(|method| method.body)
    {
        let body_start = lexed.tokens[body.start].start as usize;
        let body_end = lexed.tokens[body.end - 1].end as usize;
        if body_start < cursor || body_end > end {
            // A malformed range cannot become a cache-key omission. Header
            // recovery already emitted the source diagnostic; retain the full
            // text here so the identity fails closed.
            return header_fingerprint(lexed, source, range);
        }
        bytes.extend_from_slice(&source.as_bytes()[cursor..body_start]);
        bytes.extend_from_slice(b"\0grandiose-stage0-method-body\0");
        cursor = body_end;
    }
    bytes.extend_from_slice(&source.as_bytes()[cursor..end]);
    Digest::of_bytes(&bytes)
}

fn definition_key(
    module: &ModuleKey,
    kind: DeclarationKind,
    name: Option<&str>,
    header: Digest,
    ordinal: usize,
) -> DefKey {
    let kind = [kind as u8];
    match name {
        Some(name) => DefKey(Digest::of_parts([
            b"grandiose-stage0-def-v1".as_slice(),
            module.package.0.as_bytes(),
            module.path.as_bytes(),
            kind.as_slice(),
            name.as_bytes(),
        ])),
        // Impl/import declarations do not have an ordinary named definition;
        // their header fingerprint gives an explicit syntax anchor until their
        // later semantic identity (impl head / use tree) is available.
        None => DefKey(Digest::of_parts([
            b"grandiose-stage0-anonymous-def-v1".as_slice(),
            module.package.0.as_bytes(),
            module.path.as_bytes(),
            kind.as_slice(),
            header.as_bytes().as_slice(),
            &(ordinal as u64).to_le_bytes(),
        ])),
    }
}

fn public_fingerprint(module: &ModuleKey, definitions: &[Definition]) -> Digest {
    let mut bytes = Vec::new();
    append(&mut bytes, b"grandiose-stage0-interface-v1");
    append(&mut bytes, module.package.0.as_bytes());
    append(&mut bytes, module.path.as_bytes());
    for definition in definitions.iter().filter(|definition| definition.public) {
        append(&mut bytes, &definition.key.0.as_bytes());
        append(&mut bytes, &definition.header_fingerprint.as_bytes());
        if let Some(value) = definition.constant_value_fingerprint {
            append(&mut bytes, &value.as_bytes());
        }
    }
    Digest::of_bytes(&bytes)
}

fn append(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    output.extend_from_slice(bytes);
}
