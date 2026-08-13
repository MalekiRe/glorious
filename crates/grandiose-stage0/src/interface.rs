//! Canonical declaration interfaces.
//!
//! This is the boundary between structural source knowledge and body-demand
//! work. It indexes all declarations, captures namespace/visibility identity,
//! rejects ambiguities deterministically, and fingerprints only header facts.
//! A body edit can therefore retain the same public interface and leave a
//! downstream package green once query invalidation is connected.

use std::collections::BTreeMap;

use crate::{
    header::{HeaderParse, ParsedHeader},
    identity::{DefKey, Digest, ModuleKey, PackageKey},
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
            let header_digest = header_fingerprint(lexed, source, fingerprint_range);
            let constant_value_fingerprint = (shell.kind == DeclarationKind::Constant)
                .then(|| {
                    shell
                        .body
                        .map(|range| header_fingerprint(lexed, source, range))
                })
                .flatten();
            let syntax = HeaderParse::parse(lexed, source, shell);
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
        DeclarationKind::Function | DeclarationKind::Constant => DefinitionNamespace::Value,
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
