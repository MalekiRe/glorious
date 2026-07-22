//! Public interface extraction for build tools and editors.
//!
//! This runs the recovering parser and module/name resolver so identities,
//! visibility, and files are authoritative. It deliberately stops before body
//! type checking, ownership analysis, MIR construction, and bytecode lowering.

use serde::Serialize;

use crate::{
    ast::Program,
    diagnostic::Diagnostic,
    source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_NAME, SourceBundle},
    span::Span,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InterfaceSelection {
    User,
    StandardLibrary,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[serde(rename_all = "lowercase")]
pub enum DeclarationKind {
    Callable,
    Struct,
    Enum,
    Type,
    Effect,
    Trait,
    Impl,
    Global,
    Fixity,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct InterfaceDeclaration {
    /// Stable semantic identity within one compilation root. The identity is
    /// intentionally independent of source order and byte position so an
    /// editor can retain it across whitespace-only and body-only revisions.
    pub identity: String,
    pub name: String,
    pub kind: DeclarationKind,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub module: Option<String>,
    pub visibility: String,
    pub file: String,
    pub line: usize,
    /// Exact file-local byte range of the complete declaration.
    pub declaration_start_byte: usize,
    pub declaration_end_byte: usize,
    /// Exact file-local byte range of the declared name (or the impl head for
    /// an anonymous `impl` declaration).
    pub name_start_byte: usize,
    pub name_end_byte: usize,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub signature: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub docs: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct InterfaceOccurrence {
    pub identity: String,
    pub file: String,
    pub start_byte: usize,
    pub end_byte: usize,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct InterfaceSnapshot {
    pub declarations: Vec<InterfaceDeclaration>,
    /// Exact compiler-resolved top-level references. Definition name spans are
    /// already present on `declarations` and are not duplicated here.
    pub occurrences: Vec<InterfaceOccurrence>,
}

/// Both editor interface partitions plus the parsed program that produced
/// them. Keeping these together lets tooling pay for parsing and module/name
/// resolution once, and reuse the same syntax for auxiliary indexes such as
/// effect operations.
#[derive(Clone, Debug)]
pub struct InterfaceBundleSnapshot {
    pub user: InterfaceSnapshot,
    pub standard_library: InterfaceSnapshot,
    pub program: Program,
}

struct Collector<'a> {
    bundle: &'a SourceBundle,
    selection: InterfaceSelection,
    resolution: Option<&'a crate::modules::ModuleResolution>,
    declarations: Vec<(usize, InterfaceDeclaration)>,
}

impl<'a> Collector<'a> {
    fn accepts(&self, file: &str) -> bool {
        let standard = file == DISTRIBUTED_STANDARD_LIBRARY_NAME;
        match self.selection {
            InterfaceSelection::User => !standard,
            InterfaceSelection::StandardLibrary => standard,
        }
    }

    fn push(
        &mut self,
        name: String,
        kind: DeclarationKind,
        span: Span,
        signature_end: Option<usize>,
    ) {
        let Some(mapped) = self.bundle.map_span(span) else {
            return;
        };
        if !self.accepts(mapped.segment.name()) {
            return;
        }
        let source = mapped.segment.source();
        let start = mapped.span.start.min(source.len());
        let end = mapped.span.end.min(source.len());
        let signature_end = signature_end
            .map(|global| global.saturating_sub(mapped.segment.global_range().start))
            .unwrap_or(end)
            .clamp(start, end);
        let signature = source.get(start..signature_end).unwrap_or_default().trim();
        let (name_start_byte, name_end_byte) =
            declaration_name_range(source, start, signature_end.max(start), &name, kind);
        let line = source[..start]
            .bytes()
            .filter(|byte| *byte == b'\n')
            .count()
            + 1;
        let definition = self
            .resolution
            .and_then(|resolution| resolution.definition_at(span));
        let module = definition.and_then(|definition| {
            let path = &self.resolution.unwrap().module(definition.module).path;
            (!path.is_empty()).then(|| path.join("::"))
        });
        let visibility = definition.map_or(crate::ast::Visibility::Public, |definition| {
            if self.resolution.unwrap().is_public(definition) {
                crate::ast::Visibility::Public
            } else {
                crate::ast::Visibility::Private
            }
        });
        let visibility = match visibility {
            crate::ast::Visibility::Public => "public",
            crate::ast::Visibility::Private => "private",
        }
        .to_string();
        let identity_name = module
            .as_ref()
            .map_or_else(|| name.clone(), |module| format!("{module}::{name}"));
        self.declarations.push((
            span.start,
            InterfaceDeclaration {
                identity: declaration_identity(self.selection, kind, &identity_name),
                name,
                kind,
                module,
                visibility,
                file: mapped.segment.name().to_string(),
                line,
                declaration_start_byte: start,
                declaration_end_byte: end,
                name_start_byte,
                name_end_byte,
                signature: (!signature.is_empty()).then(|| signature.to_string()),
                docs: leading_docs(source, start),
            },
        ));
    }

    fn collect(mut self, program: &Program) -> Vec<InterfaceDeclaration> {
        for declaration in &program.type_aliases {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Type,
                declaration.span,
                None,
            );
        }
        for declaration in &program.effect_row_aliases {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Type,
                declaration.span,
                None,
            );
        }
        for declaration in &program.structs {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Struct,
                declaration.span,
                None,
            );
        }
        for declaration in &program.enums {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Enum,
                declaration.span,
                None,
            );
        }
        for declaration in &program.effects {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Effect,
                declaration.span,
                None,
            );
        }
        for declaration in &program.traits {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Trait,
                declaration.span,
                None,
            );
        }
        for declaration in &program.impls {
            let mapped = self.bundle.map_span(declaration.span);
            let name = mapped
                .and_then(|mapped| mapped.segment.source().get(mapped.span.range()))
                .and_then(|source| {
                    source
                        .split_once('{')
                        .map(|(head, _)| head.trim().to_string())
                })
                .unwrap_or_else(|| "impl".to_string());
            let signature_end = mapped.and_then(|mapped| {
                mapped
                    .segment
                    .source()
                    .get(mapped.span.range())?
                    .find('{')
                    .map(|offset| declaration.span.start + offset)
            });
            self.push(name, DeclarationKind::Impl, declaration.span, signature_end);
        }
        for declaration in &program.globals {
            let name = declaration.owner.as_ref().map_or_else(
                || declaration.name.clone(),
                |owner| format!("{owner}::{}", declaration.name),
            );
            self.push(name, DeclarationKind::Global, declaration.span, None);
        }
        for declaration in &program.fixities {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Fixity,
                declaration.span,
                None,
            );
        }
        for declaration in &program.functions {
            self.push(
                declaration.name.clone(),
                DeclarationKind::Callable,
                declaration.span,
                Some(declaration.body.span.start),
            );
        }
        self.declarations.sort_by_key(|(start, _)| *start);
        self.declarations
            .into_iter()
            .map(|(_, declaration)| declaration)
            .collect()
    }
}

fn declaration_namespace(kind: DeclarationKind) -> &'static str {
    match kind {
        DeclarationKind::Callable | DeclarationKind::Global => "value",
        DeclarationKind::Struct | DeclarationKind::Enum | DeclarationKind::Type => "type",
        DeclarationKind::Effect => "effect",
        DeclarationKind::Trait => "trait",
        DeclarationKind::Impl => "impl",
        DeclarationKind::Fixity => "fixity",
    }
}

fn declaration_identity(
    selection: InterfaceSelection,
    kind: DeclarationKind,
    name: &str,
) -> String {
    let origin = match selection {
        InterfaceSelection::User => "user",
        InterfaceSelection::StandardLibrary => "std",
    };
    format!("{origin}:{}:{name}", declaration_namespace(kind))
}

fn declaration_name_range(
    source: &str,
    declaration_start: usize,
    signature_end: usize,
    name: &str,
    kind: DeclarationKind,
) -> (usize, usize) {
    let search_end = signature_end.clamp(declaration_start, source.len());
    let head = source
        .get(declaration_start..search_end)
        .unwrap_or_default();
    if kind == DeclarationKind::Impl {
        let trimmed = head.len() - head.trim_start().len();
        return (
            declaration_start + trimmed,
            declaration_start + head.trim_end().len(),
        );
    }
    let leaf = name.rsplit("::").next().unwrap_or(name);
    if let Ok(tokens) = crate::lossless::lex_lossless(head)
        && let Some(token) = tokens.into_iter().find(|token| token.text(head) == leaf)
    {
        return (
            declaration_start + token.span.start,
            declaration_start + token.span.end,
        );
    }
    // A successfully parsed declaration should always have a matching token;
    // retain a valid exact subrange if a future declaration form violates that
    // invariant instead of manufacturing an out-of-file location.
    (declaration_start, declaration_start)
}

fn leading_docs(source: &str, offset: usize) -> Option<String> {
    let mut lines = Vec::new();
    for line in source[..offset].lines().rev() {
        let trimmed = line.trim();
        let Some(comment) = trimmed.strip_prefix("//") else {
            break;
        };
        lines.push(comment.trim().to_string());
    }
    lines.reverse();
    (!lines.is_empty()).then(|| lines.join("\n"))
}

fn definition_identity(
    bundle: &SourceBundle,
    resolution: &crate::modules::ModuleResolution,
    definition: &crate::modules::DefId,
) -> Option<(InterfaceSelection, String)> {
    let declaration = *resolution.definitions.get(definition)?;
    let mapped = bundle.map_span(declaration)?;
    let selection = if mapped.segment.name() == DISTRIBUTED_STANDARD_LIBRARY_NAME {
        InterfaceSelection::StandardLibrary
    } else {
        InterfaceSelection::User
    };
    let namespace = match definition.namespace {
        crate::modules::Namespace::Module => "module",
        crate::modules::Namespace::Type => "type",
        crate::modules::Namespace::Value => "value",
        crate::modules::Namespace::Trait => "trait",
        crate::modules::Namespace::Effect => "effect",
        crate::modules::Namespace::Fixity => "fixity",
    };
    let module = &resolution.module(definition.module).path;
    let qualified = if module.is_empty() {
        definition.name.clone()
    } else {
        format!("{}::{}", module.join("::"), definition.name)
    };
    let origin = match selection {
        InterfaceSelection::User => "user",
        InterfaceSelection::StandardLibrary => "std",
    };
    Some((selection, format!("{origin}:{namespace}:{qualified}")))
}

pub fn scan_interface_snapshot(
    bundle: &SourceBundle,
    selection: InterfaceSelection,
) -> Result<InterfaceSnapshot, Vec<Diagnostic>> {
    let program = crate::modules::parse_bundle(bundle)?;
    let resolved = crate::modules::resolve_program_for_interfaces(bundle, program.clone())?;
    Ok(interface_snapshot_from_resolved(
        bundle,
        &program,
        &resolved.resolution,
        selection,
    ))
}

/// Scan user and distributed-standard-library interfaces with one parse and
/// one resolver invocation.
pub fn scan_interface_bundle(
    bundle: &SourceBundle,
) -> Result<InterfaceBundleSnapshot, Vec<Diagnostic>> {
    let program = crate::modules::parse_bundle(bundle)?;
    let resolved = crate::modules::resolve_program_for_interfaces(bundle, program.clone())?;
    Ok(InterfaceBundleSnapshot {
        user: interface_snapshot_from_resolved(
            bundle,
            &program,
            &resolved.resolution,
            InterfaceSelection::User,
        ),
        standard_library: interface_snapshot_from_resolved(
            bundle,
            &program,
            &resolved.resolution,
            InterfaceSelection::StandardLibrary,
        ),
        program,
    })
}

fn interface_snapshot_from_resolved(
    bundle: &SourceBundle,
    program: &Program,
    resolution: &crate::modules::ModuleResolution,
    selection: InterfaceSelection,
) -> InterfaceSnapshot {
    let declarations = Collector {
        bundle,
        selection,
        resolution: Some(resolution),
        declarations: Vec::new(),
    }
    .collect(program);
    let occurrences = resolution
        .resolved_paths
        .iter()
        .filter_map(|(&(start, end), definition)| {
            let (definition_selection, identity) =
                definition_identity(bundle, resolution, definition)?;
            if definition_selection != selection {
                return None;
            }
            let mapped = bundle.map_span(Span::new(start, end))?;
            Some(InterfaceOccurrence {
                identity,
                file: mapped.segment.name().to_string(),
                start_byte: mapped.span.start,
                end_byte: mapped.span.end,
            })
        })
        .collect();
    InterfaceSnapshot {
        declarations,
        occurrences,
    }
}

pub fn scan_interfaces(
    bundle: &SourceBundle,
    selection: InterfaceSelection,
) -> Result<Vec<InterfaceDeclaration>, Vec<Diagnostic>> {
    scan_interface_snapshot(bundle, selection).map(|snapshot| snapshot.declarations)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_bundle::Segment;

    #[test]
    fn authoritative_scan_preserves_order_files_signatures_and_docs() {
        let bundle = SourceBundle::distributed(
            Segment::new(
                "primary.glorious",
                "// Public pair.\nstruct Pair { left: i64, right: i64 }\nmain() -> () { () }",
            ),
            [Segment::new(
                "extra.glorious",
                "// Computes an answer.\nanswer(value: i64) -> i64 { value }",
            )],
        );
        let declarations = scan_interfaces(&bundle, InterfaceSelection::User).unwrap();
        let pair = declarations
            .iter()
            .find(|declaration| declaration.name == "Pair")
            .unwrap();
        assert_eq!(pair.file, "primary.glorious");
        assert_eq!(pair.line, 2);
        assert_eq!(pair.docs.as_deref(), Some("Public pair."));
        assert!(pair.signature.as_deref().unwrap().contains("left: i64"));
        assert_eq!(
            &bundle.segments()[1].source()[pair.name_start_byte..pair.name_end_byte],
            "Pair"
        );
        assert_eq!(
            &bundle.segments()[1].source()[pair.declaration_start_byte..pair.declaration_end_byte],
            "struct Pair { left: i64, right: i64 }"
        );
        assert_eq!(pair.identity, "user:type:Pair");
        let answer = declarations
            .iter()
            .find(|declaration| declaration.name == "answer")
            .unwrap();
        assert_eq!(answer.file, "extra.glorious");
        assert_eq!(answer.docs.as_deref(), Some("Computes an answer."));
        assert_eq!(
            answer.signature.as_deref(),
            Some("answer(value: i64) -> i64")
        );
        assert_eq!(answer.identity, "user:value:answer");
        assert_eq!(
            answer.name_end_byte - answer.name_start_byte,
            "answer".len()
        );
    }

    #[test]
    fn standard_scan_excludes_user_declarations() {
        let bundle = SourceBundle::distributed(
            Segment::new("primary.glorious", "user_only() -> () { () }"),
            [],
        );
        let declarations = scan_interfaces(&bundle, InterfaceSelection::StandardLibrary).unwrap();
        assert!(!declarations.is_empty());
        assert!(declarations.iter().all(|declaration| {
            declaration.file == DISTRIBUTED_STANDARD_LIBRARY_NAME && declaration.name != "user_only"
        }));
        assert!(
            declarations
                .iter()
                .all(|declaration| declaration.identity.starts_with("std:"))
        );
    }

    #[test]
    fn combined_scan_returns_both_partitions_and_parsed_effects() {
        let bundle = SourceBundle::distributed(
            Segment::new(
                "primary.glorious",
                "effect Choice { choose(value: i64) -> i64 }\nmain() -> () { () }",
            ),
            [],
        );
        let snapshots = scan_interface_bundle(&bundle).unwrap();
        assert!(
            snapshots
                .user
                .declarations
                .iter()
                .any(|declaration| declaration.name == "Choice")
        );
        assert!(!snapshots.standard_library.declarations.is_empty());
        assert!(
            snapshots
                .program
                .effects
                .iter()
                .any(|effect| effect.name == "Choice")
        );
    }

    #[test]
    fn resolved_occurrences_are_module_qualified_and_exact() {
        let root_source =
            "mod values; use crate::values::answer; probe() -> i64 { answer() } main() -> { () }";
        let bundle = SourceBundle::distributed(
            Segment::new("/work/src/main.glorious", root_source),
            [Segment::new(
                "/work/src/values/values.glorious",
                "pub answer() -> i64 { 42 }",
            )],
        );
        let snapshot = scan_interface_snapshot(&bundle, InterfaceSelection::User).unwrap();
        assert!(snapshot.declarations.iter().any(|declaration| {
            declaration.identity == "user:value:values::answer"
                && declaration.module.as_deref() == Some("values")
        }));
        let occurrences = snapshot
            .occurrences
            .iter()
            .filter(|occurrence| occurrence.identity == "user:value:values::answer")
            .collect::<Vec<_>>();
        assert!(!occurrences.is_empty(), "{:#?}", snapshot.occurrences);
        for occurrence in occurrences {
            assert_eq!(
                &root_source[occurrence.start_byte..occurrence.end_byte],
                "answer"
            );
        }
    }

    #[test]
    fn unqualified_cross_file_occurrences_keep_their_definition_identity() {
        let source = "main() -> () { helper(0) }";
        let bundle = SourceBundle::distributed(
            Segment::new("/work/src/main.glorious", source),
            [Segment::new(
                "/work/src/helper.glorious",
                "helper(value: i64) -> () { () }",
            )],
        );
        let snapshot = scan_interface_snapshot(&bundle, InterfaceSelection::User).unwrap();
        let occurrence = snapshot
            .occurrences
            .iter()
            .find(|occurrence| occurrence.identity == "user:value:helper")
            .unwrap();
        assert_eq!(occurrence.file, "/work/src/main.glorious");
        assert_eq!(
            &source[occurrence.start_byte..occurrence.end_byte],
            "helper"
        );
    }
}
