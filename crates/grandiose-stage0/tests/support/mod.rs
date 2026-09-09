//! Phase fixtures use the ordinary source library, just as service requests do.
//! The import below is fixture source, not a compiler fallback for names.
#![allow(dead_code)]

use grandiose_stage0::{BodySyntax, DeclarationScan, DefKey, DefinitionIndex,
    ElaboratedInterface, FileKey, FixityTable, InterfaceSet, LexedFile, PackageInterface,
    PackageKey, ParsedHeader, TypedBody};

fn freeze_initializers(interface: &PackageInterface, source: &str, lexed: &LexedFile,
    index: &DefinitionIndex, signatures: &mut ElaboratedInterface, fixities: &FixityTable) {
    for declaration in &interface.definitions {
        if !matches!(declaration.syntax.header, ParsedHeader::ValueInitializer { .. }) { continue; }
        let Some(range) = declaration.body else { continue; };
        let syntax = BodySyntax::parse_expression_with_fixities(lexed, source, range, fixities);
        let value = TypedBody::elaborate_value_initializer(declaration, &syntax, index, signatures, fixities);
        signatures.freeze_typed_value_initializer(declaration.key, &value);
    }
}

fn standard() -> &'static (PackageInterface, ElaboratedInterface) {
    static STANDARD: std::sync::OnceLock<(PackageInterface, ElaboratedInterface)> = std::sync::OnceLock::new();
    STANDARD.get_or_init(|| {
        let package = PackageKey("std@0.1.0".into());
        let source = include_str!("../../../../stdlib/src/lib.glorious");
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let index = DefinitionIndex::from_interface(&interface);
        let mut signatures = ElaboratedInterface::elaborate(&interface);
        let fixities = FixityTable::for_module(&interface);
        freeze_initializers(&interface, source, &lexed, &index, &mut signatures, &fixities);
        assert!(signatures.diagnostics.is_empty(), "{:?}", signatures.diagnostics);
        (interface, signatures)
    })
}

pub fn frontend(package_name: &str, source: &str, function: &str) -> (DefKey, TypedBody, ElaboratedInterface) {
    let source = format!("use std::*; {source}");
    let package = PackageKey(package_name.into());
    let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), &source);
    let scan = DeclarationScan::scan(&lexed, &source);
    let interface = InterfaceSet::collect(package, "crate", &lexed, &source, &scan).interface;
    let (standard, standard_signatures) = standard();
    let index = DefinitionIndex::from_interfaces([&interface, standard]);
    let mut signatures = ElaboratedInterface::merge([
        ElaboratedInterface::elaborate_with_index(&interface, &index), standard_signatures.clone()]);
    let declarations = [&interface, standard].into_iter().flat_map(|interface| &interface.definitions)
        .filter_map(|definition| match &definition.syntax.header {
            ParsedHeader::Fixity(header) => Some((definition.key, header.clone())), _ => None,
        }).collect();
    let fixities = FixityTable::visible_in_module(&interface.module, &index, &declarations);
    freeze_initializers(&interface, &source, &lexed, &index, &mut signatures, &fixities);
    let definition = interface.definitions.iter().find(|definition| definition.name.as_deref() == Some(function))
        .expect("fixture function definition");
    let syntax = BodySyntax::parse_with_fixities(&lexed, &source, definition.body.expect("fixture body"), &fixities);
    let core = TypedBody::elaborate_with_fixities(definition, &syntax, &index, &signatures, &fixities);
    (definition.key, core, signatures)
}
