//! Declaration scanning through the compiler-owned Grandiose frontend.
//!
//! This is used only as a compatibility fallback when an external compiler
//! does not advertise `interfaces-json`. Keeping the fallback in-process makes
//! the semantic lexer and recovering parser the single syntax authority for
//! the formatter, language server, build tool, and compiler.

use std::path::Path;

use grandiose::{
    interface::{scan_interfaces, DeclarationKind as CompilerDeclarationKind, InterfaceSelection},
    source_bundle::{Segment, SourceBundle, DISTRIBUTED_STANDARD_LIBRARY_NAME},
};

use crate::contract::{Declaration, DeclarationKind};

pub fn scan(file: &Path, text: &str) -> Vec<Declaration> {
    let file_name = file.to_string_lossy().into_owned();
    // The synthetic empty standard segment must retain the standard role so
    // module graph construction treats `file` as the user package root rather
    // than mistaking the first segment for the primary source file.
    let bundle = SourceBundle::raw_with_trusted_standard_for_conformance(
        Segment::new(DISTRIBUTED_STANDARD_LIBRARY_NAME, ""),
        Segment::new(file_name, text),
        [],
    );
    scan_interfaces(&bundle, InterfaceSelection::User)
        .unwrap_or_default()
        .into_iter()
        .map(|declaration| Declaration {
            identity: Some(declaration.identity),
            name: declaration.name,
            kind: map_kind(declaration.kind),
            module: declaration.module,
            visibility: Some(declaration.visibility),
            file: declaration.file.into(),
            line: declaration.line,
            signature: declaration.signature,
            docs: declaration.docs,
        })
        .collect()
}

fn map_kind(kind: CompilerDeclarationKind) -> DeclarationKind {
    match kind {
        CompilerDeclarationKind::Callable => DeclarationKind::Callable,
        CompilerDeclarationKind::Struct => DeclarationKind::Struct,
        CompilerDeclarationKind::Enum => DeclarationKind::Enum,
        CompilerDeclarationKind::Type => DeclarationKind::Type,
        CompilerDeclarationKind::Effect => DeclarationKind::Effect,
        CompilerDeclarationKind::Trait => DeclarationKind::Trait,
        CompilerDeclarationKind::Impl => DeclarationKind::Impl,
        CompilerDeclarationKind::Global => DeclarationKind::Global,
        CompilerDeclarationKind::Fixity => DeclarationKind::Fixity,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn uses_the_semantic_frontend_for_declarations_docs_and_signatures() {
        let source = "\
// Public pair.\nstruct Pair { left: i32, right: i32 }\n\
// Computes an answer.\nanswer(value: i64) -> i64 { value }\n";
        let declarations = scan(Path::new("test.glorious"), source);
        assert_eq!(declarations.len(), 2);
        assert_eq!(declarations[0].name, "Pair");
        assert_eq!(declarations[0].docs.as_deref(), Some("Public pair."));
        assert_eq!(declarations[1].name, "answer");
        assert_eq!(
            declarations[1].signature.as_deref(),
            Some("answer(value: i64) -> i64")
        );
    }

    #[test]
    fn malformed_input_does_not_leak_partial_interfaces() {
        assert!(scan(Path::new("test.glorious"), "struct Broken {").is_empty());
    }

    #[test]
    fn module_qualified_identities_do_not_collapse_equal_leaf_names() {
        let declarations = scan(
            Path::new("test.glorious"),
            "mod left { pub same() -> () { () } }\n\
             mod right { pub same() -> () { () } }",
        );
        let identities = declarations
            .iter()
            .filter(|declaration| declaration.name == "same")
            .filter_map(|declaration| declaration.identity.as_deref())
            .collect::<Vec<_>>();
        assert_eq!(
            identities,
            ["user:value:left::same", "user:value:right::same"]
        );
    }
}
