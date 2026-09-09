use grandiose_syntax::{DeclarationKind, DeclarationScan, Digest, FileKey, LexedFile,
    ModuleKey, PackageKey, Safety, TokenKind, Visibility};

#[test]
fn lossless_scanning_does_not_need_semantic_or_vm_dependencies() {
    let source = "pub unsafe fn read() { 42 }\nstruct Values { values: [i64; 4] }";
    let lexed = LexedFile::lex(FileKey::new(&PackageKey("syntax@1".into()), "src/lib.glorious"), source);
    assert!(lexed.diagnostics.is_empty());
    assert_eq!(lexed.source_fingerprint, Digest::of_bytes(source.as_bytes()));
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:?}", scan.diagnostics);
    assert_eq!(scan.declarations.len(), 2);
    assert_eq!(scan.declarations[0].kind, DeclarationKind::Function);
    assert_eq!(scan.declarations[0].safety, Safety::Unsafe);
    assert_eq!(grandiose_syntax::source::exact_scalar_literal_kind("42"), Some(TokenKind::Integer));
    assert_eq!(grandiose_syntax::source::exact_scalar_literal_kind("42 trailing"), None);
}

#[test]
fn scanning_and_resolution_share_the_same_lexical_authority() {
    let owner = ModuleKey { package: PackageKey("syntax@1".into()), path: "crate::inner".into() };
    let child = ModuleKey { path: "crate::inner::child".into(), ..owner.clone() };
    let sibling = ModuleKey { path: "crate::innerish".into(), ..owner.clone() };
    assert!(Visibility::Private.allows(&child, &owner));
    assert!(!Visibility::Private.allows(&sibling, &owner));
    assert!(Visibility::Crate.allows(&sibling, &owner));
}
