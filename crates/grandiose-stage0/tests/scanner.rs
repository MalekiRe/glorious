use grandiose_stage0::{
    DeclarationKind, Digest, FileKey, LexedFile, LogicalPath, PackageKey, TokenKind,
};

fn scan(source: &str) -> grandiose_stage0::DeclarationScan {
    let package = PackageKey("scan@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    assert_eq!(
        lexed.source_fingerprint,
        Digest::of_bytes(source.as_bytes())
    );
    grandiose_stage0::DeclarationScan::scan(&lexed, source)
}

#[test]
fn scanner_collects_all_top_level_declaration_families_without_parsing_bodies() {
    let scan = scan(
        "pub fn run<T>(value: T) { value }\n\
         struct Pair { first: i64, second: i64 }\n\
         enum Choice { Left, Right(i64) }\n\
         trait Show { fn show(self); }\n\
         impl Show for Pair { fn show(self) { () } }\n\
         effect Ask { ask() -> i64 }\n\
         type Word = i64; const answer: i64 = 42;\n\
         mod nested { fn hidden() { () } }\n\
         use crate::nested; infixl 5 +;",
    );
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    assert_eq!(scan.declarations.len(), 11);
    assert_eq!(scan.declarations[0].kind, DeclarationKind::Function);
    assert_eq!(scan.declarations[0].name.as_deref(), Some("run"));
    assert!(scan.declarations[0].visibility.is_public());
    assert_eq!(scan.declarations[4].kind, DeclarationKind::Implementation);
    assert!(scan.declarations[4].name.is_none());
    assert_eq!(scan.declarations[8].kind, DeclarationKind::Module);
    assert!(scan.declarations[8].body.is_some());
}

#[test]
fn scanner_rejects_an_unterminated_declaration_structurally() {
    let scan = scan("fn broken(");
    assert_eq!(scan.diagnostics[0].code, "G2002");
}

#[test]
fn scanner_preserves_array_headers_and_adjacent_associated_equalities() {
    for declaration in [
        "impl<T> Pick for T where T: Source<Item<i64>=i64> { fn pick() {} }",
        "impl<T> Pick for T where T: Source<Item=<T as Source>::Item> { fn pick() {} }",
        "impl<T> Pick for T where T: Source<Item<i64>=<T as Source>::Item> { fn pick() {} }",
        "fn inspect(value: &[i64; 4]) -> [i64; 4] { value }",
        "impl<T, N: usize> ArrayTrait for [T; N] { fn inspect() {} }",
    ] {
        let source = format!("{declaration} fn following() {{ 42 }}");
        let scanned = scan(&source);
        assert!(scanned.diagnostics.is_empty(), "{source}: {scanned:#?}");
        assert_eq!(scanned.declarations.len(), 2, "{source}: {scanned:#?}");
        assert!(scanned.declarations[0].body.is_some(), "{source}");
        assert_eq!(scanned.declarations[1].name.as_deref(), Some("following"));
    }
    let scanned = scan("type Fixed<T, N: usize> = [T; N]; fn following() { 42 }");
    assert!(scanned.diagnostics.is_empty(), "{scanned:#?}");
    assert_eq!(scanned.declarations.len(), 2);
    assert!(scanned.declarations[0].body.is_none());
}

#[test]
fn scanner_keeps_braced_callable_effect_rows_inside_type_alias_headers() {
    let scan = scan("effect Trace { note() -> i64; } type Callback = () -> i64 / {Trace}; pub fn main() -> i64 { 0 }");
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    assert_eq!(scan.declarations.len(), 3);
    assert_eq!(scan.declarations[1].kind, DeclarationKind::TypeAlias);
    assert!(
        scan.declarations[1].body.is_none(),
        "a type alias effect row must not be misclassified as a body"
    );
    assert_eq!(scan.declarations[2].kind, DeclarationKind::Function);
}

#[test]
fn scanner_keeps_constant_initializers_as_lazy_expression_body_ranges() {
    let package = PackageKey("scanner-const@0.1.0".into());
    let source = "const answer: i64 = 40 + 2;";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = grandiose_stage0::DeclarationScan::scan(&lexed, source);
    let constant = &scan.declarations[0];
    assert_eq!(constant.kind, grandiose_stage0::DeclarationKind::Constant);
    let body = constant.body.expect("constant initializer range");
    let parsed = grandiose_stage0::BodySyntax::parse_expression(&lexed, source, body);
    assert!(parsed.diagnostics.is_empty(), "{:#?}", parsed.diagnostics);
}

#[test]
fn scanner_keeps_top_level_value_initializer_calls_and_records_as_one_expression_range() {
    let package = PackageKey("scanner-let@0.1.0".into());
    let source = "let none = Result::Err { code: wrap(42) };";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = grandiose_stage0::DeclarationScan::scan(&lexed, source);
    let value = &scan.declarations[0];
    assert_eq!(value.kind, grandiose_stage0::DeclarationKind::ValueAlias);
    let body = value.body.expect("value initializer range");
    let parsed = grandiose_stage0::BodySyntax::parse_expression(&lexed, source, body);
    assert!(parsed.diagnostics.is_empty(), "{:#?}", parsed.diagnostics);
}

#[test]
fn scanner_reports_g3221_for_an_unterminated_top_level_value_initializer() {
    let package = PackageKey("scanner-let-terminator@0.1.0".into());
    let source = "let answer = add_one(41)";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = grandiose_stage0::DeclarationScan::scan(&lexed, source);
    assert!(
        scan.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3221"),
        "{:#?}",
        scan.diagnostics
    );
}

#[test]
fn lexer_distinguishes_byte_string_literals_and_accepts_raw_octet_escapes() {
    let package = PackageKey("scanner-bytes@0.1.0".into());
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, r#"let image = b"\x00\xff";"#);
    assert!(lexed.diagnostics.is_empty(), "{:#?}", lexed.diagnostics);
    assert!(
        lexed.tokens
            .iter()
            .any(|token| token.kind == TokenKind::ByteString)
    );
}
