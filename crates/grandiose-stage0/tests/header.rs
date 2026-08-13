use grandiose_stage0::{
    BodySyntax, DeclarationScan, Digest, EnumVariantPayloadHeader, FileKey, HeaderParse,
    HeaderType, LexedFile, LogicalPath, NominalLayoutHeader, PackageKey, ParsedHeader, Quantity,
};

#[test]
fn callable_headers_share_generic_and_type_grammar_without_parsing_the_body() {
    let package = PackageKey("header@0.1.0".into());
    let source = "pub fn map<T>(value: &mut Array<T>, fallback: T) -> Result<T, ()> { body }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/lib.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert_eq!(header.generics, ["T"]);
    assert!(matches!(
        header.parameters[0].ty,
        HeaderType::Reference { unique: true, .. }
    ));
    assert!(matches!(header.result, Some(HeaderType::Application(_, _))));
    assert_ne!(Digest::of_bytes(b""), lexed.source_fingerprint);
}

#[test]
fn callable_types_are_header_facts_with_tuple_parameters_and_result() {
    let package = PackageKey("header-callable-type@0.1.0".into());
    let source = "pub fn apply(value: (i64, Bool) -> Text) -> Text { value }";
    let file = FileKey::new(
        &package,
        LogicalPath::parse("src/main.glorious").unwrap().as_str(),
    );
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("function header was not parsed")
    };
    assert!(matches!(
        &header.parameters[0].ty,
        HeaderType::Callable {
            parameters,
            result
        } if parameters.len() == 2 && matches!(result.as_ref(), HeaderType::Path(path) if path == &["Text"])
    ));
}

#[test]
fn grouped_import_headers_expand_to_individual_bindings_without_body_parsing() {
    let package = PackageKey("header-import@0.1.0".into());
    let source = "use crate::math::{add as plus, zero};";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    let ParsedHeader::Import(import) = parsed.header else {
        panic!("expected import header")
    };
    assert!(parsed.diagnostics.is_empty(), "{:#?}", parsed.diagnostics);
    assert_eq!(
        import.bindings,
        vec![
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into(), "add".into()],
                alias: Some("plus".into()),
            },
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into(), "zero".into()],
                alias: None,
            },
        ]
    );
}

#[test]
fn nominal_layouts_are_parsed_as_interface_facts() {
    let package = PackageKey("header-nominal-layout@0.1.0".into());
    let source = "pub struct Pair<T> { left: T, right: i64 } pub enum Result<T> { Ok(T), Err { code: i64 }, Empty }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);

    let pair = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(pair.diagnostics.is_empty(), "{pair:#?}");
    let ParsedHeader::Nominal { generics, layout } = pair.header else {
        panic!("expected struct nominal header")
    };
    assert_eq!(generics, ["T"]);
    assert!(
        matches!(layout, NominalLayoutHeader::Struct(fields) if fields.len() == 2 && fields[0].name == "left")
    );

    let result = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(result.diagnostics.is_empty(), "{result:#?}");
    let ParsedHeader::Nominal { layout, .. } = result.header else {
        panic!("expected enum nominal header")
    };
    assert!(matches!(layout, NominalLayoutHeader::Enum(variants)
        if variants.len() == 3
        && matches!(variants[0].payload, EnumVariantPayloadHeader::Tuple(ref fields) if fields.len() == 1)
        && matches!(variants[1].payload, EnumVariantPayloadHeader::Struct(ref fields) if fields[0].name == "code")
        && matches!(variants[2].payload, EnumVariantPayloadHeader::Unit)));
}

#[test]
fn nominal_layouts_reject_duplicate_field_and_variant_identities() {
    let package = PackageKey("header-nominal-duplicates@0.1.0".into());
    let source = "struct Pair { value: i64, value: Bool } enum Choice { First, First(i64) }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let struct_header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(
        struct_header
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3230")
    );
    let enum_header = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(
        enum_header
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3231")
    );
}

#[test]
fn trait_impl_and_effect_headers_preserve_their_semantic_contracts() {
    let package = PackageKey("header-protocols@0.1.0".into());
    let source = r#"
        trait Display<T>: Marker<T> {
            type Output;
            type Effects: EffectRow;
            render(value: T) -> Text;
        }
        impl<T> !Display<T> for Pair<T> where T: Marker<T> {
            type Output = Text;
        }
        effect Console<T> {
            write(value: T);
            [0, *] read() -> T;
            fail(message: Text) -> !;
        }
    "#;
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);

    let trait_header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(trait_header.diagnostics.is_empty(), "{trait_header:#?}");
    let ParsedHeader::Trait(value) = trait_header.header else {
        panic!("expected trait header")
    };
    assert_eq!(value.generics, ["T"]);
    assert_eq!(value.supertraits.len(), 1);
    assert_eq!(value.associated_types.len(), 2);
    assert!(value.associated_types[1].effect_row);
    assert_eq!(value.methods[0].name, "render");

    let implementation = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(implementation.diagnostics.is_empty(), "{implementation:#?}");
    let ParsedHeader::Implementation(value) = implementation.header else {
        panic!("expected implementation header")
    };
    assert!(value.negative);
    assert_eq!(value.relation.path, ["Display"]);
    assert_eq!(value.where_bounds.len(), 1);
    assert_eq!(value.associated_types[0].name, "Output");

    let effect = HeaderParse::parse(&lexed, source, &scan.declarations[2]);
    assert!(effect.diagnostics.is_empty(), "{effect:#?}");
    let ParsedHeader::Effect(value) = effect.header else {
        panic!("expected effect header")
    };
    assert_eq!(value.operations.len(), 3);
    assert_eq!(value.operations[0].resumption, Quantity::ONCE);
    assert_eq!(value.operations[1].resumption, Quantity::UNRESTRICTED);
    assert!(value.operations[2].terminal);
}

#[test]
fn implementation_methods_retain_exact_body_ranges_for_later_elaboration() {
    let package = PackageKey("header-implementation-method-body@0.1.0".into());
    let source = "trait Convert { fn convert(value: i64) -> i64; } impl Convert for i64 { fn convert(value: i64) -> i64 { { let next = value + 1; next } } }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Implementation(implementation) = parsed.header else {
        panic!("expected implementation header")
    };
    let method = implementation
        .methods
        .first()
        .expect("implementation method");
    let body = method.body.expect("method body range");
    let syntax = BodySyntax::parse(&lexed, source, body);
    assert!(syntax.diagnostics.is_empty(), "{:#?}", syntax.diagnostics);
    assert!(!syntax.recovered);
    assert!(syntax.expressions.len() > 1, "method body was not retained");
}

#[test]
fn terminal_effect_operations_reject_resumption_quantities() {
    let package = PackageKey("header-terminal-effect@0.1.0".into());
    let source = "effect Abort { [0, 1] stop() -> !; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(
        header
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3250")
    );
}

#[test]
fn callable_headers_preserve_closed_effect_row_annotations() {
    let package = PackageKey("header-effect-row@0.1.0".into());
    let source = "fn read() -> i64 / { Console, Trace } { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(header.diagnostics.is_empty(), "{header:#?}");
    let ParsedHeader::Function(value) = header.header else {
        panic!("expected callable")
    };
    assert!(
        matches!(value.effects.effects.as_slice(), [HeaderType::Path(first), HeaderType::Path(second)] if first == &["Console"] && second == &["Trace"])
    );
}
