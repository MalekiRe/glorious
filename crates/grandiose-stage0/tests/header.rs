use grandiose_stage0::{
    BodySyntax, ConstKind, DeclarationScan, Digest, EnumVariantPayloadHeader, FileKey,
    HeaderGenericArgument, HeaderParse, HeaderType, LexedFile, LogicalPath, NominalLayoutHeader,
    PackageKey, ParsedHeader, Quantity,
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
fn headers_parse_higher_ranked_callable_lifetime_scopes() {
    let package = PackageKey("header-hrtb@0.1.0".into());
    let source = "pub fn use_callback(callback: for<'a> (&'a i64) -> &'a i64) { callback }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        &header.parameters[0].ty,
        HeaderType::Callable {
            lifetime_binders,
            parameters,
            result,
        } if lifetime_binders == &["'a"]
            && matches!(parameters.as_slice(), [HeaderType::Reference { lifetime: Some(name), .. }] if name == "'a")
            && matches!(result.as_ref(), HeaderType::Reference { lifetime: Some(name), .. } if name == "'a")
    ));
}

#[test]
fn nominal_headers_retain_structural_u32_arguments() {
    let package = PackageKey("header-structural-u32-argument@0.1.0".into());
    let source = "pub fn seven() -> Tag<7> { seven }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        header.result,
        Some(HeaderType::Application(_, arguments))
            if arguments == vec![HeaderGenericArgument::U32(7)]
    ));
}

#[test]
fn nominal_headers_retain_structural_quantity_arguments() {
    let package = PackageKey("header-structural-quantity-argument@0.1.0".into());
    let source =
        "pub fn bounded() -> Tag<[0, 1]> { bounded } pub fn open() -> Tag<[1, *]> { open }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);

    for (declaration, expected) in scan.declarations.iter().zip([
        Quantity::ZERO.branch_hull(Quantity::ONCE),
        Quantity::new(1, None).unwrap(),
    ]) {
        let parsed = HeaderParse::parse(&lexed, source, declaration);
        assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
        let ParsedHeader::Function(header) = parsed.header else {
            panic!("expected callable header")
        };
        assert!(matches!(
            header.result,
            Some(HeaderType::Application(_, arguments))
                if arguments == vec![HeaderGenericArgument::Quantity(expected)]
        ));
    }
}

#[test]
fn nominal_headers_normalize_structural_const_arithmetic() {
    let package = PackageKey("header-structural-const-arithmetic@0.1.0".into());
    let source = "pub fn tag() -> Tag<1 + 2 * 3> { tag } pub fn budget() -> Budget<[1 + 2, 2 * 4]> { budget }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);

    let first = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(first.diagnostics.is_empty(), "{first:#?}");
    let ParsedHeader::Function(first) = first.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        first.result,
        Some(HeaderType::Application(_, arguments))
            if arguments == vec![HeaderGenericArgument::U32(7)]
    ));

    let second = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(second.diagnostics.is_empty(), "{second:#?}");
    let ParsedHeader::Function(second) = second.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        second.result,
        Some(HeaderType::Application(_, arguments))
            if arguments == vec![HeaderGenericArgument::Quantity(Quantity::new(3, Some(8)).unwrap())]
    ));
}

#[test]
fn structural_const_arithmetic_reports_overflow_and_division_by_zero() {
    let package = PackageKey("header-structural-const-arithmetic-errors@0.1.0".into());
    let source = "pub fn overflow() -> Tag<4294967295 + 1> { overflow } pub fn zero() -> Tag<8 / 0> { zero }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let overflow = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(
        overflow
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3222"),
        "{overflow:#?}"
    );
    let zero = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(
        zero.diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3228"),
        "{zero:#?}"
    );
}

#[test]
fn callable_headers_retain_generic_kind_metadata() {
    let package = PackageKey("header-generic-kinds@0.1.0".into());
    let source = "pub fn relay<T, e: EffectRow>(value: T) -> i64 / { | e } { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert_eq!(header.generics, ["T", "e"]);
    assert!(!header.generics.is_effect_row("T"));
    assert!(header.generics.is_effect_row("e"));
}

#[test]
fn callable_headers_retain_structural_const_binder_kinds() {
    let package = PackageKey("header-const-generic-kinds@0.1.0".into());
    let source = "pub fn capacity<n: u32, budget: Quantity>() -> i64 { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert_eq!(header.generics, ["n", "budget"]);
    assert_eq!(header.generics.const_kind("n"), Some(ConstKind::U32));
    assert_eq!(
        header.generics.const_kind("budget"),
        Some(ConstKind::Quantity)
    );
}

#[test]
fn callable_headers_retain_lifetime_binder_spellings() {
    let package = PackageKey("header-lifetime-binders@0.1.0".into());
    let source = "pub fn borrow<'a, '_>(value: i64) -> i64 { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert_eq!(header.generics, ["'a", "'_"]);
    assert!(header.generics.is_lifetime("'a"));
    assert!(header.generics.is_lifetime("'_"));
}

#[test]
fn callable_headers_attach_lifetime_spellings_to_references() {
    let package = PackageKey("header-reference-lifetime@0.1.0".into());
    let source = "pub fn borrow<'a>(value: &'a i64, fallback: &i64) -> &'static i64 { value }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        &header.parameters[0].ty,
        HeaderType::Reference { lifetime: Some(lifetime), .. } if lifetime == "'a"
    ));
    assert!(matches!(
        &header.parameters[1].ty,
        HeaderType::Reference { lifetime: None, .. }
    ));
    assert!(matches!(
        header.result,
        Some(HeaderType::Reference { lifetime: Some(lifetime), .. }) if lifetime == "'static"
    ));
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
            result,
            ..
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
