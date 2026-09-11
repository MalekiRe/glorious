use grandiose_stage0::{
    BodySyntax, ConstKind, DeclarationScan, Digest, EnumVariantPayloadHeader, FileKey,
    HeaderGenericArgument, HeaderParse, HeaderType, LexedFile, LogicalPath, NominalLayoutHeader,
    PackageKey, ParsedHeader, Quantity,
};

fn trait_bound(bound: &grandiose_stage0::WhereBoundHeader) -> (&HeaderType, &grandiose_stage0::TraitRefHeader) {
    let grandiose_stage0::header::PredicateHeader::Trait { subject, relation } = &bound.predicate else { panic!("expected trait predicate"); };
    (subject, relation)
}

fn parse_higher_ranked_header(source: &str) -> HeaderParse {
    let package = PackageKey("higher-ranked-header@0.1.0".into());
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    HeaderParse::parse(&lexed, source, &scan.declarations[0])
}

#[test]
fn parenthesized_types_preserve_grouping_and_tuple_arity() {
    let scalar = HeaderType::Path(vec!["i64".into()]);
    for (spelling, expected) in [
        ("(i64)", scalar.clone()),
        ("((i64))", scalar.clone()),
        ("(i64,)", HeaderType::Tuple(vec![scalar.clone()])),
        ("((i64,),)", HeaderType::Tuple(vec![HeaderType::Tuple(vec![scalar.clone()])])),
        ("()", HeaderType::Tuple(vec![])),
    ] {
        let parsed = parse_higher_ranked_header(&format!("fn accept(value: {spelling}) -> {spelling} {{ value }}"));
        assert!(parsed.diagnostics.is_empty(), "{spelling}: {parsed:#?}");
        let ParsedHeader::Function(header) = parsed.header else { panic!("callable"); };
        assert_eq!(header.parameters[0].ty, expected, "{spelling}");
        assert_eq!(header.result, Some(expected), "{spelling}");
    }
    for (spelling, expected) in [
        ("(i64) -> i64", scalar.clone()),
        ("((i64)) -> i64", scalar.clone()),
        ("((i64,)) -> i64", HeaderType::Tuple(vec![scalar])),
    ] {
        let parsed = parse_higher_ranked_header(&format!("fn accept(value: &({spelling})) {{}}"));
        assert!(parsed.diagnostics.is_empty(), "{spelling}: {parsed:#?}");
        let ParsedHeader::Function(header) = parsed.header else { panic!("callable"); };
        let HeaderType::Reference { referent, .. } = &header.parameters[0].ty else { panic!("reference"); };
        let HeaderType::Callable { parameters, .. } = referent.as_ref() else { panic!("grouped callable: {referent:?}"); };
        assert_eq!(parameters, &[expected], "{spelling}");
    }
}

#[test]
fn plus_separated_where_bounds_preserve_each_subject_and_universal_binder() {
    let parsed = parse_higher_ranked_header(
        "fn observe<T>() where T: Eq + Use<[0,1]>, for<'a> &'a T: Inspect<'a> + Stable<'a> {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else { panic!("callable"); };
    assert_eq!(header.where_bounds.len(), 4);
    assert_eq!(trait_bound(&header.where_bounds[0]).0, trait_bound(&header.where_bounds[1]).0);
    assert_eq!(trait_bound(&header.where_bounds[1]).1.path, ["Use"]);
    for bound in &header.where_bounds[2..] {
        assert_eq!(bound.universal.as_ref().unwrap().names, ["'a"]);
    }
    assert_eq!(trait_bound(&header.where_bounds[2]).0, trait_bound(&header.where_bounds[3]).0);
    assert_eq!(trait_bound(&header.where_bounds[3]).1.path, ["Stable"]);
}

#[test]
fn nominal_where_predicates_are_retained_instead_of_skipped() {
    for source in [
        "struct Cache<I> where I: Iterator { item: <I as Iterator>::Item }",
        "enum Cache<I> where I: Iterator { Full(<I as Iterator>::Item) }",
        "struct Cache<I> where I: Iterator (<I as Iterator>::Item);",
    ] {
        let parsed = parse_higher_ranked_header(source);
        assert!(parsed.diagnostics.is_empty(), "{source}: {parsed:#?}");
        let ParsedHeader::Nominal { where_bounds, .. } = parsed.header else { panic!("nominal"); };
        assert_eq!(where_bounds.len(), 1);
        assert_eq!(trait_bound(&where_bounds[0]).1.path, ["Iterator"]);
    }
}

#[test]
fn higher_ranked_where_binder_owns_subject_relation_and_equalities() {
    let parsed = parse_higher_ranked_header(
        "fn call<F>() where for<'a> &'a F: Fn<(&'a i64,), Output = &'a i64, Effects={}>, F: Use<[0,1]> {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else { panic!("callable") };
    assert_eq!(header.generics.names, ["F"]);
    assert_eq!(header.where_bounds.len(), 2);
    let bound = &header.where_bounds[0];
    assert_eq!(bound.universal.as_ref().unwrap().names, ["'a"]);
    assert!(matches!(trait_bound(bound).0, HeaderType::Reference { lifetime: Some(name), .. } if name == "'a"));
    assert!(matches!(&trait_bound(bound).1.arguments[0], HeaderGenericArgument::Type(HeaderType::Tuple(items))
        if matches!(&items[0], HeaderType::Reference { lifetime: Some(name), .. } if name == "'a")));
    assert!(matches!(&trait_bound(bound).1.arguments[1], HeaderGenericArgument::AssociatedTypeBinding { value, .. }
        if matches!(value.as_ref(), HeaderType::Reference { lifetime: Some(name), .. } if name == "'a")));
    assert!(matches!(&trait_bound(bound).1.arguments[2], HeaderGenericArgument::AssociatedEffectBinding { .. }));
    assert!(header.where_bounds[1].universal.is_none());
}

#[test]
fn higher_ranked_where_binder_preserves_kinds_and_nested_callable_scope() {
    let parsed = parse_higher_ranked_header(
        "fn call<F>() where for<'a, e: EffectRow, const n: u32> F: Rel<'a, {|e}, n, Output=for<'b> (&'b i64) -> &'b i64> {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else { panic!("callable") };
    let bound = &header.where_bounds[0];
    assert_eq!(bound.universal.as_ref().unwrap().kinds(), [
        grandiose_stage0::GenericKind::Lifetime,
        grandiose_stage0::GenericKind::EffectRow,
        grandiose_stage0::GenericKind::Const(ConstKind::U32),
    ]);
    assert!(matches!(&trait_bound(bound).1.arguments[3], HeaderGenericArgument::AssociatedTypeBinding { value, .. }
        if matches!(value.as_ref(), HeaderType::Callable { lifetime_binders, .. } if lifetime_binders == &["'b"])));
}

#[test]
fn higher_ranked_where_binders_do_not_become_declaration_generics() {
    let parsed = parse_higher_ranked_header(
        "fn call<'a, F>() where for<'a> F: First<'a>, for<'a> F: Second<'a>, F: Third<'a> {}",
    );
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else { panic!("callable") };
    assert_eq!(header.generics.names, ["'a", "F"]);
    assert_eq!(header.where_bounds[0].universal.as_ref().unwrap().names, ["'a"]);
    assert_eq!(header.where_bounds[1].universal.as_ref().unwrap().names, ["'a"]);
    assert!(header.where_bounds[2].universal.is_none());
}

#[test]
fn higher_ranked_where_binders_reject_defaults_duplicates_and_missing_lists() {
    for binders in ["for", "for<>", "for<'a, 'a>", "for<'a = 'static>", "for<n: u32 = 1>", "for<e: EffectRow = {}>"] {
        let parsed = parse_higher_ranked_header(&format!("fn call<F>() where {binders} F: Rel {{}}"));
        assert!(parsed.diagnostics.iter().any(|diagnostic| diagnostic.code == "G3334"), "{binders}: {parsed:#?}");
    }
}

#[test]
fn effect_row_union_parses_associated_projections_and_a_parameter() {
    for row in [
        "{| <T as First>::Effects, e, <T as Second>::Effects,}",
        "{Trace | e, <T as First>::Effects, <T as Second>::Effects}",
    ] {
        let source = format!("fn call<T, e: EffectRow>() / {row} {{}}");
        let package = PackageKey("projection-row@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        let parsed = HeaderParse::parse(&lexed, &source, &scan.declarations[0]);
        assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
        let ParsedHeader::Function(header) = parsed.header else { panic!("callable") };
        assert_eq!(header.effects.tails.as_slice(), ["e"]);
        assert_eq!(header.effects.effects.iter().filter(|term| matches!(term, HeaderType::Projection { .. })).count(), 2);
    }
}

#[test]
fn effect_row_union_rejects_empty_or_repeated_separator() {
    for row in ["{|}", "{|e|e}", "{|<T as First>::Effects <T as Second>::Effects}"] {
        let source = format!("fn call<T, e: EffectRow>() / {row} {{}}");
        let package = PackageKey("invalid-row@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        let parsed = HeaderParse::parse(&lexed, &source, &scan.declarations[0]);
        assert!(!parsed.diagnostics.is_empty(), "accepted {row}");
    }
}

#[test]
fn effect_payloads_parse_positional_types_without_callable_binders() {
    let package = PackageKey("positional-effects@0.1.0".into());
    let source = "effect Pack<'a, T> { send(i64, &'a T, (T, i64), module::Item<T>, (T) -> T,); empty(); stop(T) -> !; }";
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Effect(header) = parsed.header else {
        panic!("expected effect header")
    };
    let send = &header.operations[0];
    assert_eq!(send.parameters.len(), 5);
    assert_eq!(send.parameters.iter().map(|p| p.name.as_str()).collect::<Vec<_>>(), ["0", "1", "2", "3", "4"]);
    assert!(matches!(&send.parameters[1].ty, HeaderType::Reference { lifetime: Some(name), .. } if name == "'a"));
    assert!(matches!(&send.parameters[2].ty, HeaderType::Tuple(types) if types.len() == 2));
    assert!(matches!(&send.parameters[3].ty, HeaderType::Application(base, _) if matches!(base.as_ref(), HeaderType::Path(path) if path == &["module", "Item"])));
    assert!(matches!(send.parameters[4].ty, HeaderType::Callable { .. }));
    assert_eq!(send.resumption, Quantity::ONCE);
    assert!(send.result.is_none());
    assert!(header.operations[1].parameters.is_empty());
    assert!(header.operations[2].terminal);
}

#[test]
fn positional_effect_syntax_does_not_relax_function_parameter_binders() {
    let package = PackageKey("positional-function-rejection@0.1.0".into());
    let source = "pub fn invalid(i64) -> i64 { 42 }";
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.iter().any(|diagnostic| diagnostic.code == "G3203"), "{parsed:#?}");
}

#[test]
fn inherent_method_unit_type_arguments_do_not_scan_into_method_bodies() {
    let package = PackageKey("header-inherent@0.1.0".into());
    let source =
        "impl Cell { pub fn replace(value: &mut Self) -> Option<()> { *value = other(); } }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::InherentImplementation(header) = parsed.header else {
        panic!("expected inherent impl")
    };
    assert!(header.methods[0].visibility.is_public());
    assert!(
        matches!(header.methods[0].signature.result, Some(HeaderType::Application(_, ref args))
        if matches!(args.as_slice(), [HeaderGenericArgument::Type(HeaderType::Tuple(values))] if values.is_empty()))
    );
}

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
fn host_import_headers_freeze_the_capability_prefix_and_callable_abi() {
    let package = PackageKey("header-host-import@0.1.0".into());
    let source = "pub host clock fn now() -> i64;";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{scan:#?}");
    let shell = &scan.declarations[0];
    assert_eq!(shell.host_capability.as_deref(), Some("clock"));
    let parsed = HeaderParse::parse(&lexed, source, shell);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    assert!(matches!(parsed.header, ParsedHeader::Function(_)));
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
            ..
        } if lifetime_binders == &["'a"]
            && matches!(parameters.as_slice(), [HeaderType::Reference { lifetime: Some(name), .. }] if name == "'a")
            && matches!(result.as_ref(), HeaderType::Reference { lifetime: Some(name), .. } if name == "'a")
    ));
}

#[test]
fn headers_merge_stacked_higher_ranked_binder_prefixes() {
    let package = PackageKey("header-stacked-hrtb@0.1.0".into());
    let source =
        "pub fn use_callback(callback: for<'a> for<'b> (&'a i64, &'b i64) -> &'a i64) { callback }";
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
        HeaderType::Callable { lifetime_binders, parameters, result, .. }
            if lifetime_binders == &vec!["'a".to_owned(), "'b".to_owned()]
                && matches!(parameters.as_slice(), [
                    HeaderType::Reference { lifetime: Some(first), .. },
                    HeaderType::Reference { lifetime: Some(second), .. },
                ] if first == "'a" && second == "'b")
                && matches!(result.as_ref(), HeaderType::Reference { lifetime: Some(name), .. } if name == "'a")
    ));
}

#[test]
fn headers_parse_effect_rows_on_callable_types() {
    let package = PackageKey("header-callable-effects@0.1.0".into());
    let source = "pub fn apply(callback: (i64) -> i64 / { Trace, Log<Text> }) -> i64 { 0 }";
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
        HeaderType::Callable { effects, .. }
            if effects.effects.len() == 2
                && matches!(&effects.effects[0], HeaderType::Path(path) if path == &["Trace"])
                && matches!(&effects.effects[1], HeaderType::Application(base, arguments)
                    if matches!(base.as_ref(), HeaderType::Path(path) if path == &["Log"])
                        && matches!(arguments.as_slice(), [grandiose_stage0::HeaderGenericArgument::Type(HeaderType::Path(path))] if path == &["Text"]))
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
            if arguments == vec![HeaderGenericArgument::Integer("7".into())]
    ));
}

#[test]
fn trait_references_retain_explicit_lifetime_arguments() {
    let package = PackageKey("header-lifetime-generic-argument@0.1.0".into());
    let source = "pub trait Marker<'a> {} pub fn require<'a, T>() where T: Marker<'a> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        header.where_bounds.as_slice(),
        [bound] if trait_bound(bound).1.arguments == vec![HeaderGenericArgument::Lifetime("'a".into())]
    ));
}

#[test]
fn trait_references_retain_explicit_effect_row_arguments() {
    let package = PackageKey("header-effect-row-generic-argument@0.1.0".into());
    let source = "pub trait Capability<e: EffectRow> {} pub fn require<e: EffectRow, T>() where T: Capability<{ | e }> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header")
    };
    assert!(matches!(
        header.where_bounds.as_slice(),
        [bound]
            if matches!(
                trait_bound(bound).1.arguments.as_slice(),
                [HeaderGenericArgument::EffectRow(row)] if row.effects.is_empty() && row.tails.as_slice() == ["e"]
            )
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
fn structural_header_literals_accept_radices_and_digit_separators() {
    let package = PackageKey("header-const-radices@0.1.0".into());
    for literal in ["42", "4_2", "0b10_1010", "0o52", "0x2a", "0x_2A"] {
        let source = format!("fn tag() -> Tag<{literal}> {{ tag }} fn budget() -> Budget<[{literal}, {literal} + 1]> {{ budget }} fn symbolic<const N: u32>() -> Tag<N + {literal}> {{ tag }}");
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        assert!(lexed.diagnostics.is_empty(), "{literal}: {lexed:?}");
        let scan = DeclarationScan::scan(&lexed, &source);
        let parsed = scan.declarations.iter().map(|declaration| {
            let parsed = HeaderParse::parse(&lexed, &source, declaration);
            assert!(parsed.diagnostics.is_empty(), "{literal}: {parsed:?}");
            let ParsedHeader::Function(header) = parsed.header else { panic!("function") };
            header
        }).collect::<Vec<_>>();
        assert!(matches!(&parsed[0].result, Some(HeaderType::Application(_, arguments)) if arguments == &vec![HeaderGenericArgument::Integer(literal.into())]));
        assert!(matches!(&parsed[1].result, Some(HeaderType::Application(_, arguments)) if arguments == &vec![HeaderGenericArgument::Quantity(Quantity::new(42, Some(43)).unwrap())]));
        assert!(matches!(&parsed[2].result, Some(HeaderType::Application(_, arguments)) if matches!(&arguments[0], HeaderGenericArgument::StructuralConst(_))));
    }
}

#[test]
fn structural_header_radix_literals_defer_range_checks_to_declared_kind() {
    let package = PackageKey("header-const-radix-range@0.1.0".into());
    for literal in ["0x1_0000_0000", "0xffff_ffff_ffff_ffff + 1", "0x1_0000_0000_0000_0000", "0b1 / 0o0"] {
        let source = format!("fn tag() -> Tag<{literal}> {{ tag }}");
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &source);
        let scan = DeclarationScan::scan(&lexed, &source);
        let parsed = HeaderParse::parse(&lexed, &source, &scan.declarations[0]);
        assert!(parsed.diagnostics.is_empty(), "{literal}: {parsed:?}");
        let typed_source = format!("struct Tag<const N: u32>; {source}");
        let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), &typed_source);
        let scan = DeclarationScan::scan(&lexed, &typed_source);
        let interface = grandiose_stage0::InterfaceSet::collect(package.clone(), "crate", &lexed, &typed_source, &scan).interface;
        let signatures = grandiose_stage0::ElaboratedInterface::elaborate(&interface);
        assert!(signatures.diagnostics.iter().any(|diagnostic| diagnostic.code == "G4134"), "{literal}: {:?}", signatures.diagnostics);
    }
}

#[test]
fn nominal_headers_preserve_integer_arithmetic_and_normalize_quantities() {
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
            if arguments == vec![HeaderGenericArgument::StructuralConst(
                grandiose_stage0::HeaderStructuralConst::IntegerExpression(
                    grandiose_stage0::HeaderIntegerExpr::Add(
                        Box::new(grandiose_stage0::HeaderIntegerExpr::Literal("1".into())),
                        Box::new(grandiose_stage0::HeaderIntegerExpr::Mul(
                            Box::new(grandiose_stage0::HeaderIntegerExpr::Literal("2".into())),
                            Box::new(grandiose_stage0::HeaderIntegerExpr::Literal("3".into()))
                        ))
                    )
                )
            )]
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
fn structural_const_arithmetic_is_not_evaluated_before_kind_selection() {
    let package = PackageKey("header-structural-const-arithmetic-errors@0.1.0".into());
    let source = "pub fn overflow() -> Tag<4294967295 + 1> { overflow } pub fn zero() -> Tag<8 / 0> { zero }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let overflow = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(overflow.diagnostics.is_empty(), "{overflow:#?}");
    let zero = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(zero.diagnostics.is_empty(), "{zero:#?}");
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
    let ParsedHeader::Import(ref import) = parsed.header else {
        panic!("expected import header")
    };
    assert!(parsed.diagnostics.is_empty(), "{:#?}", parsed.diagnostics);
    assert_eq!(
        import.bindings,
        vec![
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into(), "add".into()],
                alias: Some("plus".into()),
                glob: false,
            },
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into(), "zero".into()],
                alias: None,
                glob: false,
            },
        ]
    );
}

#[test]
fn glob_import_headers_remain_module_facts_until_resolution() {
    let package = PackageKey("header-glob-import@0.1.0".into());
    let source = "use crate::math::{*, nested::*};";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    let ParsedHeader::Import(ref import) = parsed.header else {
        panic!("expected import header")
    };
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    assert_eq!(
        import.bindings,
        vec![
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into()],
                alias: None,
                glob: true,
            },
            grandiose_stage0::ImportBindingHeader {
                path: vec!["crate".into(), "math".into(), "nested".into()],
                alias: None,
                glob: true,
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
    let ParsedHeader::Nominal { generics, layout, .. } = pair.header else {
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
fn nominal_headers_accept_line_separated_variants_and_private_fields() {
    let package = PackageKey("header-nominal-newline@0.1.0".into());
    let source = "struct View<T> {\n private base: T\n private length: usize\n}\nenum Step<T> {\n Continue(T)\n Stop\n}";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    assert!(scan.diagnostics.is_empty(), "{:#?}", scan.diagnostics);
    let view = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(view.diagnostics.is_empty(), "{view:#?}");
    let ParsedHeader::Nominal { layout, .. } = view.header else {
        panic!("expected struct nominal header")
    };
    assert!(
        matches!(layout, NominalLayoutHeader::Struct(fields) if fields.len() == 2 && fields[0].name == "base")
    );
    let step = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(step.diagnostics.is_empty(), "{step:#?}");
    let ParsedHeader::Nominal { layout, .. } = step.header else {
        panic!("expected enum nominal header")
    };
    assert!(
        matches!(layout, NominalLayoutHeader::Enum(variants) if variants.len() == 2 && variants[0].name == "Continue")
    );
}

#[test]
fn nominal_fields_accept_pub_on_records_and_named_enum_payloads() {
    let package = PackageKey("header-pub-fields@0.1.0".into());
    let source = "pub struct Record { pub value: i64, private hidden: i64 } pub enum Event { Value { pub value: i64, private hidden: i64 } }";
    let lexed = LexedFile::lex(FileKey::new(&package, "src/lib.glorious"), source);
    let scan = DeclarationScan::scan(&lexed, source);
    for declaration in &scan.declarations {
        let parsed = HeaderParse::parse(&lexed, source, declaration);
        assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
        let ParsedHeader::Nominal { layout, .. } = parsed.header else { panic!("nominal header"); };
        let fields = match &layout {
            NominalLayoutHeader::Struct(fields) => fields,
            NominalLayoutHeader::Enum(variants) => match &variants[0].payload {
                EnumVariantPayloadHeader::Struct(fields) => fields,
                _ => panic!("named payload"),
            },
            _ => panic!("record layout"),
        };
        assert_eq!(fields.iter().map(|field| (field.name.as_str(), !field.visibility.is_public())).collect::<Vec<_>>(),
            [("value", false), ("hidden", true)]);
        assert!(source[fields[0].span.start as usize..fields[0].span.end as usize].starts_with("pub value"));
    }
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
            [0, 1] read() -> T;
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
    assert_eq!(value.operations[1].resumption, Quantity::AFFINE);
    assert!(value.operations[2].terminal);
}

#[test]
fn trait_headers_preserve_value_and_effect_row_associated_defaults() {
    let package = PackageKey("header-associated-defaults@0.1.0".into());
    let source =
        "trait Capability<T> { type Output<U> = (T, U); type Effects: EffectRow = { Trace }; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Trait(trait_header) = parsed.header else {
        panic!("expected trait header");
    };
    assert!(trait_header.associated_types[0].default.is_some());
    assert!(
        trait_header.associated_types[0]
            .effect_row_default
            .is_none()
    );
    assert!(trait_header.associated_types[1].default.is_none());
    assert!(
        trait_header.associated_types[1]
            .effect_row_default
            .is_some()
    );
}

#[test]
fn callable_where_bounds_preserve_named_type_and_effect_bindings() {
    let package = PackageKey("header-named-associated-bindings@0.1.0".into());
    let source = "pub fn apply<F>() where F: Fn<(), Output = i64, Effects = {| e}> { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header");
    };
    assert!(matches!(
        trait_bound(&header.where_bounds[0]).1.arguments.as_slice(),
        [
            HeaderGenericArgument::Type(HeaderType::Tuple(values)),
            HeaderGenericArgument::AssociatedTypeBinding { name, value, .. },
            HeaderGenericArgument::AssociatedEffectBinding { name: effects, value: row, .. },
        ] if values.is_empty()
            && name == "Output"
            && matches!(value.as_ref(), HeaderType::Path(path) if path == &["i64"])
            && effects == "Effects"
            && row.tails.as_slice() == ["e"]
    ));
}

#[test]
fn associated_bindings_accept_adjacent_type_delimiters() {
    let package = PackageKey("header-adjacent-associated-bindings@0.1.0".into());
    for source in [
        "fn select<I,J>() where J: Iterator<Item=<I as Iterator>::Item> {}",
        "fn select<I,J>() where J: Iterator<Item=&'static I> {}",
        "fn select<I,J>() where J: Iterator<Item< I>=J> {}",
    ] {
        let file = FileKey::new(&package, "src/lib.glorious");
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
        assert!(parsed.diagnostics.is_empty(), "{source}: {parsed:#?}");
        let ParsedHeader::Function(header) = parsed.header else { panic!("expected function"); };
        assert!(matches!(trait_bound(&header.where_bounds[0]).1.arguments.as_slice(),
            [HeaderGenericArgument::AssociatedTypeBinding { name, .. }] if name == "Item"));
    }
}

#[test]
fn canonical_unit_arrow_before_a_callable_body_does_not_parse_a_brace_as_a_type() {
    let package = PackageKey("header-unit-arrow@0.1.0".into());
    let source = "pub fn clear(value: &mut i64) -> { *value = 0; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Function(header) = parsed.header else {
        panic!("expected callable header");
    };
    assert!(header.result.is_none());
}

#[test]
fn nominal_fields_keep_public_and_private_as_ordinary_names_before_a_colon() {
    let package = PackageKey("header-visibility-names@0.1.0".into());
    let source = "pub struct Flags { public: Bool, private: Bool, public named: i64 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Nominal {
        layout: grandiose_stage0::NominalLayoutHeader::Struct(fields),
        ..
    } = parsed.header
    else {
        panic!("expected struct layout");
    };
    assert_eq!(
        fields
            .iter()
            .map(|field| field.name.as_str())
            .collect::<Vec<_>>(),
        ["public", "private", "named"]
    );
}

#[test]
fn malformed_named_associated_binding_reports_the_type_frontier() {
    let package = PackageKey("header-malformed-associated-binding@0.1.0".into());
    let source = "pub fn apply<F>() where F: Fn<(), Output = > { 0 }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(
        parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3207")
    );
    assert!(
        !parsed
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.code == "G3208"),
        "the named binding consumed its `=` and recovered at its value"
    );
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
fn effect_source_resumption_quantities_accept_only_affine_or_exact_intervals() {
    let package = PackageKey("header-effect-source-resumption-quantity@0.1.0".into());
    for source in [
        "effect Retry { [0, 1] retry() -> i64; }",
        "effect Retry { [0, 0] retry() -> i64; }",
        "effect Retry { [3, 3] retry() -> i64; }",
    ] {
        let file = FileKey::new(&package, "src/lib.glorious");
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        let header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
        assert!(header.diagnostics.is_empty(), "{source}: {header:#?}");
    }
    for source in [
        "effect Retry { [1, 2] retry() -> i64; }",
        "effect Retry { [0, 2] retry() -> i64; }",
        "effect Retry { [1, *] retry() -> i64; }",
    ] {
        let file = FileKey::new(&package, "src/lib.glorious");
        let lexed = LexedFile::lex(file, source);
        let scan = DeclarationScan::scan(&lexed, source);
        let header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
        assert!(
            header
                .diagnostics
                .iter()
                .any(|diagnostic| diagnostic.code == "G3254")
        );
    }
}

#[test]
fn effect_resumption_bounds_share_structural_quantity_normalization() {
    let package = PackageKey("header-effect-quantity-arithmetic@0.1.0".into());
    let source = "effect Retry { [(1 + 1), 1 + 1] retry() -> i64; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(parsed.diagnostics.is_empty(), "{parsed:#?}");
    let ParsedHeader::Effect(effect) = parsed.header else {
        panic!("expected effect header")
    };
    assert_eq!(
        effect.operations[0].resumption,
        Quantity::new(2, Some(2)).unwrap()
    );
}

#[test]
fn effect_resumption_quantity_arithmetic_reports_deterministic_overflow() {
    let package = PackageKey("header-effect-quantity-overflow@0.1.0".into());
    let source = "effect Retry { [18446744073709551615 + 1, 2] retry(); }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let parsed = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert_eq!(
        parsed
            .diagnostics
            .iter()
            .filter(|diagnostic| diagnostic.code == "G3265")
            .count(),
        1,
        "{parsed:#?}"
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

#[test]
fn terminal_callable_headers_accept_compact_effect_row_delimiters() {
    let package = PackageKey("header-terminal-effects@0.1.0".into());
    let source = "fn stop() -> !/ Stop { Stop::abort() }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(header.diagnostics.is_empty(), "{header:#?}");
    let ParsedHeader::Function(value) = header.header else {
        panic!("expected callable")
    };
    assert!(matches!(value.result, Some(HeaderType::Never)));
    assert!(
        matches!(value.effects.effects.as_slice(), [HeaderType::Path(effect)] if effect == &["Stop"])
    );
}

#[test]
fn trait_and_implementation_headers_preserve_structural_associated_constants() {
    let package = PackageKey("header-associated-const@0.1.0".into());
    let source = "trait Shape { const Width: u32 = 4; const Demand: Quantity; } impl Shape for i64 { const Width = 8; const Demand = [1, *]; }";
    let file = FileKey::new(&package, "src/lib.glorious");
    let lexed = LexedFile::lex(file, source);
    let scan = DeclarationScan::scan(&lexed, source);
    let trait_header = HeaderParse::parse(&lexed, source, &scan.declarations[0]);
    assert!(trait_header.diagnostics.is_empty(), "{trait_header:#?}");
    let ParsedHeader::Trait(trait_header) = trait_header.header else {
        panic!("expected trait")
    };
    assert_eq!(trait_header.associated_consts.len(), 2);
    assert_eq!(trait_header.associated_consts[0].kind, ConstKind::U32);
    assert!(trait_header.associated_consts[0].default.is_some());
    assert_eq!(trait_header.associated_consts[1].kind, ConstKind::Quantity);
    let implementation = HeaderParse::parse(&lexed, source, &scan.declarations[1]);
    assert!(implementation.diagnostics.is_empty(), "{implementation:#?}");
    let ParsedHeader::Implementation(implementation) = implementation.header else {
        panic!("expected implementation")
    };
    assert_eq!(implementation.associated_consts.len(), 2);
}
