//! Lexer conformance: every normative token form lexes with exact spans, and
//! every malformed form produces a deterministic diagnostic without hanging.

use grandiose::lexer::{Kw, NumberBase, TokenKind, lex};

fn kinds(source: &str) -> Vec<TokenKind> {
    lex(source)
        .unwrap_or_else(|error| panic!("{source}: {error:?}"))
        .into_iter()
        .map(|token| token.kind)
        .collect()
}

fn error_span(source: &str) -> (String, usize, usize) {
    let error = lex(source).expect_err(source);
    let span = error.span.expect("lexer errors carry spans");
    (error.title, span.start, span.end)
}

#[test]
fn keywords_are_classified_and_library_control_names_stay_identifiers() {
    for (word, keyword) in [
        ("let", Kw::Let),
        ("struct", Kw::Struct),
        ("enum", Kw::Enum),
        ("trait", Kw::Trait),
        ("impl", Kw::Impl),
        ("effect", Kw::Effect),
        ("where", Kw::Where),
        ("handle", Kw::Handle),
        ("perform", Kw::Perform),
        ("resume", Kw::Resume),
        ("cancel", Kw::Cancel),
        ("tail", Kw::Tail),
        ("is", Kw::Is),
        ("type", Kw::Type),
    ] {
        assert_eq!(
            kinds(word),
            vec![TokenKind::Keyword(keyword), TokenKind::Eof],
            "{word}"
        );
    }
    for word in [
        "if", "match", "loop", "return", "yield", "await", "label", "leave", "for", "with", "mut",
        "move", "cases", "private", "const", "infinity", "infixl", "infixr", "infix", "prefix",
        "self",
    ] {
        assert_eq!(
            kinds(word),
            vec![TokenKind::Ident(word.into()), TokenKind::Eof],
            "{word}"
        );
    }
}

#[test]
fn hyphenated_names_and_callable_reference_sigils_are_unambiguous() {
    assert_eq!(
        kinds("sum-three $sum-three value - other"),
        vec![
            TokenKind::Ident("sum-three".into()),
            TokenKind::Dollar,
            TokenKind::Ident("sum-three".into()),
            TokenKind::Ident("value".into()),
            TokenKind::Minus,
            TokenKind::Ident("other".into()),
            TokenKind::Eof,
        ]
    );
    assert_eq!(
        kinds("left-right left - right"),
        vec![
            TokenKind::Ident("left-right".into()),
            TokenKind::Ident("left".into()),
            TokenKind::Minus,
            TokenKind::Ident("right".into()),
            TokenKind::Eof,
        ]
    );
}

#[test]
fn labels_tokenize_references_and_binders() {
    assert_eq!(
        kinds("@outer"),
        vec![TokenKind::Label("outer".into()), TokenKind::Eof]
    );
    assert_eq!(
        kinds("@outer: @done(42)"),
        vec![
            TokenKind::Label("outer".into()),
            TokenKind::Colon,
            TokenKind::Label("done".into()),
            TokenKind::LParen,
            TokenKind::Number(match &kinds("42")[0] {
                TokenKind::Number(literal) => literal.clone(),
                _ => unreachable!(),
            }),
            TokenKind::RParen,
            TokenKind::Eof,
        ]
    );
    let tokens = lex("  @name").unwrap();
    assert_eq!((tokens[0].span.start, tokens[0].span.end), (2, 7));
    let (title, start, end) = error_span("@ ");
    assert_eq!((title.as_str(), start, end), ("invalid label", 0, 1));
}

#[test]
fn integer_bases_and_separators_lex_with_deferred_payloads() {
    for (source, base, digits) in [
        ("0b1010_1111", NumberBase::Binary, "10101111"),
        ("0o7_55", NumberBase::Octal, "755"),
        ("1_000_000", NumberBase::Decimal, "1000000"),
        ("0xDead_Beef", NumberBase::Hex, "DeadBeef"),
        ("0x_ff", NumberBase::Hex, "ff"),
    ] {
        let TokenKind::Number(literal) = &kinds(source)[0] else {
            panic!("{source}");
        };
        assert_eq!(literal.base, base, "{source}");
        assert_eq!(literal.digits, digits, "{source}");
        assert_eq!(literal.spelling, source, "{source}");
        assert!(!literal.is_float(), "{source}");
    }
}

#[test]
fn integer_conversion_preserves_the_full_u128_source_domain() {
    for (source, expected) in [
        ("340282366920938463463374607431768211455", u128::MAX),
        ("0xffff_ffff_ffff_ffff_ffff_ffff_ffff_ffff", u128::MAX),
    ] {
        let tokens = lex(source).unwrap();
        let TokenKind::Number(literal) = &tokens[0].kind else {
            panic!("{source}");
        };
        assert_eq!(literal.as_u128(tokens[0].span).unwrap(), expected);
        assert!(literal.as_u64(tokens[0].span).is_err());
        assert!(literal.as_i64(tokens[0].span).is_err());
    }

    let source = "340282366920938463463374607431768211456";
    let tokens = lex(source).unwrap();
    let TokenKind::Number(literal) = &tokens[0].kind else {
        panic!("{source}");
    };
    let error = literal.as_u128(tokens[0].span).unwrap_err();
    assert_eq!(error.title, "integer is too large");
    assert_eq!(error.message, "this integer does not fit in 128 bits");
}

#[test]
fn float_literals_lex_fractions_and_exponents() {
    for (source, fraction, exponent) in [
        ("1.5", Some("5"), None),
        ("0.25", Some("25"), None),
        ("1e9", None, Some((false, "9"))),
        ("2.5e-3", Some("5"), Some((true, "3"))),
        ("7E+2", None, Some((false, "2"))),
        ("1_0.2_5e1_0", Some("25"), Some((false, "10"))),
    ] {
        let TokenKind::Number(literal) = &kinds(source)[0] else {
            panic!("{source}");
        };
        assert!(literal.is_float(), "{source}");
        assert_eq!(literal.fraction.as_deref(), fraction, "{source}");
        assert_eq!(
            literal
                .exponent
                .as_ref()
                .map(|exponent| (exponent.negative, exponent.digits.as_str())),
            exponent,
            "{source}"
        );
    }
}

#[test]
fn floats_round_directly_to_the_contextual_ieee_width() {
    // Just above the midpoint between 1.0f32 and its successor. Parsing as
    // f64 first loses the final decimal increment and would double-round down.
    let source = "1.00000005960464477539062500000000000000000000000001";
    let tokens = lex(source).unwrap();
    let TokenKind::Number(literal) = &tokens[0].kind else {
        panic!("{source}");
    };
    assert_eq!(
        literal.as_f32(tokens[0].span).unwrap().to_bits(),
        0x3f80_0001
    );

    let source = "4.9406564584124654e-324";
    let tokens = lex(source).unwrap();
    let TokenKind::Number(literal) = &tokens[0].kind else {
        panic!("{source}");
    };
    assert_eq!(literal.as_f64(tokens[0].span).unwrap().to_bits(), 1);

    let source = "1e400";
    let tokens = lex(source).unwrap();
    let TokenKind::Number(literal) = &tokens[0].kind else {
        panic!("{source}");
    };
    assert_eq!(
        literal.as_f64(tokens[0].span).unwrap_err().title,
        "float literal is out of range"
    );
}

#[test]
fn tuple_projection_digits_never_form_floats() {
    let tokens = kinds("pair.0.1");
    assert_eq!(tokens.len(), 6, "{tokens:?}");
    assert!(matches!(&tokens[1], TokenKind::Dot));
    assert!(matches!(&tokens[2], TokenKind::Number(literal) if !literal.is_float()));
    assert!(matches!(&tokens[3], TokenKind::Dot));
    assert!(matches!(&tokens[4], TokenKind::Number(literal) if !literal.is_float()));
}

#[test]
fn malformed_numbers_have_exact_spans() {
    assert_eq!(error_span("0b102"), ("invalid digit".into(), 4, 5));
    assert_eq!(error_span("0o9"), ("expected digits".into(), 0, 2));
    assert_eq!(error_span("12ab"), ("invalid digit".into(), 2, 3));
    assert_eq!(
        error_span("1__2_ "),
        ("misplaced digit separator".into(), 4, 5)
    );
    assert_eq!(
        error_span("1.5_"),
        ("misplaced digit separator".into(), 3, 4)
    );
    assert_eq!(error_span("0x"), ("expected digits".into(), 0, 2));
    assert_eq!(
        error_span("1e_"),
        ("misplaced digit separator".into(), 2, 3)
    );
}

#[test]
fn character_literals_and_lifetimes_disambiguate() {
    assert_eq!(kinds("'a'"), vec![TokenKind::Char('a'), TokenKind::Eof]);
    assert_eq!(kinds("'\\n'"), vec![TokenKind::Char('\n'), TokenKind::Eof]);
    assert_eq!(
        kinds("'\\u{1F600}'"),
        vec![TokenKind::Char('😀'), TokenKind::Eof]
    );
    assert_eq!(kinds("'é'"), vec![TokenKind::Char('é'), TokenKind::Eof]);
    assert_eq!(
        kinds("'static"),
        vec![TokenKind::Lifetime("'static".into()), TokenKind::Eof]
    );
    assert_eq!(
        kinds("<'a>"),
        vec![
            TokenKind::Lt,
            TokenKind::Lifetime("'a".into()),
            TokenKind::Gt,
            TokenKind::Eof
        ]
    );
    assert_eq!(error_span("''"), ("empty character literal".into(), 0, 2));
    assert_eq!(
        error_span("'ab'"),
        ("invalid character literal".into(), 0, 4)
    );
}

#[test]
fn byte_and_byte_string_literals_lex() {
    assert_eq!(kinds("b'A'"), vec![TokenKind::Byte(65), TokenKind::Eof]);
    assert_eq!(
        kinds("b'\\xFF'"),
        vec![TokenKind::Byte(255), TokenKind::Eof]
    );
    assert_eq!(
        kinds("b\"hi\\x00\""),
        vec![TokenKind::ByteString(vec![104, 105, 0]), TokenKind::Eof]
    );
    assert_eq!(error_span("b''"), ("empty byte literal".into(), 0, 3));
    assert_eq!(error_span("b'é'"), ("invalid byte literal".into(), 2, 4));
    assert_eq!(
        error_span("b\"é\""),
        ("invalid byte string character".into(), 2, 4)
    );
    let (title, ..) = error_span("b\"\\u{41}\"");
    assert_eq!(title, "invalid byte escape");
}

#[test]
fn string_escapes_decode_completely() {
    assert_eq!(
        kinds("\"a\\n\\r\\t\\0\\\"\\'\\\\\\x41\\u{2603}\""),
        vec![TokenKind::String("a\n\r\t\0\"'\\A☃".into()), TokenKind::Eof]
    );
    assert_eq!(error_span("\"\\q\""), ("unknown escape".into(), 1, 3));
    assert_eq!(
        error_span("\"\\u{110000}\""),
        ("invalid Unicode scalar".into(), 1, 11)
    );
    let (title, ..) = error_span("\"\\uD800\"");
    assert_eq!(title, "malformed Unicode escape");
    let (title, ..) = error_span("\"\\u{D800}\"");
    assert_eq!(title, "invalid Unicode scalar");
    let (title, ..) = error_span("\"\\x80\"");
    assert_eq!(title, "invalid character escape");
    assert_eq!(error_span("\"open"), ("unfinished string".into(), 0, 5));
}

#[test]
fn structural_operators_take_priority_over_runs() {
    assert_eq!(
        kinds("type A=&i64;"),
        vec![
            TokenKind::Keyword(Kw::Type),
            TokenKind::Ident("A".into()),
            TokenKind::Eq,
            TokenKind::Amp,
            TokenKind::Ident("i64".into()),
            TokenKind::Semicolon,
            TokenKind::Eof
        ]
    );
    // A pure `>` run closes nested generics one token at a time.
    assert_eq!(
        kinds("Vec<Vec<T>>"),
        vec![
            TokenKind::Ident("Vec".into()),
            TokenKind::Lt,
            TokenKind::Ident("Vec".into()),
            TokenKind::Lt,
            TokenKind::Ident("T".into()),
            TokenKind::Gt,
            TokenKind::Gt,
            TokenKind::Eof
        ]
    );
    // Punctuation with no structural reading forms one Operator token.
    assert_eq!(
        kinds("a ?? b"),
        vec![
            TokenKind::Ident("a".into()),
            TokenKind::Operator("??".into()),
            TokenKind::Ident("b".into()),
            TokenKind::Eof
        ]
    );
    assert_eq!(
        kinds("x ~> y"),
        vec![
            TokenKind::Ident("x".into()),
            TokenKind::Operator("~".into()),
            TokenKind::Gt,
            TokenKind::Ident("y".into()),
            TokenKind::Eof
        ]
    );
}

#[test]
fn comments_nest_and_line_comments_end_at_newlines() {
    assert_eq!(
        kinds("a // trailing /* not a block\nb"),
        vec![
            TokenKind::Ident("a".into()),
            TokenKind::Ident("b".into()),
            TokenKind::Eof
        ]
    );
    assert_eq!(
        kinds("a /* one /* two */ still */ b"),
        vec![
            TokenKind::Ident("a".into()),
            TokenKind::Ident("b".into()),
            TokenKind::Eof
        ]
    );
    assert_eq!(error_span("/* /* */"), ("unfinished comment".into(), 0, 8));
}

#[test]
fn spans_are_exact_around_multibyte_text() {
    let source = "let ☃ = \"☃\";";
    // `☃` is not part of the syntax: the error span covers exactly its bytes.
    let (title, start, end) = error_span(source);
    assert_eq!(title, "unexpected character");
    assert_eq!((start, end), (4, 7));
    let tokens = lex("\"☃x\" y").unwrap();
    assert_eq!((tokens[0].span.start, tokens[0].span.end), (0, 6));
    assert_eq!((tokens[1].span.start, tokens[1].span.end), (7, 8));
}

/// Every input either lexes or errors; the lexer can never hang or panic.
#[test]
fn arbitrary_bytes_never_hang_the_lexer() {
    let mut state = 0x2545F4914F6CDD1Du64;
    let mut next = move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for round in 0..2000 {
        let length = (next() % 64) as usize;
        let bytes = (0..length)
            .map(|_| (next() % 256) as u8)
            .collect::<Vec<_>>();
        let source = String::from_utf8_lossy(&bytes).into_owned();
        let _ = lex(&source);
        let _ = round;
    }
    // Adversarial shapes: unfinished literals, long runs, deep comments.
    let mut adversarial = [
        "\"", "b\"", "'", "b'", "@", "0x", "1e", "/*", "/*/*/*", "\"\\", "'\\", "b'\\",
    ]
    .map(String::from)
    .to_vec();
    adversarial.push("+".repeat(10_000));
    adversarial.push("/*".repeat(2_000));
    adversarial.push("'".repeat(5_000));
    adversarial.push("9".repeat(5_000));
    adversarial.push(format!("\"{}", "\\\\".repeat(4_000)));
    for source in &adversarial {
        let _ = lex(source);
    }
}
