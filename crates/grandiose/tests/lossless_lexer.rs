use grandiose::lossless::{LosslessKind, lex_lossless};

fn round_trip(source: &str) {
    let tokens = lex_lossless(source).unwrap();
    assert_eq!(
        tokens
            .iter()
            .map(|token| token.text(source))
            .collect::<String>(),
        source
    );
    let mut cursor = 0;
    for token in tokens {
        assert_eq!(token.span.start, cursor);
        cursor = token.span.end;
    }
    assert_eq!(cursor, source.len());
}

#[test]
fn stream_is_a_gap_free_round_trip_with_all_trivia() {
    round_trip("\n// docs 😀\nmain() -> f64 { /* one /* two */ three */ 1.25e-3 }\n");
    round_trip("b\"raw\\xff\" 'life 'λ' '\\u{1F600}' @label 0xffff_ffff +-*\n");
}

#[test]
fn comments_are_retained_with_exact_kinds_and_spans() {
    let source = "a/* outer /* inner */ end */ // tail\nb";
    let tokens = lex_lossless(source).unwrap();
    let comments = tokens
        .iter()
        .filter(|token| token.kind.is_comment())
        .map(|token| (token.kind, token.text(source), token.span))
        .collect::<Vec<_>>();
    assert_eq!(comments.len(), 2);
    assert_eq!(comments[0].0, LosslessKind::BlockComment);
    assert_eq!(comments[0].1, "/* outer /* inner */ end */");
    assert_eq!(comments[1].0, LosslessKind::LineComment);
    assert_eq!(comments[1].1, "// tail");
}

#[test]
fn malformed_delimiters_report_the_exact_source_extent() {
    for (source, title) in [
        ("prefix /* open", "unfinished comment"),
        ("prefix \"open", "unfinished string"),
        ("prefix b\"open", "unfinished byte string"),
    ] {
        let error = lex_lossless(source).unwrap_err();
        assert_eq!(error.title, title);
        let span = error.span.unwrap();
        assert_eq!(&source[span.start..span.end], &source[7..]);
    }
}

#[test]
fn multibyte_text_keeps_byte_spans_for_utf16_consumers() {
    let source = "// 😀\nvalue + 'λ'";
    let tokens = lex_lossless(source).unwrap();
    let value = tokens
        .iter()
        .find(|token| token.text(source) == "value")
        .unwrap();
    assert_eq!(value.span.start, 8);
    assert_eq!(source[..value.span.start].encode_utf16().count(), 6);
    round_trip(source);
}
