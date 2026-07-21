use std::path::{Path, PathBuf};

use grandiose::lossless::{lex_lossless, LosslessKind};

fn significant(source: &str) -> Vec<String> {
    let mut tokens = lex_lossless(source)
        .expect("source should lex")
        .into_iter()
        .filter(|token| token.kind != LosslessKind::Whitespace)
        .map(|token| token.text(source).to_owned())
        .collect::<Vec<_>>();
    let mut index = 0;
    let mut brace_depth = 0usize;
    while index + 2 < tokens.len() {
        if tokens[index..index + 3] == ["->", "(", ")"]
            && brace_depth == 0
            && tokens
                .get(index + 3)
                .is_some_and(|next| matches!(next.as_str(), "{" | "/" | ";" | "!"))
        {
            tokens.drain(index + 1..index + 3);
            continue;
        }
        if tokens[index..index + 3] == ["/", "{", "}"] && brace_depth == 0 {
            tokens.drain(index..index + 3);
            continue;
        }
        match tokens[index].as_str() {
            "{" => brace_depth += 1,
            "}" => brace_depth = brace_depth.saturating_sub(1),
            _ => {}
        }
        index += 1;
    }
    let mut index = 0;
    while index + 1 < tokens.len() {
        if tokens[index] == "," && matches!(tokens[index + 1].as_str(), ")" | "]") {
            tokens.remove(index);
        } else {
            index += 1;
        }
    }
    tokens
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .unwrap()
}

#[test]
fn formats_repository_language_corpus_without_token_drift() {
    let root = repository_root();
    let files = [root.join("crates/grandiose/src/distributed_std.gr")];

    for file in files {
        let source = std::fs::read_to_string(&file).unwrap();
        let context = grandfmt::Context {
            sources: &[],
            include_distributed_standard_library: false,
            ..grandfmt::Context::default()
        };
        let formatted = grandfmt::format_with_context(&source, context)
            .unwrap_or_else(|error| panic!("{} did not format: {error}", file.display()));
        assert_eq!(
            significant(&source),
            significant(&formatted),
            "token drift in {}",
            file.display()
        );
        let twice = grandfmt::format_with_context(&formatted, context).unwrap();
        if twice != formatted {
            let different = twice
                .bytes()
                .zip(formatted.bytes())
                .position(|(left, right)| left != right)
                .unwrap_or_else(|| twice.len().min(formatted.len()));
            let start = different.saturating_sub(120);
            let left_end = (different + 240).min(twice.len());
            let right_end = (different + 240).min(formatted.len());
            panic!(
                "not idempotent: {}; second near {:?}; first near {:?}",
                file.display(),
                &twice[start..left_end],
                &formatted[start..right_end]
            );
        }
    }
}

#[test]
fn generated_parseable_inputs_are_idempotent_and_token_preserving() {
    // Deterministic cross-product coverage concentrates on trivia at syntax
    // boundaries while keeping every generated program parseable. Merely
    // lexable garbage is intentionally refused by the formatter.
    let gaps = ["", " ", "  ", "\n", "/* nested /* comment */ kept */"];

    for before_parameters in gaps {
        for before_arrow in gaps {
            for before_body in gaps {
                let source = format!(
                    "main{before_parameters}(){before_arrow}->{before_body}() {{\n    ()\n}}"
                );
                let formatted = grandfmt::format(&source)
                    .unwrap_or_else(|error| panic!("parseable input {source:?}: {error}"));
                assert_eq!(
                    significant(&source),
                    significant(&formatted),
                    "input: {source:?}"
                );
                assert_eq!(
                    grandfmt::format(&formatted).unwrap(),
                    formatted,
                    "input: {source:?}"
                );
            }
        }
    }
}

#[test]
fn malformed_inputs_are_rejected_without_panicking() {
    let malformed = [
        "\"unterminated",
        "b\"unterminated",
        "'1",
        "b'unterminated",
        "/* unterminated",
        "/* nested /* still open */",
        "\"trailing escape\\",
        "main( -> () { () }",
        "main() -> () { (] }",
        "not a declaration",
    ];
    for source in malformed {
        let outcome = std::panic::catch_unwind(|| grandfmt::format(source));
        assert!(outcome.is_ok(), "formatter panicked for {source:?}");
        assert!(
            outcome.unwrap().is_err(),
            "malformed input formatted: {source:?}"
        );
    }
}
