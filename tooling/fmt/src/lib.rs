//! Token-based auto-formatter for Grandiose.
//!
//! Deliberately NOT a pretty-printer: it re-lexes the file with trivia
//! (comments, blank lines, the author's line-break decisions) and normalizes
//! indentation, inter-token spacing, blank-line runs, and trailing
//! whitespace. Line-break structure is the author's; spacing and indent are
//! the formatter's. This makes it total (works on any lexable file, even
//! ones that don't parse), safe (the token stream is provably unchanged —
//! verified after every format), and idempotent (verified in tests).
//!
//! Spacing rules are fixed for unambiguous tokens. Tokens whose spacing is
//! grammatically ambiguous at the token level (`<` `>` for generics vs.
//! comparison, `&` `*` `-` `|` `!` `'` for sigil vs. operator) preserve the
//! author's original choice, which keeps the formatter honest without a
//! parse. A future AST-based formatter can tighten these; see
//! docs/tooling-plan.md §3.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Word,
    Number,
    Str,
    LineComment,
    BlockComment,
    Punct,
}

#[derive(Debug, Clone)]
struct Token {
    kind: Kind,
    text: String,
    /// Newlines between the previous token and this one (0 = same line).
    newlines_before: u32,
    /// Whether any whitespace separated this token from the previous one.
    spaced: bool,
}

#[derive(Debug)]
pub struct Error {
    pub offset: usize,
    pub message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{} (byte {})", self.message, self.offset)
    }
}

impl std::error::Error for Error {}

/// Multi-character punctuation, longest first (maximal munch).
const COMPOUND: &[&str] = &["->!", "->", "=>", "::", "==", "!=", "<=", ">=", "&&", "||", ".."];

fn lex(source: &str) -> Result<Vec<Token>, Error> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    let mut newlines = 0u32;
    let mut spaced = false;
    while i < bytes.len() {
        let start = i;
        let b = bytes[i];
        if b == b'\n' {
            newlines += 1;
            spaced = true;
            i += 1;
            continue;
        }
        if b.is_ascii_whitespace() {
            spaced = true;
            i += 1;
            continue;
        }
        let (kind, end) = if b == b'/' && bytes.get(i + 1) == Some(&b'/') {
            let end = source[i..].find('\n').map(|n| i + n).unwrap_or(bytes.len());
            (Kind::LineComment, end)
        } else if b == b'/' && bytes.get(i + 1) == Some(&b'*') {
            let mut depth = 1u32;
            let mut j = i + 2;
            while j < bytes.len() && depth > 0 {
                match (bytes[j], bytes.get(j + 1)) {
                    (b'/', Some(b'*')) => { depth += 1; j += 2; }
                    (b'*', Some(b'/')) => { depth -= 1; j += 2; }
                    _ => j += 1,
                }
            }
            if depth > 0 {
                return Err(Error { offset: start, message: "unterminated block comment".into() });
            }
            (Kind::BlockComment, j)
        } else if b == b'"' {
            let mut j = i + 1;
            loop {
                match bytes.get(j) {
                    None => return Err(Error { offset: start, message: "unterminated string".into() }),
                    Some(b'\\') => j += 2,
                    Some(b'"') => { j += 1; break; }
                    Some(_) => j += 1,
                }
            }
            (Kind::Str, j)
        } else if b.is_ascii_digit() {
            let mut j = i;
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            (Kind::Number, j)
        } else if b.is_ascii_alphabetic() || b == b'_' {
            let mut j = i;
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            (Kind::Word, j)
        } else {
            let rest = &source[i..];
            let compound = COMPOUND.iter().find(|c| rest.starts_with(**c));
            match compound {
                Some(c) => (Kind::Punct, i + c.len()),
                None => (Kind::Punct, i + (rest.chars().next().map(char::len_utf8).unwrap_or(1))),
            }
        };
        tokens.push(Token {
            kind,
            text: source[start..end].to_string(),
            newlines_before: newlines,
            spaced: spaced || newlines > 0,
        });
        newlines = 0;
        spaced = false;
        i = end;
    }
    Ok(tokens)
}

/// Should `current` be preceded by a space when it follows `previous` on the
/// same line?
fn space_between(previous: &Token, current: &Token) -> bool {
    let prev = previous.text.as_str();
    let cur = current.text.as_str();
    // Comments keep breathing room on both sides.
    if matches!(previous.kind, Kind::LineComment | Kind::BlockComment)
        || matches!(current.kind, Kind::LineComment | Kind::BlockComment)
    {
        return true;
    }
    match cur {
        "," | ";" | "." | "::" | ")" | "]" => return false,
        ":" => return false,
        "(" | "[" => {
            // Tight after a callee/name (`name(`, `list[`), spaced after
            // keywords-as-operators and punctuation (`if (`, `, (`).
            return !matches!(previous.kind, Kind::Word | Kind::Number | Kind::Str)
                && !matches!(prev, ")" | "]" | ">");
        }
        "{" | "}" => return true,
        "->" | "->!" | "=>" | "=" | "==" | "!=" | "<=" | ">=" | "&&" | "||" | "+" | "/" | "%" => {
            return true
        }
        // Grammatically ambiguous at token level: keep the author's spacing.
        "<" | ">" | "&" | "*" | "-" | "|" | "!" | "'" | "?" => return current.spaced,
        _ => {}
    }
    match prev {
        "(" | "[" | "." | "::" | "!" | "'" => false,
        "," | ";" | ":" | ")" | "]" | "}" | "{" => true,
        "->" | "->!" | "=>" | "=" | "==" | "!=" | "<=" | ">=" | "&&" | "||" | "+" | "/" | "%" => {
            true
        }
        "<" | ">" | "&" | "*" | "-" | "|" | "?" => current.spaced,
        _ => matches!(current.kind, Kind::Word | Kind::Number | Kind::Str) || cur == "{",
    }
}

/// Format a source file. Total over lexable input; returns `Err` only for
/// unterminated strings/comments (the file is left for the compiler to
/// reject with a proper diagnostic).
pub fn format(source: &str) -> Result<String, Error> {
    let tokens = lex(source)?;
    let mut out = String::with_capacity(source.len());
    let mut depth: i32 = 0;
    for (index, token) in tokens.iter().enumerate() {
        if matches!(token.text.as_str(), "}" | ")" | "]") {
            depth -= 1;
        }
        if index == 0 {
            // No leading blank lines.
        } else if token.newlines_before > 0 {
            for _ in 0..token.newlines_before.min(2) {
                out.push('\n');
            }
            for _ in 0..depth.max(0) {
                out.push_str("    ");
            }
        } else if space_between(&tokens[index - 1], token) {
            out.push(' ');
        }
        out.push_str(&token.text);
        if matches!(token.text.as_str(), "{" | "(" | "[") {
            depth += 1;
        }
    }
    out.push('\n');

    // Paranoia: formatting must never change the token stream.
    let reference: Vec<&str> = tokens.iter().map(|t| t.text.as_str()).collect();
    let formatted = lex(&out).map_err(|e| Error {
        offset: e.offset,
        message: format!("formatter produced unlexable output: {}", e.message),
    })?;
    let produced: Vec<&str> = formatted.iter().map(|t| t.text.as_str()).collect();
    if reference != produced {
        return Err(Error { offset: 0, message: "formatter would alter the token stream; refusing".into() });
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fmt(source: &str) -> String {
        format(source).unwrap()
    }

    #[test]
    fn normalizes_indentation_and_spacing() {
        let input = "main( ) -> i64 {\n  let x=1 ;\n        finish (x , 2)\n}\n";
        let expected = "main() -> i64 {\n    let x = 1;\n    finish(x, 2)\n}\n";
        assert_eq!(fmt(input), expected);
    }

    #[test]
    fn caps_blank_lines_and_strips_leading_ones() {
        let input = "\n\n\na() -> i64 { 1 }\n\n\n\nb() -> i64 { 2 }\n";
        assert_eq!(fmt(input), "a() -> i64 { 1 }\n\nb() -> i64 { 2 }\n");
    }

    #[test]
    fn preserves_comments_and_strings_verbatim() {
        let input = "// keep   my    spacing\nmain() -> i64 {\n    /* block /* nested */ ok */ print(\"a  {  b\")\n    0 // trailing note\n}\n";
        let output = fmt(input);
        assert!(output.contains("// keep   my    spacing"), "{output}");
        assert!(output.contains("/* block /* nested */ ok */"), "{output}");
        assert!(output.contains("\"a  {  b\""), "{output}");
        assert!(output.contains("0 // trailing note"), "{output}");
        assert_eq!(fmt(&output), output);
    }

    #[test]
    fn idempotent_on_a_realistic_file() {
        let input = "// Entry point.\nstruct Pair { left: i32, right: i32 }\n\
                     enum Message { Quit, Move(i32, i32) }\n\
                     effect Console { [1,1] write_line(text: &str) ->; }\n\
                     add<T>(lhs: T, rhs: i64) -> i64 / {Console} {\n\
                     handle (lhs) { Console::write_line(text) with k => resume(k, ()) }\n\
                     }\n\
                     main() -> i64 {\n    let pair = Pair { left: 40, right: 2 }\n    pair.left + add(1, 2)\n}\n";
        let once = fmt(input);
        assert_eq!(fmt(&once), once, "not idempotent");
    }

    #[test]
    fn generics_and_sigils_keep_author_spacing() {
        // `T<U>` stays tight; `a < b` stays spaced; `&str` stays tight.
        let input = "f(x: List<i64>, y: &str) -> i64 {\n    x < 3\n}\n";
        let output = fmt(input);
        assert!(output.contains("List<i64>"), "{output}");
        assert!(output.contains("&str"), "{output}");
        assert!(output.contains("x < 3"), "{output}");
        assert_eq!(fmt(&output), output);
    }

    #[test]
    fn rejects_unterminated_input() {
        assert!(format("main() -> i64 { \"oops\n").is_err());
        assert!(format("/* never closed").is_err());
    }
}
