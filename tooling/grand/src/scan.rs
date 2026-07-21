//! Heuristic top-level declaration scanner.
//!
//! Stand-in for the compiler's `--emit interfaces-json` (docs/compiler-
//! changes-for-tooling.md item 4): good enough to power cross-package
//! collision *warnings* and the fake compiler's interface emission, and
//! precisely because it is a heuristic, its findings are never hard errors —
//! only the real compiler's interface scan is (see ops::preflight).
//!
//! It tracks brace/paren/bracket depth (string- and comment-aware; comments
//! per the spec: `//` line and nested `/* */` block) and classifies
//! declarations only at depth zero.

use std::path::Path;

use crate::contract::{Declaration, DeclarationKind};

pub fn scan(file: &Path, text: &str) -> Vec<Declaration> {
    let mut declarations = Vec::new();
    let mut depth = 0i64;
    let mut comment_depth = 0u32;
    let mut pending_docs: Vec<String> = Vec::new();
    for (index, line) in text.lines().enumerate() {
        if depth == 0 && comment_depth == 0 {
            let trimmed = line.trim();
            if let Some(comment) = trimmed.strip_prefix("//") {
                pending_docs.push(comment.trim().to_string());
                continue;
            }
            if let Some(mut declaration) = classify(file, index + 1, line) {
                if !pending_docs.is_empty() {
                    declaration.docs = Some(pending_docs.join("\n"));
                }
                declarations.push(declaration);
            }
            pending_docs.clear();
        }
        advance(line, &mut depth, &mut comment_depth);
    }
    declarations
}

/// Update nesting depth across one line, skipping strings and comments.
fn advance(line: &str, depth: &mut i64, comment_depth: &mut u32) {
    let bytes = line.as_bytes();
    let mut i = 0;
    let mut in_string = false;
    while i < bytes.len() {
        let (current, next) = (bytes[i], bytes.get(i + 1).copied());
        if *comment_depth > 0 {
            match (current, next) {
                (b'*', Some(b'/')) => { *comment_depth -= 1; i += 2; continue; }
                (b'/', Some(b'*')) => { *comment_depth += 1; i += 2; continue; }
                _ => { i += 1; continue; }
            }
        }
        if in_string {
            match current {
                b'\\' => i += 2,
                b'"' => { in_string = false; i += 1; }
                _ => i += 1,
            }
            continue;
        }
        match (current, next) {
            (b'/', Some(b'/')) => return,
            (b'/', Some(b'*')) => { *comment_depth += 1; i += 2; }
            (b'"', _) => { in_string = true; i += 1; }
            (b'{' | b'(' | b'[', _) => { *depth += 1; i += 1; }
            (b'}' | b')' | b']', _) => { *depth -= 1; i += 1; }
            _ => i += 1,
        }
    }
}

fn classify(file: &Path, line_number: usize, line: &str) -> Option<Declaration> {
    let trimmed = line.trim_start();
    let (word, rest) = ident(trimmed)?;
    let declaration = |name: &str, kind| {
        Some(Declaration {
            name: name.to_string(),
            kind,
            file: file.to_path_buf(),
            line: line_number,
            signature: None,
            docs: None,
        })
    };
    match word {
        "struct" | "enum" | "effect" | "trait" | "type" => {
            let kind = match word {
                "struct" => DeclarationKind::Struct,
                "enum" => DeclarationKind::Enum,
                "effect" => DeclarationKind::Effect,
                "trait" => DeclarationKind::Trait,
                _ => DeclarationKind::Type,
            };
            declaration(ident(rest.trim_start())?.0, kind)
        }
        "let" => declaration(ident(rest.trim_start())?.0, DeclarationKind::Global),
        "infixl" | "infixr" | "infix" | "prefix" => {
            let name = rest.split_whitespace().last()?.trim_end_matches(';');
            declaration(name, DeclarationKind::Fixity)
        }
        // impl blocks and handler-style statements are not named declarations.
        "impl" | "handle" | "perform" | "resume" | "cancel" | "use" => None,
        // A top-level identifier followed by `(` or `<` is a callable head.
        _ => match rest.trim_start().as_bytes().first() {
            Some(b'(' | b'<') => {
                let signature = trimmed.split('{').next().map(|s| s.trim().to_string());
                let mut result = declaration(word, DeclarationKind::Callable);
                if let Some(declaration) = &mut result {
                    declaration.signature = signature;
                }
                result
            }
            _ => None,
        },
    }
}

/// Split a leading `[A-Za-z_][A-Za-z0-9_]*` identifier off `text`.
fn ident(text: &str) -> Option<(&str, &str)> {
    let bytes = text.as_bytes();
    if !matches!(bytes.first()?, b'a'..=b'z' | b'A'..=b'Z' | b'_') {
        return None;
    }
    let end = bytes
        .iter()
        .position(|b| !matches!(b, b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_'))
        .unwrap_or(bytes.len());
    Some((&text[..end], &text[end..]))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scans_top_level_declarations_only() {
        let source = "\
struct Pair { left: i32, right: i32 }
enum Message { Quit, Move(i32, i32) }
type Alias<T> = Result<T, ()>;
let answer = 42;
infixr 1 else;
effect Console { [1,1] write_line(text: &str) ->; }
// commented() -> i64 { 0 }
/* nested /* block */ hidden() -> i64 { 0 } */
add(lhs: i64, rhs: i64) -> i64 {
    inner() -> i64 { 0 }
    lhs + rhs
}
generic<T>(value: T) -> T { value }
impl Drop for Pair { drop(&mut self) -> { } }
";
        let declarations = scan(Path::new("test.gr"), source);
        let names: Vec<(&str, DeclarationKind)> =
            declarations.iter().map(|d| (d.name.as_str(), d.kind)).collect();
        assert_eq!(
            names,
            vec![
                ("Pair", DeclarationKind::Struct),
                ("Message", DeclarationKind::Enum),
                ("Alias", DeclarationKind::Type),
                ("answer", DeclarationKind::Global),
                ("else", DeclarationKind::Fixity),
                ("Console", DeclarationKind::Effect),
                ("add", DeclarationKind::Callable),
                ("generic", DeclarationKind::Callable),
            ]
        );
        assert_eq!(declarations[6].signature.as_deref(), Some("add(lhs: i64, rhs: i64) -> i64"));
        assert_eq!(declarations[6].line, 9);
    }

    #[test]
    fn braces_in_strings_do_not_change_depth() {
        let source = "greet() -> i64 {\n    print(\"{ \\\" }\")\n}\nafter() -> i64 { 0 }\n";
        let names: Vec<String> = scan(Path::new("t.gr"), source).into_iter().map(|d| d.name).collect();
        assert_eq!(names, vec!["greet", "after"]);
    }
}
