//! Syntax-aware, deterministic formatter for Grandiose.
//!
//! The compiler's semantic parser is the authority for whether input is
//! formatable and for source-declared operator fixity. The lossless lexer owns
//! comment text and exact token spellings. Formatting lowers that shared
//! syntax into a small Wadler-style document algebra and lays groups out at the
//! language's fixed 100-column width. A final parse and token-equivalence gate
//! makes every rewrite fail closed.

use std::collections::BTreeSet;

use grandiose::interface::{InterfaceSelection, scan_interfaces};
use grandiose::lossless::{LosslessKind, lex_lossless};
use grandiose::source_bundle::{Segment, SourceBundle};

const WIDTH: usize = 100;
const INDENT: usize = 4;
const FORMAT_SOURCE: &str = "<grandfmt:input>";

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Kind {
    Word,
    Number,
    String,
    LineComment,
    BlockComment,
    Punctuation,
}

#[derive(Debug, Clone)]
struct Token {
    kind: Kind,
    text: String,
    start: usize,
    newlines_before: u32,
    spaced: bool,
}

#[derive(Debug)]
pub struct Error {
    pub offset: usize,
    pub message: String,
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(formatter, "{} (byte {})", self.message, self.offset)
    }
}

impl std::error::Error for Error {}

/// Additional ordered source entries whose declarations (most importantly
/// fixities) participate in parsing, but which are not themselves formatted.
#[derive(Clone, Copy, Debug)]
pub struct Context<'source> {
    /// Physical/logical name of the source being formatted. Module-aware
    /// formatting requires the same path used by compiler module discovery.
    pub source_name: &'source str,
    /// Crate root when formatting one of its external module files. Omit this
    /// when the formatted source itself is the crate root.
    pub crate_root: Option<(&'source str, &'source str)>,
    pub sources: &'source [(&'source str, &'source str)],
    /// Explicit dependency package roots `(manifest name, path, source)`.
    pub dependencies: &'source [(&'source str, &'source str, &'source str)],
    /// User files see the distributed prelude. The prelude's own source file
    /// disables this to avoid parsing a second embedded copy of itself.
    pub include_distributed_standard_library: bool,
}

impl Default for Context<'_> {
    fn default() -> Self {
        Self {
            source_name: FORMAT_SOURCE,
            crate_root: None,
            sources: &[],
            dependencies: &[],
            include_distributed_standard_library: true,
        }
    }
}

#[derive(Clone, Debug)]
enum Doc {
    Empty,
    Text(String),
    Space,
    /// Space when flat, newline when broken.
    SoftLine,
    /// Nothing when flat, newline when broken.
    SoftBreak,
    HardLine,
    Concat(Vec<Doc>),
    Nest(usize, Box<Doc>),
    Group(Box<Doc>),
}

impl Doc {
    fn concat(parts: impl IntoIterator<Item = Doc>) -> Doc {
        let parts = parts
            .into_iter()
            .filter(|part| !matches!(part, Doc::Empty))
            .collect::<Vec<_>>();
        match parts.len() {
            0 => Doc::Empty,
            1 => parts.into_iter().next().unwrap(),
            _ => Doc::Concat(parts),
        }
    }

    fn group(self) -> Doc {
        Doc::Group(Box::new(self))
    }

    fn nest(self, amount: usize) -> Doc {
        Doc::Nest(amount, Box::new(self))
    }
}

fn lex(source: &str) -> Result<Vec<Token>, Error> {
    let lossless = lex_lossless(source).map_err(error_from_diagnostic)?;
    let mut tokens = Vec::new();
    let mut newlines = 0u32;
    let mut spaced = false;
    for token in lossless {
        let text = token.text(source);
        if token.kind == LosslessKind::Whitespace {
            newlines =
                newlines.saturating_add(text.bytes().filter(|byte| *byte == b'\n').count() as u32);
            spaced = true;
            continue;
        }
        let kind = match token.kind {
            LosslessKind::LineComment => Kind::LineComment,
            LosslessKind::BlockComment => Kind::BlockComment,
            LosslessKind::Identifier | LosslessKind::Lifetime | LosslessKind::Label => Kind::Word,
            LosslessKind::Number => Kind::Number,
            LosslessKind::String
            | LosslessKind::Character
            | LosslessKind::ByteString
            | LosslessKind::ByteCharacter => Kind::String,
            LosslessKind::Punctuation => Kind::Punctuation,
            LosslessKind::Whitespace => unreachable!("whitespace was consumed above"),
        };
        tokens.push(Token {
            kind,
            text: text.to_string(),
            start: token.span.start,
            newlines_before: newlines,
            spaced: spaced || newlines > 0,
        });
        newlines = 0;
        spaced = false;
    }
    Ok(tokens)
}

fn error_from_diagnostic(diagnostic: grandiose::diagnostic::Diagnostic) -> Error {
    Error {
        offset: diagnostic.span.map_or(0, |span| span.start),
        message: if diagnostic.message.is_empty() {
            diagnostic.title
        } else {
            format!("{}: {}", diagnostic.title, diagnostic.message)
        },
    }
}

fn bundle(source: &str, context: Context<'_>) -> SourceBundle {
    let target = Segment::new(context.source_name, source);
    let ordinary = context
        .sources
        .iter()
        .map(|(name, source)| Segment::new(*name, *source));
    let dependencies = context
        .dependencies
        .iter()
        .map(|(package, name, source)| Segment::new(*name, *source).with_package_root(*package));
    let additional = context
        .crate_root
        .is_some()
        .then_some(target)
        .into_iter()
        .chain(ordinary)
        .chain(dependencies);
    let primary = context.crate_root.map_or_else(
        || Segment::new(context.source_name, source),
        |(name, source)| Segment::new(name, source),
    );
    if context.include_distributed_standard_library {
        SourceBundle::distributed(primary, additional)
    } else {
        SourceBundle::raw_for_conformance(
            Segment::new("<grandfmt:no-std>", ""),
            primary,
            additional,
        )
    }
}

fn analyze(source: &str, context: Context<'_>) -> Result<BTreeSet<usize>, Error> {
    let bundle = bundle(source, context);
    let declarations =
        scan_interfaces(&bundle, InterfaceSelection::User).map_err(|diagnostics| {
            let diagnostic = &diagnostics[0];
            let offset = diagnostic
                .span
                .and_then(|span| bundle.map_span(span))
                .filter(|mapped| mapped.segment.name() == context.source_name)
                .map_or(0, |mapped| mapped.span.start);
            Error {
                offset,
                message: if diagnostic.message.is_empty() {
                    diagnostic.title.clone()
                } else {
                    format!("{}: {}", diagnostic.title, diagnostic.message)
                },
            }
        })?;
    Ok(declarations
        .into_iter()
        .filter(|declaration| declaration.file == context.source_name)
        .map(|declaration| declaration_layout_start(source, declaration.declaration_start_byte))
        .collect())
}

fn declaration_layout_start(source: &str, declaration: usize) -> usize {
    let before = &source[..declaration.min(source.len())];
    let trimmed = before.trim_end_matches(char::is_whitespace);
    let boundary = trimmed
        .strip_suffix("pub")
        .filter(|prefix| {
            prefix
                .chars()
                .next_back()
                .is_none_or(|character| !character.is_alphanumeric() && character != '_')
        })
        .map_or(declaration, |prefix| prefix.len());
    leading_comment_start(source, boundary)
}

fn leading_comment_start(source: &str, declaration: usize) -> usize {
    let mut boundary = declaration.min(source.len());
    loop {
        let before = &source[..boundary];
        let line_end = before.trim_end_matches([' ', '\t', '\r', '\n']).len();
        if line_end == 0 {
            break;
        }
        let line_start = source[..line_end]
            .rfind('\n')
            .map_or(0, |offset| offset + 1);
        if !source[line_start..line_end].trim_start().starts_with("//") {
            break;
        }
        boundary = line_start;
    }
    boundary
}

fn normalize(tokens: &mut Vec<Token>) {
    let mut index = 0;
    let mut brace_depth = 0usize;
    while index + 2 < tokens.len() {
        let triple = (
            tokens[index].text.as_str(),
            tokens[index + 1].text.as_str(),
            tokens[index + 2].text.as_str(),
        );
        if triple == ("->", "(", ")")
            && brace_depth == 0
            && !is_comment(&tokens[index + 1])
            && !is_comment(&tokens[index + 2])
            && tokens
                .get(index + 3)
                .is_some_and(|next| matches!(next.text.as_str(), "{" | "/" | ";" | "!"))
        {
            tokens.drain(index + 1..=index + 2);
            continue;
        }
        if triple == ("/", "{", "}")
            && brace_depth == 0
            && !is_comment(&tokens[index + 1])
            && !is_comment(&tokens[index + 2])
        {
            tokens.drain(index..=index + 2);
            continue;
        }
        match tokens[index].text.as_str() {
            "{" => brace_depth += 1,
            "}" => brace_depth = brace_depth.saturating_sub(1),
            _ => {}
        }
        index += 1;
    }
    remove_redundant_trailing_commas(tokens);
}

/// The renderer used to add a trailing comma whenever a parenthesized group
/// broke. Remove those grammar-neutral commas from multi-item groups while
/// preserving the one-element tuple spelling `(value,)`.
fn remove_redundant_trailing_commas(tokens: &mut Vec<Token>) {
    let mut index = 0;
    while index + 1 < tokens.len() {
        if tokens[index].text != "," || !matches!(tokens[index + 1].text.as_str(), ")" | "]") {
            index += 1;
            continue;
        }
        let close = tokens[index + 1].text.as_str();
        let open = if close == ")" { "(" } else { "[" };
        let mut depth = 0usize;
        let mut opening = None;
        for candidate in (0..index).rev() {
            match tokens[candidate].text.as_str() {
                text if text == close => depth += 1,
                text if text == open && depth > 0 => depth -= 1,
                text if text == open => {
                    opening = Some(candidate);
                    break;
                }
                _ => {}
            }
        }
        let Some(opening) = opening else {
            index += 1;
            continue;
        };
        let mut nested = 0usize;
        let has_separator = tokens[opening + 1..index].iter().any(|token| {
            match token.text.as_str() {
                "(" | "[" | "{" => nested += 1,
                ")" | "]" | "}" => nested = nested.saturating_sub(1),
                "," if nested == 0 => return true,
                _ => {}
            }
            false
        });
        if has_separator {
            tokens.remove(index);
        } else {
            index += 1;
        }
    }
}

fn is_comment(token: &Token) -> bool {
    matches!(token.kind, Kind::LineComment | Kind::BlockComment)
}

struct DocumentBuilder<'tokens> {
    tokens: &'tokens [Token],
    cursor: usize,
    declarations: &'tokens BTreeSet<usize>,
}

impl<'tokens> DocumentBuilder<'tokens> {
    fn build(mut self) -> Doc {
        self.sequence(None, true).0
    }

    fn sequence(&mut self, close: Option<&str>, top_level: bool) -> (Doc, bool) {
        let mut parts = Vec::new();
        let mut previous: Option<Token> = None;
        let mut had_comma = false;
        while let Some(token) = self.tokens.get(self.cursor).cloned() {
            if close == Some(token.text.as_str()) {
                break;
            }
            if let Some(previous) = &previous {
                parts.push(self.separator(previous, &token, top_level));
            }
            let generic = token.text == "<" && self.is_generic_open(self.cursor);
            if let Some(expected) = matching_close(&token.text).or(generic.then_some(">")) {
                self.cursor += 1;
                let inner_start = self.cursor;
                let (inner, inner_had_comma) = self.sequence(Some(expected), false);
                let closed = self
                    .tokens
                    .get(self.cursor)
                    .is_some_and(|candidate| candidate.text == expected);
                if !closed {
                    // Semantic parsing already rejected this path, but retain a
                    // total builder if a future recovery parser admits it.
                    parts.push(Doc::Text(token.text.clone()));
                    parts.push(inner);
                    previous = Some(token);
                    continue;
                }
                self.cursor += 1;
                let open = token.text.clone();
                let close_text = expected.to_string();
                let force_block = open == "{"
                    && (self.tokens[inner_start..self.cursor.saturating_sub(1)]
                        .iter()
                        .any(|token| token.text == ";")
                        || self
                            .tokens
                            .get(self.cursor)
                            .is_some_and(|token| token.text == "else"));
                let boundary = if force_block {
                    Doc::HardLine
                } else if open == "{" {
                    Doc::SoftLine
                } else {
                    Doc::SoftBreak
                };
                let _ = inner_had_comma;
                let trailing = Doc::Empty;
                let delimited = if matches!(inner, Doc::Empty) {
                    Doc::concat([Doc::Text(open), Doc::Text(close_text)])
                } else {
                    Doc::concat([
                        Doc::Text(open),
                        Doc::concat([boundary.clone(), inner, trailing]).nest(INDENT),
                        boundary,
                        Doc::Text(close_text),
                    ])
                    .group()
                };
                parts.push(delimited);
                previous = Some(Token {
                    text: expected.to_string(),
                    ..token
                });
                continue;
            }
            had_comma |= token.text == ",";
            parts.push(Doc::Text(token.text.clone()));
            self.cursor += 1;
            if token.kind == Kind::LineComment {
                parts.push(Doc::HardLine);
                previous = None;
            } else {
                previous = Some(token);
            }
        }
        (Doc::concat(parts), had_comma)
    }

    fn separator(&self, previous: &Token, current: &Token, top_level: bool) -> Doc {
        if previous.text == "pub" {
            return Doc::Space;
        }
        if previous.text == ";" {
            return Doc::HardLine;
        }
        if top_level
            && self.declarations.contains(&current.start)
            && previous.start != current.start
        {
            return Doc::concat([Doc::HardLine, Doc::HardLine]);
        }
        if top_level
            && current.newlines_before > 0
            && matches!(
                current.text.as_str(),
                "type"
                    | "struct"
                    | "enum"
                    | "trait"
                    | "impl"
                    | "effect"
                    | "infix"
                    | "infixl"
                    | "infixr"
                    | "prefix"
                    | "let"
            )
        {
            return Doc::concat([Doc::HardLine, Doc::HardLine]);
        }
        if current.kind == Kind::LineComment {
            return if current.newlines_before > 0 {
                Doc::HardLine
            } else {
                Doc::Space
            };
        }
        if current.kind == Kind::BlockComment || previous.kind == Kind::BlockComment {
            return if current.newlines_before > 0 {
                Doc::HardLine
            } else {
                Doc::Space
            };
        }
        if previous.text == "}"
            && !matches!(current.text.as_str(), "else" | "with")
            && self.starts_callable_declaration(self.cursor)
        {
            return Doc::concat([Doc::HardLine, Doc::HardLine]);
        }
        if current.text == "<" && self.is_generic_open(self.cursor) {
            return Doc::Empty;
        }
        match current.text.as_str() {
            "," | ";" | ")" | "]" | "}" | "." | "::" => return Doc::Empty,
            ":" => {
                return if previous.text == ":" && current.spaced {
                    Doc::Space
                } else {
                    Doc::Empty
                };
            }
            "(" | "[" => {
                return if previous.text == "is" {
                    Doc::Space
                } else if matches!(previous.kind, Kind::Word | Kind::Number | Kind::String)
                    || matches!(previous.text.as_str(), ")" | "]" | ">")
                {
                    Doc::Empty
                } else {
                    Doc::Space
                };
            }
            _ => {}
        }
        match previous.text.as_str() {
            "." | "::" | "(" | "[" => Doc::Empty,
            "," => Doc::SoftLine,
            ":" => Doc::Space,
            _ if self.is_prefix_operator(self.cursor.saturating_sub(1)) => Doc::Empty,
            _ if operator(previous) && operator(current) && !current.spaced => Doc::Empty,
            _ if operator(previous) || operator(current) => Doc::Space,
            _ if word_like(previous) && word_like(current) => Doc::Space,
            _ if current.newlines_before > 1 => Doc::HardLine,
            _ if current.spaced => Doc::Space,
            _ => Doc::Empty,
        }
    }

    fn starts_callable_declaration(&self, index: usize) -> bool {
        let Some(current) = self.tokens.get(index) else {
            return false;
        };
        if current.text == "pub" {
            return self.starts_callable_declaration(index + 1);
        }
        if current.kind != Kind::Word {
            return false;
        }
        self.tokens
            .get(index + 1)
            .is_some_and(|next| next.text == "(" || next.text == "<")
    }

    fn is_generic_open(&self, index: usize) -> bool {
        let Some(previous) = index
            .checked_sub(1)
            .and_then(|index| self.tokens.get(index))
        else {
            return false;
        };
        if previous.kind != Kind::Word {
            return false;
        }
        let mut depth = 0usize;
        let mut close = None;
        for candidate in index..self.tokens.len() {
            match self.tokens[candidate].text.as_str() {
                "<" => depth += 1,
                ">" if depth > 1 => depth -= 1,
                ">" => {
                    close = Some(candidate);
                    break;
                }
                ";" | "{" | "}" if depth == 1 => break,
                _ => {}
            }
        }
        let Some(close) = close else {
            return false;
        };
        let before = index
            .checked_sub(2)
            .and_then(|index| self.tokens.get(index))
            .map(|token| token.text.as_str());
        let after = self.tokens.get(close + 1).map(|token| token.text.as_str());
        previous.text.chars().next().is_some_and(char::is_uppercase)
            || matches!(
                before,
                Some(
                    ":" | "->"
                        | ","
                        | "("
                        | "["
                        | "<"
                        | "="
                        | "where"
                        | "type"
                        | "for"
                        | "impl"
                        | "as"
                        | "::"
                )
            )
            || matches!(after, Some("(" | "::"))
    }

    fn is_prefix_operator(&self, index: usize) -> bool {
        let Some(token) = self.tokens.get(index) else {
            return false;
        };
        if !matches!(token.text.as_str(), "&" | "*" | "!" | "-" | "+") {
            return false;
        }
        let Some(previous) = index
            .checked_sub(1)
            .and_then(|index| self.tokens.get(index))
        else {
            return true;
        };
        matches!(
            previous.text.as_str(),
            "(" | "[" | "{" | "," | ";" | ":" | "=" | "->" | "=>" | "/" | "&" | "*"
        ) || matches!(
            previous.text.as_str(),
            "let" | "return" | "move" | "is" | "perform" | "resume" | "tail"
        )
    }
}

fn matching_close(open: &str) -> Option<&'static str> {
    match open {
        "(" => Some(")"),
        "[" => Some("]"),
        "{" => Some("}"),
        _ => None,
    }
}

fn word_like(token: &Token) -> bool {
    matches!(token.kind, Kind::Word | Kind::Number | Kind::String)
}

fn operator(token: &Token) -> bool {
    token.kind == Kind::Punctuation
        && !matches!(
            token.text.as_str(),
            "(" | ")" | "[" | "]" | "{" | "}" | "," | ";" | ":" | "." | "::"
        )
}

fn flat_width(doc: &Doc) -> Option<usize> {
    match doc {
        Doc::Empty => Some(0),
        Doc::Text(text) => Some(text.chars().count()),
        Doc::Space | Doc::SoftLine => Some(1),
        Doc::SoftBreak => Some(0),
        Doc::HardLine => None,
        Doc::Concat(parts) => parts.iter().try_fold(0usize, |width, part| {
            flat_width(part).map(|part| width.saturating_add(part))
        }),
        Doc::Nest(_, content) | Doc::Group(content) => flat_width(content),
    }
}

struct Renderer {
    output: String,
    column: usize,
}

impl Renderer {
    fn render(mut self, doc: &Doc) -> String {
        self.doc(doc, 0, false);
        while self.output.ends_with([' ', '\t', '\n']) {
            self.output.pop();
        }
        self.output.push('\n');
        self.output
    }

    fn doc(&mut self, doc: &Doc, indent: usize, flat: bool) {
        match doc {
            Doc::Empty => {}
            Doc::Text(text) => {
                self.output.push_str(text);
                self.column += text.chars().count();
            }
            Doc::Space => self.space(),
            Doc::SoftLine => {
                if flat {
                    self.space();
                } else {
                    self.newline(indent);
                }
            }
            Doc::SoftBreak => {
                if !flat {
                    self.newline(indent);
                }
            }
            Doc::HardLine => self.newline(indent),
            Doc::Concat(parts) => {
                for part in parts {
                    self.doc(part, indent, flat);
                }
            }
            Doc::Nest(amount, content) => self.doc(content, indent + amount, flat),
            Doc::Group(content) => {
                let fits = flat_width(content)
                    .is_some_and(|width| self.column.saturating_add(width) <= WIDTH);
                self.doc(content, indent, flat || fits);
            }
        }
    }

    fn space(&mut self) {
        if !self.output.ends_with([' ', '\n']) {
            self.output.push(' ');
            self.column += 1;
        }
    }

    fn newline(&mut self, indent: usize) {
        while self.output.ends_with(' ') {
            self.output.pop();
        }
        self.output.push('\n');
        self.output.extend(std::iter::repeat_n(' ', indent));
        self.column = indent;
    }
}

fn canonical_tokens(source: &str) -> Result<Vec<String>, Error> {
    let mut tokens = lex(source)?;
    normalize(&mut tokens);
    let mut result = Vec::new();
    for (index, token) in tokens.iter().enumerate() {
        // A trailing comma introduced only in broken layout is grammar-neutral.
        if token.text == ","
            && tokens
                .get(index + 1)
                .is_some_and(|next| matches!(next.text.as_str(), ")" | "]"))
        {
            continue;
        }
        result.push(token.text.clone());
    }
    Ok(result)
}

/// Format one source entry using only its own and the embedded standard
/// library's fixity declarations.
pub fn format(source: &str) -> Result<String, Error> {
    format_with_context(source, Context::default())
}

/// Format one source entry in the fixity/declaration context of an ordered
/// resolved bundle.
pub fn format_with_context(source: &str, context: Context<'_>) -> Result<String, Error> {
    let declarations = analyze(source, context)?;
    let mut tokens = lex(source)?;
    normalize(&mut tokens);
    let document = DocumentBuilder {
        tokens: &tokens,
        cursor: 0,
        declarations: &declarations,
    }
    .build();
    let output = Renderer {
        output: String::with_capacity(source.len()),
        column: 0,
    }
    .render(&document);

    // Refuse any rewrite that the real parser does not accept under the same
    // fixity context or that changes a non-trivia token outside the two frozen
    // spec normalizations and grammar-neutral trailing commas.
    analyze(&output, context).map_err(|error| {
        let local = error.offset.min(output.len());
        let mut start = local.saturating_sub(80);
        let mut end = (local + 80).min(output.len());
        while !output.is_char_boundary(start) {
            start += 1;
        }
        while !output.is_char_boundary(end) {
            end -= 1;
        }
        Error {
            offset: error.offset,
            message: format!(
                "formatter produced invalid syntax: {}; near {:?}",
                error.message,
                &output[start..end]
            ),
        }
    })?;
    if canonical_tokens(source)? != canonical_tokens(&output)? {
        return Err(Error {
            offset: 0,
            message: "formatter would alter semantic tokens; refusing".into(),
        });
    }
    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn formatted(source: &str) -> String {
        format(source).unwrap()
    }

    #[test]
    fn normalizes_signatures_spacing_and_indentation() {
        let input = "main( ) -> () {\n  let x=1 ;\n        finish (x , 2)\n}\n";
        let expected = "main() -> {\n    let x = 1;\n    finish(x, 2)\n}\n";
        assert_eq!(formatted(input), expected);
    }

    #[test]
    fn wraps_structured_groups_at_the_fixed_width() {
        let source = "very_long_callable(first_parameter: ExtremelyLongNominalType, second_parameter: AnotherExtremelyLongNominalType, third_parameter: FinalExtremelyLongNominalType) -> () { () }";
        let output = formatted(source);
        assert!(output.contains("\n    first_parameter"), "{output}");
        assert!(output.lines().all(|line| line.chars().count() <= WIDTH));
        assert!(output.contains(",\n    third_parameter"), "{output}");
    }

    #[test]
    fn keeps_comments_verbatim_and_anchored() {
        let source = "// public   docs\nmain() -> () {\n    value /* exact   block */ // tail\n}\n";
        let output = formatted(source);
        assert!(output.starts_with("// public   docs\nmain"), "{output}");
        assert!(output.contains("/* exact   block */ // tail"), "{output}");
        assert_eq!(formatted(&output), output);
    }

    #[test]
    fn refuses_lexical_and_parse_errors() {
        for source in [
            "main() -> () { \"oops",
            "/* never closed",
            "main( -> () { () }",
            "main() -> () { (] }",
        ] {
            assert!(format(source).is_err(), "formatted invalid {source:?}");
        }
    }

    #[test]
    fn external_fixity_context_is_parsed_authoritatively() {
        let source = "main() -> () { 1 <*> 2; () }";
        assert!(format(source).is_err());
        let context_source = "infixl 40 <*>; helper(lhs: i64, rhs: i64) -> i64 { lhs }";
        let output = format_with_context(
            source,
            Context {
                sources: &[("operators.glorious", context_source)],
                ..Context::default()
            },
        )
        .unwrap();
        assert!(output.contains("1 <*> 2"), "{output}");
    }

    #[test]
    fn external_module_formatting_uses_crate_paths_imported_fixities_and_privacy() {
        let root = "pub mod ops; pub mod consumer; main()->{()}";
        let ops =
            "pub infixl 5 join; pub join(left:i64,right:i64)->i64{left-right} private()->{()}";
        let source = "use crate::ops::join; pub calculate()->i64{1 join 2*3}";
        let context = Context {
            source_name: "/work/src/consumer/consumer.glorious",
            crate_root: Some(("/work/src/main.glorious", root)),
            sources: &[("/work/src/ops/ops.glorious", ops)],
            ..Context::default()
        };
        let output = format_with_context(source, context).unwrap();
        assert!(output.contains("use crate::ops::join;"), "{output}");
        assert!(output.contains("1 join 2 * 3"), "{output}");
        assert_eq!(format_with_context(&output, context).unwrap(), output);

        let private_source = "use crate::ops::private; pub bad()->{private()}";
        let error = format_with_context(private_source, context).unwrap_err();
        assert!(error.message.contains("private"), "{error}");
    }

    #[test]
    fn formatter_context_preserves_explicit_dependency_roots() {
        let source = "use cool_pkg::answer; main()->i64{answer()}";
        let context = Context {
            source_name: "/work/app/main.glorious",
            dependencies: &[(
                "cool-pkg",
                "/deps/cool/src/lib.glorious",
                "pub answer()->i64{42}",
            )],
            ..Context::default()
        };
        let output = format_with_context(source, context).unwrap();
        assert!(output.contains("use cool_pkg::answer;"), "{output}");
        assert_eq!(format_with_context(&output, context).unwrap(), output);
    }

    #[test]
    fn spec_normalizations_are_safe_and_idempotent() {
        let source = "main() -> () / {} { () }";
        let once = formatted(source);
        assert_eq!(once, "main() -> { () }\n");
        assert_eq!(formatted(&once), once);
    }

    #[test]
    fn does_not_apply_signature_normalizations_inside_expressions() {
        let source = "main() -> () { 1 / {}; () }";
        let output = formatted(source);
        assert!(output.contains("1 / {}"), "{output}");
        assert_eq!(formatted(&output), output);
    }

    #[test]
    fn preserves_pattern_remainders_and_implicit_omissions() {
        let source = "main() -> { value is Packet::Data(first,..,last); value is (first,); value is Point { x }; () }";
        let output = formatted(source);
        assert!(output.contains("Packet::Data(first, .., last)"), "{output}");
        assert!(output.contains("value is (first,)"), "{output}");
        assert!(output.contains("Point { x }"), "{output}");
        assert_eq!(formatted(&output), output);
    }

    #[test]
    fn keeps_visibility_generics_and_prefix_operators_canonical() {
        let source = "pub struct Holder<T>{private value:T}\n\
                      pub parse<T,E>(value:& mut Holder<T>,tape:& Holder<T>)->Result<T,E>{\n\
                          let shared=&* tape;\n\
                          let field=& tape.value;\n\
                          Result::Ok(* shared)\n\
                      }";
        let output = formatted(source);
        assert!(output.contains("pub struct Holder<T>"), "{output}");
        assert!(output.contains("pub parse<T, E>"), "{output}");
        assert!(output.contains("&mut Holder<T>"), "{output}");
        assert!(output.contains("tape: &Holder<T>"), "{output}");
        assert!(output.contains("Result<T, E>"), "{output}");
        assert!(output.contains("&*tape"), "{output}");
        assert!(output.contains("&tape.value"), "{output}");
        assert!(output.contains("Result::Ok(*shared)"), "{output}");
        assert!(!output.contains("pub\n"), "{output}");
        assert!(!output.contains(",)"), "{output}");
        assert_eq!(formatted(&output), output);
    }
}
