//! Immutable source products, lossless lexing, and delimiter-safe spans.
//!
//! The lexer never reads a path. Its input is a source blob already validated
//! and owned by a request world, making source identity and diagnostics stable
//! across working directories and filesystem races.

use crate::identity::{Digest, FileKey};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Span {
    pub file: FileKey,
    pub start: u32,
    pub end: u32,
}

/// A byte-offset to editor-position index owned by one immutable source blob.
/// The compiler continues to store byte spans, while LSP-facing consumers can
/// obtain deterministic UTF-16 positions without reparsing or re-reading it.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LineIndex {
    starts: Vec<u32>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SourcePosition {
    pub line: u32,
    pub utf16_column: u32,
}

impl LineIndex {
    pub fn new(source: &str) -> Self {
        let mut starts = vec![0];
        for (offset, byte) in source.bytes().enumerate() {
            if byte == b'\n' {
                starts
                    .push(u32::try_from(offset + 1).expect("source length exceeds G1 span range"));
            }
        }
        Self { starts }
    }

    pub fn position(&self, source: &str, offset: u32) -> Option<SourcePosition> {
        let offset = usize::try_from(offset).ok()?;
        let prefix = source.get(..offset)?;
        let line = self
            .starts
            .partition_point(|start| *start as usize <= offset)
            .checked_sub(1)?;
        let start = self.starts[line] as usize;
        let column = prefix
            .get(start..)?
            .chars()
            .map(|character| character.len_utf16() as u32)
            .sum();
        Some(SourcePosition {
            line: line as u32,
            utf16_column: column,
        })
    }

    pub fn line_count(&self) -> u32 {
        self.starts.len() as u32
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TokenKind {
    Identifier,
    Integer,
    Float,
    String,
    /// An immutable raw byte sequence. Unlike `String`, `\\xNN` accepts the
    /// complete byte range, so this token can describe non-UTF-8 assets.
    ByteString,
    Character,
    Operator,
    Punctuation(char),
    Whitespace,
    LineComment,
    BlockComment,
    Invalid,
    End,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
    /// Index into the original immutable source blob. Keeping no copied text
    /// makes the token stream lossless without allocating each lexeme.
    pub start: u32,
    pub end: u32,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LexerDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DelimiterDiagnostic {
    pub code: &'static str,
    pub token: usize,
    pub span: Span,
    pub message: &'static str,
}

/// Indexed pairing for structural delimiters. Token consumers can skip a
/// balanced region in constant time without rediscovering delimiter structure
/// through recursive parsing.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DelimiterMap {
    pairs: Vec<Option<usize>>,
    pub diagnostics: Vec<DelimiterDiagnostic>,
}

impl DelimiterMap {
    pub fn matching(&self, token: usize) -> Option<usize> {
        self.pairs.get(token).copied().flatten()
    }
}

#[derive(Clone, Debug)]
pub struct LexedFile {
    pub file: FileKey,
    pub source_fingerprint: Digest,
    pub lines: LineIndex,
    pub tokens: Vec<Token>,
    pub diagnostics: Vec<LexerDiagnostic>,
    pub delimiters: DelimiterMap,
}

impl LexedFile {
    pub fn lex(file: FileKey, source: &str) -> Self {
        let bytes = source.as_bytes();
        let mut lexer = Lexer {
            file,
            bytes,
            index: 0,
            tokens: vec![],
            diagnostics: vec![],
        };
        while lexer.index < bytes.len() {
            lexer.next();
        }
        let end = u32::try_from(bytes.len()).expect("source length exceeds G1 span range");
        lexer.tokens.push(Token {
            kind: TokenKind::End,
            span: Span {
                file,
                start: end,
                end,
            },
            start: end,
            end,
        });
        let delimiters = DelimiterMap::build(&lexer.tokens);
        Self {
            file,
            source_fingerprint: Digest::of_bytes(bytes),
            lines: LineIndex::new(source),
            tokens: lexer.tokens,
            diagnostics: lexer.diagnostics,
            delimiters,
        }
    }

    pub fn text<'a>(&self, source: &'a str, token: &Token) -> &'a str {
        &source[token.start as usize..token.end as usize]
    }
}

/// Classify one complete scalar literal using the exact lossless lexer
/// contract.  Frozen MIR and VM patterns use this instead of maintaining a
/// second, broader spelling heuristic: hostile semantic products must not be
/// able to smuggle a malformed source literal past the frontend boundary.
pub(crate) fn exact_scalar_literal_kind(source: &str) -> Option<TokenKind> {
    let file = FileKey(Digest::of_bytes(b"grandiose-stage0-scalar-literal"));
    let lexed = LexedFile::lex(file, source);
    if !lexed.diagnostics.is_empty() || lexed.tokens.len() != 2 {
        return None;
    }
    let token = lexed.tokens.first()?;
    (lexed.tokens[1].kind == TokenKind::End).then_some(token.kind.clone())
}

impl DelimiterMap {
    fn build(tokens: &[Token]) -> Self {
        let mut pairs = vec![None; tokens.len()];
        let mut diagnostics = vec![];
        let mut stack: Vec<(char, usize)> = vec![];
        for (index, token) in tokens.iter().enumerate() {
            let TokenKind::Punctuation(character) = token.kind else {
                continue;
            };
            if is_open_delimiter(character) {
                stack.push((character, index));
            } else if is_close_delimiter(character) {
                match stack.last().copied() {
                    Some((open, open_index)) if matching_delimiter(open) == character => {
                        stack.pop();
                        pairs[index] = Some(open_index);
                        pairs[open_index] = Some(index);
                    }
                    Some(_) => diagnostics.push(DelimiterDiagnostic {
                        code: "G1005",
                        token: index,
                        span: token.span,
                        message: "mismatched closing delimiter",
                    }),
                    None => diagnostics.push(DelimiterDiagnostic {
                        code: "G1006",
                        token: index,
                        span: token.span,
                        message: "closing delimiter has no opener",
                    }),
                }
            }
        }
        for (_, index) in stack {
            diagnostics.push(DelimiterDiagnostic {
                code: "G1007",
                token: index,
                span: tokens[index].span,
                message: "unclosed delimiter",
            });
        }
        diagnostics.sort_by_key(|diagnostic| diagnostic.token);
        Self { pairs, diagnostics }
    }
}

struct Lexer<'a> {
    file: FileKey,
    bytes: &'a [u8],
    index: usize,
    tokens: Vec<Token>,
    diagnostics: Vec<LexerDiagnostic>,
}

impl Lexer<'_> {
    fn next(&mut self) {
        let start = self.index;
        let byte = self.bytes[self.index];
        match byte {
            b' ' | b'\t' | b'\n' | b'\r' => {
                self.index += 1;
                while self.index < self.bytes.len()
                    && matches!(self.bytes[self.index], b' ' | b'\t' | b'\n' | b'\r')
                {
                    self.index += 1;
                }
                self.push(TokenKind::Whitespace, start);
            }
            b'/' if self.peek(1) == Some(b'/') => self.line_comment(start),
            b'/' if self.peek(1) == Some(b'*') => self.block_comment(start),
            b'"' => self.string(start),
            b'b' if self.peek(1) == Some(b'"') => self.byte_string(start),
            b'\'' => self.lifetime_or_character(start),
            b'0'..=b'9' => self.number(start),
            byte if is_identifier_start(byte) => self.identifier(start),
            byte if is_punctuation(byte) => {
                self.index += 1;
                self.push(TokenKind::Punctuation(byte as char), start);
            }
            byte if is_operator(byte) => {
                // `!/ Effects` is the compact spelling for a terminal
                // callable with an effect row.  It contains two grammatical
                // delimiters, not an overloadable `!/` operator: `!` is the
                // bottom result and `/` starts the row annotation.  Preserve
                // that boundary even though ordinary operator runs use
                // maximal munch.
                if byte == b'!' && self.peek(1) == Some(b'/') {
                    self.index += 1;
                    self.push(TokenKind::Operator, start);
                } else if matches!(byte, b'<' | b'>') && self.peek(1) == Some(byte) {
                    // Nested generic applications naturally place two angle
                    // delimiters together (`Outer<Inner<T>>`).  Preserve those
                    // delimiters as individual tokens instead of inventing an
                    // undocumented shift operator, so every header/body parser
                    // can accept projection arguments without whitespace hacks.
                    self.index += 1;
                    self.push(TokenKind::Operator, start);
                } else if byte == b'<' && matches!(self.peek(1), Some(b'&' | b'!')) {
                    // `&` and `!` start reference and bottom types inside a
                    // generic application. Splitting only these type-led
                    // boundaries preserves the lexer’s ordinary maximal
                    // munch for comparisons such as `<=` while allowing
                    // canonical forms like `Option<&'a T>` and `Result<!, E>`
                    // without whitespace.
                    self.index += 1;
                    self.push(TokenKind::Operator, start);
                } else {
                    self.index += 1;
                    while self.index < self.bytes.len() && is_operator(self.bytes[self.index]) {
                        self.index += 1;
                    }
                    self.push(TokenKind::Operator, start);
                }
            }
            _ => {
                self.index += utf8_width(byte);
                self.index = self.index.min(self.bytes.len());
                self.push(TokenKind::Invalid, start);
                self.diagnostic(start, "G1001", "invalid source character");
            }
        }
    }

    fn identifier(&mut self, start: usize) {
        self.index += 1;
        while self.index < self.bytes.len() && is_identifier_continue(self.bytes[self.index]) {
            self.index += 1;
        }
        self.push(TokenKind::Identifier, start);
    }

    /// A leading apostrophe is shared by character literals and lifetime
    /// identifiers.  Prefer a character literal when a matching closing
    /// apostrophe follows the identifier-shaped payload; otherwise retain the
    /// complete `'name` spelling as an identifier.  Keeping lifetimes in the
    /// identifier token class lets all existing binder/name consumers retain
    /// their source spelling without treating the apostrophe as an operator.
    fn lifetime_or_character(&mut self, start: usize) {
        let mut end = start + 1;
        if self
            .bytes
            .get(end)
            .copied()
            .is_some_and(is_identifier_start)
        {
            end += 1;
            while self
                .bytes
                .get(end)
                .copied()
                .is_some_and(is_identifier_continue)
            {
                end += 1;
            }
            if self.bytes.get(end) != Some(&b'\'') {
                self.index = end;
                self.push(TokenKind::Identifier, start);
                return;
            }
        }
        self.character(start);
    }

    fn number(&mut self, start: usize) {
        // The scanner owns lexical number validity.  Later phases can trust
        // that an Integer or Float token has a syntactically complete radix,
        // separator layout, fraction, and exponent; malformed spellings are
        // one Invalid token rather than a misleading sequence of valid ones.
        let mut base = 10;
        let mut prefixed = false;
        if self.peek(0) == Some(b'0') {
            match self.peek(1) {
                Some(b'b') => {
                    base = 2;
                    prefixed = true;
                }
                Some(b'o') => {
                    base = 8;
                    prefixed = true;
                }
                Some(b'x') => {
                    base = 16;
                    prefixed = true;
                }
                _ => {}
            }
        }
        if prefixed {
            self.index += 2;
            // The bootstrap grammar permits separators immediately after a
            // radix prefix, e.g. `0x_dead_beef`, but still requires exactly
            // one separator before the first digit.  Consuming an arbitrary
            // run here used to admit `0x__dead` even though separators are
            // otherwise only legal between digit components.
            if self.peek(0) == Some(b'_') {
                self.index += 1;
            }
        }
        let mut valid = self.scan_digits(base);
        let mut is_float = false;
        if !prefixed
            && self.peek(0) == Some(b'.')
            && self.peek(1).is_some_and(|byte| byte.is_ascii_digit())
        {
            is_float = true;
            self.index += 1;
            valid &= self.scan_digits(10);
        }
        if !prefixed && matches!(self.peek(0), Some(b'e' | b'E')) {
            is_float = true;
            self.index += 1;
            if matches!(self.peek(0), Some(b'+' | b'-')) {
                self.index += 1;
            }
            valid &= self.scan_digits(10);
        }
        if self
            .peek(0)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        {
            valid = false;
            while self
                .peek(0)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
            {
                self.index += 1;
            }
        }
        if valid {
            self.push(
                if is_float {
                    TokenKind::Float
                } else {
                    TokenKind::Integer
                },
                start,
            );
        } else {
            self.push(TokenKind::Invalid, start);
            self.diagnostic(start, "G1008", "malformed numeric literal");
        }
    }

    /// Consume one digit component and enforce separators only between valid
    /// digits.  Callers decide whether a missing component is legal.
    fn scan_digits(&mut self, base: u8) -> bool {
        let mut saw_digit = false;
        let mut after_separator = false;
        let mut valid = true;
        while let Some(byte) = self.peek(0) {
            if digit_value(byte).is_some_and(|value| value < base) {
                saw_digit = true;
                after_separator = false;
                self.index += 1;
            } else if byte == b'_' {
                if !saw_digit || after_separator {
                    valid = false;
                }
                after_separator = true;
                self.index += 1;
            } else {
                break;
            }
        }
        saw_digit && !after_separator && valid
    }

    fn string(&mut self, start: usize) {
        self.index += 1;
        let mut valid = true;
        while self.index < self.bytes.len() {
            let byte = self.bytes[self.index];
            if byte == b'"' {
                self.index += 1;
                self.push(
                    if valid {
                        TokenKind::String
                    } else {
                        TokenKind::Invalid
                    },
                    start,
                );
                if !valid {
                    self.diagnostic(start, "G1009", "invalid escape sequence in string literal");
                }
                return;
            }
            if byte == b'\n' {
                break;
            }
            if byte == b'\\' {
                valid &= self.scalar_escape();
            } else {
                self.index += utf8_width(byte);
            }
        }
        self.push(TokenKind::Invalid, start);
        self.diagnostic(start, "G1002", "unterminated string literal");
    }

    fn byte_string(&mut self, start: usize) {
        debug_assert_eq!(self.peek(0), Some(b'b'));
        debug_assert_eq!(self.peek(1), Some(b'"'));
        self.index += 2;
        let mut valid = true;
        while self.index < self.bytes.len() {
            let byte = self.bytes[self.index];
            if byte == b'"' {
                self.index += 1;
                self.push(
                    if valid { TokenKind::ByteString } else { TokenKind::Invalid },
                    start,
                );
                if !valid {
                    self.diagnostic(start, "G1011", "invalid escape sequence in byte string literal");
                }
                return;
            }
            if byte == b'\n' {
                break;
            }
            if byte == b'\\' {
                valid &= self.byte_escape();
            } else {
                self.index += utf8_width(byte);
            }
        }
        self.push(TokenKind::Invalid, start);
        self.diagnostic(start, "G1012", "unterminated byte string literal");
    }

    fn character(&mut self, start: usize) {
        self.index += 1;
        let mut count = 0_u32;
        let mut valid = true;
        while self.index < self.bytes.len() {
            let byte = self.bytes[self.index];
            if byte == b'\'' {
                self.index += 1;
                let valid = valid && count == 1;
                self.push(
                    if valid {
                        TokenKind::Character
                    } else {
                        TokenKind::Invalid
                    },
                    start,
                );
                if !valid {
                    self.diagnostic(
                        start,
                        "G1010",
                        "character literal must contain exactly one scalar value",
                    );
                }
                return;
            }
            if byte == b'\n' {
                break;
            }
            if byte == b'\\' {
                valid &= self.scalar_escape();
            } else {
                self.index += utf8_width(byte);
            }
            count += 1;
        }
        self.push(TokenKind::Invalid, start);
        self.diagnostic(start, "G1003", "unterminated character literal");
    }

    /// Consume an escape after its leading backslash.  The scanner validates
    /// the scalar grammar itself, including fixed-width byte and braced
    /// Unicode escapes, so parser clients never need a second escape parser.
    fn scalar_escape(&mut self) -> bool {
        debug_assert_eq!(self.peek(0), Some(b'\\'));
        self.index += 1;
        let Some(selector) = self.peek(0) else {
            return false;
        };
        self.index += 1;
        match selector {
            b'n' | b'r' | b't' | b'0' | b'"' | b'\'' | b'\\' => true,
            b'x' => {
                let Some(first) = self.peek(0) else {
                    return false;
                };
                let Some(second) = self.peek(1) else {
                    self.index += 1;
                    return false;
                };
                let Some(first) = digit_value(first) else {
                    return false;
                };
                let Some(second) = digit_value(second) else {
                    return false;
                };
                self.index += 2;
                // Scalar `\\xNN` escapes are deliberately ASCII only;
                // arbitrary Unicode uses the unambiguous braced form below.
                first * 16 + second < 0x80
            }
            b'u' => self.unicode_escape(),
            _ => false,
        }
    }

    /// Byte strings share the ordinary escape grammar but intentionally admit
    /// all `\\xNN` octets.  Unicode escapes and direct non-ASCII source text
    /// are UTF-8 encoded by literal lowering; they do not reinterpret source
    /// encoding as an arbitrary machine pointer or asset type.
    fn byte_escape(&mut self) -> bool {
        debug_assert_eq!(self.peek(0), Some(b'\\'));
        if self.peek(1) != Some(b'x') {
            return self.scalar_escape();
        }
        self.index += 2;
        let Some(first) = self.peek(0).and_then(digit_value) else {
            return false;
        };
        let Some(second) = self.peek(1).and_then(digit_value) else {
            return false;
        };
        let _ = (first, second);
        self.index += 2;
        true
    }

    fn unicode_escape(&mut self) -> bool {
        if self.peek(0) != Some(b'{') {
            return false;
        }
        self.index += 1;
        let mut scalar = 0_u32;
        let mut digits = 0_u8;
        while let Some(byte) = self.peek(0) {
            if byte == b'}' {
                self.index += 1;
                return digits > 0 && char::from_u32(scalar).is_some();
            }
            let Some(value) = digit_value(byte) else {
                return false;
            };
            if digits == 6 {
                return false;
            }
            scalar = scalar * 16 + u32::from(value);
            digits += 1;
            self.index += 1;
        }
        false
    }

    fn line_comment(&mut self, start: usize) {
        self.index += 2;
        while self.index < self.bytes.len() && self.bytes[self.index] != b'\n' {
            self.index += 1;
        }
        self.push(TokenKind::LineComment, start);
    }

    fn block_comment(&mut self, start: usize) {
        self.index += 2;
        let mut depth = 1_u32;
        while self.index < self.bytes.len() {
            if self.peek(0) == Some(b'/') && self.peek(1) == Some(b'*') {
                depth += 1;
                self.index += 2;
            } else if self.peek(0) == Some(b'*') && self.peek(1) == Some(b'/') {
                depth -= 1;
                self.index += 2;
                if depth == 0 {
                    self.push(TokenKind::BlockComment, start);
                    return;
                }
            } else {
                self.index += 1;
            }
        }
        self.push(TokenKind::Invalid, start);
        self.diagnostic(start, "G1004", "unterminated block comment");
    }

    fn peek(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.index + offset).copied()
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        let start = u32::try_from(start).expect("source offset exceeds G1 span range");
        let end = u32::try_from(self.index).expect("source offset exceeds G1 span range");
        self.tokens.push(Token {
            kind,
            span: Span {
                file: self.file,
                start,
                end,
            },
            start,
            end,
        });
    }

    fn diagnostic(&mut self, start: usize, code: &'static str, message: &'static str) {
        let start = u32::try_from(start).expect("source offset exceeds G1 span range");
        self.diagnostics.push(LexerDiagnostic {
            code,
            span: Span {
                file: self.file,
                start,
                end: u32::try_from(self.index).expect("source offset exceeds G1 span range"),
            },
            message,
        });
    }
}

fn is_identifier_start(byte: u8) -> bool {
    byte.is_ascii_alphabetic() || byte == b'_'
}

fn is_identifier_continue(byte: u8) -> bool {
    is_identifier_start(byte) || byte.is_ascii_digit()
}

fn digit_value(byte: u8) -> Option<u8> {
    match byte {
        b'0'..=b'9' => Some(byte - b'0'),
        b'a'..=b'f' => Some(byte - b'a' + 10),
        b'A'..=b'F' => Some(byte - b'A' + 10),
        _ => None,
    }
}

fn is_punctuation(byte: u8) -> bool {
    matches!(
        byte,
        b'(' | b')' | b'[' | b']' | b'{' | b'}' | b',' | b';' | b':' | b'.'
    )
}

fn is_operator(byte: u8) -> bool {
    matches!(
        byte,
        b'+' | b'-'
            | b'*'
            | b'/'
            | b'%'
            | b'='
            | b'!'
            | b'<'
            | b'>'
            | b'&'
            | b'|'
            | b'^'
            | b'~'
            | b'?'
            // Labels use the compact `@name: Type { ... }` binder and
            // `@name(value)` transfer spellings.  Keep the sigil in the
            // operator family so it remains separate from its identifier.
            | b'@'
    )
}

fn is_open_delimiter(character: char) -> bool {
    matches!(character, '(' | '[' | '{')
}

fn is_close_delimiter(character: char) -> bool {
    matches!(character, ')' | ']' | '}')
}

fn matching_delimiter(character: char) -> char {
    match character {
        '(' => ')',
        '[' => ']',
        '{' => '}',
        _ => unreachable!("only opening delimiters have a matching closer"),
    }
}

fn utf8_width(byte: u8) -> usize {
    match byte {
        0x00..=0x7f => 1,
        0xc0..=0xdf => 2,
        0xe0..=0xef => 3,
        0xf0..=0xf7 => 4,
        _ => 1,
    }
}
