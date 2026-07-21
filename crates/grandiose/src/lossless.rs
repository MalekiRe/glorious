//! Lossless lexical structure for source-preserving tools.
//!
//! Unlike [`crate::lexer`], this layer retains whitespace and comments and
//! does not decode literal payloads. Its spans form an exact, gap-free
//! partition of the input, so concatenating token text reproduces the source.

use crate::{diagnostic::Diagnostic, span::Span};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum LosslessKind {
    Whitespace,
    LineComment,
    BlockComment,
    Identifier,
    Number,
    String,
    Character,
    ByteString,
    ByteCharacter,
    Lifetime,
    Label,
    Punctuation,
}

impl LosslessKind {
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            Self::Whitespace | Self::LineComment | Self::BlockComment
        )
    }

    pub fn is_comment(self) -> bool {
        matches!(self, Self::LineComment | Self::BlockComment)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LosslessToken {
    pub kind: LosslessKind,
    pub span: Span,
}

impl LosslessToken {
    pub fn text(self, source: &str) -> &str {
        &source[self.span.start..self.span.end]
    }
}

/// Lexes a gap-free source-preserving stream. Literal contents and escapes are
/// deliberately not interpreted; the semantic lexer remains authoritative for
/// language diagnostics and parser behavior.
pub fn lex_lossless(source: &str) -> Result<Vec<LosslessToken>, Diagnostic> {
    LosslessLexer {
        source,
        bytes: source.as_bytes(),
        cursor: 0,
        tokens: Vec::new(),
    }
    .run()
}

struct LosslessLexer<'source> {
    source: &'source str,
    bytes: &'source [u8],
    cursor: usize,
    tokens: Vec<LosslessToken>,
}

impl LosslessLexer<'_> {
    fn run(mut self) -> Result<Vec<LosslessToken>, Diagnostic> {
        while self.cursor < self.bytes.len() {
            let start = self.cursor;
            let kind = match self.bytes[start] {
                byte if byte.is_ascii_whitespace() => {
                    self.cursor += 1;
                    while self
                        .bytes
                        .get(self.cursor)
                        .is_some_and(u8::is_ascii_whitespace)
                    {
                        self.cursor += 1;
                    }
                    LosslessKind::Whitespace
                }
                b'/' if self.peek(1) == Some(b'/') => {
                    self.cursor += 2;
                    while self.cursor < self.bytes.len() && self.bytes[self.cursor] != b'\n' {
                        self.cursor += 1;
                    }
                    LosslessKind::LineComment
                }
                b'/' if self.peek(1) == Some(b'*') => self.block_comment(start)?,
                b'b' if self.peek(1) == Some(b'"') => {
                    self.cursor += 1;
                    self.quoted(start, b'"', "byte string")?;
                    LosslessKind::ByteString
                }
                b'b' if self.peek(1) == Some(b'\'') => {
                    self.cursor += 1;
                    self.quoted(start, b'\'', "byte literal")?;
                    LosslessKind::ByteCharacter
                }
                b'"' => {
                    self.quoted(start, b'"', "string")?;
                    LosslessKind::String
                }
                b'\'' => self.character_or_lifetime(start)?,
                b'@' => {
                    self.cursor += 1;
                    self.identifier_tail();
                    LosslessKind::Label
                }
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                    self.cursor += 1;
                    self.identifier_tail();
                    LosslessKind::Identifier
                }
                b'0'..=b'9' => {
                    self.number();
                    LosslessKind::Number
                }
                _ => {
                    self.punctuation();
                    LosslessKind::Punctuation
                }
            };
            debug_assert!(self.cursor > start);
            self.tokens.push(LosslessToken {
                kind,
                span: Span::new(start, self.cursor),
            });
        }
        Ok(self.tokens)
    }

    fn peek(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.cursor + offset).copied()
    }

    fn identifier_tail(&mut self) {
        while self
            .bytes
            .get(self.cursor)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
        {
            self.cursor += 1;
        }
    }

    fn block_comment(&mut self, start: usize) -> Result<LosslessKind, Diagnostic> {
        self.cursor += 2;
        let mut depth = 1usize;
        while self.cursor < self.bytes.len() && depth > 0 {
            match self.bytes.get(self.cursor..self.cursor + 2) {
                Some(b"/*") => {
                    depth += 1;
                    self.cursor += 2;
                }
                Some(b"*/") => {
                    depth -= 1;
                    self.cursor += 2;
                }
                _ => self.cursor += 1,
            }
        }
        if depth != 0 {
            return Err(Diagnostic::error(
                "unfinished comment",
                "this block comment is never closed",
                Span::new(start, self.bytes.len()),
            )
            .with_help("add `*/` to close the comment"));
        }
        Ok(LosslessKind::BlockComment)
    }

    fn quoted(
        &mut self,
        start: usize,
        delimiter: u8,
        description: &'static str,
    ) -> Result<(), Diagnostic> {
        debug_assert_eq!(self.bytes[self.cursor], delimiter);
        self.cursor += 1;
        while self.cursor < self.bytes.len() {
            match self.bytes[self.cursor] {
                byte if byte == delimiter => {
                    self.cursor += 1;
                    return Ok(());
                }
                b'\\' => {
                    self.cursor += 1;
                    if self.cursor == self.bytes.len() {
                        break;
                    }
                    let character = self.source[self.cursor..].chars().next().unwrap();
                    self.cursor += character.len_utf8();
                }
                _ => {
                    let character = self.source[self.cursor..].chars().next().unwrap();
                    self.cursor += character.len_utf8();
                }
            }
        }
        Err(Diagnostic::error(
            format!("unfinished {description}"),
            format!("this {description} is never closed"),
            Span::new(start, self.bytes.len()),
        ))
    }

    fn character_or_lifetime(&mut self, start: usize) -> Result<LosslessKind, Diagnostic> {
        self.cursor += 1;
        if self.peek(0) == Some(b'\\') {
            self.cursor = start;
            self.quoted(start, b'\'', "character literal")?;
            return Ok(LosslessKind::Character);
        }
        if self.cursor < self.bytes.len() {
            let character = self.source[self.cursor..].chars().next().unwrap();
            let after = self.cursor + character.len_utf8();
            if self.bytes.get(after) == Some(&b'\'') {
                self.cursor = after + 1;
                return Ok(LosslessKind::Character);
            }
        }
        if !self
            .peek(0)
            .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        {
            return Err(Diagnostic::error(
                "invalid lifetime identifier",
                "expected an ASCII identifier after `'`",
                Span::new(start, self.cursor),
            ));
        }
        self.cursor += 1;
        self.identifier_tail();
        Ok(LosslessKind::Lifetime)
    }

    fn number(&mut self) {
        let non_decimal =
            self.peek(0) == Some(b'0') && matches!(self.peek(1), Some(b'b' | b'o' | b'x'));
        self.cursor += 1;
        if non_decimal {
            self.cursor += 1;
            while self
                .bytes
                .get(self.cursor)
                .is_some_and(|byte| byte.is_ascii_alphanumeric() || *byte == b'_')
            {
                self.cursor += 1;
            }
            return;
        }
        while self
            .bytes
            .get(self.cursor)
            .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
        {
            self.cursor += 1;
        }
        if self.peek(0) == Some(b'.') && self.peek(1).is_some_and(|byte| byte.is_ascii_digit()) {
            self.cursor += 1;
            while self
                .bytes
                .get(self.cursor)
                .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
            {
                self.cursor += 1;
            }
        }
        if matches!(self.peek(0), Some(b'e' | b'E')) {
            self.cursor += 1;
            if matches!(self.peek(0), Some(b'+' | b'-')) {
                self.cursor += 1;
            }
            while self
                .bytes
                .get(self.cursor)
                .is_some_and(|byte| byte.is_ascii_digit() || *byte == b'_')
            {
                self.cursor += 1;
            }
        }
    }

    fn punctuation(&mut self) {
        for spelling in [
            "->!", "->", "=>", "::", "==", "!=", "<=", ">=", "&&", "||", "..",
        ] {
            if self.source[self.cursor..].starts_with(spelling) {
                self.cursor += spelling.len();
                return;
            }
        }
        let character = self.source[self.cursor..].chars().next().unwrap();
        self.cursor += character.len_utf8();
    }
}
