use crate::{diagnostic::Diagnostic, span::Span};

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

/// Fixed core words. Library control names such as `if`, `match`, `loop`,
/// `return`, `yield`, and `await` are ordinary identifiers; `for`, `with`,
/// `mut`, `move`, `cases`, `private`, `const`, and `infinity` stay contextual.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Kw {
    Cancel,
    Effect,
    Enum,
    Handle,
    Impl,
    Is,
    Label,
    Leave,
    Let,
    Perform,
    Resume,
    Struct,
    Tail,
    Trait,
    Type,
    Where,
}

impl Kw {
    pub fn as_str(self) -> &'static str {
        match self {
            Kw::Cancel => "cancel",
            Kw::Effect => "effect",
            Kw::Enum => "enum",
            Kw::Handle => "handle",
            Kw::Impl => "impl",
            Kw::Is => "is",
            Kw::Label => "label",
            Kw::Leave => "leave",
            Kw::Let => "let",
            Kw::Perform => "perform",
            Kw::Resume => "resume",
            Kw::Struct => "struct",
            Kw::Tail => "tail",
            Kw::Trait => "trait",
            Kw::Type => "type",
            Kw::Where => "where",
        }
    }

    fn from_str(word: &str) -> Option<Kw> {
        Some(match word {
            "cancel" => Kw::Cancel,
            "effect" => Kw::Effect,
            "enum" => Kw::Enum,
            "handle" => Kw::Handle,
            "impl" => Kw::Impl,
            "is" => Kw::Is,
            "label" => Kw::Label,
            "leave" => Kw::Leave,
            "let" => Kw::Let,
            "perform" => Kw::Perform,
            "resume" => Kw::Resume,
            "struct" => Kw::Struct,
            "tail" => Kw::Tail,
            "trait" => Kw::Trait,
            "type" => Kw::Type,
            "where" => Kw::Where,
            _ => return None,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum NumberBase {
    Binary,
    Octal,
    Decimal,
    Hex,
}

impl NumberBase {
    pub fn radix(self) -> u32 {
        match self {
            NumberBase::Binary => 2,
            NumberBase::Octal => 8,
            NumberBase::Decimal => 10,
            NumberBase::Hex => 16,
        }
    }

    fn describe(self) -> &'static str {
        match self {
            NumberBase::Binary => "binary",
            NumberBase::Octal => "octal",
            NumberBase::Decimal => "decimal",
            NumberBase::Hex => "hexadecimal",
        }
    }
}

/// A numeric literal with its complete source payload. The lexer validates
/// digits, separators, and shape but performs no range conversion; consumers
/// convert after the expected type is known.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberLiteral {
    /// The exact source spelling, separators included.
    pub spelling: String,
    pub base: NumberBase,
    /// Integral digits with separators stripped, without the base prefix.
    pub digits: String,
    /// Fractional digits with separators stripped, when a fraction was written.
    pub fraction: Option<String>,
    /// Signed exponent digits with separators stripped, when written.
    pub exponent: Option<NumberExponent>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NumberExponent {
    pub negative: bool,
    pub digits: String,
}

impl NumberLiteral {
    pub fn is_float(&self) -> bool {
        self.fraction.is_some() || self.exponent.is_some()
    }

    pub fn as_u64(&self, span: Span) -> Result<u64, Diagnostic> {
        if self.is_float() {
            return Err(Diagnostic::error(
                "expected an integer",
                "a float literal is not valid here",
                span,
            ));
        }
        let mut value: u64 = 0;
        for digit in self.digits.chars() {
            let digit = digit.to_digit(self.base.radix()).expect("lexed digit");
            value = value
                .checked_mul(self.base.radix() as u64)
                .and_then(|value| value.checked_add(digit as u64))
                .ok_or_else(|| {
                    Diagnostic::error(
                        "integer is too large",
                        "this integer does not fit in 64 bits",
                        span,
                    )
                })?;
        }
        Ok(value)
    }

    pub fn as_i64(&self, span: Span) -> Result<i64, Diagnostic> {
        let magnitude = self.as_u64(span)?;
        i64::try_from(magnitude).map_err(|_| {
            Diagnostic::error(
                "integer is too large",
                "this integer does not fit in an i64",
                span,
            )
        })
    }

    pub fn as_f64(&self) -> f64 {
        self.spelling
            .chars()
            .filter(|character| *character != '_')
            .collect::<String>()
            .parse()
            .unwrap_or(f64::INFINITY)
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Ident(String),
    Keyword(Kw),
    Lifetime(String),
    Number(NumberLiteral),
    String(String),
    Char(char),
    Byte(u8),
    ByteString(Vec<u8>),
    /// `@name`. The binder form `@name:` is the label token followed by `:`.
    Label(String),
    /// A punctuation run with no structural reading, e.g. `<*>` or `++`.
    Operator(String),
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Comma,
    Colon,
    DoubleColon,
    DotDot,
    Dot,
    Semicolon,
    Arrow,
    FatArrow,
    Slash,
    Plus,
    Minus,
    Star,
    Percent,
    Pipe,
    Eq,
    EqEq,
    BangEq,
    Lt,
    LtEq,
    Gt,
    GtEq,
    Amp,
    Bang,
    Eof,
}

/// Characters that may participate in a punctuation operator run. Structural
/// delimiters, `:`, `;`, `,`, `@`, quotes, and comments are never part of one.
fn is_operator_char(byte: u8) -> bool {
    matches!(
        byte,
        b'!' | b'#'
            | b'$'
            | b'%'
            | b'&'
            | b'*'
            | b'+'
            | b'-'
            | b'.'
            | b'/'
            | b'<'
            | b'='
            | b'>'
            | b'?'
            | b'^'
            | b'|'
            | b'~'
    )
}

fn structural_two(pair: &[u8]) -> Option<TokenKind> {
    Some(match pair {
        b"->" => TokenKind::Arrow,
        b"=>" => TokenKind::FatArrow,
        b".." => TokenKind::DotDot,
        b"==" => TokenKind::EqEq,
        b"!=" => TokenKind::BangEq,
        b"<=" => TokenKind::LtEq,
        b">=" => TokenKind::GtEq,
        _ => return None,
    })
}

fn structural_one(byte: u8) -> Option<TokenKind> {
    Some(match byte {
        b'.' => TokenKind::Dot,
        b'/' => TokenKind::Slash,
        b'+' => TokenKind::Plus,
        b'-' => TokenKind::Minus,
        b'*' => TokenKind::Star,
        b'%' => TokenKind::Percent,
        b'|' => TokenKind::Pipe,
        b'=' => TokenKind::Eq,
        b'<' => TokenKind::Lt,
        b'>' => TokenKind::Gt,
        b'&' => TokenKind::Amp,
        b'!' => TokenKind::Bang,
        _ => return None,
    })
}

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    Lexer {
        source,
        bytes: source.as_bytes(),
        cursor: 0,
        tokens: Vec::new(),
    }
    .run()
}

struct Lexer<'src> {
    source: &'src str,
    bytes: &'src [u8],
    cursor: usize,
    tokens: Vec<Token>,
}

impl<'src> Lexer<'src> {
    /// Every iteration either consumes at least one byte or returns an error,
    /// so lexing terminates on every input.
    fn run(mut self) -> Result<Vec<Token>, Diagnostic> {
        while self.cursor < self.bytes.len() {
            let start = self.cursor;
            match self.bytes[self.cursor] {
                byte if byte.is_ascii_whitespace() => self.cursor += 1,
                b'/' if self.peek_at(1) == Some(b'/') => self.line_comment(),
                b'/' if self.peek_at(1) == Some(b'*') => self.block_comment()?,
                b'b' if matches!(self.peek_at(1), Some(b'\'')) => self.byte_literal()?,
                b'b' if matches!(self.peek_at(1), Some(b'"')) => self.byte_string()?,
                b'a'..=b'z' | b'A'..=b'Z' | b'_' => self.word(),
                b'\'' => self.char_or_lifetime()?,
                b'0'..=b'9' => self.number()?,
                b'"' => self.string()?,
                b'@' => self.label()?,
                b':' => {
                    if self.peek_at(1) == Some(b':') {
                        self.cursor += 2;
                        self.push(TokenKind::DoubleColon, start);
                    } else {
                        self.cursor += 1;
                        self.push(TokenKind::Colon, start);
                    }
                }
                b'(' | b')' | b'{' | b'}' | b'[' | b']' | b',' | b';' => {
                    let kind = match self.bytes[self.cursor] {
                        b'(' => TokenKind::LParen,
                        b')' => TokenKind::RParen,
                        b'{' => TokenKind::LBrace,
                        b'}' => TokenKind::RBrace,
                        b'[' => TokenKind::LBracket,
                        b']' => TokenKind::RBracket,
                        b',' => TokenKind::Comma,
                        _ => TokenKind::Semicolon,
                    };
                    self.cursor += 1;
                    self.push(kind, start);
                }
                byte if is_operator_char(byte) => self.operator_run(),
                _ => {
                    let character = self.source[start..].chars().next().unwrap();
                    return Err(Diagnostic::error(
                        "unexpected character",
                        format!("`{}` is not part of Grandiose syntax", character),
                        Span::new(start, start + character.len_utf8()),
                    ));
                }
            }
        }
        self.tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::new(self.bytes.len(), self.bytes.len()),
        });
        Ok(self.tokens)
    }

    fn push(&mut self, kind: TokenKind, start: usize) {
        self.tokens.push(Token {
            kind,
            span: Span::new(start, self.cursor),
        });
    }

    fn peek_at(&self, offset: usize) -> Option<u8> {
        self.bytes.get(self.cursor + offset).copied()
    }

    fn line_comment(&mut self) {
        while self.cursor < self.bytes.len() && self.bytes[self.cursor] != b'\n' {
            self.cursor += 1;
        }
    }

    fn block_comment(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        self.cursor += 2;
        let mut depth = 1usize;
        while self.cursor < self.bytes.len() && depth > 0 {
            if self.bytes.get(self.cursor..self.cursor + 2) == Some(b"/*") {
                depth += 1;
                self.cursor += 2;
            } else if self.bytes.get(self.cursor..self.cursor + 2) == Some(b"*/") {
                depth -= 1;
                self.cursor += 2;
            } else {
                self.cursor += 1;
            }
        }
        if depth > 0 {
            return Err(Diagnostic::error(
                "unfinished comment",
                "this block comment is never closed",
                Span::new(start, self.bytes.len()),
            )
            .with_help("add `*/` to close the comment"));
        }
        Ok(())
    }

    fn word(&mut self) {
        let start = self.cursor;
        self.cursor += 1;
        while self.cursor < self.bytes.len()
            && (self.bytes[self.cursor].is_ascii_alphanumeric() || self.bytes[self.cursor] == b'_')
        {
            self.cursor += 1;
        }
        let word = &self.source[start..self.cursor];
        let kind = match Kw::from_str(word) {
            Some(keyword) => TokenKind::Keyword(keyword),
            None => TokenKind::Ident(word.into()),
        };
        self.push(kind, start);
    }

    fn label(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        self.cursor += 1;
        if !self
            .peek_at(0)
            .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
        {
            return Err(Diagnostic::error(
                "invalid label",
                "expected a label name after `@`",
                Span::new(start, self.cursor),
            ));
        }
        let name_start = self.cursor;
        while self.cursor < self.bytes.len()
            && (self.bytes[self.cursor].is_ascii_alphanumeric() || self.bytes[self.cursor] == b'_')
        {
            self.cursor += 1;
        }
        let name = self.source[name_start..self.cursor].to_owned();
        self.push(TokenKind::Label(name), start);
        Ok(())
    }

    /// Structural spellings take priority with a longest-first match, so
    /// adjacent structural operators such as `=&` in `type A=&i64;` keep their
    /// individual readings. Punctuation with no structural reading forms a
    /// maximal `Operator` run. Complete flat operator spellings such as `<*>`
    /// are rebuilt from adjacent tokens in operator position by the parser,
    /// where declared fixities are known.
    fn operator_run(&mut self) {
        let start = self.cursor;
        if let Some(kind) = self
            .bytes
            .get(self.cursor..self.cursor + 2)
            .and_then(structural_two)
        {
            self.cursor += 2;
            self.push(kind, start);
            return;
        }
        if let Some(kind) = structural_one(self.bytes[self.cursor]) {
            self.cursor += 1;
            self.push(kind, start);
            return;
        }
        while self.peek_at(0).is_some_and(|byte| {
            is_operator_char(byte)
                && structural_one(byte).is_none()
                && self
                    .bytes
                    .get(self.cursor..self.cursor + 2)
                    .and_then(structural_two)
                    .is_none()
        }) {
            self.cursor += 1;
        }
        let run = &self.source[start..self.cursor];
        self.push(TokenKind::Operator(run.into()), start);
    }

    /// Scans `digit (digit | _)*` in `base`, appending digits to `digits` with
    /// separators stripped. The run must not end in a separator.
    fn digit_run(
        &mut self,
        base: NumberBase,
        digits: &mut String,
        component: &str,
    ) -> Result<(), Diagnostic> {
        let mut last_was_separator: Option<usize> = None;
        loop {
            match self.peek_at(0) {
                Some(b'_') => {
                    last_was_separator = Some(self.cursor);
                    self.cursor += 1;
                }
                Some(byte) if (byte as char).is_digit(base.radix()) => {
                    digits.push(byte as char);
                    last_was_separator = None;
                    self.cursor += 1;
                }
                Some(byte) if byte.is_ascii_digit() => {
                    return Err(Diagnostic::error(
                        "invalid digit",
                        format!(
                            "`{}` is not a valid digit in a {} literal",
                            byte as char,
                            base.describe()
                        ),
                        Span::new(self.cursor, self.cursor + 1),
                    ));
                }
                _ => break,
            }
        }
        if let Some(position) = last_was_separator {
            return Err(Diagnostic::error(
                "misplaced digit separator",
                format!("a digit separator cannot end {component}"),
                Span::new(position, position + 1),
            ));
        }
        if digits.is_empty() {
            return Err(Diagnostic::error(
                "expected digits",
                format!("expected at least one digit in {component}"),
                Span::new(self.cursor.saturating_sub(1), self.cursor),
            ));
        }
        Ok(())
    }

    fn number(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        // A digit chain after a projection dot is a tuple index such as
        // `pair.0.1`, never a float, so fractions are disabled there.
        let after_projection_dot = matches!(
            self.tokens.last().map(|token| &token.kind),
            Some(TokenKind::Dot)
        );
        let base = if self.bytes[self.cursor] == b'0' {
            match self.peek_at(1) {
                Some(b'b') => NumberBase::Binary,
                Some(b'o') => NumberBase::Octal,
                Some(b'x') => NumberBase::Hex,
                _ => NumberBase::Decimal,
            }
        } else {
            NumberBase::Decimal
        };
        let mut digits = String::new();
        if base == NumberBase::Decimal {
            self.digit_run(base, &mut digits, "this integer literal")?;
        } else {
            self.cursor += 2;
            // Rust-style: separators may directly follow the base prefix.
            while self.peek_at(0) == Some(b'_') {
                self.cursor += 1;
            }
            if !self
                .peek_at(0)
                .is_some_and(|byte| (byte as char).is_digit(base.radix()))
            {
                return Err(Diagnostic::error(
                    "expected digits",
                    format!(
                        "expected {} digits after the `{}` prefix",
                        base.describe(),
                        &self.source[start..self.cursor.min(start + 2)],
                    ),
                    Span::new(start, self.cursor),
                ));
            }
            self.digit_run(base, &mut digits, "this integer literal")?;
        }
        let mut fraction = None;
        let mut exponent = None;
        if base == NumberBase::Decimal && !after_projection_dot {
            if self.peek_at(0) == Some(b'.')
                && self.peek_at(1).is_some_and(|byte| byte.is_ascii_digit())
            {
                self.cursor += 1;
                let mut fraction_digits = String::new();
                self.digit_run(base, &mut fraction_digits, "this fraction")?;
                fraction = Some(fraction_digits);
            }
            if matches!(self.peek_at(0), Some(b'e' | b'E')) {
                let sign_offset = match self.peek_at(1) {
                    Some(b'+' | b'-') => 1,
                    _ => 0,
                };
                if self
                    .peek_at(1 + sign_offset)
                    .is_some_and(|byte| byte.is_ascii_digit() || byte == b'_')
                {
                    self.cursor += 1;
                    let negative = self.peek_at(0) == Some(b'-');
                    self.cursor += sign_offset;
                    let mut exponent_digits = String::new();
                    self.digit_run(base, &mut exponent_digits, "this exponent")?;
                    exponent = Some(NumberExponent {
                        negative,
                        digits: exponent_digits,
                    });
                } else {
                    return Err(Diagnostic::error(
                        "malformed float exponent",
                        "expected exponent digits after `e`",
                        Span::new(self.cursor, self.cursor + 1 + sign_offset),
                    ));
                }
            }
        }
        if self
            .peek_at(0)
            .is_some_and(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
        {
            let stray = self.source[self.cursor..].chars().next().unwrap();
            return Err(Diagnostic::error(
                "invalid digit",
                format!("`{stray}` cannot continue a {} literal", base.describe()),
                Span::new(self.cursor, self.cursor + stray.len_utf8()),
            ));
        }
        let literal = NumberLiteral {
            spelling: self.source[start..self.cursor].to_owned(),
            base,
            digits,
            fraction,
            exponent,
        };
        self.push(TokenKind::Number(literal), start);
        Ok(())
    }

    /// Decodes one scalar escape shared by string and character literals. The
    /// cursor sits on the byte after `\` on entry and after the escape on exit.
    fn scalar_escape(&mut self, backslash: usize) -> Result<char, Diagnostic> {
        let Some(selector) = self.peek_at(0) else {
            return Err(Diagnostic::error(
                "unfinished escape",
                "expected an escape after this backslash",
                Span::new(backslash, self.bytes.len()),
            ));
        };
        self.cursor += 1;
        Ok(match selector {
            b'n' => '\n',
            b'r' => '\r',
            b't' => '\t',
            b'0' => '\0',
            b'"' => '"',
            b'\'' => '\'',
            b'\\' => '\\',
            b'x' => {
                let value = self.hex_escape_pair(backslash)?;
                if value > 0x7F {
                    return Err(Diagnostic::error(
                        "invalid character escape",
                        "`\\x` escapes in text must be at most `\\x7F`",
                        Span::new(backslash, self.cursor),
                    )
                    .with_help(
                        "use `\\u{...}` for non-ASCII scalars or a byte string for raw bytes",
                    ));
                }
                value as char
            }
            b'u' => self.unicode_escape(backslash)?,
            _ => {
                return Err(Diagnostic::error(
                    "unknown escape",
                    "valid escapes are `\\n`, `\\r`, `\\t`, `\\0`, `\\\"`, `\\'`, `\\\\`, `\\xNN`, and `\\u{...}`",
                    Span::new(backslash, self.cursor),
                ));
            }
        })
    }

    fn hex_escape_pair(&mut self, backslash: usize) -> Result<u8, Diagnostic> {
        let mut value = 0u8;
        for _ in 0..2 {
            let digit = self
                .peek_at(0)
                .and_then(|byte| (byte as char).to_digit(16))
                .ok_or_else(|| {
                    Diagnostic::error(
                        "malformed hex escape",
                        "`\\x` requires exactly two hexadecimal digits",
                        Span::new(backslash, self.cursor),
                    )
                })?;
            value = value * 16 + digit as u8;
            self.cursor += 1;
        }
        Ok(value)
    }

    fn unicode_escape(&mut self, backslash: usize) -> Result<char, Diagnostic> {
        if self.peek_at(0) != Some(b'{') {
            return Err(Diagnostic::error(
                "malformed Unicode escape",
                "expected `{` after `\\u`",
                Span::new(backslash, self.cursor),
            ));
        }
        self.cursor += 1;
        let mut value: u32 = 0;
        let mut digits = 0usize;
        loop {
            match self.peek_at(0) {
                Some(b'}') => {
                    self.cursor += 1;
                    break;
                }
                Some(byte) if (byte as char).is_ascii_hexdigit() => {
                    if digits == 6 {
                        return Err(Diagnostic::error(
                            "malformed Unicode escape",
                            "`\\u{...}` accepts at most six hexadecimal digits",
                            Span::new(backslash, self.cursor + 1),
                        ));
                    }
                    value = value * 16 + (byte as char).to_digit(16).unwrap();
                    digits += 1;
                    self.cursor += 1;
                }
                Some(_) => {
                    return Err(Diagnostic::error(
                        "malformed Unicode escape",
                        "expected hexadecimal digits and a closing `}`",
                        Span::new(self.cursor, self.cursor + 1),
                    ));
                }
                None => {
                    return Err(Diagnostic::error(
                        "unfinished Unicode escape",
                        "this `\\u{...}` escape is never closed",
                        Span::new(backslash, self.bytes.len()),
                    ));
                }
            }
        }
        if digits == 0 {
            return Err(Diagnostic::error(
                "malformed Unicode escape",
                "`\\u{}` must contain at least one hexadecimal digit",
                Span::new(backslash, self.cursor),
            ));
        }
        char::from_u32(value).ok_or_else(|| {
            Diagnostic::error(
                "invalid Unicode scalar",
                format!("`{value:#x}` is not a valid Unicode scalar value"),
                Span::new(backslash, self.cursor),
            )
        })
    }

    /// Decodes one escape in a byte context. Any `\xNN` value is permitted;
    /// `\u{...}` is not.
    fn byte_escape(&mut self, backslash: usize) -> Result<u8, Diagnostic> {
        let Some(selector) = self.peek_at(0) else {
            return Err(Diagnostic::error(
                "unfinished escape",
                "expected an escape after this backslash",
                Span::new(backslash, self.bytes.len()),
            ));
        };
        self.cursor += 1;
        Ok(match selector {
            b'n' => b'\n',
            b'r' => b'\r',
            b't' => b'\t',
            b'0' => 0,
            b'"' => b'"',
            b'\'' => b'\'',
            b'\\' => b'\\',
            b'x' => self.hex_escape_pair(backslash)?,
            b'u' => {
                return Err(Diagnostic::error(
                    "invalid byte escape",
                    "`\\u{...}` escapes are not permitted in byte literals",
                    Span::new(backslash, self.cursor),
                )
                .with_help("use `\\xNN` to spell the byte value"));
            }
            _ => {
                return Err(Diagnostic::error(
                    "unknown escape",
                    "valid byte escapes are `\\n`, `\\r`, `\\t`, `\\0`, `\\\"`, `\\'`, `\\\\`, and `\\xNN`",
                    Span::new(backslash, self.cursor),
                ));
            }
        })
    }

    fn string(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        self.cursor += 1;
        let mut value = String::new();
        loop {
            match self.peek_at(0) {
                Some(b'"') => {
                    self.cursor += 1;
                    break;
                }
                Some(b'\\') => {
                    let backslash = self.cursor;
                    self.cursor += 1;
                    value.push(self.scalar_escape(backslash)?);
                }
                Some(_) => {
                    let character = self.source[self.cursor..].chars().next().unwrap();
                    value.push(character);
                    self.cursor += character.len_utf8();
                }
                None => {
                    return Err(Diagnostic::error(
                        "unfinished string",
                        "this string is never closed",
                        Span::new(start, self.bytes.len()),
                    )
                    .with_help("add a closing `\"`"));
                }
            }
        }
        self.push(TokenKind::String(value), start);
        Ok(())
    }

    fn byte_string(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        self.cursor += 2;
        let mut value = Vec::new();
        loop {
            match self.peek_at(0) {
                Some(b'"') => {
                    self.cursor += 1;
                    break;
                }
                Some(b'\\') => {
                    let backslash = self.cursor;
                    self.cursor += 1;
                    value.push(self.byte_escape(backslash)?);
                }
                Some(byte) if byte <= 0x7F => {
                    value.push(byte);
                    self.cursor += 1;
                }
                Some(_) => {
                    let character = self.source[self.cursor..].chars().next().unwrap();
                    return Err(Diagnostic::error(
                        "invalid byte string character",
                        format!("`{character}` is not ASCII"),
                        Span::new(self.cursor, self.cursor + character.len_utf8()),
                    )
                    .with_help("spell non-ASCII bytes with `\\xNN` escapes"));
                }
                None => {
                    return Err(Diagnostic::error(
                        "unfinished byte string",
                        "this byte string is never closed",
                        Span::new(start, self.bytes.len()),
                    )
                    .with_help("add a closing `\"`"));
                }
            }
        }
        self.push(TokenKind::ByteString(value), start);
        Ok(())
    }

    fn byte_literal(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        self.cursor += 2;
        let value = match self.peek_at(0) {
            Some(b'\\') => {
                let backslash = self.cursor;
                self.cursor += 1;
                self.byte_escape(backslash)?
            }
            Some(b'\'') => {
                return Err(Diagnostic::error(
                    "empty byte literal",
                    "a byte literal must contain exactly one byte",
                    Span::new(start, self.cursor + 1),
                ));
            }
            Some(byte) if byte <= 0x7F => {
                self.cursor += 1;
                byte
            }
            Some(_) => {
                let character = self.source[self.cursor..].chars().next().unwrap();
                return Err(Diagnostic::error(
                    "invalid byte literal",
                    format!("`{character}` is not ASCII"),
                    Span::new(self.cursor, self.cursor + character.len_utf8()),
                )
                .with_help("spell non-ASCII bytes with `\\xNN` escapes"));
            }
            None => {
                return Err(Diagnostic::error(
                    "unfinished byte literal",
                    "this byte literal is never closed",
                    Span::new(start, self.bytes.len()),
                ));
            }
        };
        if self.peek_at(0) != Some(b'\'') {
            return Err(Diagnostic::error(
                "unfinished byte literal",
                "expected `'` to close this byte literal",
                Span::new(start, self.cursor),
            ));
        }
        self.cursor += 1;
        self.push(TokenKind::Byte(value), start);
        Ok(())
    }

    fn char_or_lifetime(&mut self) -> Result<(), Diagnostic> {
        let start = self.cursor;
        match self.peek_at(1) {
            Some(b'\\') => {
                self.cursor += 2;
                let value = self.scalar_escape(start + 1)?;
                if self.peek_at(0) != Some(b'\'') {
                    return Err(Diagnostic::error(
                        "unfinished character literal",
                        "expected `'` to close this character literal",
                        Span::new(start, self.cursor),
                    ));
                }
                self.cursor += 1;
                self.push(TokenKind::Char(value), start);
                Ok(())
            }
            Some(b'\'') => Err(Diagnostic::error(
                "empty character literal",
                "a character literal must contain exactly one scalar",
                Span::new(start, start + 2),
            )),
            Some(_) => {
                let character = self.source[start + 1..].chars().next().unwrap();
                let after = start + 1 + character.len_utf8();
                if self.bytes.get(after) == Some(&b'\'') {
                    self.cursor = after + 1;
                    self.push(TokenKind::Char(character), start);
                    return Ok(());
                }
                // No closing quote after one scalar: a lifetime reference.
                self.cursor += 1;
                if !self
                    .peek_at(0)
                    .is_some_and(|byte| byte.is_ascii_alphabetic() || byte == b'_')
                {
                    return Err(Diagnostic::error(
                        "invalid lifetime identifier",
                        "expected an ASCII identifier after `'`",
                        Span::new(start, self.cursor),
                    ));
                }
                self.cursor += 1;
                while self.cursor < self.bytes.len()
                    && (self.bytes[self.cursor].is_ascii_alphanumeric()
                        || self.bytes[self.cursor] == b'_')
                {
                    self.cursor += 1;
                }
                if self.peek_at(0) == Some(b'\'') {
                    return Err(Diagnostic::error(
                        "invalid character literal",
                        "a character literal may contain exactly one scalar",
                        Span::new(start, self.cursor + 1),
                    )
                    .with_help("string literals use double quotes"));
                }
                self.push(
                    TokenKind::Lifetime(self.source[start..self.cursor].into()),
                    start,
                );
                Ok(())
            }
            None => Err(Diagnostic::error(
                "invalid lifetime identifier",
                "expected an ASCII identifier after `'`",
                Span::new(start, self.cursor + 1),
            )),
        }
    }
}
