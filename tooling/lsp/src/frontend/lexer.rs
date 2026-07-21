use crate::frontend::{diagnostic::Diagnostic, span::Span};

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum TokenKind {
    Ident(String),
    Lifetime(String),
    Int(i64),
    String(String),
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

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    let bytes = source.as_bytes();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < bytes.len() {
        let start = i;
        match bytes[i] {
            b if b.is_ascii_whitespace() => i += 1,
            b'/' if bytes.get(i + 1) == Some(&b'/') => {
                i += 2;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
            }
            b'/' if bytes.get(i + 1) == Some(&b'*') => {
                i += 2;
                let mut depth = 1usize;
                while i < bytes.len() && depth > 0 {
                    if bytes.get(i..i + 2) == Some(b"/*") {
                        depth += 1;
                        i += 2;
                    } else if bytes.get(i..i + 2) == Some(b"*/") {
                        depth -= 1;
                        i += 2;
                    } else {
                        i += 1;
                    }
                }
                if depth > 0 {
                    return Err(Diagnostic::error(
                        "unfinished comment",
                        "this block comment is never closed",
                        Span::new(start, bytes.len()),
                    )
                    .with_help("add `*/` to close the comment"));
                }
            }
            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                i += 1;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                tokens.push(Token {
                    kind: TokenKind::Ident(source[start..i].into()),
                    span: Span::new(start, i),
                });
            }
            b'\'' => {
                i += 1;
                if !bytes
                    .get(i)
                    .is_some_and(|byte| byte.is_ascii_alphabetic() || *byte == b'_')
                {
                    return Err(Diagnostic::error(
                        "invalid lifetime identifier",
                        "expected an ASCII identifier after `'`",
                        Span::new(start, i),
                    ));
                }
                i += 1;
                while i < bytes.len() && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_') {
                    i += 1;
                }
                tokens.push(Token {
                    kind: TokenKind::Lifetime(source[start..i].into()),
                    span: Span::new(start, i),
                });
            }
            b'0'..=b'9' => {
                i += 1;
                while i < bytes.len() && bytes[i].is_ascii_digit() {
                    i += 1;
                }
                let value = source[start..i].parse().map_err(|_| {
                    Diagnostic::error(
                        "integer is too large",
                        "this integer does not fit in an i64",
                        Span::new(start, i),
                    )
                })?;
                tokens.push(Token {
                    kind: TokenKind::Int(value),
                    span: Span::new(start, i),
                });
            }
            b'"' => {
                i += 1;
                let mut value = String::new();
                let mut closed = false;
                while i < bytes.len() {
                    match bytes[i] {
                        b'"' => {
                            i += 1;
                            closed = true;
                            break;
                        }
                        b'\\' => {
                            i += 1;
                            let escaped = *bytes.get(i).ok_or_else(|| {
                                Diagnostic::error(
                                    "unfinished string",
                                    "expected an escape after this backslash",
                                    Span::new(start, i),
                                )
                            })?;
                            value.push(match escaped {
                                b'n' => '\n',
                                b'r' => '\r',
                                b't' => '\t',
                                b'"' => '"',
                                b'\\' => '\\',
                                _ => {
                                    return Err(Diagnostic::error(
                                        "unknown escape",
                                        "valid escapes are `\\n`, `\\r`, `\\t`, `\\\"`, and `\\\\`",
                                        Span::new(i - 1, i + 1),
                                    ));
                                }
                            });
                            i += 1;
                        }
                        _ => {
                            let ch = source[i..].chars().next().unwrap();
                            value.push(ch);
                            i += ch.len_utf8();
                        }
                    }
                }
                if !closed {
                    return Err(Diagnostic::error(
                        "unfinished string",
                        "this string is never closed",
                        Span::new(start, bytes.len()),
                    )
                    .with_help("add a closing `\"`"));
                }
                tokens.push(Token {
                    kind: TokenKind::String(value),
                    span: Span::new(start, i),
                });
            }
            _ => {
                let (kind, width) = match &bytes[i..] {
                    [b'-', b'>', ..] => (TokenKind::Arrow, 2),
                    [b'=', b'>', ..] => (TokenKind::FatArrow, 2),
                    [b':', b':', ..] => (TokenKind::DoubleColon, 2),
                    [b'.', b'.', ..] => (TokenKind::DotDot, 2),
                    [b'=', b'=', ..] => (TokenKind::EqEq, 2),
                    [b'!', b'=', ..] => (TokenKind::BangEq, 2),
                    [b'<', b'=', ..] => (TokenKind::LtEq, 2),
                    [b'>', b'=', ..] => (TokenKind::GtEq, 2),
                    [b'(', ..] => (TokenKind::LParen, 1),
                    [b')', ..] => (TokenKind::RParen, 1),
                    [b'{', ..] => (TokenKind::LBrace, 1),
                    [b'}', ..] => (TokenKind::RBrace, 1),
                    [b'[', ..] => (TokenKind::LBracket, 1),
                    [b']', ..] => (TokenKind::RBracket, 1),
                    [b',', ..] => (TokenKind::Comma, 1),
                    [b':', ..] => (TokenKind::Colon, 1),
                    [b';', ..] => (TokenKind::Semicolon, 1),
                    [b'.', ..] => (TokenKind::Dot, 1),
                    [b'/', ..] => (TokenKind::Slash, 1),
                    [b'+', ..] => (TokenKind::Plus, 1),
                    [b'-', ..] => (TokenKind::Minus, 1),
                    [b'*', ..] => (TokenKind::Star, 1),
                    [b'|', ..] => (TokenKind::Pipe, 1),
                    [b'=', ..] => (TokenKind::Eq, 1),
                    [b'<', ..] => (TokenKind::Lt, 1),
                    [b'>', ..] => (TokenKind::Gt, 1),
                    [b'&', ..] => (TokenKind::Amp, 1),
                    [b'!', ..] => (TokenKind::Bang, 1),
                    _ => {
                        let character = source[start..].chars().next().unwrap();
                        return Err(Diagnostic::error(
                            "unexpected character",
                            format!("`{}` is not part of Grandiose syntax", character),
                            Span::new(start, start + character.len_utf8()),
                        ));
                    }
                };
                i += width;
                tokens.push(Token {
                    kind,
                    span: Span::new(start, i),
                });
            }
        }
    }
    tokens.push(Token {
        kind: TokenKind::Eof,
        span: Span::new(bytes.len(), bytes.len()),
    });
    Ok(tokens)
}
