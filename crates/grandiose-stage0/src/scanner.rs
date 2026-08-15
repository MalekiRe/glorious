//! Structural top-level declaration scanning.
//!
//! This phase deliberately consumes the lossless token stream and delimiter
//! map rather than parsing bodies. It establishes the complete declaration
//! skeleton required by headers, module resolution, interfaces, and IDE
//! outlines while preserving one-body-at-a-time parsing later in the pipeline.

use crate::source::{LexedFile, Span, TokenKind};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DeclarationKind {
    Function,
    /// A callable supplied by the embedding host, never a source body.
    HostImport,
    Struct,
    Enum,
    Trait,
    Implementation,
    Effect,
    TypeAlias,
    Constant,
    /// A frozen top-level value forwarding contract: `let alias = target;`.
    ValueAlias,
    Module,
    Import,
    Fixity,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TokenRange {
    pub start: usize,
    pub end: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationShell {
    pub kind: DeclarationKind,
    pub name: Option<String>,
    pub visibility_public: bool,
    /// `auto trait` is retained by scanning so header parsing can preserve
    /// the declaration's solver policy without inspecting source text again.
    pub auto_trait: bool,
    /// Exact request capability required by a host-import declaration.
    pub host_capability: Option<String>,
    pub span: Span,
    pub header: TokenRange,
    pub body: Option<TokenRange>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ScanDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: &'static str,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct DeclarationScan {
    pub declarations: Vec<DeclarationShell>,
    pub diagnostics: Vec<ScanDiagnostic>,
}

impl DeclarationScan {
    pub fn scan(lexed: &LexedFile, source: &str) -> Self {
        Self::scan_range(
            lexed,
            source,
            TokenRange {
                start: 0,
                end: lexed.tokens.len(),
            },
        )
    }

    /// Scan declarations inside an already delimiter-validated token range.
    /// Inline module bodies use this entry point; their shells retain original
    /// file token indices and spans, so all downstream identity and source-map
    /// products remain anchored in the immutable parent source blob.
    pub fn scan_range(lexed: &LexedFile, source: &str, range: TokenRange) -> Self {
        let start = range.start.min(lexed.tokens.len());
        let end = range.end.min(lexed.tokens.len()).max(start);
        let significant = lexed
            .tokens
            .get(start..end)
            .expect("clamped token range is valid")
            .iter()
            .enumerate()
            .filter_map(|(offset, token)| (!is_trivia(&token.kind)).then_some(start + offset))
            .collect::<Vec<_>>();
        let mut scanner = Scanner {
            lexed,
            source,
            significant,
            position: 0,
            declarations: vec![],
            diagnostics: vec![],
        };
        while scanner.current().is_some() {
            scanner.next_declaration();
        }
        scanner
            .diagnostics
            .sort_by_key(|diagnostic| diagnostic.span.start);
        Self {
            declarations: scanner.declarations,
            diagnostics: scanner.diagnostics,
        }
    }
}

struct Scanner<'a> {
    lexed: &'a LexedFile,
    source: &'a str,
    significant: Vec<usize>,
    position: usize,
    declarations: Vec<DeclarationShell>,
    diagnostics: Vec<ScanDiagnostic>,
}

impl Scanner<'_> {
    fn next_declaration(&mut self) {
        let start_position = self.position;
        let mut public = false;
        if self.word_at(self.position) == Some("pub") {
            public = true;
            self.position += 1;
        }
        let auto_trait = self.word_at(self.position) == Some("auto");
        if auto_trait {
            self.position += 1;
        }
        let host_capability = if self.word_at(self.position) == Some("host") {
            self.position += 1;
            let Some(capability) = self.word_at(self.position).map(str::to_owned) else {
                self.unexpected(start_position);
                return;
            };
            self.position += 1;
            Some(capability)
        } else {
            None
        };
        let Some(keyword) = self.word_at(self.position).map(str::to_owned) else {
            self.unexpected(start_position);
            return;
        };
        // Canonical source permits a callable declaration to start directly
        // with its identifier (`map<T>(...)`), in addition to the explicit
        // `fn map<T>(...)` spelling.  Recognize only an identifier followed
        // by a callable introducer so an ordinary unknown top-level token is
        // still diagnosed instead of silently becoming a declaration.
        let bare_callable = declaration_kind(&keyword).is_none() && self.bare_callable_ahead();
        let Some(mut kind) =
            declaration_kind(&keyword).or(bare_callable.then_some(DeclarationKind::Function))
        else {
            self.unexpected(start_position);
            return;
        };
        if auto_trait && kind != DeclarationKind::Trait {
            self.unexpected(start_position);
            return;
        }
        if host_capability.is_some() {
            if kind != DeclarationKind::Function || auto_trait {
                self.unexpected(start_position);
                return;
            }
            kind = DeclarationKind::HostImport;
        }
        let declaration_position = self.position;
        self.position += 1;
        let name = if bare_callable {
            Some(keyword)
        } else {
            self.name_after(kind)
        };
        let header_start = self.significant[start_position];
        let (header_end, body, next_position) = self.find_boundary(kind, declaration_position);
        let span = Span {
            file: self.lexed.file,
            start: self.lexed.tokens[header_start].span.start,
            end: self.lexed.tokens[header_end.saturating_sub(1)].span.end,
        };
        self.declarations.push(DeclarationShell {
            kind,
            name,
            visibility_public: public,
            auto_trait,
            host_capability,
            span,
            header: TokenRange {
                start: header_start,
                end: body.map_or(header_end, |body| body.start),
            },
            body,
        });
        self.position = next_position;
    }

    fn name_after(&self, kind: DeclarationKind) -> Option<String> {
        if matches!(
            kind,
            DeclarationKind::Implementation | DeclarationKind::Import
        ) {
            return None;
        }
        // A fixity shell is `infixl|infixr|infix|prefix PRECEDENCE OPERATOR;`.
        // Its semantic name is the operator, rather than the form keyword or
        // precedence literal.  Keeping it on the shell gives interfaces the
        // same stable ownership/name treatment as every other declaration.
        if kind == DeclarationKind::Fixity {
            let index = self.significant.get(self.position + 1).copied()?;
            let token = &self.lexed.tokens[index];
            return matches!(token.kind, TokenKind::Identifier | TokenKind::Operator)
                .then(|| self.lexed.text(self.source, token).to_owned());
        }
        if kind == DeclarationKind::ValueAlias {
            let mut position = self.position;
            let mut path = vec![];
            loop {
                let index = self.significant.get(position).copied()?;
                let token = &self.lexed.tokens[index];
                if token.kind != TokenKind::Identifier {
                    return None;
                }
                path.push(self.lexed.text(self.source, token).to_owned());
                let separated = self
                    .significant
                    .get(position + 1)
                    .zip(self.significant.get(position + 2))
                    .is_some_and(|(left, right)| {
                        self.lexed.tokens[*left].kind == TokenKind::Punctuation(':')
                            && self.lexed.tokens[*right].kind == TokenKind::Punctuation(':')
                    });
                if !separated {
                    break;
                }
                position += 3;
            }
            return Some(path.join("::"));
        }
        self.current().and_then(|index| {
            let token = &self.lexed.tokens[index];
            (token.kind == TokenKind::Identifier)
                .then(|| self.lexed.text(self.source, token).to_owned())
        })
    }

    fn find_boundary(
        &mut self,
        kind: DeclarationKind,
        declaration_position: usize,
    ) -> (usize, Option<TokenRange>, usize) {
        let mut cursor = self.position;
        let mut initializer_start = None;
        // Header applications may contain braced effect-row arguments, e.g.
        // `Capability<{Trace, | e}>`. Track only header-level angle nesting
        // so those braces are skipped as syntax while the declaration body
        // remains the first brace at depth zero.
        let mut generic_depth = 0u32;
        while let Some(token_index) = self.significant.get(cursor).copied() {
            let token = &self.lexed.tokens[token_index];
            match token.kind {
                TokenKind::Operator if self.lexed.text(self.source, token) == "<" => {
                    generic_depth = generic_depth.saturating_add(1);
                    cursor += 1;
                }
                TokenKind::Operator if self.lexed.text(self.source, token) == ">" => {
                    generic_depth = generic_depth.saturating_sub(1);
                    cursor += 1;
                }
                TokenKind::Operator
                    if matches!(
                        kind,
                        DeclarationKind::Constant | DeclarationKind::ValueAlias
                    ) && self.lexed.text(self.source, token) == "=" =>
                {
                    cursor += 1;
                    initializer_start = self.significant.get(cursor).copied();
                }
                // An import tree may contain `{...}` selectors.  Those braces
                // are part of the header, never a declaration body.
                TokenKind::Punctuation('{') if kind == DeclarationKind::Import => cursor += 1,
                // An explicit effect-row generic argument is also header
                // syntax. Unlike a callable's `/ { ... }` row, this form is
                // identified structurally by an enclosing `<...>` application
                // and is valid on trait, effect, and implementation headers.
                TokenKind::Punctuation('{') if generic_depth > 0 => {
                    let Some(close) = self.lexed.delimiters.matching(token_index) else {
                        self.diagnostics.push(ScanDiagnostic {
                            code: "G2001",
                            span: token.span,
                            message: "effect-row generic argument has an unclosed delimiter",
                        });
                        return (token_index + 1, None, cursor + 1);
                    };
                    cursor = self
                        .significant
                        .binary_search(&close)
                        .expect("matched delimiter is significant")
                        + 1;
                }
                // A braced callable effect row is part of a callable header,
                // not its body.  This includes a callable type alias such as
                // `type Callback = () -> T / {Trace};`: aliases have no body
                // at all, so treating the row as one truncates the target
                // before header parsing. The scanner need not understand
                // effect-row members: a preceding `/` is the unambiguous
                // structural delimiter, and the lossless delimiter map skips
                // the row.
                TokenKind::Punctuation('{')
                    if matches!(
                        kind,
                        DeclarationKind::Function
                            | DeclarationKind::HostImport
                            | DeclarationKind::TypeAlias
                    ) && self.significant.get(cursor.saturating_sub(1)).is_some_and(
                        |previous| {
                            self.lexed.tokens[*previous].kind == TokenKind::Operator
                                && self.lexed.text(self.source, &self.lexed.tokens[*previous])
                                    == "/"
                        },
                    ) =>
                {
                    let Some(close) = self.lexed.delimiters.matching(token_index) else {
                        self.diagnostics.push(ScanDiagnostic {
                            code: "G2001",
                            span: token.span,
                            message: "effect row has an unclosed delimiter",
                        });
                        return (token_index + 1, None, cursor + 1);
                    };
                    cursor = self
                        .significant
                        .binary_search(&close)
                        .expect("matched delimiter is significant")
                        + 1;
                }
                // A top-level `let` is terminated by its semicolon, never
                // by an expression delimiter. Keep constructor records,
                // tuples, arrays, and nested call arguments inside the lazy
                // initializer range instead of mistaking `{ ... }` for a
                // declaration body.
                TokenKind::Punctuation('(' | '[' | '{')
                    if kind == DeclarationKind::ValueAlias && initializer_start.is_some() =>
                {
                    let Some(close) = self.lexed.delimiters.matching(token_index) else {
                        self.diagnostics.push(ScanDiagnostic {
                            code: "G2001",
                            span: token.span,
                            message: "top-level value initializer has an unclosed delimiter",
                        });
                        return (token_index + 1, None, cursor + 1);
                    };
                    cursor = self
                        .significant
                        .binary_search(&close)
                        .expect("matched delimiter is significant")
                        + 1;
                }
                TokenKind::Punctuation('{') => match self.lexed.delimiters.matching(token_index) {
                    Some(close) => {
                        let close_position = self
                            .significant
                            .binary_search(&close)
                            .expect("matched delimiter is significant");
                        let body = TokenRange {
                            start: token_index,
                            end: close + 1,
                        };
                        return (close + 1, Some(body), close_position + 1);
                    }
                    None => {
                        self.diagnostics.push(ScanDiagnostic {
                            code: "G2001",
                            span: token.span,
                            message: "declaration body has an unclosed delimiter",
                        });
                        return (token_index + 1, None, cursor + 1);
                    }
                },
                TokenKind::Punctuation(';') => {
                    let body = if matches!(
                        kind,
                        DeclarationKind::Constant | DeclarationKind::ValueAlias
                    ) {
                        initializer_start.map(|start| TokenRange {
                            start,
                            end: token_index,
                        })
                    } else {
                        None
                    };
                    return (token_index + 1, body, cursor + 1);
                }
                TokenKind::End => {
                    self.diagnostics.push(ScanDiagnostic {
                        code: if kind == DeclarationKind::ValueAlias && initializer_start.is_some()
                        {
                            "G3221"
                        } else {
                            "G2002"
                        },
                        span: self.lexed.tokens[self.significant[declaration_position]].span,
                        message: if kind == DeclarationKind::ValueAlias
                            && initializer_start.is_some()
                        {
                            "expected `;` after top-level value declaration"
                        } else {
                            "declaration has no body or terminator"
                        },
                    });
                    return (token_index, None, cursor);
                }
                _ => cursor += 1,
            }
        }
        let last = self.lexed.tokens.len().saturating_sub(1);
        (last, None, self.significant.len())
    }

    fn unexpected(&mut self, position: usize) {
        let Some(index) = self.significant.get(position).copied() else {
            return;
        };
        self.diagnostics.push(ScanDiagnostic {
            code: "G2003",
            span: self.lexed.tokens[index].span,
            message: "expected a top-level declaration",
        });
        self.position = position + 1;
    }

    fn current(&self) -> Option<usize> {
        self.significant
            .get(self.position)
            .copied()
            .filter(|index| self.lexed.tokens[*index].kind != TokenKind::End)
    }

    /// A bare callable's name is the current identifier; its next
    /// significant token must begin either a generic parameter list or an
    /// ordinary parameter list. This deliberately excludes arbitrary words
    /// from the declaration namespace.
    fn bare_callable_ahead(&self) -> bool {
        let Some(next) = self.significant.get(self.position + 1).copied() else {
            return false;
        };
        matches!(self.lexed.tokens[next].kind, TokenKind::Punctuation('('))
            || (self.lexed.tokens[next].kind == TokenKind::Operator
                && self.lexed.text(self.source, &self.lexed.tokens[next]) == "<")
    }

    fn word_at(&self, position: usize) -> Option<&str> {
        let index = self.significant.get(position).copied()?;
        let token = &self.lexed.tokens[index];
        (token.kind == TokenKind::Identifier).then(|| self.lexed.text(self.source, token))
    }
}

fn declaration_kind(keyword: &str) -> Option<DeclarationKind> {
    Some(match keyword {
        "fn" => DeclarationKind::Function,
        "struct" => DeclarationKind::Struct,
        "enum" => DeclarationKind::Enum,
        "trait" => DeclarationKind::Trait,
        "impl" => DeclarationKind::Implementation,
        "effect" => DeclarationKind::Effect,
        "type" => DeclarationKind::TypeAlias,
        "const" => DeclarationKind::Constant,
        "let" => DeclarationKind::ValueAlias,
        "mod" => DeclarationKind::Module,
        "use" => DeclarationKind::Import,
        "infixl" | "infixr" | "infix" | "prefix" => DeclarationKind::Fixity,
        _ => return None,
    })
}

fn is_trivia(kind: &TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
    )
}
