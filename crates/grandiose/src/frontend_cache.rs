//! Exact-content incremental caches for source-only frontend work.
//!
//! Parsed programs cannot safely be cached independently: their spans are
//! bundle-global and fixity/module resolution depends on declarations in other
//! segments. Lexed tokens are local to one segment, however, and can be
//! rebased without observing any other source. This cache deliberately keeps
//! the complete source alongside each token stream instead of trusting a hash.
//!
//! The embedded distributed standard library is immutable for the lifetime of
//! the compiler process, so its local token stream is shared by every driver
//! instead of being lexed once per test, editor session, or build command.

use std::{collections::HashMap, sync::OnceLock};

use crate::{
    ast::Program,
    diagnostic::Diagnostic,
    lexer::{Token, TokenKind},
    source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_SOURCE, SourceBundle},
    span::Span,
};

static DISTRIBUTED_STANDARD_TOKENS: OnceLock<Result<Vec<Token>, Diagnostic>> = OnceLock::new();

fn distributed_standard_tokens() -> Result<&'static [Token], Diagnostic> {
    match DISTRIBUTED_STANDARD_TOKENS
        .get_or_init(|| crate::lexer::lex(DISTRIBUTED_STANDARD_LIBRARY_SOURCE))
    {
        Ok(tokens) => Ok(tokens.as_slice()),
        Err(error) => Err(error.clone()),
    }
}

/// The distribution standard library is byte-for-byte fixed for a running
/// compiler.  Keep its *raw* AST separately from its token cache, then join
/// it with the current user AST before effect-surface normalization.  Doing
/// normalization after the join is important: standard effect declarations
/// remain visible to a user body exactly as they are in a monolithic parse.
fn parse_distributed_standard_program() -> Result<Program, Vec<Diagnostic>> {
    let tokens = distributed_standard_tokens()
        .map(|tokens| tokens.to_vec())
        .map_err(|error| vec![error])?;
    let (program, diagnostics) =
        crate::parser::parse_recovering_with_fixity_regions_raw(tokens, Vec::new());
    if diagnostics.is_empty() {
        Ok(program)
    } else {
        Err(diagnostics)
    }
}

fn append_rebased_tokens(output: &mut Vec<Token>, tokens: &[Token], offset: usize) {
    output.extend(
        tokens
            .iter()
            .filter(|token| token.kind != TokenKind::Eof)
            .cloned()
            .map(|mut token| {
                token.span.start += offset;
                token.span.end += offset;
                token
            }),
    );
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct FrontendCacheStats {
    pub lexed_segments: usize,
    pub reused_segments: usize,
    pub whole_bundle_fallbacks: usize,
    /// A cached parsed distributed standard program was joined with the
    /// request-local AST. This is zero whenever conservative parsing falls
    /// back to the canonical whole-bundle path.
    pub reused_standard_ast: usize,
}

#[derive(Clone, Default)]
pub struct IncrementalFrontendCache {
    entries: Vec<CachedLexSegment>,
    /// AST nodes use `Rc` and are deliberately session-local.  A persistent
    /// `grc --serve` owns this cache, avoiding a cross-thread static while
    /// retaining the immutable distribution parse between revisions.
    standard_program: Option<Result<Program, Vec<Diagnostic>>>,
    stats: FrontendCacheStats,
}

#[derive(Clone)]
struct CachedLexSegment {
    source: String,
    tokens: Vec<Token>,
}

impl IncrementalFrontendCache {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn begin_revision(&mut self) {
        self.stats = FrontendCacheStats::default();
    }

    pub fn stats(&self) -> FrontendCacheStats {
        self.stats
    }

    pub fn parse_bundle(
        &mut self,
        bundle: &SourceBundle,
    ) -> Result<crate::ast::Program, Vec<Diagnostic>> {
        crate::modules::parse_bundle_incremental(bundle, self)
    }

    pub(crate) fn lex_bundle(&mut self, bundle: &SourceBundle) -> Result<Vec<Token>, Diagnostic> {
        let mut combined = Vec::new();
        for (index, segment) in bundle.segments().iter().enumerate() {
            let offset = segment.global_range().start;

            // `SourceBundle::distributed` owns the only canonical embedded
            // standard-library role and always places it first. Its source and
            // token spans are immutable, so sharing this stream cannot leak
            // authority to a caller-controlled segment.
            if bundle.is_canonical_distribution() && index == 0 {
                // Keep later entries aligned with their bundle segment index.
                // The empty sentinel is also a valid token cache for an empty
                // raw segment if this driver later changes bundle kind.
                if self.entries.is_empty() {
                    self.entries.push(CachedLexSegment {
                        source: String::new(),
                        tokens: Vec::new(),
                    });
                }
                let tokens = distributed_standard_tokens()?;
                self.stats.reused_segments += 1;
                append_rebased_tokens(&mut combined, tokens, offset);
                continue;
            }

            if let Some(cached) = self
                .entries
                .get(index)
                .filter(|cached| cached.source == segment.source())
            {
                append_rebased_tokens(&mut combined, &cached.tokens, offset);
                self.stats.reused_segments += 1;
                continue;
            }

            let tokens = match crate::lexer::lex(segment.source()) {
                Ok(tokens) => tokens,
                // A lexical construct spanning a segment boundary is part of
                // the historical bundle-stream semantics. Preserve it by
                // asking the canonical lexer to diagnose/accept it.
                Err(_) => {
                    self.stats.whole_bundle_fallbacks += 1;
                    return crate::lexer::lex(bundle.source());
                }
            };
            self.stats.lexed_segments += 1;
            append_rebased_tokens(&mut combined, &tokens, offset);
            let cached = CachedLexSegment {
                source: segment.source().to_owned(),
                tokens,
            };
            if index < self.entries.len() {
                self.entries[index] = cached;
            } else {
                self.entries.push(cached);
            }
        }
        self.entries.truncate(bundle.segments().len());
        combined.push(Token {
            kind: TokenKind::Eof,
            span: Span::new(bundle.source().len(), bundle.source().len()),
        });
        Ok(combined)
    }

    /// Returns a program assembled from the immutable standard AST and a
    /// request-local user AST only in the exact context where that is
    /// observationally equivalent to the canonical parser.  In particular,
    /// any user-controlled fixity keyword takes the whole-bundle route: a
    /// later declaration can otherwise influence grouping in an earlier
    /// segment through the parser's global fallback table.
    pub(crate) fn parse_distributed_bundle_with_cached_standard_ast(
        &mut self,
        bundle: &SourceBundle,
    ) -> Option<Result<Program, Vec<Diagnostic>>> {
        if !bundle.is_canonical_distribution()
            || bundle.segments().first().is_none_or(|segment| {
                segment.source() != DISTRIBUTED_STANDARD_LIBRARY_SOURCE
                    || segment.global_range().start != 0
                    || segment.global_range().end != DISTRIBUTED_STANDARD_LIBRARY_SOURCE.len()
            })
        {
            return None;
        }

        let tokens = match self.lex_bundle(bundle) {
            Ok(tokens) => tokens,
            Err(error) => return Some(Err(vec![error])),
        };
        let standard_end = DISTRIBUTED_STANDARD_LIBRARY_SOURCE.len();
        if tokens.iter().any(|token| {
            token.span.start > standard_end
                && matches!(
                    &token.kind,
                    TokenKind::Ident(keyword)
                        if matches!(keyword.as_str(), "infixl" | "infixr" | "infix" | "prefix")
                )
        }) {
            return None;
        }

        let standard = match self
            .standard_program
            .get_or_insert_with(parse_distributed_standard_program)
        {
            Ok(program) => program,
            Err(diagnostics) => return Some(Err(diagnostics.clone())),
        };
        let standard_fixities = standard
            .fixities
            .iter()
            .map(|fixity| {
                (
                    fixity.name.clone(),
                    crate::parser::ScopedFixity {
                        kind: fixity.kind,
                        precedence: fixity.precedence,
                        declaration: Some(fixity.span),
                    },
                )
            })
            .collect::<HashMap<_, _>>();
        let regions = bundle
            .segments()
            .iter()
            .skip(1)
            .map(|segment| crate::parser::FixityRegion {
                span: Span::new(segment.global_range().start, segment.global_range().end),
                fixities: standard_fixities.clone(),
            })
            .collect();
        let user_tokens = tokens
            .into_iter()
            .filter(|token| token.span.start > standard_end || token.kind == TokenKind::Eof)
            .collect();
        let (user, diagnostics) =
            crate::parser::parse_recovering_with_fixity_regions_raw(user_tokens, regions);
        if !diagnostics.is_empty() {
            return Some(Err(diagnostics));
        }
        let mut program = standard.clone();
        append_program(&mut program, user);
        let diagnostics = crate::parser::normalize_effect_surface_program(&mut program);
        if diagnostics.is_empty() {
            self.stats.reused_standard_ast += 1;
            Some(Ok(program))
        } else {
            Some(Err(diagnostics))
        }
    }
}

fn append_program(into: &mut Program, from: Program) {
    into.modules.extend(from.modules);
    into.imports.extend(from.imports);
    into.item_visibilities.extend(from.item_visibilities);
    into.type_aliases.extend(from.type_aliases);
    into.effect_row_aliases.extend(from.effect_row_aliases);
    into.globals.extend(from.globals);
    into.fixities.extend(from.fixities);
    into.structs.extend(from.structs);
    into.enums.extend(from.enums);
    into.traits.extend(from.traits);
    into.impls.extend(from.impls);
    into.uses.extend(from.uses);
    into.effects.extend(from.effects);
    into.drops.extend(from.drops);
    into.functions.extend(from.functions);
    into.effect_paths.extend(from.effect_paths);
    into.type_const_arguments.extend(from.type_const_arguments);
    into.fixed_array_types.extend(from.fixed_array_types);
    into.numeric_literals.extend(from.numeric_literals);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::source_bundle::Segment;

    #[test]
    fn unchanged_segments_reuse_exact_token_streams_with_rebased_spans() {
        let first = SourceBundle::distributed(
            Segment::new("main.glorious", "main() -> i64 { helper() }"),
            [Segment::new("helper.glorious", "helper() -> i64 { 1 }")],
        );
        let changed = SourceBundle::distributed(
            Segment::new("main.glorious", "main() -> i64 { helper() }"),
            [Segment::new("helper.glorious", "helper() -> i64 { 2 }")],
        );
        let mut cache = IncrementalFrontendCache::new();

        let first_tokens = cache.lex_bundle(&first).unwrap();
        assert_eq!(first_tokens, crate::lexer::lex(first.source()).unwrap());
        assert_eq!(cache.stats().lexed_segments, 2);
        assert_eq!(cache.stats().reused_segments, 1);

        cache.begin_revision();
        let changed_tokens = cache.lex_bundle(&changed).unwrap();
        assert_eq!(changed_tokens, crate::lexer::lex(changed.source()).unwrap());
        assert_eq!(
            cache.stats(),
            FrontendCacheStats {
                lexed_segments: 1,
                reused_segments: 2,
                whole_bundle_fallbacks: 0,
                reused_standard_ast: 0,
            }
        );
    }

    #[test]
    fn fresh_compiler_sessions_share_the_embedded_standard_tokens() {
        let bundle =
            SourceBundle::distributed(Segment::new("main.glorious", "main() -> () { () }"), []);
        let mut first = IncrementalFrontendCache::new();
        let mut second = IncrementalFrontendCache::new();

        let first_tokens = first.lex_bundle(&bundle).unwrap();
        let second_tokens = second.lex_bundle(&bundle).unwrap();
        assert_eq!(first_tokens, second_tokens);
        assert_eq!(
            first.stats(),
            FrontendCacheStats {
                lexed_segments: 1,
                reused_segments: 1,
                whole_bundle_fallbacks: 0,
                reused_standard_ast: 0,
            }
        );
        assert_eq!(second.stats(), first.stats());
    }

    #[test]
    fn cross_segment_lexical_constructs_fall_back_to_stream_semantics() {
        let bundle = SourceBundle::raw_for_conformance(
            Segment::new("std.glorious", ""),
            Segment::new("main.glorious", "/*"),
            [Segment::new("tail.glorious", "*/ main() -> () { () }")],
        );
        let mut cache = IncrementalFrontendCache::new();

        let cached = cache.lex_bundle(&bundle).unwrap();
        assert_eq!(cached, crate::lexer::lex(bundle.source()).unwrap());
        assert_eq!(cache.stats().whole_bundle_fallbacks, 1);
    }

    #[test]
    fn distributed_standard_ast_is_reused_without_changing_program_spans() {
        let first = SourceBundle::distributed(
            Segment::new("main.glorious", "main() -> i64 { 1 + 2 }"),
            [Segment::new("helper.glorious", "helper() -> i64 { 3 * 4 }")],
        );
        let changed = SourceBundle::distributed(
            Segment::new("main.glorious", "main() -> i64 { 1 + 2 }"),
            [Segment::new("helper.glorious", "helper() -> i64 { 3 * 5 }")],
        );
        let mut cache = IncrementalFrontendCache::new();

        let expected = crate::modules::parse_bundle(&first).unwrap();
        let actual = cache.parse_bundle(&first).unwrap();
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(cache.stats().reused_standard_ast, 1);

        cache.begin_revision();
        let expected = crate::modules::parse_bundle(&changed).unwrap();
        let actual = cache.parse_bundle(&changed).unwrap();
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(cache.stats().reused_standard_ast, 1);
        assert_eq!(cache.stats().lexed_segments, 1);
    }

    #[test]
    fn user_fixity_declaration_uses_canonical_bundle_parser() {
        let bundle = SourceBundle::distributed(
            Segment::new("main.glorious", "infixr 31 +; main() -> i64 { 1 + 2 + 3 }"),
            [],
        );
        let mut cache = IncrementalFrontendCache::new();

        let expected = crate::modules::parse_bundle(&bundle);
        let actual = cache.parse_bundle(&bundle);
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        assert_eq!(cache.stats().reused_standard_ast, 0);
    }
}
