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

use std::sync::OnceLock;

use crate::{
    diagnostic::Diagnostic,
    lexer::{Token, TokenKind},
    source_bundle::{DISTRIBUTED_STANDARD_LIBRARY_SOURCE, SourceBundle},
    span::Span,
};

static DISTRIBUTED_STANDARD_TOKENS: OnceLock<Vec<Token>> = OnceLock::new();

fn distributed_standard_tokens() -> &'static [Token] {
    DISTRIBUTED_STANDARD_TOKENS
        .get_or_init(|| match crate::lexer::lex(DISTRIBUTED_STANDARD_LIBRARY_SOURCE) {
            Ok(tokens) => tokens,
            Err(_) => panic!("embedded distributed standard library failed to lex"),
        })
        .as_slice()
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
}

#[derive(Clone, Default)]
pub struct IncrementalFrontendCache {
    entries: Vec<CachedLexSegment>,
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
                self.stats.reused_segments += 1;
                append_rebased_tokens(&mut combined, distributed_standard_tokens(), offset);
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
            }
        );
    }

    #[test]
    fn fresh_compiler_sessions_share_the_embedded_standard_tokens() {
        let bundle = SourceBundle::distributed(
            Segment::new("main.glorious", "main() -> () { () }"),
            [],
        );
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
}
