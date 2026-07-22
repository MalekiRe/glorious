//! Exact-content incremental caches for source-only frontend work.
//!
//! Parsed programs cannot safely be cached independently: their spans are
//! bundle-global and fixity/module resolution depends on declarations in other
//! segments. Lexed tokens are local to one segment, however, and can be
//! rebased without observing any other source. This cache deliberately keeps
//! the complete source alongside each token stream instead of trusting a hash.

use crate::{
    diagnostic::Diagnostic,
    lexer::{Token, TokenKind},
    source_bundle::SourceBundle,
    span::Span,
};

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
            let local = if let Some(cached) = self.entries.get(index)
                && cached.source == segment.source()
            {
                self.stats.reused_segments += 1;
                cached.tokens.clone()
            } else {
                let tokens = match crate::lexer::lex(segment.source()) {
                    Ok(tokens) => tokens,
                    // A lexical construct spanning a segment boundary is part
                    // of the historical bundle-stream semantics. Preserve it
                    // by asking the canonical lexer to diagnose/accept it.
                    Err(_) => {
                        self.stats.whole_bundle_fallbacks += 1;
                        return crate::lexer::lex(bundle.source());
                    }
                };
                self.stats.lexed_segments += 1;
                let cached = CachedLexSegment {
                    source: segment.source().to_owned(),
                    tokens: tokens.clone(),
                };
                if index < self.entries.len() {
                    self.entries[index] = cached;
                } else {
                    self.entries.push(cached);
                }
                tokens
            };
            let offset = segment.global_range().start;
            combined.extend(
                local
                    .into_iter()
                    .filter(|token| token.kind != TokenKind::Eof)
                    .map(|mut token| {
                        token.span.start += offset;
                        token.span.end += offset;
                        token
                    }),
            );
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
        assert_eq!(cache.stats().lexed_segments, 3);

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
