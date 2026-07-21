use std::{io, ops::Range};

use crate::{diagnostic::Diagnostic, span::Span};

pub const DISTRIBUTED_STANDARD_LIBRARY_NAME: &str = "<grandiose:std>";
pub const DISTRIBUTED_STANDARD_LIBRARY_SOURCE: &str = include_str!("distributed_std.gr");

/// A bundle-local source identity. Numeric values have no artifact meaning and
/// cannot grant authority; the trusted-standard role is private to bundle
/// construction.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SegmentId(u32);

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SegmentRole {
    User,
    TrustedDistributedStandard,
}

/// One UTF-8 input in a generation-1 source bundle.
///
/// A segment's global range covers only its original bytes. The newline that
/// the bundle inserts after a segment is deliberately not attributed to either
/// neighboring file.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Segment {
    name: String,
    source: String,
    global_range: Range<usize>,
    id: Option<SegmentId>,
    role: SegmentRole,
}

impl Segment {
    pub fn new(name: impl Into<String>, source: impl Into<String>) -> Self {
        let source = source.into();
        Self {
            name: name.into(),
            global_range: 0..source.len(),
            source,
            id: None,
            role: SegmentRole::User,
        }
    }

    fn distributed_standard() -> Self {
        Self {
            name: DISTRIBUTED_STANDARD_LIBRARY_NAME.into(),
            source: DISTRIBUTED_STANDARD_LIBRARY_SOURCE.into(),
            global_range: 0..DISTRIBUTED_STANDARD_LIBRARY_SOURCE.len(),
            id: None,
            role: SegmentRole::TrustedDistributedStandard,
        }
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn global_range(&self) -> Range<usize> {
        self.global_range.clone()
    }

    pub fn id(&self) -> Option<SegmentId> {
        self.id
    }
}

/// The canonical generation-1 compilation stream and its diagnostic map.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SourceBundle {
    source: String,
    segments: Vec<Segment>,
    canonical_distribution: bool,
}

impl SourceBundle {
    /// Builds the distribution-facing `embedded std + primary + additional`
    /// stream. The embedded segment is the only segment carrying trusted
    /// standard-library authority.
    pub fn distributed(primary: Segment, additional: impl IntoIterator<Item = Segment>) -> Self {
        let mut segments = vec![Segment::distributed_standard(), primary];
        segments.extend(additional);
        Self::assemble(segments, Some(0), true)
    }

    /// Builds an explicitly raw, entirely untrusted fixture stream in
    /// `standard + primary + additional` order.
    pub fn raw_for_conformance(
        standard_library: Segment,
        primary: Segment,
        additional: impl IntoIterator<Item = Segment>,
    ) -> Self {
        let mut segments = vec![standard_library, primary];
        segments.extend(additional);
        Self::assemble(segments, None, false)
    }

    /// Builds a raw conformance fixture whose first segment intentionally acts
    /// as a stand-in trusted standard library. Distribution-facing APIs never
    /// call this constructor.
    pub fn raw_with_trusted_standard_for_conformance(
        standard_library: Segment,
        primary: Segment,
        additional: impl IntoIterator<Item = Segment>,
    ) -> Self {
        let mut segments = vec![standard_library, primary];
        segments.extend(additional);
        Self::assemble(segments, Some(0), false)
    }

    /// Legacy raw fixture spelling. It no longer grants authority based on the
    /// first segment's position; new fixtures should use
    /// [`SourceBundle::raw_for_conformance`] explicitly.
    pub fn new(
        standard_library: Segment,
        primary: Segment,
        additional: impl IntoIterator<Item = Segment>,
    ) -> Self {
        let mut segments = vec![standard_library, primary];
        segments.extend(additional);
        Self::assemble(segments, None, false)
    }

    fn assemble(
        mut segments: Vec<Segment>,
        trusted: Option<usize>,
        canonical_distribution: bool,
    ) -> Self {
        for (index, segment) in segments.iter_mut().enumerate() {
            segment.id = Some(SegmentId(index as u32));
            segment.role = if Some(index) == trusted {
                SegmentRole::TrustedDistributedStandard
            } else {
                SegmentRole::User
            };
        }
        let content_len = segments
            .iter()
            .map(|segment| segment.source.len())
            .sum::<usize>();
        let mut source = String::with_capacity(content_len + segments.len().saturating_sub(1));
        for (index, segment) in segments.iter_mut().enumerate() {
            if index != 0 {
                source.push('\n');
            }
            let start = source.len();
            source.push_str(&segment.source);
            segment.global_range = start..source.len();
        }
        Self {
            source,
            segments,
            canonical_distribution,
        }
    }

    /// Whether this bundle was assembled by the distribution constructor and
    /// therefore must be paired with the distribution runtime manifest. Raw
    /// trusted conformance fixtures deliberately remain distinguishable.
    pub(crate) fn is_canonical_distribution(&self) -> bool {
        self.canonical_distribution
    }

    pub(crate) fn trusted_standard_segment_id(&self) -> Option<SegmentId> {
        self.segments
            .iter()
            .find(|segment| segment.role == SegmentRole::TrustedDistributedStandard)
            .and_then(|segment| segment.id)
    }

    pub(crate) fn trusted_standard_global_range(&self) -> Option<Range<usize>> {
        self.segments
            .iter()
            .find(|segment| segment.role == SegmentRole::TrustedDistributedStandard)
            .map(Segment::global_range)
    }

    pub fn source(&self) -> &str {
        &self.source
    }

    pub fn segments(&self) -> &[Segment] {
        &self.segments
    }

    /// Locates an original source byte. Inserted boundary newlines return
    /// `None`; the end-of-bundle offset maps to the final segment for EOF
    /// diagnostics.
    pub fn segment_at(&self, global_offset: usize) -> Option<&Segment> {
        self.segments
            .iter()
            .find(|segment| segment.global_range.contains(&global_offset))
            .or_else(|| {
                (global_offset == self.source.len())
                    .then(|| self.segments.last())
                    .flatten()
            })
    }

    /// Maps a global span when all its bytes belong to one original input.
    /// Spans containing an inserted boundary newline intentionally do not map.
    pub fn map_span(&self, global: Span) -> Option<MappedSpan<'_>> {
        let segment = if global.start == global.end {
            self.segment_at(global.start)?
        } else {
            self.segments.iter().find(|segment| {
                global.start >= segment.global_range.start && global.end <= segment.global_range.end
            })?
        };
        Some(MappedSpan {
            segment,
            span: Span::new(
                global.start - segment.global_range.start,
                global.end - segment.global_range.start,
            ),
        })
    }

    /// Produces a diagnostic-only view with every independently mappable label
    /// translated back to its file-local byte offsets.
    pub fn map_diagnostic<'a>(&'a self, diagnostic: &'a Diagnostic) -> MappedDiagnostic<'a> {
        MappedDiagnostic {
            diagnostic,
            span: diagnostic.span.and_then(|span| self.map_span(span)),
            related: diagnostic
                .related
                .iter()
                .filter_map(|(span, message)| {
                    self.map_span(*span).map(|span| (span, message.as_str()))
                })
                .collect(),
        }
    }

    /// Converts a bundle-global diagnostic into the local coordinates of its
    /// primary source segment. Related labels in that same segment are retained;
    /// cross-segment labels remain available through [`SourceBundle::write_diagnostic`].
    pub fn localize_diagnostic(&self, mut diagnostic: Diagnostic) -> Diagnostic {
        let Some(primary) = diagnostic.span.and_then(|span| self.map_span(span)) else {
            return diagnostic;
        };
        diagnostic.source_name = primary.segment.name.clone();
        diagnostic.span = Some(primary.span);
        diagnostic.related = diagnostic
            .related
            .into_iter()
            .filter_map(|(span, message)| {
                let mapped = self.map_span(span)?;
                (mapped.segment.id == primary.segment.id).then_some((mapped.span, message))
            })
            .collect();
        diagnostic
    }

    /// Renders a bundle-global diagnostic using local files and offsets.
    /// Cross-file related labels are emitted as separate related-location
    /// reports because `Diagnostic` itself has a single source identity.
    pub fn write_diagnostic(
        &self,
        diagnostic: &Diagnostic,
        mut output: impl io::Write,
    ) -> io::Result<()> {
        let Some(primary) = diagnostic.span.and_then(|span| self.map_span(span)) else {
            return diagnostic.write(&self.source, output);
        };

        let mut localized = diagnostic.clone();
        localized.source_name = primary.segment.name.clone();
        localized.embedded_source = Some(primary.segment.source.clone());
        localized.span = Some(primary.span);
        localized.related = diagnostic
            .related
            .iter()
            .filter_map(|(span, message)| {
                let mapped = self.map_span(*span)?;
                std::ptr::eq(mapped.segment, primary.segment)
                    .then(|| (mapped.span, message.clone()))
            })
            .collect();
        localized.write(primary.segment.source(), &mut output)?;

        for (span, message) in &diagnostic.related {
            let Some(mapped) = self.map_span(*span) else {
                continue;
            };
            if std::ptr::eq(mapped.segment, primary.segment) {
                continue;
            }
            Diagnostic::advice("related location", message, mapped.span)
                .with_embedded_source(mapped.segment.name(), mapped.segment.source())
                .write(mapped.segment.source(), &mut output)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct MappedSpan<'a> {
    pub segment: &'a Segment,
    pub span: Span,
}

#[derive(Debug)]
pub struct MappedDiagnostic<'a> {
    pub diagnostic: &'a Diagnostic,
    pub span: Option<MappedSpan<'a>>,
    pub related: Vec<(MappedSpan<'a>, &'a str)>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_empty_inputs_and_inserts_one_newline_per_boundary() {
        let bundle = SourceBundle::new(
            Segment::new("std-lib.glorious", ""),
            Segment::new("main.glorious", "main"),
            [Segment::new("empty.glorious", "")],
        );
        assert_eq!(bundle.source(), "\nmain\n");
        assert_eq!(bundle.segments()[0].global_range(), 0..0);
        assert_eq!(bundle.segments()[1].global_range(), 1..5);
        assert_eq!(bundle.segments()[2].global_range(), 6..6);
    }

    #[test]
    fn preserves_existing_newlines_instead_of_normalizing_them() {
        let bundle = SourceBundle::new(
            Segment::new("std", "std\n"),
            Segment::new("primary", "primary"),
            [Segment::new("more", "\nmore")],
        );
        assert_eq!(bundle.source(), "std\n\nprimary\n\nmore");
    }

    #[test]
    fn preserves_canonical_segment_order() {
        let bundle = SourceBundle::new(
            Segment::new("std", "s"),
            Segment::new("primary", "p"),
            [Segment::new("first", "a"), Segment::new("second", "b")],
        );
        assert_eq!(bundle.source(), "s\np\na\nb");
        assert_eq!(
            bundle
                .segments()
                .iter()
                .map(Segment::name)
                .collect::<Vec<_>>(),
            ["std", "primary", "first", "second"]
        );
    }

    #[test]
    fn distributed_bundle_owns_the_only_trusted_role_and_canonical_mapping() {
        let bundle = SourceBundle::distributed(
            Segment::new("primary", "p"),
            [
                Segment::new(DISTRIBUTED_STANDARD_LIBRARY_NAME, "forged"),
                Segment::new("additional", "a"),
            ],
        );
        assert_eq!(
            bundle
                .segments()
                .iter()
                .map(Segment::name)
                .collect::<Vec<_>>(),
            [
                DISTRIBUTED_STANDARD_LIBRARY_NAME,
                "primary",
                DISTRIBUTED_STANDARD_LIBRARY_NAME,
                "additional",
            ]
        );
        assert_eq!(
            bundle.trusted_standard_segment_id(),
            bundle.segments()[0].id()
        );
        assert_ne!(bundle.segments()[0].id(), bundle.segments()[2].id());
        assert_eq!(
            bundle.segments()[1].global_range().start,
            DISTRIBUTED_STANDARD_LIBRARY_SOURCE.len() + 1
        );
        let mapped = bundle
            .map_span(Span::new(
                bundle.segments()[3].global_range().start,
                bundle.segments()[3].global_range().end,
            ))
            .unwrap();
        assert_eq!(mapped.segment.name(), "additional");
        assert_eq!(mapped.span, Span::new(0, 1));
    }

    #[test]
    fn raw_fixture_trust_is_explicit_and_never_inferred_from_position_or_name() {
        let raw = SourceBundle::raw_for_conformance(
            Segment::new(DISTRIBUTED_STANDARD_LIBRARY_NAME, "caller controlled"),
            Segment::new("primary", "p"),
            [],
        );
        assert_eq!(raw.trusted_standard_segment_id(), None);

        let trusted = SourceBundle::raw_with_trusted_standard_for_conformance(
            Segment::new("fixture std", "fixture"),
            Segment::new("primary", "p"),
            [],
        );
        assert_eq!(
            trusted.trusted_standard_segment_id(),
            trusted.segments()[0].id()
        );
    }

    #[test]
    fn maps_only_original_bytes_to_local_offsets() {
        let bundle = SourceBundle::new(
            Segment::new("std", "abc"),
            Segment::new("primary", "def"),
            [],
        );
        let mapped = bundle.map_span(Span::new(5, 7)).unwrap();
        assert_eq!(mapped.segment.name(), "primary");
        assert_eq!(mapped.span, Span::new(1, 3));
        assert!(bundle.segment_at(3).is_none());
        assert!(bundle.map_span(Span::new(2, 5)).is_none());
    }
}
