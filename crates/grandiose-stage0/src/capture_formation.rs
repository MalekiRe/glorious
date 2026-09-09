//! Canonical formation rules for a frozen Core capture.
//!
//! These rules describe creation, not invocation authority. Every capture
//! retains dependencies carried by its contents. Borrowing additionally retains
//! the source slot; copying or moving does not turn contained loans into owners.
//! Consumers resolve storage identity in their published provenance domain.

use crate::core::{CaptureMode, ClosureCapture, REFERENCE_PATH_DEREF};
use crate::{Lifetime, Mutability, Type};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CaptureSource {
    Borrow(Mutability),
    Copy,
    Move,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CaptureAction {
    RetainContents,
    Source(CaptureSource),
}

#[derive(Clone, Copy)]
pub(crate) struct CaptureFormation<'a> {
    capture: &'a ClosureCapture,
    source: CaptureSource,
}

impl<'a> CaptureFormation<'a> {
    pub(crate) fn new(capture: &'a ClosureCapture) -> Self {
        let source = match capture.mode {
            CaptureMode::SharedBorrow => CaptureSource::Borrow(Mutability::Shared),
            CaptureMode::UniqueBorrow => CaptureSource::Borrow(Mutability::Unique),
            CaptureMode::Copy => CaptureSource::Copy,
            CaptureMode::Move => CaptureSource::Move,
        };
        Self { capture, source }
    }

    pub(crate) fn source(self) -> CaptureSource {
        self.source
    }

    pub(crate) fn actions(self) -> [CaptureAction; 2] {
        [
            CaptureAction::RetainContents,
            CaptureAction::Source(self.source),
        ]
    }

    pub(crate) fn resident_type(self) -> Type {
        match self.source {
            CaptureSource::Borrow(mutability) => Type::Reference {
                mutability,
                lifetime: Lifetime::Elided,
                referent: Box::new(self.capture.ty.clone()),
            },
            CaptureSource::Copy | CaptureSource::Move => self.capture.ty.clone(),
        }
    }

    pub(crate) fn contents_path(self) -> &'static [u32] {
        match self.source {
            CaptureSource::Borrow(_) => &[REFERENCE_PATH_DEREF],
            CaptureSource::Copy | CaptureSource::Move => &[],
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn all_modes_retain_contents_before_changing_source_state() {
        for (mode, source) in [
            (
                CaptureMode::SharedBorrow,
                CaptureSource::Borrow(Mutability::Shared),
            ),
            (
                CaptureMode::UniqueBorrow,
                CaptureSource::Borrow(Mutability::Unique),
            ),
            (CaptureMode::Copy, CaptureSource::Copy),
            (CaptureMode::Move, CaptureSource::Move),
        ] {
            let capture = ClosureCapture {
                name: "value".into(),
                mode,
                ty: Type::Unit,
            };
            let formation = CaptureFormation::new(&capture);
            assert_eq!(
                formation.actions(),
                [CaptureAction::RetainContents, CaptureAction::Source(source)]
            );
            assert_eq!(
                formation.contents_path().is_empty(),
                !matches!(source, CaptureSource::Borrow(_))
            );
            match source {
                CaptureSource::Borrow(mutability) => assert_eq!(
                    formation.resident_type(),
                    Type::Reference {
                        mutability,
                        lifetime: Lifetime::Elided,
                        referent: Box::new(Type::Unit),
                    }
                ),
                _ => assert_eq!(formation.resident_type(), Type::Unit),
            }
        }
    }

    #[test]
    fn borrowing_a_reference_slot_adds_a_layer_but_owning_preserves_the_handle() {
        let reference = Type::Reference {
            mutability: Mutability::Shared,
            lifetime: Lifetime::Elided,
            referent: Box::new(Type::Unit),
        };
        for mode in [
            CaptureMode::Copy,
            CaptureMode::Move,
            CaptureMode::SharedBorrow,
        ] {
            let capture = ClosureCapture {
                name: "handle".into(),
                mode,
                ty: reference.clone(),
            };
            let formation = CaptureFormation::new(&capture);
            if mode == CaptureMode::SharedBorrow {
                assert_eq!(
                    formation.resident_type(),
                    Type::Reference {
                        mutability: Mutability::Shared,
                        lifetime: Lifetime::Elided,
                        referent: Box::new(reference.clone())
                    }
                );
            } else {
                assert_eq!(formation.resident_type(), reference);
            }
        }
    }
}
