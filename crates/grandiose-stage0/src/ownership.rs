//! Ownership obligations at a whole-frame boundary.
//!
//! Source bindings and ABI parameters are owners; arbitrary MIR temporaries
//! are not. Keep that distinction independent of the syntax-specific lowerer
//! which happened to construct an exit. Destruction elaboration supplies the
//! initialization guards and concrete, source-selected destructor calls.

use std::collections::BTreeSet;

use crate::{MirFunction, MirLocal};

/// Immutable owner inventory shared by frame-exit consumers. Captures belong
/// to the callable environment, not to the invocation's parameter cleanup.
/// A transferred result is protected at the exit, not removed from the frame's
/// inventory: a different exit may still have to destroy that same owner.
pub(crate) struct FrameOwnership {
    reverse_owners: Vec<MirLocal>,
}

impl FrameOwnership {
    pub(crate) fn for_function(function: &MirFunction) -> Self {
        if let Some(owners) = &function.control.cleanup_owners {
            return Self { reverse_owners: owners.clone() };
        }
        Self::from_bindings(
            &function.parameters,
            function.captures as usize,
            &function.control.source_storage.binding_locals,
        )
    }

    fn from_bindings(parameters: &[MirLocal], captures: usize, bindings: &[Option<MirLocal>]) -> Self {
        let capture_locals = parameters.iter().take(captures).copied().collect::<BTreeSet<_>>();
        let parameter_locals = parameters.iter().copied().collect::<BTreeSet<_>>();
        let mut seen = BTreeSet::new();
        // Binding identities are allocated by ownership analysis in source
        // declaration order. Do not sort by spelling or MIR register number.
        let mut reverse_owners = bindings.iter().rev().flatten().copied()
            .filter(|local| !parameter_locals.contains(local) && seen.insert(*local))
            .collect::<Vec<_>>();
        reverse_owners.extend(parameters.iter().rev().copied()
            .filter(|local| !capture_locals.contains(local) && seen.insert(*local)));
        Self { reverse_owners }
    }

    pub(crate) fn exiting(&self, transferred: Option<MirLocal>) -> impl Iterator<Item = MirLocal> + '_ {
        self.reverse_owners.iter().copied().filter(move |local| Some(*local) != transferred)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn frame_exit_uses_binding_order_and_destroys_parameters_last() {
        let owners = FrameOwnership::from_bindings(
            &[MirLocal(8), MirLocal(2)], 0,
            &[Some(MirLocal(8)), Some(MirLocal(2)), Some(MirLocal(30)), None, Some(MirLocal(4))],
        );
        assert_eq!(owners.exiting(None).collect::<Vec<_>>(),
            vec![MirLocal(4), MirLocal(30), MirLocal(2), MirLocal(8)]);
    }

    #[test]
    fn captures_and_transferred_results_are_not_frame_cleanup() {
        let owners = FrameOwnership::from_bindings(
            &[MirLocal(0), MirLocal(1)], 1,
            &[Some(MirLocal(0)), Some(MirLocal(1)), Some(MirLocal(7)), Some(MirLocal(7))],
        );
        assert_eq!(owners.exiting(Some(MirLocal(7))).collect::<Vec<_>>(), vec![MirLocal(1)]);
        assert_eq!(owners.exiting(None).collect::<Vec<_>>(), vec![MirLocal(7), MirLocal(1)]);
    }
}
