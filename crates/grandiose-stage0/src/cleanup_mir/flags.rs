//! Recompute logical initialization writes from the actual owner operations.
//! These are independently checked, not trusted as producer annotations.
use super::*;

impl CleanupMir {
    fn write_flag(
        &self,
        place: ControlPlace,
        initialized: bool,
        effects: &mut Vec<FlagTransition>,
    ) -> Result<(), CleanupError> {
        let place = self.canonical_place(place);
        if self.symbols.contains(&place.root()) {
            return Ok(());
        }
        // A dereferenced/projection view can travel through a value-flow
        // edge without becoming an owner. Its actual resident move, if any,
        // is the separate ReadPlace/Project operation and clears that path.
        if matches!(place, ControlPlace::Local(_) | ControlPlace::Temporary(_))
            && self
                .owners
                .get(place.root().0 as usize)
                .is_some_and(|owner| owner.kind == OwnerKind::View)
        {
            return Ok(());
        }
        let index = self
            .flags
            .iter()
            .position(|flag| flag.place == place)
            .ok_or_else(|| {
                CleanupError(format!(
                    "initialization transition has no path flag: {place:?}"
                ))
            })?;
        let transition = FlagTransition {
            flag: DropFlagId(index as u32),
            initialized,
        };
        if !effects.contains(&transition) {
            effects.push(transition);
        }
        Ok(())
    }
    fn consume_flag(
        &self,
        operand: OwnershipOperand,
        effects: &mut Vec<FlagTransition>,
    ) -> Result<(), CleanupError> {
        if operand.mode == ValueTransfer::Move {
            self.write_flag(ControlPlace::Local(operand.value), false, effects)?;
        }
        Ok(())
    }
    pub(super) fn instruction_flags(
        &self,
        instruction: &CleanupInstruction,
    ) -> Result<FlagEffects, CleanupError> {
        let mut effects = FlagEffects::default();
        match &instruction.operation {
            CleanupOperation::Read(_) => return Ok(effects),
            CleanupOperation::Construct { fields, .. } => {
                for field in fields {
                    self.consume_flag(*field, &mut effects.before)?;
                }
            }
            CleanupOperation::Transfer { value, mode }
            | CleanupOperation::RunCleanup {
                result: value,
                mode,
                ..
            } => self.consume_flag(
                OwnershipOperand {
                    value: *value,
                    mode: *mode,
                },
                &mut effects.before,
            )?,
            CleanupOperation::ReadPlace { place, mode }
            | CleanupOperation::Project { place, mode, .. } => {
                if *mode == ValueTransfer::Move {
                    self.write_flag(place.clone(), false, &mut effects.before)?;
                }
            }
            CleanupOperation::MovePlace(place) => {
                self.write_flag(place.clone(), false, &mut effects.before)?
            }
            CleanupOperation::Replace {
                place, value, mode, ..
            } => {
                self.consume_flag(
                    OwnershipOperand {
                        value: *value,
                        mode: *mode,
                    },
                    &mut effects.before,
                )?;
                self.write_flag(place.clone(), true, &mut effects.after)?;
            }
            CleanupOperation::Capture { captures, .. } => {
                for (value, mode) in captures {
                    if *mode == crate::CaptureMode::Move {
                        self.write_flag(ControlPlace::Local(*value), false, &mut effects.before)?;
                    }
                }
            }
            _ => {}
        }
        if self.owners[instruction.destination.0 as usize].kind != OwnerKind::View {
            self.write_flag(
                ControlPlace::Local(instruction.destination),
                true,
                &mut effects.after,
            )?;
        }
        Ok(effects)
    }
    pub(super) fn terminator_flags(
        &self,
        terminator: &CleanupTerminator,
    ) -> Result<FlagEffects, CleanupError> {
        let mut effects = FlagEffects::default();
        // Selected CFG edges own their operand transfers. Invocations and
        // performances transfer arguments before their result continuation.
        if !matches!(
            terminator.control,
            CleanupControl::Goto(_) | CleanupControl::SwitchBool { .. }
        ) {
            for operand in &terminator.operands {
                self.consume_flag(*operand, &mut effects.before)?;
            }
        }
        match &terminator.control {
            CleanupControl::Invoke {
                result,
                continuation: Some(_),
                ..
            }
            | CleanupControl::Transfer(ControlTransfer::Perform {
                result,
                continuation: Some(_),
                ..
            }) => self.write_flag(ControlPlace::Local(*result), true, &mut effects.after)?,
            _ => {}
        }
        Ok(effects)
    }
    pub(super) fn successor_flags(
        &self,
        edge: &OwnershipSuccessor,
        parameters: &[ControlValue],
    ) -> Result<FlagEffects, CleanupError> {
        let mut effects = FlagEffects::default();
        for operand in &edge.arguments {
            self.consume_flag(*operand, &mut effects.before)?;
        }
        for parameter in parameters {
            self.write_flag(ControlPlace::Local(*parameter), true, &mut effects.after)?;
        }
        Ok(effects)
    }
}
