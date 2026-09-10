//! Projection availability complements whole-owner availability. These are
//! owned local paths; indirect referents still use the imported PlaceFlow proof.
use super::*;

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct Path(OwnerId, Vec<u32>);
type Moved = BTreeSet<Path>;

impl Path {
    fn overlaps(&self, other: &Self) -> bool {
        self.0 == other.0 && (self.1.starts_with(&other.1) || other.1.starts_with(&self.1))
    }
    fn contains(&self, other: &Self) -> bool {
        self.0 == other.0 && other.1.starts_with(&self.1)
    }
}

impl OwnershipMir {
    pub(super) fn validate_partial_paths(&self) -> Result<(), OwnershipError> {
        let mut views = BTreeMap::new();
        for block in &self.blocks {
            for instruction in &block.instructions {
                if self.owners[instruction.destination.0 as usize].kind == OwnerKind::View {
                    let place = match &instruction.operation {
                        OwnershipOperation::Read(value)
                        | OwnershipOperation::Transfer { value, .. }
                        | OwnershipOperation::ExitScope { result: value, .. } => {
                            Some(ControlPlace::Local(*value))
                        }
                        OwnershipOperation::Project { place, .. }
                        | OwnershipOperation::ReadPlace { place, .. } => Some(place.clone()),
                        OwnershipOperation::ReadReference(reference) => Some(ControlPlace::Deref {
                            reference: *reference,
                            ty: self.values[instruction.destination.0 as usize].ty.clone(),
                        }),
                        _ => None,
                    };
                    if let Some(place) = place {
                        views.insert(instruction.destination, place);
                    }
                }
            }
        }
        fn path(
            mir: &OwnershipMir,
            views: &BTreeMap<ControlValue, ControlPlace>,
            place: &ControlPlace,
        ) -> Option<Path> {
            match place {
                ControlPlace::Local(value) | ControlPlace::Temporary(value) => {
                    if let Some(place) = views.get(value) {
                        path(mir, views, place)
                    } else {
                        Some(Path(mir.canonical_owner(*value), vec![]))
                    }
                }
                ControlPlace::Field { base, index, .. } => {
                    let mut result = path(mir, views, base)?;
                    result.1.push(*index);
                    Some(result)
                }
                ControlPlace::Deref { .. } => None,
            }
        }
        let value_path = |value| path(self, &views, &ControlPlace::Local(value));
        let require = |place: Option<Path>, moved: &Moved| -> Result<(), OwnershipError> {
            if let Some(place) = place
                && moved.iter().any(|other| place.overlaps(other))
            {
                return Err(OwnershipError(format!(
                    "owned path {place:?} overlaps an uninitialized projection"
                )));
            }
            Ok(())
        };
        let consume = |operand: OwnershipOperand, moved: &mut Moved, check: bool| -> Result<(), OwnershipError> {
            let place = value_path(operand.value);
            if check { require(place.clone(), moved)?; }
            if operand.mode == ValueTransfer::Move && let Some(place) = place && !place.1.is_empty() {
                moved.insert(place);
            }
            Ok(())
        };
        let transfer = |instruction: &OwnershipInstruction,
                        moved: &mut Moved,
                        check: bool|
         -> Result<(), OwnershipError> {
            let consumed = match &instruction.operation {
                OwnershipOperation::PrepareInvocation(place) => {
                    if check { require(path(self, &views, place), moved)?; }
                    None
                }
                OwnershipOperation::Project { place, mode, .. }
                | OwnershipOperation::ReadPlace { place, mode } => {
                    let place = path(self, &views, place);
                    if check {
                        require(place.clone(), moved)?;
                    }
                    (*mode == ValueTransfer::Move).then_some(place).flatten()
                }
                OwnershipOperation::MovePlace(place) => {
                    let place = path(self, &views, place);
                    if check {
                        require(place.clone(), moved)?;
                    }
                    place
                }
                OwnershipOperation::Borrow(loan) => {
                    if check {
                        require(
                            path(self, &views, &self.loans[loan.0 as usize].place),
                            moved,
                        )?;
                    }
                    None
                }
                OwnershipOperation::Replace { place, value, mode } => {
                    consume(OwnershipOperand { value: *value, mode: *mode }, moved, check)?;
                    if let Some(place) = path(self, &views, place) {
                        // Replacing a complete field restores that field and
                        // its descendants, not a separately moved sibling.
                        moved.retain(|other| !place.contains(other));
                    }
                    None
                }
                OwnershipOperation::Transfer { value, mode }
                | OwnershipOperation::ExitScope { result: value, mode, .. } => {
                    consume(OwnershipOperand { value: *value, mode: *mode }, moved, check)?;
                    None
                }
                OwnershipOperation::Construct { fields, .. } => {
                    for operand in fields { consume(*operand, moved, check)?; }
                    None
                }
                OwnershipOperation::Capture { captures, .. } => {
                    for (value, mode) in captures {
                        consume(OwnershipOperand { value: *value, mode: if *mode == crate::CaptureMode::Move { ValueTransfer::Move } else { ValueTransfer::Reborrow } }, moved, check)?;
                    }
                    None
                }
                // A read creates an address; the eventual consuming use or
                // projection decides how much of its owner must be initialized.
                OwnershipOperation::Read(_) | OwnershipOperation::Discard(_) => None,
                operation => {
                    if check {
                        for value in operation.inputs(&self.loans) {
                            require(value_path(value), moved)?;
                        }
                    }
                    None
                }
            };
            if let Some(place) = consumed
                && !place.1.is_empty()
            {
                moved.insert(place);
            }
            if self.owners[instruction.destination.0 as usize].kind != OwnerKind::View {
                moved.retain(|place| place.0 != OwnerId(instruction.destination.0));
            }
            Ok(())
        };
        let mut incoming = vec![Moved::new(); self.blocks.len()];
        let mut reachable = vec![false; self.blocks.len()];
        reachable[self.entry.0 as usize] = true;
        loop {
            let mut changed = false;
            for (index, block) in self.blocks.iter().enumerate() {
                if !reachable[index] {
                    continue;
                }
                let mut moved = incoming[index].clone();
                for instruction in &block.instructions {
                    transfer(instruction, &mut moved, false)?;
                }
                let switch = matches!(block.terminator.control, ControlTerminator::SwitchBool { .. });
                let operands = if switch { &block.terminator.operands[..1] } else { &block.terminator.operands };
                for operand in operands { consume(*operand, &mut moved, false)?; }
                for edge in &block.terminator.successors {
                    let target = edge.target.0 as usize;
                    let mut outgoing = moved.clone();
                    if switch {
                        for operand in &edge.arguments { consume(*operand, &mut outgoing, false)?; }
                    }
                    for parameter in &self.blocks[target].parameters {
                        outgoing.retain(|place| place.0 != OwnerId(parameter.0));
                    }
                    let previous = incoming[target].len();
                    incoming[target].extend(outgoing);
                    changed |= incoming[target].len() != previous || !reachable[target];
                    reachable[target] = true;
                }
            }
            if !changed {
                break;
            }
        }
        for (index, block) in self.blocks.iter().enumerate() {
            if !reachable[index] {
                continue;
            }
            let mut moved = incoming[index].clone();
            for instruction in &block.instructions {
                transfer(instruction, &mut moved, true)?;
            }
            let switch = matches!(block.terminator.control, ControlTerminator::SwitchBool { .. });
            let operands = if switch { &block.terminator.operands[..1] } else { &block.terminator.operands };
            for operand in operands { consume(*operand, &mut moved, true)?; }
            if switch {
                for edge in &block.terminator.successors {
                    let mut selected = moved.clone();
                    for operand in &edge.arguments { consume(*operand, &mut selected, true)?; }
                }
            }
        }
        Ok(())
    }
}
