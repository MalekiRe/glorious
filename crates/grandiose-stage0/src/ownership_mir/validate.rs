//! Checks the ownership phase's own vocabulary, without rerunning source
//! inference, trait selection, or retaining the preceding Control MIR body.
use super::*;

fn invalid(message: &str) -> OwnershipError {
    OwnershipError(message.into())
}

impl OwnershipMir {
    fn checked_owner(&self, value: ControlValue) -> Result<&Owner, OwnershipError> {
        self.owners
            .get(value.0 as usize)
            .ok_or_else(|| invalid("unknown owner value"))
    }

    fn checked_type(&self, value: ControlValue) -> Result<&Type, OwnershipError> {
        self.values
            .get(value.0 as usize)
            .map(|value| &value.ty)
            .ok_or_else(|| invalid("unknown typed value"))
    }

    fn validate_operand(&self, operand: OwnershipOperand) -> Result<(), OwnershipError> {
        let owner = self.checked_owner(operand.value)?;
        if operand.mode == ValueTransfer::RetainResumption
            && (!owner.retains_resumption || !matches!(self.checked_type(operand.value)?, Type::Callable { .. })
                || !self.source_flow.retains_resumption(self.values[operand.value.0 as usize].source)) {
            return Err(invalid("resumption carrier transport lacks checked quantity evidence"));
        }
        if operand.mode == ValueTransfer::Copy && owner.quantity != Some(Quantity::UNRESTRICTED) {
            return Err(invalid("copy lacks generic Use authority"));
        }
        Ok(())
    }

    fn writable_place(&self, place: &ControlPlace) -> Result<bool, OwnershipError> {
        Ok(match place {
            ControlPlace::Local(value) | ControlPlace::Temporary(value) => !matches!(
                self.checked_owner(ControlValue(self.canonical_owner(*value).0))?
                    .kind,
                OwnerKind::Capture(crate::CaptureMode::SharedBorrow)
            ),
            ControlPlace::Field { base, .. } => self.writable_place(base)?,
            ControlPlace::Deref { reference, .. } => matches!(
                self.checked_type(*reference)?,
                Type::Reference {
                    mutability: crate::Mutability::Unique,
                    ..
                }
            ),
        })
    }

    pub(super) fn checked_place_type<'a>(
        &'a self,
        place: &'a ControlPlace,
    ) -> Result<&'a Type, OwnershipError> {
        match place {
            ControlPlace::Local(value) | ControlPlace::Temporary(value) => {
                self.checked_type(*value)
            }
            ControlPlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                self.checked_place_type(base)?;
                if index >= field_count {
                    return Err(invalid("place projection exceeds its layout"));
                }
                Ok(ty)
            }
            ControlPlace::Deref { reference, ty } => {
                if !matches!(self.checked_type(*reference)?, Type::Reference { referent, .. } if referent.as_ref() == ty)
                {
                    return Err(invalid(
                        "dereference place disagrees with its reference type",
                    ));
                }
                Ok(ty)
            }
        }
    }

    pub fn validate(&self) -> Result<(), OwnershipError> {
        if self.owners.len() != self.values.len()
            || self.blocks.len() != self.live_in.len()
            || self.blocks.get(self.entry.0 as usize).is_none()
        {
            return Err(invalid("incomplete owner inventory"));
        }
        for (index, scope) in self.scopes.iter().enumerate() {
            if scope
                .parent
                .is_some_and(|parent| parent.0 as usize >= index)
            {
                return Err(invalid("scope ancestry is not canonical"));
            }
        }
        for (index, owner) in self.owners.iter().enumerate() {
            if owner.value.0 as usize != index {
                return Err(invalid("owner identity mismatch"));
            }
            if owner
                .scope
                .is_some_and(|scope| self.scopes.get(scope.0 as usize).is_none())
            {
                return Err(invalid("owner has unknown scope"));
            }
        }
        for (&alias, &source) in &self.aliases {
            self.checked_owner(alias)?;
            self.checked_owner(source)?;
            let mut cursor = source;
            let mut remaining = self.aliases.len();
            while let Some(next) = self.aliases.get(&cursor) {
                self.checked_owner(*next)?;
                if remaining == 0 {
                    return Err(invalid("cyclic owner alias"));
                }
                remaining -= 1;
                cursor = *next;
            }
        }
        for (index, loan) in self.loans.iter().enumerate() {
            if loan.id.0 as usize != index {
                return Err(invalid("loan identity mismatch"));
            }
            let referent = self.checked_place_type(&loan.place)?;
            if loan.unique && !self.writable_place(&loan.place)? {
                return Err(invalid("unique loan lacks mutable place authority"));
            }
            if !matches!(self.checked_type(loan.destination)?, Type::Reference { mutability, referent: actual, .. }
                if (*mutability == crate::Mutability::Unique) == loan.unique && actual.as_ref() == referent)
            {
                return Err(invalid(
                    "loan destination disagrees with its place or mutability",
                ));
            }
        }
        for block in &self.blocks {
            for value in &block.parameters {
                self.checked_owner(*value)?;
            }
            for edge in block.terminator.control.edges() {
                if self.blocks.get(edge.target.0 as usize).is_none() {
                    return Err(invalid("unknown control successor"));
                }
            }
            let edges = block.terminator.control.edges();
            if edges.len() != block.terminator.successors.len() {
                return Err(invalid(
                    "ownership successor count disagrees with control edges",
                ));
            }
            for (edge_index, (edge, successor)) in
                edges.iter().zip(&block.terminator.successors).enumerate()
            {
                if edge.target != successor.target
                    || edge.arguments
                        != successor
                            .arguments
                            .iter()
                            .map(|operand| operand.value)
                            .collect::<Vec<_>>()
                {
                    return Err(invalid(
                        "ownership successor operands disagree with control edge",
                    ));
                }
                let offset = match &block.terminator.control {
                    ControlTerminator::SwitchBool { on_true, .. } => Some(if edge_index == 0 {
                        1
                    } else {
                        1 + on_true.arguments.len()
                    }),
                    ControlTerminator::Invoke { .. }
                    | ControlTerminator::Transfer(ControlTransfer::Perform { .. }) => None,
                    ControlTerminator::Transfer(ControlTransfer::EnterHandler { .. })
                        if edge_index != 0 =>
                    {
                        None
                    }
                    _ => Some(0),
                };
                for (argument_index, operand) in successor.arguments.iter().enumerate() {
                    self.validate_operand(*operand)?;
                    if operand.mode == ValueTransfer::Reborrow {
                        return Err(invalid("successor argument is not an owned transfer"));
                    }
                    if offset
                        .and_then(|offset| block.terminator.operands.get(offset + argument_index))
                        .is_some_and(|input| input.mode != operand.mode)
                    {
                        return Err(invalid("successor transfer mode disagrees with its input"));
                    }
                }
            }
            let inputs = block.terminator.control.inputs();
            if inputs.len() != block.terminator.operands.len()
                || inputs
                    .iter()
                    .zip(&block.terminator.operands)
                    .any(|(value, operand)| *value != operand.value)
            {
                return Err(invalid(
                    "terminator ownership operands disagree with control inputs",
                ));
            }
            for (index, operand) in block.terminator.operands.iter().enumerate() {
                self.validate_operand(*operand)?;
                let receiver = index == 0
                    && matches!(block.terminator.control, ControlTerminator::Invoke { .. });
                if (operand.mode == ValueTransfer::Reborrow) != receiver {
                    return Err(invalid(
                        "terminator reborrow is not its invocation receiver",
                    ));
                }
            }
            let mut dispositions = BTreeSet::new();
            for (owner, disposition) in &block.terminator.dispositions {
                let descriptor = self.checked_owner(ControlValue(owner.0))?;
                if !dispositions.insert(*owner) {
                    return Err(invalid("duplicate owner disposition"));
                }
                if *disposition == OwnerDisposition::Transfer
                    && !block.terminator.operands.iter().any(|operand| {
                        operand.mode == ValueTransfer::Move
                            && self.canonical_owner(operand.value) == *owner
                    })
                {
                    return Err(invalid("owner transfer lacks a consuming operand"));
                }
                if *disposition == OwnerDisposition::ReturnCapture
                    && !matches!(descriptor.kind, OwnerKind::Capture(_))
                {
                    return Err(invalid(
                        "only a captured owner can return to its environment",
                    ));
                }
            }
            for instruction in &block.instructions {
                self.checked_owner(instruction.destination)?;
                if self.scopes.get(instruction.scope.0 as usize).is_none() {
                    return Err(invalid("instruction has unknown scope"));
                }
                match &instruction.operation {
                    OwnershipOperation::Construct { fields, .. } => {
                        for operand in fields {
                            self.validate_operand(*operand)?;
                            if operand.mode == ValueTransfer::Reborrow {
                                return Err(invalid("aggregate field lacks owned transfer"));
                            }
                        }
                    }
                    OwnershipOperation::Transfer { value, mode } => {
                        self.validate_operand(OwnershipOperand {
                            value: *value,
                            mode: *mode,
                        })?
                    }
                    OwnershipOperation::ExitScope {
                        scope,
                        result,
                        mode,
                        owners,
                    } => {
                        self.validate_operand(OwnershipOperand {
                            value: *result,
                            mode: *mode,
                        })?;
                        let mut seen = BTreeSet::new();
                        for owner in owners {
                            let descriptor = self.checked_owner(ControlValue(owner.0))?;
                            if !seen.insert(*owner)
                                || descriptor.scope != Some(*scope)
                                || matches!(
                                    descriptor.kind,
                                    OwnerKind::View
                                        | OwnerKind::Capture(_)
                                        | OwnerKind::Continuation
                                )
                            {
                                return Err(invalid("invalid scope cleanup owner"));
                            }
                        }
                    }
                    OwnershipOperation::Read(value) | OwnershipOperation::ReadReference(value) => {
                        self.checked_owner(*value)?;
                    }
                    OwnershipOperation::ReadPlace { place, mode }
                    | OwnershipOperation::Project { place, mode, .. } => {
                        self.checked_place_type(place)?;
                        if *mode == ValueTransfer::RetainResumption {
                            self.validate_operand(OwnershipOperand { value: instruction.destination, mode: *mode })?;
                        }
                        if *mode == ValueTransfer::Move && !self.writable_place(place)? {
                            return Err(OwnershipError(format!(
                                "place move lacks mutable place authority in {:?} at {:?}: {place:?}",
                                self.definition,
                                self.values[instruction.destination.0 as usize].span
                            )));
                        }
                        self.validate_operand(OwnershipOperand {
                            value: instruction.destination,
                            mode: *mode,
                        })?;
                    }
                    OwnershipOperation::PrepareInvocation(place) => {
                        if self.checked_place_type(place)? != self.checked_type(instruction.destination)?
                            || self.checked_owner(instruction.destination)?.kind != OwnerKind::View {
                            return Err(invalid("invocation receiver must be a same-typed non-owning view"));
                        }
                    }
                    OwnershipOperation::MovePlace(place) => {
                        self.checked_place_type(place)?;
                        if !self.writable_place(place)? {
                            return Err(OwnershipError(format!(
                                "place move lacks mutable place authority in {:?} at {:?}: {place:?}",
                                self.definition,
                                self.values[instruction.destination.0 as usize].span
                            )));
                        }
                    }
                    OwnershipOperation::Replace { place, value, mode } => {
                        if !self.writable_place(place)? {
                            return Err(invalid("replacement lacks mutable place authority"));
                        }
                        if !crate::control_mir::call_type_matches(self.checked_place_type(place)?, self.checked_type(*value)?) {
                            return Err(invalid("replacement type disagrees with place"));
                        }
                        self.validate_operand(OwnershipOperand {
                            value: *value,
                            mode: *mode,
                        })?;
                    }
                    OwnershipOperation::Borrow(id) => {
                        if self
                            .loans
                            .get(id.0 as usize)
                            .is_none_or(|loan| loan.destination != instruction.destination)
                        {
                            return Err(invalid("invalid loan identity"));
                        }
                    }
                    OwnershipOperation::Discard(owner) => {
                        self.checked_owner(ControlValue(owner.0))?;
                    }
                    OwnershipOperation::Capture { closure, captures } => {
                        let closure = self
                            .closures
                            .get(closure.0 as usize)
                            .ok_or_else(|| invalid("unknown closure environment"))?;
                        if let Some(error) = crate::core::capture_environment_error(
                            closure.environment.brand.callable,
                            &closure.environment,
                            self.checked_type(instruction.destination)?,
                        ) {
                            return Err(OwnershipError(error));
                        }
                        if captures.len() != closure.environment.captures.len() {
                            return Err(invalid("capture arity disagrees with sealed environment"));
                        }
                        if self.checked_owner(instruction.destination)?.quantity
                            != environment_quantity(captures, &self.owners) {
                            return Err(invalid("callable owner quantity disagrees with its capture environment"));
                        }
                        for ((value, mode), capture) in
                            captures.iter().zip(&closure.environment.captures)
                        {
                            if *mode != capture.mode || self.checked_type(*value)? != &capture.ty {
                                return Err(invalid(&format!("capture {} disagrees with sealed environment: expected {:?} {:?}, found {:?} {:?}",
                                    capture.name, capture.mode, capture.ty, mode, self.checked_type(*value)?)));
                            }
                            if *mode == crate::CaptureMode::Copy {
                                self.validate_operand(OwnershipOperand {
                                    value: *value,
                                    mode: ValueTransfer::Copy,
                                })?;
                            }
                        }
                    }
                    OwnershipOperation::Compute(_) => {}
                }
            }
        }
        for closure in &self.closures {
            closure.body.validate()?;
        }
        self.validate_graph()?;
        let aliases = self
            .blocks
            .iter()
            .flat_map(|block| &block.instructions)
            .filter_map(|instruction| match instruction.operation {
                OwnershipOperation::Read(source) => Some((instruction.destination, source)),
                _ => None,
            })
            .collect();
        if self.aliases != aliases {
            return Err(invalid(
                "owner aliases disagree with lexical read operations",
            ));
        }
        if self.live_in != self.compute_liveness() {
            return Err(invalid("value liveness disagrees with ownership graph"));
        }
        self.validate_inventory()?;
        self.validate_owner_availability()?;
        Ok(())
    }

    pub(super) fn canonical_owner(&self, mut value: ControlValue) -> OwnerId {
        // Alias acyclicity and all indices have been checked above.
        while let Some(source) = self.aliases.get(&value) {
            value = *source;
        }
        OwnerId(value.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    fn fixture(source: &str) -> OwnershipMir {
        let package = PackageKey("ownership-validator@0.1.0".into());
        let lexed = LexedFile::lex(FileKey::new(&package, "src/main.glorious"), source);
        let scan = DeclarationScan::scan(&lexed, source);
        let interface = InterfaceSet::collect(package, "crate", &lexed, source, &scan).interface;
        let signatures = ElaboratedInterface::elaborate(&interface);
        let definition = interface
            .definitions
            .iter()
            .find(|definition| definition.name.as_deref() == Some("main"))
            .unwrap();
        let syntax = BodySyntax::parse(&lexed, source, definition.body.unwrap());
        let core = TypedBody::elaborate(
            definition,
            &syntax,
            &DefinitionIndex::from_interface(&interface),
            &signatures,
        );
        assert!(core.diagnostics.is_empty(), "{:#?}", core.diagnostics);
        let flow = PlaceFlow::analyze_with_interface(&core, &signatures);
        assert!(flow.diagnostics.is_empty(), "{:#?}", flow.diagnostics);
        let children = core
            .expressions
            .iter()
            .filter_map(|expression| {
                let CoreKind::Closure {
                    environment,
                    parameters,
                    body,
                    ..
                } = &expression.kind
                else {
                    return None;
                };
                let abi = environment
                    .captures
                    .iter()
                    .map(|capture| (capture.name.clone(), capture.ty.clone()))
                    .chain(parameters.iter().cloned())
                    .collect::<Vec<_>>();
                Some((
                    crate::mir::lifted_callable_definition(environment.brand),
                    PlaceFlow::analyze_lifted_with_interface_and_bounds(
                        &core,
                        *body,
                        &abi,
                        &signatures,
                        &flow.lexical_bounds,
                    ),
                ))
            })
            .collect();
        let evaluation =
            crate::evaluation_mir::EvaluationMir::lower(definition.key, &core).unwrap();
        let control = ControlMir::lower(&evaluation).unwrap();
        OwnershipMir::lower_with_closure_flows(control, &flow, &children, Some(&signatures))
            .unwrap()
    }

    #[test]
    fn matching_a_copied_call_referent_keeps_the_completed_value() {
        fixture("fn get(value: &i64) -> &i64 { value } pub fn main(value: &i64) -> i64 { handle *get(value) { 64 => 0; other => other } }");
    }

    #[test]
    fn projecting_a_copyable_referent_does_not_own_an_intermediate_copy() {
        let mir = fixture("struct CopyProbe { field: i64 } impl Use<[0, *]> for CopyProbe {} pub fn main(value: &CopyProbe) -> i64 { value.field }");
        let read = mir.blocks.iter().flat_map(|block| &block.instructions)
            .find(|instruction| matches!(instruction.operation, OwnershipOperation::ReadReference(_))).unwrap();
        assert_eq!(mir.owners[read.destination.0 as usize].kind, OwnerKind::View);
        assert_eq!(mir.owners[read.destination.0 as usize].quantity, Some(Quantity::UNRESTRICTED));
    }

    #[test]
    fn an_explicit_copy_of_a_referent_still_has_an_owner() {
        let mir = fixture("struct CopyProbe { field: i64 } impl Use<[0, *]> for CopyProbe {} pub fn main(value: &CopyProbe) -> CopyProbe { let copy = *value; copy }");
        let read = mir.blocks.iter().flat_map(|block| &block.instructions)
            .find(|instruction| matches!(instruction.operation, OwnershipOperation::ReadReference(_))).unwrap();
        assert_ne!(mir.owners[read.destination.0 as usize].kind, OwnerKind::View);
    }

    #[test]
    fn a_reassigned_callable_cannot_keep_its_initial_copy_permission() {
        let mir = fixture("pub fn main(value: &mut i64) -> i64 { let mut pending = () -> i64 { 42 }; pending = () -> i64 { let taken = move value; 42 }; let held = pending; held() }");
        let replaced = mir.blocks.iter().flat_map(|block| &block.instructions)
            .find_map(|instruction| match &instruction.operation {
                OwnershipOperation::Replace { place: ControlPlace::Local(value), .. } => Some(*value),
                _ => None,
            }).unwrap();
        assert_eq!(mir.owners[replaced.0 as usize].quantity, Some(Quantity::AFFINE));
    }

    #[test]
    fn a_copyable_environment_can_be_copied_without_consuming_the_callable_owner() {
        let mir = fixture("pub fn main() -> i64 { let value = 42; let first = move (value) { 42 }; let second = first; first(); second() }");
        let capture = mir.blocks.iter().flat_map(|block| &block.instructions)
            .find(|instruction| matches!(instruction.operation, OwnershipOperation::Capture { .. })).unwrap();
        assert_eq!(mir.owners[capture.destination.0 as usize].quantity, Some(Quantity::UNRESTRICTED));
        assert!(matches!(mir.values[capture.destination.0 as usize].ty,
            Type::Callable { invocation: Quantity::ONCE, .. }));
    }

    #[test]
    fn an_environment_owning_a_unique_reference_does_not_gain_copy_authority() {
        let mut mir = fixture("pub fn main(value: &mut i64) -> i64 { let action = move (value) { *value }; action() }");
        let destination = mir.blocks.iter().flat_map(|block| &block.instructions)
            .find(|instruction| matches!(instruction.operation, OwnershipOperation::Capture { .. })).unwrap().destination;
        assert_eq!(mir.owners[destination.0 as usize].quantity, Some(Quantity::AFFINE));
        mir.owners[destination.0 as usize].quantity = Some(Quantity::UNRESTRICTED);
        assert!(mir.validate().unwrap_err().0.contains("capture environment"));
    }

    #[test]
    fn rejects_copying_an_affine_aggregate_operand() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(ticket: Ticket) -> (Ticket, i64) { (ticket, 42) }",
        );
        let fields = mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
            .find_map(|instruction| match &mut instruction.operation {
                OwnershipOperation::Construct { fields, .. } => Some(fields),
                _ => None,
            })
            .unwrap();
        fields[0].mode = ValueTransfer::Copy;
        assert!(mir.validate().unwrap_err().0.contains("copy lacks"));
    }

    #[test]
    fn rejects_copying_an_affine_call_argument() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} fn take(ticket: Ticket) -> i64 { 42 } pub fn main(ticket: Ticket) -> i64 { take(ticket) }",
        );
        let call = mir
            .blocks
            .iter_mut()
            .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
            .unwrap();
        call.terminator.operands[1].mode = ValueTransfer::Copy;
        assert!(mir.validate().unwrap_err().0.contains("copy lacks"));
    }

    #[test]
    fn resumption_transport_cannot_replace_an_ordinary_owned_transfer() {
        let mut mir = fixture("fn take(value:i64) -> i64 { value } pub fn main(value:i64) -> i64 { take(value) }");
        let call = mir.blocks.iter_mut().find(|block|
            matches!(block.terminator.control, ControlTerminator::Invoke { .. })).unwrap();
        call.terminator.operands[1].mode = ValueTransfer::RetainResumption;
        assert!(mir.validate().unwrap_err().0.contains("resumption carrier transport lacks"));
    }

    #[test]
    fn rejects_copying_an_affine_replacement() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(old: Ticket, new: Ticket) -> Ticket { let mut old = old; old = new; old }",
        );
        let mode = mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
            .find_map(|instruction| match &mut instruction.operation {
                OwnershipOperation::Replace { mode, .. } => Some(mode),
                _ => None,
            })
            .unwrap();
        *mode = ValueTransfer::Copy;
        assert!(mir.validate().unwrap_err().0.contains("copy lacks"));
    }

    #[test]
    fn rejects_duplicate_scope_cleanup_owners() {
        let mut mir = fixture("pub fn main() -> i64 { let value = 1; 42 }");
        let owners = mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
            .find_map(|instruction| match &mut instruction.operation {
                OwnershipOperation::ExitScope { owners, .. } if !owners.is_empty() => Some(owners),
                _ => None,
            })
            .unwrap();
        owners.push(owners[0]);
        assert!(mir.validate().unwrap_err().0.contains("scope cleanup"));
    }

    #[test]
    fn rejects_forged_transfer_of_a_copied_argument() {
        let mut mir = fixture(
            "fn identity(value: i64) -> i64 { value } pub fn main(value: i64) -> i64 { identity(value); value }",
        );
        let parameter = OwnerId(mir.parameters[0].0);
        let call = mir
            .blocks
            .iter_mut()
            .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
            .unwrap();
        let disposition = call
            .terminator
            .dispositions
            .iter_mut()
            .find(|(owner, _)| *owner == parameter)
            .unwrap();
        disposition.1 = OwnerDisposition::Transfer;
        assert!(mir.validate().unwrap_err().0.contains("consuming operand"));
    }

    #[test]
    fn rejects_invalid_indices_and_alias_cycles_without_panicking() {
        let mut mir = fixture("pub fn main(value: i64) -> i64 { value }");
        let mut invalid_index = mir.clone();
        invalid_index.blocks[0].instructions[0].destination = ControlValue(u32::MAX);
        assert!(invalid_index.validate().is_err());
        let (&alias, _) = mir.aliases.iter().next().unwrap();
        mir.aliases.insert(alias, alias);
        assert!(mir.validate().unwrap_err().0.contains("cyclic"));
    }

    #[test]
    fn rejects_a_loan_with_forged_mutability() {
        let mut mir =
            fixture("pub fn main(value: &mut i64) -> i64 { let shared = & *value; *shared }");
        mir.loans[0].unique = !mir.loans[0].unique;
        assert!(mir.validate().unwrap_err().0.contains("mutability"));
    }

    #[test]
    fn rejects_unsealed_closure_environments() {
        let mut mir =
            fixture("pub fn main(value: i64) -> i64 { let body = () -> i64 { value }; body() }");
        mir.closures[0].environment.runs_in.sealed = false;
        assert!(mir.validate().unwrap_err().0.contains("RunsIn"));
    }

    #[test]
    fn rejects_omitted_scope_cleanup() {
        let mut mir = fixture("pub fn main() -> i64 { let value = 1; 42 }");
        for instruction in mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
        {
            if let OwnershipOperation::ExitScope { owners, .. } = &mut instruction.operation {
                owners.clear();
            }
        }
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("initialized owner inventory")
        );
    }

    #[test]
    fn rejects_omitted_and_misclassified_suspended_owners() {
        let mir = fixture(
            "fn identity(value: i64) -> i64 { value } pub fn main(value: i64) -> i64 { identity(value); value }",
        );
        for omit in [false, true] {
            let mut corrupted = mir.clone();
            let call = corrupted
                .blocks
                .iter_mut()
                .find(|block| matches!(block.terminator.control, ControlTerminator::Invoke { .. }))
                .unwrap();
            if omit {
                call.terminator.dispositions.clear();
            } else {
                call.terminator.dispositions[0].1 = OwnerDisposition::Retain;
            }
            assert!(
                corrupted
                    .validate()
                    .unwrap_err()
                    .0
                    .contains("residual owner inventory")
            );
        }
    }

    #[test]
    fn rejects_an_unavailable_computation_input() {
        let mut mir = fixture("pub fn main() -> i64 { let earlier = 1; 42 }");
        let later = mir.blocks[0]
            .instructions
            .iter()
            .rev()
            .find(|instruction| {
                matches!(
                    instruction.operation,
                    OwnershipOperation::Compute(OwnershipComputation::Literal(_))
                )
            })
            .unwrap()
            .destination;
        let first = &mut mir.blocks[0].instructions[0];
        first.operation = OwnershipOperation::Compute(OwnershipComputation::Intrinsic {
            operator: "+".into(),
            arguments: vec![later],
        });
        assert!(mir.validate().unwrap_err().0.contains("unavailable value"));
    }

    #[test]
    fn rejects_duplicate_value_definitions() {
        let mut mir = fixture("pub fn main() -> i64 { 42 }");
        let duplicate = mir.blocks[0].instructions[0].clone();
        mir.blocks[0].instructions.insert(0, duplicate);
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("duplicate ownership value")
        );
    }

    #[test]
    fn rejects_forged_leaf_result_types() {
        let mut mir = fixture("pub fn main() -> i64 { 42 }");
        mir.blocks[0].instructions[0].operation =
            OwnershipOperation::Compute(OwnershipComputation::Unit);
        assert!(mir.validate().unwrap_err().0.contains("result type"));
    }

    #[test]
    fn rejects_unknown_intrinsic_operands() {
        let mut mir = fixture("pub fn main() -> i64 { 42 }");
        mir.blocks[0].instructions[0].operation =
            OwnershipOperation::Compute(OwnershipComputation::Intrinsic {
                operator: "+".into(),
                arguments: vec![ControlValue(u32::MAX)],
            });
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("unknown graph value")
        );
    }

    #[test]
    fn rejects_forged_projection_layouts() {
        let mut mir = fixture(
            "struct Pair { first: i64, second: i64 } pub fn main(value: Pair) -> i64 { value.first }",
        );
        let instruction = mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
            .find(|instruction| matches!(instruction.operation, OwnershipOperation::Project { .. }))
            .unwrap();
        let OwnershipOperation::Project {
            place: ControlPlace::Field {
                index, field_count, ..
            },
            ..
        } = &mut instruction.operation
        else {
            panic!("field place");
        };
        *index = *field_count;
        assert!(mir.validate().unwrap_err().0.contains("projection exceeds"));
    }

    #[test]
    fn rejects_replacement_through_a_shared_reference() {
        let mut mir = fixture("pub fn main(value: &mut i64) -> i64 { *value = 42; *value }");
        // Change the reference capability consistently throughout the graph;
        // the remaining store must still fail its own authority check.
        for value in &mut mir.values {
            if let Type::Reference { mutability, .. } = &mut value.ty {
                *mutability = crate::Mutability::Shared;
            }
        }
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("mutable place authority")
        );
    }

    #[test]
    fn affine_edge_arguments_only_move_on_the_selected_successor() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(flag: i64, left: Ticket, right: Ticket) -> Ticket { left }",
        );
        mir.values.truncate(3);
        mir.owners.truncate(3);
        mir.scopes.truncate(1);
        mir.scopes[0].bindings.clear();
        mir.aliases.clear();
        for (value, source, kind) in [
            (3, 0, OwnerKind::Temporary),
            (4, 1, OwnerKind::Join),
            (5, 2, OwnerKind::Join),
        ] {
            let mut declaration = mir.values[source].clone();
            if value == 3 {
                declaration.ty = Type::Scalar(ScalarType::Bool);
            }
            mir.values.push(declaration);
            let mut owner = mir.owners[source].clone();
            owner.value = ControlValue(value);
            owner.kind = kind;
            mir.owners.push(owner);
        }
        let moved = |value| OwnershipOperand {
            value: ControlValue(value),
            mode: ValueTransfer::Move,
        };
        let edge = |target, value| ControlEdge {
            target: ControlBlockId(target),
            arguments: vec![ControlValue(value)],
        };
        let successor = |target, value| OwnershipSuccessor {
            target: ControlBlockId(target),
            arguments: vec![moved(value)],
            inventory: vec![],
        };
        mir.blocks = vec![
            OwnershipBlock {
                parameters: mir.parameters.clone(),
                instructions: vec![OwnershipInstruction {
                    scope: ControlScopeId(0),
                    destination: ControlValue(3),
                    operation: OwnershipOperation::Compute(OwnershipComputation::Test {
                        subject: ControlValue(0),
                        pattern: CorePattern::Literal("0".into()),
                    }),
                }],
                terminator: OwnershipTerminator {
                    control: ControlTerminator::SwitchBool {
                        condition: ControlValue(3),
                        on_true: edge(1, 1),
                        on_false: edge(2, 2),
                    },
                    operands: vec![
                        OwnershipOperand {
                            value: ControlValue(3),
                            mode: ValueTransfer::Copy,
                        },
                        moved(1),
                        moved(2),
                    ],
                    dispositions: vec![],
                    successors: vec![successor(1, 1), successor(2, 2)],
                },
            },
            OwnershipBlock {
                parameters: vec![ControlValue(4)],
                instructions: vec![],
                terminator: OwnershipTerminator {
                    control: ControlTerminator::Return(ControlValue(4)),
                    operands: vec![moved(4)],
                    dispositions: vec![],
                    successors: vec![],
                },
            },
            OwnershipBlock {
                parameters: vec![ControlValue(5)],
                instructions: vec![],
                terminator: OwnershipTerminator {
                    control: ControlTerminator::Return(ControlValue(5)),
                    operands: vec![moved(5)],
                    dispositions: vec![],
                    successors: vec![],
                },
            },
        ];
        mir.live_in = mir.compute_liveness();
        mir.elaborate_inventory();
        mir.validate().unwrap();
        let [left, right] = mir.blocks[0].terminator.successors.as_slice() else {
            panic!("two successors");
        };
        assert!(!left.inventory.contains(&OwnerId(1)));
        assert!(left.inventory.contains(&OwnerId(2)));
        assert!(right.inventory.contains(&OwnerId(1)));
        assert!(!right.inventory.contains(&OwnerId(2)));
        mir.blocks[0].terminator.successors[0].inventory.clear();
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("selected edge transfers")
        );
    }

    #[test]
    fn rejects_consuming_one_owner_twice_even_with_recomputed_inventory() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} pub fn main(ticket: Ticket) -> (Ticket, Ticket) { (ticket, Ticket {}) }",
        );
        let fields = mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
            .find_map(|instruction| match &mut instruction.operation {
                OwnershipOperation::Construct {
                    aggregate: OwnershipAggregate::Tuple,
                    fields,
                } => Some(fields),
                _ => None,
            })
            .unwrap();
        fields[1] = fields[0];
        mir.live_in = mir.compute_liveness();
        mir.elaborate_inventory();
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("not initialized on every incoming path")
        );
    }

    #[test]
    fn rejects_using_a_previously_consumed_argument() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} fn consume(value: Ticket) -> i64 { 42 } pub fn main(ticket: Ticket) -> i64 { consume(ticket); consume(Ticket {}) }",
        );
        let calls = mir
            .blocks
            .iter()
            .enumerate()
            .filter_map(|(index, block)| {
                matches!(block.terminator.control, ControlTerminator::Invoke { .. })
                    .then_some(index)
            })
            .collect::<Vec<_>>();
        let consumed = mir.blocks[calls[0]].terminator.operands[1];
        let call = &mut mir.blocks[calls[1]].terminator;
        let ControlTerminator::Invoke { arguments, .. } = &mut call.control else {
            panic!("invocation");
        };
        arguments[0] = consumed.value;
        call.operands[1] = consumed;
        mir.live_in = mir.compute_liveness();
        mir.elaborate_inventory();
        assert!(
            mir.validate()
                .unwrap_err()
                .0
                .contains("not initialized on every incoming path")
        );
    }

    #[test]
    fn rejects_repeated_field_moves_with_recomputed_certificates() {
        let mut mir = fixture(
            "struct Ticket {} impl Use<[0, 1]> for Ticket {} struct Pair { left: Ticket, right: Ticket } impl Use<[0, 1]> for Pair {} pub fn main(pair: Pair) -> (Ticket, Ticket) { (pair.left, pair.right) }",
        );
        let mut first: Option<(ControlPlace, u32)> = None;
        for instruction in mir
            .blocks
            .iter_mut()
            .flat_map(|block| &mut block.instructions)
        {
            if let OwnershipOperation::Project {
                place,
                index,
                mode: ValueTransfer::Move,
                ..
            } = &mut instruction.operation
            {
                if let Some((first_place, first_index)) = &first {
                    *place = first_place.clone();
                    *index = *first_index;
                } else {
                    first = Some((place.clone(), *index));
                }
            }
        }
        assert!(first.is_some());
        mir.live_in = mir.compute_liveness();
        mir.elaborate_inventory();
        assert!(
            mir.validate_partial_paths()
                .unwrap_err()
                .0
                .contains("uninitialized projection")
        );
    }

    #[test]
    fn replacing_a_moved_field_restores_its_availability() {
        fixture("struct Ticket {} impl Use<[0, 1]> for Ticket {} struct Pair { left: Ticket, right: Ticket } impl Use<[0, 1]> for Pair {} pub fn main(pair: Pair) -> Ticket { let mut pair = pair; let taken = pair.left; pair.left = Ticket {}; pair.left }").validate_partial_paths().unwrap();
    }
}
