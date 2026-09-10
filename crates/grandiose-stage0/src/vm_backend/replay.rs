//! Storage duplication for a checked replay. Outer allocations retain their
//! identity; protected residents and their internal checked aliases do not.
use super::*;

type Homes = BTreeMap<usize, Arc<native_storage::NativeHome>>;

/// One transition supplies both execution engines. Snapshot uses leave their
/// original and decremented budget with the clause; the final use transfers
/// the original, including its resident storage and capture-loan identities.
pub(super) fn resume(frame: &mut RuntimeHandlerFrame, next_storage_id: &mut u64,
    budget: &mut ExecutionBudget, returns_to_clause: bool,
) -> Result<RuntimeContinuation, VmArtifactError> {
    if frame.continuation == VmContinuationPolicy::Terminal {
        return Err(VmArtifactError::HandlerResumeUnavailable);
    }
    let original = frame.suspended.pending().ok_or(VmArtifactError::HandlerResumeUnavailable)?;
    if !frame.continuation.is_replay() {
        return frame.suspended.take_pending().ok_or(VmArtifactError::HandlerResumeUnavailable);
    }
    // A non-returning snapshot transfer cannot abandon remaining required
    // invocations. Only the final original can leave the clause permanently.
    if !returns_to_clause && original.remaining_replays != 1 {
        return Err(VmArtifactError::HandlerResumeUnavailable);
    }
    match original.remaining_replays {
        0 => Err(VmArtifactError::HandlerResumeUnavailable),
        1 => {
            let original = frame.suspended.take_pending().expect("checked pending original");
            if returns_to_clause { frame.suspended = RuntimeSuspension::Replayed; }
            Ok(original)
        }
        _ => {
            let snapshot = if frame.owned_payloads {
                fork(original, frame.call_depth, &frame.shared_registers, next_storage_id, budget)?
            } else { original.clone() };
            frame.suspended.pending_mut().expect("checked pending original").remaining_replays -= 1;
            Ok(snapshot)
        }
    }
}

pub(super) fn shared_registers(
    registers: &RuntimeRegisters,
    enabled: bool,
    owned: &[u32],
    budget: &mut ExecutionBudget,
) -> Result<BTreeMap<u32, Option<u64>>, VmArtifactError> {
    if !enabled {
        return Ok(BTreeMap::new());
    }
    budget.reserve_value("retained outer storage", registers.len())?;
    Ok(registers
        .values
        .iter()
        .enumerate()
        .filter_map(|(index, _)| {
            let index = index as u32;
            (!owned.contains(&index))
                .then(|| (index, registers.source_storage.get(&index).copied()))
        })
        .collect())
}

pub(super) fn shared(
    registers: &RuntimeRegisters,
    index: u32,
    outer: &BTreeMap<u32, Option<u64>>,
) -> bool {
    !registers.prepared_receivers.contains(&index) && outer
        .get(&index)
        .is_some_and(|brand| *brand == registers.source_storage.get(&index).copied())
}

/// One identity map covers the complete retained branch. A callable's vacant
/// environment and the active frame borrowing its captures must be copied as
/// one ownership relationship, not as independent snapshots.
struct Duplication<'a> {
    homes: Homes,
    environments: BTreeMap<usize, Arc<RuntimeCaptureEnvironment>>,
    copied_homes: BTreeSet<usize>,
    copied_environments: BTreeSet<usize>,
    detached_environments: BTreeSet<usize>,
    brands: BTreeMap<u64, u64>,
    next_storage_id: &'a mut u64,
    budget: &'a mut ExecutionBudget,
}

impl Duplication<'_> {
    fn allocate_owned(&mut self, value: &VmValue) -> Result<(), VmArtifactError> {
        self.budget.tick()?;
        match value {
            VmValue::Resident(home) => {
                let identity = Arc::as_ptr(home) as usize;
                if !self.homes.contains_key(&identity) {
                    self.homes.insert(identity, native_storage::NativeHome::new(home.layout.clone(), self.budget)?);
                    let loaded = home.load(&[], self.budget)?;
                    self.allocate_owned(&loaded)?;
                }
            }
            VmValue::Callable { captures, .. } => {
                let identity = Arc::as_ptr(captures) as usize;
                if !self.environments.contains_key(&identity) {
                    self.budget.reserve_value("replayed capture environment", captures.len())?;
                    let values = captures.values.borrow();
                    let vacant = values.iter().map(|value| VmValue::Uninitialized(value.ty())).collect();
                    self.environments.insert(identity,
                        RuntimeCaptureEnvironment::with_ownership(vacant, captures.owned.clone()));
                    for (value, owned) in values.iter().zip(&captures.owned) {
                        if *owned { self.allocate_owned(value)?; }
                    }
                }
            }
            VmValue::Tuple(values) | VmValue::Array { values }
            | VmValue::Record { fields: values, .. } | VmValue::Enum { fields: values, .. } => {
                for value in values.iter() { self.allocate_owned(value)?; }
            }
            // Borrowed referents acquire a new identity only when their
            // independently owned root is selected elsewhere in this branch.
            _ => {}
        }
        Ok(())
    }

    fn rebase(&mut self, mut value: VmValue) -> Result<VmValue, VmArtifactError> {
        self.budget.tick()?;
        match &mut value {
            VmValue::Reference { target: ReferenceTarget::Home(home), .. }
            | VmValue::Resident(home) => {
                if let Some(copied) = self.homes.get(&(Arc::as_ptr(home) as usize)) {
                    *home = copied.clone();
                }
            }
            VmValue::Reference { target: ReferenceTarget::Captured(captured), .. } => {
                *captured = Arc::new(self.rebase((**captured).clone())?);
            }
            VmValue::Callable { captures, .. } => {
                if let Some(copied) = self.environments.get(&(Arc::as_ptr(captures) as usize)) {
                    *captures = copied.clone();
                }
            }
            VmValue::Tuple(values) | VmValue::Array { values }
            | VmValue::Record { fields: values, .. } | VmValue::Enum { fields: values, .. } => {
                self.budget.reserve_value("rebased aggregate", values.len())?;
                for value in Arc::make_mut(values) { *value = self.rebase(value.clone())?; }
            }
            VmValue::SuspendedReference(reference) => {
                **reference = self.rebase((**reference).clone())?;
            }
            _ => {}
        }
        Ok(value)
    }

    fn copy_owned(&mut self, mut value: VmValue) -> Result<VmValue, VmArtifactError> {
        self.budget.tick()?;
        match &mut value {
            VmValue::Resident(home) => {
                let identity = Arc::as_ptr(home) as usize;
                let copied = self.homes.get(&identity)
                    .ok_or(VmArtifactError::HandlerStateMismatch)?.clone();
                if self.copied_homes.insert(identity) {
                    let loaded = home.load(&[], self.budget)?;
                    let loaded = self.copy_owned(loaded)?;
                    copied.store(&[], &loaded, self.budget)?;
                }
                *home = copied;
            }
            VmValue::Callable { captures, .. } => {
                let identity = Arc::as_ptr(captures) as usize;
                let copied = self.environments.get(&identity)
                    .ok_or(VmArtifactError::HandlerStateMismatch)?.clone();
                if self.copied_environments.insert(identity) {
                    let values = captures.values.borrow().iter().zip(&captures.owned)
                        .map(|(value, owned)| if *owned { self.copy_owned(value.clone()) }
                            else { self.rebase(value.clone()) })
                        .collect::<Result<Vec<_>, _>>()?;
                    *copied.values.borrow_mut() = values;
                }
                *captures = copied;
            }
            VmValue::Tuple(values) | VmValue::Array { values }
            | VmValue::Record { fields: values, .. } | VmValue::Enum { fields: values, .. } => {
                self.budget.reserve_value("replayed aggregate", values.len())?;
                for value in Arc::make_mut(values) { *value = self.copy_owned(value.clone())?; }
            }
            _ => return self.rebase(value),
        }
        Ok(value)
    }

    fn allocate_registers(&mut self, registers: &RuntimeRegisters,
        outer: &BTreeMap<u32, Option<u64>>) -> Result<(), VmArtifactError>
    {
        self.budget.reserve_value("replayed registers", registers.len())?;
        for (index, value) in registers.values.iter().enumerate() {
            if registers.prepared_receivers.contains(&(index as u32)) { continue; }
            if registers.capture_environment.as_ref().is_some_and(|environment|
                environment.owned.get(index) == Some(&false)) { continue; }
            if !shared(registers, index as u32, outer) && let Some(value) = value {
                self.allocate_owned(value)?;
            }
        }
        Ok(())
    }

    fn allocate_capture_loan(&mut self, registers: &RuntimeRegisters) -> Result<(), VmArtifactError> {
        if let Some(environment) = &registers.capture_environment {
            let identity = Arc::as_ptr(environment) as usize;
            if !self.environments.contains_key(&identity) {
                self.budget.reserve_value("detached replay capture environment", environment.len())?;
                let values = environment.values.borrow().iter()
                    .map(|value| VmValue::Uninitialized(value.ty())).collect();
                self.environments.insert(identity,
                    RuntimeCaptureEnvironment::with_ownership(values, environment.owned.clone()));
                self.detached_environments.insert(identity);
            }
        }
        Ok(())
    }

    fn copy_registers(&mut self, registers: &mut RuntimeRegisters,
        outer: &BTreeMap<u32, Option<u64>>) -> Result<(), VmArtifactError>
    {
        for index in 0..registers.len() {
            self.budget.tick()?;
            let local = index as u32;
            if shared(registers, local, outer) { continue; }
            registers.native_homes.remove(&local);
            if let Some(value) = registers.values[index].take() {
                if registers.prepared_receivers.contains(&local) {
                    // The view's native home is just a carrier. Rebase its
                    // resident against the already allocated branch owners,
                    // then give this branch its own carrier on next entry.
                    let value = match value {
                        VmValue::Resident(home) => home.load(&[], self.budget)?,
                        value => value,
                    };
                    registers.values[index] = Some(self.rebase(value)?);
                    registers.native_write(local);
                    continue;
                }
                let borrowed = registers.capture_environment.as_ref().is_some_and(|environment|
                    environment.owned.get(index) == Some(&false));
                let value = if borrowed { self.rebase(value)? } else { self.copy_owned(value)? };
                if let VmValue::Resident(home) = &value {
                    registers.native_homes.insert(local, home.clone());
                }
                registers.values[index] = Some(value);
            }
            if let Some(brand) = registers.source_storage.get_mut(&local) {
                *brand = match self.brands.entry(*brand) {
                    std::collections::btree_map::Entry::Occupied(entry) => *entry.get(),
                    std::collections::btree_map::Entry::Vacant(entry) => {
                        *self.next_storage_id = self.next_storage_id.checked_add(1)
                            .ok_or(VmArtifactError::HandlerStateMismatch)?;
                        *entry.insert(*self.next_storage_id)
                    }
                };
            }
        }
        if let Some(environment) = &mut registers.capture_environment
            && let Some(copied) = self.environments.get(&(Arc::as_ptr(environment) as usize))
        {
            registers.detached_captures |= self.detached_environments.contains(&(Arc::as_ptr(environment) as usize));
            *environment = copied.clone();
        }
        Ok(())
    }
}

fn shallow_continuation(original: &RuntimeContinuation, budget: &mut ExecutionBudget)
    -> Result<RuntimeContinuation, VmArtifactError>
{
    budget.reserve_value("replayed handler suffix", original.above.len())?;
    Ok(RuntimeContinuation {
        target: original.target, dst: original.dst, registers: original.registers.clone(),
        performed: original.performed.clone(), pending_leave: original.pending_leave.clone(),
        remaining_replays: original.remaining_replays, program: original.program.clone(),
        above: original.above.iter().map(|frame| RuntimeHandlerFrame {
            id: frame.id, call_depth: frame.call_depth, effect: frame.effect,
            effect_arguments: frame.effect_arguments.clone(), operation: frame.operation,
            payload_destinations: frame.payload_destinations.clone(), continuation: frame.continuation,
            target: frame.target, owned_payloads: frame.owned_payloads,
            shared_registers: frame.shared_registers.clone(),
            suspended: if matches!(frame.suspended, RuntimeSuspension::Replayed) {
                RuntimeSuspension::Replayed
            } else { RuntimeSuspension::Active },
        }).collect(),
    })
}

pub(super) fn fork(
    original: &RuntimeContinuation,
    owner_depth: usize,
    outer: &BTreeMap<u32, Option<u64>>,
    next_storage_id: &mut u64,
    budget: &mut ExecutionBudget,
) -> Result<RuntimeContinuation, VmArtifactError> {
    // Flatten and rebuild iteratively so nesting retained handlers does not
    // turn a checked replay into unbounded Rust-stack recursion.
    let mut nodes = vec![(original, shallow_continuation(original, budget)?, None)];
    let mut index = 0;
    while index < nodes.len() {
        let source = nodes[index].0;
        for (handler, frame) in source.above.iter().enumerate() {
            if let Some(saved) = frame.suspended.pending() {
                budget.reserve_value("replayed continuation paths", nodes.len() + 1)?;
                let copied = shallow_continuation(saved, budget)?;
                nodes.push((saved, copied, Some((index, handler))));
            }
        }
        index += 1;
    }
    let mut duplication = Duplication {
        homes: Homes::new(), environments: BTreeMap::new(),
        copied_homes: BTreeSet::new(), copied_environments: BTreeSet::new(),
        detached_environments: BTreeSet::new(),
        brands: BTreeMap::new(), next_storage_id, budget,
    };
    let empty = BTreeMap::new();
    for (_, fork, _) in &nodes {
        let depth = fork.program.as_ref().map_or(0, |program| program.callers.len());
        if owner_depth > depth { return Err(VmArtifactError::HandlerStateMismatch); }
        if let Some(program) = &fork.program {
            for (index, caller) in program.callers.iter().enumerate().skip(owner_depth) {
                duplication.allocate_registers(&caller.registers,
                    if index == owner_depth { outer } else { &empty })?;
            }
        }
        duplication.allocate_registers(&fork.registers,
            if depth == owner_depth { outer } else { &empty })?;
    }
    // Allocate missing loan destinations only after every owned callable has
    // been discovered. Missing destinations belong to outer, shared callables;
    // this branch owns a detached copy of their in-flight capture slots.
    for (_, fork, _) in &nodes {
        if let Some(program) = &fork.program {
            for caller in program.callers.iter().skip(owner_depth + 1) {
                duplication.allocate_capture_loan(&caller.registers)?;
            }
        }
        if fork.program.as_ref().is_some_and(|program| program.callers.len() > owner_depth) {
            duplication.allocate_capture_loan(&fork.registers)?;
        }
    }
    for (_, fork, _) in &mut nodes {
        let depth = fork.program.as_ref().map_or(0, |program| program.callers.len());
        if let Some(program) = &mut fork.program {
            for (index, caller) in program.callers.iter_mut().enumerate().skip(owner_depth) {
                duplication.copy_registers(&mut caller.registers,
                    if index == owner_depth { outer } else { &empty })?;
            }
        }
        duplication.copy_registers(&mut fork.registers,
            if depth == owner_depth { outer } else { &empty })?;
    }
    for (_, fork, _) in &mut nodes {
        for handler in &mut fork.above {
            for brand in handler.shared_registers.values_mut().flatten() {
                if let Some(copied) = duplication.brands.get(brand) { *brand = *copied; }
            }
        }
    }
    while let Some((_, fork, parent)) = nodes.pop() {
        if let Some((parent, handler)) = parent {
            nodes[parent].1.above[handler].suspended = RuntimeSuspension::Pending(fork);
        } else { return Ok(fork); }
    }
    Err(VmArtifactError::HandlerStateMismatch)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn suspended_prepared_receivers_rebase_to_their_owner_without_copying_it() {
        for native_carrier in [false, true] { for outer_owner in [false, true] {
            let mut budget = ExecutionBudget { native_memory: NativeMemory::default(), unsafe_execution: false,
                limits: Default::default(), instructions: 0, allocated_elements: 0 };
            let definition = DefKey(Digest::of_bytes(b"prepared-receiver-replay"));
            let signature = VmType::Callable { shared_receiver: true, unique_receiver: true,
                safety: Safety::Safe, parameters: vec![], result: Box::new(VmType::I64), effects: Box::default() };
            let environment = RuntimeCaptureEnvironment::new(vec![VmValue::I64(42)]);
            let owner = VmValue::Callable { callee: definition, captures: environment.clone(), signature: signature.clone() };
            let mut registers = RuntimeRegisters { values: vec![Some(owner.clone()), Some(owner)],
                prepared_receivers: BTreeSet::from([1]), ..Default::default() };
            if native_carrier {
                let layout = Arc::new(native_memory::native_layout(&signature, &Arc::from([]), &mut vec![]).unwrap());
                let home = native_storage::NativeHome::new(layout, &mut budget).unwrap();
                home.store(&[], registers.values[1].as_ref().unwrap(), &mut budget).unwrap();
                registers.values[1] = Some(VmValue::Resident(home.clone()));
                registers.native_homes.insert(1, home);
            }
            let retained = shared_registers(&registers, true, if outer_owner { &[] } else { &[0] }, &mut budget).unwrap();
            let original = RuntimeContinuation { target: 0, dst: 0, registers,
                performed: RuntimePerformed { effect: definition, effect_arguments: vec![], operation: 0, payloads: None },
                above: vec![], pending_leave: None, remaining_replays: 2, program: None };
            let copied = fork(&original, 0, &retained, &mut 0, &mut budget).unwrap();
            let VmValue::Callable { captures: copied_owner, .. } = copied.registers.values[0].as_ref().unwrap() else { panic!() };
            let VmValue::Callable { captures: copied_view, .. } = copied.registers.values[1].as_ref().unwrap() else { panic!() };
            assert!(Arc::ptr_eq(copied_owner, copied_view));
            assert_eq!(Arc::ptr_eq(copied_view, &environment), outer_owner);
            assert!(copied.registers.prepared_receivers.contains(&1));
            assert!(original.registers.prepared_receivers.contains(&1));
        } }
    }

    #[test]
    fn final_replay_transfers_original_storage_and_retires_its_budget() {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(), unsafe_execution: false,
            limits: Default::default(), instructions: 0, allocated_elements: 0,
        };
        let definition = DefKey(Digest::of_bytes(b"final-replay-original"));
        let layout = Arc::new(native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
        let home = native_storage::NativeHome::new(layout, &mut budget).unwrap();
        home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
        let original = RuntimeContinuation {
            target: 1, dst: 1,
            registers: RuntimeRegisters {
                values: vec![Some(VmValue::Resident(home.clone())), None],
                native_homes: BTreeMap::from([(0, home.clone())]),
                source_storage: BTreeMap::from([(0, 7)]), ..Default::default()
            },
            performed: RuntimePerformed { effect: definition, effect_arguments: vec![], operation: 0, payloads: None },
            above: vec![], pending_leave: None, remaining_replays: 3, program: None,
        };
        let mut frame = RuntimeHandlerFrame {
            id: 1, call_depth: 0, effect: definition, effect_arguments: vec![], operation: 0,
            payload_destinations: vec![], continuation: VmContinuationPolicy::Replay { uses: 3 },
            target: 2, owned_payloads: true, shared_registers: BTreeMap::new(),
            suspended: RuntimeSuspension::Pending(original),
        };
        let mut next_storage_id = 7;
        let spent_child = RuntimeHandlerFrame { id: 2, suspended: RuntimeSuspension::Replayed, ..frame.clone() };
        frame.suspended.pending_mut().unwrap().above.push(spent_child);
        assert!(frame.take_canceled_continuation().is_err());
        assert!(resume(&mut frame, &mut next_storage_id, &mut budget, false).is_err());
        for remaining in [2, 1] {
            let copied = resume(&mut frame, &mut next_storage_id, &mut budget, true).unwrap();
            let copied_home = &copied.registers.native_homes[&0];
            assert!(matches!(copied.above[0].suspended, RuntimeSuspension::Replayed));
            assert!(!Arc::ptr_eq(copied_home, &home));
            copied_home.clear(&[]);
            assert!(home.is_initialized(&[]));
            assert_eq!(frame.suspended.pending().unwrap().remaining_replays, remaining);
            assert!(frame.take_canceled_continuation().is_err());
        }
        let allocated_before = budget.allocated_elements;
        let mut tail_frame = frame.clone();
        let tail_use = resume(&mut tail_frame, &mut next_storage_id, &mut budget, false).unwrap();
        assert!(Arc::ptr_eq(&tail_use.registers.native_homes[&0], &home));
        assert!(tail_frame.suspended.is_active());
        let final_use = resume(&mut frame, &mut next_storage_id, &mut budget, true).unwrap();
        assert!(Arc::ptr_eq(&final_use.registers.native_homes[&0], &home));
        assert_eq!(final_use.registers.source_storage[&0], 7);
        assert_eq!(budget.allocated_elements, allocated_before, "consuming the original must not allocate a replay copy");
        assert!(matches!(frame.suspended, RuntimeSuspension::Replayed));
        assert!(!frame.suspended.is_active(), "a spent clause must not handle its own effects");
        assert!(resume(&mut frame, &mut next_storage_id, &mut budget, true).is_err());
        assert!(frame.take_canceled_continuation().unwrap().is_none(), "final cleanup must not destroy the original again");
    }

    #[test]
    fn replay_distinguishes_reserved_storage_and_rebases_internal_aliases() {
        let mut budget = ExecutionBudget {
            native_memory: NativeMemory::default(),
            unsafe_execution: false,
            limits: Default::default(),
            instructions: 0,
            allocated_elements: 0,
        };
        let scalar = Arc::new(
            native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap(),
        );
        let outer_home = native_storage::NativeHome::new(scalar, &mut budget).unwrap();
        outer_home
            .store(&[], &VmValue::I64(7), &mut budget)
            .unwrap();
        let mut registers = RuntimeRegisters {
            values: vec![Some(VmValue::Resident(outer_home.clone())), None, None],
            source_storage: BTreeMap::from([(0, 1), (1, 2)]),
            native_homes: BTreeMap::from([(0, outer_home.clone())]),
            ..Default::default()
        };
        // Protected slots are declared by continuation ownership, even when
        // vacant at capture. Other vacant slots belong to the retained scope.
        let outer = shared_registers(&registers, true, &[1, 2], &mut budget).unwrap();
        assert!(outer.contains_key(&0));
        assert!(!outer.contains_key(&1));
        let aggregate = Arc::new(
            native_memory::native_layout(
                &VmType::Tuple(vec![VmType::I64, VmType::Unit]),
                &Arc::from([]),
                &mut vec![],
            )
            .unwrap(),
        );
        let inner = native_storage::NativeHome::new(aggregate, &mut budget).unwrap();
        inner
            .store(
                &[],
                &VmValue::Tuple(Arc::from([VmValue::I64(42), VmValue::Unit])),
                &mut budget,
            )
            .unwrap();
        inner.clear(&[1]);
        registers.values[1] = Some(VmValue::Resident(inner.clone()));
        registers.native_homes.insert(1, inner.clone());
        registers.values[2] = Some(VmValue::Reference {
            unique: false,
            target: ReferenceTarget::Home(inner.clone()),
            fields: Arc::from([0]),
            referent: VmType::I64,
        });
        registers.values.push(Some(VmValue::Reference {
            unique: false,
            target: ReferenceTarget::Captured(Arc::new(VmValue::Resident(inner.clone()))),
            fields: Arc::from([0]),
            referent: VmType::I64,
        }));
        let mut original = RuntimeContinuation {
            target: 0,
            dst: 2,
            registers,
            performed: RuntimePerformed {
                effect: DefKey(Digest::of_bytes(b"replay-storage-test")),
                effect_arguments: vec![],
                operation: 0,
                payloads: None,
            },
            above: vec![],
            pending_leave: None,
            remaining_replays: 2,
            program: None,
        };
        original.above.push(RuntimeHandlerFrame {
            id: 1, call_depth: 0, effect: original.performed.effect,
            effect_arguments: vec![], operation: 0, payload_destinations: vec![],
            continuation: VmContinuationPolicy::Replay { uses: 2 }, target: 0,
            owned_payloads: true, shared_registers: BTreeMap::from([(1, Some(2))]),
            suspended: RuntimeSuspension::Pending(original.clone()),
        });
        let copied = fork(&original, 0, &outer, &mut 2, &mut budget).unwrap();
        assert!(Arc::ptr_eq(&copied.registers.native_homes[&0], &outer_home));
        let copied_inner = &copied.registers.native_homes[&1];
        assert_eq!(copied.above[0].shared_registers[&1], Some(copied.registers.source_storage[&1]));
        assert!(Arc::ptr_eq(&copied.above[0].suspended.pending().unwrap().registers.native_homes[&1], copied_inner));
        assert!(!Arc::ptr_eq(copied_inner, &inner));
        assert_ne!(
            copied.registers.source_storage[&1],
            original.registers.source_storage[&1]
        );
        assert!(!copied_inner.is_initialized(&[1]));
        let Some(VmValue::Reference {
            target: ReferenceTarget::Home(target),
            ..
        }) = &copied.registers.values[2]
        else {
            panic!()
        };
        assert!(Arc::ptr_eq(target, copied_inner));
        let Some(VmValue::Reference {
            target: ReferenceTarget::Captured(target),
            ..
        }) = &copied.registers.values[3]
        else {
            panic!()
        };
        let VmValue::Resident(target) = target.as_ref() else {
            panic!()
        };
        assert!(Arc::ptr_eq(target, copied_inner));
        let Some(VmValue::Reference {
            target: ReferenceTarget::Captured(target),
            ..
        }) = &original.registers.values[3]
        else {
            panic!()
        };
        let VmValue::Resident(target) = target.as_ref() else {
            panic!()
        };
        assert!(Arc::ptr_eq(target, &inner));
        copied_inner.clear(&[0]);
        assert!(inner.is_initialized(&[0]));
    }

    #[test]
    fn replay_restores_captures_to_the_copied_owner_or_a_detached_environment() {
        for outer_callable in [false, true] {
            let mut budget = ExecutionBudget {
                native_memory: NativeMemory::default(), unsafe_execution: false,
                limits: Default::default(), instructions: 0, allocated_elements: 0,
            };
            let layout = Arc::new(native_memory::native_layout(&VmType::I64, &Arc::from([]), &mut vec![]).unwrap());
            let home = native_storage::NativeHome::new(layout, &mut budget).unwrap();
            home.store(&[], &VmValue::I64(42), &mut budget).unwrap();
            let environment = RuntimeCaptureEnvironment::new(vec![VmValue::Uninitialized(VmType::I64)]);
            let definition = DefKey(Digest::of_bytes(b"replay-capture-identity"));
            let original = RuntimeContinuation {
                target: 0, dst: 1,
                registers: RuntimeRegisters {
                    values: vec![Some(VmValue::Resident(home.clone())), None],
                    native_homes: BTreeMap::from([(0, home.clone())]),
                    capture_environment: Some(environment.clone()), ..Default::default()
                },
                performed: RuntimePerformed {
                    effect: definition, effect_arguments: vec![], operation: 0, payloads: None,
                },
                above: vec![], pending_leave: None, remaining_replays: 2,
                program: Some(RuntimeProgramContinuation {
                    definition,
                    callers: vec![RuntimeProgramCaller {
                        definition, pc: 0, return_destination: 0,
                        registers: RuntimeRegisters {
                            values: vec![Some(VmValue::Callable {
                                callee: definition, captures: environment.clone(),
                                signature: VmType::Callable { shared_receiver: false, unique_receiver: false,
                                    safety: Safety::Safe, parameters: vec![], result: Box::new(VmType::I64),
                                    effects: Box::default(),
                                },
                            })],
                            source_storage: BTreeMap::from([(0, 1)]), ..Default::default()
                        },
                    }],
                }),
            };
            let outer = if outer_callable { BTreeMap::from([(0, Some(1))]) } else { BTreeMap::new() };
            let mut copied = fork(&original, 0, &outer, &mut 1, &mut budget).unwrap();
            let loan = copied.registers.capture_environment.clone().unwrap();
            assert!(!Arc::ptr_eq(&loan, &environment));
            assert_eq!(copied.registers.detached_captures, outer_callable);
            let Some(VmValue::Callable { captures, .. }) = &copied.program.as_ref().unwrap().callers[0].registers[0]
                else { panic!() };
            assert_eq!(Arc::ptr_eq(captures, &loan), !outer_callable);
            copied.registers.release_capture_loan(&mut budget).unwrap();
            assert!(matches!(&environment.values.borrow()[0], VmValue::Uninitialized(_)));
            let restored = loan.values.borrow();
            let VmValue::Resident(restored) = &restored[0] else { panic!() };
            assert!(!Arc::ptr_eq(restored, &home));
            restored.clear(&[]);
            assert!(home.is_initialized(&[]));
            let mut frame = RuntimeHandlerFrame {
                id: 1, call_depth: 0, effect: definition, effect_arguments: vec![], operation: 0,
                payload_destinations: vec![], continuation: VmContinuationPolicy::Replay { uses: 2 },
                target: 0, owned_payloads: true, shared_registers: outer,
                suspended: RuntimeSuspension::Pending(original),
            };
            let snapshot = resume(&mut frame, &mut 1, &mut budget, true).unwrap();
            assert!(!Arc::ptr_eq(snapshot.registers.capture_environment.as_ref().unwrap(), &environment));
            let mut final_use = resume(&mut frame, &mut 2, &mut budget, true).unwrap();
            assert!(Arc::ptr_eq(final_use.registers.capture_environment.as_ref().unwrap(), &environment));
            assert!(!final_use.registers.detached_captures);
            final_use.registers.release_capture_loan(&mut budget).unwrap();
            let values = environment.values.borrow();
            let VmValue::Resident(restored) = &values[0] else { panic!() };
            assert!(Arc::ptr_eq(restored, &home));
        }
    }
}
