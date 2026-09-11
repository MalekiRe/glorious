//! Receiver authority reconstructed from executable capture access.
//!
//! Physical capture ownership does not decide invocation mode. In particular
//! an owned non-Copy capture can be observed through a shared receiver. The
//! actual instruction graph must neither mutate it under shared access nor
//! vacate it under either borrowed form.

use super::*;

/// Must permissions of every callable leaf in an evaluated resident. This
/// deliberately bounded product is conservative for heterogeneous fields;
/// projection cannot manufacture a permission absent from any possible leaf.
/// It is value evidence, not an ABI coercion or an assumed target identity.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(super) struct ReceiverAccess {
    shared: bool,
    unique: bool,
}

#[cfg(test)]
mod resident_tests {
    use super::*;

    fn callable(shared: bool) -> VmType {
        VmType::Callable { shared_receiver: shared, unique_receiver: shared,
            safety: Safety::Safe, parameters: vec![VmType::I64], result: Box::new(VmType::I64), effects: Box::default() }
    }

    fn fixture(prefix: Vec<VmInstruction>, callee: u32) -> VmFunction {
        let reference = VmType::Reference { unique: false, referent: Box::new(callable(false)) };
        let mut instructions = vec![VmInstruction::DeclareResult { result: VmType::I64, returns: true }];
        instructions.extend(prefix);
        instructions.extend([VmInstruction::CallIndirect { dst: 6, callee, arguments: vec![2] }, VmInstruction::Return { value: 6 }]);
        VmFunction { definition: DefKey(Digest::of_bytes(b"executed-receiver-access")), safety: Safety::Safe,
            unsafe_execution: false, captures: 0, parameters: 4, nominal_copy_descriptors: vec![],
            registers: vec![callable(true), callable(false), VmType::I64, VmType::Bool, callable(false), reference.clone(),
                VmType::I64, VmType::Tuple(vec![reference.clone()]), reference,
                VmType::Reference { unique: false, referent: Box::new(callable(true)) }, VmType::Unit],
            instructions }
    }

    fn borrow() -> VmInstruction {
        VmInstruction::Borrow { dst: 5, src: 4, fields: vec![], unique: false, reborrow: false }
    }

    fn accepted(function: &VmFunction) -> bool {
        verify_function_control(function, false, false, &Default::default()).is_ok()
    }

    fn receiver_rejected(function: &VmFunction) {
        let result = verify_function_control(function, false, false, &Default::default()).map(|_| ());
        assert!(matches!(result, Err(VmArtifactError::NotCallable { .. })), "{result:?}");
    }

    #[test]
    fn executed_receiver_access_follows_values_not_storage_types() {
        let prefix = vec![VmInstruction::Store { dst: 4, src: 0 }, borrow()];
        let direct = fixture(prefix.clone(), 5);
        assert!(accepted(&direct));
        let mut unknown = direct.clone();
        unknown.registers[0] = callable(false);
        receiver_rejected(&unknown);
        for transport in [
            vec![VmInstruction::Copy { dst: 8, src: 5 }],
            vec![VmInstruction::Move { dst: 8, src: 5 }],
            vec![VmInstruction::Borrow { dst: 8, src: 5, fields: vec![], unique: false, reborrow: true }],
            vec![VmInstruction::MakeTuple { dst: 7, fields: vec![5] },
                VmInstruction::ProjectTuple { dst: 8, base: 7, index: 0, field_count: 1, field_type: direct.registers[5].clone() }],
        ] {
            let mut transported = prefix.clone();
            transported.extend(transport);
            assert!(accepted(&fixture(transported.clone(), 8)), "{transported:?}");
            transported.push(VmInstruction::Store { dst: 4, src: 1 });
            receiver_rejected(&fixture(transported, 8));
        }
        let mut replaced = prefix.clone();
        replaced.insert(1, VmInstruction::Store { dst: 4, src: 1 });
        receiver_rejected(&fixture(replaced, 5));
        let mut mutated = prefix;
        mutated.push(VmInstruction::Call { dst: 10, callee: DefKey(Digest::of_bytes(b"unknown-writer")), arguments: vec![] });
        receiver_rejected(&fixture(mutated, 5));
    }

    #[test]
    fn executed_receiver_joins_and_weakened_reference_views_do_not_gain_authority() {
        let mut branch = fixture(vec![
            VmInstruction::BranchBool { condition: 3, then_target: 2, else_target: 4 },
            VmInstruction::Store { dst: 4, src: 0 }, VmInstruction::Jump { target: 6 },
            VmInstruction::Store { dst: 4, src: 0 }, VmInstruction::Jump { target: 6 }, borrow(),
        ], 5);
        assert!(accepted(&branch));
        branch.instructions[4] = VmInstruction::Store { dst: 4, src: 1 };
        receiver_rejected(&branch);
        let weakened = fixture(vec![
            VmInstruction::Borrow { dst: 9, src: 0, fields: vec![], unique: false, reborrow: false },
            VmInstruction::Copy { dst: 5, src: 9 },
        ], 5);
        receiver_rejected(&weakened);
    }

    #[test]
    fn executed_receiver_preparation_keeps_replacement_invalidation() {
        for reborrow in [false, true] {
            let mut function = fixture(vec![VmInstruction::Store { dst: 4, src: 0 }, borrow(),
                VmInstruction::PrepareInvocation { dst: 8, src: 5, fields: vec![], reborrow }], 8);
            if reborrow { function.registers[8] = callable(false); }
            function.instructions[4] = VmInstruction::CallPrepared { dst: 6, callee: 8, arguments: vec![2] };
            assert!(accepted(&function));
            if !reborrow {
                function.instructions.insert(4, VmInstruction::Store { dst: 4, src: 1 });
                receiver_rejected(&function);
            }
        }
    }
}

impl ReceiverAccess {
    const ALL: Self = Self { shared: true, unique: true };

    pub(super) fn meet(self, other: Self) -> Self {
        Self { shared: self.shared && other.shared, unique: self.unique && other.unique }
    }

    fn union(self, other: Self) -> Self {
        Self { shared: self.shared || other.shared, unique: self.unique || other.unique }
    }

    pub(super) fn permits(self, unique: bool) -> bool {
        if unique { self.unique } else { self.shared }
    }

    fn declared(function: &VmFunction, ty: &VmType, active: &mut Vec<VmType>) -> Self {
        match ty {
            VmType::Callable { shared_receiver, unique_receiver, .. } =>
                Self { shared: *shared_receiver, unique: *unique_receiver },
            VmType::Reference { referent, .. } | VmType::Array(referent)
            | VmType::FixedArray { element: referent, .. } | VmType::StaticData { element: referent, .. } =>
                Self::declared(function, referent, active),
            VmType::Tuple(fields) => fields.iter().fold(Self::ALL, |proof, field|
                proof.meet(Self::declared(function, field, active))),
            VmType::Nominal { .. } => {
                if active.contains(ty) { return Self::default(); }
                let Ok(layout) = nominal_layout_descriptor(function, ty) else { return Self::default(); };
                active.push(ty.clone());
                let proof = layout.variants.iter().flatten().fold(Self::ALL, |proof, field|
                    proof.meet(Self::declared(function, field, active)));
                active.pop();
                proof
            }
            VmType::RawPointer { .. } | VmType::Generic(_) | VmType::ConstGeneric { .. }
            | VmType::ConstIntegerExpr(_) => Self::default(),
            _ => Self::ALL,
        }
    }

    pub(super) fn resident(function: &VmFunction, states: &VerifierState, register: u32) -> Self {
        let Some(ty) = function.registers.get(register as usize) else { return Self::default(); };
        states.receiver_access.get(register as usize).copied().unwrap_or_default()
            .union(Self::declared(function, ty, &mut vec![]))
    }

    pub(super) fn constructed(function: &VmFunction, register: u32) -> Self {
        function.registers.get(register as usize).map(|ty| Self::declared(function, ty, &mut vec![])).unwrap_or_default()
    }

    /// Forgetting a reference view's contract cannot preserve its stronger
    /// authority in hidden provenance. Same-typed value transport and owned
    /// structural storage retain the evaluated resident's own contract.
    pub(super) fn transferred(self, function: &VmFunction, src: u32, dst: u32) -> Self {
        match (function.registers.get(src as usize), function.registers.get(dst as usize)) {
            (Some(source), Some(destination)) => self.transferred_view(source, destination),
            _ => Self::default(),
        }
    }

    pub(super) fn transferred_view(self, source: &VmType, destination: &VmType) -> Self {
        fn owned_view(source: &VmType, destination: &VmType) -> bool {
            if source == destination { return true; }
            match (source, destination) {
                (VmType::Callable { .. }, VmType::Callable { .. }) => true,
                (VmType::Tuple(source), VmType::Tuple(destination)) => source.len() == destination.len()
                    && source.iter().zip(destination).all(|(source, destination)| owned_view(source, destination)),
                (VmType::Array(source), VmType::Array(destination)) => owned_view(source, destination),
                (VmType::FixedArray { element: source, length: left }, VmType::FixedArray { element: destination, length: right }) =>
                    left == right && owned_view(source, destination),
                _ => false,
            }
        }
        if owned_view(source, destination) { self } else { Self::default() }
    }
}

fn carries_reference(function: &VmFunction, ty: &VmType) -> bool {
    !vm_tail_owned_type(ty, &function.nominal_copy_descriptors, &mut vec![])
}

fn carries_unique(function: &VmFunction, ty: &VmType, active: &mut BTreeSet<DefKey>) -> bool {
    match ty {
        VmType::Reference { unique, referent } => *unique || carries_unique(function, referent, active),
        VmType::Tuple(fields) => fields.iter().any(|ty| carries_unique(function, ty, active)),
        VmType::Array(ty) | VmType::FixedArray { element: ty, .. } | VmType::StaticData { element: ty, .. } => carries_unique(function, ty, active),
        VmType::Nominal { definition, .. } => {
            if !active.insert(*definition) { return false; }
            let value = nominal_layout_descriptor(function, ty).map_or(true, |layout|
                layout.variants.iter().flatten().any(|ty| carries_unique(function, ty, active)));
            active.remove(definition);
            value
        }
        VmType::Generic(_) => true,
        _ => false,
    }
}

/// Compute a monotone may-alias graph over all executable paths. No branch,
/// loop, handler or source-only annotation can hide a capture access. Values
/// which merely contain scalar copies do not alias the capture's storage.
fn aliases(function: &VmFunction) -> Vec<bool> {
    let mut aliases = function.registers.iter().enumerate().map(|(index, ty)|
        index < function.captures as usize && carries_reference(function, ty)).collect::<Vec<_>>();
    loop {
        let mut changed = false;
        for instruction in &function.instructions {
            let Some(dst) = native_storage::instruction_result(instruction) else { continue; };
            if aliases.get(dst as usize) != Some(&false)
                || !(matches!(instruction, VmInstruction::PrepareInvocation { .. })
                    || function.registers.get(dst as usize).is_some_and(|ty| carries_reference(function, ty))) { continue; }
            let mut tainted = false;
            native_storage::visit_locals(instruction, |value| {
                if value != dst { tainted |= aliases.get(value as usize) == Some(&true); }
            });
            if let VmInstruction::Borrow { src, .. } | VmInstruction::PrepareInvocation { src, .. } = instruction {
                tainted |= *src < function.captures;
            }
            if tainted { aliases[dst as usize] = true; changed = true; }
        }
        if !changed { return aliases; }
    }
}

pub(super) fn is_execution_boundary(instruction: &VmInstruction) -> bool {
    matches!(instruction, VmInstruction::Call { .. } | VmInstruction::CallOwned { .. }
        | VmInstruction::CallIndirect { .. } | VmInstruction::CallIndirectOwned { .. }
        | VmInstruction::CallPrepared { .. }
        | VmInstruction::HostCall { .. } | VmInstruction::HostCallOwned { .. }
        | VmInstruction::Perform { .. } | VmInstruction::PerformOwned { .. }
        | VmInstruction::TailCallOwned { .. } | VmInstruction::Return { .. }
        | VmInstruction::Forward | VmInstruction::Leave { .. })
}

pub(super) fn verify_claim(function: &VmFunction, shared: bool, unique: bool, captures_intact: bool) -> Result<(), VmArtifactError> {
    if !shared && !unique || function.captures == 0 { return Ok(()); }
    let aliases = aliases(function);
    let captured = |value: u32| value < function.captures;
    let aliases_capture = |value: u32| aliases.get(value as usize) == Some(&true);
    let mut permits_shared = true;
    let mut permits_unique = captures_intact;
    for instruction in &function.instructions {
        if native_storage::instruction_result(instruction).is_some_and(captured) {
            permits_shared = false;
        }
        if let Some(arguments) = instruction.consumed_arguments() {
            permits_shared &= !arguments.iter().copied().any(captured);
        }
        match instruction {
            VmInstruction::Move { src, .. } | VmInstruction::DestroyCallable { value: src, .. }
            | VmInstruction::StorageDead { local: src, .. } | VmInstruction::DestroyIf { local: src, .. }
                if captured(*src) => permits_shared = false,
            VmInstruction::TakeProjection { base, .. } | VmInstruction::TakeArrayElement { value: base, .. }
                if captured(*base) => { permits_shared = false; permits_unique = false; }
            VmInstruction::Borrow { src, unique: true, .. } if captured(*src) || aliases_capture(*src) => permits_shared = false,
            VmInstruction::DerefStore { reference, .. } if aliases_capture(*reference) => permits_shared = false,
            VmInstruction::DerefMove { reference, .. } if aliases_capture(*reference) => {
                // A reusable environment may not expose a moved-out resident
                // to its owner. This also catches aliased projected references.
                permits_shared = false; permits_unique = false;
            }
            VmInstruction::Call { arguments, .. } | VmInstruction::CallOwned { arguments, .. }
            | VmInstruction::TailCallOwned { arguments, .. }
            | VmInstruction::HostCall { arguments, .. } | VmInstruction::HostCallOwned { arguments, .. }
            | VmInstruction::Perform { arguments, .. } | VmInstruction::PerformOwned { arguments, .. } => {
                permits_shared &= !arguments.iter().any(|argument| aliases_capture(*argument)
                    && function.registers.get(*argument as usize).is_some_and(|ty| carries_unique(function, ty, &mut BTreeSet::new())));
            }
            VmInstruction::CallIndirect { callee, arguments, .. } | VmInstruction::CallIndirectOwned { callee, arguments, .. }
            | VmInstruction::CallPrepared { callee, arguments, .. } => {
                if captured(*callee) || aliases_capture(*callee) {
                    match function.registers.get(*callee as usize) {
                        Some(VmType::Reference { unique: false, .. }) => {},
                        Some(VmType::Reference { unique: true, .. }) => permits_shared = false,
                        _ => { permits_shared = false; permits_unique = false; },
                    }
                }
                permits_shared &= !arguments.iter().any(|argument| aliases_capture(*argument)
                    && function.registers.get(*argument as usize).is_some_and(|ty| carries_unique(function, ty, &mut BTreeSet::new())));
            }
            VmInstruction::MemoryIntrinsic { primitive: MemoryPrimitive::Forget, arguments, .. }
                if arguments.iter().copied().any(captured) => { permits_shared = false; permits_unique = false; }
            _ => {}
        }
    }
    if (shared && !permits_shared) || (unique && !permits_unique) {
        return Err(VmArtifactError::InvalidCallableEnvironment {
            message: "borrowed callable authority is not established by its executable capture accesses",
        });
    }
    Ok(())
}
