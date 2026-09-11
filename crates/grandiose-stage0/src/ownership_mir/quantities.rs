//! Resident quantity constraints produced at ownership elaboration. Closing a
//! type substitution changes the declaration inputs, not these storage rules.
use super::*;

#[derive(Clone, Debug)]
enum Rule {
    Declared,
    Constant(Quantity),
    Product(Vec<ControlValue>),
    Forward(ControlValue),
    Environment(Vec<(ControlValue, crate::CaptureMode)>),
}

/// Inputs to the resident at an executed use of a storage view. Constructor
/// evidence is separate from the whole-lifetime guarantee of its storage slot.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum ResidentInput {
    Initial(ControlValue),
    Value(ControlValue),
    Declared(ControlValue),
    Global(ControlValue),
    Unknown,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct Residents {
    values: BTreeMap<ControlValue, BTreeSet<ResidentInput>>,
    exposed: BTreeSet<ControlValue>,
}

impl Residents {
    fn join(&mut self, other: &Self) {
        let keys = self.values.keys().chain(other.values.keys()).copied().collect::<BTreeSet<_>>();
        for key in keys {
            let left = self.values.entry(key).or_insert_with(|| BTreeSet::from([ResidentInput::Unknown]));
            if let Some(right) = other.values.get(&key) { left.extend(right); }
            else { left.insert(ResidentInput::Unknown); }
        }
        self.exposed.extend(&other.exposed);
    }

    fn expose(&mut self, root: ControlValue) {
        self.exposed.insert(root);
        self.values.entry(root).or_default().insert(ResidentInput::Declared(root));
    }
}

#[derive(Clone, Debug)]
pub(super) struct Rules {
    rules: Vec<Rule>,
    replacements: BTreeMap<ControlValue, Vec<ControlValue>>,
    exposed: BTreeSet<ControlValue>,
    /// All executed uses of each whole-slot observation, not its earlier Read
    /// instruction. A deferred view cannot retain a pre-replacement snapshot.
    view_inputs: BTreeMap<ControlValue, BTreeSet<ResidentInput>>,
    /// Open lexical evidence remains valid when a closed query cannot improve
    /// it. It is not used as a substitute for a failed constraint solution.
    pub(super) declared: Vec<Option<Quantity>>,
    pub(super) input: Option<std::sync::Arc<Input>>,
}

#[derive(Clone, Debug)]
pub(super) struct Input {
    definition: DefKey,
    entry: ControlBlockId,
    parameters: Vec<ControlValue>,
    values: Vec<ControlValueDecl>,
    owners: Vec<Owner>,
    blocks: Vec<OwnershipBlock>,
    loans: Vec<Loan>,
    aliases: BTreeMap<ControlValue, ControlValue>,
    captures: Vec<crate::CaptureEnvironment>,
}

pub(super) fn declared_quantity(
    ty: &Type, signatures: Option<&ElaboratedInterface>, solver: Option<&crate::TraitSolver>,
    bounds: &[(Type, crate::ElaboratedTraitReference)],
) -> Option<Quantity> {
    match ty {
        Type::Callable { invocation, .. } => Some(*invocation),
        Type::Reference { mutability: crate::Mutability::Unique, .. } => Some(Quantity::AFFINE),
        Type::Reference { .. } | Type::Scalar(_) | Type::Unit | Type::Never => Some(Quantity::UNRESTRICTED),
        ty => signatures.zip(solver).and_then(|(signatures, solver)|
            signatures.principal_use_interval_with_solver(ty, solver).or_else(||
                signatures.principal_use_interval_with_bounds_and_solver(ty, bounds, solver))),
    }
}

impl Rules {
    #[cfg(test)]
    pub(super) fn declared_test_graph(body: &OwnershipMir) -> Self {
        // Hand-built CFG fixtures supply their declaration permissions; they
        // cannot manufacture any reaching-resident/view refinements.
        Self { rules: vec![Rule::Declared; body.owners.len()],
            replacements: BTreeMap::new(), exposed: BTreeSet::new(), view_inputs: BTreeMap::new(),
            declared: body.owners.iter().map(|owner| owner.quantity).collect(),
            input: Some(Self::seal_input(body)) }
    }

    pub(super) fn seal_input(body: &OwnershipMir) -> std::sync::Arc<Input> {
        std::sync::Arc::new(Input { definition: body.definition, entry: body.entry, parameters: body.parameters.clone(),
            values: body.values.clone(), owners: body.owners.clone(), blocks: body.blocks.clone(),
            loans: body.loans.clone(), aliases: body.aliases.clone(),
            captures: body.closures.iter().map(|closure| closure.environment.clone()).collect() })
    }

    pub(super) fn matches(&self, body: &OwnershipMir) -> bool {
        self.input.as_ref().is_some_and(|input| input.definition == body.definition
            && input.entry == body.entry && input.parameters == body.parameters
            && input.values == body.values && input.owners == body.owners && input.blocks == body.blocks
            && input.loans == body.loans && input.aliases == body.aliases
            && input.captures.len() == body.closures.len()
            && input.captures.iter().zip(&body.closures).all(|(capture, closure)| *capture == closure.environment))
    }

    pub(super) fn forward_temporary(&mut self, source: ControlValue) {
        self.rules.push(Rule::Forward(source));
        self.declared.push(self.declared[source.0 as usize]);
    }

    pub(super) fn produce(
        control: &ControlMir, value_places: &BTreeMap<ControlValue, ControlPlace>,
        owners: &[Owner], declared: Vec<Option<Quantity>>,
    ) -> Result<Self, OwnershipError> {
        let mut result = Self { rules: vec![Rule::Declared; declared.len()],
            replacements: BTreeMap::new(), exposed: BTreeSet::new(),
            view_inputs: BTreeMap::new(), declared, input: None };
        for instruction in control.blocks().iter().flat_map(|block| &block.instructions) {
            result.rules[instruction.destination.0 as usize] = match &instruction.operation {
                ControlOperation::Function { .. }
                | ControlOperation::Capability(ControlCapabilityOperation::HostFunction { .. }
                    | ControlCapabilityOperation::TraitMethod { .. }) => Rule::Constant(Quantity::UNRESTRICTED),
                ControlOperation::Tuple(fields) | ControlOperation::Array(fields) => Rule::Product(fields.clone()),
                ControlOperation::Read(source) | ControlOperation::Forward(source) | ControlOperation::Acquire(source)
                | ControlOperation::EndScope { value: source, .. } => Rule::Forward(*source),
                ControlOperation::Capability(ControlCapabilityOperation::Closure { closure, captures }) =>
                    Rule::Environment(captures.iter().zip(&control.closures()[closure.0 as usize].environment.captures)
                        .map(|(value, capture)| (*value, capture.mode)).collect()),
                _ => Rule::Declared,
            };
            match &instruction.operation {
                ControlOperation::Capability(ControlCapabilityOperation::Assign { place, value }) => {
                    let place = resolve_place(place.clone(), value_places);
                    if let Some(destination) = structural_storage_root(&place, control.values()) {
                        result.replacements.entry(destination).or_default().push(*value);
                    }
                }
                ControlOperation::Capability(ControlCapabilityOperation::Borrow { place, unique: true }) => {
                    let place = resolve_place(place.clone(), value_places);
                    if let Some(destination) = local_storage_root(&place) { result.exposed.insert(destination); }
                }
                ControlOperation::Capability(ControlCapabilityOperation::Closure { closure, captures }) => {
                    for (value, capture) in captures.iter().zip(&control.closures()[closure.0 as usize].environment.captures) {
                        if capture.mode == crate::CaptureMode::UniqueBorrow {
                            let place = value_places.get(value).cloned().unwrap_or(ControlPlace::Local(*value));
                            if let Some(destination) = local_storage_root(&place) { result.exposed.insert(destination); }
                        }
                    }
                }
                _ => {}
            }
        }
        let changed = result.replacements.keys().chain(&result.exposed).copied().collect();
        result.view_inputs = Self::view_residents(control, value_places, owners, &changed)?;
        Ok(result)
    }

    /// Project the existing Control CFG into finite reaching-resident rules.
    /// This does not infer source ownership, reference targets or Copy traits.
    /// Dynamic control edges retain the whole-storage guarantee because this
    /// CFG does not describe every suspended/handler interleaving.
    fn view_residents(control: &ControlMir, places: &BTreeMap<ControlValue, ControlPlace>, owners: &[Owner],
        changed: &BTreeSet<ControlValue>)
        -> Result<BTreeMap<ControlValue, BTreeSet<ResidentInput>>, OwnershipError>
    {
        let views = owners.iter().filter(|owner| owner.kind == OwnerKind::View)
            .filter_map(|owner| match places.get(&owner.value) {
                Some(ControlPlace::Local(root) | ControlPlace::Temporary(root)) if *root != owner.value && changed.contains(root) =>
                    Some((owner.value, *root)),
                _ => None,
            }).collect::<BTreeMap<_, _>>();
        if views.is_empty() { return Ok(BTreeMap::new()); }
        let roots = views.values().copied().collect::<BTreeSet<_>>();
        let mut entry = Residents::default();
        for value in control.parameters().iter().filter(|value| roots.contains(value)) {
            entry.values.insert(*value, BTreeSet::from([ResidentInput::Initial(*value)]));
        }
        let mut incoming = vec![None; control.blocks().len()];
        incoming[control.entry().0 as usize] = Some(entry);
        let mut pending = BTreeSet::from([control.entry()]);
        let mut inputs: BTreeMap<ControlValue, BTreeSet<ResidentInput>> = BTreeMap::new();
        let mut budget = control.values().len().saturating_add(1).saturating_pow(2)
            .saturating_mul(control.blocks().len().saturating_add(1)).saturating_mul(4);
        while let Some(block_id) = pending.pop_first() {
            let block = &control.blocks()[block_id.0 as usize];
            let mut state = incoming[block_id.0 as usize].clone().unwrap();
            for value in block.parameters.iter().filter(|value| roots.contains(value)) {
                state.values.insert(*value, BTreeSet::from([ResidentInput::Initial(*value)]));
            }
            let observe = |values: Vec<ControlValue>, state: &Residents,
                inputs: &mut BTreeMap<ControlValue, BTreeSet<ResidentInput>>| {
                for value in values {
                    if let Some(root) = views.get(&value) {
                        inputs.entry(value).or_default().extend(state.values.get(root).cloned()
                            .unwrap_or_else(|| BTreeSet::from([ResidentInput::Unknown])));
                    }
                }
            };
            for instruction in &block.instructions {
                budget = budget.checked_sub(1).ok_or_else(||
                    OwnershipError("resident view constraints exhausted their control budget".into()))?;
                observe(instruction.operation.inputs(), &state, &mut inputs);
                match &instruction.operation {
                    ControlOperation::Capability(ControlCapabilityOperation::Assign { place, value }) => {
                        let place = resolve_place(place.clone(), places);
                        if let Some(root) = structural_storage_root(&place, control.values()).filter(|root| roots.contains(root)) {
                            if matches!(place, ControlPlace::Local(_) | ControlPlace::Temporary(_)) {
                                state.values.insert(root, BTreeSet::from([ResidentInput::Value(*value)]));
                            } else {
                                state.values.entry(root).or_insert_with(|| BTreeSet::from([ResidentInput::Unknown]))
                                    .insert(ResidentInput::Value(*value));
                            }
                            if state.exposed.contains(&root) { state.expose(root); }
                        }
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Borrow { place, unique: true }) => {
                        if let Some(root) = local_storage_root(&resolve_place(place.clone(), places)).filter(|root| roots.contains(root)) {
                            state.expose(root);
                        }
                    }
                    ControlOperation::Capability(ControlCapabilityOperation::Closure { closure, captures }) => {
                        for (value, capture) in captures.iter().zip(&control.closures()[closure.0 as usize].environment.captures) {
                            if capture.mode == crate::CaptureMode::UniqueBorrow
                                && let Some(root) = local_storage_root(places.get(value).unwrap_or(&ControlPlace::Local(*value)))
                                    .filter(|root| roots.contains(root)) {
                                state.expose(root);
                            }
                        }
                    }
                    _ => {}
                }
                if roots.contains(&instruction.destination) && owners[instruction.destination.0 as usize].kind != OwnerKind::View {
                    state.values.insert(instruction.destination, BTreeSet::from([ResidentInput::Initial(instruction.destination)]));
                    if state.exposed.contains(&instruction.destination) { state.expose(instruction.destination); }
                }
            }
            observe(block.terminator.inputs(), &state, &mut inputs);
            if matches!(block.terminator, ControlTerminator::Transfer(_)) {
                for (root, resident) in &mut state.values { resident.insert(ResidentInput::Global(*root)); }
            }
            for edge in block.terminator.edges() {
                let next = &mut incoming[edge.target.0 as usize];
                if let Some(previous) = next {
                    let before = previous.clone();
                    previous.join(&state);
                    if *previous != before { pending.insert(edge.target); }
                } else {
                    *next = Some(state.clone());
                    pending.insert(edge.target);
                }
            }
        }
        Ok(inputs)
    }

    pub(super) fn solve(&self, owners: &mut [Owner], seeds: &[Option<Quantity>],
        declared: &[Option<Quantity>],
    ) -> Result<(), OwnershipError> {
        if owners.len() != self.rules.len() || declared.len() != owners.len() || seeds.len() != owners.len() {
            return Err(OwnershipError("resident quantity constraints have mismatched inputs".into()));
        }
        for (owner, quantity) in owners.iter_mut().zip(seeds) { owner.quantity = *quantity; }
        // Every derived permission is an intersection of the finite input
        // endpoints. A non-converging dependency cycle is not published.
        for _ in 0..owners.len().saturating_mul(owners.len().saturating_add(1)).saturating_add(1) {
            let mut quantities = Vec::with_capacity(owners.len());
            for (index, rule) in self.rules.iter().enumerate() {
                quantities.push(match rule {
                    Rule::Declared => seeds[index],
                    Rule::Constant(quantity) => Some(*quantity),
                    Rule::Product(fields) => product_quantity(fields.iter().copied(), owners),
                    Rule::Forward(source) => owners[source.0 as usize].quantity,
                    Rule::Environment(captures) => environment_quantity(captures, owners),
                });
            }
            // The first solution is the value originally produced at each
            // definition. Slot-wide replacement/exposure bounds follow below;
            // a view's executed uses select the appropriate resident inputs.
            let initial = quantities.clone();
            for (view, inputs) in &self.view_inputs {
                quantities[view.0 as usize] = inputs.iter().try_fold(Quantity::UNRESTRICTED, |quantity, input| {
                    let next = match input {
                        ResidentInput::Initial(value) => initial[value.0 as usize],
                        ResidentInput::Value(value) | ResidentInput::Global(value) => owners[value.0 as usize].quantity,
                        ResidentInput::Declared(value) => declared[value.0 as usize],
                        ResidentInput::Unknown => None,
                    }?;
                    quantity.intersection(next).ok()
                });
            }
            for (destination, values) in &self.replacements {
                quantities[destination.0 as usize] = quantities[destination.0 as usize].and_then(|quantity|
                    values.iter().try_fold(quantity, |quantity, value|
                        quantity.intersection(owners[value.0 as usize].quantity?).ok()));
            }
            for destination in &self.exposed {
                quantities[destination.0 as usize] = quantities[destination.0 as usize]
                    .and_then(|quantity| quantity.intersection(declared[destination.0 as usize]?).ok());
            }
            if owners.iter().zip(&quantities).all(|(owner, quantity)| owner.quantity == *quantity) { return Ok(()); }
            for (owner, quantity) in owners.iter_mut().zip(quantities) { owner.quantity = quantity; }
        }
        Err(OwnershipError("resident quantity constraints did not converge".into()))
    }

    pub(super) fn close(&self, values: &[ControlValueDecl], owners: &[Owner],
        signatures: &ElaboratedInterface, solver: &crate::TraitSolver,
    ) -> Result<Vec<Owner>, OwnershipError> {
        let declared = values.iter().zip(&self.declared).map(|(value, open)|
            declared_quantity(&value.ty, Some(signatures), Some(solver), &[]).or(*open)).collect::<Vec<_>>();
        let seeds = values.iter().zip(&declared).map(|(value, declared)|
            solver.resident_use(&value.ty).or(*declared)).collect::<Vec<_>>();
        let mut closed = owners.to_vec();
        self.solve(&mut closed, &seeds, &declared)?;
        Ok(closed)
    }
}

impl OwnershipMir {
    pub(crate) fn close_owner_quantities(&self, values: &[ControlValueDecl],
        signatures: &ElaboratedInterface, solver: &crate::TraitSolver,
    ) -> Result<Vec<Owner>, OwnershipError> {
        if !self.quantity_rules.matches(self) {
            return Err(OwnershipError("resident quantity constraints have stale ownership inputs".into()));
        }
        self.quantity_rules.close(values, &self.owners, signatures, solver)
    }
}
