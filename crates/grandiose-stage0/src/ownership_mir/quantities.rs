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

#[derive(Clone, Debug)]
pub(super) struct Rules {
    rules: Vec<Rule>,
    replacements: BTreeMap<ControlValue, Vec<ControlValue>>,
    exposed: BTreeSet<ControlValue>,
    /// Open lexical evidence remains valid when a closed query cannot improve
    /// it. It is not used as a substitute for a failed constraint solution.
    pub(super) declared: Vec<Option<Quantity>>,
    pub(super) input: Option<std::sync::Arc<Input>>,
}

#[derive(Clone, Debug)]
pub(super) struct Input {
    definition: DefKey,
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
    pub(super) fn seal_input(body: &OwnershipMir) -> std::sync::Arc<Input> {
        std::sync::Arc::new(Input { definition: body.definition,
            values: body.values.clone(), owners: body.owners.clone(), blocks: body.blocks.clone(),
            loans: body.loans.clone(), aliases: body.aliases.clone(),
            captures: body.closures.iter().map(|closure| closure.environment.clone()).collect() })
    }

    fn matches(&self, body: &OwnershipMir) -> bool {
        self.input.as_ref().is_some_and(|input| input.definition == body.definition
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
        declared: Vec<Option<Quantity>>,
    ) -> Self {
        let mut result = Self { rules: vec![Rule::Declared; declared.len()],
            replacements: BTreeMap::new(), exposed: BTreeSet::new(), declared, input: None };
        for instruction in control.blocks().iter().flat_map(|block| &block.instructions) {
            result.rules[instruction.destination.0 as usize] = match &instruction.operation {
                ControlOperation::Function { .. }
                | ControlOperation::Capability(ControlCapabilityOperation::HostFunction { .. }
                    | ControlCapabilityOperation::TraitMethod { .. }) => Rule::Constant(Quantity::UNRESTRICTED),
                ControlOperation::Tuple(fields) | ControlOperation::Array(fields) => Rule::Product(fields.clone()),
                ControlOperation::Read(source) | ControlOperation::Forward(source)
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
        result
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
