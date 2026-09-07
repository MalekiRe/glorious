//! Validates the concrete product without consulting source bodies or selecting
//! traits. Generic closure, effect, layout and call metadata must all be gone.
use super::*;

fn invalid(message: impl Into<String>) -> SpecializedError {
    SpecializedError(message.into())
}

pub(crate) fn closed_type(ty: &Type) -> Result<(), SpecializedError> {
    if regions::body_type(ty) != *ty {
        return Err(invalid(
            "specialized type refers to an unapplied outer lifetime binder",
        ));
    }
    InstanceKey::new(
        DefKey(crate::Digest::of_bytes(b"specialized-type-check")),
        &[crate::GenericKind::Type],
        vec![GenericArgument::Type(ty.clone())],
    )
    .map(|_| ())
    .map_err(|error| {
        invalid(format!(
            "Specialized MIR retains a non-concrete type {ty:?}: {error:?}"
        ))
    })
}
fn closed_arguments(arguments: &[GenericArgument]) -> Result<(), SpecializedError> {
    let kinds = arguments
        .iter()
        .map(|argument| match argument {
            GenericArgument::Type(_) => crate::GenericKind::Type,
            GenericArgument::EffectRow(_) => crate::GenericKind::EffectRow,
            GenericArgument::Lifetime(_) => crate::GenericKind::Lifetime,
            GenericArgument::ConstU32(_) | GenericArgument::ConstU32Expr(_) => {
                crate::GenericKind::Const(crate::ConstKind::U32)
            }
            GenericArgument::ConstQuantity(_) => {
                crate::GenericKind::Const(crate::ConstKind::Quantity)
            }
            GenericArgument::ConstGeneric { kind, .. }
            | GenericArgument::ConstInfer { kind, .. }
            | GenericArgument::ConstProjection { kind, .. } => crate::GenericKind::Const(*kind),
        })
        .collect::<Vec<_>>();
    InstanceKey::new(
        DefKey(crate::Digest::of_bytes(b"specialized-argument-check")),
        &kinds,
        arguments.to_vec(),
    )
    .map(|_| ())
    .map_err(|error| {
        invalid(format!(
            "Specialized MIR retains non-concrete arguments: {error:?}"
        ))
    })
}
fn closed_row(row: &crate::EffectRow) -> Result<(), SpecializedError> {
    closed_arguments(&[GenericArgument::EffectRow(row.clone())])
}
fn closed_pattern(pattern: &crate::CorePattern) -> Result<(), SpecializedError> {
    match pattern {
        crate::CorePattern::Array { element, elements } => {
            closed_type(element)?;
            for pattern in elements {
                closed_pattern(pattern)?;
            }
        }
        crate::CorePattern::Tuple(fields) => {
            for pattern in fields {
                closed_pattern(pattern)?;
            }
        }
        crate::CorePattern::Record {
            field_types,
            fields,
            ..
        }
        | crate::CorePattern::Enum {
            field_types,
            fields,
            ..
        } => {
            for ty in field_types {
                closed_type(ty)?;
            }
            for field in fields {
                closed_type(&field.ty)?;
                closed_pattern(&field.pattern)?;
            }
        }
        crate::CorePattern::Error => return Err(invalid("recovered pattern in Specialized MIR")),
        _ => {}
    }
    Ok(())
}

impl SpecializedMir {
    pub(super) fn checked_place_type<'a>(
        &'a self,
        place: &'a ControlPlace,
    ) -> Result<&'a Type, SpecializedError> {
        let ty = match place {
            ControlPlace::Local(value) | ControlPlace::Temporary(value) => {
                &self
                    .values
                    .get(value.0 as usize)
                    .ok_or_else(|| invalid("unknown specialized place"))?
                    .ty
            }
            ControlPlace::Deref { reference, ty } => {
                let reference = &self
                    .values
                    .get(reference.0 as usize)
                    .ok_or_else(|| invalid("unknown specialized reference"))?
                    .ty;
                if !matches!(reference, Type::Reference { referent, .. } if referent.as_ref() == ty)
                {
                    return Err(invalid("specialized dereference type mismatch"));
                }
                ty
            }
            ControlPlace::Field {
                base,
                index,
                field_count,
                ty,
            } => {
                let base = self.checked_place_type(base)?;
                let fields = match base {
                    Type::Tuple(fields) => Some(fields),
                    Type::Nominal { .. } => self
                        .layouts
                        .iter()
                        .find(|layout| &layout.ty == base && !layout.is_enum)
                        .and_then(|layout| layout.variants.first()),
                    _ => None,
                };
                if *index >= *field_count
                    || fields.is_some_and(|fields| {
                        fields.len() != *field_count as usize
                            || fields.get(*index as usize) != Some(ty)
                    })
                {
                    return Err(invalid("specialized field disagrees with concrete layout"));
                }
                ty
            }
        };
        closed_type(ty)?;
        Ok(ty)
    }

    pub fn validate(&self) -> Result<(), SpecializedError> {
        if self.blocks.get(self.entry.0 as usize).is_none()
            || self.owners.len() != self.values.len()
        {
            return Err(invalid("incomplete specialized body"));
        }
        let expected = if self.source_definition == self.instance.callable {
            lower::executable(&self.instance)
        } else if self.instance.arguments().is_empty() {
            self.source_definition
        } else {
            crate::mir::materialized_lifted_callable_definition(
                &self.instance,
                self.source_definition,
            )
        };
        if self.definition != expected {
            return Err(invalid(
                "specialized executable identity disagrees with its instance",
            ));
        }
        closed_arguments(self.instance.arguments())?;
        closed_type(&self.result)?;
        for value in &self.values {
            closed_type(&value.ty)?;
        }
        for (index, owner) in self.owners.iter().enumerate() {
            if owner.value.0 as usize != index
                || owner
                    .scope
                    .is_some_and(|scope| self.scopes.get(scope.0 as usize).is_none())
            {
                return Err(invalid("invalid specialized owner identity"));
            }
        }
        for (index, scope) in self.scopes.iter().enumerate() {
            if scope
                .parent
                .is_some_and(|parent| parent.0 as usize >= index)
            {
                return Err(invalid("invalid specialized scope ancestry"));
            }
        }
        for (index, loan) in self.loans.iter().enumerate() {
            if loan.id.0 as usize != index {
                return Err(invalid("invalid specialized loan identity"));
            }
            let ty = self.checked_place_type(&loan.place)?;
            if !self.values.get(loan.destination.0 as usize).is_some_and(|value| matches!(&value.ty, Type::Reference { mutability, referent, .. } if referent.as_ref() == ty && (*mutability == crate::Mutability::Unique) == loan.unique)) { return Err(invalid("specialized loan ABI mismatch")); }
        }
        for (index, layout) in self.layouts.iter().enumerate() {
            closed_type(&layout.ty)?;
            if self.layouts[..index]
                .iter()
                .any(|prior| prior.ty == layout.ty)
                || (!layout.is_enum && layout.variants.len() != 1)
            {
                return Err(invalid("duplicate or malformed specialized layout"));
            }
            for fields in &layout.variants {
                for ty in fields {
                    closed_type(ty)?;
                }
            }
        }
        super::validate_layout_closure(&self.layouts)?;
        for (definition, key) in &self.dependencies {
            closed_arguments(key.arguments())?;
            if *definition != lower::executable(key) {
                return Err(invalid("specialized dependency key mismatch"));
            }
        }
        let targets = self.symbolic_targets();
        for value in &self.symbols {
            if !targets.contains_key(value)
                || self
                    .values
                    .get(value.0 as usize)
                    .is_none_or(|value| value.ty != Type::Unit)
            {
                return Err(invalid("invalid erased symbolic callable"));
            }
        }
        let check_operand = |operand: &OwnershipOperand| -> Result<(), SpecializedError> {
            let owner = self
                .owners
                .get(operand.value.0 as usize)
                .ok_or_else(|| invalid("unknown specialized operand"))?;
            if operand.mode == ValueTransfer::Copy
                && owner.quantity != Some(crate::Quantity::UNRESTRICTED)
            {
                return Err(invalid("specialization invented generic copy authority"));
            }
            Ok(())
        };
        for block in &self.blocks {
            let runtime_inputs = match &block.terminator.control {
                SpecializedControl::Invoke {
                    callee, arguments, ..
                } if self.symbols.contains(callee) => arguments.clone(),
                terminator => terminator.inputs(),
            };
            if runtime_inputs
                .iter()
                .any(|value| self.symbols.contains(value))
            {
                return Err(invalid(
                    "erased callable escapes through a runtime terminator operand",
                ));
            }
            for edge in block.terminator.control.edges() {
                if self.blocks.get(edge.target.0 as usize).is_none() {
                    return Err(invalid("unknown specialized successor"));
                }
            }
            let edges = block.terminator.control.edges();
            if edges.len() != block.terminator.successors.len()
                || edges
                    .iter()
                    .zip(&block.terminator.successors)
                    .any(|(edge, successor)| {
                        edge.target != successor.target
                            || edge.arguments
                                != successor
                                    .arguments
                                    .iter()
                                    .map(|operand| operand.value)
                                    .collect::<Vec<_>>()
                    })
            {
                return Err(invalid(
                    "specialized ownership successors disagree with control",
                ));
            }
            if block.terminator.control.inputs()
                != block
                    .terminator
                    .operands
                    .iter()
                    .map(|operand| operand.value)
                    .collect::<Vec<_>>()
            {
                return Err(invalid(
                    "specialized terminator operands disagree with control",
                ));
            }
            for operand in &block.terminator.operands {
                check_operand(operand)?;
            }
            for edge in &block.terminator.successors {
                for operand in &edge.arguments {
                    check_operand(operand)?;
                }
            }
            match &block.terminator.control {
                SpecializedControl::Invoke { callee, target, .. } => {
                    if target
                        != targets
                            .get(callee)
                            .unwrap_or(&SpecializedCallTarget::Indirect)
                    {
                        return Err(invalid(
                            "specialized call target disagrees with symbolic value",
                        ));
                    }
                    if let SpecializedCallTarget::Direct(definition) = target
                        && !self.dependencies.contains_key(definition)
                    {
                        return Err(invalid(
                            "specialized direct target lacks an instance dependency",
                        ));
                    }
                }
                SpecializedControl::Transfer(ControlTransfer::Perform {
                    effect,
                    payload_types,
                    ..
                }) => {
                    closed_arguments(&effect.arguments)?;
                    for ty in payload_types {
                        closed_type(ty)?;
                    }
                }
                SpecializedControl::Return(value)
                    if !crate::control_mir::call_type_matches(
                        &self.result,
                        &self
                            .values
                            .get(value.0 as usize)
                            .ok_or_else(|| invalid("unknown return value"))?
                            .ty,
                    ) =>
                {
                    return Err(invalid("specialized return type mismatch"));
                }
                _ => {}
            }
            for instruction in &block.instructions {
                let symbolic_forward = self.symbols.contains(&instruction.destination)
                    && matches!(
                        instruction.operation,
                        SpecializedOperation::Read(_)
                            | SpecializedOperation::Transfer { .. }
                            | SpecializedOperation::ExitScope { .. }
                    );
                if !symbolic_forward
                    && !matches!(instruction.operation, SpecializedOperation::Discard(_))
                    && instruction
                        .operation
                        .inputs(&self.loans)
                        .iter()
                        .any(|value| self.symbols.contains(value))
                {
                    return Err(invalid(
                        "erased callable escapes through a runtime instruction operand",
                    ));
                }
                if self.scopes.get(instruction.scope.0 as usize).is_none() {
                    return Err(invalid("unknown specialized instruction scope"));
                }
                match &instruction.operation {
                    SpecializedOperation::Compute(SpecializedComputation::Function {
                        definition,
                        arguments,
                    }) => {
                        closed_arguments(arguments)?;
                        if !self.primitive_definitions.contains(definition)
                            && (!arguments.is_empty()
                                || !self.dependencies.contains_key(definition))
                        {
                            return Err(invalid("unresolved specialized function identity"));
                        }
                    }
                    SpecializedOperation::Compute(SpecializedComputation::HostFunction {
                        arguments,
                        ..
                    }) => closed_arguments(arguments)?,
                    SpecializedOperation::Compute(SpecializedComputation::Constant {
                        definition,
                    }) if !self.dependencies.contains_key(definition) => {
                        return Err(invalid("unresolved specialized constant identity"));
                    }
                    SpecializedOperation::Compute(SpecializedComputation::Test {
                        pattern, ..
                    }) => closed_pattern(pattern)?,
                    SpecializedOperation::Construct { aggregate, fields } => {
                        for field in fields {
                            check_operand(field)?;
                        }
                        if matches!(
                            aggregate,
                            OwnershipAggregate::Record(_) | OwnershipAggregate::Enum { .. }
                        ) {
                            let ty = &self
                                .values
                                .get(instruction.destination.0 as usize)
                                .ok_or_else(|| invalid("unknown aggregate destination"))?
                                .ty;
                            let layout = self
                                .layouts
                                .iter()
                                .find(|layout| &layout.ty == ty)
                                .ok_or_else(|| invalid("aggregate lacks a concrete layout"))?;
                            let index = match aggregate {
                                OwnershipAggregate::Enum { variant, .. } => *variant as usize,
                                _ => 0,
                            };
                            let expected = layout.variants.get(index).ok_or_else(|| {
                                invalid("aggregate variant exceeds concrete layout")
                            })?;
                            if expected.len() != fields.len()
                                || expected.iter().zip(fields).any(|(ty, field)| {
                                    self.values.get(field.value.0 as usize).is_none_or(|value| {
                                        !crate::control_mir::call_type_matches(ty, &value.ty)
                                    })
                                })
                            {
                                return Err(invalid(
                                    "aggregate operands disagree with concrete layout",
                                ));
                            }
                        }
                    }
                    SpecializedOperation::Transfer { value, mode }
                    | SpecializedOperation::ExitScope {
                        result: value,
                        mode,
                        ..
                    } => check_operand(&OwnershipOperand {
                        value: *value,
                        mode: *mode,
                    })?,
                    SpecializedOperation::ReadPlace { place, .. }
                    | SpecializedOperation::Project { place, .. }
                    | SpecializedOperation::MovePlace(place) => {
                        self.checked_place_type(place)?;
                    }
                    SpecializedOperation::Replace { place, value, mode } => {
                        self.checked_place_type(place)?;
                        check_operand(&OwnershipOperand {
                            value: *value,
                            mode: *mode,
                        })?;
                    }
                    SpecializedOperation::Borrow(id)
                        if self
                            .loans
                            .get(id.0 as usize)
                            .is_none_or(|loan| loan.destination != instruction.destination) =>
                    {
                        return Err(invalid("unknown specialized loan"));
                    }
                    SpecializedOperation::Capture { closure, captures } => {
                        let closure = self
                            .closures
                            .get(closure.0 as usize)
                            .ok_or_else(|| invalid("unknown specialized closure"))?;
                        let ty = &self
                            .values
                            .get(instruction.destination.0 as usize)
                            .ok_or_else(|| invalid("unknown closure destination"))?
                            .ty;
                        if let Some(error) = crate::core::capture_environment_error(
                            closure.environment.brand.callable,
                            &closure.environment,
                            ty,
                        ) {
                            return Err(invalid(error));
                        }
                        if captures.len() != closure.environment.captures.len()
                            || captures.iter().zip(&closure.environment.captures).any(
                                |((value, mode), capture)| {
                                    *mode != capture.mode
                                        || self
                                            .values
                                            .get(value.0 as usize)
                                            .is_none_or(|value| value.ty != capture.ty)
                                },
                            )
                        {
                            return Err(invalid("specialized capture ABI mismatch"));
                        }
                    }
                    _ => {}
                }
            }
        }
        for handler in &self.handlers {
            for clause in &handler.clauses {
                closed_arguments(&clause.effect.arguments)?;
                for pattern in &clause.patterns {
                    closed_pattern(pattern)?;
                }
                if let Some(contract) = &clause.contract {
                    closed_type(&contract.parameter)?;
                    closed_type(&contract.result)?;
                    closed_row(&contract.effects)?;
                }
            }
        }
        for closure in &self.closures {
            for capture in &closure.environment.captures {
                closed_type(&capture.ty)?;
            }
            closed_row(&closure.environment.runs_in.effects)?;
            closure.body.validate()?;
        }
        self.validate_graph()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::*;

    fn fixture(source: &str, arguments: Vec<GenericArgument>) -> SpecializedMir {
        let package = PackageKey("specialized-validator@0.1.0".into());
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
        let (ownership, result) = crate::ownership_mir::OwnershipMir::from_typed(
            definition.key,
            &core,
            &flow,
            Some(&signatures),
        )
        .unwrap();
        let ElaboratedHeader::Callable(signature) = &signatures.definitions[&definition.key] else {
            panic!("callable");
        };
        let key = InstanceKey::new(definition.key, &signature.generic_kinds, arguments).unwrap();
        SpecializedMir::lower(&ownership, &result, key, &signatures, None).unwrap()
    }
    fn i64_argument() -> Vec<GenericArgument> {
        vec![GenericArgument::Type(Type::Scalar(ScalarType::I64))]
    }

    #[test]
    fn specializes_all_generic_value_types_before_emission() {
        let body = fixture("pub fn main<T>(value: T) -> T { value }", i64_argument());
        assert_eq!(body.result, Type::Scalar(ScalarType::I64));
        assert!(
            body.values
                .iter()
                .all(|value| value.ty == Type::Scalar(ScalarType::I64))
        );
        assert_eq!(body.definition, DefKey(body.instance.fingerprint()));
    }
    #[test]
    fn resolves_generic_static_calls_to_executable_instance_keys() {
        let body = fixture(
            "fn identity<T>(value: T) -> T { value } pub fn main<T>(value: T) -> T { identity(value) }",
            i64_argument(),
        );
        let target = body
            .blocks
            .iter()
            .find_map(|block| match block.terminator.control {
                SpecializedControl::Invoke {
                    target: SpecializedCallTarget::Direct(target),
                    ..
                } => Some(target),
                _ => None,
            })
            .unwrap();
        let key = &body.dependencies[&target];
        assert_eq!(key.arguments(), i64_argument());
        assert_eq!(target, DefKey(key.fingerprint()));
        assert_ne!(target, key.callable);
    }
    #[test]
    fn freezes_and_rechecks_sealed_binding_pack_layouts() {
        let ty = crate::refinement::tests::environment(Type::Scalar(ScalarType::I64))
            .binding_pack_type(true, crate::Lifetime::Static).unwrap();
        let mut body = fixture("pub fn main<T>(value: T) -> T { value }", vec![GenericArgument::Type(ty.clone())]);
        let index = body.layouts.iter().position(|layout| layout.ty == ty).expect("binding pack layout");
        assert_eq!(body.layouts[index].variants, vec![vec![Type::Scalar(ScalarType::I64)]]);
        let signatures = crate::ElaboratedInterface::default();
        let mut cleanup = crate::cleanup_mir::CleanupMir::lower(&body, &signatures, &std::sync::Arc::new(BTreeMap::new())).unwrap();
        let (runtime, _) = cleanup.lower_runtime_values(ty, 0, None, Some(&signatures)).unwrap();
        let mut runtime = crate::runtime_mir::tests::finalize_fixture(runtime);
        cleanup.layouts[index].variants[0][0] = Type::Scalar(ScalarType::Bool);
        assert!(cleanup.validate().unwrap_err().0.contains("binding pack layout"));
        runtime.nominal_copy_descriptors[0].variants[0][0] = Type::Scalar(ScalarType::Bool);
        assert!(runtime.validate().unwrap_err().contains("binding pack layout"));
        body.layouts[index].variants[0][0] = Type::Scalar(ScalarType::Bool);
        assert!(body.validate().unwrap_err().0.contains("binding pack layout"));
    }

    #[test]
    fn freezes_instantiated_nominal_layouts() {
        let body = fixture(
            "struct Boxed<T> { value: T } pub fn main<T>(value: T) -> Boxed<T> { Boxed { value: value } }",
            i64_argument(),
        );
        let layout = body
            .layouts
            .iter()
            .find(|layout| layout.ty == body.result)
            .unwrap();
        assert_eq!(layout.variants, vec![vec![Type::Scalar(ScalarType::I64)]]);
    }
    #[test]
    fn specializes_nested_closure_bodies_and_capture_contracts() {
        let body = fixture(
            "pub fn main<T>(value: T) -> T { let action = move (value) { value }; action() }",
            i64_argument(),
        );
        let closure = &body.closures[0];
        assert_eq!(
            closure.environment.captures[0].ty,
            Type::Scalar(ScalarType::I64)
        );
        assert_eq!(closure.body.result, Type::Scalar(ScalarType::I64));
        assert_eq!(
            closure.body.definition,
            crate::mir::materialized_lifted_callable_definition(
                &body.instance,
                closure.body.source_definition
            )
        );
    }
    #[test]
    fn rejects_a_generic_value_after_specialization() {
        let mut body = fixture("pub fn main<T>(value: T) -> T { value }", i64_argument());
        body.values[0].ty = Type::Generic(0);
        assert!(body.validate().unwrap_err().0.contains("non-concrete type"));
    }
    #[test]
    fn rejects_a_forged_resolved_call_target() {
        let mut body = fixture(
            "fn identity<T>(value: T) -> T { value } pub fn main<T>(value: T) -> T { identity(value) }",
            i64_argument(),
        );
        for block in &mut body.blocks {
            if let SpecializedControl::Invoke { target, .. } = &mut block.terminator.control {
                *target = SpecializedCallTarget::Indirect;
            }
        }
        assert!(body.validate().unwrap_err().0.contains("target disagrees"));
    }
    #[test]
    fn rejects_a_generic_layout_field_after_specialization() {
        let mut body = fixture(
            "struct Boxed<T> { value: T } pub fn main<T>(value: T) -> Boxed<T> { Boxed { value: value } }",
            i64_argument(),
        );
        body.layouts[0].variants[0][0] = Type::Generic(0);
        assert!(body.validate().unwrap_err().0.contains("non-concrete type"));
    }
    #[test]
    fn rejects_noncanonical_instance_identity() {
        let mut body = fixture("pub fn main<T>(value: T) -> T { value }", i64_argument());
        body.definition = body.source_definition;
        assert!(
            body.validate()
                .unwrap_err()
                .0
                .contains("executable identity")
        );
    }

    #[test]
    fn concrete_layout_closure_includes_nested_instances_of_the_same_enum() {
        let mut body = fixture(
            "enum Maybe<T> { Some(T), None } struct Ticket { value: i64 } enum Phase { Ancestry(Maybe<Ticket>), Done } struct Attempt { phase: Phase } struct Engine { attempt: Maybe<Attempt> } pub fn main(engine: &mut Engine, phase: Phase) -> { let copy = phase; () }",
            vec![],
        );
        let phase = &body.values[1].ty;
        let nested = body
            .layouts
            .iter()
            .find(|layout| &layout.ty == phase)
            .unwrap()
            .variants[0][0]
            .clone();
        assert!(body.layouts.iter().any(|layout| layout.ty == nested));
        body.layouts.retain(|layout| layout.ty != nested);
        assert!(body.validate().unwrap_err().0.contains("nested instance"));
    }
}
