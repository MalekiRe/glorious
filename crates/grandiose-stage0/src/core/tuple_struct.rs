use super::*;

impl Elaborator<'_> {
    /// Tuple structs keep their nominal identity while sharing the record
    /// storage representation. Arguments are elaborated in source order.
    pub(super) fn tuple_struct_call(&mut self, expression: &ExprKind, expected: Option<Type>, span: Span) -> Option<CoreId> {
        let (callee, supplied) = match expression {
            ExprKind::Call { callee, arguments } => (self.body.expression(*callee).kind.clone(), Some(arguments)),
            ExprKind::Path(_) | ExprKind::GenericPath { .. } => (expression.clone(), None),
            _ => return None,
        };
        let (path, source_arguments) = match callee {
            ExprKind::Path(path) => (path, vec![]),
            ExprKind::GenericPath { path, effect_arguments, operation_arguments } if operation_arguments.is_empty() => (path, effect_arguments),
            _ => return None,
        };
        if path.len() == 1 && self.locals.lookup(&path[0]).is_some() { return None; }
        let ResolutionState::Resolved(definition) = self.index.resolve_path(DefinitionNamespace::Type, self.module, &path) else { return None; };
        // A transparent type alias does not reserve its spelling in the
        // value namespace. Ordinary functions/imports must still win there.
        match self.index.resolve_path(DefinitionNamespace::Value, self.module, &path) {
            ResolutionState::Resolved(value) if value == definition => {},
            ResolutionState::Unresolved => {},
            _ => return None,
        }
        if !matches!(self.signatures.definitions.get(&definition),
            Some(ElaboratedHeader::Nominal { layout: crate::signature::ElaboratedNominalLayout::TupleStruct(_), .. } | ElaboratedHeader::Alias { .. })) { return None; }
        let arguments = self.nominal_arguments(definition, &source_arguments, span)?;
        let nominal = self.signatures.normalize_type_aliases(Type::Nominal { definition, arguments });
        let Type::Nominal { definition, .. } = nominal else { return None; };
        if !matches!(self.signatures.definitions.get(&definition), Some(ElaboratedHeader::Nominal {
            layout: crate::signature::ElaboratedNominalLayout::TupleStruct(_), ..
        })) { return None; }
        let expected_result = if supplied.is_some() { expected.clone() } else {
            match &expected { Some(Type::Callable { result, .. }) => Some((**result).clone()), _ => None }
        };
        if let Some(expected) = expected_result
            && self.unify_rigid_lifetimes(nominal.clone(), expected, span).is_err() {
            return Some(self.fail(span, "G4411", "tuple struct constructor does not match its contextual expected type"));
        }
        let nominal = self.inference.zonk(nominal.clone()).unwrap_or(nominal);
        let Type::Nominal { arguments, .. } = &nominal else { unreachable!() };
        let fields = self.signatures.instantiate_struct_fields_generic(definition, arguments).ok()?;
        if supplied.is_some_and(|supplied| fields.len() != supplied.len()) {
            return Some(self.fail(span, "G4412", "tuple struct constructor argument count does not match its fields"));
        }
        for field in &fields {
            if !self.field_is_accessible(field, span) {
                return Some(self.fail(span, "G4140", "tuple struct construction names a private field outside its declaring module"));
            }
        }
        let Some(supplied) = supplied else {
            let callable = CallableId(self.next_callable);
            self.next_callable += 1;
            let parameters: Vec<_> = fields.into_iter().enumerate().map(|(index, field)| {
                (format!("<tuple-constructor-{}-{index}>", callable.0), self.normalize_concrete_type_projections(field.ty))
            }).collect();
            let callable_type = Type::Callable {
                safety: crate::Safety::Safe,
                lifetime_binders: match &expected { Some(Type::Callable { lifetime_binders, .. }) => *lifetime_binders, _ => 0 },
                parameters: parameters.iter().map(|(_, ty)| ty.clone()).collect(),
                result: Box::new(nominal.clone()), effects: EffectRow::empty(), invocation: crate::Quantity::ONCE,
            };
            if let Some(expected) = expected
                && self.unify_rigid_lifetimes(callable_type.clone(), expected, span).is_err() {
                return Some(self.fail(span, "G4414", "tuple struct constructor does not match its expected callable type"));
            }
            // The value retains its universal contract, while the lifted
            // body executes under one opened call, just like a source closure.
            let parameters: Vec<_> = parameters.into_iter().map(|(name, ty)| (name, open_hrtb_callable_body_type(ty, 0))).collect();
            let values = parameters.iter().map(|(name, ty)| self.alloc(CoreKind::Local(name.clone()), ty.clone(), span)).collect();
            let body = self.alloc(CoreKind::Record { definition, fields: values }, open_hrtb_callable_body_type(nominal, 0), span);
            return Some(self.alloc(CoreKind::Closure {
                callable, parameters,
                environment: CaptureEnvironment::seal(self.definition, callable, vec![], EffectRow::empty()), body,
            }, callable_type, span));
        };
        let mut values = Vec::with_capacity(fields.len());
        for (value, field) in supplied.iter().zip(fields) {
            let expected = self.normalize_concrete_type_projections(field.ty);
            let value = self.expression_expected(*value, Some(expected.clone()));
            let actual = self.expressions[value.0 as usize].ty.clone();
            if self.unify_rigid_lifetimes(expected, actual, span).is_err() {
                self.error(span, "G4413", "tuple struct argument does not match its declared field type");
                self.recovered = true;
            }
            values.push(value);
        }
        let ty = self.strict_result(&values, nominal);
        Some(self.alloc(CoreKind::Record { definition, fields: values }, ty, span))
    }
}
