//! Representation-derived nominal variance over one immutable interface.
//! Recursive nominal dependencies are solved monotonically; unknown layouts
//! and unnormalized projections never supply a covariant permission.
use super::*;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum Variance {
    Bivariant,
    #[default]
    Covariant,
    Contravariant,
    Invariant,
}

impl Variance {
    fn bits(self) -> u8 {
        match self {
            Self::Bivariant => 0,
            Self::Covariant => 1,
            Self::Contravariant => 2,
            Self::Invariant => 3,
        }
    }
    fn from_bits(bits: u8) -> Self {
        match bits {
            0 => Self::Bivariant,
            1 => Self::Covariant,
            2 => Self::Contravariant,
            _ => Self::Invariant,
        }
    }
    fn join(self, other: Self) -> Self {
        Self::from_bits(self.bits() | other.bits())
    }
    pub(crate) fn compose(self, inner: Self) -> Self {
        let mut bits = 0;
        for (outer_bit, inner_bit, result) in [(1, 1, 1), (1, 2, 2), (2, 1, 2), (2, 2, 1)] {
            if self.bits() & outer_bit != 0 && inner.bits() & inner_bit != 0 {
                bits |= result;
            }
        }
        Self::from_bits(bits)
    }
}

#[derive(Debug, Default)]
pub(crate) struct NominalVariances(BTreeMap<DefKey, Vec<Variance>>);

impl NominalVariances {
    pub(crate) fn argument(&self, definition: DefKey, index: usize) -> Variance {
        self.0
            .get(&definition)
            .and_then(|arguments| arguments.get(index))
            .copied()
            .unwrap_or(Variance::Invariant)
    }

    fn derive(base: &TraitSolver) -> Self {
        let mut value = Self::default();
        let mut layouts = BTreeMap::new();
        for (definition, header) in base.definitions.iter() {
            let ElaboratedHeader::Nominal {
                generic_kinds,
                layout,
                contract,
                universal_bounds,
                ..
            } = header
            else {
                continue;
            };
            let fields: Option<Vec<&Type>> = match layout {
                ElaboratedNominalLayout::Struct(fields)
                | ElaboratedNominalLayout::TupleStruct(fields) => {
                    Some(fields.iter().map(|field| &field.ty).collect())
                }
                ElaboratedNominalLayout::Enum(variants) => Some(
                    variants
                        .iter()
                        .flat_map(|variant| match &variant.payload {
                            ElaboratedEnumVariantPayload::Unit => vec![],
                            ElaboratedEnumVariantPayload::Tuple(fields) => fields.iter().collect(),
                            ElaboratedEnumVariantPayload::Struct(fields) => {
                                fields.iter().map(|field| &field.ty).collect()
                            }
                        })
                        .collect(),
                ),
                ElaboratedNominalLayout::Opaque => None,
            };
            let mut solver = base.fresh_query();
            solver.set_lexical_assumptions(
                contract
                    .where_bounds
                    .iter()
                    .map(|(subject, relation)| TraitGoal {
                        subject: subject.clone(),
                        relation: relation.clone(),
                    })
                    .collect(),
            );
            solver.set_associated_bindings(
                contract.type_bindings.clone(),
                contract.effect_bindings.clone(),
            );
            solver.set_universal_assumptions(universal_bounds.clone());
            solver.set_outlives_assumptions(contract.where_outlives.clone());
            let fields = fields.and_then(|fields| {
                fields
                    .into_iter()
                    .map(|field| solver.normalize_type(field.clone()).ok())
                    .collect::<Option<Vec<_>>>()
            });
            value.0.insert(
                *definition,
                generic_kinds
                    .iter()
                    .map(|kind| {
                        if fields.is_some()
                            && matches!(
                                kind,
                                crate::GenericKind::Type | crate::GenericKind::Lifetime
                            )
                        {
                            Variance::Bivariant
                        } else {
                            Variance::Invariant
                        }
                    })
                    .collect(),
            );
            if let Some(fields) = fields {
                layouts.insert(*definition, fields);
            }
        }
        // A finite four-point lattice. Each slot acquires at most two signs;
        // only declarations depending on a changed constructor are revisited.
        let mut dependents = BTreeMap::<DefKey, BTreeSet<DefKey>>::new();
        for (definition, fields) in &layouts {
            let mut collector = Collector::new(&value, value.0[definition].len());
            for field in fields {
                collector.ty(field, Variance::Covariant, 0);
            }
            for dependency in collector.dependencies {
                dependents
                    .entry(dependency)
                    .or_default()
                    .insert(*definition);
            }
        }
        let mut pending = layouts.keys().copied().collect::<BTreeSet<_>>();
        let mut work = 0usize;
        while let Some(definition) = pending.pop_first() {
            let mut collector = Collector::new(&value, value.0[&definition].len());
            for field in &layouts[&definition] {
                collector.ty(field, Variance::Covariant, 0);
            }
            work = work.saturating_add(collector.work);
            if work > 1_000_000 {
                // Exhaustion establishes no variance permissions, including
                // in dependents that have not reached their fixed point.
                for arguments in value.0.values_mut() {
                    arguments.fill(Variance::Invariant);
                }
                break;
            }
            let derived = if collector.unknown {
                vec![Variance::Invariant; collector.slots.len()]
            } else {
                collector.slots
            };
            let arguments = value.0.get_mut(&definition).unwrap();
            let mut changed = false;
            for (argument, found) in arguments.iter_mut().zip(derived) {
                let joined = argument.join(found);
                changed |= *argument != joined;
                *argument = joined;
            }
            if changed {
                pending.extend(dependents.get(&definition).into_iter().flatten().copied());
            }
        }
        value
    }
}

struct Collector<'a> {
    nominal: &'a NominalVariances,
    slots: Vec<Variance>,
    dependencies: BTreeSet<DefKey>,
    unknown: bool,
    work: usize,
}

impl<'a> Collector<'a> {
    fn new(nominal: &'a NominalVariances, count: usize) -> Self {
        Self {
            nominal,
            slots: vec![Variance::Bivariant; count],
            dependencies: BTreeSet::new(),
            unknown: false,
            work: 0,
        }
    }
    fn slot(&mut self, index: u32, variance: Variance) {
        if let Some(slot) = self.slots.get_mut(index as usize) {
            *slot = slot.join(variance);
        } else {
            self.unknown = true;
        }
    }
    fn lifetime(&mut self, lifetime: Lifetime, variance: Variance) {
        match lifetime {
            Lifetime::Generic(index) => self.slot(index, variance),
            Lifetime::Infer(_) | Lifetime::Placeholder(_) | Lifetime::Inferred(_) => {
                self.unknown = true
            }
            _ => {}
        }
    }
    fn argument(&mut self, argument: &GenericArgument, variance: Variance, depth: usize) {
        match argument {
            GenericArgument::Type(ty) => self.ty(ty, variance, depth + 1),
            GenericArgument::Lifetime(lifetime) => self.lifetime(*lifetime, variance),
            GenericArgument::EffectRow(row) => self.row(row, depth + 1),
            GenericArgument::ConstGeneric { index, .. } => self.slot(*index, Variance::Invariant),
            GenericArgument::ConstProjection {
                subject,
                trait_arguments,
                ..
            } => {
                self.ty(subject, Variance::Invariant, depth + 1);
                for argument in trait_arguments {
                    self.argument(argument, Variance::Invariant, depth + 1);
                }
            }
            GenericArgument::ConstInfer { .. } => self.unknown = true,
            GenericArgument::ConstInteger(_)
            | GenericArgument::ConstIntegerExpr(_)
            | GenericArgument::ConstQuantity(_) => {}
        }
    }
    fn row(&mut self, row: &EffectRow, depth: usize) {
        for effect in &row.effects {
            for argument in &effect.arguments {
                self.argument(argument, Variance::Invariant, depth + 1);
            }
        }
        for projection in &row.projections {
            self.ty(&projection.subject, Variance::Invariant, depth + 1);
            for argument in projection
                .trait_arguments
                .iter()
                .chain(&projection.item_arguments)
            {
                self.argument(argument, Variance::Invariant, depth + 1);
            }
        }
        for tail in &row.tails {
            match tail {
                crate::EffectTail::Generic(index) => self.slot(*index, Variance::Invariant),
                crate::EffectTail::Infer(_) => self.unknown = true,
            }
        }
    }
    fn ty(&mut self, ty: &Type, variance: Variance, depth: usize) {
        self.work += 1;
        if depth > 128 || self.work > 100_000 {
            self.unknown = true;
            return;
        }
        match ty {
            Type::Generic(index) => self.slot(*index, variance),
            Type::Nominal {
                definition,
                arguments,
            } => {
                self.dependencies.insert(*definition);
                for (index, argument) in arguments.iter().enumerate() {
                    self.argument(
                        argument,
                        variance.compose(self.nominal.argument(*definition, index)),
                        depth + 1,
                    );
                }
            }
            Type::Reference {
                mutability,
                lifetime,
                referent,
            } => {
                self.lifetime(*lifetime, variance);
                self.ty(
                    referent,
                    variance.compose(if *mutability == crate::Mutability::Unique {
                        Variance::Invariant
                    } else {
                        Variance::Covariant
                    }),
                    depth + 1,
                );
            }
            Type::RawPointer {
                mutability,
                pointee,
            } => self.ty(
                pointee,
                variance.compose(if *mutability == crate::PointerMutability::Mut {
                    Variance::Invariant
                } else {
                    Variance::Covariant
                }),
                depth + 1,
            ),
            Type::Callable {
                contract,
                parameters,
                result,
                effects,
                ..
            } => {
                for (argument, _) in contract.terms() {
                    self.argument(&argument, Variance::Invariant, depth + 1);
                }
                for parameter in parameters {
                    self.ty(
                        parameter,
                        variance.compose(Variance::Contravariant),
                        depth + 1,
                    );
                }
                self.ty(result, variance, depth + 1);
                self.row(effects, depth + 1);
            }
            Type::Projection {
                subject,
                trait_arguments,
                item_arguments,
                ..
            } => {
                self.ty(subject, Variance::Invariant, depth + 1);
                for argument in trait_arguments.iter().chain(item_arguments) {
                    self.argument(argument, Variance::Invariant, depth + 1);
                }
            }
            Type::Tuple(fields) => {
                for field in fields {
                    self.ty(field, variance, depth + 1);
                }
            }
            Type::Array(element) | Type::StaticData { element, .. } => {
                self.ty(element, variance, depth + 1)
            }
            Type::FixedArray { element, length } => {
                self.ty(element, variance, depth + 1);
                self.argument(length, Variance::Invariant, depth + 1);
            }
            Type::ConstGeneric { index, .. } => self.slot(*index, Variance::Invariant),
            Type::Infer(_) | Type::Error => self.unknown = true,
            Type::Unit
            | Type::Never
            | Type::Scalar(_)
            | Type::ConstInteger(_)
            | Type::ConstQuantity(_) => {}
        }
    }
}

impl TraitSolver {
    pub(crate) fn nominal_variances(&self) -> Arc<NominalVariances> {
        Arc::clone(
            self.nominal_variances
                .get_or_init(|| Arc::new(NominalVariances::derive(self))),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn key(name: &str) -> DefKey {
        DefKey(Digest::of_bytes(name.as_bytes()))
    }
    fn nominal(fields: Vec<Type>) -> ElaboratedHeader {
        ElaboratedHeader::Nominal {
            generics: 1,
            generic_kinds: vec![crate::GenericKind::Lifetime],
            layout: ElaboratedNominalLayout::TupleStruct(
                fields
                    .into_iter()
                    .enumerate()
                    .map(|(index, ty)| crate::NominalField {
                        name: index.to_string(),
                        ty,
                        private_authority: None,
                    })
                    .collect(),
            ),
            contract: Default::default(),
            universal_bounds: vec![],
        }
    }
    fn reference() -> Type {
        Type::Reference {
            mutability: crate::Mutability::Shared,
            lifetime: Lifetime::Generic(0),
            referent: Box::new(Type::Unit),
        }
    }
    fn application(name: &str) -> Type {
        Type::Nominal {
            definition: key(name),
            arguments: vec![GenericArgument::Lifetime(Lifetime::Generic(0))],
        }
    }

    #[test]
    fn representation_variance_distinguishes_shared_mutable_callable_and_phantom_positions() {
        let mut signatures = ElaboratedInterface::default();
        let contravariant = Type::Callable {
            contract: Default::default(),
            safety: crate::Safety::Safe,
            lifetime_binders: 0,
            parameters: vec![reference()],
            result: Box::new(Type::Unit),
            effects: EffectRow::empty(),
            invocation: crate::Quantity::ONCE,
        };
        for (name, fields) in [
            ("shared", vec![reference()]),
            ("phantom", vec![]),
            ("contravariant", vec![contravariant.clone()]),
            ("mixed", vec![reference(), contravariant]),
            (
                "mutable",
                vec![Type::Reference {
                    mutability: crate::Mutability::Unique,
                    lifetime: Lifetime::Static,
                    referent: Box::new(reference()),
                }],
            ),
        ] {
            signatures.definitions.insert(key(name), nominal(fields));
        }
        let solver = TraitSolver::new(&signatures);
        let variance = solver.nominal_variances();
        for (name, expected) in [
            ("shared", Variance::Covariant),
            ("phantom", Variance::Bivariant),
            ("contravariant", Variance::Contravariant),
            ("mixed", Variance::Invariant),
            ("mutable", Variance::Invariant),
        ] {
            assert_eq!(variance.argument(key(name), 0), expected, "{name}");
        }
        assert_eq!(
            variance.argument(key("unrepresented-brand"), 0),
            Variance::Invariant
        );
        assert!(Arc::ptr_eq(
            &variance,
            &solver.fresh_query().nominal_variances()
        ));
    }

    #[test]
    fn recursive_nominal_variance_reaches_a_fixed_point_and_snapshots_do_not_change() {
        let mut signatures = ElaboratedInterface::default();
        signatures
            .definitions
            .insert(key("a"), nominal(vec![application("b")]));
        signatures.definitions.insert(
            key("b"),
            nominal(vec![
                reference(),
                Type::RawPointer {
                    mutability: crate::PointerMutability::Const,
                    pointee: Box::new(application("a")),
                },
            ]),
        );
        let original = TraitSolver::new(&signatures);
        assert_eq!(
            original.nominal_variances().argument(key("a"), 0),
            Variance::Covariant
        );
        signatures.definitions.insert(
            key("b"),
            nominal(vec![Type::RawPointer {
                mutability: crate::PointerMutability::Mut,
                pointee: Box::new(reference()),
            }]),
        );
        assert_eq!(
            TraitSolver::new(&signatures)
                .nominal_variances()
                .argument(key("a"), 0),
            Variance::Invariant
        );
        assert_eq!(
            original.nominal_variances().argument(key("a"), 0),
            Variance::Covariant
        );
    }

    #[test]
    fn missing_layout_and_unresolved_projection_have_no_variance_permission() {
        let mut signatures = ElaboratedInterface::default();
        signatures.definitions.insert(
            key("opaque"),
            ElaboratedHeader::Nominal {
                generics: 1,
                generic_kinds: vec![crate::GenericKind::Lifetime],
                layout: ElaboratedNominalLayout::Opaque,
                contract: Default::default(),
                universal_bounds: vec![],
            },
        );
        signatures
            .definitions
            .insert(key("wrapper"), nominal(vec![application("opaque")]));
        assert_eq!(
            TraitSolver::new(&signatures)
                .nominal_variances()
                .argument(key("wrapper"), 0),
            Variance::Invariant
        );
        let projection = Type::Projection {
            subject: Box::new(reference()),
            trait_definition: key("missing-trait"),
            trait_arguments: vec![],
            name: "Item".into(),
            item_generic_kinds: vec![],
            item_arguments: vec![],
        };
        let empty = NominalVariances::default();
        let mut collector = Collector::new(&empty, 1);
        collector.ty(&projection, Variance::Covariant, 0);
        assert_eq!(collector.slots, vec![Variance::Invariant]);
    }
}
