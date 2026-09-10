//! Storage lookup/application adapter for the shared invocation relation.
use super::*;
use crate::resident_invocations::{CapturedInputs, Inputs, Operand};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct Value {
    core: Option<CoreId>,
    owners: BTreeSet<String>,
    path: Vec<u32>,
    fallback_regions: BTreeSet<regions::Region>,
    fallback_origins: Option<ReferenceOrigins>,
}

impl Value {
    pub(super) fn core(id: CoreId) -> Self {
        Self {
            core: Some(id),
            owners: BTreeSet::new(),
            path: vec![],
            fallback_regions: BTreeSet::new(),
            fallback_origins: None,
        }
    }

    pub(super) fn callable(id: CoreId, owner: Option<&str>) -> Self {
        match owner {
            Some(owner) => Self {
                core: None,
                owners: BTreeSet::from([owner.to_owned()]),
                path: vec![],
                fallback_regions: BTreeSet::new(),
                fallback_origins: None,
            },
            None => Self::core(id),
        }
    }
}

impl Inputs for Analyzer<'_> {
    type Value = Value;

    fn project(&self, value: &Value, path: &[u32]) -> Option<Value> {
        let mut value = value.clone();
        value.path.extend_from_slice(path);
        Some(value)
    }

    fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> {
        let Type::Callable { contract, .. } = &callable.ty else {
            unreachable!("typed callable operand");
        };
        let owners = self.invocation_owners(&callable.value);
        let mut types = contract
            .open(|_| None)
            .map(|contract| contract.captures)
            .unwrap_or_else(|| contract.captures.clone());
        for ty in self.known_capture_types(&owners) {
            if !types.contains(&ty) {
                types.push(ty);
            }
        }
        let unresolved = types.is_empty() && contract.environment.is_none();
        let (fallback_regions, fallback_loans) = self.invocation_footprint(&callable.value);
        let operands = types
            .into_iter()
            .map(|ty| {
                let roots = owners
                    .iter()
                    .map(|owner| Self::capture_origin_key(owner, &ty))
                    .collect::<BTreeSet<_>>();
                let missing =
                    roots.is_empty()
                        || roots.iter().any(|root| {
                            !self.reference_origins.contains_key(root)
                                && !self.logical.origins.keys().any(|key| {
                                    key == root || key.starts_with(&(root.clone() + "."))
                                })
                        });
                Operand {
                    ty,
                    value: Value {
                        core: None,
                        owners: roots,
                        path: vec![],
                        fallback_regions: if missing {
                            fallback_regions.clone()
                        } else {
                            BTreeSet::new()
                        },
                        fallback_origins: missing.then(|| ReferenceOrigins::unknown(fallback_loans.clone())),
                    },
                }
            })
            .collect();
        CapturedInputs {
            operands,
            unresolved,
        }
    }
}

impl crate::callable_control::PayloadInputs for Analyzer<'_> {
    type Value = Value;
    fn project(&self, value: &Value, path: &[u32]) -> Option<Value> { Inputs::project(self, value, path) }
    fn captures(&self, callable: &Operand<Value>) -> CapturedInputs<Value> { Inputs::captures(self, callable) }
    fn reborrow(&self, reference: &Value, fields: &[u32]) -> Option<Value> {
        let (regions, origins) = self.invocation_reference_origins(reference);
        Some(Value { core: None, owners: BTreeSet::new(), path: vec![],
            fallback_regions: regions,
            fallback_origins: Some(origins.project_referent(fields)),
        })
    }
    fn borrow_capture(&self, receiver: &Value, projection: crate::resident_invocations::CaptureProjection, unique: bool) -> Option<Value> {
        let (regions, origins) = self.invocation_reference_origins(receiver);
        if origins.loans.is_empty() || (unique && origins.loans.iter().any(|loan| !loan.unique)) { return None; }
        let targets = origins.targets.clone();
        Some(Value { core: None, owners: BTreeSet::new(), path: vec![], fallback_regions: regions,
            fallback_origins: Some(origins.map(|mut loan| {
                if targets.as_ref().is_some_and(|targets| targets.contains(&loan)) {
                    loan.capture_path.push(projection.clone());
                }
                loan.unique = unique;
                loan
            })),
        })
    }
}

impl crate::callable_control::ReferenceInputs for Analyzer<'_> {
    fn reference_known(&self, value: &Value) -> bool {
        let (regions, origins) = self.invocation_reference_origins(value);
        !origins.is_known_empty() && (!regions.is_empty() || !origins.loans.is_empty()
            || value.core.is_some_and(|core| self.external_reference_path(core))
        )
    }
    fn reference_empty(&self, value: &Value) -> bool { self.invocation_reference_origins(value).1.is_known_empty() }
}

impl Analyzer<'_> {
    pub(super) fn record_invocation_stores(
        &mut self,
        callee: CoreId,
        owner: Option<&str>,
        arguments: &[CoreId],
        call: CoreId,
    ) {
        if self.continuations.invocation(call).is_some_and(|control| control.storage_read_only()) { return; }
        let Some(signatures) = self.signatures else {
            return;
        };
        let callee_value = Value::callable(callee, owner);
        let arguments = arguments
            .iter()
            .map(|argument| Operand {
                ty: self.body.expression(*argument).ty.clone(),
                value: Value::core(*argument),
            })
            .collect::<Vec<_>>();
        let relations = crate::resident_invocations::derive(
            signatures,
            self.body.expression(callee),
            callee_value,
            &arguments,
            self,
        );
        // Resolve physical-write sources and destinations against the
        // pre-invocation snapshot, before an earlier write can alter them.
        let writes = relations.reference_writes.into_iter().map(|write| {
            let (_, destination) = self.invocation_reference_origins(&write.destination);
            let sources = write.sources.iter().map(|source| self.invocation_reference_origins(source)).collect::<Vec<_>>();
            (write, destination, sources)
        }).collect::<Vec<_>>();
        for (write, destination, sources) in writes {
            let span = self.body.expression(call).span;
            if write.unresolved_destination {
                self.error(span, "G5023", "invocation write has an unresolved destination projection".into());
                continue;
            }
            if write.unresolved || sources.iter().any(|(_, origins)| origins.loans.is_empty() && !origins.is_known_empty()) {
                self.error(span, "G5023", "invocation write has unresolved source provenance".into());
            }
            let Type::Reference { mutability, .. } = &write.fields.ty else { unreachable!("a typed reference write"); };
            let mut loans = BTreeSet::from([ProjectionLoan::external(call, &write.fields.value, *mutability)]);
            let mut regions = BTreeSet::new();
            for (incoming, source) in sources {
                regions.extend(incoming);
                loans.extend(source.loans.into_iter().map(|mut loan| {
                    // A shared handle copy retains its backing storage,
                    // without borrowing the replaceable source handle slot.
                    if !loan.unique { loan.owner = None; }
                    loan
                }));
            }
            if let Some(targets) = destination.targets {
                for target in targets.into_iter().filter(|target| !target.indirect && !target.external) {
                    let key = target.resident_key(&write.fields.value);
                    self.invalidate_reference_empty_ancestors(&key);
                    for loan in &loans { self.install_reference_alias(&key, loan.clone(), call); }
                    self.logical.origins.entry(key.clone()).or_default().extend(regions.iter().cloned());
                    let stored = self.reference_origins.entry(key).or_default();
                    stored.targets = None;
                    stored.reference_free = false;
                }
            } else if destination.loans.is_empty() || destination.loans.iter().any(|loan| !loan.indirect && !loan.external) {
                self.error(span, "G5023", "invocation write has unresolved local referent storage".into());
            }
        }
        let mut changed = false;
        for store in relations.stores {
            if store.source_is_callable {
                let sources = self.invocation_owners(&store.source);
                for destination in self.invocation_owners(&store.destination) {
                    self.forward_capture_origins(&destination, &sources);
                }
            }
            let (mut regions, _) = self.invocation_origins(&store.destination);
            let Some(first) = regions.first().cloned() else {
                continue;
            };
            let (source_regions, loans) = self.invocation_origins(&store.source);
            regions.extend(source_regions);
            self.logical.regions.connect(&regions);
            self.logical.regions.insert(
                first,
                loans
                    .into_iter()
                    .map(|loan| ProjectionLoan {
                        owner: None,
                        ..loan
                    })
                    .collect(),
                |loans, incoming| loans.extend(incoming),
            );
            changed = true;
        }
        // Unresolved environments retain the existing conservative whole
        // footprint relation. They are not evidence of a stateless callable.
        for callable in relations.unresolved {
            let (regions, loans) = self.invocation_footprint(&callable.value);
            let Some(first) = regions.first().cloned() else {
                continue;
            };
            self.logical.regions.connect(&regions);
            self.logical.regions.insert(
                first,
                loans
                    .into_iter()
                    .map(|loan| ProjectionLoan {
                        owner: None,
                        ..loan
                    })
                    .collect(),
                |loans, incoming| loans.extend(incoming),
            );
            changed = true;
        }
        if changed {
            self.refresh_logical_loans(call);
        }
    }

    /// Ordinary returns already have a declared provenance contract. Add
    /// known body-derived inputs without treating missing projections as
    /// either a new rejection or evidence that the result has no origins.
    pub(super) fn record_known_payload_origins(
        &mut self,
        owner: &str,
        payload: crate::callable_control::ResolvedPayload<Value>,
        source: CoreId,
    ) {
        self.record_payload_origins_at(owner, payload, source, Some(&[]), true);
    }

    pub(super) fn record_payload_origins(
        &mut self,
        owner: &str,
        payload: crate::callable_control::ResolvedPayload<Value>,
        source: CoreId,
    ) {
        self.record_payload_origins_at(owner, payload, source, None, true);
    }

    fn record_payload_origins_at(
        &mut self,
        owner: &str,
        payload: crate::callable_control::ResolvedPayload<Value>,
        source: CoreId,
        // Some denotes a normal result and retains its exact result prefix
        // for the existing checked unique-reference partition relation.
        result_path: Option<&[u32]>,
        partition: bool,
    ) {
        use crate::callable_control::ResolvedPayload;
        match payload {
            ResolvedPayload::Aggregate(fields) | ResolvedPayload::Variant(fields) => {
                if fields.is_empty() { self.merge_reference_snapshot(owner.to_owned(), ReferenceOrigins::empty()); }
                for (index, field) in fields.into_iter().enumerate() {
                    let path = result_path.map(|path| path.iter().copied().chain([index as u32]).collect::<Vec<_>>());
                    self.record_payload_origins_at(
                        &projection_key(owner, &[index as u32]),
                        field,
                        source,
                        path.as_deref(),
                        partition,
                    );
                }
            }
            ResolvedPayload::Callable { captures, .. } => {
                for (ty, capture) in captures {
                    self.capture_types.insert(Self::capture_type_key(&ty), ty.clone());
                    let root = Self::capture_origin_key(owner, &ty);
                    self.record_payload_origins_at(&root, capture, source, result_path, false);
                    self.reference_origins.entry(root).or_default();
                }
            }
            ResolvedPayload::Inputs { ty, values } => {
                let Some(signatures) = self.signatures else {
                    return;
                };
                let mut leaves = vec![];
                let _ =
                    crate::core::reference_leaf_paths(signatures, &ty, &mut vec![], &mut leaves);
                leaves.extend(regions::callable_paths(signatures, &ty, false));
                for (path, ty) in leaves {
                    let destination = projection_key(owner, &path);
                    for value in &values {
                        let Some(projected) = <Self as Inputs>::project(self, value, &path) else {
                            continue;
                        };
                        if matches!(ty, Type::Callable { .. }) {
                            let sources = self.invocation_owners(&projected);
                            self.forward_capture_origins(&destination, &sources);
                        }
                        let (regions, origins) = self.invocation_reference_origins(&projected);
                        self.logical
                            .origins
                            .entry(destination.clone())
                            .or_default()
                            .extend(regions);
                        let origins = origins.map(|loan| {
                            if let Some(prefix) = result_path.filter(|_| partition) {
                                let fields = prefix.iter().chain(&path).copied().collect::<Vec<_>>();
                                self.partition_call_result(source, &fields, loan)
                            } else { loan }
                        });
                        let mut combined = self.reference_origins.get(&destination).cloned();
                        // A second input is another possible value, not an
                        // opportunity to replace the first input's coverage.
                        let origins = match &mut combined {
                            Some(combined) => { combined.join(origins); combined.clone() }
                            None => origins,
                        };
                        self.install_reference_snapshot(&destination, origins, source);
                    }
                }
            }
            ResolvedPayload::Unknown(ty) => {
                let empty = ElaboratedInterface::default();
                if crate::core::tail::tail_owned_type(self.signatures.unwrap_or(&empty), &ty, &mut vec![]) {
                    self.merge_reference_snapshot(owner.to_owned(), ReferenceOrigins::empty());
                } else if result_path.is_none() {
                    self.error(
                        self.body.expression(source).span,
                        "G5023",
                        "label payload has no frozen input or frame-independent provenance".into(),
                    );
                }
            }
        }
    }

    fn invocation_origins(
        &self,
        value: &Value,
    ) -> (BTreeSet<regions::Region>, BTreeSet<ProjectionLoan>) {
        let (regions, origins) = self.invocation_reference_origins(value);
        (regions, origins.loans)
    }

    fn invocation_reference_origins(
        &self,
        value: &Value,
    ) -> (BTreeSet<regions::Region>, ReferenceOrigins) {
        if let Some(core) = value.core {
            return (
                self.logical_regions_from_value_path(core, &value.path),
                self.reference_origins_from_value_path(core, &value.path),
            );
        }
        let mut regions = value.fallback_regions.clone();
        let mut origins = value.fallback_origins.clone();
        if let Some(fallback) = origins.as_mut() {
            if value.path.first() == Some(&crate::core::REFERENCE_PATH_DEREF) {
                *fallback = self.reference_resident_origins(fallback.clone(), &value.path[1..], false);
            } else if !value.path.is_empty() {
                fallback.targets = None;
            }
        }
        for owner in &value.owners {
            let key = projection_key(owner, &value.path);
            regions.extend(self.logical_origin_regions(&key));
            let incoming = if let Some(deref) = value.path.iter().position(|field|
                *field == crate::core::REFERENCE_PATH_DEREF) {
                self.reference_resident_origins(self.origin_snapshot(&projection_key(owner, &value.path[..deref])),
                    &value.path[deref + 1..], false)
            } else { self.origin_snapshot(&key) };
            match &mut origins {
                Some(origins) => origins.join(incoming),
                None => origins = Some(incoming),
            }
        }
        (regions, origins.unwrap_or_default())
    }

    fn invocation_footprint(
        &self,
        value: &Value,
    ) -> (BTreeSet<regions::Region>, BTreeSet<ProjectionLoan>) {
        let owners = self.invocation_owners(value);
        let mut regions = value.fallback_regions.clone();
        let mut loans = value.fallback_origins.as_ref().map(|origins| origins.loans.clone()).unwrap_or_default();
        for owner in &owners {
            regions.extend(
                self.logical
                    .origins
                    .iter()
                    .filter(|(key, _)| *key == owner || key.starts_with(&(owner.clone() + ".")))
                    .flat_map(|(_, regions)| regions.iter().cloned()),
            );
            loans.extend(self.captured_origin_loans(owner));
        }
        if owners.is_empty() {
            let (more_regions, more_loans) = self.invocation_origins(value);
            regions.extend(more_regions);
            loans.extend(more_loans);
        }
        (regions, loans)
    }

    fn invocation_owners(&self, value: &Value) -> BTreeSet<String> {
        if let Some(core) = value.core {
            return self.callable_origin_owners(core, &value.path);
        }
        if let Some(deref) = value
            .path
            .iter()
            .position(|field| *field == crate::core::REFERENCE_PATH_DEREF)
        {
            return value
                .owners
                .iter()
                .flat_map(|owner| self.origin_snapshot(&projection_key(owner, &value.path[..deref])).targets.into_iter().flatten())
                .map(|loan| loan.resident_key(&value.path[deref + 1..]))
                .collect();
        }
        value
            .owners
            .iter()
            .map(|owner| projection_key(owner, &value.path))
            .collect()
    }

    pub(super) fn callable_origin_owners(&self, value: CoreId, path: &[u32]) -> BTreeSet<String> {
        if let Some(deref) = path
            .iter()
            .position(|field| *field == crate::core::REFERENCE_PATH_DEREF)
        {
            return self
                .reference_origins_from_value_path(value, &path[..deref])
                .targets.into_iter().flatten()
                .map(|loan| loan.resident_key(&path[deref + 1..]))
                .collect();
        }
        let owner = if self.pending_results.contains(&value) {
            Some(Self::result_owner(value))
        } else {
            self.reference_origin_key(value)
        };
        owner
            .into_iter()
            .map(|owner| projection_key(&owner, path))
            .collect()
    }

    pub(super) fn capture_type_key(ty: &Type) -> String {
        crate::resident_invocations::CaptureProjection::new(ty, &[]).origin_suffix()
    }

    fn known_capture_types(&self, owners: &BTreeSet<String>) -> Vec<Type> {
        let mut types = BTreeMap::new();
        for owner in owners {
            let prefix = owner.clone() + ".";
            for key in self
                .reference_origins
                .range(prefix.clone()..)
                .map(|(key, _)| key)
                .take_while(|key| key.starts_with(&prefix))
                .chain(
                    self.logical
                        .origins
                        .range(prefix.clone()..)
                        .map(|(key, _)| key)
                        .take_while(|key| key.starts_with(&prefix)),
                )
            {
                let suffix = key[prefix.len()..]
                    .split('.')
                    .next()
                    .expect("capture suffix");
                if let Some(ty) = self.capture_types.get(suffix) {
                    types.insert(suffix.to_owned(), ty.clone());
                }
            }
        }
        types.into_values().collect()
    }

    pub(super) fn record_factory_capture_origins(
        &mut self,
        owner: &str,
        argument: CoreId,
        path: &[u32],
        ty: &Type,
    ) {
        let Some(signatures) = self.signatures else {
            return;
        };
        self.capture_types
            .insert(Self::capture_type_key(ty), ty.clone());
        let root = Self::capture_origin_key(owner, ty);
        self.reference_origins.entry(root.clone()).or_default();
        let mut leaves = vec![];
        let _ = crate::core::input_reference_leaf_paths(signatures, ty, &mut leaves);
        for (fields, _) in leaves {
            let source = path.iter().chain(&fields).copied().collect::<Vec<_>>();
            let key = projection_key(&root, &fields);
            let origins = ReferenceOrigins::unknown(self.reference_loans_from_value_path(argument, &source));
            self.merge_reference_snapshot(key.clone(), origins);
            let regions = self.logical_regions_from_value_path(argument, &source);
            if !regions.is_empty() {
                self.logical.origins.entry(key).or_default().extend(regions);
            }
        }
    }

    pub(super) fn forward_capture_origins(&mut self, owner: &str, sources: &BTreeSet<String>) {
        for source in sources {
            let prefix = source.clone() + ".";
            let references = self
                .reference_origins
                .range(prefix.clone()..)
                .take_while(|(key, _)| key.starts_with(&prefix))
                .map(|(key, loans)| (format!("{owner}{}", &key[source.len()..]), loans.clone()))
                .collect::<Vec<_>>();
            let logical = self
                .logical
                .origins
                .range(prefix.clone()..)
                .take_while(|(key, _)| key.starts_with(&prefix))
                .map(|(key, regions)| (format!("{owner}{}", &key[source.len()..]), regions.clone()))
                .collect::<Vec<_>>();
            for (key, origins) in references {
                self.merge_reference_snapshot(key, origins);
            }
            for (key, regions) in logical {
                self.logical.origins.entry(key).or_default().extend(regions);
            }
        }
    }
}
