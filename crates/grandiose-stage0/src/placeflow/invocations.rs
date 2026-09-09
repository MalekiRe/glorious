//! Storage lookup/application adapter for the shared invocation relation.
use super::*;
use crate::resident_invocations::{CapturedInputs, Inputs, Operand};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd)]
pub(super) struct Value {
    core: Option<CoreId>,
    owners: BTreeSet<String>,
    path: Vec<u32>,
    fallback_regions: BTreeSet<regions::Region>,
    fallback_loans: BTreeSet<ProjectionLoan>,
}

impl Value {
    fn core(id: CoreId) -> Self {
        Self {
            core: Some(id),
            owners: BTreeSet::new(),
            path: vec![],
            fallback_regions: BTreeSet::new(),
            fallback_loans: BTreeSet::new(),
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
                        fallback_loans: if missing {
                            fallback_loans.clone()
                        } else {
                            BTreeSet::new()
                        },
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

impl Analyzer<'_> {
    pub(super) fn record_invocation_stores(
        &mut self,
        callee: CoreId,
        owner: Option<&str>,
        arguments: &[CoreId],
        call: CoreId,
    ) {
        let Some(signatures) = self.signatures else {
            return;
        };
        let callee_value = match owner {
            Some(owner) => Value {
                core: None,
                owners: BTreeSet::from([owner.to_owned()]),
                path: vec![],
                fallback_regions: BTreeSet::new(),
                fallback_loans: BTreeSet::new(),
            },
            None => Value::core(callee),
        };
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

    fn invocation_origins(
        &self,
        value: &Value,
    ) -> (BTreeSet<regions::Region>, BTreeSet<ProjectionLoan>) {
        if let Some(core) = value.core {
            return (
                self.logical_regions_from_value_path(core, &value.path),
                self.reference_loans_from_value_path(core, &value.path),
            );
        }
        let mut regions = value.fallback_regions.clone();
        let mut loans = value.fallback_loans.clone();
        for owner in &value.owners {
            let key = projection_key(owner, &value.path);
            regions.extend(self.logical_origin_regions(&key));
            loans.extend(self.origin_loans(&key));
        }
        (regions, loans)
    }

    fn invocation_footprint(
        &self,
        value: &Value,
    ) -> (BTreeSet<regions::Region>, BTreeSet<ProjectionLoan>) {
        let owners = self.invocation_owners(value);
        let mut regions = value.fallback_regions.clone();
        let mut loans = value.fallback_loans.clone();
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
                .flat_map(|owner| self.origin_loans(&projection_key(owner, &value.path[..deref])))
                .map(|loan| {
                    let mut fields = loan.place.fields;
                    fields.extend_from_slice(&value.path[deref + 1..]);
                    projection_key(&loan.place.root, &fields)
                })
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
                .reference_loans_from_value_path(value, &path[..deref])
                .into_iter()
                .map(|loan| {
                    let mut fields = loan.place.fields;
                    fields.extend_from_slice(&path[deref + 1..]);
                    projection_key(&loan.place.root, &fields)
                })
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
        format!(
            "<capture-{:?}>",
            crate::Digest::of_bytes(&crate::types::canonical_type_encoding(ty))
        )
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
            let loans = self.reference_loans_from_value_path(argument, &source);
            self.reference_origins
                .entry(key.clone())
                .or_default()
                .extend(loans);
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
            for (key, loans) in references {
                self.reference_origins.entry(key).or_default().extend(loans);
            }
            for (key, regions) in logical {
                self.logical.origins.entry(key).or_default().extend(regions);
            }
        }
    }
}
