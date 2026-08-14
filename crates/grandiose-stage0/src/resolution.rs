//! Namespace-aware resolution and reference indexing.
//!
//! Global interfaces and body-local scope use the same stable `DefKey` target.
//! This keeps compiler checking, definition/references, semantic highlighting,
//! and rename on one resolution product rather than independent approximations.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    header::ParsedHeader,
    identity::{DefKey, ModuleKey},
    interface::{DefinitionNamespace, PackageInterface},
    source::Span,
    types::GenericKind,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolutionState {
    Resolved(DefKey),
    Unresolved,
    Ambiguous(Vec<DefKey>),
    Inaccessible(Vec<DefKey>),
    Recovered,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum OccurrenceRole {
    Definition,
    Read,
    Write,
    Move,
    TypeUse,
    Import,
    Operator,
    LabelTransfer,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Occurrence {
    pub span: Span,
    pub namespace: DefinitionNamespace,
    pub role: OccurrenceRole,
    pub state: ResolutionState,
}

/// Deterministic module-level lookup table. A duplicate key remains an
/// ambiguity instead of silently selecting source order; interface collection
/// reports the original duplicate diagnostic and the resolver preserves it for
/// recovered IDE requests.
#[derive(Clone, Debug, Default)]
pub struct DefinitionIndex {
    entries: BTreeMap<(DefinitionNamespace, String), Vec<IndexedDefinition>>,
    qualified: BTreeMap<(DefinitionNamespace, ModuleKey, String), Vec<IndexedDefinition>>,
    modules: BTreeMap<ModuleKey, ()>,
    imports: BTreeMap<ModuleKey, Vec<ImportBinding>>,
    type_generic_arities: BTreeMap<DefKey, u32>,
    type_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
    trait_generic_arities: BTreeMap<DefKey, u32>,
    trait_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
    associated_type_generic_kinds: BTreeMap<(DefKey, String), Vec<GenericKind>>,
    effect_generic_arities: BTreeMap<DefKey, u32>,
    effect_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct IndexedDefinition {
    key: DefKey,
    module: ModuleKey,
    public: bool,
}

/// An explicit source-level import binding, retained independently of body
/// scopes so diagnostics, tooling, and all semantic namespaces consult the
/// same interface-owned fact.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ImportBinding {
    pub path: Vec<String>,
    pub alias: String,
    pub module: ModuleKey,
    pub public: bool,
    pub span: Span,
}

impl DefinitionIndex {
    pub fn from_interface(interface: &PackageInterface) -> Self {
        let mut index = Self::default();
        index.extend(interface);
        index.canonicalize();
        index
    }

    pub fn from_interfaces<'a>(interfaces: impl IntoIterator<Item = &'a PackageInterface>) -> Self {
        let mut index = Self::default();
        for interface in interfaces {
            index.extend(interface);
        }
        index.canonicalize();
        index
    }

    fn extend(&mut self, interface: &PackageInterface) {
        self.modules.insert(interface.module.clone(), ());
        for definition in &interface.definitions {
            if definition.namespace == Some(DefinitionNamespace::Type) {
                let (arity, kinds) = match &definition.syntax.header {
                    ParsedHeader::Nominal { generics, .. }
                    | ParsedHeader::TypeAlias { generics, .. } => {
                        (generics.len() as u32, generics.kinds())
                    }
                    _ => (0, vec![]),
                };
                self.type_generic_arities.insert(definition.key, arity);
                self.type_generic_kinds.insert(definition.key, kinds);
            }
            match &definition.syntax.header {
                ParsedHeader::Trait(header) => {
                    self.trait_generic_arities
                        .insert(definition.key, header.generics.len() as u32);
                    self.trait_generic_kinds
                        .insert(definition.key, header.generics.kinds());
                    for item in &header.associated_types {
                        self.associated_type_generic_kinds
                            .insert((definition.key, item.name.clone()), item.generics.kinds());
                    }
                }
                ParsedHeader::Effect(header) => {
                    self.effect_generic_arities
                        .insert(definition.key, header.generics.len() as u32);
                    self.effect_generic_kinds
                        .insert(definition.key, header.generics.kinds());
                }
                _ => {}
            }
            if let ParsedHeader::Import(import) = &definition.syntax.header {
                for binding in &import.bindings {
                    let alias = binding
                        .alias
                        .clone()
                        .or_else(|| binding.path.last().cloned())
                        .unwrap_or_else(|| "<error>".into());
                    self.imports
                        .entry(definition.module.clone())
                        .or_default()
                        .push(ImportBinding {
                            path: binding.path.clone(),
                            alias,
                            module: definition.module.clone(),
                            public: definition.public,
                            span: definition.span,
                        });
                }
            }
            if let (Some(namespace), Some(name)) = (definition.namespace, &definition.name) {
                let entry = IndexedDefinition {
                    key: definition.key,
                    module: definition.module.clone(),
                    public: definition.public,
                };
                self.entries
                    .entry((namespace, name.clone()))
                    .or_default()
                    .push(entry.clone());
                self.qualified
                    .entry((namespace, definition.module.clone(), name.clone()))
                    .or_default()
                    .push(entry);
            }
        }
    }

    fn canonicalize(&mut self) {
        for entries in self.entries.values_mut() {
            entries.sort();
            entries.dedup();
        }
        for entries in self.qualified.values_mut() {
            entries.sort();
            entries.dedup();
        }
        for imports in self.imports.values_mut() {
            imports.sort();
            imports.dedup();
        }
    }

    pub fn resolve(&self, namespace: DefinitionNamespace, name: &str) -> ResolutionState {
        self.classify(self.entries.get(&(namespace, name.to_owned())), None)
    }

    /// Binder arity is an interface fact, not a property recovered from a
    /// body. Header elaboration uses it to reject ill-kinded nominal and alias
    /// applications before any body reaches Typed Core.
    pub fn type_generic_arity(&self, definition: DefKey) -> Option<u32> {
        self.type_generic_arities.get(&definition).copied()
    }

    /// Source-slot kinds for a nominal or alias declaration. This is the
    /// authority future generic-argument elaboration uses to keep structural
    /// constants out of the type-substitution namespace.
    pub fn type_generic_kinds(&self, definition: DefKey) -> Option<&[GenericKind]> {
        self.type_generic_kinds.get(&definition).map(Vec::as_slice)
    }

    pub fn trait_generic_arity(&self, definition: DefKey) -> Option<u32> {
        self.trait_generic_arities.get(&definition).copied()
    }

    pub fn trait_generic_kinds(&self, definition: DefKey) -> Option<&[GenericKind]> {
        self.trait_generic_kinds.get(&definition).map(Vec::as_slice)
    }

    /// Source-slot kinds of an associated item selected through a particular
    /// trait.  Projection elaboration uses this rather than treating an item
    /// argument as an ordinary type before the trait contract is known.
    pub fn associated_type_generic_kinds(
        &self,
        trait_definition: DefKey,
        name: &str,
    ) -> Option<&[GenericKind]> {
        self.associated_type_generic_kinds
            .get(&(trait_definition, name.to_owned()))
            .map(Vec::as_slice)
    }

    pub fn effect_generic_arity(&self, definition: DefKey) -> Option<u32> {
        self.effect_generic_arities.get(&definition).copied()
    }

    pub fn effect_generic_kinds(&self, definition: DefKey) -> Option<&[GenericKind]> {
        self.effect_generic_kinds
            .get(&definition)
            .map(Vec::as_slice)
    }

    /// Resolve a source path from its owning lexical module.  The package
    /// graph is the authority for every module segment: spelling a path can
    /// never bypass an absent module or select a declaration from another
    /// module merely because its final identifier matches.
    pub fn resolve_path(
        &self,
        namespace: DefinitionNamespace,
        owner: &ModuleKey,
        path: &[String],
    ) -> ResolutionState {
        let Some(name) = path.last() else {
            return ResolutionState::Unresolved;
        };
        let module = if path.len() == 1 {
            return self.resolve_member(namespace, owner, name, owner, false, &mut BTreeSet::new());
        } else {
            let Some(module) = self.lexical_module(owner, &path[..path.len() - 1]) else {
                return ResolutionState::Unresolved;
            };
            module
        };
        self.resolve_member(namespace, &module, name, owner, true, &mut BTreeSet::new())
    }

    fn resolve_member(
        &self,
        namespace: DefinitionNamespace,
        module: &ModuleKey,
        name: &str,
        requester: &ModuleKey,
        require_public_import: bool,
        visited: &mut BTreeSet<(DefinitionNamespace, ModuleKey, String)>,
    ) -> ResolutionState {
        let local = self.classify(
            self.qualified
                .get(&(namespace, module.clone(), name.to_owned())),
            Some(requester),
        );
        if !matches!(local, ResolutionState::Unresolved) {
            return local;
        }
        let cycle_key = (namespace, module.clone(), name.to_owned());
        if !visited.insert(cycle_key.clone()) {
            return ResolutionState::Unresolved;
        }
        let result = self.resolve_import(namespace, module, name, require_public_import, visited);
        visited.remove(&cycle_key);
        result
    }

    fn resolve_import(
        &self,
        namespace: DefinitionNamespace,
        owner: &ModuleKey,
        alias: &str,
        require_public: bool,
        visited: &mut BTreeSet<(DefinitionNamespace, ModuleKey, String)>,
    ) -> ResolutionState {
        let Some(imports) = self.imports.get(owner) else {
            return ResolutionState::Unresolved;
        };
        let mut resolved = vec![];
        let mut ambiguous = vec![];
        let mut inaccessible = vec![];
        for import in imports
            .iter()
            .filter(|import| import.alias == alias && (!require_public || import.public))
        {
            match self.resolve_direct_path(namespace, owner, &import.path, visited) {
                ResolutionState::Resolved(definition) => resolved.push(definition),
                ResolutionState::Ambiguous(definitions) => ambiguous.extend(definitions),
                ResolutionState::Inaccessible(definitions) => inaccessible.extend(definitions),
                ResolutionState::Unresolved | ResolutionState::Recovered => {}
            }
        }
        canonicalize_keys(&mut resolved);
        canonicalize_keys(&mut ambiguous);
        canonicalize_keys(&mut inaccessible);
        if resolved.len() == 1 {
            ResolutionState::Resolved(resolved[0])
        } else if resolved.len() > 1 {
            ResolutionState::Ambiguous(resolved)
        } else if !ambiguous.is_empty() {
            ResolutionState::Ambiguous(ambiguous)
        } else if !inaccessible.is_empty() {
            ResolutionState::Inaccessible(inaccessible)
        } else {
            ResolutionState::Unresolved
        }
    }

    fn resolve_direct_path(
        &self,
        namespace: DefinitionNamespace,
        owner: &ModuleKey,
        path: &[String],
        visited: &mut BTreeSet<(DefinitionNamespace, ModuleKey, String)>,
    ) -> ResolutionState {
        let Some(name) = path.last() else {
            return ResolutionState::Unresolved;
        };
        let module = if path.len() == 1 {
            owner.clone()
        } else {
            let Some(module) = self.lexical_module(owner, &path[..path.len() - 1]) else {
                return ResolutionState::Unresolved;
            };
            module
        };
        self.resolve_member(namespace, &module, name, owner, true, visited)
    }

    fn classify(
        &self,
        entries: Option<&Vec<IndexedDefinition>>,
        owner: Option<&ModuleKey>,
    ) -> ResolutionState {
        let Some(entries) = entries else {
            return ResolutionState::Unresolved;
        };
        let visible = entries
            .iter()
            .filter(|entry| owner.is_none_or(|owner| entry.public || entry.module == *owner))
            .map(|entry| entry.key)
            .collect::<Vec<_>>();
        if visible.is_empty() {
            return ResolutionState::Inaccessible(entries.iter().map(|entry| entry.key).collect());
        }
        if visible.len() == 1 {
            ResolutionState::Resolved(visible[0])
        } else {
            ResolutionState::Ambiguous(visible)
        }
    }

    fn lexical_module(&self, owner: &ModuleKey, segments: &[String]) -> Option<ModuleKey> {
        let (first, rest) = segments.split_first()?;
        if first == "crate" {
            return self.module_key(owner, "crate", rest);
        }
        if first == "self" {
            return self.module_key(owner, &owner.path, rest);
        }
        if first == "super" {
            let mut base = owner.path.clone();
            let mut remaining = segments;
            while matches!(remaining.first(), Some(segment) if segment == "super") {
                base = parent_module_path(&base)?;
                remaining = &remaining[1..];
            }
            return self.module_key(owner, &base, remaining);
        }

        // Ordinary qualified paths are lexical.  Prefer the nearest enclosing
        // module that actually owns the requested child; this supports a
        // nested module referring to a sibling while keeping resolution
        // deterministic in the presence of similarly named descendants.
        let mut base = owner.path.clone();
        loop {
            if let Some(module) = self.module_key(owner, &base, segments) {
                return Some(module);
            }
            base = parent_module_path(&base)?;
        }
    }

    fn module_key(&self, owner: &ModuleKey, base: &str, suffix: &[String]) -> Option<ModuleKey> {
        let path = if suffix.is_empty() {
            base.to_owned()
        } else {
            format!("{base}::{}", suffix.join("::"))
        };
        let module = ModuleKey {
            package: owner.package.clone(),
            path,
        };
        self.modules.contains_key(&module).then_some(module)
    }
}

fn parent_module_path(path: &str) -> Option<String> {
    path.rsplit_once("::").map(|(parent, _)| parent.to_owned())
}

fn canonicalize_keys(keys: &mut Vec<DefKey>) {
    keys.sort();
    keys.dedup();
}

/// Journaled lexical scopes with deterministic shadowing. Parsing and body
/// elaboration create a scope marker before speculative work and roll it back
/// on any error/cancellation path, which avoids leaking temporary binders into
/// later resolution.
#[derive(Clone, Debug)]
pub struct ScopeMap<K, V> {
    values: BTreeMap<K, Vec<V>>,
    journal: Vec<K>,
    markers: Vec<usize>,
}

impl<K, V> Default for ScopeMap<K, V>
where
    K: Clone + Ord,
{
    fn default() -> Self {
        Self {
            values: BTreeMap::new(),
            journal: vec![],
            markers: vec![],
        }
    }
}

impl<K, V> ScopeMap<K, V>
where
    K: Clone + Ord,
{
    pub fn enter(&mut self) {
        self.markers.push(self.journal.len());
    }

    pub fn define(&mut self, key: K, value: V) {
        self.values.entry(key.clone()).or_default().push(value);
        self.journal.push(key);
    }

    pub fn lookup(&self, key: &K) -> Option<&V> {
        self.values.get(key).and_then(|values| values.last())
    }

    pub fn leave(&mut self) -> bool {
        let Some(marker) = self.markers.pop() else {
            return false;
        };
        while self.journal.len() > marker {
            let key = self.journal.pop().expect("journal length checked");
            let values = self.values.get_mut(&key).expect("journal key exists");
            values.pop();
            if values.is_empty() {
                self.values.remove(&key);
            }
        }
        true
    }
}

/// Revision-scoped occurrence table, grouped by the semantic target so every
/// client gets stable definition/references ordering. Recovered and ambiguous
/// occurrences are deliberately retained but never exposed as rename targets.
#[derive(Clone, Debug, Default)]
pub struct ReferenceIndex {
    by_definition: BTreeMap<DefKey, Vec<Occurrence>>,
    unresolved: Vec<Occurrence>,
}

impl ReferenceIndex {
    pub fn record(&mut self, occurrence: Occurrence) {
        match occurrence.state {
            ResolutionState::Resolved(definition) => {
                self.by_definition
                    .entry(definition)
                    .or_default()
                    .push(occurrence);
            }
            _ => self.unresolved.push(occurrence),
        }
    }

    pub fn references(&self, definition: DefKey) -> &[Occurrence] {
        self.by_definition
            .get(&definition)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    pub fn unresolved(&self) -> &[Occurrence] {
        &self.unresolved
    }

    pub fn canonicalize(&mut self) {
        for occurrences in self.by_definition.values_mut() {
            occurrences.sort_by_key(|occurrence| (occurrence.span, occurrence.role));
        }
        self.unresolved
            .sort_by_key(|occurrence| (occurrence.span, occurrence.role));
    }
}
