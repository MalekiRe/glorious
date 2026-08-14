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

/// A source-level resolution failure discovered while validating an exported
/// interface.  Unlike body diagnostics, these facts must be reported even if
/// no local body happens to exercise the invalid re-export.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ResolutionDiagnostic {
    pub code: &'static str,
    pub span: Span,
    pub message: String,
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
    /// Visibility is a property of the declaration which introduces a module,
    /// not a property recovered from definitions nested below it.  Keeping the
    /// edge in the same immutable index as definitions prevents a public item
    /// inside a private module from becoming reachable merely by spelling its
    /// fully-qualified path.
    module_visibility: BTreeMap<ModuleKey, bool>,
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
            if definition.namespace == Some(DefinitionNamespace::Module)
                && let Some(name) = &definition.name
            {
                let child = ModuleKey {
                    package: definition.module.package.clone(),
                    path: module_child_path(&definition.module.path, name),
                };
                // A duplicate module declaration is already a deterministic
                // interface error.  Never let a later recovered duplicate
                // widen access while that error is present.
                self.module_visibility
                    .entry(child)
                    .and_modify(|public| *public &= definition.public)
                    .or_insert(definition.public);
            }
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
            match self.lexical_module(owner, owner, &path[..path.len() - 1]) {
                ModuleLookup::Found(module) => module,
                ModuleLookup::Inaccessible => return ResolutionState::Inaccessible(vec![]),
                ModuleLookup::Absent => return ResolutionState::Unresolved,
            }
        };
        self.resolve_member(namespace, &module, name, owner, true, &mut BTreeSet::new())
    }

    /// Validate public import edges which are themselves reachable from the
    /// package root.  A `pub use` is part of the exported interface, so it
    /// cannot defer privacy checking until some unrelated local body happens
    /// to name its alias.  Private facade modules are intentionally skipped:
    /// their imports do not cross the package boundary and remain subject to
    /// ordinary use-site resolution.
    pub fn validate_exported_imports(&self) -> Vec<ResolutionDiagnostic> {
        let mut diagnostics = vec![];
        for imports in self.imports.values() {
            for import in imports
                .iter()
                .filter(|import| import.public && self.module_path_is_public(&import.module))
            {
                let external_requester = ModuleKey {
                    package: import.module.package.clone(),
                    // This is intentionally not a graph node.  It models a
                    // dependency consumer, which owns no private module edge
                    // or definition in this package.
                    path: "<dependency>".into(),
                };
                let mut any_public_target = false;
                let mut saw_inaccessible = false;
                for namespace in [
                    DefinitionNamespace::Type,
                    DefinitionNamespace::Value,
                    DefinitionNamespace::Trait,
                    DefinitionNamespace::Effect,
                    DefinitionNamespace::Module,
                    DefinitionNamespace::Operator,
                ] {
                    match self.resolve_direct_path(
                        namespace,
                        &import.module,
                        &external_requester,
                        &import.path,
                        &mut BTreeSet::new(),
                    ) {
                        ResolutionState::Resolved(_) | ResolutionState::Ambiguous(_) => {
                            any_public_target = true;
                        }
                        ResolutionState::Inaccessible(_) => saw_inaccessible = true,
                        ResolutionState::Unresolved | ResolutionState::Recovered => {}
                    }
                }
                if !any_public_target && saw_inaccessible {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3317",
                        span: import.span,
                        message: format!(
                            "public import `{}` exposes a private module path or definition",
                            import.path.join("::")
                        ),
                    });
                }
            }
        }
        diagnostics.sort_by(|left, right| {
            (left.code, left.span, &left.message).cmp(&(right.code, right.span, &right.message))
        });
        diagnostics.dedup();
        diagnostics
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
        let result = self.resolve_import(
            namespace,
            module,
            name,
            requester,
            require_public_import,
            visited,
        );
        visited.remove(&cycle_key);
        result
    }

    fn resolve_import(
        &self,
        namespace: DefinitionNamespace,
        owner: &ModuleKey,
        alias: &str,
        requester: &ModuleKey,
        require_public: bool,
        visited: &mut BTreeSet<(DefinitionNamespace, ModuleKey, String)>,
    ) -> ResolutionState {
        let Some(imports) = self.imports.get(owner) else {
            return ResolutionState::Unresolved;
        };
        let mut resolved = vec![];
        let mut ambiguous = vec![];
        let mut inaccessible = vec![];
        let mut saw_inaccessible = false;
        for import in imports
            .iter()
            .filter(|import| import.alias == alias && (!require_public || import.public))
        {
            // Preserve the original requester across every re-export hop.
            // Resolving a target as the facade module itself would grant its
            // local authority to callers and leak private modules/items.
            match self.resolve_direct_path(namespace, owner, requester, &import.path, visited) {
                ResolutionState::Resolved(definition) => resolved.push(definition),
                ResolutionState::Ambiguous(definitions) => ambiguous.extend(definitions),
                ResolutionState::Inaccessible(definitions) => {
                    // A denied module segment has no final DefKey to retain,
                    // but it must not be collapsed into `Unresolved` after
                    // canonicalization.  Callers distinguish a typo from a
                    // privacy failure for both diagnostics and tooling.
                    saw_inaccessible = true;
                    inaccessible.extend(definitions);
                }
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
        } else if saw_inaccessible || !inaccessible.is_empty() {
            ResolutionState::Inaccessible(inaccessible)
        } else {
            ResolutionState::Unresolved
        }
    }

    fn resolve_direct_path(
        &self,
        namespace: DefinitionNamespace,
        lexical_owner: &ModuleKey,
        requester: &ModuleKey,
        path: &[String],
        visited: &mut BTreeSet<(DefinitionNamespace, ModuleKey, String)>,
    ) -> ResolutionState {
        let Some(name) = path.last() else {
            return ResolutionState::Unresolved;
        };
        let module = if path.len() == 1 {
            lexical_owner.clone()
        } else {
            match self.lexical_module(lexical_owner, requester, &path[..path.len() - 1]) {
                ModuleLookup::Found(module) => module,
                ModuleLookup::Inaccessible => return ResolutionState::Inaccessible(vec![]),
                ModuleLookup::Absent => return ResolutionState::Unresolved,
            }
        };
        self.resolve_member(namespace, &module, name, requester, true, visited)
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

    fn lexical_module(
        &self,
        lexical_owner: &ModuleKey,
        requester: &ModuleKey,
        segments: &[String],
    ) -> ModuleLookup {
        let Some((first, rest)) = segments.split_first() else {
            return ModuleLookup::Absent;
        };
        if first == "crate" {
            return self.module_key(lexical_owner, requester, "crate", rest);
        }
        if first == "self" {
            return self.module_key(lexical_owner, requester, &lexical_owner.path, rest);
        }
        if first == "super" {
            let mut base = lexical_owner.path.clone();
            let mut remaining = segments;
            while matches!(remaining.first(), Some(segment) if segment == "super") {
                let Some(parent) = parent_module_path(&base) else {
                    return ModuleLookup::Absent;
                };
                base = parent;
                remaining = &remaining[1..];
            }
            return self.module_key(lexical_owner, requester, &base, remaining);
        }

        // Ordinary qualified paths are lexical.  Prefer the nearest enclosing
        // module that actually owns the requested child; this supports a
        // nested module referring to a sibling while keeping resolution
        // deterministic in the presence of similarly named descendants.
        let mut base = lexical_owner.path.clone();
        loop {
            match self.module_key(lexical_owner, requester, &base, segments) {
                ModuleLookup::Found(module) => return ModuleLookup::Found(module),
                ModuleLookup::Inaccessible => return ModuleLookup::Inaccessible,
                ModuleLookup::Absent => {}
            }
            let Some(parent) = parent_module_path(&base) else {
                return ModuleLookup::Absent;
            };
            base = parent;
        }
    }

    fn module_key(
        &self,
        lexical_owner: &ModuleKey,
        requester: &ModuleKey,
        base: &str,
        suffix: &[String],
    ) -> ModuleLookup {
        let path = if suffix.is_empty() {
            base.to_owned()
        } else {
            format!("{base}::{}", suffix.join("::"))
        };
        let module = ModuleKey {
            package: lexical_owner.package.clone(),
            path,
        };
        if !self.modules.contains_key(&module) {
            return ModuleLookup::Absent;
        }
        if self.module_path_visible_to(&module, requester) {
            ModuleLookup::Found(module)
        } else {
            ModuleLookup::Inaccessible
        }
    }

    /// Every module edge on a qualified path is independently checked.  A
    /// private module is visible in the module that declared it and that
    /// module's descendants; it is not visible merely because a nested item
    /// happens to be `pub`.
    fn module_path_visible_to(&self, module: &ModuleKey, requester: &ModuleKey) -> bool {
        if module.package != requester.package {
            return false;
        }
        let mut prefix = String::from("crate");
        if module.path == prefix {
            return true;
        }
        for segment in module.path.split("::").skip(1) {
            let parent = prefix.clone();
            prefix.push_str("::");
            prefix.push_str(segment);
            let child = ModuleKey {
                package: module.package.clone(),
                path: prefix.clone(),
            };
            let public = self.module_visibility.get(&child).copied().unwrap_or(false);
            if !public && !module_is_descendant_of(requester, &parent) {
                return false;
            }
        }
        true
    }

    fn module_path_is_public(&self, module: &ModuleKey) -> bool {
        if module.path == "crate" {
            return true;
        }
        let mut prefix = String::from("crate");
        for segment in module.path.split("::").skip(1) {
            prefix.push_str("::");
            prefix.push_str(segment);
            let child = ModuleKey {
                package: module.package.clone(),
                path: prefix.clone(),
            };
            if !self.module_visibility.get(&child).copied().unwrap_or(false) {
                return false;
            }
        }
        true
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ModuleLookup {
    Found(ModuleKey),
    Inaccessible,
    Absent,
}

fn parent_module_path(path: &str) -> Option<String> {
    path.rsplit_once("::").map(|(parent, _)| parent.to_owned())
}

fn module_child_path(parent: &str, child: &str) -> String {
    if parent == "crate" {
        format!("crate::{child}")
    } else {
        format!("{parent}::{child}")
    }
}

fn module_is_descendant_of(module: &ModuleKey, ancestor: &str) -> bool {
    module.path == ancestor
        || module
            .path
            .strip_prefix(ancestor)
            .is_some_and(|suffix| suffix.starts_with("::"))
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
    /// A definition receives an owner-local identity which is never reused,
    /// even after its scope is rolled back.  Stack depth alone is not an
    /// identity: a later sibling scope may recreate the same depth for a
    /// different binding.
    binding_ids: BTreeMap<K, Vec<u64>>,
    next_binding_id: u64,
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
            binding_ids: BTreeMap::new(),
            next_binding_id: 0,
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
        let identity = self.next_binding_id;
        self.next_binding_id = self.next_binding_id.saturating_add(1);
        self.binding_ids
            .entry(key.clone())
            .or_default()
            .push(identity);
        self.journal.push(key);
    }

    pub fn lookup(&self, key: &K) -> Option<&V> {
        self.values.get(key).and_then(|values| values.last())
    }

    /// Return the non-reusable lexical identity of the currently visible
    /// binding for a key. Consumers may retain it past a scope exit without
    /// risking an accidental match with a later sibling binding.
    pub fn binding_generation(&self, key: &K) -> Option<u64> {
        self.binding_ids
            .get(key)
            .and_then(|identities| identities.last())
            .copied()
    }

    pub fn leave(&mut self) -> bool {
        let Some(marker) = self.markers.pop() else {
            return false;
        };
        while self.journal.len() > marker {
            let key = self.journal.pop().expect("journal length checked");
            let values = self.values.get_mut(&key).expect("journal key exists");
            values.pop();
            let identities = self
                .binding_ids
                .get_mut(&key)
                .expect("journal binding identity exists");
            identities.pop();
            if values.is_empty() {
                self.values.remove(&key);
                self.binding_ids.remove(&key);
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
