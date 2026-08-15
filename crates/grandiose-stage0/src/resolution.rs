//! Namespace-aware resolution and reference indexing.
//!
//! Global interfaces and body-local scope use the same stable `DefKey` target.
//! This keeps compiler checking, definition/references, semantic highlighting,
//! and rename on one resolution product rather than independent approximations.

use std::collections::{BTreeMap, BTreeSet};

use crate::{
    header::{GenericParameters, HeaderStructuralConst, HeaderStructuralU32Expr, ParsedHeader},
    identity::{DefKey, ModuleKey, package_module_alias},
    interface::{DefinitionNamespace, PackageInterface},
    source::Span,
    types::{GenericArgument, GenericKind, StructuralU32Expr},
};

/// The language prelude owns the quantitative relation and destruction hook.
///
/// These are not source-spelling fallbacks: their identities and generic
/// contracts are part of the language generation, just like scalar types.
/// A source declaration with either name still wins normal resolution, which
/// keeps the prelude from silently changing a package's declared interface.
pub(crate) fn language_use_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-language-prelude-use-v1",
    ))
}

pub(crate) fn language_drop_trait_definition() -> DefKey {
    DefKey(crate::Digest::of_bytes(
        b"grandiose-stage0-language-prelude-drop-v1",
    ))
}

fn language_prelude_trait(path: &[String]) -> Option<DefKey> {
    match path {
        [name] if name == "Use" => Some(language_use_trait_definition()),
        [name] if name == "Drop" => Some(language_drop_trait_definition()),
        _ => None,
    }
}

fn language_prelude_trait_kinds(definition: DefKey) -> Option<&'static [GenericKind]> {
    match definition {
        value if value == language_use_trait_definition() => {
            Some(&[GenericKind::Const(crate::types::ConstKind::Quantity)])
        }
        value if value == language_drop_trait_definition() => Some(&[]),
        _ => None,
    }
}

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
    /// Dependency roots linked into this frozen interface set. Source uses
    /// the package-name component before `@`; full package keys remain the
    /// ownership identities used by coherence.
    package_roots: BTreeMap<String, Vec<ModuleKey>>,
    /// Visibility is a property of the declaration which introduces a module,
    /// not a property recovered from definitions nested below it.  Keeping the
    /// edge in the same immutable index as definitions prevents a public item
    /// inside a private module from becoming reachable merely by spelling its
    /// fully-qualified path.
    module_visibility: BTreeMap<ModuleKey, bool>,
    /// Module declarations retain the concrete child they introduce.  A
    /// public module binding is an exported traversal capability, so sealing
    /// an interface must include the public surface behind that binding rather
    /// than only its syntactic `mod name` header.
    module_targets: BTreeMap<DefKey, ModuleKey>,
    imports: BTreeMap<ModuleKey, Vec<ImportBinding>>,
    owners: BTreeMap<DefKey, ModuleKey>,
    definition_contracts: BTreeMap<DefKey, DefinitionContract>,
    type_generic_arities: BTreeMap<DefKey, u32>,
    type_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
    /// Structural defaults are frozen by binder position, not source name, so
    /// a consuming body can complete a trailing nominal application without
    /// reopening declaration parsing or changing specialization identity.
    type_generic_defaults: BTreeMap<DefKey, Vec<Option<GenericArgument>>>,
    trait_generic_arities: BTreeMap<DefKey, u32>,
    trait_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
    /// Source-shaped supertrait edges are retained just long enough to extend
    /// the declaration index with inherited associated-item contracts.  Core
    /// and the tabled solver still own evidence selection; this index only
    /// supplies item binder kinds while a projection is being elaborated.
    trait_supertrait_paths: BTreeMap<DefKey, Vec<Vec<String>>>,
    associated_type_generic_kinds: BTreeMap<(DefKey, String), Vec<GenericKind>>,
    /// Associated structural constants are declaration-owned contracts just
    /// like associated type binders.  Implementation headers need the kind
    /// before their value can be frozen, especially when that value is a
    /// delayed associated-constant projection rather than a literal.
    associated_const_kinds: BTreeMap<(DefKey, String), crate::types::ConstKind>,
    effect_generic_arities: BTreeMap<DefKey, u32>,
    effect_generic_kinds: BTreeMap<DefKey, Vec<GenericKind>>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct IndexedDefinition {
    key: DefKey,
    module: ModuleKey,
    public: bool,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct DefinitionContract {
    header_fingerprint: crate::identity::Digest,
    constant_value_fingerprint: Option<crate::identity::Digest>,
}

fn generic_const_defaults(generics: &GenericParameters) -> Vec<Option<GenericArgument>> {
    fn u32_expression(
        value: &HeaderStructuralU32Expr,
        generics: &GenericParameters,
    ) -> Option<StructuralU32Expr> {
        Some(match value {
            HeaderStructuralU32Expr::Literal(value) => StructuralU32Expr::Literal(*value),
            HeaderStructuralU32Expr::Param(name) => {
                let index = generics.names.iter().position(|candidate| candidate == name)?;
                (generics.kind(name) == GenericKind::Const(crate::ConstKind::U32))
                    .then_some(StructuralU32Expr::Param(index as u32))?
            }
            HeaderStructuralU32Expr::Add(left, right) => StructuralU32Expr::Add(
                Box::new(u32_expression(left, generics)?),
                Box::new(u32_expression(right, generics)?),
            ),
            HeaderStructuralU32Expr::Sub(left, right) => StructuralU32Expr::Sub(
                Box::new(u32_expression(left, generics)?),
                Box::new(u32_expression(right, generics)?),
            ),
            HeaderStructuralU32Expr::Mul(left, right) => StructuralU32Expr::Mul(
                Box::new(u32_expression(left, generics)?),
                Box::new(u32_expression(right, generics)?),
            ),
            HeaderStructuralU32Expr::Div(left, right) => StructuralU32Expr::Div(
                Box::new(u32_expression(left, generics)?),
                Box::new(u32_expression(right, generics)?),
            ),
            HeaderStructuralU32Expr::Rem(left, right) => StructuralU32Expr::Rem(
                Box::new(u32_expression(left, generics)?),
                Box::new(u32_expression(right, generics)?),
            ),
        })
    }

    generics
        .names
        .iter()
        .map(|name| {
            let kind = generics.kind(name);
            let value = generics.const_defaults.get(name)?;
            match (kind, value) {
                (GenericKind::Const(crate::ConstKind::U32), HeaderStructuralConst::U32(value)) => {
                    Some(GenericArgument::ConstU32(*value))
                }
                (
                    GenericKind::Const(crate::ConstKind::U32),
                    HeaderStructuralConst::U32Expression(value),
                ) => match u32_expression(value, generics)?.normalized().ok()? {
                    StructuralU32Expr::Literal(value) => Some(GenericArgument::ConstU32(value)),
                    value => Some(GenericArgument::ConstU32Expr(value)),
                },
                (
                    GenericKind::Const(expected),
                    HeaderStructuralConst::Generic(source_name),
                ) => {
                    let index = generics
                        .names
                        .iter()
                        .position(|candidate| candidate == source_name)?;
                    (generics.kind(source_name) == GenericKind::Const(expected)).then_some(
                        GenericArgument::ConstGeneric {
                            index: index as u32,
                            kind: expected,
                        },
                    )
                }
                (
                    GenericKind::Const(crate::ConstKind::Quantity),
                    HeaderStructuralConst::Quantity(value),
                ) => Some(GenericArgument::ConstQuantity(*value)),
                _ => None,
            }
        })
        .collect()
}

/// An explicit source-level import binding, retained independently of body
/// scopes so diagnostics, tooling, and all semantic namespaces consult the
/// same interface-owned fact.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ImportBinding {
    /// A glob targets a module and contributes all names which are visible
    /// through that module.  It is not flattened while interfaces are being
    /// collected: modules from other source files may not have been indexed
    /// yet, and flattening there would make import order observable.
    pub glob: bool,
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
            self.owners
                .entry(definition.key)
                .or_insert_with(|| definition.module.clone());
            self.definition_contracts
                .entry(definition.key)
                .or_insert(DefinitionContract {
                    header_fingerprint: definition.header_fingerprint,
                    constant_value_fingerprint: definition.constant_value_fingerprint,
                });
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
                    .entry(child.clone())
                    .and_modify(|public| *public &= definition.public)
                    .or_insert(definition.public);
                self.module_targets.entry(definition.key).or_insert(child);
            }
            if definition.namespace == Some(DefinitionNamespace::Type) {
                let (arity, kinds, defaults) = match &definition.syntax.header {
                    ParsedHeader::Nominal { generics, .. }
                    | ParsedHeader::TypeAlias { generics, .. } => {
                        (
                            generics.len() as u32,
                            generics.kinds(),
                            generic_const_defaults(generics),
                        )
                    }
                    _ => (0, vec![], vec![]),
                };
                self.type_generic_arities.insert(definition.key, arity);
                self.type_generic_kinds.insert(definition.key, kinds);
                self.type_generic_defaults.insert(definition.key, defaults);
            }
            match &definition.syntax.header {
                ParsedHeader::Trait(header) => {
                    self.trait_generic_arities
                        .insert(definition.key, header.generics.len() as u32);
                    self.trait_generic_kinds
                        .insert(definition.key, header.generics.kinds());
                    self.trait_supertrait_paths.insert(
                        definition.key,
                        header
                            .supertraits
                            .iter()
                            .map(|reference| reference.path.clone())
                            .collect(),
                    );
                    for item in &header.associated_types {
                        self.associated_type_generic_kinds
                            .insert((definition.key, item.name.clone()), item.generics.kinds());
                    }
                    for item in &header.associated_consts {
                        self.associated_const_kinds
                            .insert((definition.key, item.name.clone()), item.kind);
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
                    let alias = if binding.glob {
                        "<glob>".into()
                    } else {
                        binding
                            .alias
                            .clone()
                            .or_else(|| binding.path.last().cloned())
                            .unwrap_or_else(|| "<error>".into())
                    };
                    self.imports
                        .entry(definition.module.clone())
                        .or_default()
                        .push(ImportBinding {
                            glob: binding.glob,
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

    /// Immutable declaration ownership used by coherence and package-boundary
    /// checks. Duplicate keys retain their first canonical owner.
    pub fn owner(&self, key: DefKey) -> Option<&ModuleKey> {
        self.owners.get(&key)
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
        self.package_roots.clear();
        for module in self.modules.keys().filter(|module| module.path == "crate") {
            // Normalized request worlds have already rejected an invalid
            // package alias. Retain this guard because DefinitionIndex is a
            // public defensive boundary and can also be built from hostile or
            // recovered interface products outside a service request.
            let Some(alias) = package_module_alias(&module.package) else {
                continue;
            };
            self.package_roots.entry(alias).or_default().push(module.clone());
        }
        for roots in self.package_roots.values_mut() {
            roots.sort();
            roots.dedup();
        }
        // Projection parsing needs an associated item's binder kinds before
        // trait solving can select the parent implementation.  Flatten only
        // declaration contracts through supertrait edges here; the actual
        // parent identity, substitutions, ambiguity, and evidence remain the
        // responsibility of TraitSolver's instantiated lookup.
        let traits = self.trait_generic_arities.keys().copied().collect::<Vec<_>>();
        for definition in traits {
            for (name, kinds) in
                self.inherited_associated_type_kinds(definition, &mut BTreeSet::new())
            {
                self.associated_type_generic_kinds
                    .entry((definition, name))
                    .or_insert(kinds);
            }
        }
    }

    fn inherited_associated_type_kinds(
        &self,
        definition: DefKey,
        active: &mut BTreeSet<DefKey>,
    ) -> BTreeMap<String, Vec<GenericKind>> {
        if !active.insert(definition) {
            return BTreeMap::new();
        }
        let mut items = self
            .associated_type_generic_kinds
            .iter()
            .filter_map(|((owner, name), kinds)| {
                (*owner == definition).then(|| (name.clone(), kinds.clone()))
            })
            .collect::<BTreeMap<_, _>>();
        let requester = self.owners.get(&definition);
        if let (Some(requester), Some(supertraits)) =
            (requester, self.trait_supertrait_paths.get(&definition))
        {
            for path in supertraits {
                let ResolutionState::Resolved(parent) = self.resolve_path(
                    DefinitionNamespace::Trait,
                    requester,
                    path,
                ) else {
                    continue;
                };
                for (name, kinds) in self.inherited_associated_type_kinds(parent, active) {
                    items.entry(name).or_insert(kinds);
                }
            }
        }
        active.remove(&definition);
        items
    }

    pub fn resolve(&self, namespace: DefinitionNamespace, name: &str) -> ResolutionState {
        self.classify(self.entries.get(&(namespace, name.to_owned())), None)
    }

    /// Return the declaration identities reachable by an unqualified lookup
    /// from `requester`.  Implicit language surfaces (such as operator
    /// dispatch) must use this rather than scanning every frozen definition:
    /// a public trait in an unrelated module is not brought into scope merely
    /// because it happens to declare the same operator spelling.
    ///
    /// The result is sorted and deduplicated by `DefKey`, and every candidate
    /// has passed the ordinary lexical/import/module visibility resolver.
    pub fn visible_definitions(
        &self,
        namespace: DefinitionNamespace,
        requester: &ModuleKey,
    ) -> Vec<DefKey> {
        let mut names = BTreeSet::new();
        let mut lexical = requester.clone();
        loop {
            names.extend(self.module_member_names(&lexical, namespace, &mut BTreeSet::new()));
            let Some(parent) = parent_module_path(&lexical.path) else {
                break;
            };
            lexical.path = parent;
        }
        let mut definitions = BTreeSet::new();
        for name in names {
            match self.resolve_path(namespace, requester, &[name]) {
                ResolutionState::Resolved(definition) => {
                    definitions.insert(definition);
                }
                ResolutionState::Ambiguous(definitions_for_name) => {
                    definitions.extend(definitions_for_name);
                }
                ResolutionState::Unresolved
                | ResolutionState::Inaccessible(_)
                | ResolutionState::Recovered => {}
            }
        }
        definitions.into_iter().collect()
    }

    /// Seal a module's exported semantic surface after the complete module
    /// graph has been indexed. Interface collection intentionally runs before
    /// that graph is complete, so its local header fingerprint cannot know
    /// what a `pub use api::*` or `pub use api as facade` eventually exposes.
    ///
    /// The returned digest includes the frozen local header contract and the
    /// exact externally visible names reachable through public declarations,
    /// re-exports, and public module edges. Private names/imports are
    /// deliberately absent. This is the value published to dependency
    /// tracking and package-interface consumers; otherwise changing a public
    /// item behind a public glob could leave an unchanged facade ABI.
    pub fn sealed_public_fingerprint(
        &self,
        interface: &PackageInterface,
    ) -> crate::identity::Digest {
        let requester = ModuleKey {
            package: interface.module.package.clone(),
            path: "<dependency>".into(),
        };
        let mut active = BTreeSet::new();
        let surface = self.public_module_surface(&interface.module, &requester, &mut active);
        crate::identity::Digest::of_parts([
            b"grandiose-stage0-interface-sealed-v1".as_slice(),
            interface.public_fingerprint.as_bytes().as_slice(),
            surface.as_bytes().as_slice(),
        ])
    }

    /// Return the exact module interfaces consulted while sealing this
    /// module's public surface.  This mirrors `sealed_public_fingerprint`'s
    /// resolution walk rather than approximating it from source import syntax:
    /// a private import, an inaccessible re-export, or an unselected glob
    /// member must not become an interface dependency.  Conversely, a public
    /// module edge and every resolved public re-export contribute the target
    /// interface whose contract supplied the exported fact.
    ///
    /// The result deliberately excludes `interface.module` itself.  A module
    /// may re-export a name declared locally (or form a recovered re-export
    /// cycle); recording a self edge would turn an otherwise ordinary
    /// revision fact into a ledger cycle.  Its own source remains the direct
    /// `Input` dependency published by the service.
    pub fn sealed_public_dependencies(&self, interface: &PackageInterface) -> Vec<ModuleKey> {
        let requester = ModuleKey {
            package: interface.module.package.clone(),
            path: "<dependency>".into(),
        };
        let mut active = BTreeSet::new();
        let mut dependencies = BTreeSet::new();
        self.collect_public_surface_dependencies(
            &interface.module,
            &interface.module,
            &requester,
            &mut active,
            &mut dependencies,
        );
        dependencies.into_iter().collect()
    }

    fn collect_public_surface_dependencies(
        &self,
        module: &ModuleKey,
        origin: &ModuleKey,
        requester: &ModuleKey,
        active: &mut BTreeSet<ModuleKey>,
        dependencies: &mut BTreeSet<ModuleKey>,
    ) {
        // This matches the cycle marker in `public_module_surface`: no
        // additional target contract is observed after a recursive module
        // edge, so no dependency is added for that unobserved suffix.
        if !active.insert(module.clone()) {
            return;
        }
        if module != origin {
            dependencies.insert(module.clone());
        }
        for namespace in all_namespaces() {
            let names = self.module_member_names(module, namespace, &mut BTreeSet::new());
            for name in names {
                match self.resolve_member(
                    namespace,
                    module,
                    &name,
                    requester,
                    true,
                    &mut BTreeSet::new(),
                ) {
                    ResolutionState::Resolved(key) => {
                        if namespace == DefinitionNamespace::Module {
                            if let Some(target) = self.module_targets.get(&key) {
                                self.collect_public_surface_dependencies(
                                    target,
                                    origin,
                                    requester,
                                    active,
                                    dependencies,
                                );
                            }
                        } else {
                            self.collect_definition_owner_dependency(key, origin, dependencies);
                        }
                    }
                    ResolutionState::Ambiguous(candidates) => {
                        // Ambiguous non-module exports are still frozen
                        // surface facts. Retain each observed contract owner
                        // so a failed/recovered request cannot later be
                        // explained by a synthetic facade-only change. Module
                        // candidates do not expose a traversed target surface
                        // (the fingerprint likewise records only their
                        // recovered declaration contracts).
                        for key in candidates {
                            if namespace == DefinitionNamespace::Module {
                                continue;
                            }
                            self.collect_definition_owner_dependency(key, origin, dependencies);
                        }
                    }
                    ResolutionState::Unresolved
                    | ResolutionState::Inaccessible(_)
                    | ResolutionState::Recovered => {}
                }
            }
        }
        active.remove(module);
    }

    fn collect_definition_owner_dependency(
        &self,
        key: DefKey,
        origin: &ModuleKey,
        dependencies: &mut BTreeSet<ModuleKey>,
    ) {
        if let Some(owner) = self.owners.get(&key)
            && owner != origin
        {
            dependencies.insert(owner.clone());
        }
    }

    fn public_module_surface(
        &self,
        module: &ModuleKey,
        requester: &ModuleKey,
        active: &mut BTreeSet<ModuleKey>,
    ) -> crate::identity::Digest {
        if !active.insert(module.clone()) {
            // A cycle has no source-order-dependent fallback. Export
            // validation reports invalid value re-export cycles; retaining a
            // canonical marker here also makes malformed interface products
            // deterministic and prevents recursive fingerprinting.
            return crate::identity::Digest::of_parts([
                b"grandiose-stage0-public-surface-cycle-v1".as_slice(),
                module.package.0.as_bytes(),
                module.path.as_bytes(),
            ]);
        }

        let mut bytes = Vec::new();
        append_surface(&mut bytes, b"grandiose-stage0-public-module-surface-v1");
        append_surface(&mut bytes, module.package.0.as_bytes());
        append_surface(&mut bytes, module.path.as_bytes());
        for namespace in all_namespaces() {
            let names = self.module_member_names(module, namespace, &mut BTreeSet::new());
            for name in names {
                let state = self.resolve_member(
                    namespace,
                    module,
                    &name,
                    requester,
                    true,
                    &mut BTreeSet::new(),
                );
                match state {
                    ResolutionState::Resolved(key) => {
                        append_surface(&mut bytes, b"resolved");
                        append_surface(&mut bytes, &[namespace as u8]);
                        append_surface(&mut bytes, name.as_bytes());
                        self.append_definition_contract(&mut bytes, key);
                        if namespace == DefinitionNamespace::Module
                            && let Some(target) = self.module_targets.get(&key)
                        {
                            let nested = self.public_module_surface(target, requester, active);
                            append_surface(&mut bytes, b"module-surface");
                            append_surface(&mut bytes, nested.as_bytes().as_slice());
                        }
                    }
                    ResolutionState::Ambiguous(mut candidates) => {
                        canonicalize_keys(&mut candidates);
                        append_surface(&mut bytes, b"ambiguous");
                        append_surface(&mut bytes, &[namespace as u8]);
                        append_surface(&mut bytes, name.as_bytes());
                        for candidate in candidates {
                            self.append_definition_contract(&mut bytes, candidate);
                        }
                    }
                    // Inaccessible and absent names are not exported facts.
                    ResolutionState::Unresolved
                    | ResolutionState::Inaccessible(_)
                    | ResolutionState::Recovered => {}
                }
            }
        }
        active.remove(module);
        crate::identity::Digest::of_bytes(&bytes)
    }

    fn append_definition_contract(&self, bytes: &mut Vec<u8>, key: DefKey) {
        let Some(definition) = self.definition_contracts.get(&key) else {
            // A forged or internally inconsistent index cannot silently turn
            // into an empty contract. Keep the stable key as a fail-closed
            // fingerprint marker; normal index construction always finds the
            // corresponding declaration.
            append_surface(bytes, b"missing-definition-contract");
            append_surface(bytes, key.0.as_bytes().as_slice());
            return;
        };
        append_surface(bytes, b"definition-contract");
        append_surface(bytes, key.0.as_bytes().as_slice());
        append_surface(bytes, definition.header_fingerprint.as_bytes().as_slice());
        match definition.constant_value_fingerprint {
            Some(value) => {
                append_surface(bytes, b"constant-value");
                append_surface(bytes, value.as_bytes().as_slice());
            }
            None => append_surface(bytes, b"no-constant-value"),
        }
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

    /// Position-aligned defaults for nominal and alias binders.  A `None`
    /// entry remains a required source argument (or an inference site where
    /// that form is explicitly permitted).
    pub fn type_generic_defaults(&self, definition: DefKey) -> Option<&[Option<GenericArgument>]> {
        self.type_generic_defaults.get(&definition).map(Vec::as_slice)
    }

    pub fn trait_generic_arity(&self, definition: DefKey) -> Option<u32> {
        language_prelude_trait_kinds(definition)
            .map(|kinds| kinds.len() as u32)
            .or_else(|| self.trait_generic_arities.get(&definition).copied())
    }

    pub fn trait_generic_kinds(&self, definition: DefKey) -> Option<&[GenericKind]> {
        language_prelude_trait_kinds(definition)
            .or_else(|| self.trait_generic_kinds.get(&definition).map(Vec::as_slice))
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

    /// Declared kind of an associated structural constant.  This is queried
    /// while freezing an implementation member, before later interface
    /// validation can compare its final elaborated value with the trait.
    pub fn associated_const_kind(
        &self,
        trait_definition: DefKey,
        name: &str,
    ) -> Option<crate::types::ConstKind> {
        self.associated_const_kinds
            .get(&(trait_definition, name.to_owned()))
            .copied()
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
        // Top-level value aliases may deliberately occupy a qualified
        // receiver spelling (`Vec::len`) without declaring a module named
        // `Vec`. Prefer that exact interface-owned binding before treating
        // the segments as a module traversal.
        if namespace == DefinitionNamespace::Value && path.len() > 1 {
            let spelling = path.join("::");
            let direct = self.resolve_member(
                namespace,
                owner,
                &spelling,
                owner,
                false,
                &mut BTreeSet::new(),
            );
            if !matches!(direct, ResolutionState::Unresolved) {
                return direct;
            }
        }
        let module = if path.len() == 1 {
            // An unqualified item lookup is lexical: a nested module may use
            // declarations inherited from its enclosing modules, with the
            // nearest declaration winning.  The original owner remains the
            // requester for every step, so this does not grant a child access
            // to a private sibling or an external package's private API.
            let mut lexical = owner.clone();
            loop {
                let resolved = self.resolve_member(
                    namespace,
                    &lexical,
                    name,
                    owner,
                    false,
                    &mut BTreeSet::new(),
                );
                if !matches!(resolved, ResolutionState::Unresolved) {
                    return resolved;
                }
                let Some(parent) = parent_module_path(&lexical.path) else {
                    break;
                };
                lexical.path = parent;
            }
            return if namespace == DefinitionNamespace::Trait {
                language_prelude_trait(path)
                    .map(ResolutionState::Resolved)
                    .unwrap_or(ResolutionState::Unresolved)
            } else {
                ResolutionState::Unresolved
            };
        } else {
            match self.lexical_module(owner, owner, &path[..path.len() - 1]) {
                ModuleLookup::Found(module) => module,
                ModuleLookup::Ambiguous(modules) => {
                    return self.ambiguous_modules(modules);
                }
                ModuleLookup::Inaccessible => return ResolutionState::Inaccessible(vec![]),
                ModuleLookup::Absent => return ResolutionState::Unresolved,
            }
        };
        self.resolve_member(namespace, &module, name, owner, true, &mut BTreeSet::new())
    }

    /// Check every import edge before bodies are demanded.  This prevents an
    /// unused `use private::Thing` (and, especially, a glob through a private
    /// module) from becoming a latent capability which happens to fail only
    /// after an unrelated edit starts using it.
    pub fn validate_imports(&self) -> Vec<ResolutionDiagnostic> {
        let mut diagnostics = vec![];
        for imports in self.imports.values() {
            for import in imports {
                // Exported edges have a stricter requester (a dependency
                // consumer) and are diagnosed by `validate_exported_imports`
                // below.  Checking them here as the importing module would
                // produce a weaker, duplicate privacy diagnostic.
                if import.public {
                    continue;
                }
                let requester = &import.module;
                if import.glob {
                    match self.lexical_module(&import.module, requester, &import.path) {
                        ModuleLookup::Found(_) => {}
                        ModuleLookup::Ambiguous(_) => diagnostics.push(ResolutionDiagnostic {
                            code: "G3328",
                            span: import.span,
                            message: format!(
                                "glob import `{}` traverses an ambiguous module path",
                                import.path.join("::")
                            ),
                        }),
                        ModuleLookup::Inaccessible => diagnostics.push(ResolutionDiagnostic {
                            code: "G3326",
                            span: import.span,
                            message: format!(
                                "glob import `{}` traverses a private module path",
                                import.path.join("::")
                            ),
                        }),
                        ModuleLookup::Absent => diagnostics.push(ResolutionDiagnostic {
                            code: "G3327",
                            span: import.span,
                            message: format!(
                                "glob import `{}` does not name a module",
                                import.path.join("::")
                            ),
                        }),
                    }
                    continue;
                }

                let states = [
                    DefinitionNamespace::Type,
                    DefinitionNamespace::Value,
                    DefinitionNamespace::Trait,
                    DefinitionNamespace::Effect,
                    DefinitionNamespace::Module,
                    DefinitionNamespace::Operator,
                ]
                .into_iter()
                .map(|namespace| {
                    self.resolve_direct_path(
                        namespace,
                        &import.module,
                        requester,
                        &import.path,
                        &mut BTreeSet::new(),
                    )
                })
                .collect::<Vec<_>>();
                if states
                    .iter()
                    .all(|state| matches!(state, ResolutionState::Unresolved))
                {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3327",
                        span: import.span,
                        message: format!(
                            "import `{}` does not resolve in any namespace",
                            import.path.join("::")
                        ),
                    });
                } else if states
                    .iter()
                    .any(|state| matches!(state, ResolutionState::Ambiguous(_)))
                {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3328",
                        span: import.span,
                        message: format!(
                            "import `{}` traverses an ambiguous module path or target",
                            import.path.join("::")
                        ),
                    });
                } else if states.iter().all(|state| {
                    matches!(
                        state,
                        ResolutionState::Unresolved | ResolutionState::Inaccessible(_)
                    )
                }) {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3326",
                        span: import.span,
                        message: format!(
                            "import `{}` names an inaccessible definition",
                            import.path.join("::")
                        ),
                    });
                }
            }
        }
        canonicalize_diagnostics(&mut diagnostics);
        diagnostics
    }

    /// Source import sites are ordinary semantic occurrences.  Returning
    /// them from the same index which resolves body paths keeps definition,
    /// references, highlighting, and rename in agreement about aliases and
    /// globs.  A glob has one occurrence for each imported semantic target;
    /// all share the glob's source span because that is its one source site.
    pub fn import_occurrences(&self) -> Vec<Occurrence> {
        let mut occurrences = vec![];
        for imports in self.imports.values() {
            for import in imports {
                if import.glob {
                    let target =
                        match self.lexical_module(&import.module, &import.module, &import.path) {
                            ModuleLookup::Found(target) => target,
                            ModuleLookup::Ambiguous(modules) => {
                                occurrences.push(Occurrence {
                                    span: import.span,
                                    namespace: DefinitionNamespace::Module,
                                    role: OccurrenceRole::Import,
                                    state: self.ambiguous_modules(modules),
                                });
                                continue;
                            }
                            ModuleLookup::Inaccessible | ModuleLookup::Absent => {
                                occurrences.push(Occurrence {
                                    span: import.span,
                                    namespace: DefinitionNamespace::Module,
                                    role: OccurrenceRole::Import,
                                    state: ResolutionState::Unresolved,
                                });
                                continue;
                            }
                        };
                    for namespace in all_namespaces() {
                        for name in
                            self.module_member_names(&target, namespace, &mut BTreeSet::new())
                        {
                            occurrences.push(Occurrence {
                                span: import.span,
                                namespace,
                                role: OccurrenceRole::Import,
                                state: self.resolve_member(
                                    namespace,
                                    &import.module,
                                    &name,
                                    &import.module,
                                    false,
                                    &mut BTreeSet::new(),
                                ),
                            });
                        }
                    }
                } else {
                    let mut found = false;
                    for namespace in all_namespaces() {
                        let state = self.resolve_direct_path(
                            namespace,
                            &import.module,
                            &import.module,
                            &import.path,
                            &mut BTreeSet::new(),
                        );
                        if !matches!(state, ResolutionState::Unresolved) {
                            found = true;
                            occurrences.push(Occurrence {
                                span: import.span,
                                namespace,
                                role: OccurrenceRole::Import,
                                state,
                            });
                        }
                    }
                    if !found {
                        occurrences.push(Occurrence {
                            span: import.span,
                            namespace: DefinitionNamespace::Value,
                            role: OccurrenceRole::Import,
                            state: ResolutionState::Unresolved,
                        });
                    }
                }
            }
        }
        occurrences.sort_by_key(|occurrence| {
            (
                occurrence.span,
                occurrence.namespace,
                occurrence.role,
                format!("{:?}", occurrence.state),
            )
        });
        occurrences.dedup_by(|left, right| {
            left.span == right.span
                && left.namespace == right.namespace
                && left.role == right.role
                && left.state == right.state
        });
        occurrences
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
                if import.glob {
                    match self.lexical_module(&import.module, &external_requester, &import.path) {
                        ModuleLookup::Found(_) => continue,
                        ModuleLookup::Ambiguous(_) => {
                            diagnostics.push(ResolutionDiagnostic {
                                code: "G3318",
                                span: import.span,
                                message: format!(
                                    "public glob import `{}` traverses an ambiguous module path",
                                    import.path.join("::")
                                ),
                            });
                            continue;
                        }
                        ModuleLookup::Inaccessible | ModuleLookup::Absent => {
                            diagnostics.push(ResolutionDiagnostic {
                                code: "G3317",
                                span: import.span,
                                message: format!(
                                    "public glob import `{}` exposes a private or absent module path",
                                    import.path.join("::")
                                ),
                            });
                            continue;
                        }
                    }
                }
                let mut any_public_target = false;
                let mut saw_inaccessible = false;
                let mut saw_ambiguity = false;
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
                        ResolutionState::Resolved(_) => any_public_target = true,
                        ResolutionState::Ambiguous(_) => saw_ambiguity = true,
                        ResolutionState::Inaccessible(_) => saw_inaccessible = true,
                        ResolutionState::Unresolved | ResolutionState::Recovered => {}
                    }
                }
                if saw_ambiguity {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3318",
                        span: import.span,
                        message: format!(
                            "public import `{}` is ambiguous in an exported namespace",
                            import.path.join("::")
                        ),
                    });
                } else if !any_public_target {
                    diagnostics.push(ResolutionDiagnostic {
                        code: "G3317",
                        span: import.span,
                        message: format!(
                            "public import `{}` exposes a {} target",
                            import.path.join("::"),
                            if saw_inaccessible {
                                "private"
                            } else {
                                "missing"
                            },
                        ),
                    });
                }
            }
        }
        // A public alias is itself an exported name.  Validate the merged
        // namespace after all public edges have contributed, rather than
        // checking each edge in isolation: two individually valid `pub use`
        // declarations must not freeze an interface which is ambiguous to a
        // dependency.  Local definitions intentionally win here, matching
        // ordinary resolution and preserving lexical shadowing.
        for (module, imports) in &self.imports {
            if !self.module_path_is_public(module) {
                continue;
            }
            let requester = ModuleKey {
                package: module.package.clone(),
                path: "<dependency>".into(),
            };
            let aliases = imports
                .iter()
                .filter(|import| import.public && !import.glob)
                .map(|import| (import.alias.clone(), import.span))
                .collect::<BTreeMap<_, _>>();
            for (alias, span) in aliases {
                for namespace in all_namespaces() {
                    if matches!(
                        self.resolve_member(
                            namespace,
                            module,
                            &alias,
                            &requester,
                            true,
                            &mut BTreeSet::new(),
                        ),
                        ResolutionState::Ambiguous(_)
                    ) {
                        diagnostics.push(ResolutionDiagnostic {
                            code: "G3318",
                            span,
                            message: format!(
                                "public import alias `{alias}` is ambiguous in the exported {:?} namespace",
                                namespace
                            ),
                        });
                    }
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
            .filter(|import| !require_public || import.public)
            .filter(|import| import.glob || import.alias == alias)
        {
            // Preserve the original requester across every re-export hop.
            // Resolving a target as the facade module itself would grant its
            // local authority to callers and leak private modules/items.
            let state = if import.glob {
                match self.lexical_module(owner, requester, &import.path) {
                    ModuleLookup::Found(module) => {
                        self.resolve_member(namespace, &module, alias, requester, true, visited)
                    }
                    ModuleLookup::Ambiguous(modules) => self.ambiguous_modules(modules),
                    ModuleLookup::Inaccessible => ResolutionState::Inaccessible(vec![]),
                    ModuleLookup::Absent => ResolutionState::Unresolved,
                }
            } else {
                self.resolve_direct_path(namespace, owner, requester, &import.path, visited)
            };
            match state {
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
        if resolved.len() > 1 {
            ResolutionState::Ambiguous(resolved)
        } else if !ambiguous.is_empty() {
            ResolutionState::Ambiguous(ambiguous)
        } else if saw_inaccessible || !inaccessible.is_empty() {
            ResolutionState::Inaccessible(inaccessible)
        } else if resolved.len() == 1 {
            ResolutionState::Resolved(resolved[0])
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
        if path.len() == 1 {
            // Imports are source occurrences with the same lexical lookup
            // authority as bodies. A nested module may therefore import a
            // private item or alias introduced by an enclosing module; an
            // unrelated sibling still cannot obtain that capability because
            // the original requester is retained in every member lookup.
            let mut lexical = lexical_owner.clone();
            loop {
                let resolved = self.resolve_member(
                    namespace,
                    &lexical,
                    name,
                    requester,
                    !requester_has_lexical_authority(requester, &lexical),
                    visited,
                );
                if !matches!(resolved, ResolutionState::Unresolved) {
                    return resolved;
                }
                let Some(parent) = parent_module_path(&lexical.path) else {
                    break;
                };
                lexical.path = parent;
            }
            return ResolutionState::Unresolved;
        }
        let module = match self.lexical_module(lexical_owner, requester, &path[..path.len() - 1]) {
            ModuleLookup::Found(module) => module,
            ModuleLookup::Ambiguous(modules) => return self.ambiguous_modules(modules),
            ModuleLookup::Inaccessible => return ResolutionState::Inaccessible(vec![]),
            ModuleLookup::Absent => return ResolutionState::Unresolved,
        };
        self.resolve_member(
            namespace,
            &module,
            name,
            requester,
            !requester_has_lexical_authority(requester, &module),
            visited,
        )
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
            // Private declarations are lexical capabilities: the declaring
            // module and its descendants may use them, while siblings,
            // ancestors, and other packages may not.  This deliberately
            // mirrors `module_path_visible_to`, which already applies the
            // same descendant rule to private module edges.
            .filter(|entry| {
                owner.is_none_or(|owner| {
                    entry.public || requester_has_lexical_authority(owner, &entry.module)
                })
            })
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

    /// Preserve an ambiguity encountered while walking a module segment as a
    /// normal source-resolution ambiguity.  Module declarations have stable
    /// `DefKey`s just like value/type declarations, so callers and tooling do
    /// not have to reinterpret a missing path as a collision after the fact.
    fn ambiguous_modules(&self, modules: Vec<ModuleKey>) -> ResolutionState {
        let mut definitions = modules
            .iter()
            .flat_map(|module| self.module_definition_keys(module))
            .collect::<Vec<_>>();
        canonicalize_keys(&mut definitions);
        ResolutionState::Ambiguous(definitions)
    }

    fn module_definition_keys(&self, module: &ModuleKey) -> Vec<DefKey> {
        let Some(parent_path) = parent_module_path(&module.path) else {
            // Dependency-root ambiguity has no declaration in this package,
            // but remains an ambiguity rather than being downgraded to a
            // missing path.  The empty candidate list is intentionally only
            // possible for that root-level spelling.
            return vec![];
        };
        let Some(name) = module.path.rsplit("::").next() else {
            return vec![];
        };
        let parent = ModuleKey {
            package: module.package.clone(),
            path: parent_path,
        };
        self.qualified
            .get(&(DefinitionNamespace::Module, parent, name.to_owned()))
            .into_iter()
            .flatten()
            .map(|definition| definition.key)
            .collect()
    }

    fn lexical_module(
        &self,
        lexical_owner: &ModuleKey,
        requester: &ModuleKey,
        segments: &[String],
    ) -> ModuleLookup {
        self.lexical_module_with_visited(lexical_owner, requester, segments, &mut BTreeSet::new())
    }

    /// Resolve the module portion of a path.  This deliberately walks one
    /// segment at a time instead of formatting the whole suffix into a
    /// `ModuleKey`: an import alias is itself a module-path segment, and may
    /// appear after an ordinary module edge (`crate::facade::api::Thing`).
    /// The visited set is shared across alias expansion so cyclic re-exports
    /// remain a deterministic failed lookup rather than recursive resolver
    /// entry.
    fn lexical_module_with_visited(
        &self,
        lexical_owner: &ModuleKey,
        requester: &ModuleKey,
        segments: &[String],
        visited_aliases: &mut BTreeSet<ImportBinding>,
    ) -> ModuleLookup {
        let Some((first, rest)) = segments.split_first() else {
            return ModuleLookup::Absent;
        };
        if first == "crate" {
            let root = ModuleKey {
                package: lexical_owner.package.clone(),
                path: "crate".into(),
            };
            return self.walk_module_path(&root, requester, rest, visited_aliases);
        }
        if first == "self" {
            return self.walk_module_path(lexical_owner, requester, rest, visited_aliases);
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
            let parent = ModuleKey {
                package: lexical_owner.package.clone(),
                path: base,
            };
            return self.walk_module_path(&parent, requester, remaining, visited_aliases);
        }

        // Ordinary qualified paths are lexical.  Prefer the nearest enclosing
        // module that actually owns the requested child; this supports a
        // nested module referring to a sibling while keeping resolution
        // deterministic in the presence of similarly named descendants.
        let mut base = lexical_owner.path.clone();
        loop {
            let start = ModuleKey {
                package: lexical_owner.package.clone(),
                path: base.clone(),
            };
            match self.walk_module_path(&start, requester, segments, visited_aliases) {
                ModuleLookup::Found(module) => return ModuleLookup::Found(module),
                ModuleLookup::Ambiguous(modules) => return ModuleLookup::Ambiguous(modules),
                ModuleLookup::Inaccessible => return ModuleLookup::Inaccessible,
                ModuleLookup::Absent => {}
            }
            let Some(parent) = parent_module_path(&base) else {
                break;
            };
            base = parent;
        }

        // Select a dependency only from interfaces explicitly linked into
        // this index.  Ordinary lexical modules win a same-name tie, keeping
        // existing local path semantics stable.
        let Some(roots) = self.package_roots.get(first) else {
            return ModuleLookup::Absent;
        };
        let [root] = roots.as_slice() else {
            // An ambiguous package spelling must not pick an arbitrary
            // dependency by insertion order, nor silently pretend the
            // package is absent.
            return ModuleLookup::Ambiguous(roots.clone());
        };
        self.walk_module_path(root, requester, rest, visited_aliases)
    }

    /// Follow actual child-module edges and imported module bindings.  A
    /// child declaration shadows an import of the same spelling just as a
    /// local declaration shadows an imported final name.  In particular, an
    /// inaccessible child may not be bypassed through a conveniently named
    /// alias.
    fn walk_module_path(
        &self,
        start: &ModuleKey,
        requester: &ModuleKey,
        segments: &[String],
        visited_aliases: &mut BTreeSet<ImportBinding>,
    ) -> ModuleLookup {
        if !self.modules.contains_key(start) {
            return ModuleLookup::Absent;
        }
        if !self.module_path_visible_to(start, requester) {
            return ModuleLookup::Inaccessible;
        }
        let mut module = start.clone();
        for segment in segments {
            let child = ModuleKey {
                package: module.package.clone(),
                path: module_child_path(&module.path, segment),
            };
            if self.modules.contains_key(&child) {
                if !self.module_path_visible_to(&child, requester) {
                    return ModuleLookup::Inaccessible;
                }
                module = child;
                continue;
            }
            match self.imported_module(&module, requester, segment, visited_aliases) {
                ModuleLookup::Found(target) => module = target,
                ModuleLookup::Ambiguous(modules) => return ModuleLookup::Ambiguous(modules),
                ModuleLookup::Inaccessible => return ModuleLookup::Inaccessible,
                ModuleLookup::Absent => return ModuleLookup::Absent,
            }
        }
        ModuleLookup::Found(module)
    }

    /// Resolve an alias (or a module name made available by a glob) from the
    /// importing module.  The original requester is retained all the way
    /// through this lookup: a public facade cannot use its own private import
    /// authority to make a target traversable to another module or package.
    fn imported_module(
        &self,
        owner: &ModuleKey,
        requester: &ModuleKey,
        alias: &str,
        visited_aliases: &mut BTreeSet<ImportBinding>,
    ) -> ModuleLookup {
        let Some(imports) = self.imports.get(owner) else {
            return ModuleLookup::Absent;
        };
        let mut candidates = BTreeSet::new();
        let mut inaccessible = false;
        for import in imports {
            // A private import is lexical to its declaring module.  It must
            // not become a module edge for an outside requester merely
            // because the final imported definition happens to be public.
            if !import.public && !requester_has_lexical_authority(requester, &import.module) {
                if import.glob || import.alias == alias {
                    inaccessible = true;
                }
                continue;
            }
            if !import.glob && import.alias == alias {
                // Guard an active import *edge*, rather than the `(module,
                // alias)` spelling.  Several independently declared imports
                // may deliberately have the same alias; collapsing them here
                // would select the first sorted binding instead of preserving
                // the required ambiguity.  Removing the edge after exploring
                // it makes this a recursion stack, not a history cache.
                if !visited_aliases.insert(import.clone()) {
                    continue;
                }
                let lookup = self.lexical_module_with_visited(
                    &import.module,
                    requester,
                    &import.path,
                    visited_aliases,
                );
                visited_aliases.remove(import);
                match lookup {
                    ModuleLookup::Found(module) => {
                        candidates.insert(module);
                    }
                    ModuleLookup::Ambiguous(modules) => {
                        candidates.extend(modules);
                    }
                    ModuleLookup::Inaccessible => inaccessible = true,
                    ModuleLookup::Absent => {}
                }
                continue;
            }
            if import.glob {
                // As with explicit aliases, every glob edge contributes an
                // independent candidate.  This is important for qualified
                // module paths (`facade::api::Thing`) where two globs expose
                // the same module spelling.
                if !visited_aliases.insert(import.clone()) {
                    continue;
                }
                let target = self.lexical_module_with_visited(
                    &import.module,
                    requester,
                    &import.path,
                    visited_aliases,
                );
                match target {
                    ModuleLookup::Found(target) => match self.walk_module_path(
                        &target,
                        requester,
                        &[alias.to_owned()],
                        visited_aliases,
                    ) {
                        ModuleLookup::Found(module) => {
                            candidates.insert(module);
                        }
                        ModuleLookup::Ambiguous(modules) => {
                            candidates.extend(modules);
                        }
                        ModuleLookup::Inaccessible => inaccessible = true,
                        ModuleLookup::Absent => {}
                    },
                    ModuleLookup::Ambiguous(modules) => candidates.extend(modules),
                    ModuleLookup::Inaccessible => inaccessible = true,
                    ModuleLookup::Absent => {}
                };
                visited_aliases.remove(import);
            }
        }
        match candidates.len() {
            1 => ModuleLookup::Found(candidates.into_iter().next().expect("one candidate")),
            0 if inaccessible => ModuleLookup::Inaccessible,
            0 => ModuleLookup::Absent,
            _ => ModuleLookup::Ambiguous(candidates.into_iter().collect()),
        }
    }

    /// Every module edge on a qualified path is independently checked.  A
    /// private module is visible in the module that declared it and that
    /// module's descendants; it is not visible merely because a nested item
    /// happens to be `pub`.
    fn module_path_visible_to(&self, module: &ModuleKey, requester: &ModuleKey) -> bool {
        if module.package != requester.package {
            return self.module_path_is_public(module);
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

    fn module_member_names(
        &self,
        module: &ModuleKey,
        namespace: DefinitionNamespace,
        visited: &mut BTreeSet<(ModuleKey, DefinitionNamespace)>,
    ) -> BTreeSet<String> {
        if !visited.insert((module.clone(), namespace)) {
            return BTreeSet::new();
        }
        let mut names = self
            .qualified
            .keys()
            .filter(|(candidate_namespace, candidate_module, _)| {
                candidate_namespace == &namespace && candidate_module == module
            })
            .map(|(_, _, name)| name.clone())
            .collect::<BTreeSet<_>>();
        if let Some(imports) = self.imports.get(module) {
            for import in imports {
                if import.glob {
                    if let ModuleLookup::Found(target) =
                        self.lexical_module(module, module, &import.path)
                    {
                        names.extend(self.module_member_names(&target, namespace, visited));
                    }
                } else {
                    names.insert(import.alias.clone());
                }
            }
        }
        visited.remove(&(module.clone(), namespace));
        names
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum ModuleLookup {
    Found(ModuleKey),
    Ambiguous(Vec<ModuleKey>),
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

/// Private item and import authority is lexical rather than a property of a
/// spelling: a module may use declarations introduced by itself or any
/// enclosing module in the same package. Keeping this shared predicate for
/// direct definitions and imported module aliases prevents one namespace from
/// becoming more permissive than another.
fn requester_has_lexical_authority(requester: &ModuleKey, defining_module: &ModuleKey) -> bool {
    requester.package == defining_module.package
        && module_is_descendant_of(requester, &defining_module.path)
}

fn canonicalize_keys(keys: &mut Vec<DefKey>) {
    keys.sort();
    keys.dedup();
}

fn append_surface(output: &mut Vec<u8>, bytes: &[u8]) {
    output.extend_from_slice(&(bytes.len() as u64).to_le_bytes());
    output.extend_from_slice(bytes);
}

fn all_namespaces() -> [DefinitionNamespace; 6] {
    [
        DefinitionNamespace::Type,
        DefinitionNamespace::Value,
        DefinitionNamespace::Trait,
        DefinitionNamespace::Effect,
        DefinitionNamespace::Module,
        DefinitionNamespace::Operator,
    ]
}

fn canonicalize_diagnostics(diagnostics: &mut Vec<ResolutionDiagnostic>) {
    diagnostics.sort_by(|left, right| {
        (left.code, left.span, &left.message).cmp(&(right.code, right.span, &right.message))
    });
    diagnostics.dedup();
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

    /// Add the import-site occurrences owned by an immutable definition
    /// index.  Clients that build a revision reference index therefore do not
    /// need a separate, alias-blind import walk.
    pub fn record_imports(&mut self, definitions: &DefinitionIndex) {
        for occurrence in definitions.import_occurrences() {
            self.record(occurrence);
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
