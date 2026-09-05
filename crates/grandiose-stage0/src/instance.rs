//! Canonical, demand-driven generic instance identity and reachability.
//!
//! This is deliberately independent of MIR emission.  Discovery first proves
//! that an executable substitution is closed and gives it a stable identity;
//! a later lowering query may then materialize the body without making cache
//! keys depend on traversal order or body-local inference variables.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use crate::{
    ConstKind, DefKey, Digest, EffectRow, EffectTail, GenericArgument, GenericKind, InferContext,
    Lifetime, Quantity, Type, TypeError,
};

/// Executable instance arguments use the one canonical generic vocabulary.
/// The alias keeps the instance API readable while ensuring declaration,
/// solver, effect, and specialization identities cannot drift into parallel
/// representations.
pub type InstanceArgument = GenericArgument;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InstanceKeyError {
    Arity { expected: usize, found: usize },
    Kind { slot: usize, expected: GenericKind },
    UnresolvedType { slot: usize, error: TypeError },
    OpenEffectRow { slot: usize },
    NonConcreteType { slot: usize },
    NonConcreteLifetime { slot: usize },
    NonConcreteConst { slot: usize },
}

/// A stable executable specialization identity. The private canonical bytes
/// retain the full substitution identity while avoiding `Ord` implementations
/// on semantic type trees solely for work-queue ordering.
#[derive(Clone, Debug)]
pub struct InstanceKey {
    pub callable: DefKey,
    arguments: Vec<InstanceArgument>,
    canonical_substitution: Vec<u8>,
    /// The greatest structural depth of any substituted generic argument.
    /// This is derived from the canonical argument tree, never source spans
    /// or inference state, so resource policy cannot perturb identity.
    substitution_depth: usize,
    fingerprint: Digest,
}

impl InstanceKey {
    pub fn new(
        callable: DefKey,
        kinds: &[GenericKind],
        arguments: Vec<InstanceArgument>,
    ) -> Result<Self, InstanceKeyError> {
        // A closed structural `u32` term has the same executable meaning as
        // its literal result.  Normalize it before both key construction and
        // publication so source spelling cannot create two monomorphizations
        // of the same instance (`f<1 + 2>` versus `f<3>`).
        let arguments = arguments
            .into_iter()
            .map(normalize_instance_argument)
            .collect::<Vec<_>>();
        if kinds.len() != arguments.len() {
            return Err(InstanceKeyError::Arity {
                expected: kinds.len(),
                found: arguments.len(),
            });
        }
        let mut canonical_substitution = Vec::new();
        canonical_substitution.extend_from_slice(&(arguments.len() as u64).to_le_bytes());
        for (slot, (kind, argument)) in kinds.iter().zip(&arguments).enumerate() {
            match (kind, argument) {
                (GenericKind::Type, InstanceArgument::Type(value)) => {
                    let fingerprint = closed_type_fingerprint(value, slot)?;
                    canonical_substitution.push(0);
                    canonical_substitution.extend_from_slice(&fingerprint.as_bytes());
                }
                (GenericKind::EffectRow, InstanceArgument::EffectRow(value)) => {
                    let fingerprint = closed_effect_row_fingerprint(value, slot)?;
                    canonical_substitution.push(1);
                    canonical_substitution.extend_from_slice(&fingerprint.as_bytes());
                }
                (GenericKind::Lifetime, InstanceArgument::Lifetime(value)) => {
                    // Borrow checking has already fixed an elided region at
                    // this boundary. The VM erases regions, but instance
                    // identity still records the resolved source lifetime so
                    // it can materialize a method body instead of retaining
                    // its declaration-local generic effect metadata.
                    if !matches!(
                        value,
                        Lifetime::Static | Lifetime::Elided | Lifetime::Bound { .. }
                    ) {
                        return Err(InstanceKeyError::NonConcreteLifetime { slot });
                    }
                    canonical_substitution.push(2);
                    encode_lifetime(*value, &mut canonical_substitution);
                }
                (GenericKind::Const(ConstKind::U32), InstanceArgument::ConstU32(value)) => {
                    canonical_substitution.push(3);
                    canonical_substitution.extend_from_slice(&value.to_le_bytes());
                }
                (GenericKind::Const(ConstKind::U32), InstanceArgument::ConstU32Expr(_)) => {
                    return Err(InstanceKeyError::NonConcreteConst { slot });
                }
                (GenericKind::Const(_), InstanceArgument::ConstInfer { .. }) => {
                    return Err(InstanceKeyError::NonConcreteConst { slot });
                }
                (
                    GenericKind::Const(ConstKind::Quantity),
                    InstanceArgument::ConstQuantity(value),
                ) => {
                    canonical_substitution.push(4);
                    encode_quantity(*value, &mut canonical_substitution);
                }
                (expected, _) => {
                    return Err(InstanceKeyError::Kind {
                        slot,
                        expected: *expected,
                    });
                }
            }
        }
        let fingerprint = Digest::of_parts([
            b"grandiose-stage0-instance-key-v1".as_slice(),
            callable.0.as_bytes().as_slice(),
            canonical_substitution.as_slice(),
        ]);
        Ok(Self {
            callable,
            substitution_depth: arguments
                .iter()
                .map(instance_argument_depth)
                .max()
                .unwrap_or(0),
            arguments,
            canonical_substitution,
            fingerprint,
        })
    }

    pub fn arguments(&self) -> &[InstanceArgument] {
        &self.arguments
    }

    pub fn fingerprint(&self) -> Digest {
        self.fingerprint
    }

    /// The maximum nesting depth in this executable substitution.
    ///
    /// This covers every generic kind, including type arguments nested inside
    /// effect instances and effect rows nested in nominal applications. It is
    /// intentionally separate from the key fingerprint: changing a host
    /// resource limit must not change a program's canonical instance identity.
    pub fn substitution_depth(&self) -> usize {
        self.substitution_depth
    }
}

fn nested_depth(values: impl IntoIterator<Item = usize>) -> usize {
    1 + values.into_iter().max().unwrap_or(0)
}

fn instance_argument_depth(value: &InstanceArgument) -> usize {
    match value {
        InstanceArgument::Type(value) => type_depth(value),
        InstanceArgument::EffectRow(value) => effect_row_depth(value),
        InstanceArgument::Lifetime(_)
        | InstanceArgument::ConstU32(_)
        | InstanceArgument::ConstQuantity(_)
        | InstanceArgument::ConstGeneric { .. }
        | InstanceArgument::ConstInfer { .. } => 1,
        InstanceArgument::ConstU32Expr(value) => structural_u32_depth(value),
        InstanceArgument::ConstProjection {
            subject,
            trait_arguments,
            ..
        } => nested_depth(
            std::iter::once(type_depth(subject))
                .chain(trait_arguments.iter().map(instance_argument_depth)),
        ),
    }
}

fn structural_u32_depth(value: &crate::StructuralU32Expr) -> usize {
    match value {
        crate::StructuralU32Expr::Literal(_) | crate::StructuralU32Expr::Param(_) => 1,
        crate::StructuralU32Expr::Add(left, right)
        | crate::StructuralU32Expr::Sub(left, right)
        | crate::StructuralU32Expr::Mul(left, right)
        | crate::StructuralU32Expr::Div(left, right)
        | crate::StructuralU32Expr::Rem(left, right) => {
            nested_depth([structural_u32_depth(left), structural_u32_depth(right)])
        }
    }
}

fn effect_instance_depth(value: &crate::EffectInstance) -> usize {
    nested_depth(value.arguments.iter().map(instance_argument_depth))
}

fn effect_projection_depth(value: &crate::EffectRowProjection) -> usize {
    nested_depth(
        std::iter::once(type_depth(&value.subject))
            .chain(value.trait_arguments.iter().map(instance_argument_depth))
            .chain(value.item_arguments.iter().map(instance_argument_depth)),
    )
}

fn effect_row_depth(value: &EffectRow) -> usize {
    nested_depth(
        value
            .effects
            .iter()
            .map(effect_instance_depth)
            .chain(value.projections.iter().map(effect_projection_depth)),
    )
}

fn type_depth(value: &Type) -> usize {
    match value {
        Type::Nominal { arguments, .. } => {
            nested_depth(arguments.iter().map(instance_argument_depth))
        }
        Type::Projection {
            subject,
            trait_arguments,
            item_arguments,
            ..
        } => nested_depth(
            std::iter::once(type_depth(subject))
                .chain(trait_arguments.iter().map(instance_argument_depth))
                .chain(item_arguments.iter().map(instance_argument_depth)),
        ),
        Type::Tuple(values) => nested_depth(values.iter().map(type_depth)),
        Type::Array(value) | Type::StaticData { element: value, .. } => {
            nested_depth([type_depth(value)])
        }
        Type::Reference { referent, .. }
        | Type::RawPointer { pointee: referent, .. } => nested_depth([type_depth(referent)]),
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => nested_depth(
            parameters
                .iter()
                .map(type_depth)
                .chain(std::iter::once(type_depth(result)))
                .chain(std::iter::once(effect_row_depth(effects))),
        ),
        Type::Unit
        | Type::Never
        | Type::Scalar(_)
        | Type::ConstU32(_)
        | Type::ConstQuantity(_)
        | Type::ConstGeneric { .. }
        | Type::Generic(_)
        | Type::Infer(_)
        | Type::Error => 1,
    }
}

fn normalize_instance_argument(argument: InstanceArgument) -> InstanceArgument {
    match argument {
        InstanceArgument::ConstU32Expr(value) => match value.clone().normalized() {
            Ok(crate::StructuralU32Expr::Literal(value)) => InstanceArgument::ConstU32(value),
            Ok(value) => InstanceArgument::ConstU32Expr(value),
            Err(_) => InstanceArgument::ConstU32Expr(value),
        },
        argument => argument,
    }
}

impl PartialEq for InstanceKey {
    fn eq(&self, other: &Self) -> bool {
        self.callable == other.callable
            && self.canonical_substitution == other.canonical_substitution
    }
}

impl Eq for InstanceKey {}

impl std::hash::Hash for InstanceKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        std::hash::Hash::hash(&self.callable, state);
        std::hash::Hash::hash(&self.canonical_substitution, state);
    }
}

impl Ord for InstanceKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.callable.cmp(&other.callable).then_with(|| {
            self.canonical_substitution
                .cmp(&other.canonical_substitution)
        })
    }
}

impl PartialOrd for InstanceKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

fn closed_type_fingerprint(value: &Type, slot: usize) -> Result<Digest, InstanceKeyError> {
    if !is_concrete_type(value) {
        return Err(InstanceKeyError::NonConcreteType { slot });
    }
    InferContext::default()
        .type_fingerprint(value.clone())
        .map_err(|error| InstanceKeyError::UnresolvedType { slot, error })
}

fn closed_effect_row_fingerprint(
    value: &EffectRow,
    slot: usize,
) -> Result<Digest, InstanceKeyError> {
    if value.tail.is_some() || !value.projections.is_empty() {
        return Err(InstanceKeyError::OpenEffectRow { slot });
    }
    let wrapper = Type::Callable {
        safety: crate::Safety::Safe,
        lifetime_binders: 0,
        parameters: vec![],
        result: Box::new(Type::Unit),
        effects: value.clone(),
        invocation: Quantity::ONCE,
    };
    closed_type_fingerprint(&wrapper, slot)
}

fn is_concrete_type(value: &Type) -> bool {
    match value {
        Type::Generic(_) | Type::ConstGeneric { .. } | Type::Infer(_) | Type::Error => false,
        Type::Nominal { arguments, .. } => arguments.iter().all(is_concrete_generic_argument),
        Type::Tuple(arguments) => arguments.iter().all(is_concrete_type),
        Type::Projection { .. } => false,
        Type::Array(element) | Type::StaticData { element, .. }
        | Type::RawPointer { pointee: element, .. } => is_concrete_type(element),
        Type::Reference {
            lifetime, referent, ..
        } => {
            matches!(
                lifetime,
                Lifetime::Static | Lifetime::Elided | Lifetime::Bound { .. }
            )
                && is_concrete_type(referent)
        }
        Type::Callable {
            parameters,
            result,
            effects,
            ..
        } => {
            parameters.iter().all(is_concrete_type)
                && is_concrete_type(result)
                && effects.tail.is_none()
                && effects.projections.is_empty()
                && effects
                    .effects
                    .iter()
                    .all(|effect| effect.arguments.iter().all(is_concrete_generic_argument))
        }
        Type::Unit | Type::Never | Type::Scalar(_) | Type::ConstU32(_) | Type::ConstQuantity(_) => {
            true
        }
    }
}

fn is_concrete_generic_argument(value: &GenericArgument) -> bool {
    match value {
        GenericArgument::Type(value) => is_concrete_type(value),
        GenericArgument::EffectRow(value) => {
            value.tail.is_none()
                && value.projections.is_empty()
                && value
                    .effects
                    .iter()
                    .all(|effect| effect.arguments.iter().all(is_concrete_generic_argument))
        }
        GenericArgument::Lifetime(value) => {
            matches!(
                value,
                Lifetime::Static | Lifetime::Elided | Lifetime::Bound { .. }
            )
        }
        GenericArgument::ConstU32(_) | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::ConstU32Expr(_) => false,
        GenericArgument::ConstGeneric { .. }
        | GenericArgument::ConstProjection { .. }
        | GenericArgument::ConstInfer { .. } => false,
    }
}

fn encode_lifetime(value: Lifetime, output: &mut Vec<u8>) {
    match value {
        Lifetime::Static => output.push(0),
        Lifetime::Bound { depth, index } => {
            output.push(1);
            output.extend_from_slice(&depth.to_le_bytes());
            output.extend_from_slice(&index.to_le_bytes());
        }
        Lifetime::Elided => output.push(2),
        Lifetime::Generic(_) => unreachable!("validated concrete lifetime"),
    }
}

fn encode_quantity(value: Quantity, output: &mut Vec<u8>) {
    output.extend_from_slice(&value.lower.to_le_bytes());
    match value.upper {
        Some(upper) => {
            output.push(0);
            output.extend_from_slice(&upper.to_le_bytes());
        }
        None => output.push(1),
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct InstanceLimits {
    pub total: usize,
    pub per_definition: usize,
    /// Maximum structural nesting of one fully closed generic substitution.
    /// This prevents a single instance key such as `Wrap<Wrap<...>>` from
    /// consuming unbounded solver, fingerprinting, and materialization work
    /// while staying below the cardinality limits.
    pub substitution_depth: usize,
}

impl Default for InstanceLimits {
    fn default() -> Self {
        Self {
            total: 10_000,
            per_definition: 1_000,
            substitution_depth: 128,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct InstanceRoot {
    pub key: InstanceKey,
    pub reason: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InstanceGraphError {
    UnknownCaller {
        caller: Box<InstanceKey>,
    },
    TotalLimit {
        limit: usize,
        root: Box<InstanceKey>,
    },
    PerDefinitionLimit {
        callable: DefKey,
        limit: usize,
        root: Box<InstanceKey>,
    },
    SubstitutionDepth {
        depth: usize,
        limit: usize,
        root: Box<InstanceKey>,
    },
}

/// Deterministic demand queue. Recursive discovery reuses the existing node,
/// leaving SCC calculation to a later graph pass instead of recursively
/// cloning a body.
#[derive(Clone, Debug, Default)]
pub struct InstanceGraph {
    roots: BTreeMap<InstanceKey, String>,
    edges: BTreeMap<InstanceKey, BTreeSet<InstanceKey>>,
    pending: BTreeSet<InstanceKey>,
    /// Admitted instances grouped by their source callable. This is a
    /// resource-accounting index rather than part of instance identity: it
    /// lets the per-definition policy remain transactional without rescanning
    /// the complete graph on every discovered callee.
    instances_per_callable: BTreeMap<DefKey, usize>,
}

impl InstanceGraph {
    pub fn discover_root(
        &mut self,
        root: InstanceRoot,
        limits: InstanceLimits,
    ) -> Result<bool, InstanceGraphError> {
        self.insert(root.key, Some(root.reason), limits)
    }

    pub fn discover_callee(
        &mut self,
        caller: &InstanceKey,
        callee: InstanceKey,
        limits: InstanceLimits,
    ) -> Result<bool, InstanceGraphError> {
        if !self.edges.contains_key(caller) {
            return Err(InstanceGraphError::UnknownCaller {
                caller: Box::new(caller.clone()),
            });
        }
        // Insert before publishing the edge. A rejected specialization must
        // leave the graph unchanged, otherwise a later retry could observe an
        // unvalidated callee that was never admitted by the resource policy.
        let inserted = self.insert(callee.clone(), None, limits)?;
        self.edges
            .entry(caller.clone())
            .or_default()
            .insert(callee.clone());
        Ok(inserted)
    }

    fn insert(
        &mut self,
        key: InstanceKey,
        reason: Option<String>,
        limits: InstanceLimits,
    ) -> Result<bool, InstanceGraphError> {
        if self.edges.contains_key(&key) {
            if let Some(reason) = reason {
                self.roots.entry(key).or_insert(reason);
            }
            return Ok(false);
        }
        if key.substitution_depth() > limits.substitution_depth {
            return Err(InstanceGraphError::SubstitutionDepth {
                depth: key.substitution_depth(),
                limit: limits.substitution_depth,
                root: Box::new(key),
            });
        }
        if self.edges.len() >= limits.total {
            return Err(InstanceGraphError::TotalLimit {
                limit: limits.total,
                root: Box::new(key),
            });
        }
        let count = self
            .instances_per_callable
            .get(&key.callable)
            .copied()
            .unwrap_or(0);
        if count >= limits.per_definition {
            return Err(InstanceGraphError::PerDefinitionLimit {
                callable: key.callable,
                limit: limits.per_definition,
                root: Box::new(key),
            });
        }
        if let Some(reason) = reason {
            self.roots.insert(key.clone(), reason);
        }
        self.pending.insert(key.clone());
        *self.instances_per_callable.entry(key.callable).or_default() += 1;
        self.edges.insert(key, BTreeSet::new());
        Ok(true)
    }

    pub fn pop_pending(&mut self) -> Option<InstanceKey> {
        let key = self.pending.pop_first()?;
        Some(key)
    }

    pub fn roots(&self) -> &BTreeMap<InstanceKey, String> {
        &self.roots
    }

    pub fn callees(&self, key: &InstanceKey) -> Option<&BTreeSet<InstanceKey>> {
        self.edges.get(key)
    }

    pub fn ordered(&self) -> Vec<InstanceKey> {
        self.edges.keys().cloned().collect()
    }

    pub fn breadth_first_from_roots(&self) -> Vec<InstanceKey> {
        let mut seen = BTreeSet::new();
        let mut queue = self.roots.keys().cloned().collect::<VecDeque<_>>();
        let mut ordered = vec![];
        while let Some(key) = queue.pop_front() {
            if !seen.insert(key.clone()) {
                continue;
            }
            ordered.push(key.clone());
            if let Some(callees) = self.edges.get(&key) {
                queue.extend(callees.iter().cloned());
            }
        }
        ordered
    }

    pub fn strongly_connected_components(&self) -> Vec<Vec<InstanceKey>> {
        struct Tarjan<'graph> {
            graph: &'graph InstanceGraph,
            index: usize,
            stack: Vec<InstanceKey>,
            on_stack: BTreeSet<InstanceKey>,
            ids: BTreeMap<InstanceKey, usize>,
            low: BTreeMap<InstanceKey, usize>,
            components: Vec<Vec<InstanceKey>>,
        }
        impl Tarjan<'_> {
            fn visit(&mut self, key: InstanceKey) {
                self.ids.insert(key.clone(), self.index);
                self.low.insert(key.clone(), self.index);
                self.index += 1;
                self.stack.push(key.clone());
                self.on_stack.insert(key.clone());
                for callee in self.graph.callees(&key).into_iter().flatten() {
                    if !self.ids.contains_key(callee) {
                        self.visit(callee.clone());
                        *self.low.get_mut(&key).expect("current key has lowlink") =
                            self.low[&key].min(self.low[callee]);
                    } else if self.on_stack.contains(callee) {
                        *self.low.get_mut(&key).expect("current key has lowlink") =
                            self.low[&key].min(self.ids[callee]);
                    }
                }
                if self.low[&key] == self.ids[&key] {
                    let mut component = vec![];
                    loop {
                        let member = self.stack.pop().expect("root owns a stack member");
                        self.on_stack.remove(&member);
                        let complete = member == key;
                        component.push(member);
                        if complete {
                            break;
                        }
                    }
                    component.sort();
                    self.components.push(component);
                }
            }
        }
        let mut tarjan = Tarjan {
            graph: self,
            index: 0,
            stack: vec![],
            on_stack: BTreeSet::new(),
            ids: BTreeMap::new(),
            low: BTreeMap::new(),
            components: vec![],
        };
        for key in self.ordered() {
            if !tarjan.ids.contains_key(&key) {
                tarjan.visit(key);
            }
        }
        tarjan
            .components
            .sort_by(|left, right| left[0].cmp(&right[0]));
        tarjan.components
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CallSummary {
    pub effects: EffectRow,
    /// The quantity with which this callable may be invoked by its owner.
    pub invocation: Quantity,
    /// Per-parameter quantitative ownership facts.  Slot `i` describes uses
    /// of parameter `i` in the summarized body; an empty vector means the
    /// producer has no parameter evidence, rather than that every parameter
    /// is unused.
    pub argument_uses: Vec<Quantity>,
    pub may_abort: bool,
    pub may_control: bool,
    /// At least one path can discard a suspended continuation.  This is kept
    /// separate from `may_abort`: cancellation is a checked ownership action,
    /// while an abort need not own a handler continuation.
    pub may_cancel: bool,
    /// At least one path resumes or forwards a suspended continuation.
    pub may_resume: bool,
    pub may_escape: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct SummaryLimits {
    /// A bounded summary solver cannot publish a partially stabilized SCC.
    /// The default is deliberately generous for finite structural summaries;
    /// callers that expose this as a request resource can lower it.
    pub iterations_per_scc: usize,
}

impl Default for SummaryLimits {
    fn default() -> Self {
        Self {
            iterations_per_scc: 10_000,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum SummaryError {
    IncompatibleEffectTails {
        left: EffectTail,
        right: EffectTail,
    },
    DidNotConverge {
        component: Vec<InstanceKey>,
        limit: usize,
    },
    IncompatibleArgumentArity {
        left: usize,
        right: usize,
    },
    InvalidArgumentMapping {
        callee_slot: usize,
        caller_slot: usize,
        caller_arity: usize,
    },
    QuantityOverflow,
}

impl Default for CallSummary {
    fn default() -> Self {
        Self {
            effects: EffectRow::empty(),
            invocation: Quantity::ZERO,
            argument_uses: vec![],
            may_abort: false,
            may_control: false,
            may_cancel: false,
            may_resume: false,
            may_escape: false,
        }
    }
}
impl CallSummary {
    fn join_effects(left: &EffectRow, right: &EffectRow) -> Result<EffectRow, SummaryError> {
        let tail = match (left.tail, right.tail) {
            (Some(left), Some(right)) if left != right => {
                return Err(SummaryError::IncompatibleEffectTails { left, right });
            }
            (Some(tail), _) | (_, Some(tail)) => Some(tail),
            (None, None) => None,
        };
        let mut effects = left.clone();
        effects.effects.extend(right.effects.iter().cloned());
        effects
            .projections
            .extend(right.projections.iter().cloned());
        effects.tail = tail;
        effects.canonicalize();
        Ok(effects)
    }

    fn join_argument_uses(&self, other: &Self) -> Result<Vec<Quantity>, SummaryError> {
        // The default bottom summary intentionally has no arity.  Treat it as
        // an identity so SCC seeds cannot erase a body's ownership facts.
        if self.argument_uses.is_empty() {
            return Ok(other.argument_uses.clone());
        }
        if other.argument_uses.is_empty() {
            return Ok(self.argument_uses.clone());
        }
        if self.argument_uses.len() != other.argument_uses.len() {
            return Err(SummaryError::IncompatibleArgumentArity {
                left: self.argument_uses.len(),
                right: other.argument_uses.len(),
            });
        }
        Ok(self
            .argument_uses
            .iter()
            .zip(&other.argument_uses)
            .map(|(left, right)| left.branch_hull(*right))
            .collect())
    }

    /// Join alternative paths while preserving every monotone semantic fact.
    /// This is the SCC lattice operation used by `solve_call_summaries`.
    pub fn join(&self, other: &Self) -> Result<Self, SummaryError> {
        Ok(Self {
            effects: Self::join_effects(&self.effects, &other.effects)?,
            invocation: self.invocation.branch_hull(other.invocation),
            argument_uses: self.join_argument_uses(other)?,
            may_abort: self.may_abort || other.may_abort,
            may_control: self.may_control || other.may_control,
            may_cancel: self.may_cancel || other.may_cancel,
            may_resume: self.may_resume || other.may_resume,
            may_escape: self.may_escape || other.may_escape,
        })
    }

    /// Compose a direct callee summary into this body using the frozen mapping
    /// from callee parameter slots to this body's parameter slots.  This is
    /// deliberately not an unqualified vector zip: a generic call can reorder
    /// arguments, duplicate an argument, or call with a locally-created value.
    /// Bad or stale metadata is rejected before it can be published as an
    /// interprocedural ownership fact.
    pub fn compose_callee(
        &self,
        callee: &Self,
        callee_to_caller: &[Option<usize>],
    ) -> Result<Self, SummaryError> {
        if callee_to_caller.len() != callee.argument_uses.len() {
            return Err(SummaryError::IncompatibleArgumentArity {
                left: callee_to_caller.len(),
                right: callee.argument_uses.len(),
            });
        }
        let mut argument_uses = self.argument_uses.clone();
        for (callee_slot, (use_quantity, caller_slot)) in callee
            .argument_uses
            .iter()
            .zip(callee_to_caller)
            .enumerate()
        {
            let Some(caller_slot) = caller_slot else {
                // The argument originated in a local, constant, or capture;
                // it carries no caller-parameter ownership fact.
                continue;
            };
            let Some(existing) = argument_uses.get_mut(*caller_slot) else {
                return Err(SummaryError::InvalidArgumentMapping {
                    callee_slot,
                    caller_slot: *caller_slot,
                    caller_arity: argument_uses.len(),
                });
            };
            *existing = existing
                .sequence(*use_quantity)
                .map_err(|_| SummaryError::QuantityOverflow)?;
        }
        Ok(Self {
            effects: Self::join_effects(&self.effects, &callee.effects)?,
            invocation: self
                .invocation
                .multiply(callee.invocation)
                .map_err(|_| SummaryError::QuantityOverflow)?,
            argument_uses,
            may_abort: self.may_abort || callee.may_abort,
            may_control: self.may_control || callee.may_control,
            may_cancel: self.may_cancel || callee.may_cancel,
            may_resume: self.may_resume || callee.may_resume,
            may_escape: self.may_escape || callee.may_escape,
        })
    }
}

pub fn solve_call_summaries(
    graph: &InstanceGraph,
    limits: SummaryLimits,
    mut transfer: impl FnMut(&InstanceKey, &BTreeMap<InstanceKey, CallSummary>) -> CallSummary,
) -> Result<BTreeMap<InstanceKey, CallSummary>, SummaryError> {
    let mut summaries = BTreeMap::new();
    for scc in graph.strongly_connected_components() {
        for key in &scc {
            summaries
                .entry(key.clone())
                .or_insert_with(CallSummary::default);
        }
        let mut converged = false;
        for _ in 0..limits.iterations_per_scc {
            let mut changed = false;
            for key in &scc {
                let next = summaries[key].join(&transfer(key, &summaries))?;
                if next != summaries[key] {
                    summaries.insert(key.clone(), next);
                    changed = true;
                }
            }
            if !changed {
                converged = true;
                break;
            }
        }
        if !converged {
            return Err(SummaryError::DidNotConverge {
                component: scc,
                limit: limits.iterations_per_scc,
            });
        }
    }
    Ok(summaries)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Digest, EffectTail, ScalarType, StructuralU32Expr};

    fn definition(name: &[u8]) -> DefKey {
        DefKey(Digest::of_bytes(name))
    }

    #[test]
    fn equivalent_instances_have_stable_identity_and_queue_order() {
        let kinds = [GenericKind::Type, GenericKind::Const(ConstKind::Quantity)];
        let left = InstanceKey::new(
            definition(b"id"),
            &kinds,
            vec![
                InstanceArgument::Type(Type::Scalar(ScalarType::I64)),
                InstanceArgument::ConstQuantity(Quantity::AFFINE),
            ],
        )
        .unwrap();
        let right = InstanceKey::new(
            definition(b"id"),
            &kinds,
            vec![
                InstanceArgument::Type(Type::Scalar(ScalarType::I64)),
                InstanceArgument::ConstQuantity(Quantity::AFFINE),
            ],
        )
        .unwrap();
        assert_eq!(left, right);
        assert_eq!(left.fingerprint(), right.fingerprint());

        let mut graph = InstanceGraph::default();
        assert!(
            graph
                .discover_root(
                    InstanceRoot {
                        key: left.clone(),
                        reason: "entry".into()
                    },
                    InstanceLimits::default(),
                )
                .unwrap()
        );
        assert!(
            !graph
                .discover_root(
                    InstanceRoot {
                        key: right,
                        reason: "duplicate".into()
                    },
                    InstanceLimits::default(),
                )
                .unwrap()
        );
        assert_eq!(graph.pop_pending(), Some(left));
        assert_eq!(graph.pop_pending(), None);
    }

    #[test]
    fn elided_lifetimes_are_closed_distinct_vm_instance_identities() {
        let kinds = [GenericKind::Lifetime];
        let elided = InstanceKey::new(
            definition(b"region-sensitive"),
            &kinds,
            vec![InstanceArgument::Lifetime(Lifetime::Elided)],
        )
        .expect("an elided VM-erased region is executable metadata");
        let static_lifetime = InstanceKey::new(
            definition(b"region-sensitive"),
            &kinds,
            vec![InstanceArgument::Lifetime(Lifetime::Static)],
        )
        .unwrap();
        assert_ne!(elided, static_lifetime);
        assert_ne!(elided.fingerprint(), static_lifetime.fingerprint());
    }

    #[test]
    fn distinct_closed_substitutions_cannot_share_an_executable_identity() {
        let kinds = [GenericKind::Type, GenericKind::Const(ConstKind::U32)];
        let i64 = InstanceKey::new(
            definition(b"identity"),
            &kinds,
            vec![
                InstanceArgument::Type(Type::Scalar(ScalarType::I64)),
                InstanceArgument::ConstU32(1),
            ],
        )
        .unwrap();
        let text = InstanceKey::new(
            definition(b"identity"),
            &kinds,
            vec![
                InstanceArgument::Type(Type::Scalar(ScalarType::Text)),
                InstanceArgument::ConstU32(1),
            ],
        )
        .unwrap();
        let different_const = InstanceKey::new(
            definition(b"identity"),
            &kinds,
            vec![
                InstanceArgument::Type(Type::Scalar(ScalarType::I64)),
                InstanceArgument::ConstU32(2),
            ],
        )
        .unwrap();
        assert_ne!(i64, text);
        assert_ne!(i64, different_const);
        assert_ne!(i64.fingerprint(), text.fingerprint());
        assert_ne!(i64.fingerprint(), different_const.fingerprint());

        let effect_kinds = [GenericKind::EffectRow];
        let first_effect = InstanceKey::new(
            definition(b"effectful"),
            &effect_kinds,
            vec![InstanceArgument::EffectRow(EffectRow::closed_instances([
                crate::EffectInstance {
                    definition: definition(b"first-effect"),
                    arguments: vec![],
                },
            ]))],
        )
        .unwrap();
        let second_effect = InstanceKey::new(
            definition(b"effectful"),
            &effect_kinds,
            vec![InstanceArgument::EffectRow(EffectRow::closed_instances([
                crate::EffectInstance {
                    definition: definition(b"second-effect"),
                    arguments: vec![],
                },
            ]))],
        )
        .unwrap();
        assert_ne!(first_effect, second_effect);
        assert_ne!(first_effect.fingerprint(), second_effect.fingerprint());
    }

    #[test]
    fn executable_instances_reject_open_or_body_local_terms() {
        let generic = InstanceKey::new(
            definition(b"id"),
            &[GenericKind::Type],
            vec![InstanceArgument::Type(Type::Generic(0))],
        );
        assert!(matches!(
            generic,
            Err(InstanceKeyError::NonConcreteType { .. })
        ));

        let open_row = InstanceKey::new(
            definition(b"effect"),
            &[GenericKind::EffectRow],
            vec![InstanceArgument::EffectRow(EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(EffectTail::Generic(0)),
            })],
        );
        assert!(matches!(
            open_row,
            Err(InstanceKeyError::OpenEffectRow { .. })
        ));

        let symbolic_const = InstanceKey::new(
            definition(b"count"),
            &[GenericKind::Const(ConstKind::U32)],
            vec![InstanceArgument::ConstU32Expr(StructuralU32Expr::Param(0))],
        );
        assert!(matches!(
            symbolic_const,
            Err(InstanceKeyError::NonConcreteConst { .. })
        ));
    }

    #[test]
    fn closed_structural_u32_arguments_share_the_literal_instance() {
        let kinds = [GenericKind::Const(ConstKind::U32)];
        let structural = InstanceKey::new(
            definition(b"count"),
            &kinds,
            vec![InstanceArgument::ConstU32Expr(StructuralU32Expr::Add(
                Box::new(StructuralU32Expr::Literal(1)),
                Box::new(StructuralU32Expr::Literal(2)),
            ))],
        )
        .unwrap();
        let literal = InstanceKey::new(
            definition(b"count"),
            &kinds,
            vec![InstanceArgument::ConstU32(3)],
        )
        .unwrap();

        assert_eq!(structural, literal);
        assert_eq!(structural.arguments(), &[InstanceArgument::ConstU32(3)]);
    }

    #[test]
    fn graph_preserves_recursive_edges_without_duplicate_instances() {
        let kinds = [GenericKind::Type];
        let first = InstanceKey::new(
            definition(b"first"),
            &kinds,
            vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .unwrap();
        let second = InstanceKey::new(
            definition(b"second"),
            &kinds,
            vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .unwrap();
        let mut graph = InstanceGraph::default();
        let limits = InstanceLimits::default();
        graph
            .discover_root(
                InstanceRoot {
                    key: first.clone(),
                    reason: "entry".into(),
                },
                limits,
            )
            .unwrap();
        graph
            .discover_callee(&first, second.clone(), limits)
            .unwrap();
        assert!(
            !graph
                .discover_callee(&second, first.clone(), limits)
                .unwrap()
        );
        assert_eq!(graph.breadth_first_from_roots(), vec![first, second]);
    }

    #[test]
    fn discovery_is_transactional_and_requires_an_admitted_caller() {
        let kinds = [GenericKind::Type];
        let first = InstanceKey::new(
            definition(b"first"),
            &kinds,
            vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .unwrap();
        let second = InstanceKey::new(
            definition(b"second"),
            &kinds,
            vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .unwrap();
        let mut graph = InstanceGraph::default();
        assert!(matches!(
            graph.discover_callee(&first, second.clone(), InstanceLimits::default()),
            Err(InstanceGraphError::UnknownCaller { .. })
        ));
        graph
            .discover_root(
                InstanceRoot {
                    key: first.clone(),
                    reason: "entry".into(),
                },
                InstanceLimits {
                    total: 1,
                    per_definition: 1,
                    ..InstanceLimits::default()
                },
            )
            .unwrap();
        assert!(matches!(
            graph.discover_callee(
                &first,
                second,
                InstanceLimits {
                    total: 1,
                    per_definition: 1,
                    ..InstanceLimits::default()
                },
            ),
            Err(InstanceGraphError::TotalLimit { .. })
        ));
        assert!(graph.callees(&first).unwrap().is_empty());
    }

    #[test]
    fn per_definition_limit_counts_only_admitted_distinct_instances() {
        let kinds = [GenericKind::Type];
        let instance = |scalar| {
            InstanceKey::new(
                definition(b"bounded"),
                &kinds,
                vec![InstanceArgument::Type(Type::Scalar(scalar))],
            )
            .unwrap()
        };
        let first = instance(ScalarType::I64);
        let second = instance(ScalarType::U32);
        let rejected = instance(ScalarType::Text);
        let limits = InstanceLimits {
            per_definition: 2,
            ..InstanceLimits::default()
        };
        let mut graph = InstanceGraph::default();
        graph
            .discover_root(
                InstanceRoot {
                    key: first.clone(),
                    reason: "entry".into(),
                },
                limits,
            )
            .unwrap();
        graph
            .discover_callee(&first, second.clone(), limits)
            .unwrap();

        assert!(matches!(
            graph.discover_callee(&first, rejected, limits),
            Err(InstanceGraphError::PerDefinitionLimit { .. })
        ));
        assert!(graph.callees(&first).unwrap().contains(&second));
        assert_eq!(graph.ordered().len(), 2);

        // A rejected insertion must not perturb accounting: an already
        // admitted recursion remains a deduplicated edge, not a new charge.
        assert!(
            !graph
                .discover_callee(&first, first.clone(), limits)
                .unwrap()
        );
    }

    #[test]
    fn sccs_are_deterministic_and_keep_recursive_instances_together() {
        let kinds = [GenericKind::Type];
        let instance = |name| {
            InstanceKey::new(
                definition(name),
                &kinds,
                vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
            )
            .unwrap()
        };
        let first = instance(b"first");
        let second = instance(b"second");
        let terminal = instance(b"terminal");
        let mut graph = InstanceGraph::default();
        let limits = InstanceLimits::default();
        graph
            .discover_root(
                InstanceRoot {
                    key: first.clone(),
                    reason: "entry".into(),
                },
                limits,
            )
            .unwrap();
        graph
            .discover_callee(&first, second.clone(), limits)
            .unwrap();
        graph
            .discover_callee(&second, first.clone(), limits)
            .unwrap();
        graph
            .discover_callee(&second, terminal.clone(), limits)
            .unwrap();
        let components = graph.strongly_connected_components();
        assert_eq!(components, graph.strongly_connected_components());
        assert!(components.iter().any(|component| {
            component.len() == 2 && component.contains(&first) && component.contains(&second)
        }));
        assert!(
            components
                .iter()
                .any(|component| component.first() == Some(&terminal) && component.len() == 1)
        );
    }

    #[test]
    fn recursive_summary_fixed_point_propagates_callee_facts() {
        let kinds = [GenericKind::Type];
        let instance = |name| {
            InstanceKey::new(
                definition(name),
                &kinds,
                vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
            )
            .unwrap()
        };
        let first = instance(b"first");
        let second = instance(b"second");
        let mut graph = InstanceGraph::default();
        let limits = InstanceLimits::default();
        graph
            .discover_root(
                InstanceRoot {
                    key: first.clone(),
                    reason: "entry".into(),
                },
                limits,
            )
            .unwrap();
        graph
            .discover_callee(&first, second.clone(), limits)
            .unwrap();
        graph
            .discover_callee(&second, first.clone(), limits)
            .unwrap();
        let first_effect = definition(b"first-effect");
        let second_effect = definition(b"second-effect");
        let summaries = solve_call_summaries(&graph, SummaryLimits::default(), |key, known| {
            let direct = if key == &first {
                CallSummary {
                    effects: EffectRow::closed([first_effect]),
                    invocation: Quantity::ONCE,
                    argument_uses: vec![Quantity::ONCE],
                    may_abort: true,
                    may_control: false,
                    may_cancel: true,
                    may_resume: false,
                    may_escape: false,
                }
            } else {
                CallSummary {
                    effects: EffectRow::closed([second_effect]),
                    invocation: Quantity::ONCE,
                    argument_uses: vec![Quantity::AFFINE],
                    may_abort: false,
                    may_control: true,
                    may_cancel: false,
                    may_resume: true,
                    may_escape: true,
                }
            };
            graph
                .callees(key)
                .into_iter()
                .flatten()
                .fold(direct, |summary, callee| {
                    summary
                        .join(known.get(callee).expect("SCC member has a seed summary"))
                        .expect("closed summary rows compose")
                })
        })
        .unwrap();
        for key in [&first, &second] {
            let summary = &summaries[key];
            assert_eq!(summary.effects.effects.len(), 2);
            assert!(
                summary.may_abort
                    && summary.may_control
                    && summary.may_cancel
                    && summary.may_resume
                    && summary.may_escape
            );
            assert_eq!(summary.argument_uses, vec![Quantity::AFFINE]);
        }
    }

    #[test]
    fn summary_composition_preserves_cancellation_and_mapped_parameter_uses() {
        let caller_effect = definition(b"caller-effect");
        let callee_effect = definition(b"callee-effect");
        let caller = CallSummary {
            effects: EffectRow::closed([caller_effect]),
            invocation: Quantity::ONCE,
            argument_uses: vec![Quantity::ONCE, Quantity::ZERO],
            may_abort: false,
            may_control: false,
            may_cancel: false,
            may_resume: false,
            may_escape: false,
        };
        let callee = CallSummary {
            effects: EffectRow::closed([callee_effect]),
            invocation: Quantity::AFFINE,
            argument_uses: vec![Quantity::ONCE, Quantity::UNRESTRICTED],
            may_abort: true,
            may_control: true,
            may_cancel: true,
            may_resume: true,
            may_escape: true,
        };
        // The first callee argument is the caller's second parameter.  Its
        // second argument was created locally, so it cannot alter caller
        // ownership evidence.
        let composed = caller.compose_callee(&callee, &[Some(1), None]).unwrap();
        assert!(
            composed
                .effects
                .effects
                .iter()
                .any(|effect| effect.definition == caller_effect)
        );
        assert!(
            composed
                .effects
                .effects
                .iter()
                .any(|effect| effect.definition == callee_effect)
        );
        assert_eq!(composed.invocation, Quantity::AFFINE);
        assert_eq!(composed.argument_uses, vec![Quantity::ONCE, Quantity::ONCE]);
        assert!(
            composed.may_abort
                && composed.may_control
                && composed.may_cancel
                && composed.may_resume
                && composed.may_escape
        );

        // Repeated mappings are sequential uses of one caller-owned value,
        // not alternate control-flow paths.  Their lower bound must add.
        let repeated = CallSummary {
            argument_uses: vec![Quantity::ONCE, Quantity::ONCE],
            ..callee.clone()
        };
        let repeated = caller
            .compose_callee(&repeated, &[Some(1), Some(1)])
            .unwrap();
        assert_eq!(
            repeated.argument_uses,
            vec![Quantity::ONCE, Quantity::new(2, Some(2)).unwrap()]
        );

        assert!(matches!(
            caller.compose_callee(&callee, &[Some(2), None]),
            Err(SummaryError::InvalidArgumentMapping { .. })
        ));
    }

    #[test]
    fn summary_solver_rejects_an_unbounded_recursive_growth() {
        let key = InstanceKey::new(
            definition(b"growth"),
            &[GenericKind::Type],
            vec![InstanceArgument::Type(Type::Scalar(ScalarType::I64))],
        )
        .unwrap();
        let mut graph = InstanceGraph::default();
        graph
            .discover_root(
                InstanceRoot {
                    key: key.clone(),
                    reason: "entry".into(),
                },
                InstanceLimits::default(),
            )
            .unwrap();
        graph
            .discover_callee(&key, key.clone(), InstanceLimits::default())
            .unwrap();
        let error = solve_call_summaries(
            &graph,
            SummaryLimits {
                iterations_per_scc: 2,
            },
            |key, known| CallSummary {
                invocation: Quantity::new(0, Some(known[key].invocation.upper.unwrap_or(0) + 1))
                    .unwrap(),
                ..CallSummary::default()
            },
        )
        .unwrap_err();
        assert!(matches!(
            error,
            SummaryError::DidNotConverge { limit: 2, .. }
        ));
    }

    #[test]
    fn summary_join_never_collapses_distinct_open_effect_rows() {
        let left = CallSummary {
            effects: EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(EffectTail::Generic(0)),
            },
            ..CallSummary::default()
        };
        let right = CallSummary {
            effects: EffectRow {
                effects: BTreeSet::new(),
                projections: vec![],
                tail: Some(EffectTail::Generic(1)),
            },
            ..CallSummary::default()
        };
        assert!(matches!(
            left.join(&right),
            Err(SummaryError::IncompatibleEffectTails {
                left: EffectTail::Generic(0),
                right: EffectTail::Generic(1),
            })
        ));
    }

    #[test]
    fn depth_limit_counts_nested_mixed_kind_substitutions_before_admission() {
        let nested = InstanceKey::new(
            definition(b"mixed"),
            &[GenericKind::Type],
            vec![InstanceArgument::Type(Type::Nominal {
                definition: definition(b"outer"),
                arguments: vec![InstanceArgument::EffectRow(EffectRow::closed_instances([
                    crate::EffectInstance {
                        definition: definition(b"effect"),
                        arguments: vec![InstanceArgument::Type(Type::Nominal {
                            definition: definition(b"inner"),
                            arguments: vec![InstanceArgument::ConstQuantity(Quantity::AFFINE)],
                        })],
                    },
                ]))],
            })],
        )
        .unwrap();
        assert_eq!(nested.substitution_depth(), 5);

        let mut graph = InstanceGraph::default();
        let error = graph
            .discover_root(
                InstanceRoot {
                    key: nested,
                    reason: "adversarial nested substitution".into(),
                },
                InstanceLimits {
                    substitution_depth: 4,
                    ..InstanceLimits::default()
                },
            )
            .unwrap_err();
        assert!(matches!(
            error,
            InstanceGraphError::SubstitutionDepth {
                depth: 5,
                limit: 4,
                ..
            }
        ));
        assert!(graph.ordered().is_empty());
    }
}
