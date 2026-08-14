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
}

/// A stable executable specialization identity. The private canonical bytes
/// retain the full substitution identity while avoiding `Ord` implementations
/// on semantic type trees solely for work-queue ordering.
#[derive(Clone, Debug)]
pub struct InstanceKey {
    pub callable: DefKey,
    arguments: Vec<InstanceArgument>,
    canonical_substitution: Vec<u8>,
    fingerprint: Digest,
}

impl InstanceKey {
    pub fn new(
        callable: DefKey,
        kinds: &[GenericKind],
        arguments: Vec<InstanceArgument>,
    ) -> Result<Self, InstanceKeyError> {
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
                    if !matches!(value, Lifetime::Static | Lifetime::Bound { .. }) {
                        return Err(InstanceKeyError::NonConcreteLifetime { slot });
                    }
                    canonical_substitution.push(2);
                    encode_lifetime(*value, &mut canonical_substitution);
                }
                (GenericKind::Const(ConstKind::U32), InstanceArgument::ConstU32(value)) => {
                    canonical_substitution.push(3);
                    canonical_substitution.extend_from_slice(&value.to_le_bytes());
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
        Type::Array(element) => is_concrete_type(element),
        Type::Reference {
            lifetime, referent, ..
        } => {
            matches!(lifetime, Lifetime::Static | Lifetime::Bound { .. })
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
            matches!(value, Lifetime::Static | Lifetime::Bound { .. })
        }
        GenericArgument::ConstU32(_) | GenericArgument::ConstQuantity(_) => true,
        GenericArgument::ConstU32Expr(_) => false,
        GenericArgument::ConstGeneric { .. } => false,
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
        Lifetime::Generic(_) | Lifetime::Elided => unreachable!("validated concrete lifetime"),
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
}

impl Default for InstanceLimits {
    fn default() -> Self {
        Self {
            total: 10_000,
            per_definition: 1_000,
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
}

/// Deterministic demand queue. Recursive discovery reuses the existing node,
/// leaving SCC calculation to a later graph pass instead of recursively
/// cloning a body.
#[derive(Clone, Debug, Default)]
pub struct InstanceGraph {
    roots: BTreeMap<InstanceKey, String>,
    edges: BTreeMap<InstanceKey, BTreeSet<InstanceKey>>,
    pending: BTreeSet<InstanceKey>,
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
        if self.edges.len() >= limits.total {
            return Err(InstanceGraphError::TotalLimit {
                limit: limits.total,
                root: Box::new(key),
            });
        }
        let count = self
            .edges
            .keys()
            .filter(|existing| existing.callable == key.callable)
            .count();
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
    pub invocation: Quantity,
    pub may_abort: bool,
    pub may_control: bool,
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
}

impl Default for CallSummary {
    fn default() -> Self {
        Self {
            effects: EffectRow::empty(),
            invocation: Quantity::ZERO,
            may_abort: false,
            may_control: false,
            may_escape: false,
        }
    }
}
impl CallSummary {
    pub fn join(&self, other: &Self) -> Result<Self, SummaryError> {
        let tail = match (self.effects.tail, other.effects.tail) {
            (Some(left), Some(right)) if left != right => {
                return Err(SummaryError::IncompatibleEffectTails { left, right });
            }
            (Some(tail), _) | (_, Some(tail)) => Some(tail),
            (None, None) => None,
        };
        let mut effects = self.effects.clone();
        effects
            .effects
            .extend(other.effects.effects.iter().cloned());
        effects
            .projections
            .extend(other.effects.projections.iter().cloned());
        effects.tail = tail;
        effects.canonicalize();
        Ok(Self {
            effects,
            invocation: Quantity {
                lower: self.invocation.lower.min(other.invocation.lower),
                upper: match (self.invocation.upper, other.invocation.upper) {
                    (Some(left), Some(right)) => Some(left.max(right)),
                    _ => None,
                },
            },
            may_abort: self.may_abort || other.may_abort,
            may_control: self.may_control || other.may_control,
            may_escape: self.may_escape || other.may_escape,
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
    use crate::{Digest, EffectTail, ScalarType};

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
                },
            ),
            Err(InstanceGraphError::TotalLimit { .. })
        ));
        assert!(graph.callees(&first).unwrap().is_empty());
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
                    may_abort: true,
                    may_control: false,
                    may_escape: false,
                }
            } else {
                CallSummary {
                    effects: EffectRow::closed([second_effect]),
                    invocation: Quantity::ONCE,
                    may_abort: false,
                    may_control: true,
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
            assert!(summary.may_abort && summary.may_control && summary.may_escape);
        }
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
}
