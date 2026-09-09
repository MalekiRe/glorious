//! Frozen source-order continuation facts for all Typed Core consumers.
//!
//! This is the local continuation projection, not a complete effect/control
//! summary. Possible normal return does not prove absence of nonlocal exits. An unresolved
//! bottom-typed invocation cannot return to its next operand, but can still
//! rejoin an enclosing label. Interprocedural guarded outcomes must refine a
//! separate contract; consumers must not manufacture them from this table.
//!
//! Rules are projected once from Core, solved without recursive tree walking,
//! and published immutably. Ownership, escape and quantity checking use the
//! same table. Its input projection retains exact arena edges and label brands
//! so a consumer cannot attach facts to reordered or changed control input.

use crate::{CoreDiagnostic, CoreExpr, CoreId, CoreKind, CorePlace, LabelBrand, Type, TypedBody};
use std::collections::VecDeque;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PossibleExits {
    None,
    Label(LabelBrand),
    /// May include any label, cancellation or divergence; never absence proof.
    Unresolved,
}

impl PossibleExits {
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::None, value) | (value, Self::None) => value,
            (left, right) if left == right => left,
            _ => Self::Unresolved,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Continuation {
    may_return: bool,
    exits: PossibleExits,
}

impl Continuation {
    const NORMAL: Self = Self {
        may_return: true,
        exits: PossibleExits::None,
    };
    const OPAQUE: Self = Self {
        may_return: true,
        exits: PossibleExits::Unresolved,
    };

    fn transfer(target: LabelBrand) -> Self {
        Self {
            may_return: false,
            exits: PossibleExits::Label(target),
        }
    }

    /// Only normally returning paths evaluate the next strict operand. Retain
    /// exits from every earlier prefix, not just the first definitely abrupt
    /// child: an earlier conditional transfer may have a different target.
    fn then(self, next: Self) -> Self {
        if !self.may_return {
            return self;
        }
        Self {
            may_return: next.may_return,
            exits: self.exits.join(next.exits),
        }
    }

    fn join(self, other: Self) -> Self {
        Self {
            may_return: self.may_return || other.may_return,
            exits: self.exits.join(other.exits),
        }
    }

    fn rejoin(self, target: LabelBrand) -> Self {
        match self.exits {
            PossibleExits::Label(actual) if actual == target => Self::NORMAL,
            PossibleExits::Unresolved => Self::OPAQUE,
            _ => self,
        }
    }

    pub(crate) fn is_abrupt(self) -> bool {
        !self.may_return
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ResultRule {
    Continue,
    Invoke,
    Choose,
    Transfer(LabelBrand),
    Rejoin(LabelBrand),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Rule {
    operands: Vec<CoreId>,
    alternatives: Vec<CoreId>,
    result: ResultRule,
    bottom: bool,
}

impl Rule {
    fn project(expression: &CoreExpr) -> Self {
        let mut rule = Self {
            operands: vec![],
            alternatives: vec![],
            result: ResultRule::Continue,
            bottom: matches!(expression.ty, Type::Never),
        };
        match &expression.kind {
            CoreKind::Transfer { brand, value } => {
                rule.operands.push(*value);
                rule.result = ResultRule::Transfer(*brand);
            }
            CoreKind::Label { brand, body } => {
                rule.operands.push(*body);
                rule.result = ResultRule::Rejoin(*brand);
            }
            CoreKind::Let { value, .. }
            | CoreKind::Borrow { value, .. }
            | CoreKind::Deref(value)
            | CoreKind::Move(value)
            | CoreKind::ReleaseAvailable(value)
            | CoreKind::PatternTest { subject: value, .. }
            | CoreKind::Field { base: value, .. } => rule.operands.push(*value),
            CoreKind::Assign { value, place } => {
                // Core assignment evaluates its value before its destination.
                rule.operands.push(*value);
                let mut destination = place;
                while let CorePlace::Field { base, .. } = destination {
                    destination = base;
                }
                if let CorePlace::Deref { reference, .. } = destination {
                    rule.operands.push(*reference);
                }
            }
            CoreKind::Tuple(values) | CoreKind::Array(values) | CoreKind::Block(values) => {
                rule.operands.extend(values);
            }
            CoreKind::Record { fields, .. } | CoreKind::Enum { fields, .. } => {
                rule.operands.extend(fields);
            }
            CoreKind::IntrinsicCall { arguments, .. } => {
                rule.operands.extend(arguments);
            }
            CoreKind::Perform { arguments, .. } => {
                rule.operands.extend(arguments);
                rule.result = ResultRule::Invoke;
            }
            CoreKind::Call {
                callee, arguments, ..
            } => {
                rule.operands.push(*callee);
                rule.operands.extend(arguments);
                rule.result = ResultRule::Invoke;
            }
            CoreKind::Completion {
                computation,
                clauses,
                handles_operations: false,
                ..
            } => {
                rule.operands.push(*computation);
                rule.alternatives
                    .extend(clauses.iter().map(|clause| clause.body));
                rule.result = ResultRule::Choose;
            }
            // A handler can intercept the computation's exit. A closure body
            // is not executed at construction. Do not treat their structural
            // children as unconditionally evaluated strict operands.
            CoreKind::Handle { .. } | CoreKind::Completion { .. } | CoreKind::Constant { .. } => {
                rule.result = ResultRule::Invoke;
            }
            CoreKind::Closure { .. }
            | CoreKind::ConstValue(_)
            | CoreKind::Literal(_)
            | CoreKind::Local(_)
            | CoreKind::Resumption { .. }
            | CoreKind::LabelValue { .. }
            | CoreKind::Function { .. }
            | CoreKind::TraitMethod { .. }
            | CoreKind::Error => {}
        }
        rule
    }

    fn evaluate(&self, facts: &[Option<Continuation>]) -> Continuation {
        let prefix = self
            .operands
            .iter()
            .map(|id| {
                facts[id.0 as usize].expect("a ready rule has facts for every strict operand")
            })
            .fold(Continuation::NORMAL, Continuation::then);
        let mut result = match self.result {
            // A transfer's payload executes before the transfer itself. If
            // the payload leaves, the outer transfer never happens. A
            // conditional payload exit remains alongside the outer target.
            ResultRule::Transfer(target) => prefix.then(Continuation::transfer(target)),
            ResultRule::Rejoin(target) => prefix.rejoin(target),
            ResultRule::Continue => prefix,
            ResultRule::Invoke => prefix.then(Continuation::OPAQUE),
            ResultRule::Choose => {
                let choices = self
                    .alternatives
                    .iter()
                    .map(|id| {
                        facts[id.0 as usize].expect("a ready choice has facts for every branch")
                    })
                    .reduce(Continuation::join)
                    .unwrap_or(Continuation::OPAQUE);
                prefix.then(choices)
            }
        };
        if result.may_return && self.bottom {
            result.may_return = false;
            result.exits = PossibleExits::Unresolved;
        }
        result
    }
}

#[derive(Debug)]
pub(crate) struct CoreContinuations {
    root: CoreId,
    rules: Box<[Rule]>,
    facts: Box<[Continuation]>,
}

impl CoreContinuations {
    pub(crate) fn derive(body: &TypedBody) -> Result<Self, CoreDiagnostic> {
        if body.expressions.get(body.root.0 as usize).is_none() {
            return Err(input_error(
                body,
                "continuation facts require a valid Core root",
            ));
        }
        let rules = body
            .expressions
            .iter()
            .map(Rule::project)
            .collect::<Vec<_>>();
        let mut parents = vec![vec![]; rules.len()];
        let mut pending = vec![0; rules.len()];
        let mut ready = VecDeque::new();
        for (index, rule) in rules.iter().enumerate() {
            pending[index] = rule.operands.len() + rule.alternatives.len();
            if pending[index] == 0 {
                ready.push_back(index);
            }
            for child in rule.operands.iter().chain(&rule.alternatives) {
                let Some(parents) = parents.get_mut(child.0 as usize) else {
                    return Err(input_error(
                        body,
                        "continuation rule refers to a missing Core operand",
                    ));
                };
                parents.push(index);
            }
        }
        let mut facts = vec![None; rules.len()];
        while let Some(index) = ready.pop_front() {
            facts[index] = Some(rules[index].evaluate(&facts));
            for parent in &parents[index] {
                pending[*parent] -= 1;
                if pending[*parent] == 0 {
                    ready.push_back(*parent);
                }
            }
        }
        let Some(facts) = facts.into_iter().collect::<Option<Vec<_>>>() else {
            return Err(input_error(
                body,
                "continuation rules contain a cyclic strict-operand dependency",
            ));
        };
        Ok(Self {
            root: body.root,
            rules: rules.into_boxed_slice(),
            facts: facts.into_boxed_slice(),
        })
    }

    /// Validate the complete dependency projection once at each consumer
    /// boundary, not per query. Literal spelling and unrelated type/layout
    /// metadata are intentionally not dependencies of these control facts.
    pub(crate) fn bind(&self, body: &TypedBody) -> Result<&Self, CoreDiagnostic> {
        if self.root != body.root
            || self.rules.len() != body.expressions.len()
            || !self
                .rules
                .iter()
                .zip(&body.expressions)
                .all(|(rule, expression)| *rule == Rule::project(expression))
        {
            return Err(input_error(
                body,
                "frozen continuation facts do not match this Core control graph",
            ));
        }
        Ok(self)
    }

    pub(crate) fn get(&self, id: CoreId) -> Continuation {
        self.facts[id.0 as usize]
    }

    pub(crate) fn is_abrupt(&self, id: CoreId) -> bool {
        self.get(id).is_abrupt()
    }
}

pub(crate) fn input_error(body: &TypedBody, message: &str) -> CoreDiagnostic {
    CoreDiagnostic {
        code: "G4180",
        span: body
            .expressions
            .get(body.root.0 as usize)
            .or_else(|| body.expressions.first())
            .map_or(
                crate::Span {
                    file: crate::FileKey(crate::Digest::of_bytes(b"invalid-control-input")),
                    start: 0,
                    end: 0,
                },
                |value| value.span,
            ),
        message: message.into(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn label(index: u32) -> LabelBrand {
        LabelBrand {
            owner: crate::DefKey(crate::Digest::of_bytes(b"continuation-rules")),
            label: index,
        }
    }
    fn body(nodes: Vec<(CoreKind, Type)>) -> TypedBody {
        let span = crate::Span {
            file: crate::FileKey(crate::Digest::of_bytes(b"continuation-rules")),
            start: 0,
            end: 1,
        };
        TypedBody {
            safety: crate::Safety::Safe,
            unsafe_scopes: Default::default(),
            unsafe_implementations: Default::default(),
            parameters: vec![],
            root: CoreId(nodes.len() as u32 - 1),
            expressions: nodes
                .into_iter()
                .map(|(kind, ty)| CoreExpr { kind, ty, span })
                .collect(),
            diagnostics: vec![],
            recovered: false,
        }
    }

    #[test]
    fn transfer_payload_precedes_its_destination_and_local_rejoin() {
        let body = body(vec![
            (CoreKind::Literal("()".into()), Type::Unit),
            (
                CoreKind::Transfer {
                    brand: label(1),
                    value: CoreId(0),
                },
                Type::Never,
            ),
            (
                CoreKind::Transfer {
                    brand: label(2),
                    value: CoreId(1),
                },
                Type::Never,
            ),
            (
                CoreKind::Label {
                    brand: label(1),
                    body: CoreId(2),
                },
                Type::Unit,
            ),
        ]);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert_eq!(facts.get(CoreId(2)), Continuation::transfer(label(1)));
        assert_eq!(facts.get(CoreId(3)), Continuation::NORMAL);
    }

    #[test]
    fn strict_sequences_keep_the_first_exit_and_label_brand() {
        let body = body(vec![
            (CoreKind::Literal("()".into()), Type::Unit),
            (
                CoreKind::Transfer {
                    brand: label(1),
                    value: CoreId(0),
                },
                Type::Never,
            ),
            (
                CoreKind::Transfer {
                    brand: label(2),
                    value: CoreId(0),
                },
                Type::Never,
            ),
            (CoreKind::Tuple(vec![CoreId(1), CoreId(2)]), Type::Never),
            (
                CoreKind::Label {
                    brand: label(2),
                    body: CoreId(3),
                },
                Type::Unit,
            ),
        ]);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert_eq!(facts.get(CoreId(3)), Continuation::transfer(label(1)));
        assert_eq!(facts.get(CoreId(4)), Continuation::transfer(label(1)));
    }

    #[test]
    fn bottom_is_not_proof_that_an_enclosing_label_cannot_rejoin() {
        let body = body(vec![
            (CoreKind::Local("unknown_call_result".into()), Type::Never),
            (
                CoreKind::Label {
                    brand: label(1),
                    body: CoreId(0),
                },
                Type::Unit,
            ),
            (
                CoreKind::Label {
                    brand: label(2),
                    body: CoreId(0),
                },
                Type::Never,
            ),
        ]);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert_eq!(
            facts.get(CoreId(0)),
            Continuation {
                may_return: false,
                exits: PossibleExits::Unresolved
            }
        );
        assert_eq!(facts.get(CoreId(1)), Continuation::OPAQUE);
        assert_eq!(
            facts.get(CoreId(2)),
            Continuation {
                may_return: false,
                exits: PossibleExits::Unresolved
            }
        );
    }

    #[test]
    fn graph_order_and_repeated_operands_do_not_change_the_result() {
        let body = body(vec![
            (
                CoreKind::Tuple(vec![CoreId(2), CoreId(2), CoreId(1)]),
                Type::Never,
            ),
            (
                CoreKind::Transfer {
                    brand: label(1),
                    value: CoreId(2),
                },
                Type::Never,
            ),
            (CoreKind::Literal("()".into()), Type::Unit),
            (
                CoreKind::Label {
                    brand: label(1),
                    body: CoreId(0),
                },
                Type::Unit,
            ),
        ]);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert_eq!(facts.get(CoreId(0)), Continuation::transfer(label(1)));
        assert_eq!(facts.get(CoreId(3)), Continuation::NORMAL);
    }

    #[test]
    fn possible_earlier_exits_survive_a_later_definite_transfer() {
        let conditional = Continuation::NORMAL.join(Continuation::transfer(label(1)));
        let outer = conditional.then(Continuation::transfer(label(2)));
        assert!(outer.is_abrupt());
        assert_eq!(outer.exits, PossibleExits::Unresolved);
        assert!(!outer.rejoin(label(1)).is_abrupt());
        assert!(!outer.rejoin(label(2)).is_abrupt());

        let opaque = Continuation::OPAQUE.then(Continuation::transfer(label(2)));
        assert_eq!(
            opaque.exits,
            PossibleExits::Unresolved,
            "possible normal return is not proof that the prefix cannot exit elsewhere"
        );
    }

    #[test]
    fn continuation_rules_obey_sequence_and_choice_composition_laws() {
        let values = [
            Continuation::NORMAL,
            Continuation::OPAQUE,
            Continuation::transfer(label(1)),
            Continuation::transfer(label(2)),
            Continuation {
                may_return: false,
                exits: PossibleExits::Unresolved,
            },
        ];
        for a in values {
            assert_eq!(a.then(Continuation::NORMAL), a);
            assert_eq!(Continuation::NORMAL.then(a), a);
            assert_eq!(a.join(a), a);
            for b in values {
                assert_eq!(a.join(b), b.join(a));
                for c in values {
                    assert_eq!(a.then(b).then(c), a.then(b.then(c)));
                    assert_eq!(a.join(b).join(c), a.join(b.join(c)));
                    assert_eq!(a.then(b.join(c)), a.then(b).join(a.then(c)));
                    assert_eq!(a.join(b).then(c), a.then(c).join(b.then(c)));
                }
            }
        }
    }

    #[test]
    fn malformed_graphs_and_stale_control_inputs_fail_closed() {
        let mut body = body(vec![
            (CoreKind::Literal("()".into()), Type::Unit),
            (
                CoreKind::Transfer {
                    brand: label(1),
                    value: CoreId(0),
                },
                Type::Never,
            ),
        ]);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert!(facts.bind(&body).is_ok());
        body.expressions[0].kind = CoreKind::Literal("different_spelling".into());
        assert!(
            facts.bind(&body).is_ok(),
            "literal text is not control authority"
        );
        body.expressions[1].kind = CoreKind::Transfer {
            brand: label(2),
            value: CoreId(0),
        };
        assert!(facts.bind(&body).is_err());
        body.expressions[1].kind = CoreKind::Move(CoreId(9));
        assert!(CoreContinuations::derive(&body).is_err());
        body.expressions[1].kind = CoreKind::Move(CoreId(1));
        assert!(CoreContinuations::derive(&body).is_err());
        body.expressions[1].kind = CoreKind::Move(CoreId(0));
        body.expressions[0].kind = CoreKind::Move(CoreId(1));
        assert!(CoreContinuations::derive(&body).is_err());
    }

    #[test]
    fn deep_shared_graph_is_solved_without_recursive_expansion() {
        let mut nodes = vec![(CoreKind::Literal("()".into()), Type::Unit)];
        for index in 0..20_000 {
            nodes.push((
                CoreKind::Tuple(vec![CoreId(index), CoreId(index)]),
                Type::Unit,
            ));
        }
        let body = body(nodes);
        let facts = CoreContinuations::derive(&body).unwrap();
        assert_eq!(facts.get(body.root), Continuation::NORMAL);
    }
}
