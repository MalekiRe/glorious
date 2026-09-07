//! Cancellation facts derived from the concrete cleanup graph, not source
//! spelling or counts of direct calls (aliases and closures can invoke too).
use super::*;

impl CleanupMir {
    pub(crate) fn unused_optional_resumptions(&self) -> BTreeSet<(ControlHandlerId, u32)> {
        let referenced = self
            .blocks
            .iter()
            .flat_map(|block| {
                block
                    .instructions
                    .iter()
                    .flat_map(|instruction| instruction.operation.inputs(&self.loans))
                    .chain(block.terminator.control.inputs())
            })
            .collect::<BTreeSet<_>>();
        self.handlers
            .iter()
            .enumerate()
            .flat_map(|(handler, owner)| {
                let referenced = &referenced;
                owner
                    .clauses
                    .iter()
                    .enumerate()
                    .filter_map(move |(clause, selected)| {
                        // No operand can read, invoke, alias, or capture this token.
                        // Its suspended computation is therefore still pending at
                        // normal clause exit and must be canceled, not completed.
                        (selected
                            .contract
                            .as_ref()
                            .is_some_and(|contract| contract.invocation.lower == 0)
                            && selected
                                .token
                                .is_some_and(|token| !referenced.contains(&token)))
                        .then_some((ControlHandlerId(handler as u32), clause as u32))
                    })
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unused_token_proof_excludes_aliases_invocations_and_closure_captures() {
        for (clause, unused) in [
            ("42", true),
            ("k(42)", false),
            ("{ let alias = k; 42 }", false),
            ("{ let alias = k; alias(42) }", false),
            (
                "{ let callback = (value: i64) -> i64 { k(value) }; callback(42) }",
                false,
            ),
        ] {
            let source = format!(
                "effect Ask {{ [0,1] ask() -> i64; }} pub fn main() -> i64 {{ handle Ask::ask() {{ Ask::ask(k) => {clause} }} }}"
            );
            let body = crate::cleanup_mir::tests::fixture(&source);
            assert_eq!(
                body.unused_optional_resumptions()
                    .contains(&(ControlHandlerId(0), 0)),
                unused,
                "{clause}"
            );
        }
    }

    #[test]
    fn no_reference_does_not_authorize_cancellation_of_a_required_contract() {
        let mut body = crate::cleanup_mir::tests::fixture(
            "effect Ask { [0,1] ask() -> i64; } pub fn main() -> i64 { handle Ask::ask() { Ask::ask(k) => 42 } }",
        );
        body.handlers[0].clauses[0]
            .contract
            .as_mut()
            .unwrap()
            .invocation = crate::Quantity::ONCE;
        assert!(body.unused_optional_resumptions().is_empty());
    }
}
