//! Dependency seal for the ownership producer's closed quantity solution.
//! Validation binds the receiving representation; it does not rerun traits or
//! rediscover generic storage constraints from a specialized instruction walk.
use super::*;

#[derive(Clone, Debug)]
pub(super) struct Proof {
    source: DefKey,
    instance: InstanceKey,
    entry: ControlBlockId,
    parameters: Vec<ControlValue>,
    values: Vec<ControlValueDecl>,
    owners: Vec<Owner>,
    loans: Vec<Loan>,
    blocks: Vec<SpecializedBlock>,
    captures: Vec<crate::CaptureEnvironment>,
}

impl Proof {
    /// Called only after the ownership constraint solution is installed and
    /// the ordinary symbolic-target representation map has completed.
    pub(super) fn seal(body: &SpecializedMir) -> std::sync::Arc<Self> {
        std::sync::Arc::new(Self {
            source: body.source_definition, instance: body.instance.clone(),
            entry: body.entry, parameters: body.parameters.clone(),
            values: body.values.clone(), owners: body.owners.clone(), loans: body.loans.clone(),
            blocks: body.blocks.clone(), captures: body.closures.iter().map(|closure| closure.environment.clone()).collect(),
        })
    }

    pub(super) fn matches(&self, body: &SpecializedMir) -> bool {
        self.source == body.source_definition && self.instance == body.instance
            && self.entry == body.entry && self.parameters == body.parameters
            && self.values == body.values && self.owners == body.owners
            && self.loans == body.loans && self.blocks == body.blocks
            && self.captures.len() == body.closures.len()
            && self.captures.iter().zip(&body.closures).all(|(capture, closure)| *capture == closure.environment)
    }
}
