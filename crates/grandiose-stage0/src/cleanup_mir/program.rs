use super::*;

#[derive(Clone, Debug)]
pub struct CleanupProgram {
    entry: DefKey,
    functions: BTreeMap<DefKey, CleanupMir>,
    constants: BTreeSet<DefKey>,
    destruction: BTreeMap<InstanceKey, crate::destruction::Plan>,
}
impl CleanupProgram {
    pub fn entry(&self) -> DefKey {
        self.entry
    }
    pub fn functions(&self) -> &BTreeMap<DefKey, CleanupMir> {
        &self.functions
    }
    pub fn constants(&self) -> &BTreeSet<DefKey> {
        &self.constants
    }
    pub fn destruction_programs(&self) -> &BTreeMap<InstanceKey, DestructionProgram> {
        &self.destruction
    }

    pub(crate) fn lower(
        source: &crate::specialized_mir::SpecializedProgram,
        graph: &crate::InstanceGraph,
        signatures: &crate::ElaboratedInterface,
        planner: &crate::destruction::Planner<'_>,
    ) -> Result<Self, CleanupError> {
        source.validate().map_err(|error| CleanupError(error.0))?;
        let all = planner.frozen_plans();
        let mut destruction = BTreeMap::new();
        for key in graph
            .ordered()
            .into_iter()
            .filter(crate::destruction::is_glue)
        {
            let plan = all
                .get(&key)
                .ok_or_else(|| CleanupError("demanded destruction has no frozen plan".into()))?;
            destruction.insert(key, plan.clone());
        }
        let plans = std::sync::Arc::new(
            destruction
                .iter()
                .map(|(key, plan)| (DefKey(key.fingerprint()), plan.clone()))
                .collect(),
        );
        let functions = source
            .functions()
            .iter()
            .map(|(definition, body)| {
                Ok((*definition, CleanupMir::lower(body, signatures, &plans)?))
            })
            .collect::<Result<_, CleanupError>>()?;
        let program = Self {
            entry: source.entry(),
            functions,
            constants: source.constants().clone(),
            destruction,
        };
        program.validate()?;
        Ok(program)
    }

    pub fn validate(&self) -> Result<(), CleanupError> {
        if !self.functions.contains_key(&self.entry) {
            return Err(CleanupError("Cleanup entry is missing".into()));
        }
        let destruction = self
            .destruction
            .keys()
            .map(|key| DefKey(key.fingerprint()))
            .collect::<BTreeSet<_>>();
        for (definition, body) in &self.functions {
            if *definition != body.definition {
                return Err(CleanupError("Cleanup function identity mismatch".into()));
            }
            body.validate()?;
        }
        for plan in self.destruction.values() {
            crate::specialized_mir::closed_type(&plan.ty).map_err(|error| CleanupError(error.0))?;
            if let Some(hook) = &plan.hook {
                let target = if hook.arguments().is_empty() {
                    hook.callable
                } else {
                    DefKey(hook.fingerprint())
                };
                if !self.functions.contains_key(&target) {
                    return Err(CleanupError("Cleanup hook was not specialized".into()));
                }
            }
            let fields = match &plan.shape {
                crate::destruction::Shape::Tuple(fields) => fields.iter().collect::<Vec<_>>(),
                crate::destruction::Shape::Nominal { variants, .. } => {
                    variants.iter().flatten().collect()
                }
                crate::destruction::Shape::Array { glue, .. } => {
                    if !destruction.contains(&DefKey(glue.fingerprint())) {
                        return Err(CleanupError("Cleanup element destructor is absent".into()));
                    }
                    vec![]
                }
                _ => vec![],
            };
            for field in fields {
                crate::specialized_mir::closed_type(&field.ty)
                    .map_err(|error| CleanupError(error.0))?;
                if let Some(glue) = &field.glue
                    && !destruction.contains(&DefKey(glue.fingerprint()))
                {
                    return Err(CleanupError("Cleanup field destructor is absent".into()));
                }
            }
        }
        Ok(())
    }

}
