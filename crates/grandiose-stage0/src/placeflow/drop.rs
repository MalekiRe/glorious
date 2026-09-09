//! Custom Drop protects the initialized shell, including implicit moves and
//! constructor openings nested beneath tuples, arrays, and effect payloads.

use super::*;

impl Analyzer<'_> {
    pub(super) fn custom_drop_may_apply(&mut self, ty: &Type) -> bool {
        let Some(signatures) = self.signatures else {
            return false;
        };
        if !self.has_drop_implementations {
            return false;
        }
        let assumptions = self
            .lexical_bounds
            .iter()
            .map(|(subject, relation)| crate::TraitGoal {
                subject: subject.clone(),
                relation: relation.clone(),
            })
            .collect::<Vec<_>>();
        let solver = self.drop_solver.get_or_insert_with(|| {
            self.frozen_solver.map_or_else(
                || crate::TraitSolver::new(signatures),
                crate::TraitSolver::fresh_query,
            )
        });
        let mut solver = solver.fresh_query();
        crate::destruction::custom_drop_may_apply(signatures, &mut solver, ty, &assumptions)
    }

    pub(super) fn check_custom_drop_projection(&mut self, mut value: CoreId, span: Span) -> bool {
        loop {
            match self.body.expression(value).kind {
                CoreKind::Field { base, .. } => {
                    let ty = self.body.expression(base).ty.clone();
                    if self.custom_drop_may_apply(&ty) {
                        self.error(span, "G4188", "a custom-Drop aggregate cannot be partially moved through an owned projection".into());
                        return false;
                    }
                    value = base;
                }
                CoreKind::Move(inner) => value = inner,
                _ => return true,
            }
        }
    }

    pub(super) fn check_custom_drop_pattern(
        &mut self,
        value: CoreId,
        pattern: &CorePattern,
        span: Span,
    ) {
        let ty = self.body.expression(value).ty.clone();
        if matches!(ty, Type::Reference { .. }) || self.projected_dereference(value).is_some() {
            return;
        }
        if !self.is_duplicable(&ty)
            || matches!(
                pattern,
                CorePattern::Record { .. } | CorePattern::Enum { .. }
            )
        {
            self.check_custom_drop_projection(value, span);
        }
        self.check_custom_drop_pattern_at(&ty, pattern, span);
    }

    pub(super) fn check_custom_drop_payload_patterns(
        &mut self,
        clause: &crate::core::CoreHandlerClause,
    ) {
        for (ty, pattern) in clause.payload_types.iter().zip(&clause.patterns) {
            self.check_custom_drop_pattern_at(ty, pattern, clause.span);
        }
    }

    fn check_custom_drop_pattern_at(&mut self, ty: &Type, pattern: &CorePattern, span: Span) {
        if matches!(ty, Type::Reference { .. }) {
            return;
        }
        if !matches!(
            pattern,
            CorePattern::Tuple(_)
                | CorePattern::Array { .. }
                | CorePattern::Record { .. }
                | CorePattern::Enum { .. }
        ) {
            return;
        }
        if self.custom_drop_may_apply(ty) {
            self.error(
                span,
                "G4188",
                "a custom-Drop aggregate cannot be ownership-deconstructed by a nested pattern"
                    .into(),
            );
            return;
        }
        match pattern {
            CorePattern::Tuple(patterns) => {
                if let Type::Tuple(types) = ty {
                    for (ty, pattern) in types.iter().zip(patterns) {
                        self.check_custom_drop_pattern_at(ty, pattern, span);
                    }
                }
            }
            CorePattern::Array {
                element, elements, ..
            } => {
                for pattern in elements {
                    self.check_custom_drop_pattern_at(element, pattern, span);
                }
            }
            CorePattern::Record { fields, .. } | CorePattern::Enum { fields, .. } => {
                for field in fields {
                    self.check_custom_drop_pattern_at(&field.ty, &field.pattern, span);
                }
            }
            _ => {}
        }
    }
}
