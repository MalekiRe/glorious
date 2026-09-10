//! Recheck the selected operation application at the frozen Core boundary.
//! The declaration is the authority; payload shape alone cannot recover
//! phantom type, region, row or quantity prerequisites.
use super::*;

pub(super) fn validate_application(
    expression: &CoreExpr,
    signatures: &ElaboratedInterface,
    scope: &TraitSolver,
    outlives: &[crate::OutlivesPredicate],
    diagnostics: &mut Vec<CoreDiagnostic>,
) {
    let mut check = |effect: &EffectInstance, operation, arguments: &[GenericArgument],
                     parameters: &[Type], result: Option<&Type>, terminal, span| {
        let mut solver = scope.fresh_query();
        let error = (|| -> Result<(), &'static str> {
            let (_, selected) = signatures.instantiate_effect_operation_at(
                effect.definition, &effect.arguments, arguments, operation,
            ).map_err(|_| "operation application does not match its declaration binder contract")?;
            if !solver.effect_domain_proven(effect)
                || !solver.callable_prerequisites_proven(&selected.signature) {
                return Err("operation application does not establish its declaration prerequisites");
            }
            if terminal != selected.terminal || parameters.len() != selected.signature.parameters.len() {
                return Err("operation application changes its declaration arity or terminality");
            }
            for (required, provided) in selected.signature.parameters.iter().zip(parameters) {
                if !accepts(required, provided, &mut solver, outlives) {
                    return Err("operation payload changes its instantiated declaration type");
                }
            }
            if let Some(result) = result
                && !accepts(&selected.signature.result, result, &mut solver, outlives) {
                return Err("operation result changes its instantiated declaration type");
            }
            Ok(())
        })();
        if let Err(message) = error {
            diagnostics.push(CoreDiagnostic { code: "G4199", span,
                message: format!("Typed Core {message}") });
        }
    };
    match &expression.kind {
        CoreKind::Perform { effect, operation, operation_arguments, payload_types, terminal, .. } =>
            check(effect, *operation, operation_arguments, payload_types, Some(&expression.ty), *terminal, expression.span),
        CoreKind::Handle { clauses, .. } => {
            for clause in clauses {
                check(&clause.effect, clause.operation, &clause.operation_arguments,
                    &clause.payload_types, clause.continuation.as_ref().map(|contract| &contract.parameter),
                    clause.terminal, clause.span);
            }
        }
        _ => {}
    }
}

fn accepts(required: &Type, provided: &Type, solver: &mut TraitSolver, outlives: &[crate::OutlivesPredicate]) -> bool {
    let (Ok(required), Ok(provided)) = (solver.normalize_type(required.clone()), solver.normalize_type(provided.clone())) else { return false; };
    let mut substitution = CallLifetimeSubstitution { outlives: outlives.to_vec(),
        nominal_variances: Some(solver.nominal_variances()), ..Default::default() };
    let Ok(aligned) = align_lifetime_types(&required, &provided, &mut substitution, LifetimeMode::InstantiateBound, 0) else { return false; };
    let mut inference = InferContext::default();
    substitution.inference_outlives.is_empty()
        && inference.unify(aligned, provided).is_ok()
}
