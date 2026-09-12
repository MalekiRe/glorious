import GloriousLanguage.OperationContextTyping
import GloriousLanguage.InstantiationComposition
import GloriousLanguage.LogicalEvidence

/-! The accepting source arm and actual operation request share their one
declaration opening. Argument conversion transports its real substitution
table; it is not equality of signature syntax or a second arm matcher. -/
namespace Glorious.Language.Execution

open Kernel

theorem SelectsOperation.arguments {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace} {arm : OperationArm}
    (selected : SelectsOperation program world handler id arguments payload arm) :
    ListRel (Equal program.declarations handler.environment.static) arguments
      (arm.arguments.map handler.environment.term) := by
  obtain ⟨_,_,_,accepts,_⟩ := selected
  have converted := accepts.2.1
  cases arm
  simpa only [OperationArm.closeHead,OperationArm.arguments,List.map_append,Context.term] using converted

/-- Every parameter, result and effect component is transported from the
selected arm's actual call signature. The exact operation lookup rules out
function/operation identity collisions before either substitution is used. -/
theorem SelectsOperation.signature_components {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace} {arm : OperationArm}
    {source : Language.Context} {sourceSignature signature : Signature} {operation : OperationDefinition}
    (valid : ProgramWellFormed program.declarations)
    (selected : SelectsOperation program world handler id arguments payload arm)
    (sourceTyped : Typing.CallSignature program.declarations source arm.operation arm.arguments sourceSignature)
    (actual : OperationInstance program id arguments operation signature) :
    ListRel (Equal program.declarations handler.environment.static)
      (sourceSignature.parameters.map handler.environment.term) signature.parameters ∧
    Equal program.declarations handler.environment.static (handler.environment.term sourceSignature.result) signature.result ∧
    Equal program.declarations handler.environment.static (handler.environment.term sourceSignature.effects) signature.effects := by
  obtain ⟨targetSub,operationFound,targetInstantiated,_,rfl⟩ := actual
  obtain ⟨_,sourceTyped⟩ := sourceTyped
  rcases sourceTyped with sourceTyped | sourceTyped
  · obtain ⟨_,_,found,_⟩ := sourceTyped
    rw [selected.operation] at found
    cases (Program.function_lookup found).symm.trans (Program.operation_lookup operationFound)
  · obtain ⟨sourceOperation,sourceSub,found,sourceInstantiated,_,rfl⟩ := sourceTyped
    rw [selected.operation] at found
    have same := Option.some.inj (found.symm.trans operationFound)
    subst sourceOperation
    have mapped := sourceInstantiated.map_values handler.environment.term
      (fun term _ => handler.environment.instantiation.kind term)
    have related := targetInstantiated.related_values selected.arguments
    rw [← mapped.2.2] at related
    have tables := related.substitution_getD_related (fun _ => Equal.refl)
    have closed := valid.scopeClosed (List.mem_of_find?_eq_some (Program.operation_lookup operationFound))
    have component (term : Term) (member : term ∈ operation.signature.terms) :
        Equal program.declarations handler.environment.static
          (handler.environment.term (term.substitute sourceSub)) (term.substitute targetSub) := by
      change Equal _ _ (handler.environment.instantiation.term (term.substitute sourceSub)) _
      rw [ScopeInstantiation.term_substitute,handler.environment.instantiation.term_fixed term (closed term member)]
      exact (term.substitutions_related Equal.congr tables).symm
    refine ⟨?_,component _ (by simp [Signature.terms]),component _ (by simp [Signature.terms])⟩
    simp only [Signature.instantiate,List.map_map,Function.comp_def]
    apply ListRel.maps
    intro term member
    exact component term (by simp [Signature.terms,member])

/-- The actual selected source binder establishes the runtime continuation
type before storage allocation. Its fresh brand cannot occur in the earlier
operation signature; only that freshness fact justifies retaining the closed
argument/effect conversions when entering the resumption clause. -/
theorem SelectsOperation.continuation_binding_type {program : Kernel.Program} {before : State}
    {handler : InstalledHandler} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {arm : OperationArm} {source : Typing.Context} {operation : OperationDefinition} {signature : Signature}
    {quantity : Quantity} {lexical localSlot : Local} {clause : Context} {withRegion : World}
    (valid : ProgramWellFormed program.declarations)
    (selected : SelectsOperation program before.world handler id arguments payload arm)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations handler.syntaxNode.result)
    (actual : OperationInstance program id arguments operation signature)
    (quantityAt : operation.quantity = some quantity) (continuation : arm.continuation = some lexical)
    (started : StartsResumptionClause before handler lexical clause localSlot withRegion) :
    ContinuationBindingType program.declarations clause.static before.nextContinuation signature
      (clause.term handler.syntaxNode.result) signature.effects quantity localSlot.type := by
  obtain ⟨sourceOperation,sourceSignature,_,_,found,signatureTyped,_,mode,fresh,_,_⟩ := armsTyped.member selected.member
  have operationFound : program.declarations.operation id = some operation := by
    obtain ⟨_,found,_⟩ := actual
    exact found
  rw [selected.operation] at found
  have same := Option.some.inj (found.symm.trans operationFound)
  subst sourceOperation
  rcases mode with ⟨_,absent,_⟩ | ⟨_,sourceQuantity,sourceQuantityAt,tail | bound⟩
  · rw [continuation] at absent
    cases absent
  · have absent := tail.1
    rw [continuation] at absent
    cases absent
  · obtain rfl := Option.some.inj (sourceQuantityAt.symm.trans quantityAt)
    obtain ⟨sourceLocal,brand,present,localType,_⟩ := bound
    have sameLocal := Option.some.inj (present.symm.trans continuation)
    subst sourceLocal
    have branded : lexical.resumptionBrand = some brand := by rw [Local.resumptionBrand,localType]
    have freshBrand := fresh brand (by simp only [continuation,Option.bind_some,branded])
    have converted := selected.signature_components valid signatureTyped actual
    have admitted := signatureTyped.components_scoped valid
    obtain ⟨base,actualBrand,baseStarted,actualBranded,rfl,rfl⟩ := started
    have sameBrand := Option.some.inj (branded.symm.trans actualBranded)
    subst actualBrand
    have baseTerm : base.term = handler.environment.term := by obtain ⟨_,rfl⟩ := baseStarted; rfl
    have baseStatic : base.static = handler.environment.static := by obtain ⟨_,rfl⟩ := baseStarted; rfl
    refine ⟨(base.bindBrand brand (.resumption before.nextContinuation)).term sourceSignature.result,
      (base.bindBrand brand (.resumption before.nextContinuation)).term sourceSignature.effects,?_,?_,?_⟩
    · change (base.bindBrand brand (.resumption before.nextContinuation)).term lexical.type = _
      simp only [localType,Context.term,Context.bindBrand,ScopeInstantiation.term,
        Table.get_set,Option.map_some,Option.getD_some]
    · change Equal _ base.static _ _
      rw [Context.bindBrand_term freshBrand admitted.2.1,baseTerm,baseStatic]
      exact converted.2.1
    · change Equal _ base.static _ _
      rw [Context.bindBrand_term freshBrand admitted.2.2,baseTerm,baseStatic]
      exact converted.2.2

end Glorious.Language.Execution
