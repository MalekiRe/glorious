import GloriousLanguage.InvocationLifecycle
import GloriousLanguage.EffectPreservation

/-! Constructing real handler transitions from the common outward request.
Payload preparation and cleanup/capture root selection are derived from the
callee and caller disposition shares. Clause-pattern and continuation-storage
readiness are explicit remaining inputs, not complete effect-step premises. -/
namespace Glorious.Language.Contracts

open Kernel Execution

/-- Terminal dispatch consumes the same admitted operation and payload as
its real route. The target clause and ordered cleanup list are constructed;
only actual clause-pattern planning is supplied by its independent producer. -/
theorem MayAwait.terminal_execution {program : Kernel.Program} {function : Function}
    {state : State} {boundary : InvocationBoundary} {context : Execution.Context}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {operation : OperationDefinition} {signature : Signature} {abandoned outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world)
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (terminal : operation.terminal = true) (noContinuation : arm.continuation = none)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (caller : boundary.OperationCallerPermission program state id arguments payload .terminal)
    (patterns : ∀ clause withRegion kept moved,
      StartsClause state handler clause withRegion → Protects program clause withRegion payload kept moved →
      ∃ actions, PayloadPlan program.declarations moved kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions) :
    ∃ after, EffectStep program state none after ∧ Typing.WorldTyped program after.world := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.terminal terminal
  subst disposition
  obtain ⟨source,_,_,withRegion,sourceHome,_⟩ := ready.prepared
  let clause := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  have started : StartsClause state handler clause withRegion := ⟨sourceHome.fresh,rfl⟩
  obtain ⟨kept,moved,roots,handoff,selectedRoots,allowed,movedTyped⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  obtain ⟨actions,planned⟩ := patterns clause withRegion kept moved started handoff
  exact ⟨_,.terminal pending selected terminal noContinuation route started handoff selectedRoots allowed planned,movedTyped⟩

/-- An omitted continuation binder still captures and resumes through the
ordinary tail-arm rule. Its saved homes and quantitative bound are constructed
from the same selected roots and actual admitted quantity. -/
theorem MayAwait.tail_arm_execution {program : Kernel.Program} {function : Function}
    {state : State} {boundary : InvocationBoundary} {context : Execution.Context}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world)
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantityAt : operation.quantity = some quantity)
    (once : quantity.Contains 1) (noContinuation : arm.continuation = none)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (caller : boundary.OperationCallerPermission program state id arguments payload (.resumptive quantity))
    (patterns : ∀ clause withRegion kept moved,
      StartsClause state handler clause withRegion → Protects program clause withRegion payload kept moved →
      ∃ actions, PayloadPlan program.declarations moved kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions) :
    ∃ after, EffectStep program state (some (.suspend state.nextContinuation)) after ∧
      Typing.WorldTyped program after.world ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.resumptive resumptive quantityAt
  subst disposition
  obtain ⟨source,_,_,withRegion,sourceHome,_⟩ := ready.prepared
  let clause := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  have started : StartsClause state handler clause withRegion := ⟨sourceHome.fresh,rfl⟩
  obtain ⟨kept,moved,roots,handoff,selectedRoots,allowed,_⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  have bound : ∃ bound, quantity.upper = some bound := by
    rcases allowed.1 with rfl | ⟨n,_,_,rfl⟩ <;> exact ⟨_,rfl⟩
  obtain ⟨bound,bounded⟩ := bound
  obtain ⟨actions,planned⟩ := patterns clause withRegion kept moved started handoff
  let homes := (moved.roots.filter (fun entry => entry.1 ∈ roots)).map (fun (id,root) => (id,root.home))
  have saved : SaveHomes moved roots homes := rfl
  have step := EffectStep.suspendTailArm pending selected resumptive quantityAt bounded once noContinuation
    route started handoff selectedRoots allowed saved planned rfl
  exact ⟨_,step,step.worldTyped valid inventory typed,
    fun _ _ _ observed outcome => observed.capture_lifecycle outcome step⟩

/-- A bound resumption has the same capture construction. Its actual local
continuation allocation and payload plan are separate producer obligations;
neither a resulting state nor a completed transition is an input. -/
theorem MayAwait.resumption_execution {program : Kernel.Program} {function : Function}
    {state : State} {boundary : InvocationBoundary} {context : Execution.Context}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {lexical : Local} {brand : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world)
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantityAt : operation.quantity = some quantity)
    (continuation : arm.continuation = some lexical) (branded : lexical.resumptionBrand = some brand)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (caller : boundary.OperationCallerPermission program state id arguments payload (.resumptive quantity))
    (continuations : ∀ clause localSlot withRegion kept moved roots,
      StartsResumptionClause state handler lexical clause localSlot withRegion →
      Protects program clause withRegion payload kept moved →
      DelimitedRoots moved handler abandoned (kept.map Address.root) roots →
      ∃ address created,
        CreatesContinuation program clause (suspendRoots moved roots state.nextContinuation) state.nextContinuation
          signature (clause.term handler.syntaxNode.result) signature.effects quantity localSlot address created ∧
        ∃ actions, PayloadPlan program.declarations created kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions) :
    ∃ after, EffectStep program state (some (.suspend state.nextContinuation)) after ∧
      Typing.WorldTyped program after.world ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.resumptive resumptive quantityAt
  subst disposition
  obtain ⟨source,_,_,withRegion,sourceHome,_⟩ := ready.prepared
  let base := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  let clause := base.bindBrand brand (.resumption state.nextContinuation)
  let localSlot := clause.local lexical
  have started : StartsResumptionClause state handler lexical clause localSlot withRegion :=
    ⟨base,brand,⟨sourceHome.fresh,rfl⟩,branded,rfl,rfl⟩
  obtain ⟨kept,moved,roots,handoff,selectedRoots,allowed,_⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  have bound : ∃ bound, quantity.upper = some bound := by
    rcases allowed.1 with rfl | ⟨n,_,_,rfl⟩ <;> exact ⟨_,rfl⟩
  obtain ⟨bound,bounded⟩ := bound
  obtain ⟨address,created,constructed,actions,planned⟩ :=
    continuations clause localSlot withRegion kept moved roots started handoff selectedRoots
  let homes := (moved.roots.filter (fun entry => entry.1 ∈ roots)).map (fun (id,root) => (id,root.home))
  have saved : SaveHomes moved roots homes := rfl
  have step := EffectStep.suspend pending selected resumptive quantityAt bounded continuation route started
    handoff selectedRoots allowed saved constructed planned rfl
  exact ⟨_,step,step.worldTyped valid inventory typed,
    fun _ _ _ observed outcome => observed.capture_lifecycle outcome step⟩

end Glorious.Language.Contracts
