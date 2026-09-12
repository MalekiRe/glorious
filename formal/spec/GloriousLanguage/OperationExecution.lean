import GloriousLanguage.InvocationLifecycle
import GloriousLanguage.EffectPreservation
import GloriousLanguage.ClauseEntryContextTyping
import GloriousLanguage.ContinuationCreation

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

/-- Source arm typing chooses the actual execution rule. No caller supplies a
terminal flag, one-use proof, continuation binder or generative brand. The
constructed transition also establishes the real clause's typed binder cursor,
behind terminal cleanup or at resumptive pattern entry. Source/runtime
continuation compatibility and handle initialization are derived; pattern
access and successful physical allocation remain producer obligations. -/
theorem MayAwait.source_execution {program : Kernel.Program} {function : Function}
    {state : State} {boundary : InvocationBoundary} {context : Execution.Context}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {operation : OperationDefinition} {signature : Signature} {abandoned outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world)
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (handlers : ∀ handler owns, Frame.handler handler owns ∈ state.frames →
      Typing.InstalledHandlerTyped program state.world handler)
    (caller : ∀ disposition, OperationDisposition.Matches operation disposition →
      boundary.OperationCallerPermission program state id arguments payload disposition)
    (patterns : arm.continuation = none → ∀ clause withRegion kept moved,
      StartsClause state handler clause withRegion → Protects program clause withRegion payload kept moved →
      ∃ actions, PayloadPlan program.declarations moved kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions)
    (continuations : ∀ quantity lexical, operation.quantity = some quantity → arm.continuation = some lexical →
      ∀ clause localSlot withRegion kept moved roots,
        StartsResumptionClause state handler lexical clause localSlot withRegion →
        Protects program clause withRegion payload kept moved →
        DelimitedRoots moved handler abandoned (kept.map Address.root) roots →
        ∃ address layout allocated,
          Allocates program.declarations (suspendRoots moved roots state.nextContinuation)
            (.localSlot clause.activation clause.scope) clause.region localSlot.type layout localSlot.mutable address allocated ∧
          ∀ created, NewValue program.declarations allocated address localSlot.type (.continuation state.nextContinuation) [] created →
            ∃ actions, PayloadPlan program.declarations created kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions) :
    ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (∃ source runtime actions body locals result,
        Typing.ContextBindingsTyped program after.world source runtime ∧
        Typing.CodeType program (source.bindLocals locals) body result ∧
        (ScheduledPattern actions).filterMap PatternAction.boundLocal = locals.map (Local.mapTerms runtime.term) ∧
        (∀ localSlot ∈ locals, localSlot.type.Scoped source.static.scope) ∧
        ((event = none ∧ ∃ roots regions,
          after.task = .cleanup context roots (CloseRegions regions (.pattern runtime (ScheduledPattern actions) body))) ∨
         (event = some (.suspend state.nextContinuation) ∧ after.task = .pattern runtime (ScheduledPattern actions) body))) ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload → event = some (.suspend state.nextContinuation) →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
  obtain ⟨source,_,_,_,_,_,armsTyped⟩ := handlers handler owns route.handler_member
  obtain ⟨actual,sourceSignature,_,_,found,_,_,mode,_,_,_⟩ := armsTyped.member route.2.2.member
  have actualFound : program.declarations.operation id = some operation := by
    obtain ⟨_,found,_⟩ := selected
    exact found
  rw [route.2.2.operation] at found
  have same := Option.some.inj (found.symm.trans actualFound)
  subst actual
  have constructed : ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (event = none ∨ event = some (.suspend state.nextContinuation)) ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload → event = some (.suspend state.nextContinuation) →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
    rcases mode with ⟨terminal,absent,_⟩ | ⟨resumptive,quantity,quantityAt,tail | bound⟩
    · obtain ⟨after,step,afterTyped⟩ := awaiting.terminal_execution valid inventory typed pending selected terminal absent
        route (caller .terminal terminal) (patterns absent)
      exact ⟨after,none,step,afterTyped,Or.inl rfl,fun _ _ _ _ _ impossible => by cases impossible⟩
    · obtain ⟨absent,once,_⟩ := tail
      obtain ⟨after,step,afterTyped,lifecycle⟩ := awaiting.tail_arm_execution valid inventory typed pending selected
        resumptive quantityAt once absent route (caller (.resumptive quantity) ⟨resumptive,quantityAt⟩) (patterns absent)
      exact ⟨after,_,step,afterTyped,Or.inr rfl,fun _ _ _ observed outcome _ => lifecycle _ _ _ observed outcome⟩
    · obtain ⟨lexical,brand,present,localType,_⟩ := bound
      have branded : lexical.resumptionBrand = some brand := by rw [Local.resumptionBrand,localType]
      have prepared : ∀ clause localSlot withRegion kept moved roots,
          StartsResumptionClause state handler lexical clause localSlot withRegion →
          Protects program clause withRegion payload kept moved →
          DelimitedRoots moved handler abandoned (kept.map Address.root) roots →
          ∃ address created,
            CreatesContinuation program clause (suspendRoots moved roots state.nextContinuation) state.nextContinuation
              signature (clause.term handler.syntaxNode.result) signature.effects quantity localSlot address created ∧
            ∃ actions, PayloadPlan program.declarations created kept (arm.patterns.map (Pattern.mapTerms clause.term)) actions := by
        intro clause localSlot withRegion kept moved roots started handoff selectedRoots
        obtain ⟨address,layout,allocated,allocation,patterns⟩ :=
          continuations quantity lexical quantityAt present clause localSlot withRegion kept moved roots started handoff selectedRoots
        obtain ⟨created,constructed,initialized⟩ := route.2.2.creates_continuation valid armsTyped selected quantityAt present started allocation
        exact ⟨address,created,constructed,patterns created initialized⟩
      obtain ⟨after,step,afterTyped,lifecycle⟩ := awaiting.resumption_execution valid inventory typed pending selected
        resumptive quantityAt present branded route (caller (.resumptive quantity) ⟨resumptive,quantityAt⟩) prepared
      exact ⟨after,_,step,afterTyped,Or.inr rfl,fun _ _ _ observed outcome _ => lifecycle _ _ _ observed outcome⟩
  obtain ⟨after,event,step,afterTyped,events,lifecycle⟩ := constructed
  refine ⟨after,event,step,afterTyped,?_,lifecycle⟩
  rcases events with rfl | rfl
  · obtain ⟨source,clause,inner,handler,owns,outer,roots,actions,arm,locals,_,_,task,
      contextTyped,bodyTyped,binders,admitted⟩ := step.terminal_clause_context valid inventory typed handlers pending
    exact ⟨source,clause,actions,arm.body,locals,handler.syntaxNode.result,contextTyped,bodyTyped,binders,admitted,
      Or.inl ⟨rfl,roots,_,task⟩⟩
  · obtain ⟨source,runtime,actions,body,locals,result,task,contextTyped,bodyTyped,binders,admitted⟩ :=
      step.suspended_clause_context valid inventory typed handlers
    exact ⟨source,runtime,actions,body,locals,result,contextTyped,bodyTyped,binders,admitted,Or.inr ⟨rfl,task⟩⟩

end Glorious.Language.Contracts
