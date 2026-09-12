import GloriousLanguage.InvocationLifecycle
import GloriousLanguage.EffectPreservation
import GloriousLanguage.ClauseEntryContextTyping
import GloriousLanguage.ContinuationCreation
import GloriousLanguage.PayloadHandoff
import GloriousLanguage.PatternPlanTransport

/-! Actual handler execution consumes positive payload and continuation
allocation requests. Every exhausted prefix remains in the fatal endpoint;
only completed creation publishes a suspension event and clause cursor. -/
namespace Glorious.Language.Contracts

open Kernel Execution

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
    (caller : boundary.OperationCallerPermission program state id arguments payload .terminal) :
    ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (event = none ∨ event = some (.fatal .resource) ∧ after.task = .fatal .resource) := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.terminal terminal
  subst disposition
  obtain ⟨source,withRegion,_,sourceHome,_⟩ := ready.preflight
  let clause := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  have started : StartsClause state handler clause withRegion := ⟨sourceHome.fresh,rfl⟩
  obtain ⟨kept,moved,outcome,handoff,movedTyped,permission⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  cases outcome with
  | exhausted =>
    exact ⟨_,_,.terminalPayloadExhausted pending selected terminal noContinuation route started handoff,
      movedTyped,Or.inr ⟨rfl,rfl⟩⟩
  | complete =>
    obtain ⟨roots,selectedRoots,allowed⟩ := permission rfl
    obtain ⟨actions,planned⟩ := route.2.2.handoff_payloadPlan started.1
      (started.1.wellFormed typed.1) handoff clause.term
    exact ⟨_,none,.terminal pending selected terminal noContinuation route started handoff selectedRoots allowed planned,
      movedTyped,Or.inl rfl⟩

/-- Omitting the continuation binder does not bypass ordered preparation.
The admitted declaration supplies a finite quantity even on exhaustion. -/
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
    (caller : boundary.OperationCallerPermission program state id arguments payload (.resumptive quantity)) :
    ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (event = some (.suspend state.nextContinuation) ∨
        event = some (.fatal .resource) ∧ after.task = .fatal .resource) ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload → event = some (.suspend state.nextContinuation) →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.resumptive resumptive quantityAt
  subst disposition
  have finite : ∃ bound, quantity.upper = some bound := by
    rcases selected.surface_resumption valid resumptive quantityAt with rfl | ⟨n,_,_,rfl⟩ <;> exact ⟨_,rfl⟩
  obtain ⟨bound,bounded⟩ := finite
  obtain ⟨source,withRegion,_,sourceHome,_⟩ := ready.preflight
  let clause := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  have started : StartsClause state handler clause withRegion := ⟨sourceHome.fresh,rfl⟩
  obtain ⟨kept,moved,outcome,handoff,movedTyped,permission⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  cases outcome with
  | exhausted =>
    exact ⟨_,_,.suspendTailPayloadExhausted pending selected resumptive quantityAt bounded once noContinuation
      route started handoff,movedTyped,Or.inr ⟨rfl,rfl⟩,fun _ _ _ _ _ impossible => by cases impossible⟩
  | complete =>
    obtain ⟨roots,selectedRoots,allowed⟩ := permission rfl
    obtain ⟨actions,planned⟩ := route.2.2.handoff_payloadPlan started.1
      (started.1.wellFormed typed.1) handoff clause.term
    let homes := (moved.roots.filter (fun entry => entry.1 ∈ roots)).map (fun (id,root) => (id,root.home))
    have saved : SaveHomes moved roots homes := rfl
    have step := EffectStep.suspendTailArm pending selected resumptive quantityAt bounded once noContinuation
      route started handoff selectedRoots allowed saved planned rfl
    exact ⟨_,_,step,step.worldTyped valid inventory typed,Or.inl rfl,
      fun _ _ _ observed outcome _ => observed.capture_lifecycle outcome step⟩

/-- A bound continuation derives its logical compatibility and empty-input
initialization from the actual source arm. Positive physical requests produce
either real creation or a fatal endpoint retaining completed payload transfer
and suspended roots. No successful allocation or payload-plan callback remains. -/
theorem MayAwait.resumption_execution {program : Kernel.Program} {function : Function}
    {state : State} {boundary : InvocationBoundary} {context : Execution.Context}
    {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {lexical : Local} {brand : Identity} {source : Typing.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program state.world)
    (awaiting : MayAwait program function state boundary)
    (pending : state.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantityAt : operation.quantity = some quantity)
    (continuation : arm.continuation = some lexical) (branded : lexical.resumptionBrand = some brand)
    (route : Routes program state id arguments payload abandoned handler owns arm outer)
    (armsTyped : Typing.OperationArmsType program source handler.syntaxNode.operations handler.syntaxNode.result)
    (caller : boundary.OperationCallerPermission program state id arguments payload (.resumptive quantity))
    (continuations : ∀ clause localSlot withRegion kept moved roots,
      StartsResumptionClause state handler lexical clause localSlot withRegion →
      Protects program clause withRegion payload kept moved →
      DelimitedRoots moved handler abandoned (kept.map Address.root) roots →
      ∃ layout, AllocationRequest program.declarations (suspendRoots moved roots state.nextContinuation)
        clause.region localSlot.type layout) :
    ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      (event = some (.suspend state.nextContinuation) ∨
        event = some (.fatal .resource) ∧ after.task = .fatal .resource) ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload → event = some (.suspend state.nextContinuation) →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
  obtain ⟨disposition,matched,ready⟩ := awaiting.operation_ready pending selected
  have mode := matched.resumptive resumptive quantityAt
  subst disposition
  have finite : ∃ bound, quantity.upper = some bound := by
    rcases selected.surface_resumption valid resumptive quantityAt with rfl | ⟨n,_,_,rfl⟩ <;> exact ⟨_,rfl⟩
  obtain ⟨bound,bounded⟩ := finite
  obtain ⟨preparedContext,withRegion,_,sourceHome,_⟩ := ready.preflight
  let base := { handler.environment with activation := state.nextActivation, scope := state.world.nextRegion, region := state.world.nextRegion }
  let clause := base.bindBrand brand (.resumption state.nextContinuation)
  let localSlot := clause.local lexical
  have started : StartsResumptionClause state handler lexical clause localSlot withRegion :=
    ⟨base,brand,⟨sourceHome.fresh,rfl⟩,branded,rfl,rfl⟩
  obtain ⟨kept,moved,outcome,handoff,movedTyped,permission⟩ :=
    ready.handler_permission valid inventory typed (awaiting.outward pending) route started.payload_context caller
  cases outcome with
  | exhausted =>
    exact ⟨_,_,.suspendPayloadExhausted pending selected resumptive quantityAt bounded continuation route started handoff,
      movedTyped,Or.inr ⟨rfl,rfl⟩,fun _ _ _ _ _ impossible => by cases impossible⟩
  | complete =>
    obtain ⟨roots,selectedRoots,allowed⟩ := permission rfl
    have compatible := route.2.2.continuation_binding_type valid armsTyped selected quantityAt continuation started
    obtain ⟨layout,request⟩ := continuations clause localSlot withRegion kept moved roots started handoff selectedRoots
    rcases request.success_or_exhausted (.localSlot clause.activation clause.scope) localSlot.mutable with
      ⟨address,allocated,allocation⟩ | exhausted
    · obtain ⟨created,constructed,initialized⟩ := CreatesContinuation.of_allocation compatible allocation
      obtain ⟨actions,planned⟩ := route.2.2.handoff_payloadPlan started.payload_context.fresh
        (started.payload_context.fresh.wellFormed typed.1) handoff clause.term
      have suspendedTyped := suspendRoots.worldTyped (roots := roots) (id := state.nextContinuation) movedTyped
      have createdPlan := (planned.suspend roots state.nextContinuation).fresh_value suspendedTyped.1 allocation initialized
      let homes := (moved.roots.filter (fun entry => entry.1 ∈ roots)).map (fun (id,root) => (id,root.home))
      have saved : SaveHomes moved roots homes := rfl
      have step := EffectStep.suspend pending selected resumptive quantityAt bounded continuation route started
        handoff selectedRoots allowed saved constructed createdPlan rfl
      exact ⟨_,_,step,step.worldTyped valid inventory typed,Or.inl rfl,
        fun _ _ _ observed outcome _ => observed.capture_lifecycle outcome step⟩
    · have step := EffectStep.suspendContinuationExhausted pending selected resumptive quantityAt bounded continuation
        route started handoff selectedRoots allowed compatible exhausted
      exact ⟨_,_,step,step.worldTyped valid inventory typed,Or.inr ⟨rfl,rfl⟩,
        fun _ _ _ _ _ impossible => by cases impossible⟩

/-- Source arm typing chooses the actual terminal, tail or bound execution.
The result distinguishes resource failure from a typed successful clause cursor;
only an actual suspension event establishes the captured lifecycle. -/
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
    (continuations : ∀ quantity lexical, operation.quantity = some quantity → arm.continuation = some lexical →
      ∀ clause localSlot withRegion kept moved roots,
        StartsResumptionClause state handler lexical clause localSlot withRegion →
        Protects program clause withRegion payload kept moved →
        DelimitedRoots moved handler abandoned (kept.map Address.root) roots →
        ∃ layout, AllocationRequest program.declarations (suspendRoots moved roots state.nextContinuation)
          clause.region localSlot.type layout) :
    ∃ after event, EffectStep program state event after ∧ Typing.WorldTyped program after.world ∧
      ((event = some (.fatal .resource) ∧ after.task = .fatal .resource) ∨
       ∃ source runtime actions body locals result,
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
      ((event = none ∨ event = some (.suspend state.nextContinuation)) ∨
        event = some (.fatal .resource) ∧ after.task = .fatal .resource) ∧
      ∀ host start request, ObservationAt program host function boundary start state request →
        request.outcome = .operation id arguments payload → event = some (.suspend state.nextContinuation) →
        LifecycleObserves program host function
          ⟨request,state.nextContinuation,[.suspend state.nextContinuation],after.world,.suspended⟩ := by
    rcases mode with ⟨terminal,absent,_⟩ | ⟨resumptive,quantity,quantityAt,tail | bound⟩
    · obtain ⟨after,event,step,afterTyped,events⟩ := awaiting.terminal_execution valid inventory typed pending selected
        terminal absent route (caller .terminal terminal)
      refine ⟨after,event,step,afterTyped,events.elim (fun silent => Or.inl (Or.inl silent)) Or.inr,?_⟩
      intro host start request observed outcome suspended
      rcases events with silent | ⟨fatal,_⟩
      · cases silent.symm.trans suspended
      · cases Option.some.inj (fatal.symm.trans suspended)
    · obtain ⟨absent,once,_⟩ := tail
      obtain ⟨after,event,step,afterTyped,events,lifecycle⟩ := awaiting.tail_arm_execution valid inventory typed pending selected
        resumptive quantityAt once absent route (caller (.resumptive quantity) ⟨resumptive,quantityAt⟩)
      exact ⟨after,event,step,afterTyped,events.elim (fun captured => Or.inl (Or.inr captured)) Or.inr,lifecycle⟩
    · obtain ⟨lexical,brand,present,localType,_⟩ := bound
      have branded : lexical.resumptionBrand = some brand := by rw [Local.resumptionBrand,localType]
      obtain ⟨after,event,step,afterTyped,events,lifecycle⟩ := awaiting.resumption_execution valid inventory typed pending selected
        resumptive quantityAt present branded route armsTyped (caller (.resumptive quantity) ⟨resumptive,quantityAt⟩)
        (continuations quantity lexical quantityAt present)
      exact ⟨after,event,step,afterTyped,events.elim (fun captured => Or.inl (Or.inr captured)) Or.inr,lifecycle⟩
  obtain ⟨after,event,step,afterTyped,events,lifecycle⟩ := constructed
  refine ⟨after,event,step,afterTyped,?_,lifecycle⟩
  rcases events with success | fatal
  · right
    rcases success with rfl | rfl
    · obtain ⟨source,clause,inner,handler,owns,outer,roots,actions,arm,locals,_,_,task,
        contextTyped,bodyTyped,binders,admitted⟩ := step.terminal_clause_context valid inventory typed handlers pending
      exact ⟨source,clause,actions,arm.body,locals,handler.syntaxNode.result,contextTyped,bodyTyped,binders,admitted,
        Or.inl ⟨rfl,roots,_,task⟩⟩
    · obtain ⟨source,runtime,actions,body,locals,result,task,contextTyped,bodyTyped,binders,admitted⟩ :=
        step.suspended_clause_context valid inventory typed handlers
      exact ⟨source,runtime,actions,body,locals,result,contextTyped,bodyTyped,binders,admitted,Or.inr ⟨rfl,task⟩⟩
  · exact Or.inl fatal

end Glorious.Language.Contracts
