import GloriousLanguage.HandoffProgress

/-! One actual ordered payload preparation, including exhaustion, transports
between contexts only when their allocated homes and lifetimes agree. -/
namespace Glorious.Language.Execution
open Kernel

theorem Protect.same_home {program : Kernel.Program} {source target : Context}
    {before after : World} {address destination : Address} {authority : Authority}
    (handoff : Protect program source before address authority destination after)
    (activation : source.activation = target.activation) (scope : source.scope = target.scope)
    (region : source.region = target.region) :
    Protect program target before address authority destination after := by
  obtain ⟨value,allocated,stored,temporary,transferred⟩ := handoff
  refine ⟨value,allocated,stored,?_,transferred⟩
  simpa only [Temporary,activation,scope,region] using temporary

theorem ProtectExhausted.same_home {program : Kernel.Program} {source target : Context}
    {before : World} {address : Address} {authority : Authority}
    (exhausted : ProtectExhausted program source before address authority)
    (region : source.region = target.region) : ProtectExhausted program target before address authority := by
  simpa only [ProtectExhausted,region] using exhausted

theorem ProtectsAttemptFor.same_home {footprint : List Address} {program : Kernel.Program} {source target : Context}
    {before after : World} {payload : List ResolvedPlace} {kept : List Address} {outcome : PreparationOutcome}
    (handoff : ProtectsAttemptFor program source footprint before payload kept after outcome)
    (activation : source.activation = target.activation) (scope : source.scope = target.scope)
    (region : source.region = target.region) :
    ProtectsAttemptFor program target footprint before payload kept after outcome := by
  induction handoff with
  | nil => exact .nil
  | cons ready first _ ih => exact .cons ready (first.same_home activation scope region) ih
  | exhausted ready failed => exact .exhausted ready (failed.same_home region)

theorem ProtectsFor.same_home {footprint : List Address} {program : Kernel.Program} {source target : Context}
    {before after : World} {payload : List ResolvedPlace} {kept : List Address}
    (handoff : ProtectsFor program source footprint before payload kept after)
    (activation : source.activation = target.activation) (scope : source.scope = target.scope)
    (region : source.region = target.region) : ProtectsFor program target footprint before payload kept after :=
  ProtectsAttemptFor.same_home handoff activation scope region

theorem StartsClause.payload_context {before : State} {handler : InstalledHandler}
    {context : Context} {withRegion : World} (started : StartsClause before handler context withRegion) :
    OperationPayloadContext before context withRegion := by
  obtain ⟨fresh,rfl⟩ := started
  exact ⟨fresh,rfl,rfl,rfl⟩

theorem StartsResumptionClause.payload_context {before : State} {handler : InstalledHandler}
    {lexical localSlot : Local} {context : Context} {withRegion : World}
    (started : StartsResumptionClause before handler lexical context localSlot withRegion) :
    OperationPayloadContext before context withRegion := by
  obtain ⟨outer,brand,started,_,rfl,_⟩ := started
  have home := started.payload_context
  exact ⟨home.fresh,home.activation,home.scope,home.region⟩

theorem PreparedOperationPayload.of_clause {program : Kernel.Program} {before : State}
    {handler : InstalledHandler} {payload : List ResolvedPlace} {context : Context}
    {withRegion moved : World} {kept : List Address}
    (started : StartsClause before handler context withRegion)
    (handoff : Protects program context withRegion payload kept moved) :
    PreparedOperationPayload program before payload context kept moved :=
  ⟨withRegion,started.payload_context,handoff⟩

theorem PreparedOperationPayload.of_resumption_clause {program : Kernel.Program} {before : State}
    {handler : InstalledHandler} {payload : List ResolvedPlace} {context : Context}
    {lexical localSlot : Local} {withRegion moved : World} {kept : List Address}
    (started : StartsResumptionClause before handler lexical context localSlot withRegion)
    (handoff : Protects program context withRegion payload kept moved) :
    PreparedOperationPayload program before payload context kept moved :=
  ⟨withRegion,started.payload_context,handoff⟩

/-- A nonempty preparation witness works at the exact fresh home chosen by
any actual accepting clause. Only environment/brand coordinates may differ;
the protected addresses and resulting world remain the same. -/
theorem PreparedOperationPayloadAttempt.at_context {program : Kernel.Program} {before : State}
    {payload : List ResolvedPlace} {source target : Context} {kept : List Address}
    {moved withRegion : World} {outcome : PreparationOutcome}
    (prepared : PreparedOperationPayloadAttempt program before payload source kept moved outcome)
    (targetHome : OperationPayloadContext before target withRegion) :
    ProtectsAttemptFor program target (payload.map ResolvedPlace.address) withRegion payload kept moved outcome := by
  obtain ⟨original,sourceHome,handoff⟩ := prepared
  have same : original = withRegion := sourceHome.fresh.2.trans targetHome.fresh.2.symm
  subst original
  exact handoff.same_home (sourceHome.activation.trans targetHome.activation.symm)
    (sourceHome.scope.trans targetHome.scope.symm) (sourceHome.region.trans targetHome.region.symm)

theorem PreparedOperationPayload.at_context {program : Kernel.Program} {before : State}
    {payload : List ResolvedPlace} {source target : Context} {kept : List Address} {moved withRegion : World}
    (prepared : PreparedOperationPayload program before payload source kept moved)
    (targetHome : OperationPayloadContext before target withRegion) :
    Protects program target withRegion payload kept moved :=
  PreparedOperationPayloadAttempt.at_context prepared targetHome

/-- Positive requests and whole-batch readiness construct the actual payload
preparation outcome. Successful writes and physical allocation are not inputs. -/
theorem PreparedOperationPayloadAttempt.progress {program : Kernel.Program} {before : State}
    {payload : List ResolvedPlace} {values : List Value} {context : Context} {withRegion : World}
    (home : OperationPayloadContext before context withRegion) (valid : withRegion.WellFormed)
    (ready : ResidentHandoffReady program withRegion payload values (payload.map ResolvedPlace.address))
    (requests : ∀ value ∈ values, ∃ layout,
      AllocationRequest program.declarations withRegion context.region value.type layout) :
    ∃ kept moved outcome, PreparedOperationPayloadAttempt program before payload context kept moved outcome ∧ moved.WellFormed := by
  obtain ⟨kept,moved,outcome,attempted⟩ := ProtectsAttemptFor.progress valid ready
    (fun source member => List.mem_map.mpr ⟨source,member,rfl⟩) requests
  exact ⟨kept,moved,outcome,⟨withRegion,home,attempted⟩,attempted.wellFormed valid⟩

theorem Step.terminal_payload_exhausted {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {operation : OperationDefinition} {signature : Signature} {clause preparedContext : Context}
    {withRegion moved : World} {kept : List Address}
    (task : before.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (terminal : operation.terminal = true) (noContinuation : arm.continuation = none)
    (route : Routes program before id arguments payload inner handler owns arm outer)
    (started : StartsClause before handler clause withRegion)
    (attempted : PreparedOperationPayloadAttempt program before payload preparedContext kept moved .exhausted) :
    Step program host before (some (.fatal .resource))
      { before with world := moved, task := .fatal .resource, nextActivation := before.nextActivation+1 } :=
  Or.inr (Or.inr (Or.inl (.terminalPayloadExhausted task selected terminal noContinuation route started
    (attempted.at_context started.payload_context))))

theorem Step.suspend_payload_exhausted {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity} {bound : Nat}
    {clause preparedContext : Context} {lexical localSlot : Local} {withRegion moved : World} {kept : List Address}
    (task : before.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantitySelected : operation.quantity = some quantity)
    (finite : quantity.upper = some bound) (continuation : arm.continuation = some lexical)
    (route : Routes program before id arguments payload inner handler owns arm outer)
    (started : StartsResumptionClause before handler lexical clause localSlot withRegion)
    (attempted : PreparedOperationPayloadAttempt program before payload preparedContext kept moved .exhausted) :
    Step program host before (some (.fatal .resource))
      { before with world := moved, task := .fatal .resource, nextActivation := before.nextActivation+1 } :=
  Or.inr (Or.inr (Or.inl (.suspendPayloadExhausted task selected resumptive quantitySelected finite continuation
    route started (attempted.at_context started.payload_context))))

theorem Step.suspend_tail_payload_exhausted {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {inner outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity} {bound : Nat}
    {clause preparedContext : Context} {withRegion moved : World} {kept : List Address}
    (task : before.task = .perform context id arguments payload)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantitySelected : operation.quantity = some quantity)
    (finite : quantity.upper = some bound) (one : quantity.Contains 1) (continuation : arm.continuation = none)
    (route : Routes program before id arguments payload inner handler owns arm outer)
    (started : StartsClause before handler clause withRegion)
    (attempted : PreparedOperationPayloadAttempt program before payload preparedContext kept moved .exhausted) :
    Step program host before (some (.fatal .resource))
      { before with world := moved, task := .fatal .resource, nextActivation := before.nextActivation+1 } :=
  Or.inr (Or.inr (Or.inl (.suspendTailPayloadExhausted task selected resumptive quantitySelected finite one continuation
    route started (attempted.at_context started.payload_context))))

end Glorious.Language.Execution
