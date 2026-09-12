import GloriousLanguage.ConstructionPreservation
import GloriousLanguage.LocalPreservation
import GloriousLanguage.SnapshotWorldTyping

/-! Handler installation, continuation creation and effect transitions
preserve storage typing through their actual input-world producers. Changing
a suspended root's home changes control ownership, not its stored value or
physical storage identity. Multi-shot replay consumes the proved snapshot
relocation and external-referent scope boundary. -/
namespace Glorious.Language
namespace Execution

theorem Installs.worldTyped {program : Kernel.Program} {before : State} {outer syntaxNode handler after}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (installed : Installs program before outer syntaxNode handler after) : Typing.WorldTyped program after := by
  obtain ⟨first,second,sources,captures,captured,bindings,bound,disposed,one,two,_,capturedValues,boundValues,retired,rfl,_⟩ := installed
  exact retired.worldTyped (boundValues.worldTyped valid inventory
    (capturedValues.worldTyped valid inventory (two.worldTyped (one.worldTyped typed))))

theorem StartsClause.worldTyped {program : Kernel.Program} {before : State} {handler context after}
    (typed : Typing.WorldTyped program before.world) (started : StartsClause before handler context after) :
    Typing.WorldTyped program after := started.1.worldTyped typed

theorem StartsResumptionClause.worldTyped {program : Kernel.Program} {before : State} {handler lexical context localSlot after}
    (typed : Typing.WorldTyped program before.world)
    (started : StartsResumptionClause before handler lexical context localSlot after) : Typing.WorldTyped program after := by
  obtain ⟨outer,brand,started,_⟩ := started
  exact started.worldTyped typed

theorem CreatesContinuation.worldTyped {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity localSlot address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before)
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    Typing.WorldTyped program after := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  apply constructed.empty_worldTyped valid inventory (allocation.worldTyped typed) (by simp) (by simp)
  obtain ⟨argument,actualEffects,shape,_⟩ := type
  exact .continuation ⟨argument,answer,actualEffects,quantity,shape⟩

/-- Every effect transition, including independently relocated multi-shot
replay, preserves the full storage invariant. -/
theorem EffectStep.worldTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world) (step : EffectStep program before event after) :
    Typing.WorldTyped program after.world := by
  cases step with
  | install task installed => exact installed.worldTyped valid inventory typed
  | operationCall => exact typed
  | terminal task selected terminal continuation routes started keptTransfer roots cancelable plan =>
    exact keptTransfer.worldTyped valid inventory (started.worldTyped typed)
  | terminalPayloadExhausted _ _ _ _ _ started attempted =>
    exact attempted.worldTyped valid inventory (started.worldTyped typed)
  | suspendPayloadExhausted _ _ _ _ _ _ _ started attempted =>
    exact attempted.worldTyped valid inventory (started.worldTyped typed)
  | suspendTailPayloadExhausted _ _ _ _ _ _ _ _ started attempted =>
    exact attempted.worldTyped valid inventory (started.worldTyped typed)
  | suspendContinuationExhausted _ _ _ _ _ _ _ started keptTransfer _ _ _ _ =>
    exact suspendRoots.worldTyped (keptTransfer.worldTyped valid inventory (started.worldTyped typed))
  | suspend task selected terminal quantity bound continuation routes started keptTransfer roots permission homes created plan suspension =>
    exact created.worldTyped valid inventory
      (suspendRoots.worldTyped (keptTransfer.worldTyped valid inventory (started.worldTyped typed)))
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer roots permission homes plan suspension =>
    exact suspendRoots.worldTyped (keptTransfer.worldTyped valid inventory (started.worldTyped typed))
  | continuationCall => exact typed
  | tailArmReturn => exact typed
  | resumeLast task found obligation remaining restored keptTransfer =>
    subst restored
    exact keptTransfer.worldTyped valid inventory (restoreRoots.worldTyped typed)
  | resumeCopy task found obligation remaining copied keptTransfer =>
    exact keptTransfer.worldTyped valid inventory (copied.worldTyped valid inventory typed)
  | resumeReturns task frames keptTransfer => exact keptTransfer.worldTyped valid inventory typed
  | completionIdentity task frames completion started keptTransfer roots permission =>
    exact keptTransfer.worldTyped valid inventory (started.worldTyped typed)
  | completion task frames started keptTransfer roots permission arm plan =>
    exact keptTransfer.worldTyped valid inventory (started.worldTyped typed)
  | completed task frames activation keptTransfer roots permission => exact keptTransfer.worldTyped valid inventory typed
  | serviced task frames activation keptTransfer roots permission => exact keptTransfer.worldTyped valid inventory typed
  | finishedOwnedClause => exact typed
  | finishedLentClause => exact typed
  | disposeContinuation task stored head permission suspension cleared => exact World.clear_worldTyped typed permission cleared
  | cancel => exact restoreRoots.worldTyped typed

end Execution

end Glorious.Language
