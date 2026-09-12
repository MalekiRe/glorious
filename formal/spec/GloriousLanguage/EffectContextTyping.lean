import GloriousLanguage.ContextTyping
import GloriousLanguage.EffectPreservation

/-! Effect transitions retain lexical storage declarations even when the
active computation is suspended, replayed or cancelled. This theorem concerns
the original contexts; relocated contexts additionally require the captured
frame's lifetime and scope boundary. -/
namespace Glorious.Language

theorem World.rehome_bindingStorageTyped {program : Program} {before : World}
    (select : Identity → Root → Home) {address : Address} {type : Term}
    (binding : Typing.BindingStorageTyped program before address type) :
    Typing.BindingStorageTyped program { before with roots := before.roots.map (fun (id,root) =>
      (id,{ root with home := select id root })) } address type := by
  cases binding with
  | root whole declared =>
    refine .root whole ?_
    rw [World.rehome_get,Option.map_map]
    exact declared
  | lent found live referent referenced located =>
    exact .lent found live referent (referenced.reads (World.rehome_read before select))
      (World.rehome_addressType select located)

theorem Typing.ValueTyped.continuation_fields {program : Kernel.Program} {world : World} {value : Value} {id : Identity}
    (typed : Typing.ValueTyped program world value) (head : value.head = .continuation id) : value.fields = [] := by
  cases typed with
  | aggregate shape _ =>
    rcases shape with ⟨_,_,impossible⟩ | ⟨_,_,_,_,_,_,impossible,_,_⟩ | ⟨_,_,_,_,_,_,_,impossible,_⟩
    all_goals simp_all only [Value.head]
    all_goals cases head
  | callable => cases head
  | bindings => cases head
  | unit => rfl
  | scalar => rfl
  | reference => rfl
  | pointer => rfl
  | operation => rfl
  | label => rfl
  | continuation => rfl
  | available => rfl

namespace Execution

theorem Relocation.old_bindingStorageTyped {program : Program} {world : World} {map : Relocation} {homes : Table Home}
    {address : Address} {type : Term} (binding : Typing.BindingStorageTyped program world address type) :
    Typing.BindingStorageTyped program (map.copyWorld world homes) address type := by
  cases binding with
  | root whole declared =>
    obtain ⟨root,found,atType⟩ := Option.map_eq_some_iff.mp declared
    exact .root whole (by rw [Relocation.old_root found]; exact congrArg some atType)
  | lent found live referent referenced located =>
    obtain ⟨handle,value,resident,head⟩ := referenced
    exact .lent (Relocation.old_loan found) live referent
      ⟨handle,value,Relocation.old_resident resident,head⟩ (Relocation.old_addressType located)

theorem CopiesSnapshot.contextBindingsTyped {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation}
    (copied : CopiesSnapshot program before suspension map after)
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after.world source runtime := by
  rw [copied.result]
  exact typed.world (fun _ _ binding => Relocation.old_bindingStorageTyped binding)

theorem suspendRoots.contextBindingsTyped {program : Kernel.Program} {before : World} {roots : List Identity} {id : Identity}
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program (suspendRoots before roots id) source runtime := by
  rw [suspendRoots.eq_rehome]
  exact typed.world (fun _ _ binding => World.rehome_bindingStorageTyped
    (fun key root => if key ∈ roots then .suspended id else root.home) binding)

theorem restoreRoots.contextBindingsTyped {program : Kernel.Program} {before : World} {homes : Table Home}
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program (restoreRoots before homes) source runtime :=
  typed.world (fun _ _ binding => World.rehome_bindingStorageTyped (fun id root => (homes.get id).getD root.home) binding)

theorem Protect.contextBindingsTyped {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (worldTyped : Typing.WorldTyped program before)
    (kept : Protect program context before source authority destination after)
    {lexical : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before lexical runtime) :
    Typing.ContextBindingsTyped program after lexical runtime := by
  obtain ⟨_,_,_,⟨_,allocated⟩,moved⟩ := kept
  exact typed.world (fun _ _ binding =>
    moved.bindingStorageTyped (allocated.wellFormed worldTyped.1) (allocated.bindingStorageTyped worldTyped.1 binding))

theorem Protects.contextBindingsTyped {program : Kernel.Program} {context : Context} {before after : World}
    {sources : List ResolvedPlace} {destinations : List Address}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before)
    (kept : Protects program context before sources destinations after)
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime := by
  induction kept with
  | nil => exact typed
  | cons first _ ih => exact ih (first.worldTyped valid inventory worldTyped) (first.contextBindingsTyped worldTyped typed)

theorem CreatesContinuation.preserves_contextBindingsTyped {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity localSlot address}
    (worldTyped : Typing.WorldTyped program before)
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before source runtime) :
    Typing.ContextBindingsTyped program after source runtime := by
  obtain ⟨_,_,_,allocated,constructed⟩ := created
  exact typed.world (fun _ _ binding => constructed.bindingStorageTyped (allocated.wellFormed worldTyped.1)
    (allocated.bindingStorageTyped worldTyped.1 binding))

/-- The whole actual effect relation preserves every retained original
context. Releasing a continuation changes its control obligation but does not
erase an invocation reference hidden in some other owner. -/
theorem EffectStep.contextBindingsTyped {program : Kernel.Program} {before after : State} {event : Option Event}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (worldTyped : Typing.WorldTyped program before.world) (step : EffectStep program before event after)
    {source : Typing.Context} {runtime : Context}
    (typed : Typing.ContextBindingsTyped program before.world source runtime) :
    Typing.ContextBindingsTyped program after.world source runtime := by
  cases step with
  | install _ installed => exact installed.preserves_contextBindingsTyped valid inventory worldTyped typed
  | operationCall => exact typed
  | terminal _ _ _ _ _ started kept _ _ _ =>
    exact kept.contextBindingsTyped valid inventory (started.worldTyped worldTyped) (started.preserves_contextBindingsTyped typed)
  | suspend _ _ _ _ _ _ _ started kept _ _ _ created _ _ =>
    exact created.preserves_contextBindingsTyped
      (suspendRoots.worldTyped (kept.worldTyped valid inventory (started.worldTyped worldTyped)))
      (suspendRoots.contextBindingsTyped
        (kept.contextBindingsTyped valid inventory (started.worldTyped worldTyped) (started.preserves_contextBindingsTyped typed)))
  | suspendTailArm _ _ _ _ _ _ _ _ started kept _ _ _ _ _ =>
    exact suspendRoots.contextBindingsTyped
      (kept.contextBindingsTyped valid inventory (started.worldTyped worldTyped) (started.preserves_contextBindingsTyped typed))
  | continuationCall => exact typed
  | tailArmReturn => exact typed
  | resumeLast _ _ _ _ restored kept =>
    subst restored
    exact kept.contextBindingsTyped (restoreRoots.worldTyped worldTyped) (restoreRoots.contextBindingsTyped typed)
  | resumeCopy _ _ _ _ copied kept =>
    exact kept.contextBindingsTyped (copied.worldTyped valid inventory worldTyped) (copied.contextBindingsTyped typed)
  | resumeReturns _ _ kept => exact kept.contextBindingsTyped worldTyped typed
  | completionIdentity _ _ _ started kept _ _ =>
    exact kept.contextBindingsTyped (started.worldTyped worldTyped) (started.preserves_contextBindingsTyped typed)
  | completion _ _ started kept _ _ _ _ =>
    exact kept.contextBindingsTyped (started.worldTyped worldTyped) (started.preserves_contextBindingsTyped typed)
  | completed _ _ _ kept _ _ => exact kept.contextBindingsTyped worldTyped typed
  | serviced _ _ _ kept _ _ => exact kept.contextBindingsTyped worldTyped typed
  | finishedOwnedClause => exact typed
  | finishedLentClause => exact typed
  | disposeContinuation _ stored head permission _ cleared =>
    have valueTyped := World.stores_typed worldTyped.roots stored
    exact typed.world (fun _ _ binding => World.clear_nonreference_leaf_bindingStorageTyped worldTyped.1 stored
      (valueTyped.continuation_fields head) (by intro id; rw [head]; exact ValueHead.noConfusion) permission cleared binding)
  | cancel => exact restoreRoots.contextBindingsTyped typed

end Execution
end Glorious.Language
