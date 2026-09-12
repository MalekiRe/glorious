import GloriousLanguage.OperationBoundary
import GloriousLanguage.RootSelection
import GloriousLanguage.LocalPreservation

/-! Outward labels carry actual destination and payload-preparation evidence.
The callee and retained caller share the same post-payload cleanup selection;
their permissions construct the ordinary `ControlStep.leave` rule. Admission
does not assume that a complete machine step already exists. -/
namespace Glorious.Language.Execution

open Kernel

theorem AbandonedRoots.split_membership {world : World} {callee caller : List Frame}
    {kept all calleeRoots callerRoots : List Identity}
    (whole : AbandonedRoots world (callee ++ caller) kept all)
    (localRoots : AbandonedRoots world callee kept calleeRoots)
    (ambientRoots : AbandonedRoots world caller kept callerRoots) :
    ∀ id, id ∈ all ↔ id ∈ calleeRoots ∨ id ∈ callerRoots := by
  intro id
  constructor
  · intro member
    obtain ⟨root,found,live,outside,frame,member,owns⟩ := (whole.2 id).mp member
    exact (List.mem_append.mp member).elim
      (fun member => Or.inl ((localRoots.2 id).mpr ⟨root,found,live,outside,frame,member,owns⟩))
      (fun member => Or.inr ((ambientRoots.2 id).mpr ⟨root,found,live,outside,frame,member,owns⟩))
  · rintro (member | member)
    · obtain ⟨root,found,live,outside,frame,member,owns⟩ := (localRoots.2 id).mp member
      exact (whole.2 id).mpr ⟨root,found,live,outside,frame,List.mem_append_left _ member,owns⟩
    · obtain ⟨root,found,live,outside,frame,member,owns⟩ := (ambientRoots.2 id).mp member
      exact (whole.2 id).mpr ⟨root,found,live,outside,frame,List.mem_append_right _ member,owns⟩

theorem AbandonedRoots.cancelable_iff {program : RuntimeProgram} {world : World}
    {callee caller : List Frame} {kept all calleeRoots callerRoots : List Identity}
    (whole : AbandonedRoots world (callee ++ caller) kept all)
    (localRoots : AbandonedRoots world callee kept calleeRoots)
    (ambientRoots : AbandonedRoots world caller kept callerRoots) :
    Cancelable program world all ↔
      Cancelable program world calleeRoots ∧ Cancelable program world callerRoots := by
  constructor
  · intro permission
    exact ⟨Cancelable.covered
      (fun id member => Or.inl ((whole.split_membership localRoots ambientRoots id).mpr (Or.inl member)))
      permission permission,
      Cancelable.covered
      (fun id member => Or.inl ((whole.split_membership localRoots ambientRoots id).mpr (Or.inr member)))
      permission permission⟩
  · rintro ⟨localPermission,ambientPermission⟩
    exact Cancelable.covered
      (fun id member => (whole.split_membership localRoots ambientRoots id).mp member)
      localPermission ambientPermission

theorem LabelRoute.outward_inner {before : State} {boundary : Contracts.InvocationBoundary}
    {brand : Identity} {abandoned callee outer : List Frame}
    {context : Context} {region : Identity} {type : Term}
    (route : LabelRoute before.frames brand abandoned context region type outer)
    (stack : before.frames = callee ++ boundary.ambient)
    (outward : ¬ boundary.InternalLabel before brand) :
    ∃ caller, abandoned = callee ++ caller ∧
      boundary.ambient = caller ++ .label context brand region type :: outer := by
  rcases List.append_eq_append_iff.mp (route.1.symm.trans stack) with
    ⟨between,calleeFrames,remaining⟩ | ⟨between,abandonedFrames,ambientFrames⟩
  · cases between with
    | nil => exact ⟨[],by simpa only [List.append_nil] using calleeFrames.symm,remaining.symm⟩
    | cons frame between =>
      have remainingFrames := (List.cons.inj remaining).2
      subst outer
      exact False.elim (outward ⟨abandoned,context,region,type,between,route⟩)
  · exact ⟨between,abandonedFrames,ambientFrames⟩

end Glorious.Language.Execution

namespace Glorious.Language.Contracts

open Kernel Execution

/-- Destination and payload readiness are nonvacuous. Every actual selected
route and payload handoff must leave the callee-owned remainder cancelable.
An active label behind a foreign barrier has no `LabelRoute` witness. -/
structure InvocationBoundary.LabelReady (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (brand : Identity) (argument : ResolvedPlace) : Prop where
  prepared : ∃ abandoned context region type outer kept moved,
    LabelRoute before.frames brand abandoned context region type outer ∧
    Protect program context before.world argument.address argument.authority kept moved
  residual : ∀ abandoned context region type outer kept moved,
    LabelRoute before.frames brand abandoned context region type outer →
    Protect program context before.world argument.address argument.authority kept moved →
    ∃ callee roots, before.frames = callee ++ boundary.ambient ∧
      AbandonedRoots moved callee [kept.root] roots ∧ Cancelable program moved roots

/-- These are only the retained caller's roots, at the same actual destination
and protected payload as the callee. This obligation is consumed to construct
execution, not a promise that an executable transition already exists. -/
def InvocationBoundary.LabelCallerPermission (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (brand : Identity) (argument : ResolvedPlace) : Prop :=
  ∀ abandoned context region type outer kept moved,
    LabelRoute before.frames brand abandoned context region type outer →
    Protect program context before.world argument.address argument.authority kept moved →
    ∀ caller, boundary.ambient = caller ++ .label context brand region type :: outer →
    ∀ roots, AbandonedRoots moved caller [kept.root] roots → Cancelable program moved roots

theorem InvocationBoundary.LabelReady.foreign_free {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {brand : Identity} {argument : ResolvedPlace}
    (ready : boundary.LabelReady program before brand argument)
    (outward : ¬ boundary.InternalLabel before brand) :
    ∃ callee, before.frames = callee ++ boundary.ambient ∧ ∀ frame ∈ callee, frame.ForeignFree := by
  obtain ⟨abandoned,context,region,type,outer,kept,moved,route,handoff⟩ := ready.prepared
  obtain ⟨callee,_,stack,_⟩ := ready.residual abandoned context region type outer kept moved route handoff
  obtain ⟨caller,frames,_⟩ := route.outward_inner stack outward
  refine ⟨callee,stack,?_⟩
  intro frame member
  apply route.2.1 frame
  rw [frames]
  exact List.mem_append_left _ member

theorem InvocationBoundary.LabelReady.caller_permission {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {brand : Identity} {argument : ResolvedPlace}
    {abandoned outer : List Frame} {context : Execution.Context} {region : Identity} {type : Term}
    {kept : Address} {moved : World} {all : List Identity}
    (ready : boundary.LabelReady program before brand argument)
    (outward : ¬ boundary.InternalLabel before brand)
    (route : LabelRoute before.frames brand abandoned context region type outer)
    (handoff : Protect program context before.world argument.address argument.authority kept moved)
    (selected : AbandonedRoots moved abandoned [kept.root] all) :
    ∃ caller, boundary.ambient = caller ++ .label context brand region type :: outer ∧
      ∀ callerRoots, AbandonedRoots moved caller [kept.root] callerRoots →
        (Cancelable program moved callerRoots ↔ Cancelable program moved all) := by
  obtain ⟨callee,calleeRoots,stack,localRoots,localPermission⟩ :=
    ready.residual abandoned context region type outer kept moved route handoff
  obtain ⟨caller,frames,ambient⟩ := route.outward_inner stack outward
  refine ⟨caller,ambient,?_⟩
  intro callerRoots ambientRoots
  rw [frames] at selected
  exact ⟨fun permission => (selected.cancelable_iff localRoots ambientRoots).mpr ⟨localPermission,permission⟩,
    fun permission => ((selected.cancelable_iff localRoots ambientRoots).mp permission).2⟩

/-- Ordered root selection is constructed from the real post-payload world.
Together with callee admission and the caller share it builds the actual leave
rule, with no post-state, cleanup list, or completed step assumed as input. -/
theorem InvocationBoundary.LabelReady.execute {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {brand : Identity} {argument : ResolvedPlace} {context : Execution.Context}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (ready : boundary.LabelReady program before brand argument)
    (outward : ¬ boundary.InternalLabel before brand)
    (pending : before.task = .leave context brand argument)
    (ambientPermission : boundary.LabelCallerPermission program before brand argument) :
    ∃ after, ControlStep program before none after ∧ Typing.WorldTyped program after.world := by
  obtain ⟨abandoned,target,region,type,outer,kept,moved,route,handoff⟩ := ready.prepared
  have movedTyped := handoff.worldTyped valid inventory typed
  obtain ⟨all,selected⟩ := AbandonedRoots.exists movedTyped.1.1 abandoned [kept.root]
  obtain ⟨caller,ambient,permission⟩ := ready.caller_permission outward route handoff selected
  obtain ⟨callerRoots,callerSelected⟩ := AbandonedRoots.exists movedTyped.1.1 caller [kept.root]
  have allowed := (permission callerRoots callerSelected).mp
    (ambientPermission abandoned target region type outer kept moved route handoff caller ambient callerRoots callerSelected)
  exact ⟨_,.leave pending route handoff selected allowed,movedTyped⟩

end Glorious.Language.Contracts
