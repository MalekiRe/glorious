import GloriousLanguage.OperationBoundary
import GloriousLanguage.RootSelection
import GloriousLanguage.LocalPreservation
import GloriousLanguage.HandoffProgress

/-! Outward labels carry actual destination and positive payload readiness.
The callee and retained caller share the same post-payload cleanup selection;
their permissions construct the ordinary `ControlStep.leave` rule. Admission
does not assume that a complete machine step already exists. -/
namespace Glorious.Language.Execution

open Kernel

theorem LabelRoute.label_member {frames inner outer : List Frame} {brand region : Identity}
    {context : Context} {type : Term}
    (route : LabelRoute frames brand inner context region type outer) :
    Frame.label context brand region type ∈ frames := by
  rw [route.1]
  exact List.mem_append_right _ List.mem_cons_self

/-- The existing route's no-skipped-brand condition chooses one actual
delimiter. Its source type cannot be swapped for a later same-brand frame. -/
theorem LabelRoute.functional {frames firstInner lastInner firstOuter lastOuter : List Frame}
    {brand firstRegion lastRegion : Identity} {firstContext lastContext : Context}
    {firstType lastType : Term}
    (first : LabelRoute frames brand firstInner firstContext firstRegion firstType firstOuter)
    (last : LabelRoute frames brand lastInner lastContext lastRegion lastType lastOuter) :
    firstInner = lastInner ∧ firstContext = lastContext ∧ firstRegion = lastRegion ∧
      firstType = lastType ∧ firstOuter = lastOuter := by
  rcases List.append_eq_append_iff.mp (first.1.symm.trans last.1) with
    ⟨between,inner,remaining⟩ | ⟨between,inner,remaining⟩
  · cases between with
    | nil =>
      simp only [List.append_nil] at inner
      simp only [List.nil_append] at remaining
      obtain ⟨frame,outer⟩ := List.cons.inj remaining
      obtain ⟨context,_,region,type⟩ := Frame.label.inj frame
      exact ⟨inner.symm,context,region,type,outer⟩
    | cons frame between =>
      have same := (List.cons.inj remaining).1
      apply False.elim
      apply last.2.2 firstContext firstRegion firstType
      rw [inner]
      exact List.mem_append_right _ (same ▸ List.mem_cons_self)
  · cases between with
    | nil =>
      simp only [List.append_nil] at inner
      simp only [List.nil_append] at remaining
      obtain ⟨frame,outer⟩ := List.cons.inj remaining
      obtain ⟨context,_,region,type⟩ := Frame.label.inj frame
      exact ⟨inner,context.symm,region.symm,type.symm,outer.symm⟩
    | cons frame between =>
      have same := (List.cons.inj remaining).1
      apply False.elim
      apply first.2.2 lastContext lastRegion lastType
      rw [inner]
      exact List.mem_append_right _ (same ▸ List.mem_cons_self)

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

/-- Routing, barrier admission and the resident/request preflight are positive
before-state facts. Neither protection nor successful allocation is assumed.
Only a completed actual handoff incurs the callee's residual cleanup duty. -/
structure InvocationBoundary.LabelReady (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (brand : Identity) (argument : ResolvedPlace) : Prop where
  preflight : ∃ abandoned context region type outer value layout,
    LabelRoute before.frames brand abandoned context region type outer ∧
    ResidentHandoffReady program before.world [argument] [value] [argument.address] ∧
    AllocationRequest program.declarations before.world context.region value.type layout
  barriers : ∃ callee, before.frames = callee ++ boundary.ambient ∧
    ∀ frame ∈ callee, frame.ForeignFree
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
    (ready : boundary.LabelReady program before brand argument) :
    ∃ callee, before.frames = callee ++ boundary.ambient ∧ ∀ frame ∈ callee, frame.ForeignFree :=
  ready.barriers

/-- The single payload consumes the common ordered resident preflight. Its
actual Protect is constructed, or the same ready payload exhausts its request
without mutating the before-world. -/
theorem InvocationBoundary.LabelReady.prepare {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {brand : Identity} {argument : ResolvedPlace}
    (valid : before.world.WellFormed) (ready : boundary.LabelReady program before brand argument) :
    ∃ abandoned target region type outer,
      LabelRoute before.frames brand abandoned target region type outer ∧
      ((∃ kept moved, Protect program target before.world argument.address argument.authority kept moved) ∨
        ProtectExhausted program target before.world argument.address argument.authority) := by
  obtain ⟨abandoned,target,region,type,outer,value,layout,route,payload,request⟩ := ready.preflight
  have stored := payload.1.get_left (show [argument][0]? = some argument from rfl)
  obtain ⟨actual,found,stored⟩ := stored
  have same : actual = value := Option.some.inj found.symm
  subst actual
  have admitted := payload.2.1 value List.mem_cons_self
  exact ⟨abandoned,target,region,type,outer,route,
    Protect.success_or_exhausted valid stored admitted.1 admitted.2
      (payload.2.2.2 argument List.mem_cons_self) request⟩

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
    ∃ after event, ControlStep program before event after ∧ Typing.WorldTyped program after.world ∧
      (event = none ∨ event = some (.fatal .resource) ∧ after = { before with task := .fatal .resource }) := by
  obtain ⟨abandoned,target,region,type,outer,route,handoff | exhausted⟩ := ready.prepare typed.1
  · obtain ⟨kept,moved,handoff⟩ := handoff
    have movedTyped := handoff.worldTyped valid inventory typed
    obtain ⟨all,selected⟩ := AbandonedRoots.exists movedTyped.1.1 abandoned [kept.root]
    obtain ⟨caller,ambient,permission⟩ := ready.caller_permission outward route handoff selected
    obtain ⟨callerRoots,callerSelected⟩ := AbandonedRoots.exists movedTyped.1.1 caller [kept.root]
    have allowed := (permission callerRoots callerSelected).mp
      (ambientPermission abandoned target region type outer kept moved route handoff caller ambient callerRoots callerSelected)
    exact ⟨_,_,.leave pending route handoff selected allowed,movedTyped,Or.inl rfl⟩
  · exact ⟨_,_,.leaveExhausted pending route exhausted,typed,Or.inr ⟨rfl,rfl⟩⟩

end Glorious.Language.Contracts
