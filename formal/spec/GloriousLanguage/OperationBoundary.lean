import GloriousLanguage.InvocationBoundary
import GloriousLanguage.RootSelection
import GloriousLanguage.LocalPreservation
import GloriousLanguage.OperationPayloadPreparation

/-! An outward operation contributes its callee-owned share of the same
post-payload disposition obligation used by the actual accepting handler.
The retained ambient stack supplies the other share. Positive preflight
constructs the real ordered preparation, including physical exhaustion. -/
namespace Glorious.Language.Execution

open Kernel

theorem Suspensible.covered {program : RuntimeProgram} {world : World} {all left right : List Identity}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : Suspensible program world left) (last : Suspensible program world right) : Suspensible program world all := by
  constructor
  · intro id loan found live kind touched
    rcases touched with referent | ⟨address,value,member,resident,head⟩
    · exact (cover loan.referent.root referent).elim
        (fun member => first.1 id loan found live kind (Or.inl member))
        (fun member => last.1 id loan found live kind (Or.inl member))
    · exact (cover address.root member).elim
        (fun member => first.1 id loan found live kind (Or.inr ⟨address,value,member,resident,head⟩))
        (fun member => last.1 id loan found live kind (Or.inr ⟨address,value,member,resident,head⟩))
  · intro address value member resident
    exact (cover address.root member).elim
      (fun member => first.2 address value member resident) (fun member => last.2 address value member resident)

theorem Cancelable.covered {program : RuntimeProgram} {world : World} {all left right : List Identity}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : Cancelable program world left) (last : Cancelable program world right) :
    Cancelable program world all := by
  refine ⟨Suspensible.covered cover first.1 last.1,?_⟩
  intro address value member resident
  exact (cover address.root member).elim
    (fun member => first.2 address value member resident) (fun member => last.2 address value member resident)

theorem Replayable.covered {program : RuntimeProgram} {world : World} {all left right : List Identity}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : Replayable program world left) (last : Replayable program world right) :
    Replayable program world all := by
  refine ⟨Suspensible.covered cover first.1 last.1,?_,?_,?_⟩
  · intro address value member resident
    exact (cover address.root member).elim
      (fun member => first.2.1 address value member resident) (fun member => last.2.1 address value member resident)
  · intro address value id loan member resident head found
    exact (cover address.root member).elim
      (fun member => first.2.2.1 address value id loan member resident head found)
      (fun member => last.2.2.1 address value id loan member resident head found)
  · intro id loan found live member
    exact (cover loan.referent.root member).elim
      (fun member => first.2.2.2 id loan found live member) (fun member => last.2.2.2 id loan found live member)

theorem SuspendPermission.compose {program : Kernel.Program} {world : World} {quantity : Quantity}
    {all left right : List Identity} {firstFrames lastFrames : List Frame}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : SuspendPermission program world left quantity firstFrames)
    (last : SuspendPermission program world right quantity lastFrames) :
    SuspendPermission program world all quantity (firstFrames ++ lastFrames) := by
  refine ⟨first.1,Suspensible.covered cover first.2.1 last.2.1,?_,?_,?_⟩
  · intro optional
    exact Cancelable.covered cover (first.2.2.1 optional) (last.2.2.1 optional)
  · intro n bound multiple
    obtain ⟨firstRoots,firstFrames⟩ := first.2.2.2.1 n bound multiple
    obtain ⟨lastRoots,lastFrames⟩ := last.2.2.2.1 n bound multiple
    refine ⟨Replayable.covered cover firstRoots lastRoots,?_⟩
    intro frame member
    exact (List.mem_append.mp member).elim (firstFrames frame) (lastFrames frame)
  · intro authority member
    rw [List.flatMap_append] at member
    exact (List.mem_append.mp member).elim
      (fun inside => first.2.2.2.2 authority inside)
      (fun inside => last.2.2.2.2 authority inside)

theorem OperationDisposition.Permits.compose {program : Kernel.Program} {world : World}
    {disposition : OperationDisposition} {all left right : List Identity} {firstFrames lastFrames : List Frame}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : OperationDisposition.Permits program world left firstFrames disposition)
    (last : OperationDisposition.Permits program world right lastFrames disposition) :
    OperationDisposition.Permits program world all (firstFrames ++ lastFrames) disposition := by
  cases disposition with
  | terminal => exact Cancelable.covered cover first last
  | resumptive quantity => exact SuspendPermission.compose cover first last

theorem OperationDisposition.Permits.restrict {program : Kernel.Program} {world : World}
    {disposition : OperationDisposition} {all roots : List Identity} {frames selectedFrames : List Frame}
    (permission : OperationDisposition.Permits program world all frames disposition)
    (rootsWithin : ∀ id ∈ roots, id ∈ all) (framesWithin : ∀ frame ∈ selectedFrames, frame ∈ frames) :
    OperationDisposition.Permits program world roots selectedFrames disposition := by
  have cover : ∀ id ∈ roots, id ∈ all ∨ id ∈ all := fun id member => Or.inl (rootsWithin id member)
  cases disposition with
  | terminal => exact Cancelable.covered cover permission permission
  | resumptive quantity =>
      refine ⟨permission.1,Suspensible.covered cover permission.2.1 permission.2.1,?_,?_,?_⟩
      · intro optional
        exact Cancelable.covered cover (permission.2.2.1 optional) (permission.2.2.1 optional)
      · intro n bound multiple
        obtain ⟨replayable,framePermission⟩ := permission.2.2.2.1 n bound multiple
        exact ⟨Replayable.covered cover replayable replayable,
          fun frame member => framePermission frame (framesWithin frame member)⟩
      · intro authority member
        obtain ⟨frame,present,inside⟩ := List.mem_flatMap.mp member
        exact permission.2.2.2.2 authority
          (List.mem_flatMap.mpr ⟨frame,framesWithin frame present,inside⟩)

/-- The actual delimiter's ownership splits at a retained invocation boundary.
The handler's computation belongs to the caller share, not the callee share.
All three selections exclude the exact same protected payload homes. -/
theorem DelimitedRoots.split_membership {world : World} {handler : InstalledHandler}
    {callee caller : List Frame} {kept all calleeRoots callerRoots : List Identity}
    (whole : DelimitedRoots world handler (callee ++ caller) kept all)
    (localRoots : AbandonedRoots world callee kept calleeRoots)
    (ambientRoots : DelimitedRoots world handler caller kept callerRoots) :
    ∀ id, id ∈ all ↔ id ∈ calleeRoots ∨ id ∈ callerRoots := by
  intro id
  constructor
  · intro member
    obtain ⟨root,found,live,outside,captured⟩ := (whole.2 id).mp member
    rcases captured with scope | ⟨frame,member,owns⟩
    · exact Or.inr ((ambientRoots.2 id).mpr ⟨root,found,live,outside,Or.inl scope⟩)
    · rcases List.mem_append.mp member with localFrame | ambientFrame
      · exact Or.inl ((localRoots.2 id).mpr ⟨root,found,live,outside,frame,localFrame,owns⟩)
      · exact Or.inr ((ambientRoots.2 id).mpr ⟨root,found,live,outside,Or.inr ⟨frame,ambientFrame,owns⟩⟩)
  · rintro (member | member)
    · obtain ⟨root,found,live,outside,frame,present,owns⟩ := (localRoots.2 id).mp member
      exact (whole.2 id).mpr ⟨root,found,live,outside,Or.inr ⟨frame,List.mem_append_left _ present,owns⟩⟩
    · obtain ⟨root,found,live,outside,captured⟩ := (ambientRoots.2 id).mp member
      refine (whole.2 id).mpr ⟨root,found,live,outside,?_⟩
      rcases captured with scope | ⟨frame,present,owns⟩
      · exact Or.inl scope
      · exact Or.inr ⟨frame,List.mem_append_right _ present,owns⟩

theorem DelimitedRoots.permits_compose {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {disposition : OperationDisposition} {callee caller : List Frame} {kept all calleeRoots callerRoots : List Identity}
    (whole : DelimitedRoots world handler (callee ++ caller) kept all)
    (localRoots : AbandonedRoots world callee kept calleeRoots)
    (ambientRoots : DelimitedRoots world handler caller kept callerRoots)
    (localPermission : OperationDisposition.Permits program world calleeRoots callee disposition)
    (ambientPermission : OperationDisposition.Permits program world callerRoots caller disposition) :
    OperationDisposition.Permits program world all (callee ++ caller) disposition :=
  OperationDisposition.Permits.compose (fun id member => (whole.split_membership localRoots ambientRoots id).mp member)
    localPermission ambientPermission

theorem DelimitedRoots.permits_iff {program : Kernel.Program} {world : World} {handler : InstalledHandler}
    {disposition : OperationDisposition} {callee caller : List Frame} {kept all calleeRoots callerRoots : List Identity}
    (whole : DelimitedRoots world handler (callee ++ caller) kept all)
    (localRoots : AbandonedRoots world callee kept calleeRoots)
    (ambientRoots : DelimitedRoots world handler caller kept callerRoots) :
    OperationDisposition.Permits program world all (callee ++ caller) disposition ↔
      OperationDisposition.Permits program world calleeRoots callee disposition ∧
      OperationDisposition.Permits program world callerRoots caller disposition := by
  constructor
  · intro permission
    exact ⟨permission.restrict
      (fun id member => (whole.split_membership localRoots ambientRoots id).mpr (Or.inl member))
      (fun frame member => List.mem_append_left _ member),
      permission.restrict
      (fun id member => (whole.split_membership localRoots ambientRoots id).mpr (Or.inr member))
      (fun frame member => List.mem_append_right _ member)⟩
  · rintro ⟨localPermission,ambientPermission⟩
    exact whole.permits_compose localRoots ambientRoots localPermission ambientPermission

/-- An actual outward route locates its accepting delimiter in the retained
ambient suffix. This is a consequence of the ordinary route and interval cut,
not an independent handler-selection procedure. -/
theorem Routes.outward_inner {program : Kernel.Program} {before : State}
    {boundary : Contracts.InvocationBoundary} {operation : DeclId} {arguments : List Term}
    {payload : List ResolvedPlace} {abandoned callee outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (route : Routes program before operation arguments payload abandoned handler owns arm outer)
    (stack : before.frames = callee ++ boundary.ambient)
    (outward : ¬ boundary.InternalOperation program before operation arguments payload) :
    ∃ caller, abandoned = callee ++ caller ∧ boundary.ambient = caller ++ .handler handler owns :: outer := by
  rcases List.append_eq_append_iff.mp (route.1.symm.trans stack) with
    ⟨between,calleeFrames,remaining⟩ | ⟨between,abandonedFrames,ambientFrames⟩
  · cases between with
    | nil => exact ⟨[],by simpa only [List.append_nil] using calleeFrames.symm,remaining.symm⟩
    | cons frame between =>
      have remainingFrames := (List.cons.inj remaining).2
      subst outer
      exact False.elim (outward ⟨abandoned,handler,owns,arm,between,route⟩)
  · exact ⟨between,abandonedFrames,ambientFrames⟩

theorem Routes.prefix_foreign_free {program : Kernel.Program} {before : State} {operation : DeclId}
    {arguments : List Term} {payload : List ResolvedPlace} {abandoned callee caller outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (route : Routes program before operation arguments payload abandoned handler owns arm outer)
    (frames : abandoned = callee ++ caller) : ∀ frame ∈ callee, frame.ForeignFree := by
  intro frame member
  apply route.foreign_free frame
  rw [frames]
  exact List.mem_append_left _ member

theorem OperationInstance.definition_eq {program : Kernel.Program} {id : DeclId} {arguments : List Term}
    {first last : OperationDefinition} {firstSignature lastSignature : Signature}
    (left : OperationInstance program id arguments first firstSignature)
    (right : OperationInstance program id arguments last lastSignature) : first = last := by
  obtain ⟨_,firstAt,_⟩ := left
  obtain ⟨_,lastAt,_⟩ := right
  exact Option.some.inj (firstAt.symm.trans lastAt)

/-- The selected declaration determines a finite surface resumption quantity
before payload preparation or physical continuation allocation can succeed. -/
theorem OperationInstance.surface_resumption {program : Kernel.Program} {id : DeclId} {arguments : List Term}
    {operation : OperationDefinition} {signature : Signature} {quantity : Quantity}
    (valid : ProgramWellFormed program.declarations)
    (selected : OperationInstance program id arguments operation signature)
    (resumptive : operation.terminal = false) (quantityAt : operation.quantity = some quantity) :
    quantity.SurfaceResumption := by
  obtain ⟨_,found,_⟩ := selected
  have admitted := (valid.2.2.2.2.1 _
    (List.mem_of_find?_eq_some (Program.operation_lookup found))).2.1
  rcases admitted.2 with ⟨terminal,_⟩ | ⟨_,_,actual,actualAt,surface⟩
  · cases terminal.symm.trans resumptive
  · have same := Option.some.inj (actualAt.symm.trans quantityAt)
    subst actual
    exact surface

theorem OperationDisposition.Matches.terminal {operation : OperationDefinition} {disposition : OperationDisposition}
    (matched : OperationDisposition.Matches operation disposition) (terminal : operation.terminal = true) :
    disposition = .terminal := by
  cases disposition with
  | terminal => rfl
  | resumptive quantity => cases matched.1.symm.trans terminal

theorem OperationDisposition.Matches.resumptive {operation : OperationDefinition} {disposition : OperationDisposition}
    {quantity : Quantity} (matched : OperationDisposition.Matches operation disposition)
    (resumptive : operation.terminal = false) (selected : operation.quantity = some quantity) :
    disposition = .resumptive quantity := by
  cases disposition with
  | terminal => cases matched.symm.trans resumptive
  | resumptive actual =>
      have same := Option.some.inj (matched.2.symm.trans selected)
      cases same
      rfl

theorem OperationDisposition.Matches.functional {operation : OperationDefinition}
    {first last : OperationDisposition} (left : OperationDisposition.Matches operation first)
    (right : OperationDisposition.Matches operation last) : first = last := by
  cases last with
  | terminal => exact left.terminal right
  | resumptive quantity => exact left.resumptive right.1 right.2

end Glorious.Language.Execution

namespace Glorious.Language.Contracts

open Kernel Execution

/-- Admission supplies the complete resident handoff preflight and positive
allocation requests, not a successful physical allocation. Residual disposition
permission is required only for actual completed preparation. Routing barriers
are independent of whether physical allocation succeeds. -/
structure InvocationBoundary.OperationReady (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (payload : List ResolvedPlace) (disposition : OperationDisposition) : Prop where
  preflight : ∃ context withRegion values, OperationPayloadContext before context withRegion ∧
    ResidentHandoffReady program withRegion payload values (payload.map ResolvedPlace.address) ∧
    ∀ value ∈ values, ∃ layout,
      AllocationRequest program.declarations withRegion context.region value.type layout
  barriers : ∃ inner, before.frames = inner ++ boundary.ambient ∧ ∀ frame ∈ inner, frame.ForeignFree
  residual : ∀ context kept moved, PreparedOperationPayload program before payload context kept moved →
    ∃ inner roots, before.frames = inner ++ boundary.ambient ∧
      AbandonedRoots moved inner (kept.map Address.root) roots ∧
      OperationDisposition.Permits program moved roots inner disposition

/-- The actual accepting caller checks only its retained share, after the
same completed ordered payload preparation. -/
def InvocationBoundary.OperationCallerPermission (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
    (disposition : OperationDisposition) : Prop :=
  ∀ abandoned handler owns arm outer clause kept moved,
    Routes program before id arguments payload abandoned handler owns arm outer →
    PreparedOperationPayload program before payload clause kept moved →
    ∀ caller, boundary.ambient = caller ++ .handler handler owns :: outer →
    ∀ roots, DelimitedRoots moved handler caller (kept.map Address.root) roots →
      OperationDisposition.Permits program moved roots caller disposition

theorem InvocationBoundary.OperationReady.foreign_free {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {payload : List ResolvedPlace} {disposition : OperationDisposition}
    (ready : boundary.OperationReady program before payload disposition) :
    ∃ inner, before.frames = inner ++ boundary.ambient ∧ ∀ frame ∈ inner, frame.ForeignFree := ready.barriers

/-- The actual route supplies the admission barrier for its callee prefix.
No completed handoff or effect transition is an admission premise. -/
theorem InvocationBoundary.OperationReady.of_outward_route {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {disposition : OperationDisposition} {callee abandoned outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (route : Routes program before id arguments payload abandoned handler owns arm outer)
    (stack : before.frames = callee ++ boundary.ambient)
    (outward : ¬ boundary.InternalOperation program before id arguments payload)
    (preflight : ∃ context withRegion values, OperationPayloadContext before context withRegion ∧
      ResidentHandoffReady program withRegion payload values (payload.map ResolvedPlace.address) ∧
      ∀ value ∈ values, ∃ layout,
        AllocationRequest program.declarations withRegion context.region value.type layout)
    (residual : ∀ context kept moved, PreparedOperationPayload program before payload context kept moved →
      ∃ roots, AbandonedRoots moved callee (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots callee disposition) :
    boundary.OperationReady program before payload disposition := by
  obtain ⟨caller,frames,_⟩ := route.outward_inner stack outward
  refine ⟨preflight,⟨callee,stack,route.prefix_foreign_free frames⟩,?_⟩
  intro context kept moved actual
  obtain ⟨roots,selected,permission⟩ := residual context kept moved actual
  exact ⟨callee,roots,stack,selected,permission⟩

/-- The positive preflight constructs the actual ordered preparation outcome
at the accepting clause's fresh home, retaining a failed prefix's world. -/
theorem InvocationBoundary.OperationReady.prepare {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {payload : List ResolvedPlace} {disposition : OperationDisposition}
    {context : Execution.Context} {withRegion : World}
    (ready : boundary.OperationReady program before payload disposition)
    (home : OperationPayloadContext before context withRegion) (valid : withRegion.WellFormed) :
    ∃ kept moved outcome,
      ProtectsAttemptFor program context (payload.map ResolvedPlace.address) withRegion payload kept moved outcome ∧
      moved.WellFormed ∧
      (outcome = .complete → ∃ inner roots, before.frames = inner ++ boundary.ambient ∧
        AbandonedRoots moved inner (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots inner disposition) := by
  obtain ⟨source,original,values,sourceHome,readyPayload,requests⟩ := ready.preflight
  have same : original = withRegion := sourceHome.fresh.2.trans home.fresh.2.symm
  subst original
  have sameRegion := sourceHome.region.trans home.region.symm
  obtain ⟨kept,moved,outcome,attempted,movedValid⟩ := PreparedOperationPayloadAttempt.progress home valid readyPayload
    (fun value member => by simpa only [sameRegion] using requests value member)
  have actual := attempted.at_context home
  refine ⟨kept,moved,outcome,actual,movedValid,?_⟩
  intro completed
  subst outcome
  exact ready.residual context kept moved ⟨withRegion,home,actual⟩

/-- The caller's completed-preparation share composes with the callee share
on the same actual protected payload and selected delimited roots. -/
theorem InvocationBoundary.OperationReady.caller_permission {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {disposition : OperationDisposition} {context : Execution.Context} {kept : List Address} {moved : World}
    {abandoned outer : List Frame} {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {all : List Identity}
    (ready : boundary.OperationReady program before payload disposition)
    (outward : ¬ boundary.InternalOperation program before id arguments payload)
    (route : Routes program before id arguments payload abandoned handler owns arm outer)
    (prepared : PreparedOperationPayload program before payload context kept moved)
    (selected : DelimitedRoots moved handler abandoned (kept.map Address.root) all) :
    ∃ caller, boundary.ambient = caller ++ .handler handler owns :: outer ∧
      ∀ callerRoots, DelimitedRoots moved handler caller (kept.map Address.root) callerRoots →
        (OperationDisposition.Permits program moved callerRoots caller disposition ↔
          OperationDisposition.Permits program moved all abandoned disposition) := by
  obtain ⟨callee,calleeRoots,stack,localRoots,localPermission⟩ := ready.residual context kept moved prepared
  obtain ⟨caller,frames,ambient⟩ := route.outward_inner stack outward
  refine ⟨caller,ambient,?_⟩
  intro callerRoots ambientRoots
  rw [frames] at selected ⊢
  exact ⟨fun ambientPermission => selected.permits_compose localRoots ambientRoots localPermission ambientPermission,
    fun permission => ((selected.permits_iff localRoots ambientRoots).mp permission).2⟩

/-- Both actual preparation outcomes retain a typed world. Only completion
selects and composes handler disposition; exhaustion performs no invented
cleanup or capture and does not require successful continuation allocation. -/
theorem InvocationBoundary.OperationReady.handler_permission {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {disposition : OperationDisposition} {abandoned outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    {clause : Execution.Context} {withRegion : World}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (ready : boundary.OperationReady program before payload disposition)
    (outward : ¬ boundary.InternalOperation program before id arguments payload)
    (route : Routes program before id arguments payload abandoned handler owns arm outer)
    (home : OperationPayloadContext before clause withRegion)
    (ambientPermission : boundary.OperationCallerPermission program before id arguments payload disposition) :
    ∃ kept moved outcome,
      ProtectsAttemptFor program clause (payload.map ResolvedPlace.address) withRegion payload kept moved outcome ∧
      Typing.WorldTyped program moved ∧
      (outcome = .complete → ∃ roots,
        DelimitedRoots moved handler abandoned (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots abandoned disposition) := by
  obtain ⟨kept,moved,outcome,handoff,_,_⟩ := ready.prepare home (home.fresh.wellFormed typed.1)
  have movedTyped := handoff.worldTyped valid inventory (home.fresh.worldTyped typed)
  refine ⟨kept,moved,outcome,handoff,movedTyped,?_⟩
  intro completed
  subst outcome
  have prepared : PreparedOperationPayload program before payload clause kept moved := ⟨withRegion,home,handoff⟩
  obtain ⟨roots,selected⟩ := DelimitedRoots.exists movedTyped.1.1 handler abandoned (kept.map Address.root)
  obtain ⟨caller,ambient,permission⟩ := ready.caller_permission outward route prepared selected
  obtain ⟨callerRoots,callerSelected⟩ := DelimitedRoots.exists movedTyped.1.1 handler caller (kept.map Address.root)
  have allowed := (permission callerRoots callerSelected).mp
    (ambientPermission abandoned handler owns arm outer clause kept moved route prepared caller ambient callerRoots callerSelected)
  exact ⟨roots,selected,allowed⟩

end Glorious.Language.Contracts
