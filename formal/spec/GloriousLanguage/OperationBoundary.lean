import GloriousLanguage.OperationPayloadPreparation
import GloriousLanguage.InvocationBoundary
import GloriousLanguage.RootSelection
import GloriousLanguage.LocalPreservation

/-! An outward operation contributes its callee-owned share of the same
post-payload disposition obligation used by the actual accepting handler.
The retained ambient stack supplies the other share. Preparation is the real
ordered `Protects` relation and must have a witness before admission can hold. -/
namespace Glorious.Language.Execution

open Kernel

theorem Suspensible.covered {world : World} {all left right : List Identity}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : Suspensible world left) (last : Suspensible world right) : Suspensible world all := by
  intro id loan found live touched
  rcases touched with referent | ⟨address,value,member,resident,head⟩
  · exact (cover loan.referent.root referent).elim
      (fun member => first id loan found live (Or.inl member))
      (fun member => last id loan found live (Or.inl member))
  · exact (cover address.root member).elim
      (fun member => first id loan found live (Or.inr ⟨address,value,member,resident,head⟩))
      (fun member => last id loan found live (Or.inr ⟨address,value,member,resident,head⟩))

theorem Cancelable.covered {program : Language.Program} {world : World} {all left right : List Identity}
    (cover : ∀ id ∈ all, id ∈ left ∨ id ∈ right)
    (first : Cancelable program world left) (last : Cancelable program world right) :
    Cancelable program world all := by
  refine ⟨Suspensible.covered cover first.1 last.1,?_⟩
  intro address value member resident
  exact (cover address.root member).elim
    (fun member => first.2 address value member resident) (fun member => last.2 address value member resident)

theorem Replayable.covered {program : Language.Program} {world : World} {all left right : List Identity}
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
  refine ⟨first.1,Suspensible.covered cover first.2.1 last.2.1,?_,?_⟩
  · intro optional
    exact Cancelable.covered cover (first.2.2.1 optional) (last.2.2.1 optional)
  · intro n bound multiple
    obtain ⟨firstRoots,firstFrames⟩ := first.2.2.2 n bound multiple
    obtain ⟨lastRoots,lastFrames⟩ := last.2.2.2 n bound multiple
    refine ⟨Replayable.covered cover firstRoots lastRoots,?_⟩
    intro frame member
    exact (List.mem_append.mp member).elim (firstFrames frame) (lastFrames frame)

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
      refine ⟨permission.1,Suspensible.covered cover permission.2.1 permission.2.1,?_,?_⟩
      · intro optional
        exact Cancelable.covered cover (permission.2.2.1 optional) (permission.2.2.1 optional)
      · intro n bound multiple
        obtain ⟨replayable,framePermission⟩ := permission.2.2.2 n bound multiple
        exact ⟨Replayable.covered cover replayable replayable,
          fun frame member => framePermission frame (framesWithin frame member)⟩

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

/-- Preparation is nonvacuous, and every actual preparation must leave the
callee-owned remainder with the selected operation's disposition permission.
Its frame prefix must also permit actual routing: a foreign barrier is not an
outward request merely because no internal handler can be reached. Ambient
storage and barriers remain the caller's obligations. Isolated calls use the
same frame-owned selection with an empty ambient suffix. -/
structure InvocationBoundary.OperationReady (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (payload : List ResolvedPlace) (disposition : OperationDisposition) : Prop where
  prepared : ∃ context kept moved, PreparedOperationPayload program before payload context kept moved
  residual : ∀ context kept moved, PreparedOperationPayload program before payload context kept moved →
    ∃ inner roots, before.frames = inner ++ boundary.ambient ∧
      (∀ frame ∈ inner, frame.ForeignFree) ∧
      AbandonedRoots moved inner (kept.map Address.root) roots ∧
      OperationDisposition.Permits program moved roots inner disposition

/-- The actual accepting caller checks only its retained share, after the
same ordered payload preparation. Destination selection, payload addresses and
the terminal/resumptive mode are not reconstructed independently. -/
def InvocationBoundary.OperationCallerPermission (boundary : InvocationBoundary) (program : Kernel.Program)
    (before : State) (id : DeclId) (arguments : List Term) (payload : List ResolvedPlace)
    (disposition : OperationDisposition) : Prop :=
  ∀ abandoned handler owns arm outer clause kept moved,
    Routes program before id arguments payload abandoned handler owns arm outer →
    PreparedOperationPayload program before payload clause kept moved →
    ∀ caller, boundary.ambient = caller ++ .handler handler owns :: outer →
    ∀ roots, DelimitedRoots moved handler caller (kept.map Address.root) roots →
      OperationDisposition.Permits program moved roots caller disposition

/-- The routing condition cannot hold vacuously through unavailable payload
preparation: admission contains an actual preparation witness. -/
theorem InvocationBoundary.OperationReady.foreign_free {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {payload : List ResolvedPlace} {disposition : OperationDisposition}
    (ready : boundary.OperationReady program before payload disposition) :
    ∃ inner, before.frames = inner ++ boundary.ambient ∧ ∀ frame ∈ inner, frame.ForeignFree := by
  obtain ⟨context,kept,moved,prepared⟩ := ready.prepared
  obtain ⟨inner,roots,frames,barriers,_⟩ := ready.residual context kept moved prepared
  exact ⟨inner,frames,barriers⟩

/-- The actual route supplies the admission barrier for its callee prefix.
The other premises are only payload readiness and callee residual permission;
neither a completed effect step nor a resulting progress fact is assumed. -/
theorem InvocationBoundary.OperationReady.of_outward_route {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {id : DeclId} {arguments : List Term} {payload : List ResolvedPlace}
    {disposition : OperationDisposition} {callee abandoned outer : List Frame}
    {handler : InstalledHandler} {owns : Bool} {arm : OperationArm}
    (route : Routes program before id arguments payload abandoned handler owns arm outer)
    (stack : before.frames = callee ++ boundary.ambient)
    (outward : ¬ boundary.InternalOperation program before id arguments payload)
    (prepared : ∃ context kept moved, PreparedOperationPayload program before payload context kept moved)
    (residual : ∀ context kept moved, PreparedOperationPayload program before payload context kept moved →
      ∃ roots, AbandonedRoots moved callee (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots callee disposition) :
    boundary.OperationReady program before payload disposition := by
  obtain ⟨caller,frames,_⟩ := route.outward_inner stack outward
  have barriers := route.prefix_foreign_free frames
  refine ⟨prepared,?_⟩
  intro context kept moved actual
  obtain ⟨roots,selected,permission⟩ := residual context kept moved actual
  exact ⟨callee,roots,stack,barriers,selected,permission⟩

/-- Nonvacuity supplies successful payload protection at the exact home of
an actual clause, without assuming that its complete effect step can run. -/
theorem InvocationBoundary.OperationReady.prepare {boundary : InvocationBoundary} {program : Kernel.Program}
    {before : State} {payload : List ResolvedPlace} {disposition : OperationDisposition}
    {context : Execution.Context} {withRegion : World}
    (ready : boundary.OperationReady program before payload disposition)
    (home : OperationPayloadContext before context withRegion) :
    ∃ kept moved, Protects program context withRegion payload kept moved ∧
      ∃ inner roots, before.frames = inner ++ boundary.ambient ∧
        (∀ frame ∈ inner, frame.ForeignFree) ∧
        AbandonedRoots moved inner (kept.map Address.root) roots ∧
        OperationDisposition.Permits program moved roots inner disposition := by
  obtain ⟨source,kept,moved,prepared⟩ := ready.prepared
  have actual := prepared.at_context home
  exact ⟨kept,moved,actual,ready.residual context kept moved ⟨withRegion,home,actual⟩⟩

/-- The actual accepting handler receives exactly the caller-owned remainder
of the disposition proof. Its share composes with the admitted callee share
on the very same protected payload and selected delimited roots. No complete
effect step, continuation construction, or progress conclusion is assumed. -/
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
  obtain ⟨callee,calleeRoots,stack,_,localRoots,localPermission⟩ := ready.residual context kept moved prepared
  obtain ⟨caller,frames,ambient⟩ := route.outward_inner stack outward
  refine ⟨caller,ambient,?_⟩
  intro callerRoots ambientRoots
  rw [frames] at selected ⊢
  exact ⟨fun ambientPermission => selected.permits_compose localRoots ambientRoots localPermission ambientPermission,
    fun permission => ((selected.permits_iff localRoots ambientRoots).mp permission).2⟩

/-- Preparation and the exact ordered handler cleanup selection are produced
from the admitted callee and caller shares. Only the real clause home is an
input; no post-world, selected root list or complete effect step is presumed. -/
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
    ∃ kept moved roots,
      Protects program clause withRegion payload kept moved ∧
      DelimitedRoots moved handler abandoned (kept.map Address.root) roots ∧
      OperationDisposition.Permits program moved roots abandoned disposition ∧ Typing.WorldTyped program moved := by
  obtain ⟨kept,moved,handoff,_⟩ := ready.prepare home
  have movedTyped := handoff.worldTyped valid inventory (home.fresh.worldTyped typed)
  have prepared : PreparedOperationPayload program before payload clause kept moved := ⟨withRegion,home,handoff⟩
  obtain ⟨roots,selected⟩ := DelimitedRoots.exists movedTyped.1.1 handler abandoned (kept.map Address.root)
  obtain ⟨caller,ambient,permission⟩ := ready.caller_permission outward route prepared selected
  obtain ⟨callerRoots,callerSelected⟩ := DelimitedRoots.exists movedTyped.1.1 handler caller (kept.map Address.root)
  have allowed := (permission callerRoots callerSelected).mp
    (ambientPermission abandoned handler owns arm outer clause kept moved route prepared caller ambient callerRoots callerSelected)
  exact ⟨kept,moved,roots,handoff,selected,allowed,movedTyped⟩

end Glorious.Language.Contracts
