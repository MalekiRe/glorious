import GloriousLanguage.SuspensionRetention
import GloriousLanguage.EffectPreservation
import GloriousLanguage.ForeignEvolution
import GloriousLanguage.RehomePreservation
import GloriousLanguage.ControlSupport

/-! The captured product of the actual suspend rules. The two real suspension
instructions publish a suspension whose captured roots are replayable in the
world they leave behind, including the continuation handle that
`CreatesContinuation` really allocates: the fresh-frame content law is
instantiated at the machine's own allocation rows and at the live-loan frontier
law of the moved world, not assumed. Snapshot-frames come from the disposition's
own multi-shot admission. -/
namespace Glorious.Language.Execution

open Kernel

/-- The real allocation writes only the fresh root, so every other row of the
root table is untouched. Unlike the frontier-bounded form, this holds for every
identity, including ids at or above the frontier, which is what the fresh-root
frame consumes. -/
theorem Allocates.roots_other'' {program : Program} {before after : World}
    {home region type layout mutable address} {id : Identity}
    (allocated : Allocates program before home region type layout mutable address after)
    (different : id ≠ address.root) : after.roots.get id = before.roots.get id := by
  cases allocated
  exact Table.get_set_other _ _ _ _ different

/-- The real resident construction with no hand-off sources writes only its own
destination row; this is exactly the continuation handle's construction, whose
source list is empty. -/
theorem NewValue.roots_other_nil {program : RuntimeProgram} {before after : World}
    {destination : Address} {type : Term} {head : ValueHead} {id : Identity}
    (constructed : NewValue program before destination type head [] after)
    (different : id ≠ destination.root) : after.roots.get id = before.roots.get id := by
  cases constructed with
  | construct vacant typed ready separate cleared written =>
      cases cleared with
      | nil => simpa using World.write_roots_other' written different

/-- The identity of the continuation handle the real allocation publishes: the
frontier of the world it starts from. -/
theorem CreatesContinuation.address_root {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    address.root = before.nextRoot := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  cases allocation
  rfl

/-- The actual continuation-handle allocation retains the captured roots'
replayability in the world it publishes. Every hypothesis is the machine's own:
the row framing of the real allocation, the loan table it leaves alone, and the
frontier law of live loans. -/
theorem CreatesContinuation.replayable {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address} {roots : List Identity}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (well : before.WellFormed) (frontier : before.nextRoot ≤ address.root) (outside : address.root ∉ roots)
    (replayable : Replayable program before roots) :
    Replayable program after roots := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  refine Replayable.fresh ?_ ?_ ?_ outside replayable
  · intro other different
    exact (Execution.NewValue.roots_other_nil constructed different).trans
      (Execution.Allocates.roots_other'' allocation different)
  · exact (Glorious.Language.Allocates.authorityStable allocation).trans
      (Glorious.Language.NewValue.authorityStable constructed) |>.loans
  · intro other loan found live
    exact World.loan_referent_ne well found live frontier

/-- The two actual suspend rules publish a captured product whose roots are
replayable in the world they leave behind, as soon as the accepted quantity is
really multi-shot, which is exactly the guard under which the copy-replay rule
uses that suspension; the snapshot frames of the disposition are produced with
them. -/
theorem EffectStep.capture_replayable {program : Kernel.Program} {before after : State}
    {id : Identity}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      ∀ bound, suspension.quantity.upper = some bound → 1 < bound →
        Replayable program after.world suspension.roots ∧ ∀ frame ∈ suspension.frames, SnapshotFrame frame := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer selectedRoots permission
      homes created plan suspension =>
    subst suspension
    have movedTyped := keptTransfer.worldTyped programValid inventory (started.worldTyped typed)
    have rootEq := CreatesContinuation.address_root created
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro bound upper multi
    have admitted := DelimitedRoots.replayable_suspendRoots (id := before.nextContinuation) permission upper multi selectedRoots
    refine ⟨created.replayable (suspendRoots.worldTyped movedTyped).1 ?_ ?_ admitted.1,admitted.2⟩
    · exact Nat.le_of_eq rootEq.symm
    · intro member
      rw [rootEq] at member
      obtain ⟨root,found,_⟩ := (selectedRoots.2 _).mp member
      exact Nat.lt_irrefl _ (World.root_bound movedTyped.1 found)
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer selectedRoots
      permission homes plan suspension =>
    subst suspension
    have movedTyped := keptTransfer.worldTyped programValid inventory (started.worldTyped typed)
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro bound upper multi
    exact DelimitedRoots.replayable_suspendRoots (id := before.nextContinuation) permission upper multi selectedRoots

/-- `Authority.Replayable` observes only the loan table: presence of the row a
loan authority names, the historical backing of a shared view, and the carrier
of a guarded view. It is therefore retained by every world change that leaves
the loan table alone, which is exactly what the capture operations are. -/
theorem Authority.Replayable.congr_loans {before after : World}
    (loans : after.loans = before.loans) {authority : Authority}
    (replayable : authority.Replayable before) : authority.Replayable after := by
  induction authority with
  | owner => trivial
  | loan id =>
      simp only [Authority.Replayable]
      obtain ⟨loan,found,shared⟩ := replayable
      exact ⟨loan,by rw [loans]; exact found,shared⟩
  | shared backing =>
      simpa only [Authority.Replayable] using
        replayable.transport (fun _ loan found => ⟨loan,by rw [loans]; exact found⟩)
  | guarded backing carrier ih =>
      simp only [Authority.Replayable]
      obtain ⟨loan,carrierAt⟩ := replayable.2
      exact ⟨ih replayable.1,loan,by rw [loans]; exact carrierAt⟩

/-- The real suspension instructions retain the delimiter's own control
replayability: the relocation to `.suspended` homes moves no loan row, and the
continuation-handle allocation moves none either. This is the transport the
disposition admission needs once it carries the control clause; no admission is
produced here. -/
theorem CreatesContinuation.controlReplayable {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address} {authorities : List Authority}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (control : ∀ authority ∈ authorities, authority.Replayable before) :
    ∀ authority ∈ authorities, authority.Replayable after := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  have stable := (Glorious.Language.Allocates.authorityStable allocation).trans
    (Glorious.Language.NewValue.authorityStable constructed)
  intro authority member
  exact Authority.Replayable.congr_loans stable.loans (control authority member)

/-- The capture relocation itself moves no loan row, so a delimiter's control
admission at the protected world is still its admission at the suspended world. -/
theorem suspendRoots.controlReplayable {world : World} {roots : List Identity} {id : Identity}
    {authorities : List Authority} (control : ∀ authority ∈ authorities, authority.Replayable world) :
    ∀ authority ∈ authorities, authority.Replayable (suspendRoots world roots id) :=
  fun authority member =>
    Authority.Replayable.congr_loans (before := world) (after := suspendRoots world roots id) rfl
      (control authority member)

end Glorious.Language.Execution
