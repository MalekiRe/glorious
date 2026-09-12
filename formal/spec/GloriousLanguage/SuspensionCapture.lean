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


/-- The disposition admission of the real suspend steps carries the
control-replayability of the captured frames: the selected operation's
`SuspendPermission` requires every authority those frames name to be a replayed
authority, and the actual capture sequence - the ordered payload handoff, the
real capture relocation and the real continuation-handle allocation - moves no
loan row, so the admission still holds in the world the suspension is published
in. The handler and resumption-context authorities of the suspension are the
surrounding live control's and are not covered by this share (see the lane
manifest). -/
theorem EffectStep.capture_controlReplayable {program : Kernel.Program} {before after : State}
    {id : Identity}
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      ∀ authority ∈ suspension.frames.flatMap Frame.authoritySupport, authority.Replayable after.world := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer selectedRoots
      permission homes created plan suspension =>
    subst suspension
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro authority member
    exact created.controlReplayable (suspendRoots.controlReplayable (control := permission.2.2.2.2)) authority member
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer
      selectedRoots permission homes plan suspension =>
    subst suspension
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro authority member
    exact suspendRoots.controlReplayable (control := permission.2.2.2.2) authority member

/-- Region liveness is untouched by the actual storage producers the capture
uses: writes, allocations, transfers, retirements and the resident construction
change no `liveRegions` entry. Regions begin at `FreshRegion` and end only at
`RegionEnds`, so these framings are what a control-region liveness invariant
composes with. -/
theorem World.write_liveRegions {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) : after.liveRegions = before.liveRegions := by
  rw [World.write_rest written]

theorem Allocates.liveRegions {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    after.liveRegions = before.liveRegions := by
  cases allocated
  rfl

theorem Clears.liveRegions {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) : after.liveRegions = before.liveRegions := by
  induction cleared with
  | nil => rfl
  | cons written rest ih => exact ih.trans (World.write_liveRegions written)

theorem NewValue.liveRegions {program : RuntimeProgram} {before after : World}
    {destination type head sources}
    (constructed : NewValue program before destination type head sources after) :
    after.liveRegions = before.liveRegions := by
  cases constructed with
  | construct vacant typed ready separate cleared written =>
      exact (World.write_liveRegions written).trans (Clears.liveRegions cleared)

theorem Transfers.liveRegions {program : RuntimeProgram} {before after : World}
    {authority source destination} (transferred : Transfers program before authority source destination after) :
    after.liveRegions = before.liveRegions := by
  cases transferred with
  | move _ _ _ _ _ _ _ clear install =>
      exact (World.write_liveRegions install).trans (World.write_liveRegions clear)

theorem Retires.liveRegions {before after : World} {id : Identity} (retired : Retires before id after) :
    after.liveRegions = before.liveRegions := by
  cases retired
  rfl

theorem RetiresEmpty.liveRegions {before after : World} {addresses : List Address}
    (retired : RetiresEmpty before addresses after) : after.liveRegions = before.liveRegions := by
  induction retired with
  | nil => rfl
  | cons _ first _ ih => exact ih.trans (Retires.liveRegions first)

theorem Protect.liveRegions {program : Kernel.Program} {context : Context}
    {before after : World} {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) :
    after.liveRegions = before.liveRegions := by
  obtain ⟨value,allocated,stored,temporary,transfer⟩ := kept
  exact (Transfers.liveRegions transfer).trans (Allocates.liveRegions temporary.choose_spec)

/-- The ordered by-value handoff touches no region: every transfer is an
ordinary allocation/write pair and a failed prefix retains the world it stopped
in. -/
theorem ProtectsFor.liveRegions {program : Kernel.Program} {context : Context}
    {footprint : List Address} {before : World} {sources : List ResolvedPlace}
    {destinations : List Address} {after : World}
    (kept : ProtectsFor program context footprint before sources destinations after) :
    after.liveRegions = before.liveRegions := by
  induction kept using ProtectsFor.inductionOn with
  | nil world => rfl
  | cons ready head tail ih => exact ih.trans (Protect.liveRegions head)

theorem suspendRoots.liveRegions (world : World) (roots : List Identity) (id : Identity) :
    (suspendRoots world roots id).liveRegions = world.liveRegions := rfl

theorem restoreRoots.liveRegions (world : World) (homes : Table Home) :
    (restoreRoots world homes).liveRegions = world.liveRegions := rfl

/-- The real continuation-handle allocation publishes the world it started from
with one further root; it touches no region. -/
theorem CreatesContinuation.liveRegions {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    after.liveRegions = before.liveRegions := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  exact (NewValue.liveRegions constructed).trans (Allocates.liveRegions allocation)

/-- The clause's own region is live in the world clause entry publishes: entry
allocates exactly that region through `FreshRegion`. -/
theorem StartsClause.region_live {before : State} {handler : InstalledHandler} {context : Context}
    {after : World} (started : StartsClause before handler context after) :
    context.region ∈ after.liveRegions := by
  obtain ⟨fresh,same⟩ := started
  have region : context.region = before.world.nextRegion := by rw [same]
  rw [fresh.2, region]
  exact List.mem_cons_self ..

/-- The resumption brand is instantiation metadata, so the resumption clause
keeps the same live region as the clause entry it refines. -/
theorem StartsResumptionClause.region_live {before : State} {handler : InstalledHandler}
    {lexical : Local} {context : Context} {localSlot : Local} {after : World}
    (started : StartsResumptionClause before handler lexical context localSlot after) :
    context.region ∈ after.liveRegions := by
  obtain ⟨outer,brand,started,brandAt,contextAt,localAt⟩ := started
  have region : context.region = outer.region := by
    rw [contextAt]
    rfl
  rw [region]
  exact started.region_live

end Glorious.Language.Execution
