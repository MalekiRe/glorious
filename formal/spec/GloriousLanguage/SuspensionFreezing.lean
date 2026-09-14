import GloriousLanguage.SuspensionCapture
import GloriousLanguage.SuspensionRetention
import GloriousLanguage.ControlOrigin

/-! Captured-content freezing across actual intervening execution, and the
region liveness of captured storage.

`World.Frames` is the machine-level statement that a world change leaves the
captured roots' residents and the whole loan table alone: exactly the
hypothesis under which the *root-local* part of the replay admission is retained
(`Replayable.rootLocal`). Every producer of `World.Frames` below is one of the
real world operations the machine performs, with its actual write footprint as
the side condition — no invented separation and no second storage inventory.
The remaining, non-root-local part of `Replayable` (`Suspensible`'s closure over
the referents of live restoring/destructor loans that the captured content
touches) is not a function of the captured roots alone and is recorded as the
open boundary in the lane manifest. -/
namespace Glorious.Language

open Kernel

/-- Root rows agree outside a finite list of touched identities. -/
def World.RowsOutside (touched : List Identity) (before after : World) : Prop :=
  ∀ id, id ∉ touched → after.roots.get id = before.roots.get id

theorem World.RowsOutside.refl (touched : List Identity) (world : World) :
    world.RowsOutside touched world := fun _ _ => rfl

/-- The captured content of a root list is frozen across a world change: every
resident of a captured root agrees on both sides and the loan table is retained,
so the authority provenance the replay admission reads is unchanged. Homes may be
relabelled, unrelated roots written and fresh roots added. -/
def World.Frames (roots : List Identity) (before after : World) : Prop :=
  (∀ address value, address.root ∈ roots → (before.Resident address value ↔ after.Resident address value)) ∧
  after.loans = before.loans

theorem World.Frames.refl (roots : List Identity) (world : World) : world.Frames roots world :=
  ⟨fun _ _ _ => Iff.rfl, rfl⟩

theorem World.Frames.trans {roots : List Identity} {first second third : World}
    (left : first.Frames roots second) (right : second.Frames roots third) : first.Frames roots third :=
  ⟨fun address value member => (left.1 address value member).trans (right.1 address value member),
   right.2.trans left.2⟩

/-- Resident agreement at an address whose root is untouchable. -/
theorem World.resident_of_rows' {before after : World} {touched : List Identity}
    (rows : before.RowsOutside touched after) {address : Address} {value : Value}
    (outside : address.root ∉ touched) :
    after.Resident address value ↔ before.Resident address value := by
  constructor
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    exact ⟨root,whole,by rw [← rows address.root outside]; exact found,live,generation,contents,located⟩
  · rintro ⟨root,whole,found,live,generation,contents,located⟩
    exact ⟨root,whole,by rw [rows address.root outside]; exact found,live,generation,contents,located⟩

theorem World.Frames.of_rows {roots touched : List Identity} {before after : World}
    (rows : before.RowsOutside touched after) (loans : after.loans = before.loans)
    (outside : ∀ id ∈ roots, id ∉ touched) : before.Frames roots after :=
  ⟨fun address _value member => (World.resident_of_rows' rows (outside address.root member)).symm, loans⟩

/-- The single-identity form: a root list disjoint from the one touched identity. -/
theorem World.Frames.of_row {roots : List Identity} {before after : World} {only : Identity}
    (rows : before.RowsOutside [only] after) (loans : after.loans = before.loans)
    (outside : only ∉ roots) : before.Frames roots after :=
  World.Frames.of_rows rows loans fun id member same => by
    have equal : id = only := by simpa only [List.mem_singleton] using same
    exact outside (equal ▸ member)

namespace Execution

/-! ### Producers: the actual write footprints of the machine's world operations -/

theorem World.write_rowsOutside {before after : World} {address : Address} {value : Option Value}
    (written : before.write address value = some after) :
    before.RowsOutside [address.root] after :=
  fun id outside => World.write_roots_other' written (by simpa only [List.mem_singleton] using outside)

theorem World.write_frames {before after : World} {address : Address} {value : Option Value}
    {roots : List Identity} (written : before.write address value = some after)
    (outside : address.root ∉ roots) : before.Frames roots after :=
  World.Frames.of_row (World.write_rowsOutside written) (World.write_loans written) outside

theorem Allocates.rowsOutside {program : Program} {before after : World}
    {home region type layout mutable address}
    (allocated : Allocates program before home region type layout mutable address after) :
    before.RowsOutside [address.root] after :=
  fun id outside => Allocates.roots_other'' allocated (by simpa only [List.mem_singleton] using outside)

theorem Allocates.frames {program : Program} {before after : World}
    {home region type layout mutable address} {roots : List Identity}
    (allocated : Allocates program before home region type layout mutable address after)
    (outside : address.root ∉ roots) : before.Frames roots after :=
  World.Frames.of_row (Allocates.rowsOutside allocated) allocated.authorityStable.loans outside

theorem Clears.rowsOutside {before after : World} {addresses : List Address}
    (cleared : Clears before addresses after) :
    before.RowsOutside (addresses.map Address.root) after := by
  induction cleared with
  | nil => intro id _; rfl
  | cons first rest ih =>
      intro id outside
      simp only [List.map_cons,List.mem_cons,not_or] at outside
      exact (ih id outside.2).trans
        (World.write_roots_other' first (by simpa only [List.mem_singleton] using outside.1))

theorem Clears.frames {before after : World} {addresses : List Address} {roots : List Identity}
    (cleared : Clears before addresses after) (outside : ∀ address ∈ addresses, address.root ∉ roots) :
    before.Frames roots after := by
  revert outside
  induction cleared with
  | nil => intro _; exact World.Frames.refl roots _
  | cons first rest ih =>
      intro outside
      exact (World.write_frames first (outside _ List.mem_cons_self)).trans
        (ih (fun address member => outside address (List.mem_cons_of_mem _ member)))

theorem NewValue.rowsOutside {program : RuntimeProgram} {before after : World}
    {destination type head sources}
    (constructed : NewValue program before destination type head sources after) :
    before.RowsOutside (destination.root :: sources.map (fun source => source.address.root)) after := by
  cases constructed with
  | construct vacant typed ready separate cleared written =>
      have clearedRows := Clears.rowsOutside cleared
      simp only [List.map_map,Function.comp_def] at clearedRows
      intro id outside
      simp only [List.mem_cons,not_or] at outside
      exact (World.write_roots_other' written outside.1).trans (clearedRows id outside.2)

theorem NewValue.frames {program : RuntimeProgram} {before after : World}
    {destination type head sources} {roots : List Identity}
    (constructed : NewValue program before destination type head sources after)
    (destinationOutside : destination.root ∉ roots)
    (sourcesOutside : ∀ source ∈ sources, source.address.root ∉ roots) : before.Frames roots after :=
  World.Frames.of_rows (NewValue.rowsOutside constructed) constructed.authorityStable.loans
    (fun id member => by
      intro same
      rcases List.mem_cons.mp same with equal | member'
      · exact destinationOutside (equal ▸ member)
      · obtain ⟨source,present,equal⟩ := List.mem_map.mp member'
        exact sourcesOutside source present (equal.symm ▸ member))

theorem Transfers.rowsOutside {program : RuntimeProgram} {before after : World}
    {authority source destination} (transferred : Transfers program before authority source destination after) :
    before.RowsOutside [source.root,destination.root] after := by
  cases transferred with
  | move _ _ _ _ _ _ _ clear install =>
      intro id outside
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
      exact (World.write_roots_other' install (by simpa only [List.mem_singleton] using outside.2)).trans
        (World.write_roots_other' clear (by simpa only [List.mem_singleton] using outside.1))

theorem Transfers.frames {program : RuntimeProgram} {before after : World}
    {authority source destination} {roots : List Identity}
    (transferred : Transfers program before authority source destination after)
    (sourceOutside : source.root ∉ roots) (destinationOutside : destination.root ∉ roots) :
    before.Frames roots after :=
  World.Frames.of_rows (Transfers.rowsOutside transferred) transferred.authorityStable.loans
    (fun id member => by
      intro same
      rcases List.mem_cons.mp same with equal | rest
      · exact sourceOutside (equal ▸ member)
      · have only : id = destination.root := by simpa only [List.mem_singleton] using rest
        exact destinationOutside (only ▸ member))

theorem Retires.frames {before after : World} {id : Identity} {roots : List Identity}
    (retired : Retires before id after) : before.Frames roots after :=
  ⟨fun _ _ _ => (Retires.resident retired).symm, by cases retired; rfl⟩

theorem RetiresEmpty.frames {before after : World} {addresses : List Address} {roots : List Identity}
    (retired : RetiresEmpty before addresses after) : before.Frames roots after := by
  induction retired with
  | nil => exact World.Frames.refl roots _
  | cons _ first _ ih => exact (Retires.frames first).trans ih

theorem RegionEnds.frames {before after : World} {region : Identity} {roots : List Identity}
    (ended : RegionEnds before region after) : before.Frames roots after := by
  rw [ended.2]
  exact World.Frames.refl roots before

theorem FreshRegion.frames {before after : World} {region : Identity} {roots : List Identity}
    (fresh : FreshRegion before region after) : before.Frames roots after := by
  rw [fresh.2]
  exact World.Frames.refl roots before

theorem World.rehome_frames {before after : World} {select : Identity → Root → Home}
    (rehomed : after = before.rehome select) {roots : List Identity} : before.Frames roots after :=
  ⟨fun address value _ => by rw [rehomed]; exact (World.rehome_resident).symm,
   by rw [rehomed]; exact World.rehome_loans before select⟩

theorem suspendRoots.frames (world : World) (roots : List Identity) (id : Identity) {wanted : List Identity} :
    world.Frames wanted (suspendRoots world roots id) :=
  World.rehome_frames (suspendRoots.eq_rehome world roots id)

theorem restoreRoots.frames (world : World) (homes : Table Home) {roots : List Identity} :
    world.Frames roots (restoreRoots world homes) :=
  World.rehome_frames (restoreRoots.eq_rehome world homes)

theorem Protect.frames {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority} {roots : List Identity}
    (kept : Protect program context before source authority destination after)
    (sourceOutside : source.root ∉ roots) (destinationOutside : destination.root ∉ roots) :
    before.Frames roots after := by
  obtain ⟨value,allocated,stored,temporary,transfer⟩ := kept
  exact (Allocates.frames temporary.choose_spec destinationOutside).trans
    (Transfers.frames transfer sourceOutside destinationOutside)

theorem ProtectsFor.frames {program : Kernel.Program} {context : Context} {footprint : List Address}
    {before : World} {sources : List ResolvedPlace} {destinations : List Address} {after : World}
    {roots : List Identity}
    (kept : ProtectsFor program context footprint before sources destinations after)
    (sourcesOutside : ∀ source ∈ sources, source.address.root ∉ roots)
    (destinationsOutside : ∀ address ∈ destinations, address.root ∉ roots) :
    before.Frames roots after := by
  induction kept using ProtectsFor.inductionOn with
  | nil world => exact World.Frames.refl roots world
  | cons ready head tail ih =>
      exact (Protect.frames head (sourcesOutside _ List.mem_cons_self)
        (destinationsOutside _ List.mem_cons_self)).trans
        (ih (fun source member => sourcesOutside source (List.mem_cons_of_mem _ member))
          (fun address member => destinationsOutside address (List.mem_cons_of_mem _ member)))

theorem CreatesContinuation.frames {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address} {roots : List Identity}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (outside : address.root ∉ roots) : before.Frames roots after := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  exact (Allocates.frames allocation outside).trans
    (NewValue.frames constructed outside (fun source member => by cases member))

/-! ### The root-local part of the replay admission -/

/-- Every clause of the replay admission that reads only the captured roots'
residents and the loan table. These are exactly the clauses that captured-root
content freezing protects; the `Suspensible` closure over the referents of
touching live loans is deliberately not included (see the lane manifest). -/
def Replayable.rootLocal (program : RuntimeProgram) (world : World) (roots : List Identity) : Prop :=
  (∀ address value, address.root ∈ roots → world.Resident address value →
    (value.shellLive = true → PrincipalOf program.declarations value.type .duplicable) ∧
    (∀ brand, value.head ≠ .label brand) ∧ (∀ id, value.head ≠ .available id) ∧
    (∀ binding ∈ value.resources, binding.ReadOnly)) ∧
  (∀ address value id loan, address.root ∈ roots → world.Resident address value → value.head = .reference id →
    world.loans.get id = some loan → loan.mode = .shared) ∧
  (∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ∈ roots →
    loan.mode = .shared)

theorem Replayable.rootLocal_of_replayable {program : RuntimeProgram} {world : World} {roots : List Identity}
    (replayable : Replayable program world roots) : Replayable.rootLocal program world roots :=
  ⟨replayable.2.1,replayable.2.2.1,replayable.2.2.2⟩

/-- The root-local captured admission is retained by every world change that
freezes the roots' residents and the loan table: intervening execution may add
fresh storage, end unrelated loans or relabel homes, and the captured roots still
carry the same admission. -/
theorem Replayable.rootLocal_frames {program : RuntimeProgram} {roots : List Identity}
    {before after : World} (frames : before.Frames roots after)
    (rootLocal : Replayable.rootLocal program before roots) : Replayable.rootLocal program after roots :=
  ⟨fun address value member resident =>
      rootLocal.1 address value member ((frames.1 address value member).mpr resident),
   fun address value id loan member resident head found =>
      rootLocal.2.1 address value id loan member ((frames.1 address value member).mpr resident) head
        (by simpa only [frames.2] using found),
   fun id loan found live member => rootLocal.2.2 id loan (by rw [← frames.2]; exact found) live member⟩


/-! ### Captured-region liveness: the capture producer and the end law -/

/-- The roots an actual capture selects are live and their regions are live in
the world the selection happens in. -/
theorem DelimitedRoots.region_live {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} (well : world.WellFormed) (selected : DelimitedRoots world handler inner kept roots) :
    ∀ rootId ∈ roots, ∃ root, world.roots.get rootId = some root ∧ root.live = true ∧
      root.region ∈ world.liveRegions := by
  intro rootId member
  obtain ⟨root,found,live,_,_⟩ := (selected.2 rootId).mp member
  exact ⟨root,found,live,(well.2.2.2.2.2.2.2.2.1 rootId root found).2.1 live⟩

/-- The capture relocation is a home relabelling: it publishes the same root row
with its region, liveness and generation unchanged. -/
theorem suspendRoots.exists_root {world : World} {roots : List Identity} {id rootId : Identity} {root : Root}
    (found : world.roots.get rootId = some root) :
    ∃ current, (suspendRoots world roots id).roots.get rootId = some current ∧
      current.region = root.region ∧ current.live = root.live := by
  refine ⟨{ root with home := if rootId ∈ roots then .suspended id else root.home },?_,rfl,rfl⟩
  have rows : (suspendRoots world roots id).roots.get rootId =
      (world.roots.get rootId).map (fun current =>
        { current with home := if rootId ∈ roots then .suspended id else current.home }) := by
    rw [suspendRoots.eq_rehome]
    exact World.rehome_get world (fun key current => if key ∈ roots then .suspended id else current.home) rootId
  rw [rows,found]
  rfl

/-- The continuation handle is allocated strictly above every pre-existing root,
so it replaces no row. -/
theorem CreatesContinuation.roots_other {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address} {other : Identity}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (different : other ≠ address.root) : after.roots.get other = before.roots.get other := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  exact (NewValue.roots_other_nil constructed different).trans (Allocates.roots_other'' allocation different)

/-- The continuation-handle allocation publishes every pre-existing root row
with its region, liveness and generation unchanged. -/
theorem CreatesContinuation.exists_root {program : Kernel.Program} {context : Context}
    {before after : World} {id : Identity} {signature : Signature} {answer effects : Term}
    {quantity : Quantity} {localSlot : Local} {address : Address} {rootId : Identity} {root : Root}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after)
    (bound : rootId < before.nextRoot)
    (found : before.roots.get rootId = some root) :
    ∃ current, after.roots.get rootId = some current ∧ current.region = root.region ∧
      current.live = root.live := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  have separate : rootId ≠ address.root := by
    cases allocation
    exact Nat.ne_of_lt bound
  refine ⟨root,?_,rfl,rfl⟩
  rw [NewValue.roots_other_nil constructed separate,Allocates.roots_other'' allocation separate]
  exact found

/-- Both actual suspend rules publish, for the suspension they create, a live
captured root in a live region of the world they leave behind: the selected roots
are live in the payload handoff's world, and neither the real capture relocation
nor the real continuation-handle allocation changes a root's region or the live
region set. -/
theorem EffectStep.capture_rootRegions_live {program : Kernel.Program} {before after : State}
    {id : Identity}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧
      ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get rootId = some root ∧
        root.live = true ∧ root.region ∈ after.world.liveRegions := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer selectedRoots permission
      homes created plan suspension =>
    subst suspension
    have movedWell := (keptTransfer.worldTyped programValid inventory (started.worldTyped typed)).1
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro rootId member
    obtain ⟨root,found,live,regionLive⟩ := DelimitedRoots.region_live movedWell selectedRoots rootId member
    obtain ⟨asserted,assertedAt,assertedRegion,assertedLive⟩ := suspendRoots.exists_root (found := found)
    obtain ⟨current,currentAt,region,currentLive⟩ :=
      CreatesContinuation.exists_root created (World.root_bound movedWell found) assertedAt
    refine ⟨current,currentAt,?_,?_⟩
    · rw [currentLive,assertedLive]; exact live
    · rw [region,assertedRegion,CreatesContinuation.liveRegions created,suspendRoots.liveRegions]
      exact regionLive
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer selectedRoots
      permission homes plan suspension =>
    subst suspension
    have movedWell := (keptTransfer.worldTyped programValid inventory (started.worldTyped typed)).1
    refine ⟨_,Table.get_set _ _ _,?_⟩
    intro rootId member
    obtain ⟨root,found,live,regionLive⟩ := DelimitedRoots.region_live movedWell selectedRoots rootId member
    obtain ⟨current,currentAt,region,currentLive⟩ := suspendRoots.exists_root (found := found)
    refine ⟨current,currentAt,?_,?_⟩
    · rw [currentLive]; exact live
    · rw [region]; exact regionLive

/-- A region that holds a live root cannot be ended: `RegionCanEnd` requires that
no live root names the region. -/
theorem RegionEnds.not_live_root {world : World} {region : Identity} {after : World}
    (ended : RegionEnds world region after) {rootId : Identity} {root : Root}
    (found : world.roots.get rootId = some root) (live : root.live = true) : root.region ≠ region :=
  fun same => ended.1.1 rootId root found live same

/-- Consequently a live root's region survives a real region end: the region is
already live and the end cannot remove it. -/
theorem RegionEnds.live_root_region {world : World} {region : Identity} {after : World}
    (well : world.WellFormed) (ended : RegionEnds world region after) {rootId : Identity} {root : Root}
    (found : world.roots.get rootId = some root) (live : root.live = true) :
    root.region ∈ after.liveRegions := by
  have liveAt := (well.2.2.2.2.2.2.2.2.1 rootId root found).2.1 live
  have separate := ended.not_live_root found live
  rw [ended.2]
  exact List.mem_filter.mpr ⟨liveAt,by simpa only [bne_iff_ne,ne_eq] using separate⟩

/-- The captured-roots component of the replay admission's `regionsLive`, in the
exact shape the suspension inventory uses (`roots.filterMap` of each root's
region): every region the captured roots really carry is live, from the state's
capture invariant and world well-formedness. This is the state-level producer
that `Run.capturedRootRegions_live` composes with the Run-level invariants. -/
theorem Suspension.roots_regions_live {state : State} {id : Identity} {suspension : Suspension}
    (well : state.world.WellFormed) (formed : state.SuspensionsWellFormed)
    (found : state.resumptions.get id = some suspension) (active : suspension.active = true) :
    ∀ region ∈ suspension.roots.filterMap (fun root => (state.world.roots.get root).map Root.region),
      region ∈ state.world.liveRegions := by
  intro region member
  obtain ⟨rootId,present,selected⟩ := List.mem_filterMap.mp member
  obtain ⟨root,rootAt,live,_⟩ := (formed.active id suspension found active rootId).mp present
  have same : (state.world.roots.get rootId).map Root.region = some root.region := by
    rw [rootAt]
    rfl
  rw [same,Option.some.injEq] at selected
  subst selected
  exact (well.2.2.2.2.2.2.2.2.1 rootId root rootAt).2.1 live

/-! ### The live-control/captured-root separation and its consumer law

`State.ControlSeparated` is the authoritative address-level separation: no
address the live control of the state names carries a suspended home. It is
stated over the existing support path (`Task.rootSupport` / `Frame.rootSupport`),
not over a second inventory, and it is the fact that turns "no write inside the
captured roots" from an assumption into a consequence of the machine's own
capture invariant. Its per-step retention is the only remaining producer (it
needs the activated/temporal `ControlOriginPreservation`/`Private*Preservation`
chain the integrator is repairing, because the handler-environment activation
must be shown absent from live control). -/

def State.ControlSeparated (state : State) : Prop :=
  ∀ root ∈ state.task.rootSupport ++ state.frames.flatMap Frame.rootSupport,
    ∀ suspension, (state.world.roots.get root).map Root.home ≠ some (.suspended suspension)

theorem State.ControlSeparated.task {state : State} (separated : state.ControlSeparated) {root : Identity}
    (member : root ∈ state.task.rootSupport) :
    ∀ suspension, (state.world.roots.get root).map Root.home ≠ some (.suspended suspension) :=
  fun suspension => separated root (List.mem_append_left _ member) suspension

theorem State.ControlSeparated.frames {state : State} (separated : state.ControlSeparated) {root : Identity}
    (member : root ∈ state.frames.flatMap Frame.rootSupport) :
    ∀ suspension, (state.world.roots.get root).map Root.home ≠ some (.suspended suspension) :=
  fun suspension => separated root (List.mem_append_right _ member) suspension

/-- Under the separation, a root that live control names is never a captured root
of an active suspension: the capture invariant identifies captured roots with the
rows whose home is that suspension, and the separation forbids exactly those. This
is the producer the content-freezing frame library consumes. -/
theorem State.ControlSeparated.not_captured {state : State} (separated : state.ControlSeparated)
    (formed : state.SuspensionsWellFormed) {id : Identity} {suspension : Suspension}
    (found : state.resumptions.get id = some suspension) (active : suspension.active = true)
    {root : Identity} (member : root ∈ state.task.rootSupport ++ state.frames.flatMap Frame.rootSupport) :
    root ∉ suspension.roots := by
  intro captured
  obtain ⟨row,rowAt,live,home⟩ := (formed.active id suspension found active root).mp captured
  have rowHome : (state.world.roots.get root).map Root.home = some (.suspended id) := by
    rw [rowAt]
    exact congrArg some home
  exact separated root member id rowHome

end Execution
end Glorious.Language
