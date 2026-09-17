import GloriousLanguage.SnapshotReplayConstruction
import GloriousLanguage.Effects
import GloriousLanguage.HandoffProgress
import GloriousLanguage.RehomePreservation
import GloriousLanguage.SuspensionFreezing

/-! Actual replay and cancellation execution. A positive replay request reaches
the real replay step, the real argument handoff, or the honest physical
outcome of the resource it needs: an unplaceable snapshot copy, a copy whose
argument handoff finds no extent, or a final replay whose restored argument
finds no extent. Cancellation executes through its own source admission; this
module grants no replay, copy, extent or cancellation permission.

The admission those two boundaries consume is produced here rather than
premised. `Suspension.SuspendProduct` is the product the real suspend rules
publish for the row they create; `Suspension.Delivered` carries it to the state
the suspension is replayed or cancelled in along an actual `Run`, so the stored
row's captured roots, saved homes, frames, handler, context, control
authorities and capture limit are the ones the suspend step published. Every
component the run leaves alone is transported; the components that still depend
on the open live-control/captured-root separation are named once, in
`Suspension.Carried`, instead of restated per consumer. -/
namespace Glorious.Language.Execution

open _root_.Glorious.Language.Kernel

/-- The loan table frozen on the rows a captured admission reads: the
intervening execution may add rows and retire unrelated loans, but a row the
source table knows survives with its mode, its referent and its liveness, and no
identity the source table already knows gains a row it did not have. This is the
footprint of the recorded live-control/captured-root separation: a run that
never names a captured root can neither rewrite its residents nor form a loan
that names it. Nothing here is a post-state readiness judgement. -/
structure Suspension.LoansFrozen (start before : State) : Prop where
  present : ∀ id, (∃ loan, start.world.loans.get id = some loan) ↔
    (∃ loan, before.world.loans.get id = some loan)
  shape : ∀ id original current, start.world.loans.get id = some original →
    before.world.loans.get id = some current →
    original.mode = current.mode ∧ original.referent = current.referent ∧
      (current.live = true → original.live = true)

/-- The captured content the replay admission reads is unchanged by the
intervening execution: every resident of a captured root agrees on both sides
and the loan table is frozen on the rows that admission reads. -/
structure Suspension.ContentFrozen (start before : State) (suspension : Suspension) : Prop where
  residents : ∀ address value, address.root ∈ suspension.roots →
    (start.world.Resident address value ↔ before.world.Resident address value)
  loans : Suspension.LoansFrozen start before

/-- The suspend-time product of a stored suspension: exactly what the real
suspend rules publish for the row they store. The shares are conditional because
the disposition is: the replay share exists only for a multi-shot accepted
quantity and the cancellation share only for the one-shot kind, so a product
that demanded both unconditionally would be unsatisfiable for one-shot
suspensions. The captured frames' control admission is granted unconditionally
by the disposition (`EffectStep.capture_controlReplayable`); the authorities of
the surrounding handler and resumption context are the surrounding live
control's, not this share's, and the `Suspensible` closure both shares build on
is retained by every capture, replay and cancellation, so both are carried by
`Suspension.Carried`. -/
structure Suspension.SuspendProduct (program : Kernel.Program) (start : State)
    (suspension : Suspension) : Prop where
  replayable : ∀ bound, suspension.quantity.upper = some bound → 1 < bound →
    Replayable program start.world suspension.roots ∧
      ∀ frame ∈ suspension.frames, SnapshotFrame frame
  cancelable : suspension.quantity.lower = 0 →
    Cancelable program start.world suspension.roots
  controlReplayable : ∀ authority ∈ suspension.frames.flatMap Frame.authoritySupport,
    authority.Replayable start.world

/-- The components of the replay admission that the capture boundary still owns
for another lane: the open live-control/captured-root separation (the frozen
captured content and the loan-table footprint it implies), the `Suspensible`
referent closure, which is not a function of the captured roots alone, the
surrounding live control's authorities for the suspension's own handler and
resumption context, the liveness of the captured frames' own regions, and the
external referent scoping law the snapshot map states. Naming them once keeps
them out of the replay and cancel rules. -/
structure Suspension.Carried (program : Kernel.Program) (start before : State)
    (suspension : Suspension) : Prop where
  frozen : suspension.ContentFrozen start before
  closure : Suspensible program before.world suspension.roots
  controlAuthorities : ∀ authority ∈
    suspension.context.authoritySupport ++ suspension.handler.authoritySupport,
    authority.Replayable before.world
  controlRegionsLive : ∀ region ∈ suspension.controlRegions,
    region ∈ before.world.liveRegions
  externalScoped : ∀ address value loanId loan,
    address.root ∈ suspension.roots → before.world.Resident address value →
    value.head = .reference loanId → before.world.loans.get loanId = some loan →
    loan.referent.root ∉ suspension.roots →
    ∀ type, AddressType program.declarations before.world loan.referent type →
    ∀ region ∈ (suspension.inventory program before []).regions,
      ¬ Occurs (.runtimeRegion region) type

/-- The suspend-time product carried to the state the suspension is replayed or
cancelled in by the actual run that reached it. `delivered` is the row the
suspend step published; `suspension` at that later state is the same captured
product, which the actual resumption-table change of every step retains. -/
structure Suspension.Delivered (program : Kernel.Program) (host : Foreign.Model)
    (start : State) (trace : List Event) (before : State) (id : Identity)
    (delivered : Suspension) : Prop where
  run : Run program host start trace before
  accounted : start.ResumptionsAccounted
  published : start.resumptions.get id = some delivered
  product : delivered.SuspendProduct program start
  residual : delivered.Carried program start before

theorem Suspension.controlRegions_congr {first second : Suspension}
    (frames : first.frames = second.frames) (context : first.context = second.context)
    (handler : first.handler = second.handler) :
    first.controlRegions = second.controlRegions := by
  simp only [Suspension.controlRegions,frames,context,handler]

theorem Suspension.inventory_regions_congr {program : Kernel.Program} {before : State}
    {first second : Suspension} (physical : Table Nat)
    (control : first.controlRegions = second.controlRegions) (roots : first.roots = second.roots) :
    (first.inventory program before physical).regions =
      (second.inventory program before physical).regions := by
  simp only [Suspension.inventory,control,roots]

/-- Control replayability observes only the loan table, so freezing that table on
the rows it reads retains it: an existing row reappears with the same mode, and a
live row was already live. -/
theorem Authority.Replayable.frozen {start before : State} {authority : Authority}
    (frozen : Suspension.LoansFrozen start before)
    (replayable : authority.Replayable start.world) : authority.Replayable before.world := by
  cases authority with
  | owner => trivial
  | loan identity =>
      obtain ⟨loan,found,shared⟩ := replayable
      obtain ⟨current,currentAt⟩ := (frozen.present identity).mp ⟨loan,found⟩
      obtain ⟨mode,_,live⟩ := frozen.shape identity loan current found currentAt
      refine ⟨current,currentAt,?_⟩
      intro alive
      rw [← mode]
      exact shared (live alive)
  | shared backing =>
      exact replayable.transport (fun id loan found => (frozen.present id).mp ⟨loan,found⟩)
  | guarded backing carrier =>
      obtain ⟨backingReplayable,loan,found⟩ := replayable
      obtain ⟨current,currentAt⟩ := (frozen.present carrier).mp ⟨loan,found⟩
      exact ⟨Authority.Replayable.frozen frozen backingReplayable,current,currentAt⟩

/-- The root-local part of the replay admission is retained by the frozen
captured content: residents are the same values, and the loan rows a captured
resident reads reappear with their shared mode. The `Suspensible` closure over
the referents of touching loans is deliberately not included; it is the open
boundary carried separately. -/
theorem Replayable.rootLocal.frozen {program : Kernel.Program} {start before : State}
    {roots : List Identity} (frozen : Suspension.LoansFrozen start before)
    (residents : ∀ address value, address.root ∈ roots →
      (start.world.Resident address value ↔ before.world.Resident address value))
    (admitted : Replayable.rootLocal program start.world roots) :
    Replayable.rootLocal program before.world roots := by
  refine ⟨?_,?_,?_⟩
  · intro address value member current
    exact admitted.1 address value member ((residents address value member).mpr current)
  · intro address value identity loan member current head currentAt
    have source : start.world.Resident address value := (residents address value member).mpr current
    obtain ⟨original,originalAt⟩ := (frozen.present identity).mpr ⟨loan,currentAt⟩
    obtain ⟨mode,_,_⟩ := frozen.shape identity original loan originalAt currentAt
    rw [← mode]
    exact admitted.2.1 address value identity original member source head originalAt
  · intro identity loan currentAt alive member
    obtain ⟨original,originalAt⟩ := (frozen.present identity).mpr ⟨loan,currentAt⟩
    obtain ⟨mode,referent,liveness⟩ := frozen.shape identity original loan originalAt currentAt
    rw [← mode]
    exact admitted.2.2 identity original originalAt (liveness alive) (by rw [referent]; exact member)

/-- The stored row at the replay or cancel site is the row the suspend step
published: the actual resumption-table change of every step retains every
captured-product component of a stored suspension. -/
theorem Suspension.Delivered.retained {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {before : State} {id : Identity}
    {delivered suspension : Suspension}
    (carried : delivered.Delivered program host start trace before id)
    (found : before.resumptions.get id = some suspension) :
    suspension.roots = delivered.roots ∧ suspension.homes = delivered.homes ∧
      suspension.frames = delivered.frames ∧ suspension.handler = delivered.handler ∧
      suspension.context = delivered.context ∧
      suspension.controlAuthoritySupport = delivered.controlAuthoritySupport ∧
      suspension.quantity = delivered.quantity ∧
      suspension.captureRootLimit = delivered.captureRootLimit := by
  obtain ⟨current,present,roots,homes,frames,handler,context,authorities,quantity,limit⟩ :=
    carried.run.stored_product carried.accounted carried.published
  have same : current = suspension := Option.some.inj (present.symm.trans found)
  subst same
  exact ⟨roots,homes,frames,handler,context,authorities,quantity,limit⟩

/-- The stored suspension's physical admission, produced from the suspend-time
product the actual run carried to this state. The captured roots, saved homes,
frames, handler, context, control authorities and capture limit are the
published ones; the snapshot frames, the control replayability and the captured
roots' region liveness are transported, the latter from this state's own
capture invariant rather than from the publishing world. -/
theorem Suspension.Delivered.physicalAdmission {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {before : State} {id : Identity}
    {delivered suspension : Suspension}
    (carried : delivered.Delivered program host start trace before id)
    (found : before.resumptions.get id = some suspension)
    (formed : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (active : suspension.active = true) {bound : Nat}
    (upper : suspension.quantity.upper = some bound) (many : 1 < bound) :
    suspension.PhysicalAdmission program before := by
  obtain ⟨rootsEq,homesEq,framesEq,handlerEq,contextEq,authoritiesEq,quantityEq,_⟩ :=
    carried.retained found
  have controlEq : suspension.controlRegions = delivered.controlRegions :=
    Suspension.controlRegions_congr framesEq contextEq handlerEq
  have closure : Suspensible program before.world suspension.roots := by
    simpa only [rootsEq] using carried.residual.closure
  have share := carried.product.replayable bound (by simpa only [← quantityEq] using upper) many
  have rootPart : Replayable.rootLocal program before.world suspension.roots := by
    have base : Replayable.rootLocal program start.world delivered.roots :=
      Replayable.rootLocal_of_replayable share.1
    have moved : Replayable.rootLocal program before.world delivered.roots :=
      Replayable.rootLocal.frozen carried.residual.frozen.loans
        carried.residual.frozen.residents base
    simpa only [rootsEq] using moved
  refine
    { replayable := ⟨closure,rootPart.1,rootPart.2.1,rootPart.2.2⟩
      controlReplayable := ?_
      frames := ?_
      regionsLive := ?_
      externalScoped := ?_ }
  · intro authority member
    rw [Suspension.controlAuthoritySupport,contextEq,handlerEq,framesEq] at member
    rcases List.mem_append.mp member with live | captured
    · exact carried.residual.controlAuthorities authority live
    · exact Authority.Replayable.frozen carried.residual.frozen.loans
        (carried.product.controlReplayable authority captured)
  · intro frame member
    exact share.2 frame (by simpa only [framesEq] using member)
  · intro region member
    rw [Suspension.inventory_regions] at member
    rcases member with control | ⟨rootId,root,rootMember,rootAt,regionEq⟩
    · exact carried.residual.controlRegionsLive region (by simpa only [controlEq] using control)
    · have live := Suspension.roots_regions_live (state := before) (id := id)
        (suspension := suspension) well formed found active
      exact live region
        (List.mem_filterMap.mpr ⟨rootId,rootMember,by rw [rootAt]; exact congrArg some regionEq⟩)
  · intro address value loanId loan member resident head selected outside type typed region regionMember
    have regionEq : (suspension.inventory program before []).regions =
        (delivered.inventory program before []).regions :=
      Suspension.inventory_regions_congr [] controlEq rootsEq
    exact carried.residual.externalScoped address value loanId loan
      (by simpa only [rootsEq] using member) resident head selected
      (by simpa only [rootsEq] using outside) type typed region
      (by simpa only [regionEq] using regionMember)

/-- The stored suspension's cancellation admission, produced from the same
carried suspend-time product: the closure the capture boundary owns plus the
argument disposal law, which depends on the captured values alone and is
therefore retained by the frozen residents. -/
theorem Suspension.Delivered.cancelable {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {before : State} {id : Identity}
    {delivered suspension : Suspension}
    (carried : delivered.Delivered program host start trace before id)
    (found : before.resumptions.get id = some suspension)
    (lower : suspension.quantity.lower = 0) :
    Cancelable program before.world suspension.roots := by
  obtain ⟨rootsEq,_,_,_,_,_,quantityEq,_⟩ := carried.retained found
  have closure : Suspensible program before.world suspension.roots := by
    simpa only [rootsEq] using carried.residual.closure
  refine ⟨closure,?_⟩
  intro address value member resident
  exact (carried.product.cancelable (by simpa only [← quantityEq] using lower)).2 address value
    (by simpa only [rootsEq] using member)
    ((carried.residual.frozen.residents address value
      (by simpa only [rootsEq] using member)).mpr resident)

/-- The actual saved inventory changes only internal suspended homes. Its
original argument therefore keeps every permission, invariant and handoff
support through final restoration. -/
theorem restoreRoots.handoffReady {program : RuntimeProgram} {before : State}
    {id : Identity} {suspension : Suspension} {value : Value} {access : Access} {footprint : List Address}
    (formed : before.SuspensionsWellFormed) (found : before.resumptions.get id = some suspension)
    (active : suspension.active = true) (ready : value.HandoffReady program before.world access footprint) :
    value.HandoffReady program (restoreRoots before.world suspension.homes) access footprint := by
  rw [restoreRoots.eq_rehome]
  apply ready.rehome (roots := suspension.roots)
  · intro key outside root
    rw [(formed.origin id suspension found).home_none outside]
    rfl
  · intro key member root rootAt
    obtain ⟨actual,actualAt,_,suspended⟩ := (formed.active id suspension found active key).mp member
    have same : root = actual := Option.some.inj (rootAt.symm.trans actualAt)
    rw [same,suspended]
    constructor <;> (intro domain equal; cases equal)


/-- The final replay of one live suspension reaches the actual replay step or
the real exhaustion of the restored argument's temporary home, entirely from
the original world and its active capture inventory. This is the restoration
site: its rule needs the restored argument's storage, permission and layout
request and no physical snapshot admission, and a one-shot quantity has no
replay share to consume, so this theorem takes no carrier. -/
theorem resumeLast_or_exhausted {program : Kernel.Program} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (found : before.resumptions.get id = some suspension)
    (active : ActiveObligation suspension) (last : suspension.remaining = 1)
    (valid : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
    (∃ (destination : Address) (transferred : World), EffectStep program before (some (.replay id true))
      { before with
        world := transferred
        task := .yield suspension.context destination
        frames := suspension.frames ++ [.handler suspension.handler false,.resumed caller] ++ before.frames
        resumptions := before.resumptions.set id
          { suspension with remaining := 0, used := suspension.used+1, active := false } }) ∨
    EffectStep program before (some (.fatal .resource))
      { before with world := restoreRoots before.world suspension.homes, task := .fatal .resource } := by
  have storedAfter : (restoreRoots before.world suspension.homes).Stores argument.address value := by
    rw [restoreRoots.eq_rehome]
    exact World.rehome_stores.mpr stored
  have readyAfter := restoreRoots.handoffReady formed found active.1 ready
  have permissionAfter : Permitted (restoreRoots before.world suspension.homes) argument.authority .owned argument.address := by
    rw [restoreRoots.eq_rehome]
    exact permission.rehome
  have requestAfter := request.same_regions (after := restoreRoots before.world suspension.homes) rfl rfl
  rcases Protect.success_or_exhausted (context := suspension.context) (restoreRoots.wellFormed valid)
    storedAfter initialized readyAfter permissionAfter requestAfter with ⟨destination,transferred,kept⟩ | exhausted
  · exact Or.inl ⟨destination,transferred,.resumeLast task found active last rfl kept⟩
  · exact Or.inr (.resumeLastExhausted task found active last rfl exhausted)

/-- The copy replay of one live suspension reaches the actual copied replay
step, the real exhaustion of the copied argument's temporary home, or the real
physical exhaustion of the snapshot placement itself. The original argument
supplies storage, readiness, permission and a positive layout request. Actual
shared-loan copying derives its handoff frame and the copied world invariant.
The physical admission is produced from the suspend-time product the run
carried here, not premised. -/
theorem resumeCopy_or_blocked {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {delivered : Suspension} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (obligation : ActiveObligation suspension) (positive : 1 < suspension.remaining)
    (carried : delivered.Delivered program host start trace before id)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
    (∃ (map : Relocation) (copied : State) (destination : Address) (transferred : World),
      CopiesSnapshot program before suspension map copied ∧
      EffectStep program before (some (.replay id false))
        { copied with
          world := transferred
          task := .yield (map.context suspension.context) destination
          frames := suspension.frames.map map.frame ++
            [.handler (map.installed suspension.handler) false,.resumed caller] ++ before.frames
          resumptions := before.resumptions.set id
            { suspension with remaining := suspension.remaining-1, used := suspension.used+1 } }) ∨
    (∃ (map : Relocation) (copied : State), CopiesSnapshot program before suspension map copied ∧
      EffectStep program before (some (.fatal .resource)) { copied with task := .fatal .resource }) ∨
    EffectStep program before (some (.fatal .resource)) { before with task := .fatal .resource } := by
  have admission := carried.physicalAdmission found formed well active obligation.2.2.2 (by omega)
  rcases suspension.copiesSnapshot_or_blocked well formed found active admission with
    ⟨table,copied,copiedEq,copying⟩ | blocked
  · subst copiedEq
    have storedAfter : _ := World.resident_iff_stores.mp
      (Relocation.old_resident (map := suspension.inventory program before table) (homes := suspension.homes)
        (World.resident_iff_stores.mpr stored))
    have readyAfter := copying.old_handoffReady well ready
    have permissionAfter := copying.relocation.old_permitted (homes := suspension.homes) well permission
    have targetLive := Relocation.region_live (map := suspension.inventory program before table)
      (homes := suspension.homes) request.region_live
    have requestAfter := request.retarget targetLive (Nat.le_add_left _ _)
    rcases Protect.success_or_exhausted
      (context := (suspension.inventory program before table).context suspension.context)
      (copying.wellFormed well) storedAfter initialized readyAfter permissionAfter requestAfter with
      ⟨destination,transferred,kept⟩ | exhausted
    · exact Or.inl ⟨_,_,destination,transferred,copying,
        .resumeCopy task found obligation positive copying kept⟩
    · exact Or.inr (Or.inl ⟨_,_,copying,
        .resumeCopyExhausted task found obligation positive copying exhausted⟩)
  · exact Or.inr (Or.inr (.resumeCopyBlocked task found obligation positive blocked))

/-- Every active, accounted ordinary replay with an originally ready argument
has an actual machine step. The budget chooses restoration versus copying;
only the latter asks for the carried physical snapshot admission. Failure
retains the exact real allocation prefix provided by the branch theorem. -/
theorem resume_progress {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {delivered : Suspension} {before : State}
    {caller : Context} {id : Identity} {argument : ResolvedPlace} {suspension : Suspension}
    {value : Value} {layout : Layout}
    (task : before.task = .resume caller id argument false)
    (well : before.world.WellFormed) (formed : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (carried : delivered.Delivered program host start trace before id)
    (stored : before.world.Stores argument.address value) (initialized : value.Initialized)
    (ready : value.MoveReady program before.world [argument.address])
    (permission : Permitted before.world argument.authority .owned argument.address)
    (request : AllocationRequest program.declarations before.world suspension.context.region value.type layout) :
    ∃ event after, EffectStep program before (some event) after ∧
      (event = .replay id true ∨ event = .replay id false ∨ event = .fatal .resource) := by
  have accounted := formed.budgets.accounted id suspension found
  have obligation : ActiveObligation suspension :=
    ⟨active,accounted.original,accounted.quantity,(accounted.active active).2⟩
  by_cases last : suspension.remaining = 1
  · rcases resumeLast_or_exhausted task found obligation last well formed
      stored initialized ready permission request with
      ⟨destination,transferred,step⟩ | exhausted
    · exact ⟨_,_,step,Or.inl rfl⟩
    · exact ⟨_,_,exhausted,Or.inr (Or.inr rfl)⟩
  · have positive : 1 < suspension.remaining := by
      have remaining := (accounted.active active).1
      omega
    rcases resumeCopy_or_blocked task well formed found active obligation positive carried
      stored initialized ready permission request with
      ⟨map,copied,destination,transferred,copying,step⟩ | ⟨map,copied,copying,exhausted⟩ | blocked
    · exact ⟨_,_,step,Or.inr (Or.inl rfl)⟩
    · exact ⟨_,_,exhausted,Or.inr (Or.inr rfl)⟩
    · exact ⟨_,_,blocked,Or.inr (Or.inr rfl)⟩


/-- An active resumption with a spent lower budget quantity and the
cancellation admission its own suspend-time product carries executes the real
cancellation step. -/
theorem cancel_progress {program : Kernel.Program} {host : Foreign.Model}
    {start : State} {trace : List Event} {delivered : Suspension} {before : State}
    {context : Context} {id : Identity} {next : Task} {suspension : Suspension}
    (task : before.task = .cancel context id next)
    (found : before.resumptions.get id = some suspension)
    (active : ActiveObligation suspension) (lower : suspension.quantity.lower = 0)
    (carried : delivered.Delivered program host start trace before id) :
    EffectStep program before (some (.cancel id))
      { before with
        world := restoreRoots before.world suspension.homes
        task := .cleanup context suspension.roots (CloseRegions (SuspensionRegions suspension) next)
        resumptions := before.resumptions.set id { suspension with active := false, remaining := 0 } } :=
  .cancel task found active lower (carried.cancelable found lower)

end Glorious.Language.Execution
