import GloriousLanguage.EffectPreservation
import GloriousLanguage.ResumptionPreservation
import GloriousLanguage.SuspensionStorage

/-! Historical root provenance and active suspension ownership, derived from
the real capture, restoration and storage producers. Capture bounds remain
valid after settlement; they do not grant liveness to canceled storage. -/
namespace Glorious.Language

open Kernel

theorem Kernel.HomeOwnedByActivation.activation_home {home : Home} {activation : Identity}
    (owned : HomeOwnedByActivation home activation) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with ⟨scope,home⟩ | ⟨scope,home⟩
  · exact ⟨activation,scope,Or.inl home⟩
  · exact ⟨activation,scope,Or.inr home⟩

namespace Execution

theorem FrameOwnsHome.activation_home {frame : Frame} {home : Home} (owned : FrameOwnsHome frame home) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  cases frame <;> simp only [FrameOwnsHome] at owned
  all_goals first
    | exact owned.elim
    | exact owned.activation_home
    | exact ⟨_,_,owned⟩
    | (rcases owned with owned | ⟨_,owned⟩
       · first | exact owned.activation_home | exact ⟨_,_,owned⟩
       · exact owned.activation_home)

theorem FrameOwns.activation_home {frame : Frame} {root : Root} (owned : FrameOwns frame root) :
    ∃ activation scope, root.home = .localSlot activation scope ∨ root.home = .temporary activation scope :=
  FrameOwnsHome.activation_home owned

theorem CapturedHome.activation_home {handler : InstalledHandler} {inner : List Frame} {home : Home}
    (owned : CapturedHome handler inner home) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope := by
  rcases owned with owned | ⟨frame,_,owned⟩
  · exact ⟨_,_,owned⟩
  · exact owned.activation_home

theorem Suspension.CaptureOrigin.activationHomes {suspension : Suspension}
    (origin : suspension.CaptureOrigin) (root : Identity) (home : Home)
    (found : suspension.homes.get root = some home) :
    ∃ activation scope, home = .localSlot activation scope ∨ home = .temporary activation scope :=
  (origin.ownedHomes root home found).activation_home

theorem DelimitedRoots.selected {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} (selected : DelimitedRoots world handler inner kept roots)
    {id : Identity} (member : id ∈ roots) :
    ∃ root, world.roots.get id = some root ∧ root.live = true ∧
      ∃ activation scope, root.home = .localSlot activation scope ∨ root.home = .temporary activation scope := by
  obtain ⟨root,found,live,_,owned⟩ := (selected.2 id).mp member
  refine ⟨root,found,live,?_⟩
  rcases owned with owned | ⟨frame,_,owned⟩
  · exact ⟨_,_,owned⟩
  · exact owned.activation_home

theorem SaveHomes.unique {world : World} {roots : List Identity} {homes : Table Home}
    (unique : world.roots.Unique) (saved : SaveHomes world roots homes) : homes.Unique := by
  subst homes
  change (((world.roots.filter _).map _).map Prod.fst).Nodup
  simpa only [List.map_map,Function.comp_def] using
    unique.sublist ((List.filter_sublist).map Prod.fst)

theorem SaveHomes.get_iff {world : World} {roots : List Identity} {homes : Table Home}
    (unique : world.roots.Unique) (saved : SaveHomes world roots homes) {id : Identity} {home : Home} :
    homes.get id = some home ↔ id ∈ roots ∧ ∃ root, world.roots.get id = some root ∧ root.home = home := by
  have homesUnique := saved.unique unique
  constructor
  · intro found
    have member := Table.mem_of_get found
    rw [saved] at member
    obtain ⟨⟨key,root⟩,member,same⟩ := List.mem_map.mp member
    obtain ⟨present,selected⟩ := List.mem_filter.mp member
    have key : key = id := congrArg Prod.fst same
    have home : root.home = home := congrArg Prod.snd same
    subst key
    exact ⟨by simpa using selected,root,unique.get_of_mem present,home⟩
  · rintro ⟨selected,root,found,rfl⟩
    apply homesUnique.get_of_mem
    rw [saved]
    exact List.mem_map.mpr ⟨(id,root),List.mem_filter.mpr ⟨Table.mem_of_get found,by simpa using selected⟩,rfl⟩

/-- The immutable capture limit and saved homes are produced by the same
actual delimited-root selection that suspension executes. -/
theorem DelimitedRoots.capture_origin {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} {homes : Table Home} {suspension : Suspension}
    (well : world.WellFormed) (selected : DelimitedRoots world handler inner kept roots)
    (saved : SaveHomes world roots homes) (rootList : suspension.roots = roots)
    (savedHomes : suspension.homes = homes) (limit : suspension.captureRootLimit = world.nextRoot)
    (capturedHandler : suspension.handler = handler) (capturedFrames : suspension.frames = inner)
    (foreignFree : ∀ frame ∈ inner, frame.ForeignFree) :
    suspension.CaptureOrigin := by
  refine ⟨by simpa [rootList] using selected.1.1,?_,by simpa [savedHomes] using saved.unique well.1,?_,?_,?_⟩
  · intro id member
    obtain ⟨root,found,_⟩ := selected.selected (by simpa [rootList] using member)
    simpa [limit] using World.root_bound well found
  · intro id
    simp only [rootList,savedHomes]
    constructor
    · rintro ⟨home,found⟩
      exact ((saved.get_iff well.1).mp found).1
    · intro member
      obtain ⟨root,found,_⟩ := selected.selected member
      exact ⟨root.home,(saved.get_iff well.1).mpr ⟨member,root,found,rfl⟩⟩
  · intro id home found
    obtain ⟨member,root,rootAt,homeEq⟩ := (saved.get_iff well.1).mp (by simpa [savedHomes] using found)
    obtain ⟨original,originalAt,_,_,owned⟩ := (selected.2 id).mp member
    have same : root = original := Option.some.inj (rootAt.symm.trans originalAt)
    subst original
    simpa only [capturedHandler,capturedFrames] using homeEq ▸ owned
  · simpa only [capturedFrames] using foreignFree

theorem suspendRoots.get {world : World} {roots : List Identity} {suspension id : Identity} :
    (suspendRoots world roots suspension).roots.get id =
      (world.roots.get id).map (fun root => if id ∈ roots then { root with home := .suspended suspension } else root) :=
  Table.get_map_keyed world.roots (fun key (root : Root) =>
    if key ∈ roots then ({ root with home := .suspended suspension } : Root) else root) id

theorem restoreRoots.get {world : World} {homes : Table Home} {id : Identity} :
    (restoreRoots world homes).roots.get id =
      (world.roots.get id).map (fun root => { root with home := (homes.get id).getD root.home }) :=
  Table.get_map_keyed world.roots (fun key (root : Root) =>
    ({ root with home := (homes.get key).getD root.home } : Root)) id

/-- Root membership is exactly the storage actually rehomed by capture.
Freshness prevents an old unrelated suspended home from joining the domain. -/
theorem DelimitedRoots.suspended_iff {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} {id : Identity}
    (selected : DelimitedRoots world handler inner kept roots)
    (fresh : ∀ rootId root, world.roots.get rootId = some root → root.home ≠ .suspended id) :
    ∀ rootId, rootId ∈ roots ↔ ∃ root, (suspendRoots world roots id).roots.get rootId = some root ∧
      root.live = true ∧ root.home = .suspended id := by
  intro rootId
  constructor
  · intro member
    obtain ⟨root,found,live,_⟩ := selected.selected member
    exact ⟨{ root with home := .suspended id },by simp [suspendRoots.get,found,member],live,rfl⟩
  · rintro ⟨root,found,live,home⟩
    rw [suspendRoots.get] at found
    obtain ⟨original,originalAt,equal⟩ := Option.map_eq_some_iff.mp found
    by_cases member : rootId ∈ roots
    · exact member
    · simp only [member,↓reduceIte] at equal
      subst root
      exact False.elim (fresh rootId original originalAt home)

theorem CreatesContinuation.root_counter {program : Kernel.Program} {context : Context} {before after : World}
    {id signature answer effects quantity localSlot address}
    (created : CreatesContinuation program context before id signature answer effects quantity localSlot address after) :
    after.nextRoot = before.nextRoot+1 := by
  obtain ⟨allocated,layout,type,allocation,constructed⟩ := created
  have same := congrArg World.nextRoot constructed.rest
  cases allocation
  exact same

/-- Both real suspension instructions publish a historical capture product
whose bound precedes even the newly allocated continuation handle. -/
theorem EffectStep.created_capture {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.suspend id)) after) :
    ∃ suspension, after.resumptions.get id = some suspension ∧ suspension.CaptureOrigin ∧
      suspension.captureRootLimit ≤ after.world.nextRoot := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer roots permission homes created plan suspension =>
    subst suspension
    have movedTyped := keptTransfer.worldTyped valid inventory (started.worldTyped typed)
    refine ⟨_,Table.get_set _ _ _,roots.capture_origin movedTyped.1 homes rfl rfl rfl rfl rfl routes.foreign_free,?_⟩
    exact Nat.le_of_lt (Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) created.root_counter.symm)
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer roots permission homes plan suspension =>
    subst suspension
    have movedTyped := keptTransfer.worldTyped valid inventory (started.worldTyped typed)
    exact ⟨_,Table.get_set _ _ _,roots.capture_origin movedTyped.1 homes rfl rfl rfl rfl rfl routes.foreign_free,Nat.le_refl _⟩

theorem Suspension.CaptureOrigin.home_not_suspended {suspension : Suspension}
    (origin : suspension.CaptureOrigin) {root : Identity} {home : Home}
    (found : suspension.homes.get root = some home) (id : Identity) : home ≠ .suspended id := by
  obtain ⟨activation,scope,localHome | temporaryHome⟩ := origin.activationHomes root home found
  · simp [localHome]
  · simp [temporaryHome]

theorem Suspension.CaptureOrigin.transport {before after : Suspension} (origin : before.CaptureOrigin)
    (roots : after.roots = before.roots) (homes : after.homes = before.homes)
    (limit : after.captureRootLimit = before.captureRootLimit)
    (handler : after.handler = before.handler) (frames : after.frames = before.frames) : after.CaptureOrigin := by
  refine ⟨by simpa only [roots] using origin.roots,?_,by simpa only [homes] using origin.homes,?_,?_,?_⟩
  · simpa only [roots,limit] using origin.bounded
  · simpa only [roots,homes] using origin.domain
  · simpa only [homes,handler,frames] using origin.ownedHomes
  · simpa only [frames] using origin.foreignFree

theorem Suspension.CaptureOrigin.home_none {suspension : Suspension}
    (origin : suspension.CaptureOrigin) {root : Identity} (outside : root ∉ suspension.roots) :
    suspension.homes.get root = none := by
  cases found : suspension.homes.get root with
  | none => rfl
  | some home => exact False.elim (outside ((origin.domain root).mp ⟨home,found⟩))

/-- Active capture inventories are disjoint because a root has one actual
storage home. No separate pairwise ownership ledger is assumed. -/
theorem State.SuspensionsWellFormed.active_disjoint {state : State}
    (valid : state.SuspensionsWellFormed) {left right : Identity} {first last : Suspension}
    (leftAt : state.resumptions.get left = some first) (leftActive : first.active = true)
    (rightAt : state.resumptions.get right = some last) (rightActive : last.active = true)
    (different : left ≠ right) {rootId : Identity} (member : rootId ∈ first.roots) : rootId ∉ last.roots := by
  intro other
  obtain ⟨root,found,_,home⟩ := (valid.active left first leftAt leftActive rootId).mp member
  obtain ⟨current,currentAt,_,currentHome⟩ := (valid.active right last rightAt rightActive rootId).mp other
  have same := Option.some.inj (found.symm.trans currentAt)
  subst current
  exact different (Home.suspended.inj (home.symm.trans currentHome))

theorem restoreRoots.suspended_origin {world : World} {suspension : Suspension}
    (origin : suspension.CaptureOrigin) {rootId id : Identity} {root : Root}
    (found : (restoreRoots world suspension.homes).roots.get rootId = some root)
    (home : root.home = .suspended id) :
    ∃ original, world.roots.get rootId = some original ∧ root = original := by
  rw [restoreRoots.get] at found
  obtain ⟨original,originalAt,equal⟩ := Option.map_eq_some_iff.mp found
  cases saved : suspension.homes.get rootId with
  | none =>
    simp only [saved,Option.getD_none] at equal
    exact ⟨original,originalAt,equal.symm⟩
  | some oldHome =>
    have restoredHome := congrArg Root.home equal
    simp only [saved,Option.getD_some] at restoredHome
    exact False.elim (origin.home_not_suspended saved id (restoredHome.trans home))

theorem suspendRoots.suspended_origin_other {world : World} {roots : List Identity}
    {id other rootId : Identity} {root : Root} (different : other ≠ id)
    (found : (suspendRoots world roots id).roots.get rootId = some root)
    (home : root.home = .suspended other) : ∃ original, world.roots.get rootId = some original ∧ root = original := by
  rw [suspendRoots.get] at found
  obtain ⟨original,originalAt,equal⟩ := Option.map_eq_some_iff.mp found
  by_cases member : rootId ∈ roots
  · simp only [member,↓reduceIte] at equal
    have impossible := congrArg Root.home equal
    exact False.elim (different (Home.suspended.inj (impossible.trans home)).symm)
  · simp only [member,↓reduceIte] at equal
    exact ⟨original,originalAt,equal.symm⟩

theorem DelimitedRoots.retains_suspended {world : World} {handler : InstalledHandler} {inner : List Frame}
    {kept roots : List Identity} {rootId id other : Identity} {root : Root}
    (selected : DelimitedRoots world handler inner kept roots)
    (found : world.roots.get rootId = some root) (home : root.home = .suspended other) :
    (suspendRoots world roots id).roots.get rootId = some root := by
  have outside : rootId ∉ roots := by
    intro member
    obtain ⟨original,originalAt,_,activation,scope,localHome | temporaryHome⟩ := selected.selected member
    all_goals
      have same : root = original := Option.some.inj (found.symm.trans originalAt)
      subst original
      simp_all
  simp only [suspendRoots.get,found,Option.map_some,outside,↓reduceIte]

theorem Suspension.Accounted.created {suspension : Suspension}
    (original : suspension.original = true) (active : suspension.active = true) (used : suspension.used = 0)
    (quantity : suspension.quantity.SurfaceResumption) (bound : suspension.quantity.upper = some suspension.remaining) :
    suspension.Accounted := by
  refine ⟨original,quantity,?_,?_⟩
  · intro _
    exact ⟨(quantity.bound bound).1,by simpa only [used,Nat.add_zero] using bound⟩
  · simp [active]

/-- The real delimited-root producer establishes a new suspension while
retaining all previously active capture domains. -/
theorem State.SuspensionsWellFormed.capture {before : State} {handler : InstalledHandler}
    {inner : List Frame} {kept roots : List Identity} {homes : Table Home} {suspension : Suspension}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (selected : DelimitedRoots before.world handler inner kept roots) (saved : SaveHomes before.world roots homes)
    (accounted : suspension.Accounted) (identity : suspension.identity = before.nextContinuation)
    (_active : suspension.active = true) (rootList : suspension.roots = roots)
    (savedHomes : suspension.homes = homes) (limit : suspension.captureRootLimit = before.world.nextRoot)
    (capturedHandler : suspension.handler = handler) (capturedFrames : suspension.frames = inner)
    (foreignFree : ∀ frame ∈ inner, frame.ForeignFree) :
    State.SuspensionsWellFormed { before with world := suspendRoots before.world roots before.nextContinuation, resumptions := before.resumptions.set before.nextContinuation suspension, nextContinuation := before.nextContinuation+1 } := by
  have origin := selected.capture_origin well saved rootList savedHomes limit capturedHandler capturedFrames foreignFree
  have fresh : ∀ rootId root, before.world.roots.get rootId = some root → root.home ≠ .suspended before.nextContinuation := by
    intro rootId root found home
    exact Nat.lt_irrefl _ (valid.homeFresh rootId root before.nextContinuation found home)
  refine ⟨valid.budgets.set accounted identity (Nat.lt_succ_self _) (Nat.le_succ _) rfl,?_,?_,?_,?_⟩
  · intro target actual found
    by_cases same : target = before.nextContinuation
    · subst target
      simp only [Table.get_set,Option.some.injEq] at found
      subst actual
      exact origin
    · exact valid.origin target actual (by simpa only [Table.get_set_other _ _ _ _ same] using found)
  · intro target actual found
    by_cases same : target = before.nextContinuation
    · subst target
      simp only [Table.get_set,Option.some.injEq] at found
      subst actual
      exact Nat.le_of_eq limit
    · exact valid.frontier target actual (by simpa only [Table.get_set_other _ _ _ _ same] using found)
  · intro target actual found stillActive rootId
    by_cases same : target = before.nextContinuation
    · subst target
      simp only [Table.get_set,Option.some.injEq] at found
      subst actual
      simpa only [rootList] using selected.suspended_iff fresh rootId
    · have originalAt : before.resumptions.get target = some actual := by
        simpa only [Table.get_set_other _ _ _ _ same] using found
      constructor
      · intro member
        obtain ⟨root,rootAt,live,home⟩ := (valid.active target actual originalAt stillActive rootId).mp member
        exact ⟨root,selected.retains_suspended rootAt home,live,home⟩
      · rintro ⟨root,rootAt,live,home⟩
        obtain ⟨original,originalRootAt,equal⟩ := suspendRoots.suspended_origin_other same rootAt home
        subst root
        exact (valid.active target actual originalAt stillActive rootId).mpr ⟨original,originalRootAt,live,home⟩
  · intro rootId root id found home
    by_cases same : id = before.nextContinuation
    · subst id
      exact Nat.lt_succ_self _
    · obtain ⟨original,originalAt,equal⟩ := suspendRoots.suspended_origin_other same found home
      subst root
      exact Nat.lt_trans (valid.homeFresh rootId original id originalAt home) (Nat.lt_succ_self _)

theorem State.SuspensionsWellFormed.restore_other {state : State}
    (valid : state.SuspensionsWellFormed) {id other : Identity} {suspension retained : Suspension}
    (selected : state.resumptions.get id = some suspension) (active : suspension.active = true)
    (retainedAt : state.resumptions.get other = some retained) (retainedActive : retained.active = true)
    (different : other ≠ id) :
    ∀ rootId, rootId ∈ retained.roots ↔
      ∃ root, (restoreRoots state.world suspension.homes).roots.get rootId = some root ∧
        root.live = true ∧ root.home = .suspended other := by
  intro rootId
  constructor
  · intro member
    obtain ⟨root,found,live,home⟩ := (valid.active other retained retainedAt retainedActive rootId).mp member
    have outside := valid.active_disjoint retainedAt retainedActive selected active different member
    have absent := (valid.origin id suspension selected).home_none outside
    exact ⟨root,by simp [restoreRoots.get,found,absent],live,home⟩
  · rintro ⟨root,found,live,home⟩
    obtain ⟨original,originalAt,equal⟩ := restoreRoots.suspended_origin (valid.origin id suspension selected) found home
    subst root
    exact (valid.active other retained retainedAt retainedActive rootId).mpr ⟨original,originalAt,live,home⟩

theorem State.SuspensionsWellFormed.transport {before after : State}
    (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (storage : before.world.SuspensionExtension after.world)
    (table : after.resumptions = before.resumptions)
    (counter : before.nextContinuation ≤ after.nextContinuation) : after.SuspensionsWellFormed := by
  refine ⟨valid.budgets.transport table counter,?_,?_,?_,?_⟩
  · intro id suspension found
    exact valid.origin id suspension (by simpa only [table] using found)
  · intro id suspension found
    exact Nat.le_trans (valid.frontier id suspension (by simpa only [table] using found)) storage.counter
  · intro id suspension found active rootId
    have originalAt : before.resumptions.get id = some suspension := by simpa only [table] using found
    constructor
    · intro member
      obtain ⟨root,rootAt,live,home⟩ := (valid.active id suspension originalAt active rootId).mp member
      obtain ⟨current,currentAt,location⟩ := Option.map_eq_some_iff.mp
        (storage.retained rootId root id (World.root_bound well rootAt) rootAt home)
      have currentHome : current.home = root.home := by simpa only [Root.location] using congrArg Root.home location
      have currentLive : current.live = root.live := by simpa only [Root.location] using congrArg Root.live location
      exact ⟨current,currentAt,currentLive.trans live,currentHome.trans home⟩
    · rintro ⟨root,rootAt,live,home⟩
      obtain ⟨original,originalRootAt,location⟩ := storage.origin rootId root id rootAt home
      have originalHome : root.home = original.home := by simpa only [Root.location] using congrArg Root.home location
      have originalLive : root.live = original.live := by simpa only [Root.location] using congrArg Root.live location
      exact (valid.active id suspension originalAt active rootId).mpr
        ⟨original,originalRootAt,originalLive.symm.trans live,originalHome.symm.trans home⟩
  · intro rootId root id found home
    obtain ⟨original,originalAt,location⟩ := storage.origin rootId root id found home
    have originalHome : root.home = original.home := by simpa only [Root.location] using congrArg Root.home location
    exact Nat.lt_of_lt_of_le (valid.homeFresh rootId original id originalAt (originalHome.symm.trans home)) counter

/-- Final replay and cancellation use one actual saved-home restoration.
Only the budget update differs; all immutable capture metadata is retained. -/
theorem State.SuspensionsWellFormed.restore_settled {before : State} {id : Identity}
    {suspension settled : Suspension} (valid : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension) (active : suspension.active = true)
    (accounted : settled.Accounted) (identity : settled.identity = id) (inactive : settled.active = false)
    (roots : settled.roots = suspension.roots) (homes : settled.homes = suspension.homes)
    (limit : settled.captureRootLimit = suspension.captureRootLimit)
    (handler : settled.handler = suspension.handler) (frames : settled.frames = suspension.frames) :
    State.SuspensionsWellFormed { before with world := restoreRoots before.world suspension.homes, resumptions := before.resumptions.set id settled } := by
  refine ⟨valid.budgets.set accounted identity (valid.budgets.fresh id suspension found) (Nat.le_refl _) rfl,?_,?_,?_,?_⟩
  · intro target actual selected
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      exact (valid.origin id suspension found).transport roots homes limit handler frames
    · exact valid.origin target actual (by simpa only [Table.get_set_other _ _ _ _ same] using selected)
  · intro target actual selected
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      simpa only [limit,restoreRoots] using valid.frontier id suspension found
    · exact valid.frontier target actual (by simpa only [Table.get_set_other _ _ _ _ same] using selected)
  · intro target actual selected stillActive
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      simp only [inactive,Bool.false_eq_true] at stillActive
    · exact valid.restore_other found active
        (by simpa only [Table.get_set_other _ _ _ _ same] using selected) stillActive same
  · intro rootId root suspensionId selected home
    obtain ⟨original,originalAt,equal⟩ := restoreRoots.suspended_origin (valid.origin id suspension found) selected home
    subst root
    exact valid.homeFresh rootId original suspensionId originalAt home

/-- Changing an active replay budget retains the same historical inventory
and the same actual ownership. The budget theorem remains authoritative. -/
theorem State.SuspensionsWellFormed.replace_budget {before : State} {id : Identity}
    {suspension replacement : Suspension} (valid : before.SuspensionsWellFormed)
    (found : before.resumptions.get id = some suspension)
    (accounted : replacement.Accounted) (identity : replacement.identity = id)
    (activity : replacement.active = suspension.active) (roots : replacement.roots = suspension.roots)
    (homes : replacement.homes = suspension.homes) (limit : replacement.captureRootLimit = suspension.captureRootLimit)
    (handler : replacement.handler = suspension.handler) (frames : replacement.frames = suspension.frames) :
    State.SuspensionsWellFormed { before with resumptions := before.resumptions.set id replacement } := by
  refine ⟨valid.budgets.set accounted identity (valid.budgets.fresh id suspension found) (Nat.le_refl _) rfl,?_,?_,?_,valid.homeFresh⟩
  · intro target actual selected
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      exact (valid.origin id suspension found).transport roots homes limit handler frames
    · exact valid.origin target actual (by simpa only [Table.get_set_other _ _ _ _ same] using selected)
  · intro target actual selected
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      simpa only [limit] using valid.frontier id suspension found
    · exact valid.frontier target actual (by simpa only [Table.get_set_other _ _ _ _ same] using selected)
  · intro target actual selected active
    by_cases same : target = id
    · subst target
      simp only [Table.get_set,Option.some.injEq] at selected
      subst actual
      simpa only [roots] using valid.active id suspension found (activity ▸ active)
    · exact valid.active target actual (by simpa only [Table.get_set_other _ _ _ _ same] using selected) active

/-- Copied roots are restored to their actual saved local/temporary homes
before relocation. A copy cannot impersonate another suspended inventory. -/
theorem CopiesSnapshot.suspensionExtension {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} (well : before.world.WellFormed)
    (origin : suspension.CaptureOrigin) (copied : CopiesSnapshot program before suspension map after) :
    before.world.SuspensionExtension after.world := by
  rw [copied.result]
  refine ⟨Nat.le_add_left _ _,?_,?_,fun _ recorded =>
    recorded.transport (fun _ loan found => ⟨loan,Relocation.old_loan found⟩)⟩
  · intro id root _ _ found _
    rw [Relocation.old_root found]; rfl
  · intro id root suspensionId found home
    rcases Relocation.root_origin well.1 found with original | ⟨old,original,originalAt,member,idEq,rootEq⟩
    · exact ⟨root,original,rfl⟩
    · obtain ⟨saved,savedAt⟩ := (origin.domain old).mpr (by simpa only [copied.relocation.roots] using member)
      obtain ⟨activation,scope,localHome | temporaryHome⟩ := origin.activationHomes old saved savedAt
      · simp only [rootEq,Relocation.rootValue,savedAt,Option.getD_some,localHome,Relocation.home] at home
        cases home
      · simp only [rootEq,Relocation.rootValue,savedAt,Option.getD_some,temporaryHome,Relocation.home] at home
        cases home

/-- Cancellation really restores saved homes before scheduling destruction.
This is the complete unified invariant for that transition, not a cleanup
postcondition assumed by the cancellation instruction. -/
theorem EffectStep.cancel_suspension_storage {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed)
    (step : EffectStep program before (some (.cancel id)) after) : after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  cases step with
  | @cancel context _ next suspension task found obligation optional cancelable =>
    have settled := valid.restore_settled found obligation.1 (obligation.cancel_accounted optional)
      (valid.budgets.identity id suspension found) rfl rfl rfl rfl rfl rfl
    exact ⟨⟨settled.budgets.transport rfl (Nat.le_refl _),settled.origin,settled.frontier,settled.active,settled.homeFresh⟩,
      fun _ recorded => recorded⟩

/-- The last replay releases the original inventory, then executes the
ordinary protected argument transfer. Other active captures remain owned. -/
theorem EffectStep.last_suspension_storage {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.replay id true)) after) : after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  cases step with
  | resumeLast task found obligation remaining restored keptTransfer =>
    subst restored
    have identity := valid.budgets.identity _ _ found
    have settled := valid.restore_settled found obligation.1 (obligation.last_accounted remaining)
      identity rfl rfl rfl rfl rfl rfl
    exact ⟨settled.transport (restoreRoots.worldTyped typed).1 keptTransfer.suspensionExtension rfl (Nat.le_refl _),
      keptTransfer.suspensionExtension.recorded⟩

/-- Multi-shot replay leaves the original capture active and executes on
fresh local copies. Both old and newly allocated suspended-home origins are
accounted for by the actual finite relocation. -/
theorem EffectStep.copy_suspension_storage {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.replay id false)) after) : after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  cases step with
  | resumeCopy task found obligation remaining copied keptTransfer =>
    have identity := valid.budgets.identity _ _ found
    have replaced := valid.replace_budget found (obligation.copy_accounted remaining) identity rfl rfl rfl rfl rfl rfl
    have stored := copied.suspensionExtension typed.1 (valid.origin _ _ found)
    exact ⟨replaced.transport typed.1 (stored.trans keptTransfer.suspensionExtension) rfl
      (by rw [copied.result]; exact Nat.le_refl _), (stored.trans keptTransfer.suspensionExtension).recorded⟩

/-- Both executable capture forms preserve the entire suspension invariant,
including new continuation allocation after the captured root limit. -/
theorem EffectStep.create_suspension_storage {program : Kernel.Program} {before after : State} {id : Identity}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.suspend id)) after) : after.SuspensionsWellFormed ∧
      ∀ (authority : Authority), authority.Recorded before.world.loans → authority.Recorded after.world.loans := by
  cases step with
  | suspend task selected terminal quantity bound continuation routes started keptTransfer roots permission homes created plan suspension =>
    rename_i newSuspension
    have movedTyped := keptTransfer.worldTyped programValid inventory (started.worldTyped typed)
    have movedValid := valid.transport (after := { before with world := _ }) typed.1
      (started.suspensionExtension.trans keptTransfer.suspensionExtension) rfl (Nat.le_refl _)
    have accounted : newSuspension.Accounted := .created (by simp [suspension]) (by simp [suspension])
      (by simp [suspension]) (by simpa only [suspension] using permission.1) (by simpa only [suspension] using bound)
    have captured := movedValid.capture (suspension := newSuspension) movedTyped.1 roots homes accounted
      (by simp [suspension]) (by simp [suspension]) (by simp [suspension]) (by simp [suspension]) (by simp [suspension])
      (by simp [suspension]) (by simp [suspension]) routes.foreign_free
    exact ⟨captured.transport (suspendRoots.worldTyped movedTyped).1 created.suspensionExtension rfl (Nat.le_refl _),
      fun authority recorded => created.suspensionExtension.recorded authority
        ((started.suspensionExtension.trans keptTransfer.suspensionExtension).recorded authority recorded)⟩
  | suspendTailArm task selected terminal quantity bound contains continuation routes started keptTransfer roots permission homes plan suspension =>
    rename_i newSuspension
    have movedTyped := keptTransfer.worldTyped programValid inventory (started.worldTyped typed)
    have movedValid := valid.transport (after := { before with world := _ }) typed.1
      (started.suspensionExtension.trans keptTransfer.suspensionExtension) rfl (Nat.le_refl _)
    have accounted : newSuspension.Accounted := .created (by simp [suspension]) (by simp [suspension])
      (by simp [suspension]) (by simpa only [suspension] using permission.1) (by simpa only [suspension] using bound)
    have captured := movedValid.capture (suspension := newSuspension) movedTyped.1 roots homes accounted
      (by simp [suspension]) (by simp [suspension]) (by simp [suspension]) (by simp [suspension]) (by simp [suspension])
      (by simp [suspension]) (by simp [suspension]) routes.foreign_free
    exact ⟨captured.transport (suspendRoots.worldTyped movedTyped).1 (.refl _) rfl (Nat.le_refl _),
      (started.suspensionExtension.trans keptTransfer.suspensionExtension).recorded⟩

theorem EffectStep.cancel_suspensions {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed)
    (step : EffectStep program before (some (.cancel id)) after) : after.SuspensionsWellFormed :=
  (step.cancel_suspension_storage valid).1

theorem EffectStep.last_suspensions {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.replay id true)) after) : after.SuspensionsWellFormed :=
  (step.last_suspension_storage valid typed).1

theorem EffectStep.copy_suspensions {program : Kernel.Program} {before after : State} {id : Identity}
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.replay id false)) after) : after.SuspensionsWellFormed :=
  (step.copy_suspension_storage valid typed).1

theorem EffectStep.create_suspensions {program : Kernel.Program} {before after : State} {id : Identity}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (valid : before.SuspensionsWellFormed) (typed : Typing.WorldTyped program before.world)
    (step : EffectStep program before (some (.suspend id)) after) : after.SuspensionsWellFormed :=
  (step.create_suspension_storage programValid inventory valid typed).1

end Execution
end Glorious.Language
