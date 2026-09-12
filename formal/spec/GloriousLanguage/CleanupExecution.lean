import GloriousLanguage.CleanupPreservation

/-! Actual execution of the machine's post-cancellation cleanup chain.

Cancellation hands the machine `cleanup context roots (CloseRegions regions
next)`. This module executes that chain with the real `cleanupRoot`,
`destroyVacant`, `retire`, `regionEnd` and `cleanupDone` rules and produces the
actual `Run` from the cancel step to the task the cancel scheduled, so
post-cancel cleanup is constructed rather than assumed. The residual readiness
it consumes is exact and named: each captured root is live, empty and endable in
the restored world, and each suspension region can end. Deriving that readiness
from the suspension admission — vacancy through the destructor chain, and ending
the suspension's own live loans first — belongs to the cleanup/suspension
boundary and is not assumed here. -/
namespace Glorious.Language.Execution

open Kernel

/-- Ending a region leaves the roots, loans and reservations of the world
unchanged, so every other region can still end. -/
theorem RegionCanEnd.of_regionEnd {before after : World} {closed region : Identity}
    (safe : RegionCanEnd before region) (ended : RegionEnds before closed after) :
    RegionCanEnd after region := by
  obtain ⟨homes,loans,reservations,packings⟩ := safe
  have same : after = { before with liveRegions := before.liveRegions.filter (· != closed) } := ended.2
  refine ⟨?_,?_,?_,?_⟩
  · intro id root found live
    exact homes id root (by simpa only [same] using found) live
  · intro id loan found live
    exact loans id loan (by simpa only [same] using found) live
  · intro id available found active
    exact reservations id available (by simpa only [same] using found) active
  · intro address value pack resident head
    exact packings address value pack (by simpa only [same,World.Resident] using resident) head

/-- Retiring storage only removes one root's liveness and its now-empty value,
so every region that could end before can still end. -/
theorem RegionCanEnd.of_retires {before after : World} {retired region : Identity}
    (safe : RegionCanEnd before region) (retirement : Retires before retired after) :
    RegionCanEnd after region := by
  obtain ⟨homes,loans,reservations,packings⟩ := safe
  have loansCopy := retirement
  have availabilityCopy := retirement
  have loansEq : after.loans = before.loans := by cases loansCopy; rfl
  have availabilityEq : after.availability = before.availability := by cases availabilityCopy; rfl
  refine ⟨?_,?_,?_,?_⟩
  · intro id root found live
    exact homes id root (retirement.live_root (other := id) (root := root) found live) live
  · intro id loan found live
    exact loans id loan (by simpa only [loansEq] using found) live
  · intro id available found active
    exact reservations id available (by simpa only [availabilityEq] using found) active
  · intro address value pack resident head
    exact packings address value pack
      ((retirement.resident (address := address) (value := value)).mp resident) head

/-- Cleanup segments compose along their actual traces. -/
theorem CleanupRun.append {program : Kernel.Program} {host : Foreign.Model}
    {before middle after : State} {first last : List Event}
    (left : CleanupRun program host before first middle) (right : CleanupRun program host middle last after) :
    CleanupRun program host before (first ++ last) after := by
  induction left with
  | refl => exact right
  | silent task step _ ih => exact .silent task step (ih right)
  | visible task step _ ih => exact .visible task step (ih right)

/-- One live, empty, endable captured root is actually retired, and the cleanup
task advances to the remaining roots on the retired world. -/
theorem CleanupRun.retire_vacant {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : Identity} {roots : List Identity} {next : Task} {root : Root}
    (task : before.task = .cleanup context (id :: roots) next)
    (found : before.world.roots.get id = some root) (live : root.live = true) (empty : root.value = none)
    (safe : CanEndStorage before.world id) :
    CleanupRun program host before [.retire id]
      ({ before with
        world := { before.world with
          roots := before.world.roots.set id ({ root with live := false, generation := root.generation + 1 }) }
        task := .cleanup context roots next }) := by
  have retired : Retires before.world id
      { before.world with
        roots := before.world.roots.set id ({ root with live := false, generation := root.generation + 1 }) } :=
    Retires.vacant found live empty safe
  have vacant : before.world.Vacant ⟨id,root.generation,[]⟩ :=
    ⟨root,by simp [World.root,found,live],Or.inl ⟨rfl,empty⟩⟩
  refine CleanupRun.silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.cleanupRoot task found live)) ?_
  refine CleanupRun.silent (by simp [Task.Cleanup]) (Or.inl (LocalStep.destroyVacant (by rfl) vacant)) ?_
  exact CleanupRun.visible (by simp [Task.Cleanup]) (Or.inl (LocalStep.retire (by rfl) retired)) CleanupRun.refl

/-- Every captured root is actually retired in order. Each later root's
readiness is read at the world the earlier retirements produced, where only the
retired root's own entry changed, and every region that could end before can
still end afterwards. -/
theorem CleanupRun.retire_all {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {roots : List Identity} {next : Task}
    (task : before.task = .cleanup context roots next) (nodup : roots.Nodup)
    (ready : ∀ id ∈ roots, ∃ root, before.world.roots.get id = some root ∧ root.live = true ∧
      root.value = none ∧ CanEndStorage before.world id) :
    ∃ (after : State) (trace : List Event),
      CleanupRun program host before trace after ∧ after.task = .cleanup context [] next ∧
      (∀ region, RegionCanEnd before.world region → RegionCanEnd after.world region) := by
  induction roots generalizing before with
  | nil => exact ⟨before,[],CleanupRun.refl,task,fun _ safe => safe⟩
  | cons id rest ih =>
    obtain ⟨root,found,live,empty,safe⟩ := ready id (by simp)
    have retirement : Retires before.world id
        { before.world with
          roots := before.world.roots.set id ({ root with live := false, generation := root.generation + 1 }) } :=
      Retires.vacant found live empty safe
    let rested : State :=
      { before with
        world := { before.world with
          roots := before.world.roots.set id ({ root with live := false, generation := root.generation + 1 }) }
        task := .cleanup context rest next }
    have step : CleanupRun program host before [.retire id] rested :=
      CleanupRun.retire_vacant (program := program) (host := host) (context := context)
        (id := id) (roots := rest) (next := next) task found live empty safe
    have restedTask : rested.task = .cleanup context rest next := by simp only [rested]
    have restNodup : rest.Nodup := (List.nodup_cons.mp nodup).2
    have restReady : ∀ other ∈ rest, ∃ current,
        (rested.world.roots).get other = some current ∧
        current.live = true ∧ current.value = none ∧ CanEndStorage rested.world other := by
      intro other member
      obtain ⟨otherRoot,otherFound,otherLive,otherEmpty,otherSafe⟩ := ready other (by simp [member])
      have different : other ≠ id := by
        intro same
        exact (List.nodup_cons.mp nodup).1 (same ▸ member)
      have kept : rested.world.roots.get other = before.world.roots.get other := by
        simp only [rested,Table.get_set_other _ _ _ _ different]
      refine ⟨otherRoot,?_,otherLive,otherEmpty,?_⟩
      · rw [kept]; exact otherFound
      · refine ⟨otherSafe.1,otherSafe.2.1,?_⟩
        intro observed rootFound suspension
        exact otherSafe.2.2 observed (by simpa only [kept] using rootFound) suspension
    obtain ⟨middle,trace,run,taskAfter,monotone⟩ := ih restedTask restNodup restReady
    exact ⟨middle,.retire id :: trace,step.append run,taskAfter,
      fun region safe' => monotone region (RegionCanEnd.of_retires safe' retirement)⟩

/-- The actual transition: the cancel rule runs, and the cleanup chain it
scheduled actually retires every captured root with the machine's own
`cleanupRoot`, `destroyVacant` and `retire` steps, leaving the suspension's
region closures and the scheduled continuation next. -/
theorem EffectStep.cancel_roots_execution {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : Identity} {next : Task} {suspension : Suspension}
    (task : before.task = .cancel context id next)
    (found : before.resumptions.get id = some suspension)
    (obligation : ActiveObligation suspension) (lowered : suspension.quantity.lower = 0)
    (cancelable : Cancelable program before.world suspension.roots)
    (rootNodup : suspension.roots.Nodup)
    (rootReady : ∀ root ∈ suspension.roots,
      ∃ alive, (restoreRoots before.world suspension.homes).roots.get root = some alive ∧
        alive.live = true ∧ alive.value = none ∧
        CanEndStorage (restoreRoots before.world suspension.homes) root) :
    ∃ (after : State) (trace : List Event), Run program host before trace after ∧
      after.task = .cleanup context [] (CloseRegions (SuspensionRegions suspension) next) := by
  let cancelledState : State :=
    { before with
      world := restoreRoots before.world suspension.homes
      task := .cleanup context suspension.roots (CloseRegions (SuspensionRegions suspension) next)
      resumptions := before.resumptions.set id { suspension with active := false, remaining := 0 } }
  have cancelled : EffectStep program before (some (.cancel id)) cancelledState :=
    EffectStep.cancel task found obligation lowered cancelable
  obtain ⟨middle,trace,execution,taskAfter,_⟩ :=
    CleanupRun.retire_all (before := cancelledState) (context := context) (roots := suspension.roots)
      (next := CloseRegions (SuspensionRegions suspension) next) (task := rfl) rootNodup rootReady
  exact ⟨middle,.cancel id :: trace,
    ⟨Run.visible (Or.inr (Or.inr (Or.inl cancelled))) (CleanupRun.run execution),taskAfter⟩⟩

/-- Every scheduled region is actually closed in order, on the fold the cancel
step built. -/
theorem CleanupRun.close_regions {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {regions : List Identity} {next : Task}
    (task : before.task = List.foldr Task.closeRegion next regions)
    (ready : ∀ region ∈ regions, ∃ after, RegionEnds before.world region after) :
    ∃ (after : State) (trace : List Event), CleanupRun program host before trace after ∧ after.task = next := by
  induction regions generalizing before with
  | nil => exact ⟨before,[],CleanupRun.refl,by simpa using task⟩
  | cons region rest ih =>
    obtain ⟨closed,ended⟩ := ready region (by simp)
    let restState : State := { before with world := closed, task := List.foldr Task.closeRegion next rest }
    have restTask : restState.task = List.foldr Task.closeRegion next rest := by simp only [restState]
    have restReady : ∀ other ∈ rest, ∃ after, RegionEnds closed other after := by
      intro other member
      obtain ⟨_,safe⟩ := ready other (by simp [member])
      exact ⟨{ closed with liveRegions := closed.liveRegions.filter (· != other) },
        RegionCanEnd.of_regionEnd safe.1 ended,rfl⟩
    obtain ⟨middle,trace,run,taskAfter⟩ := ih (before := restState) restTask restReady
    have step : Step program host before none restState :=
      Or.inl (LocalStep.regionEnd (by simpa using task) ended)
    exact ⟨middle,trace,CleanupRun.silent (by simp [Task.Cleanup,task]) step run,taskAfter⟩

/-- The whole post-cancel cleanup chain: the captured roots are retired, then the
suspension's regions are closed, reaching the task the cancel step scheduled. -/
theorem CleanupRun.cleanup_execution {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {roots regions : List Identity} {next : Task}
    (task : before.task = .cleanup context roots (CloseRegions regions next))
    (rootNodup : roots.Nodup)
    (rootReady : ∀ id ∈ roots, ∃ root, before.world.roots.get id = some root ∧ root.live = true ∧
      root.value = none ∧ CanEndStorage before.world id)
    (regionReady : ∀ region ∈ regions.eraseDups, ∃ after, RegionEnds before.world region after) :
    ∃ (after : State) (trace : List Event), CleanupRun program host before trace after ∧ after.task = next := by
  obtain ⟨middle,rootsTrace,retired,taskAfter,monotone⟩ := CleanupRun.retire_all task rootNodup rootReady
  let opened : State := { middle with task := List.foldr Task.closeRegion next regions.eraseDups }
  have openedTask : opened.task = List.foldr Task.closeRegion next regions.eraseDups := by simp only [opened]
  have unwrap : Step program host middle none opened :=
    Or.inl (LocalStep.cleanupDone (by simpa only [CloseRegions] using taskAfter))
  have regionReady' : ∀ region ∈ regions.eraseDups, ∃ after, RegionEnds opened.world region after := by
    intro region member
    obtain ⟨_,safe⟩ := regionReady region member
    exact ⟨{ middle.world with liveRegions := middle.world.liveRegions.filter (· != region) },
      monotone region safe.1,by simp only [opened]⟩
  obtain ⟨final,regionTrace,closed,taskFinal⟩ :=
    CleanupRun.close_regions (before := opened) openedTask regionReady'
  exact ⟨final,rootsTrace ++ regionTrace,
    retired.append (CleanupRun.silent (by simp [Task.Cleanup,taskAfter]) unwrap closed),taskFinal⟩

end Glorious.Language.Execution
