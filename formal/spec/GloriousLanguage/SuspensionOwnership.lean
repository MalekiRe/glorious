import GloriousLanguage.SuspensionPreservation

/-! Saved homes belong to actual captured cleanup roles. Restoration and
relocation put those homes under the frames really reinstalled by replay;
saved caller environments do not become owners merely by mentioning them. -/
namespace Glorious.Language

open Kernel

namespace Execution

/-- Scope return consumes the popped frame's ownership role. The yielding
context cannot substitute a different activation as the cleanup owner. -/
theorem LocalStep.scope_return_owned {program : Kernel.Program} {before after : State}
    {context outer : Context} {value : Address} {scope region : Identity} {rest : List Frame}
    {roots : List Identity} {next : Task}
    (step : LocalStep program before none after) (task : before.task = .yield context value)
    (frames : before.frames = .scope outer scope region :: rest)
    (cleanup : after.task = .cleanup context roots next) :
    ∀ id ∈ roots, ∃ root, after.world.roots.get id = some root ∧
      FrameOwns (.scope outer scope region) root := by
  cases step <;> simp_all
  rename_i selected _
  intro id member
  obtain ⟨root,found,_,owned,_⟩ := (selected.2 id).mp member
  exact ⟨root,found,owned⟩

theorem CapturedHome.frame {handler : InstalledHandler} {inner : List Frame} {home : Home}
    (owned : CapturedHome handler inner home) :
    ∃ frame ∈ inner ++ [.handler handler false], FrameOwnsHome frame home := by
  rcases owned with scope | ⟨frame,member,owned⟩
  · exact ⟨.handler handler false,List.mem_append_right _ (by simp),Or.inl scope⟩
  · exact ⟨frame,List.mem_append_left _ member,owned⟩

theorem Relocation.home_owned_activation {map : Relocation} {home : Home} {activation : Identity}
    (owned : HomeOwnedByActivation home activation) :
    HomeOwnedByActivation (map.home home) (map.activation activation) := by
  rcases owned with ⟨scope,rfl⟩ | ⟨scope,rfl⟩
  · exact Or.inl ⟨map.scope scope,rfl⟩
  · exact Or.inr ⟨map.scope scope,rfl⟩

theorem Relocation.home_owned_scope {map : Relocation} {home : Home} {activation scope : Identity}
    (owned : HomeOwnedByScope home activation scope) :
    HomeOwnedByScope (map.home home) (map.activation activation) (map.scope scope) := by
  rcases owned with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem Relocation.frame_owns_home {map : Relocation} {frame : Frame} {home : Home}
    (owned : FrameOwnsHome frame home) : FrameOwnsHome (map.frame frame) (map.home home) := by
  cases frame <;> simp only [FrameOwnsHome,Relocation.frame,Relocation.context,Relocation.installed] at owned ⊢
  all_goals first
    | exact owned.elim
    | exact map.home_owned_activation owned
    | exact map.home_owned_scope owned
    | (rcases owned with owned | ⟨owns,owned⟩
       · first | exact Or.inl (map.home_owned_activation owned) | exact Or.inl (map.home_owned_scope owned)
       · exact Or.inr ⟨owns,map.home_owned_activation owned⟩)

theorem Relocation.captured_home {map : Relocation} {handler : InstalledHandler}
    {inner : List Frame} {home : Home} (owned : CapturedHome handler inner home) :
    CapturedHome (map.installed handler) (inner.map map.frame) (map.home home) := by
  rcases owned with scope | ⟨frame,member,owned⟩
  · exact Or.inl (map.home_owned_scope scope)
  · exact Or.inr ⟨map.frame frame,List.mem_map.mpr ⟨frame,member,rfl⟩,map.frame_owns_home owned⟩

/-- The exact saved-home lookup, not merely its local/temporary shape,
authenticates the home of every restored inventory root. -/
theorem restoreRoots.captured_home {world : World} {suspension : Suspension} {id : Identity} {root : Root}
    (origin : suspension.CaptureOrigin) (member : id ∈ suspension.roots)
    (found : (restoreRoots world suspension.homes).roots.get id = some root) :
    CapturedHome suspension.handler suspension.frames root.home := by
  obtain ⟨home,saved⟩ := (origin.domain id).mpr member
  rw [restoreRoots.get] at found
  obtain ⟨original,_,same⟩ := Option.map_eq_some_iff.mp found
  have equal : home = root.home := by
    simpa only [saved,Option.getD_some] using congrArg Root.home same
  exact equal ▸ origin.ownedHomes id home saved

theorem CopiesSnapshot.captured_home {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {id : Identity} {original root : Root}
    (copied : CopiesSnapshot program before suspension map after) (well : before.world.WellFormed)
    (origin : suspension.CaptureOrigin) (member : id ∈ suspension.roots)
    (beforeAt : before.world.roots.get id = some original)
    (afterAt : after.world.roots.get (map.root id) = some root) :
    CapturedHome (map.installed suspension.handler) (suspension.frames.map map.frame) root.home := by
  obtain ⟨home,saved⟩ := (origin.domain id).mpr member
  have copiedAt := copied.relocation.copied_root (homes := suspension.homes) well beforeAt
    (by simpa only [copied.relocation.roots] using member)
  rw [copied.result] at afterAt
  have same := Option.some.inj (copiedAt.symm.trans afterAt)
  have equal : map.home home = root.home := by
    simpa only [Relocation.rootValue,saved,Option.getD_some] using congrArg Root.home same
  exact equal ▸ map.captured_home (origin.ownedHomes id home saved)

theorem CopiesSnapshot.inventory_owned {program : Kernel.Program} {before after : State}
    {suspension : Suspension} {map : Relocation} {id : Identity} {original : Root}
    (copied : CopiesSnapshot program before suspension map after) (well : before.world.WellFormed)
    (origin : suspension.CaptureOrigin) (member : id ∈ suspension.roots)
    (beforeAt : before.world.roots.get id = some original) :
    ∃ root, after.world.roots.get (map.root id) = some root ∧
      CapturedHome (map.installed suspension.handler) (suspension.frames.map map.frame) root.home := by
  have found := copied.relocation.copied_root (homes := suspension.homes) well beforeAt
    (by simpa only [copied.relocation.roots] using member)
  have found : after.world.roots.get (map.root id) =
      some (map.rootValue id { original with home := (suspension.homes.get id).getD original.home }) := by
    simpa only [copied.result] using found
  exact ⟨_,found,copied.captured_home well origin member beforeAt found⟩

theorem Protect.homeExtension {program : Kernel.Program} {context : Context} {before after : World}
    {source destination : Address} {authority : Authority}
    (kept : Protect program context before source authority destination after) : before.HomeExtension after :=
  kept.suspensionExtension.toHomeExtension

/-- A last replay returns each original inventory root to one of the
cleanup-owning frames it actually reinstalls, after the real argument move. -/
theorem EffectStep.last_replay_owned {program : Kernel.Program} {before after : State} {id : Identity}
    {suspension : Suspension} (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (selected : before.resumptions.get id = some suspension)
    (step : EffectStep program before (some (.replay id true)) after) :
    ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get rootId = some root ∧
      ∃ frame ∈ after.frames, FrameOwns frame root := by
  cases step with
  | resumeLast task found active remaining restored kept =>
    have same := Option.some.inj (selected.symm.trans found)
    subst suspension
    subst restored
    rename_i caller argument current keptAddress transferred
    intro rootId member
    obtain ⟨original,originalAt,_,_⟩ := (valid.active _ _ found active.1 rootId).mp member
    have restoredAt : (restoreRoots before.world current.homes).roots.get rootId =
        some { original with home := (current.homes.get rootId).getD original.home } := by
      rw [restoreRoots.get,originalAt]; rfl
    have home := restoreRoots.captured_home (valid.origin _ _ found) member restoredAt
    have homePreserved := kept.homeExtension.homes rootId (World.root_bound well originalAt)
    rw [restoredAt] at homePreserved
    obtain ⟨root,rootAt,homeEq⟩ := Option.map_eq_some_iff.mp homePreserved
    obtain ⟨frame,frameAt,owned⟩ := (homeEq.symm ▸ home).frame
    refine ⟨root,rootAt,frame,?_,owned⟩
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at frameAt ⊢
    rcases frameAt with member | same
    · exact Or.inl (Or.inl member)
    · exact Or.inl (Or.inr (Or.inl same))

/-- A copied replay obtains the same ownership result through the actual
finite relocation and protected argument transfer, with fresh root identities. -/
theorem EffectStep.copy_replay_owned {program : Kernel.Program} {before after : State} {id : Identity}
    {suspension : Suspension} (valid : before.SuspensionsWellFormed) (well : before.world.WellFormed)
    (selected : before.resumptions.get id = some suspension)
    (step : EffectStep program before (some (.replay id false)) after) :
    ∃ map : Relocation, map.roots = suspension.roots ∧ map.rootBase = before.world.nextRoot ∧
      ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get (map.root rootId) = some root ∧
        ∃ frame ∈ after.frames, FrameOwns frame root := by
  cases step with
  | resumeCopy task found active remaining copied kept =>
    have same := Option.some.inj (selected.symm.trans found)
    subst suspension
    rename_i caller argument current map cloned keptAddress transferred
    refine ⟨map,copied.relocation.roots,copied.relocation.rootBase,?_⟩
    intro rootId member
    obtain ⟨original,originalAt,_,_⟩ := (valid.active _ _ found active.1 rootId).mp member
    obtain ⟨copiedRoot,copiedRootAt,home⟩ := copied.inventory_owned well (valid.origin _ _ found) member originalAt
    have homePreserved := kept.homeExtension.homes (map.root rootId)
      (World.root_bound (copied.wellFormed well) copiedRootAt)
    rw [copiedRootAt] at homePreserved
    obtain ⟨root,rootAt,homeEq⟩ := Option.map_eq_some_iff.mp homePreserved
    obtain ⟨frame,frameAt,owned⟩ := (homeEq.symm ▸ home).frame
    refine ⟨root,rootAt,frame,?_,owned⟩
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at frameAt ⊢
    rcases frameAt with member | same
    · exact Or.inl (Or.inl member)
    · exact Or.inl (Or.inr (Or.inl same))

/-- Cancellation restores only the homes authenticated by its historical
capture; the scheduled inventory is the same inventory it just restored. -/
theorem EffectStep.cancel_restores_owned {program : Kernel.Program} {before after : State} {id : Identity}
    {suspension : Suspension} (valid : before.SuspensionsWellFormed)
    (selected : before.resumptions.get id = some suspension)
    (step : EffectStep program before (some (.cancel id)) after) :
    ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get rootId = some root ∧
      CapturedHome suspension.handler suspension.frames root.home := by
  cases step with
  | cancel task found active optional disposable =>
    have same := Option.some.inj (selected.symm.trans found)
    subst suspension
    rename_i context next current
    intro rootId member
    obtain ⟨original,originalAt,_,_⟩ := (valid.active _ _ found active.1 rootId).mp member
    have restoredAt : (restoreRoots before.world current.homes).roots.get rootId =
        some { original with home := (current.homes.get rootId).getD original.home } := by
      rw [restoreRoots.get,originalAt]; rfl
    exact ⟨_,restoredAt,restoreRoots.captured_home (valid.origin _ _ found) member restoredAt⟩

/-- Replay after arbitrary actual execution still reinstalls an owner for
each inventory root. The copied case exposes the actual fresh relocation;
neither case assumes a post-replay ownership judgment. -/
theorem Run.replay_owned {program : Kernel.Program} {host : Foreign.Model}
    {before current after : State} {trace : List Event} {id : Identity} {last : Bool}
    {suspension : Suspension}
    (programValid : ProgramWellFormed program.declarations) (inventory : Kernel.BodyInventory program)
    (lawful : host.Lawful program) (typed : Typing.WorldTyped program before.world)
    (control : before.ControlWellFormed) (run : Run program host before trace current)
    (selected : current.resumptions.get id = some suspension)
    (replay : EffectStep program current (some (.replay id last)) after) :
    (last = true ∧ ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get rootId = some root ∧
      ∃ frame ∈ after.frames, FrameOwns frame root) ∨
    (last = false ∧ ∃ map : Relocation,
      map.roots = suspension.roots ∧ map.rootBase = current.world.nextRoot ∧
      ∀ rootId ∈ suspension.roots, ∃ root, after.world.roots.get (map.root rootId) = some root ∧
        ∃ frame ∈ after.frames, FrameOwns frame root) := by
  have currentValid := run.suspensions programValid inventory lawful typed control.suspensions
  have currentWell := (run.worldTyped programValid inventory lawful typed).1
  cases last with
  | true => exact Or.inl ⟨rfl,replay.last_replay_owned currentValid currentWell selected⟩
  | false => exact Or.inr ⟨rfl,replay.copy_replay_owned currentValid currentWell selected⟩

end Execution
end Glorious.Language
