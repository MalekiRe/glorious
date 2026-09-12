import GloriousLanguage.CleanupDestruction
import GloriousLanguage.ForeignRootFraming
import GloriousLanguage.InvocationLeaseCleanup

/-! Execution of the general destructor continuation: the pending-return list a
relinquished shell schedules and the fixpoint its parent/guard retries reach.

`shellDone` and every other relinquishment hand the machine
`ReleaseCustodyLoans world custody next`, a queue of the live storage-borrow
loans that asked for their storage back. Each `releaseLoan` step either consumes
its head silently or ends that loan and *retries* the recorded dependencies
(the parent and the invariant carriers) in front of the remaining queue. The
drain below runs exactly those `LocalStep` rules to the fixpoint, under the
world invariant the rules actually read: every live loan is an owning claim or
a storage borrow, every queue entry has a row, and the parent/guard rows exist.
The measure is the pair (live loans, queue length): a silent step shortens the
queue and an ending step strictly reduces the live-loan count, so the retry
fixpoint cannot grow forever.

Nothing here re-implements a release algorithm: `LocalStep.releaseReferenced`,
`releaseResourceHeld`, `releaseBorrowed`, `releaseOwnedClaim`,
`releaseStorageRetained`, `releaseStorageReturned` and `releaseAlreadyEnded` are
selected, not replaced, and the world each of them produces is the one reported. -/
namespace Glorious.Language

open Kernel

/-- The raw release queue: the fold the machine's `ReleaseLoans` performs, before
`eraseDups`. Stating the drain on the raw fold keeps each `releaseLoan` head
literal, so the successor task of every actual rule instance is the queue's own
tail. -/
def ReleaseQueue (identities : List Identity) (next : Execution.Task) : Execution.Task :=
  identities.foldr Execution.Task.releaseLoan next

theorem ReleaseQueue_nil (next : Execution.Task) : ReleaseQueue [] next = next := rfl

theorem ReleaseQueue_cons (identity : Identity) (rest : List Identity) (next : Execution.Task) :
    ReleaseQueue (identity :: rest) next =
      Execution.Task.releaseLoan identity (ReleaseQueue rest next) := rfl

/-- The queue is the fold, so draining a pushed prefix and then the remainder
is the same task as draining their concatenation. -/
theorem ReleaseQueue_append (first second : List Identity) (next : Execution.Task) :
    ReleaseQueue first (ReleaseQueue second next) = ReleaseQueue (first ++ second) next := by
  induction first with
  | nil => rfl
  | cons id rest ih => simp only [ReleaseQueue_cons,List.cons_append,ih]

/-- The machine's own release task is the raw queue of the deduplicated list. -/
theorem ReleaseLoans_eq_queue (identities : List Identity) (next : Execution.Task) :
    Execution.ReleaseLoans identities next = ReleaseQueue identities.eraseDups next := rfl

/-- The number of live loans, as the recursive count of live rows. Every ending
step below strictly reduces it. -/
def Table.liveCount : Table Loan → Nat
  | [] => 0
  | (_,loan) :: rest => (if loan.live then 1 else 0) + Table.liveCount rest

def World.liveCount (world : World) : Nat := Table.liveCount world.loans

theorem Table.liveCount_le_length (table : Table Loan) : Table.liveCount table ≤ table.length := by
  induction table with
  | nil => simp [Table.liveCount]
  | cons entry rest ih =>
    rcases entry with ⟨key,loan⟩
    simp only [Table.liveCount,List.length_cons]
    split <;> omega

/-- Erasing one identity never adds a live loan. -/
theorem Table.liveCount_erase_le (table : Table Loan) (id : Identity) :
    Table.liveCount (Table.erase table id) ≤ Table.liveCount table := by
  induction table with
  | nil => simp [Table.erase,Table.liveCount]
  | cons entry rest ih =>
    rcases entry with ⟨key,loan⟩
    by_cases same : key = id
    · subst same
      have erased : Table.erase ((key,loan) :: rest) key = Table.erase rest key := by
        simp [Table.erase]
      rw [erased]
      simp only [Table.liveCount]
      split <;> omega
    · have kept : Table.erase ((key,loan) :: rest) id = (key,loan) :: Table.erase rest id := by
        simp [Table.erase,same]
      rw [kept]
      simp only [Table.liveCount]
      split <;> omega

/-- Replacing one live row by a dead one strictly reduces the live-loan count. -/
theorem Table.liveCount_set_dead {table : Table Loan} {id : Identity} {loan : Loan}
    (found : table.get id = some loan) (live : loan.live = true) :
    Table.liveCount (Table.set table id { loan with live := false }) < Table.liveCount table := by
  induction table generalizing id loan live with
  | nil => simp [Table.get] at found
  | cons entry rest ih =>
    rcases entry with ⟨key,current⟩
    by_cases same : key = id
    · have idEq : id = key := same.symm
      subst id
      have valueEq : current = loan := by simpa [Table.get] using found
      subst current
      have erased : Table.erase ((key,loan) :: rest) key = Table.erase rest key := by
        simp [Table.erase]
      have bounded := Table.liveCount_erase_le rest key
      simp only [Table.set,erased,Table.liveCount,live,Bool.false_eq_true,if_false,if_true]
      omega
    · have later : Table.get rest id = some loan := by simpa [Table.get,same] using found
      have kept : Table.erase ((key,current) :: rest) id = (key,current) :: Table.erase rest id := by
        simp [Table.erase,same]
      have step := ih later live
      rw [Table.set,kept]
      simp only [Table.set,Table.liveCount,Bool.false_eq_true,if_false] at step ⊢
      omega

theorem World.liveCount_set_dead {world : World} {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) (live : loan.live = true) :
    ({ world with loans := world.loans.set id { loan with live := false } }).liveCount <
      world.liveCount :=
  Table.liveCount_set_dead found live


/-- The world invariant the machine's own `releaseLoan` rules read. Every queue
entry names an existing row (or is already a plain reference/resource handle),
every live loan is an owning claim or a storage borrow, and the parent/guard
rows a retry re-inserts exist. All three are preserved by an ending step. -/
structure World.ReleaseReady (world : World) (identities : List Identity) : Prop where
  rows : ∀ id ∈ identities, world.loans.get id ≠ none ∨
    world.References id ∨ world.ResourceReferences id
  kinds : ∀ id loan, world.loans.get id = some loan → loan.live = true →
    loan.kind = .owning ∨ loan.kind = .storageBorrow
  ancestry : ∀ id loan, world.loans.get id = some loan →
    (∀ parent, loan.parent = some parent → world.loans.get parent ≠ none) ∧
    (∀ guard ∈ loan.guards, world.loans.get guard ≠ none)

theorem World.ReleaseReady.tail {world : World} {id : Identity} {rest : List Identity}
    (ready : world.ReleaseReady (id :: rest)) : world.ReleaseReady rest where
  rows := fun other member => ready.rows other (List.mem_cons_of_mem _ member)
  kinds := ready.kinds
  ancestry := ready.ancestry

/-- An ending step keeps the row (dead) and leaves every other row's parent and
guard fields untouched, so the retry list stays inside the loan table. -/
theorem World.ReleaseReady.afterEnd {world : World} {id : Identity} {loan : Loan} {identities : List Identity}
    (ready : world.ReleaseReady identities) (found : world.loans.get id = some loan) :
    ({ world with loans := world.loans.set id { loan with live := false } }).ReleaseReady identities where
  rows := by
    intro other member
    rcases ready.rows other member with held | fallback
    · refine Or.inl ?_
      by_cases same : other = id
      · subst other; exact fun missing => by simp [Table.get_set] at missing
      · simpa only [Table.get_set_other _ _ _ _ same] using held
    · rcases fallback with referenced | resourced
      · exact Or.inr (Or.inl referenced)
      · exact Or.inr (Or.inr resourced)
  kinds := by
    intro other row selected live
    by_cases same : other = id
    · subst other
      have equal : ({ loan with live := false } : Loan) = row :=
        Option.some.inj ((Table.get_set _ _ _).symm.trans selected)
      exact absurd (equal ▸ rfl : row.live = false) (by simp [live])
    · have rowEq : world.loans.get other = some row := by
        simpa only [Table.get_set_other _ _ _ _ same] using selected
      exact ready.kinds other row rowEq live
  ancestry := by
    intro other row selected
    by_cases same : other = id
    · subst other
      have equal : ({ loan with live := false } : Loan) = row :=
        Option.some.inj ((Table.get_set _ _ _).symm.trans selected)
      subst equal
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · rcases (ready.ancestry id loan found).1 parent link with missing
        by_cases parentIs : parent = id
        · subst parent; exact fun gone => by simp [Table.get_set] at gone
        · simpa only [Table.get_set_other _ _ _ _ parentIs] using missing
      · rcases (ready.ancestry id loan found).2 guard member with missing
        by_cases guardIs : guard = id
        · subst guard; exact fun gone => by simp [Table.get_set] at gone
        · simpa only [Table.get_set_other _ _ _ _ guardIs] using missing
    · have rowEq : world.loans.get other = some row := by
        simpa only [Table.get_set_other _ _ _ _ same] using selected
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · rcases (ready.ancestry other row rowEq).1 parent link with missing
        by_cases parentIs : parent = id
        · subst parent; exact fun gone => by simp [Table.get_set] at gone
        · simpa only [Table.get_set_other _ _ _ _ parentIs] using missing
      · rcases (ready.ancestry other row rowEq).2 guard member with missing
        by_cases guardIs : guard = id
        · subst guard; exact fun gone => by simp [Table.get_set] at gone
        · simpa only [Table.get_set_other _ _ _ _ guardIs] using missing


/-- The retry list a storage-return step re-inserts: its parent and guard rows
exist, so the successor world's queue is still inside the loan table. -/
theorem World.ReleaseReady.retry {world : World} {id : Identity} {loan : Loan} {identities : List Identity}
    (ready : world.ReleaseReady identities) (found : world.loans.get id = some loan) :
    ({ world with loans := world.loans.set id { loan with live := false } }).ReleaseReady
      (loan.parent.toList ++ loan.guards).eraseDups where
  rows := by
    intro other member
    have member' := List.mem_eraseDups.mp member
    have held : world.loans.get other ≠ none := by
      rcases List.mem_append.mp member' with inParent | inGuards
      · cases parent : loan.parent with
        | none => simp [parent] at inParent
        | some value =>
          have equal : other = value := by simpa [parent] using inParent
          subst other
          exact (ready.ancestry id loan found).1 value parent
      · exact (ready.ancestry id loan found).2 other inGuards
    refine Or.inl ?_
    by_cases same : other = id
    · subst other; exact fun missing => by simp [Table.get_set] at missing
    · simpa only [Table.get_set_other _ _ _ _ same] using held
  kinds := (ready.afterEnd (id := id) (loan := loan) found).kinds
  ancestry := (ready.afterEnd (id := id) (loan := loan) found).ancestry


/-- One ending step only turns a live row into a dead one. -/
theorem World.loanReleaseFrame_set_dead {world : World} {id : Identity} {loan : Loan}
    (_found : world.loans.get id = some loan) :
    world.LoanReleaseFrame { world with loans := world.loans.set id { loan with live := false } } := by
  refine ⟨rfl,fun other row selected live => ?_⟩
  by_cases same : other = id
  · subst other
    have equal : ({ loan with live := false } : Loan) = row :=
      Option.some.inj ((Table.get_set _ _ _).symm.trans selected)
    exact absurd (equal ▸ rfl : row.live = false) (by simp [live])
  · simpa only [Table.get_set_other _ _ _ _ same] using selected


/-- A table entry for an identity makes that identity readable. -/
theorem Table.get_isSome_of_mem {α : Type} {table : Table α} {id : Identity} {value : α}
    (member : (id,value) ∈ table) : (table.get id).isSome := by
  have found : (table.find? (fun entry => entry.1 == id)).isSome = true :=
    List.find?_isSome.mpr ⟨(id,value),member,by simp⟩
  simpa [Table.get] using found

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Marking pending returns restamps only `returnRequested`: it changes neither a
loan's referent nor its liveness, so a retirable root stays retirable across the
relinquishment that precedes the shell write. -/
theorem World.RootClear.of_requestReturns {world : World} {custody : ClaimCustody} {rootId : Identity}
    (clear : world.RootClear rootId) : (world.RequestReturns custody).RootClear rootId := by
  refine ⟨?_,?_,?_⟩
  · intro id loan found live
    have canonical : Table.get (List.map (fun entry : Identity × Loan =>
        (entry.1, (fun current : Loan => if current.custody = some custody ∧ current.kind = .storageBorrow then
          { current with returnRequested := true } else current) entry.2)) world.loans) id = some loan := by
      show Table.get (world.RequestReturns custody).loans id = some loan
      exact found
    rw [Table.get_map_values world.loans (fun current : Loan =>
      if current.custody = some custody ∧ current.kind = .storageBorrow then
        { current with returnRequested := true } else current) id] at canonical
    obtain ⟨original,selected,shape⟩ := Option.map_eq_some_iff.mp canonical
    rw [← shape]
    have referent : (if original.custody = some custody ∧ original.kind = .storageBorrow then
        { original with returnRequested := true } else original).referent = original.referent := by
      by_cases chosen : original.custody = some custody ∧ original.kind = .storageBorrow <;> simp [chosen]
    have liveOriginal : original.live = true := by
      by_cases chosen : original.custody = some custody ∧ original.kind = .storageBorrow <;>
        simpa [chosen,← shape] using live
    rw [referent]
    exact clear.loans id original selected liveOriginal
  · intro id available found active
    exact clear.reservations id available found active
  · intro other otherFound suspension
    exact clear.home other otherFound suspension

end Glorious.Language

namespace Glorious.Language.Execution

/-- The pending-return queue drains to the task the relinquishment scheduled.
Every step is one of the machine's own `releaseLoan` rules: a silent rule
consumes its head, an ending rule ends the loan and re-inserts the recorded
parent and guard dependencies in front of the remaining queue. The measure is
the lexicographic pair (live loans, queue length): silent steps shorten the
queue, ending steps strictly reduce the live-loan count, so the retry fixpoint
is well founded and every dependency actually gets its second chance. -/
theorem CleanupRun.release_queue {program : Kernel.Program} {host : Foreign.Model} (bound : Nat) :
    ∀ (next : Task) (before : State) (identities : List Identity),
      before.world.liveCount ≤ bound →
      before.task = ReleaseQueue identities next →
      before.world.ReleaseReady identities →
      ∃ (after : State) (trace : List Event),
        CleanupRun program host before trace after ∧ after.task = next ∧
          after.world.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after.world := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro next before identities boundLe task ready
    induction identities generalizing before next with
    | nil =>
      exact ⟨before,[],CleanupRun.refl,by simpa [ReleaseQueue] using task,Nat.le_refl _,World.LoanReleaseFrame.refl _⟩
    | cons id rest listIh =>
      have head : before.task = Task.releaseLoan id (ReleaseQueue rest next) :=
        task.trans (ReleaseQueue_cons id rest next)
      have cleanup : before.task.Cleanup := by simp [Task.Cleanup,head]
      have tailReady := ready.tail (id := id)
      have silent (step : LocalStep program before none { before with task := ReleaseQueue rest next }) :
          ∃ (after : State) (trace : List Event),
            CleanupRun program host before trace after ∧ after.task = next ∧
              after.world.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after.world := by
        obtain ⟨after,trace,run,goal,counted,frame⟩ :=
          listIh (before := { before with task := ReleaseQueue rest next }) (next := next) boundLe rfl tailReady
        exact ⟨after,trace,CleanupRun.silent (before := before) (by simp [Task.Cleanup,head]) (Or.inl step) run,
          goal,counted,frame⟩
      cases found : before.world.loans.get id with
      | none =>
        have fallback : before.world.References id ∨ before.world.ResourceReferences id := by
          rcases ready.rows id (by simp) with missing | later
          · exact absurd found missing
          · exact later
        rcases fallback with referenced | resourced
        · exact silent (.releaseReferenced head referenced)
        · exact silent (.releaseResourceHeld head resourced)
      | some loan =>
        by_cases live : loan.live = true
        · rcases ready.kinds id loan found live with owning | borrowed
          · exact silent (.releaseOwnedClaim head found owning)
          · by_cases referenced : before.world.References id
            · exact silent (.releaseReferenced head referenced)
            · by_cases resourced : before.world.ResourceReferences id
              · exact silent (.releaseResourceHeld head resourced)
              · by_cases dependent : ∃ child, before.world.loans.get child.identity = some child ∧
                    (child.parent = some id ∨ id ∈ child.guards) ∧ child.live = true
                · obtain ⟨child,selected,related,active⟩ := dependent
                  exact silent (.releaseBorrowed head referenced selected related active)
                · have children : ∀ child, before.world.loans.get child.identity = some child →
                      (child.parent = some id ∨ id ∈ child.guards) → child.live = false := by
                    intro child selected related
                    cases active : child.live with
                    | false => rfl
                    | true => exact absurd ⟨child,selected,related,active⟩ dependent
                  by_cases requested : loan.returnRequested = true
                  · have free := World.referenceFree_iff.mpr ⟨referenced,resourced⟩
                    let afterWorld : World := { before.world with loans := before.world.loans.set id { loan with live := false } }
                    let pushed : List Identity := loan.parent.toList ++ loan.guards
                    let afterState : State := { before with world := afterWorld, task := ReleaseLoans pushed (ReleaseQueue rest next) }
                    have returned := ReturnsStorageLoan.of_referenceFree found live borrowed requested free children
                    have step : LocalStep program before (some (.loanEnd id)) afterState :=
                      .releaseStorageReturned head found returned
                    have decreased : afterWorld.liveCount < before.world.liveCount :=
                      World.liveCount_set_dead found live
                    have taskEq : afterState.task = ReleaseQueue (pushed.eraseDups ++ rest) next :=
                      (ReleaseLoans_eq_queue pushed (ReleaseQueue rest next)).trans
                        (ReleaseQueue_append pushed.eraseDups rest next)
                    have afterReady : afterWorld.ReleaseReady (pushed.eraseDups ++ rest) :=
                      { rows := by
                          intro other member
                          rcases List.mem_append.mp member with inPushed | inRest
                          · exact (ready.retry (id := id) (loan := loan) found).rows other inPushed
                          · exact (ready.afterEnd (id := id) (loan := loan) found).tail.rows other inRest
                        kinds := (ready.afterEnd (id := id) (loan := loan) found).kinds
                        ancestry := (ready.afterEnd (id := id) (loan := loan) found).ancestry }
                    obtain ⟨after,trace,run,goal,counted,frame⟩ :=
                      ih afterWorld.liveCount (Nat.lt_of_lt_of_le decreased boundLe) next afterState
                        (pushed.eraseDups ++ rest) (Nat.le_refl _) taskEq afterReady
                    exact ⟨after,.loanEnd id :: trace,
                      CleanupRun.visible (before := before) cleanup (Or.inl step) run,goal,
                      Nat.le_trans counted (Nat.le_of_lt decreased),
                      (World.loanReleaseFrame_set_dead found).trans frame⟩
                  · have retained : loan.returnRequested = false := by
                      cases held : loan.returnRequested with
                      | false => rfl
                      | true => exact absurd held requested
                    exact silent (.releaseStorageRetained head found borrowed retained)
        · have dead : loan.live = false := by
            cases active : loan.live with
            | false => rfl
            | true => exact absurd active live
          exact silent (.releaseAlreadyEnded head found dead)

end Glorious.Language.Execution

namespace Glorious.Language.Execution

/-- The pending-return list `shellDone` schedules drains to the task the
relinquishment preserved: the queue is read off the real loan table, every
entry names a row, and the parent/guard retries stay inside the table. -/
theorem CleanupRun.release_custody_returns {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {custody : ClaimCustody} {next : Task}
    (task : before.task = ReleaseCustodyLoans before.world custody next)
    (kinds : ∀ id loan, before.world.loans.get id = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow)
    (ancestry : ∀ id loan, before.world.loans.get id = some loan →
      (∀ parent, loan.parent = some parent → before.world.loans.get parent ≠ none) ∧
      (∀ guard ∈ loan.guards, before.world.loans.get guard ≠ none)) :
    ∃ (after : State) (trace : List Event),
      CleanupRun program host before trace after ∧ after.task = next ∧
        before.world.LoanReleaseFrame after.world := by
  let identities := before.world.loans.filterMap fun (identity,loan) =>
    if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
      some identity else none
  obtain ⟨after,trace,run,goal,_,frame⟩ :=
    CleanupRun.release_queue (program := program) (host := host) before.world.liveCount next before identities.eraseDups
      (Nat.le_refl _) (task.trans (ReleaseLoans_eq_queue identities next))
      { rows := by
          intro id member
          refine Or.inl ?_
          obtain ⟨entry,present,selected⟩ := List.mem_filterMap.mp (List.mem_eraseDups.mp member)
          rcases entry with ⟨key,loan⟩
          by_cases condition : loan.live && loan.kind == .storageBorrow && loan.returnRequested &&
              loan.custody == some custody
          · simp only [condition,if_true,Option.some.injEq] at selected
            subst selected
            exact fun missing => by
              have readable := Table.get_isSome_of_mem present
              simp [missing] at readable
          · have impossible : (Option.none : Option Identity) = some id := by
              simpa only [condition,Bool.false_eq_true,if_false] using selected
            exact absurd impossible (by simp)
        kinds := kinds
        ancestry := ancestry }
  exact ⟨after,trace,run,goal,frame⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

/-- The whole non-vacant cleanup chain of one captured root, to the actual
retirement of that root: the captured shell is destroyed field by field, its
resident owner's custody is relinquished, the pending returns the relinquishment
schedules are drained to the retirement task by the machine's own `releaseLoan`
rules, and the cleared root is actually retired, leaving the remaining captured
roots next. `World.RootClear` supplies the retirement's endability, which the
drain's release frame transports to the drained world. -/
theorem CleanupRun.cleanup_root_shell_retired {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : Identity} {roots : List Identity} {next : Task}
    {root : Root} {value : Value} {cleared : World}
    (task : before.task = .cleanup context (id :: roots) next)
    (found : before.world.roots.get id = some root) (live : root.live = true)
    (stored : before.world.Stores ⟨id,root.generation,[]⟩ value)
    (disposable : MayDispose program.declarations value)
    (shell : value.shellLive = false ∨ DropHook program.declarations value.type none)
    (noContinuation : ∀ inner, value.head ≠ .continuation inner)
    (noReference : ∀ inner, value.head ≠ .reference inner)
    (noAvailable : ∀ inner, value.head ≠ .available inner)
    (holes : ∀ index, index < value.fields.length → value.fields[index]? = some none)
    (clear : before.world.RootClear id)
    (handed : before.world.CustodyHandedOff (.resident value.owner))
    (written : (before.world.RequestReturns (.resident value.owner)).write ⟨id,root.generation,[]⟩ none = some cleared)
    (clearedRoot : cleared.roots.get id = some { root with value := none })
    (kinds : ∀ lid loan, cleared.loans.get lid = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow)
    (ancestry : ∀ lid loan, cleared.loans.get lid = some loan →
      (∀ parent, loan.parent = some parent → cleared.loans.get parent ≠ none) ∧
      (∀ guard ∈ loan.guards, cleared.loans.get guard ≠ none)) :
    ∃ (after : State) (trace : List Event),
      CleanupRun program host before trace after ∧ after.task = .cleanup context roots next ∧
        (∃ retired, after.world.roots.get id = some retired ∧ retired.live = false) := by
  have shellRun := CleanupRun.cleanup_root_shell (host := host) task found live stored disposable shell
    noContinuation noReference noAvailable holes clear handed written
  obtain ⟨released,trace,drained,goal,frame⟩ :=
    CleanupRun.release_custody_returns
      (before := { before with world := cleared, task := ReleaseCustodyLoans cleared (.resident value.owner) (.retire id (.cleanup context roots next)) })
      rfl kinds ancestry
  have releasedRoot : released.world.roots.get id = some { root with value := none } := by
    rw [congrArg World.roots frame.1]
    exact clearedRoot
  have safe : CanEndStorage released.world id :=
    frame.canEndStorage ((clear.of_requestReturns (custody := .resident value.owner)).of_write written).canEndStorage
  let retiredWorld : World := { released.world with
    roots := released.world.roots.set id { root with value := none, live := false, generation := root.generation + 1 } }
  have retired : Retires released.world id retiredWorld :=
    Retires.vacant releasedRoot (by simpa using live) rfl safe
  have step : LocalStep program released (some (.retire id))
      { released with world := retiredWorld, task := .cleanup context roots next } := .retire goal retired
  refine ⟨{ released with world := retiredWorld, task := .cleanup context roots next },
    [.destroy ⟨id,root.generation,[]⟩ value.owner] ++ (trace ++ [.retire id]), ?_, rfl, ?_⟩
  · exact shellRun.append (drained.append (.visible (by simp [Task.Cleanup,goal]) (Or.inl step) .refl))
  · exact ⟨{ root with value := none, live := false, generation := root.generation + 1 },
      Table.get_set released.world.roots id { root with value := none, live := false, generation := root.generation + 1 }, rfl⟩

end Glorious.Language.Execution

namespace Glorious.Language

open Kernel

/-- The recursive destructor's tree inventory: a stored disposable shell (no
pending drop hook, no continuation/reference/available head, owning permission at
its own address, and the pending-return readiness the drain reads for the custody
its relinquishment marks) whose fields are each either a hole or a further
destructible resident. -/
inductive World.Destroys (program : RuntimeProgram) (world : World) : Address → Prop where
  | resident {address value} : world.Stores address value →
      MayDispose program.declarations value → value.shellLive = false →
      (∀ inner, value.head ≠ .continuation inner) → (∀ inner, value.head ≠ .reference inner) →
      (∀ inner, value.head ≠ .available inner) →
      Permitted world .owner .owned address →
      (∀ id loan, (world.RequestReturns (.resident value.owner)).loans.get id = some loan →
        loan.live = true → loan.kind = .owning ∨ loan.kind = .storageBorrow) →
      (∀ id loan, (world.RequestReturns (.resident value.owner)).loans.get id = some loan →
        (∀ parent, loan.parent = some parent →
          (world.RequestReturns (.resident value.owner)).loans.get parent ≠ none) ∧
        (∀ guard ∈ loan.guards, (world.RequestReturns (.resident value.owner)).loans.get guard ≠ none)) →
      (∀ (index : Nat) (child : Value), value.fields[index]? = some (some child) →
        World.Destroys program world (address.child index)) →
      World.Destroys program world address

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A write that is apart from a destructible resident leaves that resident
destructible: its stored shell, its owning permission, its custody's
pending-return readiness (the loan table is untouched by a write) and its
children (each apart from the write by the prefix law) all survive. -/
theorem World.Destroys.write_disjoint {program : RuntimeProgram} {world : World} {address : Address}
    (tree : World.Destroys program world address) {target : Address} {replacement : Option Value} {after : World}
    (written : world.write target replacement = some after)
    (deep : ∀ probe, address.Prefix probe → ¬ target.Overlaps probe) :
    World.Destroys program after address := by
  revert deep
  induction tree with
  | @resident address value stored disposable shell noCont noRef noAvail permission kinds ancestry children ih =>
    intro deep
    have framed := World.write_disjoint written (deep address ⟨rfl,rfl,⟨[],by simp⟩⟩)
    have storedAfter : after.Stores address value := by
      simpa only [World.Stores,framed] using stored
    have loansAfter : after.loans = world.loans := by rw [World.write_rest written]
    have located : ∃ root, after.root address = some root :=
      (Option.bind_eq_some_iff.mp storedAfter).imp fun _ found => found.1
    have permissionAfter : Permitted after .owner .owned address :=
      ⟨located,fun id loan found live overlap conflict =>
        permission.2 id loan (by simpa only [loansAfter] using found) live overlap conflict⟩
    refine .resident storedAfter disposable shell noCont noRef noAvail permissionAfter ?_ ?_ ?_
    · intro id loan found live
      have previous : (world.RequestReturns (.resident value.owner)).loans.get id = some loan := by
        simpa only [World.RequestReturns,loansAfter] using found
      exact kinds id loan previous live
    · intro id loan found
      have previous : (world.RequestReturns (.resident value.owner)).loans.get id = some loan := by
        simpa only [World.RequestReturns,loansAfter] using found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have held := (ancestry id loan previous).1 parent link
        simpa only [World.RequestReturns,loansAfter] using held
      · have held := (ancestry id loan previous).2 guard member
        simpa only [World.RequestReturns,loansAfter] using held
    · intro index child selected
      exact ih index child selected
        (fun probe included => deep probe (Address.Prefix.trans (Address.Prefix.child ⟨rfl,rfl,⟨[],by simp⟩⟩ index).1 included))

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- The restamping one row receives when its custody relinquishes pending
returns: `returnRequested` is set exactly for the storage borrows of that custody
and every other field is untouched. -/
def World.restamp (custody : ClaimCustody) (loan : Loan) : Loan :=
  if loan.custody = some custody ∧ loan.kind = .storageBorrow then
    { loan with returnRequested := true } else loan

theorem World.RequestReturns.loans_eq (world : World) (custody : ClaimCustody) :
    (world.RequestReturns custody).loans = world.loans.map (fun entry => (entry.1,World.restamp custody entry.2)) :=
  rfl

theorem World.RequestReturns.get_eq (world : World) (custody : ClaimCustody) (key : Identity) :
    (world.RequestReturns custody).loans.get key = (world.loans.get key).map (World.restamp custody) := by
  rw [World.RequestReturns.loans_eq,Table.get_map_values]

theorem World.restamp_live (custody : ClaimCustody) (loan : Loan) :
    (World.restamp custody loan).live = loan.live := by
  unfold World.restamp
  by_cases chosen : loan.custody = some custody ∧ loan.kind = .storageBorrow <;> simp [chosen]

theorem World.restamp_kind (custody : ClaimCustody) (loan : Loan) :
    (World.restamp custody loan).kind = loan.kind := by
  unfold World.restamp
  by_cases chosen : loan.custody = some custody ∧ loan.kind = .storageBorrow <;> simp [chosen]

theorem World.restamp_referent (custody : ClaimCustody) (loan : Loan) :
    (World.restamp custody loan).referent = loan.referent := by
  unfold World.restamp
  by_cases chosen : loan.custody = some custody ∧ loan.kind = .storageBorrow <;> simp [chosen]

theorem World.restamp_parent (custody : ClaimCustody) (loan : Loan) :
    (World.restamp custody loan).parent = loan.parent := by
  unfold World.restamp
  by_cases chosen : loan.custody = some custody ∧ loan.kind = .storageBorrow <;> simp [chosen]

theorem World.restamp_guards (custody : ClaimCustody) (loan : Loan) :
    (World.restamp custody loan).guards = loan.guards := by
  unfold World.restamp
  by_cases chosen : loan.custody = some custody ∧ loan.kind = .storageBorrow <;> simp [chosen]

/-- Ending one row cannot turn the relinquished table's entry at another
identity into a row: the restamping map preserves `none`. -/
theorem World.RequestReturns.frame_set_none {world : World} {custody : ClaimCustody} {id : Identity} {dead : Loan}
    (_deadFound : world.loans.get id = some dead) {key : Identity}
    (missing : (({ world with loans := world.loans.set id { dead with live := false } }
      ).RequestReturns custody).loans.get key = none) :
    (world.RequestReturns custody).loans.get key = none := by
  have canonical : Table.get (List.map (fun entry : Identity × Loan => (entry.1,World.restamp custody entry.2))
      ({ world with loans := world.loans.set id { dead with live := false } }.loans)) key = none := by
    show (({ world with loans := world.loans.set id { dead with live := false } }
      ).RequestReturns custody).loans.get key = none
    exact missing
  rw [Table.get_map_values] at canonical
  have afterTable : Table.get (Table.set world.loans id { dead with live := false }) key = none :=
    Option.map_eq_none_iff.mp canonical
  by_cases same : key = id
  · subst key
    rw [Table.get_set] at afterTable
    cases afterTable
  · rw [Table.get_set_other _ _ _ _ same] at afterTable
    rw [World.RequestReturns.get_eq,afterTable]
    rfl

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- The relinquishment map and an ending row commute: every other row is
untouched, and at the ended identity the restamping decision reads only the
custody and the kind, neither of which an ending changes. -/
theorem World.RequestReturns.frame_set {world : World} {custody : ClaimCustody} {id : Identity} {dead : Loan}
    (deadFound : world.loans.get id = some dead) {key : Identity} {row : Loan}
    (found : (({ world with loans := world.loans.set id { dead with live := false } }
      ).RequestReturns custody).loans.get key = some row) :
    ∃ previous, (world.RequestReturns custody).loans.get key = some previous ∧
      previous.kind = row.kind ∧ previous.referent = row.referent ∧ previous.parent = row.parent ∧
      previous.guards = row.guards ∧ (row.live = true → previous.live = true) := by
  have canonical : Table.get (List.map (fun entry : Identity × Loan => (entry.1,World.restamp custody entry.2))
      ({ world with loans := world.loans.set id { dead with live := false } }.loans)) key = some row := by
    show (({ world with loans := world.loans.set id { dead with live := false } }
      ).RequestReturns custody).loans.get key = some row
    exact found
  rw [Table.get_map_values] at canonical
  obtain ⟨original,originalFound,rowEq⟩ := Option.map_eq_some_iff.mp canonical
  by_cases same : key = id
  · subst key
    have originalEq : original = { dead with live := false } :=
      Option.some.inj (originalFound.symm.trans (Table.get_set _ _ _))
    subst originalEq
    refine ⟨World.restamp custody dead,?_,?_,?_,?_,?_,?_⟩
    · rw [World.RequestReturns.get_eq,deadFound]
      rfl
    · simp only [← rowEq,World.restamp_kind]
    · simp only [← rowEq,World.restamp_referent]
    · simp only [← rowEq,World.restamp_parent]
    · simp only [← rowEq,World.restamp_guards]
    · simp only [← rowEq,World.restamp_live]
      intro live
      exact absurd live (by simp)
  · have previousFound : Table.get world.loans key = some original := by
      rw [Table.get_set_other _ _ _ _ same] at originalFound
      exact originalFound
    refine ⟨World.restamp custody original,?_,?_,?_,?_,?_,?_⟩
    · rw [World.RequestReturns.get_eq,previousFound]
      rfl
    · simp only [← rowEq,World.restamp_kind]
    · simp only [← rowEq,World.restamp_referent]
    · simp only [← rowEq,World.restamp_parent]
    · simp only [← rowEq,World.restamp_guards]
    · simp only [← rowEq,World.restamp_live]
      exact fun live => live

end Glorious.Language

namespace Glorious.Language

open Kernel

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Ending one loan leaves a destructible resident destructible: the ending
only kills a row, so the owning permission's exclusion still holds (a raw-table
clause), and every pending-return clause reading a living row reads an earlier
living row through the relinquishment frame. -/
theorem World.Destroys.end_loan {program : RuntimeProgram} {world : World} {address : Address}
    (tree : World.Destroys program world address) {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) :
    World.Destroys program { world with loans := world.loans.set id { loan with live := false } } address := by
  revert found
  induction tree with
  | @resident addressTree value stored disposable shell noCont noRef noAvail permission kinds ancestry children ih =>
    intro found
    refine .resident stored disposable shell noCont noRef noAvail ?_ ?_ ?_ ?_
    · refine ⟨?_,fun key row selected live overlap conflict => ?_⟩
      · obtain ⟨root,rootFound⟩ := permission.1
        exact ⟨root,by simpa only [World.root] using rootFound⟩
      · by_cases same : key = id
        · have selectedSet : (world.loans.set id { loan with live := false }).get key = some row := selected
          rw [same] at selectedSet
          rw [Table.get_set] at selectedSet
          cases selectedSet
          exact absurd live (by simp)
        · have selectedSet : (world.loans.set id { loan with live := false }).get key = some row := selected
          exact permission.2 key row (by rw [Table.get_set_other _ _ _ _ same] at selectedSet; exact selectedSet)
            live overlap conflict
    · intro key row selected live
      obtain ⟨previous,previousFound,sameKind,_,_,_,previousLive⟩ :=
        World.RequestReturns.frame_set (custody := .resident value.owner) (key := key) (row := row)
          found selected
      rw [← sameKind]
      exact kinds key previous previousFound (previousLive live)
    · intro key row selected
      obtain ⟨previous,previousFound,_,_,sameParent,sameGuards,_⟩ :=
        World.RequestReturns.frame_set (custody := .resident value.owner) (key := key) (row := row)
          found selected
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have linkPrevious : previous.parent = some parent := by rw [sameParent]; exact link
        have held := (ancestry key previous previousFound).1 parent linkPrevious
        intro missing
        exact held (World.RequestReturns.frame_set_none (custody := .resident value.owner) found missing)
      · have memberPrevious : guard ∈ previous.guards := by rw [sameGuards]; exact member
        have held := (ancestry key previous previousFound).2 guard memberPrevious
        intro missing
        exact held (World.RequestReturns.frame_set_none (custody := .resident value.owner) found missing)
    · intro index child selectedTree
      exact ih index child selectedTree found

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Two different children of one address are incomparable by the prefix
order: their field lists end in different indices. -/
theorem Address.child_not_prefix {address : Address} {first second : Nat} (different : first ≠ second) :
    ¬ (address.child first).Prefix (address.child second) := by
  intro included
  obtain ⟨_,_,suffix,shape⟩ := included
  simp only [Address.child] at shape
  have lengths : (address.fields ++ [second]).length = ((address.fields ++ [first]) ++ suffix).length := by
    rw [shape]
  simp only [List.length_append,List.length_cons,List.length_nil] at lengths
  have empty : suffix = [] := by
    cases suffix with
    | nil => rfl
    | cons head tail => simp at lengths
  subst empty
  simp only [List.append_nil] at shape
  have equal := List.append_cancel_left shape
  simp only [List.cons.injEq] at equal
  exact different equal.1.symm

/-- The prefix order is transitive, so a probe inside a descendant's subtree is
reached from the ancestor too. -/
theorem Address.Prefix.not_outer {outer inner probe : Address}
    (included : outer.Prefix inner) (down : inner.Prefix probe) : outer.Prefix probe :=
  ⟨included.1.trans down.1,included.2.1.trans down.2.1,
    by
      obtain ⟨firstSuffix,firstShape⟩ := included.2.2
      obtain ⟨secondSuffix,secondShape⟩ := down.2.2
      exact ⟨firstSuffix ++ secondSuffix,by rw [secondShape,firstShape,List.append_assoc]⟩⟩

end Glorious.Language
