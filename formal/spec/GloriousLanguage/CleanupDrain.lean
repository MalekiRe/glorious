import GloriousLanguage.BufferSlotConstruction
import GloriousLanguage.BulkMoveConstruction
import GloriousLanguage.CleanupDestruction
import GloriousLanguage.TransferPreservation
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
original admission of the actual retry closure: every reached identity has a
row or a stored reference, and reached ordinary/Drop loans are restored.
The measure is the pair (live loans, queue length): a silent step shortens the
queue and an ending step strictly reduces the live-loan count, so the retry
fixpoint cannot grow forever.

Nothing here re-implements a release algorithm: `LocalStep.releaseReferenced`,
`releaseResourceHeld`, `releaseBorrowed`, `releaseOwnedClaim`,
`releaseStorageRetained`, `releaseStorageReturned`, `releaseRoot`,
`releaseChild` and `releaseAlreadyEnded` are selected, not replaced. Each
successor world and the unchanged non-task state fields are reported exactly. -/
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


/-- The dependency closure the actual release queue retries: only its seeds
and the recorded parent/guard links, not an independent cleanup inventory. -/
inductive World.ReleaseReachable (world : World) (seeds : List Identity) : Identity → Prop where
  | seed {id} : id ∈ seeds → world.ReleaseReachable seeds id
  | retry {id loan dependency} : world.ReleaseReachable seeds id → world.loans.get id = some loan →
      dependency ∈ loan.parent.toList ++ loan.guards → world.ReleaseReachable seeds dependency

theorem World.ReleaseReachable.rebase {world : World} {seeds targets : List Identity} {id : Identity}
    (roots : ∀ identity ∈ seeds, world.ReleaseReachable targets identity)
    (reached : world.ReleaseReachable seeds id) : world.ReleaseReachable targets id := by
  induction reached with
  | seed member => exact roots _ member
  | retry _ found member ih => exact .retry ih found member

theorem World.ReleaseReachable.transport {before after : World} {seeds : List Identity} {id : Identity}
    (reached : before.ReleaseReachable seeds id)
    (rows : ∀ key loan, before.loans.get key = some loan →
      ∃ current, after.loans.get key = some current ∧ current.parent = loan.parent ∧ current.guards = loan.guards) :
    after.ReleaseReachable seeds id := by
  induction reached with
  | seed member => exact .seed member
  | retry _ found member ih =>
      obtain ⟨current,selected,parent,guards⟩ := rows _ _ found
      exact .retry ih selected (by simpa only [parent,guards] using member)


theorem World.ReleaseReachable.of_end_loan {world : World} {seeds : List Identity} {id ended : Identity} {loan : Loan}
    (found : world.loans.get ended = some loan)
    (reached : ({ world with loans := world.loans.set ended { loan with live := false } } : World).ReleaseReachable seeds id) :
    world.ReleaseReachable seeds id := by
  induction reached with
  | seed member => exact .seed member
  | @retry parent current dependency _ currentAt member ih =>
      by_cases same : parent = ended
      · subst parent
        have equal : current = { loan with live := false } :=
          Option.some.inj (currentAt.symm.trans (Table.get_set _ _ _))
        exact .retry ih found (by simpa only [equal] using member)
      · exact .retry ih (by simpa only [Table.get_set_other _ _ _ _ same] using currentAt) member

/-- Original admission for exactly the queue's retry closure. Ordinary and
Drop loans retain their real restoration obligations; unrelated live loans
need not be restorable and are not restricted to raw storage kinds. -/
structure World.ReleaseReady (program : RuntimeProgram) (world : World) (identities : List Identity) : Prop where
  rows : ∀ id, world.ReleaseReachable identities id → world.loans.get id ≠ none ∨
    world.References id ∨ world.ResourceReferences id
  restored : ∀ id, world.ReleaseReachable identities id → ∀ loan,
    world.loans.get id = some loan → loan.live = true →
    (loan.kind = .restoring ∨ loan.kind = .destructor) →
    world.Initialized loan.referent ∧ (loan.kind = .restoring → world.ResourcesClosed program loan.referent)

theorem World.ReleaseReady.rebase {program : RuntimeProgram} {world : World} {seeds targets : List Identity}
    (ready : world.ReleaseReady program seeds)
    (roots : ∀ id ∈ targets, world.ReleaseReachable seeds id) : world.ReleaseReady program targets where
  rows := fun id reached => ready.rows id (reached.rebase roots)
  restored := fun id reached => ready.restored id (reached.rebase roots)

theorem World.ReleaseReady.tail {program : RuntimeProgram} {world : World} {id : Identity} {rest : List Identity}
    (ready : world.ReleaseReady program (id :: rest)) : world.ReleaseReady program rest :=
  ready.rebase (fun _ member => .seed (List.mem_cons_of_mem _ member))

/-- The ending guards, rather than a future restoration premise, retain every
original restoration fact while the actual dead-row update keeps retry links. -/
theorem World.ReleaseReady.afterEnd {program : RuntimeProgram} {world : World} {id : Identity}
    {loan : Loan} {identities : List Identity} (ready : world.ReleaseReady program identities)
    (found : world.loans.get id = some loan) (references : ¬ world.References id)
    (resources : ¬ world.ResourceReferences id) :
    ({ world with loans := world.loans.set id { loan with live := false } }).ReleaseReady program identities where
  rows := by
    intro other reached
    rcases ready.rows other (reached.of_end_loan found) with held | fallback
    · refine Or.inl ?_
      by_cases same : other = id
      · subst other; exact fun missing => by simp [Table.get_set] at missing
      · simpa only [Table.get_set_other _ _ _ _ same] using held
    · exact Or.inr fallback
  restored := by
    intro other reached current selected live kind
    by_cases same : other = id
    · subst other
      have equal : current = { loan with live := false } :=
        Option.some.inj (selected.symm.trans (Table.get_set _ _ _))
      rw [equal] at live
      cases live
    · have previous : world.loans.get other = some current := by
        simpa only [Table.get_set_other _ _ _ _ same] using selected
      obtain ⟨initialized,closed⟩ := ready.restored other (reached.of_end_loan found) current previous live kind
      exact ⟨initialized,fun restoring => (closed restoring).end_loan found references resources⟩

/-- Raw-storage destructor admissions are one source producer of the general
retry contract. Their kind restriction is not imposed on ordinary call worlds. -/
theorem World.ReleaseReady.of_storage {program : RuntimeProgram} {world : World} {identities : List Identity}
    (rows : ∀ id ∈ identities, world.loans.get id ≠ none ∨ world.References id ∨ world.ResourceReferences id)
    (kinds : ∀ id loan, world.loans.get id = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow)
    (ancestry : ∀ id loan, world.loans.get id = some loan →
      (∀ parent, loan.parent = some parent → world.loans.get parent ≠ none) ∧
      (∀ guard ∈ loan.guards, world.loans.get guard ≠ none)) : world.ReleaseReady program identities where
  rows := by
    intro id reached
    cases reached with
    | seed member => exact rows id member
    | @retry parent loan _ _ found member =>
        refine Or.inl ?_
        rcases List.mem_append.mp member with parented | guarded
        · cases link : loan.parent with
          | none => simp [link] at parented
          | some parent =>
              have same : id = parent := by simpa [link] using parented
              subst id
              exact (ancestry _ loan found).1 parent link
        · exact (ancestry _ loan found).2 id guarded
  restored := by
    intro id _ loan found live ordinary
    rcases kinds id loan found live with kind | kind <;>
      rcases ordinary with ordinary | ordinary <;> rw [kind] at ordinary <;> cases ordinary


/-- The original custody inventory anticipates pending-return marking, not a
future world's restoration: all restoration obligations remain on this world. -/
def World.CustodyReleaseReady (program : RuntimeProgram) (world : World) (custody : ClaimCustody) : Prop :=
  world.ReleaseReady program (world.loans.filterMap fun (identity,loan) =>
    if loan.live && loan.kind == .storageBorrow && loan.custody == some custody then some identity else none)

theorem World.ReleaseReady.relinquished {program : RuntimeProgram} {before after : World}
    {identities : List Identity} {custody : ClaimCustody}
    (ready : before.ReleaseReady program identities) (relinquished : RelinquishesCustody before custody after) :
    after.ReleaseReady program identities := by
  have original : ∀ id, after.ReleaseReachable identities id → before.ReleaseReachable identities id := by
    intro id reached
    apply reached.transport
    intro key current selected
    obtain ⟨loan,found,same⟩ := relinquished.reflected selected
    obtain ⟨_,parent,_,_,_,_,_,guards⟩ := Loan.permissionState_eq_iff.mp same
    exact ⟨loan,found,parent.symm,guards.symm⟩
  refine ⟨?_,?_⟩
  · intro id reached
    rcases ready.rows id (original id reached) with present | fallback
    · refine Or.inl ?_
      cases found : before.loans.get id with
      | none => exact absurd found present
      | some loan =>
          obtain ⟨current,selected,_⟩ := relinquished.retained found
          exact fun missing => by rw [selected] at missing; cases missing
    · cases relinquished; exact Or.inr fallback
  · intro id reached current selected live ordinary
    obtain ⟨loan,found,same⟩ := relinquished.reflected selected
    obtain ⟨_,_,referent,_,_,alive,kind,_⟩ := Loan.permissionState_eq_iff.mp same
    obtain ⟨initialized,closed⟩ := ready.restored id (original id reached) loan found
      (alive.symm.trans live) (by simpa only [kind] using ordinary)
    rw [referent]
    exact ⟨by cases relinquished; exact initialized,
      fun restoring => (closed (kind.symm.trans restoring)).relinquished relinquished⟩

/-- The source custody inventory produces admission of the exact queue emitted
by relinquishment, including returns that were not previously requested. -/
theorem World.CustodyReleaseReady.requested {program : RuntimeProgram} {world : World} {custody : ClaimCustody}
    (ready : world.CustodyReleaseReady program custody) (handed : world.CustodyHandedOff custody) :
    (world.RequestReturns custody).ReleaseReady program ((world.RequestReturns custody).loans.filterMap fun (identity,loan) =>
      if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
        some identity else none) := by
  apply (World.ReleaseReady.relinquished ready (RelinquishesCustody.of_handedOff handed)).rebase
  intro id member
  apply World.ReleaseReachable.seed
  obtain ⟨entry,present,selected⟩ := List.mem_filterMap.mp member
  rw [World.RequestReturns.loans_eq] at present
  obtain ⟨⟨key,loan⟩,source,mapped⟩ := List.mem_map.mp present
  subst entry
  change (if (World.restamp custody loan).live && (World.restamp custody loan).kind == .storageBorrow &&
    (World.restamp custody loan).returnRequested && (World.restamp custody loan).custody == some custody then
      some key else none) = some id at selected
  by_cases chosen : (World.restamp custody loan).live && (World.restamp custody loan).kind == .storageBorrow &&
      (World.restamp custody loan).returnRequested && (World.restamp custody loan).custody == some custody
  · have same : key = id := by simpa only [chosen,if_true,Option.some.injEq] using selected
    subst id
    have sourceChosen : loan.live && loan.kind == .storageBorrow && loan.custody == some custody := by
      simp only [World.restamp_live,World.restamp_kind,World.restamp_custody,Bool.and_eq_true] at chosen ⊢
      exact ⟨⟨chosen.1.1.1,chosen.1.1.2⟩,chosen.2⟩
    exact List.mem_filterMap.mpr ⟨(key,loan),source,by simp only [sourceChosen,if_true]⟩
  · have impossible : (Option.none : Option Identity) = some id := by
      simpa only [chosen,Bool.false_eq_true,if_false] using selected
    exact absurd impossible (by simp)

/-- Consuming a private empty shell preserves the original retry closure.
Actual resident/resource persistence handles even the queue's rowless skips. -/
theorem World.ReleaseReady.write_empty_shell {program : RuntimeProgram} {before after : World}
    {identities : List Identity} {address : Address} {value : Value} {replacement : Option Value}
    (ready : before.ReleaseReady program identities) (safe : CanEndStorage before address.root)
    (stored : before.Stores address value) (fields : ∀ field ∈ value.fields, field = none)
    (notReference : ∀ id, value.head ≠ .reference id) (resources : value.resources = [])
    (written : before.write address replacement = some after) : after.ReleaseReady program identities := by
  have loans := World.write_loans written
  have original : ∀ id, after.ReleaseReachable identities id → before.ReleaseReachable identities id := by
    intro id reached
    exact reached.transport (fun key loan selected =>
      ⟨loan,by simpa only [loans] using selected,rfl,rfl⟩)
  refine ⟨?_,?_⟩
  · intro id reached
    rcases ready.rows id (original id reached) with present | reference | resource
    · exact Or.inl (by simpa only [loans] using present)
    · exact Or.inr (Or.inl (World.write_nonreference_shell_references stored fields notReference written reference))
    · exact Or.inr (Or.inr (World.write_empty_resources_shell_resourceReferences stored fields resources written resource))
  · intro id reached loan selected live ordinary
    have found : before.loans.get id = some loan := by simpa only [loans] using selected
    obtain ⟨initialized,closed⟩ := ready.restored id (original id reached) loan found live ordinary
    have outside : ¬ address.Overlaps loan.referent := fun overlap => safe.1 id loan found live overlap.1.symm
    exact ⟨by simpa only [World.Initialized,World.Stores,World.write_disjoint written outside] using initialized,
      fun restoring => (closed restoring).private_write safe outside written⟩





/-- A table entry for an identity makes that identity readable. -/
theorem Table.get_isSome_of_mem {α : Type} {table : Table α} {id : Identity} {value : α}
    (member : (id,value) ∈ table) : (table.get id).isSome := by
  have found : (table.find? (fun entry => entry.1 == id)).isSome = true :=
    List.find?_isSome.mpr ⟨(id,value),member,by simp⟩
  simpa [Table.get] using found

/-- The existing raw-storage destruction facts admit the actual filtered
custody queue and every recorded retry; ordinary worlds use ReleaseReady directly. -/
theorem World.ReleaseReady.custody_of_storage {program : RuntimeProgram} {world : World} {custody : ClaimCustody}
    (kinds : ∀ id loan, world.loans.get id = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow)
    (ancestry : ∀ id loan, world.loans.get id = some loan →
      (∀ parent, loan.parent = some parent → world.loans.get parent ≠ none) ∧
      (∀ guard ∈ loan.guards, world.loans.get guard ≠ none)) :
    world.ReleaseReady program (world.loans.filterMap fun (identity,loan) =>
      if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
        some identity else none) := by
  apply World.ReleaseReady.of_storage (kinds := kinds) (ancestry := ancestry)
  intro id member
  refine Or.inl ?_
  obtain ⟨entry,present,selected⟩ := List.mem_filterMap.mp member
  rcases entry with ⟨key,loan⟩
  by_cases condition : loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody
  · simp only [condition,if_true,Option.some.injEq] at selected
    subst selected
    exact fun missing => by
      have readable := Table.get_isSome_of_mem present
      simp [missing] at readable
  · have impossible : (Option.none : Option Identity) = some id := by
      simpa only [condition,Bool.false_eq_true,if_false] using selected
    exact absurd impossible (by simp)


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
      before.world.liveCount ≤ bound → before.task = ReleaseQueue identities next →
      before.world.ReleaseReady program identities →
      ∃ (after : World) (trace : List Event),
        CleanupRun program host before trace { before with world := after, task := next } ∧
          after.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after := by
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro next before identities boundLe task ready
    induction identities generalizing before next with
    | nil =>
      have same : { before with world := before.world, task := next } = before := by
        have current : before.task = next := by simpa [ReleaseQueue] using task
        simp [← current]
      exact ⟨before.world,[],by rw [same]; exact .refl,Nat.le_refl _,World.LoanReleaseFrame.refl _⟩
    | cons id rest listIh =>
      have head : before.task = Task.releaseLoan id (ReleaseQueue rest next) :=
        task.trans (ReleaseQueue_cons id rest next)
      have cleanup : before.task.Cleanup := by simp [Task.Cleanup,head]
      have silent (step : LocalStep program before none { before with task := ReleaseQueue rest next }) :
          ∃ (after : World) (trace : List Event),
            CleanupRun program host before trace { before with world := after, task := next } ∧
              after.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after := by
        obtain ⟨after,trace,run,counted,frame⟩ :=
          listIh (before := { before with task := ReleaseQueue rest next }) (next := next) boundLe rfl ready.tail
        exact ⟨after,trace,.silent cleanup (Or.inl step) run,counted,frame⟩
      cases found : before.world.loans.get id with
      | none =>
        have fallback : before.world.References id ∨ before.world.ResourceReferences id := by
          rcases ready.rows id (.seed (by simp)) with missing | later
          · exact absurd found missing
          · exact later
        rcases fallback with referenced | resourced
        · exact silent (.releaseReferenced head referenced)
        · exact silent (.releaseResourceHeld head resourced)
      | some loan =>
        by_cases live : loan.live = true
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
                let ended : World := { before.world with loans := before.world.loans.set id { loan with live := false } }
                let pushed := loan.parent.toList ++ loan.guards
                have finish (step : LocalStep program before (some (.loanEnd id))
                    { before with world := ended, task := ReleaseLoans pushed (ReleaseQueue rest next) }) :
                    ∃ (after : World) (trace : List Event),
                      CleanupRun program host before trace { before with world := after, task := next } ∧
                        after.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after := by
                  have decreased : ended.liveCount < before.world.liveCount := World.liveCount_set_dead found live
                  have afterReady : ended.ReleaseReady program (pushed.eraseDups ++ rest) := by
                    apply (ready.afterEnd found referenced resourced).rebase
                    intro other member
                    rcases List.mem_append.mp member with retry | remaining
                    · exact .retry (.seed (by simp)) (Table.get_set _ _ _) (List.mem_eraseDups.mp retry)
                    · exact .seed (List.mem_cons_of_mem _ remaining)
                  obtain ⟨after,trace,run,counted,frame⟩ :=
                    ih ended.liveCount (Nat.lt_of_lt_of_le decreased boundLe) next
                      { before with world := ended, task := ReleaseLoans pushed (ReleaseQueue rest next) }
                      (pushed.eraseDups ++ rest) (Nat.le_refl _)
                      ((ReleaseLoans_eq_queue pushed (ReleaseQueue rest next)).trans
                        (ReleaseQueue_append pushed.eraseDups rest next)) afterReady
                  exact ⟨after,.loanEnd id :: trace,.visible cleanup (Or.inl step) run,
                    Nat.le_trans counted (Nat.le_of_lt decreased),(World.loanReleaseFrame_set_dead found).trans frame⟩
                have ordinary (kind : loan.kind = .restoring ∨ loan.kind = .destructor) :
                    ∃ (after : World) (trace : List Event),
                      CleanupRun program host before trace { before with world := after, task := next } ∧
                        after.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after := by
                  obtain ⟨initialized,closed⟩ := ready.restored id (.seed (by simp)) loan found live kind
                  have ending : EndsLoan program before.world id ended :=
                    .restored found live kind initialized closed referenced resourced children
                  cases parent : loan.parent with
                  | none =>
                      apply finish
                      simpa only [pushed,parent,Option.toList_none,List.nil_append] using
                        (LocalStep.releaseRoot head found parent ending)
                  | some parentId =>
                      apply finish
                      simpa only [pushed,parent,Option.toList_some,List.singleton_append] using
                        (LocalStep.releaseChild head found parent ending)
                cases kind : loan.kind with
                | owning => exact silent (.releaseOwnedClaim head found kind)
                | restoring => exact ordinary (Or.inl kind)
                | destructor => exact ordinary (Or.inr kind)
                | storageBorrow =>
                    by_cases requested : loan.returnRequested = true
                    · exact finish (.releaseStorageReturned head found
                        (.returned found live kind requested referenced resourced children))
                    · have retained : loan.returnRequested = false := by
                        cases held : loan.returnRequested with
                        | false => rfl
                        | true => exact absurd held requested
                      exact silent (.releaseStorageRetained head found kind retained)
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
    (ready : before.world.ReleaseReady program (before.world.loans.filterMap fun (identity,loan) =>
      if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
        some identity else none)) :
    ∃ (after : World) (trace : List Event),
      CleanupRun program host before trace { before with world := after, task := next } ∧
        before.world.LoanReleaseFrame after := by
  let identities := before.world.loans.filterMap fun (identity,loan) =>
    if loan.live && loan.kind == .storageBorrow && loan.returnRequested && loan.custody == some custody then
      some identity else none
  obtain ⟨after,trace,run,_,frame⟩ :=
    CleanupRun.release_queue (program := program) (host := host) before.world.liveCount next before identities.eraseDups
      (Nat.le_refl _) (task.trans (ReleaseLoans_eq_queue identities next))
      (ready.rebase (fun _ member => .seed (List.mem_eraseDups.mp member)))
  exact ⟨after,trace,run,frame⟩

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
  obtain ⟨releasedWorld,trace,drained,frame⟩ :=
    CleanupRun.release_custody_returns
      (before := { before with world := cleared, task := ReleaseCustodyLoans cleared (.resident value.owner) (.retire id (.cleanup context roots next)) })
      rfl (World.ReleaseReady.custody_of_storage kinds ancestry)
  let released : State := { before with world := releasedWorld, task := .retire id (.cleanup context roots next) }
  have goal : released.task = .retire id (.cleanup context roots next) := rfl
  have releasedRoot : released.world.roots.get id = some { root with value := none } := by
    rw [congrArg World.roots frame.rest]
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
  · exact shellRun.append (drained.append (.visible (by simp [Task.Cleanup]) (Or.inl step) .refl))
  · exact ⟨{ root with value := none, live := false, generation := root.generation + 1 },
      Table.get_set released.world.roots id { root with value := none, live := false, generation := root.generation + 1 }, rfl⟩

end Glorious.Language.Execution

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


/-- A descendant of one child of an address can only be reached from the same
child: the field lists must agree in the index that follows the shared prefix. -/
theorem Address.child_prefix_grandchild {address : Address} {first second index : Nat}
    (included : (address.child first).Prefix ((address.child second).child index)) : first = second := by
  obtain ⟨_,_,suffix,shape⟩ := included
  simp only [Address.child,List.append_assoc,List.singleton_append] at shape
  have equal := List.append_cancel_left shape
  simp only [List.cons.injEq] at equal
  exact equal.1.symm


/-- Two prefixes of one address are comparable, because both extend the same
field list. -/
theorem Address.Prefix.comparable {first second probe : Address}
    (firstIn : first.Prefix probe) (secondIn : second.Prefix probe) :
    first.Prefix second ∨ second.Prefix first := by
  obtain ⟨firstSuffix,firstShape⟩ := firstIn.2.2
  obtain ⟨secondSuffix,secondShape⟩ := secondIn.2.2
  have same : first.fields ++ firstSuffix = second.fields ++ secondSuffix := by
    rw [← firstShape,← secondShape]
  rcases List.append_eq_append_iff.mp same with ⟨shared,firstEq,_⟩ | ⟨shared,secondEq,_⟩
  · left
    exact ⟨firstIn.1.trans secondIn.1.symm,firstIn.2.1.trans secondIn.2.1.symm,⟨shared,firstEq⟩⟩
  · right
    exact ⟨secondIn.1.trans firstIn.1.symm,secondIn.2.1.trans firstIn.2.1.symm,⟨shared,secondEq⟩⟩

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
      (∀ id loan, world.loans.get id = some loan →
        loan.live = true → loan.kind = .owning ∨ loan.kind = .storageBorrow) →
      (∀ id loan, world.loans.get id = some loan →
        (∀ parent, loan.parent = some parent → world.loans.get parent ≠ none) ∧
        (∀ guard ∈ loan.guards, world.loans.get guard ≠ none)) →
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
      exact kinds id loan (by simpa only [loansAfter] using found) live
    · intro id loan found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have held := (ancestry id loan (by simpa only [loansAfter] using found)).1 parent link
        simpa only [loansAfter] using held
      · have held := (ancestry id loan (by simpa only [loansAfter] using found)).2 guard member
        simpa only [loansAfter] using held
    · intro index child selected
      exact ih index child selected
        (fun probe included => deep probe (Address.Prefix.trans (Address.Prefix.child ⟨rfl,rfl,⟨[],by simp⟩⟩ index).1 included))

end Glorious.Language

namespace Glorious.Language

open Kernel


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

/-- Ending one loan leaves a destructible resident destructible: the ending only
kills a row, so the owning permission's exclusion and the pending-return clauses,
both read from the raw loan table, still hold. -/
theorem World.Destroys.end_loan {program : RuntimeProgram} {world : World} {address : Address}
    (tree : World.Destroys program world address) {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) :
    World.Destroys program { world with loans := world.loans.set id { loan with live := false } } address := by
  revert found
  induction tree with
  | @resident addr value stored disposable shell noCont noRef noAvail permission kinds ancestry children ih =>
    intro found
    have kept {key : Identity} {row : Loan} (different : key ≠ id)
        (selected : (world.loans.set id { loan with live := false }).get key = some row) :
        world.loans.get key = some row := by
      rw [Table.get_set_other _ _ _ _ different] at selected
      exact selected
    refine .resident stored disposable shell noCont noRef noAvail ?_ ?_ ?_ ?_
    · refine ⟨permission.1,fun key row selected live overlap conflict => ?_⟩
      by_cases same : key = id
      · have dead : (world.loans.set id { loan with live := false }).get key = some row := selected
        rw [same,Table.get_set] at dead
        cases dead
        exact absurd live (by simp)
      · exact permission.2 key row (kept same selected) live overlap conflict
    · intro key row selected live
      by_cases same : key = id
      · have dead : (world.loans.set id { loan with live := false }).get key = some row := selected
        rw [same,Table.get_set] at dead
        cases dead
        exact absurd live (by simp)
      · exact kinds key row (kept same selected) live
    · intro key row selected
      by_cases same : key = id
      · have dead : (world.loans.set id { loan with live := false }).get key = some row := selected
        rw [same,Table.get_set] at dead
        have rowEq : row = { loan with live := false } := Option.some.inj dead.symm
        subst rowEq
        refine ⟨fun parent link => ?_,fun guard member => ?_⟩
        · have justLive : ({ loan with live := false } : Loan).parent = loan.parent := rfl
          have linkOriginal : loan.parent = some parent := by rw [← justLive]; exact link
          have held := (ancestry id loan found).1 parent linkOriginal
          intro missing
          by_cases parentIs : parent = id
          · rw [parentIs,Table.get_set] at missing
            cases missing
          · exact held (by simpa only [Table.get_set_other _ _ _ _ parentIs] using missing)
        · have justGuards : ({ loan with live := false } : Loan).guards = loan.guards := rfl
          have memberOriginal : guard ∈ loan.guards := by rw [← justGuards]; exact member
          have held := (ancestry id loan found).2 guard memberOriginal
          intro missing
          by_cases guardIs : guard = id
          · rw [guardIs,Table.get_set] at missing
            cases missing
          · exact held (by simpa only [Table.get_set_other _ _ _ _ guardIs] using missing)
      · have previousFound : world.loans.get key = some row := kept same selected
        refine ⟨fun parent link => ?_,fun guard member => ?_⟩
        · have held := (ancestry key row previousFound).1 parent link
          intro missing
          by_cases parentIs : parent = id
          · rw [parentIs,Table.get_set] at missing
            cases missing
          · exact held (by simpa only [Table.get_set_other _ _ _ _ parentIs] using missing)
        · have held := (ancestry key row previousFound).2 guard member
          intro missing
          by_cases guardIs : guard = id
          · rw [guardIs,Table.get_set] at missing
            cases missing
          · exact held (by simpa only [Table.get_set_other _ _ _ _ guardIs] using missing)
    · intro index child selected
      exact ih index child selected found

end Glorious.Language

namespace Glorious.Language

open Kernel

namespace Glorious.Language

open Kernel

/-- The footprint a node's destruction leaves: outside its own subtree no stored
value and no root row changes, the loan table keeps every row it had, and every
live row of the result is a live row of the original with the same kind, mode and
referent. -/
structure World.DestroyFrame (before after : World) (outside : Address) : Prop where
  reads : ∀ probe, ¬ outside.Prefix probe → after.read probe = before.read probe
  roots : ∀ probe, ¬ outside.Prefix probe → (after.root probe).isSome = (before.root probe).isSome
  rows : ∀ key row, after.loans.get key = some row → ∃ original, before.loans.get key = some original ∧
    original.parent = row.parent ∧ original.guards = row.guards
  present : ∀ key original, before.loans.get key = some original → ∃ row, after.loans.get key = some row
  liveness : ∀ key row, after.loans.get key = some row → row.live = true →
    ∃ original, before.loans.get key = some original ∧ original.live = true ∧
      original.kind = row.kind ∧ original.mode = row.mode ∧ original.referent = row.referent

/-- A subtree whose slots all lie outside a destruction frame's sphere keeps its
whole inventory in the produced world. -/
theorem World.Destroys.of_destroy_frame {program : RuntimeProgram} {before after : World}
    {address outside : Address} (tree : World.Destroys program before address)
    (frame : World.DestroyFrame before after outside)
    (excluded : ∀ probe, address.Prefix probe → ¬ outside.Prefix probe) :
    World.Destroys program after address := by
  revert frame excluded
  induction tree with
  | @resident addr value stored disposable shell noCont noRef noAvail permission kinds ancestry children ih =>
    intro frame excluded
    have atRoot : ¬ outside.Prefix addr := excluded addr ⟨rfl,rfl,⟨[],by simp⟩⟩
    have childExcluded (index : Nat) :
        ∀ probe, (addr.child index).Prefix probe → ¬ outside.Prefix probe :=
      fun probe included => excluded probe
        (Address.Prefix.not_outer (Address.Prefix.child ⟨rfl,rfl,⟨[],by simp⟩⟩ index).1 included)
    refine .resident ?_ disposable shell noCont noRef noAvail ?_ ?_ ?_ ?_
    · show after.read addr = some value
      rw [frame.reads addr atRoot]
      exact stored
    · refine ⟨?_,fun key row selected live overlap conflict => ?_⟩
      · obtain ⟨root,rootFound⟩ := permission.1
        have same := frame.roots addr atRoot
        rw [rootFound] at same
        exact Option.isSome_iff_exists.mp (by simpa using same)
      · obtain ⟨original,originalFound,originalLive,_,sameMode,sameReferent⟩ :=
          frame.liveness key row selected live
        refine permission.2 key original originalFound originalLive (sameReferent ▸ overlap) ?_
        rcases conflict with nonshared | unique
        · exact Or.inl nonshared
        · exact Or.inr (by rw [sameMode]; exact unique)
    · intro key row selected live
      obtain ⟨original,originalFound,originalLive,sameKind,_,_⟩ := frame.liveness key row selected live
      rw [← sameKind]
      exact kinds key original originalFound originalLive
    · intro key row selected
      obtain ⟨original,originalFound,sameParent,sameGuards⟩ := frame.rows key row selected
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have linkOriginal : original.parent = some parent := by rw [sameParent]; exact link
        have held := (ancestry key original originalFound).1 parent linkOriginal
        intro missing
        obtain ⟨beforeRow,beforeFound⟩ := Option.ne_none_iff_exists'.mp held
        obtain ⟨afterRow,afterFound⟩ := frame.present parent beforeRow beforeFound
        rw [afterFound] at missing
        cases missing
      · have memberOriginal : guard ∈ original.guards := by rw [sameGuards]; exact member
        have held := (ancestry key original originalFound).2 guard memberOriginal
        intro missing
        obtain ⟨beforeRow,beforeFound⟩ := Option.ne_none_iff_exists'.mp held
        obtain ⟨afterRow,afterFound⟩ := frame.present guard beforeRow beforeFound
        rw [afterFound] at missing
        cases missing
    · intro index child selected
      exact ih index child selected frame (childExcluded index)

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Destruction frames compose along an actual run. -/
theorem World.DestroyFrame.trans {before middle after : World} {outside : Address}
    (first : World.DestroyFrame before middle outside) (second : World.DestroyFrame middle after outside) :
    World.DestroyFrame before after outside where
  reads := fun probe outside' => (second.reads probe outside').trans (first.reads probe outside')
  roots := fun probe outside' => (second.roots probe outside').trans (first.roots probe outside')
  rows := fun key row found => by
    obtain ⟨middleRow, middleFound, middleParent, middleGuards⟩ := second.rows key row found
    obtain ⟨original, originalFound, originalParent, originalGuards⟩ := first.rows key middleRow middleFound
    exact ⟨original, originalFound, originalParent.trans middleParent, originalGuards.trans middleGuards⟩
  present := fun key original found => by
    obtain ⟨middleRow, middleFound⟩ := first.present key original found
    obtain ⟨row, rowFound⟩ := second.present key middleRow middleFound
    exact ⟨row, rowFound⟩
  liveness := fun key row found live => by
    obtain ⟨middleRow, middleFound, middleLive, sameKind, sameMode, sameReferent⟩ :=
      second.liveness key row found live
    obtain ⟨original, originalFound, originalLive, originalKind, originalMode, originalReferent⟩ :=
      first.liveness key middleRow middleFound middleLive
    exact ⟨original, originalFound, originalLive, originalKind.trans sameKind, originalMode.trans sameMode,
      originalReferent.trans sameReferent⟩

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A write whose target lies inside the frame's sphere leaves the frame: the
loan table is untouched, the resolved root is read from live and generation
(which the update keeps), and outside the sphere the read does not move. -/
theorem World.DestroyFrame.of_write {before after : World} {outside target : Address}
    {replacement : Option Value} (written : before.write target replacement = some after)
    (deep : ∀ probe, ¬ outside.Prefix probe → ¬ target.Overlaps probe) :
    World.DestroyFrame before after outside where
  reads := fun probe outside' => World.write_disjoint written (deep probe outside')
  roots := fun probe outside' => by
    obtain ⟨root, replacement', found, shape⟩ := World.write_value_update written
    rw [shape]
    simp only [World.root]
    by_cases same : probe.root = target.root
    · rw [same, Table.get_set before.roots target.root { root with value := replacement' }, found]
      by_cases cond : root.live = true ∧ root.generation = probe.generation <;> simp [cond]
    · rw [Table.get_set_other before.roots target.root probe.root { root with value := replacement' } same]
  rows := fun key row found => by
    refine ⟨row,?_,rfl,rfl⟩
    rw [World.write_rest written] at found
    exact found
  present := fun key original found => by
    exact ⟨original, by rw [World.write_rest written]; exact found⟩
  liveness := fun key row found live => by
    refine ⟨row,?_,live,rfl,rfl,rfl⟩
    rw [World.write_rest written] at found
    exact found

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- The relinquishment restamp is a frame: it rewrites the loan table only,
keeping every row, its parent and guards, and the kind, mode and referent of
every live row, while the reads and the resolved roots do not move at all. -/
theorem World.DestroyFrame.of_requestReturns {before : World} {custody : ClaimCustody} {outside : Address} :
    World.DestroyFrame before (before.RequestReturns custody) outside where
  reads := fun probe outside' => rfl
  roots := fun probe outside' => rfl
  rows := fun key row found => by
    rw [World.RequestReturns.get_eq] at found
    obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
    refine ⟨original,originalFound,?_,?_⟩
    · rw [← same,World.restamp_parent]
    · rw [← same,World.restamp_guards]
  present := fun key original found => by
    refine ⟨World.restamp custody original,?_⟩
    rw [World.RequestReturns.get_eq,found]
    rfl
  liveness := fun key row found live => by
    rw [World.RequestReturns.get_eq] at found
    obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
    refine ⟨original,originalFound,?_,?_,?_,?_⟩
    · rw [← same,World.restamp_live] at live
      exact live
    · rw [← same,World.restamp_kind]
    · rw [← same,World.restamp_mode]
    · rw [← same,World.restamp_referent]

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- The custody's pending-return restamp leaves a destructible subtree
destructible: the stored shell is untouched (the restamp rewrites the loan table
only), the ownership permission reads the after table through the restamp, the
live rows keep their owning kind, and parent and guard rows are still present
because the restamp maps `some` to `some`. -/
theorem World.Destroys.requestReturns {program : RuntimeProgram} {world : World} {address : Address}
    (tree : World.Destroys program world address) (custody : ClaimCustody) :
    World.Destroys program (world.RequestReturns custody) address := by
  induction tree with
  | @resident address value stored disposable shell noCont noRef noAvail permission kinds ancestry children ih =>
    have storedAfter : (world.RequestReturns custody).Stores address value := by
      show (world.RequestReturns custody).read address = some value
      rw [show (world.RequestReturns custody).read address = world.read address from rfl]
      exact stored
    have located : ∃ root, (world.RequestReturns custody).root address = some root :=
      (Option.bind_eq_some_iff.mp storedAfter).imp fun _ found => found.1
    have permissionAfter : Permitted (world.RequestReturns custody) .owner .owned address :=
      ⟨located,fun id loan found live overlap conflict => by
        rw [World.RequestReturns.get_eq] at found
        obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
        rw [← same,World.restamp_live] at live
        rw [← same,World.restamp_referent] at overlap
        rw [← same,World.restamp_mode] at conflict
        exact permission.2 id original originalFound live overlap conflict⟩
    refine .resident storedAfter disposable shell noCont noRef noAvail permissionAfter ?_ ?_ ?_
    · intro id loan found live
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      rw [← same,World.restamp_live] at live
      rw [← same,World.restamp_kind]
      exact kinds id original originalFound live
    · intro id loan found
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have linkOriginal : original.parent = some parent := by rw [← same,World.restamp_parent] at link; exact link
        have held := (ancestry id original originalFound).1 parent linkOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
      · have memberOriginal : guard ∈ original.guards := by
          rw [← same,World.restamp_guards] at member
          exact member
        have held := (ancestry id original originalFound).2 guard memberOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
    · intro index child selected
      exact ih index child selected

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Ending one loan is a frame: the row is kept with its parent and guards, the
killed row is not live afterwards so the live-row facts carry over, and neither
the reads nor the resolved roots move. -/
theorem World.DestroyFrame.of_kill {before : World} {id : Identity} {loan : Loan} {outside : Address}
    (found : before.loans.get id = some loan) :
    World.DestroyFrame before { before with loans := before.loans.set id { loan with live := false } }
      outside where
  reads := fun probe outside' => rfl
  roots := fun probe outside' => rfl
  rows := fun key row selected => by
    dsimp only [] at selected
    by_cases same : key = id
    · rw [same] at selected
      rw [Table.get_set before.loans id { loan with live := false }] at selected
      have rowEq : { loan with live := false } = row := Option.some.inj selected
      subst rowEq
      rw [same]
      exact ⟨loan, found, rfl, rfl⟩
    · have beforeFound : before.loans.get key = some row := by
        rwa [Table.get_set_other before.loans id key { loan with live := false } same] at selected
      exact ⟨row, beforeFound, rfl, rfl⟩
  present := fun key original found' => by
    dsimp only []
    by_cases same : key = id
    · rw [same]
      exact ⟨{ loan with live := false }, by rw [Table.get_set before.loans id { loan with live := false }]⟩
    · exact ⟨original, by rw [Table.get_set_other before.loans id key { loan with live := false } same]; exact found'⟩
  liveness := fun key row selected live => by
    dsimp only [] at selected
    by_cases same : key = id
    · rw [same] at selected
      rw [Table.get_set before.loans id { loan with live := false }] at selected
      have rowEq : { loan with live := false } = row := Option.some.inj selected
      subst rowEq
      rw [same]
      simp at live
    · have beforeFound : before.loans.get key = some row := by
        rwa [Table.get_set_other _ _ _ _ same] at selected
      exact ⟨row, beforeFound, live, rfl, rfl, rfl⟩

end Glorious.Language

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A clear at one child slot re-reads its parent shell: the parent survives as
the same shell whose one slot is now a hole, with head, owner, type, liveness flag
and resources untouched and every other slot preserved. The parent may sit at any
depth, which is what a nested resident's slot clearing needs (the receiver-shaped
version states it only at a root address). -/
theorem World.Stores.write_child_none {before after : World} {address : Address} {index : Nat}
    {shell : Value} (stored : before.Stores address shell)
    (written : before.write (address.child index) none = some after) :
    ∃ changed, after.Stores address changed ∧ changed.head = shell.head ∧ changed.owner = shell.owner ∧
      changed.type = shell.type ∧ changed.shellLive = shell.shellLive ∧ changed.resources = shell.resources ∧
      changed.fields[index]? = some none ∧
      ∀ other, other ≠ index → changed.fields[other]? = shell.fields[other]? := by
  obtain ⟨parent,slot,storedParent,slotFound,rewritten⟩ := World.write_child_shape written
  have same : parent = shell := (Option.some.inj (stored.symm.trans storedParent)).symm
  subst parent
  have bound : index < shell.fields.length := (List.getElem?_eq_some_iff.mp slotFound).1
  refine ⟨shell.withFields (shell.fields.set index none),?_,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · show after.read address = some (shell.withFields (shell.fields.set index none))
    have read := World.write_read_inside rewritten []
    simpa [Value.atPath] using read
  · exact List.getElem?_set_self bound
  · intro other different
    exact List.getElem?_set_ne (Ne.symm different)

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A clear at one child slot leaves another child slot of the same parent
vacant: sibling slots do not overlap, so the write is apart from the observed one
and vacancy survives. This is what lets a field loop carry the vacancies it has
already produced across the later children's clears. -/
theorem World.Vacant.write_child_other {before after : World} {address : Address} {index other : Nat}
    {value : Option Value} (vacant : before.Vacant (address.child other))
    (written : before.write (address.child index) value = some after) (different : index ≠ other) :
    after.Vacant (address.child other) :=
  World.Vacant.write_disjoint vacant written (Address.child_not_overlaps different)

end Glorious.Language

namespace Glorious.Language.Execution

open Glorious.Language.Kernel


/-- One scheduled child of the nested field loop is fully destroyed: its own
shell with every write derived, then the pending returns its custody scheduled, so
the loop continues at the remaining indices rather than at a release task. The
parent shell is re-read with that child's slot now a hole and its head, owner,
type, liveness flag, resources and every other slot untouched. The child's
machine premises and the drain's obligations are its own tree's, so nothing here
is assumed. -/
theorem CleanupRun.destroy_child {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {index : Nat} {authority : Authority}
    {rest : List Nat} {next : Task} {value shell : Value}
    (task : before.task = .destroy context (address.child index) .owner (.destroyFields context address authority rest next))
    (tree : World.Destroys program before.world (address.child index))
    (parent : before.world.Stores address value)
    (stored : before.world.Stores (address.child index) shell)
    (holes : ∀ i, i < shell.fields.length → shell.fields[i]? = some none)
    (handed : before.world.CustodyHandedOff (.resident shell.owner)) :
    ∃ trace final changed, CleanupRun program host before trace final ∧
      final.task = .destroyFields context address authority rest next ∧
      final.world.Stores address changed ∧ changed.head = value.head ∧ changed.owner = value.owner ∧
      changed.type = value.type ∧ changed.shellLive = value.shellLive ∧ changed.resources = value.resources ∧
      changed.fields[index]? = some none ∧
      ∀ other, other ≠ index → changed.fields[other]? = value.fields[other]? := by
  cases tree with
  | resident treeStored treeDisposable treeShell treeNoContinuation treeNoReference treeNoAvailable permission kinds ancestry children =>
    have valueEq : shell = _ := Option.some.inj (stored.symm.trans treeStored)
    obtain ⟨mid, cleared, run, midWorld, midTask, written⟩ := CleanupRun.destroy_shell (before := before)
      (context := context) (address := address.child index) (authority := .owner)
      (next := .destroyFields context address authority rest next)
      task stored (by simpa only [← valueEq] using treeDisposable)
      (Or.inl (by simpa only [← valueEq] using treeShell))
      (by simpa only [← valueEq] using treeNoContinuation)
      (by simpa only [← valueEq] using treeNoReference)
      (by simpa only [← valueEq] using treeNoAvailable)
      holes permission handed
    have parentShifted : (before.world.RequestReturns (.resident shell.owner)).Stores address value := by
      show (before.world.RequestReturns (.resident shell.owner)).read address = some value
      rw [show (before.world.RequestReturns (.resident shell.owner)).read address = before.world.read address from rfl]
      exact parent
    have kindsShifted : ∀ id loan, (before.world.RequestReturns (.resident shell.owner)).loans.get id = some loan → loan.live = true → loan.kind = .owning ∨ loan.kind = .storageBorrow := by
      intro id loan found live
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      rw [← same,World.restamp_live] at live
      rw [← same,World.restamp_kind]
      exact kinds id original originalFound live
    have ancestryShifted : ∀ id loan, (before.world.RequestReturns (.resident shell.owner)).loans.get id = some loan → (∀ parent, loan.parent = some parent → (before.world.RequestReturns (.resident shell.owner)).loans.get parent ≠ none) ∧ (∀ guard ∈ loan.guards, (before.world.RequestReturns (.resident shell.owner)).loans.get guard ≠ none) := by
      intro id loan found
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have linkOriginal : original.parent = some parent := by
          rw [← same,World.restamp_parent] at link
          exact link
        have held := (ancestry id original originalFound).1 parent linkOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
      · have memberOriginal : guard ∈ original.guards := by
          rw [← same,World.restamp_guards] at member
          exact member
        have held := (ancestry id original originalFound).2 guard memberOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
    have drainTask : mid.task = ReleaseCustodyLoans mid.world (.resident shell.owner) (.destroyFields context address authority rest next) := by
      rw [← midWorld] at midTask
      exact midTask
    have midLoans : mid.world.loans = (before.world.RequestReturns (.resident shell.owner)).loans := by
      rw [midWorld]
      rw [World.write_rest written]
    obtain ⟨drained,trace,drainedRun,frame⟩ :=
      CleanupRun.release_custody_returns (program := program) (host := host) (before := mid)
        (custody := .resident shell.owner) (next := .destroyFields context address authority rest next)
        drainTask
        (World.ReleaseReady.custody_of_storage
          (by intro id loan found live; rw [midLoans] at found; exact kindsShifted id loan found live)
          (by intro id loan found; rw [midLoans] at found; rw [midLoans]; exact ancestryShifted id loan found))
    obtain ⟨changed,changedStored,head,owner,type,live,resources,slotHole,others⟩ := World.Stores.write_child_none parentShifted written
    have changedAtMid : mid.world.Stores address changed := by
      rw [midWorld]
      exact changedStored
    exact ⟨_,{ mid with world := drained, task := .destroyFields context address authority rest next },changed,
      run.append drainedRun,rfl,World.Stores.loanReleaseFrame changedAtMid frame,
      head,owner,type,live,resources,slotHole,others⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- Ending one loan cannot break the destructor's owning-kind obligation: the
killed row is not live afterwards, every other row is untouched. -/
theorem World.Destroys.kinds_set_dead {world : World} {id : Identity} {loan : Loan}
    (_found : world.loans.get id = some loan)
    (kinds : ∀ key row, world.loans.get key = some row → row.live = true →
      row.kind = .owning ∨ row.kind = .storageBorrow) :
    ∀ key row, (world.loans.set id { loan with live := false }).get key = some row → row.live = true →
      row.kind = .owning ∨ row.kind = .storageBorrow := by
  intro key row selected live
  by_cases same : key = id
  · rw [same] at selected
    rw [Table.get_set world.loans id { loan with live := false }] at selected
    have rowEq : { loan with live := false } = row := Option.some.inj selected
    subst rowEq
    simp at live
  · have beforeFound : world.loans.get key = some row := by
      rwa [Table.get_set_other world.loans id key { loan with live := false } same] at selected
    exact kinds key row beforeFound live

/-- Ending one loan cannot break the destructor's ancestry obligation either: the
killed row survives in the table, so every parent and guard row is still named. -/
theorem World.Destroys.ancestry_set_dead {world : World} {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan)
    (ancestry : ∀ key row, world.loans.get key = some row →
      (∀ parent, row.parent = some parent → world.loans.get parent ≠ none) ∧
      (∀ guard ∈ row.guards, world.loans.get guard ≠ none)) :
    ∀ key row, (world.loans.set id { loan with live := false }).get key = some row →
      (∀ parent, row.parent = some parent →
        (world.loans.set id { loan with live := false }).get parent ≠ none) ∧
      (∀ guard ∈ row.guards, (world.loans.set id { loan with live := false }).get guard ≠ none) := by
  intro key row selected
  have beforeLookup : ∀ other, ((world.loans.set id { loan with live := false }).get other = none) →
      world.loans.get other = none := by
    intro other missing
    by_cases same : other = id
    · rw [same] at missing
      rw [Table.get_set world.loans id { loan with live := false }] at missing
      cases missing
    · rwa [Table.get_set_other world.loans id other { loan with live := false } same] at missing
  by_cases same : key = id
  · rw [same] at selected
    rw [Table.get_set world.loans id { loan with live := false }] at selected
    have rowEq : { loan with live := false } = row := Option.some.inj selected
    subst rowEq
    refine ⟨fun parent link => ?_,fun guard member => ?_⟩
    · exact (ancestry id loan found).1 parent link |>.imp (beforeLookup parent)
    · exact (ancestry id loan found).2 guard member |>.imp (beforeLookup guard)
  · have beforeFound : world.loans.get key = some row := by
      rwa [Table.get_set_other world.loans id key { loan with live := false } same] at selected
    refine ⟨fun parent link => ?_,fun guard member => ?_⟩
    · exact (ancestry key row beforeFound).1 parent link |>.imp (beforeLookup parent)
    · exact (ancestry key row beforeFound).2 guard member |>.imp (beforeLookup guard)

end Glorious.Language.Execution


namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- The ownership permission is monotone in the loan table: it needs a live row of
the produced world to be a live row of the admitted one, which is exactly what the
destructor's endings and writes give. -/
theorem Permitted.of_loans {world after : World} {requested : Access} {address : Address}
    (permission : Permitted world .owner requested address)
    (shrink : ∀ id loan, after.loans.get id = some loan → loan.live = true → world.loans.get id = some loan)
    (existence : ∃ root, after.root address = some root) :
    Permitted after .owner requested address :=
  ⟨existence,fun id loan found live overlap conflict =>
    permission.2 id loan (shrink id loan found live) live overlap conflict⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- The ownership permission survives the custody's pending-return restamp: the
restamp rewrites the loan table only, and a restamped row keeps the live flag,
referent and mode the permission's obligation is about, with the root existence
re-read at the restamped world. -/
theorem Permitted.of_requestReturns {world : World} {custody : ClaimCustody} {requested : Access}
    {address : Address} (permission : Permitted world .owner requested address)
    (existence : ∃ root, (world.RequestReturns custody).root address = some root) :
    Permitted (world.RequestReturns custody) .owner requested address :=
  ⟨existence,fun id loan found live overlap conflict => by
    rw [World.RequestReturns.get_eq] at found
    obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
    rw [← same,World.restamp_live] at live
    rw [← same,World.restamp_referent] at overlap
    rw [← same,World.restamp_mode] at conflict
    exact permission.2 id original originalFound live overlap conflict⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- Reversing a duplicate-free list keeps it duplicate-free. This core has no
such lemma, and the destructor's schedule is the reverse of `List.range`, so it is
established here once. -/
theorem List.Nodup.reverse {α : Type} {l : List α} (nodup : l.Nodup) : l.reverse.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      rw [List.nodup_cons] at nodup
      rw [List.reverse_cons, List.nodup_append]
      refine ⟨ih nodup.2,by simp,?_⟩
      intro a member b memberHead same
      rw [List.mem_singleton] at memberHead
      subst memberHead
      subst same
      exact nodup.1 (by simpa using member)

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- The custody's pending-return wrapper is the identity when that custody has no
live, return-requested storage borrow: the queue it folds over is empty, so the
bare continuation is reached without a step. -/
theorem CleanupRun.release_custody_none {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {custody : ClaimCustody} {next : Task}
    (task : before.task = ReleaseCustodyLoans before.world custody next)
    (none : before.world.loans.filterMap (fun entry =>
      if entry.2.live && entry.2.kind == .storageBorrow && entry.2.returnRequested &&
        entry.2.custody == some custody then some entry.1 else none) = []) :
    ∃ trace after, CleanupRun program host before trace after ∧ after.task = next := by
  have frozen : before.task = next := by
    rw [task]
    unfold ReleaseCustodyLoans ReleaseLoans
    rw [none]
    rfl
  exact ⟨[], before, .refl, frozen⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- A node's destruction, with the children supplied as runs. -/
theorem CleanupRun.destroy_node {program : Kernel.Program} {host : Foreign.Model}
    {context : Context} {before : State} {address : Address} {next : Task} {value : Value}
    (task : before.task = .destroy context address .owner next)
    (tree : World.Destroys program before.world address)
    (stored : before.world.Stores address value)
    (permission : Permitted before.world .owner .owned address)
    (handed : before.world.CustodyHandedOff (.resident value.owner))
    (childStep : ∀ (field : Nat) (rest : List Nat) (state : State) {parent : Value},
      state.task = .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) →
      state.world.Stores address parent →
      (permission : Permitted state.world .owner .owned address) →
      (handed : state.world.CustodyHandedOff (.resident parent.owner)) →
      (kinds : ∀ id loan, state.world.loans.get id = some loan → loan.live = true →
        loan.kind = .owning ∨ loan.kind = .storageBorrow) →
      (ancestry : ∀ id loan, state.world.loans.get id = some loan →
        (∀ parent, loan.parent = some parent → state.world.loans.get parent ≠ none) ∧
        (∀ guard ∈ loan.guards, state.world.loans.get guard ≠ none)) →
      ∃ after parent', CleanupRun program host state [] after ∧
        after.task = .destroyFields context address .owner rest next ∧
        after.world.Stores address parent' ∧ parent'.fields[field]? = some none ∧
        (∀ other, other ≠ field → parent'.fields[other]? = parent.fields[other]?) ∧
        parent'.owner = parent.owner ∧ parent'.head = parent.head ∧ parent'.type = parent.type ∧
        parent'.shellLive = parent.shellLive ∧ parent'.resources = parent.resources ∧
        parent'.fields.length = parent.fields.length ∧
        Permitted after.world .owner .owned address ∧
        after.world.CustodyHandedOff (.resident parent.owner) ∧
        (∀ id loan, after.world.loans.get id = some loan → loan.live = true →
          loan.kind = .owning ∨ loan.kind = .storageBorrow) ∧
        (∀ id loan, after.world.loans.get id = some loan →
          (∀ parent, loan.parent = some parent → after.world.loans.get parent ≠ none) ∧
          (∀ guard ∈ loan.guards, after.world.loans.get guard ≠ none)) ∧
        (∀ other ∈ rest, after.world.Vacant (address.child other))) :
    ∃ trace after, CleanupRun program host before trace after ∧ after.task = next := by
  cases tree with
  | resident treeStored disposable shellLive noContinuation noReference noAvailable _ kinds ancestry children =>
    have valueEq : value = _ := Option.some.inj (stored.symm.trans treeStored)
    have structural : Step program host before none
        { before with task := .destroyFields context address .owner ((List.range value.fields.length).reverse) next } :=
      Or.inl (LocalStep.destroyStructural task stored (by simpa only [valueEq] using disposable) permission
        (Or.inl (by simpa only [← valueEq] using shellLive))
        (by simpa only [← valueEq] using noContinuation) (by simpa only [← valueEq] using noReference)
        (by simpa only [← valueEq] using noAvailable))
    obtain ⟨_, midState, midParent, fieldsRun, midTask, midStored, holes, untouched, ownerEq, headEq, typeEq, liveEq, resEq, lenEq, midPermission, midHanded, midKinds, midAncestry⟩ :=
      CleanupRun.destroy_fields_tree (program := program) (host := host) (context := context) (address := address)
        (indices := (List.range value.fields.length).reverse) (next := next) childStep
        { before with task := .destroyFields context address .owner ((List.range value.fields.length).reverse) next }
        value (by rfl) (List.Nodup.reverse List.nodup_range) stored permission handed kinds ancestry
    have midCustody : midState.world.CustodyHandedOff (.resident midParent.owner) := by
      rw [ownerEq]
      exact midHanded
    have midHoles : ∀ index, index < midParent.fields.length → midParent.fields[index]? = some none := by
      intro index bound
      have inRange : index ∈ List.range value.fields.length := by
        rw [List.mem_range, ← lenEq]
        exact bound
      exact holes index (by simpa only [List.mem_reverse] using inRange)
    obtain ⟨clearedShell, written⟩ := World.Stores.requestReturns_write_exists midStored (.resident midParent.owner)
    let released : State := { midState with world := clearedShell, task := ReleaseCustodyLoans clearedShell (.resident midParent.owner) next }
    have finishRun : CleanupRun program host midState [.destroy address midParent.owner] released :=
      CleanupRun.shell_done (value := midParent) (after := clearedShell) midTask midStored (List.eq_none_of_getElem? midHoles) midPermission midCustody written
    have afterWrite : released.world.loans = (midState.world.RequestReturns (.resident midParent.owner)).loans := by
      obtain ⟨root,replacement,found,shape⟩ := World.write_value_update written
      show clearedShell.loans = _
      rw [shape]
    have restampKinds : ∀ id loan, (midState.world.RequestReturns (.resident midParent.owner)).loans.get id = some loan →
        loan.live = true → loan.kind = .owning ∨ loan.kind = .storageBorrow := by
      intro id loan found live
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      rw [← same,World.restamp_live] at live
      rw [← same,World.restamp_kind]
      exact midKinds id original originalFound live
    have restampAncestry : ∀ id loan, (midState.world.RequestReturns (.resident midParent.owner)).loans.get id = some loan →
        (∀ parent, loan.parent = some parent →
          (midState.world.RequestReturns (.resident midParent.owner)).loans.get parent ≠ none) ∧
        (∀ guard ∈ loan.guards,
          (midState.world.RequestReturns (.resident midParent.owner)).loans.get guard ≠ none) := by
      intro id loan found
      rw [World.RequestReturns.get_eq] at found
      obtain ⟨original,originalFound,same⟩ := Option.map_eq_some_iff.mp found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have linkOriginal : original.parent = some parent := by
          rw [← same,World.restamp_parent] at link
          exact link
        have held := (midAncestry id original originalFound).1 parent linkOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
      · have memberOriginal : guard ∈ original.guards := by
          rw [← same,World.restamp_guards] at member
          exact member
        have held := (midAncestry id original originalFound).2 guard memberOriginal
        intro missing
        rw [World.RequestReturns.get_eq] at missing
        exact held (Option.map_eq_none_iff.mp missing)
    have drainTask : released.task = ReleaseCustodyLoans released.world (.resident midParent.owner) next := by
      show ({ midState with world := clearedShell, task := ReleaseCustodyLoans clearedShell (.resident midParent.owner) next } : State).task = ReleaseCustodyLoans clearedShell (.resident midParent.owner) next
      rfl
    have clearedKinds : ∀ id loan, released.world.loans.get id = some loan → loan.live = true →
        loan.kind = .owning ∨ loan.kind = .storageBorrow := by
      intro id loan found live
      exact restampKinds id loan (by rwa [afterWrite] at found) live
    have clearedAncestry : ∀ id loan, released.world.loans.get id = some loan →
        (∀ parent, loan.parent = some parent → released.world.loans.get parent ≠ none) ∧
        (∀ guard ∈ loan.guards, released.world.loans.get guard ≠ none) := by
      intro id loan found
      have bridged : (midState.world.RequestReturns (.resident midParent.owner)).loans.get id = some loan := by
        rwa [afterWrite] at found
      have held := restampAncestry id loan bridged
      rw [afterWrite]
      exact held
    obtain ⟨drained,trace,drainedRun,_⟩ :=
      CleanupRun.release_custody_returns (program := program) (host := host) (before := released)
        (custody := .resident midParent.owner) (next := next) drainTask
        (World.ReleaseReady.custody_of_storage clearedKinds clearedAncestry)
    exact ⟨_,{ released with world := drained, task := next },
      (.silent (by simp [Task.Cleanup,task]) structural (fieldsRun.append finishRun |>.append drainedRun)),rfl⟩

end Glorious.Language.Execution

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

end Glorious.Language.Execution
