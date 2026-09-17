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

/-- Requesting storage-borrow returns leaves owning rows unchanged, including
the successor that witnesses each custody handoff. -/
theorem World.CustodyHandedOff.requestReturns {world : World} {custody : ClaimCustody}
    (handed : world.CustodyHandedOff custody) (requested : ClaimCustody) :
    (world.RequestReturns requested).CustodyHandedOff custody := by
  intro id loan found live kind held
  rw [World.RequestReturns.get_eq] at found
  obtain ⟨original,selected,same⟩ := Option.map_eq_some_iff.mp found
  have originalKind : original.kind = .owning := by
    simpa only [← same,World.restamp_kind] using kind
  have unchanged : World.restamp requested original = original := by
    simp [World.restamp,originalKind]
  have equal : original = loan := unchanged.symm.trans same
  subst loan
  simp only [unchanged] at live held ⊢
  obtain ⟨child,successor,childFound,parent,active,owning,referent,recipient,recipientEq,different⟩ :=
    handed id original selected live originalKind held
  have successorUnchanged : World.restamp requested successor = successor := by
    simp [World.restamp,owning]
  refine ⟨child,successor,?_,parent,active,owning,referent,recipient,recipientEq,different⟩
  rw [World.RequestReturns.get_eq,childFound]
  exact congrArg some successorUnchanged

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
                have finish (notOwning : loan.kind ≠ .owning) (step : LocalStep program before (some (.loanEnd id))
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
                    Nat.le_trans counted (Nat.le_of_lt decreased),(World.loanReleaseFrame_set_dead found notOwning).trans frame⟩
                have ordinary (kind : loan.kind = .restoring ∨ loan.kind = .destructor) :
                    ∃ (after : World) (trace : List Event),
                      CleanupRun program host before trace { before with world := after, task := next } ∧
                        after.liveCount ≤ before.world.liveCount ∧ before.world.LoanReleaseFrame after := by
                  obtain ⟨initialized,closed⟩ := ready.restored id (.seed (by simp)) loan found live kind
                  have ending : EndsLoan program before.world id ended :=
                    .restored found live kind initialized closed referenced resourced children
                  cases parent : loan.parent with
                  | none =>
                      apply finish (by rcases kind with kind | kind <;> simp [kind])
                      simpa only [pushed,parent,Option.toList_none,List.nil_append] using
                        (LocalStep.releaseRoot head found parent ending)
                  | some parentId =>
                      apply finish (by rcases kind with kind | kind <;> simp [kind])
                      simpa only [pushed,parent,Option.toList_some,List.singleton_append] using
                        (LocalStep.releaseChild head found parent ending)
                cases kind : loan.kind with
                | owning => exact silent (.releaseOwnedClaim head found kind)
                | restoring => exact ordinary (Or.inl kind)
                | destructor => exact ordinary (Or.inr kind)
                | storageBorrow =>
                    by_cases requested : loan.returnRequested = true
                    · exact finish (by simp [kind]) (.releaseStorageReturned head found
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
its own address, the custody hand-off its relinquishment must preserve, and the
whole-table loan kind/ancestry admission its endings and drain read) whose fields
are each either a hole or a further destructible resident. The custody clause is
the pre-state admission of the node's own owner: no tree can derive it, because
the owning successor that witnesses it lives outside the destroyed subtree. -/
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
      world.CustodyHandedOff (.resident value.owner) →
      (∀ (index : Nat) (child : Value), value.fields[index]? = some (some child) →
        World.Destroys program world (address.child index)) →
      World.Destroys program world address

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A loan-table equality transports a custody hand-off: only the witness lookup
moves. This is the write case of every custody transport below. -/
theorem World.CustodyHandedOff.of_loans {before after : World} {custody : ClaimCustody}
    (handed : before.CustodyHandedOff custody) (same : after.loans = before.loans) :
    after.CustodyHandedOff custody := by
  intro identity loan found live kind held
  rw [same] at found
  simpa only [same] using handed identity loan found live kind held

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
  | @resident address value stored disposable shell noCont noRef noAvail permission kinds ancestry custody children ih =>
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
    refine .resident storedAfter disposable shell noCont noRef noAvail permissionAfter ?_ ?_ ?_ ?_
    · intro id loan found live
      exact kinds id loan (by simpa only [loansAfter] using found) live
    · intro id loan found
      refine ⟨fun parent link => ?_,fun guard member => ?_⟩
      · have held := (ancestry id loan (by simpa only [loansAfter] using found)).1 parent link
        simpa only [loansAfter] using held
      · have held := (ancestry id loan (by simpa only [loansAfter] using found)).2 guard member
        simpa only [loansAfter] using held
    · exact World.CustodyHandedOff.of_loans custody loansAfter
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

/-- Ending a row that is not an owning claim preserves the custody hand-off: every
successor witness is a live owning row, so the killed row is not one of them and
every other row keeps its parent, referent and custodian. -/
theorem World.CustodyHandedOff.set_dead {world : World} {custody : ClaimCustody} {id : Identity} {loan : Loan}
    (handed : world.CustodyHandedOff custody) (found : world.loans.get id = some loan)
    (notOwning : loan.kind ≠ .owning) :
    ({ world with loans := world.loans.set id { loan with live := false } }).CustodyHandedOff custody := by
  intro identity current selected live kind held
  have different : identity ≠ id := by
    intro same
    subst identity
    have equal : ({ loan with live := false } : Loan) = current :=
      Option.some.inj ((Table.get_set world.loans id { loan with live := false }).symm.trans selected)
    apply notOwning
    simpa only [← equal] using kind
  have previous : world.loans.get identity = some current := by
    rw [Table.get_set_other world.loans id identity { loan with live := false } different] at selected
    exact selected
  obtain ⟨child, successor, childFound, parent, active, owning, referent, recipient, recipientEq, recipientNe⟩ :=
    handed identity current previous live kind held
  have successorDifferent : child ≠ id := by
    intro same
    subst child
    have equal : successor = loan := Option.some.inj (childFound.symm.trans found)
    exact notOwning (equal ▸ owning)
  refine ⟨child, successor, ?_, parent, active, owning, referent, recipient, recipientEq, recipientNe⟩
  rw [Table.get_set_other world.loans id child { loan with live := false } successorDifferent]
  exact childFound

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Ending one loan leaves a destructible resident destructible: the ending only
kills a row, so the owning permission's exclusion and the pending-return clauses,
both read from the raw loan table, still hold. -/
theorem World.Destroys.end_loan {program : RuntimeProgram} {world : World} {address : Address}
    (tree : World.Destroys program world address) {id : Identity} {loan : Loan}
    (found : world.loans.get id = some loan) (notOwning : loan.kind ≠ .owning) :
    World.Destroys program { world with loans := world.loans.set id { loan with live := false } } address := by
  revert found
  induction tree with
  | @resident addr value stored disposable shell noCont noRef noAvail permission kinds ancestry custody children ih =>
    intro found
    have kept {key : Identity} {row : Loan} (different : key ≠ id)
        (selected : (world.loans.set id { loan with live := false }).get key = some row) :
        world.loans.get key = some row := by
      rw [Table.get_set_other _ _ _ _ different] at selected
      exact selected
    refine .resident stored disposable shell noCont noRef noAvail ?_ ?_ ?_ ?_ ?_
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
    · exact World.CustodyHandedOff.set_dead custody found notOwning
    · intro index child selected
      exact ih index child selected found

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A replacement at a non-empty path keeps the resident's owner, type, head,
liveness flag, resources and arity and changes only the first slot's subtree.
This is the value-level fact every write below a cell needs. -/
theorem Value.replace_shape {before after : Value} {first : Nat} {rest : List Nat} {replacement : Option Value}
    (written : before.replace (first :: rest) replacement = some after) :
    after.owner = before.owner ∧ after.type = before.type ∧ after.head = before.head ∧
      after.shellLive = before.shellLive ∧ after.resources = before.resources ∧
      after.fields.length = before.fields.length ∧
      (∀ other, other ≠ first → after.fields[other]? = before.fields[other]?) := by
  obtain ⟨field, found, shape⟩ := Value.replace_cons_shape written
  obtain ⟨choice, afterEq⟩ : ∃ choice, after = before.withFields (before.fields.set first choice) := by
    rcases shape with ⟨_, same⟩ | ⟨child, changed, _, _, same⟩
    · exact ⟨replacement, same⟩
    · exact ⟨some changed, same⟩
  subst afterEq
  dsimp only [Value.withFields, Value.fields] at *
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · rw [List.length_set]
  · intro other different
    rw [List.getElem?_set_ne (Ne.symm different)]

/-- A write anywhere inside a cell's slot subtree re-reads the cell as its old
shell with that subtree replaced. This is the general form of
`World.Stores.write_child_none`'s derivation, for an arbitrary path. -/
theorem World.Stores.write_below {before after : World} {cell target : Address} {first : Nat} {rest : List Nat}
    {replacement : Option Value}
    (rootEq : target.root = cell.root) (genEq : target.generation = cell.generation)
    (fieldsEq : target.fields = cell.fields ++ (first :: rest))
    (written : before.write target replacement = some after) :
    ∃ shell changed, before.Stores cell shell ∧ shell.replace (first :: rest) replacement = some changed ∧
      after.Stores cell changed := by
  have addressEq : target = { cell with fields := cell.fields ++ (first :: rest) } := by
    cases target with
    | mk targetRoot targetGeneration targetFields =>
      cases cell with
      | mk cellRoot cellGeneration cellFields =>
        simp only [Address.mk.injEq]
        exact ⟨rootEq, genEq, fieldsEq⟩
  rw [addressEq] at written
  unfold World.write at written
  cases selected : before.root { cell with fields := cell.fields ++ (first :: rest) } with
  | none => simp [selected] at written
  | some root =>
      have cellRoot : before.root cell = some root := selected
      have fieldsNonempty :
          ({ cell with fields := cell.fields ++ (first :: rest) } : Address).fields.isEmpty = false := by simp
      simp only [selected,fieldsNonempty,Bool.false_eq_true,↓reduceIte] at written
      dsimp at written
      cases resident : root.value with
      | none => simp [resident] at written
      | some whole =>
          simp only [resident] at written
          dsimp at written
          cases replaced : whole.replace (cell.fields ++ (first :: rest)) replacement with
          | none => simp [replaced] at written
          | some changed =>
              have result : after = { before with roots := before.roots.set cell.root { root with value := some changed } } := by
                simpa [replaced] using written.symm
              obtain ⟨shell,newCell,located,rewritten,outer⟩ := Value.replace_append_shape replaced (by simp)
              have writeEq : before.write cell (some newCell) = some after := by
                rw [result]
                simp only [World.write,cellRoot]
                dsimp
                split
                next emptyPath =>
                  have pathEq : cell.fields = [] := List.isEmpty_iff.mp emptyPath
                  have changedEq : changed = newCell := by simpa [pathEq,Value.replace] using outer.symm
                  rw [changedEq]
                next => simp [resident, outer]
              refine ⟨shell,newCell,?_,rewritten,?_⟩
              · simp [World.Stores,World.read,cellRoot,resident,located]
              · change after.read cell = some newCell
                simpa [Value.atPath] using World.write_read_inside writeEq []

/-- Destruction preserves reads at non-overlapping addresses. Ancestor reads
may change when a descendant slot is cleared; root presence is unchanged
everywhere. Loan rows remain present, live output rows retain their original
kind, mode and referent, and every custody hand-off of the input world is
carried to the output world. -/
structure World.DestroyFrame (before after : World) (outside : Address) : Prop where
  reads : ∀ probe, ¬ outside.Overlaps probe → after.read probe = before.read probe
  roots : ∀ probe, (after.root probe).isSome = (before.root probe).isSome
  rows : ∀ key row, after.loans.get key = some row → ∃ original, before.loans.get key = some original ∧
    original.parent = row.parent ∧ original.guards = row.guards
  present : ∀ key original, before.loans.get key = some original → ∃ row, after.loans.get key = some row
  liveness : ∀ key row, after.loans.get key = some row → row.live = true →
    ∃ original, before.loans.get key = some original ∧ original.live = true ∧
      original.kind = row.kind ∧ original.mode = row.mode ∧ original.referent = row.referent
  custody : ∀ custody, before.CustodyHandedOff custody → after.CustodyHandedOff custody
  /-- Every ancestor cell of the sphere re-reads with only the sphere's own slot
  subtree replaced: a run that changes only inside `outside`'s subtree cannot
  touch an ancestor's head data, arity or other slots. This is what carries the
  pending original child inventories past a sibling's destruction. -/
  ancestor : ∀ (cell : Address) (first : Nat) (rest : List Nat) (shell : Value),
      outside = { cell with fields := cell.fields ++ (first :: rest) } → before.Stores cell shell →
      ∃ changed, after.Stores cell changed ∧
        changed.owner = shell.owner ∧ changed.type = shell.type ∧ changed.head = shell.head ∧
        changed.shellLive = shell.shellLive ∧ changed.resources = shell.resources ∧
        changed.fields.length = shell.fields.length ∧
        (∀ other, other ≠ first → changed.fields[other]? = shell.fields[other]?)

/-- The identity frame: no destruction, no change. -/
theorem World.DestroyFrame.refl (world : World) (outside : Address) :
    World.DestroyFrame world world outside where
  reads := fun _ _ => rfl
  roots := fun _ => rfl
  rows := fun _ row found => ⟨row,found,rfl,rfl⟩
  present := fun _ original found => ⟨original,found⟩
  liveness := fun _ row found live => ⟨row,found,live,rfl,rfl,rfl⟩
  custody := fun _ handed => handed
  ancestor := fun _ _ _ shell _ stored =>
    ⟨shell,stored,rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl⟩

/-- A frame indexed on an inner sphere is a frame on any outer address that
contains it: fewer probes are excluded, and an ancestor of the outer sphere is an
ancestor of the inner one at a longer path. -/
theorem World.DestroyFrame.inside {before after : World} {inner outer : Address}
    (frame : World.DestroyFrame before after inner) (included : outer.Prefix inner) :
    World.DestroyFrame before after outer where
  reads := fun probe apart => frame.reads probe (by
    intro overlap
    apply apart
    refine ⟨included.1.trans overlap.1, included.2.1.trans overlap.2.1, ?_⟩
    obtain ⟨suffix, suffixEq⟩ := included.2.2
    rcases overlap.2.2 with ⟨more, shape⟩ | ⟨more, shape⟩
    · have split : outer.fields ++ suffix = probe.fields ++ more := by rw [← suffixEq]; exact shape
      rcases List.append_eq_append_iff.mp split with ⟨gap, outerEq, _⟩ | ⟨gap, probeEq, _⟩
      · exact Or.inr ⟨gap, outerEq⟩
      · exact Or.inl ⟨gap, probeEq⟩
    · have fieldsEq : probe.fields = outer.fields ++ (suffix ++ more) := by
        rw [shape, suffixEq, List.append_assoc]
      exact Or.inr ⟨suffix ++ more, fieldsEq⟩)
  roots := frame.roots
  rows := frame.rows
  present := frame.present
  liveness := frame.liveness
  custody := frame.custody
  ancestor := fun cell first rest shell outsideEq stored => by
    obtain ⟨suffix, suffixEq⟩ := included.2.2
    have innerShape : inner.fields = cell.fields ++ (first :: (rest ++ suffix)) := by
      rw [suffixEq, outsideEq]
      simp [List.append_assoc, List.cons_append]
    have innerRoot : inner.root = cell.root := by rw [← included.1, outsideEq]
    have innerGeneration : inner.generation = cell.generation := by rw [← included.2.1, outsideEq]
    have addrEq : inner = { cell with fields := cell.fields ++ (first :: (rest ++ suffix)) } := by
      cases inner with
      | mk innerRoot' innerGeneration' innerFields' =>
        cases cell with
        | mk cellRoot' cellGeneration' cellFields' =>
          simp only [Address.mk.injEq]
          exact ⟨innerRoot, innerGeneration, innerShape⟩
    obtain ⟨changed, changedStored, ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩ :=
      frame.ancestor cell first (rest ++ suffix) shell addrEq stored
    exact ⟨changed, changedStored, ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩

/-- The destructor's field schedule for a shell: the reverse index range. -/
def World.schedule (value : Value) : List Nat := (List.range value.fields.length).reverse

theorem World.mem_schedule {value : Value} {field : Nat} :
    field ∈ World.schedule value ↔ field < value.fields.length := by
  simp [World.schedule]

/-- A destruction frame transports the whole-table live-kind restriction. -/
theorem World.DestroyFrame.kinds {before after : World} {outside : Address}
    (frame : World.DestroyFrame before after outside)
    (kinds : ∀ id loan, before.loans.get id = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow) :
    ∀ id loan, after.loans.get id = some loan → loan.live = true →
      loan.kind = .owning ∨ loan.kind = .storageBorrow := by
  intro id loan found live
  obtain ⟨original, originalFound, originalLive, sameKind, _, _⟩ := frame.liveness id loan found live
  rw [← sameKind]
  exact kinds id original originalFound originalLive

/-- A destruction frame transports the ancestry obligation. -/
theorem World.DestroyFrame.ancestry {before after : World} {outside : Address}
    (frame : World.DestroyFrame before after outside)
    (ancestry : ∀ key row, before.loans.get key = some row →
      (∀ parent, row.parent = some parent → before.loans.get parent ≠ none) ∧
      (∀ guard ∈ row.guards, before.loans.get guard ≠ none)) :
    ∀ key row, after.loans.get key = some row →
      (∀ parent, row.parent = some parent → after.loans.get parent ≠ none) ∧
      (∀ guard ∈ row.guards, after.loans.get guard ≠ none) := by
  intro key row found
  obtain ⟨original, originalFound, sameParent, sameGuards⟩ := frame.rows key row found
  refine ⟨fun parent link => ?_, fun guard member => ?_⟩
  · have held := (ancestry key original originalFound).1 parent (by rw [sameParent]; exact link)
    intro missing
    obtain ⟨beforeRow, beforeFound⟩ := Option.ne_none_iff_exists'.mp held
    obtain ⟨afterRow, afterFound⟩ := frame.present parent beforeRow beforeFound
    rw [afterFound] at missing
    cases missing
  · have held := (ancestry key original originalFound).2 guard (by rw [sameGuards]; exact member)
    intro missing
    obtain ⟨beforeRow, beforeFound⟩ := Option.ne_none_iff_exists'.mp held
    obtain ⟨afterRow, afterFound⟩ := frame.present guard beforeRow beforeFound
    rw [afterFound] at missing
    cases missing

/-- A destruction frame transports the ownership permission at the sphere. -/
theorem World.DestroyFrame.permitted {before after : World} {outside : Address} {requested : Access}
    (frame : World.DestroyFrame before after outside)
    (permission : Permitted before .owner requested outside) :
    Permitted after .owner requested outside := by
  refine ⟨?_, ?_⟩
  · obtain ⟨root, rootFound⟩ := permission.1
    exact Option.isSome_iff_exists.mp (by simpa [rootFound] using frame.roots outside)
  · intro id loan found live overlap conflict
    obtain ⟨original, originalFound, originalLive, _, sameMode, sameReferent⟩ := frame.liveness id loan found live
    exact permission.2 id original originalFound originalLive (by simpa [sameReferent] using overlap)
      (by simpa [sameMode] using conflict)

/-- The parent cell's update produced by destroying the child at `cell.child index`:
the cell keeps its head data and every other slot, and the child's slot is a hole. -/
def World.CellUpdate (after : World) (cell : Address) (index : Nat) (shell changed : Value) : Prop :=
  after.Stores cell changed ∧ changed.fields[index]? = some none ∧
    changed.owner = shell.owner ∧ changed.type = shell.type ∧ changed.head = shell.head ∧
    changed.shellLive = shell.shellLive ∧ changed.resources = shell.resources ∧
    changed.fields.length = shell.fields.length ∧
    (∀ other, other ≠ index → changed.fields[other]? = shell.fields[other]?)

/-- A clear at one child slot re-reads the parent shell as the parent with that
slot a hole: the same shape `World.Stores.write_child_none` reports, stated as
the equality a caller can carry forward. -/
theorem World.Stores.write_child_none_eq {before after : World} {address : Address} {index : Nat}
    {shell : Value} (stored : before.Stores address shell)
    (written : before.write (address.child index) none = some after) :
    after.Stores address (Value.withFields shell (shell.fields.set index none)) := by
  obtain ⟨parent, slot, parentStored, slotFound, rewritten⟩ := World.write_child_shape written
  have same : parent = shell := Option.some.inj (parentStored.symm.trans stored)
  rw [same] at rewritten
  change after.read address = some (Value.withFields shell (shell.fields.set index none))
  simpa [Value.atPath] using World.write_read_inside rewritten []

/-- Splitting the last element off a list. This core has no such lemma and the
address decomposition below needs it. -/
theorem List.dropLast_append_getLast {α : Type} {l : List α} (h : l ≠ []) :
    l.dropLast ++ [l.getLast h] = l := by
  induction l with
  | nil => exact absurd rfl h
  | cons head tail ih =>
      cases tail with
      | nil => rfl
      | cons next rest =>
          have tailNe : (next :: rest) ≠ [] := by simp
          have step := ih tailNe
          show head :: ((next :: rest).dropLast ++ [(next :: rest).getLast tailNe]) = head :: next :: rest
          rw [step]

/-- Every address with a non-empty field list sits one step below its own prefix
parent. -/
theorem Address.exists_child {address : Address} (nonempty : address.fields ≠ []) :
    ∃ parent idx, address = Address.child parent idx := by
  have shape : address = Address.child { address with fields := address.fields.dropLast }
      (address.fields.getLast (by simpa using nonempty)) := by
    cases address with
    | mk root generation fields =>
      simp only [Address.child]
      rw [List.dropLast_append_getLast (by simpa using nonempty)]
  exact ⟨_, _, shape⟩

/-- Clearing an address with `none` makes it vacant. -/
theorem World.Vacant.of_write_none {before after : World} {address : Address}
    (written : before.write address none = some after) : after.Vacant address := by
  cases fieldsEq : address.fields with
  | nil =>
      unfold World.write at written
      cases selected : before.root address with
      | none => simp [selected] at written
      | some root =>
          have bound := World.root_found selected
          simp only [selected, fieldsEq, List.isEmpty_nil, ↓reduceIte] at written
          dsimp at written
          have afterEq : after = { before with roots := before.roots.set address.root { root with value := none } } :=
            (Option.some.inj written).symm
          refine ⟨{ root with value := none }, ?_, Or.inl ⟨fieldsEq, rfl⟩⟩
          rw [afterEq]
          simp only [World.root, Table.get_set]
          simp [bound.2.1, bound.2.2]
  | cons first rest =>
      obtain ⟨parent, idx, childEq⟩ := Address.exists_child (by rw [fieldsEq]; simp)
      rw [childEq] at written
      obtain ⟨parentShell, slot, parentStored, slotFound, rewritten⟩ := World.write_child_shape written
      have storedAfter := World.Stores.write_child_none_eq parentStored written
      have slotHole : (Value.withFields parentShell (parentShell.fields.set idx none)).fields[idx]? = some none := by
        rw [Value.withFields, Value.fields]
        exact List.getElem?_set_self (List.getElem?_eq_some_iff.mp slotFound).1
      have vacant := World.Stores.vacant_child storedAfter slotHole
      rwa [childEq]

/-- The drain moves loans only, so vacancy survives it. -/
theorem World.Vacant.loanReleaseFrame {before after : World} {address : Address}
    (vacant : before.Vacant address) (frame : before.LoanReleaseFrame after) : after.Vacant address := by
  rcases vacant with ⟨root, selected, shape⟩
  exact ⟨root, by rw [frame.rest]; exact selected, shape⟩

/-- A vacant child slot of a stored cell reads that cell's slot as a hole. -/
theorem World.Vacant.read_slot {world : World} {cell : Address} {index : Nat} {cellShell changed : Value}
    (vacant : world.Vacant (cell.child index)) (stored : world.Stores cell changed)
    (length : changed.fields.length = cellShell.fields.length)
    (slot : cellShell.fields[index]? ≠ none) :
    changed.fields[index]? = some none := by
  have readNone : world.read (cell.child index) = none := by
    cases readEq : world.read (cell.child index) with
    | none => rfl
    | some value => exact absurd ⟨value, readEq⟩ (World.Vacant.not_stored vacant)
  have readAppend : world.read (cell.child index) = (world.read cell) >>= fun value => value.atPath [index] :=
    World.read_append world cell [index]
  have cellRead : world.read cell = some changed := stored
  rw [readAppend, cellRead] at readNone
  simp [Value.atPath] at readNone
  cases slotEq : changed.fields[index]? with
  | none =>
      have le := List.getElem?_eq_none_iff.mp slotEq
      exact absurd (List.getElem?_eq_none_iff.mpr (by rwa [length] at le)) slot
  | some v =>
      rw [slotEq] at readNone
      simp at readNone
      rw [readNone]

/-- A subtree whose slots all lie outside a destruction frame's sphere keeps its
whole inventory in the produced world. -/
theorem World.Destroys.of_destroy_frame {program : RuntimeProgram} {before after : World}
    {address outside : Address} (tree : World.Destroys program before address)
    (frame : World.DestroyFrame before after outside)
    (excluded : ∀ probe, address.Prefix probe → ¬ outside.Overlaps probe) :
    World.Destroys program after address := by
  revert frame excluded
  induction tree with
  | @resident addr value stored disposable shell noCont noRef noAvail permission kinds ancestry custody children ih =>
    intro frame excluded
    have atRoot : ¬ outside.Overlaps addr := excluded addr ⟨rfl,rfl,⟨[],by simp⟩⟩
    have childExcluded (index : Nat) :
        ∀ probe, (addr.child index).Prefix probe → ¬ outside.Overlaps probe :=
      fun probe included => excluded probe
        (Address.Prefix.not_outer (Address.Prefix.child ⟨rfl,rfl,⟨[],by simp⟩⟩ index).1 included)
    refine .resident ?_ disposable shell noCont noRef noAvail ?_ ?_ ?_ ?_ ?_
    · show after.read addr = some value
      rw [frame.reads addr atRoot]
      exact stored
    · refine ⟨?_,fun key row selected live overlap conflict => ?_⟩
      · obtain ⟨root,rootFound⟩ := permission.1
        have same := frame.roots addr
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
    · exact frame.custody (.resident value.owner) custody
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
  roots := fun probe => (second.roots probe).trans (first.roots probe)
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
  custody := fun custody handed => second.custody custody (first.custody custody handed)
  ancestor := fun cell up rest shell outsideEq stored => by
    obtain ⟨middleShell, middleStored, ownerOne, typeOne, headOne, liveOne, resOne, lenOne, slotsOne⟩ :=
      first.ancestor cell up rest shell outsideEq stored
    obtain ⟨finalShell, finalStored, ownerTwo, typeTwo, headTwo, liveTwo, resTwo, lenTwo, slotsTwo⟩ :=
      second.ancestor cell up rest middleShell outsideEq middleStored
    exact ⟨finalShell, finalStored, ownerTwo.trans ownerOne, typeTwo.trans typeOne, headTwo.trans headOne,
      liveTwo.trans liveOne, resTwo.trans resOne, lenTwo.trans lenOne,
      fun other different => (slotsTwo other different).trans (slotsOne other different)⟩

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- A write whose target lies inside the frame's sphere leaves the frame: the
loan table is untouched, the resolved root is read from live and generation
(which the update keeps), and outside the sphere the read does not move. -/
theorem World.DestroyFrame.of_write {before after : World} {outside target : Address}
    {replacement : Option Value} (written : before.write target replacement = some after)
    (inside : outside.Prefix target) :
    World.DestroyFrame before after outside where
  reads := fun probe apart => World.write_disjoint written (by
    intro overlap
    apply apart
    rcases overlap.2.2 with above | below
    · have probeInside : probe.Prefix target :=
        ⟨overlap.1.symm,overlap.2.1.symm,above⟩
      rcases inside.comparable probeInside with first | second
      · exact first.overlaps
      · exact second.overlaps.symm
    · exact (inside.trans ⟨overlap.1,overlap.2.1,below⟩).overlaps)
  roots := fun probe => by
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
  custody := fun claimed handed => World.CustodyHandedOff.of_loans handed (by rw [World.write_rest written])
  ancestor := fun cell first rest shell outsideEq stored => by
    obtain ⟨more, moreEq⟩ := inside.2.2
    have rootEq : target.root = cell.root := by rw [← inside.1, outsideEq]
    have genEq : target.generation = cell.generation := by rw [← inside.2.1, outsideEq]
    have fieldsEq : target.fields = cell.fields ++ (first :: (rest ++ more)) := by
      rw [moreEq, outsideEq]
      simp [List.append_assoc, List.cons_append]
    obtain ⟨shell', changed, stored', replaced, afterStored⟩ :=
      World.Stores.write_below rootEq genEq fieldsEq written
    have shellSame : shell' = shell := Option.some.inj (stored'.symm.trans stored)
    rw [shellSame] at replaced
    obtain ⟨ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩ := Value.replace_shape replaced
    exact ⟨changed, afterStored, ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- The relinquishment restamp is a frame: it rewrites the loan table only,
keeping every row, its parent and guards, and the kind, mode and referent of
every live row, while the reads and the resolved roots do not move at all. -/
theorem World.DestroyFrame.of_requestReturns {before : World} {custody : ClaimCustody} {outside : Address} :
    World.DestroyFrame before (before.RequestReturns custody) outside where
  reads := fun probe outside' => rfl
  roots := fun probe => rfl
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
  custody := fun claimed handed => Execution.World.CustodyHandedOff.requestReturns handed custody
  ancestor := fun _ _ _ shell _ stored =>
    ⟨shell, stored, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

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
  | @resident address value stored disposable shell noCont noRef noAvail permission kinds ancestry treeCustody children ih =>
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
    refine .resident storedAfter disposable shell noCont noRef noAvail permissionAfter ?_ ?_ ?_ ?_
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
    · exact Execution.World.CustodyHandedOff.requestReturns treeCustody custody
    · intro index child selected
      exact ih index child selected

end Glorious.Language

namespace Glorious.Language

open Kernel

/-- Ending one loan is a frame: the row is kept with its parent and guards, the
killed row is not live afterwards so the live-row facts carry over, and neither
the reads nor the resolved roots move. -/
theorem World.DestroyFrame.of_kill {before : World} {id : Identity} {loan : Loan} {outside : Address}
    (found : before.loans.get id = some loan) (notOwning : loan.kind ≠ .owning) :
    World.DestroyFrame before { before with loans := before.loans.set id { loan with live := false } }
      outside where
  reads := fun probe outside' => rfl
  roots := fun probe => rfl
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
  custody := fun custody handed => World.CustodyHandedOff.set_dead handed found notOwning
  ancestor := fun _ _ _ shell _ stored =>
    ⟨shell, stored, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

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
    (holes : ∀ i, i < shell.fields.length → shell.fields[i]? = some none) :
    ∃ trace final changed, CleanupRun program host before trace final ∧
      final.task = .destroyFields context address authority rest next ∧
      final.world.Stores address changed ∧ changed.head = value.head ∧ changed.owner = value.owner ∧
      changed.type = value.type ∧ changed.shellLive = value.shellLive ∧ changed.resources = value.resources ∧
      changed.fields[index]? = some none ∧
      (∀ other, other ≠ index → changed.fields[other]? = value.fields[other]?) ∧
      ∀ custody, before.world.CustodyHandedOff custody → final.world.CustodyHandedOff custody := by
  cases tree with
  | resident treeStored treeDisposable treeShell treeNoContinuation treeNoReference treeNoAvailable permission kinds ancestry treeCustody children =>
    have valueEq : shell = _ := Option.some.inj (stored.symm.trans treeStored)
    have handed : before.world.CustodyHandedOff (.resident shell.owner) := by
      simpa only [← valueEq] using treeCustody
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
      head,owner,type,live,resources,slotHole,others,fun custody admitted => by
        have shifted := World.CustodyHandedOff.requestReturns admitted (.resident shell.owner)
        have atMid : mid.world.CustodyHandedOff custody := by
          have written : mid.world.loans = (before.world.RequestReturns (.resident shell.owner)).loans := by
            rw [midLoans]
          unfold World.CustodyHandedOff at shifted ⊢
          simpa only [written] using shifted
        exact atMid.loanReleaseFrame frame⟩

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
      ∃ trace after parent', CleanupRun program host state trace after ∧
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
          (∀ guard ∈ loan.guards, after.world.loans.get guard ≠ none))) :
    ∃ trace after, CleanupRun program host before trace after ∧ after.task = next := by
  cases tree with
  | resident treeStored disposable shellLive noContinuation noReference noAvailable _ kinds ancestry _ children =>
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

namespace Glorious.Language

open Kernel

/-- Release framing is destruction framing: the drain moves no read, no root and
no row identity, so every `World.DestroyFrame` obligation follows from the
after-to-before row origin `LoanReleaseFrame.origin`. -/
theorem World.LoanReleaseFrame.destroyFrame {before after : World} {outside : Address}
    (frame : before.LoanReleaseFrame after) : World.DestroyFrame before after outside where
  reads := fun _ _ => by rw [frame.rest]; rfl
  roots := fun _ => by rw [frame.rest]; rfl
  rows := fun key row found => by
    obtain ⟨original, originalFound, shape⟩ := frame.origin key row found
    have parentEq : original.parent = row.parent := by rcases shape with rfl | rfl <;> rfl
    have guardsEq : original.guards = row.guards := by rcases shape with rfl | rfl <;> rfl
    exact ⟨original, originalFound, parentEq, guardsEq⟩
  present := fun key original found => by
    obtain ⟨current, selected, _⟩ := frame.rows key original found
    exact ⟨current, selected⟩
  liveness := fun key row found live => by
    obtain ⟨original, originalFound, shape⟩ := frame.origin key row found
    refine ⟨original, originalFound, ?_, ?_, ?_, ?_⟩
    · rcases shape with rfl | rfl
      · exact live
      · cases live
    · rcases shape with rfl | rfl <;> rfl
    · rcases shape with rfl | rfl <;> rfl
    · rcases shape with rfl | rfl <;> rfl
  custody := fun claimed handed => World.CustodyHandedOff.loanReleaseFrame handed frame
  ancestor := fun cell first rest shell _ stored => by
    have readEq : after.read cell = before.read cell := by rw [frame.rest]; rfl
    exact ⟨shell, by simpa [World.Stores] using readEq.trans stored, rfl, rfl, rfl, rfl, rfl, rfl,
      fun _ _ => rfl⟩

/-- A probe apart from an address is apart from every descendant of it. -/
theorem Address.child_outside {address probe : Address} {index : Nat}
    (apart : ¬ address.Overlaps probe) : ¬ (address.child index).Overlaps probe := by
  intro overlap
  apply apart
  refine ⟨overlap.1, overlap.2.1, ?_⟩
  rcases overlap.2.2 with ⟨suffix, shape⟩ | ⟨suffix, shape⟩
  · have split : address.fields ++ [index] = probe.fields ++ suffix := by
      simpa only [Address.child] using shape
    rcases List.append_eq_append_iff.mp split with ⟨tail, headEq, _⟩ | ⟨tail, probeEq, _⟩
    · exact Or.inr ⟨tail, headEq⟩
    · exact Or.inl ⟨tail, probeEq⟩
  · have split : probe.fields = (address.fields ++ [index]) ++ suffix := by
      simpa only [Address.child] using shape
    exact Or.inr ⟨[index] ++ suffix, by rw [split, List.append_assoc]⟩

/-- A sibling child's stored subtree is apart from a destroyed child's sphere. -/
theorem World.Destroys.sibling_outside {address : Address} {other first : Nat} (different : other ≠ first) :
    ∀ probe, (address.child other).Prefix probe → ¬ (address.child first).Overlaps probe := by
  intro probe included overlap
  have both : (address.child first).Overlaps (address.child other) := by
    rcases overlap.2.2 with ⟨suffix, shape⟩ | ⟨suffix, shape⟩
    · have probeFirst : probe.Prefix (address.child first) :=
        ⟨overlap.1.symm, overlap.2.1.symm, ⟨suffix, shape⟩⟩
      exact (Address.Prefix.trans included probeFirst).overlaps.symm
    · have firstProbe : (address.child first).Prefix probe :=
        ⟨overlap.1, overlap.2.1, ⟨suffix, shape⟩⟩
      rcases Address.Prefix.comparable firstProbe included with left | right
      · exact left.overlaps
      · exact right.overlaps.symm
  exact Address.child_not_overlaps (Ne.symm different) both

/-- A write strictly inside one child's slot re-reads the parent cell as its old
shell whose child slot carries the write result. -/
theorem World.Stores.write_child_child {before after : World} {address : Address} {index inner : Nat}
    {parent child : Value} {replacement : Option Value}
    (stored : before.Stores address parent) (slot : parent.fields[index]? = some (some child))
    (written : before.write ((address.child index).child inner) replacement = some after) :
    ∃ child', after.Stores (address.child index) child' ∧
      after.Stores address (Value.withFields parent (parent.fields.set index (some child'))) := by
  obtain ⟨middle, slotMiddle, middleStored, slotFound, rewritten⟩ := World.write_child_shape written
  have same : middle = child := Option.some.inj (middleStored.symm.trans (World.Stores.child stored slot))
  rw [same] at rewritten
  obtain ⟨outer, slotOuter, outerStored, slotOuterFound, rewrittenOuter⟩ := World.write_child_shape rewritten
  have outerSame : outer = parent := Option.some.inj (outerStored.symm.trans stored)
  rw [outerSame] at rewrittenOuter
  refine ⟨Value.withFields child (child.fields.set inner replacement), ?_, ?_⟩
  · change after.read (address.child index) =
      some (Value.withFields child (child.fields.set inner replacement))
    simpa [Value.atPath] using World.write_read_inside rewritten []
  · change after.read address =
      some (Value.withFields parent (parent.fields.set index (some (Value.withFields child (child.fields.set inner replacement)))))
    simpa [Value.atPath] using World.write_read_inside rewrittenOuter []

/-- The pending child inventory of a field loop: every index still scheduled has
its own destructible tree at the current world, keyed on the value the node
started from. Indexing the inventory on that value rather than on the evolving
shell is what lets the measure be the original `Value` the schedule came from. -/
def World.FieldPending (program : RuntimeProgram) (address : Address) (value : Value)
    (world : World) (indices : List Nat) : Prop :=
  ∀ field ∈ indices, ∀ child, value.fields[field]? = some (some child) →
    World.Destroys program world (address.child field)

end Glorious.Language

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

namespace Glorious.Language.Execution

open Glorious.Language.Kernel

/-- The actual recursive structural destruction. From one admitted
`World.Destroys` inventory the machine runs the node's structural destruction, its
whole nested field schedule — each occupied child destroyed by its own such run,
each already-empty slot by the machine's own vacant step — then the shell clear
and the drain of the resident owner's pending returns, ending at the caller's
continuation with the node's address vacant and a destruction frame for its
sphere. The recursion is strong induction on the size of the actually stored
`Value`, so it terminates and no child run is assumed anywhere. -/
theorem CleanupRun.recursive_cleanup_correct {program : Kernel.Program} {host : Foreign.Model} :
    ∀ (bound : Nat) (before : State) (context : Context) (address : Address) (next : Task) (shell : Value),
      sizeOf shell ≤ bound →
      before.task = .destroy context address .owner next →
      before.world.Stores address shell →
      World.Destroys program before.world address →
      ∃ trace after, CleanupRun program host before trace { before with world := after, task := next } ∧
        after.Vacant address ∧ World.DestroyFrame before.world after address ∧
        (∀ (cell : Address) (index : Nat) (cellShell : Value), address = cell.child index →
          before.world.Stores cell cellShell →
          ∃ changed, World.CellUpdate after cell index cellShell changed) := by
  intro bound
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro before context address next shell boundLe task stored tree
    cases tree with
    | resident treeStored disposable shellDead noContinuation noReference noAvailable permission kinds ancestry treeCustody children =>
      have valueEq : shell = _ := Option.some.inj (stored.symm.trans treeStored)
      rw [← valueEq] at treeStored shellDead treeCustody children disposable noContinuation noReference noAvailable
      have loop : ∀ (remaining : List Nat) (w : World) (nodeShell : Value),
          remaining.Nodup →
          (∀ field ∈ remaining, field ∈ World.schedule shell) →
          w.Stores address nodeShell →
          nodeShell.fields.length = shell.fields.length →
          nodeShell.owner = shell.owner →
          (∀ field ∈ World.schedule shell, field ∉ remaining → nodeShell.fields[field]? = some none) →
          (∀ field ∈ remaining, nodeShell.fields[field]? = shell.fields[field]?) →
          World.FieldPending program address shell w remaining →
          World.DestroyFrame before.world w address →
          Permitted w .owner .owned address →
          w.CustodyHandedOff (.resident shell.owner) →
          (∀ id loan, w.loans.get id = some loan → loan.live = true →
            loan.kind = .owning ∨ loan.kind = .storageBorrow) →
          (∀ id loan, w.loans.get id = some loan →
            (∀ parent, loan.parent = some parent → w.loans.get parent ≠ none) ∧
            (∀ guard ∈ loan.guards, w.loans.get guard ≠ none)) →
          ∃ (trace : List Event) (after : World) (finalShell : Value),
            CleanupRun program host
              { before with world := w, task := .destroyFields context address .owner remaining next }
              trace { before with world := after, task := .finishShell address .owner next } ∧
            after.Stores address finalShell ∧
            (∀ field ∈ World.schedule shell, finalShell.fields[field]? = some none) ∧
            finalShell.fields.length = shell.fields.length ∧
            finalShell.owner = shell.owner ∧
            World.DestroyFrame before.world after address ∧
            Permitted after .owner .owned address ∧
            after.CustodyHandedOff (.resident shell.owner) ∧
            (∀ id loan, after.loans.get id = some loan → loan.live = true →
              loan.kind = .owning ∨ loan.kind = .storageBorrow) ∧
            (∀ id loan, after.loans.get id = some loan →
              (∀ parent, loan.parent = some parent → after.loans.get parent ≠ none) ∧
              (∀ guard ∈ loan.guards, after.loans.get guard ≠ none)) := by
        intro remaining
        induction remaining with
        | nil =>
          intro w nodeShell nodup subset shellStored lenEq ownerEq holes untouched pending frame perm custody kinds ancestry
          exact ⟨[], w, nodeShell, CleanupRun.fields_done rfl, shellStored,
            (fun field member => holes field member (by simp)),
            lenEq, ownerEq, frame, perm, custody, kinds, ancestry⟩
        | cons field rest inner =>
          intro w nodeShell nodup subset shellStored lenEq ownerEq holes untouched pending frame perm custody kinds ancestry
          have inHead : field ∈ (field :: rest : List Nat) := List.mem_cons_self ..
          have split := List.nodup_cons.mp nodup
          have fieldNotRest : field ∉ rest := split.1
          have restNodup : rest.Nodup := split.2
          have headStep : CleanupRun program host
              { before with world := w, task := .destroyFields context address .owner (field :: rest) next }
              []
              { before with world := w, task := .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) } :=
            .silent (by simp [Task.Cleanup]) (Or.inl (LocalStep.fieldNext rfl)) .refl
          by_cases occupied : ∃ child, nodeShell.fields[field]? = some (some child)
          · obtain ⟨child, slotValue⟩ := occupied
            have shellSlot : shell.fields[field]? = some (some child) := by
              rw [← untouched field inHead]
              exact slotValue
            have childStored : w.Stores (address.child field) child := World.Stores.child shellStored slotValue
            have childTree : World.Destroys program w (address.child field) := pending field inHead child shellSlot
            have sizeSmaller : sizeOf child < sizeOf shell :=
              Value.field_sizeOf (List.mem_iff_getElem?.mpr ⟨field, shellSlot⟩)
            have sizeBound : sizeOf child < bound := Nat.lt_of_lt_of_le sizeSmaller boundLe
            obtain ⟨trace, after, run, _childVacant, childFrame, cellBundle⟩ :=
              ih (sizeOf child) sizeBound
                { before with world := w, task := .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) }
                context (address.child field) (.destroyFields context address .owner rest next) child (Nat.le_refl _) rfl
                childStored childTree
            obtain ⟨changed, changedStored, changedSlot, ownerKeep, typeKeep, headKeep, liveKeep, resKeep, lenKeep, slotsKeep⟩ :=
              cellBundle address field nodeShell rfl shellStored
            have widened : World.DestroyFrame w after address :=
              childFrame.inside ⟨rfl, rfl, ⟨[field], rfl⟩⟩
            have holesNext : ∀ other ∈ World.schedule shell, other ∉ rest → changed.fields[other]? = some none := by
              intro other otherSched otherNotRest
              by_cases sameField : other = field
              · subst sameField
                exact changedSlot
              · rw [slotsKeep other sameField]
                exact holes other otherSched (by
                  intro member
                  rcases List.mem_cons.mp member with equal | member
                  · exact sameField equal
                  · exact otherNotRest member)
            have untouchedNext : ∀ other ∈ rest, changed.fields[other]? = shell.fields[other]? := by
              intro other otherRest
              have different : other ≠ field := by
                intro same
                subst same
                exact fieldNotRest otherRest
              rw [slotsKeep other different]
              exact untouched other (List.mem_cons_of_mem field otherRest)
            have pendingNext : World.FieldPending program address shell after rest := by
              intro other otherRest child' childSlot
              exact World.Destroys.of_destroy_frame (pending other (List.mem_cons_of_mem field otherRest) child' childSlot)
                childFrame (World.Destroys.sibling_outside (address := address) (other := other) (first := field) (by
                  intro same
                  exact fieldNotRest (same ▸ otherRest)))
            obtain ⟨trace2, after2, finalShell, restRun, finalStored, finalHoles, finalLen, finalOwner, finalFrame, finalPerm, finalCustody, finalKinds, finalAncestry⟩ :=
              inner after changed restNodup (fun other otherRest => subset other (List.mem_cons_of_mem field otherRest))
                changedStored (lenKeep.trans lenEq) (ownerKeep.trans ownerEq) holesNext untouchedNext pendingNext
                (frame.trans widened) (widened.permitted perm) (widened.custody (.resident shell.owner) custody)
                (widened.kinds kinds) (widened.ancestry ancestry)
            exact ⟨trace ++ trace2, after2, finalShell, (headStep.append run).append restRun, finalStored, finalHoles,
              finalLen, finalOwner, finalFrame, finalPerm, finalCustody, finalKinds, finalAncestry⟩
          · have boundField : field < nodeShell.fields.length := by
              rw [lenEq]
              exact World.mem_schedule.mp (subset field inHead)
            obtain ⟨slotValue, slotFound⟩ : ∃ x, nodeShell.fields[field]? = some x :=
              ⟨nodeShell.fields[field], List.getElem?_eq_getElem boundField⟩
            have slotNone : slotValue = none := by
              cases slotValue with
              | none => rfl
              | some childValue => exact absurd ⟨childValue, slotFound⟩ occupied
            have shellHole : shell.fields[field]? = some none := by
              rw [← untouched field inHead, slotFound, slotNone]
            have vacant : w.Vacant (address.child field) :=
              World.Stores.vacant_child shellStored (by rw [slotFound, slotNone])
            have vacantRun : CleanupRun program host
                { before with world := w, task := .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) }
                [] { before with world := w, task := .destroyFields context address .owner rest next } :=
              CleanupRun.destroy_vacant rfl vacant
            obtain ⟨trace2, after2, finalShell, restRun, finalStored, finalHoles, finalLen, finalOwner, finalFrame, finalPerm, finalCustody, finalKinds, finalAncestry⟩ :=
              inner w nodeShell restNodup (fun other otherRest => subset other (List.mem_cons_of_mem field otherRest))
                shellStored lenEq ownerEq
                (by
                  intro other otherSched otherNotRest
                  by_cases sameField : other = field
                  · subst sameField
                    rw [slotFound, slotNone]
                  · rw [holes other otherSched (by
                      intro member
                      rcases List.mem_cons.mp member with equal | member
                      · exact sameField equal
                      · exact otherNotRest member)])
                (fun other otherRest => untouched other (List.mem_cons_of_mem field otherRest))
                (fun other otherRest child' childSlot => pending other (List.mem_cons_of_mem field otherRest) child' childSlot)
                frame perm custody kinds ancestry
            exact ⟨trace2, after2, finalShell, (headStep.append vacantRun).append restRun, finalStored, finalHoles,
              finalLen, finalOwner, finalFrame, finalPerm, finalCustody, finalKinds, finalAncestry⟩
      have started : CleanupRun program host before []
          { before with task := .destroyFields context address .owner (World.schedule shell) next } :=
        .silent (by simp [Task.Cleanup,task])
          (Or.inl (LocalStep.destroyStructural task stored disposable permission (Or.inl shellDead)
            noContinuation noReference noAvailable)) .refl
      obtain ⟨trace, afterFields, finalShell, fieldsRun, finalStored, finalHoles, finalLen, finalOwner, frameFields, permFields, custodyFields, kindsFields, ancestryFields⟩ :=
        loop (World.schedule shell) before.world shell
          (List.Nodup.reverse List.nodup_range) (fun _ member => member) stored rfl rfl
          (fun _ member notMember => absurd member notMember)
          (fun _ _ => rfl)
          (fun field member child slot => children field child slot)
          (World.DestroyFrame.refl before.world address) permission treeCustody kinds ancestry
      have allHoles : ∀ item ∈ finalShell.fields, item = none :=
        List.eq_none_of_getElem? (fun index bound => by
          refine finalHoles index ?_
          rw [World.mem_schedule, ← finalLen]
          exact bound)
      obtain ⟨cleared, written⟩ := World.Stores.requestReturns_write_exists finalStored (.resident finalShell.owner)
      have handed : afterFields.CustodyHandedOff (.resident finalShell.owner) := by
        rw [finalOwner]
        exact custodyFields
      have shellStep : Step program host
          { before with world := afterFields, task := .finishShell address .owner next } (some (.destroy address finalShell.owner))
          { before with world := cleared, task := ReleaseCustodyLoans cleared (.resident finalShell.owner) next } :=
        Or.inl (LocalStep.shellDone rfl finalStored allHoles permFields (RelinquishesCustody.of_handedOff handed) written)
      have afterWrite : cleared.loans = (afterFields.RequestReturns (.resident finalShell.owner)).loans := by
        obtain ⟨root, replacement, found, shape⟩ := World.write_value_update written
        show cleared.loans = _
        rw [shape]
      have clearedKinds : ∀ id loan, cleared.loans.get id = some loan → loan.live = true →
          loan.kind = .owning ∨ loan.kind = .storageBorrow := by
        intro id loan found live
        have bridged : (afterFields.RequestReturns (.resident finalShell.owner)).loans.get id = some loan := by
          rwa [afterWrite] at found
        rw [World.RequestReturns.get_eq] at bridged
        obtain ⟨original, originalFound, same⟩ := Option.map_eq_some_iff.mp bridged
        rw [← same, World.restamp_live] at live
        rw [← same, World.restamp_kind]
        exact kindsFields id original originalFound live
      have clearedAncestry : ∀ id loan, cleared.loans.get id = some loan →
          (∀ parent, loan.parent = some parent → cleared.loans.get parent ≠ none) ∧
          (∀ guard ∈ loan.guards, cleared.loans.get guard ≠ none) := by
        intro id loan found
        have bridged : (afterFields.RequestReturns (.resident finalShell.owner)).loans.get id = some loan := by
          rwa [afterWrite] at found
        rw [World.RequestReturns.get_eq] at bridged
        obtain ⟨original, originalFound, same⟩ := Option.map_eq_some_iff.mp bridged
        refine ⟨fun parent link => ?_, fun guard member => ?_⟩
        · have linkOriginal : original.parent = some parent := by
            rw [← same, World.restamp_parent] at link
            exact link
          have held := (ancestryFields id original originalFound).1 parent linkOriginal
          intro missing
          rw [afterWrite, World.RequestReturns.get_eq] at missing
          exact held (Option.map_eq_none_iff.mp missing)
        · have memberOriginal : guard ∈ original.guards := by
            rw [← same, World.restamp_guards] at member
            exact member
          have held := (ancestryFields id original originalFound).2 guard memberOriginal
          intro missing
          rw [afterWrite, World.RequestReturns.get_eq] at missing
          exact held (Option.map_eq_none_iff.mp missing)
      obtain ⟨drained, trace2, drainRun, drainFrame⟩ :=
        CleanupRun.release_custody_returns
          (before := { before with world := cleared, task := ReleaseCustodyLoans cleared (.resident finalShell.owner) next })
          rfl (World.ReleaseReady.custody_of_storage clearedKinds clearedAncestry)
      have restampFrame : World.DestroyFrame afterFields (afterFields.RequestReturns (.resident finalShell.owner)) address :=
        World.DestroyFrame.of_requestReturns
      have clearFrame : World.DestroyFrame (afterFields.RequestReturns (.resident finalShell.owner)) cleared address :=
        World.DestroyFrame.of_write written ⟨rfl, rfl, ⟨[], by simp⟩⟩
      have drainedFrame : World.DestroyFrame cleared drained address := drainFrame.destroyFrame
      have finalFrame : World.DestroyFrame before.world drained address :=
        ((frameFields.trans restampFrame).trans clearFrame).trans drainedFrame
      have drainVacant : drained.Vacant address :=
        World.Vacant.loanReleaseFrame (World.Vacant.of_write_none written) drainFrame
      refine ⟨trace ++ (.destroy address finalShell.owner :: trace2), drained, ?_, drainVacant, finalFrame, ?_⟩
      · exact started.append (fieldsRun.append
          (CleanupRun.visible (by simp [Task.Cleanup]) shellStep .refl |>.append drainRun))
      · intro cell index cellShell cellEq cellStored
        obtain ⟨changed, changedStored, ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩ :=
          finalFrame.ancestor cell index [] cellShell (by rw [cellEq]; rfl) cellStored
        have cellSlot : cellShell.fields[index]? ≠ none := by
          intro missing
          have cellRead : before.world.read cell = some cellShell := cellStored
          have childRead : before.world.read (cell.child index) = some shell := by
            rw [← cellEq]
            exact stored
          have readAppend : before.world.read (cell.child index) =
              (before.world.read cell) >>= fun value => value.atPath [index] :=
            World.read_append before.world cell [index]
          rw [readAppend, cellRead] at childRead
          simp [Value.atPath, missing] at childRead
        have slotHole : changed.fields[index]? = some none :=
          World.Vacant.read_slot (by rw [← cellEq]; exact drainVacant) changedStored lenEq cellSlot
        exact ⟨changed, changedStored, slotHole, ownerEq, typeEq, headEq, liveEq, resEq, lenEq, slotsEq⟩

end Glorious.Language.Execution
