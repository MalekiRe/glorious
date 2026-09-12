import GloriousLanguage.CleanupExecution
import GloriousLanguage.CustodyDischarge
import GloriousLanguage.ProjectionStorage

/-! Actual outcomes of the machine's destructor and loan-ending paths.

Each theorem here runs the real `LocalStep` rule named in its statement and
reports the state the rule actually produces — the nested `destroyFields`
continuation of a structural destruction, the hook entry of a declared drop,
the relinquished write and pending release list of a finished shell, the
retired root of a cleared allocation. Nothing is re-implemented: `Step` is
selected, not replaced.

The two admission products of `CustodyDischarge` appear exactly where the
machine consumes them. `shellDone` needs `World.CustodyHandedOff` for the
value's resident owner, which the discharge inventory supplies; the
`releaseLoan`/`closeLoan` arms need `World.ReferenceFree`, which the
stored-value inventory supplies. Readiness is likewise derived rather than
assumed: `World.RootClear` reads the three actual tables (`loans`,
`availability`, `roots`) instead of assuming `CanEndStorage`, its loan clause
is exactly what the machine's owning-destruction permission needs, and it can
itself be derived from the endings that actually discharged a root. -/
namespace Glorious.Language

open Kernel

/-- Relinquishment marks the pending storage returns of that custody. This is
the successor world of the actual `RelinquishesCustody.relinquish` rule. -/
def World.RequestReturns (world : World) (custody : ClaimCustody) : World :=
  { world with loans := world.loans.map fun entry =>
      (entry.1,if entry.2.custody = some custody ∧ entry.2.kind = .storageBorrow then
        { entry.2 with returnRequested := true } else entry.2) }

theorem RelinquishesCustody.of_handedOff {world : World} {custody : ClaimCustody}
    (handed : world.CustodyHandedOff custody) :
    RelinquishesCustody world custody (world.RequestReturns custody) :=
  .relinquish handed

/-- The three obligations that actually make a root retirable, read from the
real tables rather than assumed as `CanEndStorage`. -/
structure World.RootClear (world : World) (rootId : Identity) : Prop where
  loans : ∀ id loan, world.loans.get id = some loan → loan.live = true → loan.referent.root ≠ rootId
  reservations : ∀ id available, world.availability.get id = some available → available.active = true →
    ∀ place ∈ available.reserved, place.address.root ≠ rootId
  home : ∀ root, world.roots.get rootId = some root → ∀ suspension, root.home ≠ .suspended suspension

theorem World.RootClear.canEndStorage {world : World} {rootId : Identity}
    (clear : world.RootClear rootId) : CanEndStorage world rootId :=
  ⟨clear.loans,clear.reservations,clear.home⟩

/-- Owning destruction of a root is exactly the root's loan freedom plus its
existence: owning access conflicts with every live loan, so the rule's
permission is the loan clause of retirability. -/
theorem World.RootClear.owner_permission {world : World} {rootId : Identity} {root : Root}
    (clear : world.RootClear rootId) (found : world.roots.get rootId = some root) (live : root.live = true) :
    Permitted world .owner .owned ⟨rootId,root.generation,[]⟩ :=
  ⟨⟨root,by simp [World.root,found,live]⟩,
   fun id loan selected active overlap _ => clear.loans id loan selected active overlap.1.symm⟩

/-- The loan part of retirability, derived from an actual ending: once the
recorded borrowing row is the only live claim of the root and that row is
ended, no live loan refers to the root. -/
theorem World.RootClear.of_ended_loan {before after : World} {rootId id : Identity} {loan : Loan}
    (found : before.loans.get id = some loan) (_live : loan.live = true)
    (_referent : loan.referent.root = rootId)
    (rows : after.loans = before.loans.set id { loan with live := false })
    (only : ∀ other row, before.loans.get other = some row → row.live = true →
      row.referent.root = rootId → other = id)
    (reservations : ∀ availableId available, after.availability.get availableId = some available →
      available.active = true → ∀ place ∈ available.reserved, place.address.root ≠ rootId)
    (home : ∀ root, after.roots.get rootId = some root → ∀ suspension, root.home ≠ .suspended suspension) :
    after.RootClear rootId := by
  refine ⟨?_,reservations,home⟩
  intro other row rowFound rowLive sameRoot
  rw [rows] at rowFound
  by_cases same : other = id
  · subst same
    rw [Table.get_set] at rowFound
    have sameRow : row = { loan with live := false } := (Option.some.inj rowFound).symm
    rw [sameRow] at rowLive
    exact absurd rowLive (by simp)
  · have oldFound : before.loans.get other = some row := by
      rw [Table.get_set_other _ _ _ _ same] at rowFound
      exact rowFound
    exact same (only other row oldFound rowLive sameRoot)

/-- A vacant child slot of one stored shell: the actual `Vacant` obligation of
the machine's `destroyVacant` rule at a hole. -/
theorem World.vacant_child_of_shell {world : World} {id : Identity} {root : Root} {value : Value}
    {field : Nat} (found : world.roots.get id = some root) (live : root.live = true)
    (whole : root.value = some value) (hole : value.fields[field]? = some none) :
    world.Vacant (Address.child (⟨id,root.generation,[]⟩ : Address) field) := by
  refine ⟨root,?_,Or.inr ⟨[],field,value,by simp [Address.child],whole,value,by simp [Value.atPath],hole⟩⟩
  simp [Address.child,World.root,found,live]

/-- A stored value at a root address is the root's whole value. -/
theorem World.root_value_of_stores {world : World} {id : Identity} {root : Root} {value : Value}
    (found : world.roots.get id = some root) (stored : world.Stores ⟨id,root.generation,[]⟩ value) :
    root.value = some value := by
  obtain ⟨other,whole,otherFound,_,_,wholeValue,inside⟩ := World.resident_iff_stores.mpr stored
  have sameRoot : other = root := Option.some.inj (otherFound.symm.trans found)
  cases inside with
  | root => simpa [sameRoot] using wholeValue

theorem List.eq_none_of_getElem? {α : Type} {l : List (Option α)}
    (h : ∀ index, index < l.length → l[index]? = some none) : ∀ item ∈ l, item = none := by
  induction l with
  | nil => intro item member; cases member
  | cons head tail ih =>
      intro item member
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact Option.some.inj (h 0 (by simp))
      · refine ih (fun index bound => ?_) item member
        have step := h (index+1) (by simpa using Nat.succ_lt_succ bound)
        simpa using step

end Glorious.Language

namespace Glorious.Language.Execution

open Kernel

/-- The shell write of the destructor is a conclusion, not an input: a stored
shell is still located after its custody's pending returns have been restamped
(the restamp rewrites the loan table only), so the clear at that address exists. -/
theorem World.Stores.requestReturns_write_exists {world : World} {address : Address} {value : Value}
    (stored : world.Stores address value) (custody : ClaimCustody) :
    ∃ after, (world.RequestReturns custody).write address none = some after := by
  have shifted : (world.RequestReturns custody).Stores address value := by
    show (world.RequestReturns custody).read address = some value
    rw [show (world.RequestReturns custody).read address = world.read address from rfl]
    exact stored
  exact shifted.write_exists none

/-! ## Real destructor outcomes -/

theorem CleanupRun.destroy_vacant {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    (task : before.task = .destroy context address authority next) (vacant : before.world.Vacant address) :
    CleanupRun program host before [] ({ before with task := next }) :=
  .silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.destroyVacant task vacant)) .refl

theorem CleanupRun.field_next {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {field : Nat}
    {fields : List Nat} {next : Task}
    (task : before.task = .destroyFields context address authority (field :: fields) next) :
    CleanupRun program host before [] ({ before with task := .destroy context (address.child field) authority (.destroyFields context address authority fields next) }) :=
  .silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.fieldNext task)) .refl

theorem CleanupRun.fields_done {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    (task : before.task = .destroyFields context address authority [] next) :
    CleanupRun program host before [] ({ before with task := .finishShell address authority next }) :=
  .silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.fieldsDone task)) .refl

/-- The structural destructor outcome: a real shell with real fields, disposed
without a pending drop hook, whose actual continuation is the nested field
destruction in reverse index order. -/
theorem CleanupRun.destroy_structural {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    {value : Value} (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value)
    (disposable : MayDispose program.declarations value)
    (permission : Permitted before.world authority .owned address)
    (shell : value.shellLive = false ∨ DropHook program.declarations value.type none)
    (noContinuation : ∀ id, value.head ≠ .continuation id)
    (noReference : ∀ id, value.head ≠ .reference id)
    (noAvailable : ∀ id, value.head ≠ .available id) :
    CleanupRun program host before [] ({ before with task := .destroyFields context address authority ((List.range value.fields.length).reverse) next }) :=
  .silent (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.destroyStructural task stored disposable permission shell noContinuation noReference noAvailable)) .refl

/-- The reference destructor outcome: the handle's own slot is cleared and the
loan release the rule actually schedules becomes the next task. -/
theorem CleanupRun.destroy_reference {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    {value : Value} {id : Identity} {cleared : World}
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value) (head : value.head = .reference id)
    (disposable : MayDispose program.declarations value)
    (permission : Permitted before.world authority .owned address)
    (written : before.world.write address none = some cleared) :
    CleanupRun program host before [.destroy address value.owner] ({ before with world := cleared, task := .releaseLoan id next }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.destroyReference task stored head disposable permission written)) .refl

/-- The declared-hook destructor outcome: the actual destructor lease is
formed and the hook body is entered with the handle as its single argument.
The hook body is user code; `CleanupRun.hook_returned` is the continuation the
machine schedules when it yields. -/
theorem CleanupRun.destroy_hook {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    {value : Value} {hook : DeclId} {function : Function} {withHandle after : World}
    {handle : Address} {loan : Identity}
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value) (shellLive : value.shellLive = true)
    (disposable : MayDispose program.declarations value)
    (dispatch : DropInstance program value.type (.runtimeRegion context.region) hook function)
    (allocated : Temporary program context (.reference .unique (.runtimeRegion context.region) value.type) before.world handle withHandle)
    (borrowed : FormsLoan program .destructor withHandle authority .unique context.region address handle after)
    (identity : loan = withHandle.nextLoan) :
    CleanupRun program host before [.hookEnter address hook] ({ before with world := after, task := .enter { context with unsafeAllowed := false } function (.supplied [⟨.argument 0,function.parameters.head!,handle,.owner,.owned⟩]) false, frames := .hook context address authority handle loan next :: before.frames }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.destroyHook task stored shellLive disposable dispatch allocated borrowed identity)) .refl

/-- The declared-hook return outcome: the machine schedules the destructor
handle's destruction, both retirements, the loan close and the field
destruction that continues the shell, exactly as the rule writes them. -/
theorem Run.hook_returned {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context outer : Context} {result address handle : Address}
    {authority : Authority} {loan : Identity} {next : Task} {rest : List Frame} {receiver : Value}
    (task : before.task = .yield context result)
    (frames : before.frames = .hook outer address authority handle loan next :: rest)
    (stored : before.world.Stores address receiver) :
    Run program host before [] ({ before with frames := rest, task := .destroy outer result .owner (.retire result.root (.retire handle.root (.closeLoan loan (.destroyFields outer address authority ((List.range receiver.fields.length).reverse) next)))) }) :=
  .silent (Or.inl (LocalStep.hookReturned task frames stored)) .refl

/-- The shell outcome: after the fields are gone the machine relinquishes the
resident owner's custody — which the discharge inventory supplies — writes the
empty shell and schedules the pending returns of that custody. -/
theorem CleanupRun.shell_done {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {address : Address} {authority : Authority} {next : Task} {value : Value}
    {after : World}
    (task : before.task = .finishShell address authority next)
    (stored : before.world.Stores address value)
    (cleared : ∀ field ∈ value.fields, field = none)
    (permission : Permitted before.world authority .owned address)
    (handed : before.world.CustodyHandedOff (.resident value.owner))
    (written : (before.world.RequestReturns (.resident value.owner)).write address none = some after) :
    CleanupRun program host before [.destroy address value.owner] ({ before with world := after, task := ReleaseCustodyLoans after (.resident value.owner) next }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.shellDone task stored cleared permission (.relinquish handed) written)) .refl

/-- The shell outcome with its write derived rather than supplied: the clear at
the shell's own address exists because the shell is still stored after the
custody's pending returns have been restamped. -/
theorem CleanupRun.shell_done_exists {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {address : Address} {authority : Authority} {next : Task} {value : Value}
    (task : before.task = .finishShell address authority next)
    (stored : before.world.Stores address value)
    (cleared : ∀ field ∈ value.fields, field = none)
    (permission : Permitted before.world authority .owned address)
    (handed : before.world.CustodyHandedOff (.resident value.owner)) :
    ∃ after, (before.world.RequestReturns (.resident value.owner)).write address none = some after ∧
      CleanupRun program host before [.destroy address value.owner]
        ({ before with world := after, task := ReleaseCustodyLoans after (.resident value.owner) next }) := by
  obtain ⟨after,written⟩ := World.Stores.requestReturns_write_exists stored (.resident value.owner)
  exact ⟨after,written,CleanupRun.shell_done task stored cleared permission handed written⟩

/-! ## Real loan-ending outcomes -/

/-- The requested storage return actually completes: the pending row dies and
the machine retries the recorded dependencies. -/
theorem CleanupRun.release_storage_returned {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {id : Identity} {next : Task} {loan : Loan}
    (task : before.task = .releaseLoan id next)
    (found : before.world.loans.get id = some loan) (live : loan.live = true)
    (kind : loan.kind = .storageBorrow) (requested : loan.returnRequested = true)
    (free : before.world.ReferenceFree id)
    (children : ∀ child, before.world.loans.get child.identity = some child →
      child.parent = some id ∨ id ∈ child.guards → child.live = false) :
    CleanupRun program host before [.loanEnd id] ({ before with world := { before.world with loans := before.world.loans.set id { loan with live := false } }, task := ReleaseLoans (loan.parent.toList ++ loan.guards) next }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.releaseStorageReturned task found (ReturnsStorageLoan.of_referenceFree found live kind requested free children))) .refl

/-- An already-dead release is consumed silently, so a pending return list
drains once its rows have died. -/
theorem CleanupRun.release_already_ended {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {id : Identity} {next : Task} {loan : Loan}
    (task : before.task = .releaseLoan id next)
    (found : before.world.loans.get id = some loan) (dead : loan.live = false) :
    CleanupRun program host before [] ({ before with task := next }) :=
  .silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.releaseAlreadyEnded task found dead)) .refl

/-- The ordinary loan ending of a restoring or destructor lease, with the
reference inventory discharging the two reference premises of the rule. -/
theorem CleanupRun.loan_end {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {id : Identity} {next : Task} {loan : Loan}
    (task : before.task = .closeLoan id next)
    (found : before.world.loans.get id = some loan) (live : loan.live = true)
    (kind : loan.kind = .restoring ∨ loan.kind = .destructor)
    (initialized : before.world.Initialized loan.referent)
    (closed : loan.kind = .restoring → before.world.ResourcesClosed program loan.referent)
    (free : before.world.ReferenceFree id)
    (children : ∀ child, before.world.loans.get child.identity = some child →
      child.parent = some id ∨ id ∈ child.guards → child.live = false) :
    CleanupRun program host before [.loanEnd id] ({ before with world := { before.world with loans := before.world.loans.set id { loan with live := false } }, task := next }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.loanEnd task (EndsLoan.of_referenceFree found live kind initialized closed free children))) .refl

/-- Retirement of a cleared root, with `CanEndStorage` derived from the three
actual table obligations rather than assumed. -/
theorem CleanupRun.retire_clear {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {id : Identity} {next : Task} {root : Root}
    (task : before.task = .retire id next)
    (found : before.world.roots.get id = some root) (live : root.live = true) (empty : root.value = none)
    (clear : before.world.RootClear id) :
    CleanupRun program host before [.retire id] ({ before with world := { before.world with roots := before.world.roots.set id { root with live := false, generation := root.generation + 1 } }, task := next }) :=
  .visible (by simp [Task.Cleanup,task])
    (Or.inl (LocalStep.retire task (Retires.vacant found live empty clear.canEndStorage))) .refl

/-! ## The field loop and the non-vacant root chain -/

/-- The real field loop of the structural destructor: every slot of the shell
is a hole, so each index is disposed by the two actual steps and the shell
reaches `finishShell` unchanged. -/
theorem CleanupRun.destroy_fields_holes {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority}
    {fields : List Nat} {next : Task}
    (task : before.task = .destroyFields context address authority fields next)
    (vacant : ∀ field ∈ fields, before.world.Vacant (address.child field)) :
    CleanupRun program host before [] ({ before with task := .finishShell address authority next }) := by
  induction fields generalizing before with
  | nil => exact CleanupRun.fields_done task
  | cons field rest ih =>
      refine .silent (by simp [Task.Cleanup,task]) (Or.inl (LocalStep.fieldNext task)) ?_
      refine .silent (by simp [Task.Cleanup]) (Or.inl (LocalStep.destroyVacant rfl (vacant field (by simp)))) ?_
      exact ih rfl (fun other member => vacant other (by simp [member]))

/-- The nested field loop: each scheduled child is destroyed by its own run and
the loop then continues with the remaining indices, so the shell reaches
`finishShell` with every field disposed by real steps. -/
theorem CleanupRun.destroy_fields_loop {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority}
    {indices : List Nat} {next : Task}
    (task : before.task = .destroyFields context address authority indices next)
    (step : ∀ (field : Nat) (rest : List Nat) (state : State),
      state.task = .destroy context (address.child field) authority (.destroyFields context address authority rest next) →
      ∃ middle, CleanupRun program host state [] middle ∧
        middle.task = .destroyFields context address authority rest next ∧
        (∀ other ∈ rest, middle.world.Vacant (address.child other))) :
    ∃ after, CleanupRun program host before [] after ∧ after.task = .finishShell address authority next := by
  induction indices generalizing before with
  | nil => exact ⟨_, CleanupRun.fields_done task, rfl⟩
  | cons field rest ih =>
      obtain ⟨middle, run, running, vacant⟩ :=
        step field rest ({ before with task := .destroy context (address.child field) authority (.destroyFields context address authority rest next) }) rfl
      obtain ⟨after, restRun, finished⟩ := ih running
      exact ⟨after, (CleanupRun.field_next task).append run |>.append restRun, finished⟩

/-- The nested node's shell destruction, with every write derived: the shell is
structurally destroyed, its already-empty slots are disposed by the two real
steps, and the clear that finishes it exists because the shell is still stored
after its custody's pending returns were restamped. -/
theorem CleanupRun.destroy_shell {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {address : Address} {authority : Authority} {next : Task}
    {value : Value}
    (task : before.task = .destroy context address authority next)
    (stored : before.world.Stores address value)
    (disposable : MayDispose program.declarations value)
    (shell : value.shellLive = false ∨ DropHook program.declarations value.type none)
    (noContinuation : ∀ id, value.head ≠ .continuation id)
    (noReference : ∀ id, value.head ≠ .reference id)
    (noAvailable : ∀ id, value.head ≠ .available id)
    (holes : ∀ index, index < value.fields.length → value.fields[index]? = some none)
    (permission : Permitted before.world authority .owned address)
    (handed : before.world.CustodyHandedOff (.resident value.owner)) :
    ∃ mid after, CleanupRun program host before [.destroy address value.owner] mid ∧
      mid.world = after ∧ mid.task = ReleaseCustodyLoans after (.resident value.owner) next ∧
      (before.world.RequestReturns (.resident value.owner)).write address none = some after := by
  have structural : Step program host before none
      { before with task := .destroyFields context address authority ((List.range value.fields.length).reverse) next } :=
    Or.inl (LocalStep.destroyStructural task stored disposable permission shell noContinuation noReference noAvailable)
  have vacant : ∀ field ∈ (List.range value.fields.length).reverse, before.world.Vacant (address.child field) := by
    intro field member
    have bound : field < value.fields.length := by
      simpa only [List.mem_reverse,List.mem_range] using member
    exact World.Stores.vacant_child stored (holes field bound)
  have fields : CleanupRun program host
      { before with task := .destroyFields context address authority ((List.range value.fields.length).reverse) next } []
      { before with task := .finishShell address authority next } :=
    CleanupRun.destroy_fields_holes rfl vacant
  obtain ⟨after,written,finish⟩ := CleanupRun.shell_done_exists (before := { before with task := .finishShell address authority next })
    rfl stored (List.eq_none_of_getElem? holes) permission handed
  exact ⟨_,after,.silent (by simp [Task.Cleanup,task]) structural (fields.append finish),rfl,rfl,written⟩

/-- The nested field loop with the parent shell tracked: each scheduled child is
destroyed by its own run (its slot left a hole, every other slot as the parent
held it) and the loop continues with the remaining indices, so the shell reaches
`finishShell` with exactly the scheduled fields emptied. The indices are
duplicate-free, which is what the machine's schedule supplies (the reverse of
`List.range`), so a slot emptied by one step is never re-opened by a later one.
The state between the scheduling step and the child's run is reified as a
variable, which is what lets the runs append without a record literal in the way. -/
theorem CleanupRun.destroy_fields_tree {program : Kernel.Program} {host : Foreign.Model}
    {context : Context} {address : Address} {indices : List Nat} {next : Task}
    (step : ∀ (field : Nat) (rest : List Nat) (state : State) {parent : Value},
      state.task = .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) →
      state.world.Stores address parent →
      ∃ after parent', CleanupRun program host state [] after ∧
        after.task = .destroyFields context address .owner rest next ∧
        after.world.Stores address parent' ∧ parent'.fields[field]? = some none ∧
        (∀ other, other ≠ field → parent'.fields[other]? = parent.fields[other]?) ∧
        parent'.owner = parent.owner ∧ parent'.head = parent.head ∧ parent'.type = parent.type ∧
        parent'.shellLive = parent.shellLive ∧ parent'.resources = parent.resources ∧
        (∀ other ∈ rest, after.world.Vacant (address.child other))) :
    ∀ (before : State) (parent : Value), before.task = .destroyFields context address .owner indices next →
      indices.Nodup → before.world.Stores address parent →
      ∃ trace after parent', CleanupRun program host before trace after ∧
        after.task = .finishShell address .owner next ∧ after.world.Stores address parent' ∧
        (∀ field ∈ indices, parent'.fields[field]? = some none) ∧
        (∀ field, field ∉ indices → parent'.fields[field]? = parent.fields[field]?) ∧
        parent'.owner = parent.owner ∧ parent'.head = parent.head ∧ parent'.type = parent.type ∧
        parent'.shellLive = parent.shellLive ∧ parent'.resources = parent.resources := by
  induction indices with
  | nil =>
      intro before parent task nodup stored
      exact ⟨_,{ before with task := .finishShell address .owner next },parent,CleanupRun.fields_done task,rfl,
        by simpa using stored,by simp,by intro field _; rfl,rfl,rfl,rfl,rfl,rfl⟩
  | cons field rest ih =>
      intro before parent task nodup stored
      obtain ⟨notRest, nodupRest⟩ := List.nodup_cons.mp nodup
      have moved := CleanupRun.field_next (program := program) (host := host) (before := before) (context := context)
        (address := address) (field := field) (fields := rest) (next := next) task
      obtain ⟨scheduled, movedRun, schedTask, schedWorld⟩ : ∃ scheduled, CleanupRun program host before [] scheduled ∧
          scheduled.task = .destroy context (address.child field) .owner (.destroyFields context address .owner rest next) ∧
          scheduled.world = before.world := ⟨_,moved,rfl,rfl⟩
      obtain ⟨middle, middleParent, run, running, midStored, slotHole, others, midOwner, midHead, midType, midLive, midRes, vacant⟩ :=
        step field rest scheduled (parent := parent) schedTask (by rw [schedWorld]; exact stored)
      obtain ⟨_, after, finalParent, restRun, finished, finalStored, holes, untouched, ownerEq, headEq, typeEq, liveEq, resEq⟩ :=
        ih middle middleParent running nodupRest midStored
      refine ⟨_,after,finalParent,movedRun.append run |>.append restRun,finished,finalStored,?_,?_,
        ownerEq.trans midOwner,headEq.trans midHead,typeEq.trans midType,liveEq.trans midLive,resEq.trans midRes⟩
      · intro other member
        rcases List.mem_cons.mp member with same | member
        · have notMember : other ∉ rest := by rw [same]; exact notRest
          exact (untouched other notMember).trans (by rw [same]; exact slotHole)
        · exact holes other member
      · intro other missing
        have notMember : other ∉ rest := by intro member; exact missing (List.mem_cons_of_mem _ member)
        have notHead : other ≠ field := by intro same; subst same; exact missing (by simp)
        exact (untouched other notMember).trans (others other notHead)

/-- The whole non-vacant structural destruction of one captured root, with the
real machine steps: the captured shell is structurally destroyed field by
field, the resident owner's custody is relinquished through the discharge
inventory and the empty shell is written, leaving the actual pending release
list and the retirement of the root next. -/
theorem CleanupRun.cleanup_root_shell {program : Kernel.Program} {host : Foreign.Model}
    {before : State} {context : Context} {id : Identity} {roots : List Identity} {next : Task}
    {root : Root} {value : Value} {cleared : World}
    (task : before.task = .cleanup context (id :: roots) next)
    (found : before.world.roots.get id = some root) (live : root.live = true)
    (stored : before.world.Stores ⟨id,root.generation,[]⟩ value)
    (disposable : MayDispose program.declarations value)
    (shell : value.shellLive = false ∨ DropHook program.declarations value.type none)
    (noContinuation : ∀ id, value.head ≠ .continuation id)
    (noReference : ∀ id, value.head ≠ .reference id)
    (noAvailable : ∀ id, value.head ≠ .available id)
    (holes : ∀ index, index < value.fields.length → value.fields[index]? = some none)
    (clear : before.world.RootClear id)
    (handed : before.world.CustodyHandedOff (.resident value.owner))
    (written : (before.world.RequestReturns (.resident value.owner)).write ⟨id,root.generation,[]⟩ none = some cleared) :
    CleanupRun program host before [.destroy ⟨id,root.generation,[]⟩ value.owner] ({ before with world := cleared, task := ReleaseCustodyLoans cleared (.resident value.owner) (.retire id (.cleanup context roots next)) }) := by
  let rootAddress : Address := ⟨id,root.generation,[]⟩
  let retireTask : Task := .retire id (.cleanup context roots next)
  let fieldTasks : List Nat := (List.range value.fields.length).reverse
  have permission : Permitted before.world .owner .owned rootAddress := clear.owner_permission found live
  have whole : root.value = some value := World.root_value_of_stores found stored
  have start : Step program host before none { before with task := .destroy context rootAddress .owner retireTask } :=
    Or.inl (LocalStep.cleanupRoot task found live)
  have structural : Step program host { before with task := .destroy context rootAddress .owner retireTask } none { before with task := .destroyFields context rootAddress .owner fieldTasks retireTask } :=
    Or.inl (LocalStep.destroyStructural rfl stored disposable permission shell noContinuation noReference noAvailable)
  have vacant : ∀ field ∈ fieldTasks, before.world.Vacant (rootAddress.child field) := by
    intro field member
    have bound : field < value.fields.length := by
      simpa only [List.mem_reverse,List.mem_range,fieldTasks] using member
    exact World.vacant_child_of_shell found live whole (holes field bound)
  have fields : CleanupRun program host { before with task := .destroyFields context rootAddress .owner fieldTasks retireTask } [] { before with task := .finishShell rootAddress .owner retireTask } :=
    CleanupRun.destroy_fields_holes rfl vacant
  have finish : Step program host { before with task := .finishShell rootAddress .owner retireTask } (some (.destroy rootAddress value.owner)) { before with world := cleared, task := ReleaseCustodyLoans cleared (.resident value.owner) retireTask } :=
    Or.inl (LocalStep.shellDone rfl stored (List.eq_none_of_getElem? holes) permission (.relinquish handed) written)
  exact .silent (by simp [Task.Cleanup,task]) start (.silent (by simp [Task.Cleanup]) structural (fields.append (.visible (by simp [Task.Cleanup]) finish .refl)))

end Glorious.Language.Execution

namespace Glorious.Language

open Kernel

/-- Writing storage changes neither loans, reservations nor homes, so a
retirable root stays retirable. -/
theorem World.RootClear.of_write {before after : World} {rootId : Identity} {address : Address}
    {replacement : Option Value} (clear : before.RootClear rootId)
    (written : before.write address replacement = some after) : after.RootClear rootId := by
  obtain ⟨root,inserted,found,shape⟩ := World.write_value_update written
  subst shape
  refine ⟨?_,?_,?_⟩
  · intro id loan selected active
    exact clear.loans id loan (by simpa using selected) active
  · intro availableId available selected active
    exact clear.reservations availableId available (by simpa using selected) active
  · intro other otherFound suspension
    by_cases same : rootId = address.root
    · subst same
      rw [Table.get_set] at otherFound
      have sameRow : other = { root with value := inserted } := (Option.some.inj otherFound).symm
      rw [sameRow]
      exact clear.home root found suspension
    · have beforeFound : before.roots.get rootId = some other := by
        rw [Table.get_set_other _ _ _ _ same] at otherFound
        exact otherFound
      exact clear.home other beforeFound suspension

end Glorious.Language

namespace Glorious.Language.Execution

open Kernel

end Glorious.Language.Execution
