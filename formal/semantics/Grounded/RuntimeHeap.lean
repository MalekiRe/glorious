import Grounded.Model

/-! Logical storage identities are never lexical binding IDs. Retired slots are
not reused; allocation is logical, with no physical-exhaustion claim. -/
namespace Grounded

structure StorageId where
  index : Nat
  deriving DecidableEq

structure ActivationId where
  index : Nat
  deriving DecidableEq

structure ActivationSupply where
  next : Nat

def ActivationSupply.allocate (supply : ActivationSupply) : ActivationId × ActivationSupply :=
  (⟨supply.next⟩, ⟨supply.next + 1⟩)

/-- The monotone supply records every issued activation, including activations
with no storage cells. Heap liveness alone cannot establish generativity. -/
def ActivationSupply.Issued (supply : ActivationSupply) (activation : ActivationId) : Prop :=
  activation.index < supply.next

theorem ActivationSupply.allocate_fresh (supply : ActivationSupply) :
    ¬supply.Issued supply.allocate.1 := Nat.lt_irrefl _

theorem ActivationSupply.allocate_issued (supply : ActivationSupply) :
    supply.allocate.2.Issued supply.allocate.1 := Nat.lt_succ_self _

theorem ActivationSupply.allocate_preserves {supply : ActivationSupply} {activation : ActivationId}
    (issued : supply.Issued activation) : supply.allocate.2.Issued activation :=
  Nat.lt_succ_of_lt issued

theorem ActivationSupply.allocate_distinct {supply : ActivationSupply} {activation : ActivationId}
    (issued : supply.Issued activation) : activation ≠ supply.allocate.1 := by
  intro same
  exact supply.allocate_fresh (same ▸ issued)

/-- A finite extensional store. The bound rules out invented cells above the
allocation frontier. A missing payload below the frontier is retired storage,
not a live uninitialized resident. -/
structure RuntimeHeap (α : Type) where
  next : Nat
  cells : StorageId → Option α
  bounded : ∀ identity value, cells identity = some value → identity.index < next

def RuntimeHeap.empty {α : Type} : RuntimeHeap α := ⟨0, fun _ => none, by simp⟩

def RuntimeHeap.read {α : Type} (heap : RuntimeHeap α) (identity : StorageId) : Option α :=
  heap.cells identity

def RuntimeHeap.allocate {α : Type} (heap : RuntimeHeap α) (value : α) : StorageId × RuntimeHeap α :=
  (⟨heap.next⟩, {
    next := heap.next + 1
    cells := fun identity => if identity = ⟨heap.next⟩ then some value else heap.cells identity
    bounded := by
      intro identity resident found
      split at found
      next same => subst identity; exact Nat.lt_succ_self _
      next different => exact Nat.lt_succ_of_lt (heap.bounded _ _ found) })

/-- Update cannot resurrect retired storage. A hole is a payload state, so
restoring a live hole uses this operation without allocating another identity. -/
def RuntimeHeap.write {α : Type} (heap : RuntimeHeap α) (identity : StorageId) (value : α) : Option (RuntimeHeap α) :=
  match found : heap.cells identity with
  | none => none
  | some old => some {
      next := heap.next
      cells := fun other => if other = identity then some value else heap.cells other
      bounded := by
        intro other resident selected
        split at selected
        next same => subst other; exact heap.bounded _ _ found
        next different => exact heap.bounded _ _ selected }

def RuntimeHeap.retire {α : Type} (heap : RuntimeHeap α) (identity : StorageId) : Option (RuntimeHeap α) :=
  match heap.cells identity with
  | none => none
  | some _ => some {
      next := heap.next
      cells := fun other => if other = identity then none else heap.cells other
      bounded := by
        intro other resident selected
        split at selected
        next same => cases selected
        next different => exact heap.bounded _ _ selected }

namespace RuntimeHeap
variable {α : Type}

theorem allocate_fresh (heap : RuntimeHeap α) (value : α) :
    heap.read (heap.allocate value).1 = none := by
  cases found : heap.cells ⟨heap.next⟩ with
  | none => exact found
  | some resident => exact False.elim (Nat.lt_irrefl _ (heap.bounded _ _ found))

theorem allocate_read (heap : RuntimeHeap α) (value : α) :
    (heap.allocate value).2.read (heap.allocate value).1 = some value := by
  simp [allocate, read]

theorem allocate_other (heap : RuntimeHeap α) (value : α) (identity : StorageId)
    (different : identity ≠ (heap.allocate value).1) :
    (heap.allocate value).2.read identity = heap.read identity := by
  change identity ≠ ⟨heap.next⟩ at different
  simp [allocate, read, different]

theorem write_exists {heap : RuntimeHeap α} {identity : StorageId} {old : α}
    (live : heap.read identity = some old) (value : α) :
    ∃ after, heap.write identity value = some after := by
  unfold write
  split
  next missing => simp [read, missing] at live
  next resident found => exact ⟨_, rfl⟩

theorem write_read {heap after : RuntimeHeap α} {identity : StorageId} {value : α}
    (written : heap.write identity value = some after) : after.read identity = some value := by
  unfold write at written
  split at written
  next absent => cases written
  next old found => cases written; simp [read]

theorem write_other {heap after : RuntimeHeap α} {identity other : StorageId} {value : α}
    (written : heap.write identity value = some after) (different : other ≠ identity) :
    after.read other = heap.read other := by
  unfold write at written
  split at written
  next absent => cases written
  next old found => cases written; simp [read, different]

theorem write_next {heap after : RuntimeHeap α} {identity : StorageId} {value : α}
    (written : heap.write identity value = some after) : after.next = heap.next := by
  unfold write at written
  split at written
  next absent => cases written
  next old found => cases written; rfl

theorem retire_exists {heap : RuntimeHeap α} {identity : StorageId} {old : α}
    (live : heap.read identity = some old) : ∃ after, heap.retire identity = some after := by
  simp [retire, read] at *
  rw [live]
  exact ⟨_, rfl⟩

theorem retire_read {heap after : RuntimeHeap α} {identity : StorageId}
    (retired : heap.retire identity = some after) : after.read identity = none := by
  unfold retire at retired
  split at retired
  next absent => cases retired
  next old found => cases retired; simp [read]

theorem retire_other {heap after : RuntimeHeap α} {identity other : StorageId}
    (retired : heap.retire identity = some after) (different : other ≠ identity) :
    after.read other = heap.read other := by
  unfold retire at retired
  split at retired
  next absent => cases retired
  next old found => cases retired; simp [read, different]

theorem retire_next {heap after : RuntimeHeap α} {identity : StorageId}
    (retired : heap.retire identity = some after) : after.next = heap.next := by
  unfold retire at retired
  split at retired
  next absent => cases retired
  next old found => cases retired; rfl

def Typed (predicate : StorageId → α → Prop) (heap : RuntimeHeap α) : Prop :=
  ∀ identity value, heap.read identity = some value → predicate identity value

theorem Typed.allocate {predicate : StorageId → α → Prop} {heap : RuntimeHeap α}
    (typed : heap.Typed predicate) (value : α) (resident : predicate ⟨heap.next⟩ value) :
    (heap.allocate value).2.Typed predicate := by
  intro identity other found
  by_cases same : identity = ⟨heap.next⟩
  · subst identity
    have equal := Option.some.inj ((heap.allocate_read value).symm.trans found)
    exact equal ▸ resident
  · exact typed _ _ ((heap.allocate_other value identity same).symm.trans found)

theorem Typed.write {predicate : StorageId → α → Prop} {heap after : RuntimeHeap α}
    {identity : StorageId} {value : α} (typed : heap.Typed predicate)
    (written : heap.write identity value = some after) (resident : predicate identity value) :
    after.Typed predicate := by
  intro other actual found
  by_cases same : other = identity
  · subst other
    have equal := Option.some.inj ((write_read written).symm.trans found)
    exact equal ▸ resident
  · exact typed _ _ ((write_other written same).symm.trans found)

theorem Typed.retire {predicate : StorageId → α → Prop} {heap after : RuntimeHeap α}
    {identity : StorageId} (typed : heap.Typed predicate) (retired : heap.retire identity = some after) :
    after.Typed predicate := by
  intro other value found
  by_cases same : other = identity
  · subst other; rw [retire_read retired] at found; cases found
  · exact typed _ _ ((retire_other retired same).symm.trans found)

/-- Issued-and-absent distinguishes retirement from a not-yet-issued identity. -/
def Retired (heap : RuntimeHeap α) (identity : StorageId) : Prop :=
  identity.index < heap.next ∧ heap.read identity = none

inductive Changes : RuntimeHeap α → RuntimeHeap α → Prop where
  | allocate (heap : RuntimeHeap α) (value : α) : Changes heap (heap.allocate value).2
  | write {heap after : RuntimeHeap α} {identity : StorageId} {value : α}
      (written : heap.write identity value = some after) : Changes heap after
  | retire {heap after : RuntimeHeap α} {identity : StorageId}
      (retired : heap.retire identity = some after) : Changes heap after

theorem Retired.preserved {before after : RuntimeHeap α} {identity : StorageId}
    (retired : before.Retired identity) (change : Changes before after) : after.Retired identity := by
  cases change with
  | allocate value =>
    have different : identity ≠ (before.allocate value).1 := by
      intro same
      have equal := congrArg StorageId.index same
      exact Nat.ne_of_lt retired.1 equal
    exact ⟨Nat.lt_succ_of_lt retired.1, (before.allocate_other value identity different).trans retired.2⟩
  | @write after other value written =>
    have different : identity ≠ other := by
      intro same
      subst other
      have absent : before.cells identity = none := retired.2
      unfold write at written
      split at written
      next missing => cases written
      next resident found => rw [absent] at found; cases found
    exact ⟨by rw [write_next written]; exact retired.1, (write_other written different).trans retired.2⟩
  | @retire after other removed =>
    refine ⟨by rw [retire_next removed]; exact retired.1, ?_⟩
    by_cases same : identity = other
    · subst other; exact retire_read removed
    · exact (retire_other removed same).trans retired.2


def allocateMany (heap : RuntimeHeap α) : List α → List StorageId × RuntimeHeap α
  | [] => ([], heap)
  | value :: rest =>
      let first := heap.allocate value
      let tail := allocateMany first.2 rest
      (first.1 :: tail.1, tail.2)

def retireMany (heap : RuntimeHeap α) : List StorageId → Option (RuntimeHeap α)
  | [] => some heap
  | identity :: rest => (heap.retire identity).bind (fun after => retireMany after rest)

theorem allocateMany_next (heap : RuntimeHeap α) (values : List α) :
    (heap.allocateMany values).2.next = heap.next + values.length := by
  induction values generalizing heap with
  | nil => simp [allocateMany]
  | cons value rest ih =>
    simp only [allocateMany, ih, allocate, List.length_cons]
    omega

theorem allocateMany_old (heap : RuntimeHeap α) (values : List α) (identity : StorageId)
    (old : identity.index < heap.next) :
    (heap.allocateMany values).2.read identity = heap.read identity := by
  induction values generalizing heap with
  | nil => rfl
  | cons value rest ih =>
    have different : identity ≠ (heap.allocate value).1 := by
      intro same
      exact Nat.ne_of_lt old (congrArg StorageId.index same)
    exact (ih (heap.allocate value).2 (Nat.lt_succ_of_lt old)).trans
      (heap.allocate_other value identity different)

theorem allocateMany_bounds (heap : RuntimeHeap α) (values : List α) :
    ∀ identity ∈ (heap.allocateMany values).1,
      heap.next ≤ identity.index ∧ identity.index < (heap.allocateMany values).2.next := by
  induction values generalizing heap with
  | nil => simp [allocateMany]
  | cons value rest ih =>
    intro identity member
    cases member with
    | head =>
      constructor
      · exact Nat.le_refl _
      · rw [allocateMany_next]
        simp only [allocate, List.length_cons]
        omega
    | tail _ member =>
      obtain ⟨lower, upper⟩ := ih (heap.allocate value).2 identity member
      exact ⟨Nat.le_trans (Nat.le_succ _) lower, upper⟩

theorem allocateMany_distinct (heap : RuntimeHeap α) (values : List α) :
    (heap.allocateMany values).1.Nodup := by
  induction values generalizing heap with
  | nil => exact .nil
  | cons value rest ih =>
    refine List.nodup_cons.mpr ⟨?_, ih (heap.allocate value).2⟩
    intro member
    have lower := (allocateMany_bounds (heap.allocate value).2 rest _ member).1
    change heap.next + 1 ≤ heap.next at lower
    omega

/-- Each allocated identity resolves to its corresponding input, in order. -/
theorem allocateMany_reads (heap : RuntimeHeap α) (values : List α) :
    (heap.allocateMany values).1.map (heap.allocateMany values).2.read = values.map some := by
  induction values generalizing heap with
  | nil => rfl
  | cons value rest ih =>
    change ((heap.allocate value).2.allocateMany rest).2.read (heap.allocate value).1 ::
      _ = some value :: _
    congr 1
    · exact (allocateMany_old (heap.allocate value).2 rest _ (Nat.lt_succ_self _)).trans
        (heap.allocate_read value)
    · exact ih (heap.allocate value).2

theorem retireMany_next {before after : RuntimeHeap α} {identities : List StorageId}
    (released : before.retireMany identities = some after) : after.next = before.next := by
  induction identities generalizing before with
  | nil => cases released; rfl
  | cons identity rest ih =>
    simp only [retireMany, Option.bind_eq_some_iff] at released
    obtain ⟨middle, head, tail⟩ := released
    exact (ih tail).trans (retire_next head)

theorem retireMany_outside {before after : RuntimeHeap α} {identities : List StorageId}
    (released : before.retireMany identities = some after) {identity : StorageId}
    (outside : identity ∉ identities) : after.read identity = before.read identity := by
  induction identities generalizing before with
  | nil => cases released; rfl
  | cons head rest ih =>
    simp only [retireMany, Option.bind_eq_some_iff] at released
    obtain ⟨middle, first, tail⟩ := released
    have apart : identity ≠ head ∧ identity ∉ rest := by
      simpa only [List.mem_cons, not_or] using outside
    exact (ih tail apart.2).trans (retire_other first apart.1)

/-- A typed live scope with distinct addresses can actually retire all cells.
No successful release or post-state readiness is supplied. -/
theorem retireMany_exists (heap : RuntimeHeap α) (identities : List StorageId)
    (distinct : identities.Nodup)
    (live : ∀ identity ∈ identities, ∃ value, heap.read identity = some value) :
    ∃ after, heap.retireMany identities = some after := by
  induction identities generalizing heap with
  | nil => exact ⟨heap, rfl⟩
  | cons identity rest ih =>
    have parts := List.nodup_cons.mp distinct
    obtain ⟨value, found⟩ := live identity (by simp)
    obtain ⟨middle, released⟩ := retire_exists found
    have remaining : ∀ other ∈ rest, ∃ value, middle.read other = some value := by
      intro other member
      obtain ⟨value, found⟩ := live other (List.mem_cons_of_mem _ member)
      refine ⟨value, (retire_other released ?_).trans found⟩
      intro same
      subst other
      exact parts.1 member
    obtain ⟨after, tail⟩ := ih middle parts.2 remaining
    exact ⟨after, by simp [retireMany, released, tail]⟩

/-- Histories are generated by the actual heap operations, not arbitrary
relations assuming post-state freshness. -/
inductive History : RuntimeHeap α → RuntimeHeap α → Prop where
  | refl (heap : RuntimeHeap α) : History heap heap
  | step {before middle after : RuntimeHeap α} (head : Changes before middle)
      (tail : History middle after) : History before after

theorem Retired.history {before after : RuntimeHeap α} {identity : StorageId}
    (retired : before.Retired identity) (history : History before after) : after.Retired identity := by
  induction history with
  | refl => exact retired
  | step head tail ih => exact ih (retired.preserved head)



theorem History.trans {before middle after : RuntimeHeap α}
    (first : History before middle) (second : History middle after) : History before after := by
  induction first with
  | refl => exact second
  | step head tail ih => exact .step head (ih second)

theorem allocateMany_history (heap : RuntimeHeap α) (values : List α) :
    History heap (heap.allocateMany values).2 := by
  induction values generalizing heap with
  | nil => exact .refl _
  | cons value rest ih => exact .step (.allocate heap value) (ih _)

theorem retireMany_history {before after : RuntimeHeap α} {identities : List StorageId}
    (released : before.retireMany identities = some after) : History before after := by
  induction identities generalizing before with
  | nil => cases released; exact .refl _
  | cons identity rest ih =>
    simp only [retireMany, Option.bind_eq_some_iff] at released
    obtain ⟨middle, head, tail⟩ := released
    exact .step (.retire head) (ih tail)

theorem retire_live {before after : RuntimeHeap α} {identity : StorageId}
    (released : before.retire identity = some after) :
    ∃ value, before.read identity = some value := by
  unfold retire at released
  split at released
  next missing => cases released
  next value found => exact ⟨value, found⟩

theorem retire_retired {before after : RuntimeHeap α} {identity : StorageId}
    (released : before.retire identity = some after) : after.Retired identity := by
  obtain ⟨value, found⟩ := retire_live released
  exact ⟨by rw [retire_next released]; exact before.bounded identity value found,
    retire_read released⟩

theorem retireMany_retired {before after : RuntimeHeap α} {identities : List StorageId}
    (released : before.retireMany identities = some after) :
    ∀ identity ∈ identities, after.Retired identity := by
  induction identities generalizing before with
  | nil => simp
  | cons head rest ih =>
    simp only [retireMany, Option.bind_eq_some_iff] at released
    obtain ⟨middle, first, tail⟩ := released
    intro identity member
    cases member with
    | head => exact (retire_retired first).history (retireMany_history tail)
    | tail _ member => exact ih tail identity member

theorem allocateMany_outside (heap : RuntimeHeap α) (values : List α) {identity : StorageId}
    (outside : identity ∉ (heap.allocateMany values).1) :
    (heap.allocateMany values).2.read identity = heap.read identity := by
  induction values generalizing heap with
  | nil => rfl
  | cons value rest ih =>
    have parts : identity ≠ (heap.allocate value).1 ∧
        identity ∉ ((heap.allocate value).2.allocateMany rest).1 := by
      simpa only [allocateMany, List.mem_cons, not_or] using outside
    exact (ih (heap.allocate value).2 parts.2).trans (heap.allocate_other value identity parts.1)

/-- Allocation followed by release removes exactly the new residents, frames
all previous observations, and permanently consumes the issued identity range.
This is logical scope storage, not permission to drop arbitrary language values. -/
theorem allocate_scope_retire (heap : RuntimeHeap α) (values : List α) :
    ∃ after, (heap.allocateMany values).2.retireMany (heap.allocateMany values).1 = some after ∧
      (∀ identity, after.read identity = heap.read identity) ∧
      after.next = heap.next + values.length ∧
      (∀ identity ∈ (heap.allocateMany values).1, after.Retired identity) := by
  have live : ∀ identity ∈ (heap.allocateMany values).1,
      ∃ value, (heap.allocateMany values).2.read identity = some value := by
    intro identity member
    have observed : (heap.allocateMany values).2.read identity ∈
        (heap.allocateMany values).1.map (heap.allocateMany values).2.read :=
      List.mem_map.mpr ⟨identity, member, rfl⟩
    rw [allocateMany_reads] at observed
    obtain ⟨value, _, found⟩ := List.mem_map.mp observed
    exact ⟨value, found.symm⟩
  obtain ⟨after, released⟩ := retireMany_exists _ _ (heap.allocateMany_distinct values) live
  refine ⟨after, released, ?_, (retireMany_next released).trans (heap.allocateMany_next values),
    retireMany_retired released⟩
  intro identity
  by_cases member : identity ∈ (heap.allocateMany values).1
  · rw [(retireMany_retired released identity member).2]
    symm
    cases found : heap.read identity with
    | none => rfl
    | some value =>
      have old := heap.bounded identity value found
      have fresh := (heap.allocateMany_bounds values identity member).1
      omega
  · exact (retireMany_outside released member).trans (heap.allocateMany_outside values member)


theorem History.next_le {before after : RuntimeHeap α} (history : History before after) :
    before.next ≤ after.next := by
  induction history with
  | refl => exact Nat.le_refl _
  | step head tail ih =>
    apply Nat.le_trans _ ih
    cases head with
    | allocate => exact Nat.le_succ _
    | write written => exact Nat.le_of_eq (write_next written).symm
    | retire released => exact Nat.le_of_eq (retire_next released).symm

/-- Retirement only removes cells; every survivor is the same original cell. -/
theorem retireMany_origin {before after : RuntimeHeap α} {identities : List StorageId}
    (released : before.retireMany identities = some after) {identity : StorageId} {value : α}
    (found : after.read identity = some value) : before.read identity = some value := by
  induction identities generalizing before with
  | nil => cases released; exact found
  | cons first rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp released
    exact (Typed.retire (fun _ _ selected => selected) head) identity value (ih tail)


end RuntimeHeap
end Grounded
