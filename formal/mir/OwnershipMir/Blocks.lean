import OwnershipMir.Machine

namespace OwnershipMir

/-- Finite straight-line emission; the continuation is outside the block. -/
def Block.emit {n : Nat} {α : Type} : List α → Code n α → Code n α
  | [], next => next
  | op :: rest, next => .act op (Block.emit rest next)

@[simp] theorem Block.emit_eq_halt {n : Nat} {α : Type} (ops : List α) (next : Code n α) :
    Block.emit ops next = .halt ↔ ops = [] ∧ next = .halt := by
  cases ops <;> simp [Block.emit]

def sequence {n : Nat} {α : Type} (ops : List α) : Code n α := Block.emit ops .halt

@[simp] theorem Block.emit_append {n : Nat} {α : Type} (ops : List α) (next tail : Code n α) :
    (Block.emit ops next).append tail = Block.emit ops (next.append tail) := by
  induction ops <;> simp_all [Block.emit, Code.append]

@[simp] theorem Block.emit_sequence {n : Nat} {α : Type} (ops : List α) (next : Code n α) :
    (sequence ops).append next = Block.emit ops next := by
  simp [sequence, Code.append]

@[simp] theorem sequence_append {n : Nat} {α : Type} (first last : List α) :
    sequence (n := n) (first ++ last) = (sequence first).append (sequence last) := by
  induction first <;> simp_all [sequence, Block.emit, Code.append]

theorem sequence_checked_append {n : Nat} {α : Type} {rule : Context n → α → Context n → Prop}
    {before middle after : Context n} {first last : List α}
    (head : Code.Checked rule before (sequence first) middle)
    (tail : Code.Checked rule middle (sequence last) after) :
    Code.Checked rule before (sequence (first ++ last)) after := by
  rw [sequence_append]
  exact head.append tail

def Block.exec {n : Nat} {α : Type} (exec : α → State n → Option (State n)) :
    List α → State n → Option (State n)
  | [], state => some state
  | op :: rest, state => (exec op state).bind (Block.exec exec rest)

theorem Block.exec_run {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    (ops : List α) {before after : State n} (executed : Block.exec exec ops before = some after)
    (next : Code n α) : Run exec ⟨Block.emit ops next, before⟩ ⟨next, after⟩ := by
  induction ops generalizing before with
  | nil => cases Option.some.inj executed; exact .refl _
  | cons op rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    exact .step (.act head) (ih tail)

/-- Every nonempty block performs a real first step and finitely many remaining
steps. No global bound on block length is built into the refinement proof. -/
theorem Block.exec_positive {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    (ops : List α) (nonempty : ops ≠ []) {before after : State n}
    (executed : Block.exec exec ops before = some after) (next : Code n α) :
    ∃ middle, Step exec ⟨Block.emit ops next, before⟩ middle ∧ Run exec middle ⟨next, after⟩ := by
  cases ops with
  | nil => exact False.elim (nonempty rfl)
  | cons op rest =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    exact ⟨_, .act head, Block.exec_run rest tail next⟩

/-- Administrative progress is the actual uncons of the pending instruction
list. Its strictly decreasing natural rank excludes infinite internal blocks. -/
inductive Block.Advance {n : Nat} {α : Type} (exec : α → State n → Option (State n)) :
    List α × State n → List α × State n → Prop where
  | step {op rest before after} (executed : exec op before = some after) :
      Advance exec (op :: rest, before) (rest, after)

theorem Block.Advance.rank {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before after : List α × State n} (step : Block.Advance exec before after) :
    after.1.length < before.1.length := by
  cases step
  simp

theorem Block.physical_advance {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    (ops : List α) (nonempty : ops ≠ []) (next : Code n α) {state : State n}
    {after : Configuration n α} (step : Step exec ⟨Block.emit ops next, state⟩ after) :
    ∃ rest, after.code = Block.emit rest next ∧ Block.Advance exec (ops, state) (rest, after.state) ∧
      rest.length < ops.length := by
  cases ops with
  | nil => exact False.elim (nonempty rfl)
  | cons op rest =>
    cases step with
    | act executed => exact ⟨rest, rfl, .step executed, by simp⟩

theorem Block.no_infinite {n : Nat} {α : Type} (exec : α → State n → Option (State n)) :
    ¬ ∃ trace : Nat → List α × State n, ∀ i, Block.Advance exec (trace i) (trace (i + 1)) := by
  rintro ⟨trace, steps⟩
  have bound : ∀ i, (trace i).1.length + i ≤ (trace 0).1.length := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => have smaller := (steps i).rank; omega
  have impossible := bound ((trace 0).1.length + 1)
  omega

/-- Finite block progress and preservation are derived from instruction
soundness, rather than supplied as a block-execution assumption. -/
theorem Block.checked_exec {n : Nat} {α : Type} {signature : Signature}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    (sound : InstructionSound signature rule exec) (ops : List α) {before after : Context n}
    (checked : Code.Checked rule before (sequence ops) after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ result, Block.exec exec ops state = some result ∧ result.Typed signature after ∧
      Conserves signature state result := by
  induction ops generalizing before state with
  | nil => cases checked; exact ⟨state, rfl, typed, Conserves.refl _ _⟩
  | cons op rest ih =>
    cases checked with
    | act head tail =>
      obtain ⟨middle, executed, realized, first⟩ := sound head typed
      obtain ⟨result, remainder, final, last⟩ := ih tail realized
      exact ⟨result, by simp [Block.exec, executed, remainder], final, first.trans last⟩

end OwnershipMir
