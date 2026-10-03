import OwnershipMir.Metadata
import OwnershipMir.Execution

/-! Source commands and MIR share only structured control. Their primitive
operations and operational meanings are different. Loops unfold at runtime;
neither admission nor safety assumes termination. -/
namespace OwnershipMir

variable {authority : Authority}

inductive Code (n : Nat) (instruction : Type) where
  | halt
  | act (op : instruction) (next : Code n instruction)
  | branch (guard : Fin n) (yes no : Code n instruction)
  | loop (guard : Fin n) (body next : Code n instruction)

def Code.append {n : Nat} {α : Type} : Code n α → Code n α → Code n α
  | .halt, tail => tail
  | .act op next, tail => .act op (next.append tail)
  | .branch guard yes no, tail => .branch guard (yes.append tail) (no.append tail)
  | .loop guard body next, tail => .loop guard body (next.append tail)

@[simp] theorem Code.append_halt {n : Nat} {α : Type} (code : Code n α) : code.append .halt = code := by
  induction code <;> simp_all [Code.append]

/-- Precision policy: both branches establish the same exact Context and a
loop preserves its invariant Context. These are checking restrictions, not
requirements imposed by Code execution on arbitrary machine states. -/
inductive Code.Checked {n : Nat} {α : Type} (rule : Context n → α → Context n → Prop) :
    Context n → Code n α → Context n → Prop where
  | halt {context} : Checked rule context .halt context
  | act {before middle after op next} (head : rule before op middle)
      (tail : Checked rule middle next after) : Checked rule before (.act op next) after
  | branch {before after guard yes no} (scalar : before.slots guard = some (.leaf .data))
      (left : Checked rule before yes after) (right : Checked rule before no after) :
      Checked rule before (.branch guard yes no) after
  | loop {before after guard body next} (scalar : before.slots guard = some (.leaf .data))
      (iteration : Checked rule before body before) (tail : Checked rule before next after) :
      Checked rule before (.loop guard body next) after

theorem Code.Checked.append {n : Nat} {α : Type} {rule : Context n → α → Context n → Prop}
    {before middle after : Context n} {first last : Code n α}
    (head : Code.Checked rule before first middle) (tail : Code.Checked rule middle last after) :
    Code.Checked rule before (first.append last) after := by
  induction head with
  | halt => exact tail
  | act instruction next ih => exact .act instruction (ih tail)
  | branch scalar left right leftIH rightIH => exact .branch scalar (leftIH tail) (rightIH tail)
  | loop scalar body next _ nextIH => exact .loop scalar body (nextIH tail)

structure Configuration (n : Nat) (α : Type) where
  code : Code n α
  state : State n

def observe {n : Nat} (guard : Fin n) (state : State n) : Option Bool :=
  match state.slots guard with
  | some (.leaf (.data value)) => some (value != 0)
  | _ => none

inductive Step {n : Nat} {α : Type} (exec : α → State n → Option (State n)) :
    Configuration n α → Configuration n α → Prop where
  | act {op next state after} (executed : exec op state = some after) :
      Step exec ⟨.act op next, state⟩ ⟨next, after⟩
  | branch {guard yes no state choice} (observed : observe guard state = some choice) :
      Step exec ⟨.branch guard yes no, state⟩ ⟨if choice then yes else no, state⟩
  | loop {guard body next state choice} (observed : observe guard state = some choice) :
      Step exec ⟨.loop guard body next, state⟩
        ⟨if choice then body.append (.loop guard body next) else next, state⟩


theorem Step.deterministic {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before first second : Configuration n α} (left : Step exec before first)
    (right : Step exec before second) : first = second := by
  cases left <;> cases right <;> simp_all

theorem Step.not_halt {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before after : Configuration n α} (step : Step exec before after) : before.code ≠ .halt := by
  cases step <;> simp


def Safe {n : Nat} {α : Type} (signature : Signature)
    (rule : Context n → α → Context n → Prop) (final : Context n) (config : Configuration n α) : Prop :=
  ∃ current, config.state.Typed signature current ∧ Code.Checked rule current config.code final

/-- Progress is required only when constructing an instruction step. -/
def InstructionProgress {n : Nat} {α : Type} (signature : Signature)
    (rule : Context n → α → Context n → Prop) (exec : α → State n → Option (State n)) : Prop :=
  ∀ {before after op}, rule before op after → ∀ {state}, state.Typed signature before →
    ∃ next, exec op state = some next

/-- Preservation consumes an actual execution, without assuming local progress.
Control operations may instead advance through activation transitions. -/
def InstructionPreservation {n : Nat} {α : Type} (signature : Signature)
    (rule : Context n → α → Context n → Prop) (exec : α → State n → Option (State n)) : Prop :=
  ∀ {before after op}, rule before op after → ∀ {state next}, state.Typed signature before →
    exec op state = some next → next.Typed signature after ∧ Conserves signature state next

theorem observe_ready {n : Nat} {signature : Signature} {state : State n} {context : Context n}
    (typed : state.Typed signature context) {guard : Fin n} (scalar : context.slots guard = some (.leaf .data)) :
    ∃ choice, observe guard state = some choice := by
  obtain ⟨value, found, kind⟩ := Option.map_eq_some_iff.mp ((typed.1 guard).trans scalar)
  cases value <;> simp only [Value.kind, Tree.map, Tree.leaf.injEq] at kind
  all_goals try { contradiction }
  rename_i atom
  cases atom with
  | data payload => exact ⟨payload != 0, by simp [observe, found]⟩
  | owner identity => cases h : signature identity <;> simp [Atom.kind, h, LinearKind.kind] at kind

theorem Safe.progress {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {config : Configuration n α} (safe : Safe signature rule final config)
    (localProgress : InstructionProgress signature rule exec) :
    config.code = .halt ∨ ∃ next, Step exec config next := by
  obtain ⟨current, typed, checked⟩ := safe
  cases config with
  | mk code state =>
    cases checked with
    | halt => exact Or.inl rfl
    | act head tail =>
      obtain ⟨after, executed⟩ := localProgress head typed
      exact Or.inr ⟨_, .act executed⟩
    | branch scalar left right =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .branch observed⟩
    | loop scalar body tail =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .loop observed⟩

/-- Preservation and ownership framing consume the same local operation proof. -/
theorem Safe.step {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {before after : Configuration n α} (safe : Safe signature rule final before)
    (preservation : InstructionPreservation signature rule exec) (step : Step exec before after) :
    Safe signature rule final after ∧ Conserves signature before.state after.state := by
  obtain ⟨current, typed, checked⟩ := safe
  cases step with
  | act executed =>
    cases checked with
    | act head tail =>
      obtain ⟨realized, conserved⟩ := preservation head typed executed
      exact ⟨⟨_, realized, tail⟩, conserved⟩
  | @branch guard yes no state choice observed =>
    cases checked with
    | branch scalar left right =>
      refine ⟨?_, Conserves.refl _ _⟩
      cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ⟨_, typed, right⟩
      · exact ⟨_, typed, left⟩
  | @loop guard body next state choice observed =>
    cases checked with
    | loop scalar iteration tail =>
      refine ⟨?_, Conserves.refl _ _⟩
      cases choice <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · exact ⟨_, typed, tail⟩
      · exact ⟨_, typed, iteration.append (.loop scalar iteration tail)⟩

theorem Safe.run {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {before after : Configuration n α} (safe : Safe signature rule final before)
    (preservation : InstructionPreservation signature rule exec) (run : Run (Step exec) before after) :
    Safe signature rule final after ∧ Conserves signature before.state after.state := by
  induction run with
  | refl => exact ⟨safe, Conserves.refl _ _⟩
  | step head tail ih =>
    obtain ⟨middle, first⟩ := safe.step preservation head
    obtain ⟨last, rest⟩ := ih middle
    exact ⟨last, first.trans rest⟩

/-- This includes intermediate transfer states, not only instruction boundaries. -/
theorem ownership_safety {n : Nat} {signature : Signature} {final : Context n}
    {before after : Configuration n (Op n)} (safe : Safe signature (Op.Checked authority) final before)
    (unique : before.state.Unique) (run : Run (Step Op.exec) before after) :
    Safe signature (Op.Checked authority) final after ∧ after.state.Unique ∧
      Conserves signature before.state after.state ∧
      (after.code = .halt ∨ ∃ next, Step Op.exec after next) := by
  obtain ⟨preserved, conserved⟩ := safe.run Op.Checked.executed run
  exact ⟨preserved, conserved.unique unique, conserved, preserved.progress Op.Checked.progress⟩

end OwnershipMir
