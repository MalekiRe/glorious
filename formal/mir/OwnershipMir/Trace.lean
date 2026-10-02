import OwnershipMir.Blocks

namespace OwnershipMir

/-- Observable ownership actions. Release occurs at the actual drop, not at
selection: the intervening transfer-register state remains observable. -/
inductive OwnershipEvent (n : Nat) where
  | detach (place : Place n)
  | deconstruct (place : Place n)
  | install (place : Place n)
  | duplicate (place : Place n)
  | release

def Op.event {n : Nat} : Op n → OwnershipEvent n
  | .take place .whole => .detach place
  | .take place .deconstruct => .deconstruct place
  | .put place => .install place
  | .copy place => .duplicate place
  | .drop => .release

def Configuration.events {n : Nat} (config : Configuration n (Op n)) : List (OwnershipEvent n) :=
  match config.code with
  | .act op _ => [op.event]
  | _ => []

/-- Events are interpreted from successful machine transitions; they neither
update another machine state nor supply permission to execute an instruction. -/
inductive OwnershipTrace {n : Nat} :
    Configuration n (Op n) → Configuration n (Op n) → List (OwnershipEvent n) → Prop where
  | refl (state) : OwnershipTrace state state []
  | step {before middle after events} (head : Step Op.exec before middle)
      (tail : OwnershipTrace middle after events) :
      OwnershipTrace before after (before.events ++ events)

theorem OwnershipTrace.run {n : Nat} {before after : Configuration n (Op n)} {events}
    (trace : OwnershipTrace before after events) : Run (Step Op.exec) before after := by
  induction trace with
  | refl => exact .refl _
  | step head tail ih => exact .step head ih

theorem OwnershipTrace.of_run {n : Nat} {before after : Configuration n (Op n)}
    (run : Run (Step Op.exec) before after) : ∃ events, OwnershipTrace before after events := by
  induction run with
  | refl => exact ⟨[], .refl _⟩
  | step head tail ih => obtain ⟨events, trace⟩ := ih; exact ⟨_, .step head trace⟩

theorem OwnershipTrace.trans {n : Nat} {before middle after : Configuration n (Op n)} {first last}
    (head : OwnershipTrace before middle first) (tail : OwnershipTrace middle after last) :
    OwnershipTrace before after (first ++ last) := by
  induction head with
  | refl => exact tail
  | step step rest ih => simpa [List.append_assoc] using OwnershipTrace.step step (ih tail)

theorem OwnershipTrace.empty_of_halt {n : Nat} {before after : Configuration n (Op n)} {events}
    (trace : OwnershipTrace before after events) (halted : before.code = .halt) : events = [] := by
  cases trace with
  | refl => rfl
  | step head tail => exact False.elim (head.not_halt halted)

/-- Determinism compares finite observations without assuming either endpoint
halts. The residual trace identifies which boundary was crossed. -/
theorem OwnershipTrace.compare {n : Nat} {before left right : Configuration n (Op n)} {first last}
    (a : OwnershipTrace before left first) (b : OwnershipTrace before right last) :
    (∃ rest, first ++ rest = last ∧ OwnershipTrace left right rest) ∨
    (∃ rest, last ++ rest = first ∧ OwnershipTrace right left rest) := by
  induction a generalizing right last with
  | refl => exact Or.inl ⟨last, rfl, b⟩
  | step head tail ih =>
    cases b with
    | refl => exact Or.inr ⟨_, rfl, .step head tail⟩
    | step first rest =>
      cases head.deterministic first
      rcases ih rest with ⟨suffix, equal, trace⟩ | ⟨suffix, equal, trace⟩
      · exact Or.inl ⟨suffix, by simpa only [List.append_assoc] using congrArg (_ ++ ·) equal, trace⟩
      · exact Or.inr ⟨suffix, by simpa only [List.append_assoc] using congrArg (_ ++ ·) equal, trace⟩

theorem OwnershipTrace.terminal_unique {n : Nat} {before middle after : Configuration n (Op n)} {first last}
    (left : OwnershipTrace before middle first) (leftHalt : middle.code = .halt)
    (right : OwnershipTrace before after last) (rightHalt : after.code = .halt) : first = last := by
  rcases left.compare right with ⟨rest, equal, residual⟩ | ⟨rest, equal, residual⟩
  · simpa only [residual.empty_of_halt leftHalt, List.append_nil] using equal
  · simpa only [residual.empty_of_halt rightHalt, List.append_nil] using equal.symm

theorem OwnershipTrace.prefix {n : Nat} {before middle after : Configuration n (Op n)} {first all}
    (observed : OwnershipTrace before middle first) (complete : OwnershipTrace before after all)
    (halted : after.code = .halt) : first.IsPrefix all := by
  rcases observed.compare complete with ⟨rest, equal, _⟩ | ⟨rest, equal, residual⟩
  · exact ⟨rest, equal⟩
  · have same : first = all := by
      simpa only [residual.empty_of_halt halted, List.append_nil] using equal.symm
    exact ⟨[], by simpa only [List.append_nil] using same⟩

theorem Block.exec_trace {n : Nat} (ops : List (Op n)) {before after : State n}
    (executed : Block.exec Op.exec ops before = some after) (next : Code n (Op n)) :
    OwnershipTrace ⟨Block.emit ops next, before⟩ ⟨next, after⟩ (ops.map Op.event) := by
  induction ops generalizing before with
  | nil => cases Option.some.inj executed; exact .refl _
  | cons op rest ih =>
    obtain ⟨middle, head, tail⟩ := Option.bind_eq_some_iff.mp executed
    exact .step (.act head) (ih tail)

end OwnershipMir
