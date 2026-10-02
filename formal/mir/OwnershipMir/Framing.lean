import OwnershipMir.Scope

namespace OwnershipMir

/-- A syntactic write footprint, not another ownership analysis. It states
which instructions can physically change a root, independent of checking. -/
def Op.Fixes {n : Nat} (slot : Fin n) : Op n → Prop
  | .take place _ | .put place => slot ≠ place.root
  | .copy _ | .drop => True

theorem Op.exec_frame {n : Nat} {op : Op n} {before after : State n} (slot : Fin n)
    (fixes : op.Fixes slot) (executed : op.exec before = some after) :
    after.slots slot = before.slots slot := by
  cases Op.effect_of_exec executed with
  | take found live extracted empty => exact update_other _ _ _ _ fixes
  | put found live available => exact update_other _ _ _ _ fixes
  | copy found live empty => rfl
  | drop live => rfl

def Code.Fixes {n : Nat} (slot : Fin n) : Code n (Op n) → Prop
  | .halt => True
  | .act op next => op.Fixes slot ∧ next.Fixes slot
  | .branch _ yes no => yes.Fixes slot ∧ no.Fixes slot
  | .loop _ body next => body.Fixes slot ∧ next.Fixes slot

theorem Code.Fixes.append {n : Nat} {slot : Fin n} {first last : Code n (Op n)}
    (head : first.Fixes slot) (tail : last.Fixes slot) : (first.append last).Fixes slot := by
  induction first <;> simp_all [Code.append, Code.Fixes]

theorem Step.frame {n : Nat} {slot : Fin n} {before after : Configuration n (Op n)}
    (fixes : before.code.Fixes slot) (step : Step Op.exec before after) :
    after.code.Fixes slot ∧ after.state.slots slot = before.state.slots slot := by
  cases step with
  | act executed => exact ⟨fixes.2, Op.exec_frame slot fixes.1 executed⟩
  | branch observed =>
    split
    · exact ⟨fixes.1, rfl⟩
    · exact ⟨fixes.2, rfl⟩
  | loop observed =>
    split
    · exact ⟨fixes.1.append fixes, rfl⟩
    · exact ⟨fixes.2, rfl⟩

theorem Run.frame {n : Nat} {slot : Fin n} {before after : Configuration n (Op n)}
    (fixes : before.code.Fixes slot) (run : Run Op.exec before after) :
    after.code.Fixes slot ∧ after.state.slots slot = before.state.slots slot := by
  induction run with
  | refl => exact ⟨fixes, rfl⟩
  | step head tail ih =>
    obtain ⟨middle, first⟩ := head.frame fixes
    obtain ⟨final, last⟩ := ih middle
    exact ⟨final, last.trans first⟩

theorem lowered_disposal_fixes {n : Nat} (commands : List (Command n)) (owners : List (Fin n))
    (within : ∀ command ∈ commands, command.DisposesIn owners) (slot : Fin n) (retained : slot ∉ owners) :
    (lower (sequence commands)).Fixes slot := by
  induction commands with
  | nil => trivial
  | cons command commands ih =>
    have first := within command (by simp)
    have tail := ih (fun c member => within c (by simp [member]))
    cases command with
    | move mode source target => cases first
    | copy source target => cases first
    | dispose place =>
      exact ⟨by intro same; exact retained (same ▸ first), trivial, tail⟩

/-- Every cleanup prefix leaves protected result and retained storage exactly
unchanged, including prefixes paused with a resident in the transfer register. -/
theorem Scope.cleanup_frame {n : Nat} (scope : Scope n) (context : Context n)
    {initial : State n} {reached : Configuration n (Op n)}
    (run : Run Op.exec ⟨lower (sequence (scope.commands context)), initial⟩ reached)
    (slot : Fin n) (retained : slot ∉ scope.owners) : reached.state.slots slot = initial.slots slot := by
  have within : ∀ command ∈ scope.commands context, command.DisposesIn scope.owners := by
    intro command member
    have located := cleanupOwners_disposes scope.owners.reverse context command member
    cases command with
    | move mode source target => cases located
    | copy source target => cases located
    | dispose place => exact List.mem_reverse.mp located
  exact (run.frame (lowered_disposal_fixes _ _ within slot retained)).2

private theorem Run.terminal_unique {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {start left right : Configuration n α} (first : Run exec start left) (halted : left.code = .halt)
    (second : Run exec start right) (returned : right.code = .halt) : left = right := by
  induction first generalizing right with
  | refl => cases second with
    | refl => rfl
    | step head tail => exact False.elim (head.not_halt halted)
  | step head tail ih =>
    cases second with
    | refl => exact False.elim (head.not_halt returned)
    | step other rest =>
      cases head.deterministic other
      exact ih halted rest returned

/-- Determinism rules out additional terminal outcomes, not just extra steps. -/
theorem Run.return_unique {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {start : Configuration n α} {left right : State n}
    (first : Run exec start ⟨.halt, left⟩) (second : Run exec start ⟨.halt, right⟩) : left = right :=
  congrArg Configuration.state (first.terminal_unique rfl second rfl)

/-- Full return correspondence for the independently specified atomic scope
boundary. Cleanup has exactly its prescribed result, not merely a safe one. -/
theorem Scope.exit_iff {n : Nat} {signature : Signature} {scope : Scope n} {context : Context n}
    (admitted : scope.Admitted context) {state result : State n} (typed : state.Typed signature context) :
    Run Op.exec ⟨lower (sequence (scope.commands context)), state⟩ ⟨.halt, result⟩ ↔ result = scope.exit state := by
  constructor
  · intro run
    exact run.return_unique (Scope.exit_run admitted typed).1
  · intro same
    subst result
    exact (Scope.exit_run admitted typed).1

end OwnershipMir
