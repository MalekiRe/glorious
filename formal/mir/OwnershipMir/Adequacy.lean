import OwnershipMir.Lowering

namespace OwnershipMir

variable {authority : Authority}

/-- Source readiness follows from syntactic checking and the initial store.
Preservation/conservation then reuse the proved MIR implementation. -/
theorem Command.Checked.sound {n : Nat} {signature : Signature} {before after : Context n}
    {command : Command n} (checked : (Command.Checked authority) before command after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, command.exec state = some next ∧ next.Typed signature after ∧ Conserves signature state next := by
  have checkedBlock : Code.Checked (Op.Checked authority) before (sequence command.block) after := checked.lower .halt
  obtain ⟨result, executed, realized, conserved⟩ :=
    Block.checked_exec Op.Checked.progress Op.Checked.executed command.block checkedBlock typed
  exact ⟨result, by rwa [Command.exec_eq], realized, conserved⟩

theorem Command.Checked.progress {n : Nat} {signature : Signature} {before after : Context n}
    {command : Command n} (checked : (Command.Checked authority) before command after) {state : State n}
    (typed : state.Typed signature before) : ∃ next, command.exec state = some next := by
  obtain ⟨next, executed, _, _⟩ := checked.sound typed
  exact ⟨next, executed⟩

theorem Command.Checked.executed {n : Nat} {signature : Signature} {before after : Context n}
    {command : Command n} (checked : (Command.Checked authority) before command after) {state next : State n}
    (typed : state.Typed signature before) (executed : command.exec state = some next) :
    next.Typed signature after ∧ Conserves signature state next := by
  exact Block.executed Op.Checked.executed command.block (checked.lower .halt) typed
    (by rwa [Command.exec_eq] at executed)

@[simp] theorem lower_halt {n : Nat} (source : Code n (Command n)) :
    lower source = .halt ↔ source = .halt := by
  cases source <;> simp [lower, Command.emit, Command.block_nonempty]

/-- A pending target prefix has a finite residual execution to its source
boundary. No fixed instruction count or intermediate-state shape is assumed. -/
def Matches {n : Nat} (source : Configuration n (Command n)) (target : Configuration n (Op n)) : Prop :=
  Run (Step Op.exec) target ⟨lower source.code, source.state⟩

theorem Matches.advance {n : Nat} {signature : Signature} {final : Context n}
    {source : Configuration n (Command n)} {before after : Configuration n (Op n)}
    (matched : Matches source before) (safe : Safe signature (Command.Checked authority) final source)
    (step : Step Op.exec before after) :
    ∃ next, Run (Step Command.exec) source next ∧ Safe signature (Command.Checked authority) final next ∧ Matches next after := by
  cases matched with
  | refl =>
    rcases safe.progress Command.Checked.progress with halted | ⟨next, sourceStep⟩
    · exact False.elim (step.not_halt (by simp [halted, lower]))
    · obtain ⟨middle, first, rest⟩ := lower_step sourceStep
      have same := first.deterministic step
      subst middle
      exact ⟨next, .step sourceStep (.refl _), (safe.step Command.Checked.executed sourceStep).1, rest⟩
  | step pending rest =>
    cases pending.deterministic step
    exact ⟨source, .refl _, safe, rest⟩

theorem Matches.run {n : Nat} {signature : Signature} {final : Context n}
    {source : Configuration n (Command n)} {before after : Configuration n (Op n)}
    (matched : Matches source before) (safe : Safe signature (Command.Checked authority) final source)
    (run : Run (Step Op.exec) before after) :
    ∃ next, Run (Step Command.exec) source next ∧ Safe signature (Command.Checked authority) final next ∧ Matches next after := by
  induction run generalizing source with
  | refl => exact ⟨source, .refl _, safe, matched⟩
  | step head tail ih =>
    obtain ⟨middle, earlier, current, relation⟩ := matched.advance safe head
    obtain ⟨next, suffix, final, relation⟩ := ih relation current
    exact ⟨next, earlier.trans suffix, final, relation⟩

/-- No extra target return is possible: all finite returned states correspond
in both directions, including every slot's value and initialization hole. -/
theorem compiled_return_iff {n : Nat} {signature : Signature} {before final : Context n}
    {source : Code n (Command n)} (checked : Code.Checked (Command.Checked authority) before source final)
    {initial result : State n} (typed : initial.Typed signature before) :
    Run (Step Op.exec) ⟨lower source, initial⟩ ⟨.halt, result⟩ ↔
      Run (Step Command.exec) ⟨source, initial⟩ ⟨.halt, result⟩ := by
  constructor
  · intro run
    obtain ⟨next, sourceRun, _, relation⟩ :=
      Matches.run (source := ⟨source, initial⟩) (.refl _) ⟨before, typed, checked⟩ run
    have boundary := relation.from_terminal (fun _ step => step.not_halt rfl)
    have code : next.code = .halt := (lower_halt _).mp (congrArg Configuration.code boundary)
    have state : next.state = result := congrArg Configuration.state boundary
    have same : next = ⟨.halt, result⟩ := by cases next; simp_all
    exact same ▸ sourceRun
  · exact lower_run

/-- A checked program either returns or has an actual infinite step trace.
Safety is carried by every finite prefix; no termination premise is introduced. -/
theorem Safe.behavior {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {start : Configuration n α} (safe : Safe signature rule final start)
    (progress : InstructionProgress signature rule exec)
    (preservation : InstructionPreservation signature rule exec) :
    (∃ result, Run (Step exec) start ⟨.halt, result⟩) ∨
    (∃ trace : Nat → Configuration n α, trace 0 = start ∧
      ∀ i, Step exec (trace i) (trace (i + 1)) ∧ Run (Step exec) start (trace i) ∧
        Safe signature rule final (trace i) ∧ Conserves signature start.state (trace i).state) := by
  classical
  by_cases returned : ∃ result, Run (Step exec) start ⟨.halt, result⟩
  · exact Or.inl returned
  · have advances : ∀ state, Run (Step exec) start state → ∃ next, Step exec state next := by
      intro state reached
      rcases (safe.run preservation reached).1.progress progress with halted | next
      · apply False.elim
        apply returned
        refine ⟨state.state, ?_⟩
        have same : state = ⟨.halt, state.state⟩ := by cases state; simp_all
        exact same ▸ reached
      · exact next
    obtain ⟨trace, initial, steps⟩ := diverges_of_progress advances
    exact Or.inr ⟨trace, initial, fun i =>
      ⟨steps i, trace_reachable initial steps i, safe.run preservation (trace_reachable initial steps i)⟩⟩


theorem Safe.diverges_iff {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {start : Configuration n α} (safe : Safe signature rule final start)
    (progress : InstructionProgress signature rule exec)
    (preservation : InstructionPreservation signature rule exec) :
    Diverges (Step exec) start ↔ ¬ ∃ result, Run (Step exec) start ⟨.halt, result⟩ := by
  constructor
  · intro infinite ⟨result, returned⟩
    exact returned.excludes_divergence Step.deterministic (fun _ step => step.not_halt rfl) infinite
  · intro absent
    rcases safe.behavior progress preservation with returned | ⟨trace, initial, safeSteps⟩
    · exact False.elim (absent returned)
    · exact ⟨trace, initial, fun i => (safeSteps i).1⟩

/-- Divergence is preserved and reflected as an actual infinite execution,
not identified with stuckness or inferred merely from an absent result. -/
theorem compiled_diverges_iff {n : Nat} {signature : Signature} {before final : Context n}
    {source : Code n (Command n)} (checked : Code.Checked (Command.Checked authority) before source final)
    {initial : State n} (typed : initial.Typed signature before) :
    Diverges (Step Op.exec) ⟨lower source, initial⟩ ↔ Diverges (Step Command.exec) ⟨source, initial⟩ := by
  have targetSafe : Safe signature (Op.Checked authority) final ⟨lower source, initial⟩ :=
    ⟨before, typed, lower_checked checked⟩
  have sourceSafe : Safe signature (Command.Checked authority) final ⟨source, initial⟩ := ⟨before, typed, checked⟩
  rw [targetSafe.diverges_iff Op.Checked.progress Op.Checked.executed,
    sourceSafe.diverges_iff Command.Checked.progress Command.Checked.executed]
  constructor
  · intro absent ⟨result, run⟩
    exact absent ⟨result, lower_run run⟩
  · intro absent ⟨result, run⟩
    exact absent ⟨result, (compiled_return_iff checked typed).mp run⟩

end OwnershipMir
