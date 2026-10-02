import OwnershipMir.Lowering

namespace OwnershipMir

/-- Source readiness follows from syntactic checking and the initial store.
Preservation/conservation then reuse the proved MIR implementation. -/
theorem Command.Checked.sound {n : Nat} {signature : Signature} {before after : Context n}
    {command : Command n} (checked : Command.Checked before command after) {state : State n}
    (typed : state.Typed signature before) :
    ∃ next, command.exec state = some next ∧ next.Typed signature after ∧ Conserves signature state next := by
  have ready : ∃ next, command.exec state = some next := by
    cases checked with
    | @move source target kind empty found vacant =>
      have unused : state.temp = none := by simpa [empty] using typed.2
      have available : state.slots target = none := by simpa [vacant] using typed.1 target
      obtain ⟨value, live, _⟩ := Option.map_eq_some_iff.mp ((typed.1 source).trans found)
      simp [Command.exec, unused, live, available]
    | @copy source target empty found vacant =>
      have unused : state.temp = none := by simpa [empty] using typed.2
      have available : state.slots target = none := by simpa [vacant] using typed.1 target
      obtain ⟨value, live, _⟩ := Option.map_eq_some_iff.mp ((typed.1 source).trans found)
      simp [Command.exec, unused, live, available]
    | @dispose source kind empty found allowed =>
      have unused : state.temp = none := by simpa [empty] using typed.2
      obtain ⟨value, live, _⟩ := Option.map_eq_some_iff.mp ((typed.1 source).trans found)
      simp [Command.exec, unused, live]
  obtain ⟨next, executed⟩ := ready
  obtain ⟨middle, first, last⟩ := Command.exec_lower executed
  have entry : Safe signature Op.Checked after ⟨command.emit .halt, state⟩ :=
    ⟨before, typed, checked.lower .halt⟩
  have run : Run Op.exec ⟨command.emit .halt, state⟩ ⟨.halt, next⟩ :=
    .step (.act first) (.step (.act last) (.refl _))
  obtain ⟨⟨current, realized, remaining⟩, conserved⟩ := entry.run Op.Checked.sound run
  cases remaining
  exact ⟨next, executed, realized, conserved⟩

theorem Step.deterministic {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before first second : Configuration n α} (left : Step exec before first)
    (right : Step exec before second) : first = second := by
  cases left <;> cases right <;> simp_all

theorem Step.not_halt {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before after : Configuration n α} (step : Step exec before after) : before.code ≠ .halt := by
  cases step <;> simp

@[simp] theorem lower_halt {n : Nat} (source : Code n (Command n)) :
    lower source = .halt ↔ source = .halt := by
  cases source <;> simp [lower, Command.emit]

/-- A target prefix is either at a source boundary or one physical step before
it. The latter accounts for the live transfer register, not an assumed atomic
implementation. It cannot match a halted or infinitely stuttering target. -/
def Matches {n : Nat} (source : Configuration n (Command n)) (target : Configuration n (Op n)) : Prop :=
  target = ⟨lower source.code, source.state⟩ ∨
    Step Op.exec target ⟨lower source.code, source.state⟩

theorem Matches.advance {n : Nat} {signature : Signature} {final : Context n}
    {source : Configuration n (Command n)} {before after : Configuration n (Op n)}
    (matched : Matches source before) (safe : Safe signature Command.Checked final source)
    (step : Step Op.exec before after) :
    ∃ next, Run Command.exec source next ∧ Safe signature Command.Checked final next ∧ Matches next after := by
  rcases matched with boundary | pending
  · subst before
    rcases safe.progress Command.Checked.sound with halted | ⟨next, sourceStep⟩
    · exact False.elim (step.not_halt (by simp [halted, lower]))
    · obtain ⟨middle, first, last⟩ := lower_step sourceStep
      have same := first.deterministic step
      subst middle
      exact ⟨next, .step sourceStep (.refl _), (safe.step Command.Checked.sound sourceStep).1, last⟩
  · have same := pending.deterministic step
    exact ⟨source, .refl _, safe, Or.inl same.symm⟩

theorem Matches.run {n : Nat} {signature : Signature} {final : Context n}
    {source : Configuration n (Command n)} {before after : Configuration n (Op n)}
    (matched : Matches source before) (safe : Safe signature Command.Checked final source)
    (run : Run Op.exec before after) :
    ∃ next, Run Command.exec source next ∧ Safe signature Command.Checked final next ∧ Matches next after := by
  induction run generalizing source with
  | refl => exact ⟨source, .refl _, safe, matched⟩
  | step head tail ih =>
    obtain ⟨middle, earlier, current, relation⟩ := matched.advance safe head
    obtain ⟨next, suffix, final, relation⟩ := ih relation current
    exact ⟨next, earlier.trans suffix, final, relation⟩

/-- No extra target return is possible: all finite returned states correspond
in both directions, including every slot's value and initialization hole. -/
theorem compiled_return_iff {n : Nat} {signature : Signature} {before final : Context n}
    {source : Code n (Command n)} (checked : Code.Checked Command.Checked before source final)
    {initial result : State n} (typed : initial.Typed signature before) :
    Run Op.exec ⟨lower source, initial⟩ ⟨.halt, result⟩ ↔
      Run Command.exec ⟨source, initial⟩ ⟨.halt, result⟩ := by
  constructor
  · intro run
    obtain ⟨next, sourceRun, _, relation⟩ :=
      Matches.run (source := ⟨source, initial⟩) (Or.inl rfl) ⟨before, typed, checked⟩ run
    rcases relation with boundary | pending
    · have code : next.code = .halt := (lower_halt _).mp (congrArg Configuration.code boundary).symm
      have state : next.state = result := (congrArg Configuration.state boundary).symm
      have same : next = ⟨.halt, result⟩ := by cases next; simp_all
      exact same ▸ sourceRun
    · exact False.elim (pending.not_halt rfl)
  · exact lower_run

/-- A checked program either returns or has an actual infinite step trace.
Safety is carried by every finite prefix; no termination premise is introduced. -/
theorem Safe.behavior {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {start : Configuration n α} (safe : Safe signature rule final start)
    (localSound : InstructionSound signature rule exec) :
    (∃ result, Run exec start ⟨.halt, result⟩) ∨
    (∃ trace : Nat → Configuration n α, trace 0 = start ∧
      ∀ i, Step exec (trace i) (trace (i + 1)) ∧ Run exec start (trace i) ∧
        Safe signature rule final (trace i) ∧ Conserves signature start.state (trace i).state) := by
  classical
  by_cases returned : ∃ result, Run exec start ⟨.halt, result⟩
  · exact Or.inl returned
  · have advances : ∀ state, Run exec start state → ∃ next, Step exec state next := by
      intro state reached
      rcases (safe.run localSound reached).1.progress localSound with halted | next
      · apply False.elim
        apply returned
        refine ⟨state.state, ?_⟩
        have same : state = ⟨.halt, state.state⟩ := by cases state; simp_all
        exact same ▸ reached
      · exact next
    let trace : Nat → {state : Configuration n α // Run exec start state} :=
      Nat.rec ⟨start, .refl _⟩ (fun _ previous =>
        ⟨Classical.choose (advances previous.val previous.property),
          previous.property.trans (.step (Classical.choose_spec (advances previous.val previous.property)) (.refl _))⟩)
    refine Or.inr ⟨fun i => (trace i).val, rfl, fun i => ?_⟩
    exact ⟨Classical.choose_spec (advances (trace i).val (trace i).property),
      (trace i).property, safe.run localSound (trace i).property⟩

def Diverges {n : Nat} {α : Type} (exec : α → State n → Option (State n))
    (start : Configuration n α) : Prop :=
  ∃ trace : Nat → Configuration n α, trace 0 = start ∧
    ∀ i, Step exec (trace i) (trace (i + 1))

theorem Run.excludes_divergence {n : Nat} {α : Type} {exec : α → State n → Option (State n)}
    {before after : Configuration n α} (run : Run exec before after) (halted : after.code = .halt) :
    ¬ Diverges exec before := by
  induction run with
  | refl =>
    rintro ⟨trace, initial, steps⟩
    exact (steps 0).not_halt (by rw [initial]; exact halted)
  | @step before middle after head tail ih =>
    rintro ⟨trace, initial, steps⟩
    have first : Step exec before (trace 1) := by simpa [initial] using steps 0
    have same := head.deterministic first
    apply ih halted
    exact ⟨fun i => trace (i + 1), same.symm, fun i => by
      simpa [Nat.add_assoc] using steps (i + 1)⟩

theorem Safe.diverges_iff {n : Nat} {α : Type} {signature : Signature} {final : Context n}
    {rule : Context n → α → Context n → Prop} {exec : α → State n → Option (State n)}
    {start : Configuration n α} (safe : Safe signature rule final start)
    (localSound : InstructionSound signature rule exec) :
    Diverges exec start ↔ ¬ ∃ result, Run exec start ⟨.halt, result⟩ := by
  constructor
  · intro infinite ⟨result, returned⟩
    exact returned.excludes_divergence rfl infinite
  · intro absent
    rcases safe.behavior localSound with returned | ⟨trace, initial, safeSteps⟩
    · exact False.elim (absent returned)
    · exact ⟨trace, initial, fun i => (safeSteps i).1⟩

/-- Divergence is preserved and reflected as an actual infinite execution,
not identified with stuckness or inferred merely from an absent result. -/
theorem compiled_diverges_iff {n : Nat} {signature : Signature} {before final : Context n}
    {source : Code n (Command n)} (checked : Code.Checked Command.Checked before source final)
    {initial : State n} (typed : initial.Typed signature before) :
    Diverges Op.exec ⟨lower source, initial⟩ ↔ Diverges Command.exec ⟨source, initial⟩ := by
  have targetSafe : Safe signature Op.Checked final ⟨lower source, initial⟩ :=
    ⟨before, typed, lower_checked checked⟩
  have sourceSafe : Safe signature Command.Checked final ⟨source, initial⟩ := ⟨before, typed, checked⟩
  rw [targetSafe.diverges_iff Op.Checked.sound, sourceSafe.diverges_iff Command.Checked.sound]
  constructor
  · intro absent ⟨result, run⟩
    exact absent ⟨result, lower_run run⟩
  · intro absent ⟨result, run⟩
    exact absent ⟨result, (compiled_return_iff checked typed).mp run⟩

end OwnershipMir
