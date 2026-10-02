import OwnershipMir.Calls

namespace OwnershipMir.Calls

theorem argument_typed {n : Nat} {signature : Signature} {value : Value} {shape : Shape}
    (typed : value.kind signature = shape) :
    (State.mk (argumentSlots value) none : State (n + 1)).Typed signature ⟨argumentSlots shape, none⟩ := by
  refine ⟨fun i => ?_, rfl⟩
  exact Fin.cases (by simpa [argumentSlots] using congrArg some typed) (fun _ => rfl) i

theorem typed_empty {n : Nat} {signature : Signature} {state : State (n + 1)}
    (typed : state.Typed signature (emptyContext n)) : state = emptyState n := by
  have slots : state.slots = fun _ => none := funext (fun i => Option.map_eq_none_iff.mp (typed.1 i))
  have temp : state.temp = none := Option.map_eq_none_iff.mp typed.2
  cases state
  simp_all [emptyState]

theorem Function.cleanup_checked {n : Nat} {function : Function n}
    (admitted : (activationScope n).Admitted function.cleanupContext) :
    Code.Checked Op.Checked function.cleanupContext function.cleanup (emptyContext n) := by
  have slots : clearSlots (activationScope n).owners function.cleanupContext.slots = fun _ => none := by
    funext i
    exact if_pos (List.mem_finRange i)
  simpa only [Function.cleanup, clearContext, slots, emptyContext] using lower_checked (Scope.checked admitted)

theorem Instruction.Checked.executed {n : Nat} {program : Program n} {signature : Signature}
    {before after : Context (n + 1)} {instruction : Instruction n}
    (checked : Instruction.Checked program before instruction after) {state next : State (n + 1)}
    (typed : state.Typed signature before) (executed : instruction.exec state = some next) :
    next.Typed signature after ∧ Conserves signature state next := by
  cases checked with
  | operation checked =>
    obtain ⟨effect, realized, legal⟩ := checked.effect typed executed
    exact ⟨realized, effect.conserves legal.conservationAllowed⟩
  | call => cases executed

theorem local_step {n : Nat} {program : Program n} {signature : Signature}
    {before output : Context (n + 1)} {code next : Body n} {state after : State (n + 1)}
    (typed : state.Typed signature before)
    (checked : Code.Checked (Instruction.Checked program) before code output)
    (step : OwnershipMir.Step Instruction.exec ⟨code, state⟩ ⟨next, after⟩) :
    ∃ current, after.Typed signature current ∧ Code.Checked (Instruction.Checked program) current next output ∧
      Conserves signature state after := by
  cases step with
  | act executed =>
    cases checked with
    | act head tail =>
      obtain ⟨realized, conserved⟩ := head.executed typed executed
      exact ⟨_, realized, tail, conserved⟩
  | branch observed =>
    cases checked with
    | branch scalar left right =>
      split
      · exact ⟨_, typed, left, Conserves.refl _ _⟩
      · exact ⟨_, typed, right, Conserves.refl _ _⟩
  | loop observed =>
    cases checked with
    | loop scalar body tail =>
      split
      · exact ⟨_, typed, body.append (.loop scalar body tail), Conserves.refl _ _⟩
      · exact ⟨_, typed, tail, Conserves.refl _ _⟩

/-- The activation invariant follows every physical phase: body execution,
argument transfer, protected result installation, cleanup, and empty retirement. -/
theorem Safe.preservation {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) : Safe program signature final after := by
  cases step with
  | operation step =>
    cases safe with
    | body typed checked retained =>
      obtain ⟨current, realized, remaining, _⟩ := local_step typed checked step
      exact .body realized remaining retained
  | @enter identity destination next cleanup state stack function argument resolved resident =>
    cases safe with
    | body typed checked retained =>
      cases checked with
      | act head tail =>
        cases head with
        | call selected argumentType put =>
          cases Option.some.inj (resolved.symm.trans selected)
          have classified : argument.kind signature = function.input := by
            simpa [resident] using typed.2.trans argumentType
          have admitted := functions identity function resolved
          exact .body (argument_typed classified) admitted.1
            (.cons typed.1 rfl put tail retained (Function.cleanup_checked admitted.2.1))
  | @handoff cleanup state frame stack slots installed =>
    cases safe with
    | body typed checked retained =>
      cases checked
      cases retained with
      | cons resident returned put next outer release =>
        obtain ⟨effect, realized, _⟩ := put.effect (state := ⟨frame.slots, state.temp⟩) ⟨resident, typed.2.trans returned⟩ installed
        exact .cleaning (before := ⟨_, none⟩) ⟨typed.1, rfl⟩ release (.cons realized next outer)
  | clean step =>
    cases safe with
    | cleaning typed checked retained =>
      obtain ⟨⟨current, realized, remaining⟩, _⟩ :=
        (OwnershipMir.Safe.step (signature := signature) ⟨_, typed, checked⟩ Op.Checked.sound step)
      exact .cleaning realized remaining retained
  | retire =>
    cases safe with
    | cleaning typed checked retained =>
      cases retained with
      | cons resident next outer => exact .body resident next outer

/-- Recursion is admitted through body checking. Progress never asks for a
completed callee execution, successful allocation, or terminating cleanup. -/
theorem Safe.progress {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {config : Configuration n} (safe : Safe program signature final config) :
    config.Terminal ∨ ∃ next, Transition program config next := by
  cases safe with
  | @body code cleanup state stack before output typed checked retained =>
    cases checked with
    | halt =>
      cases retained with
      | nil => exact Or.inl ⟨cleanup, rfl, rfl⟩
      | @cons frame stack output cleanup final slots shape after callerExit resident returned put next outer release =>
        obtain ⟨result, executed, realized, _⟩ := put.sound (state := ⟨frame.slots, state.temp⟩) ⟨resident, typed.2.trans returned⟩
        have empty : result.temp = none := by
          cases put
          exact Option.map_eq_none_iff.mp realized.2
        cases result with
        | mk slots temp =>
          cases empty
          exact Or.inr ⟨_, .handoff executed⟩
    | act head tail =>
      cases head with
      | operation checked =>
        obtain ⟨next, executed, _, _⟩ := checked.sound typed
        exact Or.inr ⟨_, .operation (.act executed)⟩
      | call resolved argument result =>
        obtain ⟨value, live, _⟩ := Option.map_eq_some_iff.mp (typed.2.trans argument)
        exact Or.inr ⟨_, .enter resolved live⟩
    | branch scalar left right =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .operation (.branch observed)⟩
    | loop scalar body tail =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .operation (.loop observed)⟩
  | @cleaning code state stack before typed checked retained =>
    have start : OwnershipMir.Safe signature Op.Checked (emptyContext n) ⟨code, state⟩ := ⟨before, typed, checked⟩
    rcases start.progress Op.Checked.sound with halted | ⟨next, step⟩
    · cases halted
      cases checked
      have same := typed_empty typed
      subst state
      cases retained
      exact Or.inr ⟨_, .retire⟩
    · cases next with
      | mk code state => exact Or.inr ⟨_, .clean step⟩

theorem Safe.execution {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (run : Execution program before after) : Safe program signature final after := by
  induction run with
  | refl => exact safe
  | step head tail ih => exact ih (safe.preservation functions head)

end OwnershipMir.Calls
