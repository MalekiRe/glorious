import OwnershipMir.Calls
import OwnershipMir.LoanFraming

namespace OwnershipMir.Calls
variable {module : Module} {authority : Authority}

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
    (admitted : (activationScope n).Admitted authority function.cleanupContext) :
    Code.Checked (Op.Checked authority) function.cleanupContext function.cleanup (emptyContext n) := by
  have slots : clearSlots (activationScope n).owners function.cleanupContext.slots = fun _ => none := by
    funext i
    exact if_pos (List.mem_finRange i)
  simpa only [Function.cleanup, clearContext, slots, emptyContext] using (Scope.checked admitted)

theorem Instruction.Checked.executed {n : Nat} {program : Program n} {signature : Signature}
    {before after : Context (n + 1)} {instruction : Instruction n}
    (checked : Instruction.Checked program module before instruction after) {state next : State (n + 1)}
    (typed : state.Typed signature before) (executed : instruction.exec state = some next) :
    next.Typed signature after ∧ Conserves signature state next := by
  cases checked with
  | operation checked => exact checked.executed typed executed
  | call => cases executed

theorem StackTyped.frame {n : Nat} {program : Program n} {signature : Signature}
    {before after : Store (n + 1) Atom} {ceiling : Nat} {stack : List (Frame n)}
    {output final : Context (n + 1)} {cleanup : Code (n + 1) (Op (n + 1))}
    (typed : StackTyped program signature before ceiling stack output cleanup final)
    (same : ∀ r, r < ceiling → after.regionKinds signature r = before.regionKinds signature r) :
    StackTyped program signature after ceiling stack output cleanup final := by
  induction typed generalizing after with
  | cons older live resident returned put next outer release ih =>
    have projected := same _ older
    unfold Store.regionKinds at projected
    rw [live] at projected
    obtain ⟨slots, afterLive, classified⟩ := Option.map_eq_some_iff.mp projected
    exact .cons older afterLive (fun i => (congrFun classified i).trans (resident i)) returned put next
      (ih (fun r below => same r (Nat.lt_trans below older))) release
  | nil => exact .nil

theorem ResumeTyped.frame {n : Nat} {program : Program n} {signature : Signature}
    {before after : Store (n + 1) Atom} {ceiling : Nat} {stack : List (Frame n)} {final : Context (n + 1)}
    (typed : ResumeTyped program signature before ceiling stack final)
    (same : ∀ r, r < ceiling → after.regionKinds signature r = before.regionKinds signature r) :
    ResumeTyped program signature after ceiling stack final := by
  cases typed with
  | cons older live resident next outer =>
    have projected := same _ older
    unfold Store.regionKinds at projected
    rw [live] at projected
    obtain ⟨slots, afterLive, classified⟩ := Option.map_eq_some_iff.mp projected
    exact .cons older afterLive ⟨fun i => (congrFun classified i).trans (resident.1 i), resident.2⟩ next
      (outer.frame (fun r below => same r (Nat.lt_trans below older)))

/-- The one store is updated in place logically; preserved caller typing uses
its exact typing projection, never saved snapshots of caller values. -/
theorem Safe.preservation {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (step : Transition program before after) : Safe program signature final after := by
  cases step with
  | operation live step =>
    cases safe with
    | body found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      obtain ⟨⟨current, realized, remaining⟩, _⟩ :=
        OwnershipMir.Safe.step ⟨_, typed, checked⟩ Instruction.Checked.executed step
      exact .body (Store.replace_same (Store.region_bound live) _ _) realized remaining
        (retained.frame (fun r below => by unfold Store.regionKinds; rw [Store.replace_other _ _ _ _ _ (by omega)]))
  | @enter identity destination next cleanup store active stack function argument resolved resident =>
    cases safe with
    | body live typed checked retained =>
      cases checked with
      | act head tail =>
        cases head with
        | call selected argumentType put =>
          cases Option.some.inj (resolved.symm.trans selected)
          have classified : Value.kind signature argument = function.input := by
            simpa [resident] using typed.2.trans argumentType
          have admitted := functions identity function resolved
          have bound := Store.region_bound live
          exact .body (Store.allocate_fresh _ _) (argument_typed classified) admitted.1
            (.cons bound ((Store.allocate_old bound _).trans live) typed.1 rfl put tail
              (retained.frame (fun r below => by unfold Store.regionKinds; rw [Store.allocate_old (Nat.lt_trans below bound) _]))
              (Function.cleanup_checked admitted.2.1))
  | @handoff cleanup store active frame stack caller slots live installed =>
    cases safe with
    | body activeLive typed checked retained =>
      cases checked
      cases retained with
      | cons older callerLive resident returned put next outer release =>
        cases Option.some.inj (live.symm.trans callerLive)
        obtain ⟨_, realized, _⟩ := put.effect (state := ⟨caller, store.temp⟩) ⟨resident, typed.2.trans returned⟩ installed
        exact .cleaning (before := ⟨_, none⟩)
          ((Store.replace_other _ _ _ _ _ (by omega)).trans activeLive) ⟨typed.1, rfl⟩ release
          (.cons older (Store.replace_same (Store.region_bound live) _ _) realized next
            (outer.frame (fun r below => by unfold Store.regionKinds; rw [Store.replace_other _ _ _ _ _ (by omega)])))
  | clean live step =>
    cases safe with
    | cleaning found typed checked retained =>
      cases Option.some.inj (live.symm.trans found)
      obtain ⟨⟨current, realized, remaining⟩, _⟩ :=
        OwnershipMir.Safe.step ⟨_, typed, checked⟩ Op.Checked.executed step
      exact .cleaning (Store.replace_same (Store.region_bound live) _ _) realized remaining
        (retained.frame (fun r below => by unfold Store.regionKinds; rw [Store.replace_other _ _ _ _ _ (by omega)]))
  | retire empty register =>
    cases safe with
    | cleaning live typed checked retained =>
      cases retained with
      | cons older callerLive resident next outer =>
        exact .body ((Store.retire_other _ _ _ (by omega)).trans callerLive)
          (by simpa [Store.retire, register] using resident) next
          (outer.frame (fun r below => by unfold Store.regionKinds; rw [Store.retire_other _ _ _ (by omega)]))

theorem Safe.progress {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    {config : Configuration n} (safe : Safe program signature final config) :
    config.Terminal ∨ ∃ next, Transition program config next := by
  cases safe with
  | @body code cleanup store active slots stack before output module live typed checked retained =>
    cases checked with
    | halt =>
      cases retained with
      | nil => exact Or.inl ⟨cleanup, rfl, rfl⟩
      | @cons ceiling frame stack output cleanup final callerSlots actual result after callerExit callerModule calleeModule older callerLive resident returned put next outer release =>
        obtain ⟨result, executed, realized, _⟩ := put.sound (state := ⟨actual, store.temp⟩) ⟨resident, typed.2.trans returned⟩
        have empty : result.temp = none := by
          cases put
          exact Option.map_eq_none_iff.mp realized.2
        cases result with
        | mk slots temp =>
          cases empty
          exact Or.inr ⟨_, .handoff callerLive executed⟩
    | act head tail =>
      cases head with
      | operation checked =>
        obtain ⟨next, executed⟩ := checked.progress typed
        exact Or.inr ⟨_, .operation live (.act executed)⟩
      | call resolved argument result =>
        obtain ⟨value, resident, _⟩ := Option.map_eq_some_iff.mp (typed.2.trans argument)
        exact Or.inr ⟨_, .enter resolved resident⟩
    | branch scalar left right =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .operation live (.branch observed)⟩
    | loop scalar body tail =>
      obtain ⟨choice, observed⟩ := observe_ready typed scalar
      exact Or.inr ⟨_, .operation live (.loop observed)⟩
  | @cleaning code store active slots stack before module live typed checked retained =>
    have start : OwnershipMir.Safe signature (Op.Checked _) (emptyContext n) ⟨code, ⟨slots, store.temp⟩⟩ := ⟨before, typed, checked⟩
    rcases start.progress Op.Checked.progress with halted | ⟨next, step⟩
    · cases halted
      cases checked
      have same := typed_empty typed
      have emptySlots := congrArg State.slots same
      have emptyTemp := congrArg State.temp same
      cases retained
      exact Or.inr ⟨_, .retire (live.trans (congrArg some emptySlots)) emptyTemp⟩
    · cases next with
      | mk code state => exact Or.inr ⟨_, .clean live step⟩

theorem Safe.execution {n : Nat} {program : Program n} {signature : Signature} {final : Context (n + 1)}
    (functions : program.Checked) {before after : Configuration n} (safe : Safe program signature final before)
    (run : Run (Transition program) before after) : Safe program signature final after := by
  induction run with
  | refl => exact safe
  | step head tail ih => exact ih (safe.preservation functions head)

/-- Retained callers need exact resident typing, not unchanged payloads.
This consumes the physical replacement proof and does not admit a temporary
hole as an initialized caller value. -/
theorem StackTyped.replaceLoan {n : Nat} {program : Program n} {signature : Signature}
    {store : Store (n + 1) Atom} {ceiling : Nat} {stack : List (Frame n)}
    {output final : Context (n + 1)} {cleanup : Code (n + 1) (Op (n + 1))}
    (typed : StackTyped program signature store ceiling stack output cleanup final)
    {loan : Loan (n + 1)} {slots : Region (n + 1) Atom} {lens : Lens Atom} {original value : Value}
    (live : store.region loan.referent.region = some slots)
    (focused : (loan.referent.place loan.target).find slots = some lens)
    (resident : lens.selected = some original) (oldReady : original.ready) (newReady : value.ready)
    (sameLayout : value.layout (Atom.kind signature) = original.layout (Atom.kind signature)) (temp : Cell Atom) :
    StackTyped program signature (store.replaceLoan loan slots lens value temp) ceiling stack output cleanup final :=
  typed.frame (fun region _ => store.replaceLoan_regionKinds live focused resident oldReady newReady sameLayout temp region)


end OwnershipMir.Calls
